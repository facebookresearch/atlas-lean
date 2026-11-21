/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.ApproximateDifferentialPrivacy
import Cslib.Probability.PMF
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.ENNReal.BigOperators

/-!
# Rényi differential privacy for finite discrete distributions

The Rényi moment and divergence of order `α > 1`, Rényi DP (`IsRDP`) for
ordered adjacent pairs, data processing, independent product composition,
and conversion to approximate DP (Mironov 2017, Props 1 and 3).
-/

@[expose] public section

namespace CSLibExt.Privacy.RenyiDifferentialPrivacy

open Classical
open scoped ENNReal

/-- Rényi moment of order `α` between finite distributions `P` and `Q`. -/
noncomputable def renyiMoment {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) (α : ℝ) : ℝ :=
  ∑ w, (P w).toReal ^ α / (Q w).toReal ^ (α - 1)

/-- Rényi divergence of order `α` between finite distributions `P` and `Q`. -/
noncomputable def renyiDiv {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * Real.log (renyiMoment P Q α)

/-- Support inclusion: every outcome possible under `P` is possible under `Q`. -/
def Support {Ω : Type*} (P Q : PMF Ω) : Prop :=
  ∀ w, P w ≠ 0 → Q w ≠ 0

/-- Rényi DP of order `α` with budget `ε`, for ordered adjacent pairs. -/
def IsRDP {Database Output : Type*} [Fintype Output] (M : Database → PMF Output)
    (adj : Database → Database → Prop) (α ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ d d', adj d d' →
    Support (M d) (M d') ∧ renyiDiv (M d) (M d') α ≤ ε

/-- Independent product of two distributions. -/
noncomputable def prodPMF {Ω₁ Ω₂ : Type*} (P1 : PMF Ω₁) (P2 : PMF Ω₂) :
    PMF (Ω₁ × Ω₂) :=
  P1.bind fun a => P2.bind fun b => PMF.pure (a, b)

/-- Approximate-DP epsilon obtained from Rényi DP conversion. -/
noncomputable def rdpEps2 (ε δ α : ℝ) : ℝ :=
  ε + Real.log (1 / δ) / (α - 1)

private theorem pmf_sum_eq_one {Ω : Type*} [Fintype Ω] (P : PMF Ω) :
    ∑ w, P w = 1 := by
  have h := P.tsum_coe
  rwa [tsum_fintype] at h

private theorem pmf_toReal_sum {Ω : Type*} [Fintype Ω] (P : PMF Ω) :
    ∑ w, (P w).toReal = 1 := by
  have h := congrArg ENNReal.toReal (pmf_sum_eq_one P)
  rw [ENNReal.toReal_sum (fun a _ => P.apply_ne_top a)] at h
  simpa using h

private theorem support_toReal {Ω : Type*} {P Q : PMF Ω} (hs : Support P Q)
    (w : Ω) (h : (P w).toReal ≠ 0) : (Q w).toReal ≠ 0 := by
  have hP : P w ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have hQ := hs w hP
  intro h0
  rw [ENNReal.toReal_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact hQ h0
  · exact (Q.apply_ne_top w) h0

/-- Pointwise bridge between the quotient and weight-times-ratio forms. -/
private theorem rpow_div_eq_mul_rpow {p q α : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hα : 1 < α) (hs : p ≠ 0 → q ≠ 0) :
    p ^ α / q ^ (α - 1) = q * (p / q) ^ α := by
  have hαne : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα)
  by_cases hq0 : q = 0
  · have hp0 : p = 0 := by
      by_contra hne
      exact (hs hne) hq0
    rw [hp0, hq0, Real.zero_rpow hαne]
    simp
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    rw [Real.div_rpow hp hq α]
    have hsplit : q ^ α = q ^ (α - 1) * q := by
      conv_lhs => rw [← sub_add_cancel α 1]
      rw [Real.rpow_add hqpos, Real.rpow_one]
    have hqpow : q ^ (α - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hqpos _)
    have hqpow2 : q ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hqpos _)
    have hqne : q ≠ 0 := ne_of_gt hqpos
    have heq : q * (p ^ α / q ^ α) = p ^ α / q ^ (α - 1) := by
      rw [hsplit]
      field_simp
    rw [heq]

theorem renyiMoment_self {Ω : Type*} [Fintype Ω] (P : PMF Ω) {α : ℝ}
    (hα : 1 < α) : renyiMoment P P α = 1 := by
  have hterm : ∀ w ∈ Finset.univ,
      (P w).toReal ^ α / (P w).toReal ^ (α - 1) = (P w).toReal := by
    intro w _
    by_cases h0 : (P w).toReal = 0
    · rw [h0, Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hα)), zero_div]
    · have hpos : 0 < (P w).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0)
      have hsplit : (P w).toReal ^ α
          = (P w).toReal ^ (α - 1) * (P w).toReal := by
        conv_lhs => rw [← sub_add_cancel α 1]
        rw [Real.rpow_add hpos, Real.rpow_one]
      rw [hsplit, div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hpos _))]
      ring
  rw [show renyiMoment P P α = ∑ w, (P w).toReal from
    Finset.sum_congr rfl hterm]
  exact pmf_toReal_sum P

theorem renyiDiv_self {Ω : Type*} [Fintype Ω] (P : PMF Ω) {α : ℝ}
    (hα : 1 < α) : renyiDiv P P α = 0 := by
  unfold renyiDiv
  rw [renyiMoment_self P hα, Real.log_one, mul_zero]

theorem one_le_renyiMoment {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) {α : ℝ}
    (hα : 1 < α) (hs : Support P Q) : 1 ≤ renyiMoment P Q α := by
  have hJ := ConvexOn.map_sum_le (𝕜 := ℝ) (E := ℝ) (β := ℝ)
    (convexOn_rpow (le_of_lt hα))
    (t := Finset.univ) (w := fun w => (Q w).toReal)
    (p := fun w => (P w).toReal / (Q w).toReal)
    (fun w _ => ENNReal.toReal_nonneg) (pmf_toReal_sum Q)
    (fun w _ => Set.mem_Ici.mpr
      (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
  simp only [smul_eq_mul] at hJ
  have hsum : ∑ w, (Q w).toReal * ((P w).toReal / (Q w).toReal) = 1 := by
    have hterm : ∀ w ∈ Finset.univ,
        (Q w).toReal * ((P w).toReal / (Q w).toReal) = (P w).toReal := by
      intro w _
      by_cases hq : (Q w).toReal = 0
      · have hp : (P w).toReal = 0 := by
          by_contra hne
          exact (support_toReal hs w hne) hq
        rw [hq, hp, zero_mul]
      · exact mul_div_cancel₀ _ hq
    calc ∑ w, (Q w).toReal * ((P w).toReal / (Q w).toReal)
        = ∑ w, (P w).toReal := Finset.sum_congr rfl hterm
      _ = 1 := pmf_toReal_sum P
  rw [hsum, Real.one_rpow] at hJ
  have hMom : renyiMoment P Q α
      = ∑ w, (Q w).toReal * (((P w).toReal / (Q w).toReal) ^ α) := by
    exact Finset.sum_congr rfl (fun w _ =>
      rpow_div_eq_mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg hα
        (fun h => support_toReal hs w h))
  rw [hMom]
  exact hJ

theorem nonneg_renyiDiv {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) {α : ℝ}
    (hα : 1 < α) (hs : Support P Q) : 0 ≤ renyiDiv P Q α := by
  unfold renyiDiv
  apply mul_nonneg
  · exact div_nonneg zero_le_one (le_of_lt (sub_pos.mpr hα))
  · exact Real.log_nonneg (one_le_renyiMoment P Q hα hs)

private theorem bind_toReal {Ω Ω₂ : Type*} [Fintype Ω] [Fintype Ω₂]
    (P : PMF Ω) (k : Ω → PMF Ω₂) (y : Ω₂) :
    ((P.bind k) y).toReal = ∑ x, (P x).toReal * ((k x) y).toReal := by
  rw [PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum (fun x _ =>
      ENNReal.mul_ne_top (P.apply_ne_top x) ((k x).apply_ne_top y))]
  apply Finset.sum_congr rfl
  intro x _
  exact ENNReal.toReal_mul

private theorem support_bind {Ω Ω₂ : Type*} [Fintype Ω] {P Q : PMF Ω}
    (k : Ω → PMF Ω₂) (hs : Support P Q) : Support (P.bind k) (Q.bind k) := by
  intro y hy
  rw [PMF.bind_apply, tsum_fintype] at hy ⊢
  have hnonneg : ∀ x ∈ Finset.univ, (0 : ℝ≥0∞) ≤ P x * (k x) y :=
    fun x _ => zero_le
  obtain ⟨x, _, hx⟩ : ∃ x ∈ Finset.univ, P x * (k x) y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).mpr hcon)
  have hPx : P x ≠ 0 := by
    intro h0
    exact hx (by rw [h0, zero_mul])
  have hkx : (k x) y ≠ 0 := by
    intro h0
    exact hx (by rw [h0, mul_zero])
  have hterm : Q x * (k x) y ≠ 0 := mul_ne_zero (hs x hPx) hkx
  have hle : Q x * (k x) y ≤ ∑ x', Q x' * (k x') y :=
    Finset.single_le_sum
      (fun x' _ => (zero_le : (0 : ℝ≥0∞) ≤ Q x' * (k x') y))
      (Finset.mem_univ x)
  intro hsum0
  rw [hsum0] at hle
  exact hterm (le_antisymm hle (zero_le))

theorem renyiMoment_bind_le {Ω Ω₂ : Type*} [Fintype Ω] [Fintype Ω₂]
    (P Q : PMF Ω) (k : Ω → PMF Ω₂) {α : ℝ} (hα : 1 < α)
    (hs : Support P Q) :
    renyiMoment (P.bind k) (Q.bind k) α ≤ renyiMoment P Q α := by
  have hs' : Support (P.bind k) (Q.bind k) := support_bind k hs
  have hterm_le : ∀ y ∈ Finset.univ,
      ((P.bind k) y).toReal ^ α / ((Q.bind k) y).toReal ^ (α - 1)
        ≤ ∑ x, (Q x).toReal * ((k x) y).toReal *
          ((P x).toReal / (Q x).toReal) ^ α := by
    intro y _
    set py : ℝ := ((P.bind k) y).toReal with hpy_def
    set qy : ℝ := ((Q.bind k) y).toReal with hqy_def
    have hpy : py = ∑ x, (P x).toReal * ((k x) y).toReal := bind_toReal P k y
    have hqy : qy = ∑ x, (Q x).toReal * ((k x) y).toReal := bind_toReal Q k y
    have hqy_nn : 0 ≤ qy := ENNReal.toReal_nonneg
    by_cases hqy0 : qy = 0
    · have hpy0 : py = 0 := by
        by_contra hne
        exact (support_toReal hs' y hne) hqy0
      rw [hpy0, hqy0, Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hα)),
        zero_div]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg
        (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        (Real.rpow_nonneg
          (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) _))
    · have hqy_ne : qy ≠ 0 := hqy0
      rw [rpow_div_eq_mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg hα
        (fun h => support_toReal hs' y h)]
      have hw1 : ∑ x, (Q x).toReal * ((k x) y).toReal / qy = 1 := by
        calc ∑ x, (Q x).toReal * ((k x) y).toReal / qy
            = (1 / qy) * ∑ x, (Q x).toReal * ((k x) y).toReal := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl
                (fun x _ => by rw [mul_comm (1 / qy) _, mul_one_div])
          _ = 1 := by rw [← hqy, one_div_mul_cancel hqy_ne]
      have hwp : ∑ x, ((Q x).toReal * ((k x) y).toReal / qy) *
          ((P x).toReal / (Q x).toReal) = py / qy := by
        have hterm : ∀ x ∈ Finset.univ,
            ((Q x).toReal * ((k x) y).toReal / qy) *
              ((P x).toReal / (Q x).toReal)
              = ((P x).toReal * ((k x) y).toReal) / qy := by
          intro x _
          by_cases hqx : (Q x).toReal = 0
          · have hpx : (P x).toReal = 0 := by
              by_contra hne
              exact (support_toReal hs x hne) hqx
            rw [hqx, hpx]
            simp
          · rw [div_mul_eq_mul_div, mul_assoc,
              mul_comm ((k x) y).toReal _, ← mul_assoc,
              mul_div_cancel₀ _ hqx]
        calc ∑ x, ((Q x).toReal * ((k x) y).toReal / qy) *
              ((P x).toReal / (Q x).toReal)
            = ∑ x, ((P x).toReal * ((k x) y).toReal) / qy :=
              Finset.sum_congr rfl hterm
          _ = (1 / qy) * ∑ x, ((P x).toReal * ((k x) y).toReal) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl
                (fun x _ => by rw [mul_comm (1 / qy) _, mul_one_div])
          _ = py / qy := by rw [← hpy, mul_comm, mul_one_div]
      have hJ := ConvexOn.map_sum_le (𝕜 := ℝ) (E := ℝ) (β := ℝ)
        (convexOn_rpow (le_of_lt hα))
        (t := Finset.univ)
        (w := fun x => (Q x).toReal * ((k x) y).toReal / qy)
        (p := fun x => (P x).toReal / (Q x).toReal)
        (fun x _ => div_nonneg
          (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
          ENNReal.toReal_nonneg) hw1
        (fun x _ => Set.mem_Ici.mpr
          (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))
      simp only [smul_eq_mul] at hJ
      rw [hwp] at hJ
      have hmul := mul_le_mul_of_nonneg_left hJ hqy_nn
      have hsm : qy * ∑ x, ((Q x).toReal * ((k x) y).toReal / qy) *
          (((P x).toReal / (Q x).toReal) ^ α)
          = ∑ x, (Q x).toReal * ((k x) y).toReal *
            (((P x).toReal / (Q x).toReal) ^ α) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [← mul_assoc, mul_div_cancel₀ _ hqy_ne]
      rw [hsm] at hmul
      exact hmul
  calc renyiMoment (P.bind k) (Q.bind k) α
      = ∑ y, (((P.bind k) y).toReal ^ α / ((Q.bind k) y).toReal ^ (α - 1)) :=
        rfl
    _ ≤ ∑ y, ∑ x, (Q x).toReal * ((k x) y).toReal *
        (((P x).toReal / (Q x).toReal) ^ α) :=
        Finset.sum_le_sum hterm_le
    _ = ∑ x, (Q x).toReal * (((P x).toReal / (Q x).toReal) ^ α) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        have hinner : ∀ y ∈ Finset.univ,
            (Q x).toReal * ((k x) y).toReal *
              (((P x).toReal / (Q x).toReal) ^ α)
            = ((Q x).toReal * (((P x).toReal / (Q x).toReal) ^ α)) *
              ((k x) y).toReal := by
          intro y _
          ring
        have hms := Finset.mul_sum Finset.univ (fun y => ((k x) y).toReal)
          ((Q x).toReal * (((P x).toReal / (Q x).toReal) ^ α))
        rw [Finset.sum_congr rfl hinner, ← hms, pmf_toReal_sum, mul_one]
    _ = renyiMoment P Q α :=
        Finset.sum_congr rfl (fun x _ =>
          (rpow_div_eq_mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg hα
            (fun h => support_toReal hs x h)).symm)

theorem renyiDiv_bind_le {Ω Ω₂ : Type*} [Fintype Ω] [Fintype Ω₂]
    (P Q : PMF Ω) (k : Ω → PMF Ω₂) {α : ℝ} (hα : 1 < α)
    (hs : Support P Q) :
    renyiDiv (P.bind k) (Q.bind k) α ≤ renyiDiv P Q α := by
  unfold renyiDiv
  apply mul_le_mul_of_nonneg_left
  · apply Real.log_le_log
    · exact lt_of_lt_of_le zero_lt_one
        (one_le_renyiMoment _ _ hα (support_bind k hs))
    · exact renyiMoment_bind_le P Q k hα hs
  · exact div_nonneg zero_le_one (le_of_lt (sub_pos.mpr hα))

theorem isRDP_bind {Database A B : Type*} [Fintype A] [Fintype B]
    {M : Database → PMF A} {adj : Database → Database → Prop} {α ε : ℝ}
    (hα : 1 < α) (h : IsRDP M adj α ε) (k : A → PMF B) :
    IsRDP (fun d => (M d).bind k) adj α ε := by
  refine ⟨h.1, fun d d' hadj => ?_⟩
  obtain ⟨hs, hdiv⟩ := h.2 d d' hadj
  refine ⟨support_bind k hs, (renyiDiv_bind_le _ _ k hα hs).trans hdiv⟩

theorem support_prodPMF {Ω₁ Ω₂ : Type*} (P1 Q1 : PMF Ω₁) (P2 Q2 : PMF Ω₂)
    (hs1 : Support P1 Q1) (hs2 : Support P2 Q2) :
    Support (prodPMF P1 P2) (prodPMF Q1 Q2) := by
  intro ⟨a, b⟩ h
  unfold prodPMF at h ⊢
  rw [Cslib.Probability.PMF.bind_pair_apply] at h ⊢
  have h1 : P1 a ≠ 0 := by
    intro h0
    exact h (by rw [h0, zero_mul])
  have h2 : P2 b ≠ 0 := by
    intro h0
    exact h (by rw [h0, mul_zero])
  exact mul_ne_zero (hs1 a h1) (hs2 b h2)

theorem renyiMoment_prodPMF {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (P1 Q1 : PMF Ω₁) (P2 Q2 : PMF Ω₂) {α : ℝ} :
    renyiMoment (prodPMF P1 P2) (prodPMF Q1 Q2) α
      = renyiMoment P1 Q1 α * renyiMoment P2 Q2 α := by
  unfold renyiMoment prodPMF
  rw [Fintype.sum_prod_type]
  have hpt : ∀ a b,
      ((P1.bind fun a' => (P2.bind fun b' => PMF.pure (a', b'))) (a, b)).toReal
        = (P1 a).toReal * (P2 b).toReal := by
    intro a b
    rw [Cslib.Probability.PMF.bind_pair_apply, ENNReal.toReal_mul]
  have hqt : ∀ a b,
      ((Q1.bind fun a' => (Q2.bind fun b' => PMF.pure (a', b'))) (a, b)).toReal
        = (Q1 a).toReal * (Q2 b).toReal := by
    intro a b
    rw [Cslib.Probability.PMF.bind_pair_apply, ENNReal.toReal_mul]
  simp_rw [hpt, hqt]
  have hterm : ∀ a b,
      ((P1 a).toReal * (P2 b).toReal) ^ α
          / ((Q1 a).toReal * (Q2 b).toReal) ^ (α - 1)
        = ((P1 a).toReal ^ α / (Q1 a).toReal ^ (α - 1))
          * ((P2 b).toReal ^ α / (Q2 b).toReal ^ (α - 1)) := by
    intro a b
    rw [Real.mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      Real.mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      mul_div_mul_comm]
  simp_rw [hterm, ← Finset.sum_mul_sum]

theorem renyiDiv_prodPMF {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (P1 Q1 : PMF Ω₁) (P2 Q2 : PMF Ω₂) {α : ℝ} (hα : 1 < α)
    (hs1 : Support P1 Q1) (hs2 : Support P2 Q2) :
    renyiDiv (prodPMF P1 P2) (prodPMF Q1 Q2) α
      = renyiDiv P1 Q1 α + renyiDiv P2 Q2 α := by
  unfold renyiDiv
  rw [renyiMoment_prodPMF]
  have h1 : renyiMoment P1 Q1 α ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_renyiMoment P1 Q1 hα hs1))
  have h2 : renyiMoment P2 Q2 α ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_renyiMoment P2 Q2 hα hs2))
  rw [Real.log_mul h1 h2, mul_add]

theorem isRDP_prodPMF {Database A B : Type*} [Fintype A] [Fintype B]
    {M1 : Database → PMF A} {M2 : Database → PMF B}
    {adj : Database → Database → Prop} {α ε1 ε2 : ℝ} (hα : 1 < α)
    (h1 : IsRDP M1 adj α ε1) (h2 : IsRDP M2 adj α ε2) :
    IsRDP (fun d => prodPMF (M1 d) (M2 d)) adj α (ε1 + ε2) := by
  refine ⟨add_nonneg h1.1 h2.1, fun d d' hadj => ?_⟩
  obtain ⟨hs1, hdiv1⟩ := h1.2 d d' hadj
  obtain ⟨hs2, hdiv2⟩ := h2.2 d d' hadj
  refine ⟨support_prodPMF _ _ _ _ hs1 hs2, ?_⟩
  rw [renyiDiv_prodPMF _ _ _ _ hα hs1 hs2]
  exact add_le_add hdiv1 hdiv2

private theorem exp_rpow (a b : ℝ) :
    (Real.exp a) ^ b = Real.exp (a * b) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp]

private theorem moment_le_exp_of_renyiDiv {Ω : Type*} [Fintype Ω]
    (P Q : PMF Ω) {α ε : ℝ} (hα : 1 < α) (hs : Support P Q)
    (hdiv : renyiDiv P Q α ≤ ε) :
    renyiMoment P Q α ≤ Real.exp ((α - 1) * ε) := by
  have hα1 : (0 : ℝ) < α - 1 := sub_pos.mpr hα
  have hMpos : (0 : ℝ) < renyiMoment P Q α :=
    lt_of_lt_of_le zero_lt_one (one_le_renyiMoment P Q hα hs)
  have hlog : Real.log (renyiMoment P Q α) ≤ (α - 1) * ε := by
    unfold renyiDiv at hdiv
    have h := mul_le_mul_of_nonneg_left hdiv (le_of_lt hα1)
    rwa [← mul_assoc, mul_one_div_cancel hα1.ne', one_mul] at h
  conv_lhs => rw [← Real.exp_log hMpos]
  exact Real.exp_le_exp.mpr hlog

theorem holder_event_bound {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) {α : ℝ}
    (hα : 1 < α) (hs : Support P Q) (s : Finset Ω) :
    ∑ w ∈ s, (P w).toReal ≤ renyiMoment P Q α ^ (1 / α)
      * (∑ w ∈ s, (Q w).toReal) ^ (1 - 1 / α) := by
  classical
  have hα0 : (0 : ℝ) < α := lt_trans zero_lt_one hα
  have hαne : α ≠ 0 := ne_of_gt hα0
  have hα1 : (0 : ℝ) < α - 1 := sub_pos.mpr hα
  have hα1ne : α - 1 ≠ 0 := ne_of_gt hα1
  have hqeq : α.conjExponent = α / (α - 1) := rfl
  set c : ℝ := (α - 1) / α with hc
  have hpq : α.HolderConjugate α.conjExponent :=
    Real.HolderConjugate.conjExponent hα
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s)
    (f := fun w => (P w).toReal / (Q w).toReal ^ c)
    (g := fun w => (Q w).toReal ^ c)
    (p := α) (q := α.conjExponent) hpq
    (fun w _ => div_nonneg ENNReal.toReal_nonneg
      (Real.rpow_nonneg ENNReal.toReal_nonneg _))
    (fun w _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hterm : ∀ w ∈ s, (P w).toReal / (Q w).toReal ^ c * (Q w).toReal ^ c
      = (P w).toReal := by
    intro w _
    by_cases hq0 : (Q w).toReal = 0
    · have hp0 : (P w).toReal = 0 := by
        by_contra hne
        exact (support_toReal hs w hne) hq0
      rw [hp0, hq0]
      simp
    · exact div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos
        (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hq0)) _))
  have hfpow : ∀ w ∈ s, ((P w).toReal / (Q w).toReal ^ c) ^ α
      = (P w).toReal ^ α / (Q w).toReal ^ (α - 1) := by
    intro w _
    rw [Real.div_rpow ENNReal.toReal_nonneg
      (Real.rpow_nonneg ENNReal.toReal_nonneg _) α]
    congr 1
    rw [← Real.rpow_mul ENNReal.toReal_nonneg]
    congr 1
    rw [hc]
    exact div_mul_cancel₀ _ hαne
  have hMle : (∑ w ∈ s, ((P w).toReal / (Q w).toReal ^ c) ^ α)
      ≤ renyiMoment P Q α := by
    calc (∑ w ∈ s, ((P w).toReal / (Q w).toReal ^ c) ^ α)
        = ∑ w ∈ s, ((P w).toReal ^ α / (Q w).toReal ^ (α - 1)) :=
          Finset.sum_congr rfl hfpow
      _ ≤ ∑ w, ((P w).toReal ^ α / (Q w).toReal ^ (α - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
            (fun w _ _ => div_nonneg
              (Real.rpow_nonneg ENNReal.toReal_nonneg _)
              (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      _ = renyiMoment P Q α := rfl
  have hMpow : (∑ w ∈ s, ((P w).toReal / (Q w).toReal ^ c) ^ α) ^ (1 / α)
      ≤ renyiMoment P Q α ^ (1 / α) :=
    Real.rpow_le_rpow
      (Finset.sum_nonneg (fun w _ => Real.rpow_nonneg
        (div_nonneg ENNReal.toReal_nonneg
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)) _))
      hMle (one_div_nonneg.mpr (le_of_lt hα0))
  have hq1 : c * α.conjExponent = 1 := by
    rw [hc, hqeq, div_mul_div_comm, mul_comm (α - 1) α,
      div_self (mul_ne_zero hαne hα1ne)]
  have hgpow : ∀ w ∈ s, ((Q w).toReal ^ c) ^ α.conjExponent
      = (Q w).toReal := by
    intro w _
    rw [← Real.rpow_mul ENNReal.toReal_nonneg, hq1, Real.rpow_one]
  have hexp : 1 / α.conjExponent = 1 - 1 / α := by
    rw [hqeq, one_div_div, sub_div, div_self hαne]
  calc ∑ w ∈ s, (P w).toReal
      = ∑ w ∈ s, (P w).toReal / (Q w).toReal ^ c * (Q w).toReal ^ c :=
        Finset.sum_congr rfl (fun w hw => (hterm w hw).symm)
    _ ≤ (∑ w ∈ s, ((P w).toReal / (Q w).toReal ^ c) ^ α) ^ (1 / α)
        * (∑ w ∈ s, ((Q w).toReal ^ c) ^ α.conjExponent)
          ^ (1 / α.conjExponent) := hH
    _ ≤ renyiMoment P Q α ^ (1 / α) * (∑ w ∈ s, (Q w).toReal) ^ (1 - 1 / α) := by
        rw [hexp, Finset.sum_congr rfl hgpow]
        exact mul_le_mul_of_nonneg_right hMpow (Real.rpow_nonneg
          (Finset.sum_nonneg (fun w _ => ENNReal.toReal_nonneg)) _)

private theorem toOuterMeasure_toReal {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (S : Set Ω) :
    (P.toOuterMeasure S).toReal
      = ∑ w ∈ Finset.univ.filter (fun w => w ∈ S), (P w).toReal := by
  classical
  have h1 : ∀ x ∈ Finset.univ.filter (fun w => w ∈ S),
      (S.indicator (⇑P) x).toReal = (P x).toReal := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Set.indicator_of_mem hx.2]
  have h2 : ∀ x ∈ Finset.univ, x ∉ Finset.univ.filter (fun w => w ∈ S) →
      (S.indicator (⇑P) x).toReal = 0 := by
    intro x _ hx
    rw [Finset.mem_filter] at hx
    simp only [Finset.mem_univ, true_and] at hx
    rw [Set.indicator_of_notMem hx]
    exact ENNReal.toReal_zero
  rw [PMF.toOuterMeasure_apply_fintype,
    ENNReal.toReal_sum (fun x _ => by
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        exact P.apply_ne_top x
      · rw [Set.indicator_of_notMem hx]
        exact ENNReal.zero_ne_top)]
  calc ∑ x, (S.indicator ⇑P x).toReal
      = ∑ x ∈ Finset.univ.filter (fun w => w ∈ S),
        (S.indicator ⇑P x).toReal :=
        (Finset.sum_subset (Finset.filter_subset _ _) h2).symm
    _ = ∑ x ∈ Finset.univ.filter (fun w => w ∈ S), (P x).toReal :=
        Finset.sum_congr rfl h1

private theorem toOuter_ne_top {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (S : Set Ω) : P.toOuterMeasure S ≠ ⊤ := by
  have hle : P.toOuterMeasure S ≤ 1 := by
    rw [PMF.toOuterMeasure_apply_fintype]
    calc ∑ x, S.indicator ⇑P x ≤ ∑ x, P x :=
          Finset.sum_le_sum (fun x _ => Set.indicator_le_self S ⇑P x)
      _ = 1 := pmf_sum_eq_one P
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)

theorem approx_event_of_renyi {Ω : Type*} [Fintype Ω] (P Q : PMF Ω)
    {α ε δ : ℝ} (hα : 1 < α) (hs : Support P Q)
    (hdiv : renyiDiv P Q α ≤ ε) (hδ0 : 0 < δ)
    (s : Finset Ω) :
    ∑ w ∈ s, (P w).toReal ≤ Real.exp (rdpEps2 ε δ α)
      * (∑ w ∈ s, (Q w).toReal) + δ := by
  classical
  have hα0 : (0 : ℝ) < α := lt_trans zero_lt_one hα
  have hαne : α ≠ 0 := ne_of_gt hα0
  have hα1 : (0 : ℝ) < α - 1 := sub_pos.mpr hα
  have hα1ne : α - 1 ≠ 0 := ne_of_gt hα1
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hH := holder_event_bound P Q hα hs s
  have hM := moment_le_exp_of_renyiDiv P Q hα hs hdiv
  have hQS_nn : 0 ≤ ∑ w ∈ s, (Q w).toReal :=
    Finset.sum_nonneg (fun w _ => ENNReal.toReal_nonneg)
  set γ : ℝ := 1 - 1 / α with hγ
  have hγeq : γ = (α - 1) / α := by
    rw [hγ, sub_div, div_self hαne]
  have hγnn : 0 ≤ γ := by
    rw [hγeq]
    exact div_nonneg (le_of_lt hα1) (le_of_lt hα0)
  set C : ℝ := (Real.exp ε * ∑ w ∈ s, (Q w).toReal) ^ γ with hC
  set ε2 : ℝ := rdpEps2 ε δ α with hε2
  have hPS_le : ∑ w ∈ s, (P w).toReal ≤ C := by
    have hMpow : renyiMoment P Q α ^ (1 / α) ≤ (Real.exp ε) ^ γ := by
      have h1 : renyiMoment P Q α ^ (1 / α)
          ≤ (Real.exp ((α - 1) * ε)) ^ (1 / α) :=
        Real.rpow_le_rpow
          (le_of_lt (lt_of_lt_of_le zero_lt_one
            (one_le_renyiMoment P Q hα hs)))
          hM (one_div_nonneg.mpr (le_of_lt hα0))
      have h2 : (Real.exp ((α - 1) * ε)) ^ (1 / α)
          = (Real.exp ε) ^ γ := by
        simp only [exp_rpow]
        congr 1
        rw [hγ]
        field_simp
      exact h1.trans h2.le
    calc ∑ w ∈ s, (P w).toReal
        ≤ renyiMoment P Q α ^ (1 / α) * (∑ w ∈ s, (Q w).toReal) ^ γ := hH
      _ ≤ (Real.exp ε) ^ γ * (∑ w ∈ s, (Q w).toReal) ^ γ :=
          mul_le_mul_of_nonneg_right hMpow
            (Real.rpow_nonneg hQS_nn _)
      _ = C := by
          rw [hC, ← Real.mul_rpow (Real.exp_pos ε).le hQS_nn]
  by_cases hcase : ∑ w ∈ s, (Q w).toReal ≤ δ * Real.exp (-ε2)
  · have hbelow : C ≤ δ := by
      have hbase : Real.exp ε * ∑ w ∈ s, (Q w).toReal
          ≤ Real.exp ε * (δ * Real.exp (-ε2)) :=
        mul_le_mul_of_nonneg_left hcase (Real.exp_pos ε).le
      have hbase_nn : 0 ≤ Real.exp ε * ∑ w ∈ s, (Q w).toReal :=
        mul_nonneg (Real.exp_pos ε).le hQS_nn
      have hC_le : C ≤ (Real.exp ε * (δ * Real.exp (-ε2))) ^ γ := by
        rw [hC]
        exact Real.rpow_le_rpow hbase_nn hbase hγnn
      have hval : (Real.exp ε * (δ * Real.exp (-ε2))) ^ γ = δ := by
        have hkey : Real.exp ε * (δ * Real.exp (-ε2))
            = δ ^ (α / (α - 1)) := by
          have h1 : Real.exp ε * (δ * Real.exp (-ε2))
              = δ * Real.exp (ε + -ε2) := by
            simp only [Real.exp_add]
            ring
          have hlog : Real.log (1 / δ) = -Real.log δ := by
            rw [Real.log_div one_ne_zero hδne, Real.log_one, zero_sub]
          have h2 : ε + -ε2 = Real.log δ / (α - 1) := by
            rw [hε2]
            unfold rdpEps2
            rw [hlog, neg_div]
            abel
          have h3 : Real.exp (Real.log δ / (α - 1))
              = δ ^ (1 / (α - 1)) := by
            have heq : Real.log δ / (α - 1)
                = Real.log δ * (1 / (α - 1)) := (mul_one_div _ _).symm
            rw [heq, ← exp_rpow, Real.exp_log hδ0]
          have hexp1 : (1 : ℝ) + 1 / (α - 1) = α / (α - 1) := by
            rw [eq_div_iff hα1ne, add_mul, one_mul,
              div_mul_cancel₀ _ hα1ne, sub_add_cancel]
          rw [h1, h2, h3]
          nth_rewrite 1 [← Real.rpow_one δ]
          rw [← Real.rpow_add hδ0, hexp1]
        have hγ1 : α / (α - 1) * γ = 1 := by
          rw [hγeq, div_mul_div_comm, mul_comm α (α - 1),
            div_self (mul_ne_zero hα1ne hαne)]
        rw [hkey, ← Real.rpow_mul (le_of_lt hδ0), hγ1, Real.rpow_one]
      rw [hval] at hC_le
      exact hC_le
    calc ∑ w ∈ s, (P w).toReal ≤ C := hPS_le
      _ ≤ δ := hbelow
      _ ≤ Real.exp ε2 * (∑ w ∈ s, (Q w).toReal) + δ :=
          le_add_of_nonneg_left
            (mul_nonneg (Real.exp_pos _).le hQS_nn)
  · push Not at hcase
    have hQpos : 0 < ∑ w ∈ s, (Q w).toReal :=
      lt_of_le_of_lt (mul_nonneg (le_of_lt hδ0) (Real.exp_pos _).le) hcase
    have hTle : (δ * Real.exp (-ε2)) ^ (1 / α)
        ≤ (∑ w ∈ s, (Q w).toReal) ^ (1 / α) :=
      Real.rpow_le_rpow
        (mul_nonneg (le_of_lt hδ0) (Real.exp_pos _).le)
        (le_of_lt hcase) (one_div_nonneg.mpr (le_of_lt hα0))
    have hQsplit : ∑ w ∈ s, (Q w).toReal
        = (∑ w ∈ s, (Q w).toReal) ^ γ
          * (∑ w ∈ s, (Q w).toReal) ^ (1 / α) := by
      rw [← Real.rpow_add hQpos,
        show γ + 1 / α = 1 from by rw [hγ]; ring, Real.rpow_one]
    have hTeq : Real.exp ε2 * (δ * Real.exp (-ε2)) ^ (1 / α)
        = Real.exp (ε * γ) := by
      have hlog : Real.log (1 / δ) = -Real.log δ := by
        rw [Real.log_div one_ne_zero hδne, Real.log_one, zero_sub]
      have hδrpow : δ ^ (1 / α) = Real.exp (Real.log δ * (1 / α)) := by
        rw [← exp_rpow, Real.exp_log hδ0]
      rw [Real.mul_rpow (le_of_lt hδ0) (Real.exp_pos _).le,
        exp_rpow _ (1 / α), hδrpow, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [hε2, hγ, rdpEps2, hlog]
      field_simp
      ring
    have hmain : (Real.exp ε * ∑ w ∈ s, (Q w).toReal) ^ γ
        ≤ Real.exp ε2 * ∑ w ∈ s, (Q w).toReal := by
      rw [Real.mul_rpow (Real.exp_pos ε).le hQS_nn]
      conv_rhs => rw [hQsplit]
      have hrw : Real.exp ε2
          * ((∑ w ∈ s, (Q w).toReal) ^ γ * (∑ w ∈ s, (Q w).toReal) ^ (1 / α))
          = (∑ w ∈ s, (Q w).toReal) ^ γ
            * (Real.exp ε2 * (∑ w ∈ s, (Q w).toReal) ^ (1 / α)) := by
        ring
      rw [hrw, mul_comm ((Real.exp ε) ^ γ) _]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hQS_nn _)
      calc (Real.exp ε) ^ γ = Real.exp (ε * γ) := exp_rpow ε γ
        _ = Real.exp ε2 * (δ * Real.exp (-ε2)) ^ (1 / α) := hTeq.symm
        _ ≤ Real.exp ε2 * (∑ w ∈ s, (Q w).toReal) ^ (1 / α) :=
            mul_le_mul_of_nonneg_left hTle (Real.exp_pos _).le
    calc ∑ w ∈ s, (P w).toReal ≤ C := hPS_le
      _ = (Real.exp ε * ∑ w ∈ s, (Q w).toReal) ^ γ := by rw [hC]
      _ ≤ Real.exp ε2 * ∑ w ∈ s, (Q w).toReal := hmain
      _ ≤ Real.exp ε2 * ∑ w ∈ s, (Q w).toReal + δ :=
          le_add_of_nonneg_right (le_of_lt hδ0)

theorem isApproxDP_of_isRDP {Database A : Type*} [Fintype A]
    {M : Database → PMF A} {adj : Database → Database → Prop} {α ε δ : ℝ}
    (hα : 1 < α) (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h : IsRDP M adj α ε) :
    CSLibExt.Privacy.DifferentialPrivacy.IsApproxDP M adj
      (rdpEps2 ε δ α) δ := by
  classical
  refine ⟨?_, le_of_lt hδ0, fun d d' hadj s => ?_⟩
  · unfold rdpEps2
    apply add_nonneg hε
    apply div_nonneg _ (le_of_lt (sub_pos.mpr hα))
    apply Real.log_nonneg
    exact (one_le_div hδ0).mpr (le_of_lt hδ1)
  · obtain ⟨hs, hdiv⟩ := h.2 d d' hadj
    have hreal := approx_event_of_renyi (M d) (M d') hα hs hdiv hδ0
      (Finset.univ.filter (fun w => w ∈ s))
    rw [← toOuterMeasure_toReal (M d) s,
      ← toOuterMeasure_toReal (M d') s] at hreal
    have hfin1 := toOuter_ne_top (M d) s
    have hfin2 := toOuter_ne_top (M d') s
    conv_lhs => rw [← ENNReal.ofReal_toReal hfin1]
    have hle := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_add
      (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
      (le_of_lt hδ0),
      ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_toReal hfin2] at hle
    exact hle

end CSLibExt.Privacy.RenyiDifferentialPrivacy
