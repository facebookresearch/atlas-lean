/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.ApproximateDifferentialPrivacy
public import MathlibExt.InformationTheory.MutualInformation
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
import Mathlib.Data.EReal.Basic

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

/-- Real-valued Rényi moment formula of order `α`, valid under `Support`. -/
noncomputable def renyiMomentReal {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) (α : ℝ) : ℝ :=
  ∑ w, (P w).toReal ^ α / (Q w).toReal ^ (α - 1)

/-- Support inclusion: every outcome possible under `P` is possible under `Q`. -/
def Support {Ω : Type*} (P Q : PMF Ω) : Prop :=
  ∀ w, P w ≠ 0 → Q w ≠ 0

/-- Rényi moment of order `α` between finite distributions `P` and `Q`:
`⊤` off support or at `α ≤ 1`, the real formula otherwise. -/
noncomputable def renyiMoment {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) (α : ℝ) : EReal :=
  if Support P Q ∧ 1 < α then ↑(renyiMomentReal P Q α) else ⊤

/-- Real-valued Rényi divergence formula of order `α`, valid under `Support`. -/
noncomputable def renyiDivReal {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * Real.log (renyiMomentReal P Q α)

/-- Rényi divergence of order `α`: `⊤` off support or at `α ≤ 1`, the real
formula otherwise. -/
noncomputable def renyiDiv {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) (α : ℝ) : EReal :=
  if Support P Q ∧ 1 < α then ↑(renyiDivReal P Q α) else ⊤

/-- On support and above order 1, `renyiMoment` is the real formula, coerced. -/
theorem renyiMoment_of_support {Ω : Type*} [Fintype Ω] {P Q : PMF Ω} {α : ℝ}
    (hs : Support P Q) (hα : 1 < α) :
    renyiMoment P Q α = ↑(renyiMomentReal P Q α) := by
  unfold renyiMoment
  exact ite_eq_left ⟨hs, hα⟩

/-- Off support, `renyiMoment` is infinite. -/
theorem renyiMoment_of_not_support {Ω : Type*} [Fintype Ω] {P Q : PMF Ω} {α : ℝ}
    (hs : ¬ Support P Q) : renyiMoment P Q α = ⊤ := by
  unfold renyiMoment
  exact ite_eq_right (fun h => hs h.1)

/-- At order `α ≤ 1`, `renyiMoment` is infinite. -/
theorem renyiMoment_of_le_one {Ω : Type*} [Fintype Ω] {P Q : PMF Ω} {α : ℝ}
    (hα : α ≤ 1) : renyiMoment P Q α = ⊤ := by
  unfold renyiMoment
  exact ite_eq_right (fun h => not_lt_of_ge hα h.2)

/-- On support and above order 1, `renyiDiv` is the real formula, coerced. -/
theorem renyiDiv_of_support {Ω : Type*} [Fintype Ω] {P Q : PMF Ω} {α : ℝ}
    (hs : Support P Q) (hα : 1 < α) :
    renyiDiv P Q α = ↑(renyiDivReal P Q α) := by
  unfold renyiDiv
  exact ite_eq_left ⟨hs, hα⟩

/-- Off support, `renyiDiv` is infinite. -/
theorem renyiDiv_of_not_support {Ω : Type*} [Fintype Ω] {P Q : PMF Ω} {α : ℝ}
    (hs : ¬ Support P Q) : renyiDiv P Q α = ⊤ := by
  unfold renyiDiv
  exact ite_eq_right (fun h => hs h.1)

/-- At order `α ≤ 1`, `renyiDiv` is infinite. -/
theorem renyiDiv_of_le_one {Ω : Type*} [Fintype Ω] {P Q : PMF Ω} {α : ℝ}
    (hα : α ≤ 1) : renyiDiv P Q α = ⊤ := by
  unfold renyiDiv
  exact ite_eq_right (fun h => not_lt_of_ge hα h.2)

/-- Rényi DP of order `α` with budget `ε`, for ordered adjacent pairs. -/
def IsRDP {Database Output : Type*} [Fintype Output] (M : Database → PMF Output)
    (adj : Database → Database → Prop) (α ε : ℝ) : Prop :=
  0 ≤ ε ∧ 1 < α ∧ ∀ d d', adj d d' →
    Support (M d) (M d') ∧ renyiDiv (M d) (M d') α ≤ (ε : EReal)

/-- Approximate-DP epsilon obtained from Rényi DP conversion; meaningful only
for `1 < α`. -/
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

private theorem renyiMomentReal_self {Ω : Type*} [Fintype Ω] (P : PMF Ω) {α : ℝ}
    (hα : 1 < α) : renyiMomentReal P P α = 1 := by
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
  rw [show renyiMomentReal P P α = ∑ w, (P w).toReal from
    Finset.sum_congr rfl hterm]
  exact pmf_toReal_sum P

theorem renyiMoment_self {Ω : Type*} [Fintype Ω] (P : PMF Ω) {α : ℝ}
    (hα : 1 < α) : renyiMoment P P α = 1 := by
  rw [renyiMoment_of_support (fun w h => h) hα, renyiMomentReal_self P hα,
    EReal.coe_one]

private theorem renyiDivReal_self {Ω : Type*} [Fintype Ω] (P : PMF Ω) {α : ℝ}
    (hα : 1 < α) : renyiDivReal P P α = 0 := by
  unfold renyiDivReal
  rw [renyiMomentReal_self P hα, Real.log_one, mul_zero]

theorem renyiDiv_self {Ω : Type*} [Fintype Ω] (P : PMF Ω) {α : ℝ}
    (hα : 1 < α) : renyiDiv P P α = 0 := by
  rw [renyiDiv_of_support (fun w h => h) hα, EReal.coe_eq_zero]
  exact renyiDivReal_self P hα

private theorem one_le_renyiMomentReal {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) {α : ℝ}
    (hα : 1 < α) (hs : Support P Q) : 1 ≤ renyiMomentReal P Q α := by
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
  have hMom : renyiMomentReal P Q α
      = ∑ w, (Q w).toReal * (((P w).toReal / (Q w).toReal) ^ α) := by
    exact Finset.sum_congr rfl (fun w _ =>
      rpow_div_eq_mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg hα
        (fun h => support_toReal hs w h))
  rw [hMom]
  exact hJ

theorem one_le_renyiMoment {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) {α : ℝ}
    (hα : 1 < α) (hs : Support P Q) : 1 ≤ renyiMoment P Q α := by
  rw [renyiMoment_of_support hs hα, ← EReal.coe_one, EReal.coe_le_coe_iff]
  exact one_le_renyiMomentReal P Q hα hs

private theorem renyiDivReal_nonneg {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) {α : ℝ}
    (hα : 1 < α) (hs : Support P Q) : 0 ≤ renyiDivReal P Q α := by
  unfold renyiDivReal
  apply mul_nonneg
  · exact div_nonneg zero_le_one (le_of_lt (sub_pos.mpr hα))
  · exact Real.log_nonneg (one_le_renyiMomentReal P Q hα hs)

theorem nonneg_renyiDiv {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) {α : ℝ}
    (hα : 1 < α) (hs : Support P Q) : 0 ≤ renyiDiv P Q α := by
  rw [renyiDiv_of_support hs hα, EReal.coe_nonneg]
  exact renyiDivReal_nonneg P Q hα hs

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
  exact hterm (le_antisymm hle zero_le)

private theorem renyiMomentReal_bind_le {Ω Ω₂ : Type*} [Fintype Ω] [Fintype Ω₂]
    (P Q : PMF Ω) (k : Ω → PMF Ω₂) {α : ℝ} (hα : 1 < α)
    (hs : Support P Q) :
    renyiMomentReal (P.bind k) (Q.bind k) α ≤ renyiMomentReal P Q α := by
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
  calc renyiMomentReal (P.bind k) (Q.bind k) α
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
    _ = renyiMomentReal P Q α :=
        Finset.sum_congr rfl (fun x _ =>
          (rpow_div_eq_mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg hα
            (fun h => support_toReal hs x h)).symm)

theorem renyiMoment_bind_le {Ω Ω₂ : Type*} [Fintype Ω] [Fintype Ω₂]
    (P Q : PMF Ω) (k : Ω → PMF Ω₂) {α : ℝ} (hα : 1 < α)
    (hs : Support P Q) :
    renyiMoment (P.bind k) (Q.bind k) α ≤ renyiMoment P Q α := by
  rw [renyiMoment_of_support (support_bind k hs) hα,
    renyiMoment_of_support hs hα, EReal.coe_le_coe_iff]
  exact renyiMomentReal_bind_le P Q k hα hs

private theorem renyiDivReal_bind_le {Ω Ω₂ : Type*} [Fintype Ω] [Fintype Ω₂]
    (P Q : PMF Ω) (k : Ω → PMF Ω₂) {α : ℝ} (hα : 1 < α)
    (hs : Support P Q) :
    renyiDivReal (P.bind k) (Q.bind k) α ≤ renyiDivReal P Q α := by
  unfold renyiDivReal
  apply mul_le_mul_of_nonneg_left
  · apply Real.log_le_log
    · exact lt_of_lt_of_le zero_lt_one
        (one_le_renyiMomentReal _ _ hα (support_bind k hs))
    · exact renyiMomentReal_bind_le P Q k hα hs
  · exact div_nonneg zero_le_one (le_of_lt (sub_pos.mpr hα))

theorem renyiDiv_bind_le {Ω Ω₂ : Type*} [Fintype Ω] [Fintype Ω₂]
    (P Q : PMF Ω) (k : Ω → PMF Ω₂) {α : ℝ} (hα : 1 < α)
    (hs : Support P Q) :
    renyiDiv (P.bind k) (Q.bind k) α ≤ renyiDiv P Q α := by
  rw [renyiDiv_of_support (support_bind k hs) hα,
    renyiDiv_of_support hs hα, EReal.coe_le_coe_iff]
  exact renyiDivReal_bind_le P Q k hα hs

theorem isRDP_bind {Database A B : Type*} [Fintype A] [Fintype B]
    {M : Database → PMF A} {adj : Database → Database → Prop} {α ε : ℝ}
    (h : IsRDP M adj α ε) (k : A → PMF B) :
    IsRDP (fun d => (M d).bind k) adj α ε := by
  refine ⟨h.1, h.2.1, fun d d' hadj => ?_⟩
  obtain ⟨hs, hdiv⟩ := h.2.2 d d' hadj
  refine ⟨support_bind k hs, (renyiDiv_bind_le _ _ k h.2.1 hs).trans hdiv⟩

theorem support_prodJoint {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (P1 Q1 : PMF Ω₁) (P2 Q2 : PMF Ω₂)
    (hs1 : Support P1 Q1) (hs2 : Support P2 Q2) :
    Support (InformationTheory.prodJoint P1 P2)
      (InformationTheory.prodJoint Q1 Q2) := by
  intro ⟨a, b⟩ h
  rw [InformationTheory.prodJoint_apply] at h ⊢
  have h1 : P1 a ≠ 0 := by
    intro h0
    exact h (by rw [h0, zero_mul])
  have h2 : P2 b ≠ 0 := by
    intro h0
    exact h (by rw [h0, mul_zero])
  exact mul_ne_zero (hs1 a h1) (hs2 b h2)

private theorem exists_off_support {Ω : Type*} {P Q : PMF Ω} (hs : ¬ Support P Q) :
    ∃ w, P w ≠ 0 ∧ Q w = 0 := by
  by_contra hcon
  push Not at hcon
  exact hs hcon

private theorem exists_pos_mass {Ω : Type*} [Fintype Ω] (P : PMF Ω) :
    ∃ w, P w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 : ∑ w, P w = 0 := Finset.sum_eq_zero (fun w _ => hcon w)
  rw [pmf_sum_eq_one] at h0
  exact one_ne_zero h0

private theorem renyiMomentReal_pos {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) {α : ℝ}
    (hs : Support P Q) : 0 < renyiMomentReal P Q α := by
  obtain ⟨w, hwP⟩ := exists_pos_mass P
  have hwQ := hs w hwP
  have hp : 0 < (P w).toReal := ENNReal.toReal_pos hwP (P.apply_ne_top w)
  have hq : 0 < (Q w).toReal := ENNReal.toReal_pos hwQ (Q.apply_ne_top w)
  have hterm : 0 < (P w).toReal ^ α / (Q w).toReal ^ (α - 1) :=
    div_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hq _)
  have hnonneg : ∀ x ∈ Finset.univ,
      0 ≤ (P x).toReal ^ α / (Q x).toReal ^ (α - 1) := fun x _ =>
    div_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  calc (0 : ℝ) < (P w).toReal ^ α / (Q w).toReal ^ (α - 1) := hterm
    _ ≤ ∑ x, (P x).toReal ^ α / (Q x).toReal ^ (α - 1) :=
        Finset.single_le_sum hnonneg (Finset.mem_univ w)
    _ = renyiMomentReal P Q α := rfl

private theorem not_support_prodJoint_left {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (P1 Q1 : PMF Ω₁) (P2 Q2 : PMF Ω₂) (hs : ¬ Support P1 Q1) :
    ¬ Support (InformationTheory.prodJoint P1 P2)
      (InformationTheory.prodJoint Q1 Q2) := by
  obtain ⟨a, haP, haQ⟩ := exists_off_support hs
  obtain ⟨b, hbP⟩ := exists_pos_mass P2
  intro hsup
  have hP : InformationTheory.prodJoint P1 P2 (a, b) ≠ 0 := by
    rw [InformationTheory.prodJoint_apply]
    exact mul_ne_zero haP hbP
  have hQ : InformationTheory.prodJoint Q1 Q2 (a, b) = 0 := by
    rw [InformationTheory.prodJoint_apply, haQ, zero_mul]
  exact hsup (a, b) hP hQ

private theorem not_support_prodJoint_right {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (P1 Q1 : PMF Ω₁) (P2 Q2 : PMF Ω₂) (hs : ¬ Support P2 Q2) :
    ¬ Support (InformationTheory.prodJoint P1 P2)
      (InformationTheory.prodJoint Q1 Q2) := by
  obtain ⟨b, hbP, hbQ⟩ := exists_off_support hs
  obtain ⟨a, haP⟩ := exists_pos_mass P1
  intro hsup
  have hP : InformationTheory.prodJoint P1 P2 (a, b) ≠ 0 := by
    rw [InformationTheory.prodJoint_apply]
    exact mul_ne_zero haP hbP
  have hQ : InformationTheory.prodJoint Q1 Q2 (a, b) = 0 := by
    rw [InformationTheory.prodJoint_apply, hbQ, mul_zero]
  exact hsup (a, b) hP hQ

private theorem renyiMomentReal_prodJoint {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (P1 Q1 : PMF Ω₁) (P2 Q2 : PMF Ω₂) {α : ℝ} :
    renyiMomentReal (InformationTheory.prodJoint P1 P2)
        (InformationTheory.prodJoint Q1 Q2) α
      = renyiMomentReal P1 Q1 α * renyiMomentReal P2 Q2 α := by
  unfold renyiMomentReal
  rw [Fintype.sum_prod_type]
  have hpt : ∀ a b,
      ((InformationTheory.prodJoint P1 P2) (a, b)).toReal
        = (P1 a).toReal * (P2 b).toReal := by
    intro a b
    rw [InformationTheory.prodJoint_apply, ENNReal.toReal_mul]
  have hqt : ∀ a b,
      ((InformationTheory.prodJoint Q1 Q2) (a, b)).toReal
        = (Q1 a).toReal * (Q2 b).toReal := by
    intro a b
    rw [InformationTheory.prodJoint_apply, ENNReal.toReal_mul]
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

theorem renyiMoment_prodJoint {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (P1 Q1 : PMF Ω₁) (P2 Q2 : PMF Ω₂) {α : ℝ} :
    renyiMoment (InformationTheory.prodJoint P1 P2)
        (InformationTheory.prodJoint Q1 Q2) α
      = renyiMoment P1 Q1 α * renyiMoment P2 Q2 α := by
  by_cases hα : 1 < α
  · by_cases hs1 : Support P1 Q1
    · by_cases hs2 : Support P2 Q2
      · rw [renyiMoment_of_support (support_prodJoint _ _ _ _ hs1 hs2) hα,
          renyiMoment_of_support hs1 hα, renyiMoment_of_support hs2 hα,
          ← EReal.coe_mul, renyiMomentReal_prodJoint]
      · rw [renyiMoment_of_not_support
            (not_support_prodJoint_right P1 Q1 P2 Q2 hs2),
          renyiMoment_of_support hs1 hα, renyiMoment_of_not_support hs2,
          EReal.coe_mul_top_of_pos (renyiMomentReal_pos _ _ hs1)]
    · by_cases hs2 : Support P2 Q2
      · rw [renyiMoment_of_not_support
            (not_support_prodJoint_left P1 Q1 P2 Q2 hs1),
          renyiMoment_of_not_support hs1, renyiMoment_of_support hs2 hα,
          EReal.top_mul_coe_of_pos (renyiMomentReal_pos _ _ hs2)]
      · rw [renyiMoment_of_not_support
            (not_support_prodJoint_left P1 Q1 P2 Q2 hs1),
          renyiMoment_of_not_support hs1, renyiMoment_of_not_support hs2,
          EReal.top_mul_top]
  · have hle : α ≤ 1 := le_of_not_gt hα
    rw [renyiMoment_of_le_one hle, renyiMoment_of_le_one hle,
      renyiMoment_of_le_one hle, EReal.top_mul_top]

private theorem renyiDivReal_prodJoint {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (P1 Q1 : PMF Ω₁) (P2 Q2 : PMF Ω₂) {α : ℝ} (hα : 1 < α)
    (hs1 : Support P1 Q1) (hs2 : Support P2 Q2) :
    renyiDivReal (InformationTheory.prodJoint P1 P2)
        (InformationTheory.prodJoint Q1 Q2) α
      = renyiDivReal P1 Q1 α + renyiDivReal P2 Q2 α := by
  unfold renyiDivReal
  rw [renyiMomentReal_prodJoint]
  have h1 : renyiMomentReal P1 Q1 α ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_renyiMomentReal P1 Q1 hα hs1))
  have h2 : renyiMomentReal P2 Q2 α ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_renyiMomentReal P2 Q2 hα hs2))
  rw [Real.log_mul h1 h2, mul_add]

theorem renyiDiv_prodJoint {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (P1 Q1 : PMF Ω₁) (P2 Q2 : PMF Ω₂) {α : ℝ} (hα : 1 < α)
    (hs1 : Support P1 Q1) (hs2 : Support P2 Q2) :
    renyiDiv (InformationTheory.prodJoint P1 P2)
        (InformationTheory.prodJoint Q1 Q2) α
      = renyiDiv P1 Q1 α + renyiDiv P2 Q2 α := by
  rw [renyiDiv_of_support (support_prodJoint _ _ _ _ hs1 hs2) hα,
    renyiDiv_of_support hs1 hα,
    renyiDiv_of_support hs2 hα, ← EReal.coe_add,
    EReal.coe_eq_coe_iff]
  exact renyiDivReal_prodJoint _ _ _ _ hα hs1 hs2

theorem isRDP_prodJoint {Database A B : Type*} [Fintype A] [Fintype B]
    {M1 : Database → PMF A} {M2 : Database → PMF B}
    {adj : Database → Database → Prop} {α ε1 ε2 : ℝ}
    (h1 : IsRDP M1 adj α ε1) (h2 : IsRDP M2 adj α ε2) :
    IsRDP (fun d => InformationTheory.prodJoint (M1 d) (M2 d)) adj α
      (ε1 + ε2) := by
  have hα := h1.2.1
  refine ⟨add_nonneg h1.1 h2.1, hα, fun d d' hadj => ?_⟩
  obtain ⟨hs1, hdiv1⟩ := h1.2.2 d d' hadj
  obtain ⟨hs2, hdiv2⟩ := h2.2.2 d d' hadj
  have h1R : renyiDivReal (M1 d) (M1 d') α ≤ ε1 := by
    rw [renyiDiv_of_support hs1 hα] at hdiv1
    exact EReal.coe_le_coe_iff.mp hdiv1
  have h2R : renyiDivReal (M2 d) (M2 d') α ≤ ε2 := by
    rw [renyiDiv_of_support hs2 hα] at hdiv2
    exact EReal.coe_le_coe_iff.mp hdiv2
  refine ⟨support_prodJoint _ _ _ _ hs1 hs2, ?_⟩
  rw [renyiDiv_prodJoint _ _ _ _ hα hs1 hs2,
    renyiDiv_of_support hs1 hα,
    renyiDiv_of_support hs2 hα, ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  exact add_le_add h1R h2R

private theorem exp_rpow (a b : ℝ) :
    (Real.exp a) ^ b = Real.exp (a * b) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp]

private theorem moment_le_exp_of_renyiDiv {Ω : Type*} [Fintype Ω]
    (P Q : PMF Ω) {α ε : ℝ} (hα : 1 < α) (hs : Support P Q)
    (hdiv : renyiDivReal P Q α ≤ ε) :
    renyiMomentReal P Q α ≤ Real.exp ((α - 1) * ε) := by
  have hα1 : (0 : ℝ) < α - 1 := sub_pos.mpr hα
  have hMpos : (0 : ℝ) < renyiMomentReal P Q α :=
    lt_of_lt_of_le zero_lt_one (one_le_renyiMomentReal P Q hα hs)
  have hlog : Real.log (renyiMomentReal P Q α) ≤ (α - 1) * ε := by
    unfold renyiDivReal at hdiv
    have h := mul_le_mul_of_nonneg_left hdiv (le_of_lt hα1)
    rwa [← mul_assoc, mul_one_div_cancel hα1.ne', one_mul] at h
  conv_lhs => rw [← Real.exp_log hMpos]
  exact Real.exp_le_exp.mpr hlog

private theorem bind_map_pair_apply {A B : Type*} [Fintype A] [Fintype B]
    (P1 : PMF A) (P2 : A → PMF B) (y : A) (z : B) :
    ((P1.bind (fun x => (P2 x).map (fun w => (x, w)))) (y, z))
      = P1 y * (P2 y) z := by
  rw [PMF.bind_apply, tsum_fintype]
  have hmap : ∀ x : A, ((P2 x).map (fun w => (x, w))) (y, z)
      = if x = y then (P2 x) z else 0 := by
    intro x
    simp only [PMF.map_apply, tsum_fintype]
    by_cases hxy : x = y
    · rw [hxy, Finset.sum_eq_single_of_mem z (Finset.mem_univ z)
        (fun w _ hne => by
          have hfalse : ¬ ((y, z) = (y, w)) :=
            fun h => hne (congrArg Prod.snd h).symm
          rw [ite_eq_right hfalse]),
        ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right hxy, Finset.sum_eq_zero (fun w _ => by
          have hfalse : ¬ ((y, z) = (x, w)) :=
            fun h => hxy (congrArg Prod.fst h).symm
          rw [ite_eq_right hfalse])]
  simp_rw [hmap]
  rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)
    (fun x _ hne => by rw [ite_eq_right hne, mul_zero]),
    ite_eq_left rfl]

private theorem bind_map_pair_toReal {A B : Type*} [Fintype A] [Fintype B]
    (P1 : PMF A) (P2 : A → PMF B) (y : A) (z : B) :
    (((P1.bind (fun x => (P2 x).map (fun w => (x, w)))) (y, z))).toReal
      = (P1 y).toReal * ((P2 y) z).toReal := by
  rw [bind_map_pair_apply, ENNReal.toReal_mul]

private theorem support_bind_adaptive {Database A B : Type*}
    [Fintype A] [Fintype B]
    {M1 : Database → PMF A} {M2 : Database → A → PMF B}
    {d d' : Database}
    (hs1 : Support (M1 d) (M1 d'))
    (hs2 : ∀ y, Support (M2 d y) (M2 d' y)) :
    Support ((M1 d).bind (fun y => (M2 d y).map (fun z => (y, z))))
      ((M1 d').bind (fun y => (M2 d' y).map (fun z => (y, z)))) := by
  rintro ⟨y, z⟩ hne
  rw [bind_map_pair_apply] at hne ⊢
  have h1 : M1 d y ≠ 0 := by
    intro h0
    exact hne (by rw [h0, zero_mul])
  have h2 : M2 d y z ≠ 0 := by
    intro h0
    exact hne (by rw [h0, mul_zero])
  exact mul_ne_zero (hs1 y h1) (hs2 y z h2)

private theorem renyiMomentReal_bind_adaptive {Database A B : Type*}
    [Fintype A] [Fintype B]
    {M1 : Database → PMF A} {M2 : Database → A → PMF B}
    {d d' : Database} {α : ℝ} :
    renyiMomentReal ((M1 d).bind (fun y => (M2 d y).map (fun z => (y, z))))
        ((M1 d').bind (fun y => (M2 d' y).map (fun z => (y, z)))) α
      = ∑ y, ((M1 d y).toReal ^ α / (M1 d' y).toReal ^ (α - 1))
        * renyiMomentReal (M2 d y) (M2 d' y) α := by
  unfold renyiMomentReal
  rw [Fintype.sum_prod_type]
  simp_rw [bind_map_pair_toReal]
  have hterm : ∀ y z,
      (((M1 d y).toReal * ((M2 d y) z).toReal) ^ α)
        / (((M1 d' y).toReal * ((M2 d' y) z).toReal) ^ (α - 1))
      = (((M1 d y).toReal ^ α / (M1 d' y).toReal ^ (α - 1)))
        * (((M2 d y) z).toReal ^ α / ((M2 d' y) z).toReal ^ (α - 1)) := by
    intro y z
    rw [Real.mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      Real.mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      mul_div_mul_comm]
  simp_rw [hterm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum]

/-- Adaptive composition: the second mechanism may depend on the first-stage
output. The hypothesis `h_eps2` is required because when `A` is empty `h2`
is vacuous, so nonnegativity of `ε2` does not follow from it. -/
theorem isRDP_bind_adaptive {Database A B : Type*} [Fintype A] [Fintype B]
    {M1 : Database → PMF A} {M2 : Database → A → PMF B}
    {adj : Database → Database → Prop} {α ε1 ε2 : ℝ}
    (h1 : IsRDP M1 adj α ε1) (h_eps2 : 0 ≤ ε2)
    (h2 : ∀ y, IsRDP (fun d => M2 d y) adj α ε2) :
    IsRDP (fun d => (M1 d).bind (fun y => (M2 d y).map (fun z => (y, z))))
      adj α (ε1 + ε2) := by
  have hα := h1.2.1
  refine ⟨add_nonneg h1.1 h_eps2, hα, fun d d' hadj => ?_⟩
  obtain ⟨hs1, hdiv1⟩ := h1.2.2 d d' hadj
  have hpair : ∀ y, Support (M2 d y) (M2 d' y)
      ∧ renyiDiv (M2 d y) (M2 d' y) α ≤ (ε2 : EReal) :=
    fun y => (h2 y).2.2 d d' hadj
  have hsJ : Support ((M1 d).bind (fun y => (M2 d y).map (fun z => (y, z))))
      ((M1 d').bind (fun y => (M2 d' y).map (fun z => (y, z)))) :=
    support_bind_adaptive hs1 (fun y => (hpair y).1)
  refine ⟨hsJ, ?_⟩
  have h1R : renyiDivReal (M1 d) (M1 d') α ≤ ε1 := by
    rw [renyiDiv_of_support hs1 hα] at hdiv1
    exact EReal.coe_le_coe_iff.mp hdiv1
  have h2R : ∀ y, renyiMomentReal (M2 d y) (M2 d' y) α
      ≤ Real.exp ((α - 1) * ε2) := by
    intro y
    obtain ⟨hs2y, hdiv2y⟩ := hpair y
    have hR : renyiDivReal (M2 d y) (M2 d' y) α ≤ ε2 := by
      rw [renyiDiv_of_support hs2y hα] at hdiv2y
      exact EReal.coe_le_coe_iff.mp hdiv2y
    exact moment_le_exp_of_renyiDiv _ _ hα hs2y hR
  have hM1 : renyiMomentReal (M1 d) (M1 d') α ≤ Real.exp ((α - 1) * ε1) :=
    moment_le_exp_of_renyiDiv _ _ hα hs1 h1R
  have hnn : ∀ y ∈ Finset.univ,
      0 ≤ (M1 d y).toReal ^ α / (M1 d' y).toReal ^ (α - 1) := by
    intro y _
    exact div_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hsum : renyiMomentReal
        ((M1 d).bind (fun y => (M2 d y).map (fun z => (y, z))))
        ((M1 d').bind (fun y => (M2 d' y).map (fun z => (y, z)))) α
      ≤ renyiMomentReal (M1 d) (M1 d') α * Real.exp ((α - 1) * ε2) := by
    rw [renyiMomentReal_bind_adaptive]
    calc ∑ y, ((M1 d y).toReal ^ α / (M1 d' y).toReal ^ (α - 1))
            * renyiMomentReal (M2 d y) (M2 d' y) α
        ≤ ∑ y, ((M1 d y).toReal ^ α / (M1 d' y).toReal ^ (α - 1))
            * Real.exp ((α - 1) * ε2) :=
          Finset.sum_le_sum (fun y _ =>
            mul_le_mul_of_nonneg_left (h2R y) (hnn y (Finset.mem_univ y)))
      _ = (∑ y, ((M1 d y).toReal ^ α / (M1 d' y).toReal ^ (α - 1)))
          * Real.exp ((α - 1) * ε2) := by
          rw [← Finset.sum_mul]
  have hexp : Real.exp ((α - 1) * ε1) * Real.exp ((α - 1) * ε2)
      = Real.exp ((α - 1) * (ε1 + ε2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hM : renyiMomentReal
        ((M1 d).bind (fun y => (M2 d y).map (fun z => (y, z))))
        ((M1 d').bind (fun y => (M2 d' y).map (fun z => (y, z)))) α
      ≤ Real.exp ((α - 1) * (ε1 + ε2)) := by
    calc _ ≤ renyiMomentReal (M1 d) (M1 d') α * Real.exp ((α - 1) * ε2) := hsum
      _ ≤ Real.exp ((α - 1) * ε1) * Real.exp ((α - 1) * ε2) :=
          mul_le_mul_of_nonneg_right hM1 (Real.exp_pos _).le
      _ = Real.exp ((α - 1) * (ε1 + ε2)) := hexp
  have hMpos : 0 < renyiMomentReal
        ((M1 d).bind (fun y => (M2 d y).map (fun z => (y, z))))
        ((M1 d').bind (fun y => (M2 d' y).map (fun z => (y, z)))) α :=
    lt_of_lt_of_le zero_lt_one (one_le_renyiMomentReal _ _ hα hsJ)
  rw [renyiDiv_of_support hsJ hα, EReal.coe_le_coe_iff]
  unfold renyiDivReal
  have hlog : Real.log (renyiMomentReal
        ((M1 d).bind (fun y => (M2 d y).map (fun z => (y, z))))
        ((M1 d').bind (fun y => (M2 d' y).map (fun z => (y, z)))) α)
      ≤ (α - 1) * (ε1 + ε2) := by
    calc Real.log _ ≤ Real.log (Real.exp ((α - 1) * (ε1 + ε2))) :=
          Real.log_le_log hMpos hM
      _ = (α - 1) * (ε1 + ε2) := Real.log_exp _
  calc (1 / (α - 1)) * Real.log _
      ≤ (1 / (α - 1)) * ((α - 1) * (ε1 + ε2)) :=
        mul_le_mul_of_nonneg_left hlog
          (one_div_nonneg.mpr (le_of_lt (sub_pos.mpr hα)))
    _ = ε1 + ε2 := by
        rw [← mul_assoc, one_div_mul_cancel (sub_pos.mpr hα).ne', one_mul]

theorem holder_event_bound {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) {α : ℝ}
    (hα : 1 < α) (hs : Support P Q) (s : Finset Ω) :
    ∑ w ∈ s, (P w).toReal ≤ renyiMomentReal P Q α ^ (1 / α)
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
      ≤ renyiMomentReal P Q α := by
    calc (∑ w ∈ s, ((P w).toReal / (Q w).toReal ^ c) ^ α)
        = ∑ w ∈ s, ((P w).toReal ^ α / (Q w).toReal ^ (α - 1)) :=
          Finset.sum_congr rfl hfpow
      _ ≤ ∑ w, ((P w).toReal ^ α / (Q w).toReal ^ (α - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
            (fun w _ _ => div_nonneg
              (Real.rpow_nonneg ENNReal.toReal_nonneg _)
              (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      _ = renyiMomentReal P Q α := rfl
  have hMpow : (∑ w ∈ s, ((P w).toReal / (Q w).toReal ^ c) ^ α) ^ (1 / α)
      ≤ renyiMomentReal P Q α ^ (1 / α) :=
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
    _ ≤ renyiMomentReal P Q α ^ (1 / α) * (∑ w ∈ s, (Q w).toReal) ^ (1 - 1 / α) := by
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
    (hdiv : renyiDiv P Q α ≤ (ε : EReal)) (hδ0 : 0 < δ)
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
  have hdivR : renyiDivReal P Q α ≤ ε := by
    have h := hdiv
    rw [renyiDiv_of_support hs hα] at h
    exact EReal.coe_le_coe_iff.mp h
  have hM := moment_le_exp_of_renyiDiv P Q hα hs hdivR
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
    have hMpow : renyiMomentReal P Q α ^ (1 / α) ≤ (Real.exp ε) ^ γ := by
      have h1 : renyiMomentReal P Q α ^ (1 / α)
          ≤ (Real.exp ((α - 1) * ε)) ^ (1 / α) :=
        Real.rpow_le_rpow
          (le_of_lt (lt_of_lt_of_le zero_lt_one
            (one_le_renyiMomentReal P Q hα hs)))
          hM (one_div_nonneg.mpr (le_of_lt hα0))
      have h2 : (Real.exp ((α - 1) * ε)) ^ (1 / α)
          = (Real.exp ε) ^ γ := by
        simp only [exp_rpow]
        congr 1
        rw [hγ]
        field_simp
      exact h1.trans h2.le
    calc ∑ w ∈ s, (P w).toReal
        ≤ renyiMomentReal P Q α ^ (1 / α) * (∑ w ∈ s, (Q w).toReal) ^ γ := hH
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
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h : IsRDP M adj α ε) :
    CSLibExt.Privacy.DifferentialPrivacy.IsApproxDP M adj
      (rdpEps2 ε δ α) δ := by
  classical
  have hα := h.2.1
  refine ⟨?_, le_of_lt hδ0, fun d d' hadj s => ?_⟩
  · unfold rdpEps2
    apply add_nonneg h.1
    apply div_nonneg _ (le_of_lt (sub_pos.mpr hα))
    apply Real.log_nonneg
    exact (one_le_div hδ0).mpr (le_of_lt hδ1)
  · obtain ⟨hs, hdiv⟩ := h.2.2 d d' hadj
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
