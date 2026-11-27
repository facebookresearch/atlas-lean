/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacyKFold
import CSLibExt.Crypto.Privacy.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite packing lower bounds for differential privacy

Packing lower bounds following Dwork and Roth (2014), Lemma 8.4, and Vadhan
(2017), Theorems 7.5.13 and 7.5.14, incorporating the March 14 2017 errata
(the printed `-δ` is corrected to `-m δ`).
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

open scoped ENNReal

private theorem toOuterMeasure_le_one {Ω : Type*} (p : PMF Ω) (s : Set Ω) :
    p.toOuterMeasure s ≤ 1 := by
  rw [PMF.toOuterMeasure_apply, ← p.tsum_coe]
  exact tsum_le_tsum (Set.indicator_le_self s _)

private theorem toOuterMeasure_ne_top {Ω : Type*} (p : PMF Ω) (s : Set Ω) :
    p.toOuterMeasure s ≠ ⊤ :=
  ne_of_lt ((toOuterMeasure_le_one p s).trans_lt ENNReal.one_lt_top)

private theorem toOuterMeasure_mono {Ω : Type*} (p : PMF Ω) {s t : Set Ω}
    (h : s ⊆ t) : p.toOuterMeasure s ≤ p.toOuterMeasure t := by
  simp only [PMF.toOuterMeasure_apply]
  apply tsum_le_tsum
  intro a
  by_cases ha : a ∈ t
  · by_cases has : a ∈ s
    · rw [Set.indicator_of_mem has, Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem has]
      positivity
  · have has : a ∉ s := fun hmem => ha (h hmem)
    rw [Set.indicator_of_notMem has, Set.indicator_of_notMem ha]

theorem toOuterMeasure_sum_le_one {Ω I : Type*} [Fintype I] (p : PMF Ω) (G : I → Set Ω) (hdisj : Pairwise (fun i j => Disjoint (G i) (G j))) : ∑ i : I, p.toOuterMeasure (G i) ≤ 1 := by
  simp only [PMF.toOuterMeasure_apply]
  have h1 : (∑ i : I, ∑' a, (G i).indicator (↑p) a)
      = ∑' i, ∑' a, (G i).indicator (↑p) a :=
    (tsum_fintype _).symm
  rw [h1, tsum_comm]
  simp only [tsum_fintype]
  calc ∑' a, ∑ i : I, (G i).indicator (↑p) a
      ≤ ∑' a, p a := by
        apply tsum_le_tsum
        intro a
        show ∑ i : I, (G i).indicator (↑p) a ≤ p a
        by_cases ha : ∃ i, a ∈ G i
        · obtain ⟨i₀, hi₀⟩ := ha
          rw [Finset.sum_eq_single i₀
            (fun i _ hi => Set.indicator_of_notMem
              (fun hmem => (Set.disjoint_left.mp (hdisj hi) hmem) hi₀) _)
            (fun h => absurd (Finset.mem_univ i₀) h),
            Set.indicator_of_mem hi₀ _]
        · have hall : ∀ i : I, (G i).indicator (↑p : Ω → ℝ≥0∞) a = 0 :=
            fun i => Set.indicator_of_notMem (fun hmem => ha ⟨i, hmem⟩) _
          have hzero : (∑ i : I, (G i).indicator (↑p : Ω → ℝ≥0∞) a) = 0 :=
            Finset.sum_eq_zero (fun i _ => hall i)
          rw [hzero]
          positivity
    _ = 1 := p.tsum_coe

private theorem relatesInSteps_to_chainFunc {D : Type*} (adj : D → D → Prop) :
    ∀ {k : ℕ} {d d' : D}, Relation.RelatesInSteps adj d d' k →
      ∃ z : ℕ → D, z 0 = d ∧ z k = d' ∧ ∀ i < k, adj (z i) (z (i + 1)) := by
  intro k
  induction k with
  | zero =>
    intro d d' h
    have heq : d = d' := h.zero
    subst heq
    exact ⟨fun _ => d, rfl, rfl, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ j ih =>
    intro d d' h
    obtain ⟨mid, hmid, hstep⟩ := h.succ
    obtain ⟨z, hz0, hzj, hz⟩ := ih hmid
    refine ⟨fun i => if i ≤ j then z i else d', ?_, ?_, ?_⟩
    · show (if (0 : ℕ) ≤ j then z 0 else d') = d
      rw [ite_eq_left (Nat.zero_le j), hz0]
    · show (if j + 1 ≤ j then z (j + 1) else d') = d'
      rw [ite_eq_right (by omega)]
    · intro i hi
      have h1 : i ≤ j := by omega
      show adj (if i ≤ j then z i else d') (if i + 1 ≤ j then z (i + 1) else d')
      rw [ite_eq_left h1]
      by_cases h2 : i + 1 ≤ j
      · rw [ite_eq_left h2]
        exact hz i (by omega)
      · have hij : i = j := by omega
        subst hij
        rw [ite_eq_right h2, hzj]
        exact hstep

private theorem approxDP_toDiffPrivate {D Ω : Type*} [MeasurableSpace Ω]
    {M : D → PMF Ω} {adj : D → D → Prop} {ε δ : ℝ}
    (hM : IsApproxDP M adj ε δ) :
    Cslib.Crypto.Privacy.DifferentiallyPrivate adj (fun d => (M d).toMeasure)
      ε (ENNReal.ofReal δ) := by
  intro x y hxy S hS
  show (M x).toMeasure S ≤ ENNReal.ofReal (Real.exp ε) * (M y).toMeasure S +
    ENNReal.ofReal δ
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hS,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hS]
  exact hM.2.2 x y hxy S

theorem isApproxDP_chain {D Ω : Type*} {M : D → PMF Ω} {adj : D → D → Prop} {ε δ : ℝ} (hM : IsApproxDP M adj ε δ) {k : ℕ} {d d' : D} (hchain : Relation.RelatesInSteps adj d d' k) (s : Set Ω) : (M d).toOuterMeasure s ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) * (M d').toOuterMeasure s + ENNReal.ofReal (δ * ∑ j ∈ Finset.range k, Real.exp ((j : ℝ) * ε)) := by
  let : MeasurableSpace Ω := ⊤
  obtain ⟨z, hz0, hzk, hz⟩ := relatesInSteps_to_chainFunc adj hchain
  have hDP := approxDP_toDiffPrivate hM
  have hS : MeasurableSet s := MeasurableSpace.measurableSet_top
  have h := hDP.group_sum hz hS
  rw [hz0, hzk] at h
  rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hS,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hS] at h
  have herr : Finset.sum (Finset.range k)
        (fun i => ENNReal.ofReal (Real.exp ((i : ℝ) * ε))) * ENNReal.ofReal δ =
      ENNReal.ofReal (δ * Finset.sum (Finset.range k)
        (fun j => Real.exp ((j : ℝ) * ε))) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (Real.exp_pos _).le)]
    rw [← ENNReal.ofReal_mul
      (Finset.sum_nonneg fun i _ => (Real.exp_pos _).le)]
    congr 1
    ring
  rw [herr] at h
  exact h

theorem isDP_chain_event {D Ω : Type*} {M : D → PMF Ω} {adj : D → D → Prop} {ε : ℝ} (hM : IsDP M adj ε) {k : ℕ} {d d' : D} (hchain : Relation.RelatesInSteps adj d d' k) (s : Set Ω) : (M d).toOuterMeasure s ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) * (M d').toOuterMeasure s := by
  have h := isApproxDP_chain (isApproxDP_zero_iff.mpr hM) hchain s
  rw [zero_mul, ENNReal.ofReal_zero, add_zero] at h
  exact h

theorem packing_lower_bound_approx {D Ω I : Type*} [Fintype I] {M : D → PMF Ω} {adj : D → D → Prop} {ε δ p : ℝ} {m : ℕ} (hM : IsApproxDP M adj ε δ) (d₀ : D) (d : I → D) (G : I → Set Ω) (hchain : ∀ i : I, ∃ k ≤ m, Relation.RelatesInSteps adj (d i) d₀ k) (hdisj : Pairwise (fun i j => Disjoint (G i) (G j))) (hprob : ∀ i : I, p ≤ ((M (d i)).toOuterMeasure (G i)).toReal) : (Fintype.card I : ℝ) * p ≤ Real.exp ((m : ℝ) * ε) + (Fintype.card I : ℝ) * (δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε)) := by
  have hε : 0 ≤ ε := hM.1
  have hδ : 0 ≤ δ := hM.2.1
  have hidx : ∀ i : I, p ≤ Real.exp ((m : ℝ) * ε) * ((M d₀).toOuterMeasure (G i)).toReal +
      (δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε)) := by
    intro i
    obtain ⟨k, hkm, hchain'⟩ := hchain i
    have hch := isApproxDP_chain hM hchain' (G i)
    have hkm' : (k : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hkm
    have hexp : Real.exp ((k : ℝ) * ε) ≤ Real.exp ((m : ℝ) * ε) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hkm' hε)
    have hsum : (∑ j ∈ Finset.range k, Real.exp ((j : ℝ) * ε)) ≤
        ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr hkm) (fun j _ _ => (Real.exp_pos _).le)
    have hδsum : δ * (∑ j ∈ Finset.range k, Real.exp ((j : ℝ) * ε)) ≤
        δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left hsum hδ
    have hmono : ENNReal.ofReal (Real.exp ((k : ℝ) * ε)) * (M d₀).toOuterMeasure (G i) +
          ENNReal.ofReal (δ * ∑ j ∈ Finset.range k, Real.exp ((j : ℝ) * ε)) ≤
        ENNReal.ofReal (Real.exp ((m : ℝ) * ε)) * (M d₀).toOuterMeasure (G i) +
          ENNReal.ofReal (δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε)) :=
      add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) le_rfl)
        (ENNReal.ofReal_le_ofReal hδsum)
    have hle := hch.trans hmono
    have hfin0 : (M d₀).toOuterMeasure (G i) ≠ ⊤ :=
      toOuterMeasure_ne_top _ _
    have hLHSfin : (M (d i)).toOuterMeasure (G i) ≠ ⊤ :=
      toOuterMeasure_ne_top _ _
    have hAfin : (ENNReal.ofReal (Real.exp ((m : ℝ) * ε)) *
        (M d₀).toOuterMeasure (G i)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin0
    have hBfin : ENNReal.ofReal
        (δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε)) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hRHSfin : (ENNReal.ofReal (Real.exp ((m : ℝ) * ε)) *
          (M d₀).toOuterMeasure (G i) +
        ENNReal.ofReal (δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε))) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩
    have htoReal := (ENNReal.toReal_le_toReal hLHSfin hRHSfin).mpr hle
    have hexp_nonneg : 0 ≤ Real.exp ((m : ℝ) * ε) := (Real.exp_pos _).le
    have hδsum_nonneg : 0 ≤ δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε) :=
      mul_nonneg hδ (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le)
    rw [ENNReal.toReal_add hAfin hBfin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hexp_nonneg,
      ENNReal.toReal_ofReal hδsum_nonneg] at htoReal
    exact (hprob i).trans htoReal
  have hsum1 : (∑ i : I, ((M d₀).toOuterMeasure (G i)).toReal) ≤ 1 := by
    have hle1 : ∑ i : I, (M d₀).toOuterMeasure (G i) ≤ 1 :=
      toOuterMeasure_sum_le_one _ _ hdisj
    have hfin : ∀ i ∈ Finset.univ, (M d₀).toOuterMeasure (G i) ≠ ⊤ :=
      fun i _ => toOuterMeasure_ne_top _ _
    have htoReal : (∑ i : I, ((M d₀).toOuterMeasure (G i)).toReal)
        = (∑ i : I, (M d₀).toOuterMeasure (G i)).toReal := by
      rw [ENNReal.toReal_sum hfin]
    have hsumfin : (∑ i : I, (M d₀).toOuterMeasure (G i)) ≠ ⊤ :=
      ne_of_lt (hle1.trans_lt ENNReal.one_lt_top)
    have h := (ENNReal.toReal_le_toReal hsumfin ENNReal.one_ne_top).mpr hle1
    rw [← htoReal, ENNReal.toReal_one] at h
    exact h
  have hcard : (Fintype.card I : ℝ) * p = ∑ i : I, p := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcard]
  calc ∑ i : I, p
      ≤ ∑ i : I, (Real.exp ((m : ℝ) * ε) * ((M d₀).toOuterMeasure (G i)).toReal +
          (δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε))) :=
        Finset.sum_le_sum (fun i _ => hidx i)
    _ = Real.exp ((m : ℝ) * ε) * (∑ i : I, ((M d₀).toOuterMeasure (G i)).toReal) +
          (Fintype.card I : ℝ) * (δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
    _ ≤ Real.exp ((m : ℝ) * ε) + (Fintype.card I : ℝ) *
          (δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε)) := by
        have hle : Real.exp ((m : ℝ) * ε) *
              (∑ i : I, ((M d₀).toOuterMeasure (G i)).toReal) +
              (Fintype.card I : ℝ) *
                (δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε)) ≤
            Real.exp ((m : ℝ) * ε) * 1 +
              (Fintype.card I : ℝ) *
                (δ * ∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε)) :=
          add_le_add
            (mul_le_mul_of_nonneg_left hsum1 (Real.exp_pos ((m : ℝ) * ε)).le)
            (le_refl _)
        rw [mul_one] at hle
        exact hle

theorem packing_lower_bound_approx_errata {D Ω I : Type*} [Fintype I] {M : D → PMF Ω} {adj : D → D → Prop} {ε δ p : ℝ} {m : ℕ} (hM : IsApproxDP M adj ε δ) (d₀ : D) (d : I → D) (G : I → Set Ω) (hchain : ∀ i : I, ∃ k ≤ m, Relation.RelatesInSteps adj (d i) d₀ k) (hdisj : Pairwise (fun i j => Disjoint (G i) (G j))) (hprob : ∀ i : I, p ≤ ((M (d i)).toOuterMeasure (G i)).toReal) : (Fintype.card I : ℝ) * (p * Real.exp (-((m : ℝ) * ε)) - (m : ℝ) * δ) ≤ 1 := by
  have hbase := packing_lower_bound_approx hM d₀ d G hchain hdisj hprob
  have hE : 0 ≤ Real.exp (-((m : ℝ) * ε)) := (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_right hbase hE
  have hEinv : Real.exp ((m : ℝ) * ε) * Real.exp (-((m : ℝ) * ε)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hterm : (∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε)) *
      Real.exp (-((m : ℝ) * ε)) ≤ (m : ℝ) := by
    rw [Finset.sum_mul]
    calc ∑ j ∈ Finset.range m,
            (Real.exp ((j : ℝ) * ε) * Real.exp (-((m : ℝ) * ε)))
          ≤ ∑ j ∈ Finset.range m, 1 :=
            Finset.sum_le_sum (fun j hj => by
              have hjm : (j : ℝ) ≤ (m : ℝ) := by
                exact_mod_cast le_of_lt (Finset.mem_range.mp hj)
              have h0 : ((j : ℝ) - (m : ℝ)) * ε ≤ 0 :=
                mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hjm) hM.1
              calc Real.exp ((j : ℝ) * ε) * Real.exp (-((m : ℝ) * ε))
                  = Real.exp (((j : ℝ) - (m : ℝ)) * ε) := by
                    rw [← Real.exp_add]
                    congr 1
                    ring
                _ ≤ Real.exp 0 := Real.exp_le_exp.mpr h0
                _ = 1 := Real.exp_zero)
        _ = (m : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hcard0 : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have h2 : (Fintype.card I : ℝ) * δ *
        ((∑ j ∈ Finset.range m, Real.exp ((j : ℝ) * ε)) *
          Real.exp (-((m : ℝ) * ε))) ≤
      (Fintype.card I : ℝ) * δ * (m : ℝ) :=
    mul_le_mul_of_nonneg_left hterm (mul_nonneg hcard0 hM.2.1)
  linear_combination hmul + hEinv + h2

theorem packing_lower_bound_pure {D Ω I : Type*} [Fintype I] {M : D → PMF Ω} {adj : D → D → Prop} {ε p : ℝ} {m : ℕ} (hM : IsDP M adj ε) (d₀ : D) (d : I → D) (G : I → Set Ω) (hchain : ∀ i : I, ∃ k ≤ m, Relation.RelatesInSteps adj (d i) d₀ k) (hdisj : Pairwise (fun i j => Disjoint (G i) (G j))) (hprob : ∀ i : I, p ≤ ((M (d i)).toOuterMeasure (G i)).toReal) : (Fintype.card I : ℝ) * p ≤ Real.exp ((m : ℝ) * ε) := by
  have h := packing_lower_bound_approx (isApproxDP_zero_iff.mpr hM) d₀ d G hchain
    hdisj hprob
  simpa using h

theorem packing_lower_bound_pure_log {D Ω I : Type*} [Fintype I] {M : D → PMF Ω} {adj : D → D → Prop} {ε p : ℝ} {m : ℕ} (hM : IsDP M adj ε) (d₀ : D) (d : I → D) (G : I → Set Ω) (hchain : ∀ i : I, ∃ k ≤ m, Relation.RelatesInSteps adj (d i) d₀ k) (hdisj : Pairwise (fun i j => Disjoint (G i) (G j))) (hprob : ∀ i : I, p ≤ ((M (d i)).toOuterMeasure (G i)).toReal) (hI : 0 < Fintype.card I) (hp : 0 < p) : Real.log ((Fintype.card I : ℝ) * p) ≤ (m : ℝ) * ε := by
  have hbase := packing_lower_bound_pure hM d₀ d G hchain hdisj hprob
  have hpos : 0 < (Fintype.card I : ℝ) * p :=
    mul_pos (Nat.cast_pos.mpr hI) hp
  calc Real.log ((Fintype.card I : ℝ) * p)
      ≤ Real.log (Real.exp ((m : ℝ) * ε)) := Real.log_le_log hpos hbase
    _ = (m : ℝ) * ε := Real.log_exp _

theorem packing_lower_bound_pure_eps_ge {D Ω I : Type*} [Fintype I] {M : D → PMF Ω} {adj : D → D → Prop} {ε p : ℝ} {m : ℕ} (hM : IsDP M adj ε) (d₀ : D) (d : I → D) (G : I → Set Ω) (hchain : ∀ i : I, ∃ k ≤ m, Relation.RelatesInSteps adj (d i) d₀ k) (hdisj : Pairwise (fun i j => Disjoint (G i) (G j))) (hprob : ∀ i : I, p ≤ ((M (d i)).toOuterMeasure (G i)).toReal) (hI : 0 < Fintype.card I) (hp : 0 < p) (hm : 0 < m) : Real.log ((Fintype.card I : ℝ) * p) / (m : ℝ) ≤ ε := by
  have h := packing_lower_bound_pure_log hM d₀ d G hchain hdisj hprob hI hp
  rw [div_le_iff₀ (Nat.cast_pos.mpr hm)]
  linarith [h]

theorem packing_lower_bound_pure_steps_ge {D Ω I : Type*} [Fintype I] {M : D → PMF Ω} {adj : D → D → Prop} {ε p : ℝ} {m : ℕ} (hM : IsDP M adj ε) (d₀ : D) (d : I → D) (G : I → Set Ω) (hchain : ∀ i : I, ∃ k ≤ m, Relation.RelatesInSteps adj (d i) d₀ k) (hdisj : Pairwise (fun i j => Disjoint (G i) (G j))) (hprob : ∀ i : I, p ≤ ((M (d i)).toOuterMeasure (G i)).toReal) (hI : 0 < Fintype.card I) (hp : 0 < p) (hε : 0 < ε) : Real.log ((Fintype.card I : ℝ) * p) / ε ≤ (m : ℝ) := by
  have h := packing_lower_bound_pure_log hM d₀ d G hchain hdisj hprob hI hp
  rw [div_le_iff₀ hε]
  exact h

theorem packing_lower_bound_approx_vacuous_of_delta_large {I : Type*} [Fintype I] {ε δ p : ℝ} {m : ℕ} (h : (m : ℝ) * δ ≥ p * Real.exp (-((m : ℝ) * ε))) : (Fintype.card I : ℝ) * (p * Real.exp (-((m : ℝ) * ε)) - (m : ℝ) * δ) ≤ 1 := by
  have hnonpos : p * Real.exp (-((m : ℝ) * ε)) - (m : ℝ) * δ ≤ 0 :=
    sub_nonpos.mpr h
  have hcard0 : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  calc (Fintype.card I : ℝ) * (p * Real.exp (-((m : ℝ) * ε)) - (m : ℝ) * δ)
      ≤ (Fintype.card I : ℝ) * 0 :=
        mul_le_mul_of_nonneg_left hnonpos hcard0
    _ = 0 := mul_zero _
    _ ≤ 1 := zero_le_one

def histCount {n N : ℕ} (d : Fin n → Fin N) (c : Fin N) : ℕ := (Finset.univ.filter fun i => d i = c).card

noncomputable def histFreq {n N : ℕ} (d : Fin n → Fin N) (c : Fin N) : ℝ := (histCount d c : ℝ) / (n : ℝ)

def histAccurate {n N : ℕ} (α : ℝ) (d : Fin n → Fin N) : Set (Fin N → ℝ) := {v | ∀ c : Fin N, |v c - (histCount d c : ℝ)| ≤ α}

def histPackingDB {n N : ℕ} (m : ℕ) (c₀ c : Fin N) : Fin n → Fin N := fun i => if (i : ℕ) < m then c else c₀

private theorem chainFunc_to_relatesInSteps {D : Type*} {r : D → D → Prop}
    (z : ℕ → D) :
    ∀ {m : ℕ}, (∀ i < m, r (z i) (z (i + 1))) →
      Relation.RelatesInSteps r (z 0) (z m) m := by
  intro m
  induction m with
  | zero =>
    intro _
    exact Relation.RelatesInSteps.refl _
  | succ k ih =>
    intro hz
    have hz' : ∀ i < k, r (z i) (z (i + 1)) :=
      fun i hi => hz i (Nat.lt_succ_of_lt hi)
    exact Relation.RelatesInSteps.tail _ _ _ k (ih hz') (hz k (Nat.lt_succ_self k))

private theorem replaceOne_hist_step {n N m : ℕ} (c₀ c : Fin N) (j : ℕ) :
    ReplaceOne (fun i : Fin n => if (i : ℕ) + j < m then c else c₀)
      (fun i : Fin n => if (i : ℕ) + (j + 1) < m then c else c₀) := by
  intro i hi i' hi'
  simp only [Set.mem_ofPred_eq] at hi hi'
  have key : ∀ t : Fin n,
      (if (t : ℕ) + j < m then c else c₀) ≠
        (if (t : ℕ) + (j + 1) < m then c else c₀) →
      (t : ℕ) + j + 1 = m := by
    intro t ht
    by_cases h1 : (t : ℕ) + j < m
    · by_cases h2 : (t : ℕ) + (j + 1) < m
      · exfalso
        apply ht
        rw [ite_eq_left h1, ite_eq_left h2]
      · omega
    · exfalso
      apply ht
      rw [ite_eq_right h1]
      have h2 : ¬ ((t : ℕ) + (j + 1) < m) := by omega
      rw [ite_eq_right h2]
  have e1 := key i hi
  have e2 := key i' hi'
  have hval : (i : ℕ) = (i' : ℕ) := by omega
  exact Fin.ext hval

private theorem relatesInSteps_histPackingDB {n N m : ℕ} (c₀ c : Fin N) :
    Relation.RelatesInSteps ReplaceOne
      (fun i : Fin n => if (i : ℕ) + 0 < m then c else c₀)
      (fun i : Fin n => if (i : ℕ) + m < m then c else c₀) m :=
  chainFunc_to_relatesInSteps (fun (j : ℕ) (i : Fin n) => if (i : ℕ) + j < m then c else c₀)
    (fun j _ => replaceOne_hist_step c₀ c j)

theorem histPackingDB_replaceOneChain {n N : ℕ} {m : ℕ} (hmn : m ≤ n) (c₀ c : Fin N) : ReplaceOneChain m (histPackingDB (n := n) m c₀ c) (histPackingDB (n := n) m c₀ c₀) := by
  have hchain := relatesInSteps_histPackingDB (n := n) (N := N) (m := m) c₀ c
  have hz0 : (fun i : Fin n => if (i : ℕ) + 0 < m then c else c₀)
      = histPackingDB m c₀ c := by
    funext i
    simp only [histPackingDB, Nat.add_zero]
  have hzm : (fun i : Fin n => if (i : ℕ) + m < m then c else c₀)
      = histPackingDB m c₀ c₀ := by
    funext i
    simp only [histPackingDB]
    have hneg : ¬ ((i : ℕ) + m < m) := not_lt_of_ge (Nat.le_add_left m _)
    rw [ite_eq_right hneg]
    split_ifs with h <;> rfl
  rw [hz0, hzm] at hchain
  exact hchain

private theorem card_filter_lt_of_le {n m : ℕ} (hmn : m ≤ n) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) < m)).card = m := by
  have e : {i : Fin n // (i : ℕ) < m} ≃ Fin m :=
    { toFun := fun i => ⟨i.val, i.property⟩
      invFun := fun j => ⟨⟨j.val, lt_of_lt_of_le j.2 hmn⟩, j.2⟩
      left_inv := fun i => Subtype.ext (Fin.ext rfl)
      right_inv := fun j => Fin.ext rfl }
  have hcard : Fintype.card {i : Fin n // (i : ℕ) < m} = m := by
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hsub : Fintype.card {i : Fin n // (i : ℕ) < m}
      = (Finset.univ.filter (fun i : Fin n => (i : ℕ) < m)).card := by
    have h := Fintype.card_ofFinset (p := {x : Fin n | (x : ℕ) < m})
      (Finset.univ.filter (fun i : Fin n => (i : ℕ) < m)) (fun x => by simp)
    exact h
  rw [hcard] at hsub
  exact hsub.symm

private theorem filter_packingDB_eq {n N m : ℕ} (c₀ c₁ c₂ : Fin N) :
    Finset.univ.filter (fun i : Fin n => histPackingDB m c₀ c₁ i = c₂)
      = Finset.univ.filter (fun i : Fin n => (i : ℕ) < m ∧ c₁ = c₂) ∪
        Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < m ∧ c₀ = c₂) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
  by_cases h : (i : ℕ) < m <;> simp [histPackingDB, h]

private theorem disjoint_filter_packingDB {n N m : ℕ} (c₀ c₁ c₂ : Fin N) :
    Disjoint (Finset.univ.filter (fun i : Fin n => (i : ℕ) < m ∧ c₁ = c₂))
      (Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < m ∧ c₀ = c₂)) := by
  rw [Finset.disjoint_left]
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact fun hcon => hcon.1 hi.1

private theorem card_filter_lt_and_eq {n N m : ℕ} (hmn : m ≤ n) (c₁ c₂ : Fin N) :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) < m ∧ c₁ = c₂)).card
      = if c₁ = c₂ then m else 0 := by
  by_cases h : c₁ = c₂
  · rw [ite_eq_left h]
    have heq : Finset.univ.filter (fun i : Fin n => (i : ℕ) < m ∧ c₁ = c₂)
        = Finset.univ.filter (fun i : Fin n => (i : ℕ) < m) := by
      ext i
      simp [h]
    rw [heq]
    exact card_filter_lt_of_le hmn
  · rw [ite_eq_right h]
    have hempty : Finset.univ.filter (fun i : Fin n => (i : ℕ) < m ∧ c₁ = c₂)
        = ∅ := by
      ext i
      simp [h]
    rw [hempty, Finset.card_empty]

private theorem histCount_packingDB_sub {n N m : ℕ} (hmn : m ≤ n) (c₀ c c' : Fin N)
    (hne : c ≠ c') :
    histCount (histPackingDB (n := n) m c₀ c) c
      = histCount (histPackingDB (n := n) m c₀ c') c + m := by
  unfold histCount
  rw [filter_packingDB_eq c₀ c c, filter_packingDB_eq c₀ c' c,
    Finset.card_union_of_disjoint (disjoint_filter_packingDB c₀ c c),
    Finset.card_union_of_disjoint (disjoint_filter_packingDB c₀ c' c),
    card_filter_lt_and_eq hmn c c, card_filter_lt_and_eq hmn c' c,
    ite_eq_left rfl, ite_eq_right (Ne.symm hne)]
  omega

theorem histAccurate_pairwise_disjoint {n N : ℕ} {m : ℕ} {α : ℝ} (hmn : m ≤ n) (hα : 2 * α < (m : ℝ)) (c₀ : Fin N) : Pairwise (fun c c' => Disjoint (histAccurate α (histPackingDB (n := n) m c₀ c)) (histAccurate α (histPackingDB (n := n) m c₀ c'))) := by
  intro c c' hne
  rw [Set.disjoint_left]
  intro v hvc hvc'
  simp only [histAccurate, Set.mem_ofPred_eq] at hvc hvc'
  have h1 := hvc c
  have h2 := hvc' c
  have hcount := histCount_packingDB_sub hmn c₀ c c' hne
  have htri : |(histCount (histPackingDB (n := n) m c₀ c) c : ℝ) -
      (histCount (histPackingDB (n := n) m c₀ c') c : ℝ)| ≤ 2 * α := by
    have hcalc : |(histCount (histPackingDB (n := n) m c₀ c) c : ℝ) -
          (histCount (histPackingDB (n := n) m c₀ c') c : ℝ)|
        = |((histCount (histPackingDB (n := n) m c₀ c) c : ℝ) - v c) +
          (v c - (histCount (histPackingDB (n := n) m c₀ c') c : ℝ))| := by
      congr 1
      ring
    rw [hcalc]
    calc |((histCount (histPackingDB (n := n) m c₀ c) c : ℝ) - v c) +
            (v c - (histCount (histPackingDB (n := n) m c₀ c') c : ℝ))|
          ≤ |(histCount (histPackingDB (n := n) m c₀ c) c : ℝ) - v c| +
            |v c - (histCount (histPackingDB (n := n) m c₀ c') c : ℝ)| :=
            abs_add_le _ _
      _ = |v c - (histCount (histPackingDB (n := n) m c₀ c) c : ℝ)| +
            |v c - (histCount (histPackingDB (n := n) m c₀ c') c : ℝ)| := by
            rw [abs_sub_comm]
      _ ≤ α + α := add_le_add h1 h2
      _ = 2 * α := by ring
  rw [hcount] at htri
  push_cast at htri
  have hmeq : (histCount (histPackingDB (n := n) m c₀ c') c : ℝ) + (m : ℝ) -
      (histCount (histPackingDB (n := n) m c₀ c') c : ℝ) = (m : ℝ) := by ring
  rw [hmeq, abs_of_nonneg (Nat.cast_nonneg m)] at htri
  linarith [hα, htri]

theorem histogram_packing_lower_bound {n N : ℕ} (c₀ : Fin N) {M : (Fin n → Fin N) → PMF (Fin N → ℝ)} {ε p α : ℝ} {m : ℕ} (hmn : m ≤ n) (hα : 2 * α < (m : ℝ)) (hM : IsDP M ReplaceOne ε) (hprob : ∀ d : Fin n → Fin N, p ≤ ((M d).toOuterMeasure (histAccurate α d)).toReal) : (N : ℝ) * p ≤ Real.exp ((m : ℝ) * ε) := by
  have hbase := packing_lower_bound_pure (I := Fin N) hM (histPackingDB m c₀ c₀)
    (fun c => histPackingDB m c₀ c)
    (fun c => histAccurate α (histPackingDB (n := n) m c₀ c))
    (fun c => ⟨m, le_rfl, histPackingDB_replaceOneChain hmn c₀ c⟩)
    (histAccurate_pairwise_disjoint hmn hα c₀)
    (fun c => hprob _)
  rwa [Fintype.card_fin] at hbase

theorem histogram_sample_complexity_lower_bound {n N : ℕ} (c₀ : Fin N) {M : (Fin n → Fin N) → PMF (Fin N → ℝ)} {ε p α : ℝ} (hα : 2 * α < (n : ℝ)) (hM : IsDP M ReplaceOne ε) (hprob : ∀ d : Fin n → Fin N, p ≤ ((M d).toOuterMeasure (histAccurate α d)).toReal) (hp : 0 < p) (hε : 0 < ε) : Real.log ((N : ℝ) * p) / ε ≤ (n : ℝ) := by
  have hbase : (N : ℝ) * p ≤ Real.exp ((n : ℝ) * ε) :=
    histogram_packing_lower_bound (m := n) c₀ le_rfl hα hM hprob
  have hpos : 0 < (N : ℝ) * p := mul_pos (Nat.cast_pos.mpr c₀.pos) hp
  have hlog : Real.log ((N : ℝ) * p) ≤ (n : ℝ) * ε := by
    calc Real.log ((N : ℝ) * p)
        ≤ Real.log (Real.exp ((n : ℝ) * ε)) := Real.log_le_log hpos hbase
      _ = (n : ℝ) * ε := Real.log_exp _
  rw [div_le_iff₀ hε]
  exact hlog

theorem histogram_error_lower_bound {n N : ℕ} (c₀ : Fin N) {M : (Fin n → Fin N) → PMF (Fin N → ℝ)} {ε p α : ℝ} (hα0 : 0 ≤ α) (hmn : ⌊2 * α⌋₊ + 1 ≤ n) (hM : IsDP M ReplaceOne ε) (hprob : ∀ d : Fin n → Fin N, p ≤ ((M d).toOuterMeasure (histAccurate α d)).toReal) (hp : 0 < p) (hε : 0 < ε) : (Real.log ((N : ℝ) * p) / ε - 1) / 2 ≤ α := by
  have h2α : (2 : ℝ) * α < ((⌊2 * α⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_floor_add_one (2 * α)
  have hbase : (N : ℝ) * p ≤ Real.exp (((⌊2 * α⌋₊ + 1 : ℕ) : ℝ) * ε) :=
    histogram_packing_lower_bound (m := ⌊2 * α⌋₊ + 1) c₀ hmn h2α hM hprob
  have hpos : 0 < (N : ℝ) * p := mul_pos (Nat.cast_pos.mpr c₀.pos) hp
  have hlog : Real.log ((N : ℝ) * p) ≤ ((⌊2 * α⌋₊ + 1 : ℕ) : ℝ) * ε := by
    calc Real.log ((N : ℝ) * p)
        ≤ Real.log (Real.exp (((⌊2 * α⌋₊ + 1 : ℕ) : ℝ) * ε)) :=
          Real.log_le_log hpos hbase
      _ = ((⌊2 * α⌋₊ + 1 : ℕ) : ℝ) * ε := Real.log_exp _
  have hdiv : Real.log ((N : ℝ) * p) / ε ≤ ((⌊2 * α⌋₊ + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hε]
    exact hlog
  have hfloor : (⌊2 * α⌋₊ : ℝ) ≤ 2 * α := Nat.floor_le (by positivity)
  have hcast : ((⌊2 * α⌋₊ + 1 : ℕ) : ℝ) = (⌊2 * α⌋₊ : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hcast] at hdiv
  linarith [hdiv, hfloor]

theorem histogram_freq_error_lower_bound {n N : ℕ} (c₀ : Fin N) {M : (Fin n → Fin N) → PMF (Fin N → ℝ)} {ε p α : ℝ} (hn : 0 < n) (hα0 : 0 ≤ α) (hα1 : α < 1 / 2) (hM : IsDP M ReplaceOne ε) (hprob : ∀ d : Fin n → Fin N, p ≤ ((M d).toOuterMeasure {v : Fin N → ℝ | ∀ c : Fin N, |v c - histFreq d c| ≤ α}).toReal) (hp : 0 < p) (hε : 0 < ε) : (Real.log ((N : ℝ) * p) / ε - 1) / (2 * (n : ℝ)) ≤ α := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hM' : IsDP (postProcess (fun v c => (n : ℝ) * v c) M) ReplaceOne ε :=
    isDP_postProcess hM _
  have hprob' : ∀ d : Fin n → Fin N,
      p ≤ (((postProcess (fun v c => (n : ℝ) * v c) M) d).toOuterMeasure
        (histAccurate (α * (n : ℝ)) d)).toReal := by
    intro d
    have hsub : {v : Fin N → ℝ | ∀ c : Fin N, |v c - histFreq d c| ≤ α} ⊆
        (fun v c => (n : ℝ) * v c) ⁻¹' histAccurate (α * (n : ℝ)) d := by
      intro v hv
      simp only [Set.mem_preimage, histAccurate, Set.mem_ofPred_eq] at ⊢
      simp only [Set.mem_ofPred_eq] at hv
      intro c
      have hc := hv c
      have hfreq : histFreq d c = (histCount d c : ℝ) / (n : ℝ) := rfl
      rw [hfreq] at hc
      have habs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg hnpos.le
      calc |(n : ℝ) * v c - (histCount d c : ℝ)|
          = |(n : ℝ)| * |v c - (histCount d c : ℝ) / (n : ℝ)| := by
            rw [← abs_mul]
            congr 1
            field_simp
        _ = (n : ℝ) * |v c - (histCount d c : ℝ) / (n : ℝ)| := by rw [habs]
        _ ≤ (n : ℝ) * α := mul_le_mul_of_nonneg_left hc hnpos.le
        _ = α * (n : ℝ) := mul_comm _ _
    have hmap : (((postProcess (fun v c => (n : ℝ) * v c) M) d).toOuterMeasure
        (histAccurate (α * (n : ℝ)) d)) =
        ((M d).toOuterMeasure
          ((fun v c => (n : ℝ) * v c) ⁻¹' histAccurate (α * (n : ℝ)) d)) := by
      show ((M d).map _).toOuterMeasure _ = _
      exact PMF.toOuterMeasure_map_apply _ _ _
    rw [hmap]
    have hmono := toOuterMeasure_mono (M d) hsub
    have hfin : (M d).toOuterMeasure
        ((fun v c => (n : ℝ) * v c) ⁻¹' histAccurate (α * (n : ℝ)) d) ≠ ⊤ :=
      toOuterMeasure_ne_top _ _
    have hfinS : (M d).toOuterMeasure
        {v : Fin N → ℝ | ∀ c : Fin N, |v c - histFreq d c| ≤ α} ≠ ⊤ :=
      toOuterMeasure_ne_top _ _
    have hle := (ENNReal.toReal_le_toReal hfinS hfin).mpr hmono
    exact (hprob d).trans hle
  have h2αn : 2 * (α * (n : ℝ)) < (n : ℝ) := by
    have h2α : 2 * α < 1 := by linarith [hα1]
    calc 2 * (α * (n : ℝ)) = (2 * α) * (n : ℝ) := by ring
      _ < 1 * (n : ℝ) := mul_lt_mul_of_pos_right h2α hnpos
      _ = (n : ℝ) := one_mul _
  have hfloorlt : ⌊2 * (α * (n : ℝ))⌋₊ < n := by
    have hfle : (⌊2 * (α * (n : ℝ))⌋₊ : ℝ) ≤ 2 * (α * (n : ℝ)) :=
      Nat.floor_le (by positivity)
    have hlt : (⌊2 * (α * (n : ℝ))⌋₊ : ℝ) < (n : ℝ) := lt_of_le_of_lt hfle h2αn
    exact_mod_cast hlt
  have hmn' : ⌊2 * (α * (n : ℝ))⌋₊ + 1 ≤ n := hfloorlt
  have hαn0 : 0 ≤ α * (n : ℝ) := mul_nonneg hα0 (Nat.cast_nonneg n)
  have hbase := histogram_error_lower_bound (α := α * (n : ℝ)) c₀ hαn0 hmn' hM'
    hprob' hp hε
  have h2npos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  rw [div_le_iff₀ h2npos]
  have hbase' : Real.log ((N : ℝ) * p) / ε - 1 ≤ 2 * (α * (n : ℝ)) := by
    have h := (div_le_iff₀ (two_pos)).mp hbase
    linarith [h]
  linarith [hbase']

end CSLibExt.Privacy.DifferentialPrivacy
