/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.TreeFStatistics
import Domains.Biology.PopulationGenetics.Admixture.TreeAdditivity
import Domains.Biology.PopulationGenetics.Admixture.ConditionalNegDef

/-!
# Non-identifiability of root-stem and admixture-adjacent lengths

F-statistics in a drift model depend on lineage weights and edge lengths only
through the products `(w X e - w Y e)^2 * len e` and their bilinear forms.
An edge carried with the same weight by every population therefore contributes
nothing: its length can be changed in a realized model with the same weights
without changing any `f4`. At an admixed branch, the three adjacent lengths
enter `f2` from the admixed population only through the mixed drift
`α² ℓa + (1 - α)² ℓb + ℓc`, so they are not separately identifiable from those
statistics.

## Main results

* `FStatistics.DriftModel.exists_len_ne_f4_eq_of_weight_const`: a root-stem
  length can be replaced by any other nonnegative value in a realized drift
  model with the same weights and every `f4` unchanged.
* `TreeFStatistics.f2_eq_of_mixedDrift_eq`: two models with the same weights,
  lengths agreeing off the admixture-adjacent edges, and equal mixed drift
  give the same `f2` from the admixed population to references off those edges.

## References

* N. Patterson et al., *Ancient admixture in human history*, Genetics 192
  (2012), 1065–1093.
* M. Lipson et al., *Efficient moment-based inference of admixture parameters
  and sources of gene flow*, Molecular Biology and Evolution 30 (2013),
  1788–1802.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.TreeFStatistics
open scoped symmDiff

universe u

namespace MathlibExt.Biology.PopulationGenetics.FStatistics

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- Root-stem non-identifiability, existence form: if an edge `e0` has the
same weight for every population (for example, on a rooted tree, an edge of
the root stem above the most recent common ancestor of all sampled
populations), then for every nonnegative `t ≠ len e0` there is a drift model
on a probability space with the same weights, with length `t` at `e0`, hence
with a different length vector, but
with every `f4` (hence every `f2` and `f3`) unchanged. So root-stem lengths
are not identifiable from f-statistics. This is the existential form of
`DriftModel.f4_eq_of_len_eq_of_weight_const`, realized by
`Admixture.exists_driftModel`. -/
theorem DriftModel.exists_len_ne_f4_eq_of_weight_const {E P : Type u} [Fintype E]
    (M : DriftModel μ E P) {e0 : E} (hconst : ∀ X Y, M.weight X e0 = M.weight Y e0)
    {t : ℝ} (ht : 0 ≤ t) (hne : t ≠ M.len e0) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (_ : IsProbabilityMeasure μ')
      (M' : DriftModel μ' E P), M'.weight = M.weight ∧ M'.len e0 = t ∧ M'.len ≠ M.len ∧
        ∀ A B C D, f4 μ' M'.freq A B C D = f4 μ M.freq A B C D := by
  classical
  obtain ⟨Ω', hΩ', μ', hμ', M', hw, hl⟩ :=
    MathlibExt.Biology.PopulationGenetics.Admixture.exists_driftModel M.weight
      (Function.update M.len e0 t) (by
        intro e
        by_cases he : e = e0
        · simp [Function.update, he, ht]
        · simp [Function.update, he, M.len_nonneg e])
  refine ⟨Ω', hΩ', μ', hμ', M', hw, by rw [hl]; exact Function.update_self e0 t M.len, ?_,
    fun A B C D => ?_⟩
  · intro hcon
    apply hne
    have := congrFun hcon e0
    rw [hl] at this
    exact (Function.update_self e0 t M.len).symm.trans this
  · refine DriftModel.f4_eq_of_len_eq_of_weight_const M M' hw (fun e he => ?_) A B C D
    by_cases he0 : e = e0
    · subst he0
      exact hconst
    · exfalso
      apply he
      rw [hl]
      simp [Function.update, he0]

end MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics.TreeFStatistics

variable {Ω Ω' P E : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {μ' : Measure Ω'} [Fintype E] (M : DriftModel μ E P)

/-- Admixture-adjacent lengths enter `f2` only through the mixed drift: if
two drift models have the same weights, `Mx` admixed from the endpoints of
distinct edges `a`, `b` followed by drift on `c` as in `f2_admixedBranch`
(with `A` and `B` of weight `0` on `a`, `b`, `c`), their lengths agree off
`{a, b, c}`, and their mixed drifts `α² ℓa + (1-α)² ℓb + ℓc` agree, then
`f2 Mx X` agrees for every reference `X` off those edges. Hence these `f2`
statistics do not separate the three lengths: they see them only through
the combination `mixedDrift`. -/
theorem f2_eq_of_mixedDrift_eq [DecidableEq E] (M' : DriftModel μ' E P) {Mx A B X : P}
    {a b c : E} {α : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hwM : M.weight Mx = α • (M.weight A + Pi.single a 1) +
      (1 - α) • (M.weight B + Pi.single b 1) + Pi.single c 1)
    (hw : M'.weight = M.weight)
    (hlen : ∀ e, e ∉ ({a, b, c} : Finset E) → M'.len e = M.len e)
    (hmix : mixedDrift α (M'.len a) (M'.len b) (M'.len c) =
      mixedDrift α (M.len a) (M.len b) (M.len c))
    (hA : ∀ e ∈ ({a, b, c} : Finset E), M.weight A e = 0)
    (hB : ∀ e ∈ ({a, b, c} : Finset E), M.weight B e = 0)
    (hX : ∀ e ∈ ({a, b, c} : Finset E), M.weight X e = 0) :
    f2 μ' M'.freq Mx X = f2 μ M.freq Mx X := by
  have hwM' : M'.weight Mx = α • (M'.weight A + Pi.single a 1) +
      (1 - α) • (M'.weight B + Pi.single b 1) + Pi.single c 1 := by
    rw [hw]
    exact hwM
  have key : ∀ Y Z : P, (∀ e ∈ ({a, b, c} : Finset E), M.weight Y e = 0) →
      (∀ e ∈ ({a, b, c} : Finset E), M.weight Z e = 0) →
      f2 μ' M'.freq Y Z = f2 μ M.freq Y Z := by
    intro Y Z hY hZ
    rw [M'.f2_freq, M.f2_freq, hw]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : e ∈ ({a, b, c} : Finset E)
    · rw [hY e he, hZ e he]
      norm_num
    · rw [hlen e he]
  rw [f2_admixedBranch M' hab hac hbc hwM' (fun e he => by rw [hw]; exact hA e he)
      (fun e he => by rw [hw]; exact hB e he) (fun e he => by rw [hw]; exact hX e he),
    f2_admixedBranch M hab hac hbc hwM hA hB hX, key A X hA hX, key B X hB hX, key A B hA hB,
    hmix]

/-- The level set of the mixed drift is an explicit two-dimensional family: a triple
`(la', lb', lc')` has the same mixed drift as `(la, lb, lc)` exactly when
`lc' = lc - α² (la' - la) - (1 - α)² (lb' - lb)`, with `la'`, `lb'` free. -/
theorem mixedDrift_eq_mixedDrift_iff (α la lb lc la' lb' lc' : ℝ) :
    mixedDrift α la' lb' lc' = mixedDrift α la lb lc ↔
      lc' = lc - α ^ 2 * (la' - la) - (1 - α) ^ 2 * (lb' - lb) := by
  unfold mixedDrift
  constructor <;> intro h <;> linarith

variable {Ω Ω' P E : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {μ' : Measure Ω'} [Fintype E]

/-- Equal mixed drift gives the same `f2` matrix: if two drift models have the same weights,
`Mx` is admixed as in `f2_admixedBranch`, `A`, `B` and every population other than `Mx` have
weight `0` on `a`, `b`, `c`, the lengths agree off `{a, b, c}` and the mixed drifts agree, then
`f2` agrees at every pair of populations. -/
theorem f2_eq_of_mixedDrift_eq_of_forall_ne [DecidableEq E] (M : DriftModel μ E P)
    (M' : DriftModel μ' E P) {Mx A B : P} {a b c : E} {α : ℝ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c)
    (hwM : M.weight Mx = α • (M.weight A + Pi.single a 1) +
      (1 - α) • (M.weight B + Pi.single b 1) + Pi.single c 1)
    (hw : M'.weight = M.weight)
    (hlen : ∀ e, e ∉ ({a, b, c} : Finset E) → M'.len e = M.len e)
    (hmix : mixedDrift α (M'.len a) (M'.len b) (M'.len c) =
      mixedDrift α (M.len a) (M.len b) (M.len c))
    (hA : ∀ e ∈ ({a, b, c} : Finset E), M.weight A e = 0)
    (hB : ∀ e ∈ ({a, b, c} : Finset E), M.weight B e = 0)
    (hrest : ∀ Y, Y ≠ Mx → ∀ e ∈ ({a, b, c} : Finset E), M.weight Y e = 0) (Y Z : P) :
    f2 μ' M'.freq Y Z = f2 μ M.freq Y Z := by
  by_cases hY : Y = Mx <;> by_cases hZ : Z = Mx
  · rw [hY, hZ, f2_self, f2_self]
  · rw [hY]
    exact f2_eq_of_mixedDrift_eq M M' hab hac hbc hwM hw hlen hmix hA hB (hrest Z hZ)
  · rw [hZ, f2_comm Y Mx, f2_comm Y Mx]
    exact f2_eq_of_mixedDrift_eq M M' hab hac hbc hwM hw hlen hmix hA hB (hrest Y hY)
  · rw [M'.f2_freq, M.f2_freq, hw]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : e ∈ ({a, b, c} : Finset E)
    · rw [hrest Y hY e he, hrest Z hZ e he]
      simp
    · rw [hlen e he]

/-- Equal mixed drift gives the same `f4` at every quadruple. Let two drift models have the same
weights `w`, let `a`, `b`, `c` be three distinct edges and `α` a real number with
`w Mx = α (w A + 1_a) + (1 - α) (w B + 1_b) + 1_c`, where `1_e` is the indicator of edge `e`,
and let `A`, `B` and every population other than `Mx` have weight `0` on `a`, `b`, `c`. If the
lengths agree off `{a, b, c}` and the two models have the same mixed drift
`α² ℓ_a + (1 - α)² ℓ_b + ℓ_c`, then every `f4` (hence every `f2` and `f3`) agrees. -/
theorem f4_eq_of_mixedDrift_eq_of_forall_ne [DecidableEq E] (M : DriftModel μ E P)
    (M' : DriftModel μ' E P) {Mx A B : P} {a b c : E} {α : ℝ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c)
    (hwM : M.weight Mx = α • (M.weight A + Pi.single a 1) +
      (1 - α) • (M.weight B + Pi.single b 1) + Pi.single c 1)
    (hw : M'.weight = M.weight)
    (hlen : ∀ e, e ∉ ({a, b, c} : Finset E) → M'.len e = M.len e)
    (hmix : mixedDrift α (M'.len a) (M'.len b) (M'.len c) =
      mixedDrift α (M.len a) (M.len b) (M.len c))
    (hA : ∀ e ∈ ({a, b, c} : Finset E), M.weight A e = 0)
    (hB : ∀ e ∈ ({a, b, c} : Finset E), M.weight B e = 0)
    (hrest : ∀ Y, Y ≠ Mx → ∀ e ∈ ({a, b, c} : Finset E), M.weight Y e = 0) (W X Y Z : P) :
    f4 μ' M'.freq W X Y Z = f4 μ M.freq W X Y Z := by
  rw [f4_eq_f2 M'.memLp_freq, f4_eq_f2 M.memLp_freq]
  simp only [f2_eq_of_mixedDrift_eq_of_forall_ne M M' hab hac hbc hwM hw hlen hmix hA hB hrest]

/-- Realization of the constant-mixed-drift family: for every drift model in which `Mx` is
admixed as in `f2_admixedBranch` and is the only population using the admixture-adjacent
(distinct) edges `a`, `b`, `c`, and every member
`(ℓa + s, ℓb + t, ℓc - α² s - (1 - α)² t)` of the (algebraically two-dimensional)
constant-mixed-drift family with nonnegative entries, there is a drift model on a
probability space with the same weights, those three lengths, the same lengths elsewhere,
and the same `f4` at every quadruple. The terminal lengths are therefore non-identifiable
whenever a *distinct* admissible member exists; the admissible family can also collapse to
the original triple alone (e.g. `ℓa = ℓb = ℓc = 0` with `0 < α < 1` forces `s = t = 0`), in
which case this theorem only recovers the original model. -/
theorem exists_mixedDrift_family_f4_eq {E P : Type u} [Fintype E] [DecidableEq E]
    (M : DriftModel μ E P) {Mx A B : P} {a b c : E} {α : ℝ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c)
    (hwM : M.weight Mx = α • (M.weight A + Pi.single a 1) +
      (1 - α) • (M.weight B + Pi.single b 1) + Pi.single c 1)
    (hA : ∀ e ∈ ({a, b, c} : Finset E), M.weight A e = 0)
    (hB : ∀ e ∈ ({a, b, c} : Finset E), M.weight B e = 0)
    (hrest : ∀ Y, Y ≠ Mx → ∀ e ∈ ({a, b, c} : Finset E), M.weight Y e = 0)
    {s t : ℝ} (hs : 0 ≤ M.len a + s) (ht : 0 ≤ M.len b + t)
    (hc : 0 ≤ M.len c - α ^ 2 * s - (1 - α) ^ 2 * t) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (_ : IsProbabilityMeasure μ')
      (M' : DriftModel μ' E P), M'.weight = M.weight ∧ M'.len a = M.len a + s ∧
        M'.len b = M.len b + t ∧ M'.len c = M.len c - α ^ 2 * s - (1 - α) ^ 2 * t ∧
        (∀ e, e ∉ ({a, b, c} : Finset E) → M'.len e = M.len e) ∧
        ∀ W X Y Z, f4 μ' M'.freq W X Y Z = f4 μ M.freq W X Y Z := by
  set len' : E → ℝ := fun e => if e = a then M.len a + s else if e = b then M.len b + t
    else if e = c then M.len c - α ^ 2 * s - (1 - α) ^ 2 * t else M.len e with hlen'
  have hnn : ∀ e, 0 ≤ len' e := by
    intro e
    simp only [hlen']
    split_ifs
    · exact hs
    · exact ht
    · exact hc
    · exact M.len_nonneg e
  obtain ⟨Ω', hΩ', μ', hμ', M', hw, hl⟩ :=
    MathlibExt.Biology.PopulationGenetics.Admixture.exists_driftModel M.weight len' hnn
  have la' : M'.len a = M.len a + s := by rw [hl]; simp [hlen']
  have lb' : M'.len b = M.len b + t := by rw [hl]; simp [hlen', Ne.symm hab]
  have lc' : M'.len c = M.len c - α ^ 2 * s - (1 - α) ^ 2 * t := by
    rw [hl]; simp [hlen', Ne.symm hac, Ne.symm hbc]
  have lo : ∀ e, e ∉ ({a, b, c} : Finset E) → M'.len e = M.len e := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    rw [hl]
    simp [hlen', he.1, he.2.1, he.2.2]
  refine ⟨Ω', hΩ', μ', hμ', M', hw, la', lb', lc', lo, fun W X Y Z => ?_⟩
  exact f4_eq_of_mixedDrift_eq_of_forall_ne M M' hab hac hbc hwM hw lo
    (by rw [la', lb', lc']; unfold mixedDrift; ring) hA hB hrest W X Y Z

end MathlibExt.Biology.PopulationGenetics.TreeFStatistics
