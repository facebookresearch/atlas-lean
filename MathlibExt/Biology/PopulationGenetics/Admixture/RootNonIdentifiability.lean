/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.TreeFStatistics
import MathlibExt.Biology.PopulationGenetics.Admixture.TreeAdditivity
import MathlibExt.Biology.PopulationGenetics.Admixture.ConditionalNegDef

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
same weight for every population (on a rooted tree, an edge of the root stem
above the most recent common ancestor of all sampled populations), then for
every nonnegative `t ≠ len e0` there is a realized drift model with the same
weights, with length `t` at `e0`, hence with a different length vector, but
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
edges `a`, `b` followed by drift on `c` as in `f2_admixedBranch`, their
lengths agree off `{a, b, c}`, and their mixed drifts
`α² ℓa + (1-α)² ℓb + ℓc` agree, then `f2 Mx X` agrees for every reference
`X` off those edges. Hence the three lengths are not separately identifiable
from such `f2` statistics, only the combination `mixedDrift` is. -/
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

end MathlibExt.Biology.PopulationGenetics.TreeFStatistics
