/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.DeficiencyOne
import MathlibExt.Biology.Dynamics.DeficiencyZero.Integration

/-! Tests for the linkage-class decomposition behind the deficiency-one theorem.

* **Boundary.** The network `A → B`, `2B → 2A` has two linkage classes, each of deficiency
  zero, and deficiency one, so `∑_θ δ_θ < δ`. Computed directly from the definitions, the
  concentrations `x = (1, 1)` with rate constants `k = (2, 1)` are an equilibrium while the
  field of the linkage class of `A → B` is `(-2, 2) ≠ 0`, so the equilibrium equations do not
  decouple. Consequently `∑_θ δ_θ ≠ δ` for this network.
* **Non-vacuity.** The network `A ⇌ B`, `C ⇌ D` has deficiency zero (from the linear form
  through `deficiency_eq_zero_iff`), so `∑_θ δ_θ = δ` and every `δ_θ = 0`; at its equilibrium
  `x = (1, 2, 1, 1)` with `k = (2, 1, 1, 1)` both linkage-class fields vanish. -/

namespace MathlibExtTest.Biology.Dynamics.DeficiencyOne

open MathlibExt.Biology.Dynamics.ComplexBalanced ReactionNetwork

/-! ### Boundary: `A → B`, `2B → 2A` -/

/-- The network `A → B`, `2B → 2A` on species `Fin 2` (`0 = A`, `1 = B`). -/
def twoClass : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![1, 0], ![0, 2]]
  prod := ![![0, 1], ![2, 0]]

/-- The two reactions lie in different linkage classes: every reaction preserves the total
molecularity `y A + y B`, which is `1` at `A` and `2` at `2B`. -/
theorem twoClass_linkageClassOf_ne : twoClass.linkageClassOf 1 ≠ twoClass.linkageClassOf 0 := by
  intro h
  have hreach := SimpleGraph.ConnectedComponent.eq.1 h
  have := reachable_imp_iff_of_reacts (fun y : Fin 2 → ℕ => y 0 + y 1 = 1) (fun y y' hyy' => by
    obtain ⟨r, rfl, rfl⟩ := hyy'
    fin_cases r <;> simp [twoClass]) hreach
  simp [twoClass] at this

open Classical in
theorem twoClass_filter :
    Finset.univ.filter (fun r => twoClass.linkageClassOf r = twoClass.linkageClassOf 0) = {0} := by
  ext r
  fin_cases r
  · simp
  · simp [twoClass_linkageClassOf_ne]

/-- `x = (1, 1)` is an equilibrium for `k = (2, 1)`: `2 (-1, 1) + 1 (2, -2) = 0`. -/
theorem twoClass_equilibrium : twoClass.massActionField ![2, 1] ![1, 1] = 0 := by
  funext s
  fin_cases s <;> simp [massActionField, twoClass, Fin.sum_univ_two]

/-- The field of the linkage class of `A → B` at `x = (1, 1)` is `(-2, 2)`, nonzero. -/
theorem twoClass_linkageClassField_ne_zero :
    twoClass.linkageClassField (twoClass.linkageClassOf 0) ![2, 1] ![1, 1] ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [linkageClassField] at h0
  rw [twoClass_filter] at h0
  simp [twoClass, Fin.prod_univ_two] at h0

/-- **Boundary.** Without `∑_θ δ_θ = δ` the equilibrium equations need not decouple. -/
theorem twoClass_not_decouple : ¬ (twoClass.massActionField ![2, 1] ![1, 1] = 0 ↔
    ∀ θ, twoClass.linkageClassField θ ![2, 1] ![1, 1] = 0) :=
  fun h => twoClass_linkageClassField_ne_zero (h.1 twoClass_equilibrium _)

/-- Consequently `A → B`, `2B → 2A` violates hypothesis 2 of the deficiency-one theorem. -/
example [Fintype twoClass.linkageGraph.ConnectedComponent] :
    ∑ θ, twoClass.linkageClassDeficiency θ ≠ twoClass.deficiency := fun h =>
  twoClass_not_decouple (massActionField_eq_zero_iff_of_sum_linkageClassDeficiency_eq h)

example [Fintype twoClass.linkageGraph.ConnectedComponent] :
    ∑ θ, twoClass.linkageClassDeficiency θ < twoClass.deficiency := by
  refine lt_of_le_of_ne sum_linkageClassDeficiency_le fun h => twoClass_not_decouple ?_
  exact massActionField_eq_zero_iff_of_sum_linkageClassDeficiency_eq h

/-! ### Non-vacuity: `A ⇌ B`, `C ⇌ D` -/

/-- The network `A ⇌ B`, `C ⇌ D` on species `Fin 4` (`0 = A`, `1 = B`, `2 = C`, `3 = D`). -/
def twoIso : ReactionNetwork (Fin 4) (Fin 4) where
  src := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]
  prod := ![![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]]

/-- `A ⇌ B`, `C ⇌ D` has deficiency zero, from the linear form `ker Y ∩ im ∂ = 0`. -/
theorem twoIso_deficiency : twoIso.deficiency = 0 := by
  refine twoIso.deficiency_eq_zero_iff.2 fun α hα η => ?_
  have h0 := congrFun hα 0
  have h2 := congrFun hα 2
  simp [twoIso, Fin.sum_univ_four] at h0 h2
  have h1 : α 1 = α 0 := by linarith
  have h3 : α 3 = α 2 := by linarith
  simp [twoIso, Fin.sum_univ_four, h1, h3]
  ring

example [Fintype twoIso.linkageGraph.ConnectedComponent] :
    ∑ θ, twoIso.linkageClassDeficiency θ = twoIso.deficiency :=
  sum_linkageClassDeficiency_eq_of_deficiency_eq_zero twoIso_deficiency

example (θ : twoIso.linkageGraph.ConnectedComponent) : twoIso.linkageClassDeficiency θ = 0 :=
  linkageClassDeficiency_eq_zero_of_deficiency_eq_zero twoIso_deficiency θ

/-- `x = (1, 2, 1, 1)` is an equilibrium for `k = (2, 1, 1, 1)`. -/
theorem twoIso_equilibrium : twoIso.massActionField ![2, 1, 1, 1] ![1, 2, 1, 1] = 0 := by
  funext s
  fin_cases s <;> simp [massActionField, twoIso, Fin.sum_univ_four, Fin.prod_univ_four]

/-- **Non-vacuity.** The decoupling theorem applies to `A ⇌ B`, `C ⇌ D`: at its equilibrium
every linkage-class field vanishes. -/
example [Fintype twoIso.linkageGraph.ConnectedComponent]
    (θ : twoIso.linkageGraph.ConnectedComponent) :
    twoIso.linkageClassField θ ![2, 1, 1, 1] ![1, 2, 1, 1] = 0 :=
  (massActionField_eq_zero_iff_of_sum_linkageClassDeficiency_eq
    (sum_linkageClassDeficiency_eq_of_deficiency_eq_zero twoIso_deficiency)).1
    twoIso_equilibrium θ

#print axioms ReactionNetwork.stoichiometricSubspace_eq_iSup
#print axioms ReactionNetwork.linkageClassDeficiency_nonneg
#print axioms ReactionNetwork.deficiency_sub_sum_linkageClassDeficiency
#print axioms ReactionNetwork.sum_linkageClassDeficiency_le
#print axioms ReactionNetwork.sum_linkageClassDeficiency_eq_iff
#print axioms ReactionNetwork.linkageClassDeficiency_eq_zero_of_deficiency_eq_zero
#print axioms ReactionNetwork.sum_linkageClassDeficiency_eq_of_deficiency_eq_zero
#print axioms ReactionNetwork.sum_linkageClassField
#print axioms ReactionNetwork.linkageClassField_mem
#print axioms ReactionNetwork.massActionField_eq_zero_iff_of_iSupIndep
#print axioms ReactionNetwork.massActionField_eq_zero_iff_of_sum_linkageClassDeficiency_eq
#print axioms twoClass_not_decouple

end MathlibExtTest.Biology.Dynamics.DeficiencyOne
