/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianBoundary

/-!
# Rational Eulerian Hochschild chain maps

Over a ground ring containing ℚ, the coefficient Eulerian
operators commute with the Hochschild boundary. Their chain
maps retain finite support, orthogonality and completeness.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The original rational Eulerian projector is a native Hochschild chain map. -/
def eulerianChainMap (i : ℕ) : chainComplex k A M ⟶ chainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (coefficientEulerianOperator k A M n i)) (by
    intro n
    apply ModuleCat.hom_ext
    exact coefficientEulerian_boundary k A M n i)

/-- The original coefficient-fixed Eulerian operator is retained in every degree. -/
theorem eulerianChainMap_f (n i : ℕ) :
    ((eulerianChainMap k A M i).f n).hom = coefficientEulerianOperator k A M n i := rfl

/-- The coefficient projectors are orthogonal idempotents as native chain maps. -/
theorem eulerianChainMap_comp (i j : ℕ) :
    eulerianChainMap k A M i ≫ eulerianChainMap k A M j =
      if i = j then eulerianChainMap k A M i else 0 := by
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl]
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (coefficientEulerianOperator k A M n i).comp (coefficientEulerianOperator k A M n i) =
      coefficientEulerianOperator k A M n i
    simpa only [ite_eq_left rfl, ite_true] using (coefficientEulerian_projector_laws k A M n).2 i i
  · rw [ite_eq_right h]
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (coefficientEulerianOperator k A M n j).comp (coefficientEulerianOperator k A M n i) = 0
    simpa only [ite_eq_right (Ne.symm h)] using (coefficientEulerian_projector_laws k A M n).2 j i

/-- Actual finite support is the original tensor-degree support, not a global truncation. -/
theorem eulerianChainMap_support (n i : ℕ) (h : n < i) : (eulerianChainMap k A M i).f n = 0 := by
  apply ModuleCat.hom_ext
  rw [eulerianChainMap_f, coefficientEulerian_outside k A M n i h]
  rfl

/-- Finite completeness in each original degree gives the identity component. -/
theorem eulerianChainMap_sum (n : ℕ) :
    (∑ i : Fin (n + 1), (eulerianChainMap k A M i.val).f n) = 𝟙 ((chainComplex k A M).X n) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_id, eulerianChainMap_f]
  change (∑ i : Fin (n + 1), coefficientEulerianOperator k A M n i.val) = LinearMap.id
  exact (coefficientEulerian_projector_laws k A M n).1

end ModuleCat.Algebra.Hochschild.Symmetric
