/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPositiveAlgebra

/-!
# Algebra-linear Hochschild complexes and proper-shuffle relations

Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action. Multiplication on the coefficient makes the Hochschild differential A-linear while
the tensor tails remain over k. Images of shuffle pairings with both input degrees positive
form an A-linear subcomplex. The quotient projection is an A-linear chain map, and these
relation modules vanish in degrees zero and one.

For commutative Hochschild chains and proper Harrison shuffle relations, see J.-L. Loday,
Cyclic Homology, 2nd ed., §4.5.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) (A : Type v) (M : Type w) [CommRing k] [CommRing A]
  [Algebra k A] [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The proper-shuffle relation modules vanish in degrees zero and one.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
algebraPositiveRelations(n)=0 when n≤1, since no two positive shuffle degrees sum to n. -/
theorem algebraPositiveRelations_low (n : ℕ) (hn : n ≤ 1) : algebraPositiveRelations k A M n = ⊥ := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  apply le_antisymm ?_ bot_le
  intro x hx
  change x ∈ rawPositiveRelations k A M n at hx
  change x ∈ HomologicalComplex.ChainGradedPairing.positiveImages (pairing.{u, v, w} k A M) n at hx
  rcases (show n = 0 ∨ n = 1 by omega) with h0 | h1
  · subst n
    rw [HomologicalComplex.ChainGradedPairing.positiveImages_zero] at hx
    exact (Submodule.mem_bot (R := k)).mp hx
  · subst n
    rw [HomologicalComplex.ChainGradedPairing.positiveImages_one] at hx
    exact (Submodule.mem_bot (R := k)).mp hx

/-- The A-linear Hochschild differential on coefficient tensor chains.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, this is b : M
⊗[k] A⊗(n+1) → M ⊗[k] A⊗n, viewed as A-linear through multiplication on M. -/
def algebraRawDifferential (n : ℕ) :
    ModuleCat.of A (M ⊗[k] TensorPower k (n + 1) A) ⟶
      ModuleCat.of A (M ⊗[k] TensorPower k n A) :=
  ModuleCat.ofHom (algebraBoundary k A M n)

/-- Two successive algebra-linear Hochschild differentials compose to zero.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, bₙ₊₁ ≫ bₙ = 0
on the A-linear coefficient tensor complex. -/
theorem algebraRawDifferential_comp (n : ℕ) :
    algebraRawDifferential k A M (n + 1) ≫ algebraRawDifferential k A M n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom ((chainComplex k A M).d_comp_d (n + 2) (n + 1) n) x

/-- The algebra-linear symmetric Hochschild chain complex.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, its nth term
is M ⊗[k] A⊗n with the Hochschild differential and the A-action on the coefficient. -/
def algebraRawComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (M ⊗[k] TensorPower k n A))
    (algebraRawDifferential k A M) (algebraRawDifferential_comp k A M)

/-- The Hochschild differential restricted to proper-shuffle images.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, b restricts
from the relation module in degree n+1 to the relation module in degree n. -/
def algebraPositiveRelationDifferential (n : ℕ) :
    ModuleCat.of A (algebraPositiveRelations k A M (n + 1)) ⟶
      ModuleCat.of A (algebraPositiveRelations k A M n) :=
  ModuleCat.ofHom
    (((algebraBoundary k A M n).comp (algebraPositiveRelations k A M (n + 1)).subtype).codRestrict
      (algebraPositiveRelations k A M n)
      (fun x => algebraPositiveRelations_boundary k A M n x.property))

/-- The restricted proper-shuffle differential squares to zero.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, successive
restricted relation differentials compose to zero. -/
theorem algebraPositiveRelationDifferential_comp (n : ℕ) :
    algebraPositiveRelationDifferential k A M (n + 1) ≫
      algebraPositiveRelationDifferential k A M n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom ((chainComplex k A M).d_comp_d (n + 2) (n + 1) n) x.val

/-- The subcomplex of algebra-linear proper-shuffle relations.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, degree n is
algebraPositiveRelations(n), the A-submodule generated by both-positive shuffle images. -/
def algebraPositiveRelationComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (algebraPositiveRelations k A M n))
    (algebraPositiveRelationDifferential k A M) (algebraPositiveRelationDifferential_comp k A M)

/-- The inclusion of proper-shuffle relations into Hochschild chains.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the relation
subcomplex maps to algebraRawComplex through its degreewise submodule inclusions. -/
def algebraPositiveRelationInclusion :
    algebraPositiveRelationComplex k A M ⟶ algebraRawComplex k A M :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (algebraPositiveRelations k A M n).subtype) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      dsimp only [algebraRawComplex, algebraPositiveRelationComplex]
      rw [ChainComplex.of_d, ChainComplex.of_d]
      rfl)

/-- The A-linear projection to the proper-shuffle quotient complex.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, quotient each
raw Hochschild term by the both-positive shuffle relation submodule. -/
def algebraRawPositiveProjection :
    algebraRawComplex k A M ⟶ algebraPositiveQuotientComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraPositiveRelations k A M n).mkQ) (by
    intro n
    apply ModuleCat.hom_ext
    dsimp only [algebraRawComplex, algebraPositiveQuotientComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    exact Submodule.mapQ_mkQ (algebraPositiveRelations k A M (n + 1))
      (algebraPositiveRelations k A M n) (algebraBoundary k A M n)
      (h := algebraPositiveRelations_boundary k A M n))

/-- The relation inclusion followed by the proper quotient projection is zero.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
algebraPositiveRelationInclusion ≫ algebraRawPositiveProjection = 0 as chain maps. -/
@[reassoc]
theorem algebraPositiveRelationInclusion_projection :
    algebraPositiveRelationInclusion k A M ≫ algebraRawPositiveProjection k A M = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, HomologicalComplex.zero_f,
    ModuleCat.hom_zero, LinearMap.zero_apply]
  change (algebraPositiveRelations k A M n).mkQ x.val = 0
  change x.val ∈ LinearMap.ker (algebraPositiveRelations k A M n).mkQ
  simpa only [Submodule.ker_mkQ] using x.property

end ModuleCat.Algebra.Hochschild.Symmetric
