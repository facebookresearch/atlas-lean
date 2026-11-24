/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPositiveAlgebra

/-!
# Algebra-linear symmetric Hochschild complexes

The coefficient-head A-action makes the raw symmetric
Hochschild boundary A-linear. Proper both-positive shuffle
relations form a subcomplex, and their quotient projection
is an A-linear chain map. Tensor tails remain over k.
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

/-- The original proper relation module vanishes in exactly the two original low chain degrees. -/
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

/-- The original raw boundary as an morphism of algebra modules. -/
def algebraRawDifferential (n : ℕ) :
    ModuleCat.of A (M ⊗[k] TensorPower k (n + 1) A) ⟶
      ModuleCat.of A (M ⊗[k] TensorPower k n A) :=
  ModuleCat.ofHom (algebraBoundary k A M n)

/-- The original algebra-linear raw boundary squares to zero by the original k-complex law. -/
theorem algebraRawDifferential_comp (n : ℕ) :
    algebraRawDifferential k A M (n + 1) ≫ algebraRawDifferential k A M n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom ((chainComplex k A M).d_comp_d (n + 2) (n + 1) n) x

/-- The raw symmetric Hochschild complex with its original algebra action. -/
def algebraRawComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (M ⊗[k] TensorPower k n A))
    (algebraRawDifferential k A M) (algebraRawDifferential_comp k A M)

/-- Restriction of the original boundary to the proper relation modules. -/
def algebraPositiveRelationDifferential (n : ℕ) :
    ModuleCat.of A (algebraPositiveRelations k A M (n + 1)) ⟶
      ModuleCat.of A (algebraPositiveRelations k A M n) :=
  ModuleCat.ofHom
    (((algebraBoundary k A M n).comp (algebraPositiveRelations k A M (n + 1)).subtype).codRestrict
      (algebraPositiveRelations k A M n)
      (fun x => algebraPositiveRelations_boundary k A M n x.property))

/-- The restricted relation boundary squares to zero by its original ambient differential. -/
theorem algebraPositiveRelationDifferential_comp (n : ℕ) :
    algebraPositiveRelationDifferential k A M (n + 1) ≫
      algebraPositiveRelationDifferential k A M n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom ((chainComplex k A M).d_comp_d (n + 2) (n + 1) n) x.val

/-- The proper relation subcomplex with its original A-module structure. -/
def algebraPositiveRelationComplex : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of A (algebraPositiveRelations k A M n))
    (algebraPositiveRelationDifferential k A M) (algebraPositiveRelationDifferential_comp k A M)

/-- The algebra-linear proper relation inclusion, with native subtype components. -/
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

/-- The original algebra-linear raw complex projects through its proper quotient classes. -/
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

/-- The relation inclusion is killed by the original algebra-linear quotient projection. -/
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
