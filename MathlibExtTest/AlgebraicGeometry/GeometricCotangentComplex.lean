/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

set_option autoImplicit false

/-! Tests for the affine cotangent complex of a polynomial resolution. -/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex

attribute [local instance] HasDerivedCategory.standard

namespace MathlibExtTest.GeometricCotangentComplex

universe u

variable (A : Type u) [CommRing A]

/-- A polynomial algebra over `A` is resolved by the constant simplicial algebra on itself,
augmented by the identity. -/
noncomputable def polynomialSelfResolution (σ : Type u) :
    PolynomialResolution A (MvPolynomial σ A) where
  algebra := (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A (MvPolynomial σ A))
  augmentation := 𝟙 _
  polynomial _ := ⟨σ, ⟨AlgEquiv.refl⟩⟩
  surjective _ := Function.surjective_id
  augmentation_quasiIso := inferInstance

/-- `A` over itself: every term is `A ≅ MvPolynomial PEmpty A`, and the identity augmentation is
surjective and an isomorphism, hence a quasi-isomorphism. -/
noncomputable def selfResolution : PolynomialResolution A A where
  algebra := (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A A)
  augmentation := 𝟙 _
  polynomial _ := ⟨PEmpty, ⟨MvPolynomial.isEmptyAlgEquiv A PEmpty⟩⟩
  surjective _ := Function.surjective_id
  augmentation_quasiIso := inferInstance

-- `affineDegreeIso` identifies degree `-n` with the `n`-th base-changed module of differentials.
noncomputable example (n : ℕ) :
    (affineComplex (selfResolution A)).X (-(n : ℤ)) ≅
      CommAlgCat.resolutionCotangentTerm A (CommAlgCat.of A A) (selfResolution A).algebra
        (selfResolution A).augmentation (op ⦋n⦌) :=
  affineDegreeIso (selfResolution A) n

-- The downstream usage pattern: a pure differential placed in degree `0` and read back.
example (σ : Type u) (i : σ) :
    (affineDegreeIso (polynomialSelfResolution A σ) 0).hom
        ((affineDegreeIso (polynomialSelfResolution A σ) 0).inv
          (CommAlgCat.resolutionCotangentTermDifferential A (CommAlgCat.of A (MvPolynomial σ A))
            (polynomialSelfResolution A σ).algebra (polynomialSelfResolution A σ).augmentation
            (op ⦋0⦌) (MvPolynomial.X i))) =
      CommAlgCat.resolutionCotangentTermDifferential A (CommAlgCat.of A (MvPolynomial σ A))
        (polynomialSelfResolution A σ).algebra (polynomialSelfResolution A σ).augmentation
        (op ⦋0⦌) (MvPolynomial.X i) :=
  Iso.inv_hom_id_apply _ _

/-- Every term of the self-resolution of `A` is zero, since `Ω[A⁄A] = 0`. -/
theorem isZero_term (n : SimplexCategoryᵒᵖ) :
    IsZero (CommAlgCat.resolutionCotangentTerm A (CommAlgCat.of A A) (selfResolution A).algebra
      (selfResolution A).augmentation n) := by
  rw [IsZero.iff_id_eq_zero]
  refine CommAlgCat.resolutionCotangentTerm_hom_ext A _ _ _ n _ _ fun p => ?_
  have hp : KaehlerDifferential.D A ((selfResolution A).algebra.obj n) p = 0 :=
    (KaehlerDifferential.D A A).map_algebraMap p
  rw [CommAlgCat.resolutionCotangentTermDifferential, hp]
  exact TensorProduct.tmul_zero _ _

/-- Every component of the computed cotangent complex of `A` over itself is zero: degree `-n` by
`affineDegreeIso`, and positive degrees by construction. -/
theorem isZero_X (k : ℤ) : IsZero ((affineComplex (selfResolution A)).X k) := by
  rcases le_or_gt k 0 with hk | hk
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨k.natAbs, by omega⟩
    exact (isZero_term A (op ⦋n⦌)).of_iso (affineDegreeIso (selfResolution A) n)
  · exact HomologicalComplex.isZero_extend_X _ _ k
      ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 k).2 hk)

-- Hence the derived object computed from this resolution is zero, as `L_{A/A} = 0`.
example : IsZero (affineDerived (selfResolution A)) := by
  have h : IsZero (affineComplex (selfResolution A)) := by
    rw [IsZero.iff_id_eq_zero]
    ext k : 1
    exact (isZero_X A k).eq_of_src _ _
  exact DerivedCategory.Q.map_isZero h

/-- The quasi-isomorphism field of `PolynomialResolution`, stated for `A`-modules, is equivalent
to the condition on underlying abelian groups in the criterion of Stacks Tag 08QI. -/
theorem quasiIso_iff_addCommGrp {B : Type u} [CommRing B] [Algebra A B]
    {P : SimplicialObject (CommAlgCat.{u} A)}
    (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (Functor.whiskerRight ε (forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙
          forget₂ (AlgCat.{u} A) (ModuleCat.{u} A)))) ↔
      QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (Functor.whiskerRight ε (forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙
          forget₂ (AlgCat.{u} A) (ModuleCat.{u} A) ⋙
            forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})]
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoOfNatIso (alternatingFaceMapComplexCompMapHomologicalComplexIso _) (Arrow.mk _))

-- Every `PolynomialResolution` satisfies that abelian-group condition.
example {B : Type u} [CommRing B] [Algebra A B] (R : PolynomialResolution A B) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight R.augmentation (forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙
        forget₂ (AlgCat.{u} A) (ModuleCat.{u} A) ⋙
          forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))) :=
  (quasiIso_iff_addCommGrp A R.augmentation).1 R.augmentation_quasiIso

end MathlibExtTest.GeometricCotangentComplex
