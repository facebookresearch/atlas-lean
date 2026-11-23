/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory

set_option autoImplicit false

/-! Tests for affine perfect obstruction theories and normalized extension cocycles. -/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial
open MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
open MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
open MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory

attribute [local instance] HasDerivedCategory.standard

namespace MathlibExtTest.AffinePerfectObstructionTheory

variable (k : Type) [Field k]

/-- `k` over itself, resolved by the constant simplicial algebra with identity augmentation. -/
noncomputable def selfResolution : PolynomialResolution k k where
  algebra := (SimplicialObject.const (CommAlgCat.{0} k)).obj (CommAlgCat.of k k)
  augmentation := 𝟙 _
  polynomial _ := ⟨PEmpty, ⟨MvPolynomial.isEmptyAlgEquiv k PEmpty⟩⟩
  surjective _ := Function.surjective_id
  augmentation_quasiIso := inferInstance

/-- Every component of the computed cotangent complex of `k` over itself is zero. -/
theorem isZero_affineComplex_X (i : ℤ) : IsZero ((affineComplex (selfResolution k)).X i) := by
  rcases le_or_gt i 0 with hi | hi
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨i.natAbs, by omega⟩
    refine IsZero.of_iso ?_ (affineDegreeIso (selfResolution k) n)
    rw [IsZero.iff_id_eq_zero]
    refine CommAlgCat.resolutionCotangentTerm_hom_ext k _ _ _ _ _ _ fun p => ?_
    have hp : KaehlerDifferential.D k ((selfResolution k).algebra.obj (op ⦋n⦌)) p = 0 :=
      (KaehlerDifferential.D k k).map_algebraMap p
    rw [CommAlgCat.resolutionCotangentTermDifferential, hp]
    exact TensorProduct.tmul_zero _ _
  · exact HomologicalComplex.isZero_extend_X _ _ i
      ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 i).2 hi)

theorem isZero_affineDerived : IsZero (affineDerived (selfResolution k)) := by
  have h : IsZero (affineComplex (selfResolution k)) := by
    rw [IsZero.iff_id_eq_zero]
    ext i : 1
    exact (isZero_affineComplex_X k i).eq_of_src _ _
  exact DerivedCategory.Q.map_isZero h

/-- The zero finite free two-term complex. -/
def zeroModel : FreeTwoTerm k := ⟨0, 0, 0⟩

theorem isZero_derived_zeroModel : IsZero (derived k (zeroModel k)) := by
  have hF : ∀ j : ℤ, IsZero (((CochainComplex.singleFunctor (ModuleCat.{0} k) 0).obj
      (ModuleCat.of k (Fin 0 → k))).X j) := fun j =>
    (HomologicalComplex.eval _ _ j).map_isZero
      ((CochainComplex.singleFunctor _ 0).map_isZero
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of k (Fin 0 → k))))
  have h : IsZero (complex k (zeroModel k)) := by
    rw [IsZero.iff_id_eq_zero]
    ext i : 1
    apply IsZero.eq_of_src
    rw [complex, CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hF (i + 1), hF i⟩
  exact DerivedCategory.Q.map_isZero h

/-- `k` over itself has a perfect obstruction theory: the zero model with the zero morphism to its
(zero) cotangent complex. In particular the structure is not vacuous. -/
noncomputable def zeroTheory : PerfectObstructionTheory (selfResolution k) where
  model := zeroModel k
  morphism := 0
  h0 := isIso_of_source_target_iso_zero _
    (((DerivedCategory.homologyFunctor _ 0).map_isZero (isZero_derived_zeroModel k)).isoZero)
    (((DerivedCategory.homologyFunctor _ 0).map_isZero (isZero_affineDerived k)).isoZero)
  hNegative := ((DerivedCategory.homologyFunctor _ (-1)).map_isZero
    (isZero_affineDerived k)).epi _

variable {k} (Q : Algebra.Extension.{0} k k)

/-- The structure map `k → Q.Ring` lifts the degree-zero term of the self-resolution. -/
noncomputable def unitLift : PolynomialLift (selfResolution k) Q where
  hom := Algebra.ofId k Q.Ring
  over := Subsingleton.elim (α := k →ₐ[k] k) _ _

-- The face maps of a constant simplicial algebra agree, so the lifted faces have no error.
theorem liftError_unitLift (p : (selfResolution k).algebra.obj (op ⦋1⦌)) :
    liftError (selfResolution k) Q (unitLift Q) p = 0 := by
  rw [liftError]
  convert map_zero (Algebra.Extension.Cotangent.mk (P := Q))
  change _ = (0 : Q.Ring)
  exact sub_eq_zero.mpr rfl

/-- The zero cochain map is the normalized cocycle of `unitLift`. -/
noncomputable def unitCocycle : CotangentExtensionCocycle (selfResolution k) Q (unitLift Q) where
  morphism := 0
  normalization p := by
    rw [liftError_unitLift]
    simp

-- The normalized cocycle is unique, so every cocycle of `unitLift` is the zero one.
example (C : CotangentExtensionCocycle (selfResolution k) Q (unitLift Q)) :
    C = unitCocycle Q :=
  cocycle_unique C _

-- The obstruction class is the composite of the theory with the cocycle; here it vanishes,
-- consistently with the existence of the lift `k → Q.Ring`.
example : obstructionClass (zeroTheory k) (unitCocycle Q) = 0 :=
  Limits.zero_comp

example : Nonempty (Liftings Q) := ⟨⟨Algebra.ofId k Q.Ring, Subsingleton.elim _ _⟩⟩

-- The augmentation is compatible with both face maps.
example (i : Fin 2) (p : (selfResolution k).algebra.obj (op ⦋1⦌)) :
    ((selfResolution k).augmentation.app (op ⦋0⦌)).hom ((selfResolution k).algebra.δ i p) =
      ((selfResolution k).augmentation.app (op ⦋1⦌)).hom p :=
  augmentation_face _ i p

end MathlibExtTest.AffinePerfectObstructionTheory
