/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheory
import MathlibExt.AlgebraicGeometry.AffinePerfectObstructionTheoryPolynomialLiftIndependence

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

section Polynomial

variable (k)

/-- The constant simplicial algebra on `k[X]`. -/
noncomputable abbrev constPoly : SimplicialObject (CommAlgCat.{0} k) :=
  (SimplicialObject.const (CommAlgCat.{0} k)).obj (CommAlgCat.of k (MvPolynomial (Fin 1) k))

/-- `k[X]` over `k`, resolved by the constant simplicial algebra on itself with the identity
augmentation. Unlike `selfResolution`, its cotangent complex is nonzero: every term is
`Ω[k[X]⁄k] ⊗ k[X]`. -/
noncomputable abbrev polyResolution : PolynomialResolution k (MvPolynomial (Fin 1) k) where
  algebra := constPoly k
  augmentation := 𝟙 _
  polynomial _ := ⟨Fin 1, ⟨AlgEquiv.refl⟩⟩
  surjective _ := Function.surjective_id
  augmentation_quasiIso := inferInstance

/-- The simplicial module of base-changed differentials of `polyResolution`. -/
noncomputable abbrev polyModule :=
  (CommAlgCat.resolutionCotangentSimplicialModule k (CommAlgCat.of k (MvPolynomial (Fin 1) k))
    (constPoly k) (𝟙 _)).object

/-- Read through `affineDegreeIso`, the differential from degree `-(n + 1)` to degree `-n` of
the cotangent complex of a resolution is the alternating sum of the face maps. -/
theorem affineComplex_d_eq {B : Type} [CommRing B] [Algebra k B]
    (R : PolynomialResolution k B) (n : ℕ) :
    (affineComplex R).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (affineDegreeIso R (n + 1)).hom ≫
        AlternatingFaceMapComplex.objD (CommAlgCat.resolutionCotangentSimplicialModule k
          (CommAlgCat.of k B) R.algebra R.augmentation).object n ≫
        (affineDegreeIso R n).inv := by
  rw [← alternatingFaceMapComplex_obj_d]
  exact HomologicalComplex.extend_d_eq _ (ComplexShape.embeddingUpIntLE 0) (by simp) (by simp)

/-- A face map sends `1 ⊗ d p` to `1 ⊗ d (δᵢ p)`. -/
theorem δ_differential {B : CommAlgCat.{0} k} (P : SimplicialObject (CommAlgCat.{0} k))
    (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{0} k)).obj B) (n : ℕ) (i : Fin (n + 2))
    (p : P.obj (op ⦋n + 1⦌)) :
    (CommAlgCat.resolutionCotangentSimplicialModule k B P ε).object.δ i
        (CommAlgCat.resolutionCotangentTermDifferential k B P ε (op ⦋n + 1⦌) p) =
      CommAlgCat.resolutionCotangentTermDifferential k B P ε (op ⦋n⦌) (P.δ i p) :=
  CommAlgCat.resolutionCotangentMap_D k B P ε (SimplexCategory.δ i).op p

/-- The face maps of the constant resolution all agree, as they fix the pure differentials. -/
theorem poly_δ_eq (n : ℕ) (i j : Fin (n + 2)) : (polyModule k).δ i = (polyModule k).δ j :=
  CommAlgCat.resolutionCotangentTerm_hom_ext k _ _ _ _ _ _ fun p =>
    (δ_differential k (constPoly k) (𝟙 _) n i p).trans
      (δ_differential k (constPoly k) (𝟙 _) n j p).symm

/-- From degree `-1` to degree `0` the differential is `δ₀ - δ₁ = 0`. -/
example : (affineComplex (polyResolution k)).d (-((0 + 1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) = 0 := by
  rw [affineComplex_d_eq]
  have h : AlternatingFaceMapComplex.objD (polyModule k) 0 =
      (polyModule k).δ 0 - (polyModule k).δ 1 := by
    simp [AlternatingFaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg]
  erw [h, poly_δ_eq k 0 0 1, sub_self, Limits.zero_comp, Limits.comp_zero]

/-- From degree `-2` to degree `-1` the differential is `δ₀ - δ₁ + δ₂ = δ₀`. -/
example : (affineComplex (polyResolution k)).d (-((1 + 1 : ℕ) : ℤ)) (-((1 : ℕ) : ℤ)) =
    (affineDegreeIso (polyResolution k) 2).hom ≫ (polyModule k).δ 0 ≫
      (affineDegreeIso (polyResolution k) 1).inv := by
  rw [affineComplex_d_eq]
  have h : AlternatingFaceMapComplex.objD (polyModule k) 1 =
      (polyModule k).δ 0 - (polyModule k).δ 1 + (polyModule k).δ 2 := by
    simp [AlternatingFaceMapComplex.objD, Fin.sum_univ_three, sub_eq_add_neg]
  erw [h, poly_δ_eq k 1 2 1, sub_add_cancel]

/-! Independence of the obstruction class from the polynomial lift, on the dual numbers over
`k[X]`. -/

open WantedExt.AlgebraicGeometry.AffinePerfectObstructionTheoryWanted

/-- The dual numbers over `k[X]` as a square-zero extension of `k[X]`. -/
noncomputable abbrev dualExtension : Algebra.Extension.{0} k (MvPolynomial (Fin 1) k) :=
  Algebra.Extension.ofSurjective
    (TrivSqZeroExt.fstHom k (MvPolynomial (Fin 1) k) (MvPolynomial (Fin 1) k))
    TrivSqZeroExt.fst_surjective

theorem dualExtension_ker_sq : (dualExtension k).ker ^ 2 = ⊥ :=
  TrivSqZeroExt.kerIdeal_sq _ _

/-- The algebra map `k[X] → k[X][ε]` sending `X` to `X + c ε`. -/
noncomputable def dualHom (c : MvPolynomial (Fin 1) k) :
    MvPolynomial (Fin 1) k →ₐ[k] DualNumber (MvPolynomial (Fin 1) k) :=
  MvPolynomial.aeval fun _ => TrivSqZeroExt.inl (MvPolynomial.X 0) + c • DualNumber.eps

theorem dualHom_X (c : MvPolynomial (Fin 1) k) :
    dualHom k c (MvPolynomial.X 0) = TrivSqZeroExt.inl (MvPolynomial.X 0) + c • DualNumber.eps :=
  MvPolynomial.aeval_X _ _

/-- The lift of `polyResolution` sending `X` to `X + c ε`. -/
noncomputable def dualLift (c : MvPolynomial (Fin 1) k) :
    PolynomialLift (polyResolution k) (dualExtension k) where
  hom := dualHom k c
  over := MvPolynomial.algHom_ext fun i => by
    obtain rfl := Subsingleton.elim i 0
    change TrivSqZeroExt.fst (dualHom k c (MvPolynomial.X 0)) = MvPolynomial.X 0
    simp [dualHom_X]

/-- The lifts `X ↦ X` and `X ↦ X + ε` are distinct. -/
theorem dualLift_ne : dualLift k 0 ≠ dualLift k 1 := by
  intro h
  have hX : TrivSqZeroExt.snd (dualHom k 0 (MvPolynomial.X 0)) =
      TrivSqZeroExt.snd (dualHom k 1 (MvPolynomial.X 0)) :=
    congrArg (fun L : PolynomialLift (polyResolution k) (dualExtension k) =>
      TrivSqZeroExt.snd (L.hom (MvPolynomial.X 0))) h
  simp [dualHom_X] at hX

/-- The witness `ε ≠ 0` lies in the kernel, so the extension is not trivial. -/
example : (dualExtension k).ker ≠ ⊥ := by
  intro h
  have hε : (DualNumber.eps : DualNumber (MvPolynomial (Fin 1) k)) ∈ (dualExtension k).ker :=
    RingHom.mem_ker.mpr DualNumber.fst_eps
  rw [h] at hε
  have h0 : (DualNumber.eps : DualNumber (MvPolynomial (Fin 1) k)) = 0 := Ideal.mem_bot.mp hε
  exact one_ne_zero (α := MvPolynomial (Fin 1) k) (by simpa using congrArg TrivSqZeroExt.snd h0)

/-- The obstruction class is independent of the lift on dual numbers over `k[X]`. -/
example (T : PerfectObstructionTheory (polyResolution k))
    (C : CotangentExtensionCocycle (polyResolution k) (dualExtension k) (dualLift k 0))
    (C' : CotangentExtensionCocycle (polyResolution k) (dualExtension k) (dualLift k 1)) :
    obstructionClass T C = obstructionClass T C' :=
  polynomial_lift_independence _ T _ (dualExtension_ker_sq k) _ _ C C'

/-- Vanishing of the obstruction class transfers across polynomial lifts. -/
theorem vanishing_transfer (T : PerfectObstructionTheory (polyResolution k))
    (C : CotangentExtensionCocycle (polyResolution k) (dualExtension k) (dualLift k 0))
    (C' : CotangentExtensionCocycle (polyResolution k) (dualExtension k) (dualLift k 1))
    (h : obstructionClass T C = 0) : obstructionClass T C' = 0 := by
  rw [← polynomial_lift_independence _ T _ (dualExtension_ker_sq k) _ _ C C']
  exact h

end Polynomial

end MathlibExtTest.AffinePerfectObstructionTheory
