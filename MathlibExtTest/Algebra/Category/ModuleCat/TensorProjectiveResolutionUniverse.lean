/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.TensorProjectiveResolutionAssociativityUniverse
public import MathlibExt.Algebra.Homology.TensorComponentProjection
public import MathlibExtTest.Algebra.Category.ModuleCat.NativeTorProjectiveDimensionUniverse
public import Mathlib.RingTheory.Artinian.Module

/-!
# Actual tensor-total resolution clients

The split integral presentation has nonzero projective terms in degrees zero
and one, each of infinite length. Tensoring its actual resolution with itself
has infinite-length H0. Pairing it with the original multiplication-by-two
presentation gives a genuine positive-degree tensor/Koszul client with nonzero
H0. Pairing two multiplication-by-two presentations has nonzero Tor1, which
rejects unconditional exactness of the literal tensor augmentation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ModuleCat.UniverseTensor ZeroObject

namespace TensorProjectiveResolutionTests

open ModuleCat.UniverseTensor NativeTorBoundaryTests

/-- The integral coefficient fixture has infinite composition length.
Adapted from `MathlibExtTest/Algebra/Homology/BoundedBicomplexLengthEuler.lean`
at commit `74245d6bfc646c5e3a327852651520b1c45279d4`, using stock length and Artinian APIs. -/
private theorem integer_length_top : Module.length ℤ Z = ⊤ := by
  by_contra h
  have hfin : IsFiniteLength ℤ ℤ := Module.length_ne_top_iff.mp h
  have : IsArtinian ℤ ℤ := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  have hinj : Function.Injective NativeTorBoundaryTests.mulTwo.hom :=
    NativeTorBoundaryTests.integralShortComplex_shortExact.moduleCat_injective_f
  have hsur := IsArtinian.surjective_of_injective_endomorphism
    NativeTorBoundaryTests.mulTwo.hom hinj
  obtain ⟨z, hz⟩ := hsur 1
  change (2 : ℤ) * z = 1 at hz
  omega

/-- The explicitly raw expression records the `ENat.toNat` value at infinite length;
it must not be used as a finite Euler characteristic without its length data. -/
theorem rawEuler_integer_infinite_length : rawNativeTorEulerSum ℤ Z Z 1 = 0 := by
  have h : Module.length ℤ (((Tor (ModuleCat ℤ) 0).obj Z).obj Z) = ⊤ :=
    (nativeTorZeroIso ℤ Z Z).toLinearEquiv.length_eq.trans
      ((TensorProduct.lid ℤ ℤ).length_eq.trans integer_length_top)
  simp [rawNativeTorEulerSum, h]

/-- The original split integral short complex, with its original inclusion and projection. -/
def splitPresentation : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk
    (ModuleCat.ofHom (LinearMap.inl ℤ ℤ ℤ))
    (ModuleCat.ofHom (LinearMap.snd ℤ ℤ ℤ)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

theorem splitPresentation_shortExact : splitPresentation.ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    change Function.Exact (LinearMap.inl ℤ ℤ ℤ) (LinearMap.snd ℤ ℤ ℤ)
    exact Function.Exact.inl_snd
  · apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (LinearMap.inl ℤ ℤ ℤ)
    exact LinearMap.inl_injective
  · apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (LinearMap.snd ℤ ℤ ℤ)
    exact LinearMap.snd_surjective

/-- The actual two-term projective resolution of the original integer module. -/
def splitResolution : ProjectiveResolution Z := by
  have : Projective splitPresentation.X₁ := by change Projective Z; infer_instance
  have : Projective splitPresentation.X₂ := by
    change Projective (ModuleCat.of ℤ (ℤ × ℤ))
    have : Module.Projective ℤ (ℤ × ℤ) := inferInstance
    infer_instance
  exact ProjectiveResolution.ofPresentation splitPresentation splitPresentation_shortExact

theorem splitResolution_zero_length_top : Module.length ℤ (splitResolution.complex.X 0) = ⊤ := by
  change Module.length ℤ (ℤ × ℤ) = ⊤
  rw [Module.length_prod, integer_length_top]
  exact top_add _

theorem splitResolution_one_length_top : Module.length ℤ (splitResolution.complex.X 1) = ⊤ :=
  integer_length_top

theorem integral_positiveTor_zero (n : ℕ) :
    IsZero (((Tor (ModuleCat ℤ) (n + 1)).obj Z).obj Z) :=
  isZero_Tor_succ_of_projective (ModuleCat ℤ) Z Z n

/-- The actual original tensor total is a genuine resolution with its literal augmentation. -/
def infiniteLengthTensorResolution : ProjectiveResolution (Z ⊗ Z) :=
  tensorProjectiveResolution ℤ splitResolution splitResolution integral_positiveTor_zero

example : infiniteLengthTensorResolution.complex =
    HomologicalComplex.tensorObj splitResolution.complex splitResolution.complex := rfl

example : infiniteLengthTensorResolution.π =
    tensorResolutionAugmentation ℤ splitResolution splitResolution := rfl

/-- The genuine tensor-total H0 is the original infinite-length integer module. -/
def infiniteLengthHomologyZeroIso :
    (HomologicalComplex.tensorObj splitResolution.complex splitResolution.complex).homology 0 ≅ Z :=
  tensorResolutionHomologyZeroIso ℤ splitResolution splitResolution ≪≫
    (TensorProduct.lid ℤ ℤ).toModuleIso

theorem tensorTotal_H0_length_top :
    Module.length ℤ
      ((HomologicalComplex.tensorObj splitResolution.complex splitResolution.complex).homology 0) = ⊤ :=
  infiniteLengthHomologyZeroIso.toLinearEquiv.length_eq.trans
    integer_length_top

example (a b c d : ℤ) :
    infiniteLengthTensorResolution.π.f 0
      (HomologicalComplex.ιTensorObj splitResolution.complex splitResolution.complex 0 0 0 rfl
        (TensorProduct.tmul ℤ (a, b) (c, d))) = TensorProduct.tmul ℤ b d := by
  have h := congrArg (fun f => f (TensorProduct.tmul ℤ (a, b) (c, d)))
    (ι_tensorResolutionAugmentation_zero ℤ splitResolution splitResolution)
  exact h

theorem modTwo_integral_positiveTor_zero (n : ℕ) :
    IsZero (((Tor (ModuleCat ℤ) (n + 1)).obj Q).obj Z) :=
  isZero_Tor_succ_of_projective (ModuleCat ℤ) Q Z n

/-- Both original positive-degree presentations form a genuine tensor/Koszul resolution. -/
def positiveKoszulResolution : ProjectiveResolution (Q ⊗ Z) :=
  tensorProjectiveResolution ℤ actualPresentationResolution splitResolution
    modTwo_integral_positiveTor_zero

/-- The actual positive-degree tensor total has the original nonzero mod-two H0. -/
def positiveKoszulHomologyZeroIso :
    (HomologicalComplex.tensorObj actualPresentationResolution.complex splitResolution.complex).homology 0 ≅ Q :=
  tensorResolutionHomologyZeroIso ℤ actualPresentationResolution splitResolution ≪≫
    (TensorProduct.rid ℤ (ZMod 2)).toModuleIso

example : Module.length ℤ
    ((HomologicalComplex.tensorObj actualPresentationResolution.complex splitResolution.complex).homology 0) = 1 :=
  positiveKoszulHomologyZeroIso.toLinearEquiv.length_eq.trans length_Q

example (z a b : ℤ) : positiveKoszulResolution.π.f 0
    (HomologicalComplex.ιTensorObj actualPresentationResolution.complex splitResolution.complex 0 0 0 rfl
      (TensorProduct.tmul ℤ z (a, b))) = TensorProduct.tmul ℤ (z : ZMod 2) b := by
  have h := congrArg (fun f => f (TensorProduct.tmul ℤ z (a, b)))
    (ι_tensorResolutionAugmentation_zero ℤ actualPresentationResolution splitResolution)
  exact h

/-- The second differential of the actual positive-degree tensor uses the negative Koszul sign. -/
example :
    (HomologicalComplex.ιTensorObj actualPresentationResolution.complex splitResolution.complex
      1 1 2 rfl ≫ positiveKoszulResolution.complex.d 2 1) ≫
        HomologicalComplex.tensorComponentProjection
          actualPresentationResolution.complex splitResolution.complex 1 0 =
      -(actualPresentationResolution.complex.X 1 ◁ splitResolution.complex.d 1 0) := by
  change (HomologicalComplex.ιTensorObj actualPresentationResolution.complex splitResolution.complex
    1 1 2 rfl ≫
      (HomologicalComplex.tensorObj actualPresentationResolution.complex splitResolution.complex).d 2 1) ≫
        HomologicalComplex.tensorComponentProjection
          actualPresentationResolution.complex splitResolution.complex 1 0 = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  have h₁ :
      HomologicalComplex.mapBifunctor.d₁ actualPresentationResolution.complex splitResolution.complex
        (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 1 1 1 ≫
          HomologicalComplex.tensorComponentProjection
            actualPresentationResolution.complex splitResolution.complex 1 0 = 0 :=
    HomologicalComplex.tensorComponentProjection_d₁_other
      actualPresentationResolution.complex splitResolution.complex 1 0 0 1 rfl (Or.inl (by omega))
  have h₂ :
      HomologicalComplex.mapBifunctor.d₂ actualPresentationResolution.complex splitResolution.complex
        (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 1 1 1 ≫
          HomologicalComplex.tensorComponentProjection
            actualPresentationResolution.complex splitResolution.complex 1 0 =
        -(actualPresentationResolution.complex.X 1 ◁ splitResolution.complex.d 1 0) := by
    have h :
        HomologicalComplex.mapBifunctor.d₂ actualPresentationResolution.complex splitResolution.complex
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 1 1 1 ≫
            HomologicalComplex.tensorComponentProjection
              actualPresentationResolution.complex splitResolution.complex 1 0 =
          (-1 : ℤˣ) ^ 1 •
            (actualPresentationResolution.complex.X 1 ◁ splitResolution.complex.d 1 0) :=
      HomologicalComplex.tensorComponentProjection_d₂_matching
        actualPresentationResolution.complex splitResolution.complex 1 0
    simpa only [pow_one, Units.neg_smul, one_smul] using h
  rw [h₁, h₂, zero_add]

/-- Actual nonzero native Tor1 prevents the literal tensor total from being a resolution. -/
theorem modTwo_tensor_augmentation_not_quasiIso :
    ¬ QuasiIso (tensorResolutionAugmentation ℤ actualPresentationResolution actualPresentationResolution) := by
  intro h
  exact nativeTor_one_nonzero
    ((tensorResolutionAugmentation_quasiIso_iff ℤ actualPresentationResolution
      actualPresentationResolution).mp h 0)

theorem modTwo_tensor_H1_nonzero :
    ¬ IsZero
      ((HomologicalComplex.tensorObj actualPresentationResolution.complex
        actualPresentationResolution.complex).homology 1) := by
  intro h
  exact nativeTor_one_nonzero
    (h.of_iso (tensorResolutionHomologyIso ℤ actualPresentationResolution actualPresentationResolution 1).symm)

example :
    tensorResolutionAugmentation ℤ actualPresentationResolution actualPresentationResolution =
      (ChainComplex.toSingle₀Equiv
        (HomologicalComplex.tensorObj actualPresentationResolution.complex actualPresentationResolution.complex)
        ((HomologicalComplex.tensorObj actualPresentationResolution.complex
          actualPresentationResolution.complex).homology 0)).symm
        ⟨ChainComplex.homologyZeroClass
          (HomologicalComplex.tensorObj actualPresentationResolution.complex actualPresentationResolution.complex),
          ChainComplex.d_comp_homologyZeroClass _⟩ ≫
        (ChainComplex.single₀ (ModuleCat ℤ)).map
          (tensorResolutionHomologyZeroIso ℤ actualPresentationResolution actualPresentationResolution).hom :=
  tensorResolutionAugmentation_eq_projection ℤ actualPresentationResolution actualPresentationResolution


theorem integral_tensor_first_positiveTor_zero (n : ℕ) :
    IsZero (((Tor (ModuleCat ℤ) (n + 1)).obj (Z ⊗ Z)).obj Z) :=
  isZero_Tor_succ_of_projective (ModuleCat ℤ) (Z ⊗ Z) Z n

theorem integral_tensor_second_positiveTor_zero (n : ℕ) :
    IsZero (((Tor (ModuleCat ℤ) (n + 1)).obj Z).obj (Z ⊗ Z)) := by
  have : Module.Projective ℤ ℤ := inferInstance
  have : Module.Projective ℤ (TensorProduct ℤ ℤ ℤ) :=
    Module.Projective.tensorProduct (R := ℤ) (R₀ := ℤ) (M := ℤ) (N := ℤ)
  have : Projective (Z ⊗ Z) := by
    change Projective (ModuleCat.of ℤ (TensorProduct ℤ ℤ ℤ))
    exact ModuleCat.projective_of_categoryTheory_projective _
  exact isZero_Tor_succ_of_projective (ModuleCat ℤ) Z (Z ⊗ Z) n

/-- The actual ordered associator compares two infinite-length integral resolutions. -/
example : IsIso
    (tensorProjectiveResolutionAssociatorHom ℤ splitResolution splitResolution splitResolution
      integral_positiveTor_zero integral_positiveTor_zero
      integral_tensor_first_positiveTor_zero integral_tensor_second_positiveTor_zero).hom :=
  tensorProjectiveResolutionAssociatorHom_isIso ℤ splitResolution splitResolution splitResolution
    integral_positiveTor_zero integral_positiveTor_zero
    integral_tensor_first_positiveTor_zero integral_tensor_second_positiveTor_zero

example :
    let H := tensorProjectiveResolutionAssociatorHom ℤ splitResolution splitResolution splitResolution
      integral_positiveTor_zero integral_positiveTor_zero
      integral_tensor_first_positiveTor_zero integral_tensor_second_positiveTor_zero
    H.hom ≫
      (tensorProjectiveResolution ℤ splitResolution
        (tensorProjectiveResolution ℤ splitResolution splitResolution integral_positiveTor_zero)
          integral_tensor_second_positiveTor_zero).π =
      (tensorProjectiveResolution ℤ
        (tensorProjectiveResolution ℤ splitResolution splitResolution integral_positiveTor_zero)
          splitResolution integral_tensor_first_positiveTor_zero).π ≫
            (ChainComplex.single₀ (ModuleCat ℤ)).map (α_ Z Z Z).hom :=
  ProjectiveResolution.Hom.hom_comp_π _ _
    (tensorProjectiveResolutionAssociatorHom ℤ splitResolution splitResolution splitResolution
      integral_positiveTor_zero integral_positiveTor_zero
      integral_tensor_first_positiveTor_zero integral_tensor_second_positiveTor_zero)

end TensorProjectiveResolutionTests

universe u v

open ModuleCat.UniverseTensor

example (R : Type u) [CommRing R] {M N : ModuleCat.{max u v} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (hTor : ∀ n : ℕ, IsZero (((Tor (ModuleCat.{max u v} R) (n + 1)).obj M).obj N)) :
    ProjectiveResolution (M ⊗ N) := tensorProjectiveResolution.{u,v} R P Q hTor

example (R : Type u) [CommRing R] {M N : ModuleCat.{max u v} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (HomologicalComplex.tensorObj P.complex Q.complex).homology 0 ≅ M ⊗ N :=
  tensorResolutionHomologyZeroIso.{u,v} R P Q
