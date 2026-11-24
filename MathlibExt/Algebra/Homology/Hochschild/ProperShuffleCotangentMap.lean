/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPositiveAlgebra
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricHarrisonDegreeOne
public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormProjection
public import MathlibExt.Algebra.Homology.Embedding.PositiveNat
public import Mathlib.Algebra.Homology.Single
public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormProjectionSurjective
public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# The proper-shuffle cotangent augmentation

The positive-index restriction has degree n equal to the
proper quotient in degree n + 1. Its degree-zero augmentation
sends coefficient tensor words to coefficient universal
differentials and commutes with the differential. This
uses the both-positive relation quotient. Full
coefficient-ideal relations also allow a degree-zero
second factor.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [SMulCommClass k A M]

/-- The canonical quotient projection, with the original pairing and ground actions. -/
def properShuffleProjection : chainComplex k A M ⟶ positiveQuotient k A M := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.positiveImageProjection (pairing.{u, v, w} k A M)
    (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M)

/-- The positive-index restriction is the original proper quotient with its native index shift. -/
abbrev properCotangentComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (positiveQuotient k A M).restriction ComplexShape.positiveNatEmbedding

omit [SMulCommClass k A M] in
/-- Degree n retains the original quotient degree n+1, the Harrison-to-AQ shift. -/
theorem properCotangentComplex_X (n : ℕ) :
    (properCotangentComplex k A M).X n = (positiveQuotient k A M).X (n + 1) := rfl

/-- The original coefficient differential-form module in degree one. -/
abbrev cotangentFormModule : ModuleCat.{max u v w} k :=
  (coefficientDifferentialFormComplex k A M).X 1

omit [SMulCommClass k A M] in
private theorem properRelations_one : rawPositiveRelations k A M 1 = ⊥ := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.positiveImages_one (pairing.{u, v, w} k A M)

/-- The universal-differential map descends through the proper quotient in degree one. -/
def properCotangentDegreeMap : (positiveQuotient k A M).X 1 ⟶ cotangentFormModule k A M :=
  ModuleCat.ofHom ((rawPositiveRelations k A M 1).liftQ
    ((coefficientDifferentialFormChainMap k A M).f 1).hom (by
      rw [properRelations_one]
      exact bot_le))

/-- The quotient descent retains the original differential-form map. -/
theorem properCotangentDegreeMap_projection :
    (properShuffleProjection k A M).f 1 ≫ properCotangentDegreeMap k A M =
      (coefficientDifferentialFormChainMap k A M).f 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

omit [SMulCommClass k A M] in
private theorem properProjection_epi (n : ℕ) : Epi ((properShuffleProjection k A M).f n) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  change Function.Surjective (rawPositiveRelations k A M n).mkQ
  exact Submodule.mkQ_surjective _

/-- The incoming quotient boundary is annihilated by universal differentials. -/
theorem properCotangentDegreeMap_boundary :
    (positiveQuotient k A M).d 2 1 ≫ properCotangentDegreeMap k A M = 0 := by
  let π := properShuffleProjection k A M
  let F := coefficientDifferentialFormChainMap k A M
  let _ : Epi (π.f 2) := properProjection_epi k A M 2
  apply (cancel_epi (π.f 2)).1
  calc
    _ = (π.f 2 ≫ (positiveQuotient k A M).d 2 1) ≫ properCotangentDegreeMap k A M :=
      (Category.assoc _ _ _).symm
    _ = ((chainComplex k A M).d 2 1 ≫ π.f 1) ≫ properCotangentDegreeMap k A M :=
      congrArg (fun h => h ≫ properCotangentDegreeMap k A M) (π.comm 2 1)
    _ = (chainComplex k A M).d 2 1 ≫ F.f 1 :=
      (Category.assoc _ _ _).trans
        (congrArg (fun h => (chainComplex k A M).d 2 1 ≫ h)
          (properCotangentDegreeMap_projection k A M))
    _ = F.f 2 ≫ (coefficientDifferentialFormComplex k A M).d 2 1 := (F.comm 2 1).symm
    _ = 0 := (congrArg (fun d => F.f 2 ≫ d)
      (coefficientDifferentialFormComplex_d_eq_zero k A M 2 1)).trans Limits.comp_zero
    _ = _ := Limits.comp_zero.symm

/-- The positive-index cotangent augmentation is a native chain map. -/
def properCotangentAugmentation : properCotangentComplex k A M ⟶
    (ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj (cotangentFormModule k A M) :=
  (ChainComplex.toSingle₀Equiv (properCotangentComplex k A M) (cotangentFormModule k A M)).symm
    ⟨properCotangentDegreeMap k A M, by
      change (positiveQuotient k A M).d 2 1 ≫ properCotangentDegreeMap k A M = 0
      exact properCotangentDegreeMap_boundary k A M⟩

/-- The native augmentation uses precisely the original degree-one descent. -/
theorem properCotangentAugmentation_f_zero :
    (properCotangentAugmentation k A M).f 0 = properCotangentDegreeMap k A M := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

/-- The original degree-one tensor class maps to the universal differential word. -/
theorem properCotangentDegreeMap_tprod (m : M) (a : Fin 1 → A) :
    (properCotangentDegreeMap k A M).hom
        ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A 1 (fun j => KaehlerDifferential.D k A (a j))) := by
  exact coefficientDifferentialFormChainMap_tprod k A M 1 m a

/-- The original coefficient tensor the universal cotangent module, in the same carrier height. -/
abbrev coefficientCotangentModule : ModuleCat.{max u v w} k :=
  ModuleCat.of k (ULift.{u} (M ⊗[A] KaehlerDifferential k A))

/-- Native exterior-degree-one coordinates identify the form point with universal differentials. -/
def cotangentFormOneIso : cotangentFormModule k A M ≅ coefficientCotangentModule k A M := by
  let Ω := KaehlerDifferential k A
  let e : M ⊗[A] (⋀[A]^1 Ω) ≃ₗ[k] M ⊗[A] Ω :=
    (TensorProduct.congr (LinearEquiv.refl A M) (exteriorPower.oneEquiv A Ω)).restrictScalars k
  exact ((ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^1 Ω)) ≃ₗ[k] M ⊗[A] (⋀[A]^1 Ω)).trans
    (e.trans (ULift.moduleEquiv : ULift.{u} (M ⊗[A] Ω) ≃ₗ[k] M ⊗[A] Ω).symm)).toModuleIso

/-- The quotient-to-cotangent chain map uses the original universal module and native one-form coordinates. -/
def properShuffleCotangentMap : properCotangentComplex k A M ⟶
    (ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj (coefficientCotangentModule k A M) :=
  properCotangentAugmentation k A M ≫
    (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (cotangentFormOneIso k A M).hom

/-- The full comparison factors through the computed coefficient one-form point. -/
theorem properShuffleCotangentMap_eq :
    properShuffleCotangentMap k A M = properCotangentAugmentation k A M ≫
      (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (cotangentFormOneIso k A M).hom := rfl

/-- Universal differentials make the proper quotient degree-one map surjective. -/
theorem properCotangentDegreeMap_surjective :
    Function.Surjective (properCotangentDegreeMap k A M).hom := by
  intro y
  obtain ⟨x, hx⟩ := coefficientDifferentialFormChainMap_surjective k A M 1 y
  refine ⟨(rawPositiveRelations k A M 1).mkQ x, ?_⟩
  change ((coefficientDifferentialFormChainMap k A M).f 1).hom x = y
  exact hx

/-- The degree-zero scalar augmentation uses the descent and original one-form coordinates. -/
def properCotangentScalarAugmentation : (properCotangentComplex k A M).X 0 ⟶
    coefficientCotangentModule k A M :=
  properCotangentDegreeMap k A M ≫ (cotangentFormOneIso k A M).hom

/-- The original incoming differential is killed by this scalar augmentation. -/
theorem properCotangentScalarAugmentation_boundary :
    (properCotangentComplex k A M).d 1 0 ≫ properCotangentScalarAugmentation k A M = 0 := by
  change (positiveQuotient k A M).d 2 1 ≫
    (properCotangentDegreeMap k A M ≫ (cotangentFormOneIso k A M).hom) = 0
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cotangentFormOneIso k A M).hom)
      (properCotangentDegreeMap_boundary k A M)).trans Limits.zero_comp)

/-- The literal original cotangent scalar augmentation is surjective, with no flat coefficient hypothesis. -/
theorem properCotangentScalarAugmentation_surjective :
    Function.Surjective (properCotangentScalarAugmentation k A M).hom := by
  intro y
  let e := cotangentFormOneIso k A M
  obtain ⟨x, hx⟩ := properCotangentDegreeMap_surjective k A M (e.inv.hom y)
  refine ⟨x, ?_⟩
  change e.hom.hom ((properCotangentDegreeMap k A M).hom x) = y
  exact (congrArg e.hom.hom hx).trans (ConcreteCategory.congr_hom e.inv_hom_id y)

omit [SMulCommClass k A M] in
/-- The one-form tensor coordinates retain each original universal differential. -/
theorem cotangentFormOneIso_tprod (m : M) (a : Fin 1 → A) :
    (cotangentFormOneIso k A M).hom.hom
      (ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A 1
        (fun j => KaehlerDifferential.D k A (a j)))) =
      ULift.up (m ⊗ₜ[A] KaehlerDifferential.D k A (a 0)) := by
  change ULift.up (m ⊗ₜ[A] exteriorPower.oneEquiv A (KaehlerDifferential k A)
      (exteriorPower.ιMulti A 1 (fun j => KaehlerDifferential.D k A (a j)))) = _
  rw [exteriorPower.oneEquiv_ιMulti]

/-- An original proper-shuffle tensor class has its literal coefficient cotangent augmentation value. -/
theorem properCotangentScalarAugmentation_tprod (m : M) (a : Fin 1 → A) :
    (properCotangentScalarAugmentation k A M).hom
      ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      ULift.up (m ⊗ₜ[A] KaehlerDifferential.D k A (a 0)) := by
  change (cotangentFormOneIso k A M).hom.hom
    ((properCotangentDegreeMap k A M).hom
      ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))) = _
  exact (congrArg (cotangentFormOneIso k A M).hom.hom
    (properCotangentDegreeMap_tprod k A M m a)).trans (cotangentFormOneIso_tprod k A M m a)

/-- The native homology-zero cokernel gives the induced map to original coefficient cotangents. -/
def properCotangentHomologyZeroMap : (properCotangentComplex k A M).homology 0 ⟶
    coefficientCotangentModule k A M :=
  (ChainComplex.homologyZeroCoforkIsColimit (properCotangentComplex k A M)).desc
    (CokernelCofork.ofπ (properCotangentScalarAugmentation k A M)
      (properCotangentScalarAugmentation_boundary k A M))

/-- Its universal projection square is the original scalar augmentation, not an arbitrary map. -/
@[reassoc]
theorem properCotangentHomologyZeroMap_class :
    ChainComplex.homologyZeroClass (properCotangentComplex k A M) ≫
      properCotangentHomologyZeroMap k A M = properCotangentScalarAugmentation k A M := by
  exact Cofork.IsColimit.π_desc
    (t := CokernelCofork.ofπ (properCotangentScalarAugmentation k A M)
      (properCotangentScalarAugmentation_boundary k A M))
    (ChainComplex.homologyZeroCoforkIsColimit (properCotangentComplex k A M))

/-- The native homology class of the original tensor maps to its literal universal differential. -/
theorem properCotangentHomologyZeroMap_tprod (m : M) (a : Fin 1 → A) :
    (properCotangentHomologyZeroMap k A M).hom
      ((ChainComplex.homologyZeroClass (properCotangentComplex k A M)).hom
        ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      ULift.up (m ⊗ₜ[A] KaehlerDifferential.D k A (a 0)) := by
  have h := ConcreteCategory.congr_hom (properCotangentHomologyZeroMap_class k A M)
    ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  exact h.trans (properCotangentScalarAugmentation_tprod k A M m a)

/-- Actual native degree-zero homology maps onto the original coefficient cotangent module. -/
theorem properCotangentHomologyZeroMap_surjective :
    Function.Surjective (properCotangentHomologyZeroMap k A M).hom := by
  intro y
  obtain ⟨x, hx⟩ := properCotangentScalarAugmentation_surjective k A M y
  refine ⟨(ChainComplex.homologyZeroClass (properCotangentComplex k A M)).hom x, ?_⟩
  have h := ConcreteCategory.congr_hom (properCotangentHomologyZeroMap_class k A M) x
  exact h.trans hx

/-- The induced original cokernel map is therefore an epimorphism. -/
theorem properCotangentHomologyZeroMap_epi : Epi (properCotangentHomologyZeroMap k A M) :=
  (ModuleCat.epi_iff_surjective _).mpr (properCotangentHomologyZeroMap_surjective k A M)

/-- The original scalar augmentation agrees on every representative with the
canonical A-linear tensor presentation, after the original whole-module lift. -/
theorem properCotangentScalarAugmentation_mkQ (x : M ⊗[k] TensorPower k 1 A) :
    (properCotangentScalarAugmentation k A M).hom ((rawPositiveRelations k A M 1).mkQ x) =
      ULift.up (algebraOneToKaehler k A M x) := by
  let l : (M ⊗[k] TensorPower k 1 A) →ₗ[k] ULift.{u} (M ⊗[A] KaehlerDifferential k A) :=
    ((properShuffleProjection k A M).f 1 ≫ properCotangentScalarAugmentation k A M).hom
  let r : (M ⊗[k] TensorPower k 1 A) →ₗ[k] ULift.{u} (M ⊗[A] KaehlerDifferential k A) :=
    (ULift.moduleEquiv : ULift.{u} (M ⊗[A] KaehlerDifferential k A) ≃ₗ[k]
      M ⊗[A] KaehlerDifferential k A).symm.toLinearMap.comp
        ((algebraOneToKaehler k A M).restrictScalars k)
  have h : l = r := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change (properCotangentScalarAugmentation k A M).hom
      ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
        ULift.up (algebraOneToKaehler k A M (m ⊗ₜ[k] PiTensorProduct.tprod k a))
    exact (properCotangentScalarAugmentation_tprod k A M m a).trans
      (congrArg ULift.up (algebraOneToKaehler_tprod k A M m a)).symm
  exact DFunLike.congr_fun h x

/-- Native universal derivation exactness and native tensor right exactness
identify the augmentation kernel with the original incoming proper boundary.
Neither coefficient flatness nor a comparison certificate is assumed. -/
theorem properCotangentScalarAugmentation_exact :
    Function.Exact ((properCotangentComplex k A M).d 1 0).hom
      (properCotangentScalarAugmentation k A M).hom := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (rawPositiveRelations k A M 1) y
  constructor
  · intro hx
    have hx' : algebraOneToKaehler k A M x = 0 := by
      have h : ULift.up (algebraOneToKaehler k A M x) =
          (0 : ULift.{u} (M ⊗[A] KaehlerDifferential k A)) :=
        (properCotangentScalarAugmentation_mkQ k A M x).symm.trans hx
      exact congrArg ULift.down h
    obtain ⟨z, hz⟩ := (algebraBoundary_two_exact k A M x).mp hx'
    refine ⟨(rawPositiveRelations k A M 2).mkQ z, ?_⟩
    change ((positiveQuotient k A M).d 2 1).hom
      ((rawPositiveRelations k A M 2).mkQ z) = (rawPositiveRelations k A M 1).mkQ x
    exact (positiveQuotient_d_mk k A M 1 z).trans
      (congrArg (rawPositiveRelations k A M 1).mkQ hz)
  · rintro ⟨z, hz⟩
    rw [← hz]
    exact ConcreteCategory.congr_hom (properCotangentScalarAugmentation_boundary k A M) z

/-- The literal original augmentation kernel is the range of the original degree-two boundary. -/
theorem properCotangentScalarAugmentation_kernel :
    LinearMap.ker (properCotangentScalarAugmentation k A M).hom =
      LinearMap.range ((properCotangentComplex k A M).d 1 0).hom := by
  ext x
  exact properCotangentScalarAugmentation_exact k A M x

/-- The coefficient cotangent cofork uses the augmentation. -/
def properCotangentCokernelCofork : CokernelCofork ((properCotangentComplex k A M).d 1 0) :=
  CokernelCofork.ofπ (properCotangentScalarAugmentation k A M)
    (properCotangentScalarAugmentation_boundary k A M)

/-- The universal derivation and arbitrary-coefficient tensor presentation
prove that this cofork is a cokernel of the original proper differential. -/
def properCotangentCokernelIsColimit : IsColimit (properCotangentCokernelCofork k A M) :=
  ModuleCat.isColimitCokernelCofork ((properCotangentComplex k A M).d 1 0)
    (properCotangentScalarAugmentation k A M)
    (properCotangentScalarAugmentation_exact k A M)
    (properCotangentScalarAugmentation_surjective k A M)

/-- Native cokernel uniqueness identifies degree-zero homology with the
original coefficient cotangent module, over arbitrary commutative ground rings. -/
def properCotangentHomologyZeroIso : (properCotangentComplex k A M).homology 0 ≅
    coefficientCotangentModule k A M :=
  (ChainComplex.homologyZeroCoforkIsColimit (properCotangentComplex k A M)).coconePointUniqueUpToIso
    (properCotangentCokernelIsColimit k A M)

/-- The isomorphism has exactly the previously constructed H0 comparison as its forward map. -/
theorem properCotangentHomologyZeroIso_hom :
    (properCotangentHomologyZeroIso k A M).hom = properCotangentHomologyZeroMap k A M := rfl

/-- The inverse is the native descent from the coefficient cotangent cokernel. -/
theorem properCotangentHomologyZeroIso_inv :
    (properCotangentHomologyZeroIso k A M).inv =
      (properCotangentCokernelIsColimit k A M).desc
        (ChainComplex.homologyZeroCofork (properCotangentComplex k A M)) := rfl

/-- The inverse returns the class of every original quotient representative. -/
@[reassoc]
theorem properCotangentHomologyZeroIso_class_inv :
    properCotangentScalarAugmentation k A M ≫ (properCotangentHomologyZeroIso k A M).inv =
      ChainComplex.homologyZeroClass (properCotangentComplex k A M) := by
  let e := properCotangentHomologyZeroIso k A M
  have h : ChainComplex.homologyZeroClass (properCotangentComplex k A M) ≫ e.hom =
      properCotangentScalarAugmentation k A M := properCotangentHomologyZeroMap_class k A M
  calc
    _ = (ChainComplex.homologyZeroClass (properCotangentComplex k A M) ≫ e.hom) ≫ e.inv :=
      congrArg (fun f => f ≫ e.inv) h.symm
    _ = ChainComplex.homologyZeroClass (properCotangentComplex k A M) := by
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The canonical H0 cotangent map is injective by the Leibniz presentation. -/
theorem properCotangentHomologyZeroMap_injective :
    Function.Injective (properCotangentHomologyZeroMap k A M).hom := by
  rw [← properCotangentHomologyZeroIso_hom]
  exact (properCotangentHomologyZeroIso k A M).toLinearEquiv.injective

/-- The same comparison returns the coefficient cotangent tensor in its original universe. -/
def properCotangentHomologyZeroEquiv :
    (properCotangentComplex k A M).homology 0 ≃ₗ[k] M ⊗[A] KaehlerDifferential k A :=
  (properCotangentHomologyZeroIso k A M).toLinearEquiv.trans
    (ULift.moduleEquiv : ULift.{u} (M ⊗[A] KaehlerDifferential k A) ≃ₗ[k]
      M ⊗[A] KaehlerDifferential k A)

/-- The equivalence retains the original coefficient and universal differential. -/
theorem properCotangentHomologyZeroEquiv_tprod (m : M) (a : Fin 1 → A) :
    properCotangentHomologyZeroEquiv k A M
      ((ChainComplex.homologyZeroClass (properCotangentComplex k A M)).hom
        ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      m ⊗ₜ[A] KaehlerDifferential.D k A (a 0) := by
  exact congrArg ULift.down (properCotangentHomologyZeroMap_tprod k A M m a)

end ModuleCat.Algebra.Hochschild.Symmetric
