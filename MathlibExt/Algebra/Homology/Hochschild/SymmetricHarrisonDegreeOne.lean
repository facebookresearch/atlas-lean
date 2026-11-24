/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- UNEXECUTED source proposal. Original b₂, proper quotient and native Kähler module. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficientMaps
public import MathlibExt.RingTheory.Kaehler.HochschildPresentation
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.NormNum

/-!
# Degree-one proper-shuffle homology

The degree-one proper relation module is zero, and
the degree-two boundary is the coefficient Kähler
presentation boundary. Degree-one homology of the
proper quotient is therefore M ⊗[A] Ω(A/k) for
arbitrary coefficients, without rationality, flatness
or coefficient projectivity assumptions. Ground,
algebra and coefficient universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- Native singleton coordinates and original coefficient cancellation in degree one. -/
def algebraOneTensorEquiv :
    M ⊗[k] TensorPower k 1 A ≃ₗ[A] M ⊗[A] (A ⊗[k] A) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A M)
    (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 => A) 0)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k A A M A).symm

/-- Degree-one coordinates insert the regular head one and retain the original coefficient. -/
theorem algebraOneTensorEquiv_tprod (m : M) (a : Fin 1 → A) :
    algebraOneTensorEquiv k A M (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[A] ((1 : A) ⊗ₜ[k] a 0) := by
  simp only [algebraOneTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.subsingletonEquiv_apply_tprod,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]

/-- Native cons/singleton coordinates and cancellation in degree two. -/
def algebraTwoTensorEquiv :
    M ⊗[k] TensorPower k 2 A ≃ₗ[A] M ⊗[A] (A ⊗[k] (A ⊗[k] A)) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A M)
    ((TensorPower.consEquiv k A 1).symm.trans
      (TensorProduct.congr (LinearEquiv.refl k A)
        (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 => A) 0)))).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k A A M (A ⊗[k] A)).symm

/-- Degree-two coordinates keep both original tail entries in their original order. -/
theorem algebraTwoTensorEquiv_tprod (m : M) (a : Fin 2 → A) :
    algebraTwoTensorEquiv k A M (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[A] ((1 : A) ⊗ₜ[k] (a 0 ⊗ₜ[k] a 1)) := by
  simp only [algebraTwoTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    TensorPower.consEquiv_symm_tprod, TensorProduct.congr_tmul,
    PiTensorProduct.subsingletonEquiv_apply_tprod,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  rfl

/-- The coefficient boundary is the native Kähler b₂ after the original tensor coordinates. -/
theorem algebraBoundary_two_tensor :
    (algebraOneTensorEquiv k A M).toLinearMap.comp (algebraBoundary k A M 1) =
      ((KaehlerDifferential.Hochschild.boundaryTwo k A).lTensor M).comp
        (algebraTwoTensorEquiv k A M).toLinearMap := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  apply LinearMap.restrictScalars_injective k
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.coe_coe]
  have hb (z : M ⊗[k] TensorPower k 2 A) : algebraBoundary k A M 1 z =
      (ModuleCat.Algebra.Hochschild.boundary k A M 1).hom z := by
    have h : ((chainComplex k A M).d 2 1).hom = (ModuleCat.Algebra.Hochschild.boundary k A M 1).hom :=
      congrArg ModuleCat.Hom.hom (ModuleCat.Algebra.Hochschild.chainComplex_d k A M 1)
    exact congrArg (fun f : (M ⊗[k] TensorPower k 2 A) →ₗ[k] M ⊗[k] TensorPower k 1 A => f z) h
  rw [hb, ModuleCat.Algebra.Hochschild.boundary_tprod, Fin.sum_univ_succ, Fin.sum_univ_castSucc,
    ← add_assoc]
  simp only [ModuleCat.Algebra.Hochschild.faceValue, Fin.cases_zero, Fin.cases_succ,
    Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_zero, pow_zero, one_smul,
    Fin.val_succ, Fin.val_castSucc, Fin.val_last, opModule_smul, MulOpposite.unop_op]
  simp only [map_add, map_sum, map_zsmul, Fin.sum_univ_one,
    algebraOneTensorEquiv_tprod, algebraTwoTensorEquiv_tprod,
    LinearMap.lTensor_tmul, KaehlerDifferential.Hochschild.boundaryTwo_tmul,
    Fin.val_zero, pow_one, neg_one_smul,
    (show (-1 : ℤ) ^ 2 = 1 by norm_num), one_smul, ← sub_eq_add_neg]
  simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_coe, algebraTwoTensorEquiv_tprod,
    LinearMap.lTensor_tmul, KaehlerDifferential.Hochschild.boundaryTwo_tmul,
    ModuleCat.Algebra.Hochschild.hochschildDropFirst,
    ModuleCat.Algebra.Hochschild.hochschildDropLast,
    ModuleCat.Algebra.Hochschild.hochschildMulAdjacent, if_pos rfl,
    if_true, Nat.zero_add, pow_one, neg_one_smul, TensorProduct.neg_tmul]
  have hr := congrArg ((KaehlerDifferential.Hochschild.boundaryTwo k A).lTensor M)
    (algebraTwoTensorEquiv_tprod k A M m a)
  simp only [LinearMap.lTensor_tmul, KaehlerDifferential.Hochschild.boundaryTwo_tmul] at hr
  rw [hr]
  change ((a 0 • m) ⊗ₜ[A] ((1 : A) ⊗ₜ[k] a 1)) -
      (m ⊗ₜ[A] ((1 : A) ⊗ₜ[k] (a 0 * a 1))) +
        ((a 1 • m) ⊗ₜ[A] ((1 : A) ⊗ₜ[k] a 0)) =
    m ⊗ₜ[A] (((1 : A) * a 0) ⊗ₜ[k] a 1 -
      ((1 : A) ⊗ₜ[k] (a 0 * a 1)) + ((a 1 * 1) ⊗ₜ[k] a 0))
  simp only [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
    one_mul, mul_one, TensorProduct.tmul_add, TensorProduct.tmul_sub]

/-- The original representative m⊗a maps to m tensor_A da in the native Kähler module. -/
def algebraOneToKaehler :
    M ⊗[k] TensorPower k 1 A →ₗ[A] M ⊗[A] KaehlerDifferential k A :=
  ((KaehlerDifferential.D k A).tensorProductTo.lTensor M).comp
    (algebraOneTensorEquiv k A M).toLinearMap

/-- The representative map retains the original coefficient and native universal differential. -/
theorem algebraOneToKaehler_tprod (m : M) (a : Fin 1 → A) :
    algebraOneToKaehler k A M (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[A] KaehlerDifferential.D k A (a 0) := by
  simp only [algebraOneToKaehler, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_coe, algebraOneTensorEquiv_tprod,
    LinearMap.lTensor_tmul, Derivation.tensorProductTo_tmul, one_smul]

/-- Actual right exactness of native tensor transports the Kähler
presentation to the original arbitrary coefficient boundary. -/
theorem algebraBoundary_two_exact :
    Function.Exact (algebraBoundary k A M 1) (algebraOneToKaehler k A M) := by
  have h : Function.Exact ((KaehlerDifferential.Hochschild.boundaryTwo k A).lTensor M)
      ((KaehlerDifferential.D k A).tensorProductTo.lTensor M) :=
    _root_.lTensor_exact (R := A) (f := KaehlerDifferential.Hochschild.boundaryTwo k A)
      (g := (KaehlerDifferential.D k A).tensorProductTo) M
      (KaehlerDifferential.Hochschild.boundaryTwo_exact k A)
      (KaehlerDifferential.tensorProductTo_surjective k A)
  intro x
  constructor
  · intro hx
    have hx' : (KaehlerDifferential.D k A).tensorProductTo.lTensor M
        (algebraOneTensorEquiv k A M x) = 0 := hx
    obtain ⟨y, hy⟩ := (h (algebraOneTensorEquiv k A M x)).mp hx'
    refine ⟨(algebraTwoTensorEquiv k A M).symm y, ?_⟩
    apply (algebraOneTensorEquiv k A M).injective
    have hb := DFunLike.congr_fun (algebraBoundary_two_tensor k A M)
      ((algebraTwoTensorEquiv k A M).symm y)
    change algebraOneTensorEquiv k A M
        (algebraBoundary k A M 1 ((algebraTwoTensorEquiv k A M).symm y)) =
      (KaehlerDifferential.Hochschild.boundaryTwo k A).lTensor M
        (algebraTwoTensorEquiv k A M ((algebraTwoTensorEquiv k A M).symm y)) at hb
    rw [LinearEquiv.apply_symm_apply] at hb
    exact hb.trans hy
  · rintro ⟨z, rfl⟩
    change (KaehlerDifferential.D k A).tensorProductTo.lTensor M
      (algebraOneTensorEquiv k A M (algebraBoundary k A M 1 z)) = 0
    have hb := DFunLike.congr_fun (algebraBoundary_two_tensor k A M) z
    change algebraOneTensorEquiv k A M (algebraBoundary k A M 1 z) =
      (KaehlerDifferential.Hochschild.boundaryTwo k A).lTensor M
        (algebraTwoTensorEquiv k A M z) at hb
    rw [hb]
    exact (h _).mpr ⟨algebraTwoTensorEquiv k A M z, rfl⟩

/-- The representative map is surjective without coefficient flatness. -/
theorem algebraOneToKaehler_surjective : Function.Surjective (algebraOneToKaehler k A M) :=
  (LinearMap.lTensor_surjective M (KaehlerDifferential.tensorProductTo_surjective k A)).comp
    (algebraOneTensorEquiv k A M).surjective

/-- Original degree-one proper quotient representatives map through the original Kähler representative map. -/
def algebraPositiveOneToKaehler :
    ((M ⊗[k] TensorPower k 1 A) ⧸ algebraPositiveRelations k A M 1) →ₗ[A]
      M ⊗[A] KaehlerDifferential k A :=
  (algebraPositiveRelations k A M 1).liftQ (algebraOneToKaehler k A M) (by
    rw [algebraPositiveRelations_low k A M 1 (by omega)]
    exact bot_le)

/-- The proper quotient uses the original representative map. -/
theorem algebraPositiveOneToKaehler_mkQ (x : M ⊗[k] TensorPower k 1 A) :
    algebraPositiveOneToKaehler k A M ((algebraPositiveRelations k A M 1).mkQ x) =
      algebraOneToKaehler k A M x := rfl

/-- The same original Kähler representative in the chain category's full universe. -/
def algebraPositiveOneToKaehlerLift :
    ((M ⊗[k] TensorPower k 1 A) ⧸ algebraPositiveRelations k A M 1) →ₗ[A]
      ULift.{u} (M ⊗[A] KaehlerDifferential k A) :=
  (ULift.moduleEquiv : ULift.{u} (M ⊗[A] KaehlerDifferential k A) ≃ₗ[A]
    M ⊗[A] KaehlerDifferential k A).symm.toLinearMap.comp (algebraPositiveOneToKaehler k A M)

/-- Lifting the categorical target retains every original quotient representative. -/
theorem algebraPositiveOneToKaehlerLift_mkQ (x : M ⊗[k] TensorPower k 1 A) :
    algebraPositiveOneToKaehlerLift k A M ((algebraPositiveRelations k A M 1).mkQ x) =
      ULift.up (algebraOneToKaehler k A M x) := rfl

/-- The source short complex is the native degree-one short complex of the original proper quotient. -/
def algebraPositiveOneShortComplex : ShortComplex (ModuleCat.{max u v w} A) :=
  (algebraPositiveQuotientComplex k A M).sc 1

/-- Its second map is the original symmetric degree-one zero boundary. -/
theorem algebraPositiveOneShortComplex_g : (algebraPositiveOneShortComplex k A M).g = 0 := by
  let K := algebraPositiveQuotientComplex k A M
  have h10 : (ComplexShape.down ℕ).Rel 1 0 := rfl
  have hz : algebraBoundary k A M 0 = 0 := by
    apply LinearMap.restrictScalars_injective k
    change ((chainComplex k A M).d 1 0).hom = 0
    rw [boundary_one_zero, ModuleCat.hom_zero]
  have hd : K.d 1 0 = 0 := by
    have hp : K.d 1 0 = algebraPositiveQuotientDifferential k A M 0 :=
      ChainComplex.of_d (fun n => ModuleCat.of A
        ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n))
        (algebraPositiveQuotientDifferential k A M) 0
    rw [hp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    refine Quotient.inductionOn' y ?_
    intro x
    change (algebraPositiveRelations k A M 0).mkQ (algebraBoundary k A M 0 x) = 0
    rw [hz, LinearMap.zero_apply, map_zero]
  change K.dFrom 1 = 0
  apply (cancel_mono (K.xNextIso h10).hom).1
  rw [HomologicalComplex.dFrom_comp_xNextIso, hd, zero_comp]

/-- The proper b₂ and original Kähler representative form an exact pair. -/
theorem algebraPositiveOneToKaehler_exact :
    Function.Exact (algebraPositiveOneShortComplex k A M).f.hom
      (algebraPositiveOneToKaehler k A M) := by
  let K := algebraPositiveQuotientComplex k A M
  let D := algebraPositiveQuotientDifferential k A M 1
  have h21 : (ComplexShape.down ℕ).Rel 2 1 := rfl
  let e : (algebraPositiveOneShortComplex k A M).X₁ ≅ K.X 2 := K.xPrevIso h21
  have hd : K.d 2 1 = D := by
    exact ChainComplex.of_d (fun n => ModuleCat.of A
      ((M ⊗[k] TensorPower k n A) ⧸ algebraPositiveRelations k A M n))
      (algebraPositiveQuotientDifferential k A M) 1
  have hi : e.inv ≫ (algebraPositiveOneShortComplex k A M).f = D :=
    (K.xPrevIso_comp_dTo h21).trans hd
  have hf : (algebraPositiveOneShortComplex k A M).f = e.hom ≫ D :=
    (K.dTo_eq h21).trans (congrArg (fun f => e.hom ≫ f) hd)
  have hD : Function.Exact D.hom (algebraPositiveOneToKaehler k A M) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (algebraPositiveRelations k A M 1) y
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := (algebraBoundary_two_exact k A M x).mp hx
      refine ⟨(algebraPositiveRelations k A M 2).mkQ z, ?_⟩
      change (algebraPositiveRelations k A M 1).mkQ (algebraBoundary k A M 1 z) =
        (algebraPositiveRelations k A M 1).mkQ x
      exact congrArg (algebraPositiveRelations k A M 1).mkQ hz
    · rintro ⟨z, hz⟩
      obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective (algebraPositiveRelations k A M 2) z
      rw [← hz]
      change algebraOneToKaehler k A M (algebraBoundary k A M 1 t) = 0
      exact (algebraBoundary_two_exact k A M _).mpr ⟨t, rfl⟩
  intro y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := (hD y).mp hy
    refine ⟨e.inv.hom z, ?_⟩
    have hp := congrArg (fun f : K.X 2 ⟶ K.X 1 => f.hom z) hi
    exact hp.trans hz
  · rintro ⟨z, rfl⟩
    have hp := congrArg (fun f : (algebraPositiveOneShortComplex k A M).X₁ ⟶ K.X 1 => f.hom z) hf
    exact (hD _).mpr ⟨e.hom z, hp.symm⟩

/-- Surjectivity of the quotient representative map is inherited from the tensor map. -/
theorem algebraPositiveOneToKaehler_surjective :
    Function.Surjective (algebraPositiveOneToKaehler k A M) := by
  intro z
  obtain ⟨x, hx⟩ := algebraOneToKaehler_surjective k A M z
  exact ⟨(algebraPositiveRelations k A M 1).mkQ x, hx⟩

/-- The full-universe representative remains an exact cokernel of the degree-two map. -/
theorem algebraPositiveOneToKaehlerLift_exact :
    Function.Exact (algebraPositiveOneShortComplex k A M).f.hom
      (algebraPositiveOneToKaehlerLift k A M) := by
  intro y
  rw [← algebraPositiveOneToKaehler_exact k A M y]
  change ULift.up (algebraPositiveOneToKaehler k A M y) = ULift.up 0 ↔ _
  exact ULift.up_inj

/-- The whole-module lift is surjective without coefficient hypotheses. -/
theorem algebraPositiveOneToKaehlerLift_surjective :
    Function.Surjective (algebraPositiveOneToKaehlerLift k A M) := by
  rintro ⟨z⟩
  obtain ⟨x, hx⟩ := algebraPositiveOneToKaehler_surjective k A M z
  exact ⟨x, congrArg ULift.up hx⟩

/-- The proper degree-two boundary is killed by the differential representative. -/
@[reassoc]
theorem algebraPositiveOne_boundary_toKaehler :
    (algebraPositiveOneShortComplex k A M).f ≫ ModuleCat.ofHom (algebraPositiveOneToKaehlerLift k A M) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (algebraPositiveOneToKaehlerLift_exact k A M _).mpr ⟨x, rfl⟩

/-- The native cokernel cofork of the original proper b₂ with its original Kähler map. -/
def algebraPositiveOneCokernelCofork : CokernelCofork (algebraPositiveOneShortComplex k A M).f :=
  CokernelCofork.ofπ (ModuleCat.ofHom (algebraPositiveOneToKaehlerLift k A M))
    (algebraPositiveOne_boundary_toKaehler k A M)

/-- The cofork is a native cokernel by the proved arbitrary-coefficient exact tensor presentation. -/
def algebraPositiveOneCokernelIsColimit : IsColimit (algebraPositiveOneCokernelCofork k A M) :=
  ModuleCat.isColimitCokernelCofork (algebraPositiveOneShortComplex k A M).f
    (ModuleCat.ofHom (algebraPositiveOneToKaehlerLift k A M))
    (algebraPositiveOneToKaehlerLift_exact k A M) (algebraPositiveOneToKaehlerLift_surjective k A M)

/-- Native homology data from the cokernel and the original zero b₁. -/
def algebraPositiveOneHomologyData : (algebraPositiveOneShortComplex k A M).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
    (algebraPositiveOneShortComplex k A M) (algebraPositiveOneShortComplex_g k A M)
    (algebraPositiveOneCokernelCofork k A M) (algebraPositiveOneCokernelIsColimit k A M)

/-- The degree-one comparison targets the whole-module lift of the original Kähler tensor. -/
def algebraPositiveHomologyOneIsoKaehler :
    (algebraPositiveQuotientComplex k A M).homology 1 ≅
      ModuleCat.of A (ULift.{u} (M ⊗[A] KaehlerDifferential k A)) :=
  (algebraPositiveOneHomologyData k A M).homologyIso

/-- The same comparison returns the original coefficient Kähler tensor across independent worlds. -/
def algebraPositiveHomologyOneEquivKaehler :
    (algebraPositiveQuotientComplex k A M).homology 1 ≃ₗ[A] M ⊗[A] KaehlerDifferential k A :=
  (algebraPositiveHomologyOneIsoKaehler k A M).toLinearEquiv.trans ULift.moduleEquiv

/-- The categorical comparison lifts precisely the original-world value. -/
theorem algebraPositiveHomologyOneIsoKaehler_hom_up (x : (algebraPositiveQuotientComplex k A M).homology 1) :
    (algebraPositiveHomologyOneIsoKaehler k A M).hom.hom x =
      ULift.up (algebraPositiveHomologyOneEquivKaehler k A M x) := rfl

/-- Its inverse on a lifted original tensor is the original-world inverse equivalence. -/
theorem algebraPositiveHomologyOneIsoKaehler_inv_up (x : M ⊗[A] KaehlerDifferential k A) :
    (algebraPositiveHomologyOneIsoKaehler k A M).inv.hom (ULift.up x) =
      (algebraPositiveHomologyOneEquivKaehler k A M).symm x := rfl

/-- The independently specified native degree-one homology class of an original quotient representative. -/
def algebraPositiveHomologyOneClass :
    (algebraPositiveQuotientComplex k A M).X 1 ⟶ (algebraPositiveQuotientComplex k A M).homology 1 :=
  (algebraPositiveOneShortComplex k A M).liftCycles (𝟙 _)
    (by rw [Category.id_comp, algebraPositiveOneShortComplex_g]) ≫
      (algebraPositiveOneShortComplex k A M).homologyπ

/-- The homology comparison sends the original homology class
through the original Kähler representative map. -/
@[reassoc]
theorem algebraPositiveHomologyOneClass_toKaehler :
    algebraPositiveHomologyOneClass k A M ≫ (algebraPositiveHomologyOneIsoKaehler k A M).hom =
      ModuleCat.ofHom (algebraPositiveOneToKaehlerLift k A M) := by
  let S := algebraPositiveOneShortComplex k A M
  let h : S.LeftHomologyData := algebraPositiveOneHomologyData k A M
  let hk : (𝟙 S.X₂) ≫ S.g = 0 := by
    rw [Category.id_comp]
    exact algebraPositiveOneShortComplex_g k A M
  change (S.liftCycles (𝟙 _) hk ≫ S.homologyπ) ≫ h.homologyIso.hom = h.π
  rw [Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    ← Category.assoc, ShortComplex.LeftHomologyData.liftCycles_comp_cyclesIso_hom]
  have hl : h.liftK (𝟙 S.X₂) hk = 𝟙 S.X₂ := by
    exact ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork_liftK S
      (algebraPositiveOneShortComplex_g k A M) (algebraPositiveOneCokernelCofork k A M)
      (algebraPositiveOneCokernelIsColimit k A M) (𝟙 S.X₂)
  rw [hl]
  exact Category.id_comp h.π

/-- The original pure representative class maps to the original coefficient tensor the native differential da. -/
theorem algebraPositiveHomologyOneIsoKaehler_class_tprod (m : M) (a : Fin 1 → A) :
    (algebraPositiveHomologyOneIsoKaehler k A M).hom.hom
        ((algebraPositiveHomologyOneClass k A M).hom
          ((algebraPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      ULift.up (m ⊗ₜ[A] KaehlerDifferential.D k A (a 0)) := by
  have h := ConcreteCategory.congr_hom (algebraPositiveHomologyOneClass_toKaehler k A M)
    ((algebraPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  exact h.trans (congrArg ULift.up (algebraOneToKaehler_tprod k A M m a))

/-- The original-world equivalence retains the original coefficient and universal differential value. -/
theorem algebraPositiveHomologyOneEquivKaehler_class_tprod (m : M) (a : Fin 1 → A) :
    algebraPositiveHomologyOneEquivKaehler k A M
      ((algebraPositiveHomologyOneClass k A M).hom
        ((algebraPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      m ⊗ₜ[A] KaehlerDifferential.D k A (a 0) := by
  exact congrArg ULift.down (algebraPositiveHomologyOneIsoKaehler_class_tprod k A M m a)

section CoefficientNaturality

variable {N : Type w} [AddCommGroup N] [Module k N] [Module A N]
  [SMulCommClass k A N] [IsScalarTower k A N]

/-- The original coefficient tensor map transported through whole-module lifts on both ends. -/
def algebraKaehlerCoefficientLift (f : M →ₗ[A] N) :
    ULift.{u} (M ⊗[A] KaehlerDifferential k A) →ₗ[A] ULift.{u} (N ⊗[A] KaehlerDifferential k A) :=
  (ULift.moduleEquiv : ULift.{u} (N ⊗[A] KaehlerDifferential k A) ≃ₗ[A]
    N ⊗[A] KaehlerDifferential k A).symm.toLinearMap.comp
      ((TensorProduct.map f (LinearMap.id : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A)).comp
        (ULift.moduleEquiv : ULift.{u} (M ⊗[A] KaehlerDifferential k A) ≃ₗ[A]
          M ⊗[A] KaehlerDifferential k A).toLinearMap)

/-- The native Kähler representative is natural in the original A-linear coefficient map. -/
theorem algebraOneToKaehler_coefficient (f : M →ₗ[A] N) :
    (TensorProduct.map f (LinearMap.id : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A)).comp
        (algebraOneToKaehler k A M) =
      (algebraOneToKaehler k A N).comp (algebraCoefficientLevelMap k A f 1) := by
  apply LinearMap.restrictScalars_injective k
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, algebraOneToKaehler_tprod,
    algebraCoefficientLevelMap_tmul, TensorProduct.map_tmul, LinearMap.id_apply]

/-- The quotient Kähler map retains the original coefficient naturality square. -/
@[reassoc]
theorem algebraPositiveOneToKaehler_coefficient (f : M →ₗ[A] N) :
    ModuleCat.ofHom (algebraPositiveOneToKaehlerLift k A M) ≫
        ModuleCat.ofHom (algebraKaehlerCoefficientLift k A M f) =
      (algebraPositiveCoefficientMap k A f).f 1 ≫ ModuleCat.ofHom (algebraPositiveOneToKaehlerLift k A N) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  refine Quotient.inductionOn' y ?_
  intro x
  change ULift.up ((TensorProduct.map f
    (LinearMap.id : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A))
      (algebraOneToKaehler k A M x)) =
    ULift.up (algebraOneToKaehler k A N (algebraCoefficientLevelMap k A f 1 x))
  exact congrArg ULift.up (DFunLike.congr_fun (algebraOneToKaehler_coefficient k A M f) x)

/-- Actual native homology map data from the original coefficient map and its
proved original Kähler representative square. -/
def algebraPositiveOneHomologyMapData (f : M →ₗ[A] N) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{max u v w} A) (ComplexShape.down ℕ) 1).map
        (algebraPositiveCoefficientMap k A f))
      (algebraPositiveOneHomologyData k A M) (algebraPositiveOneHomologyData k A N) where
  φK := (algebraPositiveCoefficientMap k A f).f 1
  φH := ModuleCat.ofHom (algebraKaehlerCoefficientLift k A M f)
  commi := by
    change (algebraPositiveCoefficientMap k A f).f 1 ≫ 𝟙 _ =
      𝟙 _ ≫ (algebraPositiveCoefficientMap k A f).f 1
    rw [Category.comp_id, Category.id_comp]
  commf' := by
    exact ((algebraPositiveCoefficientMap k A f).comm_to 1).symm
  commπ := algebraPositiveOneToKaehler_coefficient k A M f

/-- The all-k degree-one proper-shuffle homology isomorphism is natural in
arbitrary original A-linear coefficient maps; the target keeps M first. -/
@[reassoc]
theorem algebraPositiveHomologyOneIsoKaehler_coefficient (f : M →ₗ[A] N) :
    HomologicalComplex.homologyMap (algebraPositiveCoefficientMap k A f) 1 ≫
        (algebraPositiveHomologyOneIsoKaehler k A N).hom =
      (algebraPositiveHomologyOneIsoKaehler k A M).hom ≫
        ModuleCat.ofHom (algebraKaehlerCoefficientLift k A M f) :=
  (algebraPositiveOneHomologyMapData k A M f).homologyMap_comm

end CoefficientNaturality

end ModuleCat.Algebra.Hochschild.Symmetric
