/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficientMaps
public import MathlibExt.RingTheory.Kaehler.HochschildPresentation
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.NormNum

/-!
# Degree-one proper-shuffle homology and coefficient Kähler differentials

Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module. Both-
positive shuffle relations vanish in degree one. The degree-two Hochschild boundary presents M
⊗[A] Ω¹(A/k), so H₁ of the proper-shuffle quotient is A-linearly isomorphic to that module.
The class of m ⊗ a maps to m ⊗ da. This uses no rational scalar structure, and it is natural
in A-linear coefficient maps.

For degree-one Harrison/Kähler comparisons, see J.-L. Loday, Cyclic Homology, 2nd ed., Chapter
4; the coefficient presentation uses tensor right exactness.
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

/-- Degree-one coefficient chains in the balanced Kähler presentation.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, M ⊗[k] A⊗1 is
A-linearly equivalent to M ⊗[A] (A ⊗[k] A). -/
def algebraOneTensorEquiv :
    M ⊗[k] TensorPower k 1 A ≃ₗ[A] M ⊗[A] (A ⊗[k] A) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A M)
    (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 => A) 0)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k A A M A).symm

/-- The degree-one word coordinate of the Kähler presentation.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, m ⊗ tprod(a)
maps to m ⊗[A] (1_A ⊗[k] a₀). -/
theorem algebraOneTensorEquiv_tprod (m : M) (a : Fin 1 → A) :
    algebraOneTensorEquiv k A M (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[A] ((1 : A) ⊗ₜ[k] a 0) := by
  simp only [algebraOneTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.subsingletonEquiv_apply_tprod,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]

/-- Degree-two coefficient chains in the balanced Kähler boundary presentation.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, M ⊗[k] A⊗2 is
A-linearly equivalent to M ⊗[A] (A ⊗[k] (A ⊗[k] A)). -/
def algebraTwoTensorEquiv :
    M ⊗[k] TensorPower k 2 A ≃ₗ[A] M ⊗[A] (A ⊗[k] (A ⊗[k] A)) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A M)
    ((TensorPower.consEquiv k A 1).symm.trans
      (TensorProduct.congr (LinearEquiv.refl k A)
        (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Fin 1 => A) 0)))).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k A A M (A ⊗[k] A)).symm

/-- The degree-two word coordinate of the Kähler boundary presentation.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, m ⊗ tprod(a)
maps to m ⊗[A] (1_A ⊗[k] (a₀ ⊗[k] a₁)). -/
theorem algebraTwoTensorEquiv_tprod (m : M) (a : Fin 2 → A) :
    algebraTwoTensorEquiv k A M (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[A] ((1 : A) ⊗ₜ[k] (a 0 ⊗ₜ[k] a 1)) := by
  simp only [algebraTwoTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    TensorPower.consEquiv_symm_tprod, TensorProduct.congr_tmul,
    PiTensorProduct.subsingletonEquiv_apply_tprod,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  rfl

/-- The coefficient Hochschild degree-two boundary equals the tensor Kähler boundary.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the one- and
two-word coordinate equivalences identify b₂ with M ⊗[A]
KaehlerDifferential.Hochschild.boundaryTwo. -/
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

/-- The coefficient universal-differential map from degree-one chains.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, m ⊗ a maps
A-linearly to m ⊗[A] da. -/
def algebraOneToKaehler :
    M ⊗[k] TensorPower k 1 A →ₗ[A] M ⊗[A] KaehlerDifferential k A :=
  ((KaehlerDifferential.D k A).tensorProductTo.lTensor M).comp
    (algebraOneTensorEquiv k A M).toLinearMap

/-- The universal-differential value of a pure degree-one coefficient word.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
algebraOneToKaehler(m ⊗ tprod(a))=m ⊗[A] D(a₀). -/
theorem algebraOneToKaehler_tprod (m : M) (a : Fin 1 → A) :
    algebraOneToKaehler k A M (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[A] KaehlerDifferential.D k A (a 0) := by
  simp only [algebraOneToKaehler, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_coe, algebraOneTensorEquiv_tprod,
    LinearMap.lTensor_tmul, Derivation.tensorProductTo_tmul, one_smul]

/-- The degree-two boundary presents the kernel of coefficient differentials.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
image(b₂)=ker(algebraOneToKaehler). This uses tensor right exactness for arbitrary M. -/
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

/-- Degree-one coefficient words surject onto coefficient Kähler differentials.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
algebraOneToKaehler is surjective onto M ⊗[A] Ω¹(A/k). -/
theorem algebraOneToKaehler_surjective : Function.Surjective (algebraOneToKaehler k A M) :=
  (LinearMap.lTensor_surjective M (KaehlerDifferential.tensorProductTo_surjective k A)).comp
    (algebraOneTensorEquiv k A M).surjective

/-- The universal-differential map from the degree-one proper quotient.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, descend m ⊗ a
↦ m ⊗ da through the degree-one proper relation module, which is zero. -/
def algebraPositiveOneToKaehler :
    ((M ⊗[k] TensorPower k 1 A) ⧸ algebraPositiveRelations k A M 1) →ₗ[A]
      M ⊗[A] KaehlerDifferential k A :=
  (algebraPositiveRelations k A M 1).liftQ (algebraOneToKaehler k A M) (by
    rw [algebraPositiveRelations_low k A M 1 (by omega)]
    exact bot_le)

/-- The proper quotient differential map retains a degree-one representative.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
algebraPositiveOneToKaehler([x])=algebraOneToKaehler(x). -/
theorem algebraPositiveOneToKaehler_mkQ (x : M ⊗[k] TensorPower k 1 A) :
    algebraPositiveOneToKaehler k A M ((algebraPositiveRelations k A M 1).mkQ x) =
      algebraOneToKaehler k A M x := rfl

/-- The lifted coefficient differential map from the degree-one proper quotient.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the target is
ULift(M ⊗[A] Ω¹(A/k)), retaining independent carrier universes. -/
def algebraPositiveOneToKaehlerLift :
    ((M ⊗[k] TensorPower k 1 A) ⧸ algebraPositiveRelations k A M 1) →ₗ[A]
      ULift.{u} (M ⊗[A] KaehlerDifferential k A) :=
  (ULift.moduleEquiv : ULift.{u} (M ⊗[A] KaehlerDifferential k A) ≃ₗ[A]
    M ⊗[A] KaehlerDifferential k A).symm.toLinearMap.comp (algebraPositiveOneToKaehler k A M)

/-- The lifted differential value of a proper quotient representative.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, [x] maps to
ULift.up(algebraOneToKaehler(x)). -/
theorem algebraPositiveOneToKaehlerLift_mkQ (x : M ⊗[k] TensorPower k 1 A) :
    algebraPositiveOneToKaehlerLift k A M ((algebraPositiveRelations k A M 1).mkQ x) =
      ULift.up (algebraOneToKaehler k A M x) := rfl

/-- The short complex computing proper-shuffle homology in degree one.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, use degrees
two, one and zero of algebraPositiveQuotientComplex; its outgoing degree-one boundary is zero. -/
def algebraPositiveOneShortComplex : ShortComplex (ModuleCat.{max u v w} A) :=
  (algebraPositiveQuotientComplex k A M).sc 1

/-- The outgoing map of the degree-one proper homology short complex is zero.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
algebraPositiveOneShortComplex.g is the symmetric boundary b₁=0. -/
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

/-- Exactness of the proper degree-one differential presentation.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the image of
the incoming proper boundary equals the kernel of algebraPositiveOneToKaehler. -/
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

/-- The proper degree-one quotient surjects onto coefficient differentials.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
algebraPositiveOneToKaehler maps onto M ⊗[A] Ω¹(A/k). -/
theorem algebraPositiveOneToKaehler_surjective :
    Function.Surjective (algebraPositiveOneToKaehler k A M) := by
  intro z
  obtain ⟨x, hx⟩ := algebraOneToKaehler_surjective k A M z
  exact ⟨(algebraPositiveRelations k A M 1).mkQ x, hx⟩

/-- Exactness of the lifted proper degree-one differential presentation.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the image of the incoming proper boundary equals the kernel of algebraPositiveOneToKaehlerLift. -/
theorem algebraPositiveOneToKaehlerLift_exact :
    Function.Exact (algebraPositiveOneShortComplex k A M).f.hom
      (algebraPositiveOneToKaehlerLift k A M) := by
  intro y
  rw [← algebraPositiveOneToKaehler_exact k A M y]
  change ULift.up (algebraPositiveOneToKaehler k A M y) = ULift.up 0 ↔ _
  exact ULift.up_inj

/-- Surjectivity of the lifted proper differential map.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, every element
of ULift(M ⊗[A] Ω¹(A/k)) comes from the proper degree-one quotient. -/
theorem algebraPositiveOneToKaehlerLift_surjective :
    Function.Surjective (algebraPositiveOneToKaehlerLift k A M) := by
  rintro ⟨z⟩
  obtain ⟨x, hx⟩ := algebraPositiveOneToKaehler_surjective k A M z
  exact ⟨x, congrArg ULift.up hx⟩

/-- The proper degree-two boundary is annihilated by lifted coefficient differentials.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the incoming
map of algebraPositiveOneShortComplex followed by algebraPositiveOneToKaehlerLift is zero. -/
@[reassoc]
theorem algebraPositiveOne_boundary_toKaehler :
    (algebraPositiveOneShortComplex k A M).f ≫ ModuleCat.ofHom (algebraPositiveOneToKaehlerLift k A M) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (algebraPositiveOneToKaehlerLift_exact k A M _).mpr ⟨x, rfl⟩

/-- The coefficient Kähler cokernel cofork for proper degree-one chains.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the incoming
proper boundary has cofork projection algebraPositiveOneToKaehlerLift. -/
def algebraPositiveOneCokernelCofork : CokernelCofork (algebraPositiveOneShortComplex k A M).f :=
  CokernelCofork.ofπ (ModuleCat.ofHom (algebraPositiveOneToKaehlerLift k A M))
    (algebraPositiveOne_boundary_toKaehler k A M)

/-- The coefficient differential cofork is the cokernel of the incoming proper boundary.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
algebraPositiveOneCokernelCofork satisfies the cokernel universal property. -/
def algebraPositiveOneCokernelIsColimit : IsColimit (algebraPositiveOneCokernelCofork k A M) :=
  ModuleCat.isColimitCokernelCofork (algebraPositiveOneShortComplex k A M).f
    (ModuleCat.ofHom (algebraPositiveOneToKaehlerLift k A M))
    (algebraPositiveOneToKaehlerLift_exact k A M) (algebraPositiveOneToKaehlerLift_surjective k A M)

/-- The coefficient differential model of proper degree-one homology.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the zero
outgoing boundary and the Kähler cokernel give LeftHomologyData for the degree-one short
complex. -/
def algebraPositiveOneHomologyData : (algebraPositiveOneShortComplex k A M).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
    (algebraPositiveOneShortComplex k A M) (algebraPositiveOneShortComplex_g k A M)
    (algebraPositiveOneCokernelCofork k A M) (algebraPositiveOneCokernelIsColimit k A M)

/-- Proper-shuffle H₁ is the lifted coefficient Kähler module.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M,
H₁(algebraPositiveQuotientComplex) ≅ ULift(M ⊗[A] Ω¹(A/k)) in ModuleCat A. -/
def algebraPositiveHomologyOneIsoKaehler :
    (algebraPositiveQuotientComplex k A M).homology 1 ≅
      ModuleCat.of A (ULift.{u} (M ⊗[A] KaehlerDifferential k A)) :=
  (algebraPositiveOneHomologyData k A M).homologyIso

/-- The coefficient Kähler equivalence for proper H₁ in the unlifted carrier.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the same
degree-one homology is A-linearly equivalent to M ⊗[A] Ω¹(A/k). -/
def algebraPositiveHomologyOneEquivKaehler :
    (algebraPositiveQuotientComplex k A M).homology 1 ≃ₗ[A] M ⊗[A] KaehlerDifferential k A :=
  (algebraPositiveHomologyOneIsoKaehler k A M).toLinearEquiv.trans ULift.moduleEquiv

/-- The forward lifted H₁ comparison agrees with its unlifted equivalence.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the
isomorphism sends x to ULift.up(algebraPositiveHomologyOneEquivKaehler(x)). -/
theorem algebraPositiveHomologyOneIsoKaehler_hom_up (x : (algebraPositiveQuotientComplex k A M).homology 1) :
    (algebraPositiveHomologyOneIsoKaehler k A M).hom.hom x =
      ULift.up (algebraPositiveHomologyOneEquivKaehler k A M x) := rfl

/-- The inverse lifted H₁ comparison agrees with the coefficient differential equivalence.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the inverse
on ULift.up(x) is the inverse of algebraPositiveHomologyOneEquivKaehler on x. -/
theorem algebraPositiveHomologyOneIsoKaehler_inv_up (x : M ⊗[A] KaehlerDifferential k A) :
    (algebraPositiveHomologyOneIsoKaehler k A M).inv.hom (ULift.up x) =
      (algebraPositiveHomologyOneEquivKaehler k A M).symm x := rfl

/-- The class map from proper degree-one chains to their homology.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, every degree-
one proper quotient chain is a cycle because b₁=0, giving this homology class map. -/
def algebraPositiveHomologyOneClass :
    (algebraPositiveQuotientComplex k A M).X 1 ⟶ (algebraPositiveQuotientComplex k A M).homology 1 :=
  (algebraPositiveOneShortComplex k A M).liftCycles (𝟙 _)
    (by rw [Category.id_comp, algebraPositiveOneShortComplex_g]) ≫
      (algebraPositiveOneShortComplex k A M).homologyπ

/-- The degree-one class map followed by the Kähler comparison.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, class
followed by algebraPositiveHomologyOneIsoKaehler is algebraPositiveOneToKaehlerLift. -/
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

/-- The lifted H₁ comparison on a pure coefficient tensor class.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the homology
class of [m ⊗ tprod(a)] maps to ULift.up(m ⊗[A] D(a₀)). -/
theorem algebraPositiveHomologyOneIsoKaehler_class_tprod (m : M) (a : Fin 1 → A) :
    (algebraPositiveHomologyOneIsoKaehler k A M).hom.hom
        ((algebraPositiveHomologyOneClass k A M).hom
          ((algebraPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      ULift.up (m ⊗ₜ[A] KaehlerDifferential.D k A (a 0)) := by
  have h := ConcreteCategory.congr_hom (algebraPositiveHomologyOneClass_toKaehler k A M)
    ((algebraPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  exact h.trans (congrArg ULift.up (algebraOneToKaehler_tprod k A M m a))

/-- The unlifted H₁ comparison on a pure coefficient tensor class.

For a commutative ring k, a commutative k-algebra A and a compatible A-module M, the homology
class of [m ⊗ tprod(a)] maps to m ⊗[A] D(a₀). -/
theorem algebraPositiveHomologyOneEquivKaehler_class_tprod (m : M) (a : Fin 1 → A) :
    algebraPositiveHomologyOneEquivKaehler k A M
      ((algebraPositiveHomologyOneClass k A M).hom
        ((algebraPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      m ⊗ₜ[A] KaehlerDifferential.D k A (a 0) := by
  exact congrArg ULift.down (algebraPositiveHomologyOneIsoKaehler_class_tprod k A M m a)

section CoefficientNaturality

variable {N : Type w} [AddCommGroup N] [Module k N] [Module A N]
  [SMulCommClass k A N] [IsScalarTower k A N]

/-- The lifted Kähler tensor map of an A-linear coefficient arrow.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, send
ULift.up(m ⊗ ω) to ULift.up(f(m) ⊗ ω). -/
def algebraKaehlerCoefficientLift (f : M →ₗ[A] N) :
    ULift.{u} (M ⊗[A] KaehlerDifferential k A) →ₗ[A] ULift.{u} (N ⊗[A] KaehlerDifferential k A) :=
  (ULift.moduleEquiv : ULift.{u} (N ⊗[A] KaehlerDifferential k A) ≃ₗ[A]
    N ⊗[A] KaehlerDifferential k A).symm.toLinearMap.comp
      ((TensorProduct.map f (LinearMap.id : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A)).comp
        (ULift.moduleEquiv : ULift.{u} (M ⊗[A] KaehlerDifferential k A) ≃ₗ[A]
          M ⊗[A] KaehlerDifferential k A).toLinearMap)

/-- Coefficient arrows commute with the degree-one universal-differential map.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, (f ⊗
id) ∘ algebraOneToKaehler_M = algebraOneToKaehler_N ∘ algebraCoefficientLevelMap(f,1). -/
theorem algebraOneToKaehler_coefficient (f : M →ₗ[A] N) :
    (TensorProduct.map f (LinearMap.id : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A)).comp
        (algebraOneToKaehler k A M) =
      (algebraOneToKaehler k A N).comp (algebraCoefficientLevelMap k A f 1) := by
  apply LinearMap.restrictScalars_injective k
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, algebraOneToKaehler_tprod,
    algebraCoefficientLevelMap_tmul, TensorProduct.map_tmul, LinearMap.id_apply]

/-- The proper degree-one Kähler presentation is natural in coefficients.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, the
lifted differential projection and algebraPositiveCoefficientMap(f) form the coefficient
tensor square. -/
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

/-- The degree-one proper homology map data of a coefficient arrow.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N, the
map on cycles is its proper degree-one coefficient component and the homology-model map is
algebraKaehlerCoefficientLift(f). -/
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

/-- The proper H₁ Kähler isomorphism is natural in A-linear coefficients.

For a commutative ring k, a commutative k-algebra A and a compatible A-linear f : M → N,
homologyMap(f,1) followed by the target Kähler comparison equals the source Kähler comparison
followed by the lifted map f ⊗ id. -/
@[reassoc]
theorem algebraPositiveHomologyOneIsoKaehler_coefficient (f : M →ₗ[A] N) :
    HomologicalComplex.homologyMap (algebraPositiveCoefficientMap k A f) 1 ≫
        (algebraPositiveHomologyOneIsoKaehler k A N).hom =
      (algebraPositiveHomologyOneIsoKaehler k A M).hom ≫
        ModuleCat.ofHom (algebraKaehlerCoefficientLift k A M f) :=
  (algebraPositiveOneHomologyMapData k A M f).homologyMap_comm

end CoefficientNaturality

end ModuleCat.Algebra.Hochschild.Symmetric
