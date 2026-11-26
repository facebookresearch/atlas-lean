/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.TorNaturality
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.RightHomologyZero
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ZeroClass

/-!
# Degree-zero Tor at lifted augmentation modules

Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). The lifted augmentation module T_H has scalar representatives
up(up(r)); its two lifts are kept distinct from the single lift in the augmentation module T.

The homology-to-Tor comparison followed by the derived-zero morphism sends the degree-zero
class of 1 ⊗ m to [m,up(up(1))] in N ⊗_U T_H. Cancelling the outer input lift recovers the
canonical coinvariant identification with N ⊗_U T. The derived-zero morphism at T_H is an
isomorphism, and is the forward map of the degree-zero Tor coordinates.
-/

@[expose] public section

noncomputable section

universe u v v' w z z'

open CategoryTheory MulOpposite
open scoped TensorProduct ModuleCat.Algebra

namespace ChevalleyEilenberg

attribute [local implicit_reducible] coefficientComplex
attribute [local instance] LieRing.ofAssociativeRing rightRegularLieRingModule rightRegularLieModule

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L

variable (N : ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)ᵐᵒᵖ) [Module.Free R L]


local instance tensorZeroAt_additive {A : Type v} [Ring A] [Algebra R A]
    (M : ModuleCat.{z} Aᵐᵒᵖ) : (ModuleCat.BalancedTensor.functor.{u, v, z, z'} R A M).Additive :=
  ModuleCat.BalancedTensor.additive R A M

/-- Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). Let Q_H be the lifted enveloping projective resolution. For n ∈ ℕ,
m ∈ N, and a ∈ Λⁿ_R L, the inverse equivalence Λⁿ_R L ⊗_R N → N ⊗_U Q_H,n sends a ⊗ m to
[m,up(a ⊗ 1_U)]. The coefficient complex uses the converted left action [x,m] = −m·ι(x). -/
theorem rightTensorCoordinatesAt_symm_tmul (n : ℕ) (m : N) (x : ⋀[R]^n L) :
    (rightTensorCoordinatesAt.{u, v, v', w} R L N n).symm (x ⊗ₜ[R] (show rightCoefficients R L N from m)) =
      TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj
          ((liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L).complex.X n)) m
          (ULift.up (x ⊗ₜ[R] (1 : regularCoefficients R L))) := by
  apply (rightTensorCoordinatesAt.{u, v, v', w} R L N n).injective
  rw [LinearEquiv.apply_symm_apply, rightTensorCoordinatesAt_mk_tmul, op_one, one_smul]

/-- Let R be a commutative ring, L an R-Lie algebra, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). Let T be the augmentation module and T_H = ULift_H(T) its further
lift. Removing the outer lift in the left input gives an R-linear equivalence N ⊗_U T_H ≃ₗ[R]
N ⊗_U T. It sends [m,up(x)] to [m,x] and its inverse sends [m,x] to [m,up(x)]. This
equivalence requires no freeness of L. -/
def rightTrivialTensorLiftEquiv :
    (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R).obj (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) ≃ₗ[R]
      (ModuleCat.BalancedTensor.functor R U N).obj (envelopingTrivialObject R L) := by
  let X := liftedEnvelopingTrivial.{u, v, max u v v' w} R L
  let Y := envelopingTrivialObject R L
  letI : Module R X := Module.compHom X (algebraMap R U)
  letI : Module R Y := Module.compHom Y (algebraMap R U)
  let eU : X ≃ₗ[U] Y := ULift.moduleEquiv
  let eR : X ≃ₗ[R] Y :=
    { eU.toAddEquiv with
      map_smul' := by
        intro r x
        change eU (algebraMap R U r • x) = algebraMap R U r • eU x
        exact eU.map_smul (algebraMap R U r) x }
  exact TensorProduct.Balanced.congr (LinearEquiv.refl R N) eR
    (fun _ _ => rfl) (fun u x => eU.map_smul u x)

omit [Module.Free R L] in
@[simp]
theorem rightTrivialTensorLiftEquiv_mk_up (m : N) (x : envelopingTrivialObject R L) :
    rightTrivialTensorLiftEquiv.{u, v, v', w} R L N
      (TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (liftedEnvelopingTrivial.{u, v, max u v v' w} R L)) m
          (ULift.up x)) =
      TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (envelopingTrivialObject R L)) m x := by
  simp only [rightTrivialTensorLiftEquiv, TensorProduct.Balanced.congr_mk, LinearEquiv.refl_apply]
  rfl

/-- Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). Put F(X) = N ⊗_U X and T_H = ULift_H(T), where T is the
augmentation module with carrier ULift(R). If cl(m) is the H₀ class of the empty-exterior
tensor 1 ⊗ m, its image under the homology-to-Tor comparison and then F.fromLeftDerivedZero at
T_H is [m,up(up(1_R))] in F(T_H). -/
theorem rightCoefficientDerivedZeroAt_unit_class (m : N) :
    ((ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R).fromLeftDerivedZero.app (liftedEnvelopingTrivial.{u, v, max u v v' w} R L)).hom
      ((rightCoefficientHomologyIsoTorAt.{u, v, v', w} R L N 0).hom
        ((rightEnvelopingCoefficientComplex R L N).isoHomologyι₀.inv
          ((rightEnvelopingCoefficientComplex R L N).pOpcycles 0
            (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] (show rightCoefficients R L N from m))))) =
      TensorProduct.Balanced.mk R U N
        ((ModuleCat.restrictScalars (algebraMap R U)).obj (liftedEnvelopingTrivial.{u, v, max u v v' w} R L)) m
          (ULift.up (ULift.up (1 : R))) := by
  let K := rightEnvelopingCoefficientComplex R L N
  let e := (rightTensorCoefficientIsoAt.{u, v, v', w} R L N).symm
  let P := liftedEnvelopingProjectiveResolution.{u, v, max u v v' w} R L
  let F : ModuleCat.{max u v v' w} U ⥤ ModuleCat.{max u v v' w} R :=
    ModuleCat.BalancedTensor.functor R U N
  have h := ProjectiveResolution.zeroClass_fromLeftDerivedZero_of_iso P F K e
  let z : K.X 0 := exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] (show rightCoefficients R L N from m)
  have hval := congrArg (fun g : K.X 0 ⟶ F.obj (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) =>
    g.hom z) h
  let X := P.complex.X 0
  let Y := liftedEnvelopingTrivial.{u, v, max u v v' w} R L
  letI : Module R X := Module.compHom X (algebraMap R U)
  letI : Module R Y := Module.compHom Y (algebraMap R U)
  let aug : X ⟶ Y := P.π.f 0
  let p : X := ULift.up (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] (1 : regularCoefficients R L))
  let unit : Y := ULift.up (ULift.up (1 : R))
  have hAug : aug.hom p = unit := by
    exact (liftedEnvelopingAugmentation_tmul.{u, v, v', w} R L
      (exteriorPower.ιMulti R 0 Fin.elim0) 1).trans
        (congrArg (fun r : R => ULift.up (ULift.up r))
          (by rw [exteriorPower.zeroEquiv_ιMulti, one_smul, map_one]))
  have hTensor := ModuleCat.BalancedTensor.map_mk R U N aug m p
  have hUnit : (F.map aug).hom (TensorProduct.Balanced.mk R U N X m p) =
      TensorProduct.Balanced.mk R U N Y m unit :=
    hTensor.trans (congrArg (TensorProduct.Balanced.mk R U N Y m) hAug)
  have hInput : (e.hom.f 0).hom z = TensorProduct.Balanced.mk R U N X m p :=
    rightTensorCoordinatesAt_symm_tmul.{u, v, v', w} R L N 0 m (exteriorPower.ιMulti R 0 Fin.elim0)
  exact hval.trans ((congrArg (F.map aug).hom hInput).trans hUnit)

/-- Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). Let Φ : H₀(C_*(L;N)) ≅ (L₀F)(T_H), where F(X) = N ⊗_U X and T_H is
the further lift of the augmentation module T. Let k : F(T_H) ≅ F(T) remove that outer input
lift, and let e : H₀(C_*(L;N)) ≅ F(T) be the coinvariant tensor identification. Then Φ.hom ≫
F.fromLeftDerivedZero at T_H ≫ k.hom = e.hom, with e sending the class of 1 ⊗ m to [m,up(1)]. -/
theorem rightCoefficientHomologyIsoTorAt_zero_canonical :
    (rightCoefficientHomologyIsoTorAt.{u, v, v', w} R L N 0).hom ≫
      (ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
      ModuleCat.{max u v v' w} R).fromLeftDerivedZero.app (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) ≫
      (rightTrivialTensorLiftEquiv.{u, v, v', w} R L N).toModuleIso.hom =
      (rightCoefficientHomologyZeroTensorIso R L N).hom := by
  apply ModuleCat.hom_ext
  ext a
  let M := rightCoefficients R L N
  obtain ⟨m, hm⟩ := LieSubmodule.Quotient.surjective_mk'
    ⁅(⊤ : LieIdeal R L), (⊤ : LieSubmodule R L M)⁆
      (coefficientHomologyZeroLinearEquiv R L M a)
  have ha : a = (rightEnvelopingCoefficientComplex R L N).isoHomologyι₀.inv
      ((rightEnvelopingCoefficientComplex R L N).pOpcycles 0
        (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] m)) := by
    apply (coefficientHomologyZeroLinearEquiv R L M).injective
    rw [coefficientHomologyZeroLinearEquiv_class]
    exact hm.symm
  let left := ((rightCoefficientHomologyIsoTorAt.{u, v, v', w} R L N 0).hom ≫
    (ModuleCat.BalancedTensor.functor R U N).fromLeftDerivedZero.app
      (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) ≫
        (rightTrivialTensorLiftEquiv.{u, v, v', w} R L N).toModuleIso.hom).hom
  let right := (rightCoefficientHomologyZeroTensorIso R L N).hom.hom
  have hClass := rightCoefficientDerivedZeroAt_unit_class.{u, v, v', w} R L N m
  have hLift := rightTrivialTensorLiftEquiv_mk_up.{u, v, v', w} R L N m (ULift.up (1 : R))
  exact (congrArg left ha).trans
    (((congrArg (rightTrivialTensorLiftEquiv.{u, v, v', w} R L N) hClass).trans hLift).trans
      ((rightCoefficientHomologyZeroTensorIso_class R L N m).symm.trans
        (congrArg right ha.symm)))

/-- Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). For F(X) = N ⊗_U X and the lifted augmentation module T_H, the
canonical morphism F.fromLeftDerivedZero at T_H : (L₀F)(T_H) → F(T_H) is an isomorphism. Its
inverse is obtained from the coefficient H₀-to-Tor comparison, the coinvariant tensor
identification, and the cancellation of the outer lift of T_H. -/
instance rightEnvelopingTorZeroAt_isIso : IsIso
  ((ModuleCat.BalancedTensor.functor R U N : (ModuleCat.{max u v v' w} (UniversalEnvelopingAlgebra R L)) ⥤
  ModuleCat.{max u v v' w} R).fromLeftDerivedZero.app (liftedEnvelopingTrivial.{u, v, max u v v' w} R L)) := by
  let a := rightCoefficientHomologyIsoTorAt.{u, v, v', w} R L N 0
  let b := rightCoefficientHomologyZeroTensorIso R L N
  let c := (rightTrivialTensorLiftEquiv.{u, v, v', w} R L N).toModuleIso
  let d := a.symm ≪≫ b ≪≫ c.symm
  let g := (ModuleCat.BalancedTensor.functor R U N : ModuleCat.{max u v v' w} U ⥤
    ModuleCat.{max u v v' w} R).fromLeftDerivedZero.app
    (liftedEnvelopingTrivial.{u, v, max u v v' w} R L)
  have h : g = d.hom := by
    apply (cancel_epi a.hom).1
    apply (cancel_mono c.hom).1
    have hCanon := rightCoefficientHomologyIsoTorAt_zero_canonical.{u, v, v', w} R L N
    have hCancel : (a.hom ≫ d.hom) ≫ c.hom = b.hom := by
      change (a.hom ≫ (a.inv ≫ b.hom ≫ c.inv)) ≫ c.hom = b.hom
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun t => b.hom ≫ t) c.inv_hom_id).trans (Category.comp_id _))
    exact (Category.assoc _ _ _).trans (hCanon.trans hCancel.symm)
  change IsIso g
  exact h.symm ▸ (inferInstance : IsIso d.hom)

/-- Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). Put F(X) = N ⊗_U X and let T_H be the lifted augmentation module.
The isomorphism (L₀F)(T_H) ≅ F(T_H) is the composite of the inverse coefficient
homology-to-Tor comparison, the H₀ identification with F(T), and the inverse input-lift
cancellation F(T) ≅ F(T_H). Its forward morphism is the canonical map F.fromLeftDerivedZero at
T_H. -/
def rightEnvelopingTorZeroIsoAt :
    ((ModuleCat.BalancedTensor.functor R U N : ModuleCat.{max u v v' w} U ⥤
      ModuleCat.{max u v v' w} R).leftDerived 0).obj
        (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) ≅
      (ModuleCat.BalancedTensor.functor R U N).obj
        (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) :=
  (rightCoefficientHomologyIsoTorAt.{u, v, v', w} R L N 0).symm ≪≫
    rightCoefficientHomologyZeroTensorIso R L N ≪≫
      (rightTrivialTensorLiftEquiv.{u, v, v', w} R L N).toModuleIso.symm

/-- Let R be a commutative ring, L a free R-Lie module, U = U_R(L), and N a right U-module in
universe H = max(u,v,v′,w). With F(X) = N ⊗_U X and T_H the lifted augmentation module, the
forward map of the constructed isomorphism (L₀F)(T_H) ≅ F(T_H) equals F.fromLeftDerivedZero at
T_H. This identifies the coordinate isomorphism with the canonical natural transformation as
an R-module morphism. -/
theorem rightEnvelopingTorZeroIsoAt_hom :
    (rightEnvelopingTorZeroIsoAt.{u, v, v', w} R L N).hom =
      (ModuleCat.BalancedTensor.functor R U N).fromLeftDerivedZero.app
        (liftedEnvelopingTrivial.{u, v, max u v v' w} R L) := by
  let a := rightCoefficientHomologyIsoTorAt.{u, v, v', w} R L N 0
  let b := rightCoefficientHomologyZeroTensorIso R L N
  let c := (rightTrivialTensorLiftEquiv.{u, v, v', w} R L N).toModuleIso
  apply (cancel_epi a.hom).1
  apply (cancel_mono c.hom).1
  have hCancel : (a.hom ≫ (rightEnvelopingTorZeroIsoAt.{u, v, v', w} R L N).hom) ≫ c.hom = b.hom := by
    change (a.hom ≫ (a.inv ≫ b.hom ≫ c.inv)) ≫ c.hom = b.hom
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => b.hom ≫ t) c.inv_hom_id).trans (Category.comp_id _))
  exact hCancel.trans ((rightCoefficientHomologyIsoTorAt_zero_canonical.{u, v, v', w} R L N).symm.trans
    (Category.assoc _ _ _).symm)

end ChevalleyEilenberg
