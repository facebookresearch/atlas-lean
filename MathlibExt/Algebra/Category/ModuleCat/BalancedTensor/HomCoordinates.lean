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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.IntegerCoordinates
public import MathlibExt.Algebra.Homology.ChainComplex.ModuleHomCochainComplex
public meta import Mathlib.Tactic.DSimpPercent

/-!
# Integer-linear and additive Hom coordinates

For a left `R`-module `N` and an additive commutative group `I`, the Hom object in the
coefficient tensor adjunction over the opposite integer ring consists of `ℤᵐᵒᵖᵐᵒᵖ`-linear maps
`N → I`. Use the integer actions of the groups and restriction along the double-opposite
integer ring equivalence.

These maps are linearly equivalent over `Rᵐᵒᵖ` to the additive Hom group `Hom_ℤ(N, I)`. Both
actions are domain precomposition, `(h r)(n) = h(r n)`, and the equivalence preserves each
function value. Precomposition by an `R`-linear map of domains is right-linear in these
coordinates.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite

namespace ModuleCat.BalancedTensor

universe u v

variable (R : Type u) [Ring R]

/-- Coefficient Hom as the additive Hom group with right R action.

Give `N` and `I` their integer actions transported to `ℤᵐᵒᵖᵐᵒᵖ`. The coefficient Hom object is
`Rᵐᵒᵖ`-linearly equivalent to additive maps `N → I`, where the right `R`-action in both
objects is precomposition by the left action on `N`. -/
def homCoordinates (N : ModuleCat.{v} R) (I : AddCommGrpCat.{v}) :
    letI : Module ℤ N := AddCommGroup.toIntModule N
    letI : Module ℤᵐᵒᵖᵐᵒᵖ N :=
      Module.compHom N (RingEquiv.opOp ℤ).symm.toRingHom
    letI : SMulCommClass R ℤᵐᵒᵖᵐᵒᵖ N := by
      refine ⟨?_⟩
      intro r z x
      change r • (z.unop.unop • x) = z.unop.unop • (r • x)
      exact map_zsmul (DistribSMul.toAddMonoidHom N r) z.unop.unop x
    letI : Module ℤ I := AddCommGroup.toIntModule I
    letI : Module ℤᵐᵒᵖᵐᵒᵖ I :=
      Module.compHom I (RingEquiv.opOp ℤ).symm.toRingHom
    letI := ChainComplex.homGroupModule R N I
    ModuleCat.BalancedTensorRight.homObj R ℤᵐᵒᵖ N (ModuleCat.of ℤᵐᵒᵖᵐᵒᵖ I) ≃ₗ[Rᵐᵒᵖ]
      ((forget₂ (ModuleCat R) AddCommGrpCat).obj N ⟶ I) := by
  letI : Module ℤ N := AddCommGroup.toIntModule N
  letI : Module ℤᵐᵒᵖᵐᵒᵖ N :=
    Module.compHom N (RingEquiv.opOp ℤ).symm.toRingHom
  letI : SMulCommClass R ℤᵐᵒᵖᵐᵒᵖ N := by
    refine ⟨?_⟩
    intro r z x
    change r • (z.unop.unop • x) = z.unop.unop • (r • x)
    exact map_zsmul (DistribSMul.toAddMonoidHom N r) z.unop.unop x
  letI : Module ℤ I := AddCommGroup.toIntModule I
  letI : Module ℤᵐᵒᵖᵐᵒᵖ I :=
    Module.compHom I (RingEquiv.opOp ℤ).symm.toRingHom
  letI := TensorProduct.Balanced.CoefficientHom.homModule R ℤᵐᵒᵖ N I
  letI := ChainComplex.homGroupModule R N I
  let eInt : (N →ₗ[ℤᵐᵒᵖᵐᵒᵖ] I) ≃+ (N →ₗ[ℤ] I) :=
    { toFun := fun f => f.toAddMonoidHom.toIntLinearMap
      invFun := fun f =>
        { toFun := f
          map_add' := f.map_add
          map_smul' := by
            intro z x
            change f (z.unop.unop • x) = z.unop.unop • f x
            exact f.map_smul z.unop.unop x }
      left_inv := fun f => LinearMap.ext (fun _ => rfl)
      right_inv := fun f => LinearMap.ext (fun _ => rfl)
      map_add' := fun f g => LinearMap.ext (fun _ => rfl) }
  let eAdd : (N →ₗ[ℤ] I) ≃+ ((forget₂ (ModuleCat R) AddCommGrpCat).obj N ⟶ I) :=
    { toFun := fun f => AddCommGrpCat.ofHom f.toAddMonoidHom
      invFun := fun f => f.hom.toIntLinearMap
      left_inv := fun f => LinearMap.ext (fun _ => rfl)
      right_inv := fun f => AddCommGrpCat.hom_ext rfl
      map_add' := fun f g => AddCommGrpCat.hom_ext rfl }
  let e := eInt.trans eAdd
  apply e.toLinearEquiv
  intro r f
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change (r • f) x = (r • e f).hom x
  have hLeft := TensorProduct.Balanced.CoefficientHom.homModule_smul_apply
    R ℤᵐᵒᵖ N I r f (show N from x)
  have hRight := ChainComplex.homGroupModule_smul_apply R N I r (e f) (show N from x)
  exact hLeft.trans hRight.symm

/-- Forward coefficient Hom coordinate preserves evaluation.

For a coefficient Hom element `f` and `x : N`, the additive map corresponding to `f` under
`homCoordinates R N I` evaluates at `x` as `f x`. -/
@[simp]
theorem homCoordinates_apply (N : ModuleCat.{v} R) (I : AddCommGrpCat.{v})
    (f :
      letI : Module ℤ N := AddCommGroup.toIntModule N
      letI : Module ℤᵐᵒᵖᵐᵒᵖ N :=
        Module.compHom N (RingEquiv.opOp ℤ).symm.toRingHom
      letI : SMulCommClass R ℤᵐᵒᵖᵐᵒᵖ N := by
        refine ⟨?_⟩
        intro r z x
        change r • (z.unop.unop • x) = z.unop.unop • (r • x)
        exact map_zsmul (DistribSMul.toAddMonoidHom N r) z.unop.unop x
      letI : Module ℤ I := AddCommGroup.toIntModule I
      letI : Module ℤᵐᵒᵖᵐᵒᵖ I :=
        Module.compHom I (RingEquiv.opOp ℤ).symm.toRingHom
      ModuleCat.BalancedTensorRight.homObj R ℤᵐᵒᵖ N (ModuleCat.of ℤᵐᵒᵖᵐᵒᵖ I)) (x : N) :
    dsimp% only [ModuleCat.forget₂_obj] (
    letI : Module ℤ N := AddCommGroup.toIntModule N
    letI : Module ℤᵐᵒᵖᵐᵒᵖ N :=
      Module.compHom N (RingEquiv.opOp ℤ).symm.toRingHom
    letI : SMulCommClass R ℤᵐᵒᵖᵐᵒᵖ N := by
      refine ⟨?_⟩
      intro r z x
      change r • (z.unop.unop • x) = z.unop.unop • (r • x)
      exact map_zsmul (DistribSMul.toAddMonoidHom N r) z.unop.unop x
    letI : Module ℤ I := AddCommGroup.toIntModule I
    letI : Module ℤᵐᵒᵖᵐᵒᵖ I :=
      Module.compHom I (RingEquiv.opOp ℤ).symm.toRingHom
    letI := ChainComplex.homGroupModule R N I
    (@AddCommGrpCat.Hom.hom (AddCommGrpCat.of N) I (homCoordinates R N I f)) x = f x) := rfl

/-- Inverse coefficient Hom coordinate preserves evaluation.

For an additive map `f : N → I`, the inverse coordinate equips the same function with double-
opposite integer linearity; its value at `x : N` is `f.hom x`. -/
@[simp]
theorem homCoordinates_symm_apply (N : ModuleCat.{v} R) (I : AddCommGrpCat.{v})
    (f : (forget₂ (ModuleCat R) AddCommGrpCat).obj N ⟶ I) (x : N) :
    dsimp% only [ModuleCat.forget₂_obj] (
    letI : Module ℤ N := AddCommGroup.toIntModule N
    letI : Module ℤᵐᵒᵖᵐᵒᵖ N :=
      Module.compHom N (RingEquiv.opOp ℤ).symm.toRingHom
    letI : SMulCommClass R ℤᵐᵒᵖᵐᵒᵖ N := by
      refine ⟨?_⟩
      intro r z x
      change r • (z.unop.unop • x) = z.unop.unop • (r • x)
      exact map_zsmul (DistribSMul.toAddMonoidHom N r) z.unop.unop x
    letI : Module ℤ I := AddCommGroup.toIntModule I
    letI : Module ℤᵐᵒᵖᵐᵒᵖ I :=
      Module.compHom I (RingEquiv.opOp ℤ).symm.toRingHom
    letI := ChainComplex.homGroupModule R N I
    @DFunLike.coe (N →ₗ[ℤᵐᵒᵖᵐᵒᵖ] I) N (fun _ => I) _
      ((homCoordinates R N I).symm f) x = f.hom x) := rfl

/-- Right-linear precomposition on additive Hom groups.

For an `R`-linear morphism `f : N' ⟶ N`, precomposition gives an `Rᵐᵒᵖ`-linear map `Hom_ℤ(N,
I) → Hom_ℤ(N', I)` using their domain-action module structures. -/
def homGroupPrecomp {N N' : ModuleCat.{v} R} (f : N' ⟶ N) (I : AddCommGrpCat.{v}) :
    letI := ChainComplex.homGroupModule R N I
    letI := ChainComplex.homGroupModule R N' I
    ((forget₂ (ModuleCat R) AddCommGrpCat).obj N ⟶ I) →ₗ[Rᵐᵒᵖ]
      ((forget₂ (ModuleCat R) AddCommGrpCat).obj N' ⟶ I) := by
  letI := ChainComplex.homGroupModule R N I
  letI := ChainComplex.homGroupModule R N' I
  refine
    { toFun := fun g => (forget₂ (ModuleCat R) AddCommGrpCat).map f ≫ g
      map_add' := by
        intro g h
        exact Preadditive.comp_add
          ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj N')
          ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).obj N) I
          ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).map f) g h
      map_smul' := ?_ }
  intro r g
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change (r • g).hom (f.hom x) =
    (r • ((forget₂ (ModuleCat R) AddCommGrpCat).map f ≫ g)).hom x
  have hLeft := ChainComplex.homGroupModule_smul_apply R N I r g
    (show N from f.hom x)
  have hRight := ChainComplex.homGroupModule_smul_apply R N' I r
    ((forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).map f ≫ g) (show N' from x)
  have hLinear := congrArg g.hom (f.hom.map_smul r.unop (show N' from x)).symm
  exact hLeft.trans (hLinear.trans hRight.symm)

/-- Evaluation formula for additive Hom precomposition.

For `g : N → I` and `x : N'`, the precomposed map satisfies `(homGroupPrecomp R f I g)(x) =
g(f x)`. -/
@[simp]
theorem homGroupPrecomp_apply {N N' : ModuleCat.{v} R} (f : N' ⟶ N)
    (I : AddCommGrpCat.{v}) (g : (forget₂ (ModuleCat R) AddCommGrpCat).obj N ⟶ I) (x : N') :
    dsimp% only [ModuleCat.forget₂_obj] (
    letI := ChainComplex.homGroupModule R N I
    letI := ChainComplex.homGroupModule R N' I
    (@AddCommGrpCat.Hom.hom (AddCommGrpCat.of N') I (homGroupPrecomp R f I g)) x =
      g.hom (f.hom x)) := rfl

end ModuleCat.BalancedTensor
