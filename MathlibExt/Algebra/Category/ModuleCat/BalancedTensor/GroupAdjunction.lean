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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.HomCoordinates

/-!
# Additive tensor–Hom currying for right modules

Let `R` be an associative ring, `M` a right `R`-module, `N` a left `R`-module, and `I` an
additive commutative group. The group of additive maps `N → I` carries a right `R`-action by
`(h r)(n) = h(r n)`.

An additive map `M ⊗_R N → I` therefore curries to an `Rᵐᵒᵖ`-linear map `M → Hom_ℤ(N, I)`,
with `m ↦ (n ↦ f([m ⊗ n]))`. Uncurrying gives the inverse, and these maps form an additive
equivalence. The tensor and target carriers share universe `v`, independently of the ring
universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite

namespace ModuleCat.BalancedTensor

universe u v

variable (R : Type u) [Ring R]

/-- Currying an additive balanced tensor map in the right-module variable.

For `f : M ⊗_R N ⟶ I` in additive groups, currying gives an `Rᵐᵒᵖ`-linear map from `M` to
additive maps `N → I`. The right action on this Hom group is precomposition with the left
`R`-action on `N`. -/
def groupCurry (M : ModuleCat.{v} Rᵐᵒᵖ) (N : ModuleCat.{v} R) (I : AddCommGrpCat.{v})
    (f : ((groupBifunctor R).obj M).obj N ⟶ I) :
    letI := ChainComplex.homGroupModule R N I
    M →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj N ⟶ I) := by
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
  let T := ModuleCat.BalancedTensorRight.tensorObj R ℤᵐᵒᵖ N M
  let C := ModuleCat.of ℤᵐᵒᵖᵐᵒᵖ I
  let U := forget₂ (ModuleCat.{v} ℤᵐᵒᵖᵐᵒᵖ) AddCommGrpCat.{v}
  let e := coefficientCoordinates R M N
  let φ : U.obj T ⟶ U.obj C := e.inv ≫ f
  letI : Module ℤᵐᵒᵖᵐᵒᵖ (U.obj T) := T.isModule
  letI : Module ℤᵐᵒᵖᵐᵒᵖ (U.obj C) := C.isModule
  let L : T.carrier →ₗ[ℤᵐᵒᵖᵐᵒᵖ] C.carrier :=
    { toFun := φ.hom
      map_add' := φ.hom.map_add
      map_smul' := by
        intro z x
        have hz : (z.unop.unop : ℤᵐᵒᵖᵐᵒᵖ) = z := by
          change op (op z.unop.unop) = z
          rfl
        simpa only [hz, RingHom.id_apply] using
          map_intCast_smul φ.hom ℤᵐᵒᵖᵐᵒᵖ ℤᵐᵒᵖᵐᵒᵖ z.unop.unop x }
  let a : T ⟶ C := @ModuleCat.ofHom ℤᵐᵒᵖᵐᵒᵖ _ T.carrier C.carrier
    T.isAddCommGroup T.isModule C.isAddCommGroup C.isModule L
  exact (homCoordinates R N I).toLinearMap.comp
    ((ModuleCat.BalancedTensorRight.tensorHomEquiv R ℤᵐᵒᵖ N M C) a).hom

/-- Uncurrying a right-linear map to an additive Hom group.

An `Rᵐᵒᵖ`-linear map `g : M → Hom_ℤ(N, I)` descends to an additive map `M ⊗_R N → I` by
evaluation on the two factors. -/
def groupUncurry (M : ModuleCat.{v} Rᵐᵒᵖ) (N : ModuleCat.{v} R) (I : AddCommGrpCat.{v})
    (g : letI := ChainComplex.homGroupModule R N I
      M →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj N ⟶ I)) :
    ((groupBifunctor R).obj M).obj N ⟶ I := by
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
  let C := ModuleCat.of ℤᵐᵒᵖᵐᵒᵖ I
  let a : M ⟶ ModuleCat.BalancedTensorRight.homObj R ℤᵐᵒᵖ N C :=
    ModuleCat.ofHom ((homCoordinates R N I).symm.toLinearMap.comp g)
  exact (coefficientCoordinates R M N).hom ≫
    (forget₂ (ModuleCat.{v} ℤᵐᵒᵖᵐᵒᵖ) AddCommGrpCat.{v}).map
      ((ModuleCat.BalancedTensorRight.tensorHomEquiv R ℤᵐᵒᵖ N M C).symm a)

/-- Right-variable uncurrying on pure balanced classes.

For `m : M` and `n : N`, the uncurried map of `g` satisfies `groupUncurry g [m ⊗ n] = (g
m)(n)`. -/
theorem groupUncurry_mk (M : ModuleCat.{v} Rᵐᵒᵖ) (N : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v})
    (g : letI := ChainComplex.homGroupModule R N I
      M →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj N ⟶ I)) (m : M) (n : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    (groupUncurry R M N I g).hom (TensorProduct.Balanced.mk ℤ R M N m n) = (g m).hom n := by
  let x : ((groupBifunctor R).obj M).obj N := by
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    exact TensorProduct.Balanced.mk ℤ R M N m n
  change (groupUncurry R M N I g).hom x = _
  let : Module ℤ N := AddCommGroup.toIntModule N
  let : Module ℤᵐᵒᵖᵐᵒᵖ N :=
    Module.compHom N (RingEquiv.opOp ℤ).symm.toRingHom
  let : SMulCommClass R ℤᵐᵒᵖᵐᵒᵖ N := by
    refine ⟨?_⟩
    intro r z x
    change r • (z.unop.unop • x) = z.unop.unop • (r • x)
    exact map_zsmul (DistribSMul.toAddMonoidHom N r) z.unop.unop x
  let : Module ℤ I := AddCommGroup.toIntModule I
  let : Module ℤᵐᵒᵖᵐᵒᵖ I :=
    Module.compHom I (RingEquiv.opOp ℤ).symm.toRingHom
  let := TensorProduct.Balanced.CoefficientHom.homModule R ℤᵐᵒᵖ N I
  let := ChainComplex.homGroupModule R N I
  let C := ModuleCat.of ℤᵐᵒᵖᵐᵒᵖ I
  let a : M ⟶ ModuleCat.BalancedTensorRight.homObj R ℤᵐᵒᵖ N C :=
    ModuleCat.ofHom ((homCoordinates R N I).symm.toLinearMap.comp g)
  let e := coefficientCoordinates R M N
  change ((forget₂ (ModuleCat.{v} ℤᵐᵒᵖᵐᵒᵖ) AddCommGrpCat.{v}).map
    ((ModuleCat.BalancedTensorRight.tensorHomEquiv R ℤᵐᵒᵖ N M C).symm a)).hom
      (e.hom.hom x) = _
  have hx : e.hom.hom x = coefficientMk R M N m n := coefficientCoordinates_mk R M N m n
  rw [hx]
  change ((ModuleCat.BalancedTensorRight.tensorHomEquiv R ℤᵐᵒᵖ N M C).symm a).hom
    (TensorProduct.Balanced.mk ℤ R M N m n) = _
  rw [ModuleCat.BalancedTensorRight.tensorHomEquiv_symm_mk]
  change (homCoordinates R N I).symm (g m) n = _
  exact homCoordinates_symm_apply R N I (g m) n

/-- Right-variable currying evaluates on pure balanced classes.

For an additive balanced tensor map `f`, the curried value at `m` evaluated at `n` is `f([m ⊗
n])`. -/
theorem groupCurry_mk (M : ModuleCat.{v} Rᵐᵒᵖ) (N : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) (f : ((groupBifunctor R).obj M).obj N ⟶ I) (m : M) (n : N) :
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    letI := ChainComplex.homGroupModule R N I
    (groupCurry R M N I f m).hom n = f.hom (TensorProduct.Balanced.mk ℤ R M N m n) := by
  let x : ((groupBifunctor R).obj M).obj N := by
    letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    exact TensorProduct.Balanced.mk ℤ R M N m n
  change (groupCurry R M N I f m).hom n = f.hom x
  let : Module ℤ N := AddCommGroup.toIntModule N
  let : Module ℤᵐᵒᵖᵐᵒᵖ N :=
    Module.compHom N (RingEquiv.opOp ℤ).symm.toRingHom
  let : SMulCommClass R ℤᵐᵒᵖᵐᵒᵖ N := by
    refine ⟨?_⟩
    intro r z x
    change r • (z.unop.unop • x) = z.unop.unop • (r • x)
    exact map_zsmul (DistribSMul.toAddMonoidHom N r) z.unop.unop x
  let : Module ℤ I := AddCommGroup.toIntModule I
  let : Module ℤᵐᵒᵖᵐᵒᵖ I :=
    Module.compHom I (RingEquiv.opOp ℤ).symm.toRingHom
  let := TensorProduct.Balanced.CoefficientHom.homModule R ℤᵐᵒᵖ N I
  let := ChainComplex.homGroupModule R N I
  let T := ModuleCat.BalancedTensorRight.tensorObj R ℤᵐᵒᵖ N M
  let C := ModuleCat.of ℤᵐᵒᵖᵐᵒᵖ I
  let U := forget₂ (ModuleCat.{v} ℤᵐᵒᵖᵐᵒᵖ) AddCommGrpCat.{v}
  let e := coefficientCoordinates R M N
  let φ : U.obj T ⟶ U.obj C := e.inv ≫ f
  let : Module ℤᵐᵒᵖᵐᵒᵖ (U.obj T) := T.isModule
  let : Module ℤᵐᵒᵖᵐᵒᵖ (U.obj C) := C.isModule
  let L : T.carrier →ₗ[ℤᵐᵒᵖᵐᵒᵖ] C.carrier :=
    { toFun := φ.hom
      map_add' := φ.hom.map_add
      map_smul' := by
        intro z x
        have hz : (z.unop.unop : ℤᵐᵒᵖᵐᵒᵖ) = z := by
          change op (op z.unop.unop) = z
          rfl
        simpa only [hz, RingHom.id_apply] using
          map_intCast_smul φ.hom ℤᵐᵒᵖᵐᵒᵖ ℤᵐᵒᵖᵐᵒᵖ z.unop.unop x }
  let a : T ⟶ C := @ModuleCat.ofHom ℤᵐᵒᵖᵐᵒᵖ _ T.carrier C.carrier
    T.isAddCommGroup T.isModule C.isAddCommGroup C.isModule L
  have he : e.hom.hom x = coefficientMk R M N m n := coefficientCoordinates_mk R M N m n
  have hi : e.inv.hom (coefficientMk R M N m n) = x := by
    have h := congrArg (fun q : ((groupBifunctor R).obj M).obj N ⟶
      ((groupBifunctor R).obj M).obj N => q.hom x) e.hom_inv_id
    have h' : e.inv.hom (e.hom.hom x) = x := by
      simpa only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
        AddCommGrpCat.hom_id, AddMonoidHom.id_apply] using h
    exact (congrArg e.inv.hom he).symm.trans h'
  have hForget : U.map a = φ := rfl
  have ha := congrArg (fun q : U.obj T ⟶ U.obj C => q.hom (coefficientMk R M N m n))
    hForget
  have hav : a.hom (TensorProduct.Balanced.mk ℤ R M N m n) = f.hom x := by
    change (U.map a).hom (coefficientMk R M N m n) = f.hom x
    exact ha.trans (by
      change f.hom (e.inv.hom (coefficientMk R M N m n)) = f.hom x
      exact congrArg f.hom hi)
  change (homCoordinates R N I
    (((ModuleCat.BalancedTensorRight.tensorHomEquiv R ℤᵐᵒᵖ N M C) a).hom m)).hom n = f.hom x
  rw [homCoordinates_apply, ModuleCat.BalancedTensorRight.tensorHomEquiv_apply]
  exact hav

/-- Pure balanced classes determine an additive tensor map.

Two additive maps from `M ⊗_R N` to `I` are equal if they agree on `[m ⊗ n]` for all `m` and
`n`. -/
theorem groupHom_ext (M : ModuleCat.{v} Rᵐᵒᵖ) (N : ModuleCat.{v} R) (I : AddCommGrpCat.{v})
    {f g : ((groupBifunctor R).obj M).obj N ⟶ I}
    (h : letI : Module ℤ N := Module.compHom N (algebraMap ℤ R)
      ∀ (m : M) (n : N),
        f.hom (TensorProduct.Balanced.mk ℤ R M N m n) =
          g.hom (TensorProduct.Balanced.mk ℤ R M N m n)) : f = g := by
  let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
  apply AddCommGrpCat.hom_ext
  exact TensorProduct.Balanced.addHom_ext ℤ R M N
    (f := f.hom) (g := g.hom) h

/-- Additive equivalence for right-variable balanced tensor currying.

Currying and uncurrying give an additive equivalence between additive maps `M ⊗_R N → I` and
`Rᵐᵒᵖ`-linear maps `M → Hom_ℤ(N, I)`, with the Hom action defined by domain precomposition. -/
def groupTensorHomEquiv (M : ModuleCat.{v} Rᵐᵒᵖ) (N : ModuleCat.{v} R)
    (I : AddCommGrpCat.{v}) :
    letI := ChainComplex.homGroupModule R N I
    (((groupBifunctor R).obj M).obj N ⟶ I) ≃+
      (M →ₗ[Rᵐᵒᵖ] ((forget₂ (ModuleCat R) AddCommGrpCat).obj N ⟶ I)) := by
  letI := ChainComplex.homGroupModule R N I
  refine
    { toFun := groupCurry R M N I
      invFun := groupUncurry R M N I
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro f
    apply groupHom_ext R M N I
    intro m n
    rw [groupUncurry_mk, groupCurry_mk]
  · intro g
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    apply LinearMap.ext
    intro m
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro n
    rw [groupCurry_mk, groupUncurry_mk]
  · intro f g
    let : Module ℤ N := Module.compHom N (algebraMap ℤ R)
    apply LinearMap.ext
    intro m
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro n
    change (groupCurry R M N I (f + g) m).hom n =
      ((groupCurry R M N I f m) + (groupCurry R M N I g m)).hom n
    rw [groupCurry_mk]
    simp only [AddCommGrpCat.hom_add, AddMonoidHom.add_apply, groupCurry_mk]
    let z : ((groupBifunctor R).obj M).obj N :=
      TensorProduct.Balanced.mk ℤ R M N m n
    exact AddMonoidHom.add_apply f.hom g.hom z

end ModuleCat.BalancedTensor
