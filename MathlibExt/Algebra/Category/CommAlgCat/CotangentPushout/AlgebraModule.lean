/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.PolynomialSplitting
public import MathlibExt.Algebra.Category.CommAlgCat.AdditiveResolutionCondition
public import MathlibExt.Algebra.Category.ModuleCat.CompatibleScalarRestriction
public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedAugmentation
public import Mathlib.CategoryTheory.Whiskering

/-!
# Scalar extension of algebra and module augmentations

For commutative rings `k` and `K` with a `k`-algebra structure on `K`, extending the
underlying `k`-module of a commutative `k`-algebra `P` gives a `K`-module naturally
isomorphic to the underlying module of the tensor-product algebra `K ⊗[k] P`. The
comparison sends `a ⊗ p` to `a ⊗ p` and respects the `K`-action on the first factor.

This natural comparison also identifies the entire augmented module diagrams for
`P → const A` and its scalar-changed augmentation to `K ⊗[k] A`, including the maps to
the augmentation target. No asphericity or flatness condition on the diagram is assumed.
The ground-ring, extension-ring, and algebra-carrier universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped TensorProduct ChangeOfRings Simplicial

universe u v w

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]

/--
Extension of scalars on modules along the ground-ring morphism `algebraMap k K`,
with source and target carriers in the common height `max u v w`.
-/
abbrev groundModuleFunctor : ModuleCat.{max u v w} k ⥤ ModuleCat.{max u v w} K :=
  ModuleCat.extendScalars (algebraMap k K)

/--
The `K`-linear equivalence between the scalar extension of the underlying `k`-module
of `P` and the underlying `K`-module of `K ⊗[k] P`. On pure tensors it preserves both
factors: `a ⊗ p ↦ a ⊗ p`.
-/
def algebraModuleBaseChangeEquiv (P : CommAlgCat.{max u v w} k) :
    (groundModuleFunctor.{u, v, w} k K).obj ((algebraModuleFunctor.{u, max v w} k).obj P) ≃ₗ[K]
      (algebraModuleFunctor.{w, max u v} K).obj ((algebraFunctor.{u, v, w} k K).obj P) := by
  let M : ModuleCat.{max u v w} k := (algebraModuleFunctor.{u, max v w} k).obj P
  let X : ModuleCat.{max u v w} K := (groundModuleFunctor.{u, v, w} k K).obj M
  let Y : ModuleCat.{max u v w} K :=
    (algebraModuleFunctor.{w, max u v} K).obj ((algebraFunctor.{u, v, w} k K).obj P)
  let e : (((ModuleCat.restrictScalars (algebraMap k K)).obj (ModuleCat.of K K)) ⊗[k] M) ≃ₗ[k]
      (K ⊗[k] M) :=
    TensorProduct.congr (ModuleCat.compatibleRestrictScalarsEquiv k K K)
      (LinearEquiv.refl k M)
  letI : Module K X := X.isModule
  letI : Module K Y := Y.isModule
  change X ≃ₗ[K] Y
  refine
    { toFun := fun x : X => e x
      invFun := fun y : Y => e.symm y
      left_inv := fun x => e.left_inv x
      right_inv := fun y => e.right_inv y
      map_add' := fun x y => e.map_add x y
      map_smul' := ?_ }
  intro a x
  have he (b : K) (p : M) :
      e (b ⊗ₜ[k,algebraMap k K] p : X) = (b ⊗ₜ[k] p : Y) := by
    exact TensorProduct.congr_tmul
      (ModuleCat.compatibleRestrictScalarsEquiv k K K) (LinearEquiv.refl k M) b p
  change e ((@SMul.smul K X X.isModule.toSMul a x)) = (@SMul.smul K Y Y.isModule.toSMul a (e x))
  refine TensorProduct.inductionOn
    (motive := fun z =>
      e ((@SMul.smul K X X.isModule.toSMul a (show X from z))) =
        (@SMul.smul K Y Y.isModule.toSMul a (e z))) x ?_ ?_
  · intro (b : (ModuleCat.restrictScalars (algebraMap k K)).obj (ModuleCat.of K K)) (p : M)
    let bK : K := b
    have hx : (@SMul.smul K X X.isModule.toSMul a (bK ⊗ₜ[k,algebraMap k K] p : X)) = (a * bK) ⊗ₜ[k,algebraMap k K] p :=
      ModuleCat.ExtendScalars.smul_tmul (algebraMap k K) a bK p
    have hy : (@SMul.smul K Y Y.isModule.toSMul a (bK ⊗ₜ[k] p : Y)) = ((a * bK) ⊗ₜ[k] p : Y) := by
      exact TensorProduct.smul_tmul' a bK p
    exact (congrArg e hx).trans ((he (a * bK) p).trans
      ((congrArg (fun y : Y => a • y) (he bK p)).trans hy).symm)
  · intro x y hx hy
    let x' : X := x
    let y' : X := y
    let smX : X → X := fun z => @SMul.smul K X X.isModule.toSMul a z
    let smY : Y → Y := fun z => @SMul.smul K Y Y.isModule.toSMul a z
    have hX : smX (x' + y') = smX x' + smX y' := by
      change (a • (x' + y') : X) = (a • x' : X) + (a • y' : X)
      exact smul_add a x' y'
    have hY : smY (e x' + e y') = smY (e x') + smY (e y') := by
      change (a • ((e x' : Y) + (e y' : Y)) : Y) =
        (a • (e x' : Y) : Y) + (a • (e y' : Y) : Y)
      exact smul_add a (e x' : Y) (e y' : Y)
    change e (smX (x' + y')) = smY (e (x' + y'))
    exact (congrArg e hX).trans ((e.map_add (smX x') (smX y')).trans
      ((congrArg₂ (fun x y : Y => x + y) hx hy).trans
        (hY.symm.trans (congrArg smY (e.map_add x' y').symm))))

/--
The module-category isomorphism corresponding to `algebraModuleBaseChangeEquiv`,
from extension of the underlying module of `P` to the underlying module of its
scalar-changed algebra.
-/
def algebraModuleBaseChangeIso (P : CommAlgCat.{max u v w} k) :
    (groundModuleFunctor.{u, v, w} k K).obj ((algebraModuleFunctor.{u, max v w} k).obj P) ≅
      (algebraModuleFunctor.{w, max u v} K).obj ((algebraFunctor.{u, v, w} k K).obj P) :=
  (algebraModuleBaseChangeEquiv.{u, v, w} k K P).toModuleIso

/--
The algebra-module comparison sends the extension-of-scalars tensor `a ⊗ p` to the
algebra tensor `a ⊗ p`, for `a : K` and `p : P`.
-/
@[simp]
theorem algebraModuleBaseChangeIso_tmul (P : CommAlgCat.{max u v w} k) (a : K) (p : P) :
    (algebraModuleBaseChangeIso.{u, v, w} k K P).hom.hom
        (a ⊗ₜ[k,algebraMap k K] p) = a ⊗ₜ[k] p  := by
  unfold algebraModuleBaseChangeIso
  change algebraModuleBaseChangeEquiv.{u, v, w} k K P (a ⊗ₜ[k,algebraMap k K] p) = a ⊗ₜ[k] p
  unfold algebraModuleBaseChangeEquiv
  dsimp only
  exact TensorProduct.congr_tmul
    (ModuleCat.compatibleRestrictScalarsEquiv k K K) (LinearEquiv.refl k _) a p

/--
For a `k`-algebra map `f : P ⟶ Q`, the comparison from scalar-extended modules to
underlying scalar-changed algebras commutes with the maps induced by `f`.
-/
@[reassoc]
theorem algebraModuleBaseChangeIso_naturality
    {P Q : CommAlgCat.{max u v w} k} (f : P ⟶ Q) :
    (groundModuleFunctor.{u, v, w} k K).map ((algebraModuleFunctor.{u, max v w} k).map f) ≫
        (algebraModuleBaseChangeIso.{u, v, w} k K Q).hom =
      (algebraModuleBaseChangeIso.{u, v, w} k K P).hom ≫
        (algebraModuleFunctor.{w, max u v} K).map ((algebraFunctor.{u, v, w} k K).map f) := by
  let F := groundModuleFunctor.{u, v, w} k K
  let MP : ModuleCat.{max u v w} k := (algebraModuleFunctor.{u, max v w} k).obj P
  let MQ : ModuleCat.{max u v w} k := (algebraModuleFunctor.{u, max v w} k).obj Q
  let XP : ModuleCat.{max u v w} K := F.obj MP
  let XQ : ModuleCat.{max u v w} K := F.obj MQ
  let YP : ModuleCat.{max u v w} K :=
    (algebraModuleFunctor.{w, max u v} K).obj ((algebraFunctor.{u, v, w} k K).obj P)
  let YQ : ModuleCat.{max u v w} K :=
    (algebraModuleFunctor.{w, max u v} K).obj ((algebraFunctor.{u, v, w} k K).obj Q)
  let fM : MP ⟶ MQ := (algebraModuleFunctor.{u, max v w} k).map f
  let fY : YP ⟶ YQ :=
    (algebraModuleFunctor.{w, max u v} K).map ((algebraFunctor.{u, v, w} k K).map f)
  let eP : XP ≅ YP := algebraModuleBaseChangeIso.{u, v, w} k K P
  let eQ : XQ ≅ YQ := algebraModuleBaseChangeIso.{u, v, w} k K Q
  change F.map fM ≫ eQ.hom = eP.hom ≫ fY
  apply ModuleCat.ExtendScalars.hom_ext (f := algebraMap k K)
  intro p
  change eQ.hom.hom ((F.map fM).hom ((1 : K) ⊗ₜ[k,algebraMap k K] p : XP)) =
    fY.hom (eP.hom.hom ((1 : K) ⊗ₜ[k,algebraMap k K] p : XP))
  have hf : (F.map fM).hom ((1 : K) ⊗ₜ[k,algebraMap k K] p : XP) =
      ((1 : K) ⊗ₜ[k,algebraMap k K] fM.hom p : XQ) :=
    ModuleCat.ExtendScalars.map_tmul (algebraMap k K) fM 1 p
  have heP : eP.hom.hom ((1 : K) ⊗ₜ[k,algebraMap k K] p : XP) = ((1 : K) ⊗ₜ[k] p : YP) :=
    algebraModuleBaseChangeIso_tmul.{u, v, w} k K P 1 (p : P)
  have heQ : eQ.hom.hom ((1 : K) ⊗ₜ[k,algebraMap k K] fM.hom p : XQ) =
      ((1 : K) ⊗ₜ[k] fM.hom p : YQ) :=
    algebraModuleBaseChangeIso_tmul.{u, v, w} k K Q 1 (fM.hom p : Q)
  have hY : fY.hom ((1 : K) ⊗ₜ[k] p : YP) = ((1 : K) ⊗ₜ[k] fM.hom p : YQ) :=
    algebraFunctor_map_tmul.{u, v, w} k K f 1 (p : P)
  exact (congrArg eQ.hom.hom hf).trans
    (heQ.trans (hY.symm.trans (congrArg fY.hom heP).symm))

/--
The natural isomorphism between forgetting a `k`-algebra to a module and then extending
scalars, and extending the algebra scalars and then forgetting to a `K`-module.
-/
def algebraModuleBaseChangeNatIso :
    algebraModuleFunctor.{u, max v w} k ⋙ groundModuleFunctor.{u, v, w} k K ≅
      algebraFunctor.{u, v, w} k K ⋙ algebraModuleFunctor.{w, max u v} K :=
  NatIso.ofComponents (algebraModuleBaseChangeIso.{u, v, w} k K)
    (algebraModuleBaseChangeIso_naturality.{u, v, w} k K)

variable (A : CommAlgCat.{max u v w} k)

/--
The augmentation `K ⊗[k] P → const (K ⊗[k] A)` obtained by applying algebra scalar
extension to every component of the augmentation `P → const A`.
-/
def augmentation
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    P.left ⋙ algebraFunctor.{u, v, w} k K ⟶
      (SimplicialObject.const (CommAlgCat.{max u v w} K)).obj (target.{u, v, w} k K A) where
  app i := (algebraFunctor.{u, v, w} k K).map (P.hom.app i)
  naturality {i j} θ := by
    have hc : ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A).map θ = 𝟙 A := rfl
    have hp : P.left.map θ ≫ P.hom.app j = P.hom.app i := by
      exact (P.hom.naturality θ).trans
        ((congrArg (fun z => P.hom.app i ≫ z) hc).trans (Category.comp_id (P.hom.app i)))
    change (algebraFunctor.{u, v, w} k K).map (P.left.map θ) ≫
        (algebraFunctor.{u, v, w} k K).map (P.hom.app j) =
      (algebraFunctor.{u, v, w} k K).map (P.hom.app i) ≫ 𝟙 _
    rw [Category.comp_id, ← Functor.map_comp, hp]

/--
The scalar-changed augmented simplicial algebra, viewed in the over category of the
constant diagram on `K ⊗[k] A`. This construction is defined for any augmented diagram.
-/
def resolution
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    Over ((SimplicialObject.const (CommAlgCat.{max u v w} K)).obj (target.{u, v, w} k K A)) :=
  Over.mk (augmentation.{u, v, w} k K A P)

/--
The isomorphism of augmented module diagrams between scalar extension of the
underlying augmentation of `P` and the underlying augmentation of its scalar-changed
algebra. It includes the degreewise comparison and the comparison at the target `A`.
-/
def additiveAugmentedIso
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v w} k)).obj A)) :
    NormalizedAugmentation.mapped (groundModuleFunctor.{u, v, w} k K)
        (additiveAugmentedResolution.{u, max v w} k A P) ≅
      additiveAugmentedResolution.{w, max u v} K
        (target.{u, v, w} k K A) (resolution.{u, v, w} k K A P) := by
  let e := (Functor.associator P.left (algebraModuleFunctor.{u, max v w} k)
      (groundModuleFunctor.{u, v, w} k K)) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft P.left (algebraModuleBaseChangeNatIso.{u, v, w} k K) ≪≫
      (Functor.associator P.left (algebraFunctor.{u, v, w} k K) (algebraModuleFunctor.{w, max u v} K)).symm
  let a := algebraModuleBaseChangeIso.{u, v, w} k K A
  refine
    { hom :=
        { left := e.hom
          right := a.hom
          w := ?_ }
      inv :=
        { left := e.inv
          right := a.inv
          w := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply NatTrans.ext
    funext i
    have h := (algebraModuleBaseChangeIso_naturality.{u, v, w} k K (P.hom.app i)).symm
    change (algebraModuleBaseChangeIso.{u, v, w} k K (P.left.obj i)).hom ≫
        (algebraModuleFunctor.{w, max u v} K).map
          ((algebraFunctor.{u, v, w} k K).map (P.hom.app i)) =
      (groundModuleFunctor.{u, v, w} k K).map
        ((algebraModuleFunctor.{u, max v w} k).map (P.hom.app i)) ≫
          (algebraModuleBaseChangeIso.{u, v, w} k K A).hom
    exact h
  · apply NatTrans.ext
    funext i
    have h := ((algebraModuleBaseChangeNatIso.{u, v, w} k K).inv.naturality (P.hom.app i)).symm
    change (algebraModuleBaseChangeIso.{u, v, w} k K (P.left.obj i)).inv ≫
        (groundModuleFunctor.{u, v, w} k K).map
          ((algebraModuleFunctor.{u, max v w} k).map (P.hom.app i)) =
      (algebraModuleFunctor.{w, max u v} K).map
        ((algebraFunctor.{u, v, w} k K).map (P.hom.app i)) ≫
          (algebraModuleBaseChangeIso.{u, v, w} k K A).inv
    exact h
  · apply CommaMorphism.ext
    · exact e.hom_inv_id
    · exact a.hom_inv_id
  · apply CommaMorphism.ext
    · exact e.inv_hom_id
    · exact a.inv_hom_id

end CommAlgCat.CotangentPushout

end
