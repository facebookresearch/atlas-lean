/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monad.CartesianClassifyingBar
public import MathlibExt.CategoryTheory.Monad.TensorMonadNaturality
public import MathlibExt.CategoryTheory.Monad.BarChange
public import MathlibExt.CategoryTheory.Monad.BarRegularContraction
import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedWhiskering

/-!
# Functorial cartesian classifying bars and their augmentations

Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its terminal tensor unit. For an internal monoid M, the tensor monad T_M sends X to M⊗X. The
evaluated classifying and universal bars have degree-n objects B_M(n)=I⊗T_M^n(I) and
E_M(n)=T_M(T_M^n(I)).

An internal-monoid morphism f:M→N induces simplicial maps on both bars through the tensor-monad
morphism φ_X=f⊗id_X. If q_n is the induced map of n-th powers at I, the classifying-bar
component is id_I⊗q_n, and the universal-bar component is φ_{T_M^n(I)} followed by T_N(q_n).
These maps respect identities and composition.

The terminal augmentation M→I induces a natural simplicial bundle map E_M→B_M, applying the
augmentation to the outer M-coordinate. The regular universal-bar augmentation E_M→const(I) is
also natural in M. The canonical point I→E_M(0) is the tensor-monad unit, and internal-monoid
morphisms preserve it.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.Monad.ClassifyingBar

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {M N P : Mon C}

attribute [local instance] pointModObj

private noncomputable abbrev pointRightModule (M : Mon C) :=
  rightModuleOfRightAction (𝟙_ C) M.X (pointRightAction M)
    (pointRightAction_one M) (pointRightAction_assoc M)

private noncomputable abbrev pointLeftModule (M : Mon C) :=
  leftPointModule M.X (𝟙_ C)

private noncomputable def pointRightModuleHom (f : M ⟶ N) :
    pointRightModule M ⟶
      (rightModuleRestrictAlongHom (tensorMonadHom f)).obj (pointRightModule N) where
  f := 𝟙 _
  h := by
    apply NatTrans.ext
    funext X
    rw [Functor.map_id]
    unfold pointRightModule
    simp only [Category.id_comp, Category.comp_id,
      RightModule.restrictAlongHom_obj_action_app,
      rightModuleOfRightAction_action_app, tensorMonadHom_app]
    let map : ((𝟙_ C) ⊗ (M.X ⊗ X)) ⟶ ((𝟙_ C) ⊗ (N.X ⊗ X)) :=
      (pointRightModule N).functor.map (f.hom ▷ X)
    have hMap : map = (𝟙_ C) ◁ (f.hom ▷ X) := rfl
    have hActN : (pointRightModule N).action.app X =
        (α_ (𝟙_ C) N.X X).inv ≫ (pointRightAction N ▷ X) :=
      rightModuleOfRightAction_action_app _ _ _ _ _ _
    have hActM : (pointRightModule M).action.app X =
        (α_ (𝟙_ C) M.X X).inv ≫ (pointRightAction M ▷ X) :=
      rightModuleOfRightAction_action_app _ _ _ _ _ _
    apply CartesianMonoidalCategory.hom_ext
    · exact CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
    · calc
        (map ≫ (pointRightModule N).action.app X) ≫
            CartesianMonoidalCategory.snd (𝟙_ C) X =
          (((𝟙_ C) ◁ (f.hom ▷ X)) ≫
            ((α_ (𝟙_ C) N.X X).inv ≫ (pointRightAction N ▷ X))) ≫
              CartesianMonoidalCategory.snd (𝟙_ C) X := by
            exact congrArg (· ≫ CartesianMonoidalCategory.snd (𝟙_ C) X)
              (congrArg₂ (· ≫ ·) hMap hActN)
        _ = ((α_ (𝟙_ C) M.X X).inv ≫ (pointRightAction M ▷ X)) ≫
            CartesianMonoidalCategory.snd (𝟙_ C) X := by
          simp only [pointRightAction, Category.assoc,
            CartesianMonoidalCategory.whiskerRight_snd,
            CartesianMonoidalCategory.associator_inv_snd]
          rw [CartesianMonoidalCategory.whiskerLeft_snd_assoc,
            CartesianMonoidalCategory.whiskerRight_snd]
        _ = (pointRightModule M).action.app X ≫
            CartesianMonoidalCategory.snd (𝟙_ C) X :=
          congrArg (· ≫ CartesianMonoidalCategory.snd (𝟙_ C) X) hActM.symm

private noncomputable def pointLeftModuleHom (f : M ⟶ N) :
    pointLeftModule M ⟶
      (leftModuleRestrictAlongHom (tensorMonadHom f)).obj (pointLeftModule N) where
  f := 𝟙 _
  h := by
    apply NatTrans.ext
    funext a
    rw [Functor.map_id]
    simp only [Category.id_comp, Category.comp_id,
      LeftModule.restrictAlongHom_obj_action_app]
    unfold pointLeftModule
    change (tensorMonadHom f).app (𝟙_ C) ≫
        (pointLeftModule N).action.app a =
      (pointLeftModule M).action.app a
    exact CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

private noncomputable def classifyingBarRawMap (f : M ⟶ N) :
    classifyingBar M.X (𝟙_ C) (pointRightAction M)
        (pointRightAction_one M) (pointRightAction_assoc M) ⟶
      classifyingBar N.X (𝟙_ C) (pointRightAction N)
        (pointRightAction_one N) (pointRightAction_assoc N) :=
  twoSidedBarHom (pointRightModuleHom f) (pointLeftModuleHom f) ≫
    barChangeHom (tensorMonadHom f) (pointRightModule N) (pointLeftModule N)

private noncomputable def universalRightModuleHom (f : M ⟶ N) :
    rightModuleOfRightAction M.X M.X MonObj.mul (MonObj.mul_one M.X)
        ((MonObj.mul_assoc M.X).symm) ⟶
      (rightModuleRestrictAlongHom (tensorMonadHom f)).obj
        (rightModuleOfRightAction N.X N.X MonObj.mul (MonObj.mul_one N.X)
          ((MonObj.mul_assoc N.X).symm)) where
  f := (tensorMonadHom f).toNatTrans
  h := by
    apply NatTrans.ext
    funext X
    change (tensorMonadHom f).app ((tensorMonad M.X).obj X) ≫
        ((tensorMonad N.X).map ((tensorMonadHom f).app X) ≫
          (tensorMonad N.X).μ.app X) =
      (tensorMonad M.X).μ.app X ≫ (tensorMonadHom f).app X
    rw [← Category.assoc, ← (tensorMonadHom f).naturality]
    exact ((tensorMonadHom f).app_μ X).symm

private noncomputable def universalBarRawMap (f : M ⟶ N) :
    universalBar (M := M.X) (Pt := 𝟙_ C) ⟶
      universalBar (M := N.X) (Pt := 𝟙_ C) :=
  twoSidedBarHom (universalRightModuleHom f) (pointLeftModuleHom f) ≫
    barChangeHom (tensorMonadHom f)
      (rightModuleOfRightAction N.X N.X MonObj.mul (MonObj.mul_one N.X)
        ((MonObj.mul_assoc N.X).symm)) (pointLeftModule N)

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For an internal-monoid morphism f:M→N, let φ_X=f⊗id_X and
q_n:T_M^n(I)→T_N^n(I) be the component of the induced power morphism. The induced map
B(f):B_M→B_N is a morphism of simplicial objects. In degree n it is id_I⊗q_n:B_M(n)→B_N(n),
preserving the leading tensor-unit factor and all simplicial face and degeneracy maps. -/
noncomputable def classifyingBarMap (f : M ⟶ N) :
    (classifyingBar M.X (𝟙_ C) (pointRightAction M)
        (pointRightAction_one M) (pointRightAction_assoc M) ⋙ pointEvaluation C) ⟶
      (classifyingBar N.X (𝟙_ C) (pointRightAction N)
        (pointRightAction_one N) (pointRightAction_assoc N) ⋙ pointEvaluation C) :=
  Functor.whiskerRight (classifyingBarRawMap f) (pointEvaluation C)

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For an internal-monoid morphism f:M→N, let φ_X=f⊗id_X and
q_n:T_M^n(I)→T_N^n(I) be the component of the induced power morphism. The induced map
E(f):E_M→E_N is a morphism of simplicial objects. Its degree-n component is
φ_{T_M^n(I)}≫T_N(q_n), applying f to the outer monoid factor and the power comparison to the
remaining factors. -/
noncomputable def universalBarMap (f : M ⟶ N) :
    (universalBar (M := M.X) (Pt := 𝟙_ C) ⋙ pointEvaluation C) ⟶
      (universalBar (M := N.X) (Pt := 𝟙_ C) ⋙ pointEvaluation C) :=
  Functor.whiskerRight (universalBarRawMap f) (pointEvaluation C)

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For an internal-monoid morphism f:M→N, let φ_X=f⊗id_X and
q_n:T_M^n(I)→T_N^n(I) be the component of the induced power morphism. For every n≥0, the
component of B(f) at the simplicial object [n] is (id_I⊗q_n):I⊗T_M^n(I)→I⊗T_N^n(I). This is the
image of q_n under the functor I⊗(-). -/
theorem classifyingBarMap_app_op_mk (f : M ⟶ N) (n : ℕ) :
    (classifyingBarMap f).app (op (SimplexCategory.mk n)) =
      (tensorLeft (𝟙_ C)).map
        ((monadPowHom (tensorMonadHom f) n).app (𝟙_ C)) := by
  change (((classifyingBarRawMap f).app (op (SimplexCategory.mk n))).app index) = _
  unfold classifyingBarRawMap
  simp only [NatTrans.comp_app]
  rw [twoSidedBarHom_app_app_op_mk, barChangeHom_app_app_op_mk]
  simp only [pointLeftModuleHom, NatTrans.id_app, Functor.map_id,
    pointRightModuleHom, Category.id_comp]
  change 𝟙 _ ≫ (tensorLeft (𝟙_ C)).map
      ((monadPowHom (tensorMonadHom f) n).app (𝟙_ C)) = _
  rw [Category.id_comp]

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For an internal-monoid morphism f:M→N, let φ_X=f⊗id_X and
q_n:T_M^n(I)→T_N^n(I) be the component of the induced power morphism. For every n≥0,
E(f)_n=φ_{T_M^n(I)}≫T_N(q_n):T_M(T_M^n(I))→T_N(T_N^n(I)). The first map replaces the outer
M-factor by N; the second is id_N tensored with q_n. -/
theorem universalBarMap_app_op_mk (f : M ⟶ N) (n : ℕ) :
    (universalBarMap f).app (op (SimplexCategory.mk n)) =
      (tensorMonadHom f).app
          ((monadPow (tensorMonad M.X) n).obj (𝟙_ C)) ≫
        (tensorMonad N.X).map
          ((monadPowHom (tensorMonadHom f) n).app (𝟙_ C)) := by
  change (((universalBarRawMap f).app (op (SimplexCategory.mk n))).app index) = _
  unfold universalBarRawMap
  simp only [NatTrans.comp_app]
  rw [twoSidedBarHom_app_app_op_mk, barChangeHom_app_app_op_mk]
  simp only [pointLeftModuleHom, NatTrans.id_app, Functor.map_id,
    universalRightModuleHom, Category.id_comp]
  rfl

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For every internal monoid M, the simplicial map B(id_M):B_M→B_M
equals id_{B_M}. In each degree n≥0, the induced power comparison is the identity on T_M^n(I),
so the full component is the identity on I⊗T_M^n(I). -/
@[simp]
theorem classifyingBarMap_id (M : Mon C) :
    classifyingBarMap (𝟙 M) = 𝟙 _ := by
  ext Δ
  obtain ⟨⟨n⟩⟩ := Δ
  change (classifyingBarMap (𝟙 M)).app (op (SimplexCategory.mk n)) =
    𝟙 ((tensorLeft (𝟙_ C)).obj
      ((monadPow (tensorMonad M.X) n).obj (𝟙_ C)))
  rw [classifyingBarMap_app_op_mk, tensorMonadHom_id, monadPowHom_id]
  simp only [NatTrans.id_app, Functor.map_id]

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For internal-monoid morphisms f:M→N and g:N→P, B(f≫g)=B(f)≫B(g)
as simplicial maps B_M→B_P. Thus in each degree n the map of the nested monoid factors is the
composite of the corresponding power comparisons, tensored on the left with I. -/
@[simp]
theorem classifyingBarMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    classifyingBarMap (f ≫ g) = classifyingBarMap f ≫ classifyingBarMap g := by
  ext Δ
  obtain ⟨⟨n⟩⟩ := Δ
  rw [classifyingBarMap_app_op_mk, NatTrans.comp_app,
    classifyingBarMap_app_op_mk, classifyingBarMap_app_op_mk,
    tensorMonadHom_comp, monadPowHom_comp_app]
  exact Functor.map_comp _ _ _

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For every internal monoid M, E(id_M)=id_{E_M} as a simplicial
map. At every degree n≥0, the outer tensor-monad component and the power comparison are identity
morphisms of E_M(n)=T_M(T_M^n(I)). -/
@[simp]
theorem universalBarMap_id (M : Mon C) :
    universalBarMap (𝟙 M) = 𝟙 _ := by
  ext Δ
  obtain ⟨⟨n⟩⟩ := Δ
  change (universalBarMap (𝟙 M)).app (op (SimplexCategory.mk n)) =
    𝟙 ((tensorMonad M.X).obj
      ((monadPow (tensorMonad M.X) n).obj (𝟙_ C)))
  rw [universalBarMap_app_op_mk, tensorMonadHom_id, monadPowHom_id]
  simp only [NatTrans.id_app, Functor.map_id, Category.comp_id]
  rfl

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For internal-monoid morphisms f:M→N and g:N→P, the induced
simplicial maps satisfy E(f≫g)=E(f)≫E(g):E_M→E_P. Naturality of the tensor-monad comparison
combines the outer-factor map with the n-fold power comparison in each degree. -/
@[simp]
theorem universalBarMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    universalBarMap (f ≫ g) = universalBarMap f ≫ universalBarMap g := by
  ext Δ
  obtain ⟨⟨n⟩⟩ := Δ
  rw [universalBarMap_app_op_mk, NatTrans.comp_app,
    universalBarMap_app_op_mk, universalBarMap_app_op_mk,
    tensorMonadHom_comp, monadPowHom_comp_app, Functor.map_comp]
  simp only [MonadHom.comp_toNatTrans, NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, ← (tensorMonadHom g).naturality_assoc]

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. The functor B:Mon(C)→SimplicialObject(C) sends M to the evaluated
two-sided bar with trivial point actions and f:M→N to B(f). Its degree-n coefficient is
I⊗T_M^n(I), and its morphisms preserve identities, composition, faces, and degeneracies. -/
noncomputable def classifyingBarFunctor (C : Type u) [Category.{v} C]
    [CartesianMonoidalCategory C] : Mon C ⥤ SimplicialObject C where
  obj M := classifyingBar M.X (𝟙_ C) (pointRightAction M)
      (pointRightAction_one M) (pointRightAction_assoc M) ⋙ pointEvaluation C
  map f := classifyingBarMap f
  map_id M := classifyingBarMap_id M
  map_comp f g := classifyingBarMap_comp f g

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. The functor E:Mon(C)→SimplicialObject(C) sends M to the evaluated
bar with regular right M-module and trivial left point module. Its degree-n object is
T_M(T_M^n(I)), and f:M→N acts by φ_{T_M^n(I)} followed by T_N(q_n). -/
noncomputable def universalBarFunctor (C : Type u) [Category.{v} C]
    [CartesianMonoidalCategory C] : Mon C ⥤ SimplicialObject C where
  obj M := universalBar (M := M.X) (Pt := 𝟙_ C) ⋙ pointEvaluation C
  map f := universalBarMap f
  map_id M := universalBarMap_id M
  map_comp f g := universalBarMap_comp f g

@[simp]
theorem classifyingBarFunctor_obj (M : Mon C) :
    (classifyingBarFunctor C).obj M =
      classifyingBar M.X (𝟙_ C) (pointRightAction M)
        (pointRightAction_one M) (pointRightAction_assoc M) ⋙ pointEvaluation C :=
  rfl

@[simp]
theorem classifyingBarFunctor_map (f : M ⟶ N) :
    (classifyingBarFunctor C).map f = classifyingBarMap f :=
  rfl

@[simp]
theorem universalBarFunctor_obj (M : Mon C) :
    (universalBarFunctor C).obj M =
      universalBar (M := M.X) (Pt := 𝟙_ C) ⋙ pointEvaluation C :=
  rfl

@[simp]
theorem universalBarFunctor_map (f : M ⟶ N) :
    (universalBarFunctor C).map f = universalBarMap f :=
  rfl

private noncomputable def bundleRightModuleHom (M : Mon C) :
    rightModuleOfRightAction M.X M.X MonObj.mul (MonObj.mul_one M.X)
        ((MonObj.mul_assoc M.X).symm) ⟶
      pointRightModule M :=
  rightModuleHomOfRightComp (augmentation M) (augmentation_compat M)
    (h_one := MonObj.mul_one M.X)
    (h_assoc := (MonObj.mul_assoc M.X).symm)
    (h_one' := pointRightAction_one M)
    (h_assoc' := pointRightAction_assoc M)

private noncomputable def bundleLeftModuleHom (M : Mon C) :
    pointLeftModule M ⟶ pointLeftModule M :=
  leftPointModuleHomOfIsModHom (M := M.X) (𝟙 (𝟙_ C))

private noncomputable def universalBundleRawMap (M : Mon C) :
    universalBar (M := M.X) (Pt := 𝟙_ C) ⟶
      classifyingBar M.X (𝟙_ C) (pointRightAction M)
        (pointRightAction_one M) (pointRightAction_assoc M) :=
  twoSidedBarHom (bundleRightModuleHom M) (bundleLeftModuleHom M)

private theorem universalBundleRawMap_eq (M : Mon C) :
    universalBundleRawMap M =
      universalBundle M.X (𝟙_ C) (pointRightAction M)
        (pointRightAction_one M) (pointRightAction_assoc M)
        (augmentation M) (augmentation_compat M) :=
  rfl

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. Let ε_M:M→I be the unique terminal augmentation. The simplicial
morphism π_M:E_M→B_M is induced by ε_M on the regular right module and the identity on the left
point module. In degree n≥0 it is ε_M⊗id_{T_M^n(I)}:M⊗T_M^n(I)→I⊗T_M^n(I). -/
noncomputable def universalBundleMap (M : Mon C) :
    (universalBarFunctor C).obj M ⟶ (classifyingBarFunctor C).obj M :=
  Functor.whiskerRight (universalBundleRawMap M) (pointEvaluation C)

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For an internal monoid M and terminal augmentation ε_M:M→I,
π_M:E_M→B_M equals the evaluation at the unique point of the two-sided bar morphism induced by
ε_M and the identity left point map. The right point action I⊗M→I is the first projection, and
ε_M intertwines it with multiplication. -/
theorem universalBundleMap_eq (M : Mon C) :
    universalBundleMap M =
      Functor.whiskerRight
        (universalBundle M.X (𝟙_ C) (pointRightAction M)
          (pointRightAction_one M) (pointRightAction_assoc M)
          (augmentation M) (augmentation_compat M))
        (pointEvaluation C) :=
  rfl

private theorem universalBundleRightModuleHom_naturality (f : M ⟶ N) :
    universalRightModuleHom f ≫
        (rightModuleRestrictAlongHom (tensorMonadHom f)).map
          (bundleRightModuleHom N) =
      bundleRightModuleHom M ≫ pointRightModuleHom f := by
  ext X
  have hReg : (universalRightModuleHom f).f.app X =
      (tensorMonadHom f).app X := rfl
  have hAugN : (bundleRightModuleHom N).f.app X = augmentation N ▷ X := rfl
  have hAugM : (bundleRightModuleHom M).f.app X = augmentation M ▷ X := rfl
  have hPoint : (pointRightModuleHom f).f.app X = 𝟙 ((𝟙_ C) ⊗ X) := rfl
  have hDropN : (augmentation N ▷ X) ≫
      CartesianMonoidalCategory.snd (𝟙_ C) X =
        CartesianMonoidalCategory.snd N.X X := by
    unfold augmentation
    rw [← CartesianMonoidalCategory.leftUnitor_hom]
    exact CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom N.X X
  have hDropM : (augmentation M ▷ X) ≫
      CartesianMonoidalCategory.snd (𝟙_ C) X =
        CartesianMonoidalCategory.snd M.X X := by
    unfold augmentation
    rw [← CartesianMonoidalCategory.leftUnitor_hom]
    exact CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom M.X X
  apply CartesianMonoidalCategory.hom_ext
  · exact CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  · calc
      (((universalRightModuleHom f).f.app X ≫
            (bundleRightModuleHom N).f.app X) ≫
          CartesianMonoidalCategory.snd (𝟙_ C) X) =
        ((tensorMonadHom f).app X ≫ (augmentation N ▷ X)) ≫
          CartesianMonoidalCategory.snd (𝟙_ C) X := by
            rw [hReg, hAugN]
      _ = (f.hom ▷ X) ≫
          ((augmentation N ▷ X) ≫
            CartesianMonoidalCategory.snd (𝟙_ C) X) := by
            rw [tensorMonadHom_app, Category.assoc]
      _ = (f.hom ▷ X) ≫ CartesianMonoidalCategory.snd N.X X := by
            rw [hDropN]
      _ = CartesianMonoidalCategory.snd M.X X :=
        CartesianMonoidalCategory.whiskerRight_snd f.hom X
      _ = (augmentation M ▷ X) ≫
          CartesianMonoidalCategory.snd (𝟙_ C) X := hDropM.symm
      _ = (((bundleRightModuleHom M).f.app X ≫
            (pointRightModuleHom f).f.app X) ≫
          CartesianMonoidalCategory.snd (𝟙_ C) X) := by
            have hId : augmentation M ▷ X =
                (augmentation M ▷ X) ≫ 𝟙 ((𝟙_ C) ⊗ X) :=
              (Category.comp_id _).symm
            have hPost := congrArg
              (· ≫ CartesianMonoidalCategory.snd (𝟙_ C) X)
              (congrArg₂ (· ≫ ·) hAugM hPoint)
            exact (congrArg
              (· ≫ CartesianMonoidalCategory.snd (𝟙_ C) X) hId).trans hPost.symm

private theorem universalBundleLeftModuleHom_naturality (f : M ⟶ N) :
    pointLeftModuleHom f ≫
        (leftModuleRestrictAlongHom (tensorMonadHom f)).map
          (bundleLeftModuleHom N) =
      bundleLeftModuleHom M ≫ pointLeftModuleHom f := by
  ext a
  rfl

private theorem universalBundlePreChange_naturality (f : M ⟶ N) :
    twoSidedBarHom (universalRightModuleHom f) (pointLeftModuleHom f) ≫
        twoSidedBarHom
          ((rightModuleRestrictAlongHom (tensorMonadHom f)).map
            (bundleRightModuleHom N))
          ((leftModuleRestrictAlongHom (tensorMonadHom f)).map
            (bundleLeftModuleHom N)) =
      twoSidedBarHom (bundleRightModuleHom M)
          (bundleLeftModuleHom M) ≫
        twoSidedBarHom (pointRightModuleHom f) (pointLeftModuleHom f) := by
  rw [twoSidedBarHom_comp, twoSidedBarHom_comp,
    universalBundleRightModuleHom_naturality,
    universalBundleLeftModuleHom_naturality]

private theorem universalBundleRaw_naturality (f : M ⟶ N) :
    universalBarRawMap f ≫ universalBundleRawMap N =
      universalBundleRawMap M ≫ classifyingBarRawMap f := by
  let h := tensorMonadHom f
  let preE := twoSidedBarHom (universalRightModuleHom f) (pointLeftModuleHom f)
  let changeE := barChangeHom h
    (rightModuleOfRightAction N.X N.X MonObj.mul (MonObj.mul_one N.X)
      ((MonObj.mul_assoc N.X).symm)) (pointLeftModule N)
  let augN := twoSidedBarHom (bundleRightModuleHom N)
    (bundleLeftModuleHom N)
  let augM := twoSidedBarHom (bundleRightModuleHom M)
    (bundleLeftModuleHom M)
  let augN' := twoSidedBarHom
    ((rightModuleRestrictAlongHom h).map (bundleRightModuleHom N))
    ((leftModuleRestrictAlongHom h).map (bundleLeftModuleHom N))
  let changeB := barChangeHom h (pointRightModule N) (pointLeftModule N)
  let preB := twoSidedBarHom (pointRightModuleHom f) (pointLeftModuleHom f)
  have hMixed : changeE ≫ augN = augN' ≫ changeB :=
    (barChangeHom_naturality h (bundleRightModuleHom N)
      (bundleLeftModuleHom N)).symm
  have hPre : preE ≫ augN' = augM ≫ preB :=
    universalBundlePreChange_naturality f
  unfold universalBarRawMap classifyingBarRawMap universalBundleRawMap
  change (preE ≫ changeE) ≫ augN = augM ≫ (preB ≫ changeB)
  calc
    _ = preE ≫ (changeE ≫ augN) := Category.assoc _ _ _
    _ = preE ≫ (augN' ≫ changeB) := congrArg (preE ≫ ·) hMixed
    _ = (preE ≫ augN') ≫ changeB := (Category.assoc _ _ _).symm
    _ = (augM ≫ preB) ≫ changeB := congrArg (· ≫ changeB) hPre
    _ = augM ≫ (preB ≫ changeB) := Category.assoc _ _ _

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For an internal-monoid morphism f:M→N, the simplicial square
E(f)≫π_N=π_M≫B(f) commutes. Here π_M:E_M→B_M and π_N:E_N→B_N apply the respective terminal
augmentations to the outer regular-module coordinate. -/
theorem universalBundle_naturality (f : M ⟶ N) :
    universalBarMap f ≫ universalBundleMap N =
      universalBundleMap M ≫ classifyingBarMap f := by
  unfold universalBarMap classifyingBarMap universalBundleMap
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp]
  exact congrArg (fun q => Functor.whiskerRight q (pointEvaluation C))
    (universalBundleRaw_naturality f)

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. The simplicial bundle maps π_M:E_M→B_M define a natural
transformation π:E⇒B between functors Mon(C)→SimplicialObject(C). Its component at M applies
ε_M:M→I to the outer monoid coordinate, and its naturality equation is E(f)≫π_N=π_M≫B(f). -/
noncomputable def universalBundleNatTrans (C : Type u) [Category.{v} C]
    [CartesianMonoidalCategory C] :
    universalBarFunctor C ⟶ classifyingBarFunctor C where
  app M := universalBundleMap M
  naturality _ _ f := universalBundle_naturality f

@[simp]
theorem universalBundleNatTrans_app (M : Mon C) :
    (universalBundleNatTrans C).app M = universalBundleMap M :=
  rfl

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. The regular balanced pairing of the tensor monad gives an
augmented simplicial object with left object E_M and augmentation target I. Its augmentation
E_M→const(I) has, in every degree n≥0, the unique map E_M(n)→I. The left point coefficient is
the trivial M-module I. -/
noncomputable def universalBarAugmented (M : Mon C) :
    SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj _ _ (pointEvaluation C)).obj
    (BalancedPairing.toSimplicialAugmented
      (BarRegularContraction.regularBalancedPairing (pointLeftModule M)))

@[simp]
theorem universalBarAugmented_left (M : Mon C) :
    (universalBarAugmented M).left = (universalBarFunctor C).obj M :=
  by
    unfold universalBarAugmented universalBarFunctor
    rfl

@[simp]
theorem universalBarAugmented_right (M : Mon C) :
    (universalBarAugmented M).right = 𝟙_ C :=
  by
    unfold universalBarAugmented
    rfl

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For each internal monoid M, the augmented regular bar gives a
simplicial map a_M:E_M→const(I). Its degree-n component is the unique morphism T_M(T_M^n(I))→I,
and all face and degeneracy compatibility equations have terminal target I. -/
noncomputable def universalBarAugmentationMap (M : Mon C) :
    (universalBarFunctor C).obj M ⟶
      (SimplicialObject.const C).obj (𝟙_ C) :=
  by
    change (universalBarAugmented M).left ⟶
      (SimplicialObject.const C).obj (universalBarAugmented M).right
    exact (universalBarAugmented M).hom

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. The functor K:Mon(C)→SimplicialObject(C) sends every internal monoid to the
constant simplicial object const(I), with value I in every degree, and every monoid morphism to
its identity simplicial map. -/
noncomputable def tensorUnitSimplicialFunctor
    (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] :
    Mon C ⥤ SimplicialObject C :=
  (Functor.const (Mon C)).obj ((SimplicialObject.const C).obj (𝟙_ C))

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For an internal-monoid morphism f:M→N and the regular
augmentations a_M:E_M→const(I), a_N:E_N→const(I), the identity E(f)≫a_N=a_M holds as a
simplicial map. Its degree-n equation equates two maps E_M(n)→the terminal unit I. -/
theorem universalBarAugmentation_naturality (f : M ⟶ N) :
    universalBarMap f ≫ universalBarAugmentationMap N =
      universalBarAugmentationMap M := by
  apply NatTrans.ext
  funext Δ
  exact CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. Let K:Mon(C)→SimplicialObject(C) be constant at const(I). The
regular augmentations define a natural transformation a:E⇒K with component a_M:E_M→const(I). For
f:M→N, naturality is E(f)≫a_N=a_M because K(f) is the identity. -/
noncomputable def universalBarAugmentationNatTrans
    (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] :
    universalBarFunctor C ⟶ tensorUnitSimplicialFunctor C where
  app M := universalBarAugmentationMap M
  naturality _ _ f := by
    change universalBarMap f ≫ universalBarAugmentationMap _ =
      universalBarAugmentationMap _ ≫ 𝟙 _
    rw [universalBarAugmentation_naturality, Category.comp_id]

@[simp]
theorem universalBarAugmentationNatTrans_app (M : Mon C) :
    (universalBarAugmentationNatTrans C).app M =
      universalBarAugmentationMap M :=
  rfl

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For an internal monoid M, the canonical point
s_M:I→E_M(0)=T_M(I)=M⊗I is the tensor-monad unit η^M_I. It inserts the monoid unit into the
regular right-module factor while retaining the tensor-unit coefficient. -/
noncomputable def universalBarSection (M : Mon C) :
    (𝟙_ C) ⟶ ((universalBarFunctor C).obj M).obj
      (op (SimplexCategory.mk 0)) :=
  (BarRegularContraction.s' (pointLeftModule M)).app index

/-- Let C be a cartesian monoidal category with independent object and morphism universes u,v, and I
its tensor unit. For an internal monoid M, put T_M(X)=M⊗X, B_M(n)=I⊗T_M^n(I), and
E_M(n)=T_M(T_M^n(I)), for n≥0. For f:M→N, the degree-zero points s_M:I→E_M(0) and s_N:I→E_N(0)
satisfy s_M≫E(f)_0=s_N. They are the tensor-monad units at I, and this equality is preservation
of the internal monoid unit under f. -/
theorem universalBarSection_naturality (f : M ⟶ N) :
    universalBarSection M ≫
        ((universalBarFunctor C).map f).app (op (SimplexCategory.mk 0)) =
      universalBarSection N := by
  unfold universalBarSection
  rw [universalBarFunctor_map]
  change (BarRegularContraction.s' (pointLeftModule M)).app index ≫
      (universalBarMap f).app (op (SimplexCategory.mk 0)) =
    (BarRegularContraction.s' (pointLeftModule N)).app index
  rw [universalBarMap_app_op_mk]
  simp only [BarRegularContraction.s'_app, Functor.id_obj,
    monadPowHom_zero_app, Functor.map_id, Category.comp_id]
  exact tensorMonadHom_η f (𝟙_ C)

end CategoryTheory.Monad.ClassifyingBar

end
