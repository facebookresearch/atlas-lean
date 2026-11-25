/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Monad.BarChange
public import MathlibExt.CategoryTheory.Monad.BarEilenbergMoore
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Functor-valued bar of an adjunction

For an adjunction `adj : F ⊣ U` with `F : C ⥤ D` and `U : D ⥤ C`, write
`T := adj.toMonad : Monad C` for the pinned induced monad on the source. Its
underlying functor is `F ⋙ U`, its unit is `adj.unit`, and its multiplication
acts pointwise by `U.map (adj.counit.app _)`.

The left adjoint carries a canonical right `T`-module (`adjRightModule`) whose
action at `X` is the counit at `F.obj X`; the unit law is the left triangle
identity and associativity is naturality of the counit. Dually, the right
adjoint carries a canonical left `T`-module (`adjLeftModule`) whose action at
`Y` is `U.map (adj.counit.app Y)`; the unit law is the right triangle identity
while naturality and associativity follow from naturality of the counit.

Instantiating the accepted Cat-valued two-sided bar at these modules gives the
strict functor-valued resolution `adjBar adj : SimplicialObject (D ⥤ D)`, i.e.
`B(F, F ⋙ U, U)`. In degree `n` at `Y : D` this is `F (Tⁿ (U Y))`; faces and
degeneracies are inherited, with computation lemmas below. The counit
`U ⋙ F ⟶ 𝟭 D` equalizes the two degree-zero faces (again by counit
naturality), so it induces a balanced pairing (`adjBalancedPairing`) and hence
a genuine augmentation `adjAugmented adj` of the bar over the identity
endofunctor of `D`.

All computation lemmas are thin specializations of the accepted `twoSidedBar`
and `BalancedPairing` APIs; no simplicial identity is reproved. Functoriality
in module morphisms is inherited from `twoSidedBarHom` (recorded as the
identity law); no product-category bifunctor is bundled.

The evaluated/forgotten adjunction augmentation is compared with the
Eilenberg--Moore underlying augmentation (`emUnderlyingAugmented`) by a
canonical one-way augmented morphism (`adjToEMComparison`), assembled from
`Adjunction.adjToMonadIso`, restriction of scalars, `barChangeHom`, and the
accepted outer-whiskering/evaluation isomorphisms. The comparison is not
asserted to be an isomorphism.

Explicit nonclaims: no contraction in `T.Algebra`; no monadicity, equivalence,
realization, derived, operadic, or enriched statement; and no naturality in a
morphism of adjunctions (change-of-adjunction). Endpoint-face comparison via
`BarChange` is available and used here.

Mathematical source: J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.
This file is the functor-valued form `B(F,UF,U)` of May's two-sided bar for
the monad induced by the adjunction, augmented over the identity endofunctor
by the counit; it is the functor-valued form behind the usual monadic
resolution. Degree and face/degeneracy conventions are inherited from `Bar`.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {F : C ⥤ D} {U : D ⥤ C}

section AdjModules

/-- Canonical right `adj.toMonad`-module carried by the left adjoint: the
action at `X` is the counit at `F.obj X`. The unit law is the left triangle
identity and associativity is naturality of the counit. -/
def adjRightModule (adj : F ⊣ U) : RightModule adj.toMonad D :=
  RightModule.mk F
    { app := fun X => adj.counit.app (F.obj X)
      naturality := fun _X _Y f => adj.counit.naturality (F.map f) }
    (fun X => adj.left_triangle_components X)
    (fun X => adj.counit.naturality (adj.counit.app (F.obj X)))

/-- The underlying functor of the right module is the left adjoint. -/
@[simp]
theorem adjRightModule_functor (adj : F ⊣ U) :
    (adjRightModule adj).functor = F :=
  rfl

/-- The right-module action is pointwise the counit at `F.obj X`. -/
@[simp]
theorem adjRightModule_action_app (adj : F ⊣ U) (X : C) :
    (adjRightModule adj).action.app X = adj.counit.app (F.obj X) :=
  rfl

/-- Canonical left `adj.toMonad`-module carried by the right adjoint: the
action at `Y` is `U.map` of the counit at `Y`. The unit law is the right
triangle identity; naturality and associativity follow from naturality of the
counit after splitting `U.map` over composition. -/
def adjLeftModule (adj : F ⊣ U) : LeftModule D adj.toMonad :=
  LeftModule.mk U
    { app := fun Y => U.map (adj.counit.app Y)
      naturality := fun Y₁ Y₂ g => by
        have h := congrArg (U.map) (adj.counit.naturality g)
        simp only [Functor.map_comp, Functor.id_map] at h
        exact h }
    (fun Y => adj.right_triangle_components Y)
    (fun Y => by
      have h :=
        congrArg (U.map) (adj.counit.naturality (adj.counit.app Y))
      simp only [Functor.map_comp, Functor.id_map] at h
      exact h.symm)

/-- The underlying functor of the left module is the right adjoint. -/
@[simp]
theorem adjLeftModule_functor (adj : F ⊣ U) :
    (adjLeftModule adj).functor = U :=
  rfl

/-- The left-module action is `U.map` of the counit. -/
@[simp]
theorem adjLeftModule_action_app (adj : F ⊣ U) (Y : D) :
    (adjLeftModule adj).action.app Y = U.map (adj.counit.app Y) :=
  rfl

end AdjModules

section AdjBar

/-- Functor-valued bar of an adjunction: the accepted two-sided bar at the
canonical modules, a simplicial endofunctor on the target `D`. -/
noncomputable def adjBar (adj : F ⊣ U) : SimplicialObject (D ⥤ D) :=
  twoSidedBar adj.toMonad (adjRightModule adj) (adjLeftModule adj)

/-- Degree `n` is the levelwise bar object. -/
@[simp]
theorem adjBar_obj (adj : F ⊣ U) (n : ℕ) :
    (adjBar adj).obj (Opposite.op (SimplexCategory.mk n)) =
      barObj adj.toMonad (adjRightModule adj) (adjLeftModule adj) n :=
  rfl

/-- Degree `n` at `Y : D` is `F` applied to `Tⁿ (U.obj Y)`. -/
@[simp]
theorem adjBar_obj_obj (adj : F ⊣ U) (n : ℕ) (Y : D) :
    ((adjBar adj).obj (Opposite.op (SimplexCategory.mk n))).obj Y =
      F.obj ((monadPow adj.toMonad n).obj (U.obj Y)) :=
  rfl

/-- Functoriality on morphisms in `D` passes through `F`, `Tⁿ`, and `U`. -/
@[simp]
theorem adjBar_obj_map (adj : F ⊣ U) {n : ℕ} {Y Z : D} (g : Y ⟶ Z) :
    ((adjBar adj).obj (Opposite.op (SimplexCategory.mk n))).map g =
      F.map ((monadPow adj.toMonad n).map (U.map g)) :=
  rfl

/-- Degree zero is the comonad functor `U ⋙ F` on `D`. -/
theorem adjBar_obj_zero (adj : F ⊣ U) :
    (adjBar adj).obj (Opposite.op (SimplexCategory.mk 0)) = U ⋙ F :=
  barObj_zero adj.toMonad (adjRightModule adj) (adjLeftModule adj)

/-- Faces are the two-sided faces at the adjunction modules. -/
@[simp]
theorem adjBar_map_δ_op (adj : F ⊣ U) {n : ℕ} (i : Fin (n + 2)) :
    (adjBar adj).map (SimplexCategory.δ i).op =
      barFace (T := adj.toMonad) (R := adjRightModule adj)
        (L := adjLeftModule adj) n i :=
  twoSidedBar_map_δ_op _ _ _ _

/-- Degeneracies are the two-sided degeneracies at the adjunction modules. -/
@[simp]
theorem adjBar_map_σ_op (adj : F ⊣ U) {n : ℕ} (i : Fin (n + 1)) :
    (adjBar adj).map (SimplexCategory.σ i).op =
      barDegeneracy (T := adj.toMonad) (R := adjRightModule adj)
        (L := adjLeftModule adj) n i :=
  twoSidedBar_map_σ_op _ _ _ _

/-- Face components are the elementary `barFaceApp` operators. -/
@[simp]
theorem adjBar_map_δ_op_app (adj : F ⊣ U) {n : ℕ} (i : Fin (n + 2))
    (Y : D) :
    ((adjBar adj).map (SimplexCategory.δ i).op).app Y =
      barFaceApp (T := adj.toMonad) (R := adjRightModule adj)
        (L := adjLeftModule adj) n i Y := by
  rw [adjBar_map_δ_op]
  rfl

/-- Degeneracy components insert the unit via `barEtaAtPos`. -/
@[simp]
theorem adjBar_map_σ_op_app (adj : F ⊣ U) {n : ℕ} (i : Fin (n + 1))
    (Y : D) :
    ((adjBar adj).map (SimplexCategory.σ i).op).app Y =
      F.map (barEtaAtPos adj.toMonad n i (U.obj Y)) := by
  rw [adjBar_map_σ_op]
  rfl

end AdjBar

section AdjAugmentation

/-- Degree-zero pairing for the adjunction bar: the counit `U ⋙ F ⟶ 𝟭 D`,
well typed since `barObj _ _ _ 0` is definitionally `U ⋙ F`. -/
def adjPairing (adj : F ⊣ U) :
    barObj adj.toMonad (adjRightModule adj) (adjLeftModule adj) 0 ⟶ 𝟭 D :=
  adj.counit

/-- The pairing acts as the counit at every `Y : D`. -/
@[simp]
theorem adjPairing_app (adj : F ⊣ U) (Y : D) :
    (adjPairing adj).app Y = adj.counit.app Y :=
  rfl

/-- Balanced pairing for the adjunction bar, from the pointwise action
equation: both composites are `ε ≫ ε` versus `F.map (U.map ε) ≫ ε`, equal by
naturality of the counit. -/
noncomputable def adjBalancedPairing (adj : F ⊣ U) :
    BalancedPairing adj.toMonad (adjRightModule adj) (adjLeftModule adj) :=
  BalancedPairing.mkOfActionEq (adjPairing adj) (fun Y =>
    (adj.counit.naturality (adj.counit.app Y)).symm)

/-- The balanced-pairing target is the identity endofunctor. -/
@[simp]
theorem adjBalancedPairing_target (adj : F ⊣ U) :
    (adjBalancedPairing adj).target = 𝟭 D :=
  rfl

/-- The balanced-pairing map is the counit pairing. -/
@[simp]
theorem adjBalancedPairing_pairing (adj : F ⊣ U) :
    (adjBalancedPairing adj).pairing = adjPairing adj :=
  rfl

/-- Augmented adjunction bar over the identity endofunctor, via the genuine
transport of the balanced pairing. -/
noncomputable def adjAugmented (adj : F ⊣ U) :
    SimplicialObject.Augmented (D ⥤ D) :=
  BalancedPairing.toSimplicialAugmented (adjBalancedPairing adj)

/-- The underlying simplicial object is the adjunction bar. -/
@[simp]
theorem adjAugmented_left (adj : F ⊣ U) :
    (adjAugmented adj).left = adjBar adj :=
  rfl

/-- The augmentation target is the identity endofunctor. -/
@[simp]
theorem adjAugmented_right (adj : F ⊣ U) :
    (adjAugmented adj).right = 𝟭 D :=
  rfl

/-- The augmentation point is the identity endofunctor. -/
@[simp]
theorem adjAugmented_point_obj (adj : F ⊣ U) :
    (SimplicialObject.Augmented.point.obj (adjAugmented adj)) = 𝟭 D :=
  rfl

/-- The augmentation at an arbitrary simplex is the data-level extension. -/
theorem adjAugmented_hom_app_mk (adj : F ⊣ U) (n : ℕ) :
    (adjAugmented adj).hom.app (Opposite.op (SimplexCategory.mk n)) =
      (adjBalancedPairing adj).toDataHom.app n :=
  BalancedPairing.toSimplicialAugmented_hom_app_mk _ _

/-- The degree-zero augmentation component is the counit pairing. -/
@[simp]
theorem adjAugmented_hom_zero (adj : F ⊣ U) :
    (adjAugmented adj).hom.app (Opposite.op (SimplexCategory.mk 0)) =
      adjPairing adj := by
  change (BalancedPairing.toSimplicialAugmented (adjBalancedPairing adj)).hom.app
    (Opposite.op (SimplexCategory.mk 0)) = _
  rw [BalancedPairing.toSimplicialAugmented_hom_app_mk,
    BalancedPairing.toDataHom_app_zero, adjBalancedPairing_pairing]

end AdjAugmentation

section AdjEMComparison

variable {T : Monad C}

/-- Monad morphism from the free–forgetful monad to `T` (components are identities). -/
private def adjMonadHom : T.adj.toMonad ⟶ T :=
  (Adjunction.adjToMonadIso T).hom

private theorem adjMonadHom_app (X : C) :
    (adjMonadHom (T := T)).app X = 𝟙 _ := rfl

/-- Algebra for the free–forgetful monad induced by `alg`, via restriction. -/
private def adjAlg (alg : T.Algebra) : T.adj.toMonad.Algebra :=
  (algebraFunctorOfMonadHom (adjMonadHom (T := T))).obj alg

/-- Right-module comparison over the free–forgetful monad: the adjunction
right module postcomposed with forget agrees with the restricted forgotten
free module. Both carry `T.free ⋙ T.forget`; the actions agree by counit
naturality with identity comparisons via `(Adjunction.adjToMonadIso T).hom`. -/
private def adjRightIso :
    (adjRightModule T.adj).postcomp T.forget ≅
      (rightModuleRestrictAlongHom (D := C) adjMonadHom).obj
        (emRightModule.postcomp T.forget) := by
  refine Algebra.isoMk (Iso.refl _) ?_
  ext X
  simp only [RightModule.postcomp_functor, adjRightModule_functor, Functor.comp_obj,
    RightModule.restrictAlongHom_obj_A, emRightModule_functor, Iso.refl_hom,
    Functor.whiskerLeft_id', algebraFunctorOfMonadHom_obj_a, precompMonadHom_app,
    RightModule.action_app, Category.id_comp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.comp_map, forget_map, free_map_f,
    Category.comp_id]
  rw [adjMonadHom_app]
  change T.map (𝟙 (T.obj X)) ≫ T.forget.map (emRightModule.a.app X) =
    T.forget.map ((adjRightModule T.adj).a.app X)
  rw [Functor.map_id]
  refine (Category.id_comp _).trans ?_
  rw [Monad.forget_map, Monad.forget_map, emRightModule_action_f]
  simp only [adjRightModule_action_app]
  simp
  rfl

/-- Left-module comparison over the free–forgetful monad: the terminal-index
module of `adjAlg alg` agrees with the restricted terminal-index module of
`alg`. Both carry the constant functor at `alg.A` with action from `alg.a`
up to identity comparisons via `(Adjunction.adjToMonadIso T).hom`. -/
private def adjLeftIso (alg : T.Algebra) :
    algebraLeftModule (adjAlg alg) ≅
      (leftModuleRestrictAlongHom (A := Discrete PUnit.{1}) adjMonadHom).obj
        (algebraLeftModule alg) := by
  refine Algebra.isoMk (Iso.refl _) ?_
  ext X
  rw [NatTrans.comp_app, NatTrans.comp_app,
    leftModuleRestrictAlongHom_obj_action_app,
    algebraLeftModule_action_app, adjMonadHom_app,
    Iso.refl_hom]
  simp only [NatTrans.id_app,
    ← LeftModule.action_app, algebraLeftModule_action_app, adjAlg,
    algebraFunctorOfMonadHom_obj_a, adjMonadHom_app]
  have hw1 : (Functor.whiskerRight (𝟙 (algebraLeftModule
      ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).obj alg)).A)
      T.adj.toMonad.toFunctor).app X = 𝟙 _ := by simp
  have hL : (Functor.whiskerRight (𝟙 (algebraLeftModule
      ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).obj alg)).A)
      T.adj.toMonad.toFunctor).app X ≫ 𝟙 _ ≫ alg.a = alg.a :=
    (congrArg (· ≫ (𝟙 _ ≫ alg.a)) hw1).trans
      ((Category.id_comp _).trans (Category.id_comp _))
  have hR : (𝟙 _ ≫ alg.a) ≫ 𝟙 _ = alg.a := by simp
  exact hL.trans hR.symm

/-- Underlying balanced pairing for the adjunction side, mirroring
`emUnderlyingPairing`: target the regular target and pair by `alg.a` via
`adjAlg`. -/
private noncomputable def adjUnderlyingPairing (alg : T.Algebra) :
    BalancedPairing T.adj.toMonad ((adjRightModule T.adj).postcomp T.forget)
      (algebraLeftModule (adjAlg alg)) where
  target := BarRegularContraction.regularTarget (algebraLeftModule (adjAlg alg))
  pairing :=
    { app := fun _ => (adjAlg alg).a
      naturality := fun _ _ _ => by
        change T.adj.toMonad.map (𝟙 _) ≫ (adjAlg alg).a = (adjAlg alg).a ≫ 𝟙 _
        simp }
  balanced :=
    (isBalancedPairing_iff_action_eq (T := T.adj.toMonad)).mpr
      (fun a => (adjAlg alg).assoc)

/-- Evaluated/forgotten adjunction augmentation over `C`, mirroring
`emUnderlyingAugmented`: whisker the adjunction pairing with
`resolutionEvalPoint`. Its formal relation to the literal
forgetful/evaluated image of `adjAugmented T.adj` is recorded in
`adjLiteralAugmented` and `adjLiteralIso` below: the literal image is the
whiskered `adjAugmented T.adj`, naturally isomorphic to this surrogate model. -/
@[no_expose]
noncomputable def adjEvaluatedAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).obj
    (BalancedPairing.toSimplicialAugmented (adjUnderlyingPairing alg))

/-- Auxiliary point identity, proved by unfolding the opaque surrogate
(private so the unfolding is permitted). -/
private theorem adjEvaluatedAugmented_point_aux (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).right = alg.A :=
  rfl

/-- The augmentation target is the algebra carrier. -/
@[simp]
theorem adjEvaluatedAugmented_point (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).right = alg.A :=
  adjEvaluatedAugmented_point_aux alg

/-- Auxiliary degree-zero object identity, proved by unfolding the opaque surrogate
(private so the unfolding is permitted). -/
private theorem adjEvaluatedAugmented_obj_zero_aux (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).left.obj
      (Opposite.op (SimplexCategory.mk 0)) = T.obj alg.A :=
  rfl

/-- Degree-zero object law for the evaluated augmentation, private-name-free:
the degree-zero bar object is the monad applied to the carrier. -/
@[simp]
theorem adjEvaluatedAugmented_obj_zero (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).left.obj
      (Opposite.op (SimplexCategory.mk 0)) = T.obj alg.A :=
  adjEvaluatedAugmented_obj_zero_aux alg

/-- Evaluation at an algebra, mirroring `emEvalAlgebra`: applying an
`Algebra`-valued endofunctor diagram to `alg`. -/
noncomputable def adjEvalAlgebra (alg : T.Algebra) :
    (T.Algebra ⥤ T.Algebra) ⥤ T.Algebra :=
  (evaluation _ _).obj alg

/-- The literal forgetful image in `C`: `adjAugmented T.adj` evaluated at `alg`
then whiskered with `T.forget`. This is the honest evaluated/forgotten object;
`adjEvaluatedAugmented` above is the reusable surrogate model. -/
noncomputable def adjLiteralAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj _ _
    (adjEvalAlgebra alg ⋙ T.forget)).obj (adjAugmented T.adj)

/-- The underlying simplicial object of the literal image is the evaluated bar
postcomposed with the forgetful functor. -/
@[simp]
theorem adjLiteralAugmented_left (alg : T.Algebra) :
    (adjLiteralAugmented alg).left =
      (adjAugmented T.adj).left ⋙ (adjEvalAlgebra alg ⋙ T.forget) := by
  unfold adjLiteralAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_left]
  rfl

/-- The augmentation point of the literal image is the algebra carrier. -/
@[simp]
theorem adjLiteralAugmented_point (alg : T.Algebra) :
    (adjLiteralAugmented alg).right = alg.A :=
  rfl

/-- Degree-zero object law for the literal image. -/
@[simp]
theorem adjLiteralAugmented_obj_zero (alg : T.Algebra) :
    (adjLiteralAugmented alg).left.obj
      (Opposite.op (SimplexCategory.mk 0)) = T.obj alg.A :=
  rfl

/-- Evaluation at algebras, forgotten to `C`, is natural in the algebra
morphism: at an `Algebra`-valued endofunctor `F`, act by `F.map φ` then
forget. Genuine evaluation naturality, no surrogate involved. Public because
the headline literal maps whisker along it. -/
noncomputable def adjEvalForgetNatTrans {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    (adjEvalAlgebra alg ⋙ T.forget) ⟶ (adjEvalAlgebra alg' ⋙ T.forget) :=
  Functor.whiskerRight ((evaluation T.Algebra T.Algebra).map φ) T.forget

/-- Maps induced by algebra morphisms on the literal forgetful image: whisker
the genuine functor-valued adjunction augmentation along evaluation
naturality. No surrogate reconstruction. -/
noncomputable def adjLiteralHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    adjLiteralAugmented alg ⟶ adjLiteralAugmented alg' :=
  ((SimplicialObject.Augmented.whiskering (T.Algebra ⥤ T.Algebra) C).map
    (adjEvalForgetNatTrans φ)).app (adjAugmented T.adj)

/-- The target component of a literal map is the algebra morphism itself:
evaluating the identity endofunctor at `φ` then forgetting is `φ.f`. -/
theorem adjLiteralHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (adjLiteralHom φ).right = φ.f :=
  rfl

/-- The simplicial component of a literal map acts by the forgotten
endofunctor map: at `Δ`, apply `(adjBar T.adj).obj Δ` to `φ` then forget.
Private-name-free: only the public bar, forgetful functor, and `φ`. -/
theorem adjLiteralHom_left_app {alg alg' : T.Algebra} (φ : alg ⟶ alg')
    (Δ : SimplexCategoryᵒᵖ) :
    ((adjLiteralHom φ).left).app Δ =
      T.forget.map (((adjBar T.adj).obj Δ).map φ) :=
  rfl

/-- Identity algebra morphisms induce identity literal maps. -/
theorem adjLiteralHom_id (alg : T.Algebra) :
    adjLiteralHom (𝟙 alg) = 𝟙 (adjLiteralAugmented alg) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · ext Δ
    -- Restate defeq (via `adjLiteralHom_left_app`) so neither side
    -- mentions an identity projection; then two `map_id`s close it.
    change T.forget.map ((((adjAugmented T.adj).left).obj Δ).map (𝟙 alg)) =
      𝟙 _
    simp only [Functor.map_id]
  · -- Mirror `emHom_id`, chaining through the algebra identity law
    -- (never projecting `.f` off `𝟙` directly); the final link is
    -- definitional on objects.
    have e1 : (adjLiteralHom (𝟙 alg)).right = 𝟙 alg.A :=
      (adjLiteralHom_right _).trans (Algebra.id_f _)
    have e3r : (𝟙 alg.A) = 𝟙 (adjLiteralAugmented alg).right := rfl
    exact e1.trans e3r

/-- Composition of algebra morphisms induces composition of literal maps. -/
theorem adjLiteralHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    adjLiteralHom φ ≫ adjLiteralHom ψ = adjLiteralHom (φ ≫ ψ) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · ext Δ
    have hL12 : ((adjLiteralHom φ ≫ adjLiteralHom ψ).left).app Δ =
        (((adjLiteralHom φ).left).app Δ ≫ ((adjLiteralHom ψ).left).app Δ) :=
      rfl
    rw [hL12, adjLiteralHom_left_app, adjLiteralHom_left_app,
      adjLiteralHom_left_app, Functor.map_comp, Functor.map_comp]
    rfl
  ·     -- The stated equation would elaborate `φ.f ≫ ψ.f` against a
    -- semireducible `right`-projection type (implicit-transparency gap),
    -- so restate defeq and close by `Algebra.comp_f`.
    change φ.f ≫ ψ.f = (φ ≫ ψ).f
    exact (Algebra.comp_f φ ψ).symm

/-- Evaluation at an algebra for `Algebra`-indexed `C`-valued diagrams,
for the postcomposition commutation below. Assembly-only scaffolding. -/
private noncomputable def adjEvalC (alg : T.Algebra) : (T.Algebra ⥤ C) ⥤ C :=
  (evaluation _ _).obj alg

/-- Evaluation/postcomposition commutation as an explicit isomorphism, so the
literal comparison chain below is well-typed at every transparency.
Assembly-only scaffolding. -/
private noncomputable def adjEvalForgetIso (alg : T.Algebra) :
    (adjEvalAlgebra alg ⋙ T.forget) ≅
      (functorPostcompOuter T.forget ⋙ adjEvalC alg) :=
  Iso.refl _

/-- Postcomposed adjunction bar, still `Algebra`-indexed: the adjunction bar
with the right module postcomposed by `forget`. Assembly-only scaffolding. -/
private noncomputable def adjPostcompBar :
    SimplicialObject (T.Algebra ⥤ C) :=
  twoSidedBar T.adj.toMonad ((adjRightModule T.adj).postcomp T.forget)
    (adjLeftModule T.adj)

/-- Stepwise simplicial comparison to the postcomposed evaluated bar, via the
functor associators, the explicit evaluation/postcomposition commutation iso,
and the whiskered genuine `twoSidedBarPostcompWhiskerIso`.
Assembly-only scaffolding. -/
private noncomputable def adjLiteralBarIsoStep (alg : T.Algebra) :
    (adjLiteralAugmented alg).left ≅ (adjPostcompBar ⋙ adjEvalC alg) :=
  (Functor.isoWhiskerLeft (adjBar T.adj) (adjEvalForgetIso alg)) ≪≫
    (Functor.associator (adjBar T.adj) (functorPostcompOuter T.forget)
      (adjEvalC alg)).symm ≪≫
    (Functor.isoWhiskerRight
      (twoSidedBarPostcompWhiskerIso T.forget (adjRightModule T.adj)
        (adjLeftModule T.adj))
      (adjEvalC alg))

/-- Degreewise objects of the postcomposed evaluated bar agree with the
surrogate model, by unfolding to the same forgotten bar object at each
simplex length. Assembly-only scaffolding. -/
private theorem adjPostcompEval_obj_eq (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (adjPostcompBar ⋙ adjEvalC alg).obj Δ =
      (adjEvaluatedAugmented alg).left.obj Δ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ]
  rfl

/-- Evaluation acts by application, by definition. -/
private theorem adjEvalAlgebra_map_app {F G : T.Algebra ⥤ T.Algebra}
    (η : F ⟶ G) (alg : T.Algebra) :
    (adjEvalAlgebra alg).map η = η.app alg :=
  rfl

/-- Forgotten counit is the algebra structure map, standalone so prior
unfolding cannot pollute transparency. Term-mode only: `rfl` bridges the
free/forget carrier gap at default transparency; no `rw` motive is built over
the bridged composite. -/
private theorem adjCounitForget_app (alg : T.Algebra) :
    T.forget.map ((T.adj).counit.app alg) = alg.a := by
  have hForget : T.forget.map ((T.adj).counit.app alg) =
      ((T.adj).counit.app alg).f := rfl
  have hDef : ((T.adj).counit.app alg).f =
      T.map (𝟙 (T.forget.obj alg)) ≫ alg.a := rfl
  have hMap : T.map (𝟙 (T.forget.obj alg)) = 𝟙 _ :=
    Functor.map_id _ _
  have hComp : (T.map (𝟙 (T.forget.obj alg)) ≫ alg.a) = alg.a :=
    (congrArg (· ≫ alg.a) hMap).trans (Category.id_comp _)
  exact hForget.trans (hDef.trans hComp)

/-- Evaluation at the discrete point acts by application, by definition
(mirrors `emEvalPoint_map_app`). Placed early so the literal bridge below can
use it. -/
private theorem adjEvalPoint_map_app {F G : Discrete PUnit.{1} ⥤ C}
    (η : F ⟶ G) :
    resolutionEvalPoint.map η = η.app (Discrete.mk PUnit.unit) :=
  rfl

/-- Constant `T.Algebra`-valued index functor at `alg`: every discrete point
goes to `alg`. Precomposing with it then evaluating at the discrete point is
evaluation at `alg`. Assembly-only scaffolding. -/
private noncomputable def adjConstAlg (alg : T.Algebra) :
    Discrete PUnit.{1} ⥤ T.Algebra :=
  (Functor.const (Discrete PUnit.{1})).obj alg

/-- Evaluation at `alg` factors through precomposition with the constant index
functor followed by evaluation at the discrete point. Both sides act by
application, so the reflexive iso is well-typed and keeps the bridge below
well-typed at every transparency. Assembly-only scaffolding. -/
private noncomputable def adjEvalFactorIso (alg : T.Algebra) :
    adjEvalC alg ≅
      (functorPrecompOuter (adjConstAlg alg) ⋙ resolutionEvalPoint) :=
  Iso.refl _

/-- The precomposed adjunction left module agrees with the restricted
terminal-index module: both carry the constant functor at the carrier, and
both actions are the algebra structure map (forgotten counit versus
restriction). Assembled with a reflexive functor iso, mirroring `adjLeftIso`. -/
private noncomputable def adjPrecompLeftIso (alg : T.Algebra) :
    (adjLeftModule T.adj).precomp (adjConstAlg alg) ≅
      algebraLeftModule (adjAlg alg) := by
  refine Algebra.isoMk (Iso.refl _) ?_
  ext X
  have e1 : ((adjLeftModule T.adj).precomp (adjConstAlg alg)).action.app X =
      (adjLeftModule T.adj).action.app ((adjConstAlg alg).obj X) :=
    LeftModule.precomp_action_app _ _ _
  have e2 : (adjLeftModule T.adj).action.app ((adjConstAlg alg).obj X) =
      T.forget.map (T.adj.counit.app ((adjConstAlg alg).obj X)) :=
    adjLeftModule_action_app _ _
  have e3 : T.forget.map (T.adj.counit.app ((adjConstAlg alg).obj X)) =
      T.forget.map (T.adj.counit.app alg) := rfl
  have hL : ((adjLeftModule T.adj).precomp (adjConstAlg alg)).action.app X =
      T.forget.map (T.adj.counit.app alg) :=
    e1.trans (e2.trans e3)
  have hLa : T.forget.map (T.adj.counit.app alg) = alg.a :=
    adjCounitForget_app alg
  have qA : (adjAlg (T := T) alg).a = alg.a :=
    Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
  have hR : (algebraLeftModule (adjAlg (T := T) alg)).action.app X = alg.a :=
    (algebraLeftModule_action_app _ _).trans qA
  rw [NatTrans.comp_app, NatTrans.comp_app,
    LeftModule.precomp_action_app, algebraLeftModule_action_app,
    Iso.refl_hom]
  simp only [NatTrans.id_app]
  have hW : (Functor.whiskerRight (𝟙 (adjConstAlg alg ⋙ (adjLeftModule T.adj).functor))
      T.adj.toMonad.toFunctor).app X = 𝟙 _ := by
    rw [Functor.whiskerRight_id']
    rfl
  have hLHS : (Functor.whiskerRight (𝟙 (adjConstAlg alg ⋙ (adjLeftModule T.adj).functor))
      T.adj.toMonad.toFunctor).app X ≫ (adjAlg alg).a = alg.a :=
    ((congrArg (· ≫ (adjAlg alg).a) hW).trans (Category.id_comp _)).trans qA
  have hRHS : (adjLeftModule T.adj).action.app ((adjConstAlg alg).obj X) ≫
      𝟙 _ = alg.a :=
    (Category.comp_id _).trans (hL.trans hLa)
  exact hLHS.trans hRHS.symm

/-- The precomp comparison is the identity on underlying functors. -/
@[simp]
private theorem adjPrecompLeftIso_hom_f (alg : T.Algebra) :
    (adjPrecompLeftIso (T := T) alg).hom.f = 𝟙 _ := rfl

/-- Reflexive right-module comparison is the identity on components,
by definition. -/
private theorem adjRightRefl_f_app (X : C) :
    (((Iso.refl ((adjRightModule T.adj).postcomp T.forget)).hom).f.app X) =
      𝟙 _ :=
  rfl

/-- The third bridge link acts by `𝟙` at each simplex length: evaluation acts
by application, then the precomposition bridge and the module comparison are
both identities. The two links are closed separately (each by syntactic
rewrites only) and combined through the definitional unfolding of the
whiskered comparison, so no `simp` set ever needs to split the mixed
`(X ≫ barMap ..).app b` composite. -/
private theorem adjBridgeThird_hom_app (alg : T.Algebra) (n : ℕ) :
    (Functor.isoWhiskerRight
      ((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj)) ≪≫
        (twoSidedBarIso (Iso.refl _) (adjPrecompLeftIso alg)))
      resolutionEvalPoint).hom.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  have h1 : (((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget)
        (adjLeftModule T.adj)).hom.app
      (Opposite.op (SimplexCategory.mk n))).app
      (Discrete.mk PUnit.unit)) = 𝟙 _ :=
    twoSidedBarPrecompWhiskerIso_hom_app_app_id _ _ _ _ _
  have h2 : ((barMap (Iso.refl ((adjRightModule T.adj).postcomp T.forget)).hom
        (adjPrecompLeftIso alg).hom n).app
      (Discrete.mk PUnit.unit)) = 𝟙 _ := by
    rw [barMap_app, adjRightRefl_f_app, adjPrecompLeftIso_hom_f,
      NatTrans.id_app]
    -- Term-mode close: `rw`/`simp` never match the `map_id` redex under the
    -- reducible `monadPow` unfolding, so supply fully-applied instances and
    -- assemble by congruence (cf. `hL`/`hR` below for `adjDataAug`).
    have eMap := Functor.map_id (T.adj.toMonad.monadPow n)
      ((adjConstAlg alg ⋙ (adjLeftModule T.adj).functor).obj
        { as := PUnit.unit })
    have eOut := Functor.map_id
      ((adjRightModule T.adj).postcomp T.forget).functor
      ((T.adj.toMonad.monadPow n).obj
        ((adjConstAlg alg ⋙ (adjLeftModule T.adj).functor).obj
          { as := PUnit.unit }))
    exact (((congrArg (fun m =>
        ((adjRightModule T.adj).postcomp T.forget).functor.map m ≫ 𝟙 _)
        eMap).trans
      (congrArg (fun m => m ≫ 𝟙 _) eOut)).trans (Category.comp_id _))
  have hsplit : (Functor.isoWhiskerRight
      ((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj)) ≪≫
        (twoSidedBarIso (Iso.refl _) (adjPrecompLeftIso alg)))
      resolutionEvalPoint).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      (((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget)
        (adjLeftModule T.adj)).hom.app
      (Opposite.op (SimplexCategory.mk n))).app
      (Discrete.mk PUnit.unit)) ≫
      ((barMap (Iso.refl ((adjRightModule T.adj).postcomp T.forget)).hom
        (adjPrecompLeftIso alg).hom n).app
      (Discrete.mk PUnit.unit)) := rfl
  rw [hsplit, h1, h2]
  exact Category.id_comp _

/-- Simplicial bridge from the postcomposed evaluated bar to the surrogate
model: factor evaluation through the constant index functor, reassociate,
then cross the genuine precomposition whisker iso and the precomp
left-module iso. All naturality is inherited from the genuine combinators;
no manual `eqToHom` naturality is needed. Assembly-only scaffolding. -/
private noncomputable def adjPostcompEvalBridge (alg : T.Algebra) :
    (adjPostcompBar ⋙ adjEvalC alg) ≅ (adjEvaluatedAugmented alg).left :=
  (Functor.isoWhiskerLeft adjPostcompBar (adjEvalFactorIso alg)) ≪≫
    (Functor.associator adjPostcompBar (functorPrecompOuter (adjConstAlg alg))
      resolutionEvalPoint).symm ≪≫
    (Functor.isoWhiskerRight
      ((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj)) ≪≫
        (twoSidedBarIso (Iso.refl _) (adjPrecompLeftIso alg)))
      resolutionEvalPoint)

/-- Functor associator symmetric components on the stepwise chain are
identities, by definition. Stated with the explicit `twoSidedBar` functor so
consecutive comparison links agree syntactically. -/
private theorem adjStepAssocSymm_hom_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.associator (twoSidedBar T.adj.toMonad (adjRightModule T.adj)
      (adjLeftModule T.adj)) (functorPostcompOuter T.forget)
      (adjEvalC alg)).symm.hom.app Δ =
      𝟙 _ :=
  rfl

/-- The evaluation-commutation whisker on the stepwise chain acts by `𝟙`,
by definition. Stated with the explicit `twoSidedBar` functor so consecutive
comparison links agree syntactically. -/
private theorem adjStepWhiskerComm_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.isoWhiskerLeft (twoSidedBar T.adj.toMonad (adjRightModule T.adj)
      (adjLeftModule T.adj)) (adjEvalForgetIso alg)).hom.app Δ =
      𝟙 _ :=
  rfl

/-- Evaluation in `C` at `alg` acts by application, by definition. -/
private theorem adjEvalC_map_app {F G : T.Algebra ⥤ C} (η : F ⟶ G)
    (alg : T.Algebra) :
    (adjEvalC alg).map η = η.app alg :=
  rfl

/-- Degreewise objects of the literal whiskered bar agree with the
postcomposed evaluated bar, by unfolding to the same forgotten bar object.
Assembly-only scaffolding. -/
private theorem adjLiteralStep_obj_eq (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (adjLiteralAugmented alg).left.obj Δ =
      (adjPostcompBar ⋙ adjEvalC alg).obj Δ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ]
  rfl

/-- The stepwise comparison has identity components: the commutation whisker,
the associator, and the postcomposition bridge all act by `𝟙`. Stated with
`eqToHom` over the object identification, since the target composite
is only propositionally (not syntactically) the literal-bar object at
`rw`-motive transparency. Assembly-only scaffolding. -/
private theorem adjLiteralBarIsoStep_hom_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (adjLiteralBarIsoStep alg).hom.app Δ =
      eqToHom (adjLiteralStep_obj_eq alg _) := by
  have hdecomp : (adjLiteralBarIsoStep alg).hom =
      (Functor.isoWhiskerLeft (twoSidedBar T.adj.toMonad (adjRightModule T.adj)
        (adjLeftModule T.adj)) (adjEvalForgetIso alg)).hom ≫
      (Functor.associator (twoSidedBar T.adj.toMonad (adjRightModule T.adj)
        (adjLeftModule T.adj)) (functorPostcompOuter T.forget)
        (adjEvalC alg)).symm.hom ≫
      (Functor.isoWhiskerRight
        (twoSidedBarPostcompWhiskerIso T.forget (adjRightModule T.adj)
          (adjLeftModule T.adj))
        (adjEvalC alg)).hom := rfl
  rw [hdecomp, NatTrans.comp_app, NatTrans.comp_app,
    adjStepWhiskerComm_app, adjStepAssocSymm_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    adjEvalC_map_app,
    twoSidedBarPostcompWhiskerIso_hom_app_app_id]
  have hE : eqToHom (adjLiteralStep_obj_eq alg Δ) = 𝟙 _ := rfl
  exact ((Category.id_comp _).trans (Category.id_comp _)).trans hE.symm

/-- Functor associator symmetric components on the bridge chain are
identities, by definition. Stated with the explicit `twoSidedBar` functor so
consecutive comparison links agree syntactically. -/
private theorem adjBridgeAssocSymm_hom_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.associator (twoSidedBar T.adj.toMonad
      ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj))
      (functorPrecompOuter (adjConstAlg alg))
      resolutionEvalPoint).symm.hom.app Δ =
      𝟙 _ :=
  rfl

/-- The evaluation-factorization whisker on the bridge chain acts by `𝟙`,
by definition. Stated with the explicit `twoSidedBar` functor so consecutive
comparison links agree syntactically. -/
private theorem adjBridgeWhiskerComm_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.isoWhiskerLeft (twoSidedBar T.adj.toMonad
      ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj))
      (adjEvalFactorIso alg)).hom.app Δ =
      𝟙 _ :=
  rfl

/-- The bridge comparison has identity components at each simplex length:
the factorization whisker, the associator, the precomposition bridge, and
the module comparison all act by `𝟙` once evaluated at the discrete point.
Stated with `eqToHom` over the object identification, since a `𝟙`
ascription would force the kernel to unfold the opaque surrogate model at
statement elaboration. Assembly-only scaffolding. -/
private theorem adjPostcompEvalBridge_hom_app (alg : T.Algebra) (n : ℕ) :
    (adjPostcompEvalBridge alg).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      eqToHom (adjPostcompEval_obj_eq alg _) := by
  have hdecomp : (adjPostcompEvalBridge alg).hom =
      (Functor.isoWhiskerLeft (twoSidedBar T.adj.toMonad
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj))
        (adjEvalFactorIso alg)).hom ≫
      (Functor.associator (twoSidedBar T.adj.toMonad
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj))
        (functorPrecompOuter (adjConstAlg alg))
        resolutionEvalPoint).symm.hom ≫
      (Functor.isoWhiskerRight
        ((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
          ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj)) ≪≫
          (twoSidedBarIso (Iso.refl _) (adjPrecompLeftIso alg)))
        resolutionEvalPoint).hom := rfl
  rw [hdecomp, NatTrans.comp_app, NatTrans.comp_app,
    adjBridgeWhiskerComm_app, adjBridgeAssocSymm_hom_app]
  -- Stop rewriting here: the goal now carries `𝟙`-pinned links, and any
  -- further `rw` motive over the mixed composite would need `no_expose`
  -- unfolding. Assemble the rest in term mode at default transparency.
  have l3 : (Functor.isoWhiskerRight
      ((twoSidedBarPrecompWhiskerIso (adjConstAlg alg)
        ((adjRightModule T.adj).postcomp T.forget) (adjLeftModule T.adj)) ≪≫
        (twoSidedBarIso (Iso.refl _) (adjPrecompLeftIso alg)))
      resolutionEvalPoint).hom.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ :=
    adjBridgeThird_hom_app alg n
  have hE : eqToHom (adjPostcompEval_obj_eq alg
      (Opposite.op (SimplexCategory.mk n))) = 𝟙 _ := rfl
  exact ((congrArg (fun c => 𝟙 _ ≫ 𝟙 _ ≫ c) l3).trans
    (((Category.id_comp _).trans (Category.id_comp _)).trans hE.symm))

/-- Degreewise objects of the literal whiskered bar agree with the
surrogate model, by unfolding to the same forgotten bar object at each
simplex length. -/
theorem adjLiteralBar_obj_eq (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (adjLiteralAugmented alg).left.obj Δ =
      (adjEvaluatedAugmented alg).left.obj Δ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ]
  rfl

/-- The honest simplicial comparison: the literal whiskered bar is isomorphic
to the surrogate model, by composing the stepwise postcomposition comparison
with the precomposition-factorization bridge. -/
@[no_expose]
noncomputable def adjLiteralBarIso (alg : T.Algebra) :
    (adjLiteralAugmented alg).left ≅ (adjEvaluatedAugmented alg).left :=
  adjLiteralBarIsoStep alg ≪≫ adjPostcompEvalBridge alg

/-- The full simplicial comparison has identity components at each simplex
length, stated with `eqToHom` over the public object identification for the
same opacity reason as the bridge law. -/
theorem adjLiteralBarIso_hom_app (alg : T.Algebra) (n : ℕ) :
    (adjLiteralBarIso alg).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      eqToHom (adjLiteralBar_obj_eq alg _) := by
  have hcomp : (adjLiteralBarIso alg).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      (adjLiteralBarIsoStep alg).hom.app
        (Opposite.op (SimplexCategory.mk n)) ≫
        (adjPostcompEvalBridge alg).hom.app
          (Opposite.op (SimplexCategory.mk n)) := rfl
  simp only [hcomp, adjLiteralBarIsoStep_hom_app, adjPostcompEvalBridge_hom_app,
    eqToHom_trans]

/-- Auxiliary degree-zero augmentation identity for the surrogate model,
proved by unfolding the opaque surrogate (private so the unfolding is
permitted): the degree-zero component is the bundled algebra map. -/
private theorem adjEvaluatedAugmented_hom_zero_aux (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = (adjAlg alg).a := by
  unfold adjEvaluatedAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    BalancedPairing.toSimplicialAugmented_hom_app_mk,
    BalancedPairing.toDataHom_app_zero]
  rfl

/-- Degree-zero augmentation component of the evaluated augmentation is the
algebra structure map, up to the public object/point identifications.
Transport-normalized: a plain `= alg.a` is ill-typed without unfolding the
opaque surrogate model at statement elaboration. -/
theorem adjEvaluatedAugmented_hom_zero (alg : T.Algebra) :
    eqToHom (adjEvaluatedAugmented_obj_zero alg).symm ≫
      (adjEvaluatedAugmented alg).hom.app
        (Opposite.op (SimplexCategory.mk 0)) ≫
      eqToHom (adjEvaluatedAugmented_point alg) = alg.a := by
  have hAux : (adjEvaluatedAugmented (T := T) alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = (adjAlg (T := T) alg).a :=
    adjEvaluatedAugmented_hom_zero_aux alg
  have qA : (adjAlg (T := T) alg).a = alg.a :=
    Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
  have hE1 : eqToHom (adjEvaluatedAugmented_obj_zero (T := T) alg).symm =
      𝟙 (T.obj alg.A) := rfl
  have hE2 : eqToHom (adjEvaluatedAugmented_point (T := T) alg) =
      𝟙 alg.A := rfl
  -- Single term-mode close: every `rw` motive over the mixed
  -- transport/augmentation composite would need `no_expose` unfolding.
  -- (`≫` is right-associative, so no `assoc` step is needed.)
  have hclose : (𝟙 _ ≫ alg.a ≫ 𝟙 _) = alg.a :=
    ((congrArg (fun f => 𝟙 _ ≫ f) (Category.comp_id alg.a)).trans
      (Category.id_comp alg.a))
  exact (congrArg (fun m => eqToHom
      (adjEvaluatedAugmented_obj_zero (T := T) alg).symm ≫ m ≫
      eqToHom (adjEvaluatedAugmented_point (T := T) alg))
      (hAux.trans qA)).trans
    (((congrArg (fun e => e ≫ alg.a ≫
      eqToHom (adjEvaluatedAugmented_point (T := T) alg)) hE1).trans
      (congrArg (fun e => 𝟙 _ ≫ alg.a ≫ e) hE2)).trans hclose)

/-- Forgotten iterated right actions agree with postcomposed ones, by
induction on the power: the base case is the postcomposition action law and
the step is definitional unfolding. -/
private theorem adjRightPowForget_agree (n : ℕ) (X : C) :
    T.forget.map (rightActionPow T.adj.toMonad (adjRightModule T.adj) n X) =
      rightActionPow T.adj.toMonad
        ((adjRightModule T.adj).postcomp T.forget) n X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact ih _

/-- Degree-zero faces agree after forgetting: both sides are the iterated
right action at the carrier, once the `d₀` branch is exposed. -/
private theorem adjDataFace_agree (alg : T.Algebra) (n : ℕ) :
    T.forget.map (((((barData T.adj.toMonad (adjRightModule T.adj)
        (adjLeftModule T.adj)).δ (0 : Fin (n + 2))).app alg))) =
      ((((barData T.adj.toMonad ((adjRightModule T.adj).postcomp T.forget)
        (algebraLeftModule (adjAlg alg))).δ (0 : Fin (n + 2))).app
          ⟨PUnit.unit⟩)) := by
  rw [barData_δ_app, barData_δ_app]
  have h0 : ((0 : Fin (n + 2)).val = 0) := rfl
  unfold barFaceApp
  rw [dite_eq_left h0]
  exact adjRightPowForget_agree n _

/-- Forgetting the adjunction augmentation data agrees with the surrogate
model data, by induction on degree: base case is `alg.a` on both sides; the
step uses face agreement under the data face laws. -/
private theorem adjDataForget_agree (alg : T.Algebra) (n : ℕ) :
    T.forget.map ((((adjBalancedPairing T.adj).toDataHom.app n).app alg)) =
      ((((adjUnderlyingPairing alg).toDataHom.app n).app
        ⟨PUnit.unit⟩)) := by
  induction n with
  | zero =>
    have hLp : ((adjUnderlyingPairing (T := T) alg).pairing).app
        ⟨PUnit.unit⟩ = (adjAlg alg).a := rfl
    have qA : (adjAlg (T := T) alg).a = alg.a :=
      Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
    simp only [BalancedPairing.toDataHom_app_zero, adjBalancedPairing_pairing,
      adjPairing_app]
    exact (adjCounitForget_app alg).trans (hLp.trans qA).symm
  | succ n ih =>
    have eL : T.forget.map ((((adjBalancedPairing T.adj).toDataHom.app
        (n + 1))).app alg) =
        T.forget.map (((((barData T.adj.toMonad (adjRightModule T.adj)
          (adjLeftModule T.adj)).δ (0 : Fin (n + 2))).app alg))) ≫
          T.forget.map ((((adjBalancedPairing T.adj).toDataHom.app n).app
            alg)) := by
      rw [BalancedPairing.toDataHom_app_succ, NatTrans.comp_app]
      exact Functor.map_comp _ _ _
    have eR : ((((adjUnderlyingPairing alg).toDataHom.app (n + 1))).app
        ⟨PUnit.unit⟩) =
        (((((barData T.adj.toMonad ((adjRightModule T.adj).postcomp T.forget)
          (algebraLeftModule (adjAlg alg))).δ (0 : Fin (n + 2))).app
            ⟨PUnit.unit⟩))) ≫
        ((((adjUnderlyingPairing alg).toDataHom.app n).app
          ⟨PUnit.unit⟩)) := by
      rw [BalancedPairing.toDataHom_app_succ, NatTrans.comp_app]
    -- Single term-mode close: after the face/consensus rewrites the goal
    -- is `X ≫ Y = X ≫ Y`, which neither `rw` nor `simp` discharge here,
    -- so assemble from the two one-sided equations by congruence.
    exact eL.trans ((congrArg (· ≫ _) (adjDataFace_agree alg n)).trans
      ((congrArg (_ ≫ ·) ih).trans eR.symm))

/-- The literal and surrogate augmentations agree componentwise: forgetting
the evaluated adjunction augmentation is the surrogate augmentation. Unfolds
the double whiskering; kept separate so the `Comma` square below never
rewrites with the `𝟙`-valued comparison component. -/
private theorem adjLiteralHomAgree_app (alg : T.Algebra) (n : ℕ) :
    (adjLiteralAugmented alg).hom.app (Opposite.op (SimplexCategory.mk n)) =
      (adjEvaluatedAugmented alg).hom.app
        (Opposite.op (SimplexCategory.mk n)) := by
  unfold adjLiteralAugmented adjEvaluatedAugmented adjAugmented
  simp only [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    BalancedPairing.toSimplicialAugmented_hom_app_mk]
  change T.forget.map ((adjEvalAlgebra alg).map
      ((adjBalancedPairing T.adj).toDataHom.app n)) =
    resolutionEvalPoint.map ((adjUnderlyingPairing alg).toDataHom.app n)
  rw [adjEvalAlgebra_map_app, adjEvalPoint_map_app]
  exact adjDataForget_agree alg n

/-- The honest augmented comparison: the literal forgetful image is naturally
isomorphic to the reusable surrogate model. -/
@[no_expose]
noncomputable def adjLiteralIso (alg : T.Algebra) :
    adjLiteralAugmented alg ≅ adjEvaluatedAugmented alg :=
  Comma.isoMk (adjLiteralBarIso alg) (Iso.refl _) (by
    ext Δ
    simp only [NatTrans.comp_app, Functor.id_map]
    have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
      obtain ⟨d⟩ := Δ
      exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
    rw [hΔ, adjLiteralHomAgree_app]
    have h1 := adjLiteralBarIso_hom_app alg (Opposite.unop Δ).len
    rw [h1]
    -- Term-mode close: `rw` cannot form motives over the opaque
    -- mixed `𝟙`-then-augmentation composites, so bridge with `congrArg`
    -- and the identity laws at default transparency.
    have hE : eqToHom (adjLiteralBar_obj_eq alg
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) = 𝟙 _ := rfl
    have hR : ((SimplicialObject.const C).map
        (Iso.refl (adjLiteralAugmented alg).right).hom).app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) = 𝟙 _ := by
      simp only [Iso.refl_hom, Functor.map_id, NatTrans.id_app]
    exact ((congrArg (fun e => e ≫ (adjEvaluatedAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) hE).trans
      (Category.id_comp _)).trans
      (((congrArg (fun e => (adjEvaluatedAugmented alg).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) ≫ e) hR).trans
        (Category.comp_id _)).symm))

/-- Degree-zero augmentation component of the literal image is the algebra
structure map: evaluation/forgotten counit is the structure map. -/
@[simp]
theorem adjLiteralAugmented_hom_zero (alg : T.Algebra) :
    (adjLiteralAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = alg.a := by
  have hWhisk : (adjLiteralAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) =
      (adjEvalAlgebra alg ⋙ T.forget).map ((adjAugmented T.adj).hom.app
        (Opposite.op (SimplexCategory.mk 0))) := by
    unfold adjLiteralAugmented
    rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk]
  have hAug : (adjAugmented T.adj).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = adjPairing T.adj :=
    adjAugmented_hom_zero _
  have hComp : (adjEvalAlgebra alg ⋙ T.forget).map (adjPairing T.adj) =
      T.forget.map ((adjEvalAlgebra alg).map (adjPairing T.adj)) :=
    Functor.comp_map _ _ _
  have hEval : (adjEvalAlgebra alg).map (adjPairing T.adj) =
      (adjPairing T.adj).app alg :=
    adjEvalAlgebra_map_app _ _
  have hPair : (adjPairing T.adj).app alg = (T.adj).counit.app alg :=
    adjPairing_app _ _
  have hEvalPair : (adjEvalAlgebra alg).map (adjPairing T.adj) =
      (T.adj).counit.app alg :=
    hEval.trans hPair
  have hForgetEval : T.forget.map ((adjEvalAlgebra alg).map (adjPairing T.adj)) =
      alg.a :=
    (congrArg T.forget.map hEvalPair).trans (adjCounitForget_app alg)
  have hKPair : (adjEvalAlgebra alg ⋙ T.forget).map (adjPairing T.adj) = alg.a :=
    hComp.trans hForgetEval
  exact hWhisk.trans ((congrArg _ hAug).trans hKPair)

/-- The left-module comparison is the identity on underlying functors. -/
@[simp]
private theorem adjLeftIso_hom_f (alg : T.Algebra) :
    (adjLeftIso (T := T) alg).hom.f = 𝟙 _ := rfl

/-- Data-level comparison square for the adjunction side: the module-isomorphism
bar map followed by the monad-change map, then the EM pairing, equals the
adjunction pairing followed by the identity. By `hom_eq_of_app_zero_eq` this
reduces to degree zero, where both sides are `alg.a` after normalizing the
identity components. The right-hand side uses `constDataHom` (definitionally
the constant functor's action) so that middle objects match syntactically. -/
private theorem adjDataAug_w (alg : T.Algebra) :
    (barDataHom (adjRightIso (T := T)).hom (adjLeftIso alg).hom ≫
          barChangeDataHom (adjMonadHom (T := T))
            (emRightModule.postcomp T.forget)
            (algebraLeftModule alg)) ≫ (emUnderlyingPairing alg).toDataHom =
        (adjUnderlyingPairing alg).toDataHom ≫
          SimplicialObject.Data.constDataHom (𝟙 _) := by
  apply SimplicialObject.Data.hom_eq_of_app_zero_eq
  simp only [SimplicialObject.comp_app,
    BalancedPairing.toDataHom_app_zero,
    SimplicialObject.Data.constDataHom_app]
  ext X
  -- Term-mode: `rfl`/`exact` bridge the `barObj`/`barData.obj` gap (default
  -- transparency); every propositional step below elaborates a closed term,
  -- so no `rw` motive is ever built over the bridged composite.
  have m1 (Z : C) : (monadPow T.adj.toMonad 0).map (𝟙 Z) = 𝟙 Z := by simp
  have m2 (Z : C) : (monadPowHom (adjMonadHom (T := T)) 0).app Z = 𝟙 Z :=
    monadPowHom_zero_app _ Z
  have eL : ((((barDataHom adjRightIso.hom (adjLeftIso alg).hom).app 0 ≫
        (barChangeDataHom adjMonadHom (emRightModule.postcomp T.forget)
          (algebraLeftModule alg)).app 0) ≫
      (emUnderlyingPairing alg).pairing)).app X
      = (((((adjRightModule T.adj).postcomp T.forget).functor.map
        ((monadPow T.adj.toMonad 0).map
          (𝟙 ((algebraLeftModule (adjAlg alg)).functor.obj X))) ≫ 𝟙 _) ≫
        ((emRightModule.postcomp T.forget).functor.map
          ((monadPowHom (adjMonadHom (T := T)) 0).app _))) ≫ alg.a) := rfl
  have eR : (((adjUnderlyingPairing alg).pairing ≫ 𝟙 _)).app X
      = ((adjAlg alg).a ≫ 𝟙 _) := rfl
  have r1 : (((adjRightModule T.adj).postcomp T.forget).functor.map
      ((monadPow T.adj.toMonad 0).map
        (𝟙 ((algebraLeftModule (adjAlg alg)).functor.obj X)))) = 𝟙 _ :=
    (congrArg _ (m1 _)).trans (Functor.map_id _ _)
  have r2 : ((emRightModule.postcomp T.forget).functor.map
      ((monadPowHom (adjMonadHom (T := T)) 0).app
        ((algebraLeftModule (adjAlg alg)).functor.obj X))) = 𝟙 _ :=
    (congrArg _ (m2 _)).trans (Functor.map_id _ _)
  have qA : (adjAlg alg).a = alg.a :=
    Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
  have s1 : ((((adjRightModule T.adj).postcomp T.forget).functor.map
      ((monadPow T.adj.toMonad 0).map
        (𝟙 ((algebraLeftModule (adjAlg alg)).functor.obj X))) ≫ 𝟙 _)) = 𝟙 _ :=
    (congrArg (· ≫ 𝟙 _) r1).trans (Category.id_comp _)
  have nL : (((((adjRightModule T.adj).postcomp T.forget).functor.map
        ((monadPow T.adj.toMonad 0).map
          (𝟙 ((algebraLeftModule (adjAlg alg)).functor.obj X))) ≫ 𝟙 _) ≫
        ((emRightModule.postcomp T.forget).functor.map
          ((monadPowHom (adjMonadHom (T := T)) 0).app _))) ≫ alg.a) = alg.a :=
    (congrArg (· ≫ alg.a)
      ((congrArg (· ≫ ((emRightModule.postcomp T.forget).functor.map
        ((monadPowHom (adjMonadHom (T := T)) 0).app _))) s1).trans
        (Category.id_comp _))).trans
      ((congrArg (· ≫ alg.a) r2).trans (Category.id_comp _))
  have nR : ((adjAlg alg).a ≫ 𝟙 _) = alg.a :=
    (congrArg (· ≫ 𝟙 _) qA).trans (Category.comp_id _)
  exact eL.trans (nL.trans (nR.symm.trans eR.symm))

/-- Data-level comparison morphism for the adjunction side, via the module
isomorphisms and the monad-change map. -/
private noncomputable def adjDataAugHom (alg : T.Algebra) :
    (adjUnderlyingPairing alg).toAugmented ⟶
      (emUnderlyingPairing alg).toAugmented where
  left :=
    barDataHom (adjRightIso (T := T)).hom (adjLeftIso alg).hom ≫
      barChangeDataHom (adjMonadHom (T := T))
        (emRightModule.postcomp T.forget) (algebraLeftModule alg)
  right := 𝟙 _
  w := adjDataAug_w alg

/-- Canonical one-way augmented morphism to the Eilenberg--Moore underlying
augmentation, via `barChangeHom` along `(Adjunction.adjToMonadIso T).hom`
and the module isomorphisms above. Not asserted to be an isomorphism. -/
@[no_expose]
noncomputable def adjToEMComparison (alg : T.Algebra) :
    adjEvaluatedAugmented alg ⟶ emUnderlyingAugmented alg :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).map
    (SimplicialObject.Data.Augmented.toSimplicialFunctor.map (adjDataAugHom alg))

/-- Left computation: the simplicial component is the whiskered change-map. -/
@[simp]
private theorem adjToEMComparison_left (alg : T.Algebra) :
    (adjToEMComparison alg).left =
      Functor.whiskerRight
        ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg)).hom ≫
          barChangeHom (adjMonadHom (T := T)) _ _) resolutionEvalPoint := by
  simp only [adjToEMComparison, adjDataAugHom, twoSidedBarIso_hom]
  rfl

/-- Right computation (private): the target component is the whiskered
Data-identity. The statement mentions the private `adjDataAugHom`, which is
fine for a private lemma. A public `(adjToEMComparison alg).right = 𝟙 _` is
not statable: checking `𝟙 _` forces the kernel to identify the two hidden
`Augmented`-object `.right` projections through the `Comma.map` object
machinery (depth limit). Right-component naturality therefore closes at the
concrete level (`dL`/`dR`/`uEq` below). -/
@[simp]
private theorem adjToEMComparison_right (alg : T.Algebra) :
    (adjToEMComparison alg).right =
      resolutionEvalPoint.map (adjDataAugHom alg).right :=
  Eq.trans
    (SimplicialObject.Augmented.whiskeringObj_map_right _ _)
    (congrArg resolutionEvalPoint.map
      (SimplicialObject.Data.Augmented.toSimplicialFunctor_map_right _))

/-- Transport-normalized right-component law for the comparison: the comparison
acts as the identity up to the public point identifications. -/
theorem adjToEMComparison_right_eqToHom (alg : T.Algebra) :
    (adjToEMComparison alg).right ≫
      eqToHom (emUnderlyingAugmented_point alg) =
      eqToHom (adjEvaluatedAugmented_point alg) := by
  have hR : (adjToEMComparison (T := T) alg).right =
      resolutionEvalPoint.map (adjDataAugHom (T := T) alg).right :=
    adjToEMComparison_right alg
  have hId : (adjDataAugHom (T := T) alg).right = 𝟙 _ := rfl
  have hMap : resolutionEvalPoint.map (adjDataAugHom (T := T) alg).right =
      𝟙 (adjEvaluatedAugmented (T := T) alg).right :=
    (congrArg resolutionEvalPoint.map hId).trans (Functor.map_id _ _)
  have hRightEq : (adjToEMComparison (T := T) alg).right =
      𝟙 (adjEvaluatedAugmented (T := T) alg).right :=
    hR.trans hMap
  have hStep1 : ((adjToEMComparison (T := T) alg).right ≫
      eqToHom (emUnderlyingAugmented_point alg)) =
      (𝟙 (adjEvaluatedAugmented (T := T) alg).right ≫
        eqToHom (emUnderlyingAugmented_point alg)) :=
    congrArg (· ≫ eqToHom (emUnderlyingAugmented_point alg)) hRightEq
  have hStep2 : (𝟙 (adjEvaluatedAugmented (T := T) alg).right ≫
      eqToHom (emUnderlyingAugmented_point alg)) =
      eqToHom (adjEvaluatedAugmented_point alg) :=
    Category.id_comp _ |>.trans (by rfl)
  exact hStep1.trans hStep2

/-- Auxiliary degree-zero object identity, proved by unfolding the opaque
surrogate (private so the unfolding is permitted). -/
private theorem adjToEMComparison_obj_zero_aux (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).left.obj
      (Opposite.op (SimplexCategory.mk 0)) =
      (emUnderlyingAugmented alg).left.obj
        (Opposite.op (SimplexCategory.mk 0)) :=
  rfl

/-- Degree-zero objects of the evaluated and underlying augmentations agree. -/
theorem adjToEMComparison_obj_zero (alg : T.Algebra) :
    (adjEvaluatedAugmented alg).left.obj
      (Opposite.op (SimplexCategory.mk 0)) =
      (emUnderlyingAugmented alg).left.obj
        (Opposite.op (SimplexCategory.mk 0)) :=
  adjToEMComparison_obj_zero_aux alg

/-- Auxiliary degree-zero left app identity, proved by unfolding the opaque
comparison (private so the unfolding is permitted). -/
private theorem adjToEMComparison_left_zero_aux (alg : T.Algebra) :
    ((adjToEMComparison alg).left).app
      (Opposite.op (SimplexCategory.mk 0)) =
      eqToHom (adjToEMComparison_obj_zero alg) := by
  have hEq : eqToHom (adjToEMComparison_obj_zero (T := T) alg) = 𝟙 _ := rfl
  have hFL0 : (((adjLeftIso (T := T) alg).hom.f).app
      (Discrete.mk PUnit.unit)) = 𝟙 _ := rfl
  have hFR0 : ∀ (X : C), (((adjRightIso (T := T)).hom.f).app X) = 𝟙 _ :=
    fun X => rfl
  have hPowHom0 : ∀ (X : C),
      (monadPowHom (adjMonadHom (T := T)) 0).app X = 𝟙 X :=
    fun X => rfl
  have hPowMap : ∀ (X : C),
      (monadPow T.adj.toMonad 0).map (𝟙 X) = 𝟙 X :=
    fun X => rfl
  have hPoint : (barMap (adjRightIso (T := T)).hom
      (adjLeftIso (T := T) alg).hom 0 ≫
      barChangeMap (adjMonadHom (T := T)) (emRightModule.postcomp T.forget)
        (algebraLeftModule alg) 0).app (Discrete.mk PUnit.unit) = 𝟙 _ := by
    -- Term-mode: `rfl` bridges the `barMap`/`barChangeMap` unfolding gap
    -- (default transparency; `rw`/`simp` motives re-check at implicit
    -- transparency and misfire here). Every propositional step below is a
    -- closed `congrArg`/`trans` over morphisms in `C`.
    have eL : (barMap (adjRightIso (T := T)).hom
        (adjLeftIso (T := T) alg).hom 0 ≫
        barChangeMap (adjMonadHom (T := T)) (emRightModule.postcomp T.forget)
          (algebraLeftModule alg) 0).app (Discrete.mk PUnit.unit)
        = (((((adjRightModule T.adj).postcomp T.forget).functor.map
            ((monadPow T.adj.toMonad 0).map
              (((adjLeftIso (T := T) alg).hom.f).app
                (Discrete.mk PUnit.unit))) ≫
            (((adjRightIso (T := T)).hom.f).app _)) ≫
          (emRightModule.postcomp T.forget).functor.map
            ((monadPowHom (adjMonadHom (T := T)) 0).app
              ((algebraLeftModule alg).functor.obj
                (Discrete.mk PUnit.unit))))) := rfl
    have q1 : (monadPow T.adj.toMonad 0).map
        (((adjLeftIso (T := T) alg).hom.f).app
          (Discrete.mk PUnit.unit)) = 𝟙 _ :=
      (congrArg ((monadPow T.adj.toMonad 0).map) hFL0).trans (hPowMap _)
    have qR : (((adjRightModule T.adj).postcomp T.forget).functor.map
        ((monadPow T.adj.toMonad 0).map
          (((adjLeftIso (T := T) alg).hom.f).app
            (Discrete.mk PUnit.unit)))) = 𝟙 _ :=
      (congrArg (((adjRightModule T.adj).postcomp T.forget).functor.map)
        q1).trans (Functor.map_id _ _)
    have sMid : ((adjRightModule T.adj).postcomp T.forget).functor.map
          ((monadPow T.adj.toMonad 0).map
            (((adjLeftIso (T := T) alg).hom.f).app (Discrete.mk PUnit.unit)))
          ≫ (((adjRightIso (T := T)).hom.f).app ((monadPow T.adj.toMonad 0).obj
            (((leftModuleRestrictAlongHom (adjMonadHom (T := T))).obj
              (algebraLeftModule alg)).A.obj
              (Discrete.mk PUnit.unit)))) = 𝟙 _ :=
      ((congrArg (· ≫ _) qR).trans (congrArg (𝟙 _ ≫ ·) (hFR0 _))).trans
        (Category.comp_id _)
    rw [sMid] at eL
    have hPH : (monadPowHom (adjMonadHom (T := T)) 0).app
        ((algebraLeftModule alg).functor.obj
          (Discrete.mk PUnit.unit)) = 𝟙 _ :=
      hPowHom0 _
    rw [hPH] at eL
    have hRem : ((emRightModule.postcomp T.forget).functor.map
        (𝟙 ((monadPow T.adj.toMonad 0).obj
          ((algebraLeftModule alg).functor.obj (Discrete.mk PUnit.unit))))) =
        𝟙 _ :=
      Functor.map_id _ _
    have hStep : (𝟙 (((adjRightModule T.adj).postcomp T.forget).functor.obj
          ((monadPow T.adj.toMonad 0).obj
            ((algebraLeftModule (adjAlg alg)).A.obj (Discrete.mk PUnit.unit))))
          ≫ (emRightModule.postcomp T.forget).functor.map
            (𝟙 ((monadPow T.adj.toMonad 0).obj
              ((algebraLeftModule alg).functor.obj
                (Discrete.mk PUnit.unit))))) =
        𝟙 (((adjRightModule T.adj).postcomp T.forget).functor.obj
          ((monadPow T.adj.toMonad 0).obj
            ((algebraLeftModule (adjAlg alg)).A.obj (Discrete.mk PUnit.unit)))) :=
      ((congrArg (𝟙 _ ≫ ·) hRem).trans (Category.comp_id _))
    exact eL.trans hStep
  have hApp : ((adjToEMComparison (T := T) alg).left).app
      (Opposite.op (SimplexCategory.mk 0)) = 𝟙 _ := by
    have e1 : ((adjToEMComparison (T := T) alg).left).app
        (Opposite.op (SimplexCategory.mk 0)) =
        resolutionEvalPoint.map (barMap (adjRightIso (T := T)).hom
          ((adjLeftIso (T := T) alg).hom) 0 ≫
          barChangeMap (adjMonadHom (T := T))
          (emRightModule.postcomp T.forget) (algebraLeftModule alg) 0) := by
      rw [adjToEMComparison_left]
      have hInner : (((twoSidedBarIso (adjRightIso (T := T))
          (adjLeftIso alg)).hom ≫
          barChangeHom (adjMonadHom (T := T)) _ _).app
          (Opposite.op (SimplexCategory.mk 0)))
          = (barMap (adjRightIso (T := T)).hom
            ((adjLeftIso (T := T) alg).hom) 0 ≫
            barChangeMap (adjMonadHom (T := T))
            (emRightModule.postcomp T.forget) (algebraLeftModule alg) 0) :=
        rfl
      exact congrArg resolutionEvalPoint.map hInner
    have eEval : resolutionEvalPoint.map (barMap (adjRightIso (T := T)).hom
        ((adjLeftIso (T := T) alg).hom) 0 ≫
        barChangeMap (adjMonadHom (T := T))
        (emRightModule.postcomp T.forget) (algebraLeftModule alg) 0) =
        (barMap (adjRightIso (T := T)).hom (adjLeftIso (T := T) alg).hom 0 ≫
          barChangeMap (adjMonadHom (T := T)) (emRightModule.postcomp T.forget)
            (algebraLeftModule alg) 0).app (Discrete.mk PUnit.unit) := rfl
    exact e1.trans (eEval.trans hPoint)
  exact hApp.trans hEq.symm

/-- Transport-normalized degree-zero left formula for the comparison: the
degree-zero simplicial component is the identity up to the public object
identification. -/
theorem adjToEMComparison_left_zero (alg : T.Algebra) :
    ((adjToEMComparison alg).left).app
      (Opposite.op (SimplexCategory.mk 0)) =
      eqToHom (adjToEMComparison_obj_zero alg) :=
  adjToEMComparison_left_zero_aux alg

/-- Pointwise target map for the adjunction side, mirroring
`emUnderlyingTargetHom`: the component at every discrete point is `φ.f`. -/
private noncomputable def adjUnderlyingTargetHom {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    (adjUnderlyingPairing alg).target ⟶ (adjUnderlyingPairing alg').target where
  app _ := φ.f
  naturality _ _ _ := by
    change (𝟙 alg.A) ≫ φ.f = φ.f ≫ (𝟙 alg'.A)
    simp

/-- The adjunction-side target map is pointwise the algebra morphism. -/
@[simp]
private theorem adjUnderlyingTargetHom_app {alg alg' : T.Algebra} (φ : alg ⟶ alg')
    (X : Discrete PUnit.{1}) :
    ((adjUnderlyingTargetHom (T := T) φ).app X) = φ.f :=
  rfl

/-- Degree-zero naturality square for the adjunction side, mirroring
`emUnderlying_hq`: after normalization both sides are `φ.h`. -/
private theorem adjUnderlying_hq {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    barMap (𝟙 ((adjRightModule T.adj).postcomp T.forget))
        (algebraLeftModuleHom ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) 0 ≫
        (adjUnderlyingPairing alg').pairing =
      (adjUnderlyingPairing alg).pairing ≫ adjUnderlyingTargetHom φ := by
  ext X
  -- Term-mode bridge: every link below is `rfl` at default transparency
  -- (`barMap_app`, the module-hom `f` projections, the pairing lemmas), so
  -- `rfl`/`exact` cross the `barObj`/`barData.obj` gap that blocks `rw`/`simp`
  -- motives (which re-check at implicit transparency).
  have p1 : (monadPow T.adj.toMonad 0).map φ.f = φ.f := by
    change (𝟭 C).map φ.f = φ.f
    exact Functor.id_map _
  have qA' : (adjAlg alg').a = alg'.a :=
    Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
  have qA : (adjAlg alg).a = alg.a :=
    Eq.trans (algebraFunctorOfMonadHom_obj_a _ _) (Category.id_comp _)
  have eL : (barMap (𝟙 ((adjRightModule T.adj).postcomp T.forget))
        (algebraLeftModuleHom ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) 0 ≫
        (adjUnderlyingPairing alg').pairing).app X
      = ((((adjRightModule T.adj).postcomp T.forget).functor.map
        ((monadPow T.adj.toMonad 0).map φ.f) ≫ 𝟙 _) ≫ (adjAlg alg').a) := rfl
  have eR : (adjUnderlyingPairing alg).pairing.app X ≫
      (adjUnderlyingTargetHom φ).app X = alg.a ≫ φ.f :=
    congrArg (· ≫ φ.f) qA
  have q1 : (((adjRightModule T.adj).postcomp T.forget).functor.map
      ((monadPow T.adj.toMonad 0).map φ.f))
      = (((adjRightModule T.adj).postcomp T.forget).functor.map φ.f) :=
    congrArg _ p1
  have q2 : ((((adjRightModule T.adj).postcomp T.forget).functor.map
      ((monadPow T.adj.toMonad 0).map φ.f) ≫ 𝟙 _))
      = (((adjRightModule T.adj).postcomp T.forget).functor.map φ.f) :=
    (Category.comp_id _).trans q1
  have eM : ((((adjRightModule T.adj).postcomp T.forget).functor.map
      ((monadPow T.adj.toMonad 0).map φ.f) ≫ 𝟙 _) ≫ (adjAlg alg').a)
      = ((((adjRightModule T.adj).postcomp T.forget).functor.map φ.f) ≫ alg'.a) :=
    (congrArg (· ≫ (adjAlg alg').a) q2).trans
      (congrArg ((((adjRightModule T.adj).postcomp T.forget).functor.map φ.f) ≫ ·) qA')
  have hRT : (((adjRightModule T.adj).postcomp T.forget).functor.map φ.f)
      = T.map φ.f := rfl
  have eN : ((((adjRightModule T.adj).postcomp T.forget).functor.map φ.f) ≫ alg'.a)
      = alg.a ≫ φ.f :=
    (congrArg (· ≫ alg'.a) hRT).trans φ.h
  exact eL.trans (eM.trans (eN.trans eR.symm))

/-- Evaluated map induced by an algebra morphism, mirroring `emUnderlyingHom`:
whisker the pairing-level map with `resolutionEvalPoint`. -/
@[no_expose]
noncomputable def adjEvaluatedHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    adjEvaluatedAugmented alg ⟶ adjEvaluatedAugmented alg' :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).map
    (BalancedPairing.toSimplicialAugmentedMap (adjUnderlyingPairing alg)
      (adjUnderlyingPairing alg')
      (𝟙 ((adjRightModule T.adj).postcomp T.forget))
      (algebraLeftModuleHom ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
      (adjUnderlyingTargetHom φ)
      (adjUnderlying_hq φ))

/-- The simplicial component of an adjunction-side evaluated map. Mirrors
`resolutionHom_left` (`BarResolution`) and `emUnderlyingHom_left`. -/
private theorem adjEvaluatedHom_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (adjEvaluatedHom φ).left =
      Functor.whiskerRight
        (BalancedPairing.toSimplicialAugmentedMap (adjUnderlyingPairing alg)
          (adjUnderlyingPairing alg')
          (𝟙 ((adjRightModule T.adj).postcomp T.forget))
          (algebraLeftModuleHom
            ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
          (adjUnderlyingTargetHom φ)
          (adjUnderlying_hq φ)).left resolutionEvalPoint := rfl

/-- The target component of an adjunction-side evaluated map, as the whiskered
target map (private form of `resolutionHom_right` in `BarResolution`). A public `= φ.f`
statement is not statable for the same reason as above (hidden `.right`
projections); the `φ.f` identification happens at the concrete level via
`adjEvalPoint_map_app` + `adjUnderlyingTargetHom_app` in the naturality
proof. -/
private theorem adjEvaluatedHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (adjEvaluatedHom φ).right =
      resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) := rfl

/-- Full naturality in algebra morphisms, by augmented `hom_ext` from the left
`barChangeHom` naturality and the right identity. -/
theorem adjToEMComparison_naturality {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    adjToEMComparison alg ≫ emUnderlyingHom φ =
      adjEvaluatedHom φ ≫ adjToEMComparison alg' := by
  apply SimplicialObject.Augmented.hom_ext
  · -- `_`-threaded term mode: every `rw` motive stays over folded or
    -- genuine-simplicial terms. Unfolding `adjToEMComparison_left`-style
    -- equations inside one big `rw` left the goal ill-typed at implicit
    -- transparency (the `toSimplicialFunctor` gap) and later `rw`s failed.
    have e12 : ((adjToEMComparison alg ≫ emUnderlyingHom φ).left) =
        (Functor.whiskerRight
          ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg)).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg))
          resolutionEvalPoint ≫
        algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) φ) := by
      rw [Comma.comp_left, adjToEMComparison_left, emUnderlyingHom_left]
      -- `rw` normalizes the LHS to the stated RHS but its auto-`rfl`
      -- (reducible transparency) does not close across the
      -- `toSimplicialFunctor` gap; explicit `rfl` (default) does.
      rfl
    have eC : ((adjUnderlyingPairing alg).toSimplicialAugmentedMap
          (adjUnderlyingPairing alg') (𝟙 ((adjRightModule T.adj).postcomp T.forget))
          (algebraLeftModuleHom
            ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
          (adjUnderlyingTargetHom φ) (adjUnderlying_hq φ)).left =
        twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
          (algebraLeftModuleHom
            ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) :=
      BalancedPairing.toSimplicialAugmentedMap_left _ _ _ _ _ _
    have e45 : ((adjEvaluatedHom φ ≫ adjToEMComparison alg').left) =
        (Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)))
          resolutionEvalPoint ≫
        Functor.whiskerRight
          ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg')).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg'))
          resolutionEvalPoint) := by
      rw [Comma.comp_left, adjEvaluatedHom_left, adjToEMComparison_left, eC]
      -- `rw` normalizes the LHS to the stated RHS but its auto-`rfl`
      -- (reducible transparency) does not close across the
      -- `toSimplicialFunctor` gap; explicit `rfl` (default) does.
      rfl
    have heL : (adjLeftIso (T := T) alg).hom ≫
          (leftModuleRestrictAlongHom (adjMonadHom (T := T))).map
            (algebraLeftModuleHom φ) =
        algebraLeftModuleHom
            ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ) ≫
          (adjLeftIso (T := T) alg').hom := by
      refine Algebra.Hom.ext' _ _ _ _ ?_
      ext X0
      simp only [Algebra.comp_f, adjLeftIso_hom_f]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    have hslide := (barChangeHom_naturality (adjMonadHom (T := T))
      (𝟙 (emRightModule.postcomp T.forget)) (algebraLeftModuleHom φ)).symm
    have hW : (Functor.whiskerRight
          ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg)).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg))
          resolutionEvalPoint ≫
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 (emRightModule.postcomp T.forget))
            (algebraLeftModuleHom φ))
          ((evaluation (Discrete PUnit.{1}) C).obj
            (⟨PUnit.unit⟩ : Discrete PUnit.{1}))) =
        (Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)))
          resolutionEvalPoint ≫
        Functor.whiskerRight
          ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg')).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg'))
          resolutionEvalPoint) := by
      -- `hEVAL'` aligns the evaluation object to `resolutionEvalPoint` by
      -- `rfl` on a *single-factor* equation (motive-local, well-typed);
      -- `rw [hEVAL']` then abstracts only that hom (pinned type, safe),
      -- unlike `rw [hEVAL]` which abstracts the shared object into a
      -- motive over the still-concrete first factor (ill-typed at implicit
      -- transparency). The rest are hom-pattern rewrites (safe motives).
      have hEVAL' : Functor.whiskerRight
            (twoSidedBarHom (𝟙 (emRightModule.postcomp T.forget))
              (algebraLeftModuleHom φ))
            ((evaluation (Discrete PUnit.{1}) C).obj
              (⟨PUnit.unit⟩ : Discrete PUnit.{1})) =
          Functor.whiskerRight
            (twoSidedBarHom (𝟙 (emRightModule.postcomp T.forget))
              (algebraLeftModuleHom φ))
            resolutionEvalPoint := rfl
      rw [hEVAL']
      -- Whiskered same-functor pairs combine in term mode
      -- (`Eq.trans`/`congrArg`, default transparency). `rw` cannot form the
      -- motive here: the goal is ill-typed at implicit transparency (the
      -- `toSimplicialFunctor` gap), so even `rw` matching fails with
      -- "did not find occurrence". The middle-composite rewrite stays in
      -- hom-pattern `rw` (safe motives) on the unwhiskered equality.
      have mid : ((((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg)).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg)) ≫
          twoSidedBarHom (𝟙 (emRightModule.postcomp T.forget))
            (algebraLeftModuleHom φ))) =
          (((twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))) ≫
          ((twoSidedBarIso (adjRightIso (T := T)) (adjLeftIso alg')).hom ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg')))) := by
        -- Safe prefix: unfold Isos (rfl), reassoc, slide, simplify
        -- right-module map, reassoc, fuse LHS pair, simplify right identity.
        -- All motives are hom-pattern and well-typed at implicit transparency.
        rw [twoSidedBarIso_hom, twoSidedBarIso_hom, Category.assoc, hslide,
          Functor.map_id, ← Category.assoc, twoSidedBarHom_comp,
          Category.comp_id]
        -- Align LHS left-module composite via `heL` (module-hom motive, safe).
        rw [heL]
        -- Remaining goal fuses the RHS pair `D ≫ I`, whose middle object is
        -- only semireducibly equal (`adjAlg` vs `obj` unfolding), so `rw`
        -- cannot form the motive at implicit transparency. Finish in term
        -- mode (default transparency) with explicit typed equalities.
        have hDI : (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) ≫
            twoSidedBarHom adjRightIso.hom (adjLeftIso alg').hom) =
            twoSidedBarHom adjRightIso.hom
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ) ≫
              (adjLeftIso alg').hom) := by
          have hcomp := twoSidedBarHom_comp
            (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            adjRightIso.hom
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
            (adjLeftIso alg').hom
          have hid : (𝟙 ((adjRightModule T.adj).postcomp T.forget) ≫
              adjRightIso.hom) = adjRightIso.hom :=
            Category.id_comp _
          exact hcomp.trans (congrArg
            (fun gR => twoSidedBarHom gR
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ) ≫
              (adjLeftIso alg').hom)) hid)
        have hRHS : (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) ≫
            (twoSidedBarHom adjRightIso.hom (adjLeftIso alg').hom ≫
              barChangeHom (adjMonadHom (T := T))
                (emRightModule.postcomp T.forget) (algebraLeftModule alg'))) =
            ((twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) ≫
            twoSidedBarHom adjRightIso.hom (adjLeftIso alg').hom) ≫
            barChangeHom (adjMonadHom (T := T))
              (emRightModule.postcomp T.forget) (algebraLeftModule alg')) :=
          (Category.assoc _ _ _).symm
        exact (hRHS.trans (congrArg
          (fun x => x ≫ barChangeHom (adjMonadHom (T := T))
            (emRightModule.postcomp T.forget) (algebraLeftModule alg')) hDI)).symm
      exact (Functor.whiskerRight_comp _ _ _).symm.trans
        ((congrArg (fun f => Functor.whiskerRight f resolutionEvalPoint) mid).trans
          (Functor.whiskerRight_comp _ _ _))
    exact e12.trans (hW.trans e45.symm)
  · have eR12 : ((adjToEMComparison alg ≫ emUnderlyingHom φ).right) =
        (resolutionEvalPoint.map (adjDataAugHom alg).right ≫ φ.f) := by
      rw [Comma.comp_right, adjToEMComparison_right, emUnderlyingHom_right]
      rfl
    have eR45 : ((adjEvaluatedHom φ ≫ adjToEMComparison alg').right) =
        (resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) ≫
          resolutionEvalPoint.map (adjDataAugHom alg').right) := by
      rw [Comma.comp_right, adjEvaluatedHom_right, adjToEMComparison_right]
      rfl
    -- Concrete-level closure: both whiskered Data-identities are identities
    -- (the `𝟙 _` objects come from `Functor.map_id`, never inferred against
    -- hidden types), and the whiskered target map is `φ.f` (evaluation acts
    -- by application). All unfolding below stays over private/public
    -- helpers, never over hidden `.right`s.
    have hL := (congrArg resolutionEvalPoint.map
      (rfl : (adjDataAugHom (T := T) alg).right = 𝟙 _)).trans
      (Functor.map_id _ _)
    have hR := (congrArg resolutionEvalPoint.map
      (rfl : (adjDataAugHom (T := T) alg').right = 𝟙 _)).trans
      (Functor.map_id _ _)
    have uEq : resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) =
        φ.f :=
      (adjEvalPoint_map_app _).trans (adjUnderlyingTargetHom_app _ _)
    -- Term-mode closure: `rw` would rebuild motives at implicit
    -- transparency, where the inferred `𝟙 _` objects (spelled through
    -- `.toAugmented.right`) do not re-unfold. `congrArg`/`trans` elaborate
    -- at default transparency and avoid motives entirely.
    have h2map : (resolutionEvalPoint.map (adjDataAugHom alg).right ≫ φ.f) =
        (resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) ≫
          resolutionEvalPoint.map (adjDataAugHom alg').right) :=
      let step1 : (resolutionEvalPoint.map (adjDataAugHom alg).right ≫ φ.f) =
          φ.f :=
        (congrArg (· ≫ φ.f) hL).trans (Category.id_comp _)
      let step2 : (resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) ≫
          resolutionEvalPoint.map (adjDataAugHom alg').right) =
          resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) :=
        (congrArg
          (resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) ≫ ·)
          hR).trans (Category.comp_id _)
      step1.trans (step2.trans uEq).symm
    exact eR12.trans (h2map.trans eR45.symm)

/-- Transport-normalized target law for evaluated maps: the whiskered target
acts as `φ.f` up to the public point identifications. -/
theorem adjEvaluatedHom_right_eqToHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (adjEvaluatedHom φ).right ≫ eqToHom (adjEvaluatedAugmented_point alg') =
      eqToHom (adjEvaluatedAugmented_point alg) ≫ φ.f := by
  have hR : (adjEvaluatedHom (T := T) φ).right =
      resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) :=
    adjEvaluatedHom_right φ
  have uEq : resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) =
      φ.f :=
    (adjEvalPoint_map_app _).trans (adjUnderlyingTargetHom_app _ _)
  have hRightEq : (adjEvaluatedHom (T := T) φ).right = φ.f :=
    hR.trans uEq
  have hStep1 : ((adjEvaluatedHom (T := T) φ).right ≫
      eqToHom (adjEvaluatedAugmented_point alg')) =
      (φ.f ≫ eqToHom (adjEvaluatedAugmented_point alg')) :=
    congrArg (· ≫ eqToHom (adjEvaluatedAugmented_point alg')) hRightEq
  have hStep2 : (φ.f ≫ eqToHom (adjEvaluatedAugmented_point alg')) =
      (eqToHom (adjEvaluatedAugmented_point alg) ≫ φ.f) := by
    have hL : (φ.f ≫ eqToHom (adjEvaluatedAugmented_point alg')) = φ.f :=
      Category.comp_id _ |>.trans (by rfl)
    have hRr : (eqToHom (adjEvaluatedAugmented_point alg) ≫ φ.f) = φ.f :=
      Category.id_comp _ |>.trans (by rfl)
    exact hL.trans hRr.symm
  exact hStep1.trans hStep2

/-- Identity evaluated maps are identities. -/
theorem adjEvaluatedHom_id (alg : T.Algebra) :
    adjEvaluatedHom (𝟙 alg) = 𝟙 (adjEvaluatedAugmented alg) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have e1 : (adjEvaluatedHom (𝟙 alg)).left =
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map (𝟙 alg))))
          resolutionEvalPoint := by
      simp only [adjEvaluatedHom,
        SimplicialObject.Augmented.whiskeringObj_map_left]
      rfl
    have eMapId : ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map
        (𝟙 alg)) = 𝟙 _ := by
      rw [Functor.map_id]
    have eLeftHom : (algebraLeftModuleHom
        ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map (𝟙 alg))) =
        𝟙 _ := by
      rw [eMapId]
      exact algebraLeftModuleHom_id _
    have e2 : Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map (𝟙 alg))))
          resolutionEvalPoint =
        𝟙 ((adjEvaluatedAugmented alg).left) := by
      rw [eLeftHom, twoSidedBarHom_id, Functor.whiskerRight_id']
      rfl
    exact e1.trans e2
  · have e1r : (adjEvaluatedHom (𝟙 alg)).right =
        resolutionEvalPoint.map (adjUnderlyingTargetHom (𝟙 alg)) := by
      rw [adjEvaluatedHom_right]
    have eTargetId : (adjUnderlyingTargetHom (𝟙 alg)) = 𝟙 _ := by
      ext X
      simp only [adjUnderlyingTargetHom_app, Algebra.id_f, NatTrans.id_app]
      rfl
    have e2r : resolutionEvalPoint.map (adjUnderlyingTargetHom (𝟙 alg)) =
        𝟙 (adjEvaluatedAugmented alg).right := by
      rw [eTargetId]
      exact Functor.map_id _ _
    exact e1r.trans e2r

/-- Composition of evaluated maps is the evaluated composite. -/
theorem adjEvaluatedHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    adjEvaluatedHom φ ≫ adjEvaluatedHom ψ = adjEvaluatedHom (φ ≫ ψ) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have f1 : (adjEvaluatedHom φ ≫ adjEvaluatedHom ψ).left =
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)))
          resolutionEvalPoint ≫
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map ψ)))
          resolutionEvalPoint := by
      rw [Comma.comp_left]
      simp only [adjEvaluatedHom,
        SimplicialObject.Augmented.whiskeringObj_map_left]
      rfl
    have fMap : ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map
        (φ ≫ ψ)) =
        ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ) ≫
        ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map ψ) := by
      rw [Functor.map_comp]
    have f2 : Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)))
          resolutionEvalPoint ≫
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map ψ)))
          resolutionEvalPoint =
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map (φ ≫ ψ))))
          resolutionEvalPoint := by
      rw [← Functor.whiskerRight_comp, twoSidedBarHom_comp, Category.id_comp,
        algebraLeftModuleHom_comp, ← fMap]
    have f3 : Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map (φ ≫ ψ))))
          resolutionEvalPoint =
        (adjEvaluatedHom (φ ≫ ψ)).left :=
      rfl
    exact f1.trans (f2.trans f3)
  · have g1 : (adjEvaluatedHom φ ≫ adjEvaluatedHom ψ).right =
        resolutionEvalPoint.map (adjUnderlyingTargetHom φ) ≫
          resolutionEvalPoint.map (adjUnderlyingTargetHom ψ) :=
      rfl
    have gTarget : (adjUnderlyingTargetHom (φ ≫ ψ)) =
        (adjUnderlyingTargetHom φ) ≫ (adjUnderlyingTargetHom ψ) := by
      ext X
      simp only [adjUnderlyingTargetHom_app, Algebra.comp_f,
        NatTrans.comp_app]
      rfl
    have g2 : resolutionEvalPoint.map (adjUnderlyingTargetHom φ) ≫
        resolutionEvalPoint.map (adjUnderlyingTargetHom ψ) =
        resolutionEvalPoint.map (adjUnderlyingTargetHom (φ ≫ ψ)) := by
      rw [← Functor.map_comp, ← gTarget]
    have g3 : resolutionEvalPoint.map (adjUnderlyingTargetHom (φ ≫ ψ)) =
        (adjEvaluatedHom (φ ≫ ψ)).right := by
      rw [adjEvaluatedHom_right]
    exact g1.trans (g2.trans g3)

/-- Auxiliary left projection, proved by unfolding the opaque comparison
(private so the unfolding is permitted). -/
private theorem adjLiteralIso_hom_left_aux (alg : T.Algebra) :
    ((adjLiteralIso alg).hom).left = (adjLiteralBarIso alg).hom :=
  rfl

/-- Left projection of the honest augmented comparison: the simplicial
isomorphism. -/
theorem adjLiteralIso_hom_left (alg : T.Algebra) :
    ((adjLiteralIso alg).hom).left = (adjLiteralBarIso alg).hom :=
  adjLiteralIso_hom_left_aux alg

/-- Auxiliary right projection, proved by unfolding the opaque comparison
(private so the unfolding is permitted): the target component is the identity. -/
private theorem adjLiteralIso_hom_right_aux (alg : T.Algebra) :
    ((adjLiteralIso alg).hom).right =
      𝟙 (adjLiteralAugmented alg).right :=
  rfl

/-- Transport-normalized right projection of the honest comparison: identity
up to the public point identifications. -/
theorem adjLiteralIso_hom_right_eqToHom (alg : T.Algebra) :
    ((adjLiteralIso alg).hom).right ≫
      eqToHom (adjEvaluatedAugmented_point alg) =
      eqToHom (adjLiteralAugmented_point alg) := by
  have hR : ((adjLiteralIso (T := T) alg).hom).right =
      𝟙 (adjLiteralAugmented (T := T) alg).right :=
    adjLiteralIso_hom_right_aux alg
  have hStep1 : (((adjLiteralIso (T := T) alg).hom).right ≫
      eqToHom (adjEvaluatedAugmented_point alg)) =
      (𝟙 _ ≫ eqToHom (adjEvaluatedAugmented_point alg)) :=
    congrArg (· ≫ eqToHom (adjEvaluatedAugmented_point alg)) hR
  have hStep2 : (𝟙 (adjLiteralAugmented (T := T) alg).right ≫
      eqToHom (adjEvaluatedAugmented_point alg)) =
      eqToHom (adjLiteralAugmented_point alg) := by
    have hL : (𝟙 (adjLiteralAugmented (T := T) alg).right ≫
        eqToHom (adjEvaluatedAugmented_point alg)) =
        eqToHom (adjEvaluatedAugmented_point alg) :=
      Category.id_comp _ |>.trans (by rfl)
    have hRr : (eqToHom (adjLiteralAugmented_point alg)) =
        eqToHom (adjEvaluatedAugmented_point alg) := by rfl
    exact hL.trans hRr.symm
  exact hStep1.trans hStep2

/-- Literal-to-EM comparison: the honest literal image compared with the
Eilenberg--Moore underlying augmentation, via the literal iso and the
surrogate comparison. -/
noncomputable def adjLiteralToEMComparison (alg : T.Algebra) :
    adjLiteralAugmented alg ⟶ emUnderlyingAugmented alg :=
  (adjLiteralIso alg).hom ≫ adjToEMComparison alg

/-- Naturality of the honest comparison: literal maps correspond to surrogate
maps under the iso. -/
theorem adjLiteralIso_naturality {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    adjLiteralHom φ ≫ (adjLiteralIso alg').hom =
      (adjLiteralIso alg).hom ≫ adjEvaluatedHom φ := by
  apply SimplicialObject.Augmented.hom_ext
  · have eL12 : ((adjLiteralHom φ ≫ (adjLiteralIso alg').hom).left) =
        (adjLiteralHom φ).left ≫ (adjLiteralBarIso alg').hom := by
      rw [Comma.comp_left, adjLiteralIso_hom_left]
    have eL45 : (((adjLiteralIso alg).hom ≫ adjEvaluatedHom φ).left) =
        (adjLiteralBarIso alg).hom ≫ (adjEvaluatedHom φ).left := by
      rw [Comma.comp_left, adjLiteralIso_hom_left]
    have hEvalL : (adjEvaluatedHom (T := T) φ).left =
        Functor.whiskerRight
          (twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)))
          resolutionEvalPoint := by
      have hC : ((adjUnderlyingPairing alg).toSimplicialAugmentedMap
            (adjUnderlyingPairing alg') (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
            (adjUnderlyingTargetHom φ) (adjUnderlying_hq φ)).left =
          twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ)) :=
        BalancedPairing.toSimplicialAugmentedMap_left _ _ _ _ _ _
      have hW : (adjEvaluatedHom (T := T) φ).left =
          Functor.whiskerRight
            ((adjUnderlyingPairing alg).toSimplicialAugmentedMap
              (adjUnderlyingPairing alg') (𝟙 ((adjRightModule T.adj).postcomp T.forget))
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))
              (adjUnderlyingTargetHom φ) (adjUnderlying_hq φ)).left
            resolutionEvalPoint := rfl
      exact hW.trans
        (congrArg (fun m => Functor.whiskerRight m resolutionEvalPoint) hC)
    ext Δ
    have hIso : ((adjLiteralBarIso (T := T) alg).hom).app Δ =
        eqToHom (adjLiteralBar_obj_eq alg Δ) := by
      have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
        obtain ⟨d⟩ := Δ
        exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
      rw [hΔ]
      exact adjLiteralBarIso_hom_app alg _
    have hIso' : ((adjLiteralBarIso (T := T) alg').hom).app Δ =
        eqToHom (adjLiteralBar_obj_eq alg' Δ) := by
      have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
        obtain ⟨d⟩ := Δ
        exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
      rw [hΔ]
      exact adjLiteralBarIso_hom_app alg' _
    have hLit : ((adjLiteralHom (T := T) φ).left).app Δ =
        T.forget.map ((((adjAugmented T.adj).left).obj Δ).map φ) :=
      adjLiteralHom_left_app _ _
    have hEval : ((adjEvaluatedHom (T := T) φ).left).app Δ =
        resolutionEvalPoint.map
          ((twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
            (algebraLeftModuleHom
              ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))).app
            Δ) := by
      rw [hEvalL]
      rfl
    rw [eL12, eL45] at *
    simp only [NatTrans.comp_app] at *
    rw [hLit, hEval, hIso, hIso']
    have hAgree : T.forget.map ((((adjAugmented T.adj).left).obj Δ).map φ) ≫
        eqToHom (adjLiteralBar_obj_eq alg' Δ) =
        eqToHom (adjLiteralBar_obj_eq alg Δ) ≫
          resolutionEvalPoint.map
            ((twoSidedBarHom (𝟙 ((adjRightModule T.adj).postcomp T.forget))
              (algebraLeftModuleHom
                ((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ))).app
              Δ) := by
      have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
        obtain ⟨d⟩ := Δ
        exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
      rw [hΔ]
      have hIdL : eqToHom (adjLiteralBar_obj_eq alg
          (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) =
          𝟙 _ := rfl
      have hIdR : eqToHom (adjLiteralBar_obj_eq alg'
          (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) =
          𝟙 _ := rfl
      erw [hIdL, hIdR, Category.comp_id, Category.id_comp]
      -- Both sides compute to forgotten free-monad-pow maps over the same
      -- monad `T.adj.toMonad`: unfold via the `rfl` computation lemmas.
      have hψ : (((algebraFunctorOfMonadHom (adjMonadHom (T := T))).map φ).f) =
          φ.f := rfl
      -- Bind the identity module hom so `.f` resolves (dot notation does
      -- not unfold `𝟙`-headed applications); the factor is then `rfl`.
      set fR1 : (adjRightModule T.adj).postcomp T.forget ⟶
          (adjRightModule T.adj).postcomp T.forget := 𝟙 _ with hdef
      have h1R : ∀ (X : C), (fR1.f.app X) = 𝟙 _ := fun X => rfl
      simp only [adjAugmented_left, adjBar_obj_map, adjRightModule_functor,
        adjEvalPoint_map_app,
        twoSidedBarHom_app_app_op_mk, algebraLeftModuleHom_f_app,
        Monad.forget_map, hψ, h1R, RightModule.postcomp_functor,
        Functor.comp_map]
      -- Residue: forgotten map vs its `.f` form plus `≫ 𝟙`; close in
      -- term mode (no `rw` motives over the forgotten types).
      have eF : T.forget.map (T.free.map ((T.adj.toMonad.monadPow
          (Opposite.unop Δ).len).map φ.f)) =
          (T.free.map ((T.adj.toMonad.monadPow
            (Opposite.unop Δ).len).map φ.f)).f :=
        Monad.forget_map _ _
      exact eF.trans (Category.comp_id _).symm
    exact hAgree
  · have eR12 : ((adjLiteralHom φ ≫ (adjLiteralIso alg').hom).right) =
        (φ.f ≫ ((adjLiteralIso alg').hom).right) :=
      Comma.comp_right.trans
        (congrArg (· ≫ ((adjLiteralIso alg').hom).right)
          (adjLiteralHom_right φ))
    have eR45 : (((adjLiteralIso alg).hom ≫ adjEvaluatedHom φ).right) =
        (((adjLiteralIso alg).hom).right ≫
          resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ)) :=
      Comma.comp_right.trans
        (congrArg (((adjLiteralIso alg).hom).right ≫ ·)
          (adjEvaluatedHom_right φ))
    have hIsoR : ((adjLiteralIso (T := T) alg).hom).right =
        𝟙 (adjLiteralAugmented (T := T) alg).right :=
      adjLiteralIso_hom_right_aux alg
    have hIsoR' : ((adjLiteralIso (T := T) alg').hom).right =
        𝟙 (adjLiteralAugmented (T := T) alg').right :=
      adjLiteralIso_hom_right_aux alg'
    have uEq : resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ) =
        φ.f :=
      (adjEvalPoint_map_app _).trans (adjUnderlyingTargetHom_app _ _)
    have hLhs : (φ.f ≫ ((adjLiteralIso alg').hom).right) = φ.f := by
      rw [hIsoR']
      exact Category.comp_id _
    have hRhs : (((adjLiteralIso alg).hom).right ≫
        resolutionEvalPoint.map (adjUnderlyingTargetHom (T := T) φ)) = φ.f := by
      rw [hIsoR, uEq]
      exact Category.id_comp _
    exact eR12.trans (hLhs.trans (hRhs.symm.trans eR45.symm))

/-- Naturality of the literal-to-EM comparison: literal maps correspond to
EM maps. Follows from literal-iso naturality and the accepted surrogate
naturality, without touching the 210-line proof. -/
theorem adjLiteralToEMComparison_naturality {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    adjLiteralHom φ ≫ adjLiteralToEMComparison alg' =
      adjLiteralToEMComparison alg ≫ emUnderlyingHom φ := by
  have h1 := adjLiteralIso_naturality (T := T) φ
  have h2 := adjToEMComparison_naturality (T := T) φ
  change adjLiteralHom φ ≫
      ((adjLiteralIso alg').hom ≫ adjToEMComparison alg') =
    ((adjLiteralIso alg).hom ≫ adjToEMComparison alg) ≫ emUnderlyingHom φ
  calc adjLiteralHom φ ≫ ((adjLiteralIso alg').hom ≫ adjToEMComparison alg')
      _ = (adjLiteralHom φ ≫ (adjLiteralIso alg').hom) ≫
          adjToEMComparison alg' :=
        (Category.assoc _ _ _).symm
      _ = ((adjLiteralIso alg).hom ≫ adjEvaluatedHom φ) ≫
          adjToEMComparison alg' :=
        congrArg (· ≫ adjToEMComparison alg') h1
      _ = (adjLiteralIso alg).hom ≫
          (adjEvaluatedHom φ ≫ adjToEMComparison alg') :=
        Category.assoc _ _ _
      _ = (adjLiteralIso alg).hom ≫
          (adjToEMComparison alg ≫ emUnderlyingHom φ) :=
        congrArg ((adjLiteralIso alg).hom ≫ ·) h2.symm
      _ = ((adjLiteralIso alg).hom ≫ adjToEMComparison alg) ≫
          emUnderlyingHom φ :=
        (Category.assoc _ _ _).symm

end AdjEMComparison

end Monad
end CategoryTheory
