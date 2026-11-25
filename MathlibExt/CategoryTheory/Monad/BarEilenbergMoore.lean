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

public import MathlibExt.CategoryTheory.Monad.BarResolution

/-!
# Eilenberg--Moore-valued monadic bar and underlying comparison

For a monad `T` on `C` and a `T`-algebra `alg`, the Eilenberg--Moore bar
`emBar alg : SimplicialObject (Discrete PUnit ⥤ T.Algebra)` is the Cat-valued
two-sided bar at the free-algebra right module `emRightModule` and the
terminal-index left module of `alg`. In degree `n` at the discrete point this
is the free algebra on `Tⁿ(alg.A)` with structure map `T.μ`; faces and
degeneracies are inherited from the two-sided bar.

The EM-valued bar carries a balanced pairing over the constant functor at
`alg` (pairing `alg.a`) and hence an augmentation `emAugmented alg`, with
algebra-morphism functoriality `emHom` and identity/composition/projection
lemmas. Forgetting along `T.forget` and evaluating at the discrete point is
modelled on the underlying side by postcomposing the right module with the
forgetful functor; the resulting `emUnderlyingAugmented alg` is compared with
`BarResolution.resolutionAugmented alg` by the honest natural isomorphism
`emAugmentedIso alg`, assembled from the module isomorphism
`emModuleIso`, the data isomorphism `barDataIso`, and whiskering transport.
The postcomposed-module comparison is packaged as `emUnderlyingAugmentedFunctor`,
`emAugmented_naturality`, and `emAugmentedNatIso`, with public left/right
computation lemmas.
The actual forgetful image is exposed literally: `emEvaluatedAugmented alg`
evaluates `emAugmented alg` at the terminal point in `T.Algebra`, and
`emLiteralAugmented alg` whiskers that image with `T.forget`. The honest
isomorphism `emLiteralIso alg` identifies this literal image with the
postcomposed-module model, assembled from augmented whiskering/compositor
and `twoSidedBarPostcompWhiskerIso` (outer whiskering, evaluation,
`constComp`, and associators prevent definitional equality);
`emLiteralResolutionIso alg` composes it with `emAugmentedIso` to reach
`BarResolution.resolutionAugmented alg`, with algebra-morphism maps `emLiteralHom` and full
augmented naturality. The underlying contraction, split-epi, and homotopy are
transported from `BarResolution` along this isomorphism.

No contraction in `T.Algebra`, derived equivalence, realization statement, or
adjunction-bar result is claimed here. Carrier directions are explicit: right
modules are algebras for precomposition, left modules for postcomposition,
and the forgetful image is postcomposition with `T.forget`.

Mathematical source: J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.
This file evaluates the Cat-valued two-sided bar `B(R,T,L)` of `Bar` in
`T.Algebra`: the right module is the free-algebra module and the left module
is the terminal-index module of the algebra. The underlying comparison
identifies the forgetful image with the `BarResolution` bar `B(T,T,A)`.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {T : Monad C}

section EMModule

/-- Action of the free-algebra right module: at `X` the algebra morphism
with underlying map `T.μ.app X`, from the free algebra on `T.obj X` to the
free algebra on `X`. The compatibility law is `T.assoc`. -/
def emAction : T.toFunctor ⋙ Monad.free T ⟶ Monad.free T where
  app X :=
    { f := T.μ.app X
      h := T.assoc X }
  naturality X Y f := by
    ext
    exact T.μ.naturality f

/-- The underlying map of the free-algebra action is multiplication. -/
@[simp]
theorem emAction_f (X : C) : (emAction.app X).f = T.μ.app X :=
  rfl

/-- The free-algebra right `T`-module in `T.Algebra`: underlying functor
`T.free` with action `emAction`. -/
def emRightModule : RightModule T T.Algebra :=
  RightModule.mk (Monad.free T) emAction (fun X => by ext; exact T.right_unit X)
    (fun X => by ext; exact T.assoc X)

/-- The underlying functor is the free-algebra functor. -/
@[simp]
theorem emRightModule_functor : emRightModule.functor = Monad.free T :=
  rfl

/-- The action is pointwise `emAction`. -/
@[simp]
theorem emRightModule_action_app (X : C) :
    (emRightModule (T := T)).action.app X = emAction.app X :=
  rfl

/-- The underlying map of the action is multiplication. -/
@[simp]
theorem emRightModule_action_f (X : C) :
    (emRightModule.action.app X).f = T.μ.app X :=
  rfl

/-- The underlying map of the module functor on morphisms. -/
@[simp]
theorem emRightModule_functor_map_f {X Y : C} (g : X ⟶ Y) :
    (emRightModule.functor.map g).f = T.map g :=
  rfl

/-- Postcomposing with the forgetful functor lands definitionally on the
underlying endofunctor: morphisms go to `T.map`. -/
@[simp]
theorem emPostcomp_functor_map {X Y : C} (g : X ⟶ Y) :
    (emRightModule.postcomp T.forget).functor.map g = T.map g :=
  rfl

/-- Postcomposing with the forgetful functor acts by multiplication. -/
@[simp]
theorem emPostcomp_action_app (X : C) :
    (emRightModule.postcomp T.forget).action.app X = T.μ.app X :=
  rfl

/-- The forgotten free-algebra module is isomorphic to the regular right
module: both carry the functor `T` with action `T.μ`, so the identity
comparison applies. -/
noncomputable def emModuleIso :
    emRightModule.postcomp T.forget ≅ RightModule.regular T :=
  Iso.refl _

/-- The forward module-morphism components are identities. -/
@[simp]
theorem emModuleIso_hom_f_app (X : C) :
    ((emModuleIso (T := T)).hom.f).app X = 𝟙 _ :=
  rfl

/-- The inverse module-morphism components are identities. -/
@[simp]
theorem emModuleIso_inv_f_app (X : C) :
    ((emModuleIso (T := T)).inv.f).app X = 𝟙 _ :=
  rfl

end EMModule

section EMBar

/-- Eilenberg--Moore-valued two-sided bar: `twoSidedBar` at the free-algebra
right module and the terminal-index left module of `alg`. -/
noncomputable def emBar (alg : T.Algebra) :
    SimplicialObject (Discrete PUnit.{1} ⥤ T.Algebra) :=
  twoSidedBar T emRightModule (algebraLeftModule alg)

/-- Degree `n` is the levelwise bar object, by `twoSidedBar_obj_op_mk`. -/
@[simp]
theorem emBar_obj (alg : T.Algebra) (n : ℕ) :
    (emBar alg).obj (Opposite.op (SimplexCategory.mk n)) =
      barObj T emRightModule (algebraLeftModule alg) n :=
  rfl

/-- The carrier at the discrete point is `T` applied to `Tⁿ(alg.A)`. -/
@[simp]
theorem emBar_obj_A (alg : T.Algebra) (n : ℕ) (X : Discrete PUnit.{1}) :
    (((emBar alg).obj (Opposite.op (SimplexCategory.mk n))).obj X).A =
      T.obj ((monadPow T n).obj alg.A) :=
  rfl

/-- The structure map at the discrete point is multiplication. -/
@[simp]
theorem emBar_obj_a (alg : T.Algebra) (n : ℕ) (X : Discrete PUnit.{1}) :
    (((emBar alg).obj (Opposite.op (SimplexCategory.mk n))).obj X).a =
      T.μ.app ((monadPow T n).obj alg.A) :=
  rfl

/-- Faces are the two-sided faces at the EM modules. -/
@[simp]
theorem emBar_map_δ_op (alg : T.Algebra) {n : ℕ} (i : Fin (n + 2)) :
    (emBar alg).map (SimplexCategory.δ i).op =
      barFace (T := T) (R := emRightModule) (L := algebraLeftModule alg) n i :=
  twoSidedBar_map_δ_op _ _ _ _

/-- Degeneracies are the two-sided degeneracies at the EM modules. -/
@[simp]
theorem emBar_map_σ_op (alg : T.Algebra) {n : ℕ} (i : Fin (n + 1)) :
    (emBar alg).map (SimplexCategory.σ i).op =
      barDegeneracy (T := T) (R := emRightModule)
        (L := algebraLeftModule alg) n i :=
  twoSidedBar_map_σ_op _ _ _ _

end EMBar

section EMPairing

/-- Constant target functor at the algebra, for the EM pairing. -/
abbrev emTarget (alg : T.Algebra) : Discrete PUnit.{1} ⥤ T.Algebra :=
  (Functor.const (Discrete PUnit.{1})).obj alg

/-- The EM pairing: at every discrete point the algebra morphism with
underlying map `alg.a`, from the free algebra on `alg.A` to `alg`. The
compatibility law is `alg.assoc`. -/
def emPairing (alg : T.Algebra) :
    barObj T emRightModule (algebraLeftModule alg) 0 ⟶ emTarget alg where
  app X :=
    { f := alg.a
      h := alg.assoc.symm }
  naturality := fun X Y f => by
    ext
    change T.map (𝟙 _) ≫ alg.a = alg.a ≫ 𝟙 _
    simp

/-- The underlying map of the pairing is the algebra structure map. -/
@[simp]
theorem emPairing_f (alg : T.Algebra) (X : Discrete PUnit.{1}) :
    ((emPairing (T := T) alg).app X).f = alg.a :=
  rfl

/-- The EM balanced pairing, from the pointwise action equation: both
composites are `T.μ ≫ alg.a` versus `T.map alg.a ≫ alg.a`, equal by
`alg.assoc`. -/
noncomputable def emBalancedPairing (alg : T.Algebra) :
    BalancedPairing T emRightModule (algebraLeftModule alg) :=
  BalancedPairing.mkOfActionEq (emPairing alg) (fun a => by ext; exact alg.assoc)

/-- The underlying map of the balanced pairing is `alg.a`. -/
@[simp]
theorem emBalancedPairing_pairing_f (alg : T.Algebra) (X : Discrete PUnit.{1}) :
    (((emBalancedPairing (T := T) alg).pairing).app X).f = alg.a :=
  rfl

end EMPairing

section EMAugmented

/-- The augmented EM-valued bar, via the genuine transport of the balanced
pairing. -/
noncomputable def emAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented (Discrete PUnit.{1} ⥤ T.Algebra) :=
  BalancedPairing.toSimplicialAugmented (emBalancedPairing alg)

/-- The underlying simplicial object is the EM bar. -/
@[simp]
theorem emAugmented_left (alg : T.Algebra) :
    (emAugmented alg).left = emBar alg :=
  rfl

/-- The augmentation target is the constant functor at `alg`. -/
@[simp]
theorem emAugmented_right (alg : T.Algebra) :
    (emAugmented alg).right = emTarget alg :=
  rfl

/-- The augmentation point is the constant functor at `alg`. -/
@[simp]
theorem emAugmented_point_obj (alg : T.Algebra) :
    (SimplicialObject.Augmented.point.obj (emAugmented alg)) = emTarget alg :=
  rfl

/-- The degree-zero augmentation component is the EM pairing. -/
@[simp]
theorem emAugmented_hom_zero (alg : T.Algebra) :
    (emAugmented alg).hom.app (Opposite.op (SimplexCategory.mk 0)) =
      emPairing alg := by
  unfold emAugmented emBalancedPairing
  rw [BalancedPairing.toSimplicialAugmented_hom_app_mk,
    BalancedPairing.toDataHom_app_zero, BalancedPairing.mkOfActionEq_pairing]

end EMAugmented

section EMFunctoriality

/-- Pointwise target map of an algebra morphism: the component at every
discrete point is `φ` itself, as `Functor.const.map`. -/
noncomputable def emTargetHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    emTarget alg ⟶ emTarget alg' :=
  (Functor.const (Discrete PUnit.{1})).map φ

/-- The underlying map of the target map is the algebra morphism. -/
@[simp]
theorem emTargetHom_app_f {alg alg' : T.Algebra} (φ : alg ⟶ alg')
    (X : Discrete PUnit.{1}) :
    (((emTargetHom (T := T) φ).app X)).f = φ.f :=
  rfl

private theorem emTargetHom_id (alg : T.Algebra) :
    emTargetHom (𝟙 alg) = 𝟙 _ := by
  ext X
  rfl

private theorem emTargetHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    emTargetHom φ ≫ emTargetHom ψ = emTargetHom (φ ≫ ψ) := by
  ext X
  rfl

/-- Degree-zero naturality square for the EM map: `barMap` at level `0`
followed by the target pairing equals the source pairing followed by the
pointwise algebra morphism. This is the algebra-morphism law `φ.h`. -/
theorem em_hq {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    barMap (𝟙 emRightModule) (algebraLeftModuleHom φ) 0 ≫
        (emBalancedPairing alg').pairing =
      (emBalancedPairing alg).pairing ≫ emTargetHom φ := by
  ext X
  simp only [NatTrans.comp_app, barMap_app, algebraLeftModuleHom_f_app,
    Algebra.comp_f, emRightModule_functor_map_f, Algebra.id_f, NatTrans.id_app,
    emBalancedPairing_pairing_f, Category.comp_id]
  exact φ.h

/-- Naturality: an algebra morphism induces a map of augmented EM bars. -/
noncomputable def emHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    emAugmented alg ⟶ emAugmented alg' :=
  BalancedPairing.toSimplicialAugmentedMap (emBalancedPairing alg)
    (emBalancedPairing alg') (𝟙 emRightModule) (algebraLeftModuleHom φ)
    (emTargetHom φ) (em_hq φ)

/-- Identity algebra morphisms induce identity EM maps. -/
theorem emHom_id (alg : T.Algebra) :
    emHom (𝟙 alg) = 𝟙 (emAugmented alg) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have e1 : (emHom (𝟙 alg)).left =
        twoSidedBarHom (𝟙 emRightModule) (𝟙 (algebraLeftModule alg)) := by
      simp only [emHom, algebraLeftModuleHom_id]
      rfl
    have e2 : twoSidedBarHom (𝟙 emRightModule) (𝟙 (algebraLeftModule alg)) =
        𝟙 (twoSidedBar T emRightModule (algebraLeftModule alg)) :=
      twoSidedBarHom_id _ _
    have e3 : (𝟙 (twoSidedBar T emRightModule (algebraLeftModule alg))) =
        𝟙 (emAugmented alg).left :=
      rfl
    exact e1.trans (e2.trans e3)
  · have e1r : (emHom (𝟙 alg)).right = emTargetHom (𝟙 alg) := by
      simp only [emHom]
      rfl
    have e2r : emTargetHom (𝟙 alg) = 𝟙 (emTarget alg) :=
      emTargetHom_id alg
    have e3r : (𝟙 (emTarget alg)) = 𝟙 (emAugmented alg).right :=
      rfl
    exact e1r.trans (e2r.trans e3r)

/-- Composition of algebra morphisms induces composition of EM maps. -/
theorem emHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    emHom φ ≫ emHom ψ = emHom (φ ≫ ψ) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have f1 : (emHom φ ≫ emHom ψ).left =
        twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom φ) ≫
          twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom ψ) := by
      rw [Comma.comp_left]
      simp only [emHom]
      rfl
    have f2 : twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom φ) ≫
        twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom ψ) =
        twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom (φ ≫ ψ)) := by
      rw [twoSidedBarHom_comp, Category.id_comp, algebraLeftModuleHom_comp]
    have f3 : twoSidedBarHom (𝟙 emRightModule)
        (algebraLeftModuleHom (φ ≫ ψ)) = (emHom (φ ≫ ψ)).left := by
      simp only [emHom]
      rfl
    exact f1.trans (f2.trans f3)
  · have g1 : (emHom φ ≫ emHom ψ).right =
        emTargetHom φ ≫ emTargetHom ψ := by
      rw [Comma.comp_right]
      simp only [emHom]
      rfl
    have g2 : emTargetHom φ ≫ emTargetHom ψ = emTargetHom (φ ≫ ψ) :=
      emTargetHom_comp φ ψ
    have g3 : emTargetHom (φ ≫ ψ) = (emHom (φ ≫ ψ)).right := by
      simp only [emHom]
      rfl
    exact g1.trans (g2.trans g3)

/-- The simplicial component of an EM map is the two-sided bar map at the
identity right-module morphism. -/
theorem emHom_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emHom φ).left =
      twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom φ) := by
  simp only [emHom]
  rfl

/-- The target component of an EM map is the pointwise algebra morphism. -/
theorem emHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emHom φ).right = emTargetHom φ := by
  simp only [emHom]
  rfl

end EMFunctoriality

section UnderlyingComparison

/-- Underlying balanced pairing for the forgotten module: target the regular
target functor and pair by `alg.a`. This is the forgetful image of the EM
pairing, since forgetting `free` composed with evaluation is `T`. -/
noncomputable def emUnderlyingPairing (alg : T.Algebra) :
    BalancedPairing T (emRightModule.postcomp T.forget)
      (algebraLeftModule alg) where
  target := BarRegularContraction.regularTarget (algebraLeftModule alg)
  pairing :=
    { app := fun _ => alg.a
      naturality := fun _ _ _ => by
        change T.map (𝟙 _) ≫ alg.a = alg.a ≫ 𝟙 _
        simp }
  balanced :=
    (isBalancedPairing_iff_action_eq (T := T)).mpr (fun a => alg.assoc)

/-- The underlying pairing component is the algebra structure map. -/
@[simp]
theorem emUnderlyingPairing_pairing_app (alg : T.Algebra)
    (a : Discrete PUnit.{1}) :
    ((emUnderlyingPairing (T := T) alg).pairing).app a = alg.a :=
  rfl

/-- The underlying augmented object in `C`: the genuine augmentation of the
forgotten bar, evaluated at the discrete point. -/
noncomputable def emUnderlyingAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).obj
    (BalancedPairing.toSimplicialAugmented (emUnderlyingPairing alg))

/-- The augmentation target is the algebra carrier. -/
@[simp]
theorem emUnderlyingAugmented_point (alg : T.Algebra) :
    (emUnderlyingAugmented alg).right = alg.A :=
  rfl

/-- The forgotten bar in `C`: the algebra-valued bar at the postcomposed
right module. Faces are `T.forget.map` of the EM faces by
`barFaceApp_postcomp`. -/
noncomputable def emUnderlyingBar (alg : T.Algebra) : SimplicialObject C :=
  algebraBar (emRightModule.postcomp T.forget) alg

/-- Degree `n` is the forgotten free-algebra value at `Tⁿ(alg.A)`,
inherited from `algebraBar`. Mirrors `BarResolution.resolutionBar_obj`. -/
@[simp]
theorem emUnderlyingBar_obj (alg : T.Algebra) (n : ℕ) :
    (emUnderlyingBar alg).obj (Opposite.op (SimplexCategory.mk n)) =
      (emRightModule.postcomp T.forget).functor.obj
        ((monadPow T n).obj alg.A) :=
  algebraBar_obj _ _ _

/-- Faces are the forgotten two-sided faces evaluated at the discrete point.
Mirrors `BarResolution.resolutionBar_map_δ_op`. -/
@[simp]
theorem emUnderlyingBar_map_δ_op (alg : T.Algebra) {n : ℕ}
    (i : Fin (n + 2)) :
    (emUnderlyingBar alg).map (SimplexCategory.δ i).op =
      barFaceApp (T := T) (R := emRightModule.postcomp T.forget)
        (L := algebraLeftModule alg) n i ⟨PUnit.unit⟩ :=
  algebraBar_map_δ_op _ _ _

/-- Degeneracies insert the unit via `barEtaAtPos` at `alg.A`.
Mirrors `BarResolution.resolutionBar_map_σ_op`. -/
@[simp]
theorem emUnderlyingBar_map_σ_op (alg : T.Algebra) {n : ℕ}
    (i : Fin (n + 1)) :
    (emUnderlyingBar alg).map (SimplexCategory.σ i).op =
      (emRightModule.postcomp T.forget).functor.map
        (barEtaAtPos T n i alg.A) :=
  algebraBar_map_σ_op _ _ _

/-- The underlying simplicial object of the forgotten augmentation is the
forgotten bar. This is definitional, as in `BarResolution`. -/
@[simp]
theorem emUnderlyingAugmented_left (alg : T.Algebra) :
    (emUnderlyingAugmented alg).left = emUnderlyingBar alg :=
  rfl

/-- The degree-zero augmentation component is the algebra structure map. -/
@[simp]
theorem emUnderlyingAugmented_hom_zero (alg : T.Algebra) :
    (emUnderlyingAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = alg.a := by
  unfold emUnderlyingAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    BalancedPairing.toSimplicialAugmented_hom_app_mk,
    BalancedPairing.toDataHom_app_zero]
  change ((emUnderlyingPairing alg).pairing).app (Discrete.mk PUnit.unit) = alg.a
  rfl

/-- The forgotten bar is isomorphic to the `BarResolution` resolution, via the module
isomorphism and evaluation. Honest isomorphism, not definitional equality. -/
noncomputable def emUnderlyingBarIso (alg : T.Algebra) :
    emUnderlyingBar alg ≅ resolutionBar alg :=
  Functor.isoWhiskerRight (twoSidedBarIso emModuleIso (Iso.refl _)) resolutionEvalPoint

/-- The forward underlying comparison component in degree `n` is the whiskered
`barMap` at the module isomorphisms. This removes the `isoWhiskerRight` and
`twoSidedBarIso` unfolding: downstream `simp` with `barMap_app`,
`emModuleIso_hom_f_app`, and `emModRefl_f_app` collapses both reflexive
components to identities. Mirrors `twoSidedBarIso_hom_app_op_mk`. -/
@[simp]
theorem emUnderlyingBarIso_hom_app (alg : T.Algebra) (n : ℕ) :
    (emUnderlyingBarIso alg).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
      resolutionEvalPoint.map (barMap emModuleIso.hom (Iso.refl _).hom n) :=
  rfl

/-- The inverse underlying comparison component in degree `n` is the whiskered
`barMap` at the inverse module isomorphisms. Symmetric to
`emUnderlyingBarIso_hom_app`. -/
@[simp]
theorem emUnderlyingBarIso_inv_app (alg : T.Algebra) (n : ℕ) :
    (emUnderlyingBarIso alg).inv.app
      (Opposite.op (SimplexCategory.mk n)) =
      resolutionEvalPoint.map (barMap emModuleIso.inv (Iso.refl _).inv n) :=
  rfl

/-- Reflexive data-level target maps are identities at every component.
Normalizes the `constFunctor` side of the comparison square. -/
@[simp]
theorem emConstRefl_app (Q : Discrete PUnit.{1} ⥤ C)
    (a : Discrete PUnit.{1}) :
    ((SimplicialObject.Data.constFunctor.map (Iso.refl Q).hom).app 0).app a =
      𝟙 _ :=
  rfl

/-- Reflexive module-morphism components on the regular side are identities.
Normalizes `barMap` of the reflexive left-module isomorphism. -/
@[simp]
theorem emModRefl_f_app (L : LeftModule (Discrete PUnit.{1}) T)
    (a : Discrete PUnit.{1}) :
    ((((Iso.refl L).hom).f).app a) = 𝟙 _ :=
  rfl

/-- The data-level comparison square: the module-isomorphism bar map followed
by the regular extension equals the postcomposed extension. By
`hom_eq_of_app_zero_eq` this reduces to degree zero, where both sides are
`alg.a` after normalizing the identity components. -/
theorem emDataAug_w (alg : T.Algebra) :
    (𝟭 (SimplicialObject.Data (Discrete PUnit.{1} ⥤ C))).map
        (barDataIso emModuleIso (Iso.refl _)).hom ≫
        (BarRegularContraction.regularBalancedPairing
          (algebraLeftModule alg)).toDataHom =
      (emUnderlyingPairing alg).toDataHom ≫
        SimplicialObject.Data.constFunctor.map (Iso.refl _).hom := by
  apply SimplicialObject.Data.hom_eq_of_app_zero_eq
  ext a
  change ((T.map (𝟙 _) ≫ 𝟙 _) ≫ alg.a) = (alg.a ≫ 𝟙 _)
  simp only [Functor.map_id, Category.id_comp, Category.comp_id]

/-- Data-level comparison isomorphism between the forgotten augmentation and
the regular augmentation. -/
noncomputable def emDataAugIso (alg : T.Algebra) :
    (emUnderlyingPairing alg).toAugmented ≅
      (BarRegularContraction.regularBalancedPairing
        (algebraLeftModule alg)).toAugmented :=
  Comma.isoMk (barDataIso emModuleIso (Iso.refl _)) (Iso.refl _)
    (emDataAug_w alg)

/-- The honest comparison isomorphism: the forgotten/evaluated augmented EM
bar is naturally isomorphic to `BarResolution.resolutionAugmented`. Outer whiskering,
evaluation, `constComp`, and associators prevent definitional equality, so
the isomorphism is assembled from the data isomorphism by transport along
the genuine augmentation functor and evaluation whiskering. -/
noncomputable def emAugmentedIso (alg : T.Algebra) :
    emUnderlyingAugmented alg ≅ resolutionAugmented alg :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).mapIso
    (SimplicialObject.Data.Augmented.toSimplicialFunctor.mapIso (emDataAugIso alg))

/-- Both augmentations agree in degree zero: each side is `alg.a`. Consumes
`BarResolution.resolutionAugmented_hom_zero`. -/
theorem emUnderlying_hom_zero_eq (alg : T.Algebra) :
    (emUnderlyingAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) =
      (resolutionAugmented alg).hom.app
        (Opposite.op (SimplexCategory.mk 0)) := by
  rw [emUnderlyingAugmented_hom_zero, resolutionAugmented_hom_zero]

/-- The forgotten bar is isomorphic to the left side of the `BarResolution` resolution.
Consumes `BarResolution.resolutionAugmented_left`. -/
noncomputable def emUnderlyingBar_iso_resLeft (alg : T.Algebra) :
    emUnderlyingBar alg ≅ (resolutionAugmented alg).left := by
  rw [resolutionAugmented_left]
  exact emUnderlyingBarIso alg

/-- Pointwise target map for the underlying comparison: the component at
every discrete point is `φ.f`. -/
noncomputable def emUnderlyingTargetHom {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    (emUnderlyingPairing alg).target ⟶ (emUnderlyingPairing alg').target where
  app _ := φ.f
  naturality _ _ _ := by
    change (𝟙 alg.A) ≫ φ.f = φ.f ≫ (𝟙 alg'.A)
    simp

/-- The underlying target map is pointwise the algebra morphism. -/
@[simp]
theorem emUnderlyingTargetHom_app {alg alg' : T.Algebra} (φ : alg ⟶ alg')
    (X : Discrete PUnit.{1}) :
    ((emUnderlyingTargetHom (T := T) φ).app X) = φ.f :=
  rfl

/-- Degree-zero naturality square for the underlying map. Mirrors the degree-zero
compatibility used by `BarResolution.resolutionHom`: after normalization both sides are `φ.h`. -/
theorem emUnderlying_hq {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    barMap (𝟙 (emRightModule.postcomp T.forget)) (algebraLeftModuleHom φ) 0 ≫
        (emUnderlyingPairing alg').pairing =
      (emUnderlyingPairing alg).pairing ≫ emUnderlyingTargetHom φ := by
  ext X
  simp only [NatTrans.comp_app, barMap_app]
  simp only [Functor.id_map]
  simp only [algebraLeftModuleHom_f_app, Algebra.id_f,
    NatTrans.id_app, Category.comp_id,
    emUnderlyingTargetHom_app, emUnderlyingPairing_pairing_app]
  exact φ.h

/-- Naturality: an algebra morphism induces a map of underlying augmentations,
mirroring `BarResolution.resolutionHom`. -/
noncomputable def emUnderlyingHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    emUnderlyingAugmented alg ⟶ emUnderlyingAugmented alg' :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).map
    (BalancedPairing.toSimplicialAugmentedMap (emUnderlyingPairing alg)
      (emUnderlyingPairing alg') (𝟙 (emRightModule.postcomp T.forget))
      (algebraLeftModuleHom φ) (emUnderlyingTargetHom φ)
      (emUnderlying_hq φ))

/-- The simplicial component of an underlying map is the algebra-bar map.
Mirrors `BarResolution.resolutionHom_left`. -/
theorem emUnderlyingHom_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emUnderlyingHom φ).left =
      algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) φ := by
  simp only [emUnderlyingHom,
    SimplicialObject.Augmented.whiskeringObj_map_left,
    BalancedPairing.toSimplicialAugmentedMap_left]
  rfl

/-- The target component of an underlying map is the algebra morphism itself.
Mirrors `BarResolution.resolutionHom_right`. -/
theorem emUnderlyingHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emUnderlyingHom φ).right = φ.f := by
  simp only [emUnderlyingHom,
    SimplicialObject.Augmented.whiskeringObj_map_right,
    BalancedPairing.toSimplicialAugmentedMap_right]
  rfl

/-- Identity algebra morphisms induce identity underlying maps.
Mirrors `BarResolution.resolutionHom_id`. -/
theorem emUnderlyingHom_id (alg : T.Algebra) :
    emUnderlyingHom (𝟙 alg) = 𝟙 (emUnderlyingAugmented alg) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have e1 : (emUnderlyingHom (𝟙 alg)).left =
        algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) (𝟙 alg) := by
      rw [emUnderlyingHom_left]
    have e2 : algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) (𝟙 alg) =
        𝟙 (emUnderlyingBar alg) :=
      algebraBarHom_id _ _
    have e3 : (𝟙 (emUnderlyingBar alg)) =
        𝟙 (emUnderlyingAugmented alg).left :=
      rfl
    exact e1.trans (e2.trans e3.symm)
  · have e1r : (emUnderlyingHom (𝟙 alg)).right =
        (𝟙 alg : alg ⟶ alg).f := by
      rw [emUnderlyingHom_right]
    have e2r : (𝟙 alg : alg ⟶ alg).f = 𝟙 alg.A :=
      Algebra.id_f _
    have e3r : (𝟙 alg.A) = 𝟙 (emUnderlyingAugmented alg).right :=
      rfl
    exact e1r.trans (e2r.trans e3r.symm)

/-- Composition of algebra morphisms induces composition of underlying maps.
Mirrors `BarResolution.resolutionHom_comp`. -/
theorem emUnderlyingHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    emUnderlyingHom φ ≫ emUnderlyingHom ψ = emUnderlyingHom (φ ≫ ψ) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have f1 : (emUnderlyingHom φ ≫ emUnderlyingHom ψ).left =
        algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) φ ≫
          algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) ψ :=
      rfl
    have f2 : algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) φ ≫
        algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) ψ =
        algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) (φ ≫ ψ) := by
      simp only [algebraBarHom_comp, Category.id_comp]
    have f3 : algebraBarHom (𝟙 (emRightModule.postcomp T.forget)) (φ ≫ ψ) =
        (emUnderlyingHom (φ ≫ ψ)).left :=
      rfl
    exact f1.trans (f2.trans f3.symm)
  · have g1 : (emUnderlyingHom φ ≫ emUnderlyingHom ψ).right =
        φ.f ≫ ψ.f :=
      rfl
    have g2 : φ.f ≫ ψ.f = (φ ≫ ψ).f :=
      (Algebra.comp_f _ _).symm
    have g3 : (φ ≫ ψ).f = (emUnderlyingHom (φ ≫ ψ)).right :=
      rfl
    exact g1.trans (g2.trans g3.symm)

/-- The comparison isomorphism is natural in the algebra morphism on
simplicial components. Consumes `BarResolution.resolutionHom_left`: after rewriting
both sides to `algebraBarHom` form, the whiskered `twoSidedBarHom`
composition laws close the square. -/
theorem emNaturality_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emUnderlyingHom φ).left ≫ (emUnderlyingBarIso alg').hom =
      (emUnderlyingBarIso alg).hom ≫ (resolutionHom φ).left := by
  rw [emUnderlyingHom_left, resolutionHom_left]
  change Functor.whiskerRight
      (twoSidedBarHom (𝟙 (emRightModule.postcomp T.forget))
        (algebraLeftModuleHom φ)) resolutionEvalPoint ≫
      Functor.whiskerRight (twoSidedBarHom emModuleIso.hom (Iso.refl _).hom)
        resolutionEvalPoint =
    Functor.whiskerRight (twoSidedBarHom emModuleIso.hom (Iso.refl _).hom)
        resolutionEvalPoint ≫
      Functor.whiskerRight
        (twoSidedBarHom (𝟙 (RightModule.regular T))
          (algebraLeftModuleHom φ)) resolutionEvalPoint
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp,
    twoSidedBarHom_comp, twoSidedBarHom_comp, Iso.refl_hom, Iso.refl_hom,
    Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]

/-- The target components agree: both underlying and resolution maps act by
`φ.f`. Consumes `BarResolution.resolutionHom_right`. -/
theorem emNaturality_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emUnderlyingHom φ).right = (resolutionHom φ).right := by
  rw [emUnderlyingHom_right, resolutionHom_right]

/-- The model comparison acts as the underlying bar iso on simplicial
components, definitionally: both transport the same reflexive module iso
through evaluation. This is the postcomposed-module model comparison,
not the literal forgetful image. -/
@[simp]
theorem emAugmentedIso_hom_left (alg : T.Algebra) :
    (emAugmentedIso alg).hom.left = (emUnderlyingBarIso alg).hom :=
  rfl

/-- The target component of the model comparison is the identity: both
constituent isomorphisms are the identity on targets, transported along
evaluation whiskering. Postcomposed-module model, not the literal
forgetful image. -/
@[simp]
theorem emAugmentedIso_hom_right (alg : T.Algebra) :
    (emAugmentedIso alg).hom.right = 𝟙 _ := by
  have hA : (emAugmentedIso alg).hom.right =
      resolutionEvalPoint.map ((emDataAugIso alg).hom.right) := rfl
  have hB : (emDataAugIso alg).hom.right =
      𝟙 (emUnderlyingPairing alg).toAugmented.right := rfl
  rw [hA, hB]
  exact Functor.map_id _ _

/-- Bundled postcomposed-module underlying augmented functor: objects are
`emUnderlyingAugmented`, maps are `emUnderlyingHom`. Postcomposed-module
model, not the literal forgetful image. -/
noncomputable def emUnderlyingAugmentedFunctor :
    T.Algebra ⥤ SimplicialObject.Augmented C where
  obj alg := emUnderlyingAugmented alg
  map φ := emUnderlyingHom φ
  map_id alg := emUnderlyingHom_id alg
  map_comp φ ψ := (emUnderlyingHom_comp φ ψ).symm

/-- Object computation: bundling recovers `emUnderlyingAugmented`, by `rfl`. -/
@[simp]
theorem emUnderlyingAugmentedFunctor_obj (alg : T.Algebra) :
    emUnderlyingAugmentedFunctor.obj alg = emUnderlyingAugmented alg :=
  rfl

/-- Map computation: bundling recovers `emUnderlyingHom`, by `rfl`. -/
@[simp]
theorem emUnderlyingAugmentedFunctor_map {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    emUnderlyingAugmentedFunctor.map φ = emUnderlyingHom φ :=
  rfl

/-- Full augmented-morphism naturality for the model comparison:
postcomposed-module underlying maps commute with the comparison against
`BarResolution.resolutionHom`, oriented
`emUnderlyingHom φ ≫ (emAugmentedIso alg').hom =
  (emAugmentedIso alg).hom ≫ resolutionHom φ`.
The simplicial square reuses `emNaturality_left`; the target square uses
`emNaturality_right` with the identity comparison components.
Postcomposed-module model, not the literal forgetful image. -/
theorem emAugmented_naturality {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    emUnderlyingHom φ ≫ (emAugmentedIso alg').hom =
      (emAugmentedIso alg).hom ≫ resolutionHom φ := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · rw [Comma.comp_left, Comma.comp_left, emAugmentedIso_hom_left,
      emAugmentedIso_hom_left]
    exact emNaturality_left φ
  · rw [Comma.comp_right, Comma.comp_right, emAugmentedIso_hom_right,
      emAugmentedIso_hom_right, emNaturality_right φ]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Packaged natural isomorphism between the postcomposed-module underlying
augmented functor and the resolution augmented functor, via
`NatIso.ofComponents`. Postcomposed-module model, not the literal forgetful image. -/
noncomputable def emAugmentedNatIso :
    (emUnderlyingAugmentedFunctor : T.Algebra ⥤ SimplicialObject.Augmented C) ≅
      (resolutionAugmentedFunctor : T.Algebra ⥤ SimplicialObject.Augmented C) :=
  NatIso.ofComponents
    (fun alg => by
      rw [emUnderlyingAugmentedFunctor_obj, resolutionAugmentedFunctor_obj]
      exact emAugmentedIso alg)
    (fun φ => by
      rw [emUnderlyingAugmentedFunctor_map, resolutionAugmentedFunctor_map]
      exact emAugmented_naturality φ)

/-- Application recovers `emAugmentedIso`, by `rfl`. -/
@[simp]
theorem emAugmentedNatIso_app (alg : T.Algebra) :
    emAugmentedNatIso.app alg = emAugmentedIso alg :=
  rfl

end UnderlyingComparison

section LiteralComparison

/-- Evaluation at the discrete point in `T.Algebra`, mirroring
`BarResolution.resolutionEvalPoint` in `C`. -/
noncomputable def emEvalAlgebra : (Discrete PUnit.{1} ⥤ T.Algebra) ⥤ T.Algebra :=
  (evaluation (Discrete PUnit.{1}) T.Algebra).obj (Discrete.mk PUnit.unit)

/-- The actual EM-valued bar evaluated at the terminal point: the genuine
augmented object in `T.Algebra` underlying `emAugmented alg`. -/
noncomputable def emEvaluatedAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented T.Algebra :=
  (SimplicialObject.Augmented.whiskeringObj _ _ emEvalAlgebra).obj (emAugmented alg)

/-- The underlying simplicial object of the evaluated bar is the evaluated
EM bar. -/
@[simp]
theorem emEvaluatedAugmented_left (alg : T.Algebra) :
    (emEvaluatedAugmented alg).left = emBar alg ⋙ emEvalAlgebra := by
  unfold emEvaluatedAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_left]
  rfl

/-- The literal forgetful image in `C`: `emEvaluatedAugmented` whiskered with
`T.forget`. The comparison with the postcomposed-module model
`emUnderlyingAugmented` is an honest isomorphism, not a definitional
equality: outer whiskering, evaluation, `constComp`, and associators prevent
strict equality. -/
noncomputable def emLiteralAugmented (alg : T.Algebra) :
    SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj _ _ T.forget).obj
    (emEvaluatedAugmented alg)

/-- The underlying simplicial object of the literal image is the evaluated
bar postcomposed with the forgetful functor. -/
@[simp]
theorem emLiteralAugmented_left (alg : T.Algebra) :
    (emLiteralAugmented alg).left =
      (emEvaluatedAugmented alg).left ⋙ T.forget := by
  unfold emLiteralAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_left]
  rfl

/-- The augmentation point of the literal image is the algebra carrier. -/
@[simp]
theorem emLiteralAugmented_point (alg : T.Algebra) :
    (emLiteralAugmented alg).right = alg.A :=
  rfl

/-- The degree-zero augmentation component of the literal image is the algebra
structure map. -/
@[simp]
theorem emLiteralAugmented_hom_zero (alg : T.Algebra) :
    (emLiteralAugmented alg).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = alg.a := by
  unfold emLiteralAugmented emEvaluatedAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    emAugmented_hom_zero]
  rfl

/-- Evaluation/postcomposition commutation as an explicit isomorphism, so the
literal comparison chain below is well-typed at every transparency: no tactic
must unfold semireducible definitions to see two consecutive links agree. -/
noncomputable def emEvalForgetIso :
    (emEvalAlgebra ⋙ T.forget) ≅
      (functorPostcompOuter T.forget ⋙ resolutionEvalPoint) :=
  Iso.refl _

/-- The honest simplicial comparison: the literal whiskered bar is isomorphic
to the postcomposed-module bar, via the functor associators, the explicit
evaluation/postcomposition commutation iso, and the whiskered genuine
`twoSidedBarPostcompWhiskerIso`. Every link is stated with explicit
`twoSidedBar` functors so consecutive links agree syntactically. -/
noncomputable def emLiteralBarIso (alg : T.Algebra) :
    (emLiteralAugmented alg).left ≅ emUnderlyingBar alg :=
  (Functor.associator
    (twoSidedBar T emRightModule (algebraLeftModule alg))
    emEvalAlgebra T.forget) ≪≫
    (Functor.isoWhiskerLeft
      (twoSidedBar T emRightModule (algebraLeftModule alg))
      emEvalForgetIso) ≪≫
    (Functor.associator
      (twoSidedBar T emRightModule (algebraLeftModule alg))
      (functorPostcompOuter T.forget) resolutionEvalPoint).symm ≪≫
    (Functor.isoWhiskerRight
      (twoSidedBarPostcompWhiskerIso T.forget emRightModule
        (algebraLeftModule alg))
      resolutionEvalPoint)

/-- Functor associator forward components on the literal chain are identities,
by definition. -/
private theorem emLiteralAssoc_hom_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.associator
      (twoSidedBar T emRightModule (algebraLeftModule alg))
      emEvalAlgebra T.forget).hom.app Δ =
      𝟙 _ :=
  rfl

/-- Functor associator symmetric components on the literal chain are
identities, by definition. -/
private theorem emLiteralAssocSymm_hom_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.associator
      (twoSidedBar T emRightModule (algebraLeftModule alg))
      (functorPostcompOuter T.forget) resolutionEvalPoint).symm.hom.app Δ =
      𝟙 _ :=
  rfl

/-- The evaluation-commutation whisker acts by `𝟙`, by definition. -/
private theorem emLiteralWhiskerComm_app (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (Functor.isoWhiskerLeft
      (twoSidedBar T emRightModule (algebraLeftModule alg))
      emEvalForgetIso).hom.app Δ =
      𝟙 _ :=
  rfl

/-- Evaluation at the discrete point acts by application, by definition. -/
private theorem emEvalPoint_map_app {F G : Discrete PUnit.{1} ⥤ C}
    (η : F ⟶ G) :
    resolutionEvalPoint.map η = η.app (Discrete.mk PUnit.unit) :=
  rfl

/-- Evaluation in `T.Algebra` acts by application, by definition. -/
private theorem emEvalAlgebra_map_app {F G : Discrete PUnit.{1} ⥤ T.Algebra}
    (η : F ⟶ G) :
    emEvalAlgebra.map η = η.app (Discrete.mk PUnit.unit) :=
  rfl

/-- Faces of the EM bar, forgotten, agree with faces of the postcomposed bar. -/
private theorem emDataForget_face_agree (alg : T.Algebra) (n : ℕ)
    (a : Discrete PUnit.{1}) :
    ((((barData T emRightModule (algebraLeftModule alg)).δ
      (0 : Fin (n + 2))).app a).f) =
      (((barData T (emRightModule.postcomp T.forget)
        (algebraLeftModule alg)).δ (0 : Fin (n + 2))).app a) := by
  rw [barData_δ_app, barData_δ_app]
  exact (barFaceApp_postcomp T.forget emRightModule
    (algebraLeftModule alg) n _ a).symm

/-- Forgetting the EM augmentation data agrees with the underlying data, by
induction on degree: base case is `alg.a` on both sides; the step uses face
agreement under `barFaceApp_postcomp` and functoriality of forgetting. -/
private theorem emDataForget_agree (alg : T.Algebra) (n : ℕ)
    (a : Discrete PUnit.{1}) :
    (((((emBalancedPairing (T := T) alg).toDataHom.app n).app a)).f) =
      ((((emUnderlyingPairing (T := T) alg).toDataHom.app n).app a)) := by
  induction n with
  | zero =>
    simp only [BalancedPairing.toDataHom_app_zero, emBalancedPairing_pairing_f,
      emUnderlyingPairing_pairing_app] ; rfl
  | succ n ih =>
    simp only [BalancedPairing.toDataHom_app_succ, NatTrans.comp_app,
      Algebra.comp_f, emDataForget_face_agree alg n a, ih] ; rfl

/-- The simplicial comparison has identity components: every associator,
evaluation-commutation, and postcomposition bridge acts by `𝟙`. -/
@[simp]
theorem emLiteralBarIso_hom_app (alg : T.Algebra) (Δ : SimplexCategoryᵒᵖ) :
    (emLiteralBarIso alg).hom.app Δ = 𝟙 _ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ]
  have hdecomp : (emLiteralBarIso alg).hom =
      (Functor.associator
        (twoSidedBar T emRightModule (algebraLeftModule alg))
        emEvalAlgebra T.forget).hom ≫
      (Functor.isoWhiskerLeft
        (twoSidedBar T emRightModule (algebraLeftModule alg))
        emEvalForgetIso).hom ≫
      (Functor.associator
        (twoSidedBar T emRightModule (algebraLeftModule alg))
        (functorPostcompOuter T.forget)
        resolutionEvalPoint).symm.hom ≫
      (Functor.isoWhiskerRight
        (twoSidedBarPostcompWhiskerIso T.forget emRightModule
          (algebraLeftModule alg))
        resolutionEvalPoint).hom := rfl
  rw [hdecomp, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    emLiteralAssoc_hom_app, emLiteralWhiskerComm_app,
    emLiteralAssocSymm_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, emEvalPoint_map_app,
    twoSidedBarPostcompWhiskerIso_hom_app_app_id]
  change 𝟙 (((twoSidedBar T emRightModule (algebraLeftModule alg) ⋙
      emEvalAlgebra ⋙ T.forget).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)))) ≫
    𝟙 (((twoSidedBar T emRightModule (algebraLeftModule alg) ⋙
      emEvalAlgebra ⋙ T.forget).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)))) ≫
    𝟙 (((twoSidedBar T emRightModule (algebraLeftModule alg) ⋙
      emEvalAlgebra ⋙ T.forget).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)))) ≫
    𝟙 (((twoSidedBar T emRightModule (algebraLeftModule alg) ⋙
      emEvalAlgebra ⋙ T.forget).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)))) =
    𝟙 (((twoSidedBar T emRightModule (algebraLeftModule alg) ⋙
      emEvalAlgebra ⋙ T.forget).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))))
  simp only [Category.comp_id]

/-- The literal and model augmentations agree componentwise: forgetting the
evaluated EM augmentation is the postcomposed-module augmentation. Unfolds the
double whiskering and applies `emDataForget_agree`; kept separate so the
`Comma` square below never rewrites with the `𝟙`-valued comparison component,
whose type ascription is invisible below default transparency. -/
private theorem emLiteralHomAgree_app (alg : T.Algebra) (n : ℕ) :
    (emLiteralAugmented alg).hom.app (Opposite.op (SimplexCategory.mk n)) =
      (emUnderlyingAugmented alg).hom.app
        (Opposite.op (SimplexCategory.mk n)) := by
  unfold emLiteralAugmented emEvaluatedAugmented emAugmented
    emUnderlyingAugmented
  simp only [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    BalancedPairing.toSimplicialAugmented_hom_app_mk]
  change T.forget.map (emEvalAlgebra.map
      ((emBalancedPairing alg).toDataHom.app n)) =
    resolutionEvalPoint.map ((emUnderlyingPairing alg).toDataHom.app n)
  rw [emEvalAlgebra_map_app, emEvalPoint_map_app]
  exact emDataForget_agree alg n _

/-- The honest augmented comparison: the literal forgetful image is naturally
isomorphic to the postcomposed-module model. -/
noncomputable def emLiteralIso (alg : T.Algebra) :
    emLiteralAugmented alg ≅ emUnderlyingAugmented alg :=
  Comma.isoMk (emLiteralBarIso alg) (Iso.refl _) (by
    ext Δ
    simp only [NatTrans.comp_app, Functor.id_map]
    have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
      obtain ⟨d⟩ := Δ
      exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
    rw [hΔ, emLiteralHomAgree_app]
    have h1 : (emLiteralBarIso alg).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) =
        𝟙 ((emUnderlyingAugmented alg).left.obj
          (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) :=
      emLiteralBarIso_hom_app alg _
    rw [h1]
    simp only [Functor.id_obj, SimplexCategory.mk_len, Opposite.op_unop,
      emUnderlyingAugmented_point, Functor.const_obj_obj,
      emUnderlyingAugmented_left, emLiteralAugmented_point, Iso.refl_hom,
      Functor.map_id, NatTrans.id_app]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- The final comparison: the actual forgetful image is identified with
`BarResolution.resolutionAugmented`, by composing the literal isomorphism with the existing
model comparison. -/
noncomputable def emLiteralResolutionIso (alg : T.Algebra) :
    emLiteralAugmented alg ≅ resolutionAugmented alg :=
  emLiteralIso alg ≪≫ emAugmentedIso alg

/-- Maps induced by algebra morphisms on the literal image. -/
noncomputable def emLiteralHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    emLiteralAugmented alg ⟶ emLiteralAugmented alg' :=
  (SimplicialObject.Augmented.whiskeringObj _ _ T.forget).map
    ((SimplicialObject.Augmented.whiskeringObj _ _ emEvalAlgebra).map
      (emHom φ))

/-- The simplicial component of a literal map is the doubly whiskered
two-sided bar map. -/
theorem emLiteralHom_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emLiteralHom φ).left =
      Functor.whiskerRight
        (Functor.whiskerRight
          (twoSidedBarHom (𝟙 emRightModule) (algebraLeftModuleHom φ))
          emEvalAlgebra)
        T.forget :=
  rfl

/-- The target component of a literal map is the algebra morphism itself. -/
theorem emLiteralHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (emLiteralHom φ).right = φ.f :=
  rfl

/-- Identity algebra morphisms induce identity literal maps, by the EM identity
law transported along the double whiskering. -/
theorem emLiteralHom_id (alg : T.Algebra) :
    emLiteralHom (𝟙 alg) = 𝟙 (emLiteralAugmented alg) := by
  dsimp only [emLiteralHom, emEvaluatedAugmented, emLiteralAugmented]
  rw [emHom_id, Functor.map_id, Functor.map_id]

/-- Composition of algebra morphisms induces composition of literal maps, by the
EM composition law transported along the double whiskering. -/
theorem emLiteralHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
    (ψ : alg₂ ⟶ alg₃) :
    emLiteralHom φ ≫ emLiteralHom ψ = emLiteralHom (φ ≫ ψ) := by
  dsimp only [emLiteralHom, emEvaluatedAugmented, emLiteralAugmented]
  rw [← Functor.map_comp, ← Functor.map_comp, emHom_comp]

/-- The target component of the final comparison is the identity: both
constituent isomorphisms are the identity on targets, transported along
whiskering. -/
theorem emLiteralResolutionIso_hom_right (alg : T.Algebra) :
    (emLiteralResolutionIso alg).hom.right = 𝟙 _ := by
  have hA : (emLiteralResolutionIso alg).hom =
      (emLiteralIso alg).hom ≫ (emAugmentedIso alg).hom := rfl
  rw [hA, Comma.comp_right]
  change (Iso.refl (emLiteralAugmented alg).right).hom ≫
      resolutionEvalPoint.map
        ((Iso.refl (emUnderlyingPairing alg).toAugmented.right).hom) = 𝟙 _
  simp only [Iso.refl_hom, Functor.map_id]
  exact Category.id_comp _

/-- The underlying comparison has identity components: the module
isomorphism is reflexive, so the whiskered `barMap` collapses. Proved at
morphism level via `.f.app` identities, never unfolding the reflexive iso
itself. -/
private theorem emUnderlyingBarIso_hom_app_id (alg : T.Algebra)
    (Δ : SimplexCategoryᵒᵖ) :
    (emUnderlyingBarIso alg).hom.app Δ = 𝟙 _ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ, emUnderlyingBarIso_hom_app, emEvalPoint_map_app, barMap_app,
    emModuleIso_hom_f_app, emModRefl_f_app]
  simp only [Functor.map_id]
  change 𝟙 ((emUnderlyingBar alg).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) ≫
    𝟙 ((emUnderlyingBar alg).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) =
    𝟙 ((emUnderlyingBar alg).obj
      (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)))
  simp only [Category.id_comp]

/-- Literal and resolution maps agree appwise: both evaluate the same
two-sided bar map and forget, reducing to the same `T.map` composite.
Stated at app level so the definitionally-identified objects (via the
`𝟙`-valued comparisons) typecheck; proved by unfolding both whiskerings to
`twoSidedBarHom` apps. Reuses the existing `emLiteralHom_left`,
`resolutionHom_left`, and `algebraBarHom` component lemmas. -/
private theorem emLiteralHom_app_eq_resolutionHom_app {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') (Δ : SimplexCategoryᵒᵖ) :
    (emLiteralHom φ).left.app Δ = (resolutionHom φ).left.app Δ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
    obtain ⟨d⟩ := Δ
    exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
  rw [hΔ]
  simp only [emLiteralHom_left, resolutionHom_left, algebraBarHom,
    Functor.whiskerRight_app, emEvalAlgebra_map_app,
    twoSidedBarHom_app_app, algebraLeftModuleHom_f_app]
  rfl

/-- Full augmented-morphism naturality for the final comparison: literal maps
commute with the literal-to-resolution isomorphism against
`BarResolution.resolutionHom`. Reuses `hom_ext`, the existing `emLiteralHom_left`,
`resolutionHom_left`, and `algebraBarHom` component lemmas, plus the
`𝟙`-valued comparison components; no new functor bookkeeping. -/
theorem emLiteralResolution_naturality {alg alg' : T.Algebra}
    (φ : alg ⟶ alg') :
    emLiteralHom φ ≫ (emLiteralResolutionIso alg').hom =
      (emLiteralResolutionIso alg).hom ≫ resolutionHom φ := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have hAL : (emLiteralResolutionIso alg).hom.left =
        (emLiteralIso alg).hom.left ≫ (emAugmentedIso alg).hom.left := rfl
    have hAL' : (emLiteralResolutionIso alg').hom.left =
        (emLiteralIso alg').hom.left ≫ (emAugmentedIso alg').hom.left := rfl
    have hLitL : (emLiteralIso alg).hom.left = (emLiteralBarIso alg).hom := rfl
    have hLitL' : (emLiteralIso alg').hom.left =
        (emLiteralBarIso alg').hom := rfl
    rw [Comma.comp_left, Comma.comp_left, hAL, hAL', hLitL, hLitL',
      emAugmentedIso_hom_left,
      emAugmentedIso_hom_left]
    ext Δ
    have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
      obtain ⟨d⟩ := Δ
      exact congrArg Opposite.op (SimplexCategory.mk_len d).symm
    rw [hΔ]
    simp only [← resolutionAugmented_left, ← emUnderlyingAugmented_left]
    rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
      NatTrans.comp_app]
    simp only [emLiteralBarIso_hom_app, emUnderlyingBarIso_hom_app_id,
      emLiteralHom_left, resolutionHom_left, algebraBarHom,
      Functor.whiskerRight_app]
    change (emLiteralHom φ).left.app Δ ≫
        𝟙 ((emLiteralAugmented alg').left.obj Δ) ≫
        𝟙 ((emUnderlyingBar alg').obj Δ) =
      (𝟙 ((emLiteralAugmented alg).left.obj Δ) ≫
        𝟙 ((emUnderlyingBar alg).obj Δ)) ≫
        (resolutionHom φ).left.app Δ
    change (emLiteralHom φ).left.app Δ ≫
        𝟙 ((emLiteralAugmented alg').left.obj Δ) ≫
        𝟙 ((emLiteralAugmented alg').left.obj Δ) =
      (𝟙 ((emLiteralAugmented alg).left.obj Δ) ≫
        𝟙 ((emLiteralAugmented alg).left.obj Δ)) ≫
        (resolutionHom φ).left.app Δ
    simp only [Category.comp_id]
    change (emLiteralHom φ).left.app Δ =
      𝟙 ((resolutionAugmented alg).left.obj Δ) ≫
        (resolutionHom φ).left.app Δ
    simp only [Category.id_comp]
    exact emLiteralHom_app_eq_resolutionHom_app φ _
  · rw [Comma.comp_right, Comma.comp_right, emLiteralHom_right,
      resolutionHom_right, emLiteralResolutionIso_hom_right alg,
      emLiteralResolutionIso_hom_right alg']
    exact (Category.comp_id _).trans (Category.id_comp _).symm

end LiteralComparison

section UnderlyingContraction

/-- The contracted extra degeneracy in `C`, transported from `BarResolution` along the
comparison isomorphism. No contraction in `T.Algebra` is claimed. -/
noncomputable def emExtra (alg : T.Algebra) :
    SimplicialObject.Augmented.ExtraDegeneracy (emUnderlyingAugmented alg) :=
  SimplicialObject.Augmented.ExtraDegeneracy.ofIso (emAugmentedIso alg).symm
    (resolutionExtra alg)

/-- The augmentation is split epi in `C`, inherited from `BarResolution`. -/
noncomputable def emSplitEpi (alg : T.Algebra) :
    SplitEpi (emUnderlyingAugmented alg).hom :=
  (emExtra alg).splitEpi

/-- The standard simplicial homotopy in `C`, inherited from Mathlib via `BarResolution`. -/
noncomputable def emHomotopy (alg : T.Algebra) :
    SimplicialObject.Homotopy
      ((emUnderlyingAugmented alg).hom ≫ (emExtra alg).section_)
      (𝟙 (emUnderlyingAugmented alg).left) :=
  (emExtra alg).homotopy

end UnderlyingContraction

end Monad
end CategoryTheory
