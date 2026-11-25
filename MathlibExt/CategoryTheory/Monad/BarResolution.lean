/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.BarRegularContraction
public import MathlibExt.CategoryTheory.Monad.BarAlgebra

/-!
# Monad bar resolution

For a monad `T` on `C` and a `T`-algebra `alg`, the resolution is the algebra-valued
bar at the regular right module, augmented over `alg.A` by evaluating the regular
balanced pairing (`BarRegularContraction.regularBalancedPairing`) at the discrete
point, with augmentation component `alg.a`. The genuine extra degeneracy
(`BarRegularContraction.extraDegeneracySimplicial`) is transported along evaluation,
giving split-epi and homotopy consequences in `C`. Algebra morphisms induce
resolution maps with identity and composition laws. These maps package into
`resolutionAugmentedFunctor` with its object and map computation lemmas. No simplicial identity is
reproved and no Eilenberg--Moore, derived, or operadic claim is made.

Mathematical source: J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.
This file is the regular-right-module case `B(T,T,A)` of the algebra-valued
bar, augmented over `alg.A` by the algebra structure map; the left extra
degeneracy is the specialization of the general regular-right contraction.
Degree and face/degeneracy conventions are inherited from `Bar`.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {T : Monad C}

/--
Evaluation at the discrete point: applying a `Discrete PUnit`-indexed diagram
to its unique object. Shared by the augmentation, the naturality maps, and the
contraction transport.
-/
def resolutionEvalPoint : (Discrete PUnit.{1} ⥤ C) ⥤ C :=
  (evaluation (Discrete PUnit.{1}) C).obj (Discrete.mk PUnit.unit)
/-- The monad bar resolution: the algebra-valued bar at the regular right module. -/
noncomputable def resolutionBar (alg : T.Algebra) : SimplicialObject C :=
  algebraBar (RightModule.regular T) alg
/-- Degree `n` is `T`-valued at `Tⁿ(alg.A)`, inherited from `algebraBar`. -/
@[simp]
theorem resolutionBar_obj (alg : T.Algebra) (n : ℕ) :
  (resolutionBar alg).obj (Opposite.op (SimplexCategory.mk n)) =
    (RightModule.regular T).functor.obj ((monadPow T n).obj alg.A) :=
  algebraBar_obj _ _ _
/-- Faces are inherited from `algebraBar`. -/
@[simp]
theorem resolutionBar_map_δ_op (alg : T.Algebra) {n : ℕ} (i : Fin (n + 2)) :
  (resolutionBar alg).map (SimplexCategory.δ i).op =
    barFaceApp (T := T) (R := RightModule.regular T) (L := algebraLeftModule alg) n i
      ⟨PUnit.unit⟩ :=
  algebraBar_map_δ_op _ _ _
/-- Degeneracies are inherited from `algebraBar`. -/
@[simp]
theorem resolutionBar_map_σ_op (alg : T.Algebra) {n : ℕ} (i : Fin (n + 1)) :
  (resolutionBar alg).map (SimplexCategory.σ i).op =
    (RightModule.regular T).functor.map (barEtaAtPos T n i alg.A) :=
  algebraBar_map_σ_op _ _ _
/-- The augmented resolution over `C`, evaluated at the discrete point. -/
noncomputable def resolutionAugmented (alg : T.Algebra) :
  SimplicialObject.Augmented C :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).obj
    (BalancedPairing.toSimplicialAugmented
      (BarRegularContraction.regularBalancedPairing (algebraLeftModule alg)))
/-- The augmentation target is the algebra carrier. -/
@[simp]
theorem resolutionAugmented_point (alg : T.Algebra) :
  (resolutionAugmented alg).right = alg.A :=
  rfl
/--
The underlying simplicial object of the augmented resolution is the bar
resolution. This is definitional: whiskering the transported augmentation at
the discrete point forgets to `algebraBar` at the regular right module.
-/
@[simp]
theorem resolutionAugmented_left (alg : T.Algebra) :
    (resolutionAugmented alg).left = resolutionBar alg :=
  rfl
/-- The degree-zero augmentation component is the algebra structure map. -/
@[simp]
theorem resolutionAugmented_hom_zero (alg : T.Algebra) :
  (resolutionAugmented alg).hom.app (Opposite.op (SimplexCategory.mk 0)) = alg.a := by
  unfold resolutionAugmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    BalancedPairing.toSimplicialAugmented_hom_app_mk, BalancedPairing.toDataHom_app_zero,
    BarRegularContraction.regularBalancedPairing_pairing]
  change (BarRegularContraction.regularPairing (algebraLeftModule alg)).app
    (Discrete.mk PUnit.unit) = alg.a
  rw [BarRegularContraction.regularPairing_app]
  exact algebraLeftModule_action_app _ _
/-- Naturality: an algebra morphism induces a map of augmented resolutions. -/
noncomputable def resolutionHom {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
  resolutionAugmented alg ⟶ resolutionAugmented alg' :=
  (SimplicialObject.Augmented.whiskeringObj _ _ resolutionEvalPoint).map
    (BalancedPairing.toSimplicialAugmentedMap
      (BarRegularContraction.regularBalancedPairing (algebraLeftModule alg))
      (BarRegularContraction.regularBalancedPairing (algebraLeftModule alg'))
      (𝟙 (RightModule.regular T)) (algebraLeftModuleHom φ)
      ((Functor.const (Discrete PUnit.{1})).map φ.f)
      (by
        ext X
        simp only [NatTrans.comp_app, barMap_app, algebraLeftModuleHom_f_app,
          RightModule.regular_functor, Algebra.id_f, NatTrans.id_app, Category.comp_id,
          BarRegularContraction.regularBalancedPairing_pairing_app,
          algebraLeftModule_action_app]
        exact φ.h))
/-- Identity algebra morphisms induce identity resolution maps. -/
theorem resolutionHom_id (alg : T.Algebra) :
    resolutionHom (𝟙 alg) = 𝟙 (resolutionAugmented alg) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have e1 : (resolutionHom (𝟙 alg)).left =
        Functor.whiskerRight (twoSidedBarHom (𝟙 (RightModule.regular T))
          (𝟙 (algebraLeftModule alg))) resolutionEvalPoint := by
      simp only [resolutionHom, SimplicialObject.Augmented.whiskeringObj_map_left,
        algebraLeftModuleHom_id]
      rfl
    have e2 : Functor.whiskerRight (twoSidedBarHom (𝟙 (RightModule.regular T))
        (𝟙 (algebraLeftModule alg))) resolutionEvalPoint =
        𝟙 (twoSidedBar T (RightModule.regular T) (algebraLeftModule alg) ⋙
          resolutionEvalPoint) := by
      rw [twoSidedBarHom_id, Functor.whiskerRight_id']
    have e3 : (𝟙 (twoSidedBar T (RightModule.regular T) (algebraLeftModule alg) ⋙
        resolutionEvalPoint)) = 𝟙 (resolutionAugmented alg).left :=
      rfl
    exact e1.trans (e2.trans e3)
  · have e1r : (resolutionHom (𝟙 alg)).right =
        resolutionEvalPoint.map
          ((Functor.const (Discrete PUnit.{1})).map (𝟙 alg : alg ⟶ alg).f) := by
      simp only [resolutionHom, SimplicialObject.Augmented.whiskeringObj_map_right]
      rfl
    have e2r : resolutionEvalPoint.map
          ((Functor.const (Discrete PUnit.{1})).map (𝟙 alg : alg ⟶ alg).f) =
        𝟙 (resolutionEvalPoint.obj (BarRegularContraction.regularBalancedPairing
          (algebraLeftModule alg)).target) := by
      rw [Algebra.id_f, Functor.map_id, Functor.map_id]
      rfl
    have e3r : (𝟙 (resolutionEvalPoint.obj (BarRegularContraction.regularBalancedPairing
        (algebraLeftModule alg)).target)) = 𝟙 (resolutionAugmented alg).right :=
      rfl
    exact e1r.trans (e2r.trans e3r)
/-- Composition of algebra morphisms induces composition of resolution maps. -/
theorem resolutionHom_comp {alg₁ alg₂ alg₃ : T.Algebra} (φ : alg₁ ⟶ alg₂)
  (ψ : alg₂ ⟶ alg₃) :
  resolutionHom φ ≫ resolutionHom ψ = resolutionHom (φ ≫ ψ) := by
  refine SimplicialObject.Augmented.hom_ext _ _ ?_ ?_
  · have f1 : (resolutionHom φ ≫ resolutionHom ψ).left =
        Functor.whiskerRight (twoSidedBarHom (𝟙 (RightModule.regular T))
          (algebraLeftModuleHom φ)) resolutionEvalPoint ≫ Functor.whiskerRight
          (twoSidedBarHom (𝟙 (RightModule.regular T)) (algebraLeftModuleHom ψ))
          resolutionEvalPoint := by
      rw [Comma.comp_left]
      simp only [resolutionHom, SimplicialObject.Augmented.whiskeringObj_map_left]
      rfl
    have f2 : Functor.whiskerRight (twoSidedBarHom (𝟙 (RightModule.regular T))
        (algebraLeftModuleHom φ)) resolutionEvalPoint ≫ Functor.whiskerRight
        (twoSidedBarHom (𝟙 (RightModule.regular T)) (algebraLeftModuleHom ψ))
        resolutionEvalPoint =
        Functor.whiskerRight (twoSidedBarHom (𝟙 (RightModule.regular T))
          (algebraLeftModuleHom (φ ≫ ψ))) resolutionEvalPoint := by
      rw [← Functor.whiskerRight_comp, twoSidedBarHom_comp, Category.id_comp,
        algebraLeftModuleHom_comp]
    have f3 : Functor.whiskerRight (twoSidedBarHom (𝟙 (RightModule.regular T))
        (algebraLeftModuleHom (φ ≫ ψ))) resolutionEvalPoint =
        (resolutionHom (φ ≫ ψ)).left := by
      simp only [resolutionHom, SimplicialObject.Augmented.whiskeringObj_map_left]
      rfl
    exact f1.trans (f2.trans f3)
  · have g1 : (resolutionHom φ ≫ resolutionHom ψ).right =
        resolutionEvalPoint.map ((Functor.const (Discrete PUnit.{1})).map φ.f) ≫
          resolutionEvalPoint.map ((Functor.const (Discrete PUnit.{1})).map ψ.f) := by
      rw [Comma.comp_right]
      simp only [resolutionHom, SimplicialObject.Augmented.whiskeringObj_map_right]
      rfl
    have g2 : resolutionEvalPoint.map ((Functor.const (Discrete PUnit.{1})).map φ.f) ≫
        resolutionEvalPoint.map ((Functor.const (Discrete PUnit.{1})).map ψ.f) =
        resolutionEvalPoint.map ((Functor.const (Discrete PUnit.{1})).map (φ ≫ ψ).f) := by
      rw [← Functor.map_comp, ← Functor.map_comp, Algebra.comp_f]
    have g3 : resolutionEvalPoint.map ((Functor.const (Discrete PUnit.{1})).map (φ ≫ ψ).f) =
        (resolutionHom (φ ≫ ψ)).right := by
      simp only [resolutionHom, SimplicialObject.Augmented.whiskeringObj_map_right]
      rfl
    exact g1.trans (g2.trans g3)
/-- Bundled resolution augmented functor. -/
noncomputable def resolutionAugmentedFunctor :
    T.Algebra ⥤ SimplicialObject.Augmented C where
  obj alg := resolutionAugmented alg
  map φ := resolutionHom φ
  map_id alg := resolutionHom_id alg
  map_comp φ ψ := (resolutionHom_comp φ ψ).symm

/-- Object computation: bundling recovers `resolutionAugmented`, by `rfl`. -/
@[simp]
theorem resolutionAugmentedFunctor_obj (alg : T.Algebra) :
    resolutionAugmentedFunctor.obj alg = resolutionAugmented alg :=
  rfl

/-- Map computation: bundling recovers `resolutionHom`, by `rfl`. -/
@[simp]
theorem resolutionAugmentedFunctor_map {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    resolutionAugmentedFunctor.map φ = resolutionHom φ :=
  rfl

/--
The simplicial component of a resolution map is the algebra-bar map at the
identity right-module morphism. This is the form needed to compare
Eilenberg--Moore bars with the underlying resolution.
-/
theorem resolutionHom_left {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (resolutionHom φ).left = algebraBarHom (𝟙 (RightModule.regular T)) φ := by
  simp only [resolutionHom, SimplicialObject.Augmented.whiskeringObj_map_left]
  rfl
/--
The target component of a resolution map is the algebra morphism itself:
evaluating the pointwise target map at the discrete point gives `φ.f`. This is
the form needed for the Eilenberg--Moore comparison.
-/
theorem resolutionHom_right {alg alg' : T.Algebra} (φ : alg ⟶ alg') :
    (resolutionHom φ).right = φ.f := by
  simp only [resolutionHom, SimplicialObject.Augmented.whiskeringObj_map_right]
  rfl
/-- The contracted extra degeneracy in `C`, transported along evaluation. -/
noncomputable def resolutionExtra (alg : T.Algebra) :
  SimplicialObject.Augmented.ExtraDegeneracy (resolutionAugmented alg) :=
  (BarRegularContraction.extraDegeneracySimplicial (algebraLeftModule alg)).map resolutionEvalPoint
/-- The section is the monad unit at the algebra carrier. -/
@[simp]
theorem resolutionExtra_s' (alg : T.Algebra) :
  (resolutionExtra alg).s' = T.η.app alg.A :=
  rfl
/-- The extra degeneracy evaluates `BarRegularContraction.s` at the discrete point. -/
@[simp]
theorem resolutionExtra_s (alg : T.Algebra) (n : ℕ) :
  (resolutionExtra alg).s n =
    (BarRegularContraction.s (algebraLeftModule alg) n).app (Discrete.mk PUnit.unit) :=
  rfl
/-- The augmentation is split epi in `C`. -/
noncomputable def resolutionSplitEpi (alg : T.Algebra) :
  SplitEpi (resolutionAugmented alg).hom :=
  (resolutionExtra alg).splitEpi
/-- The standard simplicial homotopy in `C`, inherited from Mathlib. -/
noncomputable def resolutionHomotopy (alg : T.Algebra) :
  SimplicialObject.Homotopy ((resolutionAugmented alg).hom ≫ (resolutionExtra alg).section_)
    (𝟙 (resolutionAugmented alg).left) :=
  (resolutionExtra alg).homotopy
end Monad
end CategoryTheory
