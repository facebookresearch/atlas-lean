/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeSupportedSuffix
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeSupportOperators
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeOperatorRelations

/-!
# Actual range of original injected right-cube faces

The supported suffix preimage and genuine original prefix relation
construct an actual source cube class over every target cell whose
retained support lies in the injected front range. Both original
endpoint witnesses and whole path readbacks are retained. This proves
the exact face range rather than assuming a relative-latching outcome.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeSupportedFaces
open PathLastMaximum PathMaximumOperators RightCubeRelations RightCubeReduction RightCubeSupport
  RightCubeSupportedSuffix RightCubeSupportOperators
variable {n m : ℕ}

/-- The whole original supported suffix preimage, imaged and zero-adjoined, is exactly the target's actual
  reduced chain. -/
theorem image_prepend_normalize (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (LastPath.{u} (0 : Fin (m + 1)))).obj q)
    (i : Fin (n + 1)) (hi : θ.toOrderHom i = initialMaximum p)
    (hp : support p ⊆ Set.range θ.toOrderHom) :
    preimage θ hθ p i hi hp ⋙ imageFunctor θ i ⋙ prependFunctor (θ.toOrderHom i) = normalize p := by
  refine Functor.ext (fun k => ?_) ?_
  · apply SimplicialThickening.Path.ext
    change {ULift.up.{u} (0 : Fin (m + 2))} ∪
      (extension θ).toOrderHom.uliftMap '' ((preimage θ hθ p i hi hp).obj k).I =
        {ULift.up.{u} (0 : Fin (m + 2))} ∪
          (RightCubeIntervalCuts.suffix (initialMaximum p) (p.obj k) (initialMaximum_mem p k)).I
    exact congrArg (fun S => ({ULift.up.{u} (0 : Fin (m + 2))} ∪ S)) (image_I θ hθ p i hi hp k)
  · intro k l f
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The actual original injected cube face has the constructed supported source preimage with exact whole
  target class readback. -/
theorem map_preimage (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (LastPath.{u} (0 : Fin (m + 1)))).obj q)
    (i : Fin (n + 1)) (hi : θ.toOrderHom i = initialMaximum p)
    (hp : support p ⊆ Set.range θ.toOrderHom) :
    (RightCubeCosimplicialMaps.map θ).app q
      (_root_.Quotient.mk (setoid.{u} n q) (preimage θ hθ p i hi hp ⋙ prependFunctor i)) =
        _root_.Quotient.mk (setoid.{u} m q) p := by
  let r := preimage θ hθ p i hi hp
  have hr := RightCubeOperatorRelations.image_prepend_relation θ i r
  have he := image_prepend_normalize θ hθ p i hi hp
  have hNorm : (setoid.{u} m q).r (r ⋙ prependFunctor i ⋙ RightCubeOperator.functor θ) (normalize p) :=
    Eq.mp (congrArg (fun z => (setoid.{u} m q).r (r ⋙ prependFunctor i ⋙ RightCubeOperator.functor θ) z) he) hr
  exact _root_.Quotient.sound (Relation.EqvGen.trans _ _ _ hNorm
    (Relation.EqvGen.symm _ _ (related_normalize p)))

/-- An actual target cube cell belongs to an injected original face exactly when its same original retained
  support lies in that front range. -/
theorem map_range_iff_support (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    {q : SimplexCategoryᵒᵖ} (b : (RightCubeRelations.object.{u} m).obj q) :
    (∃ a : (RightCubeRelations.object.{u} n).obj q, (RightCubeCosimplicialMaps.map θ).app q a = b) ↔
      quotientSupport b ⊆ Set.range θ.toOrderHom := by
  constructor
  · rintro ⟨a, rfl⟩ j hj
    rw [quotientSupport_image] at hj
    obtain ⟨i, _, hi⟩ := hj
    exact ⟨i, hi⟩
  · intro hp
    induction b using _root_.Quotient.inductionOn with
    | _ p =>
      change support p ⊆ Set.range θ.toOrderHom at hp
      obtain ⟨i, hi⟩ := hp (initialMaximum_support p)
      exact ⟨_root_.Quotient.mk (setoid.{u} n q) (preimage θ hθ p i hi hp ⋙ prependFunctor i), map_preimage
        θ hθ p i hi hp⟩

/-- An actual original coface range is exactly omission of its supplied original front support label,
  including the zero coface. -/
theorem coface_range (j : Fin (n + 2)) {q : SimplexCategoryᵒᵖ}
    (b : (RightCubeRelations.object.{u} (n + 1)).obj q) :
    (∃ a : (RightCubeRelations.object.{u} n).obj q, (RightCubeCosimplicialMaps.map (SimplexCategory.δ j)).app q a = b) ↔
      j ∉ quotientSupport b := by
  have hRange : Set.range (SimplexCategory.δ j).toOrderHom = {j}ᶜ := by
    change Set.range (Fin.succAboveOrderEmb j) = {j}ᶜ
    exact Fin.range_succAboveOrderEmb j
  apply (map_range_iff_support (SimplexCategory.δ j) (Fin.succAboveOrderEmb j).injective b).trans
  rw [hRange]
  constructor
  · intro h hj
    exact h hj rfl
  · intro h k hk hkj
    exact h (hkj ▸ hk)

end CategoryTheory.CoherentRealization.RightCubeSupportedFaces
