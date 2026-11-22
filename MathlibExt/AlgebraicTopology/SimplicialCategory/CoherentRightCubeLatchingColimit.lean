/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeLatchingCompatibility
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeBoundaryLinearGlue

/-!
# Genuine original right-cube latching boundary colimit

Every actual proper-injection section family descends uniquely to the
constructed proper-support boundary. Its intersection agreements follow
from the same original pair-index maps. Degree zero is literally empty.
This proves the whole boundary cocone is a colimit without a latching
or coherence outcome hypothesis.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeLatchingColimit
open RightCubeSupportBoundary RightCubeFaceRangeIso RightCubeLatchingDiagram

/-- Every whole original proper-injection section family descends uniquely to the actual right-cube support boundary. -/
theorem sections (n : ℕ) (T : SSet.{u})
    (s : ∀ a : SimplicialObject.matchingIndex n, RightCubeRelations.object.{u} a.obj.right.unop.len ⟶ T)
    (hs : ∀ {a b : SimplicialObject.matchingIndex n} (g : a ⟶ b), RightCubeCosimplicialMaps.map
      g.hom.right.unop ≫ s a = s b) :
    ∃! f : (boundary.{u} n : SSet.{u}) ⟶ T, ∀ a, inclusion a ≫ f = s a := by
  cases n with
  | zero =>
    have h0 : IsInitial (boundary.{u} 0 : SSet.{u}) := by
      simpa only [boundary_zero] using (SSet.Subcomplex.isInitialBot (X := RightCubeRelations.object.{u} 0))
    refine ⟨h0.to T, ?_, ?_⟩
    · intro a
      exact False.elim (ProperFaceIndex.zero_elim a)
    · intro f _
      exact h0.hom_ext _ _
  | succ t =>
    let k := RightCubeLatchingCompatibility.family s
    let hk := RightCubeLatchingCompatibility.ordered s hs
    let f := RightCubeBoundaryLinearGlue.glue (t + 1) T k hk
    have facFace (i : Fin (t + 2)) : inclusion (ProperFaceIndex.face t i) ≫ f = s (ProperFaceIndex.face t i) :=
      (congrArg (fun h => h ≫ f) (inclusion_face t i)).trans
        ((Category.assoc (cofaceIso i).hom (SSet.Subcomplex.homOfLE (missing_le_boundary (t + 1) i)) f).trans
          ((congrArg (fun h => (cofaceIso i).hom ≫ h)
            (RightCubeBoundaryLinearGlue.inclusion_glue (t + 1) T k hk i)).trans
              ((cofaceIso i).hom_inv_id_assoc (s (ProperFaceIndex.face t i)))))
    have fac (a : SimplicialObject.matchingIndex (t + 1)) : inclusion a ≫ f = s a := by
      obtain ⟨i, θ, hθ⟩ := ProperFaceIndex.factor_face a
      let g : ProperFaceIndex.face t i ⟶ a := ProperFaceIndex.hom _ _ θ hθ.symm
      exact (congrArg (fun h => h ≫ f) (inclusion_naturality g)).symm.trans
        ((Category.assoc (RightCubeCosimplicialMaps.map θ) (inclusion (ProperFaceIndex.face t i)) f).trans
          ((congrArg (fun h => RightCubeCosimplicialMaps.map θ ≫ h) (facFace i)).trans (hs g)))
    refine ⟨f, fac, ?_⟩
    intro g hg
    apply RightCubeBoundaryGlue.hom_ext (t + 1)
    intro i
    apply (cancel_epi (cofaceIso.{u} i).hom).1
    exact (Category.assoc (cofaceIso i).hom (SSet.Subcomplex.homOfLE (missing_le_boundary (t + 1) i)) g).symm.trans
      ((congrArg (fun h => h ≫ g) (inclusion_face t i).symm).trans
        ((hg (ProperFaceIndex.face t i)).trans
          ((facFace i).symm.trans
            ((congrArg (fun h => h ≫ f) (inclusion_face t i)).trans
              (Category.assoc (cofaceIso i).hom (SSet.Subcomplex.homOfLE (missing_le_boundary (t + 1) i)) f)))))

/-- The actual whole original proper-injection boundary cocone is a genuine colimit, retaining all original
  scalar faces. -/
def isColimit (n : ℕ) : IsColimit (RightCubeLatchingDiagram.cocone.{u} n) := by
  let data (c : Cocone (RightCubeLatchingDiagram.diagram.{u} n)) :=
    sections n c.pt (fun a => c.ι.app (op a)) (fun {a b} g => by
      have h := c.w g.op
      change RightCubeCosimplicialMaps.map g.hom.right.unop ≫ c.ι.app (op a) = c.ι.app (op b) at h
      exact h)
  refine {
    desc := fun c => Classical.choose (data c)
    fac := ?_
    uniq := ?_ }
  · intro c a
    exact (Classical.choose_spec (data c)).1 a.unop
  · intro c f hf
    exact (Classical.choose_spec (data c)).2 f (fun a => hf (op a))

end CategoryTheory.CoherentRealization.RightCubeLatchingColimit
