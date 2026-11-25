/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Colimits of the original marked simplicial-set carriers

The underlying cocone is marked by the images of all original marked
edges and all original degenerate edges. Its ordinary universal map
preserves precisely those generators. This constructs the genuine marked
colimit whenever the underlying colimit exists, at the same shape bounds.
Forgetting preserves colimits through its actual maximal-marking adjunction.
-/

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.Marked

variable {J : Type w} [Category.{v} J] (F : J ⥤ Marked.{u})

/-- Mark the original cocone point by the image generators and its original degenerate edges. -/
def colimitCocone (c : Cocone (F ⋙ forget)) : Cocone F where
  pt :=
    { toSSet := c.pt
      marking := {a | (∃ x : c.pt _⦋0⦌, c.pt.σ 0 x = a) ∨
        ∃ (j : J) (b : (F.obj j).toSSet _⦋1⦌), b ∈ (F.obj j).marking ∧
          (c.ι.app j).app (op ⦋1⦌) b = a}
      degenerate_mem x := Or.inl ⟨x, rfl⟩ }
  ι :=
    { app j := ⟨c.ι.app j, fun ha => Or.inr ⟨j, _, ha, rfl⟩⟩
      naturality _ _ f := Hom.ext (c.ι.naturality f) }

/-- Every original inclusion is retained as the whole original simplicial map. -/
@[simp] theorem colimitCocone_ι_hom (c : Cocone (F ⋙ forget)) (j : J) :
    ((colimitCocone F c).ι.app j).hom = c.ι.app j := rfl

/-- The image-generated marking makes the actual underlying colimit a genuine marked colimit. -/
def colimitCoconeIsColimit {c : Cocone (F ⋙ forget)} (hc : IsColimit c) :
    IsColimit (colimitCocone F c) where
  desc s :=
    { hom := hc.desc (forget.mapCocone s)
      preserve {a} ha := by
        rcases ha with ⟨x, rfl⟩ | ⟨j, b, hb, rfl⟩
        · let l : c.pt ⟶ s.pt.toSSet := hc.desc (forget.mapCocone s)
          change l.app (op ⦋1⦌) (c.pt.σ 0 x) ∈ s.pt.marking
          exact (σ_naturality_apply l 0 x).symm ▸ s.pt.degenerate_mem (l.app _ x)
        · have he := congrArg (fun f => f.app (op ⦋1⦌) b) (hc.fac (forget.mapCocone s) j)
          change (hc.desc (forget.mapCocone s)).app _ ((c.ι.app j).app _ b) =
            (s.ι.app j).hom.app _ b at he
          exact he.symm ▸ (s.ι.app j).preserve hb }
  fac s j := Hom.ext (hc.fac (forget.mapCocone s) j)
  uniq s m hm := by
    apply Hom.ext
    apply hc.uniq (forget.mapCocone s) m.hom
    intro j
    exact congrArg Hom.hom (hm j)

/-- Underlying colimits give actual marked colimits at the same original shape universes. -/
instance hasColimit [HasColimit (F ⋙ forget)] : HasColimit F :=
  ⟨⟨{ cocone := colimitCocone F (colimit.cocone (F ⋙ forget)),
       isColimit := colimitCoconeIsColimit F (colimit.isColimit (F ⋙ forget)) }⟩⟩

/-- Forgetting the marking preserves colimits by the actual maximal-marking adjunction. -/
theorem forgetPreservesColimits : PreservesColimitsOfSize.{v, w} forget.{u} :=
  maximalAdjunction.leftAdjoint_preservesColimits

end SSet.Marked
