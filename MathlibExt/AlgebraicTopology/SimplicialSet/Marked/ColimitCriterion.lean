/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Colimits

/-!
# Underlying colimits with the actual marked-edge coverage

An original marked cocone is a colimit when its underlying cocone is and
every marked edge of its actual point comes from a marked stage edge.
Its universal marked map is the same underlying universal map. Diagram,
Hom and value universes keep their original independent bounds.
-/

noncomputable section
universe u v w
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Actual underlying colimits and original marked-edge image coverage give the full marked universal property. -/
def isColimitOfUnderlyingMarking {J : Type w} [Category.{v} J]
    {F : J ⥤ Marked.{u}} {c : Cocone F}
    (hc : IsColimit (forget.mapCocone c))
    (hm : ∀ e : c.pt.toSSet _⦋1⦌, e ∈ c.pt.marking →
      ∃ (j : J) (b : (F.obj j).toSSet _⦋1⦌),
        b ∈ (F.obj j).marking ∧ (c.ι.app j).hom.app (op ⦋1⦌) b = e) : IsColimit c where
  desc s :=
    { hom := hc.desc (forget.mapCocone s)
      preserve {e} he := by
        obtain ⟨j, b, hb, hbe⟩ := hm e he
        let l := hc.desc (forget.mapCocone s)
        have h : l.app (op ⦋1⦌) e = (s.ι.app j).hom.app (op ⦋1⦌) b :=
          (congrArg (l.app (op ⦋1⦌)) hbe).symm.trans
            (ConcreteCategory.congr_hom (congr_app (hc.fac (forget.mapCocone s) j) (op ⦋1⦌)) b)
        exact h.symm ▸ (s.ι.app j).preserve hb }
  fac s j := Hom.ext (hc.fac (forget.mapCocone s) j)
  uniq s m hm := by
    apply Hom.ext
    exact hc.uniq (forget.mapCocone s) m.hom (fun j => congrArg Hom.hom (hm j))

end SSet.Marked
