/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Original marked edges in small colimits

Every marked edge of an actual small colimit comes from a marked edge
at an original stage. The universal map to the image-generated colimit
has the original identity as its underlying map. Degenerate edges also
come from stages, using evaluation at the original vertices. The statement
keeps every original stage map and imposes no fibrancy or base hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Marked edges of an actual small colimit are exactly images of original marked stage edges. -/
theorem mem_marking_of_isColimit_iff {J : Type u} [SmallCategory J]
    {F : J ⥤ Marked.{u}} {c : Cocone F} (hc : IsColimit c) (e : c.pt.toSSet _⦋1⦌) :
    e ∈ c.pt.marking ↔ ∃ (j : J) (b : (F.obj j).toSSet _⦋1⦌),
      b ∈ (F.obj j).marking ∧ (c.ι.app j).hom.app (op ⦋1⦌) b = e := by
  constructor
  · intro he
    let _ : PreservesColimitsOfSize.{u, u} forget.{u} := forgetPreservesColimits
    let cU := forget.mapCocone c
    have hcU : IsColimit cU := isColimitOfPreserves forget hc
    let c' := colimitCocone F cU
    let d : c.pt ⟶ c'.pt := hc.desc c'
    have hd : d.hom = 𝟙 c.pt.toSSet := by
      apply hcU.hom_ext
      intro j
      have h := congrArg Hom.hom (hc.fac c' j)
      exact h.trans (Category.comp_id _).symm
    have hm : e ∈ c'.pt.marking := by
      have h : d.hom.app (op ⦋1⦌) e = e := by rw [hd]; rfl
      exact h ▸ d.preserve he
    change (∃ x : c.pt.toSSet _⦋0⦌, c.pt.toSSet.σ 0 x = e) ∨
      (∃ (j : J) (b : (F.obj j).toSSet _⦋1⦌), b ∈ (F.obj j).marking ∧
        (c.ι.app j).hom.app (op ⦋1⦌) b = e) at hm
    rcases hm with ⟨x, hx⟩ | hm
    · let ev := (evaluation (SimplexCategoryᵒᵖ) (Type u)).obj (op ⦋0⦌)
      have hc₀ := isColimitOfPreserves ev hcU
      obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc₀ x
      refine ⟨j, (F.obj j).toSSet.σ 0 y, (F.obj j).degenerate_mem y, ?_⟩
      exact (σ_naturality_apply (c.ι.app j).hom 0 y).trans
        ((congrArg (c.pt.toSSet.σ (0 : Fin 1)) hy).trans hx)
    · exact hm
  · rintro ⟨j, b, hb, h⟩
    exact h ▸ (c.ι.app j).preserve hb

end SSet.Marked
