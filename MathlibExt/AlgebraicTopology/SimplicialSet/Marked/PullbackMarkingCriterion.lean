/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Interval

/-!
# Markings of categorical pullbacks

An edge of a marked pullback is marked exactly when both its projections
are marked. The maximally marked interval represents these two markings,
and its universal lift recovers the original pullback edge.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The actual original marked pullback retains exactly the intersection of its SAME two original projection
markings. -/
theorem pullback_marking_iff {X Y Z : Marked.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (e : (pullback f g).toSSet _⦋1⦌) :
    e ∈ (pullback f g).marking ↔
      (pullback.fst f g).hom.app (op ⦋1⦌) e ∈ X.marking ∧
      (pullback.snd f g).hom.app (op ⦋1⦌) e ∈ Y.marking := by
  constructor
  · intro he
    exact ⟨(pullback.fst f g).preserve he, (pullback.snd f g).preserve he⟩
  · rintro ⟨hx, hy⟩
    let a : min (Δ[1] : SSet.{u}) ⟶ pullback f g := ofMin (yonedaEquiv.symm e)
    let x := intervalMapOfMarkedEdge ((pullback.fst f g).hom.app (op ⦋1⦌) e) hx
    let y := intervalMapOfMarkedEdge ((pullback.snd f g).hom.app (op ⦋1⦌) e) hy
    have hw : x ≫ f = y ≫ g := by
      apply Hom.ext
      change yonedaEquiv.symm ((pullback.fst f g).hom.app (op ⦋1⦌) e) ≫ f.hom =
        yonedaEquiv.symm ((pullback.snd f g).hom.app (op ⦋1⦌) e) ≫ g.hom
      apply yonedaEquiv.injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact congrArg (fun h => h.hom.app (op ⦋1⦌) e) (pullback.condition (f := f) (g := g))
    let l := pullback.lift x y hw
    let i : min (Δ[1] : SSet.{u}) ⟶ max (Δ[1] : SSet.{u}) := ofMin (𝟙 _)
    have hl : i ≫ l = a := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst]
        apply Hom.ext
        apply yonedaEquiv.injective
        change yonedaEquiv (𝟙 (Δ[1] : SSet.{u}) ≫
          yonedaEquiv.symm ((pullback.fst f g).hom.app (op ⦋1⦌) e)) =
            yonedaEquiv (yonedaEquiv.symm e ≫ (pullback.fst f g).hom)
        simp only [Category.id_comp, yonedaEquiv_comp, Equiv.apply_symm_apply]
      · rw [Category.assoc, pullback.lift_snd]
        apply Hom.ext
        apply yonedaEquiv.injective
        change yonedaEquiv (𝟙 (Δ[1] : SSet.{u}) ≫
          yonedaEquiv.symm ((pullback.snd f g).hom.app (op ⦋1⦌) e)) =
            yonedaEquiv (yonedaEquiv.symm e ≫ (pullback.snd f g).hom)
        simp only [Category.id_comp, yonedaEquiv_comp, Equiv.apply_symm_apply]
    have h : l.hom = yonedaEquiv.symm e :=
      (Category.id_comp l.hom).symm.trans (congrArg Hom.hom hl)
    have he : yonedaEquiv l.hom ∈ (pullback f g).marking := l.preserve (Set.mem_univ _)
    rwa [h, Equiv.apply_symm_apply] at he

end SSet.Marked
