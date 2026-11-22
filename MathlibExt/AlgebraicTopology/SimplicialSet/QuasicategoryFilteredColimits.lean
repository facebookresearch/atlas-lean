/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Limits.Filtered

/-!
# Filtered colimits of quasicategories

Classical fact: a finite simplicial set is finitely presentable in `SSet`,
so a map from a finite simplicial set into a filtered colimit factors through
some stage, and equalities of such maps are coequalized at a later stage.
Via the inner-horn-filling criterion `SSet.Quasicategory.hornFilling'` this
implies that a filtered colimit of quasicategories is again a quasicategory.

Standard source: Goerss–Jardine, *Simplicial Homotopy Theory*, VII Lemma 3.5.
The formal fact used here is `SSet.Finite → IsFinitelyPresentable` from
`Mathlib.AlgebraicTopology.SimplicialSet.Presentable`, so filtered colimits
commute with the finite lifting data `Λ[n,i] ⟶ –` and `Δ[n] ⟶ –`.

This file exposes only the reusable quasicategory-colimit closure; no other
homotopical structure is claimed here. It is the inner-horn analogue of the
Kan-complex closure in
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexFilteredColimits`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial

namespace SSet

namespace Quasicategory

variable {J : Type u} [Category.{u} J] [IsFiltered J]

/-- **Filtered colimits of quasicategories are quasicategories**
(same universe). An inner horn in the colimit factors through some
stage because the horn is a finite simplicial set, hence finitely
presentable (`IsFinitelyPresentable.exists_hom_of_isColimit`);
fill it there and map the filler to the colimit. -/
theorem ofIsFilteredColimit {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, Quasicategory (F.obj j)) : Quasicategory c.pt where
  hornFilling' := by
    intro n i σ₀ h0 hn
    obtain ⟨j, σ₀', hσ₀'⟩ :=
      IsFinitelyPresentable.exists_hom_of_isColimit
        (X := (Λ[n + 2, i] : SSet.{u})) hc σ₀
    have : Quasicategory (F.obj j) := hF j
    obtain ⟨σ, hσ⟩ := SSet.Quasicategory.hornFilling' σ₀' h0 hn
    exact ⟨σ ≫ c.ι.app j, by rw [← hσ₀', hσ, Category.assoc]⟩

end Quasicategory

end SSet
