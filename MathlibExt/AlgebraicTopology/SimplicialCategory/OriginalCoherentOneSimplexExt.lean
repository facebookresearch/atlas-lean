/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomUnitsAndEmpty
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornHomFaces

/-!
# Whole original one-simplex maps retain both objects and full forward Hom

The two actual original vertices and complete original forward Hom
determine a whole enriched functor from the original coherent
one-simplex. Diagonal maps are forced by its genuine singleton
identity Homs, and reverse Homs are genuinely empty.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OneSimplexMaps
open SimplicialEnrichment

/-- The same individual original first vertex of the coherent one-simplex. -/
abbrev first : coherentSimplex.{u} ⦋1⦌ := .mk (ULift.up 0)

/-- The same individual original last vertex of the coherent one-simplex. -/
abbrev last : coherentSimplex.{u} ⦋1⦌ := .mk (ULift.up (Fin.last 1))

private theorem identity_transport {C : Carrier.{u}} (x y : C) (h : x = y) :
    eId SSet.{u} x ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) h h) = eId SSet.{u} y := by
  cases h
  exact Category.comp_id _

private theorem diagonal_eq {A C : Carrier.{u}} (F G : A ⟶ C) (a : A)
    [IsIso (eId SSet.{u} a)] (h : F.obj a = G.obj a) :
    F.map a a ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) h h) = G.map a a := by
  apply (cancel_epi (eId SSet.{u} a)).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) h h))
      (F.map_id a)).trans ((identity_transport _ _ h).trans (G.map_id a).symm))

/-- Both original vertex images and the whole original forward Hom determine the SAME complete one-simplex functor. -/
theorem ext {C : Carrier.{u}} (F G : coherentSimplex.{u} ⦋1⦌ ⟶ C)
    (h₀ : F.obj first = G.obj first) (h₁ : F.obj last = G.obj last)
    (hm : F.map first last ≫
      eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) h₀ h₁) = G.map first last) : F = G := by
  have hObj (a : coherentSimplex.{u} ⦋1⦌) : F.obj a = G.obj a := by
    rcases a with ⟨⟨a⟩⟩
    fin_cases a
    · exact h₀
    · exact h₁
  apply EnrichedFunctor.ext SSet.{u} (F := F) (G := G) hObj
  intro a b
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  fin_cases a <;> fin_cases b
  · let _ : IsIso (eId SSet.{u} first) :=
      HomUnitsAndEmpty.unit_isIso (ULift.up.{u} (0 : Fin 2))
    exact diagonal_eq F G first h₀
  · exact hm
  · exact HomUnitsAndEmpty.empty_hom_ext
      (show ¬(ULift.up.{u} (Fin.last 1) : ULift.{u} (Fin 2)) ≤ ULift.up 0 from by decide) _ _
  · let _ : IsIso (eId SSet.{u} last) :=
      HomUnitsAndEmpty.unit_isIso (ULift.up.{u} (Fin.last 1))
    exact diagonal_eq F G last h₁

end CategoryTheory.CoherentRealization.OneSimplexMaps
