/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint

/-!
# Weak equivalences between standard simplices

The finite-ordinal nerve contraction makes every standard-simplex point map
a realization weak equivalence. The terminal point factorization then gives
weakness for every simplicial map between standard simplices.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

public section

namespace SSet

/-- The point projection is weak using the existing finite-ordinal nerve. -/
theorem stdSimplex_to_point_mem_realizationWeakEquivalences (A : SimplexCategory) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj A : SSet.{u})) := by
  obtain ⟨n⟩ := A
  let C : Type u := ULift.{u} (Fin (n + 1))
  let z : C := ULift.up (Fin.last n)
  have hz : IsTerminal z :=
    IsTerminal.ofUniqueHom
      (fun a : C => homOfLE (show a.down ≤ Fin.last n from Fin.le_last a.down))
      (fun _ _ => Subsingleton.elim _ _)
  have hn : SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (CategoryTheory.nerve C : SSet.{u})) :=
    NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal hz
  let e : (Δ[n] : SSet.{u}) ≅ CategoryTheory.nerve C :=
    SSet.stdSimplex.isoNerve.{u} n
  have hcomp : e.hom ≫ SSet.stdSimplex.isTerminalObj₀.from (CategoryTheory.nerve C) =
      SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hpre := MorphismProperty.RespectsIso.precomp
    SSet.realizationWeakEquivalences e.hom
      (SSet.stdSimplex.isTerminalObj₀.from (CategoryTheory.nerve C)) hn
  exact hcomp ▸ hpre

/-- Every standard-simplex map is weak, without a desired weak-map input. -/
theorem stdSimplex_map_mem_realizationWeakEquivalences {A B : SimplexCategory}
    (a : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ SSet.stdSimplex.obj B) :
    SSet.realizationWeakEquivalences a := by
  let qm := SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj A)
  let qn := SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj B)
  have hfac : a ≫ qn = qm := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hcomp : SSet.realizationWeakEquivalences (a ≫ qn) :=
    hfac.symm ▸ stdSimplex_to_point_mem_realizationWeakEquivalences A
  exact SSet.realizationWeakEquivalences.of_postcomp a qn
    (stdSimplex_to_point_mem_realizationWeakEquivalences B) hcomp

end SSet
