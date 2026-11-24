/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractible
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Contractible nerves and the standard simplicial point

The chosen categorical terminal object of `SSet` and the standard simplex
`Δ[0]` are canonically isomorphic.  This file transports realization weak
equivalences of maps to the chosen terminal object across that isomorphism,
then applies the transport to nerves with chosen or typeclass-provided initial
or terminal objects.

No converse, homotopy-fiber, or Quillen-Theorem-A statement is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MorphismProperty

open scoped Simplicial

universe u v

namespace SSet

/-- The chosen terminal simplicial set is canonically isomorphic to the
standard simplicial point. -/
noncomputable def terminalIsoStdSimplexZero :
    (⊤_ SSet.{u}) ≅ (Δ[0] : SSet.{u}) :=
  terminalIsTerminal.uniqueUpToIso stdSimplex.isTerminalObj₀

/-- The map to `Δ[0]` factors through the chosen terminal object and its
canonical comparison isomorphism. -/
@[reassoc]
theorem terminal_from_comp_terminalIsoStdSimplexZero (X : SSet.{u}) :
    terminal.from X ≫ terminalIsoStdSimplexZero.hom =
      stdSimplex.isTerminalObj₀.from X :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

/-- A realization weak equivalence to the chosen terminal simplicial set is
also one to the standard simplicial point. -/
theorem stdSimplex_zero_from_mem_realizationWeakEquivalences
    {X : SSet.{u}}
    (h : realizationWeakEquivalences (terminal.from X)) :
    realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from X) := by
  have hcomp := RespectsIso.postcomp realizationWeakEquivalences
    terminalIsoStdSimplexZero.hom (terminal.from X) h
  rw [terminal_from_comp_terminalIsoStdSimplexZero] at hcomp
  exact hcomp

end SSet

namespace NerveContractible

/-- The canonical map from the nerve of a category with a chosen initial
object to `Δ[0]` is a realization weak equivalence. -/
theorem nerve_to_point_mem_realizationWeakEquivalences_of_isInitial
    {C : Type u} [Category.{v} C] {X : C} (hX : IsInitial X) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (CategoryTheory.nerve C : SSet.{max u v})) :=
  SSet.stdSimplex_zero_from_mem_realizationWeakEquivalences
    (nerve_to_terminal_mem_realizationWeakEquivalences_of_isInitial hX)

/-- The canonical map from the nerve of a category with a chosen terminal
object to `Δ[0]` is a realization weak equivalence. -/
theorem nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal
    {C : Type u} [Category.{v} C] {X : C} (hX : IsTerminal X) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (CategoryTheory.nerve C : SSet.{max u v})) :=
  SSet.stdSimplex_zero_from_mem_realizationWeakEquivalences
    (nerve_to_terminal_mem_realizationWeakEquivalences_of_isTerminal hX)

/-- The canonical map from the nerve of a category with an initial object to
`Δ[0]` is a realization weak equivalence. -/
theorem nerve_to_point_mem_realizationWeakEquivalences_of_hasInitial
    {C : Type u} [Category.{v} C] [HasInitial C] :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (CategoryTheory.nerve C : SSet.{max u v})) :=
  nerve_to_point_mem_realizationWeakEquivalences_of_isInitial initialIsInitial

/-- The canonical map from the nerve of a category with a terminal object to
`Δ[0]` is a realization weak equivalence. -/
theorem nerve_to_point_mem_realizationWeakEquivalences_of_hasTerminal
    {C : Type u} [Category.{v} C] [HasTerminal C] :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (CategoryTheory.nerve C : SSet.{max u v})) :=
  nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal
    terminalIsTerminal

end NerveContractible

end
