/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint

/-!
# Public-client tests for contractible nerves and the simplicial point

These tests pin the canonical comparison between the chosen terminal
simplicial set and `Δ[0]`, the generic transport of realization weak
equivalences across that comparison, and the initial/terminal-object nerve
corollaries.  No Quillen-Theorem-A or homotopy-fiber conclusion is asserted.
-/

namespace NerveContractiblePointTests

open CategoryTheory CategoryTheory.Limits MorphismProperty

open scoped Simplicial

noncomputable section

universe u v

example : (⊤_ SSet.{u}) ≅ (Δ[0] : SSet.{u}) :=
  SSet.terminalIsoStdSimplexZero

example (X : SSet.{u}) :
    terminal.from X ≫ SSet.terminalIsoStdSimplexZero.hom =
      SSet.stdSimplex.isTerminalObj₀.from X :=
  SSet.terminal_from_comp_terminalIsoStdSimplexZero X

example {X : SSet.{u}}
    (h : SSet.realizationWeakEquivalences (terminal.from X)) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from X) :=
  SSet.stdSimplex_zero_from_mem_realizationWeakEquivalences h

variable {C : Type u} [Category.{v} C]

example {X : C} (hX : IsInitial X) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (CategoryTheory.nerve C : SSet.{max u v})) :=
  NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isInitial hX

example {X : C} (hX : IsTerminal X) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (CategoryTheory.nerve C : SSet.{max u v})) :=
  NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_isTerminal hX

example [HasInitial C] :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (CategoryTheory.nerve C : SSet.{max u v})) :=
  NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_hasInitial

example [HasTerminal C] :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from
        (CategoryTheory.nerve C : SSet.{max u v})) :=
  NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_hasTerminal

end

end NerveContractiblePointTests
