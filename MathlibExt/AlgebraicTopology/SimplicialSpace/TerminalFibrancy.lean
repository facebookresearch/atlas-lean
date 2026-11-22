/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.AuxiliaryGeneratorProperties
import MathlibExt.AlgebraicTopology.SimplicialSpace.TerminalLocality
import MathlibExt.AlgebraicTopology.SimplicialSpace.CSSTerminalLifting

/-!
# The full monic-weak terminal lifting criterion

Complete Segal locality is equivalent to terminal lifting against all original
monic Rezk weak maps. Restriction to the actual auxiliary generators gives
the forward implication; strict CSS terminal lifting gives the reverse.
-/

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace SimplicialSpace

/-- The full monic all-CSS-weak terminal lifting class detects actual CSS objects. -/
theorem monomorphisms_inf_rezkWeakEquivalences_terminal_rlp_iff_completeSegalSpaces
    (Z : SimplicialSpace.{u}) :
    (monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u}).rlp
        (terminal.from Z) ↔ completeSegalSpaces Z := by
  constructor
  · intro h
    apply (LocalGenerators.terminal_rlp_iff_completeSegalSpaces Z).1
    exact antitone_rlp LocalGenerators.le_monomorphisms_inf_rezkWeakEquivalences
      (terminal.from Z) h
  · exact completeSegalSpaces_terminal_rlp Z

end SimplicialSpace
