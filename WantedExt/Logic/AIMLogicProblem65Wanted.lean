/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AIM Logic Problem 65
-/
module

public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Logic.AIMLogicProblem65Wanted

open FirstOrder

/-! Source record `UM-20002289-Q001`. -/
/-- `F` is elementarily equivalent to `ℚ` in Mathlib's first-order language of rings
`FirstOrder.Language.ring` (symbols `+`, `*`, `-`, `0`, `1`): `ℚ` and `F` satisfy the same
sentences when the symbols are interpreted by the field operations
(`FirstOrder.Ring.compatibleRingOfRing`). -/
def ElementarilyEquivalentToRat (F : Type) [Field F] : Prop :=
  letI := Ring.compatibleRingOfRing ℚ
  letI := Ring.compatibleRingOfRing F
  Language.ring.ElementarilyEquivalent ℚ F

/-- Koenigsmann's question: if `ℚ* ⊆ ℚ**` are both elementarily equivalent to `ℚ`, then `ℚ*` is
relatively algebraically closed in `ℚ**`. -/
def conjecture : Prop :=
  ∀ (Qstar : Type) (QstarStar : Type) [Field Qstar] [Field QstarStar] [Algebra Qstar QstarStar],
    ElementarilyEquivalentToRat Qstar → ElementarilyEquivalentToRat QstarStar →
      ∀ x : QstarStar, IsAlgebraic Qstar x → ∃ y : Qstar, algebraMap Qstar QstarStar y = x

-- Carried source audit `UM-20002289-Q001` (see the Moved/ record).

/--
Resolved true: Resolved true: Dittmann (Irreducibility of polynomials over global fields is
diophantine, arXiv:1601.07829, Corollary 5.3) proves that if K** ⊇ K* are elementary extensions
of a global field K then K* is relatively algebraically closed in K**; with K = Q, whose
elements are all definable, this answers Koenigsmann's question. Source: P. Dittmann,
Irreducibility of polynomials over global fields is diophantine, arXiv:1601.07829,
https://arxiv.org/abs/1601.07829. Moved from `OpenConjectures/Logic/AIMLogicProblem65`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Logic.AIMLogicProblem65Wanted
