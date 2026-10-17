/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.PCP

@[expose] public section

/-!
# Tests for the reduction from MPCP to PCP

A solvable MPCP instance and its PCP image, the counterexample showing that the nonempty-words
hypothesis of `mpcp_iff_pcp_toPCP` is needed, and the many-one reduction.
-/

set_option autoImplicit false

open Cslib.Decidability.Post

namespace CSLibExtTest.Computability.Decidability.PCP

/-- The one-domino instance `[(1, 1)]` has an MPCP solution, so its image has a PCP solution. -/
example : PCP (toPCP [(([true] : List Bool), ([true] : List Bool))]) :=
  (mpcp_iff_pcp_toPCP (by intro d hd; simp at hd; simp [hd])).mp
    ⟨_, [], rfl, List.cons_ne_nil _ _, by simp, rfl⟩

/-- `[(b, ab), (a, ε)]` with `a = false`, `b = true`. -/
def badP : List (Domino Bool) := [([true], [false, true]), ([false], [])]

/-- It has no MPCP solution: every candidate starts with `(b, ab)`, whose words begin with
different letters. -/
theorem not_mpcp_badP : ¬MPCP badP := by
  rintro ⟨d₀, s, hd₀, -, -, heq⟩
  obtain rfl : d₀ = ([true], [false, true]) := (Option.some.inj hd₀).symm
  simp only [top_cons, bottom_cons, List.cons_append, List.cons.injEq] at heq
  exact Bool.noConfusion heq.1

/-- Yet its image has a PCP solution, starting with the image of `(a, ε)`. So the
nonempty-words hypothesis cannot be dropped. -/
theorem pcp_toPCP_badP : PCP (toPCP badP) :=
  ⟨[mapDomino ([false], []), startDomino ([true], [false, true]), endDomino],
    List.cons_ne_nil _ _, by decide, by decide⟩

example : ¬(MPCP badP ↔ PCP (toPCP badP)) := fun h ↦ not_mpcp_badP (h.mpr pcp_toPCP_badP)

/-- The many-one reduction, over the alphabet `Bool`. -/
example : ManyOneReducible (fun P : List (Domino Bool) ↦ NonemptyWords P ∧ MPCP P)
    (PCP (α := Sym Bool)) :=
  manyOneReducible_mpcp_pcp

/-- PCP over `Bool` is recognizable by a multi-stack machine. -/
example : Cslib.Decidability.TM2Recognizable (PCP (α := Bool)) := tm2Recognizable_pcp

/-- The solution check agrees with the definition on the counterexample's solution. -/
example : isSolutionB (toPCP badP)
    [mapDomino ([false], []), startDomino ([true], [false, true]), endDomino] = true := by
  decide

end CSLibExtTest.Computability.Decidability.PCP
