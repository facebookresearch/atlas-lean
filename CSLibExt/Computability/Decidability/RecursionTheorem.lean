/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Self-reference through the recursion theorem
-/
module

public import Mathlib.Computability.Halting

/-!
# Self-reference through the recursion theorem

Kleene's recursion theorem is Mathlib's `Nat.Partrec.Code.fixed_point₂`: for every partial
recursive `f : Code → ℕ →. ℕ` some code `c` computes `f c`, so a code may use its own number.
Its fixed-point form (Sipser, Theorem 6.8: every computable transformation of codes has a code
computing the same function as its image) is `Nat.Partrec.Code.fixed_point`. This file adds two
standard self-referential codes:

* `exists_quine`: a code that outputs its own number on every input (Sipser, §6.1, the machine
  `SELF`);
* `exists_dom_eq_singleton_encode`: a code that halts exactly on its own number.

The tests also apply the recursion-theorem argument Sipser uses for the undecidability of
`A_TM` to the fixed-input halting predicate `fun c ↦ (c.eval 0).Dom` (Mathlib's
`ComputablePred.halting_problem`); acceptance itself is `Accepts` in
`Reductions.lean`. Sipser's Theorem 6.7 (the
minimal codes are not recognizable) is `not_tm2Recognizable_minimalCode` in `Minimal.lean`.

## Main results

- `exists_quine`, `exists_dom_eq_singleton_encode`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §6.1.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Encodable
open Nat.Partrec (Code)

/-- **A quine.** There is a code $c$ of a partial recursive function on $\mathbb{N}$ that, on
every input $n \in \mathbb{N}$, halts and outputs the number encoding $c$. -/
theorem exists_quine : ∃ c : Code, ∀ n, c.eval n = Part.some (encode c) := by
  obtain ⟨c, hc⟩ := Code.fixed_point₂ (f := fun c _ ↦ Part.some (encode c))
    (Computable.encode.comp Computable.fst).partrec.to₂
  exact ⟨c, fun n ↦ by rw [hc]⟩

/-- **A code that halts exactly on its own number.** There is a code $c$ of a partial recursive
function on $\mathbb{N}$ such that, for every $n \in \mathbb{N}$, $c$ halts on input $n$ if and
only if $n$ is the number encoding $c$. -/
theorem exists_dom_eq_singleton_encode : ∃ c : Code, c.eval.Dom = {encode c} := by
  obtain ⟨c, hc⟩ := Code.fixed_point₂
    (f := fun c n ↦ cond (decide (n = encode c)) (Part.some 0) Part.none)
    (Partrec.cond (Primrec.eq.comp Primrec.snd (Primrec.encode.comp Primrec.fst)).decide.to_comp
      (Partrec.const' _) Partrec.none).to₂
  refine ⟨c, Set.ext fun n ↦ ?_⟩
  change (c.eval n).Dom ↔ n = encode c
  rw [hc]
  by_cases h : n = encode c <;> simp [h]

end Cslib.Decidability
