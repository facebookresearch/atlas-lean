/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Levi's lemma for word equations
-/
module

public import Mathlib.Data.List.Basic

/-!
# Levi's lemma for word equations

If two concatenations are equal, one of the two left factors is a
prefix of the other. This is the basic splitting step of every
word-equation algorithm: Makanin's algorithm, Plandowski's algorithm,
and Jeż's recompression all proceed by comparing the two sides of an
equation and splitting at the shorter prefix. Only Levi's lemma is
formalized here; the cited algorithms are background.

## Main results

- `levi`: Levi's lemma.
- `levi_of_le`: the length-directed form: when the left factor is no
  longer than the other, the split is determined.
- `append_left_cancel`, `append_right_cancel`: cancellation of a common
  prefix or suffix in a word equation.

## References

* G. S. Makanin, *The problem of solvability of equations in a free
  semigroup*, Math. USSR-Sb. 32 (1977).
* W. Plandowski, *Satisfiability of word equations with length
  constraints*, J. Comput. Syst. Sci. 1999.
* A. Jeż, *Recompression: A Simple and Powerful Technique for Word
  Equations*, JACM 2017.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.AutomatedReasoning.StringConstraints

variable {α : Type*}

/-- **Levi's lemma**: from `u ++ v = x ++ y`, either `x` starts with
`u` (and the remainders match) or `u` starts with `x`. -/
theorem levi {u v x y : List α} (h : u ++ v = x ++ y) :
    (∃ w, x = u ++ w ∧ v = w ++ y) ∨ (∃ w, u = x ++ w ∧ y = w ++ v) :=
  List.append_eq_append_iff.mp h

/-- Length-directed Levi's lemma: if `u` is no longer than `x`, then
`x` splits as `u ++ w` and the remainders satisfy `v = w ++ y`. -/
theorem levi_of_le {u v x y : List α} (h : u ++ v = x ++ y)
    (hle : u.length ≤ x.length) : ∃ w, x = u ++ w ∧ v = w ++ y := by
  rcases levi h with ⟨w, hx, hv⟩ | ⟨w, hu, hy⟩
  · exact ⟨w, hx, hv⟩
  · have hw : w = [] := by
      have hlen : u.length = x.length + w.length := by rw [hu, List.length_append]
      have h0 : w.length = 0 := by omega
      exact List.eq_nil_of_length_eq_zero h0
    subst hw
    exact ⟨[], by simpa using hu.symm, by simpa using hy.symm⟩

/-- Cancellation of a common prefix in a word equation. -/
theorem append_left_cancel {u v w : List α} (h : u ++ v = u ++ w) : v = w :=
  List.append_cancel_left h

/-- Cancellation of a common suffix in a word equation. -/
theorem append_right_cancel {u v w : List α} (h : v ++ u = w ++ u) : v = w :=
  List.append_cancel_right h

end Cslib.AutomatedReasoning.StringConstraints
