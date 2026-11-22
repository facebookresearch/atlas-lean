/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The fourth positive element in the greedy `B_h`-set

Statements from Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth
Positive Element in the Greedy `B_h`-Set", *Journal of Integer
Sequences* 27 (2024), Article 24.7.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/OBryant2/obryant4.html>).

The greedy choice is expressed stage by stage with MathlibExt's
canonical `AdditiveCombinatorics.IsBhSet`, using the paper's known
terms `a₀(h) = 0`, `a₁(h) = 1`, `a₂(h) = h + 1`, and
`a₃(h) = h² + h + 1`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.Combinatorics.Additive.BhSet

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.GreedyBhFourthWanted

/-- **Next term of a greedy $B_h$-set.** Let $h$ and $a$ be natural numbers and $A$ a set of natural
numbers. Then $a$ is the next greedy $B_h$ choice after $A$ if $a$ is greater than every element
of $A$, the set $A \cup \{a\}$ is a $B_h$-set, and for every natural number $b < a$ that is
greater than every element of $A$, the set $A \cup \{b\}$ is not a $B_h$-set. -/
def IsNextGreedyBh (h : ℕ) (A : Set ℕ) (a : ℕ) : Prop :=
  (∀ x ∈ A, x < a) ∧ AdditiveCombinatorics.IsBhSet (insert a A) h ∧
    ∀ b : ℕ, (∀ x ∈ A, x < b) → b < a →
      ¬AdditiveCombinatorics.IsBhSet (insert b A) h

/-- **Fourth positive term of the greedy $B_h$-set.** For natural numbers $h$ and $a$, we say that
$a$ is the fourth positive element $a_4(h)$ of the greedy $B_h$-set if $1$ is the next greedy
$B_h$ choice after $\{0\}$, $h + 1$ is the next greedy $B_h$ choice after $\{0, 1\}$,
$h^2 + h + 1$ is the next greedy $B_h$ choice after $\{0, 1, h + 1\}$, and $a$ is the next
greedy $B_h$ choice after $\{0, 1, h + 1, h^2 + h + 1\}$. -/
def IsFourthGreedyBh (h a : ℕ) : Prop :=
  IsNextGreedyBh h {0} 1 ∧
    IsNextGreedyBh h {0, 1} (h + 1) ∧
    IsNextGreedyBh h {0, 1, h + 1} (h ^ 2 + h + 1) ∧
    IsNextGreedyBh h {0, 1, h + 1, h ^ 2 + h + 1} a

/-- **Quasipolynomial for the fourth greedy $B_h$ term.** For a natural number $h$, the value
$v(h)$ is $(h^3 + 3h^2 + 3h + 1)/2$ if $h$ is odd and $(h^3 + 2h^2 + 3h + 2)/2$ if $h$ is even.

Both numerators are even, so the divisions are exact. -/
def fourthValue (h : ℕ) : ℕ :=
  if Odd h then (h ^ 3 + 3 * h ^ 2 + 3 * h + 1) / 2
  else (h ^ 3 + 2 * h ^ 2 + 3 * h + 2) / 2

/-- **Formula for the fourth greedy $B_h$ term.** For every integer $h \ge 1$, the fourth positive
element $a_4(h)$ of the greedy $B_h$-set is $(h^3 + 3h^2 + 3h + 1)/2$ if $h$ is odd and
$(h^3 + 2h^2 + 3h + 2)/2$ if $h$ is even.

Source: Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth Positive
Element in the Greedy `B_h`-Set", Theorem 1. -/
theorem_wanted isFourthGreedyBh_fourthValue
    (h : ℕ) (hh : 0 < h) :
    IsFourthGreedyBh h (fourthValue h)

/-- **Lower bound for the fourth greedy $B_h$ term.** Let $h$ and $a$ be natural numbers with
$h \ge 2$. If $a$ is the fourth positive element $a_4(h)$ of the greedy $B_h$-set, then
$a \ge v(h)$, where $v(h) = (h^3 + 3h^2 + 3h + 1)/2$ if $h$ is odd and
$v(h) = (h^3 + 2h^2 + 3h + 2)/2$ if $h$ is even.

Source: Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth Positive
Element in the Greedy `B_h`-Set", Lemma 2. -/
theorem_wanted fourthValue_le_of_isFourthGreedyBh
    (h a : ℕ) (hh : 2 ≤ h) (ha : IsFourthGreedyBh h a) :
    fourthValue h ≤ a

/-- **Upper bound for the fourth greedy $B_h$ term.** Let $h$ and $a$ be natural numbers with
$h \ge 1$. If $a$ is the fourth positive element $a_4(h)$ of the greedy $B_h$-set, then
$a \le v(h)$, where $v(h) = (h^3 + 3h^2 + 3h + 1)/2$ if $h$ is odd and
$v(h) = (h^3 + 2h^2 + 3h + 2)/2$ if $h$ is even.

Source: Melvyn B. Nathanson and Kevin O'Bryant, "The Fourth Positive
Element in the Greedy `B_h`-Set", Lemma 3. -/
theorem_wanted isFourthGreedyBh_le_fourthValue
    (h a : ℕ) (hh : 0 < h) (ha : IsFourthGreedyBh h a) :
    a ≤ fourthValue h

end MathlibExt.Combinatorics.GreedyBhFourthWanted
