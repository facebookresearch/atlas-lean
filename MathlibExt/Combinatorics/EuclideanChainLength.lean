/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# The Euclidean chain function

For natural numbers $x_1$ and $x_2$, the Euclidean chain $x_1, x_2, x_3, \dots$ continues by
$x_{i+1} = (-x_{i-1}) \bmod x_i$ while $x_i \ne 0$. The Euclidean chain function
`euclideanChainLength` follows the recursion $F(x, 0) = 1$ and
$F(x, y) = 1 + F(y, (-x) \bmod y)$ for $y \ne 0$; for $x_1 > 0$, $F(x_1, x_2)$ counts the positive
terms of the chain. Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith use it to read off the path
length of a smooth arithmetical structure on a coconut tree from its labels.

## Main declarations

* `MetaMathlibExt.euclideanChainLength`: the Euclidean chain function $F$, with its defining
  recursion `euclideanChainLength_zero` and `euclideanChainLength_of_ne_zero`.
* `MetaMathlibExt.euclideanChainLength_thirteen_sixty`: $F(13, 60) = 8$.
* `MetaMathlibExt.euclideanChainLength_one_left_and_one_right`: $F(1, y) = y + 1$ for every
  natural number $y$, and $F(x, 1) = 2$ for every natural number $x \ge 1$.

## Implementation notes

The source obtains $F(1, y) = y + 1$ from its formula $F(x, y) = 1 + y / x$ for $x \mid y$,
which rests on a result it quotes from Archer et al. Here a direct induction replaces it: when
$x \equiv 1 \pmod{m + 1}$ the recursion gives $F(x, m + 1) = 1 + F(m + 1, m)$, hence
$F(n + 1, n) = n + 1$ for every $n$ and then $F(1, y) = y + 1$. As $(-x) \bmod 1 = 0$, the
recursion gives $F(x, 1) = 1 + F(1, 0) = 2$ for every $x$, including $x = 0$, so the hypothesis
$x \ge 1$ of the source statement is kept but not used.

## References

* Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical Structures on Coconut Trees*,
  INTEGERS 25 (2025), Article A82; preprint arXiv:2406.11183, Definition 4.12, Example 4.13
  and Corollary 4.16.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Euclidean chain function.** For natural numbers $x_1$ and $x_2$, the Euclidean chain
$x_1, x_2, x_3, \dots$ is given by $x_{i+1} = (-x_{i-1}) \bmod x_i$ (the least nonnegative
residue) while $x_i \ne 0$, and by $x_{i+1} = 0$ once $x_i = 0$. The Euclidean chain function is
defined by the recursion $F(x, 0) = 1$ and $F(x, y) = 1 + F(y, (-x) \bmod y)$ for $y \ne 0$. For
$x_1 > 0$, $F(x_1, x_2)$ is the number of positive terms of the Euclidean chain.

For $x_1 = 0$ the recursion also counts the first term $0$: $F(0, 0) = 1$ and $F(0, 1) = 2$,
although the chains $0, 0$ and $0, 1, 0$ have $0$ and $1$ positive terms.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 4.12
(arXiv numbering). -/
public def euclideanChainLength (x y : ℕ) : ℕ :=
  if h : y = 0 then 1 else 1 + euclideanChainLength y ((y - x % y) % y)
termination_by y
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- **Euclidean chain function with second argument zero.** For every natural number $x$, the
Euclidean chain function $F$ satisfies $F(x, 0) = 1$.

For $x = 0$ this is the value given by the recursive definition of $F$, not a count of positive
terms.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 4.12
(arXiv numbering). -/
public theorem euclideanChainLength_zero (x : ℕ) : euclideanChainLength x 0 = 1 := by
  rw [euclideanChainLength]
  simp

/-- **Recursion for the Euclidean chain function.** For natural numbers $x$ and $y$ with $y \ne 0$,
the Euclidean chain function $F$ satisfies $F(x, y) = 1 + F(y, (-x) \bmod y)$, where
$(-x) \bmod y$ is the least nonnegative residue of $-x$ modulo $y$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 4.12
(arXiv numbering). -/
public theorem euclideanChainLength_of_ne_zero (x : ℕ) {y : ℕ} (hy : y ≠ 0) :
    euclideanChainLength x y = 1 + euclideanChainLength y ((y - x % y) % y) := by
  rw [euclideanChainLength]
  simp [hy]

/-- **Euclidean chain function of 13 and 60.** The Euclidean chain function $F$ satisfies
$F(13, 60) = 8$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Example 4.13
(arXiv numbering). -/
public theorem euclideanChainLength_thirteen_sixty : euclideanChainLength 13 60 = 8 := by
  simp [euclideanChainLength_of_ne_zero, euclideanChainLength_zero]

/-- If $x \equiv 1 \pmod{m + 1}$, the recursion gives $F(x, m + 1) = 1 + F(m + 1, m)$. -/
private theorem euclideanChainLength_add_one_of_mod_eq {x m : ℕ}
    (hx : x % (m + 1) = 1 % (m + 1)) :
    euclideanChainLength x (m + 1) = 1 + euclideanChainLength (m + 1) m := by
  rw [euclideanChainLength_of_ne_zero x (Nat.add_one_ne_zero m), hx]
  congr 2
  rcases m with _ | m
  · rfl
  · rw [Nat.mod_eq_of_lt (by omega : 1 < m + 1 + 1), Nat.add_sub_cancel,
      Nat.mod_eq_of_lt (Nat.lt_add_one _)]

/-- The Euclidean chain function satisfies $F(n + 1, n) = n + 1$. -/
private theorem euclideanChainLength_add_one_self (n : ℕ) :
    euclideanChainLength (n + 1) n = n + 1 := by
  induction n with
  | zero => exact euclideanChainLength_zero 1
  | succ n ih =>
    rw [euclideanChainLength_add_one_of_mod_eq (Nat.add_mod_left (n + 1) 1), ih, Nat.add_comm]

-- `hx` is a hypothesis of the source statement, kept for fidelity; the proof does not need it.
set_option linter.unusedVariables false in
/-- **Euclidean chain function at one.** For every natural number $y$, the Euclidean chain
function $F$ satisfies $F(1, y) = y + 1$, and for every natural number $x \ge 1$ it satisfies
$F(x, 1) = 2$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 5
(`integers-2025-A82-cor-5`). -/
public theorem euclideanChainLength_one_left_and_one_right (y : ℕ) {x : ℕ}
    (hx : 0 < x) :
    euclideanChainLength 1 y = y + 1 ∧ euclideanChainLength x 1 = 2 := by
  refine ⟨?_, ?_⟩
  · rcases y with _ | y
    · exact euclideanChainLength_zero 1
    · rw [euclideanChainLength_add_one_of_mod_eq rfl, euclideanChainLength_add_one_self,
        Nat.add_comm]
  · rw [euclideanChainLength_add_one_of_mod_eq (m := 0) (by rw [Nat.mod_one, Nat.mod_one]),
      euclideanChainLength_zero]

/-- **Euclidean chain function under adding multiples.** For natural numbers $x \ge 1$, $y$ and
$k$, the Euclidean chain function $F$ satisfies $F(x + k y, y) = F(x, y)$ and
$F(x, k x + y) = F(x, y) + k$.

The source quotes this result from Archer et al.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 6
(`integers-2025-A82-prop-6`). -/
public theorem euclideanChainLength_add_mul {x : ℕ} (hx : 0 < x) (y k : ℕ) :
    euclideanChainLength (x + k * y) y = euclideanChainLength x y ∧
      euclideanChainLength x (k * x + y) = euclideanChainLength x y + k := by
  have add_left (a b n : ℕ) :
      euclideanChainLength (a + n * b) b = euclideanChainLength a b := by
    by_cases hb : b = 0
    · simp [hb, euclideanChainLength_zero]
    · rw [euclideanChainLength_of_ne_zero (a + n * b) hb,
        euclideanChainLength_of_ne_zero a hb, Nat.add_mul_mod_self_right]
  have add_right (z : ℕ) :
      euclideanChainLength x (z + x) = euclideanChainLength x z + 1 := by
    have hmod : (z + x - x % (z + x)) % (z + x) = z := by
      obtain rfl | hz := Nat.eq_zero_or_pos z
      · simp
      · rw [Nat.mod_eq_of_lt (show x < z + x by omega), Nat.add_sub_cancel,
          Nat.mod_eq_of_lt (show z < z + x by omega)]
    have hleft : euclideanChainLength (z + x) z = euclideanChainLength x z := by
      simpa only [Nat.one_mul, Nat.add_comm] using add_left x z 1
    rw [euclideanChainLength_of_ne_zero x (by omega : z + x ≠ 0), hmod, hleft, Nat.add_comm 1]
  refine ⟨add_left x y k, ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.add_right_comm (k * x) x y, add_right, ih, Nat.add_assoc]

-- The proof also works for `y = 0`; retain the original positive-`y` hypothesis.
set_option linter.unusedVariables false in
/-- **Euclidean chain function when the first argument divides the second.** For natural numbers
$x, y \ge 1$ with $x \mid y$, the Euclidean chain function $F$ satisfies $F(x, y) = 1 + y / x$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 4
(`integers-2025-A82-cor-4`). -/
public theorem euclideanChainLength_of_dvd {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ∣ y) : euclideanChainLength x y = 1 + y / x := by
  simpa only [Nat.add_zero, Nat.div_mul_cancel hxy, euclideanChainLength_zero] using
    (euclideanChainLength_add_mul hx 0 (y / x)).2

end

end MetaMathlibExt
