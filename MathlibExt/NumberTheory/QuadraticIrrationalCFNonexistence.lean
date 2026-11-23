/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Convergent denominators of symmetric continued fractions

For an even period length, symmetry determines the parity of the shifted continuant
from the middle coefficient and the continuant on its left.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Convergent denominators as continuants.** For a sequence of natural numbers
$a_0, a_1, a_2, \dots$, its convergent denominators $q_0, q_1, q_2, \dots$ are the natural
numbers defined by $q_0 = 1$, $q_1 = a_1$ and $q_{i+2} = a_{i+2} q_{i+1} + q_i$ for $i \ge 0$.
They are the denominators of the convergents of $[a_0; a_1, a_2, \dots]$, and $q_i$ is the
continuant $K(a_1, \dots, a_i)$; the term $a_0$ is never used.

The denominators $r_i$ of the paper, those of the convergents of $[a_1; a_2, \dots, a_i]$, are
the convergent denominators of the shifted sequence $(a_{n+1})_{n \ge 0}$ at index $i - 1$, for
$i \ge 1$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, notation of
Proposition 2 (`integers-2026-A69-prop-2`). -/
def convergentDen (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 1
  | n + 2 => a (n + 2) * convergentDen a (n + 1) + convergentDen a n

/-- **The convergent denominator $q_0$ equals $1$.** For every sequence of natural numbers
$a_0, a_1, a_2, \dots$ with convergent denominators $q_0, q_1, q_2, \dots$, we have $q_0 = 1$.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_zero (a : ℕ → ℕ) : convergentDen a 0 = 1 := rfl

/-- **The convergent denominator $q_1$ equals $a_1$.** For every sequence of natural numbers
$a_0, a_1, a_2, \dots$ with convergent denominators $q_0, q_1, q_2, \dots$, we have $q_1 = a_1$.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_one (a : ℕ → ℕ) : convergentDen a 1 = a 1 := rfl

/-- **Recurrence for the convergent denominators.** For every sequence of natural numbers
$a_0, a_1, a_2, \dots$ with convergent denominators $q_0, q_1, q_2, \dots$ and every natural
number $n$, we have $q_{n+2} = a_{n+2} q_{n+1} + q_n$.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_add_two (a : ℕ → ℕ) (n : ℕ) :
    convergentDen a (n + 2) = a (n + 2) * convergentDen a (n + 1) + convergentDen a n := rfl

/-- **The convergent denominator $q_2$ equals $a_2 a_1 + 1$.** For every sequence of natural
numbers $a_0, a_1, a_2, \dots$ with convergent denominators $q_0, q_1, q_2, \dots$, we have
$q_2 = a_2 a_1 + 1$.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_two (a : ℕ → ℕ) : convergentDen a 2 = a 2 * a 1 + 1 := rfl

/-- **Continued fractions with a prescribed period.** For a real number $x$, natural numbers
$a_0$, $l$, $c$ and a sequence of natural numbers $a_1, a_2, \dots$, we write
$x = [a_0; \overline{a_1, \dots, a_{l-1}, c}]$ when the regular continued fraction of $x$ is the
infinite expansion $[a_0; a_1, \dots, a_{l-1}, c, a_1, \dots, a_{l-1}, c, \dots]$: its integer
part is $a_0$, and for every $k \ge 1$ its $k$-th partial quotient exists and equals $c$ when $l$
divides $k$ and $a_{k \bmod l}$ otherwise. The period $l$ need not be minimal.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, the expansions
`√d = [a₀; a₁, …, a_{l-1}, 2a₀]` of Theorem 1 (`integers-2026-A69-thm-1`). -/
def HasPeriodicCF (x : ℝ) (a₀ : ℕ) (a : ℕ → ℕ) (l c : ℕ) : Prop :=
  (GenContFract.of x).h = a₀ ∧ ∀ n : ℕ, (GenContFract.of x).partDens.get? n =
    some (if (n + 1) % l = 0 then (c : ℝ) else (a ((n + 1) % l) : ℝ))

/-- **The integer part of a periodic continued fraction is the floor.** Let $x$ be a real
number and let $a_0$, $l$, $c$ and $a_1, a_2, \dots$ be natural numbers. Suppose that the regular
continued fraction of $x$ has integer part $a_0$ and that, for every $k \ge 1$, its $k$-th
partial quotient is $c$ when $l$ divides $k$ and $a_r$ otherwise, where $r$ is the remainder of
$k$ modulo $l$ (so $r = k$ when $l = 0$). For $l \ge 1$ this says that the continued fraction
is $[a_0; a_1, \dots, a_{l-1}, c, a_1, \dots, a_{l-1}, c, \dots]$. Then $\lfloor x \rfloor = a_0$.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, Theorem 1 (`a₀ = ⌊√d⌋`). -/
theorem HasPeriodicCF.floor_eq {x : ℝ} {a₀ : ℕ} {a : ℕ → ℕ} {l c : ℕ}
    (h : HasPeriodicCF x a₀ a l c) : ⌊x⌋ = a₀ := by
  have h0 := h.1
  rw [GenContFract.of_h_eq_floor] at h0
  exact_mod_cast h0

/-- **Parity of the shifted continuant of a symmetric sequence, even length.** Let $l \ge 4$ be
even and let $a_1, \dots, a_{l-1}$ be natural numbers with $a_i = a_{l-i}$ for
$1 \le i \le l - 1$. For $j \ge 1$ let $r_j = K(a_2, \dots, a_j)$ be the continuant, given by
$r_1 = 1$, $r_2 = a_2$ and $r_{j+2} = a_{j+2} r_{j+1} + r_j$. Then
$r_{l-2} \equiv a_{l/2} \, r_{l/2-1} \pmod 2$.

The case $l = 2$ of the paper, which needs $r_0 = 0$, is omitted.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 1 (ii)
(`integers-2026-A69-cor-1`). -/
theorem shifted_convergentDen_parity_of_even (l : ℕ) (hl : Even l) (hl4 : 4 ≤ l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen (fun n => a (n + 1)) (l - 3) ≡
      a (l / 2) * convergentDen (fun n => a (n + 1)) (l / 2 - 2) [MOD 2] := by
  let r : ℕ → ℕ
    | 0 => 0
    | n + 1 => convergentDen (fun j => a (j + 1)) n
  have step (n : ℕ) : r (n + 2) = a (n + 2) * r (n + 1) + r n := by
    cases n with
    | zero => simp [r, convergentDen]
    | succ n => rfl
  -- Moving the split one position to the right preserves this sum of products.
  have split (i j : ℕ) (hij : i + j + 3 = l) :
      r (l - 2) = r (i + 1) * r (j + 1) + r i * r j := by
    induction i generalizing j with
    | zero =>
      rw [show l - 2 = j + 1 by omega]
      simp [r, convergentDen]
    | succ i ih =>
      have hmirror : a (i + 2) = a (j + 2) := by
        simpa only [show l - (i + 2) = j + 2 by omega] using
          hsymm (i + 2) (by omega) (by omega)
      rw [ih (j + 1) (by omega), step j, step i, hmirror]
      ring
  obtain ⟨m, hm⟩ := hl
  let k := l / 2 - 2
  have hk : k + 2 = l / 2 := by dsimp [k]; omega
  have hsplit := split k (k + 1) (by dsimp [k]; omega)
  have hsquare : r (k + 1) * r (k + 1) ≡ r (k + 1) [MOD 2] := by
    rw [Nat.ModEq, Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one (r (k + 1)) with h | h <;> simp [h]
  change r (l - 3 + 1) ≡ a (l / 2) * r (k + 1) [MOD 2]
  rw [show l - 3 + 1 = l - 2 by omega, hsplit, step k, hk]
  calc
    _ = 2 * (r k * r (k + 1)) + a (l / 2) * (r (k + 1) * r (k + 1)) := by ring
    _ ≡ a (l / 2) * (r (k + 1) * r (k + 1)) [MOD 2] := Nat.ModEq.modulus_mul_add
    _ ≡ _ [MOD 2] := hsquare.mul_left _

end

end MetaMathlibExt
