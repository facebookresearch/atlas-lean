/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.Combinatorics.CleanLatticeParallelogram

/-!
# Lamé's theorem on Euclid's algorithm

For a fixed positive number of division steps, the pair with least larger input
consists of two consecutive Fibonacci numbers.
-/

namespace MetaMathlibExt

namespace lame_euclidSteps_minimal

private theorem steps_fib (n : ℕ) :
    euclidSteps (Nat.fib (n + 3)) (Nat.fib (n + 2)) = n + 1 := by
  induction n with
  | zero => exact euclidSteps_small_values.1
  | succ n ih =>
    have hlt : Nat.fib (n + 2) < Nat.fib (n + 3) := Nat.fib_lt_fib_succ (by omega)
    have hmod : Nat.fib (n + 4) % Nat.fib (n + 3) = Nat.fib (n + 2) := by
      rw [Nat.fib_add_two (n := n + 2), Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    rw [euclidSteps, dite_eq_right (Nat.fib_pos.mpr (by omega)).ne', hmod, ih]

-- Bound the smaller input and the gap to the larger input. Their sum bounds the
-- larger input, and equality in the sum forces equality in both bounds.
private theorem fib_bounds {n u v : ℕ} (huv : v < u) (hv : 0 < v)
    (hsteps : euclidSteps u v = n + 1) :
    Nat.fib (n + 2) ≤ v ∧ Nat.fib (n + 1) + v ≤ u := by
  induction n generalizing u v with
  | zero => exact ⟨hv, by simpa [Nat.add_comm] using huv⟩
  | succ n ih =>
    rw [euclidSteps, dite_eq_right hv.ne', Nat.add_right_cancel_iff] at hsteps
    have hpos : 0 < u % v := by
      by_contra! hzero
      simp [Nat.eq_zero_of_le_zero hzero, euclidSteps] at hsteps
    obtain ⟨hr, hvr⟩ := ih (Nat.mod_lt _ hv) hpos hsteps
    have hgap : u % v ≤ u - v := by
      rw [Nat.mod_eq_sub_mod huv.le]
      exact Nat.mod_le _ _
    change Nat.fib (n + 3) ≤ v ∧ Nat.fib (n + 2) + v ≤ u
    have hrec : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    rw [hrec]
    omega

end lame_euclidSteps_minimal

open lame_euclidSteps_minimal in
/-- **Lamé's theorem (1844).** Let $F_0 = 0$, $F_1 = 1$, $F_{k+2} = F_{k+1} + F_k$ be the
Fibonacci numbers, and let $N \ge 1$. Let $u > v > 0$ be natural numbers on which Euclid's
algorithm takes exactly $N$ division steps, and suppose that $u \le u'$ whenever $u' > v' > 0$
are natural numbers on which it takes exactly $N$ division steps. Then $u = F_{N+2}$ and
$v = F_{N+1}$.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Theorem 7 (`integers-2026-A10-thm-7`). -/
public theorem lame_euclidSteps_minimal {N u v : ℕ} (hN : 1 ≤ N) (huv : v < u) (hv : 0 < v)
    (hsteps : euclidSteps u v = N)
    (hmin : ∀ u' v', v' < u' → 0 < v' → euclidSteps u' v' = N → u ≤ u') :
    u = Nat.fib (N + 2) ∧ v = Nat.fib (N + 1) := by
  cases N with
  | zero => omega
  | succ n =>
    obtain ⟨hvLower, hgap⟩ := fib_bounds (n := n) huv hv hsteps
    have huUpper : u ≤ Nat.fib (n + 3) :=
      hmin _ _ (Nat.fib_lt_fib_succ (by omega)) (Nat.fib_pos.mpr (by omega)) (steps_fib n)
    change u = Nat.fib (n + 3) ∧ v = Nat.fib (n + 2)
    have hrec : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    rw [hrec] at huUpper ⊢
    omega

end MetaMathlibExt
