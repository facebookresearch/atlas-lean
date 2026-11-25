/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Data.Matrix.Mul

/-!
# Powers of the Padovan–Perrin companion matrix

Each column of a power of the companion matrix lists consecutive terms of one fundamental
solution in reverse order. Left multiplication advances the recurrence in the first row
and shifts the remaining rows down.
-/

@[expose] public section

namespace MetaMathlibExt

variable {R : Type*}

/-- **Generalized Padovan–Perrin recurrence.** Let $R$ be a commutative semiring, $k_1, k_2 \in R$
and $p, s \in \mathbb{N}$. The $([k]; p; s)$-generalized Padovan–Perrin recurrence is the linear
recurrence of order $s + p$ with coefficients $c_i = [i = 0] \, k_2 + [i = p] \, k_1$ for
$0 \le i < s + p$, where $[\cdot]$ is $1$ if the condition holds and $0$ otherwise: a sequence
$v \colon \mathbb{N} \to R$ solves it when $v_{n+s+p} = \sum_{i=0}^{s+p-1} c_i v_{n+i}$ for every
$n \ge 0$. For $s > 0$ this reads $v_{n+s+p} = k_1 v_{n+p} + k_2 v_n$, that is,
$v_n = k_1 v_{n-s} + k_2 v_{n-s-p}$ for $n \ge s + p$ (equation (1)).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (1). -/
def padovanPerrinRecurrence [CommSemiring R] (k₁ k₂ : R) (p s : ℕ) : LinearRecurrence R :=
  ⟨s + p, fun i => (if (i : ℕ) = 0 then k₂ else 0) + (if (i : ℕ) = p then k₁ else 0)⟩

/-- **Characterization of solutions of the generalized Padovan–Perrin recurrence.** Let $R$ be a
commutative semiring, $k_1, k_2 \in R$, and $p, s \in \mathbb{N}$ with $s > 0$. A sequence
$v \colon \mathbb{N} \to R$ is a solution of the $([k]; p; s)$-Padovan–Perrin recurrence if and
only if $v_{n+s+p} = k_1 v_{n+p} + k_2 v_n$ for every $n \ge 0$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (1). -/
theorem padovanPerrinRecurrence_isSolution_iff [CommSemiring R] (k₁ k₂ : R) (p s : ℕ)
    (hs : 0 < s) (v : ℕ → R) :
    (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v ↔
      ∀ n, v (n + (s + p)) = k₁ * v (n + p) + k₂ * v n := by
  unfold LinearRecurrence.IsSolution
  refine forall_congr' fun n => ?_
  have key : ∑ i : Fin (padovanPerrinRecurrence k₁ k₂ p s).order,
      (padovanPerrinRecurrence k₁ k₂ p s).coeffs i * v (n + i) = k₁ * v (n + p) + k₂ * v n := by
    change ∑ i : Fin (s + p),
      ((if (i : ℕ) = 0 then k₂ else 0) + (if (i : ℕ) = p then k₁ else 0)) * v (n + i) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ((if i = 0 then k₂ else 0) + (if i = p then k₁ else 0)) * v (n + i)) (s + p)]
    simp [add_mul, Finset.sum_add_distrib, hs, add_comm]
  rw [key]
  exact Iff.rfl

/-- **Fibonacci fundamental system of the generalized Padovan–Perrin recurrence.** Let $R$ be a
commutative semiring, $k_1, k_2 \in R$ and $p, s \in \mathbb{N}$. For a natural number $j$, the
$j$-th fundamental sequence $v^{(j)} \colon \mathbb{N} \to R$ is the solution of the
$([k]; p; s)$-Padovan–Perrin recurrence with initial values $v^{(j)}_n = 1$ if $n + 1 = j$ and
$v^{(j)}_n = 0$ otherwise, for $0 \le n < s + p$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (2) and Definition 1. -/
def padovanPerrinFundamental [CommSemiring R] (k₁ k₂ : R) (p s j : ℕ) : ℕ → R :=
  (padovanPerrinRecurrence k₁ k₂ p s).mkSol fun i => if (i : ℕ) + 1 = j then 1 else 0

/-- **Initial values of the generalized Padovan–Perrin fundamental system.** Let $R$ be a
commutative semiring, $k_1, k_2 \in R$ and $p, s, j \in \mathbb{N}$. For every $n < s + p$, the
$j$-th sequence $v^{(j)}$ of the Fibonacci fundamental system satisfies $v^{(j)}_n = 1$ if
$n + 1 = j$ and $v^{(j)}_n = 0$ otherwise.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (2). -/
theorem padovanPerrinFundamental_of_lt [CommSemiring R] (k₁ k₂ : R) (p s j n : ℕ)
    (hn : n < s + p) :
    padovanPerrinFundamental k₁ k₂ p s j n = if n + 1 = j then 1 else 0 :=
  (padovanPerrinRecurrence k₁ k₂ p s).mkSol_eq_init _ ⟨n, hn⟩

/-- **The generalized Padovan–Perrin fundamental sequences solve the recurrence.** Let $R$ be a
commutative semiring, $k_1, k_2 \in R$ and $p, s \in \mathbb{N}$. For every natural number $j$,
the $j$-th sequence $v^{(j)}$ of the Fibonacci fundamental system is a solution of the
$([k]; p; s)$-Padovan–Perrin recurrence.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (2). -/
theorem padovanPerrinFundamental_isSolution [CommSemiring R] (k₁ k₂ : R) (p s j : ℕ) :
    (padovanPerrinRecurrence k₁ k₂ p s).IsSolution (padovanPerrinFundamental k₁ k₂ p s j) :=
  (padovanPerrinRecurrence k₁ k₂ p s).is_sol_mkSol _

private theorem padovanPerrin_companion_pow_apply.sum_at_predecessor [CommRing R] {r d : ℕ}
    (hd : 0 < d) (hdr : d ≤ r) (c : R) (f : ℕ → R) :
    (∑ b : Fin r, (if (b : ℕ) + 1 = d then c else 0) * f b) = c * f (d - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun b => (if b + 1 = d then c else 0) * f b)]
  have heq (b : ℕ) : b + 1 = d ↔ b = d - 1 := by omega
  simp [heq, ite_mul, show d - 1 < r by omega]

open padovanPerrin_companion_pow_apply in
/-- **Powers of the Padovan–Perrin companion matrix.** Let $R$ be a commutative ring, let
$k_1, k_2 \in R$, let $p, s$ be positive integers, and write $r = s + p$. Let $A$ be the
$r \times r$ matrix over $R$, with rows and columns indexed by $0, \dots, r - 1$, whose row $0$ has
$k_1$ in column $s - 1$, $k_2$ in column $r - 1$ and $0$ elsewhere, and whose entry in row
$a \ge 1$ and column $b$ is $1$ if $a = b + 1$ and $0$ otherwise. For $1 \le \ell \le r$ let
$v^{(\ell)}$ be the solution of the $([k]; p; s)$-Padovan–Perrin recurrence with
$v^{(\ell)}(m) = 1$ if $m + 1 = \ell$ and $v^{(\ell)}(m) = 0$ otherwise, for $0 \le m < r$. Then
for every $n \ge 0$ and all $0 \le i, j \le r - 1$,
$$(A^n)_{ij} = v^{(r - j)}(n + r - 1 - i).$$

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Theorem 1, equations (5) and (9) (`integers-2024-A49-thm-1`). -/
theorem padovanPerrin_companion_pow_apply [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (hp : 0 < p) (hs : 0 < s) (n : ℕ) (i j : Fin (s + p)) :
    ((Matrix.of fun a b : Fin (s + p) =>
        if (a : ℕ) = 0 then
          (if (b : ℕ) + 1 = s then k₁ else 0) + (if (b : ℕ) + 1 = s + p then k₂ else 0)
        else if (a : ℕ) = (b : ℕ) + 1 then 1 else 0) ^ n) i j =
      padovanPerrinFundamental k₁ k₂ p s (s + p - j) (n + (s + p) - 1 - i) := by
  let v := padovanPerrinFundamental k₁ k₂ p s (s + p - j)
  change _ = v _
  induction n generalizing i with
  | zero =>
    dsimp only [v]
    rw [pow_zero, Matrix.one_apply, padovanPerrinFundamental_of_lt _ _ _ _ _ _ (by omega)]
    have hij : i = j ↔ s + p - 1 - (i : ℕ) + 1 = s + p - (j : ℕ) := by
      rw [Fin.ext_iff]
      omega
    simp only [Nat.zero_add, hij]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [Matrix.of_apply, ih]
    let f (b : ℕ) := v (n + (s + p) - 1 - b)
    by_cases hi : (i : ℕ) = 0
    · -- The first row computes the next term from the two recurrence coefficients.
      simp only [hi, ↓reduceIte, add_mul, Finset.sum_add_distrib]
      rw [sum_at_predecessor hs (Nat.le_add_right s p) k₁ f,
        sum_at_predecessor (Nat.add_pos_right s hp) le_rfl k₂ f]
      have hv := (padovanPerrinRecurrence_isSolution_iff k₁ k₂ p s hs v).mp
        (padovanPerrinFundamental_isSolution k₁ k₂ p s (s + p - j)) n
      simpa only [f, show n + (s + p) - 1 - (s - 1) = n + p by omega,
        show n + (s + p) - 1 - (s + p - 1) = n by omega, Nat.sub_zero,
        show n + 1 + (s + p) - 1 = n + (s + p) by omega] using hv.symm
    · -- Each other row copies its predecessor.
      simp only [hi, ↓reduceIte, eq_comm (a := (i : ℕ)) (b := _ + 1)]
      rw [sum_at_predecessor (Nat.pos_of_ne_zero hi) i.isLt.le 1 f, one_mul]
      exact congrArg v (by omega)

end MetaMathlibExt
