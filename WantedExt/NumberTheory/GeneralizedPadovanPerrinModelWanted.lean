/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Matrix.Mul

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Simple roots of the Padovan–Perrin characteristic polynomial.** Let $k_1, k_2, p, s$ be
natural numbers with $k_1 > 0$, $p \ge 2$, $p < s$ and $k_1^2 < k_2$. Then the characteristic
polynomial $P(z) = z^{s+p} - k_1 z^p - k_2$ of the $([k]; p; s)$-generalized Padovan–Perrin
recurrence is separable over $\mathbb{C}$, that is, it has only simple roots.

The hypotheses force $k_2 > 0$ and $s > 0$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 4 (`integers-2024-A49-lem-4`). -/
public theorem_wanted padovanPerrin_charPoly_separable (k₁ k₂ p s : ℕ) (hk₁ : 0 < k₁)
    (hp : 2 ≤ p) (hps : p < s) (hk : k₁ ^ 2 < k₂) :
    (X ^ (s + p) - C (k₁ : ℂ) * X ^ p - C (k₂ : ℂ)).Separable

section Model

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

/-- **Padovan–Perrin coefficients.** Let $R$ be a commutative semiring, let $k_1, k_2 \in R$ and
let $p, s, n$ be natural numbers. The coefficient $\rho(n, s + p)$ attached to $k_1, k_2, p, s$ is
$0$ when $n < s + p$; when $n \ge s + p$ it is the sum of $\binom{a + b}{a} k_1^a k_2^b$ over all
pairs of natural numbers $a, b \le n$ with $s a + (s + p) b = n - (s + p)$. For $s > 0$ the bounds
$a, b \le n$ hold automatically.

For $s > 0$ this is the coefficient $\rho(n, r)$, $r = s + p$, of the paper's general formula (12)
for the recurrence $v_n = k_1 v_{n-s} + k_2 v_{n-s-p}$. The paper's Proposition 4 prints the
constraint as $s a + (s + p) b = n - (s + p - 1)$, which contradicts its own normalization
$\rho(s + p, s + p) = 1$ for $s \ge 2$; the constraint used here is the one of formula (12).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (12) and Proposition 4. -/
def padovanPerrinRho [CommSemiring R] (k₁ k₂ : R) (p s n : ℕ) : R :=
  if n < s + p then 0 else
    ∑ ab ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun ab => s * ab.1 + (s + p) * ab.2 = n - (s + p)),
      (Nat.choose (ab.1 + ab.2) ab.1 : R) * k₁ ^ ab.1 * k₂ ^ ab.2

/-- **The Padovan–Perrin coefficients vanish below the order.** Let $R$ be a commutative
semiring, let $k_1, k_2 \in R$ and let $p, s, n$ be natural numbers with $n < s + p$. Then the
Padovan–Perrin coefficient $\rho(n, s + p)$ attached to $k_1, k_2, p, s$ equals $0$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 4. -/
theorem padovanPerrinRho_of_lt [CommSemiring R] (k₁ k₂ : R) (p s n : ℕ) (hn : n < s + p) :
    padovanPerrinRho k₁ k₂ p s n = 0 := by
  simp [padovanPerrinRho, hn]

/-- **Normalization of the Padovan–Perrin coefficients.** Let $R$ be a commutative semiring, let
$k_1, k_2 \in R$ and let $p, s$ be natural numbers with $s > 0$. Then the Padovan–Perrin
coefficient $\rho(s + p, s + p)$ attached to $k_1, k_2, p, s$ equals $1$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 4. -/
theorem padovanPerrinRho_self [CommSemiring R] (k₁ k₂ : R) (p s : ℕ) (hs : 0 < s) :
    padovanPerrinRho k₁ k₂ p s (s + p) = 1 := by
  rw [padovanPerrinRho, Nat.sub_self]
  simp only [lt_irrefl, ↓reduceIte]
  rw [Finset.sum_eq_single (0, 0)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    simp only [Finset.mem_filter] at hab
    exfalso
    apply hne
    have ha : a = 0 := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exact h
      · nlinarith [hab.2]
    have hb : b = 0 := by
      rcases Nat.eq_zero_or_pos b with h | h
      · exact h
      · nlinarith [hab.2]
    simp [ha, hb]
  · intro h
    exfalso
    apply h
    simp

/-- **Recurrence for the generalized Padovan–Perrin coefficients ρ.** Let $R$ be a commutative
semiring, $k_1, k_2 \in R$, and $p, s \in \mathbb{N}$ with $s > 0$, and write $\rho(m, s+p)$ for
the Padovan–Perrin coefficient. For every $n \ge 0$,

$$\rho(n + s + p + 1, s + p) = k_1 \, \rho(n + p + 1, s + p) + k_2 \, \rho(n + 1, s + p),$$

that is, $\rho(m, s+p) = k_1 \rho(m - s, s+p) + k_2 \rho(m - s - p, s+p)$ for every $m > s + p$.

Together with $\rho(m, s+p) = 0$ for $m < s + p$ and $\rho(s+p, s+p) = 1$, this determines $\rho$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (12) and Proposition 4. -/
theorem padovanPerrinRho_add_succ [CommSemiring R] (k₁ k₂ : R) (p s n : ℕ) (hs : 0 < s) :
    padovanPerrinRho k₁ k₂ p s (n + (s + p) + 1) =
      k₁ * padovanPerrinRho k₁ k₂ p s (n + p + 1) + k₂ * padovanPerrinRho k₁ k₂ p s (n + 1) := by
  set r := s + p with hr
  have hr1 : 0 < r := by omega
  let c : ℕ → ℕ → R := fun a b => (Nat.choose (a + b) a : R) * k₁ ^ a * k₂ ^ b
  let box : ℕ → ℕ → ℕ → R := fun A B m =>
    ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, if s * a + r * b = m then c a b else 0
  have hrho : ∀ N, r ≤ N → padovanPerrinRho k₁ k₂ p s N = box (N + 1) (N + 1) (N - r) := by
    intro N hN
    simp only [padovanPerrinRho, ← hr, not_lt.2 hN, ite_false, box, c]
    rw [Finset.sum_filter, Finset.sum_product]
  have hbox : ∀ A B m, m < A → m < B → box A B m = box (m + 1) (m + 1) m := by
    intro A B m hA hB
    have inner : ∀ a, (∑ b ∈ Finset.range B, if s * a + r * b = m then c a b else 0) =
        ∑ b ∈ Finset.range (m + 1), if s * a + r * b = m then c a b else 0 := by
      intro a
      symm
      apply Finset.sum_subset (Finset.range_subset_range.2 hB)
      intro b _ hb
      simp only [Finset.mem_range, not_lt] at hb
      rw [ite_eq_right_iff]
      intro h
      exfalso
      nlinarith
    simp only [box, inner]
    symm
    apply Finset.sum_subset (Finset.range_subset_range.2 hA)
    intro a _ ha
    simp only [Finset.mem_range, not_lt] at ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right_iff]
    intro h
    exfalso
    nlinarith
  have pascal : ∀ a b, a + b ≠ 0 → c a b =
      (if 0 < a then k₁ * c (a - 1) b else 0) + (if 0 < b then k₂ * c a (b - 1) else 0) := by
    intro a b hab
    rcases a with _ | a <;> rcases b with _ | b
    · simp at hab
    · simp [c, pow_succ]
      ring
    · simp [c, pow_succ]
      ring
    · have e1 : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
      have e2 : a + 1 + b = a + b + 1 := by omega
      have e3 : a + (b + 1) = a + b + 1 := by omega
      simp only [c, e1, e2, e3, Nat.choose_succ_succ, Nat.cast_add, Nat.succ_pos, ite_true,
        Nat.add_sub_cancel, pow_succ]
      ring
  have step : ∀ M m, box (M + 1) (M + 1) (m + 1) =
      k₁ * (if s ≤ m + 1 then box M (M + 1) (m + 1 - s) else 0) +
        k₂ * (if r ≤ m + 1 then box (M + 1) M (m + 1 - r) else 0) := by
    intro M m
    have e : ∀ a b, (if s * a + r * b = m + 1 then c a b else 0) =
        (if s * a + r * b = m + 1 then (if 0 < a then k₁ * c (a - 1) b else 0) else 0) +
        (if s * a + r * b = m + 1 then (if 0 < b then k₂ * c a (b - 1) else 0) else 0) := by
      intro a b
      by_cases h : s * a + r * b = m + 1
      · simp only [h, ite_true]
        apply pascal
        intro h0
        obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
        simp at h
      · simp [h]
    have part1 : (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
        if s * a + r * b = m + 1 then (if 0 < a then k₁ * c (a - 1) b else 0) else 0) =
        k₁ * (if s ≤ m + 1 then box M (M + 1) (m + 1 - s) else 0) := by
      rw [Finset.sum_range_succ']
      simp only [lt_irrefl, ite_false, ite_self, Finset.sum_const_zero, add_zero, Nat.succ_pos,
        ite_true, Nat.add_sub_cancel]
      split_ifs with hsm
      · simp only [box, Finset.mul_sum, mul_ite, mul_zero]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have : s * (a + 1) + r * b = (s * a + r * b) + s := by ring
        rw [this]
        congr 1
        apply propext
        omega
      · rw [mul_zero]
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right_iff]
        intro h
        exfalso
        nlinarith
    have part2 : (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
        if s * a + r * b = m + 1 then (if 0 < b then k₂ * c a (b - 1) else 0) else 0) =
        k₂ * (if r ≤ m + 1 then box (M + 1) M (m + 1 - r) else 0) := by
      refine (Finset.sum_congr rfl fun a _ => Finset.sum_range_succ' _ _).trans ?_
      simp only [lt_irrefl, ite_false, ite_self, add_zero, Nat.succ_pos,
        ite_true, Nat.add_sub_cancel]
      split_ifs with hrm
      · simp only [box, Finset.mul_sum, mul_ite, mul_zero]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        have : s * a + r * (b + 1) = (s * a + r * b) + r := by ring
        rw [this]
        congr 1
        apply propext
        omega
      · rw [mul_zero]
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right_iff]
        intro h
        exfalso
        nlinarith
    simp only [box]
    simp_rw [e, Finset.sum_add_distrib]
    rw [part1, part2]
  -- assemble
  rw [hrho _ (by omega)]
  have h1 : n + r + 1 - r = n + 1 := by omega
  rw [h1, step]
  congr 1
  · by_cases hsn : s ≤ n + 1
    · have h2 : n + p + 1 - r = n + 1 - s := by omega
      simp only [hsn, ite_true]
      rw [hrho _ (by omega), h2,
        hbox _ _ _ (by omega) (by omega), hbox (n + p + 1 + 1) _ _ (by omega) (by omega)]
    · simp only [hsn, ite_false, mul_zero, padovanPerrinRho,
        show n + p + 1 < s + p by omega, ite_true]
  · by_cases hrn : r ≤ n + 1
    · simp only [hrn, ite_true]
      rw [hrho _ hrn, hbox _ _ _ (by omega) (by omega),
        hbox (n + 1 + 1) _ _ (by omega) (by omega)]
    · simp only [hrn, ite_false, mul_zero, padovanPerrinRho,
        show n + 1 < s + p by omega, ite_true]

/-- **The Padovan–Perrin coefficient $\rho(12, 3)$ equals $5$.** Over the integers, with
$k_1 = k_2 = 1$, $p = 1$ and $s = 2$ (the Padovan–Perrin recurrence $v_n = v_{n-2} + v_{n-3}$),
the coefficient $\rho(12, 3)$ equals $5$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, equation (14) and Table 1. -/
theorem padovanPerrinRho_one_one_one_two_twelve : padovanPerrinRho (1 : ℤ) 1 1 2 12 = 5 := by
  decide

/-- **Expansion in the Fibonacci fundamental system.** Let $R$ be a commutative ring, let
$k_1, k_2 \in R$ and $p, s \in \mathbb{N}$, and for $1 \le j \le s + p$ let $v^{(j)}$ be the
solution of the $([k]; p; s)$-Padovan–Perrin recurrence with $v^{(j)}(m) = 1$ if $m + 1 = j$ and
$v^{(j)}(m) = 0$ otherwise, for $0 \le m < s + p$. Then every solution $v \colon \mathbb{N} \to R$
of the recurrence satisfies, for every $n \ge 0$,
$$v(n) = \sum_{j=0}^{s+p-1} v(j)\, v^{(j+1)}(n).$$

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 1 (`integers-2024-A49-prop-1`). -/
public theorem_wanted padovanPerrin_eq_sum_fundamental [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (v : ℕ → R)
    (hv : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v) (n : ℕ) :
    v n = ∑ j ∈ Finset.range (s + p), v j * padovanPerrinFundamental k₁ k₂ p s (j + 1) n

/-- **Solutions agreeing on a window agree afterwards.** Let $R$ be a commutative ring, let
$k_1, k_2 \in R$, let $p, s$ be natural numbers and let $v, w \colon \mathbb{N} \to R$ be solutions
of the Padovan–Perrin recurrence with parameters $k_1, k_2, p, s$. Let $n_0, m_0, N$ be natural
numbers such that $v(j + n_0) = w(j + m_0)$ for every $j$ with $N \le j < N + s + p$. Then
$v(n + n_0) = w(n + m_0)$ for every $n \ge N$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 1 (`integers-2024-A49-lem-1`). -/
public theorem_wanted padovanPerrin_shift_eq_of_window [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    {v w : ℕ → R}
    (hv : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v)
    (hw : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution w) (n₀ m₀ N : ℕ)
    (h : ∀ j, N ≤ j → j < N + (s + p) → v (j + n₀) = w (j + m₀)) :
    ∀ n, N ≤ n → v (n + n₀) = w (n + m₀)

/-- **The Fibonacci fundamental system spans the solutions.** Let $R$ be a commutative ring, let
$k_1, k_2 \in R$ and let $p, s$ be natural numbers. For $1 \le j \le s + p$ let $v^{(j)}$ be the
solution of the Padovan–Perrin recurrence with parameters $k_1, k_2, p, s$ whose initial values
are $v^{(j)}(n) = 1$ if $n + 1 = j$ and $v^{(j)}(n) = 0$ otherwise, for $n < s + p$. Then the
submodule of $R^{\mathbb{N}}$ formed by all solutions of this recurrence is the submodule spanned
by $v^{(1)}, \dots, v^{(s+p)}$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Corollary 1 (`integers-2024-A49-cor-1`). -/
public theorem_wanted padovanPerrin_solSpace_eq_span_fundamental [CommRing R] (k₁ k₂ : R)
    (p s : ℕ) :
    (padovanPerrinRecurrence k₁ k₂ p s).solSpace =
      Submodule.span R
        (Set.range fun j : Fin (s + p) => padovanPerrinFundamental k₁ k₂ p s ((j : ℕ) + 1))

/-- **Shift property of the generalized Padovan–Perrin fundamental system.** Let $R$ be a
commutative ring, $k_1, k_2 \in R$, and let $p, s, j$ be natural numbers with $p \ge 1$ and
$p + 1 \le j \le s + p - 1$. Write $v^{(\ell)}$ for the $\ell$-th sequence of the Fibonacci
fundamental system of the $([k]; p; s)$-Padovan–Perrin recurrence. Then
$v^{(j)}_n = v^{(s+p)}_{n+s+p-j}$ for every $n \ge 0$, and
$v^{(j)}_n = k_1 v^{(s+p)}_{n-j+p} + k_2 v^{(s+p)}_{n-j}$ for every $n \ge j$.

The paper's second clause, $v^{(j)}_n = k_2 v^{(s+p)}_{n+j}$ for $1 \le j \le p$, is omitted: it
fails for $k_1 = k_2 = 1$, $p = 1$, $s = 2$, $j = 1$, $n = 0$, where $v^{(1)}_0 = 1$ but
$v^{(3)}_1 = 0$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 2 (`integers-2024-A49-prop-2`). -/
public theorem_wanted padovanPerrinFundamental_eq_shift [CommRing R] (k₁ k₂ : R) (p s j : ℕ)
    (hp : 0 < p) (hpj : p + 1 ≤ j) (hjs : j ≤ s + p - 1) :
    (∀ n, padovanPerrinFundamental k₁ k₂ p s j n =
        padovanPerrinFundamental k₁ k₂ p s (s + p) (n + (s + p) - j)) ∧
      ∀ n, j ≤ n → padovanPerrinFundamental k₁ k₂ p s j n =
        k₁ * padovanPerrinFundamental k₁ k₂ p s (s + p) (n - j + p) +
          k₂ * padovanPerrinFundamental k₁ k₂ p s (s + p) (n - j)

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
public theorem_wanted padovanPerrin_companion_pow_apply [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (hp : 0 < p) (hs : 0 < s) (n : ℕ) (i j : Fin (s + p)) :
    ((Matrix.of fun a b : Fin (s + p) =>
        if (a : ℕ) = 0 then
          (if (b : ℕ) + 1 = s then k₁ else 0) + (if (b : ℕ) + 1 = s + p then k₂ else 0)
        else if (a : ℕ) = (b : ℕ) + 1 then 1 else 0) ^ n) i j =
      padovanPerrinFundamental k₁ k₂ p s (s + p - j) (n + (s + p) - 1 - i)

/-- **Product identity for the generalized Padovan–Perrin fundamental system.** Let $R$ be a
commutative ring, $k_1, k_2 \in R$, and $p, s \ge 1$. Write $r = s + p$ and $v^{(\ell)}$ for the
$\ell$-th sequence of the Fibonacci fundamental system of the $([k]; p; s)$-Padovan–Perrin
recurrence. Then for all $m, n \ge 0$ and all $1 \le i, j \le r$,

$$v^{(r-j+1)}_{n+m+r-i} = \sum_{k=1}^{r} v^{(r-k+1)}_{m+r-i} \, v^{(r-j+1)}_{n+r-k}.$$

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 3, equation (10) (`integers-2024-A49-prop-3`). -/
public theorem_wanted padovanPerrinFundamental_mul_sum [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (hp : 0 < p) (hs : 0 < s) (m n i j : ℕ) (hi : 1 ≤ i) (hi' : i ≤ s + p) (hj : 1 ≤ j)
    (hj' : j ≤ s + p) :
    padovanPerrinFundamental k₁ k₂ p s (s + p - j + 1) (n + m + (s + p) - i) =
      ∑ k ∈ Finset.Icc 1 (s + p),
        padovanPerrinFundamental k₁ k₂ p s (s + p - k + 1) (m + (s + p) - i) *
          padovanPerrinFundamental k₁ k₂ p s (s + p - j + 1) (n + (s + p) - k)

/-- **Combinatorial expression of the Padovan–Perrin sequences.** Let $R$ be a commutative ring,
let $k_1, k_2 \in R$, let $p, s$ be positive integers, and let $v \colon \mathbb{N} \to R$ satisfy
$v(n + s + p) = k_1 v(n + p) + k_2 v(n)$ for every $n$. For $0 \le m \le s + p - 1$ put
$A_m = k_2 v(m) + k_1 v(m + p)$ if $m < s$ and $A_m = k_2 v(m)$ if $m \ge s$. Let $\rho(N, s + p)$
be the Padovan–Perrin coefficient: $0$ for $N < s + p$, and for $N \ge s + p$ the sum of
$\binom{a+b}{a} k_1^a k_2^b$ over all $a, b \ge 0$ with $s a + (s + p) b = N - (s + p)$. Then for
every $n \ge s + p$,
$$v(n) = \sum_{m=0}^{s+p-1} \rho(n - m, s + p)\, A_m.$$

The paper prints the constraint in $\rho$ as $s a + (s + p) b = N - (s + p - 1)$, and with it the
identity fails (for $k_1 = k_2 = 1$, $p = 1$, $s = 2$ the printed $\rho(4, 3)$ is $1$ instead of
$0$); the constraint used here is the one of the paper's general formula (12).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Theorem 3 (`integers-2024-A49-thm-3`). -/
public theorem_wanted padovanPerrin_eq_sum_rho [CommRing R] (k₁ k₂ : R) (p s : ℕ) (hp : 0 < p)
    (hs : 0 < s) (v : ℕ → R) (hv : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v) (n : ℕ)
    (hn : s + p ≤ n) :
    v n = ∑ m ∈ Finset.range (s + p), padovanPerrinRho k₁ k₂ p s (n - m) *
      (k₂ * v m + if m < s then k₁ * v (m + p) else 0)

/-- **The last generalized Padovan–Perrin fundamental sequence is a shifted ρ.** Let $R$ be a
commutative ring, $k_1, k_2 \in R$, and $p, s \ge 1$. Write $v^{(s+p)}$ for the $(s+p)$-th
sequence of the Fibonacci fundamental system of the $([k]; p; s)$-Padovan–Perrin recurrence and
$\rho(m, s+p)$ for the Padovan–Perrin coefficient. Then $v^{(s+p)}_n = \rho(n + 1, s + p)$ for
every $n \ge s + p$.

Here $\rho(m, s+p)$ sums over $a, b \ge 0$ with $sa + (s+p)b = m - (s+p)$, the constraint of
formula (12). With the printed constraint $m - (s + p - 1)$ the identity fails, e.g. for
$k_1 = k_2 = 1$, $p = 1$, $s = 2$, $n = 3$, where $v^{(3)}_3 = 0$ but the printed
$\rho(4, 3)$ is $1$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 4 (`integers-2024-A49-prop-4`). -/
public theorem_wanted padovanPerrinFundamental_last_eq_rho [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (hp : 0 < p) (hs : 0 < s) (n : ℕ) (hn : s + p ≤ n) :
    padovanPerrinFundamental k₁ k₂ p s (s + p) n = padovanPerrinRho k₁ k₂ p s (n + 1)

/-- **Fundamental Padovan–Perrin solutions as shifted coefficients $\rho$.** Let $R$ be a
commutative ring, let $k_1, k_2 \in R$, let $p \ge 1$ and $s$ be natural numbers, and let $j$
satisfy $p + 1 \le j \le s + p - 1$. For $1 \le \ell \le s + p$ let $v^{(\ell)}$ be the solution of
the $([k]; p; s)$-Padovan–Perrin recurrence with $v^{(\ell)}(m) = 1$ if $m + 1 = \ell$ and
$v^{(\ell)}(m) = 0$ otherwise, for $0 \le m < s + p$. Let $\rho(N, s + p)$ be the Padovan–Perrin
coefficient: $0$ for $N < s + p$, and for $N \ge s + p$ the sum of $\binom{a+b}{a} k_1^a k_2^b$
over all $a, b \ge 0$ with $s a + (s + p) b = N - (s + p)$. Then for every $n \ge 0$,
$$v^{(j)}(n) = v^{(s+p)}(n + s + p - j) = \rho(n + s + p - j + 1, s + p).$$

The paper's second clause $v^{(j)}(n) = k_2\,\rho(n + j + 1, s + p)$ for $1 \le j \le p$ is
omitted: it fails for $k_1 = 1$, $k_2 = 2$, $p = 1$, $s = 2$, $j = 1$, $n = 0$, where
$v^{(1)}(0) = 1$ but $2\rho(2, 3) = 0$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 5 (`integers-2024-A49-prop-5`). -/
public theorem_wanted padovanPerrinFundamental_eq_rho [CommRing R] (k₁ k₂ : R) (p s j : ℕ)
    (hp : 0 < p) (hpj : p + 1 ≤ j) (hjs : j ≤ s + p - 1) (n : ℕ) :
    padovanPerrinFundamental k₁ k₂ p s j n =
        padovanPerrinFundamental k₁ k₂ p s (s + p) (n + (s + p) - j) ∧
      padovanPerrinFundamental k₁ k₂ p s (s + p) (n + (s + p) - j) =
        padovanPerrinRho k₁ k₂ p s (n + (s + p) - j + 1)

/-- **Simple roots of the Padovan–Perrin polynomial for $p = 1$.** Let $k_1, k_2, s$ be positive
integers with $\left(-\frac{k_2 (s + 1)}{k_1 s}\right)^s \neq \frac{k_1}{s + 1}$. Then the
polynomial $P(z) = z^{s+1} - k_1 z - k_2$ is separable over $\mathbb{C}$, that is, it has only
simple roots.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 2 (`integers-2024-A49-lem-2`). -/
public theorem_wanted padovanPerrin_charPoly_separable_of_p_eq_one (k₁ k₂ s : ℕ) (hk₁ : 0 < k₁)
    (hk₂ : 0 < k₂) (hs : 0 < s)
    (h : (-(k₂ : ℚ) * (s + 1) / (k₁ * s)) ^ s ≠ k₁ / (s + 1)) :
    (X ^ (s + 1) - C (k₁ : ℂ) * X - C (k₂ : ℂ)).Separable

/-- **Root formula for the generalized Padovan–Perrin coefficients ρ.** Let $k_1, k_2$ be complex
numbers with $k_2 \neq 0$, let $p, s \ge 1$, and let $P(z) = z^{s+p} - k_1 z^p - k_2$. If $P$ is
separable, that is, has $s + p$ distinct roots $\lambda_1, \dots, \lambda_{s+p}$ in $\mathbb{C}$,
then for every $n \ge s + p$ the Padovan–Perrin coefficient satisfies

$$\rho(n, s + p) = \sum_{i=1}^{s+p} \frac{\lambda_i^{n-1}}{P'(\lambda_i)}.$$

The paper states this for the general $\rho$ of formula (12) attached to an arbitrary
characteristic polynomial $z^r - a_0 z^{r-1} - \cdots - a_{r-1}$; this is its specialization to
the $([k]; p; s)$-Padovan–Perrin coefficients, the case the paper applies.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Lemma 5 (`integers-2024-A49-lem-5`). -/
public theorem_wanted padovanPerrinRho_eq_sum_roots (k₁ k₂ : ℂ) (p s : ℕ) (hp : 0 < p)
    (hs : 0 < s) (hk₂ : k₂ ≠ 0) (hsep : (X ^ (s + p) - C k₁ * X ^ p - C k₂).Separable) (n : ℕ)
    (hn : s + p ≤ n) :
    padovanPerrinRho k₁ k₂ p s n =
      ((X ^ (s + p) - C k₁ * X ^ p - C k₂).roots.map fun x =>
        x ^ (n - 1) / (derivative (X ^ (s + p) - C k₁ * X ^ p - C k₂)).eval x).sum

/-- **Analytic expression of the Padovan–Perrin sequences.** Let $k_1, k_2, p, s$ be natural
numbers with $k_1 > 0$, $p \ge 2$, $p < s$ and $k_1^2 < k_2$, let
$P(z) = z^{s+p} - k_1 z^p - k_2$, and let $v \colon \mathbb{N} \to \mathbb{C}$ satisfy
$v(n + s + p) = k_1 v(n + p) + k_2 v(n)$ for every $n$. For $0 \le m \le s + p - 1$ put
$A_m = k_2 v(m) + k_1 v(m + p)$ if $m < s$ and $A_m = k_2 v(m)$ if $m \ge s$. Then for every
$n \ge s + p$,
$$v(n) = \sum_{m=0}^{s+p-1} A_m \sum_{\lambda} \frac{\lambda^{n-1-m}}{P'(\lambda)},$$
where $\lambda$ runs over the complex roots of $P$ counted with multiplicity.

The paper assumes that the roots of $P$ are distinct; this follows from the other hypotheses
(Lemma 4 of the paper).

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 6 (`integers-2024-A49-prop-6`). -/
public theorem_wanted padovanPerrin_eq_sum_roots (k₁ k₂ p s : ℕ) (hk₁ : 0 < k₁) (hp : 2 ≤ p)
    (hps : p < s) (hk : k₁ ^ 2 < k₂) (v : ℕ → ℂ)
    (hv : (padovanPerrinRecurrence (k₁ : ℂ) (k₂ : ℂ) p s).IsSolution v) (n : ℕ)
    (hn : s + p ≤ n) :
    v n = ∑ m ∈ Finset.range (s + p),
      ((k₂ : ℂ) * v m + if m < s then (k₁ : ℂ) * v (m + p) else 0) *
        ((X ^ (s + p) - C (k₁ : ℂ) * X ^ p - C (k₂ : ℂ)).roots.map fun x =>
          x ^ (n - 1 - m) /
            (derivative (X ^ (s + p) - C (k₁ : ℂ) * X ^ p - C (k₂ : ℂ))).eval x).sum

/-- **Combinatorial formula for the $k$-Padovan–Perrin numbers.** Let $R$ be a commutative ring,
let $k \in R$, and let $v \colon \mathbb{N} \to R$ satisfy $v(n + 3) = v(n + 1) + k\,v(n)$ for
every $n$, that is, $v$ solves the Padovan–Perrin recurrence with $k_1 = 1$, $k_2 = k$, $p = 1$,
$s = 2$. Let $\rho(m) = \rho(m, 3)$ be the Padovan–Perrin coefficient for these parameters:
$\rho(m) = 0$ for $m < 3$, and for $m \ge 3$ it is the sum of $\binom{a+b}{a} k^b$ over all
$a, b \ge 0$ with $2a + 3b = m - 3$. Then for every $n \ge 3$,
$$v(n) = \rho(n)\,(k\,v(0) + v(1)) + (k\,v(1) + v(2))\,\rho(n - 1) + k\,v(2)\,\rho(n - 2).$$

The paper prints the middle coefficient as $k\,v(1)$; the coefficient $k\,v(1) + v(2)$ is the one
its Theorem 3 gives, and the printed form fails for $k = 2$, $(v(0), v(1), v(2)) = (0, 0, 1)$,
$n = 4$, where $v(4) = 1$ but the printed right side is $0$. The paper takes $k \ge 2$ an integer.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 8 (`integers-2024-A49-prop-8`). -/
public theorem_wanted kPadovanPerrin_eq_sum_rho [CommRing R] (k : R) (v : ℕ → R)
    (hv : (padovanPerrinRecurrence 1 k 1 2).IsSolution v) (n : ℕ) (hn : 3 ≤ n) :
    v n = padovanPerrinRho 1 k 1 2 n * (k * v 0 + v 1) +
      (k * v 1 + v 2) * padovanPerrinRho 1 k 1 2 (n - 1) +
        k * v 2 * padovanPerrinRho 1 k 1 2 (n - 2)

/-- **Fundamental $k$-Padovan–Perrin solutions as coefficients $\rho$.** Let $R$ be a commutative
ring and $k \in R$, and take the Padovan–Perrin recurrence with $k_1 = 1$, $k_2 = k$, $p = 1$,
$s = 2$, that is, $v(n + 3) = v(n + 1) + k\,v(n)$. Let $v^{(2)}$ and $v^{(3)}$ be its solutions
with initial values $(v^{(2)}(0), v^{(2)}(1), v^{(2)}(2)) = (0, 1, 0)$ and
$(v^{(3)}(0), v^{(3)}(1), v^{(3)}(2)) = (0, 0, 1)$. Let $\rho(m) = \rho(m, 3)$ be the
Padovan–Perrin coefficient for these parameters: $\rho(m) = 0$ for $m < 3$, and for $m \ge 3$ it
is the sum of $\binom{a+b}{a} k^b$ over all $a, b \ge 0$ with $2a + 3b = m - 3$. Then for every
$n \ge 0$, $v^{(3)}(n) = \rho(n + 1)$ and $v^{(2)}(n) = \rho(n + 2)$.

The paper's third formula $v^{(1)}(n) = k\,\rho(n + 2)$, for the solution $v^{(1)}$ with initial
values $(1, 0, 0)$, is omitted: it fails for $k = 2$, $n = 0$ ($v^{(1)}(0) = 1$, $2\rho(2) = 0$).
The paper takes $k \ge 2$ an integer.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 9 (`integers-2024-A49-prop-9`). -/
public theorem_wanted kPadovanPerrinFundamental_eq_rho [CommRing R] (k : R) (n : ℕ) :
    padovanPerrinFundamental 1 k 1 2 3 n = padovanPerrinRho 1 k 1 2 (n + 1) ∧
      padovanPerrinFundamental 1 k 1 2 2 n = padovanPerrinRho 1 k 1 2 (n + 2)

/-- **Root formula for the $k$-Padovan–Perrin numbers.** Let $k \ge 2$ be an integer, let
$P(z) = z^3 - z - k$, and let $v \colon \mathbb{N} \to \mathbb{C}$ satisfy
$v(n + 3) = v(n + 1) + k\,v(n)$ for every $n$, that is, $v$ solves the Padovan–Perrin recurrence
with $k_1 = 1$, $k_2 = k$, $p = 1$, $s = 2$. Put $A_0 = k\,v(0) + v(1)$, $A_1 = k\,v(1) + v(2)$
and $A_2 = k\,v(2)$. Then for every $n \ge 3$,
$$v(n) = \sum_\lambda \frac{A_0\lambda^{n-1} + A_1\lambda^{n-2} + A_2\lambda^{n-3}}{P'(\lambda)},$$
where $\lambda$ runs over the complex roots of $P$ counted with multiplicity.

Since $27 k^2 - 4 \neq 0$, the roots of $P$ are distinct. The paper prints the middle coefficient
as $k\,v(1)$; $k\,v(1) + v(2)$ is the coefficient $A_1$ of its Theorem 3, and the printed form
fails already for $k = 2$, $(v(0), v(1), v(2)) = (0, 0, 1)$, $n = 4$, where it gives $0$ while
$v(4) = 1$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 10 (`integers-2024-A49-prop-10`). -/
public theorem_wanted kPadovanPerrin_eq_sum_roots (k : ℕ) (hk : 2 ≤ k) (v : ℕ → ℂ)
    (hv : (padovanPerrinRecurrence 1 (k : ℂ) 1 2).IsSolution v) (n : ℕ) (hn : 3 ≤ n) :
    v n = ((X ^ 3 - X - C (k : ℂ)).roots.map fun x =>
      (((k : ℂ) * v 0 + v 1) * x ^ (n - 1) + ((k : ℂ) * v 1 + v 2) * x ^ (n - 2) +
          (k : ℂ) * v 2 * x ^ (n - 3)) /
        (derivative (X ^ 3 - X - C (k : ℂ))).eval x).sum

end Model

end

end MetaMathlibExt
