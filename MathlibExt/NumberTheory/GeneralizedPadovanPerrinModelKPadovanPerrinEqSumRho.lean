/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinCompanion

/-!
# Combinatorial formula for the `k`-Padovan–Perrin numbers

For the `(k; 1; 2)`-Padovan–Perrin recurrence `v (n + 3) = v (n + 1) + k * v n`, every solution
satisfies, for `n ≥ 3`, `v n = ρ n * (k * v 0 + v 1) + (k * v 1 + v 2) * ρ (n - 1) +
k * v 2 * ρ (n - 2)` with `ρ = padovanPerrinRho 1 k 1 2` (`kPadovanPerrin_eq_sum_rho`).
Both sides satisfy the same recurrence for `n ≥ 3` and agree at `3`, `4` and `5`.

## References

* Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
  *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*,
  INTEGERS 24 (2024), Article A49.
-/

@[expose] public section

namespace MetaMathlibExt

variable {R : Type*}

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
public theorem kPadovanPerrin_eq_sum_rho [CommRing R] (k : R) (v : ℕ → R)
    (hv : (padovanPerrinRecurrence 1 k 1 2).IsSolution v) (n : ℕ) (hn : 3 ≤ n) :
    v n = padovanPerrinRho 1 k 1 2 n * (k * v 0 + v 1) +
      (k * v 1 + v 2) * padovanPerrinRho 1 k 1 2 (n - 1) +
        k * v 2 * padovanPerrinRho 1 k 1 2 (n - 2) := by
  have hv3 : ∀ t, v (t + 3) = v (t + 1) + k * v t := by
    intro t
    have h := (padovanPerrinRecurrence_isSolution_iff 1 k 1 2 two_pos v).mp hv t
    rw [one_mul] at h
    exact h
  have hrho : ∀ t, padovanPerrinRho 1 k 1 2 (t + 4) =
      padovanPerrinRho 1 k 1 2 (t + 2) + k * padovanPerrinRho 1 k 1 2 (t + 1) := by
    intro t
    have h := padovanPerrinRho_add_succ 1 k 1 2 t two_pos
    rw [one_mul] at h
    exact h
  have h0 : padovanPerrinRho 1 k 1 2 0 = 0 :=
    padovanPerrinRho_of_lt 1 k 1 2 0 (by omega)
  have h1 : padovanPerrinRho 1 k 1 2 1 = 0 :=
    padovanPerrinRho_of_lt 1 k 1 2 1 (by omega)
  have h2 : padovanPerrinRho 1 k 1 2 2 = 0 :=
    padovanPerrinRho_of_lt 1 k 1 2 2 (by omega)
  have h3 : padovanPerrinRho 1 k 1 2 3 = 1 :=
    padovanPerrinRho_self 1 k 1 2 two_pos
  have h4 : padovanPerrinRho 1 k 1 2 4 = 0 := by
    have e : padovanPerrinRho 1 k 1 2 4 =
        padovanPerrinRho 1 k 1 2 2 + k * padovanPerrinRho 1 k 1 2 1 := hrho 0
    rw [e, h2, h1, mul_zero, add_zero]
  have h5 : padovanPerrinRho 1 k 1 2 5 = 1 := by
    have e : padovanPerrinRho 1 k 1 2 5 =
        padovanPerrinRho 1 k 1 2 3 + k * padovanPerrinRho 1 k 1 2 2 := hrho 1
    rw [e, h3, h2, mul_zero, add_zero]
  have v3 : v 3 = v 1 + k * v 0 := hv3 0
  have v4 : v 4 = v 2 + k * v 1 := hv3 1
  have v5 : v 5 = v 3 + k * v 2 := hv3 2
  have b3 : v 3 = padovanPerrinRho 1 k 1 2 3 * (k * v 0 + v 1) +
      (k * v 1 + v 2) * padovanPerrinRho 1 k 1 2 2 +
        k * v 2 * padovanPerrinRho 1 k 1 2 1 := by
    rw [v3, h3, h2, h1]
    ring
  have b4 : v 4 = padovanPerrinRho 1 k 1 2 4 * (k * v 0 + v 1) +
      (k * v 1 + v 2) * padovanPerrinRho 1 k 1 2 3 +
        k * v 2 * padovanPerrinRho 1 k 1 2 2 := by
    rw [v4, h4, h3, h2]
    ring
  have b5 : v 5 = padovanPerrinRho 1 k 1 2 5 * (k * v 0 + v 1) +
      (k * v 1 + v 2) * padovanPerrinRho 1 k 1 2 4 +
        k * v 2 * padovanPerrinRho 1 k 1 2 3 := by
    rw [v5, v3, h5, h4, h3]
    ring
  have key : ∀ t : ℕ,
      (v (t + 3) = padovanPerrinRho 1 k 1 2 (t + 3) * (k * v 0 + v 1) +
        (k * v 1 + v 2) * padovanPerrinRho 1 k 1 2 (t + 2) +
          k * v 2 * padovanPerrinRho 1 k 1 2 (t + 1)) ∧
      (v (t + 4) = padovanPerrinRho 1 k 1 2 (t + 4) * (k * v 0 + v 1) +
        (k * v 1 + v 2) * padovanPerrinRho 1 k 1 2 (t + 3) +
          k * v 2 * padovanPerrinRho 1 k 1 2 (t + 2)) ∧
      (v (t + 5) = padovanPerrinRho 1 k 1 2 (t + 5) * (k * v 0 + v 1) +
        (k * v 1 + v 2) * padovanPerrinRho 1 k 1 2 (t + 4) +
          k * v 2 * padovanPerrinRho 1 k 1 2 (t + 3)) := by
    intro t
    induction t with
    | zero => exact ⟨b3, b4, b5⟩
    | succ t ih =>
      obtain ⟨ih3, ih4, ih5⟩ := ih
      refine ⟨ih4, ih5, ?_⟩
      have vt : v (t + 6) = v (t + 4) + k * v (t + 3) := hv3 (t + 3)
      have rt6 : padovanPerrinRho 1 k 1 2 (t + 6) =
          padovanPerrinRho 1 k 1 2 (t + 4) + k * padovanPerrinRho 1 k 1 2 (t + 3) :=
        hrho (t + 2)
      have rt5 : padovanPerrinRho 1 k 1 2 (t + 5) =
          padovanPerrinRho 1 k 1 2 (t + 3) + k * padovanPerrinRho 1 k 1 2 (t + 2) :=
        hrho (t + 1)
      have rt4 : padovanPerrinRho 1 k 1 2 (t + 4) =
          padovanPerrinRho 1 k 1 2 (t + 2) + k * padovanPerrinRho 1 k 1 2 (t + 1) :=
        hrho t
      have goal6 : v (t + 6) = padovanPerrinRho 1 k 1 2 (t + 6) * (k * v 0 + v 1) +
          (k * v 1 + v 2) * padovanPerrinRho 1 k 1 2 (t + 5) +
            k * v 2 * padovanPerrinRho 1 k 1 2 (t + 4) := by
        rw [vt, ih4, ih3, rt6, rt5, rt4]
        ring
      exact goal6
  obtain ⟨hmain, -, -⟩ := key (n - 3)
  have e1 : (n - 3) + 3 = n := by omega
  have e2 : (n - 3) + 2 = n - 1 := by omega
  have e3 : (n - 3) + 1 = n - 2 := by omega
  rw [e1, e2, e3] at hmain
  exact hmain

end MetaMathlibExt
