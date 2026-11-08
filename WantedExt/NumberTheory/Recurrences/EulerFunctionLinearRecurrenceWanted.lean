/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
Statements from Luca and Manape on the Euler function of linearly recurrent sequences.

A sequence `(U_n)_{n ≥ 1}` is encoded as `U : ℕ → R` whose shift `fun n => U (n + 1)` solves a
Mathlib `LinearRecurrence R` `E`; `U 0` is unused. Following the paper, `E` is taken of minimal
order, and nondegeneracy says that `0` is not a root of the characteristic polynomial and no
quotient of two distinct roots is a root of unity.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- Minimal order of `φ(n)` and maximal order of `σ(n)`: for `n ≥ 3`,
`φ(n)/n ≫ 1/log log n` and `σ(n)/n ≪ log log n`.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 1 (`fq-2024-luca09162024rev2-lem-1`),
quoted from Hardy and Wright, Theorems 323, 328 and 329. -/
public theorem_wanted totient_div_gg_and_sigma_div_ll_log_log :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
        C / Real.log (Real.log n) ≤ (Nat.totient n : ℝ) / n) ∧
      ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
        (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ C * Real.log (Real.log n)

/-- Brun sieve bound: uniformly for `x ≥ y ≥ 2`, the number `Φ(x, y)` of positive `n ≤ x` whose
least prime factor `p(n)` exceeds `y` (with `p(1) = 1`, as `Nat.minFac 1 = 1`) is `≪ x / log y`.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 2 (`fq-2024-luca09162024rev2-lem-2`),
quoted from Tenenbaum, page 397. -/
public theorem_wanted card_minFac_gt_le_div_log :
    ∃ C : ℝ, ∀ x y : ℝ, 2 ≤ y → y ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => y < (Nat.minFac n : ℝ))).card ≤
        C * x / Real.log y

/-- For `x ≥ 10`, the number of positive `n ≤ x` with `Ω(n) ≥ 10 log log x` is
`O(x / (log x)²)`.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 3 (`fq-2024-luca09162024rev2-lem-3`). -/
public theorem_wanted card_cardFactors_ge_ten_log_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 10 ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          10 * Real.log (Real.log x) ≤ (ArithmeticFunction.cardFactors n : ℝ))).card ≤
        C * x / Real.log x ^ 2

/-- For `x ≥ 10`, the number of positive `n ≤ x` with `τ(σ(n)) > exp(√(log x))` is
`O(x / (log x)²)`.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 4 (`fq-2024-luca09162024rev2-lem-4`). -/
public theorem_wanted card_divisors_sigma_gt_exp_sqrt_log_le :
    ∃ C : ℝ, ∀ x : ℝ, 10 ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          Real.exp (Real.sqrt (Real.log x)) <
            ((Nat.divisors (ArithmeticFunction.sigma 1 n)).card : ℝ))).card ≤
        C * x / Real.log x ^ 2

/-- Schmidt's zero bound: a nondegenerate complex linearly recurrent sequence `(U_n)_{n ≥ 1}` of
(minimal) order `k ≥ 2` has finitely many zeros, at most `exp(exp(exp(3k log k)))`.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Theorem 3 (`fq-2024-luca09162024rev2-thm-3`), quoted from Schmidt. -/
public theorem_wanted zero_set_card_le_exp_exp_exp (E : LinearRecurrence ℂ) (U : ℕ → ℂ)
    (hU : E.IsSolution (fun n => U (n + 1)))
    (hmin : ∀ E' : LinearRecurrence ℂ, E'.IsSolution (fun n => U (n + 1)) → E.order ≤ E'.order)
    (hnd : ∀ α β : ℂ, E.charPoly.IsRoot α → E.charPoly.IsRoot β →
      α ≠ 0 ∧ (α ≠ β → ∀ m : ℕ, 0 < m → (α / β) ^ m ≠ 1))
    (hk : 2 ≤ E.order) :
    {n : ℕ | 1 ≤ n ∧ U n = 0}.Finite ∧
      ({n : ℕ | 1 ≤ n ∧ U n = 0}.ncard : ℝ) ≤
        Real.exp (Real.exp (Real.exp (3 * E.order * Real.log E.order)))

/-- Small values of a nondegenerate integer linearly recurrent sequence with `s ≥ 2` distinct
characteristic roots: if `α₁` is a root of maximal modulus, there are `c ∈ (0, 1/3)` and `x₀` such
that for `x ≥ x₀` the number of positive `n ≤ x` with `|U_n| ≤ |α₁|^{n(1 - δ)}`, `δ = x^{-c}`,
is `O_U(√x)`.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Lemma 5 (`fq-2024-luca09162024rev2-lem-5`). -/
public theorem_wanted card_abs_le_dominant_root_pow_le_sqrt (E : LinearRecurrence ℤ)
    (U : ℕ → ℤ) (hU : E.IsSolution (fun n => U (n + 1)))
    (hmin : ∀ E' : LinearRecurrence ℤ, E'.IsSolution (fun n => U (n + 1)) → E.order ≤ E'.order)
    (hnd : ∀ α β : ℂ, (E.charPoly.map (Int.castRingHom ℂ)).IsRoot α →
      (E.charPoly.map (Int.castRingHom ℂ)).IsRoot β →
      α ≠ 0 ∧ (α ≠ β → ∀ m : ℕ, 0 < m → (α / β) ^ m ≠ 1))
    (hs : ∃ α β : ℂ, (E.charPoly.map (Int.castRingHom ℂ)).IsRoot α ∧
      (E.charPoly.map (Int.castRingHom ℂ)).IsRoot β ∧ α ≠ β)
    (α₁ : ℂ) (hα₁ : (E.charPoly.map (Int.castRingHom ℂ)).IsRoot α₁)
    (hmax : ∀ β : ℂ, (E.charPoly.map (Int.castRingHom ℂ)).IsRoot β → ‖β‖ ≤ ‖α₁‖) :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 3 ∧ ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          (|U n| : ℝ) ≤ ‖α₁‖ ^ ((n : ℝ) * (1 - x ^ (-c))))).card ≤ C * Real.sqrt x

/-- Main theorem: if `(U_n)_{n ≥ 1}` is a nondegenerate integer linearly recurrent sequence and
`|U_n|` is not eventually a polynomial in `n`, then `φ(|U_n|) ≥ |U_{φ(n)}|` fails for
`O_U(x / log x)` positive integers `n ≤ x`, and so does `σ(|U_n|) ≤ |U_{σ(n)}|`.

Source: Florian Luca and Makoko Campbell Manape, *On the Euler Function of Linearly Recurrence
Sequences*, Fibonacci Quarterly 62 (2024), Article 62-4/luca09162024rev2,
Theorem 1 (`fq-2024-luca09162024rev2-thm-1`). -/
public theorem_wanted card_totient_sigma_inequality_fails_le_div_log (E : LinearRecurrence ℤ)
    (U : ℕ → ℤ) (hU : E.IsSolution (fun n => U (n + 1)))
    (hmin : ∀ E' : LinearRecurrence ℤ, E'.IsSolution (fun n => U (n + 1)) → E.order ≤ E'.order)
    (hnd : ∀ α β : ℂ, (E.charPoly.map (Int.castRingHom ℂ)).IsRoot α →
      (E.charPoly.map (Int.castRingHom ℂ)).IsRoot β →
      α ≠ 0 ∧ (α ≠ β → ∀ m : ℕ, 0 < m → (α / β) ^ m ≠ 1))
    (hpoly : ¬ ∃ P : Polynomial ℚ, ∀ᶠ n in atTop, ((|U n| : ℤ) : ℚ) = P.eval (n : ℚ)) :
    ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          ((Nat.totient (U n).natAbs : ℕ) : ℤ) < |U (Nat.totient n)|)).card ≤
          C * x / Real.log x ∧
        ((Finset.Icc 1 ⌊x⌋₊).filter (fun n =>
          |U (ArithmeticFunction.sigma 1 n)| <
            ((ArithmeticFunction.sigma 1 (U n).natAbs : ℕ) : ℤ))).card ≤
          C * x / Real.log x

end

end MetaMathlibExt
