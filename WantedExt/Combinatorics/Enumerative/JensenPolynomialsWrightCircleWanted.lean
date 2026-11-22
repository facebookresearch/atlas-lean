/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Jensen polynomials of coefficients from Wright's circle method

Statement-only requests from Bal, Haraldson, Males and Thompson's paper on hyperbolicity of
Jensen polynomials. The Jensen polynomial of degree `d` and shift `n` of a sequence `α` is
`J_α^{d,n}(X) = ∑_{j=0}^{d} (d choose j) α(n + j) Xʲ` (Griffin, Ono, Rolen and Zagier); it is
written out in each statement. A real polynomial is hyperbolic when all of its roots are real,
written `p.roots.card = p.natDegree`.
-/

open Filter Asymptotics Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- For every real `N > 0`,
`∫₀^∞ (e^{-x} / (x (1 - e^{-Nx})) - 1 / (N x²) - (1/2 - 1/N) e^{-x} / x) dx
  = log Γ(1/N) + (1/2 - 1/N) log(1/N) - (1/2) log(2π)`.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Lemma 2 (`integers-2025-A36-lem-2`). -/
public theorem_wanted integral_exp_div_one_sub_exp_sub_eq_log_Gamma {N : ℝ} (hN : 0 < N) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Real.exp (-x) / (x * (1 - Real.exp (-(N * x)))) - 1 / (N * x ^ 2) -
          (1 / 2 - 1 / N) * Real.exp (-x) / x) =
      Real.log (Real.Gamma (1 / N)) + (1 / 2 - 1 / N) * Real.log (1 / N) -
        1 / 2 * Real.log (2 * Real.pi)

/-- For integers `1 ≤ k < p`, with `ζₚ = e^{2πi/p}`,
`∑_{α=1}^{p} ζₚ^{kα} ψ(α/p) = p Log(1 - ζₚ^k)`, where `ψ` is the digamma function and `Log` the
principal logarithm.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Lemma 3 (`integers-2025-A36-lem-3`). -/
public theorem_wanted sum_exp_mul_digamma_div_eq_mul_log_one_sub {p k : ℕ} (hk : 1 ≤ k)
    (hkp : k < p) :
    ∑ α ∈ Finset.Icc 1 p,
        Complex.exp (2 * Real.pi * Complex.I * k * α / p) * Complex.digamma (α / p) =
      p * Complex.log (1 - Complex.exp (2 * Real.pi * Complex.I * k / p))

/-- Let `α`, `A`, `δ` be sequences of positive reals with `δ(n) → 0` (all three positive as
printed in the quoted theorem), and let `d ≥ 1`. Suppose
that for `0 ≤ k ≤ d`,
`log (α(n + k) / α(n)) = A(n) k - δ(n)² k² + ∑_{j=3}^{d} g_j(n) kʲ + o(δ(n)^d)` with
`g_j(n) = o(δ(n)ʲ)`. Then the Jensen polynomial `J_α^{d,n}` is hyperbolic for all but finitely
many `n`. The convergence of the renormalized Jensen polynomials to Hermite polynomials is
omitted.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Theorem 5 (`integers-2025-A36-thm-5`), quoted there from Griffin, Ono, Rolen and
Zagier. -/
public theorem_wanted eventually_jensen_hyperbolic_of_log_ratio_expansion {α A δ : ℕ → ℝ}
    (hα : ∀ n, 0 < α n) (hA : ∀ n, 0 < A n) (hδ : ∀ n, 0 < δ n)
    (hδ0 : Tendsto δ atTop (nhds 0)) {d : ℕ} (hd : 1 ≤ d) (g : ℕ → ℕ → ℝ)
    (hg : ∀ j ∈ Finset.Icc 3 d, g j =o[atTop] fun n => δ n ^ j)
    (hexp : ∀ k ≤ d, (fun n => Real.log (α (n + k) / α n) -
        (A n * k - δ n ^ 2 * k ^ 2 + ∑ j ∈ Finset.Icc 3 d, g j n * (k : ℝ) ^ j)) =o[atTop]
      fun n => δ n ^ d) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j).natDegree

/-- Let `r ≥ 1`, `t ≥ 1` and `H_{r,t}(q) = 1/(q^t; q^t)_∞^r = ∑ c_{r,t}(n) qⁿ`. Then
`C_{r,t}(n) = c_{r,t}(tn)` is the number of `r`-colored partitions of `n` (independent of `t`),
written as `∑_{n₁ + ⋯ + n_r = n} ∏ᵢ p(nᵢ)`. For each `d ≥ 1`, the Jensen polynomial
`J_{C_{r,t}}^{d,n}` is hyperbolic for all but finitely many `n`. The Hermite-limit clause and the
higher order Turán inequalities clause are omitted.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Theorem 3, part 1 (`integers-2025-A36-thm-3`). -/
public theorem_wanted eventually_jensen_hyperbolic_coloredPartitions {r : ℕ} (hr : 1 ≤ r)
    {d : ℕ} (hd : 1 ≤ d) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) *
          ((∑ x ∈ Finset.Nat.antidiagonalTuple r (n + j),
            ∏ i, Fintype.card (Nat.Partition (x i)) : ℕ) : ℝ)) * X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) *
          ((∑ x ∈ Finset.Nat.antidiagonalTuple r (n + j),
            ∏ i, Fintype.card (Nat.Partition (x i)) : ℕ) : ℝ)) * X ^ j).natDegree

open scoped Classical in
/-- Let `p` be prime, `1 ≤ a < p`, and `G_{a,p}(q) = 1/(q^a; q^p)_∞ = ∑ b_{a,p}(n) qⁿ`, so
`b_{a,p}(n)` is the number of partitions of `n` into parts `≡ a (mod p)`. For each `d ≥ 1`, the
Jensen polynomial `J_{b_{a,p}}^{d,n}` is hyperbolic for all but finitely many `n`. The case
`a = 0` admitted by the paper is excluded (`(1; q^p)_∞ = 0`); the asymptotic formula, the
Hermite-limit clause and the higher order Turán inequalities clause are omitted.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Theorem 4, part 2 (`integers-2025-A36-thm-4`). -/
public theorem_wanted eventually_jensen_hyperbolic_partitions_parts_mod {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hap : a < p) {d : ℕ} (hd : 1 ≤ d) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) *
          ((Finset.univ.filter fun π : Nat.Partition (n + j) =>
            ∀ i ∈ π.parts, i % p = a).card : ℝ)) * X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) *
          ((Finset.univ.filter fun π : Nat.Partition (n + j) =>
            ∀ i ∈ π.parts, i % p = a).card : ℝ)) * X ^ j).natDegree

end

end MetaMathlibExt
