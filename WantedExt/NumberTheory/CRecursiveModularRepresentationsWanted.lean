/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.PowerSeries.Basic

namespace MetaMathlibExt

@[expose] public section

/--
For a natural-valued sequence whose generating-function series is summable at `c⁻¹`, if
`c ≥ 8` and `t n < c ^ (n / 3)` for every `n ≥ 1`, then every such `t n` is the remainder
modulo `c ^ n` of the floor of `c ^ (n ^ 2)` times the series evaluated at `c⁻ⁿ`.

The paper's clauses `c ≥ 8` and `n ≥ 1` are `hc` and `hn`; its growth condition is `hbound`,
where the cast to `ℝ` and real exponent `(n : ℝ) / 3` avoid natural-number division. Its
generating function is written explicitly as the infinite sum in the conclusion. The radius
condition `c⁻¹ < R` is represented by `hconv`, summability at `c⁻¹`, as in the existing
formalization of the first part of Theorem 2. Summability at that point is implied by the
paper's radius condition but is strictly weaker, so this formal statement is stronger than the
paper's result. The floor and outer modulus use `Nat.floor` and `%`, respectively.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Theorem 2, second part.
-/
public theorem_wanted generating_function_term_extraction_of_one_third_growth
    (t : ℕ → ℕ) (c : ℕ)
    (hc : 8 ≤ c)
    (hconv : Summable (fun k : ℕ => (t k : ℝ) * ((c : ℝ)⁻¹) ^ k))
    (hbound : ∀ n, 1 ≤ n → (t n : ℝ) < (c : ℝ) ^ ((n : ℝ) / 3))
    (n : ℕ) (hn : 1 ≤ n) :
    t n = Nat.floor ((c : ℝ) ^ (n ^ 2) *
      (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)) % c ^ n

/--
If the generating-function representation holds in base `c` for every `n ≥ m`, then it also
holds in every natural base `r ≥ c`. The paper's standing assumptions `2 ≤ c`, `2 ≤ m`, and
`c ≤ r` are `hc`, `hm`, and `hcr`. The base-`c` representation is `hrep`, and `hconv` states
separately that its displayed series is summable at every `c⁻ⁿ` for `n ≥ m`, so each `tsum`
denotes the genuine series value.

No growth hypothesis is added, and no convergence hypothesis at `r⁻ⁿ` is assumed. This is a
deviation in presentation needed for the explicit `tsum`: for `n ≥ m ≥ 2`, `hrep` forces
`t n < c ^ n`, and together with `c ≤ r` this makes the series at every `r⁻ⁿ` converge. The
paper's generating functions, floors, and congruences are encoded by the displayed sums,
`Nat.floor`, and equality to a natural remainder `%`, respectively.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Corollary 3.
-/
public theorem_wanted generating_function_term_representation_mono_base
    (t : ℕ → ℕ) (c m r : ℕ)
    (hc : 2 ≤ c) (hm : 2 ≤ m) (hcr : c ≤ r)
    (hrep : ∀ n, m ≤ n →
      t n = Nat.floor ((c : ℝ) ^ (n ^ 2) *
        (∑' k : ℕ, (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k)) % c ^ n)
    (hconv : ∀ n, m ≤ n →
      Summable (fun k : ℕ => (t k : ℝ) * (((c : ℝ) ^ n)⁻¹) ^ k))
    (n : ℕ) (hmn : m ≤ n) :
    t n = Nat.floor ((r : ℝ) ^ (n ^ 2) *
      (∑' k : ℕ, (t k : ℝ) * (((r : ℝ) ^ n)⁻¹) ^ k)) % r ^ n

/--
For integers `A ≥ 1` and `B ≥ 2` such that `B` does not divide `A`, negating the floor quotient
of `-A` by `B` gives the floor quotient of `A` by `B` plus one. The paper's lower bounds are
`hA` and `hB`, and its nondivisibility clause is `hndvd`. Lean's integer `/` is `Int.ediv`,
which is floor division because `hB` makes the divisor positive; thus no rational floor is
introduced. Integer negation and addition directly encode the remaining operations, with no
other deviation from the paper.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 4.
-/
public theorem_wanted neg_ediv_eq_ediv_add_one_of_not_dvd
    (A B : ℤ) (hA : 1 ≤ A) (hB : 2 ≤ B) (hndvd : ¬ B ∣ A) :
    -((-A) / B) = A / B + 1

/--
For naturals `a`, `y`, and `C`, if `a * y < C`, then reducing `a * y` modulo `C` is the same
as multiplying `a` by the reduction of `y` modulo `C`. The paper's upper bound is exactly
`hbound`, while its lower bound `0 ≤ a * y` is omitted because it is automatic in `ℕ`. The
paper's products and modular reductions are Lean multiplication and natural remainder `%`;
apart from the automatic nonnegativity clause, there is no deviation.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 5.
-/
public theorem_wanted mul_mod_eq_mul_mod_of_mul_lt
    (a y C : ℕ) (hbound : a * y < C) :
    (a * y) % C = a * (y % C)

/--
For naturals `x` and `C ≥ 2`, if `x` is not congruent to `C - 1` modulo `C`, then incrementing
`x` increments its remainder without wrapping: `(x + 1) % C = x % C + 1`. The paper's bound
on `C` is `hC`. Its incongruence clause is `hne`, expressed as inequality of the natural
remainders `x % C` and `(C - 1) % C`; the conclusion likewise uses natural remainder `%`.
Using remainder equality rather than a separate congruence predicate is the only presentational
deviation.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 6.
-/
public theorem_wanted add_one_mod_eq_mod_add_one_of_ne
    (x C : ℕ) (hC : 2 ≤ C) (hne : x % C ≠ (C - 1) % C) :
    (x + 1) % C = x % C + 1

/--
Let integers `A` and `B` be positive, let `C ≥ 2` divide `A` while `B` does not divide `A`,
and let the nonzero integer `a < 0` be congruent to `B` modulo `C`. If
`|a| * ((A / B) % C) < C`, then `(A % B) % C` equals that product. These paper clauses are,
respectively, `hA`, `hB`, `hC`, `hCA`, `hBA`, `ha`, `hcongr`, and `hbound`; the paper's `a ≠ 0` is
implied by the sign hypothesis `ha` and is not repeated.

Congruence is represented by equality of integer remainders `B % C = a % C`; every modular
operation uses Lean's `Int.emod`, whose remainder is nonnegative for the nonzero modulus ensured
by `hC`. The paper's floor `⌊A / B⌋` is Lean's integer `/`, namely `Int.ediv`, which is floor
division because `hB` makes `B` positive. Absolute value is the integer notation `|a|`. These
encoding choices are the only deviations, and this part carries only the negative-sign bound.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 7(i).
-/
public theorem_wanted emod_emod_eq_abs_mul_ediv_emod_of_neg
    (a A B C : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 2 ≤ C)
    (hCA : C ∣ A) (hBA : ¬ B ∣ A)
    (hcongr : B % C = a % C) (ha : a < 0)
    (hbound : |a| * ((A / B) % C) < C) :
    (A % B) % C = |a| * ((A / B) % C)

/--
Let integers `A` and `B` be positive, let `C ≥ 2` divide `A` while `B` does not divide `A`,
and let the nonzero integer `a > 0` be congruent to `B` modulo `C`. If
`a + a * ((A / B) % C) < C`, then `((-A) % B) % C` equals
`a * (1 + (A / B) % C)`. These paper clauses are, respectively, `hA`, `hB`, `hC`, `hCA`,
`hBA`, `ha`, `hcongr`, and `hbound`; the paper's `a ≠ 0` is implied by the sign hypothesis `ha` and
is not repeated.

Congruence is represented by equality of integer remainders `B % C = a % C`; every modular
operation uses Lean's `Int.emod`, whose remainder is nonnegative for the nonzero moduli ensured
by `hB` and `hC`. The paper's floor `⌊A / B⌋` is Lean's integer `/`, namely `Int.ediv`, which
is floor division because `hB` makes `B` positive. These encoding choices are the only
deviations, and this part carries only the positive-sign bound.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 7(ii).
-/
public theorem_wanted neg_emod_emod_eq_mul_one_add_ediv_emod_of_pos
    (a A B C : ℤ)
    (hA : 0 < A) (hB : 0 < B) (hC : 2 ≤ C)
    (hCA : C ∣ A) (hBA : ¬ B ∣ A)
    (hcongr : B % C = a % C) (ha : 0 < a)
    (hbound : a + a * ((A / B) % C) < C) :
    ((-A) % B) % C = a * (1 + (A / B) % C)

/--
Mod-mod representation of a natural C-recursive sequence. Let `t : ℕ → ℕ` have generating
function `A(z)/B(z)` with `A, B ∈ ℤ[z]`, `B(0) = 1` (the recurrence polynomial
`1 + a₁z + ⋯ + a_d z^d`) and `deg A = k < deg B = d`; put `Ã(x) = x^k A(1/x)` and
`B̃(x) = x^d B(1/x)` (`Polynomial.reverse`), so that
`c^{n²} c^{n(d-k)} Ã(cⁿ) / B̃(cⁿ) = c^{n²} A(c⁻ⁿ)/B(c⁻ⁿ)`. If `t` has the div-mod
representation `t(n) = ⌊c^{n²} c^{n(d-k)} Ã(cⁿ)/B̃(cⁿ)⌋ mod cⁿ` for all `n ≥ 1` (`hrep`) and
the free term `α_d = a_d` of `B̃` is negative, then for some natural `r` and all `n ≥ 1`,
`|α_d| t(n) = ((r^{n²} r^{n(d-k)} Ã(rⁿ)) mod B̃(rⁿ)) mod rⁿ` (the paper's `t(n) = (1/|α_d|)(…)`
with the factor cleared). Remainders are `Int.emod` and the floor is taken in `ℚ`. Added
hypothesis `A ≠ 0`, excluding the zero sequence: for `A = 0`, `B = 1 + z` (`α_d = 1 > 0`) the
companion positive case would give `t(n) = -1`.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Theorem 8, negative free term.
-/
public theorem_wanted exists_mod_mod_representation_of_neg_free_term
    (t : ℕ → ℕ) (A B : Polynomial ℤ) (c : ℕ)
    (hB0 : B.coeff 0 = 1) (hAB : A.natDegree < B.natDegree) (hA : A ≠ 0)
    (hgf : PowerSeries.mk (fun n => (t n : ℤ)) * (B : PowerSeries ℤ) = (A : PowerSeries ℤ))
    (hrep : ∀ n, 1 ≤ n →
      (t n : ℤ) = ⌊((c : ℚ) ^ (n ^ 2) * (c : ℚ) ^ (n * (B.natDegree - A.natDegree)) *
          A.reverse.eval ((c : ℤ) ^ n)) / B.reverse.eval ((c : ℤ) ^ n)⌋ % (c : ℤ) ^ n)
    (hα : B.reverse.coeff 0 < 0) :
    ∃ r : ℕ, ∀ n, 1 ≤ n →
      |B.reverse.coeff 0| * (t n : ℤ) =
        ((r : ℤ) ^ (n ^ 2) * (r : ℤ) ^ (n * (B.natDegree - A.natDegree)) *
            A.reverse.eval ((r : ℤ) ^ n)) % B.reverse.eval ((r : ℤ) ^ n) % (r : ℤ) ^ n

/--
Positive free term case of the mod-mod representation, with the same setting as
`exists_mod_mod_representation_of_neg_free_term`: if the free term `α_d` of `B̃` is positive,
then for some natural `r` and all `n ≥ 1`,
`α_d (t(n) + 1) = ((-r^{n²} r^{n(d-k)} Ã(rⁿ)) mod B̃(rⁿ)) mod rⁿ` (the paper's
`t(n) = -1 + (1/α_d)(…)` with the factor cleared). Added hypothesis `A ≠ 0`: for `A = 0`,
`B = 1 + z` the right side is `0`, so the paper's formula would give `t(n) = -1`.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Theorem 8, positive free term.
-/
public theorem_wanted exists_mod_mod_representation_of_pos_free_term
    (t : ℕ → ℕ) (A B : Polynomial ℤ) (c : ℕ)
    (hB0 : B.coeff 0 = 1) (hAB : A.natDegree < B.natDegree) (hA : A ≠ 0)
    (hgf : PowerSeries.mk (fun n => (t n : ℤ)) * (B : PowerSeries ℤ) = (A : PowerSeries ℤ))
    (hrep : ∀ n, 1 ≤ n →
      (t n : ℤ) = ⌊((c : ℚ) ^ (n ^ 2) * (c : ℚ) ^ (n * (B.natDegree - A.natDegree)) *
          A.reverse.eval ((c : ℤ) ^ n)) / B.reverse.eval ((c : ℤ) ^ n)⌋ % (c : ℤ) ^ n)
    (hα : 0 < B.reverse.coeff 0) :
    ∃ r : ℕ, ∀ n, 1 ≤ n →
      B.reverse.coeff 0 * ((t n : ℤ) + 1) =
        (-((r : ℤ) ^ (n ^ 2) * (r : ℤ) ^ (n * (B.natDegree - A.natDegree)) *
            A.reverse.eval ((r : ℤ) ^ n))) % B.reverse.eval ((r : ℤ) ^ n) % (r : ℤ) ^ n

/--
Single-formula mod-mod representation: in the setting of
`exists_mod_mod_representation_of_neg_free_term`, if the free term `α_d` of `B̃` is nonzero,
then there is an integer `r ≥ c` such that for all `n ≥ 1`,
`t(n) = (-1 - sgn α_d)/2 + (1/|α_d|) (((-sgn α_d · r^{n²} r^{n(d-k)} Ã(rⁿ)) mod B̃(rⁿ)) mod rⁿ)`,
stated over `ℚ`. The hypothesis `α_d ≠ 0` is automatic (`α_d` is the leading coefficient of
`B`) and is omitted. Added hypothesis `A ≠ 0`, excluding the zero sequence (for `A = 0`,
`B = 1 + z` the right side is `-1`).

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Corollary 9.
-/
public theorem_wanted exists_mod_mod_representation_sign
    (t : ℕ → ℕ) (A B : Polynomial ℤ) (c : ℕ)
    (hB0 : B.coeff 0 = 1) (hAB : A.natDegree < B.natDegree) (hA : A ≠ 0)
    (hgf : PowerSeries.mk (fun n => (t n : ℤ)) * (B : PowerSeries ℤ) = (A : PowerSeries ℤ))
    (hrep : ∀ n, 1 ≤ n →
      (t n : ℤ) = ⌊((c : ℚ) ^ (n ^ 2) * (c : ℚ) ^ (n * (B.natDegree - A.natDegree)) *
          A.reverse.eval ((c : ℤ) ^ n)) / B.reverse.eval ((c : ℤ) ^ n)⌋ % (c : ℤ) ^ n) :
    ∃ r : ℕ, c ≤ r ∧ ∀ n, 1 ≤ n →
      (t n : ℚ) = (-1 - (B.reverse.coeff 0).sign : ℚ) / 2 +
        (1 / |(B.reverse.coeff 0 : ℚ)|) *
          (((-(B.reverse.coeff 0).sign * ((r : ℤ) ^ (n ^ 2) *
              (r : ℤ) ^ (n * (B.natDegree - A.natDegree)) * A.reverse.eval ((r : ℤ) ^ n))) %
            B.reverse.eval ((r : ℤ) ^ n) % (r : ℤ) ^ n : ℤ) : ℚ)

end

end MetaMathlibExt
