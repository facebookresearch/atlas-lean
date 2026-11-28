/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bernstein's square-root estimates for the ABO blood groups

Under the triple-allele model with Hardy–Weinberg proportions and allele frequencies
`p, q, r ≥ 0` with `p + q + r = 1`, the phenotype frequencies are `O = r²`, `A = p² + 2pr`,
`B = q² + 2qr` and `AB = 2pq`. They sum to `1`, the allele frequencies are recovered by
`r = √O`, `p = 1 - √(O + B)` and `q = 1 - √(O + A)`, and these three estimates sum to `1`.

## Main statements

* `sqrt_estimates`: the four phenotype frequencies sum to `1`, the three square-root
  identities hold, and the three estimates sum to `1`.
* `tripleAllele_violates_twoLocus`: with the same hypotheses and `p > 0` and `q > 0`,
  the triple-allele frequencies satisfy `AB < (A + AB)(B + AB)`, including when `r = 0`.
  This is an algebraic consequence of the expected frequencies in Crow's Table 1, not
  the comparison of observed frequencies on p. 4. The independent two-locus model instead
  gives equality under Hardy–Weinberg proportions and linkage equilibrium.

## References

* Felix Bernstein, *Zusammenfassende Betrachtungen über die erblichen Blutstrukturen des Menschen*,
  Z. Indukt. Abstamm. Vererbungsl. 37 (1925), 237–270.
  See also Klin. Wochenschr. 3 (1924), 1495–1497.
* James F. Crow, *Felix Bernstein and the First Human Marker Locus*, Genetics 133 (1993), 4–7:
  the two-locus equality on p. 4 and the expected frequencies in Table 1.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.BernsteinABOWanted

/-- Frequency of blood group `O` under the triple-allele model with allele frequencies
`p` (allele `A`), `q` (allele `B`), `r` (allele `O`) in Hardy–Weinberg proportions:
genotype `OO`. -/
noncomputable def freqO (_p _q r : ℝ) : ℝ := r ^ 2

/-- Frequency of blood group `A` under the triple-allele model: genotypes `AA` and `AO`. -/
noncomputable def freqA (p _q r : ℝ) : ℝ := p ^ 2 + 2 * p * r

/-- Frequency of blood group `B` under the triple-allele model: genotypes `BB` and `BO`. -/
noncomputable def freqB (_p q r : ℝ) : ℝ := q ^ 2 + 2 * q * r

/-- Frequency of blood group `AB` under the triple-allele model: genotype `AB`. -/
noncomputable def freqAB (p q _r : ℝ) : ℝ := 2 * p * q

/-- **Bernstein's square-root estimates** (triple-allele model; derived from Crow 1993,
Table 1): for allele frequencies `p, q, r ≥ 0` with `p + q + r = 1`, the four phenotype
frequencies sum to `1`, `√O = r`, `1 - √(O + B) = p`, `1 - √(O + A) = q`, and the three
estimates `√O`, `1 - √(O + B)`, `1 - √(O + A)` sum to exactly `1`.

Sources: Bernstein (1924, 1925); Crow (1993), Table 1. -/
public theorem sqrt_estimates (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hsum : p + q + r = 1) :
    freqO p q r + freqA p q r + freqB p q r + freqAB p q r = 1 ∧
      Real.sqrt (freqO p q r) = r ∧
      1 - Real.sqrt (freqO p q r + freqB p q r) = p ∧
      1 - Real.sqrt (freqO p q r + freqA p q r) = q ∧
      Real.sqrt (freqO p q r) + (1 - Real.sqrt (freqO p q r + freqB p q r)) +
        (1 - Real.sqrt (freqO p q r + freqA p q r)) = 1 := by
  have hsum1 : freqO p q r + freqA p q r + freqB p q r + freqAB p q r = 1 := by
    have hsq : freqO p q r + freqA p q r + freqB p q r + freqAB p q r
        = (p + q + r) ^ 2 := by
      simp only [freqO, freqA, freqB, freqAB]
      ring
    rw [hsq, hsum, one_pow]
  have hsqrtO : Real.sqrt (freqO p q r) = r := by
    simp only [freqO, Real.sqrt_sq hr]
  have hsqB : freqO p q r + freqB p q r = (q + r) ^ 2 := by
    simp only [freqO, freqB]
    ring
  have hsqrtB : 1 - Real.sqrt (freqO p q r + freqB p q r) = p := by
    rw [hsqB, Real.sqrt_sq (add_nonneg hq hr)]
    linarith
  have hsqA : freqO p q r + freqA p q r = (p + r) ^ 2 := by
    simp only [freqO, freqA]
    ring
  have hsqrtA : 1 - Real.sqrt (freqO p q r + freqA p q r) = q := by
    rw [hsqA, Real.sqrt_sq (add_nonneg hp hr)]
    linarith
  refine ⟨hsum1, hsqrtO, hsqrtB, hsqrtA, ?_⟩
  rw [hsqrtO, hsqrtB, hsqrtA]
  linarith

/-- **The triple-allele model violates the two-locus constraint** (derived): for allele
frequencies `p, q, r ≥ 0` with `p + q + r = 1` and both `p > 0` and `q > 0`, the triple-allele
phenotype frequencies satisfy `(A + AB)(B + AB) ≠ AB`; in fact `(A + AB)(B + AB) > AB`.

Sources: Bernstein (1925); Crow (1993), p. 4 and Table 1. -/
public theorem tripleAllele_violates_twoLocus (p q r : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 ≤ r) (hsum : p + q + r = 1) :
    freqAB p q r < (freqA p q r + freqAB p q r) * (freqB p q r + freqAB p q r) := by
  have hgap : (freqA p q r + freqAB p q r) * (freqB p q r + freqAB p q r) - freqAB p q r =
      p * q * (2 * r + p * q) := by
    have hr_eq : r = 1 - p - q := by linarith only [hsum]
    simp only [freqA, freqB, freqAB, hr_eq]
    ring
  rw [← sub_pos, hgap]
  have hpq := mul_pos hp hq
  exact mul_pos hpq (add_pos_of_nonneg_of_pos (mul_nonneg two_pos.le hr) hpq)

end WantedExt.Biology.StatisticalGenetics.BernsteinABOWanted
