/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# The two-locus constraint for the ABO blood groups

The rival model of von Dungern and Hirszfeld puts the `A` and `B` antigens at two independent
loci. With allele frequencies `a` and `b`, in Hardy–Weinberg and linkage equilibrium, the
carrier probabilities are `carrierProb a = 1 - (1 - a)²` and `carrierProb b = 1 - (1 - b)²`,
and the phenotype frequencies are `twoLocusAB a b = carrierProb a * carrierProb b`,
`twoLocusA a b = carrierProb a * (1 - carrierProb b)` and
`twoLocusB a b = (1 - carrierProb a) * carrierProb b`. They satisfy the two-locus constraint
`(A + AB)(B + AB) = AB`, the relation Bernstein used to reject the model (Crow 1993, p. 4).

## Main statements

* `twoLocus_constraint`: the phenotype frequencies of the two-locus model satisfy
  `(A + AB)(B + AB) = AB`.

## References

* F. Bernstein, Klin. Wochenschr. 3 (1924) 1495–1497; F. Bernstein, Z. indukt. Abstamm.-
  Vererbungsl. 37 (1925) 237–270; J. F. Crow, "Felix Bernstein and the first human marker
  locus", Genetics 133 (1993) 4–7, p. 4 and Table 1.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.BernsteinABOWanted

/-- Probability that an individual carries antigen `X` when the antigen is dominant at its own
locus with allele frequency `a`, in Hardy–Weinberg proportions: `1 - (1 - a)²`. -/
noncomputable def carrierProb (a : ℝ) : ℝ := 1 - (1 - a) ^ 2

/-- Frequency of blood group `AB` under the two-locus model (independent loci for the `A` and
`B` antigens, allele frequencies `a` and `b`, Hardy–Weinberg and linkage equilibrium). -/
noncomputable def twoLocusAB (a b : ℝ) : ℝ := carrierProb a * carrierProb b

/-- Frequency of blood group `A` under the two-locus model. -/
noncomputable def twoLocusA (a b : ℝ) : ℝ := carrierProb a * (1 - carrierProb b)

/-- Frequency of blood group `B` under the two-locus model. -/
noncomputable def twoLocusB (a b : ℝ) : ℝ := (1 - carrierProb a) * carrierProb b

set_option linter.unusedVariables false in
/-- **The two-locus constraint** (von Dungern–Hirszfeld model, as used by Bernstein; Crow 1993,
p. 4): if the `A` and `B` antigens are dominant at two independent loci with allele frequencies
`a, b ∈ [0, 1]`, in Hardy–Weinberg and linkage equilibrium, then the phenotype frequencies
satisfy `(A + AB)(B + AB) = AB`.

Sources: Bernstein (1925); Crow (1993), p. 4. -/
public theorem twoLocus_constraint (a b : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b)
    (hb₁ : b ≤ 1) :
    (twoLocusA a b + twoLocusAB a b) * (twoLocusB a b + twoLocusAB a b) = twoLocusAB a b := by
  simp only [twoLocusA, twoLocusB, twoLocusAB]
  ring

end WantedExt.Biology.StatisticalGenetics.BernsteinABOWanted
