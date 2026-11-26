/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bernstein's triple-allele law for the ABO blood groups

Bernstein (1924, 1925) explained the ABO blood groups by one locus with three alleles `O`, `A`,
`B` at frequencies `r`, `p`, `q` (`p + q + r = 1`). Under Hardy–Weinberg proportions the
phenotype frequencies are `O = r²`, `A = p² + 2pr`, `B = q² + 2qr` and `AB = 2pq` (Crow 1993,
Table 1), so `r = √O`, `p = 1 - √(O + B)` and `q = 1 - √(O + A)`, and these three estimates sum
to `1` exactly under the model. The rival model of von Dungern and Hirszfeld puts the `A` and `B`
antigens at two independent loci; with Hardy–Weinberg and linkage equilibrium it forces
`(A + AB)(B + AB) = AB`, the relation Bernstein used to reject it (Crow 1993, p. 4).

The square-root identities of the triple-allele model (derived from Crow's Table 1; they are not
printed in that table) are proved in `Domains.Biology.StatisticalGenetics.BernsteinABOSqrtEstimates`.
Recorded here: the two-locus constraint, and the fact (derived) that the
triple-allele model never satisfies the two-locus constraint when both `A` and `B` alleles are
present, so the two models are distinguishable from phenotype frequencies alone. Hardy–Weinberg
proportions are inputs. The numerical rejection on Bernstein's data and any likelihood
comparison are not formalized.

Sources: F. Bernstein, Klin. Wochenschr. 3 (1924) 1495–1497; F. Bernstein, Z. indukt.
Abstamm.- Vererbungsl. 37 (1925) 237–270; J. F. Crow, "Felix Bernstein and the first human
marker locus", Genetics 133 (1993) 4–7, p. 4 and Table 1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Domains.Biology.StatisticalGenetics.BernsteinABOSqrtEstimates

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

/-- **The two-locus constraint** (von Dungern–Hirszfeld model, as used by Bernstein; Crow 1993,
p. 4): if the `A` and `B` antigens are dominant at two independent loci with allele frequencies
`a, b ∈ [0, 1]`, in Hardy–Weinberg and linkage equilibrium, then the phenotype frequencies
satisfy `(A + AB)(B + AB) = AB`.

Sources: Bernstein (1925); Crow (1993), p. 4. -/
public theorem_wanted twoLocus_constraint (a b : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b)
    (hb₁ : b ≤ 1) :
    (twoLocusA a b + twoLocusAB a b) * (twoLocusB a b + twoLocusAB a b) = twoLocusAB a b

/-- **The triple-allele model violates the two-locus constraint** (derived): for allele
frequencies `p, q, r ≥ 0` with `p + q + r = 1` and both `p > 0` and `q > 0`, the triple-allele
phenotype frequencies satisfy `(A + AB)(B + AB) ≠ AB`; in fact `(A + AB)(B + AB) > AB`.

Sources: Bernstein (1925); Crow (1993), p. 4 and Table 1. -/
public theorem_wanted tripleAllele_violates_twoLocus (p q r : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 ≤ r) (hsum : p + q + r = 1) :
    freqAB p q r < (freqA p q r + freqAB p q r) * (freqB p q r + freqAB p q r)

end WantedExt.Biology.StatisticalGenetics.BernsteinABOWanted
