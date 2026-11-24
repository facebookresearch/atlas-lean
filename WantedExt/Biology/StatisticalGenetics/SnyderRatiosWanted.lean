/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Snyder's ratios for a recessive trait

One autosomal locus with a dominant allele `T` (taster) and a recessive allele `t` (non-taster)
at frequencies `p = 1 - q` and `q`. Parents are drawn independently from the Hardy–Weinberg
genotype law (`TT`, `Tt`, `tt` with probabilities `p²`, `2pq`, `q²`; an input, not a result) and
each parent transmits one of its two alleles with probability `1/2` (Mendelian segregation).
Snyder (1932, p. 438) showed that among the children of taster × non-taster matings the
non-taster fraction is `S = q / (p + 2q)`, among the children of taster × taster matings it is
`R = (q / (p + 2q))²`, and the non-taster frequency `B = q²` gives `q = √B`. Since
`p + 2q = 1 + q`, these are `S = q / (1 + q)` and `R = S²` (the `1 + q` form is derived).

Recorded here: the two ratios computed from the explicit mating model, the identity `R = S²`,
and Snyder's inverse `q = √B`. The probable-error formulas and the data of Snyder's Table I are
not formalized.

Sources: L. H. Snyder, "Studies in human inheritance IX. The inheritance of taste deficiency in
man", Ohio J. Sci. 32 (1932) 436–440, p. 438 and Table I.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.SnyderRatiosWanted

/-- Hardy–Weinberg genotype law at a two-allele locus, indexed by the number `k ∈ {0, 1, 2}` of
recessive alleles `t`: `P(TT) = (1 - q)²`, `P(Tt) = 2q(1 - q)`, `P(tt) = q²`. -/
noncomputable def hwGenotype (q : ℝ) (k : Fin 3) : ℝ :=
  (Nat.choose 2 k : ℝ) * q ^ (k : ℕ) * (1 - q) ^ (2 - (k : ℕ))

/-- Probability that a parent with `k` copies of the recessive allele transmits a recessive
allele to a child (Mendelian segregation): `k / 2`. -/
noncomputable def transmitRecessive (k : Fin 3) : ℝ := (k : ℝ) / 2

/-- The dominant phenotype (taster): at least one dominant allele, i.e. `k < 2`. -/
def IsDominant (k : Fin 3) : Prop := (k : ℕ) < 2

instance (k : Fin 3) : Decidable (IsDominant k) := inferInstanceAs (Decidable ((k : ℕ) < 2))

/-- Frequency of the dominant phenotype under the Hardy–Weinberg genotype law. -/
noncomputable def dominantFreq (q : ℝ) : ℝ :=
  ∑ k : Fin 3, if IsDominant k then hwGenotype q k else 0

/-- Frequency `B` of the recessive phenotype (genotype `tt`) under Hardy–Weinberg. -/
noncomputable def recessiveFreq (q : ℝ) : ℝ := hwGenotype q 2

/-- **Snyder's `S`**: the probability that a child of a dominant × recessive mating is recessive,
for parents drawn independently from the Hardy–Weinberg law. The recessive parent always
transmits `t`, so the child is recessive exactly when the dominant parent transmits `t`. -/
noncomputable def ratioDominantRecessive (q : ℝ) : ℝ :=
  (∑ k : Fin 3, if IsDominant k then hwGenotype q k * transmitRecessive k else 0) /
    dominantFreq q

/-- **Snyder's `R`**: the probability that a child of a dominant × dominant mating is recessive,
for parents drawn independently from the Hardy–Weinberg law: both parents must transmit `t`,
independently. -/
noncomputable def ratioDominantDominant (q : ℝ) : ℝ :=
  (∑ k₁ : Fin 3, ∑ k₂ : Fin 3,
      if IsDominant k₁ ∧ IsDominant k₂ then
        hwGenotype q k₁ * hwGenotype q k₂ * (transmitRecessive k₁ * transmitRecessive k₂)
      else 0) /
    (dominantFreq q) ^ 2

/-- **Snyder's ratios** (Snyder 1932, p. 438): for a recessive allele frequency `0 < q < 1`,
with parents drawn independently from the Hardy–Weinberg genotype law and Mendelian
transmission, the recessive fraction among children of dominant × recessive matings is
`S = q / (1 + q)`, the recessive fraction among children of dominant × dominant matings is
`R = (q / (1 + q))² = S²`, and the recessive phenotype frequency `B` determines the allele
frequency by `q = √B`.

Source: Snyder (1932), p. 438. -/
public theorem_wanted snyder_ratios (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    ratioDominantRecessive q = q / (1 + q) ∧
      ratioDominantDominant q = (q / (1 + q)) ^ 2 ∧
      ratioDominantDominant q = (ratioDominantRecessive q) ^ 2 ∧
      Real.sqrt (recessiveFreq q) = q

end WantedExt.Biology.StatisticalGenetics.SnyderRatiosWanted
