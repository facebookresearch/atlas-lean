/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics
public import MathlibExt.Biology.PopulationGenetics.Linkage
public import Mathlib.MeasureTheory.Integral.Prod

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Admixture linkage disequilibrium and ALDER weighted LD

A population `C` is formed in one pulse by mixing populations `A` and `B` in proportions
`α : 1 - α` and then mates at random for `n` generations. Two biallelic loci `x`, `y` with
recombination fraction `r` are in linkage equilibrium inside `A` and inside `B`, where the
`'1'` alleles have frequencies `p_A(x), p_A(y)` and `p_B(x), p_B(y)`; write
`δ(x) = p_A(x) - p_B(x)`. Gametes are pairs `g : Bool × Bool` as in `Linkage` (`true` is the
`'1'` allele), and the two-locus random-mating recursion `Linkage.recombine` acts on gamete
frequencies `x : Bool × Bool → ℝ`. Population sizes are infinite (deterministic recursion);
`n` counts generations and `r` is the per-generation recombination fraction.

## Main results

* `alleleCov_eq_linkageDiseq`: the covariance of the `0/1` allele indicators of one gamete is
  `D = x_AB x_ab - x_Ab x_aB`.
* `genotypeCov_eq_two_mul`: for an unphased diploid genotype made of two independent gametes,
  the covariance of the `0/1/2` genotypes at `x` and `y` is `2 D` (Loh et al. 2013, Eqs. 1–3).
* `linkageDiseq_sourceMix`: right after the pulse, `D₀ = α (1 - α) δ(x) δ(y)`;
  `linkageDiseq_admixed`: after `n` generations, `D_n = (1 - r)^n α (1 - α) δ(x) δ(y)`;
  `genotypeCov_admixed`: the diploid covariance is `z = 2 (1 - r)^n α (1 - α) δ(x) δ(y)`.
* `alleleCov_ancestryPulse`: local ancestry. Let `I_x = 1` if the gamete's segment at `x`
  descends from `A`. The pair of ancestry indicators follows the same recursion as a pair of
  perfectly differentiated alleles, so `Cov(I_x, I_y) = α (1 - α) (1 - r)^n` exactly.
* `pow_one_sub_haldane`: with Haldane's map, `(1 - r)^n = e^{-n d} (cosh d)^n` for map length
  `d` Morgans; hence `exp_neg_mul_le_pow_one_sub_haldane`: the continuous form `e^{-n d}`
  used in the literature is a lower bound for the exact discrete-generation decay.
* `weightedLD_eq`: the expected ALDER two-site statistic `𝔼[z(x, y) w(x) w(y)]` with weights
  `w = p_R - p_S` and independently drifting loci equals
  `2 α (1 - α) (1 - r)^n (f4 A B R S)^2`.
* `DriftModel.weightedLD_sources`, `DriftModel.weightedLD_branch`,
  `DriftModel.weightedLD_admixedRef`, `DriftModel.weightedLD_oneRef`: in the admixture-graph
  drift model, the amplitude is `2 α β F2(A, B)^2` (true sources), `2 α β F2(A″, B″)^2` (two
  references branching off the `A–B` path at `A″`, `B″`), `2 α β^3 F2(A, B)^2` (reference `A`
  and the admixed population itself), and `2 α β (α F2(A, R″) - β F2(B, R″))^2` (reference `R′`
  branching off at `R″` and the admixed population), with `β = 1 - α` and the decay factor
  `(1 - r)^n` (Loh et al. 2013, Eqs. 4, 6, 7, 8).

## Conventions and scope

`z` and `w` are population quantities, not sample estimators; the drift expectation is over a
probability space `(Ω, μ)` describing one locus, and two loci are independent copies
(`μ.prod μ`), which is the "no background LD" assumption of Loh et al. (2013), Appendix A.
There is no drift in `C` after the pulse, matching the paper's "negligible postadmixture
drift". The finite-population correction factor, the affine term from assortative mating, and
the polyache one-reference estimator are not covered.

The exact `(1 - r)^n` form follows from the two-locus recursion; Chakraborty and Weiss (1988)
and Loh et al. (2013) write the decay as `e^{-n d}`; `pow_one_sub_haldane` relates the two.

## References

* R. Chakraborty, K. M. Weiss, *Admixture as a tool for finding linked genes and detecting
  that difference from allelic association between loci*, Proc. Natl. Acad. Sci. USA 85
  (1988), 9119–9123.
* P.-R. Loh, M. Lipson, N. Patterson, P. Moorjani, J. K. Pickrell, D. Reich, B. Berger,
  *Inferring admixture histories of human populations using linkage disequilibrium*,
  Genetics 193 (2013), 1233–1254.
-/

@[expose] public section

open MeasureTheory Real
open MathlibExt.Biology.PopulationGenetics.Linkage
open MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics.AdmixtureLD

/-! ### Haplotype and genotype covariances -/

private theorem sum_four (x : Bool × Bool → ℝ) :
    ∑ g, x g = x (true, true) + x (true, false) + x (false, true) + x (false, false) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- The `0/1` count of the `'1'` allele carried by a gamete at one locus. -/
def alleleCount (b : Bool) : ℝ := if b then 1 else 0

/-- The covariance of the allele counts at the two loci of one gamete drawn from the gamete
frequencies `x`: `∑ g, x g a(g.1) a(g.2) - (∑ g, x g a(g.1)) (∑ g, x g a(g.2))`. -/
def alleleCov (x : Bool × Bool → ℝ) : ℝ :=
  ∑ g, x g * (alleleCount g.1 * alleleCount g.2) -
    (∑ g, x g * alleleCount g.1) * ∑ g, x g * alleleCount g.2

/-- The covariance of the unphased diploid genotypes `X = X₁ + X₂ ∈ {0, 1, 2}` at the first
locus and `Y = Y₁ + Y₂` at the second, for an individual made of two gametes `g`, `h` drawn
independently from `x` (random union of gametes). This is `z(x, y)` of Loh et al. (2013),
Eq. 1. -/
def genotypeCov (x : Bool × Bool → ℝ) : ℝ :=
  (∑ g, ∑ h, x g * x h * ((alleleCount g.1 + alleleCount h.1) *
      (alleleCount g.2 + alleleCount h.2))) -
    (∑ g, ∑ h, x g * x h * (alleleCount g.1 + alleleCount h.1)) *
      ∑ g, ∑ h, x g * x h * (alleleCount g.2 + alleleCount h.2)

/-- The covariance of the allele counts of one gamete is the linkage disequilibrium
`D = x_AB x_ab - x_Ab x_aB` (frequencies summing to `1`). -/
theorem alleleCov_eq_linkageDiseq {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) :
    alleleCov x = linkageDiseq x := by
  rw [sum_four] at hx
  have h : x (false, false) = 1 - x (true, true) - x (true, false) - x (false, true) := by
    linarith
  simp only [alleleCov, linkageDiseq, alleleCount, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  rw [h]
  ring

/-- The diploid genotype covariance is twice the haplotype one, `z = 2 D`: the two
same-gamete terms each contribute `D` and the two cross-gamete terms vanish by independence
(Loh et al. 2013, Eqs. 2–3). -/
theorem genotypeCov_eq_two_mul {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) :
    genotypeCov x = 2 * linkageDiseq x := by
  rw [sum_four] at hx
  have h : x (false, false) = 1 - x (true, true) - x (true, false) - x (false, true) := by
    linarith
  simp only [genotypeCov, linkageDiseq, alleleCount, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  rw [h]
  ring

/-! ### Pulse admixture of two source populations -/

/-- The frequency `p` of the `'1'` allele (`b = true`) or `1 - p` of the `'0'` allele. -/
def bernFreq (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Gamete frequencies right after the pulse: with probability `α` the gamete comes from `A`,
where the loci are in linkage equilibrium with `'1'` frequencies `pA` and `qA`, and otherwise
from `B` (frequencies `pB`, `qB`). The biological domain is `α, pA, qA, pB, qB ∈ [0, 1]`;
the identities below hold for all reals. -/
def sourceMix (α pA qA pB qB : ℝ) (g : Bool × Bool) : ℝ :=
  α * (bernFreq pA g.1 * bernFreq qA g.2) + (1 - α) * (bernFreq pB g.1 * bernFreq qB g.2)

/-- The pulse gamete frequencies sum to `1`. -/
theorem sum_sourceMix (α pA qA pB qB : ℝ) : ∑ g, sourceMix α pA qA pB qB g = 1 := by
  simp only [sourceMix, bernFreq, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring

/-- Admixture LD right after the pulse: `D₀ = α (1 - α) δ(x) δ(y)`, with
`δ(x) = pA - pB`, `δ(y) = qA - qB` (Chakraborty and Weiss 1988). -/
theorem linkageDiseq_sourceMix (α pA qA pB qB : ℝ) :
    linkageDiseq (sourceMix α pA qA pB qB) = α * (1 - α) * ((pA - pB) * (qA - qB)) := by
  simp only [linkageDiseq, sourceMix, bernFreq]
  norm_num
  ring

/-- Admixture LD after `n` generations of random mating with recombination fraction `r`:
`D_n = (1 - r)^n α (1 - α) δ(x) δ(y)`. -/
theorem linkageDiseq_admixed (α pA qA pB qB r : ℝ) (n : ℕ) :
    linkageDiseq ((recombine r)^[n] (sourceMix α pA qA pB qB)) =
      (1 - r) ^ n * (α * (1 - α) * ((pA - pB) * (qA - qB))) := by
  rw [linkageDiseq_iterate (sum_sourceMix α pA qA pB qB), linkageDiseq_sourceMix]

/-- Recombination keeps gamete frequencies summing to `1` over any number of generations. -/
theorem sum_iterate_recombine {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) (r : ℝ) (n : ℕ) :
    ∑ g, (recombine r)^[n] x g = 1 := by
  induction n with
  | zero => exact hx
  | succ n ih => rw [Function.iterate_succ_apply']; exact sum_recombine ih r

/-- The diploid genotype covariance in the admixed population `n` generations after the
pulse: `z(x, y) = 2 α (1 - α) (1 - r)^n δ(x) δ(y)` (Loh et al. 2013, Eq. 3, with the exact
discrete-generation factor `(1 - r)^n` in place of `e^{-n d}`). -/
theorem genotypeCov_admixed (α pA qA pB qB r : ℝ) (n : ℕ) :
    genotypeCov ((recombine r)^[n] (sourceMix α pA qA pB qB)) =
      2 * (α * (1 - α)) * (1 - r) ^ n * ((pA - pB) * (qA - qB)) := by
  rw [genotypeCov_eq_two_mul (sum_iterate_recombine (sum_sourceMix α pA qA pB qB) r n),
    linkageDiseq_admixed]
  ring

/-! ### Local-ancestry covariance after a pulse -/

/-- Joint law of the local-ancestry labels at the two loci right after the pulse
(`true` = descends from `A`): every gamete is entirely from `A` (probability `α`) or entirely
from `B`. This is `sourceMix` with perfectly differentiated markers (`pA = qA = 1`,
`pB = qB = 0`). -/
def ancestryPulse (α : ℝ) : Bool × Bool → ℝ := sourceMix α 1 1 0 0

/-- Pulse admixture: after `n` generations of random mating the local-ancestry indicators at
two loci with recombination fraction `r` have covariance `Cov(I_x, I_y) = α (1 - α) (1 - r)^n`
(for every real `α`, `r`; the biological domain is `0 ≤ α ≤ 1`, `0 ≤ r ≤ 1/2`). The
ancestry labels obey the two-locus random-mating recursion of `Linkage.recombine`
(Chakraborty and Weiss 1988). -/
theorem alleleCov_ancestryPulse (α r : ℝ) (n : ℕ) :
    alleleCov ((recombine r)^[n] (ancestryPulse α)) = α * (1 - α) * (1 - r) ^ n := by
  rw [ancestryPulse,
    alleleCov_eq_linkageDiseq (sum_iterate_recombine (sum_sourceMix α 1 1 0 0) r n),
    linkageDiseq_admixed]
  ring

/-! ### Relation to the continuous form `e^{-n d}` -/

/-- With Haldane's map function, `1 - r = e^{-d} cosh d` for map length `d`. -/
theorem one_sub_haldane (d : ℝ) : 1 - haldane d = exp (-d) * cosh d := by
  rw [haldane, cosh_eq]
  have h2 : exp (-2 * d) = exp (-d) * exp (-d) := by rw [← exp_add]; ring_nf
  have h1 : exp (-d) * exp d = 1 := by rw [← exp_add]; simp
  rw [h2]
  linear_combination (-1 / 2 : ℝ) * h1

/-- Exact decay in Morgans: `(1 - r)^n = e^{-n d} (cosh d)^n` when `r = haldane d`. -/
theorem pow_one_sub_haldane (d : ℝ) (n : ℕ) :
    (1 - haldane d) ^ n = exp (-(n * d)) * cosh d ^ n := by
  rw [one_sub_haldane, mul_pow, ← exp_nat_mul]
  ring_nf

/-- The continuous decay `e^{-n d}` used by Chakraborty and Weiss (1988) and Loh et al.
(2013) is a lower bound for the exact factor `(1 - r)^n` under Haldane's map (all real
`d`; the biological domain is `0 ≤ d`). -/
theorem exp_neg_mul_le_pow_one_sub_haldane (d : ℝ) (n : ℕ) :
    exp (-(n * d)) ≤ (1 - haldane d) ^ n := by
  rw [pow_one_sub_haldane]
  exact le_mul_of_one_le_right (exp_pos _).le (one_le_pow₀ (one_le_cosh d))

/-- Local-ancestry covariance in Morgans:
`Cov(I_x, I_y) = α (1 - α) e^{-n d} (cosh d)^n` for loci `d` Morgans apart. -/
theorem alleleCov_ancestryPulse_haldane (α d : ℝ) (n : ℕ) :
    alleleCov ((recombine (haldane d))^[n] (ancestryPulse α)) =
      α * (1 - α) * (exp (-(n * d)) * cosh d ^ n) := by
  rw [alleleCov_ancestryPulse, pow_one_sub_haldane]

/-! ### ALDER weighted LD -/

section WeightedLD

variable {Ω P : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) (p : P → Ω → ℝ)

/-- The expected ALDER two-site weighted-LD statistic `𝔼[z(x, y) w(x) w(y)]` (Loh et al.
2013, Appendix A, without distance binning). The loci `x` and `y` drift independently: `ω.1`
and `ω.2` are independent draws from `μ`, and `p X ω` is the frequency of the `'1'` allele in
population `X`. The covariance `z(x, y)` is that of the population formed `n` generations ago
as an `α : 1 - α` mixture of `A` and `B` (`genotypeCov_admixed`), and the weights are the
frequency differences `w = p R - p S` between two reference populations `R` and `S`. -/
noncomputable def weightedLD (α r : ℝ) (n : ℕ) (A B R S : P) : ℝ :=
  ∫ ω, genotypeCov ((recombine r)^[n] (sourceMix α (p A ω.1) (p A ω.2) (p B ω.1) (p B ω.2))) *
      ((p R ω.1 - p S ω.1) * (p R ω.2 - p S ω.2)) ∂μ.prod μ

/-- The expected weighted LD factors as `2 α (1 - α) (1 - r)^n (f4 A B R S)^2`: by
independence of the loci, `𝔼[δ(x) w(x) δ(y) w(y)] = 𝔼[δ w]^2` and `𝔼[δ w] = f4 A B R S`.
The identity holds with the Bochner-integral conventions as stated; it is meaningful when the
frequencies are square integrable, as in every `DriftModel`. -/
theorem weightedLD_eq [SFinite μ] (α r : ℝ) (n : ℕ) (A B R S : P) :
    weightedLD μ p α r n A B R S = 2 * (α * (1 - α)) * (1 - r) ^ n * f4 μ p A B R S ^ 2 := by
  have key : ∀ ω : Ω × Ω,
      genotypeCov ((recombine r)^[n] (sourceMix α (p A ω.1) (p A ω.2) (p B ω.1) (p B ω.2))) *
        ((p R ω.1 - p S ω.1) * (p R ω.2 - p S ω.2)) =
      2 * (α * (1 - α)) * (1 - r) ^ n *
        (((p A ω.1 - p B ω.1) * (p R ω.1 - p S ω.1)) *
          ((p A ω.2 - p B ω.2) * (p R ω.2 - p S ω.2))) := fun ω => by
    rw [genotypeCov_admixed]; ring
  unfold weightedLD
  simp_rw [key]
  rw [integral_const_mul, integral_prod_mul (f := fun ω => (p A ω - p B ω) * (p R ω - p S ω))
    (g := fun ω => (p A ω - p B ω) * (p R ω - p S ω)), f4, sq]

namespace DriftModel

variable {μ} {E : Type*} [Fintype E] (M : FStatistics.DriftModel μ E P)

/-- Weights from the true mixing populations (`R = A`, `S = B`): the amplitude is
`2 α β F2(A, B)^2` (Loh et al. 2013, Eq. 4). -/
theorem weightedLD_sources [SFinite μ] (α r : ℝ) (n : ℕ) (A B : P) :
    weightedLD μ M.freq α r n A B A B =
      2 * (α * (1 - α)) * (1 - r) ^ n * f2 μ M.freq A B ^ 2 := by
  rw [weightedLD_eq, ← f2_eq_f4]

/-- Branch points on the `A–B` path. Suppose that `A = A″ + uA`, `A′ = A″ + uA'`,
`B = B″ + uB`, `B′ = B″ + uB'` at the level of lineage weights, where `w A″ - w B″` is
disjoint in support from each of `uA`, `uB`, `uA'`, `uB'`, and each of `uA`, `uB` is disjoint
from each of `uA'`, `uB'`. On a tree this says that the paths `A″–B″`, `A″–A`, `B″–B`,
`A″–A′`, `B″–B′` share no edge (the vectors may be signed, so every rooting is allowed).
Then `f4 A B A′ B′ = f2 A″ B″`. -/
theorem f4_eq_f2_of_branch {A B A' B' A'' B'' : P} {uA uB uA' uB' : E → ℝ}
    (hA : M.weight A = M.weight A'' + uA) (hB : M.weight B = M.weight B'' + uB)
    (hA' : M.weight A' = M.weight A'' + uA') (hB' : M.weight B' = M.weight B'' + uB')
    (hdisj : ∀ e, ∀ u ∈ [uA, uB], ∀ v ∈ [uA', uB'], u e * v e = 0)
    (hpath : ∀ e, ∀ u ∈ [uA, uB, uA', uB'], (M.weight A'' e - M.weight B'' e) * u e = 0) :
    f4 μ M.freq A B A' B' = f2 μ M.freq A'' B'' := by
  rw [M.f4_freq, M.f2_freq]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hA, hB, hA', hB']
  simp only [Pi.add_apply]
  have h1 := hdisj e uA (by simp) uA' (by simp)
  have h2 := hdisj e uA (by simp) uB' (by simp)
  have h3 := hdisj e uB (by simp) uA' (by simp)
  have h4 := hdisj e uB (by simp) uB' (by simp)
  have h5 := hpath e uA (by simp)
  have h6 := hpath e uB (by simp)
  have h7 := hpath e uA' (by simp)
  have h8 := hpath e uB' (by simp)
  linear_combination M.len e * (h1 - h2 - h3 + h4 + h5 - h6 + h7 - h8)

/-- Two diverged references `A′`, `B′` branching off the `A–B` path at `A″` and `B″`: the
amplitude is `2 α β F2(A″, B″)^2` (Loh et al. 2013, Eq. 6). -/
theorem weightedLD_branch [SFinite μ] (α r : ℝ) (n : ℕ) {A B A' B' A'' B'' : P}
    {uA uB uA' uB' : E → ℝ}
    (hA : M.weight A = M.weight A'' + uA) (hB : M.weight B = M.weight B'' + uB)
    (hA' : M.weight A' = M.weight A'' + uA') (hB' : M.weight B' = M.weight B'' + uB')
    (hdisj : ∀ e, ∀ u ∈ [uA, uB], ∀ v ∈ [uA', uB'], u e * v e = 0)
    (hpath : ∀ e, ∀ u ∈ [uA, uB, uA', uB'], (M.weight A'' e - M.weight B'' e) * u e = 0) :
    weightedLD μ M.freq α r n A B A' B' =
      2 * (α * (1 - α)) * (1 - r) ^ n * f2 μ M.freq A'' B'' ^ 2 := by
  rw [weightedLD_eq, f4_eq_f2_of_branch M hA hB hA' hB' hdisj hpath]

/-- One reference `A` and the admixed population `C` itself, with no drift in `C` after the
pulse (`w C = α w A + (1 - α) w B`): the weights are `p A - p C = β δ` and the amplitude is
`2 α β^3 F2(A, B)^2` (Loh et al. 2013, Eq. 7). -/
theorem weightedLD_admixedRef [SFinite μ] (α r : ℝ) (n : ℕ) {A B C : P}
    (hC : M.weight C = α • M.weight A + (1 - α) • M.weight B) :
    weightedLD μ M.freq α r n A B A C =
      2 * (α * (1 - α) ^ 3) * (1 - r) ^ n * f2 μ M.freq A B ^ 2 := by
  have : f4 μ M.freq A B A C = (1 - α) * f2 μ M.freq A B := by
    rw [M.f4_freq, M.f2_freq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hC]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [weightedLD_eq, this]
  ring

/-- One diverged reference `R′` branching off the `A–B` path at `R″` (so `A = R″ + uA`,
`B = R″ + uB`, `R′ = R″ + uR` with pairwise disjoint supports) and the admixed population `C`
with no post-pulse drift: the weights `p R′ - p C` give the amplitude
`2 α β (α F2(A, R″) - β F2(B, R″))^2` (Loh et al. 2013, Eq. 8). -/
theorem weightedLD_oneRef [SFinite μ] (α r : ℝ) (n : ℕ) {A B C R' R'' : P}
    {uA uB uR : E → ℝ}
    (hA : M.weight A = M.weight R'' + uA) (hB : M.weight B = M.weight R'' + uB)
    (hR : M.weight R' = M.weight R'' + uR)
    (hAB : ∀ e, uA e * uB e = 0) (hAR : ∀ e, uA e * uR e = 0) (hBR : ∀ e, uB e * uR e = 0)
    (hC : M.weight C = α • M.weight A + (1 - α) • M.weight B) :
    weightedLD μ M.freq α r n A B R' C =
      2 * (α * (1 - α)) * (1 - r) ^ n *
        (α * f2 μ M.freq A R'' - (1 - α) * f2 μ M.freq B R'') ^ 2 := by
  have : f4 μ M.freq A B R' C =
      -(α * f2 μ M.freq A R'' - (1 - α) * f2 μ M.freq B R'') := by
    rw [M.f4_freq, M.f2_freq, M.f2_freq, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hC]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hA, hB, hR]
    simp only [Pi.add_apply]
    linear_combination M.len e * ((2 * α - 1) * hAB e + hAR e - hBR e)
  rw [weightedLD_eq, this]
  ring

end DriftModel

end WeightedLD

end MathlibExt.Biology.PopulationGenetics.AdmixtureLD
