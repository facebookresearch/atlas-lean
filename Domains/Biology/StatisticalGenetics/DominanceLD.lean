/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Dominance linkage disequilibrium is the square of additive linkage disequilibrium

Consider two biallelic loci `A` and `B` and a diploid individual formed by random union of
gametes: its two haplotypes `H₁ = (X₁, Y₁)` and `H₂ = (X₂, Y₂)` are independent and identically
distributed, where `X_h` and `Y_h` code the alleles carried by haplotype `h` at `A` and `B`
(classically `0`/`1` indicators, but any square-integrable coding is allowed here). Write
`p = E X₁`, `q = E Y₁` for the allele frequencies, `V_A = Var X₁`, `V_B = Var Y₁`, and
`D = Cov(X₁, Y₁)` for the gametic linkage disequilibrium.

The additive coding of the genotype at `A` is the centred allele count
`a_A = (X₁ - p) + (X₂ - p)`, and the dominance coding is the product of centred allele indicators
`d_A = (X₁ - p) (X₂ - p)`. For `0`/`1` alleles `d_A` is a function of the genotype `X₁ + X₂`
alone, taking the values `p²`, `-p(1 - p)`, `(1 - p)²` at genotypes `0`, `1`, `2`
(`domCode_eq_dominanceEncoding`); dividing by `-p(1 - p)` gives the dominance encoding
`-p/(1 - p)`, `1`, `-(1 - p)/p` of Palmer et al. (2023), which has the same correlations.

* `RandomUnion.integral_addA_mul_addB`: `E(a_A a_B) = 2 D`, and `E(a_A²) = 2 V_A`;
* `RandomUnion.integral_domA_mul_domB`: `E(d_A d_B) = D²`, and `E(d_A²) = V_A²`;
* `RandomUnion.integral_addA_mul_domB`: the additive and dominance codings are uncorrelated.

Consequently (`RandomUnion.domCorr_eq_addCorr_sq`) the correlation between the dominance codings
at two loci is the square of the correlation between their additive codings, which is the
gametic correlation `r = D / √(V_A V_B)` (`RandomUnion.addCorr_eq`): "the correlation structure
between variants under the dominance encoding decays as the square of the additive correlation"
(Palmer et al. 2023, graphical abstract). So, with population correlations, the dominance LD
score `∑ r_d²` of a variant is the sum of the fourth powers of its additive correlations. For
d-LDSC, the exact expectation `LDScore.Model.integral_chiSq_of_standardized` applies verbatim to
a standardized dominance-coded genotype matrix, with the in-sample dominance LD scores; it needs
no new statement.

## Main results

* `RandomUnion`: two-locus diploid genotypes under random union of gametes.
* `RandomUnion.integral_addA_mul_addB`, `RandomUnion.integral_addA_sq`,
  `RandomUnion.integral_domA_mul_domB`, `RandomUnion.integral_domA_sq`,
  `RandomUnion.integral_addA_mul_domB`.
* `RandomUnion.addCorr_eq`, `RandomUnion.domCorr_eq_addCorr_sq`.
* `dominanceEncoding`, `domCode_eq_dominanceEncoding`.

## References

* D. S. Palmer, W. Zhou, L. Abbott, E. M. Wigdor, N. Baya, C. Churchhouse, C. Seed, T. Poterba,
  D. King, M. Kanai, A. Bloemendal, B. M. Neale, *Analysis of genetic dominance in the UK
  Biobank*, Science 379 (2023), 1341–1348.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Biology.StatisticalGenetics.DominanceLD

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A diploid two-locus genotype under random union of gametes: the haplotypes
`(X₁, Y₁)` and `(X₂, Y₂)` are independent and identically distributed, with square-integrable
allele codings. -/
structure RandomUnion (P : Measure Ω) where
  /-- The allele coding of haplotype 1 at locus `A`. -/
  x1 : Ω → ℝ
  /-- The allele coding of haplotype 1 at locus `B`. -/
  y1 : Ω → ℝ
  /-- The allele coding of haplotype 2 at locus `A`. -/
  x2 : Ω → ℝ
  /-- The allele coding of haplotype 2 at locus `B`. -/
  y2 : Ω → ℝ
  memLp_x1 : MemLp x1 2 P
  memLp_y1 : MemLp y1 2 P
  memLp_x2 : MemLp x2 2 P
  memLp_y2 : MemLp y2 2 P
  /-- The two haplotypes are independent. -/
  indep : IndepFun (fun ω => (x1 ω, y1 ω)) (fun ω => (x2 ω, y2 ω)) P
  /-- The two haplotypes are identically distributed. -/
  ident : IdentDistrib (fun ω => (x1 ω, y1 ω)) (fun ω => (x2 ω, y2 ω)) P P

namespace RandomUnion

variable {P : Measure Ω} [IsProbabilityMeasure P] (G : RandomUnion P)

/-- The allele frequency (mean coding) `p = E X₁` at locus `A`. -/
noncomputable def freqA : ℝ := ∫ ω, G.x1 ω ∂P

/-- The allele frequency (mean coding) `q = E Y₁` at locus `B`. -/
noncomputable def freqB : ℝ := ∫ ω, G.y1 ω ∂P

/-- The haplotype variance `V_A = E (X₁ - p)²` at locus `A`. -/
noncomputable def varA : ℝ := ∫ ω, (G.x1 ω - G.freqA) ^ 2 ∂P

/-- The haplotype variance `V_B = E (Y₁ - q)²` at locus `B`. -/
noncomputable def varB : ℝ := ∫ ω, (G.y1 ω - G.freqB) ^ 2 ∂P

/-- The gametic linkage disequilibrium `D = E (X₁ - p) (Y₁ - q)`. -/
noncomputable def ldD : ℝ := ∫ ω, (G.x1 ω - G.freqA) * (G.y1 ω - G.freqB) ∂P

/-- The additive coding `a_A = (X₁ - p) + (X₂ - p)` (centred allele count) at locus `A`. -/
noncomputable def addA (ω : Ω) : ℝ := (G.x1 ω - G.freqA) + (G.x2 ω - G.freqA)

/-- The additive coding `a_B = (Y₁ - q) + (Y₂ - q)` at locus `B`. -/
noncomputable def addB (ω : Ω) : ℝ := (G.y1 ω - G.freqB) + (G.y2 ω - G.freqB)

/-- The dominance coding `d_A = (X₁ - p) (X₂ - p)` at locus `A`. -/
noncomputable def domA (ω : Ω) : ℝ := (G.x1 ω - G.freqA) * (G.x2 ω - G.freqA)

/-- The dominance coding `d_B = (Y₁ - q) (Y₂ - q)` at locus `B`. -/
noncomputable def domB (ω : Ω) : ℝ := (G.y1 ω - G.freqB) * (G.y2 ω - G.freqB)

private theorem integral_transfer
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (G : RandomUnion P)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    (∫ ω, f (G.x2 ω, G.y2 ω) ∂P) = ∫ ω, f (G.x1 ω, G.y1 ω) ∂P :=
  (G.ident.comp hf).integral_eq.symm

private theorem integral_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (G : RandomUnion P)
    {f g : ℝ × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    (∫ ω, f (G.x1 ω, G.y1 ω) * g (G.x2 ω, G.y2 ω) ∂P) =
      (∫ ω, f (G.x1 ω, G.y1 ω) ∂P) * ∫ ω, g (G.x2 ω, G.y2 ω) ∂P := by
  exact (G.indep.comp hf hg).integral_fun_mul_eq_mul_integral
    (G.ident.comp hf).aemeasurable_fst.aestronglyMeasurable
    (G.ident.comp hg).aemeasurable_snd.aestronglyMeasurable

private theorem integral_add_mul
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (G : RandomUnion P) {f g : ℝ × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf1 : MemLp (fun ω => f (G.x1 ω, G.y1 ω)) 2 P)
    (hg1 : MemLp (fun ω => g (G.x1 ω, G.y1 ω)) 2 P)
    (hf2 : MemLp (fun ω => f (G.x2 ω, G.y2 ω)) 2 P)
    (hg2 : MemLp (fun ω => g (G.x2 ω, G.y2 ω)) 2 P)
    (hf0 : (∫ ω, f (G.x1 ω, G.y1 ω) ∂P) = 0)
    (hg0 : (∫ ω, g (G.x1 ω, G.y1 ω) ∂P) = 0) :
    (∫ ω, (f (G.x1 ω, G.y1 ω) + f (G.x2 ω, G.y2 ω)) *
      (g (G.x1 ω, G.y1 ω) + g (G.x2 ω, G.y2 ω)) ∂P) =
      2 * ∫ ω, f (G.x1 ω, G.y1 ω) * g (G.x1 ω, G.y1 ω) ∂P := by
  have h11 : Integrable (fun ω => f (G.x1 ω, G.y1 ω) * g (G.x1 ω, G.y1 ω)) P :=
    hf1.integrable_mul hg1
  have h12 : Integrable (fun ω => f (G.x1 ω, G.y1 ω) * g (G.x2 ω, G.y2 ω)) P :=
    hf1.integrable_mul hg2
  have h21 : Integrable (fun ω => g (G.x1 ω, G.y1 ω) * f (G.x2 ω, G.y2 ω)) P :=
    hg1.integrable_mul hf2
  have h22 : Integrable (fun ω => f (G.x2 ω, G.y2 ω) * g (G.x2 ω, G.y2 ω)) P :=
    hf2.integrable_mul hg2
  have h112 : Integrable (fun ω =>
      f (G.x1 ω, G.y1 ω) * g (G.x1 ω, G.y1 ω) +
      f (G.x1 ω, G.y1 ω) * g (G.x2 ω, G.y2 ω)) P := h11.add h12
  have h1121 : Integrable (fun ω =>
      (f (G.x1 ω, G.y1 ω) * g (G.x1 ω, G.y1 ω) +
       f (G.x1 ω, G.y1 ω) * g (G.x2 ω, G.y2 ω)) +
      g (G.x1 ω, G.y1 ω) * f (G.x2 ω, G.y2 ω)) P := h112.add h21
  have hexp : ∀ ω, (f (G.x1 ω, G.y1 ω) + f (G.x2 ω, G.y2 ω)) *
      (g (G.x1 ω, G.y1 ω) + g (G.x2 ω, G.y2 ω)) =
      ((f (G.x1 ω, G.y1 ω) * g (G.x1 ω, G.y1 ω) +
        f (G.x1 ω, G.y1 ω) * g (G.x2 ω, G.y2 ω)) +
        g (G.x1 ω, G.y1 ω) * f (G.x2 ω, G.y2 ω)) +
        f (G.x2 ω, G.y2 ω) * g (G.x2 ω, G.y2 ω) := by
    intro ω
    ring
  simp_rw [hexp]
  rw [integral_add h1121 h22,
    integral_add h112 h21, integral_add h11 h12,
    G.integral_product hf hg, G.integral_product hg hf,
    G.integral_transfer (f := fun z => f z * g z) (hf.mul hg), hf0, hg0]
  ring

private theorem integral_dom_mul
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (G : RandomUnion P)
    {f g : ℝ × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    (∫ ω, (f (G.x1 ω, G.y1 ω) * f (G.x2 ω, G.y2 ω)) *
      (g (G.x1 ω, G.y1 ω) * g (G.x2 ω, G.y2 ω)) ∂P) =
      (∫ ω, f (G.x1 ω, G.y1 ω) * g (G.x1 ω, G.y1 ω) ∂P) ^ 2 := by
  have hexp : ∀ ω, (f (G.x1 ω, G.y1 ω) * f (G.x2 ω, G.y2 ω)) *
      (g (G.x1 ω, G.y1 ω) * g (G.x2 ω, G.y2 ω)) =
      (f (G.x1 ω, G.y1 ω) * g (G.x1 ω, G.y1 ω)) *
      (f (G.x2 ω, G.y2 ω) * g (G.x2 ω, G.y2 ω)) := by
    intro ω
    ring
  simp_rw [hexp]
  rw [G.integral_product (f := fun z => f z * g z)
      (g := fun z => f z * g z) (hf.mul hg) (hf.mul hg),
    G.integral_transfer (f := fun z => f z * g z) (hf.mul hg), pow_two]

private theorem integral_add_dom
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (G : RandomUnion P) {f g : ℝ × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf1 : MemLp (fun ω => f (G.x1 ω, G.y1 ω)) 2 P)
    (hg1 : MemLp (fun ω => g (G.x1 ω, G.y1 ω)) 2 P)
    (hf2 : MemLp (fun ω => f (G.x2 ω, G.y2 ω)) 2 P)
    (hg2 : MemLp (fun ω => g (G.x2 ω, G.y2 ω)) 2 P)
    (hg0 : (∫ ω, g (G.x1 ω, G.y1 ω) ∂P) = 0) :
    (∫ ω, (f (G.x1 ω, G.y1 ω) + f (G.x2 ω, G.y2 ω)) *
      (g (G.x1 ω, G.y1 ω) * g (G.x2 ω, G.y2 ω)) ∂P) = 0 := by
  have h1 := (G.indep.comp (hf.mul hg) hg).integrable_mul
    (hf1.integrable_mul hg1) (hg2.integrable (by norm_num))
  have h2 := (G.indep.comp hg (hf.mul hg)).integrable_mul
    (hg1.integrable (by norm_num)) (hf2.integrable_mul hg2)
  change Integrable (fun ω =>
    (f (G.x1 ω, G.y1 ω) * g (G.x1 ω, G.y1 ω)) * g (G.x2 ω, G.y2 ω)) P at h1
  change Integrable (fun ω =>
    g (G.x1 ω, G.y1 ω) * (f (G.x2 ω, G.y2 ω) * g (G.x2 ω, G.y2 ω))) P at h2
  have hexp : ∀ ω, (f (G.x1 ω, G.y1 ω) + f (G.x2 ω, G.y2 ω)) *
      (g (G.x1 ω, G.y1 ω) * g (G.x2 ω, G.y2 ω)) =
      (f (G.x1 ω, G.y1 ω) * g (G.x1 ω, G.y1 ω)) * g (G.x2 ω, G.y2 ω) +
      g (G.x1 ω, G.y1 ω) * (f (G.x2 ω, G.y2 ω) * g (G.x2 ω, G.y2 ω)) := by
    intro ω
    ring
  simp_rw [hexp]
  rw [integral_add h1 h2, G.integral_product (f := fun z => f z * g z) (hf.mul hg) hg,
    G.integral_product (g := fun z => f z * g z) hg (hf.mul hg), G.integral_transfer hg, hg0]
  ring

private theorem integral_centered
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (∫ ω, f ω - (∫ ω, f ω ∂P) ∂P) = 0 := by
  rw [integral_sub (hf.integrable (by norm_num)) (integrable_const _)]
  simp

private theorem integral_add_sq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (G : RandomUnion P) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hf1 : MemLp (fun ω => f (G.x1 ω, G.y1 ω)) 2 P)
    (hf2 : MemLp (fun ω => f (G.x2 ω, G.y2 ω)) 2 P)
    (hf0 : (∫ ω, f (G.x1 ω, G.y1 ω) ∂P) = 0) :
    (∫ ω, (f (G.x1 ω, G.y1 ω) + f (G.x2 ω, G.y2 ω)) ^ 2 ∂P) =
      2 * ∫ ω, f (G.x1 ω, G.y1 ω) ^ 2 ∂P := by
  simpa only [pow_two] using G.integral_add_mul hf hf hf1 hf1 hf2 hf2 hf0 hf0

private theorem integral_dom_sq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (G : RandomUnion P)
    {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    (∫ ω, (f (G.x1 ω, G.y1 ω) * f (G.x2 ω, G.y2 ω)) ^ 2 ∂P) =
      (∫ ω, f (G.x1 ω, G.y1 ω) ^ 2 ∂P) ^ 2 := by
  simpa only [pow_two] using G.integral_dom_mul hf hf

/-- Additive LD: `E(a_A a_B) = 2 D`. -/
theorem integral_addA_mul_addB : ∫ ω, G.addA ω * G.addB ω ∂P = 2 * G.ldD := by
  simpa only [addA, addB, ldD] using
    G.integral_add_mul
      (f := fun z => z.1 - G.freqA) (g := fun z => z.2 - G.freqB)
      (measurable_fst.sub measurable_const) (measurable_snd.sub measurable_const)
      (G.memLp_x1.sub (memLp_const G.freqA))
      (G.memLp_y1.sub (memLp_const G.freqB))
      (G.memLp_x2.sub (memLp_const G.freqA))
      (G.memLp_y2.sub (memLp_const G.freqB))
      (integral_centered G.memLp_x1) (integral_centered G.memLp_y1)


/-- The additive coding has second moment `E(a_A²) = 2 V_A`. -/
theorem integral_addA_sq : ∫ ω, G.addA ω ^ 2 ∂P = 2 * G.varA := by
  simpa only [addA, varA] using
    G.integral_add_sq (f := fun z => z.1 - G.freqA)
      (measurable_fst.sub measurable_const)
      (G.memLp_x1.sub (memLp_const G.freqA))
      (G.memLp_x2.sub (memLp_const G.freqA))
      (integral_centered G.memLp_x1)


/-- The additive coding has second moment `E(a_B²) = 2 V_B`. -/
theorem integral_addB_sq : ∫ ω, G.addB ω ^ 2 ∂P = 2 * G.varB := by
  simpa only [addB, varB] using
    G.integral_add_sq (f := fun z => z.2 - G.freqB)
      (measurable_snd.sub measurable_const)
      (G.memLp_y1.sub (memLp_const G.freqB))
      (G.memLp_y2.sub (memLp_const G.freqB))
      (integral_centered G.memLp_y1)


omit [IsProbabilityMeasure P] in
/-- Dominance LD: `E(d_A d_B) = D²`. -/
theorem integral_domA_mul_domB : ∫ ω, G.domA ω * G.domB ω ∂P = G.ldD ^ 2 := by
  simpa only [domA, domB, ldD] using
    G.integral_dom_mul
      (f := fun z => z.1 - G.freqA) (g := fun z => z.2 - G.freqB)
      (measurable_fst.sub measurable_const) (measurable_snd.sub measurable_const)


omit [IsProbabilityMeasure P] in
/-- The dominance coding has second moment `E(d_A²) = V_A²`. -/
theorem integral_domA_sq : ∫ ω, G.domA ω ^ 2 ∂P = G.varA ^ 2 := by
  simpa only [domA, varA] using
    G.integral_dom_sq (f := fun z => z.1 - G.freqA)
      (measurable_fst.sub measurable_const)


omit [IsProbabilityMeasure P] in
/-- The dominance coding has second moment `E(d_B²) = V_B²`. -/
theorem integral_domB_sq : ∫ ω, G.domB ω ^ 2 ∂P = G.varB ^ 2 := by
  simpa only [domB, varB] using
    G.integral_dom_sq (f := fun z => z.2 - G.freqB)
      (measurable_snd.sub measurable_const)


/-- The additive coding at `A` and the dominance coding at `B` are uncorrelated:
`E(a_A d_B) = 0`. -/
theorem integral_addA_mul_domB : ∫ ω, G.addA ω * G.domB ω ∂P = 0 := by
  simpa only [addA, domB] using
    G.integral_add_dom
      (f := fun z => z.1 - G.freqA) (g := fun z => z.2 - G.freqB)
      (measurable_fst.sub measurable_const) (measurable_snd.sub measurable_const)
      (G.memLp_x1.sub (memLp_const G.freqA))
      (G.memLp_y1.sub (memLp_const G.freqB))
      (G.memLp_x2.sub (memLp_const G.freqA))
      (G.memLp_y2.sub (memLp_const G.freqB))
      (integral_centered G.memLp_y1)


omit [IsProbabilityMeasure P] in
private theorem varA_nonneg : 0 ≤ G.varA := integral_nonneg fun _ => sq_nonneg _

omit [IsProbabilityMeasure P] in
private theorem varB_nonneg : 0 ≤ G.varB := integral_nonneg fun _ => sq_nonneg _

/-- The correlation of the additive codings is the gametic correlation
`r = D / √(V_A V_B)`. -/
theorem addCorr_eq :
    (∫ ω, G.addA ω * G.addB ω ∂P) /
        Real.sqrt ((∫ ω, G.addA ω ^ 2 ∂P) * ∫ ω, G.addB ω ^ 2 ∂P) =
      G.ldD / Real.sqrt (G.varA * G.varB) := by
  rw [G.integral_addA_mul_addB, G.integral_addA_sq, G.integral_addB_sq,
    show 2 * G.varA * (2 * G.varB) = 2 ^ 2 * (G.varA * G.varB) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), mul_div_mul_left _ _ two_ne_zero]

/-- **Dominance LD is the square of additive LD** (Palmer et al. 2023, graphical abstract): the
correlation of the dominance codings at two loci is the square of the correlation of their
additive codings. -/
theorem domCorr_eq_addCorr_sq :
    (∫ ω, G.domA ω * G.domB ω ∂P) /
        Real.sqrt ((∫ ω, G.domA ω ^ 2 ∂P) * ∫ ω, G.domB ω ^ 2 ∂P) =
      ((∫ ω, G.addA ω * G.addB ω ∂P) /
        Real.sqrt ((∫ ω, G.addA ω ^ 2 ∂P) * ∫ ω, G.addB ω ^ 2 ∂P)) ^ 2 := by
  have hA := G.varA_nonneg
  have hB := G.varB_nonneg
  rw [G.addCorr_eq, G.integral_domA_mul_domB, G.integral_domA_sq, G.integral_domB_sq,
    ← mul_pow, Real.sqrt_sq (mul_nonneg hA hB), div_pow, Real.sq_sqrt (mul_nonneg hA hB)]

end RandomUnion

/-- The dominance encoding of a biallelic genotype `g ∈ {0, 1, 2}` (count of the allele with
frequency `p`): `p²`, `-p (1 - p)`, `(1 - p)²`. Dividing by `-p (1 - p)` gives the encoding
`-p / (1 - p)`, `1`, `-(1 - p) / p` of Palmer et al. (2023). -/
noncomputable def dominanceEncoding (p g : ℝ) : ℝ :=
  if g = 0 then p ^ 2 else if g = 1 then -(p * (1 - p)) else (1 - p) ^ 2

/-- For `0`/`1` allele indicators the dominance coding `(X₁ - p) (X₂ - p)` depends only on the
genotype `X₁ + X₂` and equals its dominance encoding. -/
theorem domCode_eq_dominanceEncoding {x1 x2 : ℝ} (h1 : x1 = 0 ∨ x1 = 1) (h2 : x2 = 0 ∨ x2 = 1)
    (p : ℝ) : (x1 - p) * (x2 - p) = dominanceEncoding p (x1 + x2) := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> norm_num [dominanceEncoding] <;> ring

end MathlibExt.Biology.StatisticalGenetics.DominanceLD
