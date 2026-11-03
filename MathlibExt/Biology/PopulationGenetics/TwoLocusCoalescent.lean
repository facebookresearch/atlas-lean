/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Linkage
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.RateMatrix
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The two-locus coalescent and the Ohta–Kimura moment system

Two neutral loci `A` and `B` at scaled recombination rate `ρ = 4 N r` in a diploid population of
size `N`, with time measured in units of `2 N` generations.

## The two-locus ancestral process for a sample of two

Follow the ancestry of two sequences at both loci backward in time (Hudson 1983; Kaplan &
Hudson 1985; Griffiths 1991; Griffiths 1981 studied the same two-locus sample moments in the
diffusion model). Every pair of ancestral lineages coalesces at rate `1` (a merger of a lineage
ancestral at `A` only with one ancestral at `B` only gives a chromosome ancestral at both loci),
and every lineage ancestral at both loci splits by recombination at rate `ρ / 2`. As long as
neither locus has found its most recent common ancestor, the configuration is one of

* `linked`: two chromosomes, each ancestral at both loci;
* `partlySplit`: one chromosome ancestral at both loci, one at `A` only, one at `B` only;
* `split`: four chromosomes, two ancestral at `A` only and two at `B` only;

and once a locus has coalesced only the other locus matters (`aCoalesced`, `bCoalesced`,
`bothCoalesced`). `twoLocusRate ρ` is the rate matrix of this chain. The coalescence time
`T_A` (resp. `T_B`) is the hitting time of `{aCoalesced, bothCoalesced}` (resp.
`{bCoalesced, bothCoalesced}`).

The moments of these hitting times are characterized by the backward (first-step) equations of
the chain: `m_A i = E_i T_A` vanishes where `A` has coalesced and solves `(Q m_A) i = -1`
elsewhere; `E_i T_A²` solves `(Q g) i = -2 m_A i`; and, since
`T_A T_B = ∫₀^{T_A ∧ T_B} ((T_A - t) + (T_B - t)) dt`, `f i = E_i (T_A T_B)` vanishes where
either locus has coalesced and solves `(Q f) i = -(m_A i + m_B i)` elsewhere. This file proves
that these linear systems have exactly one solution for `ρ ≥ 0` and computes it:
`E T_A = 1`, `Var T_A = 1`, and from two linked sequences
`Cov(T_A, T_B) = (ρ + 18) / (ρ² + 13 ρ + 18)` (Hudson 1983; Kaplan & Hudson 1985). The
identification of the solutions with path-space expectations of the chain constructed in
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path` is proved in
`MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescentPath`.

## The Ohta–Kimura moment system

Gamete frequencies `x : Bool × Bool → ℝ` follow the encoding of
`MathlibExt.Biology.PopulationGenetics.Linkage` (`linkageDiseq`, `alleleFreqFst`,
`alleleFreqSnd`). The two-locus Wright–Fisher diffusion with symmetric two-allele mutation at
rate `ν` per locus in each direction (`ν = 2 N u` for a per-generation probability `u` of
mutating to the other allele, so `ν = θ / 2` with `θ = 4 N u`) has generator (on polynomials
in the four gamete frequencies, `twoLocusGenerator`)

`L f = ½ ∑_{g,h} x_g (δ_{gh} - x_h) ∂_g ∂_h f
  + ∑_g (-(ρ/2) ε_g D + ν (x_{g'} + x_{g''} - 2 x_g)) ∂_g f`,

with `ε_g = 1` for coupling gametes `AB`, `ab` and `-1` for `Ab`, `aB`, and `g'`, `g''` the two
gametes differing from `g` at one locus. Its recombination drift is `2 N` times the
per-generation change of `Linkage.recombine` (`twoLocusGenerator_X`). Writing
`p = alleleFreqFst x true`, `q = alleleFreqSnd x true`, `D = linkageDiseq x`,
`z = (1 - 2p)(1 - 2q)` and `Π = p (1 - p) q (1 - q)`, on the simplex

* `L D² = -(3 + ρ + 8ν) D² + D z + Π`,
* `L (D z) = 4 D² - (5 + ρ/2 + 8ν) D z`,
* `L Π = D z - (2 + 8ν) Π + ν (p (1 - p) + q (1 - q))`

(Ohta & Kimura 1969, 1971; Hill & Robertson 1968 give the discrete-generation analogue).
Without mutation the three functions span an
`L`-invariant space, the closed `3 × 3` system of the moments `E D²`, `E D z`, `E Π`. For a
stationary law (`∫ L f dμ = 0` for every polynomial `f`) the first two rows give
`σ_d² = E D² / E Π = (10 + ρ + 16ν) / (22 + 13ρ + ρ² + 128ν + 24ρν + 128ν²)`, which at
`ν = 0` is Ohta and Kimura's (1971) `(10 + ρ) / (22 + 13ρ + ρ²)`. The weak stationarity
condition is what a stationary law of the diffusion satisfies (`d/dt E f = E L f`); the
existence of such a law for `ν > 0` is not proved here.

## Main results

* `isRateMatrix_twoLocusRate`: `twoLocusRate ρ` is a rate matrix for `ρ ≥ 0`.
* `eq_one_of_meanTimeA`, `eq_one_of_meanTimeB`: the mean equations force `m = 1` in every state
  where the locus has not coalesced.
* `eq_two_of_secondMomentA`: the second-moment equations force `g = 2` (variance `1`).
* `covariance_of_productMoment`: `f - m_A m_B` equals `(ρ + 18) / (ρ² + 13ρ + 18)`,
  `6 / (ρ² + 13ρ + 18)` and `4 / (ρ² + 13ρ + 18)` in the three states where neither locus has
  coalesced; `productMoment_solution` shows the systems are solvable.
* `twoLocusCov_zero`, `twoLocusCov_pos`, `twoLocusCov_le_one`, `antitoneOn_twoLocusCov`,
  `tendsto_twoLocusCov_atTop`: the covariance is `1` for complete linkage, lies in `(0, 1]`,
  decreases in `ρ`, and tends to `0`.
* `twoLocusGenerator_X`: the recombination drift is the diffusion scaling of `recombine`.
* `twoLocusGenerator_diseqSq`, `twoLocusGenerator_diseqZ`, `twoLocusGenerator_hetProd`: the
  Hill–Robertson / Ohta–Kimura closure identities.
* `IsStationaryLaw.sigmaDSq_eq`: `σ_d²` of a stationary law; `sigmaDSq_zero`,
  `tendsto_sigmaDSq_zero`: the low-mutation value `(10 + ρ) / (22 + 13ρ + ρ²)`.

## References

* R. C. Griffiths, *Neutral two-locus multiple allele models with recombination*, Theor.
  Popul. Biol. 19 (1981), 169–186.
* R. R. Hudson, *Properties of a neutral allele model with intragenic recombination*, Theor.
  Popul. Biol. 23 (1983), 183–201.
* N. L. Kaplan and R. R. Hudson, *The use of sample genealogies for studying a selectively
  neutral m-loci model with recombination*, Theor. Popul. Biol. 28 (1985), 382–396.
* R. C. Griffiths, *The two-locus ancestral graph*, in *Selected Proceedings of the Symposium
  on Applied Probability, Sheffield, 1989*, IMS Lecture Notes 18 (1991), 100–117.
* W. G. Hill and A. Robertson, *Linkage disequilibrium in finite populations*, Theor. Appl.
  Genet. 38 (1968), 226–231.
* T. Ohta and M. Kimura, *Linkage disequilibrium at steady state determined by random genetic
  drift and recurrent mutation*, Genetics 63 (1969), 229–238.
* T. Ohta and M. Kimura, *Linkage disequilibrium between two segregating nucleotide sites
  under the steady flux of mutations in a finite population*, Genetics 68 (1971), 571–580.
-/

@[expose] public section

open Filter Topology MeasureTheory MvPolynomial ProbabilityTheory Matrix
open MathlibExt.Biology.PopulationGenetics.Linkage

namespace MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent


/-! ### The two-locus ancestral process of a sample of two -/

/-- The states of the two-locus ancestral process of a sample of two sequences. -/
inductive TwoLocusState
  /-- Two chromosomes, each ancestral at both loci. -/
  | linked
  /-- One chromosome ancestral at both loci, one at `A` only and one at `B` only. -/
  | partlySplit
  /-- Four chromosomes: two ancestral at `A` only and two at `B` only. -/
  | split
  /-- Locus `A` has coalesced; two lineages remain at locus `B`. -/
  | aCoalesced
  /-- Locus `B` has coalesced; two lineages remain at locus `A`. -/
  | bCoalesced
  /-- Both loci have coalesced. -/
  | bothCoalesced
  deriving DecidableEq

namespace TwoLocusState

instance : Fintype TwoLocusState :=
  ⟨{linked, partlySplit, split, aCoalesced, bCoalesced, bothCoalesced}, by
    intro i; cases i <;> simp⟩

/-- A sum over the six states. -/
theorem sum_univ {M : Type*} [AddCommMonoid M] (f : TwoLocusState → M) :
    ∑ i, f i = f linked + f partlySplit + f split + f aCoalesced + f bCoalesced +
      f bothCoalesced := by
  change ∑ i ∈ {linked, partlySplit, split, aCoalesced, bCoalesced, bothCoalesced}, f i = _
  simp [Finset.sum_insert, add_assoc]

/-- Whether locus `A` has found its most recent common ancestor. -/
def coalescedA : TwoLocusState → Bool
  | aCoalesced | bothCoalesced => true
  | _ => false

/-- Whether locus `B` has found its most recent common ancestor. -/
def coalescedB : TwoLocusState → Bool
  | bCoalesced | bothCoalesced => true
  | _ => false

end TwoLocusState

open TwoLocusState

/-- The rate matrix of the two-locus ancestral process of a sample of two, with time in units of
`2 N` generations and `ρ = 4 N r`: coalescence at rate `1` for every pair of ancestral lineages,
recombination at rate `ρ / 2` for every lineage ancestral at both loci. -/
noncomputable def twoLocusRate (ρ : ℝ) : Matrix TwoLocusState TwoLocusState ℝ := fun i j =>
  match i, j with
  | linked, linked => -(1 + ρ)
  | linked, partlySplit => ρ
  | linked, bothCoalesced => 1
  | partlySplit, linked => 1
  | partlySplit, partlySplit => -(3 + ρ / 2)
  | partlySplit, split => ρ / 2
  | partlySplit, aCoalesced => 1
  | partlySplit, bCoalesced => 1
  | split, partlySplit => 4
  | split, split => -6
  | split, aCoalesced => 1
  | split, bCoalesced => 1
  | aCoalesced, aCoalesced => -1
  | aCoalesced, bothCoalesced => 1
  | bCoalesced, bCoalesced => -1
  | bCoalesced, bothCoalesced => 1
  | _, _ => 0

/-- For `ρ ≥ 0`, `twoLocusRate ρ` is a rate matrix. -/
theorem isRateMatrix_twoLocusRate {ρ : ℝ} (hρ : 0 ≤ ρ) : IsRateMatrix (twoLocusRate ρ) where
  nonneg_of_ne i j hij := by
    cases i <;> cases j <;> simp only [twoLocusRate] <;>
      first | exact absurd rfl hij | linarith
  sum_row i := by
    cases i <;> simp [sum_univ, twoLocusRate] <;> ring

private theorem mulVec_linked (ρ : ℝ) (m : TwoLocusState → ℝ) :
    (twoLocusRate ρ *ᵥ m) linked = -(1 + ρ) * m linked + ρ * m partlySplit + m bothCoalesced := by
  simp [mulVec, dotProduct, sum_univ, twoLocusRate]

private theorem mulVec_partlySplit (ρ : ℝ) (m : TwoLocusState → ℝ) :
    (twoLocusRate ρ *ᵥ m) partlySplit = m linked - (3 + ρ / 2) * m partlySplit +
      ρ / 2 * m split + m aCoalesced + m bCoalesced := by
  simp [mulVec, dotProduct, sum_univ, twoLocusRate]; ring

private theorem mulVec_split (ρ : ℝ) (m : TwoLocusState → ℝ) :
    (twoLocusRate ρ *ᵥ m) split = 4 * m partlySplit - 6 * m split + m aCoalesced +
      m bCoalesced := by
  simp [mulVec, dotProduct, sum_univ, twoLocusRate]; ring

private theorem mulVec_aCoalesced (ρ : ℝ) (m : TwoLocusState → ℝ) :
    (twoLocusRate ρ *ᵥ m) aCoalesced = -m aCoalesced + m bothCoalesced := by
  simp [mulVec, dotProduct, sum_univ, twoLocusRate]

private theorem mulVec_bCoalesced (ρ : ℝ) (m : TwoLocusState → ℝ) :
    (twoLocusRate ρ *ᵥ m) bCoalesced = -m bCoalesced + m bothCoalesced := by
  simp [mulVec, dotProduct, sum_univ, twoLocusRate]

/-- The common denominator `ρ² + 13 ρ + 18` of the two-locus moments. -/
def twoLocusDenom (ρ : ℝ) : ℝ := ρ ^ 2 + 13 * ρ + 18

/-- The denominator `ρ² + 13 ρ + 18` is positive for `ρ ≥ 0`. -/
theorem twoLocusDenom_pos {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < twoLocusDenom ρ := by
  unfold twoLocusDenom; positivity

/-- **Mean coalescence time at locus `A`.** For `ρ ≥ 0`, the backward equations of `E_i T_A`
(`m i = 0` where `A` has coalesced, `(Q m) i = -1` elsewhere) force `m i = 1` in every state where
`A` has not coalesced: locus `A` alone is Kingman's coalescent of two genes. -/
theorem eq_one_of_meanTimeA {ρ : ℝ} (hρ : 0 ≤ ρ) {m : TwoLocusState → ℝ}
    (h0 : ∀ i, coalescedA i = true → m i = 0)
    (h : ∀ i, coalescedA i = false → (twoLocusRate ρ *ᵥ m) i = -1) :
    ∀ i, coalescedA i = false → m i = 1 := by
  have hd := twoLocusDenom_pos hρ
  have h1 := h0 aCoalesced rfl
  have h2 := h0 bothCoalesced rfl
  have hL := h linked rfl
  have hP := h partlySplit rfl
  have hS := h split rfl
  have hB := h bCoalesced rfl
  rw [mulVec_linked] at hL
  rw [mulVec_partlySplit] at hP
  rw [mulVec_split] at hS
  rw [mulVec_bCoalesced] at hB
  rw [h1, h2] at *
  have hb : m bCoalesced = 1 := by linarith
  rw [hb] at hP hS
  unfold twoLocusDenom at hd
  intro i hi
  cases i
  · refine eq_of_sub_eq_zero ((mul_eq_zero.1 ?_).resolve_left hd.ne')
    linear_combination (-(ρ + 18)) * hL + (-6 * ρ) * hP + (-(ρ ^ 2 / 2)) * hS
  · refine eq_of_sub_eq_zero ((mul_eq_zero.1 ?_).resolve_left hd.ne')
    linear_combination (-6) * hL + (-(6 * ρ + 6)) * hP + (-(ρ * (ρ + 1) / 2)) * hS
  · refine eq_of_sub_eq_zero ((mul_eq_zero.1 ?_).resolve_left hd.ne')
    linear_combination (-4) * hL + (-(4 * ρ + 4)) * hP + (-(ρ ^ 2 / 2 + 5 * ρ / 2 + 3)) * hS
  · simp [coalescedA] at hi
  · exact hb
  · simp [coalescedA] at hi

/-- **Mean coalescence time at locus `B`** (the mirror image of `eq_one_of_meanTimeA`). -/
theorem eq_one_of_meanTimeB {ρ : ℝ} (hρ : 0 ≤ ρ) {m : TwoLocusState → ℝ}
    (h0 : ∀ i, coalescedB i = true → m i = 0)
    (h : ∀ i, coalescedB i = false → (twoLocusRate ρ *ᵥ m) i = -1) :
    ∀ i, coalescedB i = false → m i = 1 := by
  have hd := twoLocusDenom_pos hρ
  have h1 := h0 bCoalesced rfl
  have h2 := h0 bothCoalesced rfl
  have hL := h linked rfl
  have hP := h partlySplit rfl
  have hS := h split rfl
  have hA := h aCoalesced rfl
  rw [mulVec_linked] at hL
  rw [mulVec_partlySplit] at hP
  rw [mulVec_split] at hS
  rw [mulVec_aCoalesced] at hA
  rw [h1, h2] at *
  have ha : m aCoalesced = 1 := by linarith
  rw [ha] at hP hS
  unfold twoLocusDenom at hd
  intro i hi
  cases i
  · refine eq_of_sub_eq_zero ((mul_eq_zero.1 ?_).resolve_left hd.ne')
    linear_combination (-(ρ + 18)) * hL + (-6 * ρ) * hP + (-(ρ ^ 2 / 2)) * hS
  · refine eq_of_sub_eq_zero ((mul_eq_zero.1 ?_).resolve_left hd.ne')
    linear_combination (-6) * hL + (-(6 * ρ + 6)) * hP + (-(ρ * (ρ + 1) / 2)) * hS
  · refine eq_of_sub_eq_zero ((mul_eq_zero.1 ?_).resolve_left hd.ne')
    linear_combination (-4) * hL + (-(4 * ρ + 4)) * hP + (-(ρ ^ 2 / 2 + 5 * ρ / 2 + 3)) * hS
  · exact ha
  · simp [coalescedB] at hi
  · simp [coalescedB] at hi

/-- **Second moment of `T_A`.** If `m` solves the mean equations of `eq_one_of_meanTimeA` and
`g` the second-moment equations (`g i = 0` where `A` has coalesced, `(Q g) i = -2 m i`
elsewhere), then `g i = 2` where `A` has not coalesced, so the variance read off from these
equations is `2 - 1² = 1`. -/
theorem eq_two_of_secondMomentA {ρ : ℝ} (hρ : 0 ≤ ρ) {m g : TwoLocusState → ℝ}
    (hm0 : ∀ i, coalescedA i = true → m i = 0)
    (hm : ∀ i, coalescedA i = false → (twoLocusRate ρ *ᵥ m) i = -1)
    (hg0 : ∀ i, coalescedA i = true → g i = 0)
    (hg : ∀ i, coalescedA i = false → (twoLocusRate ρ *ᵥ g) i = -2 * m i) :
    ∀ i, coalescedA i = false → g i = 2 := by
  have hm1 := eq_one_of_meanTimeA hρ hm0 hm
  have hd := twoLocusDenom_pos hρ
  have h1 := hg0 aCoalesced rfl
  have h2 := hg0 bothCoalesced rfl
  have hL := hg linked rfl
  have hP := hg partlySplit rfl
  have hS := hg split rfl
  have hB := hg bCoalesced rfl
  rw [mulVec_linked, hm1 linked rfl] at hL
  rw [mulVec_partlySplit, hm1 partlySplit rfl] at hP
  rw [mulVec_split, hm1 split rfl] at hS
  rw [mulVec_bCoalesced, hm1 bCoalesced rfl] at hB
  simp only [h1, h2] at hL hP hS hB
  have hb : g bCoalesced = 2 := by linarith
  rw [hb] at hP hS
  unfold twoLocusDenom at hd
  intro i hi
  cases i
  · refine eq_of_sub_eq_zero ((mul_eq_zero.1 ?_).resolve_left hd.ne')
    linear_combination (-(ρ + 18)) * hL + (-6 * ρ) * hP + (-(ρ ^ 2 / 2)) * hS
  · refine eq_of_sub_eq_zero ((mul_eq_zero.1 ?_).resolve_left hd.ne')
    linear_combination (-6) * hL + (-(6 * ρ + 6)) * hP + (-(ρ * (ρ + 1) / 2)) * hS
  · refine eq_of_sub_eq_zero ((mul_eq_zero.1 ?_).resolve_left hd.ne')
    linear_combination (-4) * hL + (-(4 * ρ + 4)) * hP + (-(ρ ^ 2 / 2 + 5 * ρ / 2 + 3)) * hS
  · simp [coalescedA] at hi
  · exact hb
  · simp [coalescedA] at hi

/-- The covariance `Cov(T_A, T_B) = (ρ + 18) / (ρ² + 13 ρ + 18)` of the coalescence times at two
loci of two sequences sampled linked (Hudson 1983; Kaplan & Hudson 1985). -/
noncomputable def twoLocusCov (ρ : ℝ) : ℝ := (ρ + 18) / twoLocusDenom ρ

/-- **Covariance of coalescence times** (Hudson 1983; Kaplan & Hudson 1985). Let `mA`, `mB`
solve the mean equations of the two loci and `f` the product-moment equations (`f i = 0` where
either locus has coalesced, `(Q f) i = -(mA i + mB i)` where neither has). Then `f - mA mB` is
`(ρ + 18) / (ρ² + 13ρ + 18)` from `linked`, `6 / (ρ² + 13ρ + 18)` from `partlySplit` and
`4 / (ρ² + 13ρ + 18)` from `split`. This is a statement about the backward equations; that their
solutions are the path-space moments of the chain is proved in `TwoLocusCoalescentPath`. -/
theorem covariance_of_productMoment {ρ : ℝ} (hρ : 0 ≤ ρ) {mA mB f : TwoLocusState → ℝ}
    (hA0 : ∀ i, coalescedA i = true → mA i = 0)
    (hA : ∀ i, coalescedA i = false → (twoLocusRate ρ *ᵥ mA) i = -1)
    (hB0 : ∀ i, coalescedB i = true → mB i = 0)
    (hB : ∀ i, coalescedB i = false → (twoLocusRate ρ *ᵥ mB) i = -1)
    (hf0 : ∀ i, (coalescedA i || coalescedB i) = true → f i = 0)
    (hf : ∀ i, (coalescedA i || coalescedB i) = false →
      (twoLocusRate ρ *ᵥ f) i = -(mA i + mB i)) :
    f linked - mA linked * mB linked = twoLocusCov ρ ∧
      f partlySplit - mA partlySplit * mB partlySplit = 6 / twoLocusDenom ρ ∧
      f split - mA split * mB split = 4 / twoLocusDenom ρ := by
  have hA1 := eq_one_of_meanTimeA hρ hA0 hA
  have hB1 := eq_one_of_meanTimeB hρ hB0 hB
  have hd := twoLocusDenom_pos hρ
  have h1 := hf0 aCoalesced rfl
  have h2 := hf0 bCoalesced rfl
  have h3 := hf0 bothCoalesced rfl
  have hL := hf linked rfl
  have hP := hf partlySplit rfl
  have hS := hf split rfl
  rw [mulVec_linked, hA1 linked rfl, hB1 linked rfl] at hL
  rw [mulVec_partlySplit, hA1 partlySplit rfl, hB1 partlySplit rfl] at hP
  rw [mulVec_split, hA1 split rfl, hB1 split rfl] at hS
  simp only [h1, h2, h3] at hL hP hS
  rw [hA1 linked rfl, hB1 linked rfl, hA1 partlySplit rfl, hB1 partlySplit rfl, hA1 split rfl,
    hB1 split rfl, twoLocusCov, eq_div_iff hd.ne', eq_div_iff hd.ne', eq_div_iff hd.ne']
  unfold twoLocusDenom
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(ρ + 18)) * hL + (-6 * ρ) * hP + (-(ρ ^ 2 / 2)) * hS
  · linear_combination (-6) * hL + (-(6 * ρ + 6)) * hP + (-(ρ * (ρ + 1) / 2)) * hS
  · linear_combination (-4) * hL + (-(4 * ρ + 4)) * hP + (-(ρ ^ 2 / 2 + 5 * ρ / 2 + 3)) * hS

/-- The explicit solution of the product-moment equations: `1 + Cov` in the three states where
neither locus has coalesced, `0` elsewhere. -/
noncomputable def productMoment (ρ : ℝ) : TwoLocusState → ℝ
  | linked => 1 + twoLocusCov ρ
  | partlySplit => 1 + 6 / twoLocusDenom ρ
  | split => 1 + 4 / twoLocusDenom ρ
  | _ => 0

/-- The mean coalescence time at locus `A`: `1` before `A` coalesces, `0` after. -/
def meanTimeA (i : TwoLocusState) : ℝ := if coalescedA i then 0 else 1

/-- The mean coalescence time at locus `B`: `1` before `B` coalesces, `0` after. -/
def meanTimeB (i : TwoLocusState) : ℝ := if coalescedB i then 0 else 1

/-- The systems of `covariance_of_productMoment` are solvable: `meanTimeA`, `meanTimeB` and
`productMoment ρ` satisfy them. -/
theorem productMoment_solution {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∀ i, coalescedA i = false → (twoLocusRate ρ *ᵥ meanTimeA) i = -1) ∧
    (∀ i, coalescedB i = false → (twoLocusRate ρ *ᵥ meanTimeB) i = -1) ∧
    (∀ i, (coalescedA i || coalescedB i) = true → productMoment ρ i = 0) ∧
    (∀ i, (coalescedA i || coalescedB i) = false →
      (twoLocusRate ρ *ᵥ productMoment ρ) i = -(meanTimeA i + meanTimeB i)) := by
  have hd := (twoLocusDenom_pos hρ).ne'
  have hkey : (1 + ρ) * twoLocusCov ρ - ρ * (6 / twoLocusDenom ρ) = 1 := by
    rw [twoLocusCov, mul_div_assoc', mul_div_assoc', ← sub_div, div_eq_one_iff_eq hd]
    unfold twoLocusDenom
    ring
  have hC : twoLocusCov ρ = (ρ + 18) * (twoLocusDenom ρ)⁻¹ := by rw [twoLocusCov, div_eq_mul_inv]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩ <;> cases i <;>
    simp only [coalescedA, coalescedB, Bool.or_false, Bool.false_or, Bool.or_self,
      Bool.false_eq_true, Bool.true_eq_false] at hi <;>
    simp only [mulVec_linked, mulVec_partlySplit, mulVec_split, mulVec_aCoalesced,
      mulVec_bCoalesced, meanTimeA, meanTimeB, coalescedA, coalescedB, productMoment,
      Bool.false_eq_true, ↓reduceIte] <;>
    first | ring1 | linear_combination (-1) * hkey | linear_combination hC

/-- Complete linkage: `Cov(T_A, T_B) = 1 = Var T_A`. -/
theorem twoLocusCov_zero : twoLocusCov 0 = 1 := by
  norm_num [twoLocusCov, twoLocusDenom]

/-- The covariance is positive for `ρ ≥ 0`. -/
theorem twoLocusCov_pos {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < twoLocusCov ρ :=
  div_pos (by linarith) (twoLocusDenom_pos hρ)

/-- The covariance is at most `Var T_A = 1` for `ρ ≥ 0` (outside this domain the formula can
exceed `1`; e.g. `twoLocusCov (-1) = 17 / 6`). -/
theorem twoLocusCov_le_one {ρ : ℝ} (hρ : 0 ≤ ρ) : twoLocusCov ρ ≤ 1 := by
  rw [twoLocusCov, div_le_one (twoLocusDenom_pos hρ), twoLocusDenom]
  nlinarith

/-- The covariance decreases with the recombination rate. -/
theorem antitoneOn_twoLocusCov : AntitoneOn twoLocusCov (Set.Ici 0) := by
  intro a ha b hb hab
  rw [Set.mem_Ici] at ha hb
  rw [twoLocusCov, twoLocusCov, div_le_div_iff₀ (twoLocusDenom_pos hb) (twoLocusDenom_pos ha),
    twoLocusDenom, twoLocusDenom]
  nlinarith [mul_nonneg (sub_nonneg.2 hab)
    (by positivity : (0 : ℝ) ≤ a * b + 18 * a + 18 * b + 216)]

/-- Free recombination: `Cov(T_A, T_B) → 0` as `ρ → ∞`. -/
theorem tendsto_twoLocusCov_atTop : Tendsto twoLocusCov atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun ρ : ℝ => 2 / ρ) atTop (𝓝 0)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with ρ hρ using (twoLocusCov_pos hρ).le
  · filter_upwards [eventually_ge_atTop 18] with ρ hρ
    rw [twoLocusCov, div_le_div_iff₀ (twoLocusDenom_pos (by linarith)) (by linarith),
      twoLocusDenom]
    nlinarith


/-! ### The Ohta–Kimura moment system -/

/-- The linkage disequilibrium `D = x_AB x_ab - x_Ab x_aB` as a polynomial. -/
noncomputable def diseqPoly : MvPolynomial (Bool × Bool) ℝ :=
  X (true, true) * X (false, false) - X (true, false) * X (false, true)

/-- The frequency `p = x_AB + x_Ab` of allele `A` as a polynomial. -/
noncomputable def freqFstPoly : MvPolynomial (Bool × Bool) ℝ := X (true, true) + X (true, false)

/-- The frequency `q = x_AB + x_aB` of allele `B` as a polynomial. -/
noncomputable def freqSndPoly : MvPolynomial (Bool × Bool) ℝ := X (true, true) + X (false, true)

/-- `D (1 - 2p)(1 - 2q)` as a polynomial. -/
noncomputable def diseqZPoly : MvPolynomial (Bool × Bool) ℝ :=
  diseqPoly * (1 - 2 * freqFstPoly) * (1 - 2 * freqSndPoly)

/-- `Π = p (1 - p) q (1 - q)` as a polynomial. -/
noncomputable def hetProdPoly : MvPolynomial (Bool × Bool) ℝ :=
  freqFstPoly * (1 - freqFstPoly) * freqSndPoly * (1 - freqSndPoly)

/-- The generator of the two-locus Wright–Fisher diffusion on polynomials in the gamete
frequencies, time in units of `2 N` generations, `ρ = 4 N r`, symmetric mutation at rate `ν` per
locus in each direction (`ν = θ / 2`, `θ = 4 N u`):
`L f = ½ ∑ x_g (δ_{gh} - x_h) ∂_g ∂_h f + ∑ (-(ρ/2) ε_g D + ν (x_{g'} + x_{g''} - 2 x_g)) ∂_g f`. -/
noncomputable def twoLocusGenerator (ρ ν : ℝ) (f : MvPolynomial (Bool × Bool) ℝ) :
    MvPolynomial (Bool × Bool) ℝ :=
  ∑ g, ∑ h, C (1 / 2 : ℝ) * X g * ((if g = h then 1 else 0) - X h) * pderiv g (pderiv h f) +
    ∑ g, (C (-(ρ / 2) * (if g.1 = g.2 then 1 else -1)) * diseqPoly +
      C ν * (X (!g.1, g.2) + X (g.1, !g.2) - 2 * X g)) * pderiv g f

private theorem sum_bb {M : Type*} [AddCommMonoid M] (f : Bool × Bool → M) :
    ∑ g, f g = f (true, true) + f (true, false) + f (false, true) + f (false, false) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]; abel

private theorem pderiv_two (g : Bool × Bool) :
    pderiv g (2 : MvPolynomial (Bool × Bool) ℝ) = 0 := by
  rw [show (2 : MvPolynomial (Bool × Bool) ℝ) = C 2 from (map_ofNat C 2).symm]
  exact pderiv_C

/-- Without mutation the drift of a gamete frequency is `2 N` times its per-generation change
under `Linkage.recombine` when `ρ = 4 N r`. -/
theorem twoLocusGenerator_X {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) {N r ρ : ℝ}
    (hρ : ρ = 4 * N * r) (g : Bool × Bool) :
    eval x (twoLocusGenerator ρ 0 (X g)) = 2 * N * (recombine r x g - x g) := by
  rw [recombine_eq_sub hx, hρ]
  obtain ⟨a, b⟩ := g
  cases a <;> cases b <;>
    simp only [twoLocusGenerator, diseqPoly, sum_bb, map_sub, map_mul, pderiv_X,
      Pi.single_apply, Derivation.map_one_eq_zero, map_zero, eval_X, eval_C, linkageDiseq,
      Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, and_self, and_false, false_and,
      ite_true, ite_false, mul_one, mul_zero, zero_mul, add_zero, zero_add] <;>
    ring

/-- **Hill–Robertson / Ohta–Kimura, first row.** On the simplex,
`L D² = -(3 + ρ + 8ν) D² + D (1 - 2p)(1 - 2q) + p (1 - p) q (1 - q)` (for all real `ρ`, `ν`). -/
theorem twoLocusGenerator_diseqSq {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) (ρ ν : ℝ) :
    eval x (twoLocusGenerator ρ ν (diseqPoly ^ 2)) =
      -(3 + ρ + 8 * ν) * linkageDiseq x ^ 2 +
        linkageDiseq x * (1 - 2 * alleleFreqFst x true) * (1 - 2 * alleleFreqSnd x true) +
        alleleFreqFst x true * (1 - alleleFreqFst x true) * alleleFreqSnd x true *
          (1 - alleleFreqSnd x true) := by
  rw [sum_bb] at hx
  simp only [twoLocusGenerator, diseqPoly, sum_bb, sq, map_add, map_sub, map_mul,
    Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, eval_X, eval_C,
    map_ofNat, linkageDiseq, alleleFreqFst, alleleFreqSnd, Fintype.sum_bool]
  simp only [Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, and_self, and_false,
    false_and, ite_true, ite_false, Bool.not_true, Bool.not_false, map_zero, map_one,
    Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, zero_sub]
  set a := x (true, true)
  set b := x (true, false)
  set c := x (false, true)
  set d := x (false, false)
  linear_combination
    (-ρ * d ^ 2 * a ^ 2 + 2 * ρ * d * c * b * a - ρ * c ^ 2 * b ^ 2 - 3 * d * a ^ 2 + d * a +
      2 * c * b * a - c * a ^ 2 + c * a - b * a ^ 2 + b * a - a ^ 3 + a ^ 2) * hx

/-- **Hill–Robertson / Ohta–Kimura, second row.** On the simplex,
`L (D z) = 4 D² - (5 + ρ/2 + 8ν) D z` with `z = (1 - 2p)(1 - 2q)`. -/
theorem twoLocusGenerator_diseqZ {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) (ρ ν : ℝ) :
    eval x (twoLocusGenerator ρ ν diseqZPoly) =
      4 * linkageDiseq x ^ 2 - (5 + ρ / 2 + 8 * ν) *
        (linkageDiseq x * (1 - 2 * alleleFreqFst x true) * (1 - 2 * alleleFreqSnd x true)) := by
  rw [sum_bb] at hx
  simp only [twoLocusGenerator, diseqPoly, diseqZPoly, freqFstPoly, freqSndPoly, sum_bb, sq,
    map_add, map_sub, map_mul, Derivation.leibniz, pderiv_two, pderiv_X, Pi.single_apply,
    smul_eq_mul, eval_X, eval_C,
    map_ofNat, linkageDiseq, alleleFreqFst, alleleFreqSnd, Fintype.sum_bool]
  simp only [Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, and_self, and_false,
    false_and, ite_true, ite_false, Bool.not_true, Bool.not_false, map_zero, map_one,
    Derivation.map_one_eq_zero, mul_one, mul_zero, zero_mul, add_zero,
    zero_add, sub_zero, zero_sub]
  set a := x (true, true)
  set b := x (true, false)
  set c := x (false, true)
  set d := x (false, false)
  linear_combination
    (-(d * a - c * b) * (-8 * ν * c - 8 * ν * b - 16 * ν * a + 8 * ν + 4 * ρ * c * b +
      4 * ρ * c * a - 2 * ρ * c + 4 * ρ * b * a - 2 * ρ * b + 4 * ρ * a ^ 2 - 4 * ρ * a + ρ +
      8 * a) / 2) * hx

/-- **Hill–Robertson / Ohta–Kimura, third row.** On the simplex,
`L Π = D z - (2 + 8ν) Π + ν (p (1 - p) + q (1 - q))`; for `ν = 0` the three rows close. -/
theorem twoLocusGenerator_hetProd {x : Bool × Bool → ℝ} (hx : ∑ g, x g = 1) (ρ ν : ℝ) :
    eval x (twoLocusGenerator ρ ν hetProdPoly) =
      linkageDiseq x * (1 - 2 * alleleFreqFst x true) * (1 - 2 * alleleFreqSnd x true) -
        (2 + 8 * ν) * (alleleFreqFst x true * (1 - alleleFreqFst x true) * alleleFreqSnd x true *
          (1 - alleleFreqSnd x true)) +
        ν * (alleleFreqFst x true * (1 - alleleFreqFst x true) +
          alleleFreqSnd x true * (1 - alleleFreqSnd x true)) := by
  rw [sum_bb] at hx
  simp only [twoLocusGenerator, hetProdPoly, freqFstPoly, freqSndPoly, sum_bb, map_add,
    map_sub, map_mul, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul, eval_X,
    eval_C,
    map_ofNat, linkageDiseq, alleleFreqFst, alleleFreqSnd, Fintype.sum_bool]
  simp only [Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, and_self, and_false,
    false_and, ite_true, ite_false, Bool.not_true, Bool.not_false, map_zero, map_one,
    Derivation.map_one_eq_zero, mul_one, mul_zero, zero_mul, one_mul, add_zero,
    zero_add, sub_zero, zero_sub]
  set a := x (true, true)
  set b := x (true, false)
  set c := x (false, true)
  set d := x (false, false)
  linear_combination
    (2 * ν * c ^ 2 * b + 2 * ν * c ^ 2 * a - ν * c ^ 2 + 2 * ν * c * b ^ 2 + 8 * ν * c * b * a
      - 4 * ν * c * b + 6 * ν * c * a ^ 2 - 6 * ν * c * a + ν * c + 2 * ν * b ^ 2 * a -
      ν * b ^ 2 + 6 * ν * b * a ^ 2 - 6 * ν * b * a + ν * b + 4 * ν * a ^ 3 - 6 * ν * a ^ 2 +
      2 * ν * a - 4 * c * b * a - 4 * c * a ^ 2 + 2 * c * a - 4 * b * a ^ 2 + 2 * b * a -
      4 * a ^ 3 + 4 * a ^ 2 - a) * hx

/-- A **stationary law** of the two-locus diffusion in the weak (basic adjoint) sense: a
probability measure on the gamete-frequency simplex with `∫ L f dμ = 0` for every polynomial
`f`. -/
structure IsStationaryLaw (ρ ν : ℝ) (μ : Measure (Bool × Bool → ℝ)) : Prop where
  /-- `μ` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure μ
  /-- `μ` lives on the simplex of gamete frequencies. -/
  ae_mem_simplex : ∀ᵐ x ∂μ, (∀ g, 0 ≤ x g) ∧ ∑ g, x g = 1
  /-- The expected generator vanishes on polynomials. -/
  integral_generator : ∀ f, ∫ x, eval x (twoLocusGenerator ρ ν f) ∂μ = 0

private theorem integrable_of_continuous {ρ ν : ℝ} {μ : Measure (Bool × Bool → ℝ)}
    (hμ : IsStationaryLaw ρ ν μ) {f : (Bool × Bool → ℝ) → ℝ} (hf : Continuous f) :
    Integrable f μ := by
  have := hμ.isProbabilityMeasure
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ : Bool × Bool => isCompact_Icc (a := (0 : ℝ))
    (b := 1)).exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [hμ.ae_mem_simplex] with x hx
  refine hC x fun g _ => ⟨hx.1 g, ?_⟩
  rw [← hx.2]
  exact Finset.single_le_sum (fun h _ => hx.1 h) (Finset.mem_univ g)

/-- The stationary standardized disequilibrium
`σ_d² = (10 + ρ + 16ν) / (22 + 13ρ + ρ² + 128ν + 24ρν + 128ν²)`. -/
noncomputable def sigmaDSq (ρ ν : ℝ) : ℝ :=
  (10 + ρ + 16 * ν) / (22 + 13 * ρ + ρ ^ 2 + 128 * ν + 24 * ρ * ν + 128 * ν ^ 2)

/-- **Ohta–Kimura `σ_d²`.** For a stationary law with `ρ, ν ≥ 0` and `E Π > 0`,
`E D² / E[p (1 - p) q (1 - q)] = sigmaDSq ρ ν`. -/
theorem IsStationaryLaw.sigmaDSq_eq {ρ ν : ℝ} (hρ : 0 ≤ ρ) (hν : 0 ≤ ν)
    {μ : Measure (Bool × Bool → ℝ)} (hμ : IsStationaryLaw ρ ν μ)
    (hpos : 0 < ∫ x, alleleFreqFst x true * (1 - alleleFreqFst x true) * alleleFreqSnd x true *
      (1 - alleleFreqSnd x true) ∂μ) :
    (∫ x, linkageDiseq x ^ 2 ∂μ) / (∫ x, alleleFreqFst x true * (1 - alleleFreqFst x true) *
      alleleFreqSnd x true * (1 - alleleFreqSnd x true) ∂μ) = sigmaDSq ρ ν := by
  have hint : ∀ f : (Bool × Bool → ℝ) → ℝ, Continuous f → Integrable f μ :=
    fun f hf => integrable_of_continuous hμ hf
  have hp : Continuous fun x : Bool × Bool → ℝ => alleleFreqFst x true := by
    simp only [alleleFreqFst, Fintype.sum_bool]; fun_prop
  have hq : Continuous fun x : Bool × Bool → ℝ => alleleFreqSnd x true := by
    simp only [alleleFreqSnd, Fintype.sum_bool]; fun_prop
  have hD : Continuous linkageDiseq := by unfold linkageDiseq; fun_prop
  have iD : Integrable (fun x => linkageDiseq x ^ 2) μ := hint _ (by fun_prop)
  have iZ : Integrable (fun x => linkageDiseq x * (1 - 2 * alleleFreqFst x true) *
      (1 - 2 * alleleFreqSnd x true)) μ := hint _ (by fun_prop)
  have iP : Integrable (fun x => alleleFreqFst x true * (1 - alleleFreqFst x true) *
      alleleFreqSnd x true * (1 - alleleFreqSnd x true)) μ := hint _ (by fun_prop)
  have iDZ : Integrable (fun x => -(3 + ρ + 8 * ν) * linkageDiseq x ^ 2 +
      linkageDiseq x * (1 - 2 * alleleFreqFst x true) * (1 - 2 * alleleFreqSnd x true)) μ :=
    (iD.const_mul _).add iZ
  have e1 := hμ.integral_generator (diseqPoly ^ 2)
  have e2 := hμ.integral_generator diseqZPoly
  rw [integral_congr_ae (hμ.ae_mem_simplex.mono fun x hx =>
    twoLocusGenerator_diseqSq hx.2 ρ ν), integral_add iDZ iP, integral_add (iD.const_mul _) iZ,
    integral_const_mul] at e1
  rw [integral_congr_ae (hμ.ae_mem_simplex.mono fun x hx =>
    twoLocusGenerator_diseqZ hx.2 ρ ν), integral_sub (iD.const_mul _) (iZ.const_mul _),
    integral_const_mul, integral_const_mul] at e2
  have hden : 0 < 22 + 13 * ρ + ρ ^ 2 + 128 * ν + 24 * ρ * ν + 128 * ν ^ 2 := by positivity
  rw [sigmaDSq, div_eq_div_iff hpos.ne' hden.ne']
  linear_combination (-(10 + ρ + 16 * ν)) * e1 + (-2) * e2

/-- The low-mutation value `σ_d² = (10 + ρ) / (22 + 13ρ + ρ²)` (Ohta & Kimura 1971). -/
theorem sigmaDSq_zero (ρ : ℝ) : sigmaDSq ρ 0 = (10 + ρ) / (22 + 13 * ρ + ρ ^ 2) := by
  simp [sigmaDSq]

/-- `σ_d² → (10 + ρ) / (22 + 13ρ + ρ²)` as the mutation rate tends to `0`, for `ρ ≥ 0`. -/
theorem tendsto_sigmaDSq_zero {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Tendsto (sigmaDSq ρ) (𝓝 0) (𝓝 ((10 + ρ) / (22 + 13 * ρ + ρ ^ 2))) := by
  have h : ContinuousAt (sigmaDSq ρ) 0 := by
    unfold sigmaDSq
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    positivity
  simpa [sigmaDSq_zero] using h.tendsto

end MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent
