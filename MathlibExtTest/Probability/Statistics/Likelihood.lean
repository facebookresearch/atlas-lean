/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Likelihood
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Tactic.Linarith

/-!
# Tests for iid likelihood, MLE maps, and induced likelihood (Casella–Berger §7.2.2)

Full source gate: genuine normalized finite `Bool` family with all-sample MLE,
wrong-map rejection, flat model with two distinct MLE maps, open-interval
Bernoulli nonattained supremum with explicit improvement and MLE nonexistence,
endpoints, `n = 0`, empty parameter/sample, zero/unnormalized rejection,
infinite density on a null singleton retained in the quantifier, and
whole-fiber induced likelihood (many-to-one, injective, constant,
vector-valued, off-image, zero, continuous unbounded with supremum `∞`).

Source locators only: normalized `text.txt` 11226–11237 (iid product and
complete MLE map) and 11335–11359 (induced fiber supremum);
raw OCR inspected directly by Muse. No source text is reproduced here.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory

open scoped BigOperators ENNReal

/-- Point-mass density on `Bool`: mass `1` at the parameter value. -/
private def boolDiracDens (θ x : Bool) : ℝ≥0∞ :=
  if x = θ then 1 else 0

/-- Genuine normalized finite population family under counting measure. -/
private def boolDirac : NormalizedDensityFamily Bool Bool Measure.count where
  dens := boolDiracDens
  measurable := fun _ => Measurable.of_discrete.aemeasurable
  normalized := by
    intro θ
    rw [lintegral_count, tsum_fintype, Fintype.sum_bool]
    cases θ <;> simp [boolDiracDens]

/-- Projection rewrite for the point-mass density. -/
private theorem boolDirac_dens (θ x : Bool) :
    boolDirac.dens θ x = (if x = θ then (1 : ℝ≥0∞) else 0) :=
  rfl

/-- The derived population law is a probability measure. -/
example (θ : Bool) : IsProbabilityMeasure (boolDirac.law θ) :=
  boolDirac.isProbabilityMeasure_law θ

/-- Genuine all-sample MLE map at `n = 1`: estimate the observed bit. -/
example : boolDirac.IsMaximumLikelihoodEstimator 1 (fun x => x 0) := by
  rw [NormalizedDensityFamily.isMaximumLikelihoodEstimator_iff]
  intro x θ
  simp only [NormalizedDensityFamily.iidLikelihood_apply, Fin.prod_univ_one,
    boolDirac_dens, ite_true]
  by_cases h : x 0 = θ
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact zero_le

/-- Canonical wrong map (negated bit) is rejected at a witnessing sample. -/
example : ¬ boolDirac.IsMaximumLikelihoodEstimator 1 (fun x => !(x 0)) := by
  rw [NormalizedDensityFamily.isMaximumLikelihoodEstimator_iff]
  intro h
  have h0 := h (fun _ => false) false
  simp only [NormalizedDensityFamily.iidLikelihood_apply, Fin.prod_univ_one,
    boolDirac_dens] at h0
  simp at h0

/-- Separately packaged point-mass density: mass `1` when parameters agree. -/
private def boolDiracAltDens (θ x : Bool) : ℝ≥0∞ :=
  if θ = x then 1 else 0

/-- Separately packaged genuine normalized Dirac-equivalent family. -/
private def boolDiracAlt : NormalizedDensityFamily Bool Bool Measure.count where
  dens := boolDiracAltDens
  measurable := fun _ => Measurable.of_discrete.aemeasurable
  normalized := by
    intro θ
    rw [lintegral_count, tsum_fintype, Fintype.sum_bool]
    cases θ <;> simp [boolDiracAltDens]

/-- Projection rewrite for the repackaged point-mass density. -/
private theorem boolDiracAlt_dens (θ x : Bool) :
    boolDiracAlt.dens θ x = (if θ = x then (1 : ℝ≥0∞) else 0) :=
  rfl

/-- The repackaged family equals `boolDirac` by density extensionality. -/
private theorem boolDiracAlt_eq : boolDiracAlt = boolDirac := by
  ext θ x
  simp only [boolDiracAlt_dens, boolDirac_dens]
  by_cases h : x = θ
  · subst h; rfl
  · simp [h, Ne.symm h]

/-- Transported one-sample likelihood through density-family extensionality. -/
example : boolDiracAlt.iidLikelihood 1 true (fun _ => true) = 1 := by
  rw [boolDiracAlt_eq]
  simp [NormalizedDensityFamily.iidLikelihood_apply, boolDirac_dens]

/-- Zero densities integrate to `0`, never `1`: malformed models cannot
be normalized. -/
example : (∫⁻ _x : Bool, (0 : ℝ≥0∞) ∂Measure.count) ≠ 1 := by
  simp

/-- No normalized family can have identically zero densities. -/
example : ¬ ∃ F : NormalizedDensityFamily Bool Bool Measure.count,
    ∀ θ x, F.dens θ x = 0 := by
  rintro ⟨F, h⟩
  have h1 := F.normalized false
  have h0 : (∫⁻ x, F.dens false x ∂Measure.count) = 0 := by
    simp [h false]
  rw [h0] at h1
  exact zero_ne_one h1

/-- At `n = 0` every map is an MLE: the empty product is constantly `1`. -/
example (θhat : (Fin 0 → Bool) → Bool) :
    boolDirac.IsMaximumLikelihoodEstimator 0 θhat := by
  rw [NormalizedDensityFamily.isMaximumLikelihoodEstimator_iff]
  intro x θ
  simp

/-- Empty parameter family: all fields hold vacuously. -/
private def emptyParam : NormalizedDensityFamily Bool Empty Measure.count where
  dens := fun θ => nomatch θ
  measurable := fun θ => nomatch θ
  normalized := fun θ => nomatch θ

/-- False antecedent: over an empty parameter domain any hypothetical
estimator vacuously satisfies the MLE predicate. -/
example (θhat : (Fin 1 → Bool) → Empty) :
    emptyParam.IsMaximumLikelihoodEstimator 1 θhat := by
  rw [NormalizedDensityFamily.isMaximumLikelihoodEstimator_iff]
  intro x θ
  exact nomatch θ

/-- Flat density on `Unit`: constant `1`, independent of the parameter. -/
private def flatUnitDens (_ : Bool) (_ : Unit) : ℝ≥0∞ := 1

/-- Flat normalized family under counting measure: identical laws. -/
private def flatUnit : NormalizedDensityFamily Unit Bool Measure.count where
  dens := flatUnitDens
  measurable := fun _ => measurable_const.aemeasurable
  normalized := by
    intro θ
    rw [lintegral_count, tsum_fintype, Fintype.sum_unique]
    simp [flatUnitDens]

/-- Flat likelihood is constantly `1`. -/
private theorem flatUnit_likelihood (n : ℕ) (θ : Bool) (x : Fin n → Unit) :
    flatUnit.iidLikelihood n θ x = 1 := by
  simp only [NormalizedDensityFamily.iidLikelihood_apply]
  show (∏ i, flatUnitDens θ (x i)) = 1
  simp [flatUnitDens]

/-- First flat MLE map: constantly `true`. -/
example : flatUnit.IsMaximumLikelihoodEstimator 1 (fun _ => true) := by
  rw [NormalizedDensityFamily.isMaximumLikelihoodEstimator_iff]
  intro x θ
  simp only [flatUnit_likelihood]
  exact le_rfl

/-- Second flat MLE map: constantly `false`. -/
example : flatUnit.IsMaximumLikelihoodEstimator 1 (fun _ => false) := by
  rw [NormalizedDensityFamily.isMaximumLikelihoodEstimator_iff]
  intro x θ
  simp only [flatUnit_likelihood]
  exact le_rfl

/-- The two flat MLE maps are distinct. -/
example : (fun _ : (Fin 1 → Unit) => true) ≠ (fun _ => false) := by
  intro h
  have h0 : (true : Bool) = false := congrFun h (fun _ => ())
  exact absurd h0 (by simp)

/-- Open success-probability interval `(0,1)` as a subtype. -/
private abbrev OpenProb := {p : ℝ // 0 < p ∧ p < 1}

/-- Noisy two-outcome density: `ofReal p` on `true`, `ofReal (1-p)` on `false`. -/
private def openBernoulliDens (p : OpenProb) (b : Bool) : ℝ≥0∞ :=
  match b with
  | true => ENNReal.ofReal p.val
  | false => ENNReal.ofReal (1 - p.val)

/-- Normalized open-interval Bernoulli family under counting measure. -/
private def openBernoulli : NormalizedDensityFamily Bool OpenProb Measure.count where
  dens := openBernoulliDens
  measurable := fun _ => Measurable.of_discrete.aemeasurable
  normalized := by
    intro p
    obtain ⟨hp0, hp1⟩ := p.property
    have h0 : (0 : ℝ) ≤ p.val := le_of_lt hp0
    have h1 : (0 : ℝ) ≤ 1 - p.val := by linarith
    rw [lintegral_count, tsum_fintype, Fintype.sum_bool]
    show ENNReal.ofReal p.val + ENNReal.ofReal (1 - p.val) = 1
    rw [← ENNReal.ofReal_add h0 h1]
    have hsum : p.val + (1 - p.val) = 1 := by ring
    rw [hsum, ENNReal.ofReal_one]

/-- Likelihood of the all-success sample is `ofReal p`. -/
private theorem openBernoulli_success (p : OpenProb) :
    openBernoulli.iidLikelihood 1 p (fun _ => true) = ENNReal.ofReal p.val := by
  simp only [NormalizedDensityFamily.iidLikelihood_apply, Fin.prod_univ_one]
  rfl

/-- Explicit improving parameter `(p+1)/2` for the all-success sample. -/
private theorem openBernoulli_improved (p : OpenProb) :
    ∃ q : OpenProb, openBernoulli.iidLikelihood 1 p (fun _ => true) <
      openBernoulli.iidLikelihood 1 q (fun _ => true) := by
  obtain ⟨hp0, hp1⟩ := p.property
  refine ⟨⟨(p.val + 1) / 2, by constructor <;> linarith⟩, ?_⟩
  rw [openBernoulli_success, openBernoulli_success]
  rw [ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : ℝ) < (p.val + 1) / 2)]
  linarith

/-- No all-sample MLE map exists on the open interval. -/
example : ¬∃ θhat : (Fin 1 → Bool) → OpenProb,
    openBernoulli.IsMaximumLikelihoodEstimator 1 θhat := by
  rintro ⟨θhat, hMLE⟩
  rw [NormalizedDensityFamily.isMaximumLikelihoodEstimator_iff] at hMLE
  obtain ⟨q, hlt⟩ := openBernoulli_improved (θhat (fun _ => true))
  exact (not_le_of_gt hlt) (hMLE (fun _ => true) q)

/-- `n = 0` likelihood is the empty product `1`. -/
example (θ : Bool) (x : Fin 0 → Bool) : boolDirac.iidLikelihood 0 θ x = 1 := by
  simp

/-- Endpoint `1`: all-success likelihood at `true` is `1`. -/
example : boolDirac.iidLikelihood 1 true (fun _ => true) = 1 := by
  simp [NormalizedDensityFamily.iidLikelihood_apply, boolDirac_dens]

/-- Impossible observation: all-success likelihood at `false` is `0`. -/
example : boolDirac.iidLikelihood 1 false (fun _ => true) = 0 := by
  simp [NormalizedDensityFamily.iidLikelihood_apply, boolDirac_dens]

/-- Endpoint `0`: all-failure likelihood at `false` is `1`. -/
example : boolDirac.iidLikelihood 1 false (fun _ => false) = 1 := by
  simp [NormalizedDensityFamily.iidLikelihood_apply, boolDirac_dens]

/-- Impossible observation: all-failure likelihood at `true` is `0`. -/
example : boolDirac.iidLikelihood 1 true (fun _ => false) = 0 := by
  simp [NormalizedDensityFamily.iidLikelihood_apply, boolDirac_dens]

/-- The empty-sample space is nonempty. -/
example : Nonempty (Fin 0 → Bool) := ⟨Fin.elim0⟩

/-- No map into an empty parameter domain from the nonempty empty-sample space. -/
example (f : (Fin 0 → Bool) → Empty) : False := nomatch f Fin.elim0

/-- No normalized density on an empty sample space for inhabited parameters. -/
example : ¬∃ _ : NormalizedDensityFamily Empty Bool Measure.count, True := by
  rintro ⟨F, _⟩
  have h1 := F.normalized true
  have h0 : (∫⁻ x, F.dens true x ∂Measure.count) = 0 := by
    rw [lintegral_count, tsum_fintype, Fintype.sum_empty]
  rw [h0] at h1
  exact zero_ne_one h1

/-- Constant `∞` densities integrate to `∞`, never `1`. -/
example : (∫⁻ _x : Bool, (∞ : ℝ≥0∞) ∂Measure.count) ≠ 1 := by
  rw [lintegral_count, tsum_fintype, Fintype.sum_bool]
  simp

/-- No normalized family can have identically infinite densities. -/
example : ¬∃ F : NormalizedDensityFamily Bool Bool Measure.count,
    ∀ θ x, F.dens θ x = ∞ := by
  rintro ⟨F, h⟩
  have h1 := F.normalized false
  have h0 : (∫⁻ x, F.dens false x ∂Measure.count) = ∞ := by
    rw [lintegral_count, tsum_fintype, Fintype.sum_bool, h false true, h false false]
    simp
  rw [h0] at h1
  exact ENNReal.top_ne_one h1

/-- Dirac dominating measure at `false`: `{true}` is null. -/
private noncomputable abbrev diracFalse : Measure Bool := Measure.dirac false

/-- Spike density: `∞` at the null point `true`, `1` at `false`. -/
private def spikeDens (_ : Unit) (b : Bool) : ℝ≥0∞ :=
  match b with
  | true => ∞
  | false => 1

/-- Normalized spike family: infinite value on a null singleton. -/
private def spikeFamily : NormalizedDensityFamily Bool Unit diracFalse where
  dens := spikeDens
  measurable := fun _ => Measurable.of_discrete.aemeasurable
  normalized := by
    intro u
    show (∫⁻ x, spikeDens u x ∂(Measure.dirac false)) = 1
    rw [lintegral_dirac]
    rfl

/-- The spike singleton is null under the Dirac dominating measure. -/
example : diracFalse {true} = 0 := by
  simp [diracFalse]

/-- Infinite density value at the null observation. -/
example : spikeFamily.dens () true = ∞ := rfl

/-- Infinite likelihood at the null observation is retained. -/
example : spikeFamily.iidLikelihood 1 () (fun _ => true) = ∞ := by
  simp only [NormalizedDensityFamily.iidLikelihood_apply, Fin.prod_univ_one]
  rfl

/-- Subsingleton MLE still quantifies over the infinite null observation. -/
example : spikeFamily.IsMaximumLikelihoodEstimator 1 (fun _ => ()) := by
  rw [NormalizedDensityFamily.isMaximumLikelihoodEstimator_iff]
  intro x θ
  cases θ
  exact le_rfl

/-- Product Dirac density at `p.1 && p.2`: genuine normalized family. -/
private def prodDens (p : Bool × Bool) (b : Bool) : ℝ≥0∞ :=
  if b = (p.1 && p.2) then 1 else 0

private def prodFamily : NormalizedDensityFamily Bool (Bool × Bool) Measure.count where
  dens := prodDens
  measurable := fun _ => Measurable.of_discrete.aemeasurable
  normalized := by
    intro p
    rw [lintegral_count, tsum_fintype, Fintype.sum_bool]
    cases hp : (p.1 && p.2) <;> simp [prodDens, hp]

/-- Many-to-one transformation: first projection (non-constant, 2-to-1). -/
private def prodTau : Bool × Bool → Bool := Prod.fst

/-- Likelihood in the `true` fiber: `(true,true)` gives `1`. -/
private theorem prod_true_true :
    prodFamily.iidLikelihood 1 (true, true) (fun _ => true) = 1 := by
  simp only [NormalizedDensityFamily.iidLikelihood_apply, Fin.prod_univ_one]
  show prodDens (true, true) true = 1
  simp [prodDens]

/-- Likelihood in the `true` fiber: `(true,false)` gives `0` (zero in fiber). -/
private theorem prod_true_false :
    prodFamily.iidLikelihood 1 (true, false) (fun _ => true) = 0 := by
  simp only [NormalizedDensityFamily.iidLikelihood_apply, Fin.prod_univ_one]
  show prodDens (true, false) true = 0
  simp [prodDens]

/-- Whole-fiber induced value over `true` is the larger value `1`. -/
private theorem prod_induced_true :
    prodFamily.inducedLikelihood 1 prodTau (fun _ => true)
      ⟨true, (true, true), rfl⟩ = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro θ
    simp only [NormalizedDensityFamily.iidLikelihood_apply, Fin.prod_univ_one]
    show prodDens θ.val true ≤ 1
    simp only [prodDens]
    by_cases h : (true : Bool) = (θ.val.1 && θ.val.2)
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact zero_le
  · have hw : prodTau (true, true) =
        (⟨true, (true, true), rfl⟩ : Set.range prodTau).val := rfl
    have hle := le_iSup (fun θ : {θ : Bool × Bool // prodTau θ =
        (⟨true, (true, true), rfl⟩ : Set.range prodTau).val} =>
      prodFamily.iidLikelihood 1 θ.val (fun _ => true)) ⟨(true, true), hw⟩
    rw [prod_true_true] at hle
    exact hle

example :
    prodFamily.inducedLikelihood 1 prodTau (fun _ => true)
      ⟨true, (true, true), rfl⟩ = 1 :=
  prod_induced_true

/-- Arbitrary lower preimage is not the induced value. -/
example :
    prodFamily.inducedLikelihood 1 prodTau (fun _ => true)
      ⟨true, (true, true), rfl⟩ ≠
      prodFamily.iidLikelihood 1 (true, false) (fun _ => true) := by
  rw [prod_true_false, prod_induced_true]
  exact one_ne_zero

/-- Injective transformation: identity on `Bool`. -/
private def idTau : Bool → Bool := id

/-- Induced value over `true` under identity is the original likelihood `1`. -/
private theorem id_induced_true :
    boolDirac.inducedLikelihood 1 idTau (fun _ => true) ⟨true, true, rfl⟩ = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro θ
    have hθ : θ.val = true := θ.property
    simp [NormalizedDensityFamily.iidLikelihood_apply,
      boolDirac_dens, hθ]
  · have hw : idTau true = (⟨true, true, rfl⟩ : Set.range idTau).val := rfl
    have hle := le_iSup (fun θ : {θ : Bool // idTau θ =
      (⟨true, true, rfl⟩ : Set.range idTau).val} =>
      boolDirac.iidLikelihood 1 θ.val (fun _ => true)) ⟨true, hw⟩
    have h1 : boolDirac.iidLikelihood 1 true (fun _ => true) = 1 := by
      simp [NormalizedDensityFamily.iidLikelihood_apply, boolDirac_dens]
    rw [h1] at hle
    exact hle

example :
    boolDirac.inducedLikelihood 1 idTau (fun _ => true) ⟨true, true, rfl⟩ = 1 :=
  id_induced_true

/-- Constant transformation to `Unit`. -/
private def constTau : Bool → Unit := fun _ => ()

/-- Induced value over `()` is the whole-range supremum `1`. -/
private theorem const_induced :
    boolDirac.inducedLikelihood 1 constTau (fun _ => true) ⟨(), true, rfl⟩ = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro θ
    simp only [NormalizedDensityFamily.iidLikelihood_apply, Fin.prod_univ_one,
      boolDirac_dens]
    by_cases h : (true : Bool) = θ.val
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact zero_le
  · have hw : constTau true = (⟨(), true, rfl⟩ : Set.range constTau).val := rfl
    have hle := le_iSup (fun θ : {θ : Bool // constTau θ =
      (⟨(), true, rfl⟩ : Set.range constTau).val} =>
      boolDirac.iidLikelihood 1 θ.val (fun _ => true)) ⟨true, hw⟩
    have h1 : boolDirac.iidLikelihood 1 true (fun _ => true) = 1 := by
      simp [NormalizedDensityFamily.iidLikelihood_apply, boolDirac_dens]
    rw [h1] at hle
    exact hle

example :
    boolDirac.inducedLikelihood 1 constTau (fun _ => true) ⟨(), true, rfl⟩ = 1 :=
  const_induced

/-- Vector-valued transformation: pair with `true`. -/
private def vecTau : Bool → Bool × Bool := fun b => (b, true)

/-- Induced value over `(true,true)` is `1`. -/
private theorem vec_induced :
    boolDirac.inducedLikelihood 1 vecTau (fun _ => true)
      ⟨(true, true), true, rfl⟩ = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro θ
    have hθ : θ.val = true := congrArg Prod.fst θ.property
    simp [NormalizedDensityFamily.iidLikelihood_apply,
      boolDirac_dens, hθ]
  · have hw : vecTau true =
        (⟨(true, true), true, rfl⟩ : Set.range vecTau).val := rfl
    have hle := le_iSup (fun θ : {θ : Bool // vecTau θ =
      (⟨(true, true), true, rfl⟩ : Set.range vecTau).val} =>
      boolDirac.iidLikelihood 1 θ.val (fun _ => true)) ⟨true, hw⟩
    have h1 : boolDirac.iidLikelihood 1 true (fun _ => true) = 1 := by
      simp [NormalizedDensityFamily.iidLikelihood_apply, boolDirac_dens]
    rw [h1] at hle
    exact hle

example :
    boolDirac.inducedLikelihood 1 vecTau (fun _ => true)
      ⟨(true, true), true, rfl⟩ = 1 :=
  vec_induced

/-- Off-image value `false` is not in the range of the constant-`true` map. -/
example : (false : Bool) ∉ Set.range (fun _ : Bool => true) := by
  rintro ⟨b, hb⟩
  have h0 : (true : Bool) = false := hb
  exact absurd h0 (by simp)

/-- Inhabited fibers are derived from the image subtype. -/
example (τ : Bool → Bool) (η : Set.range τ) : ∃ θ, τ θ = η.val := η.2

/-- Continuous spike density: uniform `[0,1]` plus `n` on null `{2}`. -/
private noncomputable def spikeContDens (n : ℕ) (x : ℝ) : ℝ≥0∞ :=
  Set.indicator {(2 : ℝ)} (fun _ => (n : ℝ≥0∞)) x +
  Set.indicator (Set.Icc 0 1) 1 x

/-- Genuine continuous-density family with volume dominating measure. -/
private noncomputable def spikeContFamily : NormalizedDensityFamily ℝ ℕ volume where
  dens := spikeContDens
  measurable := fun n =>
    ((measurable_const.indicator (measurableSet_singleton (2 : ℝ))).add
      (measurable_one.indicator measurableSet_Icc)).aemeasurable
  normalized := by
    intro n
    have hbase : (∫⁻ x, Set.indicator (Set.Icc (0 : ℝ) 1) 1 x ∂volume) = 1 := by
      rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
      simp
    have hae : spikeContDens n =ᵐ[volume] Set.indicator (Set.Icc (0 : ℝ) 1) 1 := by
      have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (2 : ℝ) := by
        simp [ae_iff, measure_singleton]
      filter_upwards [h2] with x hx
      simp only [spikeContDens]
      have hnot : x ∉ ({(2 : ℝ)} : Set ℝ) := by simp [Set.mem_singleton_iff, hx]
      rw [Set.indicator_of_notMem hnot _]
      simp
    rw [lintegral_congr_ae hae, hbase]

/-- Likelihood at the spike point `2` is `n`. -/
private theorem spikeCont_likelihood (n : ℕ) :
    spikeContFamily.iidLikelihood 1 n (fun _ => (2 : ℝ)) = (n : ℝ≥0∞) := by
  simp only [NormalizedDensityFamily.iidLikelihood_apply, Fin.prod_univ_one]
  show spikeContDens n 2 = (n : ℝ≥0∞)
  simp only [spikeContDens]
  have hmem : ((2 : ℝ) ∈ ({(2 : ℝ)} : Set ℝ)) := by simp
  have hnot : (2 : ℝ) ∉ Set.Icc (0 : ℝ) 1 := by
    intro h
    rw [Set.mem_Icc] at h
    linarith
  rw [Set.indicator_of_mem hmem _, Set.indicator_of_notMem hnot _]
  simp

/-- Continuous unbounded fiber supremum is `∞`; no maximizer is invented. -/
example :
    spikeContFamily.inducedLikelihood 1 (fun _ : ℕ => ()) (fun _ => (2 : ℝ))
      ⟨(), 0, rfl⟩ = ∞ := by
  have hge : ∀ k : ℕ, (k : ℝ≥0∞) ≤
      spikeContFamily.inducedLikelihood 1 (fun _ : ℕ => ()) (fun _ => (2 : ℝ))
        ⟨(), 0, rfl⟩ := by
    intro k
    have hw : (fun _ : ℕ => ()) k =
        (⟨(), 0, rfl⟩ : Set.range (fun _ : ℕ => ())).val := rfl
    have hle := le_iSup (fun θ : {θ : ℕ // (fun _ : ℕ => ()) θ =
        (⟨(), 0, rfl⟩ : Set.range (fun _ : ℕ => ())).val} =>
      spikeContFamily.iidLikelihood 1 θ.val (fun _ => (2 : ℝ))) ⟨k, hw⟩
    rw [spikeCont_likelihood] at hle
    exact hle
  have hsup : (⨆ k : ℕ, (k : ℝ≥0∞)) ≤
      spikeContFamily.inducedLikelihood 1 (fun _ : ℕ => ()) (fun _ => (2 : ℝ))
        ⟨(), 0, rfl⟩ := iSup_le hge
  rw [ENNReal.iSup_natCast] at hsup
  exact le_antisymm le_top hsup
