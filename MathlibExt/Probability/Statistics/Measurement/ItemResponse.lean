/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Discrete
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Basic.ENNReal.Real
import Mathlib.Data.Fintype.BigOperators

/-!
# Item response theory: Rasch sufficiency, 2PL affine maps, graded response

This module combines three item-response contracts.

D03.3 Finite Rasch model with local independence. Total score is sufficient
for person ability given fixed item difficulties (Mair and Hatzinger 2007,
Section 3.1), proved by the factorization theorem.

D06.2 Two-parameter logistic (2PL) affine invariance. The law is unchanged
under ability rescaling `θ ↦ A * θ + B` with matching slope and difficulty
maps (Weeks 2010, (7), (8a), (8b)). The algebra needs only `A ≠ 0`. A
positive-scale version keeps discriminations positive. One anchor item pins
`A = 1` and `B = 0`.

D06.3 Graded-response model. Cumulative probabilities follow Weeks 2010,
(2); category probabilities follow Weeks 2010, (3). Categories are shifted
down by one relative to Weeks. Sums telescope to one. Nonnegativity needs
`0 ≤ a` with ordered thresholds; positivity needs strict versions.

Logistic metric: every model here uses the scaling constant `D = 1`.
Weeks (2010) writes the logistic argument as `D * a * (θ - b)`, in (1) for
the dichotomous models and in (2) for the graded model; the common choice
`D = 1.7` approximates the normal ogive and gives different probabilities
for the same parameters. The `D`-scaled model with discriminations `a` is the
model here with discriminations `D * a`.

We do not claim identification of the 2PL parameters from the law.
Identification is addressed only within affine maps.

References:

* Mair and Hatzinger (2007), extended Rasch modeling.
* J. P. Weeks, *plink: An R package for linking mixed-format tests using
  IRT-based methods*, Journal of Statistical Software 35(12) (2010),
  DOI 10.18637/jss.v035.i12, Section 2, Equations (1), (2), (3), (7), (8a),
  (8b).
* Rizopoulos, JSS v017 i05, DOI 10.18637/jss.v017.i05.
-/

namespace MathlibExt.Probability.Statistics.Measurement

@[expose]
public section

/-- Locally independent binary responses with success probabilities `q`. -/
noncomputable def localIndepPMF {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    PMF (ι → Bool) :=
  PMF.ofFintype (fun x => ∏ i, (if x i then ENNReal.ofReal (q i)
    else ENNReal.ofReal (1 - q i))) (by
    have hfac : (∑ x : ι → Bool, ∏ i, (if x i
      then ENNReal.ofReal (q i) else ENNReal.ofReal (1 - q i)))
      = ∏ i, ∑ b : Bool, (if b then ENNReal.ofReal (q i)
        else ENNReal.ofReal (1 - q i)) := by
      have h := Finset.sum_prod_piFinset (ι := ι) (κ := Bool)
        (s := Finset.univ)
        (fun i b => if b then ENNReal.ofReal (q i)
          else ENNReal.ofReal (1 - q i))
      rw [Fintype.piFinset_univ] at h
      exact h
    rw [hfac]
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    have h1 : 0 ≤ q i := hq0 i
    have h2 : 0 ≤ 1 - q i := sub_nonneg.mpr (hq1 i)
    have heq : q i + (1 - q i) = 1 := by ring
    rw [← ENNReal.ofReal_add h1 h2, heq, ENNReal.ofReal_one])

/-- Mass of a response pattern under locally independent binary responses. -/
theorem localIndepPMF_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (x : ι → Bool) :
    localIndepPMF q hq0 hq1 x
      = ∏ i, (if x i then ENNReal.ofReal (q i)
        else ENNReal.ofReal (1 - q i)) := by
  exact rfl

/-- Raw score: the number of correct responses. -/
def totalScore {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

/-- Rasch model with fixed item difficulties `b`, indexed by ability `θ`. -/
noncomputable def raschPMF {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (θ : ℝ) : PMF (ι → Bool) :=
  localIndepPMF (fun i => Real.sigmoid (θ - b i))
    (fun i => le_of_lt (Real.sigmoid_pos (θ - b i)))
    (fun i => le_of_lt (Real.sigmoid_lt_one (θ - b i)))

/-- Mass of a response pattern under the Rasch model. -/
theorem raschPMF_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (θ : ℝ) (x : ι → Bool) :
    raschPMF b θ x = ∏ i, (if x i
      then ENNReal.ofReal (Real.sigmoid (θ - b i))
      else ENNReal.ofReal (1 - Real.sigmoid (θ - b i))) := by
  exact rfl

/-- Two-parameter logistic model with discriminations `a` and difficulties `b`,
in the logistic metric `D = 1` (Weeks 2010, (1), with no lower asymptote and
`D = 1`). -/
noncomputable def twoPLPMF {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) : PMF (ι → Bool) :=
  localIndepPMF (fun i => Real.sigmoid (a i * (θ - b i)))
    (fun i => le_of_lt (Real.sigmoid_pos (a i * (θ - b i))))
    (fun i => le_of_lt (Real.sigmoid_lt_one (a i * (θ - b i))))

/-- Mass of a response pattern under the two-parameter logistic model. -/
theorem twoPLPMF_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) (x : ι → Bool) :
    twoPLPMF a b θ x = ∏ i, (if x i
      then ENNReal.ofReal (Real.sigmoid (a i * (θ - b i)))
      else ENNReal.ofReal (1 - Real.sigmoid (a i * (θ - b i)))) := by
  exact rfl

/-- The Rasch model is the two-parameter model with all discriminations one. -/
theorem raschPMF_eq_twoPLPMF_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (θ : ℝ) :
    raschPMF b θ = twoPLPMF (fun _ => 1) b θ := by
  apply PMF.ext
  intro x
  rw [raschPMF_apply, twoPLPMF_apply]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hx : x i = true
  · simp [hx, one_mul]
  · simp [hx]

private theorem raschPMF_factor_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (x : ι → Bool) (θ : ℝ) :
    raschPMF b θ x
      = (ENNReal.ofReal (Real.exp (θ * (totalScore x : ℝ)))
        * ∏ i, ENNReal.ofReal ((1 + Real.exp (θ - b i))⁻¹))
        * ENNReal.ofReal (Real.exp
          (-∑ i ∈ Finset.univ.filter (fun i => x i = true), b i)) := by
  classical
  rw [raschPMF_apply]
  have hsig : ∀ i : ι, Real.sigmoid (θ - b i)
      = Real.exp (θ - b i) / (1 + Real.exp (θ - b i)) := by
    intro i
    rw [Real.sigmoid_def, Real.exp_neg]
    have hne : (1 + Real.exp (θ - b i)) ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring
  have h1sig : ∀ i : ι, 1 - Real.sigmoid (θ - b i)
      = 1 / (1 + Real.exp (θ - b i)) := by
    intro i
    rw [hsig i]
    have hpos : (0 : ℝ) < 1 + Real.exp (θ - b i) := by
      positivity
    field_simp
    ring
  have hmass : ∀ i : ι, (if x i then ENNReal.ofReal
      (Real.sigmoid (θ - b i))
      else ENNReal.ofReal (1 - Real.sigmoid (θ - b i)))
      = ENNReal.ofReal ((1 + Real.exp (θ - b i))⁻¹)
        * (if x i then ENNReal.ofReal (Real.exp (θ - b i))
          else 1) := by
    intro i
    by_cases hx : x i = true
    · rw [ite_eq_left hx, ite_eq_left hx, hsig i]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_eq_inv_mul, mul_comm]
    · rw [ite_eq_right hx, ite_eq_right hx, h1sig i, mul_one, one_div]
  rw [Finset.prod_congr rfl (fun i _ => hmass i)]
  rw [Finset.prod_mul_distrib]
  have hscore : totalScore x = (Finset.univ.filter
      (fun i => x i = true)).card := by
    exact rfl
  have hcard : (∑ i ∈ Finset.univ.filter (fun i => x i = true), θ)
      = θ * (totalScore x : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm, hscore]
  have hbase : (∏ i, (if x i then Real.exp (θ - b i) else 1))
      = ∏ i ∈ Finset.univ.filter (fun i => x i = true),
        Real.exp (θ - b i) := by
    have h1 : (∏ i ∈ Finset.univ.filter (fun i => x i = true),
        (if x i then Real.exp (θ - b i) else 1))
        = ∏ i ∈ (Finset.univ : Finset ι),
          (if x i then Real.exp (θ - b i) else 1) := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro i _ hi
      simp_all
    have h2 : (∏ i ∈ Finset.univ.filter (fun i => x i = true),
        (if x i then Real.exp (θ - b i) else 1))
        = ∏ i ∈ Finset.univ.filter (fun i => x i = true),
          Real.exp (θ - b i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp_all
    rw [← h1, h2]
  have hsum : (∑ i ∈ Finset.univ.filter (fun i => x i = true), (θ - b i))
      = θ * (totalScore x : ℝ)
        - ∑ i ∈ Finset.univ.filter (fun i => x i = true), b i := by
    rw [Finset.sum_sub_distrib, hcard]
  have hprod_real : (∏ i, (if x i then Real.exp (θ - b i) else 1))
      = Real.exp (θ * (totalScore x : ℝ)
        - ∑ i ∈ Finset.univ.filter (fun i => x i = true), b i) := by
    rw [hbase, ← Real.exp_sum, hsum]
  have hB : (∏ i, if x i then ENNReal.ofReal (Real.exp (θ - b i)) else 1)
      = ENNReal.ofReal (Real.exp (θ * (totalScore x : ℝ)))
        * ENNReal.ofReal (Real.exp
          (-∑ i ∈ Finset.univ.filter (fun i => x i = true), b i)) := by
    have hnn : ∀ i ∈ (Finset.univ : Finset ι),
        0 ≤ (if x i then Real.exp (θ - b i) else 1) := by
      intro i _
      by_cases hx : x i = true
      · simp [hx, Real.exp_nonneg _]
      · simp [hx]
    have hof : (∏ i, if x i then ENNReal.ofReal (Real.exp (θ - b i))
        else 1)
        = ENNReal.ofReal
          (∏ i, (if x i then Real.exp (θ - b i) else 1)) := by
      rw [ENNReal.ofReal_prod_of_nonneg hnn]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hx : x i = true
      · simp [hx]
      · simp [hx, ENNReal.ofReal_one]
    rw [hof, hprod_real, sub_eq_add_neg, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [hB]
  ring

/-- The Rasch likelihood factors through the raw score: the first factor sees
the data only through `totalScore x`, and the second is free of `θ`. -/
theorem raschPMF_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) :
    ∃ (g : ℕ → ℝ → ENNReal) (h : (ι → Bool) → ENNReal),
      ∀ (x : ι → Bool) (θ : ℝ),
        raschPMF b θ x = g (totalScore x) θ * h x :=
  ⟨fun s θ => ENNReal.ofReal (Real.exp (θ * s))
    * ∏ i, ENNReal.ofReal ((1 + Real.exp (θ - b i))⁻¹),
    fun x => ENNReal.ofReal (Real.exp
      (-∑ i ∈ Finset.univ.filter (fun i => x i = true), b i)),
    fun x θ => raschPMF_factor_eq b x θ⟩

/-- The raw score is sufficient for ability in the Rasch model with fixed
difficulties (Mair and Hatzinger 2007, Section 3.1), proved by the
factorization theorem. -/
theorem totalScore_sufficient_rasch {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : ι → ℝ) :
    MathlibExt.Probability.Statistics.Sufficiency.IsSufficientPMF
      (fun θ : ℝ => raschPMF b θ) totalScore := by
  classical
  refine MathlibExt.Probability.Statistics.Sufficiency.isSufficientPMF_of_factorization
    (fun θ s => (ENNReal.ofReal (Real.exp (θ * s))
      * ∏ i, ENNReal.ofReal ((1 + Real.exp (θ - b i))⁻¹)).toNNReal)
    (fun x => (ENNReal.ofReal (Real.exp
      (-∑ i ∈ Finset.univ.filter (fun i => x i = true), b i))).toNNReal)
    (fun θ x => ?_)
  have hg : ∀ (s : ℕ) (θ : ℝ),
      (ENNReal.ofReal (Real.exp (θ * s))
        * ∏ i, ENNReal.ofReal ((1 + Real.exp (θ - b i))⁻¹)) ≠ ⊤ := by
    intro s θ
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    have hnn : ∀ i ∈ (Finset.univ : Finset ι),
        0 ≤ ((1 + Real.exp (θ - b i))⁻¹) := fun i _ => by positivity
    rw [← ENNReal.ofReal_prod_of_nonneg hnn]
    exact ENNReal.ofReal_ne_top
  have hh : ∀ x : ι → Bool, ENNReal.ofReal (Real.exp
      (-∑ i ∈ Finset.univ.filter (fun i => x i = true), b i)) ≠ ⊤ :=
    fun _ => ENNReal.ofReal_ne_top
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (hg _ _),
    ENNReal.coe_toNNReal (hh _)]
  exact raschPMF_factor_eq b x θ

/-- Invariance of the locally independent 2PL law under the change of ability
scale `θ ↦ A * θ + B` with the corresponding slope and difficulty
transformation (Weeks 2010, (7), (8a), (8b)); the algebra needs only `A ≠ 0`.
-/
theorem twoPLPMF_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ A B : ℝ) (hA : A ≠ 0) :
    twoPLPMF a b θ = twoPLPMF (fun i => a i / A)
      (fun i => A * b i + B) (A * θ + B) := by
  apply PMF.ext
  intro x
  rw [twoPLPMF_apply, twoPLPMF_apply]
  apply Finset.prod_congr rfl
  intro i _
  have harg : a i * (θ - b i) = (a i / A)
      * ((A * θ + B) - (A * b i + B)) := by
    field_simp
    ring
  rw [harg]

/-- Under a positive affine change of the ability scale with positive
discriminations, the transformed discriminations stay positive and the 2PL law
is unchanged. -/
theorem twoPLPMF_affine_of_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ A B : ℝ) (hA : 0 < A)
    (ha : ∀ i, 0 < a i) :
    (∀ i, 0 < a i / A) ∧ twoPLPMF a b θ
      = twoPLPMF (fun i => a i / A) (fun i => A * b i + B)
        (A * θ + B) := by
  refine ⟨fun i => div_pos (ha i) hA, ?_⟩
  exact twoPLPMF_affine a b θ A B (ne_of_gt hA)

/-- Fixing the discrimination and difficulty of one anchor item removes the
affine indeterminacy (the other common choice, standardizing the ability
distribution, is not formalized here). -/
theorem affine_eq_of_anchor {ι : Type*} (a b : ι → ℝ) (k : ι)
    (A B : ℝ) (hA : A ≠ 0) (ha : a k ≠ 0)
    (hda : a k / A = a k) (hdb : A * b k + B = b k) :
    A = 1 ∧ B = 0 := by
  have hmul : a k = a k * A := (div_eq_iff hA).mp hda
  have hA1 : A = 1 := by
    have h2 : a k * 1 = a k * A := by
      rw [mul_one]
      exact hmul
    exact (mul_left_cancel₀ ha h2).symm
  refine ⟨hA1, ?_⟩
  rw [hA1, one_mul] at hdb
  exact (add_eq_left).mp hdb

/-- Graded-response cumulative probability (Weeks 2010, (2)) in the logistic
metric `D = 1`: the argument is `a * (θ - b)` where Weeks has
`D * a * (θ - b)`. -/
noncomputable def gradedCumulative (a : ℝ) {m : ℕ} (b : Fin m → ℝ)
    (θ : ℝ) (j : ℕ) : ℝ :=
  if _ : j = 0 then 1
  else if _ : m < j then 0
  else Real.sigmoid (a * (θ - b ⟨j - 1, by omega⟩))

/-- Cumulative probability at zero is one (Weeks 2010, (2)). -/
theorem gradedCumulative_zero (a : ℝ) {m : ℕ} (b : Fin m → ℝ)
    (θ : ℝ) : gradedCumulative a b θ 0 = 1 := by
  simp [gradedCumulative]

/-- Cumulative probability vanishes beyond the last threshold (Weeks 2010,
(2)). -/
theorem gradedCumulative_beyond (a : ℝ) {m : ℕ} (b : Fin m → ℝ)
    (θ : ℝ) (j : ℕ) (hj : m < j) :
    gradedCumulative a b θ j = 0 := by
  unfold gradedCumulative
  by_cases hj0 : j = 0
  · omega
  · simp [hj0, hj]

/-- Cumulative probability at a threshold index (Weeks 2010, (2)). -/
theorem gradedCumulative_succ (a : ℝ) {m : ℕ} (b : Fin m → ℝ)
    (θ : ℝ) (j : ℕ) (hj : j < m) :
    gradedCumulative a b θ (j + 1)
      = Real.sigmoid (a * (θ - b ⟨j, hj⟩)) := by
  have hjm : ¬ m < j + 1 := by omega
  unfold gradedCumulative
  simp [hjm]

/-- Graded-response category probability (Weeks 2010, (3)). -/
noncomputable def gradedProb (a : ℝ) {m : ℕ} (b : Fin m → ℝ)
    (θ : ℝ) (j : ℕ) : ℝ :=
  gradedCumulative a b θ j - gradedCumulative a b θ (j + 1)

/-- Category probabilities telescope to one (Weeks 2010, (3)). -/
theorem gradedProb_sum (a : ℝ) {m : ℕ} (b : Fin m → ℝ) (θ : ℝ) :
    ∑ j : Fin (m + 1), gradedProb a b θ j.val = 1 := by
  have hrange : ∑ j ∈ Finset.range (m + 1), gradedProb a b θ j = 1 := by
    have htel : ∑ j ∈ Finset.range (m + 1), gradedProb a b θ j
        = gradedCumulative a b θ 0
          - gradedCumulative a b θ (m + 1) := by
      have h := Finset.sum_range_sub'
        (fun j => gradedCumulative a b θ j) (m + 1)
      simpa [gradedProb] using h
    rw [htel, gradedCumulative_zero]
    have hbey : gradedCumulative a b θ (m + 1) = 0 := by
      exact gradedCumulative_beyond a b θ (m + 1) (by omega)
    rw [hbey, sub_zero]
  have hfin : ∑ j : Fin (m + 1), gradedProb a b θ j.val
      = ∑ j ∈ Finset.range (m + 1), gradedProb a b θ j := by
    exact Fin.sum_univ_eq_sum_range _ _
  rw [hfin, hrange]

private theorem gradedCumulative_step_le (a : ℝ) {m : ℕ} (b : Fin m → ℝ)
    (θ : ℝ) (ha : 0 ≤ a) (hb : Monotone b) (j : ℕ) (hj1 : 1 ≤ j)
    (hj2 : j + 1 ≤ m) :
    gradedCumulative a b θ (j + 1) ≤ gradedCumulative a b θ j := by
  have hjm : j < m := by omega
  have hj0 : j ≠ 0 := by omega
  rw [gradedCumulative_succ a b θ j hjm]
  have hprev : gradedCumulative a b θ j
      = Real.sigmoid (a * (θ - b ⟨j - 1, by omega⟩)) := by
    unfold gradedCumulative
    have hjmj : ¬ m < j := by omega
    simp [hj0, hjmj]
  rw [hprev]
  have hble : b ⟨j - 1, by omega⟩ ≤ b ⟨j, hjm⟩ := by
    apply hb
    rw [Fin.mk_le_mk]
    omega
  have harg : a * (θ - b ⟨j, hjm⟩) ≤ a * (θ - b ⟨j - 1, by omega⟩) := by
    apply mul_le_mul_of_nonneg_left _ ha
    linarith
  exact Real.sigmoid_monotone harg

private theorem gradedCumulative_step_lt (a : ℝ) {m : ℕ} (b : Fin m → ℝ)
    (θ : ℝ) (ha : 0 < a) (hb : StrictMono b) (j : ℕ) (hj1 : 1 ≤ j)
    (hj2 : j + 1 ≤ m) :
    gradedCumulative a b θ (j + 1) < gradedCumulative a b θ j := by
  have hjm : j < m := by omega
  have hj0 : j ≠ 0 := by omega
  rw [gradedCumulative_succ a b θ j hjm]
  have hprev : gradedCumulative a b θ j
      = Real.sigmoid (a * (θ - b ⟨j - 1, by omega⟩)) := by
    unfold gradedCumulative
    have hjmj : ¬ m < j := by omega
    simp [hj0, hjmj]
  rw [hprev]
  have hblt : b ⟨j - 1, by omega⟩ < b ⟨j, hjm⟩ := by
    apply hb
    rw [Fin.mk_lt_mk]
    omega
  have harg : a * (θ - b ⟨j, hjm⟩) < a * (θ - b ⟨j - 1, by omega⟩) := by
    apply mul_lt_mul_of_pos_left _ ha
    linarith
  exact Real.sigmoid_strictMono harg

/-- Category probabilities are nonnegative for ordered thresholds. -/
theorem gradedProb_nonneg (a : ℝ) {m : ℕ} (b : Fin m → ℝ) (θ : ℝ)
    (ha : 0 ≤ a) (hb : Monotone b) (j : Fin (m + 1)) :
    0 ≤ gradedProb a b θ j.val := by
  unfold gradedProb
  by_cases hj0 : j.val = 0
  · have hC0 : gradedCumulative a b θ 0 = 1 := gradedCumulative_zero a b θ
    rw [hj0, hC0]
    simp only [sub_nonneg]
    by_cases h1m : 1 ≤ m
    · have hmem : 0 < m := by omega
      rw [gradedCumulative_succ a b θ 0 hmem]
      exact le_of_lt (Real.sigmoid_lt_one _)
    · have hbey : gradedCumulative a b θ 1 = 0 := by
        apply gradedCumulative_beyond
        omega
      rw [hbey]
      exact zero_le_one
  · have hj1 : 1 ≤ j.val := by omega
    by_cases hjm : j.val < m
    · by_cases hj1m : j.val + 1 ≤ m
      · exact sub_nonneg.mpr (gradedCumulative_step_le a b θ ha hb
          j.val hj1 hj1m)
      · have hjeq : j.val = m := by omega
        rw [hjeq]
        have hbey : gradedCumulative a b θ (m + 1) = 0 := by
          exact gradedCumulative_beyond a b θ (m + 1) (by omega)
        rw [hbey, sub_zero]
        have hmem : 0 < m := by omega
        have hC : gradedCumulative a b θ m
            = Real.sigmoid (a * (θ - b ⟨m - 1, by omega⟩)) := by
          unfold gradedCumulative
          have hj0m : m ≠ 0 := by omega
          simp [hj0m]
        rw [hC]
        exact le_of_lt (Real.sigmoid_pos _)
    · have hjeq : j.val = m := by omega
      rw [hjeq]
      have hbey : gradedCumulative a b θ (m + 1) = 0 := by
        exact gradedCumulative_beyond a b θ (m + 1) (by omega)
      rw [hbey, sub_zero]
      by_cases hm0 : m = 0
      · subst hm0
        rw [gradedCumulative_zero]
        exact zero_le_one
      · have hC : gradedCumulative a b θ m
            = Real.sigmoid (a * (θ - b ⟨m - 1, by omega⟩)) := by
          unfold gradedCumulative
          have hj0m : m ≠ 0 := by omega
          simp [hj0m]
        rw [hC]
        exact le_of_lt (Real.sigmoid_pos _)

/-- Category probabilities are positive for strictly ordered thresholds. -/
theorem gradedProb_pos (a : ℝ) {m : ℕ} (b : Fin m → ℝ) (θ : ℝ)
    (ha : 0 < a) (hb : StrictMono b) (j : Fin (m + 1)) :
    0 < gradedProb a b θ j.val := by
  unfold gradedProb
  by_cases hj0 : j.val = 0
  · have hC0 : gradedCumulative a b θ 0 = 1 := gradedCumulative_zero a b θ
    rw [hj0, hC0]
    simp only [sub_pos]
    by_cases h1m : 1 ≤ m
    · have hmem : 0 < m := by omega
      rw [gradedCumulative_succ a b θ 0 hmem]
      exact Real.sigmoid_lt_one _
    · have hbey : gradedCumulative a b θ 1 = 0 := by
        apply gradedCumulative_beyond
        omega
      rw [hbey]
      exact zero_lt_one
  · have hj1 : 1 ≤ j.val := by omega
    by_cases hjm : j.val < m
    · by_cases hj1m : j.val + 1 ≤ m
      · exact sub_pos.mpr (gradedCumulative_step_lt a b θ ha hb
          j.val hj1 hj1m)
      · have hjeq : j.val = m := by omega
        rw [hjeq]
        have hbey : gradedCumulative a b θ (m + 1) = 0 := by
          exact gradedCumulative_beyond a b θ (m + 1) (by omega)
        rw [hbey, sub_zero]
        have hmem : 0 < m := by omega
        have hC : gradedCumulative a b θ m
            = Real.sigmoid (a * (θ - b ⟨m - 1, by omega⟩)) := by
          unfold gradedCumulative
          have hj0m : m ≠ 0 := by omega
          simp [hj0m]
        rw [hC]
        exact Real.sigmoid_pos _
    · have hjeq : j.val = m := by omega
      rw [hjeq]
      have hbey : gradedCumulative a b θ (m + 1) = 0 := by
        exact gradedCumulative_beyond a b θ (m + 1) (by omega)
      rw [hbey, sub_zero]
      by_cases hm0 : m = 0
      · subst hm0
        rw [gradedCumulative_zero]
        exact zero_lt_one
      · have hC : gradedCumulative a b θ m
            = Real.sigmoid (a * (θ - b ⟨m - 1, by omega⟩)) := by
          unfold gradedCumulative
          have hj0m : m ≠ 0 := by omega
          simp [hj0m]
        rw [hC]
        exact Real.sigmoid_pos _

/-- Graded-response law for ordered thresholds (Weeks 2010, (3)). -/
noncomputable def gradedResponsePMF (a : ℝ) {m : ℕ} (b : Fin m → ℝ)
    (θ : ℝ) (ha : 0 ≤ a) (hb : Monotone b) : PMF (Fin (m + 1)) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (gradedProb a b θ j.val)) (by
    have hnn : ∀ j : Fin (m + 1), 0 ≤ gradedProb a b θ j.val := by
      intro j
      exact gradedProb_nonneg a b θ ha hb j
    have hsum : ∑ j : Fin (m + 1), gradedProb a b θ j.val = 1 := by
      exact gradedProb_sum a b θ
    have hof : ∑ j : Fin (m + 1), ENNReal.ofReal (gradedProb a b θ j.val)
        = ENNReal.ofReal (∑ j : Fin (m + 1), gradedProb a b θ j.val) := by
      exact (ENNReal.ofReal_sum_of_nonneg (fun j _ => hnn j)).symm
    rw [hof, hsum, ENNReal.ofReal_one])

/-- Mass of a category under the graded-response law (Weeks 2010, (3)). -/
theorem gradedResponsePMF_apply (a : ℝ) {m : ℕ} (b : Fin m → ℝ)
    (θ : ℝ) (ha : 0 ≤ a) (hb : Monotone b) (j : Fin (m + 1)) :
    gradedResponsePMF a b θ ha hb j
      = ENNReal.ofReal (gradedProb a b θ j.val) := by
  exact rfl

end

end MathlibExt.Probability.Statistics.Measurement
