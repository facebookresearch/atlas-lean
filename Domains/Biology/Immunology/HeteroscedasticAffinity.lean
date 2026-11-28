/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Heteroscedastic Gaussian likelihood for measured binding affinity

DeepLigand (Zeng and Gifford, 2019) treats the measured binding affinity `a(x)` of an input pair
`x`, a peptide and an MHC allele, as its true affinity plus zero-mean Gaussian noise whose scale
may depend on `x`. A model with parameters `θ` predicts both the mean `μ_θ(x)` and the variance
`σ²_θ(x) > 0`, and `a(x) | x ~ 𝒩(μ_θ(x), σ²_θ(x))`. The negative log-likelihood of a measured
affinity `a` is, up to the constant `log (2π) / 2`,

  `((a - μ_θ(x)) ^ 2 / σ²_θ(x) + log σ²_θ(x)) / 2`,

so that maximising the likelihood of a training set `(xᵢ, aᵢ)` means minimising the sum `L_aff(θ)`
of these terms: each example is weighted by its predicted precision `1 / σ²_θ(xᵢ)`, and the
`log σ²` term penalises inflating the variance to escape a hard example. An example that carries
only an inequality, `aᵢ ≤ c` or `aᵢ ≥ c`, contributes only when the predicted mean violates it.
When the same model also predicts a probability `p_θ(xᵢ)` that the peptide is a naturally
presented ligand, it is trained against

  `L(θ) = L_aff(θ) + ∑ᵢ CE(yᵢ, p_θ(xᵢ))`,

each sum taken over the examples whose corresponding label is observed.

## Conventions

* The training set is indexed by a finite type `ι`; example `i` has the input `x i`, the affinity
  label `a i : Option AffinityLabel` and the presentation label `y i : Option Bool`, where `none`
  is an unobserved label, which contributes nothing to its sum.
* An affinity label is a measurement `exact a`, or only a bound: `atMost c` (`a ≤ c`) or
  `atLeast c` (`a ≥ c`). A bound is inclusive: the predicted mean `m` violates `atMost c` exactly
  when `c < m`, and `atLeast c` exactly when `m < c`. A violated bound contributes the Gaussian term
  of a measurement at the bound `c`, as the source scores the value recorded with the inequality,
  and a satisfied bound contributes `0`: within the bound the label says nothing about the mean.
* The variance is a nonnegative real `ℝ≥0`, as for Mathlib's `gaussianPDFReal`. The model of the
  source predicts a positive variance; the definitions accept any, and the results that need a
  positive variance assume it (`var θ (x i) ≠ 0`). The definitions take Lean's conventions
  `r / 0 = 0` and `log 0 = 0` at a zero variance, where no Gaussian density exists.
* The cross-entropy of a presentation label `b` against a predicted probability `p` is `-log p`
  for `b = true` and `-log (1 - p)` for `b = false`, that is `-(y log p + (1 - y) log (1 - p))`
  with `y ∈ {0, 1}`. The definition asks nothing of `p`; it is the negative log-likelihood of `b`
  under the Bernoulli law of parameter `p` when `0 < p < 1`.
* The losses leave out the constant `log (2π) / 2` of each measured example, which does not
  depend on `θ` (`affinityLoss_exact_eq_neg_log_prod_gaussianPDFReal`).

## Main definitions

* `AffinityLabel`: a measured binding affinity, or an upper or lower bound on it.
* `affinityTerm m v l`: the contribution of the affinity label `l` of one example whose predicted
  mean and variance are `m` and `v`.
* `affinityLoss mean var x a θ`: the heteroscedastic affinity loss `L_aff(θ)`.
* `jointLoss mean var prob x a y θ`: the joint loss `L(θ)` of affinity and presentation labels.

## Main results

* `affinityTerm_exact_eq_neg_log_gaussianPDFReal`: the term of a measurement is its Gaussian
  negative log-likelihood less `log (2π) / 2`.
* `affinityLoss_exact_eq_neg_log_prod_gaussianPDFReal` and
  `isMaxOn_prod_gaussianPDFReal_iff_isMinOn_affinityLoss`: on measured affinities, `L_aff` is the
  negative log-likelihood up to a constant, so the parameters that maximise the likelihood over a
  set are those that minimise `L_aff`.
* `affinityTerm_atMost_of_le`, `affinityTerm_atMost_of_lt`, `affinityTerm_atLeast_of_le` and
  `affinityTerm_atLeast_of_lt`: a bound contributes only when the mean violates it, and then as a
  measurement at the bound.
* `affinityLoss_const_var` and `isMinOn_affinityLoss_const_var_iff`: with a constant variance the
  loss is a rescaled sum of squared residuals plus a constant, so it has the minimisers of
  ordinary least squares.
* `hasDerivAt_affinityTerm_exact_var`, `deriv_affinityTerm_exact_var_eq_zero_iff` and
  `isMinOn_affinityTerm_exact_var`: for a fixed mean `m ≠ a`, the term of a measurement `a` is
  stationary in the variance exactly at `(a - m) ^ 2`, where it attains its minimum over the
  positive variances.
* `jointLoss_of_forall_eq_none`: without presentation labels the joint loss is `L_aff`.

## References

* H. Zeng, D. K. Gifford, "DeepLigand: accurate prediction of MHC class I ligands using peptide
  embedding", *Bioinformatics* 35 (2019), i278–i283, <https://doi.org/10.1093/bioinformatics/btz330>:
  Section 2.1, "Datasets", for the labels (measurements, inequalities and unknown labels), and
  Section 2.2, "Model structure", for the Gaussian model of the measured affinity, the joint loss
  and the treatment of inequalities.
* T. J. O'Donnell, A. Rubinsteyn, M. Bonsack, A. B. Riemer, U. Laserson, J. Hammerbacher,
  "MHCflurry: open-source class I MHC binding affinity prediction", *Cell Systems* 7 (2018),
  129–132.e4, <https://doi.org/10.1016/j.cels.2018.05.014>, for affinity labels carrying an
  inequality, whose loss counts only when the prediction violates it.
-/

@[expose] public section

namespace Domains.Biology.Immunology.HeteroscedasticAffinity

open Real ProbabilityTheory
open scoped NNReal

/-- A recorded **binding-affinity label** of a training example (Zeng and Gifford, 2019,
Section 2.1; O'Donnell et al., 2018): a quantitative measurement `exact a` of the affinity, or,
for a qualitative measurement, only a bound on it, `atMost c` (the affinity is at most `c`) or
`atLeast c` (it is at least `c`). -/
inductive AffinityLabel where
  /-- A measurement: the affinity is `a`. -/
  | exact (a : ℝ)
  /-- An upper bound: the affinity is at most `c`. -/
  | atMost (c : ℝ)
  /-- A lower bound: the affinity is at least `c`. -/
  | atLeast (c : ℝ)

/-- The **contribution of one affinity label** to the heteroscedastic Gaussian loss of an example
whose predicted mean and variance are `m` and `v` (Zeng and Gifford, 2019, Section 2.2):

* a measurement `a` contributes `((a - m) ^ 2 / v + log v) / 2`, its Gaussian negative
  log-likelihood under `𝒩(m, v)` less the constant `log (2π) / 2`
  (`affinityTerm_exact_eq_neg_log_gaussianPDFReal`);
* an upper bound `c` (`a ≤ c`) contributes the term of a measurement at `c` when the mean violates
  it, `c < m`, and `0` otherwise;
* a lower bound `c` (`a ≥ c`) contributes the term of a measurement at `c` when `m < c`, and `0`
  otherwise.

At `v = 0`, where no Gaussian density exists, the term takes Lean's conventions `r / 0 = 0` and
`log 0 = 0`. -/
noncomputable def affinityTerm (m : ℝ) (v : ℝ≥0) : AffinityLabel → ℝ
  | .exact a => ((a - m) ^ 2 / v + log v) / 2
  | .atMost c => if c < m then ((c - m) ^ 2 / v + log v) / 2 else 0
  | .atLeast c => if m < c then ((c - m) ^ 2 / v + log v) / 2 else 0

variable {Θ X ι : Type*} [Fintype ι]

/-- The **heteroscedastic Gaussian affinity loss** `L_aff(θ)` (Zeng and Gifford, 2019,
Section 2.2) of a model that predicts, for an input `x`, the mean `mean θ x` and the variance
`var θ x` of the measured binding affinity, `a(x) | x ~ 𝒩(mean θ x, var θ x)`, on the training set
whose example `i` has the input `x i` and the affinity label `a i`. On measured affinities `aᵢ` it
is

  `L_aff(θ) = ∑ᵢ ((aᵢ - μ_θ(xᵢ)) ^ 2 / σ²_θ(xᵢ) + log σ²_θ(xᵢ)) / 2`

(`affinityLoss_exact`), with `μ_θ = mean θ` and `σ²_θ = var θ`. In general each example
contributes `affinityTerm (mean θ (x i)) (var θ (x i))` of its label: the term above for a
measurement, and, for a label that is only a bound `c`, the term of a measurement at `c` when the
predicted mean violates the bound and `0` when it satisfies it. An example whose label is
unobserved (`a i = none`) contributes `0`.

On measured affinities and positive variances the loss is the negative log-likelihood of the
training set less the constant `log (2π) / 2` per example
(`affinityLoss_exact_eq_neg_log_prod_gaussianPDFReal`), so its minimisers are the
maximum-likelihood parameters (`isMaxOn_prod_gaussianPDFReal_iff_isMinOn_affinityLoss`). -/
noncomputable def affinityLoss (mean : Θ → X → ℝ) (var : Θ → X → ℝ≥0) (x : ι → X)
    (a : ι → Option AffinityLabel) (θ : Θ) : ℝ :=
  ∑ i, (a i).elim 0 (affinityTerm (mean θ (x i)) (var θ (x i)))

/-- The **joint loss of binding-affinity and ligand-presentation labels** (Zeng and Gifford,
2019, Section 2.2)

  `L(θ) = L_aff(θ) + ∑ᵢ CE(yᵢ, p_θ(xᵢ))`

of a model that predicts, for an input `x`, the mean `mean θ x` and the variance `var θ x` of the
measured binding affinity and the probability `prob θ x` that the peptide is a naturally presented
ligand, on the training set whose example `i` has the input `x i`, the affinity label `a i` and the
presentation label `y i`. The first part is the heteroscedastic affinity loss `affinityLoss`, over
the examples whose affinity label is observed, measurements and bounds alike. The second is the
binary cross-entropy over the examples whose presentation label is observed: `-log p` for a
presented ligand (`y i = some true`) and `-log (1 - p)` for a peptide that is not one
(`y i = some false`), with `p = prob θ (x i)`, that is `-(y log p + (1 - y) log (1 - p))` for
`y ∈ {0, 1}`. So measured affinities and mass-spectrometry ligand data train one model. -/
noncomputable def jointLoss (mean : Θ → X → ℝ) (var : Θ → X → ℝ≥0) (prob : Θ → X → ℝ)
    (x : ι → X) (a : ι → Option AffinityLabel) (y : ι → Option Bool) (θ : Θ) : ℝ :=
  affinityLoss mean var x a θ +
    ∑ i, (y i).elim 0 fun b => -log (if b then prob θ (x i) else 1 - prob θ (x i))

/-! ### One example -/

@[simp]
theorem affinityTerm_exact (m : ℝ) (v : ℝ≥0) (a : ℝ) :
    affinityTerm m v (.exact a) = ((a - m) ^ 2 / v + log v) / 2 :=
  rfl

/-- A measured affinity's term is its **Gaussian negative log-likelihood** up to a constant: for a
positive variance `v`, `((a - m) ^ 2 / v + log v) / 2 = -log 𝒩(a; m, v) - log (2π) / 2`, where
`𝒩(a; m, v)` is the density at `a` of the Gaussian law of mean `m` and variance `v`. -/
theorem affinityTerm_exact_eq_neg_log_gaussianPDFReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    affinityTerm m v (.exact a) = -log (gaussianPDFReal m v a) - log (2 * π) / 2 := by
  have hv' : (0 : ℝ) < v := by positivity
  have h2 : 0 < 2 * π * (v : ℝ) := by positivity
  rw [affinityTerm_exact, gaussianPDFReal, log_mul (inv_pos.2 (sqrt_pos.2 h2)).ne' (exp_pos _).ne',
    log_inv, log_exp, log_sqrt h2.le, log_mul (by positivity) hv'.ne']
  ring

/-- An upper bound `c` that the predicted mean satisfies, `m ≤ c`, contributes nothing. -/
theorem affinityTerm_atMost_of_le {m c : ℝ} (v : ℝ≥0) (h : m ≤ c) :
    affinityTerm m v (.atMost c) = 0 := by
  simp [affinityTerm, not_lt.2 h]

/-- An upper bound `c` that the predicted mean violates, `c < m`, contributes as a measurement at
`c`. -/
theorem affinityTerm_atMost_of_lt {m c : ℝ} (v : ℝ≥0) (h : c < m) :
    affinityTerm m v (.atMost c) = affinityTerm m v (.exact c) := by
  simp [affinityTerm, h]

/-- A lower bound `c` that the predicted mean satisfies, `c ≤ m`, contributes nothing. -/
theorem affinityTerm_atLeast_of_le {m c : ℝ} (v : ℝ≥0) (h : c ≤ m) :
    affinityTerm m v (.atLeast c) = 0 := by
  simp [affinityTerm, not_lt.2 h]

/-- A lower bound `c` that the predicted mean violates, `m < c`, contributes as a measurement at
`c`. -/
theorem affinityTerm_atLeast_of_lt {m c : ℝ} (v : ℝ≥0) (h : m < c) :
    affinityTerm m v (.atLeast c) = affinityTerm m v (.exact c) := by
  simp [affinityTerm, h]

/-- The term of a measurement `a`, as a function of a positive variance `s` for a fixed mean `m`,
has the derivative `(1 / s - (a - m) ^ 2 / s ^ 2) / 2`. -/
theorem hasDerivAt_affinityTerm_exact_var (m a : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => affinityTerm m s.toNNReal (.exact a))
      ((1 / s - (a - m) ^ 2 / s ^ 2) / 2) s := by
  have h : HasDerivAt (fun s : ℝ => ((a - m) ^ 2 * s⁻¹ + log s) / 2)
      (((a - m) ^ 2 * -(s ^ 2)⁻¹ + s⁻¹) / 2) s :=
    (((hasDerivAt_inv hs.ne').const_mul _).add (hasDerivAt_log hs.ne')).div_const 2
  refine (h.congr_of_eventuallyEq ?_).congr_deriv (by field_simp; ring)
  filter_upwards [lt_mem_nhds hs] with t ht
  simp [Real.coe_toNNReal _ ht.le, div_eq_mul_inv]

/-- **The stationary point in the variance.** For a fixed mean `m`, the term of a measurement `a`
is stationary at a positive variance `s` exactly when `s = (a - m) ^ 2`. -/
theorem deriv_affinityTerm_exact_var_eq_zero_iff (m a : ℝ) {s : ℝ} (hs : 0 < s) :
    deriv (fun s : ℝ => affinityTerm m s.toNNReal (.exact a)) s = 0 ↔ s = (a - m) ^ 2 := by
  rw [(hasDerivAt_affinityTerm_exact_var m a hs).deriv]
  have hs2 : 0 < s ^ 2 := by positivity
  constructor
  · intro h
    have : (1 / s - (a - m) ^ 2 / s ^ 2) / 2 * (2 * s ^ 2) = s - (a - m) ^ 2 := by
      field_simp
    rw [h, zero_mul] at this
    linarith
  · rintro rfl
    field_simp
    ring

/-- **The variance balances the two terms.** For a fixed mean `m ≠ a`, the term
`((a - m) ^ 2 / v + log v) / 2` of a measurement `a`, whose residual part decreases in the
variance `v` and whose `log v` part increases, attains its minimum over the positive variances at
`v = (a - m) ^ 2`. -/
theorem isMinOn_affinityTerm_exact_var (m : ℝ) {a : ℝ} (ha : a ≠ m) :
    IsMinOn (fun v : ℝ≥0 => affinityTerm m v (.exact a)) {v | v ≠ 0} ((a - m) ^ 2).toNNReal := by
  intro v (hv : v ≠ 0)
  have hr : 0 < (a - m) ^ 2 := by
    have : a - m ≠ 0 := sub_ne_zero.2 ha
    positivity
  have hv' : (0 : ℝ) < v := by positivity
  have ht : 0 < (a - m) ^ 2 / v := div_pos hr hv'
  have hlog := log_le_sub_one_of_pos ht
  rw [log_div hr.ne' hv'.ne'] at hlog
  simp only [Set.mem_ofPred_eq, affinityTerm_exact, Real.coe_toNNReal _ hr.le, div_self hr.ne']
  linarith

/-! ### The affinity loss -/

/-- On measured affinities `b i`, the affinity loss is the sum of the terms
`((b i - μ_θ(x i)) ^ 2 / σ²_θ(x i) + log σ²_θ(x i)) / 2`. -/
theorem affinityLoss_exact (mean : Θ → X → ℝ) (var : Θ → X → ℝ≥0) (x : ι → X) (b : ι → ℝ)
    (θ : Θ) :
    affinityLoss mean var x (fun i => some (.exact (b i))) θ =
      (∑ i, ((b i - mean θ (x i)) ^ 2 / var θ (x i) + log (var θ (x i)))) / 2 := by
  simp [affinityLoss, Finset.sum_div]

/-- **The affinity loss is the Gaussian negative log-likelihood up to a constant.** On measured
affinities `b i` and positive predicted variances, the affinity loss is the negative
log-likelihood of the training set under the model, `-log ∏ᵢ 𝒩(b i; μ_θ(x i), σ²_θ(x i))`, less
the constant `n log (2π) / 2` for `n` examples. -/
theorem affinityLoss_exact_eq_neg_log_prod_gaussianPDFReal {mean : Θ → X → ℝ}
    {var : Θ → X → ℝ≥0} {x : ι → X} (b : ι → ℝ) {θ : Θ} (hvar : ∀ i, var θ (x i) ≠ 0) :
    affinityLoss mean var x (fun i => some (.exact (b i))) θ =
      -log (∏ i, gaussianPDFReal (mean θ (x i)) (var θ (x i)) (b i)) -
        Fintype.card ι * log (2 * π) / 2 := by
  rw [log_prod fun i _ => (gaussianPDFReal_pos _ _ _ (hvar i)).ne']
  simp only [affinityLoss, Option.elim,
    affinityTerm_exact_eq_neg_log_gaussianPDFReal _ (hvar _), Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- **Maximum likelihood is minimum affinity loss.** On measured affinities `b i`, if the
predicted variances are positive at every parameter of a set `S`, a parameter `θ₀ ∈ S` maximises
the Gaussian likelihood `∏ᵢ 𝒩(b i; μ_θ(x i), σ²_θ(x i))` over `S` exactly when it minimises the
affinity loss over `S`. -/
theorem isMaxOn_prod_gaussianPDFReal_iff_isMinOn_affinityLoss {mean : Θ → X → ℝ}
    {var : Θ → X → ℝ≥0} {x : ι → X} (b : ι → ℝ) {S : Set Θ} {θ₀ : Θ} (hθ₀ : θ₀ ∈ S)
    (hvar : ∀ θ ∈ S, ∀ i, var θ (x i) ≠ 0) :
    IsMaxOn (fun θ => ∏ i, gaussianPDFReal (mean θ (x i)) (var θ (x i)) (b i)) S θ₀ ↔
      IsMinOn (affinityLoss mean var x fun i => some (.exact (b i))) S θ₀ := by
  have key : ∀ θ ∈ S, ∏ i, gaussianPDFReal (mean θ (x i)) (var θ (x i)) (b i) =
      exp (-(affinityLoss mean var x (fun i => some (.exact (b i))) θ +
        Fintype.card ι * log (2 * π) / 2)) := by
    intro θ hθ
    rw [affinityLoss_exact_eq_neg_log_prod_gaussianPDFReal b (hvar θ hθ), sub_add_cancel, neg_neg,
      exp_log (Finset.prod_pos fun i _ => gaussianPDFReal_pos _ _ _ (hvar θ hθ i))]
  simp only [isMaxOn_iff, isMinOn_iff]
  refine forall₂_congr fun θ hθ => ?_
  rw [key θ hθ, key θ₀ hθ₀, exp_le_exp]
  constructor <;> intro h <;> linarith

/-- **With a constant variance the affinity loss is least squares.** On measured affinities
`b i`, a constant predicted variance `v` turns the affinity loss into the sum of squared residuals
divided by `2 v`, plus a constant. -/
theorem affinityLoss_const_var (mean : Θ → X → ℝ) (v : ℝ≥0) (x : ι → X) (b : ι → ℝ) (θ : Θ) :
    affinityLoss mean (fun _ _ => v) x (fun i => some (.exact (b i))) θ =
      (∑ i, (b i - mean θ (x i)) ^ 2) / (2 * v) + Fintype.card ι * log v / 2 := by
  simp only [affinityLoss_exact, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.sum_div]
  ring

/-- **With a constant positive variance the affinity loss has the least-squares minimisers.** On
measured affinities `b i`, under a constant predicted variance `v ≠ 0`, a parameter minimises the
affinity loss over a set `S` exactly when it minimises the sum of squared residuals
`∑ᵢ (b i - μ_θ(x i)) ^ 2` over `S`. -/
theorem isMinOn_affinityLoss_const_var_iff {mean : Θ → X → ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {x : ι → X} (b : ι → ℝ) {S : Set Θ} {θ₀ : Θ} :
    IsMinOn (affinityLoss mean (fun _ _ => v) x fun i => some (.exact (b i))) S θ₀ ↔
      IsMinOn (fun θ => ∑ i, (b i - mean θ (x i)) ^ 2) S θ₀ := by
  have hv' : (0 : ℝ) < 2 * v := by positivity
  simp only [isMinOn_iff, affinityLoss_const_var, add_le_add_iff_right,
    div_le_div_iff_of_pos_right hv']

/-! ### The joint loss -/

/-- Without observed presentation labels, the joint loss is the affinity loss. -/
theorem jointLoss_of_forall_eq_none (mean : Θ → X → ℝ) (var : Θ → X → ℝ≥0) (prob : Θ → X → ℝ)
    (x : ι → X) (a : ι → Option AffinityLabel) {y : ι → Option Bool} (hy : ∀ i, y i = none)
    (θ : Θ) :
    jointLoss mean var prob x a y θ = affinityLoss mean var x a θ := by
  simp [jointLoss, hy]

end Domains.Biology.Immunology.HeteroscedasticAffinity
