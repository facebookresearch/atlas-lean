/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SplitConformalExactCoverage

/-!
# Full conformal prediction

Full (transductive) conformal prediction refits on the augmented data set
`Z_1, …, Z_n, (x, y)` for every trial response `y`, scores all `n + 1` points, and keeps `y`
when the score of the trial point is at most the `⌈(1 - α)(n + 1)⌉`-th smallest of the other
`n` scores. Lei, G'Sell, Rinaldo, Tibshirani and Wasserman (arXiv:1604.04173v2, 9 March 2017,
published in J. Amer. Statist. Assoc. 113 (2018) 1094–1111), Theorem 2.1, state the coverage
`P(Y_{n+1} ∈ C_conf(X_{n+1})) ≥ 1 - α` for i.i.d. data and a fitting algorithm that is symmetric
in the data, and the upper bound `1 - α + 1 / (n + 1)` when the fitted residuals have a
continuous joint law.

The proof here is the one sketched in that paper: at the true response `y = Y_{n+1}` the
augmented data set is the data itself, so `Y_{n+1} ∈ C_conf(X_{n+1})` is exactly the event that
the score of the last point is covered by the split conformal threshold of the score vector.
A score map that is equivariant under permutations of the data points sends an exchangeable
data vector to an exchangeable score vector, and the split conformal bounds
(`MathlibExt.Probability.Statistics.SplitConformal`,
`MathlibExt.Probability.Statistics.SplitConformalExactCoverage`) apply.

The set keeps a trial value when fewer than `k` data scores are strictly below its score, as
the split conformal threshold does. Lei et al.'s `π(y)` (their (5)) counts the data scores `≤` the
trial score instead; the two sets agree when the scores are distinct, and only the strict count
gives the lower bound without an assumption on ties.

The statements assume only that the law of the data vector is invariant under coordinate
permutations (exchangeability), which covers the i.i.d. case of the source; the upper bound
assumes that the scores are almost surely distinct, which is what the continuity assumption of
the source is used for. As in `SplitConformal`, `α = 0` is admitted as a trivial endpoint.

## Main definitions

* `IsPermEquivariant S`: the score map commutes with permutations of the data points.
* `fullConformalSet S k z x`: the full conformal prediction set at `x` built from `n` data points.
* `absResidualScore A`: absolute residuals of a fitting algorithm `A` trained on the full data.

## Main results

* `map_comp_perm_map_eq`: an equivariant score map sends an exchangeable law to an exchangeable
  law.
* `ofReal_one_sub_le_measure_mem_fullConformalSet`: coverage at least `1 - α`.
* `measure_mem_fullConformalSet_le`: without ties, coverage at most `1 - α + 1 / (n + 1)`.
* `isPermEquivariant_absResidualScore`: absolute residuals of a symmetric algorithm are
  equivariant, so the theorems apply to the regression set `(4)`, `(5)`, `(7)` of the source.
-/

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Statistics.SplitConformal
open MathlibExt.Probability.Statistics.SplitConformalExactCoverage

namespace MathlibExt.Probability.Statistics.FullConformal

variable {n : ℕ}

section Equivariance

variable {𝒵 : Type*}

/-- **Permutation-equivariant score map.** A map `S` from data vectors `z : Fin (n + 1) → 𝒵` to
score vectors is permutation equivariant if permuting the data points permutes the scores in the
same way: `S (z ∘ σ) = S z ∘ σ`. Scores of the form `f(z_{-i}; z_i)` with `f` symmetric in its
first `n` arguments (Lei et al., arXiv:1604.04173v2, Remark 2.4) have this property. -/
def IsPermEquivariant (S : (Fin (n + 1) → 𝒵) → Fin (n + 1) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin (n + 1))) (z : Fin (n + 1) → 𝒵), S (z ∘ σ) = S z ∘ σ

variable [MeasurableSpace 𝒵]

/-- **Equivariant scores of exchangeable data are exchangeable.** If the law `μ` of the data
vector is invariant under every coordinate permutation and the score map `S` is measurable and
permutation equivariant, then the law of the score vector `S z` is invariant under every
coordinate permutation. -/
theorem map_comp_perm_map_eq (μ : Measure (Fin (n + 1) → 𝒵))
    (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun z => z ∘ σ) = μ)
    {S : (Fin (n + 1) → 𝒵) → Fin (n + 1) → ℝ} (hS : IsPermEquivariant S) (hSm : Measurable S)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (μ.map S).map (fun ω => ω ∘ σ) = μ.map S := by
  have hpermR : Measurable (fun ω : Fin (n + 1) → ℝ => ω ∘ σ) :=
    Measurable.of_eval fun i => measurable_pi_apply (σ i)
  have hpermZ : Measurable (fun z : Fin (n + 1) → 𝒵 => z ∘ σ) :=
    Measurable.of_eval fun i => measurable_pi_apply (σ i)
  rw [Measure.map_map hpermR hSm]
  have hcomm : (fun ω : Fin (n + 1) → ℝ => ω ∘ σ) ∘ S = S ∘ fun z => z ∘ σ :=
    funext fun z => (hS σ z).symm
  rw [hcomm, ← Measure.map_map hSm hpermZ, hμ σ]

end Equivariance

section FullConformal

variable {𝒳 𝒴 : Type*}

/-- **Full conformal prediction set.** Given `n` data points `z : Fin n → 𝒳 × 𝒴`, a test
covariate `x` and a score map `S` on augmented data vectors, the full conformal set at `x` is the
set of trial responses `y` such that the score of the trial point `(x, y)` in the augmented data
set `Fin.snoc z (x, y)` is at most the `k`-th smallest of the other `n` scores (`⊤` when
`k > n`), i.e. such that fewer than `k` of the data scores are strictly below the trial score.
With `k = ⌈(1 - α)(n + 1)⌉` and distinct scores this is the set `{y : (n + 1) π(y) ≤ k}` of
Lei et al., arXiv:1604.04173v2, equation (7). Ties are treated differently: their `π(y)` in (5)
counts the data scores `≤` the trial score, which excludes a trial value tied with many data
scores, while this set keeps it; with their count the lower coverage bound needs almost surely
distinct scores, with this one it holds with no assumption on ties. -/
def fullConformalSet (S : (Fin (n + 1) → 𝒳 × 𝒴) → Fin (n + 1) → ℝ) (k : ℕ)
    (z : Fin n → 𝒳 × 𝒴) (x : 𝒳) : Set 𝒴 :=
  {y | (S (Fin.snoc (α := fun _ => 𝒳 × 𝒴) z (x, y)) (Fin.last n) : WithTop ℝ) ≤
    splitConformalThreshold k (S (Fin.snoc (α := fun _ => 𝒳 × 𝒴) z (x, y)))}

/-- **Full conformal coverage event as a split conformal event.** At the true response the
augmented data set is the data vector itself, so `Y_{n+1} ∈ C_conf(X_{n+1})` is the event that
the last score is covered by the split conformal threshold of the score vector. -/
theorem setOf_mem_fullConformalSet_eq (S : (Fin (n + 1) → 𝒳 × 𝒴) → Fin (n + 1) → ℝ) (k : ℕ) :
    {z : Fin (n + 1) → 𝒳 × 𝒴 |
        (z (Fin.last n)).2 ∈ fullConformalSet S k (Fin.init z) (z (Fin.last n)).1} =
      S ⁻¹' {ω | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold k ω} := by
  ext z
  simp only [fullConformalSet, Set.mem_ofPred_eq, Set.mem_preimage, Prod.mk.eta]
  rw [Fin.snoc_init_self]

variable [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

private theorem measurableSet_coe_le_splitConformalThreshold {k : ℕ} (hk : 1 ≤ k) :
    MeasurableSet {ω : Fin (n + 1) → ℝ |
      (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold k ω} := by
  have : {ω : Fin (n + 1) → ℝ | (ω (Fin.last n) : WithTop ℝ) ≤ splitConformalThreshold k ω} =
      strictLowerCount ⁻¹' Set.Iio k := by
    ext ω
    exact coe_le_splitConformalThreshold_iff hk ω
  rw [this]
  exact measurable_strictLowerCount MeasurableSet.of_discrete

/-- **Full conformal coverage.** Let the law `μ` of the data vector `(Z_1, …, Z_{n+1})`,
`Z_i = (X_i, Y_i)`, be a probability measure invariant under every coordinate permutation (an
i.i.d. law, for example), and let the score map `S` be measurable and permutation equivariant.
Then for `0 ≤ α < 1` the full conformal set built from the first `n` points at level
`k = ⌈(1 - α)(n + 1)⌉` covers `Y_{n+1}` at `X_{n+1}` with probability at least `1 - α`
(Lei, G'Sell, Rinaldo, Tibshirani and Wasserman, arXiv:1604.04173v2, Theorem 2.1, first part,
stated there for i.i.d. data and a symmetric fitting algorithm; due to Vovk). Ties are allowed;
see `fullConformalSet` for how they are counted. -/
theorem ofReal_one_sub_le_measure_mem_fullConformalSet (μ : Measure (Fin (n + 1) → 𝒳 × 𝒴))
    [IsProbabilityMeasure μ] (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun z => z ∘ σ) = μ)
    {S : (Fin (n + 1) → 𝒳 × 𝒴) → Fin (n + 1) → ℝ} (hS : IsPermEquivariant S)
    (hSm : Measurable S) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
      μ {z | (z (Fin.last n)).2 ∈
        fullConformalSet S ⌈(1 - α) * (n + 1)⌉₊ (Fin.init z) (z (Fin.last n)).1} := by
  have hk : 1 ≤ ⌈(1 - α) * (n + 1)⌉₊ :=
    Nat.one_le_ceil_iff.2 (mul_pos (sub_pos.2 hα1) (by positivity))
  rw [setOf_mem_fullConformalSet_eq, ← Measure.map_apply hSm
    (measurableSet_coe_le_splitConformalThreshold hk)]
  exact ofReal_one_sub_le_measure_coe_le_splitConformalThreshold (μ.map S)
    (map_comp_perm_map_eq μ hμ hS hSm) hα0 hα1

/-- **Upper bound on full conformal coverage without ties.** Under the hypotheses of
`ofReal_one_sub_le_measure_mem_fullConformalSet`, if moreover the `n + 1` scores `S z` are
almost surely distinct, the full conformal set covers `Y_{n+1}` with probability at most
`1 - α + 1 / (n + 1)` (Lei et al., arXiv:1604.04173v2, Theorem 2.1, second part, which assumes
that the fitted absolute residuals have a continuous joint distribution, used there only to
exclude ties). -/
theorem measure_mem_fullConformalSet_le (μ : Measure (Fin (n + 1) → 𝒳 × 𝒴))
    [IsProbabilityMeasure μ] (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun z => z ∘ σ) = μ)
    {S : (Fin (n + 1) → 𝒳 × 𝒴) → Fin (n + 1) → ℝ} (hS : IsPermEquivariant S)
    (hSm : Measurable S) (hinj : ∀ᵐ z ∂μ, Function.Injective (S z)) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) :
    μ {z | (z (Fin.last n)).2 ∈
        fullConformalSet S ⌈(1 - α) * (n + 1)⌉₊ (Fin.init z) (z (Fin.last n)).1} ≤
      ENNReal.ofReal (1 - α + 1 / (n + 1)) := by
  have hk : 1 ≤ ⌈(1 - α) * (n + 1)⌉₊ :=
    Nat.one_le_ceil_iff.2 (mul_pos (sub_pos.2 hα1) (by positivity))
  rw [setOf_mem_fullConformalSet_eq, ← Measure.map_apply hSm
    (measurableSet_coe_le_splitConformalThreshold hk)]
  refine measure_coe_le_splitConformalThreshold_le (μ.map S)
    (map_comp_perm_map_eq μ hμ hS hSm) ?_ hα0 hα1
  exact (ae_map_iff hSm.aemeasurable measurableSet_setOf_injective).2 hinj

end FullConformal

section Regression

variable {𝒳 : Type*}

/-- **Absolute residual score of a fitting algorithm.** For a fitting algorithm `A` that maps an
augmented data vector to a regression function, the score of point `i` is the absolute residual
`|Y_i - μ̂(X_i)|` of the fit `μ̂ = A z` trained on all `n + 1` points (Lei et al.,
arXiv:1604.04173v2, equation (4), with `μ̂_y = A (Fin.snoc z (x, y))`). -/
noncomputable def absResidualScore (A : (Fin (n + 1) → 𝒳 × ℝ) → 𝒳 → ℝ)
    (z : Fin (n + 1) → 𝒳 × ℝ) (i : Fin (n + 1)) : ℝ :=
  |(z i).2 - A z (z i).1|

/-- **Residuals of a symmetric algorithm are equivariant.** If the fitted regression function
does not depend on the order of the data points, `A (z ∘ σ) = A z`, then the absolute residual
score is permutation equivariant; the full conformal theorems then give Theorem 2.1 of Lei et al.
(arXiv:1604.04173v2) for its regression set. -/
theorem isPermEquivariant_absResidualScore {A : (Fin (n + 1) → 𝒳 × ℝ) → 𝒳 → ℝ}
    (hA : ∀ (σ : Equiv.Perm (Fin (n + 1))) (z : Fin (n + 1) → 𝒳 × ℝ), A (z ∘ σ) = A z) :
    IsPermEquivariant (absResidualScore A) := by
  intro σ z
  funext i
  simp [absResidualScore, hA]

end Regression

end MathlibExt.Probability.Statistics.FullConformal
