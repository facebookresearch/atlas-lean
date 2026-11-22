/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.MetricInCoordinates

/-!
# The `C^k` topology on smooth Riemannian metrics

The space `𝒢^k(M)` of all smooth Riemannian metrics on a manifold `M`, with the `C^k`
topology of K. Burns and V. S. Matveev, Open problems and questions about geodesics,
Ergodic Theory Dynam. Systems 41 (2021) 641-684, §8.3 (arXiv:1308.5417v2 §8.4:
finite-atlas `ε`-balls of `C^k` norms of the `g_ij`), which they identify with the weak
`C^k` topology of M. W. Hirsch, Differential Topology, GTM 33, Ch. 2. `k = ⊤` is the
`C^∞` topology (smooth, not real-analytic). The metrics are smooth for every `k`. The
definition ranges over the whole maximal atlas, so no chart is chosen. On a closed
manifold it agrees with the finite-atlas `ε`-ball topology by the standard argument
(relatively compact chart domains, chain rule), which is not formalized here.
-/

@[expose] public section

open scoped ContDiff Manifold
open Topology Filter

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]

/-- The weak (compact-open) `C^k` topology on smooth Riemannian metrics: the infimum, over
all charts of the maximal atlas and all orders `i` with `(i : ℕ∞) ≤ k`, of the topology
induced by sending `g` to the iterated derivative of its coordinate expression, with
uniform convergence on compact subsets of the chart target. Source: Burns-Matveev v2 §8.4
finite-atlas `ε`-balls, v3 §8.3 weak `C^k` topology after Hirsch Ch. II. `k = ⊤` is the
`C^∞` topology (smooth, not analytic). The space carries smooth metrics for every `k`, and
no chart is chosen. Equality with the finite-atlas `ε`-ball topology on a closed manifold
is the standard argument (relatively compact chart domains and chain rule) and is not
formalized here. -/
@[instance_reducible]
def metricCkTopology (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (k : ℕ∞) :
    TopologicalSpace (Bundle.ContMDiffRiemannianMetric I ∞ E
      (fun x : M ↦ TangentSpace I x)) :=
  ⨅ (e : ↥(IsManifold.maximalAtlas I ∞ M)) (i : ℕ) (_hh : (i : ℕ∞) ≤ k),
    TopologicalSpace.induced
      (fun g =>
        UniformOnFun.ofFun {K : Set E | IsCompact K ∧ K ⊆ (e.val.extend I).target}
          (iteratedFDerivWithin ℝ i (metricInCoordinates g e.val)
            (e.val.extend I).target))
      inferInstance

set_option linter.unusedVariables false in
-- The synonym keeps the model and manifold parameters explicit to match the API contract.
/-- The space `𝒢^k(M)` of all smooth metrics with the `C^k` topology: a type synonym for
the smooth Riemannian metrics, carrying `metricCkTopology`. It is not the space of `C^k`
metrics; every element is smooth, and `k` only indexes the topology. -/
@[nolint unusedArguments]
def RiemannianMetricWithCk (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (k : ℕ∞) : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)

/-- The synonym `RiemannianMetricWithCk` carries the `C^k` topology `metricCkTopology`. -/
instance (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (k : ℕ∞) :
    TopologicalSpace (RiemannianMetricWithCk I M k) :=
  metricCkTopology I M k

/-- The identity equivalence between smooth metrics and the `𝒢^k(M)` synonym. -/
def RiemannianMetricWithCk.ofMetric {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] (k : ℕ∞) :
    Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ≃
      RiemannianMetricWithCk I M k :=
  Equiv.refl _

/-- Explicit convergence criterion for the `C^k` topology (Burns-Matveev v3 §8.3):
convergence means uniform convergence on compact subsets of every chart target, of every
iterated derivative of order at most `k` of the coordinate expression. -/
theorem tendsto_metricCkTopology_iff {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k : ℕ∞}
    {α : Type*} {l : Filter α}
    {g : α → Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g₀ : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    Tendsto g l (@nhds _ (metricCkTopology I M k) g₀) ↔
      ∀ e ∈ IsManifold.maximalAtlas I ∞ M, ∀ i : ℕ, (i : ℕ∞) ≤ k →
        ∀ K : Set E, IsCompact K → K ⊆ (e.extend I).target →
          TendstoUniformlyOn
            (fun a => iteratedFDerivWithin ℝ i (metricInCoordinates (g a) e)
              (e.extend I).target)
            (iteratedFDerivWithin ℝ i (metricInCoordinates g₀ e) (e.extend I).target)
            l K := by
  have key : ∀ (e : OpenPartialHomeomorph M H) (i : ℕ),
      Tendsto g l
          (@nhds _ (TopologicalSpace.induced
            (fun g' : Bundle.ContMDiffRiemannianMetric I ∞ E
              (fun x : M ↦ TangentSpace I x) =>
              UniformOnFun.ofFun
                {K : Set E | IsCompact K ∧ K ⊆ (e.extend I).target}
                (iteratedFDerivWithin ℝ i (metricInCoordinates g' e)
                  (e.extend I).target)) inferInstance) g₀) ↔
        ∀ K : Set E, IsCompact K → K ⊆ (e.extend I).target →
          TendstoUniformlyOn
            (fun a => iteratedFDerivWithin ℝ i (metricInCoordinates (g a) e)
              (e.extend I).target)
            (iteratedFDerivWithin ℝ i (metricInCoordinates g₀ e) (e.extend I).target)
            l K := by
    intro e i
    rw [nhds_induced, tendsto_comap_iff,
      UniformOnFun.tendsto_iff_tendstoUniformlyOn]
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h K hK hKs
      exact h K ⟨hK, hKs⟩
    · intro h K hK
      exact h K hK.1 hK.2
  unfold metricCkTopology
  simp only [nhds_iInf, tendsto_iInf]
  constructor
  · intro h e he i hi K hK hKs
    exact (key e i).mp (h ⟨e, he⟩ i hi) K hK hKs
  · intro h e i hi
    obtain ⟨e, he⟩ := e
    exact (key e i).mpr (h e he i hi)

/-- The same convergence criterion for the `𝒢^k(M)` synonym. -/
theorem RiemannianMetricWithCk.tendsto_iff {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k : ℕ∞}
    {α : Type*} {l : Filter α}
    {g : α → Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    {g₀ : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} :
    Tendsto (fun a => RiemannianMetricWithCk.ofMetric k (g a)) l
        (𝓝 (RiemannianMetricWithCk.ofMetric k g₀)) ↔
      ∀ e ∈ IsManifold.maximalAtlas I ∞ M, ∀ i : ℕ, (i : ℕ∞) ≤ k →
        ∀ K : Set E, IsCompact K → K ⊆ (e.extend I).target →
          TendstoUniformlyOn
            (fun a => iteratedFDerivWithin ℝ i (metricInCoordinates (g a) e)
              (e.extend I).target)
            (iteratedFDerivWithin ℝ i (metricInCoordinates g₀ e) (e.extend I).target)
            l K := by
  exact tendsto_metricCkTopology_iff

/-- The `C^{k'}` topology is finer than the `C^k` topology when `k ≤ k'`. -/
theorem metricCkTopology_anti {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k k' : ℕ∞}
    (h : k ≤ k') :
    metricCkTopology I M k' ≤ metricCkTopology I M k := by
  unfold metricCkTopology
  apply le_iInf
  intro e
  apply le_iInf
  intro i
  apply le_iInf
  intro hi
  exact (iInf_le _ e).trans ((iInf_le _ i).trans (iInf_le _ (le_trans hi h)))

set_option maxSynthPendingDepth 2 in
-- Instances on the iterated-derivative codomain are not found at the default depth 1;
-- the norm estimate in `tendsto_conformalScale_const_metricCkTopology` fails without it.
/-- Constant rescalings of a metric converge to it in every `C^k` topology as the factor
tends to `1`: in every chart the coordinate expression of the rescaled metric is `c a •`
that of `g`, hence so is each iterated derivative within the chart target, while those
derivatives of `g` are bounded on each compact subset of the target. -/
theorem tendsto_conformalScale_const_metricCkTopology {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {α : Type*} {l : Filter α} (c : α → ℝ) (hc : ∀ a, 0 < c a)
    (hlim : Tendsto c l (𝓝 1)) (k : ℕ∞) :
    Tendsto
      (fun a => g.conformalScale (fun _ => c a) contMDiff_const (fun _ => hc a)) l
      (@nhds _ (metricCkTopology I M k) g) := by
  rw [tendsto_metricCkTopology_iff]
  intro e he i hi K hK hKs
  have hcont : ContDiffOn ℝ ∞ (metricInCoordinates g e) (e.extend I).target :=
    contDiffOn_metricInCoordinates g he
  have hopen : IsOpen e.target := e.open_target
  have huniq : UniqueDiffOn ℝ (e.extend I).target := by
    rw [OpenPartialHomeomorph.extend_target]
    exact ModelWithCorners.uniqueDiffOn_preimage I hopen
  have hle : ContDiffOn ℝ (↑i : WithTop ℕ∞) (metricInCoordinates g e)
      (e.extend I).target :=
    hcont.of_le (by simp)
  have hcts : ContinuousOn
      (iteratedFDerivWithin ℝ i (metricInCoordinates g e) (e.extend I).target)
      (e.extend I).target :=
    hcont.continuousOn_iteratedFDerivWithin (by simp) huniq
  have hderiv : ∀ a x, x ∈ (e.extend I).target →
      iteratedFDerivWithin ℝ i
        (metricInCoordinates
          (g.conformalScale (fun _ => c a) contMDiff_const (fun _ => hc a)) e)
        (e.extend I).target x
      = (c a) • iteratedFDerivWithin ℝ i (metricInCoordinates g e)
        (e.extend I).target x := by
    intro a x hx
    have hfun : metricInCoordinates
          (g.conformalScale (fun _ => c a) contMDiff_const (fun _ => hc a)) e
        = (c a) • metricInCoordinates g e := by
      funext y
      simp only [metricInCoordinates_conformalScale, Pi.smul_apply]
    rw [hfun]
    exact iteratedFDerivWithin_const_smul_apply (hle.contDiffWithinAt hx) huniq hx
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcts.mono hKs)
  have hB : (0 : ℝ) < |C| + 1 := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hevent : ∀ᶠ a in l, dist (c a) 1 < ε / (|C| + 1) :=
    (Metric.tendsto_nhds.mp hlim) _ (div_pos hε hB)
  filter_upwards [hevent] with a ha
  intro x hxK
  have hx : x ∈ (e.extend I).target := hKs hxK
  have hDeq := hderiv a x hx
  have hnorm : ‖iteratedFDerivWithin ℝ i (metricInCoordinates g e)
      (e.extend I).target x‖ ≤ |C| + 1 :=
    le_trans (le_trans (hC x hxK) (le_abs_self C))
      (le_add_of_nonneg_right zero_le_one)
  have habs : |1 - c a| < ε / (|C| + 1) := by
    have h1 : dist (c a) 1 < ε / (|C| + 1) := ha
    rwa [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] at h1
  have hsm : (1 - c a) • iteratedFDerivWithin ℝ i (metricInCoordinates g e)
        (e.extend I).target x
      = (1 : ℝ) • iteratedFDerivWithin ℝ i (metricInCoordinates g e)
        (e.extend I).target x - (c a) • iteratedFDerivWithin ℝ i
        (metricInCoordinates g e) (e.extend I).target x :=
    sub_smul _ _ _
  have hsub : iteratedFDerivWithin ℝ i (metricInCoordinates g e)
        (e.extend I).target x - (c a) • iteratedFDerivWithin ℝ i
        (metricInCoordinates g e) (e.extend I).target x
      = (1 - c a) • iteratedFDerivWithin ℝ i (metricInCoordinates g e)
        (e.extend I).target x := by
    rw [hsm, one_smul]
  rw [hDeq]
  calc dist (iteratedFDerivWithin ℝ i (metricInCoordinates g e)
            (e.extend I).target x)
          ((c a) • iteratedFDerivWithin ℝ i (metricInCoordinates g e)
            (e.extend I).target x)
        = ‖(1 - c a) • iteratedFDerivWithin ℝ i (metricInCoordinates g e)
            (e.extend I).target x‖ := by
          rw [dist_eq_norm, hsub]
      _ ≤ ‖(1 - c a : ℝ)‖ * ‖iteratedFDerivWithin ℝ i (metricInCoordinates g e)
            (e.extend I).target x‖ :=
          norm_smul_le (1 - c a) (iteratedFDerivWithin ℝ i (metricInCoordinates g e)
            (e.extend I).target x)
      _ = |1 - c a| * ‖iteratedFDerivWithin ℝ i (metricInCoordinates g e)
            (e.extend I).target x‖ := by
          rw [Real.norm_eq_abs]
      _ ≤ |1 - c a| * (|C| + 1) :=
          mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
      _ < ε / (|C| + 1) * (|C| + 1) :=
          mul_lt_mul_of_pos_right habs hB
      _ = ε := div_mul_cancel₀ _ (ne_of_gt hB)

end Manifold
