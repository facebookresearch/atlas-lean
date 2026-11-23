/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.Volume
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Variational Laplace eigenvalues on Riemannian manifolds

Values in `ℝ≥0∞` with `∫⁻` and `⨅`/`⨆`. Energy integrand `‖mvfderiv I u x‖ₑ ^ 2`
is the metric differential norm. Zero-based smooth-core min-max over `(k+1)`-dimensional
spaces staying `(k+1)`-dimensional in `L²(μ)`; the admissibility condition is as in
Karpukhin-Stern arXiv:2004.04086 eq. (2.4), whose energy is integrated against `dv_g`
with only the mass against `μ`. Here both energy and mass use `μ`: the smooth-function
analogue of the weighted (Bakry-Emery) form of Colbois-El Soufi-Savo Sec. 2, whose `R`
integrates energy against `σ dv_g` and mass against `ν`, with `λ_k(L_σ) = μ_k(σ, σ dv_g)`;
their `μ_k` runs over `k`-dimensional subspaces of `H¹(M)` (one-based, so their `μ_1` is
the bottom) while this file runs over smooth `(k+1)`-dimensional subspaces (zero-based,
so index `k` here corresponds to their index `k + 1`); no equality of the smooth-core
and `H¹` values is claimed; for `μ = dv_g`
this is the classical quotient of Kokarev arXiv:1103.2448 eq. (1.2), the `k`-th Laplace
eigenvalue for the volume of a compact surface with `W = ⊤` (Neumann when the boundary is
nonempty). Dirichlet uses `C∞_c(U)`; Lamboley-Sicbaldi arXiv:1907.08159 eq. (1) gives the
first eigenvalue `λ₁(Ω)` as the minimum over `H¹₀`, the `H¹`-closure of `C∞_c`, for open
`Ω` in a manifold without boundary in dimension `n ≥ 2`. Outside that setting the file
defines min-max values only (manifolds with boundary and other indices/dimensions are
admitted by the signatures; e.g. `U = M` on compact `M` with boundary admits constants
with value `0`). Value `⊤` for empty family. Compactness, connectedness and boundary
conditions are hypotheses of statements, not definitions. No existence, discreteness,
eigenfunction or spectrum claim.

Euclidean counterpart: `MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean`
bundles `DirichletLaplacian.SmoothTestSpace Ω` as `TestFunction Ω ℝ ⊤`, with real
`DirichletLaplacian.rayleighQuotient` from Bochner integrals over `volume` and zero-based
real `DirichletLaplacian.variationalEigenvalue` from `sInf`/`sSup` in `ℝ` (hence `0` for
an empty family or an unbounded quotient), underpinning
`NonnegativeDiscreteSpectrum.IsDirichletSpectrum`. Euclidean-domain statements through
that predicate belong there; this file covers Riemannian manifolds, weighted measures,
and settings needing `⊤` for the empty family. The Dirichlet core here is a submodule
cut out by `HasCompactSupport` and `tsupport ⊆ U` on `C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯` because
Mathlib `TestFunction` exists only over open sets in a normed space, not over manifolds;
over a normed space the cores match via `Manifold.testFunctionLinearEquiv`. Nonzero
core members have positive finite mass via
`Manifold.mass_pos_lt_top_of_mem_smoothTestSubmodule`, proved here, which discharges
the mass-admissibility condition of `Manifold.variationalEigenvalue`. The
`EuclideanSpace ℝ (Fin n)` comparison with `volume` and `U = Ω` lives in the separate
bridge module `VariationalEigenvalueEuclidean.lean`, which imports this file, via
`Manifold.rayleighQuotient_testFunction`,
`Manifold.ofReal_dirichletLaplacian_variationalEigenvalue_le` and
`Manifold.variationalEigenvalue_eq_top_of_forall_finrank_ne`; no equality of the two
values is claimed here.
-/

@[expose] public section
open Bundle MeasureTheory
open scoped ENNReal NNReal Manifold ContDiff
noncomputable section
namespace Manifold
universe uE uH uM uF
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
/-- Dirichlet energy `∫ |∇_g u|² dμ`; `⊤` means infinite energy. -/
def dirichletEnergy (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [MeasurableSpace M] (μ : Measure M) (u : M → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ‖mvfderiv I u x‖ₑ ^ 2 ∂μ
/-- Rayleigh quotient; meaningful for positive finite `L²(μ)` mass. -/
def rayleighQuotient (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [MeasurableSpace M] (μ : Measure M) (u : M → ℝ) : ℝ≥0∞ :=
  dirichletEnergy I μ u / ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ
/-- Zero-based smooth-core min-max; `⊤` when no admissible subspace exists. Admissibility
of `(k+1)`-dimensional spaces remaining `(k+1)`-dimensional in `L²(μ)` is as in
Karpukhin-Stern eq. (2.4), where the energy uses `dv_g` and only the mass uses `μ`; here
both use `μ`, i.e. the smooth-function analogue of the weighted (Bakry-Emery) form
`μ_k(σ, σ dv_g)` of Colbois-El Soufi-Savo Sec. 2, taken over smooth subspaces rather than
their `H¹(M)` subspaces, with zero-based index `k` here corresponding to their one-based
index `k + 1`; no equality with their `H¹` value is claimed. For `μ` the Riemannian
volume this is the classical quotient of Kokarev eq. (1.2), the `k`-th Laplace eigenvalue
for a compact surface with `W = ⊤` (Neumann with boundary). -/
def variationalEigenvalue (I : ModelWithCorners ℝ E H) {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [MeasurableSpace M]
    (W : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) (μ : Measure M) (k : ℕ) : ℝ≥0∞ :=
  ⨅ V : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, ⨅ (_ : V ≤ W),
    ⨅ (_ : Module.finrank ℝ ↥V = k + 1),
      ⨅ (_ : ∀ u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, u ∈ V → u ≠ 0 →
        0 < ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ ∧ ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ < ⊤),
        ⨆ (u : ↥V), ⨆ (_ : u ≠ 0),
          rayleighQuotient I μ ⇑(u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)
/-- Dirichlet core `C∞_c(U)`: compactly supported smooth functions in `U`.
Cut out by `HasCompactSupport` and `tsupport ⊆ U` on `C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯`
rather than a bundled type since Mathlib `TestFunction` is only on open subsets
of a normed space, not on manifolds; on a normed space the cores agree through
`Manifold.testFunctionLinearEquiv`. -/
def smoothTestSubmodule (I : ModelWithCorners ℝ E H) {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M] (U : TopologicalSpace.Opens M) :
    Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ where
  carrier := {u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ |
    HasCompactSupport (⇑u : M → ℝ) ∧ tsupport (⇑u : M → ℝ) ⊆ (↑U : Set M)}
  zero_mem' := by
    have hcoe : (⇑(0 : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) : M → ℝ) = (0 : M → ℝ) :=
      ContMDiffMap.coe_zero
    have hsup : HasCompactSupport (0 : M → ℝ) := HasCompactSupport.zero
    have hts : tsupport (0 : M → ℝ) = ∅ := tsupport_zero
    constructor
    · rw [hcoe]; exact hsup
    · rw [hcoe, hts]; exact Set.empty_subset _
  add_mem' := by
    intro (x : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) (y : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)
      (hx : HasCompactSupport (⇑x : M → ℝ) ∧ tsupport (⇑x : M → ℝ) ⊆ (↑U : Set M))
      (hy : HasCompactSupport (⇑y : M → ℝ) ∧ tsupport (⇑y : M → ℝ) ⊆ (↑U : Set M))
    have hcoe : (⇑(x + y) : M → ℝ) = (⇑x : M → ℝ) + (⇑y : M → ℝ) :=
      ContMDiffMap.coe_add x y
    have hsup : HasCompactSupport (⇑(x + y) : M → ℝ) := by
      rw [hcoe]; exact HasCompactSupport.add hx.1 hy.1
    have hts : tsupport (⇑(x + y) : M → ℝ) ⊆
        tsupport (⇑x : M → ℝ) ∪ tsupport (⇑y : M → ℝ) := by
      rw [hcoe]; exact tsupport_add _ _
    exact ⟨hsup, Set.Subset.trans hts (Set.union_subset hx.2 hy.2)⟩
  smul_mem' := by
    intro (r : ℝ) (x : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)
      (hx : HasCompactSupport (⇑x : M → ℝ) ∧ tsupport (⇑x : M → ℝ) ⊆ (↑U : Set M))
    have hcoe : (⇑(r • x) : M → ℝ) = r • (⇑x : M → ℝ) :=
      ContMDiffMap.coe_smul r x
    have heq : (r • (⇑x : M → ℝ) : M → ℝ) =
        (((fun _ : M => r) • (⇑x : M → ℝ)) : M → ℝ) := by
      funext (a : M); rfl
    have hsup : HasCompactSupport (⇑(r • x) : M → ℝ) := by
      rw [hcoe, heq]
      exact HasCompactSupport.smul_left (f := (fun _ : M => r)) hx.1
    have hts : tsupport (⇑(r • x) : M → ℝ) ⊆ tsupport (⇑x : M → ℝ) := by
      rw [hcoe, heq]
      exact tsupport_smul_subset_right (fun _ : M => r) (⇑x : M → ℝ)
    exact ⟨hsup, Set.Subset.trans hts hx.2⟩
/-- Energy of a constant function is `0`. -/
theorem dirichletEnergy_const (I : ModelWithCorners ℝ E H) {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [MeasurableSpace M]
    (μ : Measure M) (c : ℝ) : dirichletEnergy I μ (fun _ => c) = 0 := by
  have hder : ∀ x : M, mvfderiv I (fun _ => c) x =
      (0 : TangentSpace I x →L[ℝ] ℝ) := fun (x : M) => mvfderiv_const c
  have hreal0 : ∀ x : M, ‖(0 : TangentSpace I x →L[ℝ] ℝ)‖ = 0 := by
    intro (x : M)
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (le_refl (0 : ℝ))
      intro (w : TangentSpace I x)
      simp
    · exact norm_nonneg (0 : TangentSpace I x →L[ℝ] ℝ)
  have hnn0 : ∀ x : M, ‖(0 : TangentSpace I x →L[ℝ] ℝ)‖₊ = 0 :=
    fun (x : M) => Subtype.ext (hreal0 x)
  have h0 : ∀ x : M, (‖mvfderiv I (fun _ => c) x‖ₑ : ℝ≥0∞) = 0 := by
    intro (x : M)
    rw [hder x, enorm_eq_nnnorm, hnn0 x]
    simp
  have hfun : (fun x : M => (‖mvfderiv I (fun _ => c) x‖ₑ ^ 2 : ℝ≥0∞)) =
      fun _ => 0 := by
    funext (x : M)
    rw [h0 x]
    simp
  unfold dirichletEnergy; rw [hfun]; exact lintegral_zero
/-- Monotonicity: a larger test space gives a smaller min-max value. -/
theorem variationalEigenvalue_antitone (I : ModelWithCorners ℝ E H) {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [MeasurableSpace M]
    {W₁ W₂ : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯} (hW : W₁ ≤ W₂)
    (μ : Measure M) (k : ℕ) :
    variationalEigenvalue I W₂ μ k ≤ variationalEigenvalue I W₁ μ k := by
  apply le_iInf; intro V; apply le_iInf; intro h₁
  exact le_trans (iInf_le _ V) (iInf_le _ (le_trans h₁ hW))
/-- Test-space upper bound over one admissible `V`. -/
theorem variationalEigenvalue_le_iSup (I : ModelWithCorners ℝ E H) {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [MeasurableSpace M]
    {W V : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯}
    (μ : Measure M) (k : ℕ) (hVW : V ≤ W)
    (hfin : Module.finrank ℝ ↥V = k + 1)
    (hmass : ∀ u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, u ∈ V → u ≠ 0 →
      0 < ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ ∧ ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ < ⊤) :
    variationalEigenvalue I W μ k ≤
      ⨆ (u : ↥V), ⨆ (_ : u ≠ 0),
        rayleighQuotient I μ ⇑(u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :=
  le_trans (iInf_le _ V) (le_trans (iInf_le _ hVW)
    (le_trans (iInf_le _ hfin) (iInf_le _ hmass)))
/-- Uniform lower bound for every min-max value. -/
theorem le_variationalEigenvalue (I : ModelWithCorners ℝ E H) {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [MeasurableSpace M]
    {W : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯} {c : ℝ≥0∞}
    (μ : Measure M) (k : ℕ)
    (h : ∀ u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯, u ∈ W → u ≠ 0 →
      0 < ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ → ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ < ⊤ →
      c ≤ rayleighQuotient I μ ⇑u) :
    c ≤ variationalEigenvalue I W μ k := by
  apply le_iInf; intro V; apply le_iInf; intro hVW
  apply le_iInf; intro hfin; apply le_iInf; intro hL2
  have hne : V ≠ ⊥ := by
    intro hV
    have hfin0 : Module.finrank ℝ ↥V = 0 := by
      rw [hV]; exact finrank_bot ℝ _
    have hcontra : k + 1 = 0 := by rw [← hfin, hfin0]
    omega
  obtain ⟨x₀, hxV, hxne⟩ : ∃ x ∈ V, x ≠ (0 : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :=
    Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxW : x₀ ∈ W := hVW hxV
  have hm : 0 < ∫⁻ x, ‖⇑x₀ x‖ₑ ^ 2 ∂μ ∧ ∫⁻ x, ‖⇑x₀ x‖ₑ ^ 2 ∂μ < ⊤ :=
    hL2 x₀ hxV hxne
  have hc : c ≤ rayleighQuotient I μ ⇑x₀ := h x₀ hxW hxne hm.1 hm.2
  have hu0 : (⟨x₀, hxV⟩ : ↥V) ≠ 0 := by
    intro h0
    exact hxne (congrArg Subtype.val h0)
  apply le_trans hc
  apply le_iSup_of_le (⟨x₀, hxV⟩ : ↥V)
  apply le_iSup_of_le hu0
  exact le_rfl
/-- Empty family: no admissible subspace of `⊥`, so the infimum is `⊤`. -/
theorem variationalEigenvalue_bot (I : ModelWithCorners ℝ E H) {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [MeasurableSpace M]
    (μ : Measure M) (k : ℕ) : variationalEigenvalue I ⊥ μ k = ⊤ := by
  apply iInf_eq_top.mpr; intro V; apply iInf_eq_top.mpr; intro hV
  apply iInf_eq_top.mpr; intro hfin
  have hVeq : V = ⊥ := le_antisymm hV bot_le
  have hfin0 : Module.finrank ℝ ↥V = 0 := by rw [hVeq]; exact finrank_bot ℝ _
  have hcontra : k + 1 = 0 := by rw [← hfin, hfin0]
  omega
/-- Zero measure: every mass is `0`, so no subspace is `L²`-faithful. -/
theorem variationalEigenvalue_zero_measure (I : ModelWithCorners ℝ E H)
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [MeasurableSpace M]
    (W : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) (k : ℕ) :
    variationalEigenvalue I W 0 k = ⊤ := by
  apply iInf_eq_top.mpr; intro V; apply iInf_eq_top.mpr; intro hVW
  apply iInf_eq_top.mpr; intro hfin; apply iInf_eq_top.mpr; intro hL2
  have hne : V ≠ ⊥ := by
    intro hV
    have hfin0 : Module.finrank ℝ ↥V = 0 := by
      rw [hV]; exact finrank_bot ℝ _
    have hcontra : k + 1 = 0 := by rw [← hfin, hfin0]
    omega
  obtain ⟨x₀, hxV, hxne⟩ : ∃ x ∈ V, x ≠ (0 : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :=
    Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hm : 0 < ∫⁻ x, ‖⇑x₀ x‖ₑ ^ 2 ∂(0 : Measure M) := (hL2 x₀ hxV hxne).1
  have hmass0 : (∫⁻ x, ‖⇑x₀ x‖ₑ ^ 2 ∂(0 : Measure M)) = 0 := by simp
  rw [hmass0] at hm; exact False.elim (lt_irrefl _ hm)
/-- The bottom min-max is `0` when constants lie in `W` with finite positive mass. -/
theorem variationalEigenvalue_zero_eq_zero (I : ModelWithCorners ℝ E H)
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [MeasurableSpace M]
    {W : Submodule ℝ C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯} (μ : Measure M)
    (h1 : ContMDiffMap.const (1 : ℝ) ∈ W)
    (hpos : 0 < μ Set.univ) (hfin : μ Set.univ < ⊤) :
    variationalEigenvalue I W μ 0 = 0 := by
  have hmass1 : (∫⁻ _ : M, (‖(1 : ℝ)‖ₑ ^ 2 : ℝ≥0∞) ∂μ) = μ Set.univ := by
    have h1e : (‖(1 : ℝ)‖ₑ ^ 2 : ℝ≥0∞) = 1 := by simp
    have hconst : (∫⁻ _ : M, (‖(1 : ℝ)‖ₑ ^ 2 : ℝ≥0∞) ∂μ) =
        (1 : ℝ≥0∞) * μ Set.univ := by rw [← h1e]; exact lintegral_const _
    rw [hconst, one_mul]
  have hVle : Submodule.span ℝ
      {(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)} ≤ W := by
    rw [Submodule.span_le]
    intro (x : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)
      (hx : x ∈ ({(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)} : Set _))
    have hxeq : x = ContMDiffMap.const (1 : ℝ) :=
      Set.mem_singleton_iff.mp hx
    rw [hxeq]; exact h1
  have hne1 : (ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) ≠ 0 := by
    intro hcon
    have hm0 : (∫⁻ x : M,
        ‖⇑(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) x‖ₑ ^ 2 ∂μ) = 0 := by
      rw [hcon]; simp [ContMDiffMap.coe_zero]
    have hm1 : (∫⁻ x : M,
        ‖⇑(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) x‖ₑ ^ 2 ∂μ) =
        μ Set.univ := by
      have heq : (fun x : M => ‖⇑(ContMDiffMap.const (1 : ℝ) :
          C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) x‖ₑ ^ 2) =
          (fun _ : M => (‖(1 : ℝ)‖ₑ ^ 2 : ℝ≥0∞)) := by funext (x : M); rfl
      rw [heq]; exact hmass1
    rw [hm1] at hm0; rw [hm0] at hpos; exact lt_irrefl _ hpos
  have hfin1 : Module.finrank ℝ ↥(Submodule.span ℝ
      {(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)}) = 0 + 1 :=
    finrank_span_singleton hne1
  have hL2 : ∀ (u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯),
      u ∈ Submodule.span ℝ
        {(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)} → u ≠ 0 →
      0 < ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ ∧ ∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ < ⊤ := by
    intro (u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)
      (hu : u ∈ Submodule.span ℝ
        {(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)}) (hune : u ≠ 0)
    obtain ⟨c, hcu⟩ := Submodule.mem_span_singleton.mp hu
    have hcne : c ≠ 0 := by
      intro hc0; exact hune (by rw [← hcu, hc0]; simp)
    have hfun : (⇑u : M → ℝ) = (fun _ : M => c) := by
      rw [← hcu, ContMDiffMap.coe_smul]; funext (x : M)
      have h1x : (⇑(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :
          M → ℝ) x = 1 := rfl
      change c • (⇑(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :
        M → ℝ) x = c
      rw [h1x, smul_eq_mul, mul_one]
    have hcabs : (0 : ℝ) < |c| := abs_pos.mpr hcne
    have hof : (0 : ℝ≥0∞) < ENNReal.ofReal |c| := ENNReal.ofReal_pos.mpr hcabs
    have he : ‖c‖ₑ = ENNReal.ofReal |c| := Real.enorm_eq_ofReal_abs c
    have hcpos : (0 : ℝ≥0∞) < ‖c‖ₑ := by rw [he]; exact hof
    have hsqpos : (0 : ℝ≥0∞) < ‖c‖ₑ ^ 2 := by
      rw [pow_two]; exact ENNReal.mul_pos (ne_of_gt hcpos) (ne_of_gt hcpos)
    have hnormtop : (‖c‖ₑ ^ 2 : ℝ≥0∞) < ⊤ := by
      rw [he, pow_two]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    have hmass : (∫⁻ x, ‖⇑u x‖ₑ ^ 2 ∂μ) = (‖c‖ₑ ^ 2) * μ Set.univ := by
      have heq : (fun x : M => ‖⇑u x‖ₑ ^ 2) =
          (fun _ : M => (‖c‖ₑ ^ 2 : ℝ≥0∞)) := by funext (x : M); rw [hfun]
      rw [heq]; exact lintegral_const _
    refine ⟨?_, ?_⟩
    · rw [hmass]
      exact ENNReal.mul_pos (ne_of_gt hsqpos) (ne_of_gt hpos)
    · rw [hmass]; exact ENNReal.mul_lt_top hnormtop hfin
  have hsup0 : (⨆ (u : ↥(Submodule.span ℝ
      {(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)})),
      ⨆ (_ : u ≠ 0), rayleighQuotient I μ
        ⇑(u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯)) ≤ 0 := by
    apply iSup_le; intro u; apply iSup_le; intro _
    obtain ⟨c, hcu⟩ := Submodule.mem_span_singleton.mp u.property
    have hfun : ⇑(u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) = (fun _ : M => c) := by
      have hrew : (u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) =
          c • ContMDiffMap.const (1 : ℝ) := hcu.symm
      rw [hrew, ContMDiffMap.coe_smul]; funext (x : M)
      have h1x : (⇑(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :
          M → ℝ) x = 1 := rfl
      change c • (⇑(ContMDiffMap.const (1 : ℝ) : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) :
        M → ℝ) x = c
      rw [h1x, smul_eq_mul, mul_one]
    have henergy : dirichletEnergy I μ ⇑(u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) = 0 := by
      rw [hfun]; exact dirichletEnergy_const I μ c
    have hrw : rayleighQuotient I μ ⇑(u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) = 0 := by
      unfold rayleighQuotient; rw [henergy]; exact ENNReal.zero_div
    exact le_of_eq hrw
  have hle : variationalEigenvalue I W μ 0 ≤ 0 :=
    le_trans (variationalEigenvalue_le_iSup I μ 0 hVle hfin1 hL2) hsup0
  exact le_antisymm hle bot_le
/-- A larger open set has a larger Dirichlet core. -/
theorem smoothTestSubmodule_mono (I : ModelWithCorners ℝ E H) {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M]
    {U₁ U₂ : TopologicalSpace.Opens M} (h : U₁ ≤ U₂) :
    smoothTestSubmodule I U₁ ≤ smoothTestSubmodule I U₂ := by
  intro (u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) (hu : u ∈ smoothTestSubmodule I U₁)
  obtain ⟨hsup, hsub⟩ : HasCompactSupport (⇑u : M → ℝ) ∧
      tsupport (⇑u : M → ℝ) ⊆ (↑U₁ : Set M) := hu
  have hsub2 : tsupport (⇑u : M → ℝ) ⊆ (↑U₂ : Set M) :=
    Set.Subset.trans hsub h
  exact ⟨hsup, hsub2⟩
/-- Squared norm of a compactly supported function keeps compact support. -/
theorem hasCompactSupport_norm_sq {X : Type*} [TopologicalSpace X]
    {G : Type*} [NormedAddCommGroup G] {g : X → G}
    (hg : HasCompactSupport g) :
    HasCompactSupport fun x : X => (‖g x‖ ^ 2 : ℝ) := by
  have hsub : Function.support (fun x : X => (‖g x‖ ^ 2 : ℝ)) ⊆
      Function.support g := by
    intro x hx
    have hne : (‖g x‖ ^ 2 : ℝ) ≠ 0 := Function.mem_support.mp hx
    have hgx : g x ≠ 0 := by
      intro h0
      exact hne (by rw [h0]; simp)
    exact Function.mem_support.mpr hgx
  exact IsCompact.of_isClosed_subset hg.isCompact isClosed_closure
    (closure_mono hsub)
/-- Positive finite mass of a nonzero smooth-core function. -/
theorem mass_pos_lt_top_of_mem_smoothTestSubmodule {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E' H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
    [OpensMeasurableSpace M] (μ : Measure M) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] {U : TopologicalSpace.Opens M}
    {u : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯} (hu : u ∈ smoothTestSubmodule I U)
    (hne : u ≠ 0) :
    0 < ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ ∧ ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ < ⊤ := by
  have hsupp : HasCompactSupport (⇑u : M → ℝ) := hu.1
  have hcont : Continuous (⇑u : M → ℝ) := (ContMDiffMap.contMDiff u).continuous
  have hfun_ne : (⇑u : M → ℝ) ≠ (0 : M → ℝ) := by
    intro h0
    apply hne
    apply ContMDiffMap.ext
    intro x
    have hx1 : (⇑u : M → ℝ) x = 0 := by rw [h0]; rfl
    have hzero : ((0 : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯) : M → ℝ) x = 0 := by
      rw [ContMDiffMap.coe_zero]; rfl
    exact hx1.trans hzero.symm
  obtain ⟨x₀, hx₀⟩ : ∃ x : M, (⇑u : M → ℝ) x ≠ 0 := by
    obtain ⟨y, hy⟩ : ∃ x : M, (⇑u : M → ℝ) x ≠ (0 : M → ℝ) x :=
      Function.ne_iff.mp hfun_ne
    exact ⟨y, by simpa using hy⟩
  have hRcont : Continuous (fun x : M => (((⇑u : M → ℝ) x) ^ 2 : ℝ)) :=
    hcont.pow 2
  have hnorm_eq : (fun x : M => (‖(⇑u : M → ℝ) x‖ ^ 2 : ℝ)) =
      (fun x : M => (((⇑u : M → ℝ) x) ^ 2 : ℝ)) := by
    funext x
    rw [Real.norm_eq_abs, sq_abs]
  have hRsupp : HasCompactSupport (fun x : M => (((⇑u : M → ℝ) x) ^ 2 : ℝ)) := by
    rw [← hnorm_eq]
    exact hasCompactSupport_norm_sq (g := (⇑u : M → ℝ)) hsupp
  have hRne : (fun x : M => (((⇑u : M → ℝ) x) ^ 2 : ℝ)) x₀ ≠ 0 :=
    pow_ne_zero 2 hx₀
  have hIntPos : 0 < ∫ x : M, (((⇑u : M → ℝ) x) ^ 2 : ℝ) ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hRcont
      hRsupp (fun x => sq_nonneg _) hRne
  have hInt : Integrable (fun x : M => (((⇑u : M → ℝ) x) ^ 2 : ℝ)) μ :=
    Continuous.integrable_of_hasCompactSupport hRcont hRsupp
  have hAE : 0 ≤ᵐ[μ] (fun x : M => (((⇑u : M → ℝ) x) ^ 2 : ℝ)) :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have heq : ENNReal.ofReal (∫ x : M, (((⇑u : M → ℝ) x) ^ 2 : ℝ) ∂μ) =
      ∫⁻ x : M, ENNReal.ofReal (((⇑u : M → ℝ) x) ^ 2) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hInt hAE
  have hpt : ∀ x : M, ENNReal.ofReal (((⇑u : M → ℝ) x) ^ 2) =
      (‖((⇑u : M → ℝ) x)‖ₑ ^ 2) := by
    intro x
    have hr : (‖((⇑u : M → ℝ) x)‖ₑ) = ENNReal.ofReal |((⇑u : M → ℝ) x)| :=
      Real.enorm_eq_ofReal_abs _
    rw [← sq_abs ((⇑u : M → ℝ) x), ENNReal.ofReal_pow (abs_nonneg _) 2, ← hr]
  have hmass : (∫⁻ x : M, (‖((⇑u : M → ℝ) x)‖ₑ ^ 2) ∂μ) =
      ENNReal.ofReal (∫ x : M, (((⇑u : M → ℝ) x) ^ 2 : ℝ) ∂μ) := by
    rw [← funext hpt]
    exact heq.symm
  rw [hmass]
  exact ⟨ENNReal.ofReal_pos.mpr hIntPos, ENNReal.ofReal_lt_top⟩
/-- On a vector space the bundle energy is the Euclidean gradient energy. -/
theorem dirichletEnergy_vectorSpace {F : Type uF} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] (μ : Measure F) (u : F → ℝ) :
    dirichletEnergy 𝓘(ℝ, F) μ u = ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ 2 ∂μ := by
  have h_eq : ∀ x : F, (‖mvfderiv 𝓘(ℝ, F) u x‖ₑ ^ 2 : ℝ≥0∞) =
      (‖fderiv ℝ u x‖ₑ ^ 2 : ℝ≥0∞) := by
    intro (x : F)
    have hmv : mvfderiv 𝓘(ℝ, F) u x = fderiv ℝ u x ∘SL
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap :=
      mvfderiv_eq_fderiv
    have hiso : ∀ v : TangentSpace 𝓘(ℝ, F) x,
        ‖(NormedSpace.fromTangentSpace (𝕜 := ℝ) x) v‖ = ‖v‖ := fun v =>
      (norm_tangentSpace_vectorSpace (v := v)).symm
    have hM_R : (0 : ℝ) ≤ ‖fderiv ℝ u x‖ := norm_nonneg _
    have hleR : ‖mvfderiv 𝓘(ℝ, F) u x‖ ≤ ‖fderiv ℝ u x‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ hM_R
      intro (w : TangentSpace 𝓘(ℝ, F) x)
      have hisow : ‖(NormedSpace.fromTangentSpace (𝕜 := ℝ) x) w‖ = ‖w‖ := hiso w
      have happ : (fderiv ℝ u x ∘SL
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap) w =
          fderiv ℝ u x ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) w) := by simp
      have hle : ‖fderiv ℝ u x ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) w)‖ ≤
          ‖fderiv ℝ u x‖ * ‖(NormedSpace.fromTangentSpace (𝕜 := ℝ) x) w‖ :=
        ContinuousLinearMap.le_opNorm _ _
      rw [hmv, happ, ← hisow]; exact hle
    have hM_L : (0 : ℝ) ≤ ‖mvfderiv 𝓘(ℝ, F) u x‖ :=
      norm_nonneg (mvfderiv 𝓘(ℝ, F) u x)
    have hleL : ‖fderiv ℝ u x‖ ≤ ‖mvfderiv 𝓘(ℝ, F) u x‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ hM_L
      intro (y : F)
      have hnorms : ‖(NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm y‖ = ‖y‖ := by
        have h1 := hiso ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm y)
        have h2 : (NormedSpace.fromTangentSpace (𝕜 := ℝ) x)
            ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm y) = y := by simp
        rw [h2] at h1; exact h1.symm
      have happ : (fderiv ℝ u x ∘SL
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap)
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm y) = fderiv ℝ u x y := by simp
      have hle : ‖(fderiv ℝ u x ∘SL
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap)
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm y)‖ ≤
          ‖mvfderiv 𝓘(ℝ, F) u x‖ * ‖(NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm y‖ := by
        rw [← hmv]; exact ContinuousLinearMap.le_opNorm _ _
      rw [happ, hnorms] at hle; exact hle
    have hnorm : ‖mvfderiv 𝓘(ℝ, F) u x‖ = ‖fderiv ℝ u x‖ :=
      le_antisymm hleR hleL
    have hcoe : ((‖mvfderiv 𝓘(ℝ, F) u x‖₊ : ℝ≥0) : ℝ) =
        ((‖fderiv ℝ u x‖₊ : ℝ≥0) : ℝ) := by
      rw [coe_nnnorm, coe_nnnorm, hnorm]
    have hnn : ‖mvfderiv 𝓘(ℝ, F) u x‖₊ = ‖fderiv ℝ u x‖₊ :=
      Subtype.ext hcoe
    have henorm : (‖mvfderiv 𝓘(ℝ, F) u x‖ₑ : ℝ≥0∞) = ‖fderiv ℝ u x‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, hnn]
    rw [henorm]
  have hfun : (fun x : F => (‖mvfderiv 𝓘(ℝ, F) u x‖ₑ ^ 2 : ℝ≥0∞)) =
      (fun x : F => (‖fderiv ℝ u x‖ₑ ^ 2 : ℝ≥0∞)) := funext h_eq
  unfold dirichletEnergy; rw [hfun]
/-- Dirichlet min-max values of `U` over `C∞_c(U)` with Riemannian volume. Zero-based.
Lamboley-Sicbaldi eq. (1) gives the first eigenvalue `λ₁(Ω)` (`k = 0` here) as the minimum
over `H¹₀`, the `H¹`-closure of `C∞_c`, for open `Ω` in a manifold without boundary with
`n ≥ 2`; there the smooth-core infimum agrees. Otherwise min-max values only: the signature
admits manifolds with boundary and all dimensions/indices, and e.g. `U = M` on compact `M`
with boundary admits constants with bottom value `0`. -/
def dirichletEigenvalue (I : ModelWithCorners ℝ E H) {M : Type uM}
    [FiniteDimensional ℝ E] [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [MeasurableSpace M] [BorelSpace M]
    (U : TopologicalSpace.Opens M) (k : ℕ) : ℝ≥0∞ :=
  variationalEigenvalue I (smoothTestSubmodule I U) (Manifold.riemannianVolume I M) k
/-- Closed/Neumann min-max values over all smooth functions with Riemannian volume.
Kokarev eq. (1.2) states the identification with the `k`-th Laplace eigenvalue for the
volume of a compact surface (Neumann when the boundary is nonempty); no cited source states
it in other dimensions. For a connected closed compact surface `k = 1` is the first nonzero
mode; otherwise min-max values only. -/
def neumannEigenvalue (I : ModelWithCorners ℝ E H) (M : Type uM)
    [FiniteDimensional ℝ E] [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [MeasurableSpace M] [BorelSpace M] (k : ℕ) : ℝ≥0∞ :=
  variationalEigenvalue I ⊤ (Manifold.riemannianVolume I M) k
end Manifold
