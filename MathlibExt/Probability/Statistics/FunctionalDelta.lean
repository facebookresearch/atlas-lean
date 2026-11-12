/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import MathlibExt.Probability.Statistics.Survival.NelsonAalen

/-!
# The functional delta theorem and the product-integral (Kaplan–Meier) map

## Topology

All weak convergence here is Mathlib's `MeasureTheory.TendstoInDistribution`: weak convergence of
the laws as Borel probability measures, tested against bounded continuous functions, on a
**normed space** `E` with its norm topology. No separability is assumed on `E`. The concrete
instances use two norms:

* the **sup norm on a fixed finite grid**, `Fin k → ℝ` (Mathlib's `Pi` norm is the max norm), for
  the fully proved Kaplan–Meier statements. Both grid theorems state their conclusion on the
  survival values at the grid times, and the hypothesis of
  `tendstoInDistribution_kmSurvival_grid_of_nelsonAalen` is on the cumulative hazard; on these
  coordinates the norm is the uniform topology of `D[0, τ]` restricted to the grid points. Only the
  hypothesis of `tendstoInDistribution_kmSurvival_grid` is on the hazard increments, where the
  norm is equivalent to the restricted uniform one only for fixed `k`;
* the **uniform (sup-norm) topology on `ℓ^∞([0, τ])`**, Mathlib's `lp (fun _ : Icc 0 τ ↦ ℝ) ∞`,
  for the continuous-time statement. `D[0, τ]` with the uniform norm sits isometrically inside it;
  this is the topology of van der Vaart (1998), §20.3, not the Skorokhod `J₁` topology.

## Main statements

* `HasHadamardDerivWithinAt φ φ' D E₀ θ`: Hadamard (directional) differentiability at `θ`,
  tangentially to `E₀`, for a map defined on the domain `D`.
* `HasFDerivAt.hasHadamardDerivWithinAt`: Fréchet differentiable maps are Hadamard
  differentiable, tangentially to every set.
* `MeasureTheory.TendstoInDistribution.extended_comp`: the **extended continuous mapping
  theorem** (van der Vaart, Theorem 18.11(i)) for `ℕ`-indexed sequences, proved from the
  portmanteau theorem.
* `MeasureTheory.TendstoInDistribution.functional_delta`: the **functional delta theorem**
  (van der Vaart, Theorem 20.8): if `r n → ∞`, `r n • (X n - θ) ⇒ G` with `G ∈ E₀` a.s., and `φ` is
  Hadamard differentiable at `θ` tangentially to `E₀`, then `r n • (φ (X n) - φ θ) ⇒ φ' G`.
  `functional_delta_of_continuous` drops the measurability side conditions for continuous
  `φ`, `φ'`.
* `MathlibExt.Probability.Statistics.FunctionalDelta.prodIntegral`: the product integral
  `x ↦ (j ↦ ∏_{i ≤ j} (1 + x i))` of a hazard-increment vector on a fixed grid.
  `prodIntegral_sub_prodIntegral` is the exact **discrete Duhamel equation**, and
  `hasFDerivAt_prodIntegral` / `hasHadamardDerivWithinAt_prodIntegral` give its derivative in
  **Duhamel (Volterra) form** `duhamelDeriv x h j = ∑_{i ≤ j} ∏_{l < i} (1 + x l) · h i ·
  ∏_{i < l ≤ j} (1 + x l)`.
* `kmSurvival_time_eq_prodIntegral`: the Kaplan–Meier estimate at the grid times is the product
  integral of minus the Nelson–Aalen increments.
* `tendstoInDistribution_kmSurvival_grid`, `tendstoInDistribution_kmSurvival_grid_of_nelsonAalen`:
  the **Kaplan–Meier limit law on a fixed grid** from a hazard (increment or cumulative
  Nelson–Aalen) CLT hypothesis: `√n (Ŝₙ - S) ⇒ -duhamelDeriv (-ΔΛ) (ΔG)`.
* `abs_prodIntegral_sub_le`: a Lipschitz bound for the grid product integral, with constants
  controlled by the total variations `∑ |x i|`, `∑ |y i|` and independent of `k`.
* `tendstoInDistribution_lInfty_of_hadamard`: `functional_delta` specialized to `ℓ^∞([0, τ])`
  with tangent set `C[0, τ]` and `r n = √n`, for arbitrary maps; it is the shape of the
  continuous-time Kaplan–Meier statement but is not tied to the Kaplan–Meier or Nelson–Aalen
  objects, and (see below) its hypotheses cannot hold for continuous-time Kaplan–Meier.

## What is proved and what is assumed

* The functional CLT for the Nelson–Aalen (counting-process) estimator is always an explicit
  hypothesis (`hCLT`); it is the target of a separate task and is not imported.
* Hadamard differentiability of the **continuous-time** product-integral map
  `A ↦ ∏_{(0, t]} (1 + dA)` on bounded-variation functions in `D[0, τ]` (van der Vaart,
  §20.3; Gill–Johansen 1990) is **not proved**: Mathlib has no Lebesgue–Stieltjes product
  integral. It is the explicit hypothesis `hHad` of `tendstoInDistribution_lInfty_of_hadamard`.
  What is proved is the finite-grid version, where the map is a polynomial in `k` variables and
  is Fréchet differentiable with the Duhamel derivative. The derivative, Hadamard derivative and
  continuity results are qualitative; `abs_prodIntegral_sub_le` is the only quantitative grid
  estimate, and its constants do not depend on `k`.
* Measurability is Borel measurability throughout (Mathlib's framework), not van der Vaart's
  outer-probability (Hoffmann-Jørgensen) framework. On a fixed grid this costs nothing. In the
  nonseparable space `ℓ^∞([0, τ])` it is disqualifying for Kaplan–Meier: the `AEMeasurable`
  fields of `hCLT` in `tendstoInDistribution_lInfty_of_hadamard` **fail on the canonical space
  of the observations whenever the law of the uncensored observation times in `[0, τ]` has a
  non-atomic part**. Take `n = 1` (enough, since the `AEMeasurable` field covers every `n` and
  translation is a homeomorphism) and the canonical space: the observation `(T, δ)` with the
  completion of `σ(T, δ)`. Then `Λ̂₁ = δ · 1[T, τ]` when `T ≤ τ` (and `0` otherwise); distinct
  such paths and the zero path are pairwise at sup distance `1`, so every set of paths is closed
  in `ℓ^∞([0, τ])`. The preimage of `{1[u, τ] | u ∈ A}` is `{δ = 1, T ∈ A}`, which is not in the
  completed `σ(T, δ)` when `A ⊆ [0, τ]` is non-measurable for the law of `T` on `{δ = 1}`; such
  `A` exists when that law has a non-atomic part. (On a general `Ω` the probability can be
  extended to make this set measurable, so the statement needs the canonical space or an
  Ulam-type set-theoretic assumption. With censoring before every death in `[0, τ]`, e.g.
  `C ≡ 0`, `Λ̂₁ ≡ 0` a.s. and the field holds.) This is the classical non-measurability of the
  empirical distribution function in `D[0, 1]` with the uniform metric (Billingsley 1999, §15;
  van der Vaart–Wellner 1996, §1.1). So that statement is a conditional that does not apply to
  continuous-time Kaplan–Meier in this case; the outer-probability framework is needed. The
  abstract theorems are correct as stated and apply whenever the processes are Borel measurable,
  e.g. on the grid or in a separable subspace.
* The sequences are indexed by `ℕ` with `atTop`.
* The Hadamard derivative is one-sided (`t ↓ 0`) and `φ'` need not be linear. Van der Vaart's
  definition (two-sided, `φ'` continuous linear on `E₀`) implies this one, so the delta theorem
  here applies under weaker hypotheses; for nonlinear `φ'` it is the directional delta method of
  Shapiro (1991).

## Source receipt (reuse search, 2026-11-11)

Mathlib v4.35.0 has convergence in distribution, Slutsky, and the portmanteau theorem
(`MeasureTheory.tendsto_of_forall_isClosed_limsup_le'`,
`ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`), used here; it has no Hadamard
differentiability, no extended continuous mapping theorem, and no product integral. The repo's
`MathlibExt.Probability.Statistics.DeltaMethod` is the Fréchet delta method on second-countable
spaces; `functional_delta` does not need second countability and allows tangential, directional
derivatives. The Kaplan–Meier and Nelson–Aalen estimators are reused from
`MathlibExt.Probability.Statistics.Survival.KaplanMeier` / `.NelsonAalen`.

## References

* A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 18.11, Theorem 20.8, §20.3.
* R. D. Gill and S. Johansen, *A survey of product-integration with a view toward application in
  survival analysis*, Ann. Statist. 18 (1990), 1501–1555.
* A. Shapiro, *Asymptotic analysis of stochastic programs*, Ann. Oper. Res. 30 (1991), 169–186.
* P. Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999), §15 "Uniform
  Topologies" (the uniform metric on `D[0, 1]`).
* A. W. van der Vaart and J. A. Wellner, *Weak Convergence and Empirical Processes* (1996), §1.1.
-/

@[expose] public section

open Filter Topology

section Hadamard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `φ` is **Hadamard differentiable** at `θ` with derivative `φ'`, tangentially to `E₀`, for the
domain `D`: for every `h ∈ E₀`,
`t⁻¹ • (φ (θ + t • k) - φ θ) → φ' h` as `t ↓ 0` and `k → h`, along those `(t, k)` with
`θ + t • k ∈ D`.

Equivalently, `(φ (θ + tₙ • hₙ) - φ θ) / tₙ → φ' h` for all sequences `tₙ ↓ 0`, `hₙ → h ∈ E₀`
with `θ + tₙ • hₙ ∈ D`. This is van der Vaart (1998), §20.2, except that `t` is one-sided and
`φ'` is not required to be linear (Shapiro's directional notion); the usual definition implies
this one. -/
def HasHadamardDerivWithinAt (φ φ' : E → F) (D E₀ : Set E) (θ : E) : Prop :=
  ∀ h ∈ E₀, Tendsto (fun p : ℝ × E ↦ p.1⁻¹ • (φ (θ + p.1 • p.2) - φ θ))
    ((𝓝[>] 0 ×ˢ 𝓝 h) ⊓ 𝓟 {p | θ + p.1 • p.2 ∈ D}) (𝓝 (φ' h))


/-- A Fréchet differentiable map is Hadamard differentiable, tangentially to every set `E₀` and
for every domain `D`, with the same derivative. -/
theorem HasFDerivAt.hasHadamardDerivWithinAt {φ : E → F} {L : E →L[ℝ] F} {θ : E}
    (hφ : HasFDerivAt φ L θ) (D E₀ : Set E) : HasHadamardDerivWithinAt φ L D E₀ θ := by
  intro h _
  set ψ : E → F := fun x ↦ ‖x - θ‖⁻¹ • (φ x - φ θ - L (x - θ)) with hψ_def
  have hψθ : ψ θ = 0 := by simp [ψ]
  have hψ : ContinuousAt ψ θ := by
    rw [ContinuousAt, hψθ, tendsto_zero_iff_norm_tendsto_zero]
    simpa [ψ, norm_smul] using hasFDerivAt_iff_tendsto.1 hφ
  have hmove : Tendsto (fun p : ℝ × E ↦ θ + p.1 • p.2) (𝓝[>] 0 ×ˢ 𝓝 h) (𝓝 θ) := by
    have hc : Continuous (fun p : ℝ × E ↦ θ + p.1 • p.2) := by fun_prop
    have := (hc.tendsto ((0 : ℝ), h)).mono_left (nhds_prod_eq (x := (0 : ℝ)) (y := h) ▸
      prod_mono_left (𝓝 h) (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (a := 0)))
    simpa using this
  have hlim : Tendsto (fun p : ℝ × E ↦ L p.2 + ‖p.2‖ • ψ (θ + p.1 • p.2)) (𝓝[>] 0 ×ˢ 𝓝 h)
      (𝓝 (L h + ‖h‖ • 0)) := by
    refine Tendsto.add ?_ (Tendsto.smul ?_ ?_)
    · exact (L.continuous.tendsto h).comp tendsto_snd
    · exact (continuous_norm.tendsto h).comp tendsto_snd
    · exact hψθ ▸ hψ.tendsto.comp hmove
  rw [smul_zero, add_zero] at hlim
  refine (hlim.congr' ?_).mono_left inf_le_left
  filter_upwards [(eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)).prod_inl (𝓝 h)]
    with p hp
  obtain ⟨t, k⟩ := p
  simp only [Set.mem_Ioi] at hp
  by_cases hk : k = 0
  · simp [hk]
  · have hkn : ‖k‖ ≠ 0 := norm_ne_zero_iff.2 hk
    simp only [ψ, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hp.le, map_smul, smul_smul]
    have h1 : ‖k‖ * (t * ‖k‖)⁻¹ = t⁻¹ := by field_simp
    rw [h1, smul_sub, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
    abel

end Hadamard

namespace MeasureTheory

section ExtendedCMT

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- **Extended continuous mapping theorem** (van der Vaart, Theorem 18.11(i)). Let `U n ⇒ V`
and let `g n, g₀ : X → Y` satisfy `g n xₙ → g₀ x` whenever `xₙ → x ∈ X₀` with `xₙ ∈ D n`
(stated with the filter `atTop ×ˢ 𝓝 x` restricted to `{(n, y) | y ∈ D n}`). If `U n ∈ D n` a.s.
and `V ∈ X₀` a.s., then `g n (U n) ⇒ g₀ V`.

No continuity of `g n` or `g₀` is assumed; the measurability of `g n ∘ U n` and `g₀ ∘ V` is.
`X` needs `HasOuterApproxClosed` (e.g. any pseudo-metric space) for the portmanteau direction
"weak convergence ⇒ limsup on closed sets"; `X₀` need not be measurable. -/
theorem TendstoInDistribution.extended_comp {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X] [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {U : ℕ → Ω → X} {V : Ω' → X} {g : ℕ → X → Y} {g₀ : X → Y}
    {D : ℕ → Set X} {X₀ : Set X}
    (hUV : TendstoInDistribution U atTop V (fun _ ↦ μ) μ')
    (hg : ∀ x ∈ X₀, Tendsto (fun p : ℕ × X ↦ g p.1 p.2) ((atTop ×ˢ 𝓝 x) ⊓ 𝓟 {p | p.2 ∈ D p.1})
      (𝓝 (g₀ x)))
    (hUD : ∀ n, ∀ᵐ ω ∂μ, U n ω ∈ D n) (hV : ∀ᵐ ω ∂μ', V ω ∈ X₀)
    (hgU : ∀ n, AEMeasurable (fun ω ↦ g n (U n ω)) μ) (hgV : AEMeasurable (fun ω ↦ g₀ (V ω)) μ') :
    TendstoInDistribution (fun n ω ↦ g n (U n ω)) atTop (fun ω ↦ g₀ (V ω)) (fun _ ↦ μ) μ' := by
  refine ⟨hgU, hgV, tendsto_of_forall_isClosed_limsup_le' fun K hK ↦ ?_⟩
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_apply_of_aemeasurable hgV hK.measurableSet]
  simp_rw [Measure.map_apply_of_aemeasurable (hgU _) hK.measurableSet]
  -- The closed sets `S k` capture all points where some `g m`, `m ≥ k`, lands in `K`.
  set S : ℕ → Set X := fun k ↦ closure (⋃ m ≥ k, D m ∩ g m ⁻¹' K) with hS_def
  have hS_closed : ∀ k, IsClosed (S k) := fun k ↦ isClosed_closure
  have hS_anti : Antitone S := fun k k' hkk' ↦ closure_mono <|
    Set.iUnion₂_mono' fun m hm ↦ ⟨m, hkk'.trans hm, subset_rfl⟩
  -- Step 1: `limsup ≤ P(V ∈ S k)` for each `k`.
  have h1 : ∀ k, limsup (fun n ↦ μ ((fun ω ↦ g n (U n ω)) ⁻¹' K)) atTop ≤ μ' (V ⁻¹' S k) := by
    intro k
    have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hUV.tendsto (hS_closed k)
    simp only [ProbabilityMeasure.coe_mk] at hlim
    rw [Measure.map_apply_of_aemeasurable hUV.aemeasurable_limit (hS_closed k).measurableSet]
      at hlim
    have hmid : limsup (fun n ↦ μ (U n ⁻¹' S k)) atTop ≤ μ' (V ⁻¹' S k) := by
      refine le_of_eq_of_le ?_ hlim
      congr 1
      funext n
      rw [Measure.map_apply_of_aemeasurable (hUV.forall_aemeasurable n)
        (hS_closed k).measurableSet]
    refine le_trans (limsup_le_limsup ?_) hmid
    filter_upwards [eventually_ge_atTop k] with n hn
    refine measure_mono_ae ?_
    filter_upwards [hUD n] with ω hω hgω
    exact subset_closure (Set.mem_biUnion hn ⟨hω, hgω⟩)
  -- Step 2: points of `X₀` in every `S k` are mapped by `g₀` into `K`.
  have h2 : ∀ x ∈ X₀, x ∈ ⋂ k, S k → g₀ x ∈ K := by
    intro x hx hxS
    by_contra hgx
    have hev := (hg x hx).eventually (hK.isOpen_compl.mem_nhds hgx)
    rw [eventually_inf_principal, eventually_prod_iff] at hev
    obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := hev
    obtain ⟨N, hN⟩ := eventually_atTop.1 hpa
    obtain ⟨y, hy, hyS⟩ := mem_closure_iff_nhds.1 (Set.mem_iInter.1 hxS N) _ hpb
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage] at hyS
    obtain ⟨m, hm, hyD, hyK⟩ := hyS
    exact hpapb (hN m hm) hy hyD hyK
  -- Step 3: continuity from above.
  have h3 : μ' (V ⁻¹' ⋂ k, S k) ≤ μ' ((fun ω ↦ g₀ (V ω)) ⁻¹' K) := by
    refine measure_mono_ae ?_
    filter_upwards [hV] with ω hω hωS
    exact h2 _ hω hωS
  have h4 : μ' (V ⁻¹' ⋂ k, S k) = ⨅ k, μ' (V ⁻¹' S k) := by
    rw [Set.preimage_iInter]
    exact Antitone.measure_iInter (fun k k' hkk' ↦ Set.preimage_mono (hS_anti hkk'))
      (fun k ↦ hUV.aemeasurable_limit.nullMeasurableSet_preimage (hS_closed k).measurableSet)
      ⟨0, measure_ne_top _ _⟩
  exact (le_iInf h1).trans (h4 ▸ h3)

end ExtendedCMT

section FunctionalDelta

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- **Functional delta theorem** (van der Vaart, Theorem 20.8). Let `r n → ∞` and
`r n • (X n - θ) ⇒ G` in the normed space `E`, with `G ∈ E₀` almost surely and `X n ∈ D` almost
surely. If `φ` is Hadamard differentiable at `θ` tangentially to `E₀` with derivative `φ'`, then
`r n • (φ (X n) - φ θ) ⇒ φ' G`.

`E` need not be separable. The measurability of `r n • (φ (X n) - φ θ)` and of `φ' ∘ G` is
assumed (Borel framework); `functional_delta_of_continuous` derives both when `φ` and `φ'` are
continuous. The proof applies `extended_comp` to `g n y = r n • (φ (θ + (r n)⁻¹ • y) - φ θ)`. -/
theorem TendstoInDistribution.functional_delta {X : ℕ → Ω → E} {G : Ω' → E} {θ : E}
    {r : ℕ → ℝ} {φ φ' : E → F} {D E₀ : Set E}
    (hXG : TendstoInDistribution (fun n ω ↦ r n • (X n ω - θ)) atTop G (fun _ ↦ μ) μ')
    (hr : Tendsto r atTop atTop) (hφ : HasHadamardDerivWithinAt φ φ' D E₀ θ)
    (hXD : ∀ n, ∀ᵐ ω ∂μ, X n ω ∈ D) (hG : ∀ᵐ ω ∂μ', G ω ∈ E₀)
    (hφX : ∀ n, AEMeasurable (fun ω ↦ r n • (φ (X n ω) - φ θ)) μ)
    (hφ'G : AEMeasurable (fun ω ↦ φ' (G ω)) μ') :
    TendstoInDistribution (fun n ω ↦ r n • (φ (X n ω) - φ θ)) atTop (fun ω ↦ φ' (G ω))
      (fun _ ↦ μ) μ' := by
  set g : ℕ → E → F := fun n y ↦ r n • (φ (θ + (r n)⁻¹ • y) - φ θ) with hg_def
  have hgX : ∀ n ω, g n (r n • (X n ω - θ)) = r n • (φ (X n ω) - φ θ) := by
    intro n ω
    by_cases hn : r n = 0
    · simp [g, hn]
    · simp [g, smul_smul, inv_mul_cancel₀ hn]
  set Dn : ℕ → Set E := fun n ↦ {y | r n ≠ 0 → θ + (r n)⁻¹ • y ∈ D} with hDn_def
  have hlim : ∀ h ∈ E₀, Tendsto (fun p : ℕ × E ↦ g p.1 p.2)
      ((atTop ×ˢ 𝓝 h) ⊓ 𝓟 {p | p.2 ∈ Dn p.1}) (𝓝 (φ' h)) := by
    intro h hh
    have hψ : Tendsto (fun p : ℕ × E ↦ ((r p.1)⁻¹, p.2))
        ((atTop ×ˢ 𝓝 h) ⊓ 𝓟 {p | p.2 ∈ Dn p.1})
        ((𝓝[>] 0 ×ˢ 𝓝 h) ⊓ 𝓟 {q : ℝ × E | θ + q.1 • q.2 ∈ D}) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
      · exact (((tendsto_inv_atTop_nhdsGT_zero.comp hr).prodMap tendsto_id)).mono_left
          inf_le_left
      · have hpos : {p : ℕ × E | 0 < r p.1} ∈ atTop ×ˢ 𝓝 h :=
          (hr.eventually_gt_atTop 0).prod_inl _
        filter_upwards [mem_inf_of_left hpos, mem_inf_of_right (mem_principal_self _)]
          with p hp hpD
        exact hpD hp.ne'
    refine ((hφ h hh).comp hψ).congr fun p ↦ ?_
    simp [g]
  have hXDn : ∀ n, ∀ᵐ ω ∂μ, r n • (X n ω - θ) ∈ Dn n := by
    intro n
    filter_upwards [hXD n] with ω hω hn
    simpa [smul_smul, inv_mul_cancel₀ hn] using hω
  have key := hXG.extended_comp hlim hXDn hG (fun n ↦ (hφX n).congr
    (ae_of_all _ fun ω ↦ (hgX n ω).symm)) hφ'G
  simpa only [hgX] using key

/-- **Functional delta theorem, continuous case.** As `functional_delta`, but when `φ` and `φ'`
are continuous the measurability side conditions are automatic. -/
theorem TendstoInDistribution.functional_delta_of_continuous {X : ℕ → Ω → E} {G : Ω' → E}
    {θ : E} {r : ℕ → ℝ} {φ φ' : E → F} {D E₀ : Set E}
    (hXG : TendstoInDistribution (fun n ω ↦ r n • (X n ω - θ)) atTop G (fun _ ↦ μ) μ')
    (hr : Tendsto r atTop atTop) (hφ : HasHadamardDerivWithinAt φ φ' D E₀ θ)
    (hXD : ∀ n, ∀ᵐ ω ∂μ, X n ω ∈ D) (hG : ∀ᵐ ω ∂μ', G ω ∈ E₀) (hφc : Continuous φ)
    (hφ'c : Continuous φ') :
    TendstoInDistribution (fun n ω ↦ r n • (φ (X n ω) - φ θ)) atTop (fun ω ↦ φ' (G ω))
      (fun _ ↦ μ) μ' := by
  refine hXG.functional_delta hr hφ hXD hG (fun n ↦ ?_)
    (hφ'c.measurable.comp_aemeasurable hXG.aemeasurable_limit)
  by_cases hn : r n = 0
  · exact (aemeasurable_const (b := (0 : F))).congr (ae_of_all _ fun ω ↦ by simp [hn])
  · have hc : Continuous fun y : E ↦ r n • (φ (θ + (r n)⁻¹ • y) - φ θ) := by fun_prop
    refine (hc.measurable.comp_aemeasurable (hXG.forall_aemeasurable n)).congr
      (ae_of_all _ fun ω ↦ ?_)
    simp [smul_smul, inv_mul_cancel₀ hn]

end FunctionalDelta

end MeasureTheory

namespace MathlibExt.Probability.Statistics.FunctionalDelta

open Finset MeasureTheory
open scoped ENNReal

section Telescoping

/-- Telescoping identity behind the discrete Duhamel equation: over a finset of a linearly
ordered type,
`∏ a - ∏ b = ∑_i (∏_{l < i} b l) (a i - b i) (∏_{l > i} a l)`. -/
theorem prod_sub_prod_eq_sum {α R : Type*} [LinearOrder α] [CommRing R] (s : Finset α)
    (a b : α → R) :
    ∏ i ∈ s, a i - ∏ i ∈ s, b i =
      ∑ i ∈ s, (∏ l ∈ s.filter (· < i), b l) * (a i - b i) * ∏ l ∈ s.filter (i < ·), a l := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert m s hm ih =>
    have hms : m ∉ s := fun h ↦ lt_irrefl _ (hm m h)
    rw [prod_insert hms, prod_insert hms, sum_insert hms]
    have e1 : (insert m s).filter (· < m) = s := by
      ext x
      simp only [mem_filter, mem_insert]
      exact ⟨fun h ↦ h.1.resolve_left (ne_of_lt h.2), fun h ↦ ⟨Or.inr h, hm x h⟩⟩
    have e2 : (insert m s).filter (m < ·) = ∅ := by
      ext x
      simp only [mem_filter, mem_insert, notMem_empty, iff_false, not_and, not_lt]
      rintro (rfl | hx)
      · exact le_rfl
      · exact (hm x hx).le
    have e3 : ∀ i ∈ s, (insert m s).filter (· < i) = s.filter (· < i) := by
      intro i hi
      rw [filter_insert, ite_eq_right (not_lt.2 (hm i hi).le)]
    have e4 : ∀ i ∈ s, (insert m s).filter (i < ·) = insert m (s.filter (i < ·)) := by
      intro i hi
      rw [filter_insert, ite_eq_left (hm i hi)]
    rw [e1, e2, prod_empty, sum_congr rfl fun i hi ↦ by
      rw [e3 i hi, e4 i hi, prod_insert (fun h ↦ hms (mem_filter.1 h).1)]]
    have : ∑ i ∈ s, (∏ l ∈ s.filter (· < i), b l) * (a i - b i) *
        (a m * ∏ l ∈ s.filter (i < ·), a l) =
        a m * ∑ i ∈ s, (∏ l ∈ s.filter (· < i), b l) * (a i - b i) *
          ∏ l ∈ s.filter (i < ·), a l := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    rw [this, ← ih]
    ring

end Telescoping

section ProductIntegral

variable {k : ℕ}

/-- The **product integral on a fixed grid**: for hazard increments `x i` at the grid points
`t₀ < ⋯ < t_{k-1}`, `prodIntegral x j = ∏_{i ≤ j} (1 + x i)`, the product integral
`∏_{(0, t_j]} (1 + dA)` of the pure-jump function `A` with jumps `x i` at `tᵢ`. With
`x = -ΔΛ` it is the survival function of the cumulative hazard `Λ`
(see `kmSurvival_time_eq_prodIntegral`). -/
def prodIntegral (x : Fin k → ℝ) (j : Fin k) : ℝ := ∏ i ∈ Iic j, (1 + x i)

/-- The derivative of `prodIntegral` at `x`, in **Duhamel (Volterra) form**:
`duhamelDeriv x h j = ∑_{i ≤ j} (∏_{l < i} (1 + x l)) · h i · ∏_{i < l ≤ j} (1 + x l)`,
the grid analogue of `h ↦ ∫_{(0, t]} ∏_{(0, s)} (1 + dA) dh(s) ∏_{(s, t]} (1 + dA)`
(Gill–Johansen 1990). -/
noncomputable def duhamelDeriv (x : Fin k → ℝ) : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun j ↦ ∑ i ∈ Iic j,
    ((∏ l ∈ Iio i, (1 + x l)) * ∏ l ∈ Ioc i j, (1 + x l)) • ContinuousLinearMap.proj i

/-- Coordinates of `duhamelDeriv`. -/
theorem duhamelDeriv_apply (x h : Fin k → ℝ) (j : Fin k) :
    duhamelDeriv x h j =
      ∑ i ∈ Iic j, (∏ l ∈ Iio i, (1 + x l)) * h i * ∏ l ∈ Ioc i j, (1 + x l) := by
  simp only [duhamelDeriv, ContinuousLinearMap.pi_apply, FunLike.coe_sum,
    Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  exact sum_congr rfl fun i _ ↦ by ring

private theorem filter_Iic_lt {i j : Fin k} (hij : i ≤ j) : (Iic j).filter (· < i) = Iio i := by
  ext l
  simp only [mem_filter, mem_Iic, mem_Iio]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.le.trans hij, h⟩⟩

private theorem filter_Iic_gt {i j : Fin k} : (Iic j).filter (i < ·) = Ioc i j := by
  ext l
  simp only [mem_filter, mem_Iic, mem_Ioc]
  exact And.comm

/-- **Discrete Duhamel equation**: the exact difference of two product integrals,
`∏_{i ≤ j} (1 + y i) - ∏_{i ≤ j} (1 + x i) = ∑_{i ≤ j} (∏_{l < i} (1 + x l)) (y i - x i)
∏_{i < l ≤ j} (1 + y l)` (Gill–Johansen 1990, on a grid). -/
theorem prodIntegral_sub_prodIntegral (x y : Fin k → ℝ) (j : Fin k) :
    prodIntegral y j - prodIntegral x j =
      ∑ i ∈ Iic j, (∏ l ∈ Iio i, (1 + x l)) * (y i - x i) * ∏ l ∈ Ioc i j, (1 + y l) := by
  rw [prodIntegral, prodIntegral, prod_sub_prod_eq_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [filter_Iic_lt (mem_Iic.1 hi), filter_Iic_gt]
  ring

private theorem erase_Iic {i j : Fin k} (hij : i ≤ j) : (Iic j).erase i = Iio i ∪ Ioc i j := by
  ext l
  simp only [mem_erase, mem_Iic, mem_union, mem_Iio, mem_Ioc]
  constructor
  · rintro ⟨hne, hl⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hl⟩
  · rintro (h | h)
    · exact ⟨h.ne, h.le.trans hij⟩
    · exact ⟨h.1.ne', h.2⟩

/-- The product integral on a grid is Fréchet differentiable, with derivative `duhamelDeriv`. -/
theorem hasFDerivAt_prodIntegral (x : Fin k → ℝ) :
    HasFDerivAt prodIntegral (duhamelDeriv x) x := by
  rw [duhamelDeriv]
  refine hasFDerivAt_pi.2 fun j ↦ ?_
  have h := HasFDerivAt.finsetProd (u := Iic j) (g := fun i (y : Fin k → ℝ) ↦ 1 + y i)
    (g' := fun i ↦ (ContinuousLinearMap.proj (R := ℝ) i : (Fin k → ℝ) →L[ℝ] ℝ)) (x := x)
    (fun i _ ↦ (hasFDerivAt_apply (𝕜 := ℝ) i x).const_add (1 : ℝ))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [erase_Iic (mem_Iic.1 hi), prod_union]
  exact disjoint_left.2 fun l hl hl' ↦ (mem_Iio.1 hl).not_gt (mem_Ioc.1 hl').1

/-- The product integral on a grid is Hadamard differentiable, tangentially to every set, with
the Duhamel derivative. -/
theorem hasHadamardDerivWithinAt_prodIntegral (x : Fin k → ℝ) (D E₀ : Set (Fin k → ℝ)) :
    HasHadamardDerivWithinAt prodIntegral (duhamelDeriv x) D E₀ x :=
  (hasFDerivAt_prodIntegral x).hasHadamardDerivWithinAt D E₀

/-- The increments `ΔA j = A j - A (j - 1)` (with `A (-1) := 0`) of a cumulative function sampled
on the grid; it turns a cumulative hazard into hazard increments. -/
noncomputable def gridIncrements : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.proj j -
    if h : 0 < (j : ℕ) then ContinuousLinearMap.proj ⟨j - 1, by omega⟩ else 0

/-- Coordinates of `gridIncrements`. -/
theorem gridIncrements_apply (A : Fin k → ℝ) (j : Fin k) :
    gridIncrements A j = A j - if h : 0 < (j : ℕ) then A ⟨j - 1, by omega⟩ else 0 := by
  simp only [gridIncrements, ContinuousLinearMap.pi_apply, sub_apply,
    ContinuousLinearMap.proj_apply]
  split_ifs <;> simp

/-- `gridIncrements` inverts cumulative sums. -/
theorem gridIncrements_cumsum (x : Fin k → ℝ) :
    gridIncrements (fun j ↦ ∑ i ∈ Iic j, x i) = x := by
  funext j
  rw [gridIncrements_apply]
  split_ifs with hj
  · have hIic : Iic j = insert j (Iic (⟨j - 1, by omega⟩ : Fin k)) := by
      ext l
      simp only [mem_Iic, mem_insert, Fin.le_def, Fin.ext_iff]
      omega
    rw [hIic, sum_insert (by simp [Fin.le_def]; omega)]
    ring
  · have hIic : Iic j = {j} := by
      ext l
      simp only [mem_Iic, mem_singleton, Fin.le_def, Fin.ext_iff]
      omega
    simp [hIic]

private theorem abs_prod_one_add_le (x : Fin k → ℝ) (t : Finset (Fin k)) :
    |∏ l ∈ t, (1 + x l)| ≤ Real.exp (∑ l, |x l|) := by
  rw [abs_prod]
  calc ∏ l ∈ t, |1 + x l| ≤ ∏ l ∈ t, Real.exp |x l| :=
        prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun l _ ↦ (abs_add_le _ _).trans <| by
          rw [abs_one, add_comm]; exact Real.add_one_le_exp _
    _ = Real.exp (∑ l ∈ t, |x l|) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑ l, |x l|) := Real.exp_le_exp.2 <|
        sum_le_sum_of_subset_of_nonneg (subset_univ t) fun _ _ _ ↦ abs_nonneg _

/-- **Lipschitz bound for the grid product integral**, uniform in the grid size:
`|∏_{i ≤ j} (1 + y i) - ∏_{i ≤ j} (1 + x i)| ≤ exp (∑ |x i|) exp (∑ |y i|) ∑_{i ≤ j} |y i - x i|`.
The constants depend only on the total variations `∑ |x i|`, `∑ |y i|` of the pure-jump
functions with jumps `x`, `y`, and the right side is the total variation of the difference on
`(0, t_j]`; this is the Duhamel estimate behind the continuity of the continuous-time
product-integral map on bounded-variation balls (Gill–Johansen 1990). -/
theorem abs_prodIntegral_sub_le (x y : Fin k → ℝ) (j : Fin k) :
    |prodIntegral y j - prodIntegral x j| ≤
      Real.exp (∑ l, |x l|) * Real.exp (∑ l, |y l|) * ∑ i ∈ Iic j, |y i - x i| := by
  rw [prodIntegral_sub_prodIntegral, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul, abs_mul]
  have h1 := abs_prod_one_add_le x (Iio i)
  have h2 := abs_prod_one_add_le y (Ioc i j)
  calc |∏ l ∈ Iio i, (1 + x l)| * |y i - x i| * |∏ l ∈ Ioc i j, (1 + y l)|
      ≤ Real.exp (∑ l, |x l|) * |y i - x i| * Real.exp (∑ l, |y l|) := by gcongr
    _ = _ := by ring

/-- The product integral on a grid is continuous. -/
theorem continuous_prodIntegral : Continuous (prodIntegral (k := k)) :=
  continuous_iff_continuousAt.2 fun x ↦ (hasFDerivAt_prodIntegral x).continuousAt

end ProductIntegral

section KaplanMeier

open KaplanMeier

variable {k : ℕ}

/-- The Kaplan–Meier estimate at the observation time `tⱼ` is the grid product integral of minus
the Nelson–Aalen increments: `Ŝ(tⱼ) = ∏_{i ≤ j} (1 - dᵢ / Yᵢ)`. -/
theorem kmSurvival_time_eq_prodIntegral (D : CensoredData k) (j : Fin k) :
    D.kmSurvival (D.time j) = prodIntegral (fun i ↦ -((D.deaths i : ℝ) / D.atRisk i)) j := by
  have hfilt : univ.filter (fun l ↦ D.time l ≤ D.time j) = Iic j := by
    ext l
    simp [D.strictMono_time.le_iff_le]
  rw [CensoredData.kmSurvival, prodIntegral, hfilt]
  exact prod_congr rfl fun i _ ↦ by simp [CensoredData.kmFactor, sub_eq_add_neg]

/-- The Nelson–Aalen estimate at the grid times is the cumulative sum of its increments. -/
theorem nelsonAalen_time_eq_sum (D : CensoredData k) (j : Fin k) :
    D.nelsonAalen (D.time j) = ∑ i ∈ Iic j, (D.deaths i : ℝ) / D.atRisk i := by
  have hfilt : univ.filter (fun l ↦ D.time l ≤ D.time j) = Iic j := by
    ext l
    simp [D.strictMono_time.le_iff_le]
  rw [CensoredData.nelsonAalen, hfilt]

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']

/-- **Kaplan–Meier limit law on a fixed grid.** For any sequence of random grouped censored
data sets `Dn n` (for instance `SurvivalConsistency.empiricalData` on the grid `0, …, k - 1`), if
the Nelson–Aalen increments satisfy `√n (ΔΛ̂ₙ - λ) ⇒ G` in `Fin k → ℝ` (sup norm), then the
Kaplan–Meier estimates at the grid times satisfy
`√n (Ŝₙ - S) ⇒ -duhamelDeriv (-λ) G`, where `S = prodIntegral (-λ)`; coordinatewise the limit is
`-∑_{i ≤ j} S(t_{i-1}) G i ∏_{i < l ≤ j} (1 - λ l)`.

The CLT is the explicit hypothesis `hCLT`. The estimates are evaluated at `(Dn n ω).time j`;
for the statement to be about a fixed grid, the data sets should share the grid times (as
`empiricalData` does). -/
theorem tendstoInDistribution_kmSurvival_grid {Dn : ℕ → Ω → CensoredData k}
    {Λ : Fin k → ℝ} {G : Ω' → Fin k → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • ((fun i ↦ ((Dn n ω).deaths i : ℝ) / (Dn n ω).atRisk i) - Λ))
      atTop G (fun _ ↦ μ) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) •
        ((fun j ↦ (Dn n ω).kmSurvival ((Dn n ω).time j)) - prodIntegral (-Λ)))
      atTop (fun ω ↦ -duhamelDeriv (-Λ) (G ω)) (fun _ ↦ μ) μ' := by
  set φ : (Fin k → ℝ) → Fin k → ℝ := fun x ↦ prodIntegral (-x) with hφ_def
  have hφd : HasFDerivAt φ ((duhamelDeriv (-Λ)).comp (-ContinuousLinearMap.id ℝ _)) Λ :=
    (hasFDerivAt_prodIntegral (-Λ)).comp Λ (hasFDerivAt_id Λ).neg
  have hr : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have key := hCLT.functional_delta_of_continuous hr
    (hφd.hasHadamardDerivWithinAt Set.univ Set.univ) (fun _ ↦ ae_of_all _ fun _ ↦ trivial)
    (ae_of_all _ fun _ ↦ trivial) (continuous_prodIntegral.comp continuous_neg)
    (ContinuousLinearMap.continuous _)
  refine key.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_)
  · congr 2
    funext j
    rw [kmSurvival_time_eq_prodIntegral]
    rfl
  · simp

/-- **Kaplan–Meier limit law on a fixed grid, from the cumulative-hazard CLT.** If the
Nelson–Aalen estimates at the grid times satisfy `√n (Λ̂ₙ - Λ) ⇒ G` in `Fin k → ℝ` (sup norm),
then `√n (Ŝₙ - S) ⇒ -duhamelDeriv (-ΔΛ) (ΔG)` with `S = prodIntegral (-ΔΛ)` and
`Δ = gridIncrements`. This is the cumulative-hazard → survival map on the grid.

The CLT is the explicit hypothesis `hCLT`. As in `tendstoInDistribution_kmSurvival_grid`, the
data sets should share the fixed grid times. -/
theorem tendstoInDistribution_kmSurvival_grid_of_nelsonAalen {Dn : ℕ → Ω → CensoredData k}
    {Λ : Fin k → ℝ} {G : Ω' → Fin k → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • ((fun j ↦ (Dn n ω).nelsonAalen ((Dn n ω).time j)) - Λ))
      atTop G (fun _ ↦ μ) μ') :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) •
        ((fun j ↦ (Dn n ω).kmSurvival ((Dn n ω).time j)) - prodIntegral (-gridIncrements Λ)))
      atTop (fun ω ↦ -duhamelDeriv (-gridIncrements Λ) (gridIncrements (G ω))) (fun _ ↦ μ) μ' := by
  refine tendstoInDistribution_kmSurvival_grid (G := fun ω ↦ gridIncrements (G ω)) ?_
  refine (hCLT.continuous_comp gridIncrements.continuous).congr
    (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ rfl)
  simp_rw [Function.comp_apply, nelsonAalen_time_eq_sum, map_smul, map_sub,
    gridIncrements_cumsum]

/-- **Functional delta theorem in `ℓ^∞([0, τ])`**, the shape of the continuous-time
Kaplan–Meier statement. Topology: the uniform (sup-norm) topology of `ℓ^∞([0, τ])`, tangent set
the continuous functions `C[0, τ]`, scale `r n = √n`. If `√n (Λ̂ₙ - Λ) ⇒ G` with continuous `G`
(`hCLT`, `hG`) and `prodInt` is Hadamard differentiable at `Λ` tangentially to `C[0, τ]` with
derivative `prodInt'` (`hHad`), then `√n (prodInt Λ̂ₙ - prodInt Λ) ⇒ prodInt' G`.

`Λhat`, `prodInt`, `prodInt'` and `dom` are arbitrary: nothing ties them to the Nelson–Aalen
estimator or a product integral, and the Hadamard differentiability of the continuous-time
product-integral map (van der Vaart §20.3) is **not proved here**. Moreover the
`AEMeasurable` fields of `hCLT` fail for the continuous-time Nelson–Aalen process on the
canonical space of the observations whenever the law of the uncensored observation times in
`[0, τ]` has a non-atomic part (the `n = 1` counterexample in the module docstring), so this
theorem does not apply to continuous-time Kaplan–Meier in that case; it applies when the
processes stay Borel measurable, e.g. in a separable subspace. -/
theorem tendstoInDistribution_lInfty_of_hadamard {τ : ℝ}
    [MeasurableSpace (lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞)]
    [BorelSpace (lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞)]
    {Λhat : ℕ → Ω → lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞}
    {Λ : lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞}
    {G : Ω' → lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞}
    {prodInt prodInt' :
      lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞ → lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞}
    {dom : Set (lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞)}
    (hCLT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (Λhat n ω - Λ)) atTop G
      (fun _ ↦ μ) μ')
    (hG : ∀ᵐ ω ∂μ', Continuous fun t ↦ G ω t)
    (hHad : HasHadamardDerivWithinAt prodInt prodInt' dom {h | Continuous fun t ↦ h t} Λ)
    (hdom : ∀ n, ∀ᵐ ω ∂μ, Λhat n ω ∈ dom)
    (hmeas : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) • (prodInt (Λhat n ω) - prodInt Λ)) μ)
    (hmeas' : AEMeasurable (fun ω ↦ prodInt' (G ω)) μ') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (prodInt (Λhat n ω) - prodInt Λ)) atTop
      (fun ω ↦ prodInt' (G ω)) (fun _ ↦ μ) μ' :=
  hCLT.functional_delta (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) hHad hdom hG
    hmeas hmeas'

end KaplanMeier

end MathlibExt.Probability.Statistics.FunctionalDelta
