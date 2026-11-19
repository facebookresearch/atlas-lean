/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMonotoneClass
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Monotone-class extensions of the Markov property of the Wright–Fisher diffusion with selection

`Diffusion.NeutralMonotoneClass` extends the strong Markov property of the neutral Wright–Fisher
diffusion from continuous one-time test functions to bounded measurable, multi-time and
whole-path functionals. This file does the same for the Wright–Fisher diffusion with genic
selection: a continuous `[0, 1]`-valued process `X` solving the selection martingale problem
`KimuraFixationProcess.IsWrightFisherSolution σ` (generator
`L_σ f = x (1 - x) / 2 · f'' + σ x (1 - x) · f'`) that is Markov, with respect to its filtration,
for a family of transition kernels `κ t` on `[0, 1]`.

The extensions are proved for an arbitrary family of Markov kernels `κ` satisfying the
Chapman–Kolmogorov equations; the Feller property (`x ↦ ∫ g dκ_t(x)` continuous for continuous
`g`) is used only at stopping times, through the dyadic approximation of the stopping time.

## Main results

* `IsKernelMarkovFamily`: a process `Y` adapted to a filtration and Markov for a kernel family
  `κ` on continuous test functions, in integrated form; its one-time, joint, multi-time and path
  laws (`map_restrict_eq_comp`, `map_restrict_finite_eq_comp`, `map_restrict_path_eq_comp`).
* `measurable_pathMeasure`, `pathKernel`: the canonical path measures of a Chapman–Kolmogorov
  family form a Markov kernel.
* `setIntegral_stoppedValue_add_eq_integral`: the strong Markov property for continuous `g`, for
  a Feller kernel family.
* `IsSelectionMarkov`: `X` solves the selection martingale problem and is Markov for `κ`.
* `IsSelectionMarkov.condExp_indicator_comp_stoppedValue_add`,
  `.condExp_indicator_finite_stoppedValue_add`, `.condExp_indicator_path_stoppedValue_add`: the
  strong Markov property for bounded measurable `g`, multi-time and whole-path functionals.
* `IsSelectionMarkov.condExp_path_add`: the simple Markov property at a deterministic time for
  whole-path functionals, with no Feller hypothesis.
* `isSelectionMarkov_zero_modifiedProcess`, `isFellerFamily_neutralKernel`: at `σ = 0` the
  hypotheses hold for the neutral realization with `neutralKernel`.

## Scope

The transition kernel of the selection diffusion is a hypothesis. Main has the selection
diffusion only as a solution of its martingale problem; neither well-posedness of that problem
for `σ ≠ 0` nor a selection semigroup or transition kernel (via Girsanov's theorem, or via the
Feller semigroup of `L_σ`) is formalized. The martingale-problem field identifies the process
and supplies path continuity and adaptedness; the Markov field, which ties `X` to `κ`, is what
the monotone-class arguments use. At `σ = 0` both are discharged for the neutral realization.
The only `σ ≠ 0` instance available is degenerate: the process frozen at the boundary state
`0`, with identity kernels (`MathlibExtTest`), where nothing ties `κ` to the selection dynamics
in the interior of `[0, 1]`.

## Method

As in `Diffusion.NeutralMonotoneClass`, with `neutralKernel` replaced by `κ`. On continuous test
functions the Markov property gives the kernel form of the one-step law on every event of the
past; finite measures on `[0, 1]` agreeing on continuous functions are equal. Joint laws follow
by uniqueness on rectangles, multi-time laws by induction on the number of times
(`MarkovSemigroupProjective.map_init_last_finiteChainLaw_snoc`), path laws by uniqueness on
measurable cylinders. At a stopping time `τ`, the one-step identity is proved by the dyadic
approximation `τₙ = ⌈2ⁿ τ⌉ / 2ⁿ` of `NeutralStrongMarkov`, using only continuity of `X` and of
`x ↦ ∫ g dκ_t(x)`.

## Source receipt

* Reused: `condExp_indicator_ae_eq_of_map_restrict`, `cylinder_eq_preimage`,
  `isStoppingTime_add_const`, `postFiltration` (`Diffusion.NeutralMonotoneClass`),
  `finiteChainKernel`, `map_init_last_finiteChainLaw_snoc`, `pathMeasure`,
  `map_ordered_pathMeasure` (`MathlibExt.Probability.MarkovSemigroupProjective`),
  `IsWrightFisherSolution` (`Diffusion.KimuraFixationProcess`),
  `isWrightFisherSolution_zero_modifiedProcess`, `condExp_modifiedProcess_eq_wfSemigroup`
  (`NeutralMartingaleProblem.Markov`).
* Copied and generalized from `neutralKernel` to a kernel family `κ`, about 475 lines:
  - from `Diffusion.NeutralMonotoneClass`, the public `rawMeasure_cylinder`,
    `measurable_rawMeasure`, `wfPathKernel` (here `pathMeasure_cylinder`,
    `measurable_pathMeasure`, `pathKernel`) and the public
    `IsNeutralMarkovFamily.map_restrict_eq_comp`, `.lintegral_step`,
    `.map_restrict_prod_eq_compProd`, `.map_restrict_finite_eq_comp`,
    `.map_restrict_path_eq_comp` (here on `IsKernelMarkovFamily`), copied because they are fixed
    to `neutralKernel`, together with their private helpers;
  - from `Diffusion.NeutralStrongMarkov`, the private dyadic approximation of stopping times,
    with `wfSemigroup t g` replaced by an arbitrary continuous `P t g`.
  The post-`τ` Markov family and the three strong Markov theorems follow the proofs of
  `Diffusion.NeutralMonotoneClass` step for step. Re-deriving the neutral API as the
  `κ = neutralKernel` case of this file is a filed follow-up.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), ch. 4, §1 (Markov property for path functionals by monotone class), ch. 4, Thm. 2.7
  (Feller processes are strong Markov) and ch. 10 (Wright–Fisher diffusions with selection).
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999),
  ch. III, §1 and §3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal unitInterval

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.SelectionMonotoneClass

open MathlibExt.Probability.MarkovSemigroupProjective
open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
  (SamplePath neutralKernel neutralKernel_add rawMeasure modifiedProcess)
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
  (naturalFiltration isWrightFisherSolution_zero_modifiedProcess
    condExp_modifiedProcess_eq_wfSemigroup)
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMonotoneClass
  (cylinder_eq_preimage condExp_indicator_ae_eq_of_map_restrict isStoppingTime_add_const
    postFiltration measurableSpace_le_postFiltration_zero)

noncomputable section

/-- States are read in `[0, 1]` through `Set.projIcc`. -/
local notation "toI" => projIcc (0 : ℝ) 1 zero_le_one

/-- A family of kernels on `[0, 1]` is **Feller** if it maps continuous functions to continuous
functions: `x ↦ ∫ g dκ_t(x)` is continuous for every `t` and every continuous `g`. -/
def IsFellerFamily (κ : ℝ≥0 → Kernel I I) : Prop :=
  ∀ (t : ℝ≥0) (g : C(I, ℝ)), Continuous fun x => ∫ y, g y ∂κ t x

variable {κ : ℝ≥0 → Kernel I I} [∀ t, IsMarkovKernel (κ t)]

/-! ### The path-measure kernel of a Chapman–Kolmogorov family -/

section PathKernel

variable (hκ : ∀ s t, κ (s + t) = κ t ∘ₖ κ s)

/-- The canonical path measure of a measurable cylinder is given by the ordered
finite-dimensional law. -/
theorem pathMeasure_cylinder (x : I) (J : Finset ℝ≥0) {S : Set (J → I)}
    (hS : MeasurableSet S) :
    pathMeasure κ hκ x (cylinder J S) =
      finiteChainKernel κ 0 (J.orderEmbOfFin rfl) x
        ((orderMeasurableEquiv J : (Fin J.card → I) ≃ᵐ (J → I)) ⁻¹' S) := by
  have hproj : Measurable fun ω : SamplePath => fun i => ω (J.orderEmbOfFin rfl i) :=
    Measurable.of_eval fun i => measurable_pi_apply (J.orderEmbOfFin rfl i)
  rw [cylinder_eq_preimage, ← Measure.map_apply hproj ((orderMeasurableEquiv J).measurable hS)]
  exact congrArg (fun ν : Measure (Fin J.card → I) => ν _) (map_ordered_pathMeasure κ hκ x J)

/-- **The path measure is measurable in the initial state.** -/
theorem measurable_pathMeasure : Measurable fun x => pathMeasure κ hκ x := by
  refine Measurable.measure_of_isPiSystem generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_ (by simp)
  intro C hC
  obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders C).1 hC
  simp_rw [pathMeasure_cylinder hκ _ J hS]
  exact Kernel.measurable_coe _ ((orderMeasurableEquiv J).measurable hS)

/-- The canonical path measures of a Chapman–Kolmogorov family, as a Markov kernel from the
initial state to sample paths. -/
def pathKernel : Kernel I SamplePath :=
  ⟨fun x => pathMeasure κ hκ x, measurable_pathMeasure hκ⟩

@[simp]
theorem pathKernel_apply (x : I) : pathKernel hκ x = pathMeasure κ hκ x :=
  rfl

instance isMarkovKernel_pathKernel : IsMarkovKernel (pathKernel hκ) :=
  ⟨fun x => by rw [pathKernel_apply]; infer_instance⟩

end PathKernel

/-! ### Integrals against a kernel pushed forward along a map -/

private theorem lintegral_comp_map {Ω : Type*} {mΩ : MeasurableSpace Ω} {β : Type*}
    [MeasurableSpace β] (K : Kernel I β) {ν : Measure Ω} {W : Ω → I} (hW : Measurable W)
    {F : β → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y, F y ∂(K ∘ₘ ν.map W) = ∫⁻ ω, ∫⁻ y, F y ∂K (W ω) ∂ν := by
  rw [Measure.lintegral_bind K.aemeasurable hF.aemeasurable,
    lintegral_map hF.lintegral_kernel hW]

private theorem integral_comp_map {Ω : Type*} {mΩ : MeasurableSpace Ω} {β : Type*}
    [MeasurableSpace β] (K : Kernel I β) [IsMarkovKernel K] {ν : Measure Ω} [IsFiniteMeasure ν]
    {W : Ω → I} (hW : Measurable W) {F : β → ℝ} (hF : Measurable F) {C : ℝ}
    (hFC : ∀ y, ‖F y‖ ≤ C) :
    ∫ y, F y ∂(K ∘ₘ ν.map W) = ∫ ω, ∫ y, F y ∂K (W ω) ∂ν := by
  have hint : Integrable F ((K ∘ₖ Kernel.const Unit (ν.map W)) ()) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Eventually.of_forall hFC)
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp hint]
  simp only [Kernel.const_apply]
  exact integral_map hW.aemeasurable
    ((hF.stronglyMeasurable.comp_measurable measurable_snd).integral_kernel_prod_right'
      (κ := K)).aestronglyMeasurable

/-! ### Markov families for a kernel family -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `Y` is a **Markov family for the kernel family `κ`** with respect to the filtration `𝒢`
under `μ`: each `Y u` is `𝒢 u`-measurable, and for `u ≤ v`, every `A ∈ 𝒢 u` and every
continuous `g` on `[0, 1]`, `∫_A g (Y v) dμ = ∫_A ∫ g dκ_{v - u}(Y u) dμ`. -/
structure IsKernelMarkovFamily (κ : ℝ≥0 → Kernel I I) (μ : Measure Ω) (𝒢 : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 → Ω → I) : Prop where
  measurable : ∀ u, Measurable[𝒢 u] (Y u)
  setIntegral_eq : ∀ u v, u ≤ v → ∀ A, MeasurableSet[𝒢 u] A → ∀ g : C(I, ℝ),
    ∫ ω in A, g (Y v ω) ∂μ = ∫ ω in A, ∫ y, g y ∂κ (v - u) (Y u ω) ∂μ

namespace IsKernelMarkovFamily

variable {𝒢 : Filtration ℝ≥0 mΩ} {Y : ℝ≥0 → Ω → I}

omit [∀ t, IsMarkovKernel (κ t)] in
theorem measurable' (hY : IsKernelMarkovFamily κ μ 𝒢 Y) (u : ℝ≥0) : Measurable (Y u) :=
  (hY.measurable u).mono (𝒢.le u) le_rfl

/-- **Kernel form of the Markov property.** For `u ≤ v` and `A ∈ 𝒢 u`, the law of `Y v` on `A`
is the law of `Y u` on `A` pushed through `κ (v - u)`. -/
theorem map_restrict_eq_comp [IsFiniteMeasure μ] (hY : IsKernelMarkovFamily κ μ 𝒢 Y)
    {u v : ℝ≥0} (huv : u ≤ v) {A : Set Ω} (hA : MeasurableSet[𝒢 u] A) :
    (μ.restrict A).map (Y v) = κ (v - u) ∘ₘ (μ.restrict A).map (Y u) := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map (hY.measurable' v).aemeasurable f.continuous.aestronglyMeasurable,
    integral_comp_map _ (hY.measurable' u) f.continuous.measurable (C := ‖f‖)
      (f.norm_coe_le_norm ·)]
  exact hY.setIntegral_eq u v huv A hA f.toContinuousMap

/-- The kernel form of the Markov property for nonnegative measurable test functions. -/
theorem lintegral_step [IsFiniteMeasure μ] (hY : IsKernelMarkovFamily κ μ 𝒢 Y) {u v : ℝ≥0}
    (huv : u ≤ v) {A : Set Ω} (hA : MeasurableSet[𝒢 u] A) {f : I → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in A, f (Y v ω) ∂μ = ∫⁻ ω in A, ∫⁻ y, f y ∂κ (v - u) (Y u ω) ∂μ := by
  rw [← lintegral_map hf (hY.measurable' v), hY.map_restrict_eq_comp huv hA,
    lintegral_comp_map _ (hY.measurable' u) hf]

/-- **Joint law with the past.** For `u ≤ v`, a `𝒢 u`-measurable `Z` with `Y u = φ ∘ Z` and
`A ∈ 𝒢 u`, the joint law of `(Z, Y v)` on `A` is the law of `Z` on `A` composed with one kernel
step from `φ`. -/
theorem map_restrict_prod_eq_compProd [IsFiniteMeasure μ] (hY : IsKernelMarkovFamily κ μ 𝒢 Y)
    {β : Type*} [MeasurableSpace β] {u v : ℝ≥0} (huv : u ≤ v) {Z : Ω → β}
    (hZ : Measurable[𝒢 u] Z) {φ : β → I} (hφ : Measurable φ) (hZφ : ∀ ω, φ (Z ω) = Y u ω)
    {A : Set Ω} (hA : MeasurableSet[𝒢 u] A) :
    (μ.restrict A).map (fun ω => (Z ω, Y v ω)) =
      (μ.restrict A).map Z ⊗ₘ (κ (v - u)).comap φ hφ := by
  have hZ' : Measurable Z := hZ.mono (𝒢.le u) le_rfl
  have hA' : MeasurableSet A := 𝒢.le u _ hA
  have hrect : ∀ S, MeasurableSet S → ∀ B, MeasurableSet B →
      (μ.restrict A).map (fun ω => (Z ω, Y v ω)) (S ×ˢ B) =
        ((μ.restrict A).map Z ⊗ₘ (κ (v - u)).comap φ hφ) (S ×ˢ B) := by
    intro S hS B hB
    have hA₂ : MeasurableSet[𝒢 u] (Z ⁻¹' S ∩ A) := (hZ hS).inter hA
    have h := congrArg (fun ν : Measure I => ν B) (hY.map_restrict_eq_comp huv hA₂)
    rw [Measure.map_apply (hY.measurable' v) hB, Measure.bind_apply hB
      (Kernel.aemeasurable _), lintegral_map (Kernel.measurable_coe _ hB)
      (hY.measurable' u)] at h
    rw [Measure.map_apply (hZ'.prodMk (hY.measurable' v)) (hS.prod hB),
      Measure.compProd_apply_prod hS hB,
      setLIntegral_map hS (Kernel.measurable_coe _ hB) hZ', mk_preimage_prod,
      Measure.restrict_apply ((hZ' hS).inter (hY.measurable' v hB)),
      Measure.restrict_restrict (hZ' hS)]
    simp only [Kernel.comap_apply, hZφ]
    rw [← h, Measure.restrict_apply (hY.measurable' v hB)]
    congr 1
    ext ω
    simp only [mem_inter_iff, mem_preimage]
    tauto
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨S, hS, B, hB, rfl⟩
    exact hrect S hS B hB
  · rw [← univ_prod_univ]
    exact hrect _ MeasurableSet.univ _ MeasurableSet.univ

private theorem measurable_snoc {n : ℕ} :
    Measurable fun p : (Fin (n + 1) → I) × I => (Fin.snoc p.1 p.2 : Fin (n + 2) → I) := by
  refine Measurable.of_eval fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

/-- The one-time chain law is one kernel step. This is the `n = 0` case of the private
`MarkovSemigroupProjective.lintegral_finiteChainLaw_cons`; delete it once that lemma is
public. -/
private theorem lintegral_finiteChainKernel_one (s : ℝ≥0) (t : Fin 1 → ℝ≥0) (x : I)
    {F : (Fin 1 → I) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂finiteChainKernel κ s t x = ∫⁻ y, F (fun _ => y) ∂κ (t 0 - s) x := by
  rw [finiteChainKernel, Kernel.map_apply _ (MeasurableEquiv.measurable _),
    lintegral_map hF (MeasurableEquiv.measurable _),
    Kernel.lintegral_compProd _ _ _
      (f := fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 1 => I) 0).symm p))
      (hF.comp (MeasurableEquiv.measurable _))]
  refine lintegral_congr fun y => ?_
  rw [Kernel.prodMkLeft_apply, finiteChainKernel, Kernel.deterministic_apply,
    lintegral_dirac]
  congr 1
  funext i
  fin_cases i
  rfl

/-- The multi-time law for at least one time, in integrated form. -/
private theorem lintegral_finite_succ [IsFiniteMeasure μ] (hY : IsKernelMarkovFamily κ μ 𝒢 Y) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ s, (∀ i, s ≤ t i) →
      ∀ A, MeasurableSet[𝒢 s] A → ∀ F : (Fin (n + 1) → I) → ℝ≥0∞, Measurable F →
        ∫⁻ ω in A, F (fun i => Y (t i) ω) ∂μ =
          ∫⁻ ω in A, ∫⁻ z, F z ∂finiteChainKernel κ s t (Y s ω) ∂μ
  | 0, t, _, s, hs, A, hA, F, hF => by
    have hfun : ∀ ω, (fun i => Y (t i) ω) = fun _ => Y (t 0) ω := fun ω => by
      funext i
      fin_cases i
      rfl
    simp_rw [hfun, lintegral_finiteChainKernel_one _ _ _ hF]
    exact hY.lintegral_step (hs 0) hA (hF.comp (Measurable.of_eval fun _ => measurable_id))
  | n + 1, t, ht, s, hs, A, hA, F, hF => by
    set τ : Fin (n + 1) → ℝ≥0 := Fin.init t with hτdef
    set b : ℝ≥0 := t (Fin.last (n + 1)) with hbdef
    set u : ℝ≥0 := τ (Fin.last n) with hudef
    have hτm : Monotone τ := ht.comp Fin.strictMono_castSucc.monotone
    have hub : u ≤ b := ht (Fin.le_last _)
    have hsu : s ≤ u := hs _
    have hZ : Measurable[𝒢 u] fun ω (i : Fin (n + 1)) => Y (τ i) ω := by
      let _ := 𝒢 u
      exact Measurable.of_eval fun i =>
        (hY.measurable (τ i)).mono (𝒢.mono (hτm (Fin.le_last i))) le_rfl
    have hZ' : Measurable fun ω (i : Fin (n + 1)) => Y (τ i) ω :=
      hZ.mono (𝒢.le u) le_rfl
    let G : (Fin (n + 1) → I) × I → ℝ≥0∞ := fun p => F (Fin.snoc p.1 p.2)
    have hG : Measurable G := hF.comp measurable_snoc
    let H : (Fin (n + 1) → I) → ℝ≥0∞ := fun w =>
      ∫⁻ y, G (w, y) ∂κ (b - u) (w (Fin.last n))
    have hH : Measurable H :=
      Measurable.lintegral_kernel_prod_right'
        (κ := (κ (b - u)).comap (fun w : Fin (n + 1) → I => w (Fin.last n))
          (measurable_pi_apply _)) hG
    have hsnoc : ∀ z : Fin (n + 2) → I, F z = G (Fin.init z, z (Fin.last (n + 1))) := fun z => by
      simp only [G, Fin.snoc_init_self]
    have hsplit : ∀ ω, F (fun i => Y (t i) ω) = G ((fun i => Y (τ i) ω), Y b ω) := fun ω => by
      rw [hsnoc]
      rfl
    have hchain : ∀ x, ∫⁻ z, F z ∂finiteChainKernel κ s t x =
        ∫⁻ w, H w ∂finiteChainKernel κ s τ x := fun x => by
      have ht' : t = Fin.snoc τ b := (Fin.snoc_init_self t).symm
      have hmap := map_init_last_finiteChainLaw_snoc κ x s τ b
      simp_rw [hsnoc]
      have hinit : Measurable fun z : Fin (n + 2) → I => (Fin.init z, z (Fin.last (n + 1))) :=
        (Measurable.of_eval fun i => measurable_pi_apply (Fin.castSucc i)).prodMk
          (measurable_pi_apply _)
      rw [ht', ← lintegral_map hG hinit]
      unfold finiteChainLaw at hmap
      rw [hmap, Measure.lintegral_compProd hG]
      rfl
    simp_rw [hsplit, hchain]
    rw [← lintegral_map hG (hZ'.prodMk (hY.measurable' b)),
      hY.map_restrict_prod_eq_compProd hub hZ (measurable_pi_apply (Fin.last n))
        (fun _ => rfl) (𝒢.mono hsu _ hA),
      Measure.lintegral_compProd hG]
    exact (lintegral_map hH hZ').trans
      (lintegral_finite_succ hY n τ hτm s (fun i => hs _) A hA H hH)

/-- **Multi-time law of a Markov family.** For times `t₁ ≤ … ≤ tₙ` after `s` and `A ∈ 𝒢 s`, the
joint law of `(Y t₁, …, Y tₙ)` on `A` is the law of `Y s` on `A` pushed through the ordered
finite-dimensional kernel `finiteChainKernel κ s t`. -/
theorem map_restrict_finite_eq_comp [IsFiniteMeasure μ] (hY : IsKernelMarkovFamily κ μ 𝒢 Y)
    {n : ℕ} {t : Fin n → ℝ≥0} (ht : Monotone t) {s : ℝ≥0} (hs : ∀ i, s ≤ t i) {A : Set Ω}
    (hA : MeasurableSet[𝒢 s] A) :
    (μ.restrict A).map (fun ω i => Y (t i) ω) =
      finiteChainKernel κ s t ∘ₘ (μ.restrict A).map (Y s) := by
  have hV : Measurable fun ω i => Y (t i) ω :=
    Measurable.of_eval fun i => hY.measurable' (t i)
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF hV, lintegral_comp_map _ (hY.measurable' s) hF]
  cases n with
  | zero =>
    refine lintegral_congr fun ω => ?_
    rw [finiteChainKernel, Kernel.deterministic_apply, lintegral_dirac' _ hF]
    exact congrArg F (Subsingleton.elim _ _)
  | succ n => exact lintegral_finite_succ hY n t ht s hs A hA F hF

/-- **Path law of a Markov family.** For `A ∈ 𝒢 0`, the law of the path `(Y u)_{u ≥ 0}` on `A`
is the law of `Y 0` on `A` pushed through the path-measure kernel `pathKernel hκ`. -/
theorem map_restrict_path_eq_comp [IsFiniteMeasure μ] (hκ : ∀ s t, κ (s + t) = κ t ∘ₖ κ s)
    (hY : IsKernelMarkovFamily κ μ 𝒢 Y) {A : Set Ω} (hA : MeasurableSet[𝒢 0] A) :
    (μ.restrict A).map (fun ω u => Y u ω) = pathKernel hκ ∘ₘ (μ.restrict A).map (Y 0) := by
  have hpath : Measurable fun ω u => Y u ω := Measurable.of_eval hY.measurable'
  have hcyl : ∀ J : Finset ℝ≥0, ∀ S : Set (J → I), MeasurableSet S →
      (μ.restrict A).map (fun ω u => Y u ω) (cylinder J S) =
        (pathKernel hκ ∘ₘ (μ.restrict A).map (Y 0)) (cylinder J S) := by
    intro J S hS
    have hS' : MeasurableSet
        ((orderMeasurableEquiv J : (Fin J.card → I) ≃ᵐ (J → I)) ⁻¹' S) :=
      (orderMeasurableEquiv J).measurable hS
    have h := congrArg (fun ν : Measure (Fin J.card → I) =>
        ν ((orderMeasurableEquiv J : (Fin J.card → I) ≃ᵐ (J → I)) ⁻¹' S))
      (hY.map_restrict_finite_eq_comp (t := ⇑(J.orderEmbOfFin rfl)) (J.orderEmbOfFin rfl).monotone
        (fun _ => zero_le) hA)
    rw [Measure.map_apply (Measurable.of_eval fun i => hY.measurable' _) hS',
      Measure.bind_apply hS' (Kernel.aemeasurable _)] at h
    rw [Measure.map_apply hpath (hS.cylinder J),
      Measure.bind_apply (hS.cylinder J) (Kernel.aemeasurable _)]
    simp_rw [pathKernel_apply, pathMeasure_cylinder hκ _ J hS]
    rw [← h, cylinder_eq_preimage]
    rfl
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders C).1 hC
    exact hcyl J S hS
  · have h := hcyl ∅ univ MeasurableSet.univ
    rwa [cylinder_univ] at h

end IsKernelMarkovFamily

/-! ### Dyadic approximation of a stopping time

Adapted from the private helpers of `Diffusion.NeutralStrongMarkov`, whose argument does not use
any property of the semigroup beyond continuity of `P_t g`. -/

/-- The dyadic upper approximation `⌈2ⁿ r⌉ / 2ⁿ` of a time `r`. -/
private def dyadicUp (n : ℕ) (r : ℝ≥0) : ℝ≥0 :=
  (⌈(2 : ℝ≥0) ^ n * r⌉₊ : ℝ≥0) / 2 ^ n

private theorem le_dyadicUp (n : ℕ) (r : ℝ≥0) : r ≤ dyadicUp n r := by
  unfold dyadicUp
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact Nat.le_ceil _

private theorem dyadicUp_le (n : ℕ) (r : ℝ≥0) : dyadicUp n r ≤ r + (1 / 2) ^ n := by
  unfold dyadicUp
  rw [div_le_iff₀ (by positivity), add_mul, div_pow, one_pow,
    div_mul_cancel₀ _ (by positivity), mul_comm r]
  exact (Nat.ceil_lt_add_one (by positivity)).le

private theorem tendsto_dyadicUp (r : ℝ≥0) :
    Tendsto (fun n => dyadicUp n r) atTop (𝓝 r) := by
  have h : Tendsto (fun n : ℕ => r + (1 / 2 : ℝ≥0) ^ n) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 / 2) (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (le_dyadicUp · r)
    (dyadicUp_le · r)

private theorem measurable_dyadicUp (n : ℕ) : Measurable (dyadicUp n) := by
  unfold dyadicUp
  exact (measurable_from_nat.comp (Nat.measurable_ceil.comp
    (measurable_const.mul measurable_id))).div_const _

@[simp]
private theorem untopA_coe (r : ℝ≥0) : (r : WithTop ℝ≥0).untopA = r :=
  WithTop.untopD_coe _ r

/-- The dyadic grid point `k / 2ⁿ`. -/
private def grid (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

private theorem grid_mono (n : ℕ) {j k : ℕ} (h : j ≤ k) : grid n j ≤ grid n k := by
  unfold grid
  gcongr

private theorem le_grid_iff (n m : ℕ) (a : WithTop ℝ≥0) :
    a ≤ (grid n m : WithTop ℝ≥0) ↔ a ≠ ⊤ ∧ ⌈(2 : ℝ≥0) ^ n * a.untopA⌉₊ ≤ m := by
  induction a with
  | top => simpa using WithTop.not_top_le_coe (grid n m)
  | coe r =>
    simp only [WithTop.coe_le_coe, ne_eq, WithTop.coe_ne_top, not_false_eq_true,
      untopA_coe, true_and, Nat.ceil_le, grid]
    rw [le_div_iff₀ (by positivity), mul_comm]

variable {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

private theorem measurable_uncurry (hcont : ∀ ω, Continuous fun t => X t ω)
    (hadapt : StronglyAdapted ℱ X) : Measurable (Function.uncurry X) :=
  measurable_uncurry_of_continuous_of_measurable hcont fun t =>
    ((hadapt t).mono (ℱ.le t)).measurable

private theorem measurable_comp_time (hX : Measurable (Function.uncurry X)) {ρ : Ω → ℝ≥0}
    (hρ : Measurable ρ) (g : C(I, ℝ)) : Measurable fun ω => g (toI (X (ρ ω) ω)) :=
  (g.continuous.comp continuous_projIcc).measurable.comp (hX.comp (hρ.prodMk measurable_id))

private theorem integrable_comp [IsFiniteMeasure μ] {F : Ω → ℝ} (hF : Measurable F)
    (g : C(I, ℝ)) : Integrable (fun ω => g (toI (F ω))) μ :=
  Integrable.of_bound
    ((g.continuous.comp continuous_projIcc).measurable.comp hF).aestronglyMeasurable
    ‖g‖ (Eventually.of_forall fun _ => g.norm_coe_le_norm _)

private theorem integrable_comp_time [IsFiniteMeasure μ] (hX : Measurable (Function.uncurry X))
    {ρ : Ω → ℝ≥0} (hρ : Measurable ρ) (g : C(I, ℝ)) :
    Integrable (fun ω => g (toI (X (ρ ω) ω))) μ :=
  integrable_comp (hX.comp (hρ.prodMk measurable_id)) g

private theorem stoppedValue_add_of_ne_top {ω : Ω} (hω : τ ω ≠ ⊤) (t : ℝ≥0) :
    stoppedValue X (fun ω => τ ω + t) ω = X ((τ ω).untopA + t) ω := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hω
  simp only [stoppedValue, ← hr, ← WithTop.coe_add, untopA_coe]

/-- The event `{τ < ∞, ⌈2ⁿ τ⌉ = k}`. -/
private def dyadicSet (τ : Ω → WithTop ℝ≥0) (n k : ℕ) : Set Ω :=
  {ω | τ ω ≠ ⊤ ∧ ⌈(2 : ℝ≥0) ^ n * (τ ω).untopA⌉₊ = k}

private theorem measurableSet_inter_dyadicSet (hτ : IsStoppingTime ℱ τ) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) (n k : ℕ) :
    MeasurableSet[ℱ (grid n k)] (A ∩ dyadicSet τ n k) := by
  cases k with
  | zero =>
    have h : A ∩ dyadicSet τ n 0 = A ∩ {ω | τ ω ≤ grid n 0} := by
      ext ω
      simp only [dyadicSet, mem_inter_iff, mem_ofPred_eq, le_grid_iff, Nat.le_zero]
    rw [h]
    exact hA.2 _
  | succ j =>
    have h : A ∩ dyadicSet τ n (j + 1) =
        (A ∩ {ω | τ ω ≤ grid n (j + 1)}) ∩ {ω | τ ω ≤ grid n j}ᶜ := by
      ext ω
      simp only [dyadicSet, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, le_grid_iff]
      by_cases hω : τ ω = ⊤
      · simp [hω]
      · simp only [ne_eq, hω, not_false_eq_true, true_and]
        constructor
        · rintro ⟨ha, hk⟩
          exact ⟨⟨ha, hk.le⟩, by omega⟩
        · rintro ⟨⟨ha, hk⟩, hj⟩
          exact ⟨ha, by omega⟩
    rw [h]
    exact (hA.2 _).inter ((ℱ.mono (grid_mono n j.le_succ) _ (hτ _)).compl)

private theorem dyadicUp_of_mem_dyadicSet {n k : ℕ} {ω : Ω} (hω : ω ∈ dyadicSet τ n k) :
    dyadicUp n (τ ω).untopA = grid n k := by
  simp only [dyadicUp, grid, hω.2]

/-- The integrated identity at a dyadic approximation of `τ`, for an arbitrary family of
operators `P` on continuous functions for which `X` is Markov. -/
private theorem setIntegral_dyadic [IsFiniteMeasure μ] {P : ℝ≥0 → C(I, ℝ) → C(I, ℝ)}
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (toI (X t ω)) | ℱ s] =ᵐ[μ] fun ω => P (t - s) g (toI (X s ω)))
    (hτ : IsStoppingTime ℱ τ) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (t : ℝ≥0) (g : C(I, ℝ)) (n : ℕ) :
    ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, g (toI (X (dyadicUp n (τ ω).untopA + t) ω)) ∂μ =
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, P t g (toI (X (dyadicUp n (τ ω).untopA) ω)) ∂μ := by
  have hX := measurable_uncurry hcont hadapt
  have hρ : Measurable fun ω => dyadicUp n (τ ω).untopA :=
    (measurable_dyadicUp n).comp hτ.measurable'.untopA
  have hS : ∀ k, MeasurableSet (A ∩ dyadicSet τ n k) := fun k =>
    ℱ.le _ _ (measurableSet_inter_dyadicSet hτ hA n k)
  have hU : A ∩ {ω | τ ω ≠ ⊤} = ⋃ k, A ∩ dyadicSet τ n k := by
    ext ω
    simp [dyadicSet]
  have hD : Pairwise (Function.onFun Disjoint fun k => A ∩ dyadicSet τ n k) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, -, hi⟩ ⟨-, -, hj⟩
    exact hij (hi.symm.trans hj)
  rw [hU, integral_iUnion hS hD (integrable_comp_time hX (hρ.add_const t) g).integrableOn,
    integral_iUnion hS hD (integrable_comp_time hX hρ (P t g)).integrableOn]
  refine tsum_congr fun k => ?_
  have hm := hmarkov (grid n k) (grid n k + t) le_self_add g
  have hgap : grid n k + t - grid n k = t := add_tsub_cancel_left _ _
  calc ∫ ω in A ∩ dyadicSet τ n k, g (toI (X (dyadicUp n (τ ω).untopA + t) ω)) ∂μ
      = ∫ ω in A ∩ dyadicSet τ n k, g (toI (X (grid n k + t) ω)) ∂μ :=
        setIntegral_congr_fun (hS k) fun ω hω => by
          simp only [dyadicUp_of_mem_dyadicSet hω.2]
    _ = ∫ ω in A ∩ dyadicSet τ n k,
          (μ[fun ω => g (toI (X (grid n k + t) ω)) | ℱ (grid n k)]) ω ∂μ :=
        (setIntegral_condExp (ℱ.le _)
          (integrable_comp ((hadapt _).mono (ℱ.le _)).measurable g)
          (measurableSet_inter_dyadicSet hτ hA n k)).symm
    _ = ∫ ω in A ∩ dyadicSet τ n k, P t g (toI (X (grid n k) ω)) ∂μ :=
        setIntegral_congr_ae (hS k) (hm.mono fun ω hω _ => by rw [hω, hgap])
    _ = ∫ ω in A ∩ dyadicSet τ n k, P t g (toI (X (dyadicUp n (τ ω).untopA) ω)) ∂μ :=
        (setIntegral_congr_fun (hS k) fun ω hω => by
          simp only [dyadicUp_of_mem_dyadicSet hω.2]).symm

/-- The integrated strong Markov identity for an arbitrary operator family `P`. -/
private theorem setIntegral_stoppedValue_add_eq_op [IsFiniteMeasure μ]
    {P : ℝ≥0 → C(I, ℝ) → C(I, ℝ)}
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (toI (X t ω)) | ℱ s] =ᵐ[μ] fun ω => P (t - s) g (toI (X s ω)))
    (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) (g : C(I, ℝ)) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, g (toI (stoppedValue X (fun ω => τ ω + t) ω)) ∂μ =
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, P t g (toI (stoppedValue X τ ω)) ∂μ := by
  have hX := measurable_uncurry hcont hadapt
  have hτm : Measurable fun ω => (τ ω).untopA := hτ.measurable'.untopA
  have hB : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter hτ.measurableSet_eq_top.compl
  have hcongr : ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, g (toI (stoppedValue X (fun ω => τ ω + t) ω)) ∂μ =
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤}, g (toI (X ((τ ω).untopA + t) ω)) ∂μ :=
    setIntegral_congr_fun hB fun ω hω => by simp only [stoppedValue_add_of_ne_top hω.2]
  rw [hcongr]
  simp only [stoppedValue]
  have hL : Tendsto (fun n => ∫ ω in A ∩ {ω | τ ω ≠ ⊤},
      g (toI (X (dyadicUp n (τ ω).untopA + t) ω)) ∂μ) atTop
      (𝓝 (∫ ω in A ∩ {ω | τ ω ≠ ⊤}, g (toI (X ((τ ω).untopA + t) ω)) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
      (fun n => (measurable_comp_time hX
        (((measurable_dyadicUp n).comp hτm).add_const t) g).aestronglyMeasurable)
      (integrable_const _) (fun _ => Eventually.of_forall fun _ => g.norm_coe_le_norm _)
      (Eventually.of_forall fun ω => ((g.continuous.comp continuous_projIcc).tendsto _).comp
        (((hcont ω).tendsto _).comp ((tendsto_dyadicUp _).add_const t)))
  have hR : Tendsto (fun n => ∫ ω in A ∩ {ω | τ ω ≠ ⊤},
      P t g (toI (X (dyadicUp n (τ ω).untopA) ω)) ∂μ) atTop
      (𝓝 (∫ ω in A ∩ {ω | τ ω ≠ ⊤}, P t g (toI (X (τ ω).untopA ω)) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => ‖P t g‖)
      (fun n => (measurable_comp_time hX ((measurable_dyadicUp n).comp hτm)
        (P t g)).aestronglyMeasurable)
      (integrable_const _)
      (fun _ => Eventually.of_forall fun _ => (P t g).norm_coe_le_norm _)
      (Eventually.of_forall fun ω =>
        (((P t g).continuous.comp continuous_projIcc).tendsto _).comp
          (((hcont ω).tendsto _).comp (tendsto_dyadicUp _)))
  exact tendsto_nhds_unique
    (hL.congr fun n => setIntegral_dyadic hcont hadapt hmarkov hτ hA t g n) hR

/-- The operator `g ↦ (x ↦ ∫ g dκ_t(x))` of a Feller family, on continuous functions. -/
private def kernelOp (hfeller : IsFellerFamily κ) (t : ℝ≥0) (g : C(I, ℝ)) : C(I, ℝ) :=
  ⟨fun x => ∫ y, g y ∂κ t x, hfeller t g⟩

/-! ### The strong Markov property for continuous test functions -/

omit [∀ t, IsMarkovKernel (κ t)] in
/-- **Strong Markov property for a Feller kernel family, integrated form.** Let `X` be a
continuous process adapted to `ℱ` under a finite measure `μ` that is Markov for the Feller
kernel family `κ`: `μ[g (X t) | ℱ s] = ∫ g dκ_{t - s}(X s)` for `s ≤ t` and continuous `g`.
Then for every `ℱ`-stopping time `τ`, every `A ∈ ℱ_τ`, every `t ≥ 0` and every continuous `g`,
`∫_{A ∩ {τ < ∞}} g (X (τ + t)) dμ = ∫_{A ∩ {τ < ∞}} ∫ g dκ_t(X τ) dμ`.

Source: Ethier & Kurtz (1986), ch. 4, Thm. 2.7; Revuz & Yor (1999), ch. III, §3. -/
theorem setIntegral_stoppedValue_add_eq_integral [IsFiniteMeasure μ]
    (hfeller : IsFellerFamily κ)
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => ∫ y, g y ∂κ (t - s) (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) (g : C(I, ℝ)) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    ∫ ω in A ∩ {ω | τ ω ≠ ⊤},
        g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun ω => τ ω + t) ω)) ∂μ =
      ∫ ω in A ∩ {ω | τ ω ≠ ⊤},
        ∫ y, g y ∂κ t (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω)) ∂μ :=
  setIntegral_stoppedValue_add_eq_op (P := kernelOp hfeller) hcont hadapt hmarkov hτ t g hA

/-! ### The process after a stopping time -/

omit [∀ t, IsMarkovKernel (κ t)] in
/-- **The process after a stopping time is a Markov family.** On `{τ < ∞}`, the states
`X (τ + u)` of a process that is Markov for a Feller kernel family `κ` form a Markov family for
`κ` with respect to the filtration `ℱ_{τ + u}`. -/
theorem isKernelMarkovFamily_stoppedValue_add [IsFiniteMeasure μ]
    (hfeller : IsFellerFamily κ)
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => ∫ y, g y ∂κ (t - s) (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (hτ : IsStoppingTime ℱ τ) :
    IsKernelMarkovFamily κ (μ.restrict {ω | τ ω ≠ ⊤}) (postFiltration hτ)
      fun u ω => toI (stoppedValue X (fun ω => τ ω + u) ω) where
  measurable u := continuous_projIcc.measurable.comp
    (measurable_stoppedValue (hadapt.isStronglyProgressive_of_continuous hcont)
      (isStoppingTime_add_const hτ u))
  setIntegral_eq u v huv A hA g := by
    have hτu := isStoppingTime_add_const hτ u
    have hA' : MeasurableSet A := hτu.measurableSpace_le _ hA
    have hfin : {ω | τ ω + (u : WithTop ℝ≥0) ≠ ⊤} = {ω | τ ω ≠ ⊤} := by
      ext ω
      simp only [mem_ofPred_eq]
      induction τ ω with
      | top => simp only [WithTop.top_add]
      | coe r =>
        rw [← WithTop.coe_add]
        simp only [ne_eq, WithTop.coe_ne_top, not_false_eq_true]
    have hsum : (fun ω => τ ω + (u : WithTop ℝ≥0) + ((v - u : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => τ ω + v := by
      funext ω
      rw [add_assoc, ← WithTop.coe_add, add_tsub_cancel_of_le huv]
    have h := setIntegral_stoppedValue_add_eq_integral hfeller hcont hadapt hmarkov hτu
      (v - u) g hA
    simp only [hfin, hsum] at h
    rw [Measure.restrict_restrict hA']
    exact h

/-! ### The process after a deterministic time -/

/-- The σ-algebras `ℱ_{s + u}`, `u ≥ 0`, as a filtration. -/
def shiftFiltration (ℱ : Filtration ℝ≥0 mΩ) (s : ℝ≥0) : Filtration ℝ≥0 mΩ where
  seq u := ℱ (s + u)
  mono' _ _ huv := ℱ.mono (add_le_add le_rfl huv)
  le' u := ℱ.le (s + u)

omit [∀ t, IsMarkovKernel (κ t)] in
/-- **The process after a deterministic time is a Markov family**, with no Feller hypothesis:
the states `X (s + u)` of a process adapted to `ℱ` and Markov for `κ` form a Markov family for
`κ` with respect to the filtration `ℱ_{s + u}`. -/
theorem isKernelMarkovFamily_shift (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => ∫ y, g y ∂κ (t - s) (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    [IsFiniteMeasure μ] (s : ℝ≥0) :
    IsKernelMarkovFamily κ μ (shiftFiltration ℱ s) fun u ω => toI (X (s + u) ω) where
  measurable u := continuous_projIcc.measurable.comp (hadapt (s + u)).measurable
  setIntegral_eq u v huv A hA g := by
    have hA' : MeasurableSet[ℱ (s + u)] A := hA
    have hint : Integrable (fun ω => g (toI (X (s + v) ω))) μ :=
      integrable_comp ((hadapt _).mono (ℱ.le _)).measurable g
    have hm := hmarkov (s + u) (s + v) (add_le_add le_rfl huv) g
    rw [add_tsub_add_eq_tsub_left] at hm
    change ∫ ω in A, g (toI (X (s + v) ω)) ∂μ =
      ∫ ω in A, ∫ y, g y ∂κ (v - u) (toI (X (s + u) ω)) ∂μ
    rw [← setIntegral_condExp (ℱ.le _) hint hA']
    exact setIntegral_congr_ae (ℱ.le _ _ hA') (hm.mono fun ω hω _ => hω)

/-! ### The Wright–Fisher diffusion with selection -/

/-- `X` is a **Wright–Fisher diffusion with scaled selection coefficient `sel` (`σ = 2Ns`),
Markov for the kernel family `κ`**: it solves the martingale problem
`IsWrightFisherSolution sel` for the generator `L_σ f = x (1 - x) / 2 · f'' + σ x (1 - x) · f'`,
and for `s ≤ t` and every continuous `g`, `μ[g (X t) | ℱ s] = ∫ g dκ_{t - s}(X s)` almost surely. -/
structure IsSelectionMarkov (sel : ℝ) (κ : ℝ≥0 → Kernel I I) (ℱ : Filtration ℝ≥0 mΩ)
    (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop where
  solution : KimuraFixationProcess.IsWrightFisherSolution sel ℱ μ X
  markov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
    μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
      fun ω => ∫ y, g y ∂κ (t - s) (projIcc (0 : ℝ) 1 zero_le_one (X s ω))

namespace IsSelectionMarkov

variable {sel : ℝ}

omit [∀ t, IsMarkovKernel (κ t)] in
theorem continuous (hX : IsSelectionMarkov sel κ ℱ μ X) (ω : Ω) : Continuous fun t => X t ω :=
  hX.solution.2.1 ω

omit [∀ t, IsMarkovKernel (κ t)] in
theorem stronglyAdapted (hX : IsSelectionMarkov sel κ ℱ μ X) : StronglyAdapted ℱ X :=
  hX.solution.2.2.1

omit [∀ t, IsMarkovKernel (κ t)] in
private theorem measurable_stoppedValue_toI (hX : IsSelectionMarkov sel κ ℱ μ X)
    (hτ : IsStoppingTime ℱ τ) :
    Measurable[hτ.measurableSpace] fun ω => toI (stoppedValue X τ ω) :=
  continuous_projIcc.measurable.comp
    (measurable_stoppedValue (hX.stronglyAdapted.isStronglyProgressive_of_continuous
      hX.continuous) hτ)

private theorem stoppedValue_add_zero :
    (fun ω => toI (stoppedValue X (fun ω => τ ω + ((0 : ℝ≥0) : WithTop ℝ≥0)) ω)) =
      fun ω => toI (stoppedValue X τ ω) := by
  simp

/-- **Strong Markov property of the selection diffusion for bounded measurable `g`.** For a
Wright–Fisher diffusion with selection that is Markov for a Feller kernel family `κ`, every
`ℱ`-stopping time `τ`, every `t ≥ 0` and every bounded measurable `g` on `[0, 1]`,
`μ[1_{τ < ∞} g (X (τ + t)) | ℱ_τ] = 1_{τ < ∞} ∫ g dκ_t(X τ)` almost surely.

Source: Ethier & Kurtz (1986), ch. 4, §1 and Thm. 2.7; Revuz & Yor (1999), ch. III,
§1 and §3. -/
theorem condExp_indicator_comp_stoppedValue_add [IsFiniteMeasure μ]
    (hX : IsSelectionMarkov sel κ ℱ μ X) (hfeller : IsFellerFamily κ)
    (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) {g : I → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ y, ‖g y‖ ≤ C) :
    μ[{ω | τ ω ≠ ⊤}.indicator
        (fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun ω => τ ω + t) ω))) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator (fun ω =>
        ∫ y, g y ∂κ t (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) := by
  have hY := isKernelMarkovFamily_stoppedValue_add hfeller hX.continuous hX.stronglyAdapted
    hX.markov hτ
  have hle := measurableSpace_le_postFiltration_zero hτ
  have hS : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    hτ.measurable (measurableSet_singleton ⊤).compl
  refine condExp_indicator_ae_eq_of_map_restrict hτ.measurableSpace_le (hY.measurable' t)
    (hX.measurable_stoppedValue_toI hτ) hS (fun A hA => ?_) hg hgC
  have h := hY.map_restrict_eq_comp (u := 0) (v := t) zero_le (hle _ hA)
  rwa [tsub_zero, stoppedValue_add_zero] at h

/-- **Strong Markov property of the selection diffusion for multi-time functionals.** For a
Wright–Fisher diffusion with selection that is Markov for a Feller kernel family `κ`, every
`ℱ`-stopping time `τ`, times `t₁ ≤ … ≤ tₙ` and every bounded measurable `F` on `[0, 1]ⁿ`,
`μ[1_{τ < ∞} F (X (τ + t₁), …, X (τ + tₙ)) | ℱ_τ] = 1_{τ < ∞} ∫ F dP_t(X τ)` almost surely,
where `P_t = finiteChainKernel κ 0 t` is the ordered finite-dimensional law.

Source: Ethier & Kurtz (1986), ch. 4, §1 and Thm. 2.7; Revuz & Yor (1999), ch. III,
§1 and §3. -/
theorem condExp_indicator_finite_stoppedValue_add [IsFiniteMeasure μ]
    (hX : IsSelectionMarkov sel κ ℱ μ X) (hfeller : IsFellerFamily κ)
    (hτ : IsStoppingTime ℱ τ) {n : ℕ} {t : Fin n → ℝ≥0} (ht : Monotone t)
    {F : (Fin n → I) → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ y, ‖F y‖ ≤ C) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω =>
        F fun i => projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun ω => τ ω + t i) ω)) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator (fun ω => ∫ y, F y ∂finiteChainKernel κ 0 t
        (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) := by
  have hY := isKernelMarkovFamily_stoppedValue_add hfeller hX.continuous hX.stronglyAdapted
    hX.markov hτ
  have hle := measurableSpace_le_postFiltration_zero hτ
  have hS : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    hτ.measurable (measurableSet_singleton ⊤).compl
  refine condExp_indicator_ae_eq_of_map_restrict hτ.measurableSpace_le
    (Measurable.of_eval fun i => hY.measurable' (t i))
    (hX.measurable_stoppedValue_toI hτ) hS (fun A hA => ?_) hF hFC
  have h := hY.map_restrict_finite_eq_comp ht (fun _ => zero_le) (hle _ hA)
  rwa [stoppedValue_add_zero] at h

/-- **Strong Markov property of the selection diffusion for whole-path functionals.** For a
Wright–Fisher diffusion with selection that is Markov for a Feller Chapman–Kolmogorov kernel
family `κ`, every `ℱ`-stopping time `τ` and every bounded measurable `F` on sample paths
`ℝ≥0 → [0, 1]` (product σ-algebra),
`μ[1_{τ < ∞} F ((X (τ + u))_{u ≥ 0}) | ℱ_τ] = 1_{τ < ∞} ∫ F d(pathMeasure κ (X τ))` almost
surely: given `ℱ_τ`, the post-`τ` process has the canonical law of `κ` started at `X τ`.

Source: Ethier & Kurtz (1986), ch. 4, §1 and Thm. 2.7; Revuz & Yor (1999), ch. III,
§1 and §3. -/
theorem condExp_indicator_path_stoppedValue_add [IsFiniteMeasure μ]
    (hX : IsSelectionMarkov sel κ ℱ μ X) (hfeller : IsFellerFamily κ)
    (hκ : ∀ s t, κ (s + t) = κ t ∘ₖ κ s) (hτ : IsStoppingTime ℱ τ) {F : SamplePath → ℝ}
    (hF : Measurable F) {C : ℝ} (hFC : ∀ y, ‖F y‖ ≤ C) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω =>
        F fun u => projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun ω => τ ω + u) ω)) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator (fun ω =>
        ∫ y, F y ∂pathMeasure κ hκ (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) := by
  have hY := isKernelMarkovFamily_stoppedValue_add hfeller hX.continuous hX.stronglyAdapted
    hX.markov hτ
  have hle := measurableSpace_le_postFiltration_zero hτ
  have hS : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    hτ.measurable (measurableSet_singleton ⊤).compl
  refine condExp_indicator_ae_eq_of_map_restrict (κ := pathKernel hκ) hτ.measurableSpace_le
    (Measurable.of_eval hY.measurable')
    (hX.measurable_stoppedValue_toI hτ) hS (fun A hA => ?_) hF hFC
  have h := hY.map_restrict_path_eq_comp hκ (hle _ hA)
  rwa [stoppedValue_add_zero] at h

/-- **Markov property of the selection diffusion for whole-path functionals at a deterministic
time**, with no Feller hypothesis. For a Wright–Fisher diffusion with selection that is Markov
for a Chapman–Kolmogorov kernel family `κ`, every `s ≥ 0` and every bounded measurable `F` on
sample paths, `μ[F ((X (s + u))_{u ≥ 0}) | ℱ_s] = ∫ F d(pathMeasure κ (X s))` almost surely.

Source: Ethier & Kurtz (1986), ch. 4, §1; Revuz & Yor (1999), ch. III, §1. -/
theorem condExp_path_add [IsFiniteMeasure μ] (hX : IsSelectionMarkov sel κ ℱ μ X)
    (hκ : ∀ s t, κ (s + t) = κ t ∘ₖ κ s) (s : ℝ≥0) {F : SamplePath → ℝ} (hF : Measurable F)
    {C : ℝ} (hFC : ∀ y, ‖F y‖ ≤ C) :
    μ[fun ω => F fun u => projIcc (0 : ℝ) 1 zero_le_one (X (s + u) ω) | ℱ s] =ᵐ[μ]
      fun ω => ∫ y, F y ∂pathMeasure κ hκ (projIcc (0 : ℝ) 1 zero_le_one (X s ω)) := by
  have hY := isKernelMarkovFamily_shift hX.stronglyAdapted hX.markov s
  have hW : Measurable[ℱ s] fun ω => toI (X s ω) :=
    continuous_projIcc.measurable.comp (hX.stronglyAdapted s).measurable
  have hlaw : ∀ A, MeasurableSet[ℱ s] A →
      ((μ.restrict univ).restrict A).map (fun ω u => toI (X (s + u) ω)) =
        pathKernel hκ ∘ₘ ((μ.restrict univ).restrict A).map fun ω => toI (X s ω) := by
    intro A hA
    have hA' : MeasurableSet[shiftFiltration ℱ s 0] A := by
      change MeasurableSet[ℱ (s + 0)] A
      rwa [add_zero]
    have hmap := hY.map_restrict_path_eq_comp hκ hA'
    simp only [add_zero] at hmap
    simpa only [Measure.restrict_univ] using hmap
  have h := condExp_indicator_ae_eq_of_map_restrict (κ := pathKernel hκ) (ℱ.le s)
    (Measurable.of_eval hY.measurable') hW MeasurableSet.univ hlaw hF hFC
  simpa only [indicator_univ, pathKernel_apply] using h

end IsSelectionMarkov

/-! ### The neutral case -/

/-- The neutral Wright–Fisher transition kernels are Feller: `∫ g dK_t(x) = (P_t g)(x)`. -/
theorem isFellerFamily_neutralKernel : IsFellerFamily neutralKernel := fun t g => by
  have h : (fun x => ∫ y, g y ∂neutralKernel t x) = wfSemigroup (t : ℝ) g :=
    funext fun x => integral_wfTransitionKernel _ g x
  rw [h]
  exact (wfSemigroup (t : ℝ) g).continuous

/-- **At `σ = 0` the hypotheses hold.** The neutral realization `modifiedProcess x` under
`rawMeasure x` with its natural filtration is a Wright–Fisher diffusion with selection `0`,
Markov for `neutralKernel`. -/
theorem isSelectionMarkov_zero_modifiedProcess (x : I) :
    IsSelectionMarkov 0 neutralKernel (naturalFiltration x) (rawMeasure x)
      (modifiedProcess x) where
  solution := isWrightFisherSolution_zero_modifiedProcess x
  markov s t hst g := (condExp_modifiedProcess_eq_wfSemigroup x hst g).mono fun ω hω => by
    rw [hω, ← NNReal.coe_sub hst]
    exact (integral_wfTransitionKernel _ g _).symm

end

end MathlibExt.Biology.PopulationGenetics.Diffusion.SelectionMonotoneClass
