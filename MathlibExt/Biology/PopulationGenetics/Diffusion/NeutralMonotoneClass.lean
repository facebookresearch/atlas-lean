/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralStrongMarkov
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Monotone-class extensions of the neutral Wright–Fisher Markov property

`Diffusion.NeutralStrongMarkov` proves the strong Markov property of a continuous `[0, 1]`-valued
process `X` that is Markov for the neutral Wright–Fisher semigroup `wfSemigroup`, for one-time
functionals `g (X (τ + t))` with `g` continuous. This file extends it, by monotone-class
(π-λ) arguments, to

* bounded measurable `g`, with the semigroup replaced by the transition kernel `neutralKernel t`;
* multi-time functionals `F (X (τ + t₁), …, X (τ + tₙ))`, whose conditional law is the ordered
  finite-dimensional law `finiteChainKernel neutralKernel 0 t` started at `X τ`;
* whole-path functionals `F ((X (τ + u))_{u ≥ 0})`, whose conditional law is the canonical
  path measure `rawMeasure (X τ)` of the neutral Wright–Fisher diffusion.

## Main results

* `measurable_rawMeasure`, `wfPathKernel`: `x ↦ rawMeasure x` is a Markov kernel.
* `IsNeutralMarkovFamily`: a process `Y` adapted to a filtration and Markov for `wfSemigroup` on
  continuous test functions, in integrated form.
* `IsNeutralMarkovFamily.map_restrict_eq_comp`, `.map_restrict_finite_eq_comp`,
  `.map_restrict_path_eq_comp`: the one-time, multi-time and path laws of such a family.
* `condExp_indicator_comp_stoppedValue_add`: strong Markov property for bounded measurable `g`.
* `condExp_indicator_finite_stoppedValue_add`: strong Markov property for multi-time
  functionals.
* `condExp_indicator_path_stoppedValue_add`: strong Markov property for whole-path functionals.
* `condExp_modifiedState_path_stoppedValue_add`: the whole-path statement for the realization
  `modifiedState x`, with no Markov hypothesis.

## Method

On continuous test functions the Markov property says that, restricted to an event `A` of the
past, the law of the next state equals the law of the current state pushed through the kernel;
two finite measures on `[0, 1]` that agree on continuous functions are equal
(`ext_of_forall_integral_eq_of_IsFiniteMeasure`), which gives the kernel form on all measurable
sets. Joint laws with a past variable follow by uniqueness on measurable rectangles; the
multi-time law follows by induction on the number of times, appending one time at a time with
`MarkovSemigroupProjective.map_init_last_finiteChainLaw_snoc`. The path law follows by
uniqueness on measurable cylinders, which form a π-system generating the product σ-algebra, and
the same uniqueness shows that `x ↦ rawMeasure x` is measurable. The strong Markov statements
apply this to `Y u = X (τ + u)` on `{τ < ∞}` with the filtration `ℱ_{τ + u}`, using
`NeutralStrongMarkov.setIntegral_stoppedValue_add_eq` for the one-step identity.

## Source receipt

* Reused: `setIntegral_stoppedValue_add_eq` (`Diffusion.NeutralStrongMarkov`),
  `condExp_modifiedProcess_eq_wfSemigroup`
  (`NeutralMartingaleProblem.Markov`), `finiteChainKernel`, `map_init_last_finiteChainLaw_snoc`,
  `map_ordered_pathMeasure` (`MathlibExt.Probability.MarkovSemigroupProjective`),
  `integral_wfTransitionKernel` (`Diffusion.TransitionKernel`), and Mathlib's
  `ext_of_generate_finite`, `ext_of_forall_integral_eq_of_IsFiniteMeasure`,
  `Measurable.measure_of_isPiSystem` and measurable cylinders.
* Proved here: measurability of `x ↦ rawMeasure x`, the kernel, joint, multi-time and path laws
  of a Markov family, that `τ + u` is a stopping time for `ℝ≥0`-indexed filtrations, and the
  conditional-expectation statements.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), ch. 4, §1 (the Markov property for path functionals; monotone-class
  extension from finite-dimensional to path functionals) and ch. 4, Thm. 2.7.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer (1999),
  ch. III, §1 and §3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal unitInterval

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMonotoneClass

open MathlibExt.Probability.MarkovSemigroupProjective
open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralStrongMarkov

noncomputable section

/-! ### The path-measure kernel -/

/-- A measurable cylinder of sample paths, read through the increasing enumeration of its finite
set of times. -/
theorem cylinder_eq_preimage (J : Finset ℝ≥0) (S : Set (J → I)) :
    cylinder J S = (fun ω : SamplePath => fun i => ω (J.orderEmbOfFin rfl i)) ⁻¹'
      ((orderMeasurableEquiv J : (Fin J.card → I) ≃ᵐ (J → I)) ⁻¹' S) := by
  ext ω
  simp only [cylinder, mem_preimage]
  congr! 1
  funext j
  simp only [orderMeasurableEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  rfl

/-- The canonical path measure of a measurable cylinder is given by the ordered
finite-dimensional law. -/
theorem rawMeasure_cylinder (x : I) (J : Finset ℝ≥0) {S : Set (J → I)}
    (hS : MeasurableSet S) :
    rawMeasure x (cylinder J S) =
      finiteChainKernel neutralKernel 0 (J.orderEmbOfFin rfl) x
        ((orderMeasurableEquiv J : (Fin J.card → I) ≃ᵐ (J → I)) ⁻¹' S) := by
  have hproj : Measurable fun ω : SamplePath => fun i => ω (J.orderEmbOfFin rfl i) :=
    Measurable.of_eval fun i => measurable_pi_apply (J.orderEmbOfFin rfl i)
  rw [cylinder_eq_preimage, ← Measure.map_apply hproj ((orderMeasurableEquiv J).measurable hS)]
  exact congrArg (fun ν : Measure (Fin J.card → I) => ν _)
    (map_ordered_pathMeasure neutralKernel neutralKernel_add x J)

/-- **The path measure is measurable in the initial state.** Measurability on measurable
cylinders, a π-system generating the product σ-algebra, extends to all measurable sets. -/
theorem measurable_rawMeasure : Measurable rawMeasure := by
  refine Measurable.measure_of_isPiSystem generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_ (by simp)
  intro C hC
  obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders C).1 hC
  simp_rw [rawMeasure_cylinder _ J hS]
  exact Kernel.measurable_coe _ ((orderMeasurableEquiv J).measurable hS)

/-- The canonical path measures of the neutral Wright–Fisher diffusion, as a Markov kernel from
the initial state to sample paths. -/
def wfPathKernel : Kernel I SamplePath :=
  ⟨rawMeasure, measurable_rawMeasure⟩

@[simp]
theorem wfPathKernel_apply (x : I) : wfPathKernel x = rawMeasure x :=
  rfl

instance isMarkovKernel_wfPathKernel : IsMarkovKernel wfPathKernel :=
  ⟨fun x => by rw [wfPathKernel_apply]; infer_instance⟩

/-! ### Integrals against a kernel pushed forward along a map -/

private theorem lintegral_comp_map {Ω : Type*} {mΩ : MeasurableSpace Ω} {β : Type*}
    [MeasurableSpace β] (κ : Kernel I β) {ν : Measure Ω} {W : Ω → I} (hW : Measurable W)
    {F : β → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y, F y ∂(κ ∘ₘ ν.map W) = ∫⁻ ω, ∫⁻ y, F y ∂κ (W ω) ∂ν := by
  rw [Measure.lintegral_bind κ.aemeasurable hF.aemeasurable,
    lintegral_map hF.lintegral_kernel hW]

private theorem integral_comp_map {Ω : Type*} {mΩ : MeasurableSpace Ω} {β : Type*}
    [MeasurableSpace β] (κ : Kernel I β) [IsMarkovKernel κ] {ν : Measure Ω} [IsFiniteMeasure ν]
    {W : Ω → I} (hW : Measurable W) {F : β → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ y, ‖F y‖ ≤ C) :
    ∫ y, F y ∂(κ ∘ₘ ν.map W) = ∫ ω, ∫ y, F y ∂κ (W ω) ∂ν := by
  have hint : Integrable F ((κ ∘ₖ Kernel.const Unit (ν.map W)) ()) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Eventually.of_forall hFC)
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp hint]
  simp only [Kernel.const_apply]
  exact integral_map hW.aemeasurable
    ((hF.stronglyMeasurable.comp_measurable measurable_snd).integral_kernel_prod_right'
      (κ := κ)).aestronglyMeasurable

/-! ### Conditional expectations from conditional laws -/

/-- **Conditional expectation from a conditional law, on an event.** If, restricted to every
`A ∈ 𝒢`, the law of `V` under `μ` restricted to `S` is the law of the `𝒢`-measurable `W` pushed
through `κ`, then `μ[1_S F (V) | 𝒢] = 1_S ∫ F dκ(W)` for every bounded measurable `F`. -/
theorem condExp_indicator_ae_eq_of_map_restrict {Ω : Type*} {𝒢 mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {β : Type*} [MeasurableSpace β] (h𝒢 : 𝒢 ≤ mΩ)
    {κ : Kernel I β} [IsMarkovKernel κ] {V : Ω → β} {W : Ω → I} (hV : Measurable V)
    (hW : Measurable[𝒢] W)
    {S : Set Ω} (hS : MeasurableSet[𝒢] S)
    (hlaw : ∀ A, MeasurableSet[𝒢] A →
      ((μ.restrict S).restrict A).map V = κ ∘ₘ ((μ.restrict S).restrict A).map W)
    {F : β → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ y, ‖F y‖ ≤ C) :
    μ[S.indicator fun ω => F (V ω) | 𝒢] =ᵐ[μ] S.indicator fun ω => ∫ y, F y ∂κ (W ω) := by
  have hW' : Measurable W := hW.mono h𝒢 le_rfl
  have hS' : MeasurableSet S := h𝒢 _ hS
  have hGm : StronglyMeasurable[𝒢] fun ω => ∫ y, F y ∂κ (W ω) :=
    ((hF.stronglyMeasurable.comp_measurable measurable_snd).integral_kernel_prod_right'
      (κ := κ)).comp_measurable hW
  have hGC : ∀ ω, ‖∫ y, F y ∂κ (W ω)‖ ≤ C := fun ω => by
    refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hFC)).trans ?_
    simp
  have hFint : Integrable (S.indicator fun ω => F (V ω)) μ :=
    (Integrable.of_bound (f := fun ω => F (V ω)) (hF.comp hV).aestronglyMeasurable C
      (Eventually.of_forall fun ω => hFC _)).indicator hS'
  have hGint : Integrable (S.indicator fun ω => ∫ y, F y ∂κ (W ω)) μ :=
    (Integrable.of_bound (hGm.mono h𝒢).aestronglyMeasurable C
      (Eventually.of_forall hGC)).indicator hS'
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝒢 hFint (fun _ _ _ => hGint.integrableOn)
    (fun A hA _ => ?_) (hGm.indicator hS).aestronglyMeasurable).symm
  have hA' : MeasurableSet A := h𝒢 _ hA
  rw [setIntegral_indicator hS', setIntegral_indicator hS', ← Measure.restrict_restrict hA',
    ← integral_map hV.aemeasurable hF.aestronglyMeasurable,
    hlaw A hA, integral_comp_map κ hW' hF hFC]

/-! ### Markov families for the neutral Wright–Fisher semigroup -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `Y` is a **Markov family for the neutral Wright–Fisher semigroup** with respect to the
filtration `𝒢` under `μ`: each `Y u` is `𝒢 u`-measurable, and for `u ≤ v`, every `A ∈ 𝒢 u` and
every continuous `g` on `[0, 1]`, `∫_A g (Y v) dμ = ∫_A (wfSemigroup (v - u) g) (Y u) dμ`. -/
structure IsNeutralMarkovFamily (μ : Measure Ω) (𝒢 : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 → Ω → I) : Prop where
  measurable : ∀ u, Measurable[𝒢 u] (Y u)
  setIntegral_eq : ∀ u v, u ≤ v → ∀ A, MeasurableSet[𝒢 u] A → ∀ g : C(I, ℝ),
    ∫ ω in A, g (Y v ω) ∂μ = ∫ ω in A, wfSemigroup ((v : ℝ) - u) g (Y u ω) ∂μ

namespace IsNeutralMarkovFamily

variable {𝒢 : Filtration ℝ≥0 mΩ} {Y : ℝ≥0 → Ω → I}

theorem measurable' (hY : IsNeutralMarkovFamily μ 𝒢 Y) (u : ℝ≥0) : Measurable (Y u) :=
  (hY.measurable u).mono (𝒢.le u) le_rfl

/-- **Kernel form of the Markov property.** For `u ≤ v` and `A ∈ 𝒢 u`, the law of `Y v` on `A`
is the law of `Y u` on `A` pushed through `neutralKernel (v - u)`. -/
theorem map_restrict_eq_comp [IsFiniteMeasure μ] (hY : IsNeutralMarkovFamily μ 𝒢 Y)
    {u v : ℝ≥0} (huv : u ≤ v) {A : Set Ω} (hA : MeasurableSet[𝒢 u] A) :
    (μ.restrict A).map (Y v) = neutralKernel (v - u) ∘ₘ (μ.restrict A).map (Y u) := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map (hY.measurable' v).aemeasurable f.continuous.aestronglyMeasurable,
    integral_comp_map _ (hY.measurable' u) f.continuous.measurable (C := ‖f‖)
      (f.norm_coe_le_norm ·)]
  have h := hY.setIntegral_eq u v huv A hA f.toContinuousMap
  have hK : ∀ x, ∫ y, f y ∂neutralKernel (v - u) x =
      wfSemigroup ((v : ℝ) - u) f.toContinuousMap x := fun x => by
    rw [neutralKernel, NNReal.coe_sub huv]
    exact integral_wfTransitionKernel _ f.toContinuousMap x
  simp only [hK]
  exact h

/-- The kernel form of the Markov property for nonnegative measurable test functions. -/
theorem lintegral_step [IsFiniteMeasure μ] (hY : IsNeutralMarkovFamily μ 𝒢 Y) {u v : ℝ≥0}
    (huv : u ≤ v) {A : Set Ω} (hA : MeasurableSet[𝒢 u] A) {f : I → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in A, f (Y v ω) ∂μ = ∫⁻ ω in A, ∫⁻ y, f y ∂neutralKernel (v - u) (Y u ω) ∂μ := by
  rw [← lintegral_map hf (hY.measurable' v), hY.map_restrict_eq_comp huv hA,
    lintegral_comp_map _ (hY.measurable' u) hf]

/-- **Joint law with the past.** For `u ≤ v`, a `𝒢 u`-measurable `Z` with `Y u = φ ∘ Z` and
`A ∈ 𝒢 u`, the joint law of `(Z, Y v)` on `A` is the law of `Z` on `A` composed with one kernel
step from `φ`. -/
theorem map_restrict_prod_eq_compProd [IsFiniteMeasure μ] (hY : IsNeutralMarkovFamily μ 𝒢 Y)
    {β : Type*} [MeasurableSpace β] {u v : ℝ≥0} (huv : u ≤ v) {Z : Ω → β}
    (hZ : Measurable[𝒢 u] Z) {φ : β → I} (hφ : Measurable φ) (hZφ : ∀ ω, φ (Z ω) = Y u ω)
    {A : Set Ω} (hA : MeasurableSet[𝒢 u] A) :
    (μ.restrict A).map (fun ω => (Z ω, Y v ω)) =
      (μ.restrict A).map Z ⊗ₘ (neutralKernel (v - u)).comap φ hφ := by
  have hZ' : Measurable Z := hZ.mono (𝒢.le u) le_rfl
  have hA' : MeasurableSet A := 𝒢.le u _ hA
  have hrect : ∀ S, MeasurableSet S → ∀ B, MeasurableSet B →
      (μ.restrict A).map (fun ω => (Z ω, Y v ω)) (S ×ˢ B) =
        ((μ.restrict A).map Z ⊗ₘ (neutralKernel (v - u)).comap φ hφ) (S ×ˢ B) := by
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
    ∫⁻ z, F z ∂finiteChainKernel neutralKernel s t x =
      ∫⁻ y, F (fun _ => y) ∂neutralKernel (t 0 - s) x := by
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
private theorem lintegral_finite_succ [IsFiniteMeasure μ] (hY : IsNeutralMarkovFamily μ 𝒢 Y) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ s, (∀ i, s ≤ t i) →
      ∀ A, MeasurableSet[𝒢 s] A → ∀ F : (Fin (n + 1) → I) → ℝ≥0∞, Measurable F →
        ∫⁻ ω in A, F (fun i => Y (t i) ω) ∂μ =
          ∫⁻ ω in A, ∫⁻ z, F z ∂finiteChainKernel neutralKernel s t (Y s ω) ∂μ
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
      ∫⁻ y, G (w, y) ∂neutralKernel (b - u) (w (Fin.last n))
    have hH : Measurable H :=
      Measurable.lintegral_kernel_prod_right'
        (κ := (neutralKernel (b - u)).comap (fun w : Fin (n + 1) → I => w (Fin.last n))
          (measurable_pi_apply _)) hG
    have hsnoc : ∀ z : Fin (n + 2) → I, F z = G (Fin.init z, z (Fin.last (n + 1))) := fun z => by
      simp only [G, Fin.snoc_init_self]
    have hsplit : ∀ ω, F (fun i => Y (t i) ω) = G ((fun i => Y (τ i) ω), Y b ω) := fun ω => by
      rw [hsnoc]
      rfl
    have hchain : ∀ x, ∫⁻ z, F z ∂finiteChainKernel neutralKernel s t x =
        ∫⁻ w, H w ∂finiteChainKernel neutralKernel s τ x := fun x => by
      have ht' : t = Fin.snoc τ b := (Fin.snoc_init_self t).symm
      have hmap := map_init_last_finiteChainLaw_snoc neutralKernel x s τ b
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
finite-dimensional kernel `finiteChainKernel neutralKernel s t`. -/
theorem map_restrict_finite_eq_comp [IsFiniteMeasure μ] (hY : IsNeutralMarkovFamily μ 𝒢 Y)
    {n : ℕ} {t : Fin n → ℝ≥0} (ht : Monotone t) {s : ℝ≥0} (hs : ∀ i, s ≤ t i) {A : Set Ω}
    (hA : MeasurableSet[𝒢 s] A) :
    (μ.restrict A).map (fun ω i => Y (t i) ω) =
      finiteChainKernel neutralKernel s t ∘ₘ (μ.restrict A).map (Y s) := by
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
is the law of `Y 0` on `A` pushed through the path-measure kernel `wfPathKernel`. -/
theorem map_restrict_path_eq_comp [IsFiniteMeasure μ] (hY : IsNeutralMarkovFamily μ 𝒢 Y)
    {A : Set Ω} (hA : MeasurableSet[𝒢 0] A) :
    (μ.restrict A).map (fun ω u => Y u ω) = wfPathKernel ∘ₘ (μ.restrict A).map (Y 0) := by
  have hpath : Measurable fun ω u => Y u ω := Measurable.of_eval hY.measurable'
  have hcyl : ∀ J : Finset ℝ≥0, ∀ S : Set (J → I), MeasurableSet S →
      (μ.restrict A).map (fun ω u => Y u ω) (cylinder J S) =
        (wfPathKernel ∘ₘ (μ.restrict A).map (Y 0)) (cylinder J S) := by
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
    simp_rw [wfPathKernel_apply, rawMeasure_cylinder _ J hS]
    rw [← h, cylinder_eq_preimage]
    rfl
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders C).1 hC
    exact hcyl J S hS
  · have h := hcyl ∅ univ MeasurableSet.univ
    rwa [cylinder_univ] at h

end IsNeutralMarkovFamily

/-! ### The process after a stopping time -/

/-- States are read in `[0, 1]` through `Set.projIcc`, as in the Markov hypothesis. -/
local notation "toI" => projIcc (0 : ℝ) 1 zero_le_one

variable {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

/-- A stopping time shifted by a constant is a stopping time. (Mathlib's
`IsStoppingTime.add_const` requires an additive group of times, which `ℝ≥0` is not.) -/
theorem isStoppingTime_add_const (hτ : IsStoppingTime ℱ τ) (u : ℝ≥0) :
    IsStoppingTime ℱ fun ω => τ ω + u := by
  intro i
  by_cases hui : u ≤ i
  · have h : {ω | τ ω + u ≤ i} = {ω | τ ω ≤ ((i - u : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq]
      induction τ ω with
      | top => simp only [WithTop.top_add, top_le_iff, WithTop.coe_ne_top]
      | coe r =>
        rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
        exact (le_tsub_iff_right hui).symm
    rw [h]
    exact ℱ.mono tsub_le_self _ (hτ (i - u))
  · have h : {ω | τ ω + u ≤ i} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hle
      exact hui (WithTop.coe_le_coe.1 ((le_add_self).trans hle))
    rw [h]
    exact @MeasurableSet.empty _ (ℱ i)

/-- The σ-algebras `ℱ_{τ + u}`, `u ≥ 0`, as a filtration. -/
def postFiltration (hτ : IsStoppingTime ℱ τ) : Filtration ℝ≥0 mΩ where
  seq u := (isStoppingTime_add_const hτ u).measurableSpace
  mono' _ _ huv := IsStoppingTime.measurableSpace_mono _ _ fun _ =>
    add_le_add le_rfl (WithTop.coe_le_coe.2 huv)
  le' u := (isStoppingTime_add_const hτ u).measurableSpace_le

/-- `ℱ_τ` is contained in the first σ-algebra of the post-`τ` filtration. -/
theorem measurableSpace_le_postFiltration_zero (hτ : IsStoppingTime ℱ τ) :
    hτ.measurableSpace ≤ postFiltration hτ 0 :=
  hτ.measurableSpace_mono (isStoppingTime_add_const hτ 0) fun _ => le_self_add

/-- **The process after a stopping time is a Markov family.** On `{τ < ∞}`, the states
`X (τ + u)` form a Markov family for the neutral Wright–Fisher semigroup with respect to the
filtration `ℱ_{τ + u}`. -/
theorem isNeutralMarkovFamily_stoppedValue_add [IsFiniteMeasure μ]
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (hτ : IsStoppingTime ℱ τ) :
    IsNeutralMarkovFamily (μ.restrict {ω | τ ω ≠ ⊤}) (postFiltration hτ)
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
    have h := setIntegral_stoppedValue_add_eq hcont hadapt hmarkov hτu (v - u) g hA
    simp only [hfin, hsum, NNReal.coe_sub huv] at h
    rw [Measure.restrict_restrict hA']
    exact h

/-! ### Strong Markov property for bounded measurable, multi-time and path functionals -/

private theorem stoppedValue_add_zero :
    (fun ω => toI (stoppedValue X (fun ω => τ ω + ((0 : ℝ≥0) : WithTop ℝ≥0)) ω)) =
      fun ω => toI (stoppedValue X τ ω) := by
  simp

/-- **Strong Markov property for bounded measurable `g`.** Under the hypotheses of
`NeutralStrongMarkov.condExp_stoppedValue_add_ae_eq`, for every `ℱ`-stopping time `τ`, every
`t ≥ 0` and every bounded measurable `g` on `[0, 1]`,
`μ[1_{τ < ∞} g (X (τ + t)) | ℱ_τ] = 1_{τ < ∞} ∫ g dK_t(X τ)` almost surely, where
`K_t = neutralKernel t` is the transition kernel of `wfSemigroup t`.

Source: Ethier & Kurtz (1986), ch. 4, §1 and Thm. 2.7; Revuz & Yor (1999), ch. III,
§1 and §3. -/
theorem condExp_indicator_comp_stoppedValue_add [IsFiniteMeasure μ]
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) {g : I → ℝ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ y, ‖g y‖ ≤ C) :
    μ[{ω | τ ω ≠ ⊤}.indicator
        (fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun ω => τ ω + t) ω))) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator (fun ω =>
        ∫ y, g y ∂neutralKernel t (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) := by
  have hY := isNeutralMarkovFamily_stoppedValue_add hcont hadapt hmarkov hτ
  have hle := measurableSpace_le_postFiltration_zero hτ
  have hW : Measurable[hτ.measurableSpace] fun ω => toI (stoppedValue X τ ω) :=
    continuous_projIcc.measurable.comp
      (measurable_stoppedValue (hadapt.isStronglyProgressive_of_continuous hcont) hτ)
  have hS : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    hτ.measurable (measurableSet_singleton ⊤).compl
  refine condExp_indicator_ae_eq_of_map_restrict hτ.measurableSpace_le (hY.measurable' t)
    hW hS (fun A hA => ?_) hg hgC
  have h := hY.map_restrict_eq_comp (u := 0) (v := t) zero_le (hle _ hA)
  rwa [tsub_zero, stoppedValue_add_zero] at h

/-- **Strong Markov property for multi-time functionals.** Under the hypotheses of
`NeutralStrongMarkov.condExp_stoppedValue_add_ae_eq`, for every `ℱ`-stopping time `τ`, times
`t₁ ≤ … ≤ tₙ` and every bounded measurable `F` on `[0, 1]ⁿ`,
`μ[1_{τ < ∞} F (X (τ + t₁), …, X (τ + tₙ)) | ℱ_τ] = 1_{τ < ∞} ∫ F dP_t(X τ)` almost surely,
where `P_t = finiteChainKernel neutralKernel 0 t` is the ordered finite-dimensional law of the
neutral Wright–Fisher diffusion at times `t`.

Source: Ethier & Kurtz (1986), ch. 4, §1 and Thm. 2.7; Revuz & Yor (1999), ch. III,
§1 and §3. -/
theorem condExp_indicator_finite_stoppedValue_add [IsFiniteMeasure μ]
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (hτ : IsStoppingTime ℱ τ) {n : ℕ} {t : Fin n → ℝ≥0} (ht : Monotone t)
    {F : (Fin n → I) → ℝ} (hF : Measurable F) {C : ℝ} (hFC : ∀ y, ‖F y‖ ≤ C) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω =>
        F fun i => projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun ω => τ ω + t i) ω)) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator (fun ω => ∫ y, F y ∂finiteChainKernel neutralKernel 0 t
        (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) := by
  have hY := isNeutralMarkovFamily_stoppedValue_add hcont hadapt hmarkov hτ
  have hle := measurableSpace_le_postFiltration_zero hτ
  have hW : Measurable[hτ.measurableSpace] fun ω => toI (stoppedValue X τ ω) :=
    continuous_projIcc.measurable.comp
      (measurable_stoppedValue (hadapt.isStronglyProgressive_of_continuous hcont) hτ)
  have hS : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    hτ.measurable (measurableSet_singleton ⊤).compl
  refine condExp_indicator_ae_eq_of_map_restrict hτ.measurableSpace_le
    (Measurable.of_eval fun i => hY.measurable' (t i))
    hW hS (fun A hA => ?_) hF hFC
  have h := hY.map_restrict_finite_eq_comp ht (fun _ => zero_le) (hle _ hA)
  rwa [stoppedValue_add_zero] at h

/-- **Strong Markov property for whole-path functionals.** Under the hypotheses of
`NeutralStrongMarkov.condExp_stoppedValue_add_ae_eq`, for every `ℱ`-stopping time `τ` and every
bounded measurable `F` on sample paths `ℝ≥0 → [0, 1]` (product σ-algebra),
`μ[1_{τ < ∞} F ((X (τ + u))_{u ≥ 0}) | ℱ_τ] = 1_{τ < ∞} ∫ F d(rawMeasure (X τ))` almost surely:
given `ℱ_τ`, the post-`τ` process is the neutral Wright–Fisher diffusion started at `X τ`.

Source: Ethier & Kurtz (1986), ch. 4, §1 and Thm. 2.7; Revuz & Yor (1999), ch. III,
§1 and §3. -/
theorem condExp_indicator_path_stoppedValue_add [IsFiniteMeasure μ]
    (hcont : ∀ ω, Continuous fun t => X t ω) (hadapt : StronglyAdapted ℱ X)
    (hmarkov : ∀ s t : ℝ≥0, s ≤ t → ∀ g : C(I, ℝ),
      μ[fun ω => g (projIcc (0 : ℝ) 1 zero_le_one (X t ω)) | ℱ s] =ᵐ[μ]
        fun ω => wfSemigroup ((t : ℝ) - s) g (projIcc (0 : ℝ) 1 zero_le_one (X s ω)))
    (hτ : IsStoppingTime ℱ τ) {F : SamplePath → ℝ} (hF : Measurable F) {C : ℝ}
    (hFC : ∀ y, ‖F y‖ ≤ C) :
    μ[{ω | τ ω ≠ ⊤}.indicator (fun ω =>
        F fun u => projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X (fun ω => τ ω + u) ω)) |
        hτ.measurableSpace] =ᵐ[μ]
      {ω | τ ω ≠ ⊤}.indicator (fun ω =>
        ∫ y, F y ∂rawMeasure (projIcc (0 : ℝ) 1 zero_le_one (stoppedValue X τ ω))) := by
  have hY := isNeutralMarkovFamily_stoppedValue_add hcont hadapt hmarkov hτ
  have hle := measurableSpace_le_postFiltration_zero hτ
  have hW : Measurable[hτ.measurableSpace] fun ω => toI (stoppedValue X τ ω) :=
    continuous_projIcc.measurable.comp
      (measurable_stoppedValue (hadapt.isStronglyProgressive_of_continuous hcont) hτ)
  have hS : MeasurableSet[hτ.measurableSpace] {ω | τ ω ≠ ⊤} :=
    hτ.measurable (measurableSet_singleton ⊤).compl
  refine condExp_indicator_ae_eq_of_map_restrict (κ := wfPathKernel) hτ.measurableSpace_le
    (Measurable.of_eval hY.measurable')
    hW hS (fun A hA => ?_) hF hFC
  have h := hY.map_restrict_path_eq_comp (hle _ hA)
  rwa [stoppedValue_add_zero] at h

/-! ### The neutral Wright–Fisher realization -/

/-- **Strong Markov property of the realization for whole-path functionals, unconditional.**
For the selected continuous realization `modifiedState x` under `rawMeasure x` with its natural
filtration, every stopping time `τ` and every bounded measurable `F` on sample paths,
`E_x[1_{τ < ∞} F ((X (τ + u))_{u ≥ 0}) | ℱ_τ] = 1_{τ < ∞} ∫ F d(rawMeasure (X τ))` almost surely.
The Markov hypothesis is discharged by `condExp_modifiedProcess_eq_wfSemigroup`.

Source: Ethier & Kurtz (1986), ch. 4, Thm. 2.7 and ch. 10 (Wright–Fisher diffusion). -/
theorem condExp_modifiedState_path_stoppedValue_add (x : I) {τ : SamplePath → WithTop ℝ≥0}
    (hτ : IsStoppingTime (naturalFiltration x) τ) {F : SamplePath → ℝ} (hF : Measurable F)
    {C : ℝ} (hFC : ∀ y, ‖F y‖ ≤ C) :
    (rawMeasure x)[{ω | τ ω ≠ ⊤}.indicator (fun ω =>
        F fun u => stoppedValue (modifiedState x) (fun ω => τ ω + u) ω) |
        hτ.measurableSpace] =ᵐ[rawMeasure x]
      {ω | τ ω ≠ ⊤}.indicator (fun ω =>
        ∫ y, F y ∂rawMeasure (stoppedValue (modifiedState x) τ ω)) := by
  have hproj : ∀ (ρ : SamplePath → WithTop ℝ≥0) ω,
      projIcc (0 : ℝ) 1 zero_le_one (stoppedValue (modifiedProcess x) ρ ω) =
        stoppedValue (modifiedState x) ρ ω :=
    fun ρ ω => projIcc_of_mem _ (modifiedProcess_mem_Icc x _ ω)
  simpa only [hproj] using condExp_indicator_path_stoppedValue_add
    (continuous_modifiedProcess x) (stronglyAdapted_naturalFiltration x)
    (fun _ _ hst g => condExp_modifiedProcess_eq_wfSemigroup x hst g) hτ hF hFC

end

end MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMonotoneClass
