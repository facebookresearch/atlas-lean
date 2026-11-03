/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import MathlibExt.Biology.PopulationGenetics.Diffusion.SemigroupMoments
public import MathlibExt.Biology.PopulationGenetics.Diffusion.TransitionKernel
public import MathlibExt.Probability.KolmogorovContinuousModification
public import MathlibExt.Probability.MarkovSemigroupProjective

/-!
# Raw neutral Wright--Fisher process and continuous modification

This file specializes the canonical Markov-semigroup construction to the
neutral Wright--Fisher transition kernel.  It proves an explicit fourth-moment
Kolmogorov bound and selects a continuous `[0,1]`-valued modification whose
initial value is deterministic on every sample.

Finite-dimensional laws are transferred to the modified process one finite
set of times at a time.  No equality between raw and modified natural
filtrations is asserted.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory unitInterval

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw

open MathlibExt.Probability.MarkovSemigroupProjective
open MathlibExt.Probability.KolmogorovContinuousModification
open WrightFisherSemigroup
open Polynomial

noncomputable section

/-- Canonical sample paths before continuous modification. -/
abbrev SamplePath := NNReal → I

/-- The neutral Wright--Fisher transition kernel at nonnegative time. -/
noncomputable def neutralKernel (t : NNReal) : Kernel I I :=
  wfTransitionKernel (t : ℝ)

noncomputable instance neutralKernel.instIsMarkovKernel (t : NNReal) :
    IsMarkovKernel (neutralKernel t) := by
  unfold neutralKernel
  infer_instance

@[simp]
theorem neutralKernel_zero : neutralKernel 0 = (Kernel.id : Kernel I I) := by
  simp [neutralKernel]

/-- Chapman--Kolmogorov for the nonnegative-time specialization. -/
theorem neutralKernel_add (s t : NNReal) :
    neutralKernel (s + t) = neutralKernel t ∘ₖ neutralKernel s := by
  simpa only [neutralKernel, NNReal.coe_add] using
    (wfTransitionKernel_add (s := (s : ℝ)) (t := (t : ℝ))
      s.coe_nonneg t.coe_nonneg)

/-- The canonical probability measure on `NNReal → I`. -/
noncomputable def rawMeasure (x : I) : Measure SamplePath :=
  pathMeasure neutralKernel neutralKernel_add x

noncomputable instance rawMeasure.instIsProbabilityMeasure (x : I) :
    IsProbabilityMeasure (rawMeasure x) := by
  unfold rawMeasure
  infer_instance

/-- The raw real-valued coordinate process, normalized at time zero on every
sample rather than merely almost surely. -/
noncomputable def rawProcess (x : I) (t : NNReal) (ω : SamplePath) : ℝ :=
  if t = 0 then x else ω t

@[simp]
theorem rawProcess_zero (x : I) (ω : SamplePath) :
    rawProcess x 0 ω = x := by
  simp [rawProcess]

theorem measurable_rawProcess (x : I) (t : NNReal) :
    Measurable (rawProcess x t) := by
  by_cases ht : t = 0
  · subst t
    have h : rawProcess x 0 = fun _ : SamplePath => (x : ℝ) :=
      funext (rawProcess_zero x)
    rw [h]
    fun_prop
  · change Measurable (fun ω : SamplePath =>
      if t = 0 then (x : ℝ) else ((ω t : I) : ℝ))
    simp only [ht, ↓reduceIte]
    fun_prop

theorem rawProcess_mem_Icc (x : I) (t : NNReal) (ω : SamplePath) :
    rawProcess x t ω ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases ht : t = 0
  · change (if t = 0 then (x : ℝ) else ((ω t : I) : ℝ)) ∈ _
    simp only [ht, ↓reduceIte]
    exact x.property
  · change (if t = 0 then (x : ℝ) else ((ω t : I) : ℝ)) ∈ _
    simp only [ht, ↓reduceIte]
    exact (ω t).property

private theorem map_zero_finiteChainLaw
    (K : NNReal → Kernel I I) [∀ t, IsMarkovKernel (K t)]
    (x : I) (s t : NNReal) :
    (finiteChainLaw K x s (fun _ : Fin 1 => t)).map (fun z => z 0) =
      K (t - s) x := by
  rw [finiteChainLaw, finiteChainKernel]
  rw [Kernel.map_apply _
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 1 => I) 0).symm.measurable]
  rw [Measure.map_map (by fun_prop)
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin 1 => I) 0).symm.measurable]
  have hcomp :
      (fun z : Fin 1 → I => z 0) ∘
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin 1 => I) 0).symm = Prod.fst := by
    funext z
    rfl
  rw [hcomp]
  change Kernel.fst
    (K (t - s) ⊗ₖ Kernel.prodMkLeft I
      (finiteChainKernel K t fun i => Fin.elim0 i)) x = _
  rw [Kernel.fst_compProd]

private theorem finiteChainKernel_map_zero
    (K : NNReal → Kernel I I) [∀ t, IsMarkovKernel (K t)]
    (s t : NNReal) :
    (finiteChainKernel K s (fun _ : Fin 1 => t)).map (fun z => z 0) =
      K (t - s) := by
  apply Kernel.ext
  intro x
  rw [Kernel.map_apply _ (by fun_prop)]
  exact map_zero_finiteChainLaw K x s t

private theorem map_pair_finiteChainLaw
    (K : NNReal → Kernel I I) [∀ t, IsMarkovKernel (K t)]
    (x : I) (s t : NNReal) :
    (finiteChainLaw K x 0 (Fin.cases s fun _ : Fin 1 => t)).map
        (fun z => (z 0, z 1)) =
      (K s x) ⊗ₘ K (t - s) := by
  rw [finiteChainLaw, finiteChainKernel]
  rw [Kernel.map_apply _
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => I) 0).symm.measurable]
  rw [Measure.map_map (by fun_prop)
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin 2 => I) 0).symm.measurable]
  have hcomp :
      (fun z : Fin 2 → I => (z 0, z 1)) ∘
          (MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin 2 => I) 0).symm =
        Prod.map id (fun z : Fin 1 → I => z 0) := by
    funext z
    ext <;> rfl
  rw [hcomp]
  rw [← Kernel.map_apply _ (measurable_id.prodMap (by fun_prop))]
  rw [Kernel.compProd_prodMkLeft_eq_comp, Kernel.map_comp,
    ← Kernel.map_prod_map _ _ measurable_id (by fun_prop),
    Kernel.map_id]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [finiteChainKernel_map_zero,
    ← Kernel.compProd_prodMkLeft_eq_comp]
  simp only [tsub_zero]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.sectR_prodMkLeft]

/-- One-time marginals of the canonical raw path measure. -/
theorem map_eval_rawMeasure (x : I) (t : NNReal) :
    (rawMeasure x).map (fun ω => ω t) = neutralKernel t x := by
  let J : Finset NNReal := {t}
  let jt : J := ⟨t, by simp [J]⟩
  let i0 : Fin J.card := (J.orderIsoOfFin rfl).symm jt
  let e : Fin 1 → Fin J.card := fun _ => i0
  have he : StrictMono e := by
    intro a b hab
    omega
  have htime :
      (fun k : Fin 1 => J.orderEmbOfFin rfl (e k)) =
        (fun _ : Fin 1 => t) := by
    funext k
    change J.orderEmbOfFin rfl i0 = t
    exact congrArg Subtype.val
      ((J.orderIsoOfFin rfl).apply_symm_apply jt)
  have hreindex :=
    finiteChainLaw_map_strictMono neutralKernel neutralKernel_add x
      (J.orderEmbOfFin rfl) (fun _ => bot_le)
      (J.orderEmbOfFin rfl).strictMono e he
  have hfinite :
      (finiteLaw neutralKernel x J).map (fun z => z jt) =
        neutralKernel t x := by
    unfold finiteLaw
    rw [Measure.map_map (measurable_pi_apply jt)
      (orderMeasurableEquiv J).measurable]
    change (finiteChainLaw neutralKernel x 0
      (J.orderEmbOfFin rfl)).map (fun z => z i0) = _
    calc
      (finiteChainLaw neutralKernel x 0
          (J.orderEmbOfFin rfl)).map (fun z => z i0) =
          ((finiteChainLaw neutralKernel x 0
            (J.orderEmbOfFin rfl)).map
              (fun z k => z (e k))).map (fun z => z 0) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = (finiteChainLaw neutralKernel x 0
          (fun k => J.orderEmbOfFin rfl (e k))).map
            (fun z => z 0) := by
        simpa using congrArg
          (fun μ : Measure (Fin 1 → I) => μ.map (fun z => z 0))
          hreindex
      _ = (finiteChainLaw neutralKernel x 0
          (fun _ : Fin 1 => t)).map (fun z => z 0) := by
        rw [htime]
      _ = neutralKernel t x := by
        simpa using map_zero_finiteChainLaw neutralKernel x 0 t
  calc
    (rawMeasure x).map (fun ω => ω t) =
        ((rawMeasure x).map J.restrict).map (fun z => z jt) := by
      convert (Measure.map_map (μ := rawMeasure x)
        (measurable_pi_apply jt)
        (Finset.measurable_restrict J)).symm using 1
      congr 1
    _ = (finiteLaw neutralKernel x J).map (fun z => z jt) := by
      rw [rawMeasure, map_restrict_pathMeasure]
    _ = neutralKernel t x := hfinite

/-- The time-zero coordinate of the canonical path law is the prescribed
initial state. -/
theorem map_eval_zero_rawMeasure (x : I) :
    (rawMeasure x).map (fun ω => ω 0) = Measure.dirac x := by
  rw [map_eval_rawMeasure, neutralKernel_zero, Kernel.id_apply]

/-- The ordered two-time law is the first marginal followed by the
transition over the time gap. -/
theorem map_pair_rawMeasure_of_lt (x : I) {s t : NNReal} (hst : s < t) :
    (rawMeasure x).map (fun ω => (ω s, ω t)) =
      (neutralKernel s x) ⊗ₘ neutralKernel (t - s) := by
  let J : Finset NNReal := {s, t}
  let js : J := ⟨s, by simp [J]⟩
  let jt : J := ⟨t, by simp [J]⟩
  let is : Fin J.card := (J.orderIsoOfFin rfl).symm js
  let it : Fin J.card := (J.orderIsoOfFin rfl).symm jt
  have hisit : is < it := (J.orderIsoOfFin rfl).symm.strictMono hst
  let e : Fin 2 → Fin J.card := Fin.cases is fun _ : Fin 1 => it
  have he : StrictMono e := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hisit
  have htime :
      (fun k : Fin 2 => J.orderEmbOfFin rfl (e k)) =
        Fin.cases s (fun _ : Fin 1 => t) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · change J.orderEmbOfFin rfl is = s
      exact congrArg Subtype.val
        ((J.orderIsoOfFin rfl).apply_symm_apply js)
    · have hi : i = 0 := Fin.eq_zero i
      subst i
      change J.orderEmbOfFin rfl it = t
      exact congrArg Subtype.val
        ((J.orderIsoOfFin rfl).apply_symm_apply jt)
  have hreindex :=
    finiteChainLaw_map_strictMono neutralKernel neutralKernel_add x
      (J.orderEmbOfFin rfl) (fun _ => bot_le)
      (J.orderEmbOfFin rfl).strictMono e he
  have hfinite :
      (finiteLaw neutralKernel x J).map (fun z => (z js, z jt)) =
        (neutralKernel s x) ⊗ₘ neutralKernel (t - s) := by
    unfold finiteLaw
    rw [Measure.map_map (by fun_prop)
      (orderMeasurableEquiv J).measurable]
    change (finiteChainLaw neutralKernel x 0
      (J.orderEmbOfFin rfl)).map (fun z => (z is, z it)) = _
    calc
      (finiteChainLaw neutralKernel x 0
          (J.orderEmbOfFin rfl)).map (fun z => (z is, z it)) =
          ((finiteChainLaw neutralKernel x 0
            (J.orderEmbOfFin rfl)).map
              (fun z k => z (e k))).map
                (fun z => (z 0, z 1)) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = (finiteChainLaw neutralKernel x 0
          (fun k => J.orderEmbOfFin rfl (e k))).map
            (fun z => (z 0, z 1)) := by
        simpa using congrArg
          (fun μ : Measure (Fin 2 → I) =>
            μ.map (fun z => (z 0, z 1))) hreindex
      _ = (finiteChainLaw neutralKernel x 0
          (Fin.cases s fun _ : Fin 1 => t)).map
            (fun z => (z 0, z 1)) := by
        rw [htime]
      _ = (neutralKernel s x) ⊗ₘ neutralKernel (t - s) :=
        map_pair_finiteChainLaw neutralKernel x s t
  calc
    (rawMeasure x).map (fun ω => (ω s, ω t)) =
        ((rawMeasure x).map J.restrict).map
          (fun z => (z js, z jt)) := by
      convert (Measure.map_map (μ := rawMeasure x)
        ((measurable_pi_apply js).prodMk (measurable_pi_apply jt))
        (Finset.measurable_restrict J)).symm using 1
      congr 1
    _ = (finiteLaw neutralKernel x J).map
          (fun z => (z js, z jt)) := by
      rw [rawMeasure, map_restrict_pathMeasure]
    _ = (neutralKernel s x) ⊗ₘ neutralKernel (t - s) := hfinite

theorem ae_eval_zero_eq (x : I) :
    (fun ω : SamplePath => ω 0) =ᵐ[rawMeasure x] fun _ => x := by
  apply HasLaw.ae_eq_of_dirac
  exact ⟨(measurable_pi_apply 0).aemeasurable, map_eval_zero_rawMeasure x⟩

/-- Exact normalization changes no fixed-time law. -/
theorem rawProcess_ae_eq_coordinate (x : I) (t : NNReal) :
    rawProcess x t =ᵐ[rawMeasure x] fun ω => ((ω t : I) : ℝ) := by
  by_cases ht : t = 0
  · subst t
    filter_upwards [ae_eval_zero_eq x] with ω hω
    rw [rawProcess_zero, hω]
  · exact Filter.Eventually.of_forall fun ω => by
      change (if t = 0 then (x : ℝ) else ((ω t : I) : ℝ)) = _
      simp only [ht, ↓reduceIte]

private theorem lintegral_neutralKernel_fourth (u : NNReal) (y : I) :
    ∫⁻ z, ENNReal.ofReal (((z : ℝ) - (y : ℝ)) ^ 4)
        ∂neutralKernel u y =
      ENNReal.ofReal
        (wfSemigroup (u : ℝ)
          (((Polynomial.X - Polynomial.C (y : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) y) := by
  let f : I → ℝ := fun z => ((z : ℝ) - (y : ℝ)) ^ 4
  have hf_meas : AEStronglyMeasurable f (neutralKernel u y) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hf_bound : ∀ᵐ z ∂neutralKernel u y, ‖f z‖ ≤ 1 :=
    Filter.Eventually.of_forall fun z => by
      have habs : |(z : ℝ) - (y : ℝ)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [z.property.1, z.property.2,
          y.property.1, y.property.2]
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) habs
  have hf_int : Integrable f (neutralKernel u y) :=
    Integrable.of_bound hf_meas 1 hf_bound
  have hf_nonneg : 0 ≤ᵐ[neutralKernel u y] f :=
    Filter.Eventually.of_forall fun _ => by positivity
  have hf_eq : f = fun z =>
      (((Polynomial.X - Polynomial.C (y : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) z := by
    funext z
    simp [f]
  have hf_integral :
      ∫ z, f z ∂neutralKernel u y =
        wfSemigroup (u : ℝ)
          (((Polynomial.X - Polynomial.C (y : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) y := by
    rw [hf_eq, neutralKernel]
    exact integral_wfTransitionKernel (u : ℝ)
      (((Polynomial.X - Polynomial.C (y : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) y
  calc
    (∫⁻ z, ENNReal.ofReal (((z : ℝ) - (y : ℝ)) ^ 4)
        ∂neutralKernel u y) = ENNReal.ofReal (∫ z, f z ∂neutralKernel u y) :=
      (ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg).symm
    _ = ENNReal.ofReal
        (wfSemigroup (u : ℝ)
          (((Polynomial.X - Polynomial.C (y : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) y) := by
      rw [hf_integral]

private theorem lintegral_neutralKernel_fourth_le (u : NNReal) (y : I) :
    ∫⁻ z, ENNReal.ofReal (((z : ℝ) - (y : ℝ)) ^ 4)
        ∂neutralKernel u y ≤
      ENNReal.ofReal ((3 / 16 : ℝ) * (u : ℝ) ^ 2) := by
  rw [lintegral_neutralKernel_fourth]
  exact ENNReal.ofReal_le_ofReal
    (wfSemigroup_fourth_increment_le u.coe_nonneg y)

private theorem lintegral_coordinate_fourth_le_of_lt
    (x : I) {s t : NNReal} (hst : s < t) :
    ∫⁻ ω, ENNReal.ofReal
        ((((ω t : I) : ℝ) - ((ω s : I) : ℝ)) ^ 4) ∂rawMeasure x ≤
      ENNReal.ofReal ((3 / 16 : ℝ) * ((t - s : NNReal) : ℝ) ^ 2) := by
  let g : I × I → ENNReal := fun p =>
    ENNReal.ofReal (((p.2 : ℝ) - (p.1 : ℝ)) ^ 4)
  have hg : Measurable g := by
    apply ENNReal.measurable_ofReal.comp
    fun_prop
  calc
    (∫⁻ ω, ENNReal.ofReal
        ((((ω t : I) : ℝ) - ((ω s : I) : ℝ)) ^ 4) ∂rawMeasure x) =
        ∫⁻ p, g p ∂(rawMeasure x).map (fun ω => (ω s, ω t)) := by
      rw [lintegral_map hg ((measurable_pi_apply s).prodMk
        (measurable_pi_apply t))]
    _ = ∫⁻ p, g p ∂((neutralKernel s x) ⊗ₘ neutralKernel (t - s)) := by
      rw [map_pair_rawMeasure_of_lt x hst]
    _ = ∫⁻ y, ∫⁻ z, ENNReal.ofReal
          (((z : ℝ) - (y : ℝ)) ^ 4) ∂neutralKernel (t - s) y
        ∂neutralKernel s x := by
      rw [Measure.lintegral_compProd hg]
    _ ≤ ∫⁻ _y : I,
          ENNReal.ofReal ((3 / 16 : ℝ) * ((t - s : NNReal) : ℝ) ^ 2)
        ∂neutralKernel s x :=
      lintegral_mono fun y => lintegral_neutralKernel_fourth_le (t - s) y
    _ = ENNReal.ofReal
          ((3 / 16 : ℝ) * ((t - s : NNReal) : ℝ) ^ 2) := by
      simp

private theorem lintegral_rawProcess_fourth_le_of_lt
    (x : I) {s t : NNReal} (hst : s < t) :
    ∫⁻ ω, ENNReal.ofReal ((rawProcess x t ω - rawProcess x s ω) ^ 4)
        ∂rawMeasure x ≤
      ENNReal.ofReal ((3 / 16 : ℝ) * ((t - s : NNReal) : ℝ) ^ 2) := by
  calc
    (∫⁻ ω, ENNReal.ofReal ((rawProcess x t ω - rawProcess x s ω) ^ 4)
        ∂rawMeasure x) =
        ∫⁻ ω, ENNReal.ofReal
          ((((ω t : I) : ℝ) - ((ω s : I) : ℝ)) ^ 4) ∂rawMeasure x := by
      apply lintegral_congr_ae
      filter_upwards [rawProcess_ae_eq_coordinate x s,
        rawProcess_ae_eq_coordinate x t] with ω hs ht
      rw [hs, ht]
    _ ≤ ENNReal.ofReal
        ((3 / 16 : ℝ) * ((t - s : NNReal) : ℝ) ^ 2) :=
      lintegral_coordinate_fourth_le_of_lt x hst

private theorem edist_rpow_four_eq_ofReal_sub_pow (a b : ℝ) :
    edist a b ^ (4 : ℝ) = ENNReal.ofReal ((a - b) ^ 4) := by
  change edist a b ^ ((4 : ℕ) : ℝ) = _
  rw [ENNReal.rpow_natCast, edist_dist, Real.dist_eq,
    ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
    abs_of_nonneg (by positivity : 0 ≤ (a - b) ^ 4)]

/-- The explicit Kolmogorov constant `3/16`. -/
def kolmogorovConstant : NNReal := ⟨3 / 16, by positivity⟩

private theorem kolmogorov_rhs_eq (s t : NNReal) (hst : s ≤ t) :
    ENNReal.ofReal ((3 / 16 : ℝ) * ((t - s : NNReal) : ℝ) ^ 2) =
      (kolmogorovConstant : ENNReal) * edist s t ^ (2 : ℝ) := by
  change _ = (kolmogorovConstant : ENNReal) *
    edist s t ^ ((2 : ℕ) : ℝ)
  rw [ENNReal.rpow_natCast, edist_nndist, NNReal.nndist_eq,
    tsub_eq_zero_of_le hst,
    max_eq_right (show (0 : NNReal) ≤ t - s from bot_le),
    ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_coe_nnreal]
  change ENNReal.ofReal (kolmogorovConstant : ℝ) * _ = _
  rw [ENNReal.ofReal_coe_nnreal]

private theorem kolmogorovCondition_rawProcess_of_lt
    (x : I) {s t : NNReal} (hst : s < t) :
    ∫⁻ ω, edist (rawProcess x s ω) (rawProcess x t ω) ^ (4 : ℝ)
        ∂rawMeasure x ≤
      (kolmogorovConstant : ENNReal) * edist s t ^ (2 : ℝ) := by
  calc
    (∫⁻ ω, edist (rawProcess x s ω) (rawProcess x t ω) ^ (4 : ℝ)
        ∂rawMeasure x) =
        ∫⁻ ω, ENNReal.ofReal
          ((rawProcess x t ω - rawProcess x s ω) ^ 4) ∂rawMeasure x := by
      apply lintegral_congr
      intro ω
      rw [edist_comm, edist_rpow_four_eq_ofReal_sub_pow]
    _ ≤ ENNReal.ofReal
        ((3 / 16 : ℝ) * ((t - s : NNReal) : ℝ) ^ 2) :=
      lintegral_rawProcess_fourth_le_of_lt x hst
    _ = (kolmogorovConstant : ENNReal) * edist s t ^ (2 : ℝ) :=
      kolmogorov_rhs_eq s t hst.le

/-- The normalized raw coordinate process satisfies the explicit fourth-moment
Kolmogorov condition with `p=4`, `q=2`, and `M=3/16`. -/
theorem isKolmogorovProcess_rawProcess (x : I) :
    IsKolmogorovProcess (rawProcess x) (rawMeasure x) 4 2
      kolmogorovConstant := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology
  · exact measurable_rawProcess x
  · intro s t
    rcases lt_trichotomy s t with hst | rfl | hts
    · exact kolmogorovCondition_rawProcess_of_lt x hst
    · simp
    · simpa only [edist_comm] using
        kolmogorovCondition_rawProcess_of_lt x hts
  · norm_num
  · norm_num

/-- A selected continuous modification of the raw Wright--Fisher process,
with all pathwise properties stated on every sample. -/
structure ContinuousRealization (x : I) where
  /-- The modified real-valued process. -/
  process : NNReal → SamplePath → ℝ
  /-- Every time coordinate is measurable. -/
  measurable : ∀ t, Measurable (process t)
  /-- Every sample path is continuous. -/
  continuous : ∀ ω, Continuous fun t => process t ω
  /-- Fixed-time almost-everywhere agreement with the normalized raw process. -/
  ae_eq_raw : ∀ t, process t =ᵐ[rawMeasure x] rawProcess x t
  /-- The initial value is exact on every sample. -/
  initial : ∀ ω, process 0 ω = x
  /-- Every value lies in the allele-frequency interval. -/
  mem_Icc : ∀ t ω, process t ω ∈ Set.Icc (0 : ℝ) 1

/-- The continuous modification selected by Kolmogorov's theorem. -/
noncomputable def continuousRealization (x : I) : ContinuousRealization x := by
  let h := exists_continuous_modification
    (isKolmogorovProcess_rawProcess x) (by norm_num : (1 : ℝ) < 2)
  let Y := Classical.choose h
  have hY := Classical.choose_spec h
  refine ⟨Y, hY.1, hY.2.1, hY.2.2.1, ?_, ?_⟩
  · intro ω
    change Classical.choose h 0 ω = (x : ℝ)
    rw [hY.2.2.2.1, rawProcess_zero]
  · intro t ω
    change Classical.choose h t ω ∈ Set.Icc (0 : ℝ) 1
    exact hY.2.2.2.2 (Set.Icc (0 : ℝ) 1) isClosed_Icc ω
      (fun s => rawProcess_mem_Icc x s ω) t

/-- The concrete continuous process used by the final realization. -/
noncomputable def modifiedProcess (x : I) : NNReal → SamplePath → ℝ :=
  (continuousRealization x).process

theorem measurable_modifiedProcess (x : I) (t : NNReal) :
    Measurable (modifiedProcess x t) :=
  (continuousRealization x).measurable t

theorem continuous_modifiedProcess (x : I) (ω : SamplePath) :
    Continuous fun t => modifiedProcess x t ω :=
  (continuousRealization x).continuous ω

theorem modifiedProcess_ae_eq_raw (x : I) (t : NNReal) :
    modifiedProcess x t =ᵐ[rawMeasure x] rawProcess x t :=
  (continuousRealization x).ae_eq_raw t

@[simp]
theorem modifiedProcess_zero (x : I) (ω : SamplePath) :
    modifiedProcess x 0 ω = x :=
  (continuousRealization x).initial ω

theorem modifiedProcess_mem_Icc (x : I) (t : NNReal) (ω : SamplePath) :
    modifiedProcess x t ω ∈ Set.Icc (0 : ℝ) 1 :=
  (continuousRealization x).mem_Icc t ω

/-- The modified process has the raw finite-dimensional laws, proved on each
finite set by intersecting its fixed-time modification events. -/
theorem map_restrict_modified_eq_raw (x : I) (J : Finset NNReal) :
    (rawMeasure x).map
        (fun ω => J.restrict (fun t => modifiedProcess x t ω)) =
      (rawMeasure x).map
        (fun ω => J.restrict (fun t => rawProcess x t ω)) :=
  ProbabilityTheory.map_restrict_eq_of_forall_ae_eq
    (modifiedProcess_ae_eq_raw x) J

/-- The modified finite-dimensional laws also equal the original canonical
coordinate laws after coercion from `I` to `ℝ`. -/
theorem map_restrict_modified_eq_coordinate (x : I) (J : Finset NNReal) :
    (rawMeasure x).map
        (fun ω => J.restrict (fun t => modifiedProcess x t ω)) =
      (rawMeasure x).map
        (fun ω => J.restrict (fun t => ((ω t : I) : ℝ))) := by
  exact ProbabilityTheory.map_restrict_eq_of_forall_ae_eq
    (fun t => (modifiedProcess_ae_eq_raw x t).trans
      (rawProcess_ae_eq_coordinate x t)) J

end

end MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
