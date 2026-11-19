/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.StochasticSIRKurtz
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Independence.InfinitePi
import MathlibExt.Probability.Distributions.GammaLIntegral

/-!
# Pathwise construction of the stochastic SIR chain

`MathlibExt.Biology.Epidemiology.StochasticSIRKurtz` proves Kurtz's law of large numbers for
the stochastic SIR epidemic, taking the chain as a hypothesis (`hchain`): a family of paths that
solve the random time-change equations `IsChainPath` almost surely. This file constructs such
paths from the unit Poisson clocks and identifies their law with the continuous-time Markov
chain of `MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`.

## The construction

A unit clock is given by its interarrival times `e 0, e 1, …`; its counting path is
`clockCount e u = #{n | e 0 + ⋯ + e n ≤ u}` (`PoissonProcess.count`). The chain is built jump by
jump, by the "next reaction" recursion: each channel (infection, recovery) keeps a residual
internal time until its clock next rings. From state `x`, with channel rates `a = β S I / N`
and `b = γ I` and residuals `r₁, r₂`, channel `1` rings first when `b r₁ < a r₂`, after time
`r₁ / a`; the other channel's residual drops by the internal time it consumed, and the channel
that rang draws its next interarrival time. When both ring at the same instant (a null event for
independent clocks, but possible for dependent ones) both fire. The recursion is set up for any
two-channel chain (`TwoChannel`); the SIR epidemic is `sirChannels`. The jumps are written as
steps of the jump-chain construction of `ProbabilityTheory.ctmcPath`, so the path is a
`ctmcPath` (`TwoChannel.path`).

## Main definitions

* `TwoChannel`, `TwoChannel.rateMatrix`: two-channel chains on a finite state space and their
  rate matrices; `TwoChannel.next`, `TwoChannel.hold`, `TwoChannel.nextClock`: one jump.
* `TwoChannel.path`: the path of the chain driven by a clock configuration (`ClockConfig`).
* `clockMeasure`, `clockLaw`: the laws of independent rate-`1` exponential clocks.
* `sirChannels`: the SIR epidemic as a two-channel chain on `SIRState N = Fin (N+1) × Fin (N+1)`.
* `sirPath`, `sirS`, `sirI`, `sirR`: the constructed SIR path and its counts, driven by unit
  clocks with interarrival times `e₁` (infection) and `e₂` (recovery).

## Main results

* `isChainPath_sir`: **pathwise existence**. For all positive interarrival times `e₁`, `e₂`,
  dependent or not, and every initial state with `S₀ + I₀ ≤ N`, the constructed counts solve the
  time-change equations `IsChainPath β γ N (clockCount e₁) (clockCount e₂) S I R` for all
  `t ≥ 0`. The chain is absorbed after at most `2 N` jumps (`sir_exists_absorbing`), so the
  paths are defined for all times.
* `ae_isChainPath_sir`: the same for almost every outcome of two independent unit Poisson
  clocks (`clockLaw`, under which both counting paths are unit-rate Poisson processes,
  `isPoissonProcess_clockCount_fst`, `isPoissonProcess_clockCount_snd`). This gives a
  non-trivial instance of the `hchain` hypothesis of Kurtz's theorem.
* `TwoChannel.IsValid.map_path`, `map_sirPath`: **law identification**. Driven by independent
  rate-`1` exponential clocks, the constructed path has the law, on the path space `ℝ≥0 → ι`
  with its product σ-algebra, of `ctmcPath` under `ctmcInputMeasure`: the continuous-time
  Markov chain with the same rate matrix built from the jump chain and holding times.
  `map_sirPath_of_hasLaw` states it on any probability space.
* `TwoChannel.IsValid.clockMeasure_real_path_fdd`, `clockLaw_real_sirPath_eq`: consequently the
  finite-dimensional distributions of the constructed chain are products of `exp (t Q)`.

## Proof of the law identification

The proof is a coupling. Auxiliary i.i.d. steps fill in the coordinates of the jump-chain steps
that the clocks do not determine (the random map `ξ` away from the current state, and the clock
at absorbing states). The key lemma `TwoChannel.IsValid.map_firstStep` says that the first
step read off the clocks has the step law and is independent of the restarted input, which has
the input law again. Its core is the joint law of competing exponential clocks
(`lintegral_competing`): on the event that channel `1` rings first, the total clock and the
overshoot of channel `2` are independent rate-`1` exponentials. Induction over initial segments
then identifies the law of the whole step sequence with `ctmcInputMeasure`
(`TwoChannel.IsValid.map_steps`), and the paths coincide pathwise
(`TwoChannel.ctmcPath_steps`).

## Scope

* Existence is pathwise and uses only positivity of the interarrival times; it holds for
  dependent clocks. The law identification needs independent exponential clocks: with a single
  clock driving both channels the first jump can be a simultaneous infection and recovery,
  which the jump chain makes with probability `0` (see the tests).
* The clocks are the canonical counting processes of exponential interarrival times. A general
  `IsPoissonProcess` only fixes finite-dimensional distributions, not path regularity, so the
  construction is not stated for it.
* The law identification is for the path law on the product σ-algebra of `ℝ≥0 → ι`, as in
  `MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), ch. 6, §4.
* M. A. Gibson and J. Bruck, *Efficient exact stochastic simulation of chemical systems with
  many species and many channels*, J. Phys. Chem. A 104 (2000) 1876–1889.
* D. F. Anderson, *A modified next reaction method for simulating chemical systems with time
  dependent propensities and delays*, J. Chem. Phys. 127 (2007) 214107.
* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §2.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal

namespace MathlibExt.Biology.Epidemiology.StochasticSIR

/-! ### Sequences and their head/tail decomposition -/

section Seq

variable {α : Type*}

/-- The tail `(f 1, f 2, …)` of a sequence. -/
def seqTail (f : ℕ → α) : ℕ → α := fun n => f (n + 1)

@[fun_prop]
theorem measurable_seqTail [MeasurableSpace α] : Measurable (seqTail (α := α)) :=
  Measurable.of_eval fun n => measurable_pi_apply (n + 1)

variable [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

/-- Under an i.i.d. product law, the head and the tail of the sequence are independent, the
tail having the same law as the sequence. -/
theorem infinitePi_map_head_tail :
    (Measure.infinitePi fun _ : ℕ => μ).map (fun f => (f 0, seqTail f)) =
      μ.prod (Measure.infinitePi fun _ : ℕ => μ) := by
  set P := Measure.infinitePi fun _ : ℕ => μ
  have hind : IndepFun (fun f : ℕ → α => f 0) seqTail P := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ x => x)
      (fun _ => measurable_id)
    rw [iIndepFun_iff_iIndep] at h
    have hI := indep_iSup_of_disjoint (fun k => (measurable_pi_apply k).comap_le) h
      (S := Set.Iio 1) (T := Set.Ici 1)
      (Set.disjoint_left.mpr fun k hk hk' => absurd (Set.mem_Iio.mp hk) (not_lt.mpr hk'))
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI ?_) ?_
    · exact le_iSup₂ (f := fun k (_ : k ∈ Set.Iio 1) =>
        MeasurableSpace.comap (fun f : ℕ → α => f k) inferInstance) 0
        (Set.mem_Iio.mpr Nat.zero_lt_one)
    · rw [MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.pi]
      refine iSup_le fun j => ?_
      rw [← MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.comap_comp]
      exact le_iSup₂ (f := fun k (_ : k ∈ Set.Ici 1) =>
        MeasurableSpace.comap (fun f : ℕ → α => f k) inferInstance) (j + 1)
        (Set.mem_Ici.mpr (Nat.le_add_left 1 j))
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
    measurable_seqTail.aemeasurable).1 hind]
  congr 1
  · exact Measure.infinitePi_map_eval _ 0
  · exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ)
      (f := fun j => j + 1) (add_left_injective 1)

/-- Integrals against an i.i.d. product law, split into the head and the tail. -/
theorem lintegral_infinitePi_head_tail {G : α × (ℕ → α) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ f, G (f 0, seqTail f) ∂(Measure.infinitePi fun _ : ℕ => μ) =
      ∫⁻ a, ∫⁻ f, G (a, f) ∂(Measure.infinitePi fun _ : ℕ => μ) ∂μ := by
  rw [← lintegral_prod _ hG.aemeasurable, ← infinitePi_map_head_tail μ,
    lintegral_map hG ((measurable_pi_apply 0).prodMk measurable_seqTail)]

end Seq

/-! ### Updating one coordinate of a finite product law -/

section Update

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Resampling coordinate `x` of a product law from its marginal does not change the law. -/
theorem pi_map_update (x : ι) :
    ((μ x).prod (Measure.pi μ)).map (fun p => Function.update p.2 x p.1) = Measure.pi μ := by
  have hm : Measurable fun p : α x × (∀ i, α i) => Function.update p.2 x p.1 :=
    measurable_update'.comp (measurable_snd.prodMk measurable_fst)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : α x × (∀ i, α i) => Function.update p.2 x p.1) ⁻¹' Set.pi univ s =
      s x ×ˢ Set.pi univ (Function.update s x univ) := by
    ext ⟨z, ξ⟩
    simp only [mem_preimage, Set.mem_pi, mem_univ, forall_const, mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h x, fun i => ?_⟩
      by_cases hi : i = x
      · subst hi; simp
      · simpa [Function.update_of_ne hi] using h i
    · rintro ⟨hz, h⟩ i
      by_cases hi : i = x
      · subst hi; simpa using hz
      · simpa [Function.update_of_ne hi] using h i
  rw [hpre, Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ (fun i => μ i (s i)) (Finset.mem_univ x),
    ← Finset.mul_prod_erase Finset.univ (fun i => μ i (Function.update s x univ i))
      (Finset.mem_univ x)]
  simp only [Function.update_self, measure_univ, one_mul]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- Integrals against a product law, with coordinate `x` resampled from its marginal. -/
theorem lintegral_pi_update (x : ι) {G : (∀ i, α i) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ξ, G ξ ∂(Measure.pi μ) = ∫⁻ z, ∫⁻ ξ, G (Function.update ξ x z) ∂(Measure.pi μ) ∂(μ x) := by
  have hm : Measurable fun p : α x × (∀ i, α i) => Function.update p.2 x p.1 :=
    measurable_update'.comp (measurable_snd.prodMk measurable_fst)
  conv_lhs => rw [← pi_map_update μ x]
  rw [lintegral_map hG hm]
  exact lintegral_prod (fun p => G (Function.update p.2 x p.1)) (hG.comp hm).aemeasurable

end Update

/-! ### Competing exponential clocks -/

section Competing

/-- The density of the rate-`1` exponential law. -/
noncomputable def expDens (x : ℝ) : ℝ≥0∞ := if 0 ≤ x then ENNReal.ofReal (Real.exp (-x)) else 0

theorem measurable_expDens : Measurable expDens :=
  Measurable.ite measurableSet_Ici (ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp measurable_neg)) measurable_const

theorem lintegral_expMeasure_one {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(expMeasure 1) = ∫⁻ x, expDens x * f x := by
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ (f := gammaPDF 1 1)
    (measurable_gammaPDFReal 1 1).ennreal_ofReal hf]
  congr 1
  funext x
  have := exponentialPDF_eq 1 x
  simp only [exponentialPDF, exponentialPDFReal] at this
  simp only [Pi.mul_apply, gammaPDF, this, expDens, one_mul]
  split_ifs <;> simp

/-- **Competing exponential clocks, joint law.** Let `r₁, r₂` be independent rate-`1`
exponential clocks, run at speeds `a > 0` and `b ≥ 0`; channel `1` rings first when
`b r₁ < a r₂`, at time `h = r₁ / a`. On that event, the total clock `(a + b) h` and the
overshoot `r₂ - b h` of the other channel are again independent rate-`1` exponentials, and the
event has probability `a / (a + b)`. -/
theorem lintegral_competing {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) {φ : ℝ × ℝ → ℝ≥0∞}
    (hφ : Measurable φ) :
    ∫⁻ r, {r : ℝ × ℝ | b * r.1 < a * r.2}.indicator
        (fun r => φ ((a + b) * (r.1 / a), r.2 - b * (r.1 / a))) r
        ∂((expMeasure 1).prod (expMeasure 1)) =
      ENNReal.ofReal (a / (a + b)) * ∫⁻ p, φ p ∂((expMeasure 1).prod (expMeasure 1)) := by
  have hν : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  set S : Set (ℝ × ℝ) := {r | b * r.1 < a * r.2} with hS_def
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) (by fun_prop)
  set g : ℝ × ℝ → ℝ≥0∞ := fun r => φ ((a + b) * (r.1 / a), r.2 - b * (r.1 / a)) with hg_def
  have hg : Measurable g := hφ.comp (by fun_prop)
  set Φ : ℝ → ℝ≥0∞ := fun y => ∫⁻ s, φ (y, s) ∂(expMeasure 1) with hΦ_def
  have hΦ : Measurable Φ := hφ.lintegral_prod_right'
  have hind : Measurable (S.indicator g) := hg.indicator hS
  have hae0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
    rw [ae_iff]; simp
  have hinner : ∀ r₁, 0 ≤ r₁ → ∫⁻ r₂, S.indicator g (r₁, r₂) ∂(expMeasure 1) =
      ENNReal.ofReal (Real.exp (-(b * (r₁ / a)))) * Φ ((a + b) * (r₁ / a)) := by
    intro r₁ hr₁
    set d := b * (r₁ / a) with hd
    set y := (a + b) * (r₁ / a) with hy
    have hd0 : 0 ≤ d := mul_nonneg hb (div_nonneg hr₁ ha.le)
    have hsec : ∀ r₂, S.indicator g (r₁, r₂) = if d < r₂ then φ (y, r₂ - d) else 0 := by
      intro r₂
      have hmem : (r₁, r₂) ∈ S ↔ d < r₂ := by
        simp only [hS_def, mem_ofPred_eq, hd]
        rw [← mul_div_assoc, div_lt_iff₀ ha, mul_comm r₂ a]
      by_cases h : d < r₂
      · rw [Set.indicator_of_mem (hmem.2 h), ite_eq_left h]
      · rw [Set.indicator_of_notMem (fun h' => h (hmem.1 h')), ite_eq_right h]
    have hm : Measurable fun r₂ => S.indicator g (r₁, r₂) := hind.comp measurable_prodMk_left
    have hk : Measurable fun s => expDens s * (if 0 < s then φ (y, s) else 0) :=
      measurable_expDens.mul (Measurable.ite measurableSet_Ioi
        (hφ.comp measurable_prodMk_left) measurable_const)
    rw [lintegral_expMeasure_one hm]
    simp_rw [hsec]
    calc ∫⁻ r₂, expDens r₂ * (if d < r₂ then φ (y, r₂ - d) else 0)
        = ∫⁻ s, expDens (s + d) * (if d < s + d then φ (y, s + d - d) else 0) :=
          (lintegral_add_right_eq_self
            (fun r₂ => expDens r₂ * (if d < r₂ then φ (y, r₂ - d) else 0)) d).symm
      _ = ∫⁻ s, ENNReal.ofReal (Real.exp (-d)) *
            (expDens s * (if 0 < s then φ (y, s) else 0)) := by
          congr 1
          funext s
          by_cases hs : 0 < s
          · have hsd : 0 ≤ s + d := by linarith
            rw [ite_eq_left (by linarith), ite_eq_left hs, add_sub_cancel_right, expDens,
              ite_eq_left hsd, expDens, ite_eq_left hs.le, ← mul_assoc,
              ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_rev]
          · rw [ite_eq_right (by linarith), ite_eq_right hs]
            simp
      _ = ENNReal.ofReal (Real.exp (-d)) * Φ y := by
          rw [lintegral_const_mul _ hk, hΦ_def]
          dsimp only
          rw [lintegral_expMeasure_one (f := fun s => φ (y, s)) (hφ.comp measurable_prodMk_left)]
          congr 1
          refine lintegral_congr_ae (hae0.mono fun s hs => ?_)
          dsimp only
          by_cases hpos : 0 < s
          · rw [ite_eq_left hpos]
          · have hneg : s < 0 := lt_of_le_of_ne (not_lt.mp hpos) hs
            simp [expDens, not_le.mpr hneg]
  have hc : 0 < (a + b) / a := div_pos (by linarith) ha
  have houter : ∀ r₁, expDens r₁ * ∫⁻ r₂, S.indicator g (r₁, r₂) ∂(expMeasure 1) =
      expDens ((a + b) / a * r₁) * Φ ((a + b) / a * r₁) := by
    intro r₁
    have hy : (a + b) * (r₁ / a) = (a + b) / a * r₁ := by ring
    by_cases hr₁ : 0 ≤ r₁
    · rw [hinner r₁ hr₁, hy, ← mul_assoc]
      congr 1
      rw [expDens, ite_eq_left hr₁, expDens, ite_eq_left (mul_nonneg hc.le hr₁),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      field_simp
      ring
    · have hneg : (a + b) / a * r₁ < 0 := mul_neg_of_pos_of_neg hc (not_le.mp hr₁)
      simp [expDens, hr₁, not_le.mpr hneg]
  rw [lintegral_prod _ hind.aemeasurable, lintegral_expMeasure_one hind.lintegral_prod_right']
  simp_rw [houter]
  have hcv : ∫⁻ x, expDens ((a + b) / a * x) * Φ ((a + b) / a * x) =
      ENNReal.ofReal ((a + b) / a)⁻¹ * ∫⁻ y, expDens y * Φ y := by
    rw [ProbabilityTheory.lintegral_comp_mul_left_of_pos hc (fun y => expDens y * Φ y),
      ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne',
      ENNReal.ofReal_one, one_mul]
  rw [hcv, inv_div, ← lintegral_expMeasure_one hΦ, lintegral_prod _ hφ.aemeasurable]

end Competing

/-! ### Exponential clocks: null sets -/

section ExpNull

instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

instance : NullSingletonClass (expMeasure 1) := by
  unfold expMeasure gammaMeasure; infer_instance

/-- A rate-`1` exponential clock is nonpositive with probability `0`. -/
theorem expMeasure_Iic_zero : expMeasure 1 (Iic 0) = 0 := by
  rw [← lintegral_indicator_one measurableSet_Iic,
    lintegral_expMeasure_one (measurable_one.indicator measurableSet_Iic)]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  have hae0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hae0] with s hs
  by_cases h : s ≤ 0
  · simp [expDens, not_le.mpr (lt_of_le_of_ne h hs)]
  · simp [Set.indicator_of_notMem (show s ∉ Iic 0 from h)]

/-- A rate-`1` exponential clock is positive almost surely. -/
theorem ae_pos_expMeasure : ∀ᵐ s ∂(expMeasure 1), 0 < s := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext; simp
  rw [this]
  exact expMeasure_Iic_zero

/-- Measurability of a partial Lebesgue integral, in a form usable by `fun_prop`. -/
theorem measurable_lintegral_of_uncurry {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : Measurable fun p : α × β => f p.1 p.2) : Measurable fun x => ∫⁻ y, f x y ∂ν :=
  hf.lintegral_prod_right'

/-- For independent exponential clocks and speeds `a, b ≥ 0`, not both `0`, a tie
`a r₂ = b r₁` has probability `0`. -/
theorem prod_expMeasure_tie {a b : ℝ} (hab : 0 < a ∨ 0 < b) :
    ((expMeasure 1).prod (expMeasure 1)) {r : ℝ × ℝ | a * r.2 = b * r.1} = 0 := by
  have hS : MeasurableSet {r : ℝ × ℝ | a * r.2 = b * r.1} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  rcases hab with ha | hb
  · rw [Measure.prod_apply hS]
    refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun r₁ => ?_)
    have : Prod.mk r₁ ⁻¹' {r : ℝ × ℝ | a * r.2 = b * r.1} = {b * r₁ / a} := by
      ext r₂
      simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff]
      constructor
      · intro h; field_simp; linarith
      · intro h; rw [h]; field_simp
    simp [this]
  · rw [Measure.prod_apply_symm hS]
    refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun r₂ => ?_)
    have : (fun r₁ => (r₁, r₂)) ⁻¹' {r : ℝ × ℝ | a * r.2 = b * r.1} = {a * r₂ / b} := by
      ext r₁
      simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff]
      constructor
      · intro h; field_simp; linarith
      · intro h; rw [h]; field_simp
    simp [this]

/-- For a nonnegative speed `b`, the event `b r₁ < 0` has probability `0`. -/
theorem prod_expMeasure_neg {b : ℝ} (hb : 0 ≤ b) :
    ((expMeasure 1).prod (expMeasure 1)) {r : ℝ × ℝ | b * r.1 < 0 * r.2} = 0 := by
  refine measure_mono_null (t := Iic 0 ×ˢ univ) (fun r hr => ?_) ?_
  · simp only [mem_ofPred_eq, zero_mul] at hr
    exact ⟨by
      by_contra h
      exact absurd hr (not_lt.mpr (mul_nonneg hb (le_of_lt (not_le.mp h)))), mem_univ _⟩
  · rw [Measure.prod_prod, expMeasure_Iic_zero, zero_mul]

/-- For a nonnegative speed `a`, the event `a r₂ < 0` has probability `0`. -/
theorem prod_expMeasure_neg' {a : ℝ} (ha : 0 ≤ a) :
    ((expMeasure 1).prod (expMeasure 1)) {r : ℝ × ℝ | a * r.2 < 0 * r.1} = 0 := by
  refine measure_mono_null (t := univ ×ˢ Iic 0) (fun r hr => ?_) ?_
  · simp only [mem_ofPred_eq, zero_mul] at hr
    exact ⟨mem_univ _, by
      by_contra h
      exact absurd hr (not_lt.mpr (mul_nonneg ha (le_of_lt (not_le.mp h))))⟩
  · rw [Measure.prod_prod, expMeasure_Iic_zero, mul_zero]

end ExpNull

/-! ### Two-channel chains driven by unit clocks -/

/-- A **clock configuration** of a two-channel chain: the residual internal times `(r₁, r₂)`
until the next ring of each channel, and the future interarrival times `(u₁, u₂)` of each
channel's unit clock. -/
abbrev ClockConfig := (ℝ × ℝ) × ((ℕ → ℝ) × (ℕ → ℝ))

/-- The law of a clock configuration whose residuals and interarrivals are all independent
rate-`1` exponentials. -/
noncomputable def clockMeasure : Measure ClockConfig :=
  ((expMeasure 1).prod (expMeasure 1)).prod
    ((Measure.infinitePi fun _ : ℕ => expMeasure 1).prod
      (Measure.infinitePi fun _ : ℕ => expMeasure 1))

instance : IsProbabilityMeasure clockMeasure := by
  unfold clockMeasure; infer_instance

/-- A **two-channel chain** on a state space `ι`: in state `x`, channel `1` fires at rate
`rate₁ x` and moves the chain to `target₁ x`, channel `2` fires at rate `rate₂ x` and moves it
to `target₂ x`; `target₁₂ x` is the state reached when both channels fire at the same instant. -/
structure TwoChannel (ι : Type*) where
  /-- The rate of channel `1`. -/
  rate₁ : ι → ℝ
  /-- The rate of channel `2`. -/
  rate₂ : ι → ℝ
  /-- The state after a jump of channel `1`. -/
  target₁ : ι → ι
  /-- The state after a jump of channel `2`. -/
  target₂ : ι → ι
  /-- The state after simultaneous jumps of both channels. -/
  target₁₂ : ι → ι

namespace TwoChannel

variable {ι : Type*} (K : TwoChannel ι)

/-- A two-channel chain is **valid** if its rates are nonnegative and a channel whose jump
would not move the chain has rate `0`. -/
structure IsValid : Prop where
  /-- The rate of channel `1` is nonnegative. -/
  rate₁_nonneg : ∀ x, 0 ≤ K.rate₁ x
  /-- The rate of channel `2` is nonnegative. -/
  rate₂_nonneg : ∀ x, 0 ≤ K.rate₂ x
  /-- Channel `1` is inactive where its jump would not move the chain. -/
  rate₁_eq_zero : ∀ x, K.target₁ x = x → K.rate₁ x = 0
  /-- Channel `2` is inactive where its jump would not move the chain. -/
  rate₂_eq_zero : ∀ x, K.target₂ x = x → K.rate₂ x = 0

/-- The total jump rate out of `x`. -/
def totalRate (x : ι) : ℝ := K.rate₁ x + K.rate₂ x

/-- The time to the next jump from `x` with residual clocks `r`: channel `1` rings first when
`rate₂ x * r₁ < rate₁ x * r₂`, after time `r₁ / rate₁ x`, and symmetrically for channel `2`. -/
noncomputable def hold (x : ι) (r : ℝ × ℝ) : ℝ :=
  if K.rate₂ x * r.1 < K.rate₁ x * r.2 then r.1 / K.rate₁ x
  else if K.rate₁ x * r.2 < K.rate₂ x * r.1 then r.2 / K.rate₂ x
  else r.1 / K.rate₁ x

/-- The state after the next jump from `x` with residual clocks `r` (`x` itself when no channel
is active). -/
noncomputable def next (x : ι) (r : ℝ × ℝ) : ι :=
  if K.totalRate x = 0 then x
  else if K.rate₂ x * r.1 < K.rate₁ x * r.2 then K.target₁ x
  else if K.rate₁ x * r.2 < K.rate₂ x * r.1 then K.target₂ x
  else K.target₁₂ x

/-- The clock configuration after the next jump from `x`: a channel that fires draws its next
interarrival time, and the residual of a channel that does not fire decreases by the internal
time it has consumed. -/
noncomputable def nextClock (x : ι) (c : ClockConfig) : ClockConfig :=
  if K.totalRate x = 0 then c
  else if K.rate₂ x * c.1.1 < K.rate₁ x * c.1.2 then
    ((c.2.1 0, c.1.2 - K.rate₂ x * K.hold x c.1), (seqTail c.2.1, c.2.2))
  else if K.rate₁ x * c.1.2 < K.rate₂ x * c.1.1 then
    ((c.1.1 - K.rate₁ x * K.hold x c.1, c.2.2 0), (c.2.1, seqTail c.2.2))
  else ((c.2.1 0, c.2.2 0), (seqTail c.2.1, seqTail c.2.2))

/-- One jump of the chain together with its clocks. -/
noncomputable def step (p : ι × ClockConfig) : ι × ClockConfig :=
  (K.next p.1 p.2.1, K.nextClock p.1 p.2)

/-- The state and clocks after `n` jumps. -/
noncomputable def config (n : ℕ) (p : ι × ClockConfig) : ι × ClockConfig := K.step^[n] p

variable [DecidableEq ι]

/-- The rate matrix of the chain: `x → target₁ x` at rate `rate₁ x` and `x → target₂ x` at
rate `rate₂ x`. -/
def rateMatrix : Matrix ι ι ℝ := fun x y =>
  if y = x then -K.totalRate x
  else (if K.target₁ x = y then K.rate₁ x else 0) + (if K.target₂ x = y then K.rate₂ x else 0)

/-- The step of the jump-chain construction of `ProbabilityTheory.ctmcPath` read off one jump of
the clock chain: the map `ξ` sends the current state to the next one and agrees with the
auxiliary map `g.1` elsewhere; the exponential clock is the total rate times the holding time
(the auxiliary clock `g.2` when no channel is active). -/
noncomputable def output (p : ι × ClockConfig) (g : (ι → ι) × ℝ) : (ι → ι) × ℝ :=
  (Function.update g.1 p.1 (K.next p.1 p.2.1),
    if K.totalRate p.1 = 0 then g.2 else K.totalRate p.1 * K.hold p.1 p.2.1)

/-- The steps read off the clock chain started at `x` with clocks `w.1`, using the auxiliary
steps `w.2`. -/
noncomputable def steps (x : ι) (w : ClockConfig × (ℕ → (ι → ι) × ℝ)) :
    ℕ → (ι → ι) × ℝ :=
  fun n => K.output (K.config n (x, w.1)) (w.2 n)

/-- **The path of the clock chain** started at `x` with clock configuration `c`. -/
noncomputable def path (x : ι) (c : ClockConfig) (t : ℝ≥0) : ι :=
  ctmcPath K.rateMatrix x (K.steps x (c, fun _ => (id, 0))) t

variable {K}

theorem IsValid.isRateMatrix [Fintype ι] (hK : K.IsValid) : IsRateMatrix K.rateMatrix where
  nonneg_of_ne x y hxy := by
    simp only [rateMatrix, Ne.symm hxy, ↓reduceIte]
    exact add_nonneg (by split_ifs <;> simp [hK.rate₁_nonneg x])
      (by split_ifs <;> simp [hK.rate₂_nonneg x])
  sum_row x := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    simp only [rateMatrix, ↓reduceIte]
    rw [Finset.sum_congr rfl fun y hy => by rw [ite_eq_right (Finset.ne_of_mem_erase hy)],
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, totalRate]
    by_cases h₁ : K.target₁ x = x <;> by_cases h₂ : K.target₂ x = x <;>
      simp [h₁, h₂, hK.rate₁_eq_zero x, hK.rate₂_eq_zero x]

theorem rateMatrix_diag (x : ι) : K.rateMatrix x x = -K.totalRate x := by
  simp [rateMatrix]

/-- The jump matrix of a valid two-channel chain at an active state. -/
theorem IsValid.ctmcJumpMatrix_eq (hK : K.IsValid) {x : ι} (hx : K.totalRate x ≠ 0)
    (z : ι) : ctmcJumpMatrix K.rateMatrix x z =
      (if K.target₁ x = z then K.rate₁ x / K.totalRate x else 0) +
        (if K.target₂ x = z then K.rate₂ x / K.totalRate x else 0) := by
  have hd : K.rateMatrix x x ≠ 0 := by rw [rateMatrix_diag]; exact neg_ne_zero.mpr hx
  rw [ctmcJumpMatrix, ite_eq_right hd, rateMatrix_diag, neg_neg]
  by_cases hz : x = z
  · subst hz
    by_cases h₁ : K.target₁ x = x <;> by_cases h₂ : K.target₂ x = x <;>
      simp [h₁, h₂, hK.rate₁_eq_zero x, hK.rate₂_eq_zero x]
  · simp only [hz, ↓reduceIte, rateMatrix, Ne.symm hz]
    split_ifs <;> ring

/-- Integrals against a row of the jump matrix of a valid two-channel chain. -/
theorem IsValid.lintegral_ctmcJumpPMF [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (hK : K.IsValid) {x : ι} (hx : K.totalRate x ≠ 0) (ψ : ι → ℝ≥0∞) :
    ∫⁻ z, ψ z ∂(hK.isRateMatrix.ctmcJumpPMF x).toMeasure =
      ENNReal.ofReal (K.rate₁ x / K.totalRate x) * ψ (K.target₁ x) +
        ENNReal.ofReal (K.rate₂ x / K.totalRate x) * ψ (K.target₂ x) := by
  have hq : 0 ≤ K.totalRate x := add_nonneg (hK.rate₁_nonneg x) (hK.rate₂_nonneg x)
  have h₁ : 0 ≤ K.rate₁ x / K.totalRate x := div_nonneg (hK.rate₁_nonneg x) hq
  have h₂ : 0 ≤ K.rate₂ x / K.totalRate x := div_nonneg (hK.rate₂_nonneg x) hq
  rw [lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    IsRateMatrix.ctmcJumpPMF, PMF.ofFintype_apply, hK.ctmcJumpMatrix_eq hx]
  have : ∀ z, ENNReal.ofReal ((if K.target₁ x = z then K.rate₁ x / K.totalRate x else 0) +
      (if K.target₂ x = z then K.rate₂ x / K.totalRate x else 0)) =
      (if K.target₁ x = z then ENNReal.ofReal (K.rate₁ x / K.totalRate x) else 0) +
      (if K.target₂ x = z then ENNReal.ofReal (K.rate₂ x / K.totalRate x) else 0) := by
    intro z
    rw [ENNReal.ofReal_add (by split_ifs <;> simp [h₁]) (by split_ifs <;> simp [h₂])]
    congr 1 <;> split_ifs <;> simp
  simp only [this, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  ring

/-! #### Measurability -/

omit [DecidableEq ι] in
variable (K) in
theorem measurable_hold (x : ι) : Measurable (K.hold x) := by
  unfold hold
  refine Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)
    (Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop))

omit [DecidableEq ι] in
variable (K) in
theorem measurable_next [MeasurableSpace ι] (x : ι) : Measurable (K.next x) := by
  unfold next
  split_ifs
  · exact measurable_const
  · exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) measurable_const
      (Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) measurable_const
        measurable_const)

omit [DecidableEq ι] in
variable (K) in
theorem measurable_nextClock (x : ι) : Measurable (K.nextClock x) := by
  have hh := K.measurable_hold x
  unfold nextClock
  split_ifs
  · exact measurable_id
  · exact Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop)
      (Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop))

/-! #### One jump of the clocks -/

attribute [local fun_prop] measurable_lintegral_of_uncurry

/-- Integrals against `clockMeasure`, as iterated integrals over the four components. -/
theorem lintegral_clockMeasure {G : ClockConfig → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ c, G c ∂clockMeasure = ∫⁻ r₁, ∫⁻ r₂, ∫⁻ u₁, ∫⁻ u₂, G ((r₁, r₂), (u₁, u₂))
      ∂(Measure.infinitePi fun _ : ℕ => expMeasure 1)
      ∂(Measure.infinitePi fun _ : ℕ => expMeasure 1) ∂(expMeasure 1) ∂(expMeasure 1) := by
  rw [clockMeasure, lintegral_prod _ hG.aemeasurable, lintegral_prod _ (by fun_prop)]
  refine lintegral_congr fun r₁ => lintegral_congr fun r₂ => ?_
  exact lintegral_prod _ (by fun_prop)

/-- **One jump of the clocks from an active state.** If the clock configuration has law
`clockMeasure`, then the next state, the total clock `totalRate x * hold`, and the clock
configuration after the jump are independent, with laws the row of the jump matrix at `x`, the
rate-`1` exponential law, and `clockMeasure` again (competing exponential clocks and the
memoryless property). -/
theorem IsValid.map_clock [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (hK : K.IsValid) {x : ι} (hx : K.totalRate x ≠ 0) :
    clockMeasure.map (fun c => ((K.next x c.1, K.totalRate x * K.hold x c.1), K.nextClock x c)) =
      (((hK.isRateMatrix.ctmcJumpPMF x).toMeasure).prod (expMeasure 1)).prod clockMeasure := by
  set ν := expMeasure 1
  set μs := Measure.infinitePi fun _ : ℕ => ν
  set a := K.rate₁ x with ha_def
  set b := K.rate₂ x with hb_def
  have ha : 0 ≤ a := hK.rate₁_nonneg x
  have hb : 0 ≤ b := hK.rate₂_nonneg x
  have hq : K.totalRate x = a + b := rfl
  have hΓ : Measurable fun c : ClockConfig =>
      ((K.next x c.1, K.totalRate x * K.hold x c.1), K.nextClock x c) :=
    (((K.measurable_next x).comp measurable_fst).prodMk
      (((K.measurable_hold x).comp measurable_fst).const_mul _)).prodMk
      (K.measurable_nextClock x)
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF hΓ]
  -- the right-hand side
  set J : ι → ℝ≥0∞ := fun z => ∫⁻ E, ∫⁻ c, F ((z, E), c) ∂clockMeasure ∂ν with hJ
  have hRHS : ∫⁻ p, F p ∂((((hK.isRateMatrix.ctmcJumpPMF x).toMeasure).prod ν).prod
      clockMeasure) = ENNReal.ofReal (a / (a + b)) * J (K.target₁ x) +
        ENNReal.ofReal (b / (a + b)) * J (K.target₂ x) := by
    rw [lintegral_prod _ hF.aemeasurable, lintegral_prod _ (by fun_prop),
      hK.lintegral_ctmcJumpPMF hx]
    rfl
  rw [hRHS]
  -- the left-hand side, split according to the channel that rings first
  set I₁ : ℝ × ℝ → ℝ≥0∞ := fun p => ∫⁻ u, F ((K.target₁ x, p.1), ((u.1 0, p.2),
    (seqTail u.1, u.2))) ∂(μs.prod μs) with hI₁
  set I₂ : ℝ × ℝ → ℝ≥0∞ := fun p => ∫⁻ u, F ((K.target₂ x, p.1), ((p.2, u.2 0),
    (u.1, seqTail u.2))) ∂(μs.prod μs) with hI₂
  have hI₁m : Measurable I₁ := by fun_prop
  have hI₂m : Measurable I₂ := by fun_prop
  set S₁ : Set (ℝ × ℝ) := {r | b * r.1 < a * r.2} with hS₁
  set S₂ : Set (ℝ × ℝ) := {r | a * r.2 < b * r.1} with hS₂
  have hS₁m : MeasurableSet S₁ := measurableSet_lt (by fun_prop) (by fun_prop)
  have hS₂m : MeasurableSet S₂ := measurableSet_lt (by fun_prop) (by fun_prop)
  have hq0 : a + b ≠ 0 := by rw [← hq]; exact hx
  have hsplit : (fun r => ∫⁻ u, F ((K.next x r, K.totalRate x * K.hold x r),
      K.nextClock x (r, u)) ∂(μs.prod μs)) =ᵐ[ν.prod ν]
      fun r => S₁.indicator (fun r => I₁ ((a + b) * (r.1 / a), r.2 - b * (r.1 / a))) r +
        S₂.indicator (fun r => I₂ ((a + b) * (r.2 / b), r.1 - a * (r.2 / b))) r := by
    have htie : ∀ᵐ r ∂(ν.prod ν), ¬ (a * r.2 = b * r.1) := by
      rw [ae_iff]; simp only [not_not]
      refine prod_expMeasure_tie ?_
      by_contra h
      push Not at h
      exact hx (by rw [hq]; linarith [le_antisymm h.1 ha, le_antisymm h.2 hb])
    filter_upwards [htie] with r hr
    rcases lt_trichotomy (b * r.1) (a * r.2) with h | h | h
    · have h' : ¬ a * r.2 < b * r.1 := not_lt.mpr h.le
      rw [Set.indicator_of_mem (show r ∈ S₁ from h),
        Set.indicator_of_notMem (show r ∉ S₂ from h'), add_zero]
      simp only [next, nextClock, hold, hq, hq0, ↓reduceIte, h, hI₁, ← ha_def, ← hb_def]
    · exact absurd h.symm hr
    · have h' : ¬ b * r.1 < a * r.2 := not_lt.mpr h.le
      rw [Set.indicator_of_notMem (show r ∉ S₁ from h'),
        Set.indicator_of_mem (show r ∈ S₂ from h), zero_add]
      simp only [next, nextClock, hold, hq, hq0, ↓reduceIte, h, h', hI₂, ← ha_def, ← hb_def]
  rw [clockMeasure, lintegral_prod (fun c : ClockConfig =>
    F ((K.next x c.1, K.totalRate x * K.hold x c.1), K.nextClock x c)) (hF.comp hΓ).aemeasurable]
  dsimp only
  rw [lintegral_congr_ae hsplit, lintegral_add_left ((by fun_prop : Measurable
    fun r : ℝ × ℝ => I₁ ((a + b) * (r.1 / a), r.2 - b * (r.1 / a))).indicator hS₁m)]
  -- the first channel rings first
  have hfirst : ∫⁻ r, S₁.indicator (fun r => I₁ ((a + b) * (r.1 / a), r.2 - b * (r.1 / a))) r
      ∂(ν.prod ν) = ENNReal.ofReal (a / (a + b)) * ∫⁻ p, I₁ p ∂(ν.prod ν) := by
    rcases ha.lt_or_eq with ha' | ha'
    · exact lintegral_competing ha' hb hI₁m
    · rw [← ha', zero_div, ENNReal.ofReal_zero, zero_mul, lintegral_indicator hS₁m]
      refine setLIntegral_measure_zero _ _ ?_
      rw [hS₁, ← ha']
      exact prod_expMeasure_neg hb
  -- the second channel rings first
  have hsecond : ∫⁻ r, S₂.indicator (fun r => I₂ ((a + b) * (r.2 / b), r.1 - a * (r.2 / b))) r
      ∂(ν.prod ν) = ENNReal.ofReal (b / (a + b)) * ∫⁻ p, I₂ p ∂(ν.prod ν) := by
    rcases hb.lt_or_eq with hb' | hb'
    · rw [← lintegral_prod_swap, add_comm a b, ← lintegral_competing hb' ha hI₂m]
      rfl
    · rw [← hb', zero_div, ENNReal.ofReal_zero, zero_mul, lintegral_indicator hS₂m]
      refine setLIntegral_measure_zero _ _ ?_
      rw [hS₂, ← hb']
      exact prod_expMeasure_neg' ha
  -- identify the remaining integrals
  have hI₁J : ∫⁻ p, I₁ p ∂(ν.prod ν) = J (K.target₁ x) := by
    rw [lintegral_prod _ hI₁m.aemeasurable, hJ]
    refine lintegral_congr fun E => ?_
    rw [lintegral_clockMeasure (by fun_prop)]
    have hstep : ∀ R, I₁ (E, R) = ∫⁻ h, ∫⁻ t, ∫⁻ u₂,
        F ((K.target₁ x, E), ((h, R), (t, u₂))) ∂μs ∂μs ∂ν := by
      intro R
      simp only [hI₁]
      rw [lintegral_prod _ (by fun_prop)]
      exact lintegral_infinitePi_head_tail ν
        (G := fun p => ∫⁻ u₂, F ((K.target₁ x, E), ((p.1, R), (p.2, u₂))) ∂μs) (by fun_prop)
    simp_rw [hstep]
    exact lintegral_lintegral_swap (by fun_prop)
  have hI₂J : ∫⁻ p, I₂ p ∂(ν.prod ν) = J (K.target₂ x) := by
    rw [lintegral_prod _ hI₂m.aemeasurable, hJ]
    refine lintegral_congr fun E => ?_
    rw [lintegral_clockMeasure (by fun_prop)]
    refine lintegral_congr fun R => ?_
    have hstep : ∀ u₁, ∫⁻ u₂, F ((K.target₂ x, E), ((R, u₂ 0), (u₁, seqTail u₂))) ∂μs =
        ∫⁻ h, ∫⁻ t, F ((K.target₂ x, E), ((R, h), (u₁, t))) ∂μs ∂ν := fun u₁ =>
      lintegral_infinitePi_head_tail ν
        (G := fun p => F ((K.target₂ x, E), ((R, p.1), (u₁, p.2)))) (by fun_prop)
    simp only [hI₂]
    rw [lintegral_prod _ (by fun_prop)]
    simp_rw [hstep]
    exact lintegral_lintegral_swap (by fun_prop)
  rw [hfirst, hsecond, hI₁J, hI₂J]

/-! #### The steps read off the clock chain -/

omit [DecidableEq ι] in
/-- The path of the jump-chain construction depends on the steps only through the jump chain
and the jump times. -/
theorem ctmcPath_congr {Q : Matrix ι ι ℝ} {i : ι} {ω ω' : ℕ → (ι → ι) × ℝ}
    (hY : ctmcJumpChain i ω = ctmcJumpChain i ω')
    (hT : ctmcJumpTime Q i ω = ctmcJumpTime Q i ω') (t : ℝ≥0) :
    ctmcPath Q i ω t = ctmcPath Q i ω' t := by
  unfold ctmcPath
  rw [hY]
  split_ifs with h₁ h₂ h₂
  · revert h₁
    rw [hT]
    intro h₁
    rfl
  · exact absurd (hT ▸ h₁) h₂
  · exact absurd (hT ▸ h₂) h₁
  · rfl

omit [DecidableEq ι] in
variable (K) in
theorem config_succ (n : ℕ) (p : ι × ClockConfig) :
    K.config (n + 1) p = K.config n (K.step p) :=
  Function.iterate_succ_apply _ _ _

omit [DecidableEq ι] in
variable (K) in
theorem config_succ' (n : ℕ) (p : ι × ClockConfig) :
    K.config (n + 1) p = K.step (K.config n p) :=
  Function.iterate_succ_apply' _ _ _

omit [DecidableEq ι] in
variable (K) in
@[simp] theorem config_zero (p : ι × ClockConfig) : K.config 0 p = p := rfl

variable (K) in
/-- The steps after the first one are the steps of the chain restarted after its first jump. -/
theorem steps_succ (x : ι) (w : ClockConfig × (ℕ → (ι → ι) × ℝ)) (n : ℕ) :
    K.steps x w (n + 1) = K.steps (K.next x w.1.1) (K.nextClock x w.1, seqTail w.2) n := by
  simp only [steps, config_succ, step, seqTail]

variable (K) in
/-- The jump chain of the steps read off the clock chain is the state sequence of the clock
chain. -/
theorem ctmcJumpChain_steps (x : ι) (w : ClockConfig × (ℕ → (ι → ι) × ℝ)) (n : ℕ) :
    ctmcJumpChain x (K.steps x w) n = (K.config n (x, w.1)).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ctmcJumpChain, ih, steps, output, Function.update_self, config_succ', step]

variable (K) in
/-- The holding times of the steps read off the clock chain are its holding times. -/
theorem ctmcHoldingTime_steps (x : ι) (w : ClockConfig × (ℕ → (ι → ι) × ℝ)) (n : ℕ) :
    ctmcHoldingTime K.rateMatrix x (K.steps x w) n =
      if K.totalRate (K.config n (x, w.1)).1 = 0 then ∞
      else ENNReal.ofReal (K.hold (K.config n (x, w.1)).1 (K.config n (x, w.1)).2.1) := by
  simp only [ctmcHoldingTime, ctmcJumpChain_steps, rateMatrix_diag, neg_eq_zero, neg_neg]
  split_ifs with h
  · rfl
  · simp only [steps, output, h, ↓reduceIte]
    rw [mul_div_cancel_left₀ _ h]

variable (K) in
/-- The path driven by the steps read off the clock chain does not depend on the auxiliary
steps. -/
theorem ctmcPath_steps (x : ι) (c : ClockConfig) (f : ℕ → (ι → ι) × ℝ) (t : ℝ≥0) :
    ctmcPath K.rateMatrix x (K.steps x (c, f)) t = K.path x c t := by
  have hY : ctmcJumpChain x (K.steps x (c, f)) =
      ctmcJumpChain x (K.steps x (c, fun _ => (id, 0))) :=
    funext fun n => by rw [ctmcJumpChain_steps, ctmcJumpChain_steps]
  have hT : ctmcJumpTime K.rateMatrix x (K.steps x (c, f)) =
      ctmcJumpTime K.rateMatrix x (K.steps x (c, fun _ => (id, 0))) :=
    funext fun n => by simp only [ctmcJumpTime, ctmcHoldingTime_steps]
  exact ctmcPath_congr hY hT t

/-! #### Measurability of the steps -/

omit [DecidableEq ι] in
variable (K) in
theorem measurable_step [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι] :
    Measurable K.step := by
  refine measurable_from_prod_countable_right fun y => ?_
  exact ((K.measurable_next y).comp measurable_fst).prodMk (K.measurable_nextClock y)

omit [DecidableEq ι] in
variable (K) in
theorem measurable_config [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (n : ℕ) : Measurable (K.config n) :=
  (K.measurable_step).iterate n

variable (K) in
theorem measurable_output [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι] :
    Measurable fun q : (ι × ClockConfig) × ((ι → ι) × ℝ) => K.output q.1 q.2 := by
  have h : ∀ y : ι, Measurable fun q : ClockConfig × ((ι → ι) × ℝ) => K.output (y, q.1) q.2 := by
    intro y
    have hn := K.measurable_next y
    have hh := K.measurable_hold y
    unfold output
    refine Measurable.prodMk ?_ ?_
    · exact measurable_update'.comp ((measurable_fst.comp measurable_snd).prodMk
        (hn.comp (measurable_fst.comp measurable_fst)))
    · by_cases hy : K.totalRate y = 0
      · simp only [hy, ↓reduceIte]
        exact measurable_snd.comp measurable_snd
      · simp only [hy, ↓reduceIte]
        exact (hh.comp (measurable_fst.comp measurable_fst)).const_mul _
  have h' : Measurable fun q : ι × (ClockConfig × ((ι → ι) × ℝ)) => K.output (q.1, q.2.1) q.2.2 :=
    measurable_from_prod_countable_right fun y => h y
  exact h'.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

variable (K) in
theorem measurable_steps [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (x : ι) : Measurable (K.steps x) := by
  refine Measurable.of_eval fun n => ?_
  exact K.measurable_output.comp ((((K.measurable_config n).comp
    (measurable_const.prodMk measurable_fst))).prodMk ((measurable_pi_apply n).comp measurable_snd))

variable (K) in
theorem measurable_path [Finite ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] (x : ι)
    (t : ℝ≥0) : Measurable fun c => K.path x c t :=
  (measurable_ctmcPath x t).comp ((K.measurable_steps x).comp
    (measurable_id.prodMk measurable_const))

/-! #### The law of the steps -/

variable (K) in
/-- The first step read off the clock chain started at `x`, and the input of the chain
restarted after the first jump. -/
noncomputable def firstStep (x : ι) (w : ClockConfig × (ℕ → (ι → ι) × ℝ)) :
    ((ι → ι) × ℝ) × (ClockConfig × (ℕ → (ι → ι) × ℝ)) :=
  (K.output (x, w.1) (w.2 0), (K.nextClock x w.1, seqTail w.2))

variable (K) in
theorem measurable_firstStep [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (x : ι) : Measurable (K.firstStep x) :=
  (K.measurable_output.comp ((measurable_const.prodMk measurable_fst).prodMk
    ((measurable_pi_apply 0).comp measurable_snd))).prodMk
    (((K.measurable_nextClock x).comp measurable_fst).prodMk
      (measurable_seqTail.comp measurable_snd))

/-- **One step of the coupling.** When the clocks have law `clockMeasure` and the auxiliary
steps are i.i.d. with the step law of `ProbabilityTheory.ctmcInputMeasure`, the first step read
off the clock chain has the step law and is independent of the restarted input, which has the
same law as the input. -/
theorem IsValid.map_firstStep [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (hK : K.IsValid) (x : ι) :
    (clockMeasure.prod (ctmcInputMeasure hK.isRateMatrix)).map (K.firstStep x) =
      (ctmcStepMeasure hK.isRateMatrix).prod
        (clockMeasure.prod (ctmcInputMeasure hK.isRateMatrix)) := by
  set hQ := hK.isRateMatrix
  set ν := expMeasure 1
  set σ := ctmcStepMeasure hQ
  set P := ctmcInputMeasure hQ
  set Pr : ι → Measure ι := fun i => (hQ.ctmcJumpPMF i).toMeasure with hPr
  have hσ : σ = (Measure.pi Pr).prod ν := rfl
  have hP : P = Measure.infinitePi fun _ : ℕ => σ := rfl
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF (K.measurable_firstStep x),
    lintegral_prod (fun w => F (K.firstStep x w)) (hF.comp (K.measurable_firstStep x)).aemeasurable,
    lintegral_prod _ hF.aemeasurable]
  have hout := K.measurable_output
  have hinner : ∀ c, ∫⁻ f, F (K.firstStep x (c, f)) ∂P =
      ∫⁻ g, ∫⁻ f', F (K.output (x, c) g, (K.nextClock x c, f')) ∂P ∂σ := fun c =>
    lintegral_infinitePi_head_tail σ
      (G := fun p => F (K.output (x, c) p.1, (K.nextClock x c, p.2)))
      (hF.comp ((hout.comp (measurable_const.prodMk measurable_fst)).prodMk
        (measurable_const.prodMk measurable_snd)))
  simp_rw [hinner]
  have hRHS : ∀ g, ∫⁻ w, F (g, w) ∂(clockMeasure.prod P) =
      ∫⁻ c, ∫⁻ f', F (g, (c, f')) ∂P ∂clockMeasure := fun g =>
    lintegral_prod _ (by fun_prop)
  simp_rw [hRHS]
  by_cases hx : K.totalRate x = 0
  · -- an absorbing state: the step is the auxiliary step, up to a null set
    have hPrx : ∀ ψ : ι → ℝ≥0∞, ∫⁻ z, ψ z ∂(Pr x) = ψ x := by
      intro ψ
      have hd : K.rateMatrix x x = 0 := by rw [rateMatrix_diag, hx, neg_zero]
      rw [lintegral_fintype]
      simp only [hPr, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
        IsRateMatrix.ctmcJumpPMF, PMF.ofFintype_apply, ctmcJumpMatrix, hd, ↓reduceIte]
      rw [Finset.sum_eq_single x (fun z _ hz => by simp [Ne.symm hz]) (by simp)]
      simp
    have hupd : ∀ c, ∫⁻ g, ∫⁻ f', F (K.output (x, c) g, (K.nextClock x c, f')) ∂P ∂σ =
        ∫⁻ g, ∫⁻ f', F (g, (c, f')) ∂P ∂σ := by
      intro c
      have hmeas : Measurable fun ξ : ι → ι => ∫⁻ E, ∫⁻ f', F ((ξ, E), (c, f')) ∂P ∂ν := by
        fun_prop
      simp only [output, nextClock, next, hx, ↓reduceIte, hσ]
      rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop),
        lintegral_pi_update Pr x hmeas, hPrx]
    simp_rw [hupd]
    exact lintegral_lintegral_swap (by fun_prop)
  · -- an active state: competing clocks
    set Λ : (ι × ℝ) × ClockConfig → ℝ≥0∞ := fun p =>
      ∫⁻ ξ, ∫⁻ f', F ((Function.update ξ x p.1.1, p.1.2), (p.2, f')) ∂P ∂(Measure.pi Pr) with hΛ
    have hΛm : Measurable Λ := by fun_prop
    have hstep : ∀ c, ∫⁻ g, ∫⁻ f', F (K.output (x, c) g, (K.nextClock x c, f')) ∂P ∂σ =
        Λ ((K.next x c.1, K.totalRate x * K.hold x c.1), K.nextClock x c) := by
      intro c
      simp only [output, hx, ↓reduceIte, hσ]
      rw [lintegral_prod _ (by fun_prop)]
      simp only [lintegral_const, measure_univ, mul_one, hΛ]
    simp_rw [hstep]
    have hΓ : Measurable fun c : ClockConfig =>
        ((K.next x c.1, K.totalRate x * K.hold x c.1), K.nextClock x c) :=
      (((K.measurable_next x).comp measurable_fst).prodMk
        (((K.measurable_hold x).comp measurable_fst).const_mul _)).prodMk
        (K.measurable_nextClock x)
    rw [← lintegral_map hΛm hΓ, hK.map_clock hx, lintegral_prod _ hΛm.aemeasurable,
      lintegral_prod _ (by fun_prop), hσ, lintegral_prod _ (by fun_prop)]
    have hmeas : Measurable fun ξ : ι → ι =>
        ∫⁻ E, ∫⁻ c, ∫⁻ f', F ((ξ, E), (c, f')) ∂P ∂clockMeasure ∂ν := by fun_prop
    rw [lintegral_pi_update Pr x hmeas]
    refine lintegral_congr fun z => ?_
    simp only [hΛ]
    calc _ = ∫⁻ E, ∫⁻ ξ, ∫⁻ c, ∫⁻ f', F ((Function.update ξ x z, E), (c, f'))
            ∂P ∂clockMeasure ∂(Measure.pi Pr) ∂ν :=
          lintegral_congr fun E => lintegral_lintegral_swap (by fun_prop)
      _ = _ := lintegral_lintegral_swap (by fun_prop)

/-- **The coupling has the input law.** When the clocks have law `clockMeasure` and the
auxiliary steps are i.i.d. with the step law, the steps read off the clock chain started at
`x` are i.i.d. with the step law: their law is `ProbabilityTheory.ctmcInputMeasure`. -/
theorem IsValid.map_steps [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (hK : K.IsValid) (x : ι) :
    (clockMeasure.prod (ctmcInputMeasure hK.isRateMatrix)).map (K.steps x) =
      ctmcInputMeasure hK.isRateMatrix := by
  set hQ := hK.isRateMatrix
  set σ := ctmcStepMeasure hQ
  set M := clockMeasure.prod (ctmcInputMeasure hQ)
  have hjoint : ∀ y : ι, Measurable fun p : ((ι → ι) × ℝ) × (ClockConfig × (ℕ → (ι → ι) × ℝ)) =>
      K.steps (p.1.1 y) p.2 := fun y =>
    (measurable_from_prod_countable_right (f := fun q : ι × (ClockConfig × (ℕ → (ι → ι) × ℝ)) =>
      K.steps q.1 q.2) fun z => K.measurable_steps z).comp
      (f := fun p : ((ι → ι) × ℝ) × (ClockConfig × (ℕ → (ι → ι) × ℝ)) => (p.1.1 y, p.2))
      (((measurable_pi_apply y).comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
  have hbox : ∀ n (y : ι) (t : ℕ → Set ((ι → ι) × ℝ)), (∀ i, MeasurableSet (t i)) →
      M (K.steps y ⁻¹' Set.pi (Finset.range n : Set ℕ) t) = ∏ i ∈ Finset.range n, σ (t i) := by
    intro n
    induction n with
    | zero => intro y t _; simp
    | succ n ih =>
      intro y t ht
      set A : Set (((ι → ι) × ℝ) × (ClockConfig × (ℕ → (ι → ι) × ℝ))) :=
        {p | p.1 ∈ t 0 ∧ K.steps (p.1.1 y) p.2 ∈
          Set.pi (Finset.range n : Set ℕ) (fun i => t (i + 1))} with hA
      have hAm : MeasurableSet A :=
        (measurable_fst (ht 0)).inter (hjoint y (MeasurableSet.pi (Set.to_countable _)
          fun i _ => ht (i + 1)))
      have hpre : K.steps y ⁻¹' Set.pi (Finset.range (n + 1) : Set ℕ) t =
          K.firstStep y ⁻¹' A := by
        ext w
        have h1 : (K.output (y, w.1) (w.2 0)).1 y = K.next y w.1.1 := by simp [output]
        simp only [mem_preimage, Set.mem_pi, Finset.coe_range, mem_Iio, hA, mem_ofPred_eq,
          firstStep, h1]
        constructor
        · intro h
          refine ⟨h 0 (Nat.succ_pos n), fun i hi => ?_⟩
          rw [← steps_succ]
          exact h (i + 1) (by omega)
        · rintro ⟨h0, h⟩ i hi
          cases i with
          | zero => exact h0
          | succ i =>
            rw [steps_succ]
            exact h i (by omega)
      rw [hpre, ← Measure.map_apply (K.measurable_firstStep y) hAm, hK.map_firstStep y,
        Measure.prod_apply hAm]
      have hsec : ∀ g, M (Prod.mk g ⁻¹' A) =
          (t 0).indicator (fun _ => ∏ i ∈ Finset.range n, σ (t (i + 1))) g := by
        intro g
        by_cases hg : g ∈ t 0
        · rw [Set.indicator_of_mem hg, ← ih (g.1 y) (fun i => t (i + 1)) (fun i => ht _)]
          congr 1
          ext w
          simp [hA, hg]
        · rw [Set.indicator_of_notMem hg]
          have : Prod.mk g ⁻¹' A = ∅ := by
            ext w
            simp [hA, hg]
          rw [this, measure_empty]
      refine (lintegral_congr fun g => hsec g).trans ?_
      rw [lintegral_indicator_const (ht 0), Finset.prod_range_succ', mul_comm]
  rw [show ctmcInputMeasure hQ = Measure.infinitePi fun _ : ℕ => σ from rfl]
  refine Measure.eq_infinitePi (fun _ : ℕ => σ) fun s t ht => ?_
  obtain ⟨n, hn⟩ : ∃ n, s ⊆ Finset.range n :=
    ⟨s.sup id + 1, fun i hi => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))⟩
  set t' : ℕ → Set ((ι → ι) × ℝ) := fun i => if i ∈ s then t i else univ with ht'
  have hset : Set.pi (s : Set ℕ) t = Set.pi (Finset.range n : Set ℕ) t' := by
    ext ω
    simp only [Set.mem_pi, Finset.mem_coe, Finset.coe_range, mem_Iio, ht']
    constructor
    · intro h i _
      split_ifs with hi
      · exact h i hi
      · exact mem_univ _
    · intro h i hi
      have := h i (Finset.mem_range.1 (hn hi))
      rwa [ite_eq_left hi] at this
  rw [Measure.map_apply (K.measurable_steps x) (MeasurableSet.pi s.countable_toSet
    fun i _ => ht i), hset, hbox n x t' (fun i => by
      by_cases h : i ∈ s
      · simp only [ht', h, ↓reduceIte]; exact ht i
      · simp only [ht', h, ↓reduceIte]; exact MeasurableSet.univ)]
  rw [← Finset.prod_subset hn (fun i _ hi => by simp [ht', hi])]
  exact Finset.prod_congr rfl fun i hi => by simp [ht', hi]

/-- **Law identification.** For independent rate-`1` exponential clocks (law `clockMeasure`),
the path of the clock chain started at `x` has the law of the continuous-time Markov chain with
rate matrix `rateMatrix`, built from the jump chain and holding times in
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`. The laws are measures on the
path space `ℝ≥0 → ι` with its product σ-algebra. -/
theorem IsValid.map_path [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (hK : K.IsValid) (x : ι) :
    clockMeasure.map (fun c t => K.path x c t) =
      (ctmcInputMeasure hK.isRateMatrix).map (fun ω t => ctmcPath K.rateMatrix x ω t) := by
  set P := ctmcInputMeasure hK.isRateMatrix
  have hX : Measurable fun ω : ℕ → (ι → ι) × ℝ => fun t => ctmcPath K.rateMatrix x ω t :=
    measurable_pi_iff.mpr fun t => measurable_ctmcPath x t
  have hpath : Measurable fun c : ClockConfig => fun t => K.path x c t :=
    measurable_pi_iff.mpr fun t => K.measurable_path x t
  calc clockMeasure.map (fun c t => K.path x c t)
      = (clockMeasure.prod P).map ((fun c t => K.path x c t) ∘ Prod.fst) := by
        rw [← Measure.map_map hpath measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    _ = (clockMeasure.prod P).map ((fun ω t => ctmcPath K.rateMatrix x ω t) ∘ K.steps x) := by
        congr 1
        funext w
        funext t
        simp only [Function.comp_apply, ← ctmcPath_steps K x w.1 w.2]
    _ = P.map (fun ω t => ctmcPath K.rateMatrix x ω t) := by
        rw [← Measure.map_map hX (K.measurable_steps x), hK.map_steps x]

/-- **Finite-dimensional distributions of the clock chain**: with increments
`s 0, …, s (n - 1)`, times `t k = s 0 + ⋯ + s k`, and states `j 0, …, j (n - 1)`,
`P(X (t k) = j k for all k) = ∏ₖ exp (s k Q) (j (k - 1)) (j k)`, where `j (-1) = x`. -/
theorem IsValid.clockMeasure_real_path_fdd [Fintype ι] [MeasurableSpace ι]
    [DiscreteMeasurableSpace ι] (hK : K.IsValid) (x : ι) {n : ℕ} (s : Fin n → ℝ≥0)
    (j : Fin n → ι) :
    clockMeasure.real {c | ∀ k, K.path x c (∑ l ∈ Finset.Iic k, s l) = j k} =
      ∏ k, ctmcTransition K.rateMatrix (s k) ((Fin.cons x j : Fin (n + 1) → ι) k.castSucc)
        (j k) := by
  set B : Set (ℝ≥0 → ι) := {f | ∀ k, f (∑ l ∈ Finset.Iic k, s l) = j k} with hB
  have hBm : MeasurableSet B := by
    rw [hB, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k =>
      measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have hpath : Measurable fun c : ClockConfig => fun t => K.path x c t :=
    measurable_pi_iff.mpr fun t => K.measurable_path x t
  have hX : Measurable fun ω : ℕ → (ι → ι) × ℝ => fun t => ctmcPath K.rateMatrix x ω t :=
    measurable_pi_iff.mpr fun t => measurable_ctmcPath x t
  have h1 : clockMeasure.real {c | ∀ k, K.path x c (∑ l ∈ Finset.Iic k, s l) = j k} =
      (clockMeasure.map (fun c t => K.path x c t)).real B := by
    rw [map_measureReal_apply hpath hBm]; rfl
  rw [h1, hK.map_path x, map_measureReal_apply hX hBm]
  exact hK.isRateMatrix.ctmcInputMeasure_real_ctmcPath_fdd x s j

/-- **Transition probabilities of the clock chain** (Kolmogorov): `P(X t = j) = exp (t Q) x j`. -/
theorem IsValid.clockMeasure_real_path_eq [Fintype ι] [MeasurableSpace ι]
    [DiscreteMeasurableSpace ι] (hK : K.IsValid) (x j : ι) (t : ℝ≥0) :
    clockMeasure.real {c | K.path x c t = j} = ctmcTransition K.rateMatrix t x j := by
  have hpath : Measurable fun c : ClockConfig => fun t => K.path x c t :=
    measurable_pi_iff.mpr fun t => K.measurable_path x t
  have hX : Measurable fun ω : ℕ → (ι → ι) × ℝ => fun t => ctmcPath K.rateMatrix x ω t :=
    measurable_pi_iff.mpr fun t => measurable_ctmcPath x t
  have hBm : MeasurableSet {f : ℝ≥0 → ι | f t = j} :=
    measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have h1 : clockMeasure.real {c | K.path x c t = j} =
      (clockMeasure.map (fun c t => K.path x c t)).real {f | f t = j} := by
    rw [map_measureReal_apply hpath hBm]; rfl
  rw [h1, hK.map_path x, map_measureReal_apply hX hBm]
  exact hK.isRateMatrix.ctmcInputMeasure_real_ctmcPath_eq x j t

/-! #### Event times and integrated rates along a path -/

omit [DecidableEq ι] in
variable (K) in
/-- The duration of a jump from `y` with residual clocks `r`; `0` when `y` is absorbing. -/
noncomputable def dur (y : ι) (r : ℝ × ℝ) : ℝ := if K.totalRate y = 0 then 0 else K.hold y r

omit [DecidableEq ι] in
variable (K) in
/-- The time of the `n`-th jump of the clock chain, as a real number (jumps from absorbing
states take no time). -/
noncomputable def eventTime (p : ι × ClockConfig) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, K.dur (K.config j p).1 (K.config j p).2.1

omit [DecidableEq ι] in
theorem eventTime_succ (p : ι × ClockConfig) (n : ℕ) :
    K.eventTime p (n + 1) = K.eventTime p n + K.dur (K.config n p).1 (K.config n p).2.1 :=
  Finset.sum_range_succ _ _

omit [DecidableEq ι] in
theorem eventTime_mono {p : ι × ClockConfig}
    (hdur : ∀ j, 0 ≤ K.dur (K.config j p).1 (K.config j p).2.1) : Monotone (K.eventTime p) :=
  monotone_nat_of_le_succ fun n => by rw [eventTime_succ]; linarith [hdur n]

/-- Before absorption, the jump times of the steps are the real event times. -/
theorem ctmcJumpTime_steps_eq (x : ι) (c : ClockConfig) (f : ℕ → (ι → ι) × ℝ) {n : ℕ}
    (hact : ∀ j < n, K.totalRate (K.config j (x, c)).1 ≠ 0)
    (hdur : ∀ j, 0 ≤ K.dur (K.config j (x, c)).1 (K.config j (x, c)).2.1) :
    ctmcJumpTime K.rateMatrix x (K.steps x (c, f)) n = ENNReal.ofReal (K.eventTime (x, c) n) := by
  induction n with
  | zero => simp [ctmcJumpTime, eventTime]
  | succ n ih =>
    have h := hact n (Nat.lt_succ_self n)
    rw [ctmcJumpTime, Finset.sum_range_succ, ← ctmcJumpTime, ih fun j hj => hact j (by omega),
      ctmcHoldingTime_steps, ite_eq_right h, eventTime_succ,
      ENNReal.ofReal_add (show 0 ≤ K.eventTime (x, c) n from Finset.sum_nonneg fun j _ => hdur j)
        (hdur n)]
    congr 1
    simp only [dur, h, ↓reduceIte]

/-- After an absorbing state, the next jump time is infinite. -/
theorem ctmcJumpTime_steps_succ_eq_top (x : ι) (c : ClockConfig) (f : ℕ → (ι → ι) × ℝ) {n : ℕ}
    (habs : K.totalRate (K.config n (x, c)).1 = 0) :
    ctmcJumpTime K.rateMatrix x (K.steps x (c, f)) (n + 1) = ∞ := by
  rw [ctmcJumpTime, Finset.sum_range_succ, ctmcHoldingTime_steps, ite_eq_left habs,
    add_top]

/-- On the interval between the `m`-th and the next jump, the path is the `m`-th state. -/
theorem path_eq_config (x : ι) (c : ClockConfig) {t : ℝ≥0} {m : ℕ}
    (h₁ : ctmcJumpTime K.rateMatrix x (K.steps x (c, fun _ => (id, 0))) m ≤ t)
    (h₂ : (t : ℝ≥0∞) < ctmcJumpTime K.rateMatrix x (K.steps x (c, fun _ => (id, 0))) (m + 1)) :
    K.path x c t = (K.config m (x, c)).1 := by
  rw [path, ctmcPath_eq_of_mem x _ h₁ h₂, ctmcJumpChain_steps]

/-- The path of the clock chain on the real line (constant before time `0`). -/
noncomputable def realPath (x : ι) (c : ClockConfig) (t : ℝ) : ι := K.path x c t.toNNReal

/-- The real path is the `m`-th state between the `m`-th and the next event time, before the
absorbing index `n`, and the absorbing state after the `n`-th event. -/
theorem realPath_eq (x : ι) (c : ClockConfig) {n : ℕ}
    (hact : ∀ j < n, K.totalRate (K.config j (x, c)).1 ≠ 0)
    (habs : K.totalRate (K.config n (x, c)).1 = 0)
    (hdur : ∀ j, 0 ≤ K.dur (K.config j (x, c)).1 (K.config j (x, c)).2.1)
    {m : ℕ} (hm : m ≤ n) {t : ℝ} (ht₁ : K.eventTime (x, c) m ≤ t)
    (ht₂ : m < n → t < K.eventTime (x, c) (m + 1)) :
    K.realPath x c t = (K.config m (x, c)).1 := by
  have ht0 : 0 ≤ t := le_trans (Finset.sum_nonneg fun j _ => hdur j) ht₁
  have hcoe : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal t := rfl
  refine path_eq_config x c ?_ ?_
  · rw [ctmcJumpTime_steps_eq x c _ (fun j hj => hact j (by omega)) hdur, hcoe]
    exact ENNReal.ofReal_le_ofReal ht₁
  · rcases hm.lt_or_eq with hlt | heq
    · rw [ctmcJumpTime_steps_eq x c _ (fun j hj => hact j (by omega)) hdur, hcoe]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ht0 (ht₂ hlt))).2 (ht₂ hlt)
    · subst heq
      rw [ctmcJumpTime_steps_succ_eq_top x c _ habs]
      exact ENNReal.coe_lt_top

variable (K) in
theorem measurable_realPath [Finite ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (x : ι) (c : ClockConfig) : Measurable (K.realPath x c) := by
  have h := measurable_ctmcPath_uncurry (Q := K.rateMatrix) x
  exact (h.comp (measurable_real_toNNReal.prodMk measurable_const) :)

/-- The integral of a constant-on-`[u, t)` function. -/
theorem integral_eq_of_forall_Ico {g : ℝ → ℝ} {C u t : ℝ} (hut : u ≤ t)
    (hg : ∀ s ∈ Ico u t, g s = C) : ∫ s in u..t, g s = C * (t - u) := by
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by rw [ae_iff]; simp
  rw [intervalIntegral.integral_congr_ae (g := fun _ => C) (hae.mono fun s hs hmem => ?_)]
  · simp [mul_comm]
  · rw [uIoc_of_le hut] at hmem
    exact hg s ⟨le_of_lt hmem.1, lt_of_le_of_ne hmem.2 hs⟩

/-- **Integrated rates along the path.** For a function `φ` of the state, the integral of
`φ (X s)` over `[0, t]` is the sum of `φ` times the durations of the completed jumps, plus `φ`
of the current state times the time elapsed since the last jump. -/
theorem integral_realPath [Finite ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (φ : ι → ℝ) (x : ι) (c : ClockConfig) {n : ℕ}
    (hact : ∀ j < n, K.totalRate (K.config j (x, c)).1 ≠ 0)
    (habs : K.totalRate (K.config n (x, c)).1 = 0)
    (hdur : ∀ j, 0 ≤ K.dur (K.config j (x, c)).1 (K.config j (x, c)).2.1)
    {m : ℕ} (hm : m ≤ n) {t : ℝ} (ht₁ : K.eventTime (x, c) m ≤ t)
    (ht₂ : m < n → t ≤ K.eventTime (x, c) (m + 1)) :
    ∫ s in (0 : ℝ)..t, φ (K.realPath x c s) =
      ∑ j ∈ Finset.range m, φ (K.config j (x, c)).1 * K.dur (K.config j (x, c)).1
        (K.config j (x, c)).2.1 + φ (K.config m (x, c)).1 * (t - K.eventTime (x, c) m) := by
  have hmono := eventTime_mono hdur
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun s => φ (K.realPath x c s)) volume u v := by
    intro u v
    have hfin : Set.Finite (Set.range φ) := Set.finite_range φ
    obtain ⟨C, hC⟩ := hfin.isBounded.exists_norm_le
    refine (intervalIntegrable_const (c := C)).mono_fun
      ((measurable_of_countable φ).comp (K.measurable_realPath x c)).aestronglyMeasurable
      (ae_of_all _ fun s => ?_)
    exact (hC _ ⟨_, rfl⟩).trans (le_abs_self C)
  induction m generalizing t with
  | zero =>
    have h0 : K.eventTime (x, c) 0 = 0 := by simp [eventTime]
    rw [h0] at ht₁
    rw [Finset.range_zero, Finset.sum_empty, zero_add, h0]
    refine integral_eq_of_forall_Ico ht₁ fun s hs => ?_
    rw [realPath_eq x c hact habs hdur (Nat.zero_le n) (by rw [h0]; exact hs.1)
      fun hn => lt_of_lt_of_le hs.2 (ht₂ hn)]
  | succ m ih =>
    have hmn : m < n := hm
    have hE : K.eventTime (x, c) m ≤ K.eventTime (x, c) (m + 1) := hmono (Nat.le_succ m)
    have hsecond : ∫ s in K.eventTime (x, c) (m + 1)..t, φ (K.realPath x c s) =
        φ (K.config (m + 1) (x, c)).1 * (t - K.eventTime (x, c) (m + 1)) :=
      integral_eq_of_forall_Ico ht₁ fun s hs => by
        rw [realPath_eq x c hact habs hdur hm hs.1 fun hn => lt_of_lt_of_le hs.2 (ht₂ hn)]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (K.eventTime (x, c) (m + 1)))
      (hint _ t), ih hmn.le hE (fun _ => le_rfl), hsecond, Finset.sum_range_succ, eventTime_succ]
    ring

end TwoChannel

/-! ### Clock facts for a single jump -/

namespace TwoChannel

variable {ι : Type*} {K : TwoChannel ι}

/-- The three cases of a jump from an active state with positive residual clocks: channel `1`
first, channel `2` first, or a tie with both channels active. -/
theorem IsValid.jump_cases (hK : K.IsValid) {y : ι} (hy : K.totalRate y ≠ 0) {r : ℝ × ℝ}
    (hr₁ : 0 < r.1) (hr₂ : 0 < r.2) :
    (K.rate₂ y * r.1 < K.rate₁ y * r.2 ∧ 0 < K.rate₁ y) ∨
      (¬ K.rate₂ y * r.1 < K.rate₁ y * r.2 ∧ K.rate₁ y * r.2 < K.rate₂ y * r.1 ∧
        0 < K.rate₂ y) ∨
      (¬ K.rate₂ y * r.1 < K.rate₁ y * r.2 ∧ ¬ K.rate₁ y * r.2 < K.rate₂ y * r.1 ∧
        0 < K.rate₁ y ∧ 0 < K.rate₂ y ∧ K.rate₂ y * (r.1 / K.rate₁ y) = r.2) := by
  have ha := hK.rate₁_nonneg y
  have hb := hK.rate₂_nonneg y
  by_cases h₁ : K.rate₂ y * r.1 < K.rate₁ y * r.2
  · refine Or.inl ⟨h₁, lt_of_le_of_ne ha fun h => ?_⟩
    rw [← h, zero_mul] at h₁
    exact absurd h₁ (not_lt.mpr (mul_nonneg hb hr₁.le))
  by_cases h₂ : K.rate₁ y * r.2 < K.rate₂ y * r.1
  · refine Or.inr (Or.inl ⟨h₁, h₂, lt_of_le_of_ne hb fun h => ?_⟩)
    rw [← h, zero_mul] at h₂
    exact absurd h₂ (not_lt.mpr (mul_nonneg ha hr₂.le))
  have heq : K.rate₁ y * r.2 = K.rate₂ y * r.1 := le_antisymm (not_lt.mp h₁) (not_lt.mp h₂)
  have ha' : 0 < K.rate₁ y := by
    refine lt_of_le_of_ne ha fun h => hy ?_
    rw [← h, zero_mul] at heq
    have : K.rate₂ y = 0 := by
      rcases mul_eq_zero.mp heq.symm with h' | h'
      · exact h'
      · exact absurd h' hr₁.ne'
    simp [totalRate, ← h, this]
  have hb' : 0 < K.rate₂ y := by
    refine lt_of_le_of_ne hb fun h => ?_
    rw [← h, zero_mul] at heq
    rcases mul_eq_zero.mp heq with h' | h'
    · exact absurd h' ha'.ne'
    · exact absurd h' hr₂.ne'
  refine Or.inr (Or.inr ⟨h₁, h₂, ha', hb', ?_⟩)
  field_simp
  linarith

/-- From an active state with positive residual clocks, the jump takes a positive time, during
which neither channel consumes more than its residual clock. -/
theorem IsValid.hold_bounds (hK : K.IsValid) {y : ι} (hy : K.totalRate y ≠ 0) {r : ℝ × ℝ}
    (hr₁ : 0 < r.1) (hr₂ : 0 < r.2) :
    0 < K.hold y r ∧ K.rate₁ y * K.hold y r ≤ r.1 ∧ K.rate₂ y * K.hold y r ≤ r.2 := by
  rcases hK.jump_cases hy hr₁ hr₂ with ⟨h1, ha⟩ | ⟨h1, h2, hb⟩ | ⟨h1, h2, ha, hb, htie⟩
  · have hh : K.hold y r = r.1 / K.rate₁ y := by simp [hold, h1]
    rw [hh, mul_div_cancel₀ _ ha.ne']
    refine ⟨div_pos hr₁ ha, le_rfl, ?_⟩
    rw [mul_div_assoc', div_le_iff₀ ha, mul_comm r.2]
    exact h1.le
  · have hh : K.hold y r = r.2 / K.rate₂ y := by simp [hold, h1, h2]
    rw [hh, mul_div_cancel₀ _ hb.ne']
    refine ⟨div_pos hr₂ hb, ?_, le_rfl⟩
    rw [mul_div_assoc', div_le_iff₀ hb, mul_comm r.1]
    exact h2.le
  · have hh : K.hold y r = r.1 / K.rate₁ y := by simp [hold, h1, h2]
    rw [hh, mul_div_cancel₀ _ ha.ne', htie]
    exact ⟨div_pos hr₁ ha, le_rfl, le_rfl⟩

variable (K) in
/-- The internal clock of channel `1` after `n` jumps: its rate integrated over the jumps. -/
noncomputable def internal₁ (p : ι × ClockConfig) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, K.rate₁ (K.config j p).1 * K.dur (K.config j p).1 (K.config j p).2.1

variable (K) in
/-- The internal clock of channel `2` after `n` jumps. -/
noncomputable def internal₂ (p : ι × ClockConfig) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, K.rate₂ (K.config j p).1 * K.dur (K.config j p).1 (K.config j p).2.1

end TwoChannel

/-! ### The SIR epidemic as a two-channel chain -/

/-- States `(S, I)` of the SIR epidemic in a population of size `N` (the number of removed
individuals is `N - S - I`). -/
abbrev SIRState (N : ℕ) := Fin (N + 1) × Fin (N + 1)

/-- **The SIR epidemic as a two-channel chain**: infection `(S, I) → (S - 1, I + 1)` at rate
`β S I / N` and recovery `(S, I) → (S, I - 1)` at rate `γ I`; an infection and a recovery at the
same instant lead to `(S - 1, I)`. -/
noncomputable def sirChannels (β γ : ℝ) (N : ℕ) : TwoChannel (SIRState N) where
  rate₁ x := β * (x.1 : ℕ) * (x.2 : ℕ) / N
  rate₂ x := γ * (x.2 : ℕ)
  target₁ x := (⟨x.1.val - 1, by have := x.1.isLt; omega⟩,
    ⟨min (x.2.val + 1) N, by omega⟩)
  target₂ x := (x.1, ⟨x.2.val - 1, by have := x.2.isLt; omega⟩)
  target₁₂ x := (⟨x.1.val - 1, by have := x.1.isLt; omega⟩, x.2)

theorem sirChannels_isValid {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (N : ℕ) :
    (sirChannels β γ N).IsValid where
  rate₁_nonneg x := by simp only [sirChannels]; positivity
  rate₂_nonneg x := by simp only [sirChannels]; positivity
  rate₁_eq_zero x h := by
    have h1 := congrArg (fun z : SIRState N => (z.1 : ℕ)) h
    simp only [sirChannels] at h1 ⊢
    have : (x.1 : ℕ) = 0 := by omega
    simp [this]
  rate₂_eq_zero x h := by
    have h1 := congrArg (fun z : SIRState N => (z.2 : ℕ)) h
    simp only [sirChannels] at h1 ⊢
    have : (x.2 : ℕ) = 0 := by omega
    simp [this]

/-- The clock configuration of unit clocks with interarrival times `e₁` and `e₂`: the residual
clocks are the first interarrival times, and the future interarrivals are the rest. -/
def initClock (e₁ e₂ : ℕ → ℝ) : ClockConfig := ((e₁ 0, e₂ 0), (seqTail e₁, seqTail e₂))

/-- The counting path of a unit clock with interarrival times `e`: the number of arrivals
`e 0 + ⋯ + e n ≤ u`. -/
noncomputable def clockCount (e : ℕ → ℝ) (u : ℝ≥0) : ℕ :=
  PoissonProcess.count (fun n (e : ℕ → ℝ) => e n) u e

/-- **The constructed SIR path**, started at `x₀` and driven by unit clocks with interarrival
times `e₁` (infection) and `e₂` (recovery). -/
noncomputable def sirPath (β γ : ℝ) (N : ℕ) (x₀ : SIRState N) (e₁ e₂ : ℕ → ℝ) (t : ℝ) :
    SIRState N :=
  (sirChannels β γ N).realPath x₀ (initClock e₁ e₂) t

/-- The susceptible count of the constructed SIR path. -/
noncomputable def sirS (β γ : ℝ) (N : ℕ) (x₀ : SIRState N) (e₁ e₂ : ℕ → ℝ) (t : ℝ) : ℕ :=
  (sirPath β γ N x₀ e₁ e₂ t).1

/-- The infective count of the constructed SIR path. -/
noncomputable def sirI (β γ : ℝ) (N : ℕ) (x₀ : SIRState N) (e₁ e₂ : ℕ → ℝ) (t : ℝ) : ℕ :=
  (sirPath β γ N x₀ e₁ e₂ t).2

/-- The removed count of the constructed SIR path. -/
noncomputable def sirR (β γ : ℝ) (N : ℕ) (x₀ : SIRState N) (e₁ e₂ : ℕ → ℝ) (t : ℝ) : ℕ :=
  N - sirS β γ N x₀ e₁ e₂ t - sirI β γ N x₀ e₁ e₂ t

/-- The arrival times `e 0 + ⋯ + e (k - 1)` of a unit clock. -/
def arrival (e : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, e j

theorem arrival_succ (e : ℕ → ℝ) (k : ℕ) : arrival e (k + 1) = arrival e k + e k :=
  Finset.sum_range_succ _ _

theorem arrival_mono {e : ℕ → ℝ} (he : ∀ n, 0 < e n) : Monotone (arrival e) :=
  monotone_nat_of_le_succ fun k => by rw [arrival_succ]; linarith [he k]

/-- The counting path between the `k`-th and the next arrival is `k`. -/
theorem clockCount_eq {e : ℕ → ℝ} (he : ∀ n, 0 < e n) {k : ℕ} {v : ℝ} (hv : 0 ≤ v)
    (h₁ : arrival e k ≤ v) (h₂ : v < arrival e (k + 1)) : clockCount e v.toNNReal = k := by
  have hset : {n : ℕ | PoissonProcess.arrivalTime (fun n (e : ℕ → ℝ) => e n) (n + 1) e ≤
      (v.toNNReal : ℝ)} = ↑(Finset.range k) := by
    ext n
    simp only [mem_ofPred_eq, Real.coe_toNNReal _ hv, Finset.coe_range, mem_Iio]
    change arrival e (n + 1) ≤ v ↔ n < k
    constructor
    · intro h
      by_contra hn
      exact absurd (lt_of_lt_of_le h₂ (arrival_mono he (by omega))) (not_lt.mpr h)
    · intro hn
      exact le_trans (arrival_mono he (by omega)) h₁
  rw [clockCount, PoissonProcess.count, hset, Set.ncard_coe_finset, Finset.card_range]

/-! ### Invariants of the constructed SIR chain -/

section Invariant

variable {β γ : ℝ} {N : ℕ} {x₀ : SIRState N} {e₁ e₂ : ℕ → ℝ}

open TwoChannel

/-- **Bookkeeping invariant** of the constructed SIR chain after `n` jumps, with `k₁`
infections and `k₂` recoveries so far: the counts are `S = S₀ - k₁`, `I = I₀ + k₁ - k₂`; the
future interarrivals of each clock are its interarrivals after the ones consumed; the internal
clock plus the residual is the next arrival time; the internal clock is at least the last
arrival time; and the residuals are positive. -/
def SIRInv (β γ : ℝ) (N : ℕ) (x₀ : SIRState N) (e₁ e₂ : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ k₁ k₂ : ℕ,
    (((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).1.1 : ℕ) + k₁ = x₀.1 ∧
    (((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).1.2 : ℕ) + k₂ = x₀.2 + k₁ ∧
    (((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).1.1 : ℕ) +
      ((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).1.2 ≤ N ∧
    ((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).2.2.1 = (fun j => e₁ (k₁ + 1 + j)) ∧
    ((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).2.2.2 = (fun j => e₂ (k₂ + 1 + j)) ∧
    (sirChannels β γ N).internal₁ (x₀, initClock e₁ e₂) n +
      ((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).2.1.1 = arrival e₁ (k₁ + 1) ∧
    (sirChannels β γ N).internal₂ (x₀, initClock e₁ e₂) n +
      ((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).2.1.2 = arrival e₂ (k₂ + 1) ∧
    arrival e₁ k₁ ≤ (sirChannels β γ N).internal₁ (x₀, initClock e₁ e₂) n ∧
    arrival e₂ k₂ ≤ (sirChannels β γ N).internal₂ (x₀, initClock e₁ e₂) n ∧
    0 < ((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).2.1.1 ∧
    0 < ((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).2.1.2

theorem sirInv_zero (hx₀ : (x₀.1 : ℕ) + x₀.2 ≤ N) (he₁ : ∀ n, 0 < e₁ n)
    (he₂ : ∀ n, 0 < e₂ n) : SIRInv β γ N x₀ e₁ e₂ 0 := by
  refine ⟨0, 0, rfl, rfl, hx₀, ?_, ?_, ?_, ?_, ?_, ?_, he₁ 0, he₂ 0⟩
  · funext j; simp only [config_zero, initClock, seqTail]; congr 1; omega
  · funext j; simp only [config_zero, initClock, seqTail]; congr 1; omega
  · simp only [internal₁, arrival, Finset.range_zero, Finset.sum_empty, zero_add,
      Finset.sum_range_one, config_zero, initClock]
  · simp only [internal₂, arrival, Finset.range_zero, Finset.sum_empty, zero_add,
      Finset.sum_range_one, config_zero, initClock]
  · simp only [internal₁, arrival, Finset.range_zero, Finset.sum_empty, le_refl]
  · simp only [internal₂, arrival, Finset.range_zero, Finset.sum_empty, le_refl]

theorem sirInv_succ (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (he₁ : ∀ n, 0 < e₁ n) (he₂ : ∀ n, 0 < e₂ n)
    {n : ℕ} (ih : SIRInv β γ N x₀ e₁ e₂ n) : SIRInv β γ N x₀ e₁ e₂ (n + 1) := by
  obtain ⟨k₁, k₂, hS, hI, hSI, hu₁, hu₂, hτ₁, hτ₂, hA₁, hA₂, hr₁, hr₂⟩ := ih
  set K := sirChannels β γ N
  set p := (x₀, initClock e₁ e₂)
  set y := (K.config n p).1 with hy
  set c := (K.config n p).2 with hc
  have hK : K.IsValid := sirChannels_isValid hβ hγ N
  have hcfg : K.config (n + 1) p = (K.next y c.1, K.nextClock y c) := config_succ' K n p
  have hi₁ : K.internal₁ p (n + 1) = K.internal₁ p n + K.rate₁ y * K.dur y c.1 :=
    Finset.sum_range_succ _ _
  have hi₂ : K.internal₂ p (n + 1) = K.internal₂ p n + K.rate₂ y * K.dur y c.1 :=
    Finset.sum_range_succ _ _
  unfold SIRInv
  rw [hcfg, hi₁, hi₂]
  by_cases hq : K.totalRate y = 0
  · have hdur : K.dur y c.1 = 0 := by simp [dur, hq]
    simp only [next, nextClock, hq, ↓reduceIte, hdur, mul_zero, add_zero]
    exact ⟨k₁, k₂, hS, hI, hSI, hu₁, hu₂, hτ₁, hτ₂, hA₁, hA₂, hr₁, hr₂⟩
  have hdur : K.dur y c.1 = K.hold y c.1 := by simp [dur, hq]
  rw [hdur]
  rcases hK.jump_cases hq hr₁ hr₂ with ⟨h1, ha⟩ | ⟨h1, h2, hb⟩ | ⟨h1, h2, ha, hb, htie⟩
  · -- an infection
    have hS1 : 1 ≤ (y.1 : ℕ) := by
      by_contra h
      have : (y.1 : ℕ) = 0 := by omega
      simp [K, sirChannels, this] at ha
    have hI1 : (y.2 : ℕ) + 1 ≤ N := by omega
    have hhold : K.hold y c.1 = c.1.1 / K.rate₁ y := by simp [hold, h1]
    simp only [next, nextClock, hq, h1, ↓reduceIte, hhold]
    refine ⟨k₁ + 1, k₂, ?_, ?_, ?_, ?_, hu₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [K, sirChannels]; omega
    · simp only [K, sirChannels]; omega
    · simp only [K, sirChannels]; omega
    · rw [hu₁]; funext j; simp only [seqTail]; congr 1; omega
    · rw [hu₁, arrival_succ, ← hτ₁, mul_div_cancel₀ _ ha.ne']
    · rw [← hτ₂]; ring
    · rw [mul_div_cancel₀ _ ha.ne', hτ₁]
    · have : 0 ≤ K.rate₂ y * (c.1.1 / K.rate₁ y) :=
        mul_nonneg (hK.rate₂_nonneg y) (div_nonneg hr₁.le ha.le)
      linarith
    · rw [hu₁]; exact he₁ _
    · rw [sub_pos, mul_div_assoc', div_lt_iff₀ ha, mul_comm _ (K.rate₁ y)]; exact h1
  · -- a recovery
    have hI1 : 1 ≤ (y.2 : ℕ) := by
      by_contra h
      have : (y.2 : ℕ) = 0 := by omega
      simp [K, sirChannels, this] at hb
    have hhold : K.hold y c.1 = c.1.2 / K.rate₂ y := by simp [hold, h1, h2]
    simp only [next, nextClock, hq, h1, h2, ↓reduceIte, hhold]
    refine ⟨k₁, k₂ + 1, ?_, ?_, ?_, hu₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [K, sirChannels]; omega
    · simp only [K, sirChannels]; omega
    · simp only [K, sirChannels]; omega
    · rw [hu₂]; funext j; simp only [seqTail]; congr 1; omega
    · rw [← hτ₁]; ring
    · rw [hu₂, arrival_succ, ← hτ₂, mul_div_cancel₀ _ hb.ne']
    · have : 0 ≤ K.rate₁ y * (c.1.2 / K.rate₂ y) :=
        mul_nonneg (hK.rate₁_nonneg y) (div_nonneg hr₂.le hb.le)
      linarith
    · rw [mul_div_cancel₀ _ hb.ne', hτ₂]
    · rw [sub_pos, mul_div_assoc', div_lt_iff₀ hb, mul_comm _ (K.rate₂ y)]; exact h2
    · rw [hu₂]; exact he₂ _
  · -- an infection and a recovery at the same instant
    have hS1 : 1 ≤ (y.1 : ℕ) := by
      by_contra h
      have : (y.1 : ℕ) = 0 := by omega
      simp [K, sirChannels, this] at ha
    have hI1 : 1 ≤ (y.2 : ℕ) := by
      by_contra h
      have : (y.2 : ℕ) = 0 := by omega
      simp [K, sirChannels, this] at hb
    have hhold : K.hold y c.1 = c.1.1 / K.rate₁ y := by simp [hold, h1, h2]
    simp only [next, nextClock, hq, h1, h2, ↓reduceIte, hhold]
    refine ⟨k₁ + 1, k₂ + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [K, sirChannels]; omega
    · simp only [K, sirChannels]; omega
    · simp only [K, sirChannels]; omega
    · rw [hu₁]; funext j; simp only [seqTail]; congr 1; omega
    · rw [hu₂]; funext j; simp only [seqTail]; congr 1; omega
    · rw [hu₁, arrival_succ, ← hτ₁, mul_div_cancel₀ _ ha.ne']
    · rw [hu₂, arrival_succ, ← hτ₂, htie]
    · rw [mul_div_cancel₀ _ ha.ne', hτ₁]
    · rw [htie, hτ₂]
    · rw [hu₁]; exact he₁ _
    · rw [hu₂]; exact he₂ _

theorem sirInv (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hx₀ : (x₀.1 : ℕ) + x₀.2 ≤ N)
    (he₁ : ∀ n, 0 < e₁ n) (he₂ : ∀ n, 0 < e₂ n) (n : ℕ) : SIRInv β γ N x₀ e₁ e₂ n := by
  induction n with
  | zero => exact sirInv_zero hx₀ he₁ he₂
  | succ n ih => exact sirInv_succ hβ hγ he₁ he₂ ih

/-- Each jump of the constructed SIR chain lowers `2 S + I`. -/
theorem sir_next_potential (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {y : SIRState N}
    (hy : (sirChannels β γ N).totalRate y ≠ 0) (hSI : (y.1 : ℕ) + y.2 ≤ N) {r : ℝ × ℝ}
    (hr₁ : 0 < r.1) (hr₂ : 0 < r.2) :
    2 * (((sirChannels β γ N).next y r).1 : ℕ) + ((sirChannels β γ N).next y r).2 <
      2 * (y.1 : ℕ) + y.2 := by
  set K := sirChannels β γ N
  have hK : K.IsValid := sirChannels_isValid hβ hγ N
  rcases hK.jump_cases hy hr₁ hr₂ with ⟨h1, ha⟩ | ⟨h1, h2, hb⟩ | ⟨h1, h2, ha, hb, -⟩
  · have hS1 : 1 ≤ (y.1 : ℕ) := by
      by_contra h
      have : (y.1 : ℕ) = 0 := by omega
      simp [K, sirChannels, this] at ha
    simp only [next, hy, h1, ↓reduceIte]
    simp only [K, sirChannels]
    omega
  · have hI1 : 1 ≤ (y.2 : ℕ) := by
      by_contra h
      have : (y.2 : ℕ) = 0 := by omega
      simp [K, sirChannels, this] at hb
    simp only [next, hy, h1, h2, ↓reduceIte]
    simp only [K, sirChannels]
    omega
  · have hS1 : 1 ≤ (y.1 : ℕ) := by
      by_contra h
      have : (y.1 : ℕ) = 0 := by omega
      simp [K, sirChannels, this] at ha
    simp only [next, hy, h1, h2, ↓reduceIte]
    simp only [K, sirChannels]
    omega

/-- **The constructed SIR chain is absorbed after at most `2 N` jumps.** -/
theorem sir_exists_absorbing (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hx₀ : (x₀.1 : ℕ) + x₀.2 ≤ N)
    (he₁ : ∀ n, 0 < e₁ n) (he₂ : ∀ n, 0 < e₂ n) :
    ∃ n ≤ 2 * N, (sirChannels β γ N).totalRate
      ((sirChannels β γ N).config n (x₀, initClock e₁ e₂)).1 = 0 := by
  set K := sirChannels β γ N
  set p := (x₀, initClock e₁ e₂)
  by_contra hcon
  push Not at hcon
  have hpot : ∀ n, n ≤ 2 * (x₀.1 : ℕ) + x₀.2 + 1 →
      2 * ((K.config n p).1.1 : ℕ) + (K.config n p).1.2 + n ≤ 2 * (x₀.1 : ℕ) + x₀.2 := by
    intro n
    induction n with
    | zero => intro _; simp [p]
    | succ n ih =>
      intro hn
      have ih := ih (by omega)
      obtain ⟨k₁, k₂, -, -, hSI, -, -, -, -, -, -, hr₁, hr₂⟩ := sirInv hβ hγ hx₀ he₁ he₂ n
      have h' : 2 * ((K.next (K.config n p).1 (K.config n p).2.1).1 : ℕ) +
          (K.next (K.config n p).1 (K.config n p).2.1).2 <
          2 * ((K.config n p).1.1 : ℕ) + (K.config n p).1.2 :=
        sir_next_potential hβ hγ (hcon n (by omega)) hSI hr₁ hr₂
      rw [config_succ']
      simp only [step]
      omega
  have := hpot (2 * x₀.1 + x₀.2 + 1) le_rfl
  omega

end Invariant

/-! ### Pathwise existence -/

section Existence

variable {β γ : ℝ} {N : ℕ} {x₀ : SIRState N} {e₁ e₂ : ℕ → ℝ}

open TwoChannel

theorem clockCount_zero {e : ℕ → ℝ} (he : ∀ n, 0 < e n) : clockCount e 0 = 0 := by
  have := clockCount_eq he (k := 0) (v := 0) le_rfl (by simp [arrival])
    (by simp [arrival, he 0])
  simpa using this

/-- The jumps of the constructed SIR chain take nonnegative time. -/
theorem sir_dur_nonneg (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hx₀ : (x₀.1 : ℕ) + x₀.2 ≤ N)
    (he₁ : ∀ n, 0 < e₁ n) (he₂ : ∀ n, 0 < e₂ n) (j : ℕ) :
    0 ≤ (sirChannels β γ N).dur ((sirChannels β γ N).config j (x₀, initClock e₁ e₂)).1
      ((sirChannels β γ N).config j (x₀, initClock e₁ e₂)).2.1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hr₁, hr₂⟩ := sirInv hβ hγ hx₀ he₁ he₂ j
  unfold dur
  split_ifs with h
  · exact le_rfl
  · exact ((sirChannels_isValid hβ hγ N).hold_bounds h hr₁ hr₂).1.le

/-- **The time-change equations at one time**, relative to the initial state: at every time
`t ≥ 0` the constructed SIR counts are `S = S₀ - Y₁(∫₀ᵗ β S I / N)`,
`I = I₀ + Y₁(∫₀ᵗ β S I / N) - Y₂(∫₀ᵗ γ I)` and `R = R₀ + Y₂(∫₀ᵗ γ I)`, with `S + I ≤ N`. -/
theorem sir_timeChange (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hx₀ : (x₀.1 : ℕ) + x₀.2 ≤ N)
    (he₁ : ∀ n, 0 < e₁ n) (he₂ : ∀ n, 0 < e₂ n) {t : ℝ} (ht : 0 ≤ t) :
    (sirS β γ N x₀ e₁ e₂ t : ℝ) = (x₀.1 : ℕ) - clockCount e₁
        (infectionClock β N (sirS β γ N x₀ e₁ e₂) (sirI β γ N x₀ e₁ e₂) t) ∧
      (sirI β γ N x₀ e₁ e₂ t : ℝ) = (x₀.2 : ℕ) + clockCount e₁
        (infectionClock β N (sirS β γ N x₀ e₁ e₂) (sirI β γ N x₀ e₁ e₂) t) -
          clockCount e₂ (recoveryClock γ (sirI β γ N x₀ e₁ e₂) t) ∧
      sirS β γ N x₀ e₁ e₂ t + sirI β γ N x₀ e₁ e₂ t ≤ N ∧
      sirR β γ N x₀ e₁ e₂ t = (N - x₀.1 - x₀.2) +
        clockCount e₂ (recoveryClock γ (sirI β γ N x₀ e₁ e₂) t) := by
  classical
  set K := sirChannels β γ N
  set c := initClock e₁ e₂
  set p : SIRState N × ClockConfig := (x₀, c)
  have hK : K.IsValid := sirChannels_isValid hβ hγ N
  have hex : ∃ n, K.totalRate (K.config n p).1 = 0 :=
    let ⟨n, _, hn⟩ := sir_exists_absorbing hβ hγ hx₀ he₁ he₂; ⟨n, hn⟩
  set n := Nat.find hex
  have habs : K.totalRate (K.config n p).1 = 0 := Nat.find_spec hex
  have hact : ∀ j < n, K.totalRate (K.config j p).1 ≠ 0 := fun j hj => Nat.find_min hex hj
  have hdur : ∀ j, 0 ≤ K.dur (K.config j p).1 (K.config j p).2.1 :=
    sir_dur_nonneg hβ hγ hx₀ he₁ he₂
  -- the index of the current jump
  have hmex : ∃ m, m = n ∨ t < K.eventTime p (m + 1) := ⟨n, Or.inl rfl⟩
  set m := Nat.find hmex
  have hmn : m ≤ n := Nat.find_min' hmex (Or.inl rfl)
  have ht₂ : m < n → t < K.eventTime p (m + 1) := fun hlt =>
    (Nat.find_spec hmex).resolve_left (ne_of_lt hlt)
  have ht₁ : K.eventTime p m ≤ t := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]; simpa [eventTime] using ht
    · obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have := Nat.find_min hmex (show m' < m by omega)
      push Not at this
      rw [hm']
      exact this.2
  obtain ⟨k₁, k₂, hS, hI, hSI, -, -, hτ₁, hτ₂, hA₁, hA₂, hr₁, hr₂⟩ :=
    sirInv hβ hγ hx₀ he₁ he₂ m
  replace hS : ((K.config m p).1.1 : ℕ) + k₁ = x₀.1 := hS
  replace hI : ((K.config m p).1.2 : ℕ) + k₂ = x₀.2 + k₁ := hI
  replace hSI : ((K.config m p).1.1 : ℕ) + (K.config m p).1.2 ≤ N := hSI
  have hX : K.realPath x₀ c t = (K.config m p).1 := realPath_eq x₀ c hact habs hdur hmn ht₁ ht₂
  have hXS : sirS β γ N x₀ e₁ e₂ t = ((K.config m p).1.1 : ℕ) := by
    simp only [sirS, sirPath, ← hX]; rfl
  have hXI : sirI β γ N x₀ e₁ e₂ t = ((K.config m p).1.2 : ℕ) := by
    simp only [sirI, sirPath, ← hX]; rfl
  -- the internal clocks
  have hle : m < n → t ≤ K.eventTime p (m + 1) := fun h => (ht₂ h).le
  have hint₁ : ∫ s in (0 : ℝ)..t, β * (sirS β γ N x₀ e₁ e₂ s : ℝ) *
      (sirI β γ N x₀ e₁ e₂ s : ℝ) / N =
      K.internal₁ p m + K.rate₁ (K.config m p).1 * (t - K.eventTime p m) :=
    integral_realPath K.rate₁ x₀ c hact habs hdur hmn ht₁ hle
  have hint₂ : ∫ s in (0 : ℝ)..t, γ * (sirI β γ N x₀ e₁ e₂ s : ℝ) =
      K.internal₂ p m + K.rate₂ (K.config m p).1 * (t - K.eventTime p m) :=
    integral_realPath K.rate₂ x₀ c hact habs hdur hmn ht₁ hle
  -- the clocks have not reached their next arrivals
  have hgap₁ : K.rate₁ (K.config m p).1 * (t - K.eventTime p m) < (K.config m p).2.1.1 := by
    rcases (hK.rate₁_nonneg (K.config m p).1).lt_or_eq with ha | ha
    · rcases hmn.lt_or_eq with hlt | heq
      · have hb := hK.hold_bounds (hact m hlt) hr₁ hr₂
        have hd : K.dur (K.config m p).1 (K.config m p).2.1 =
            K.hold (K.config m p).1 (K.config m p).2.1 := by simp [dur, hact m hlt]
        have := ht₂ hlt
        rw [eventTime_succ, hd] at this
        calc _ < K.rate₁ (K.config m p).1 * K.hold (K.config m p).1 (K.config m p).2.1 :=
              mul_lt_mul_of_pos_left (by linarith) ha
          _ ≤ _ := hb.2.1
      · exfalso
        have h0 : K.totalRate (K.config m p).1 = 0 := by rw [heq]; exact habs
        have := hK.rate₂_nonneg (K.config m p).1
        simp only [totalRate] at h0
        linarith
    · rw [← ha, zero_mul]; exact hr₁
  have hgap₂ : K.rate₂ (K.config m p).1 * (t - K.eventTime p m) < (K.config m p).2.1.2 := by
    rcases (hK.rate₂_nonneg (K.config m p).1).lt_or_eq with hb' | hb'
    · rcases hmn.lt_or_eq with hlt | heq
      · have hb := hK.hold_bounds (hact m hlt) hr₁ hr₂
        have hd : K.dur (K.config m p).1 (K.config m p).2.1 =
            K.hold (K.config m p).1 (K.config m p).2.1 := by simp [dur, hact m hlt]
        have := ht₂ hlt
        rw [eventTime_succ, hd] at this
        calc _ < K.rate₂ (K.config m p).1 * K.hold (K.config m p).1 (K.config m p).2.1 :=
              mul_lt_mul_of_pos_left (by linarith) hb'
          _ ≤ _ := hb.2.2
      · exfalso
        have h0 : K.totalRate (K.config m p).1 = 0 := by rw [heq]; exact habs
        have := hK.rate₁_nonneg (K.config m p).1
        simp only [totalRate] at h0
        linarith
    · rw [← hb', zero_mul]; exact hr₂
  have htm : 0 ≤ t - K.eventTime p m := sub_nonneg.mpr ht₁
  have hc₁ : clockCount e₁ (infectionClock β N (sirS β γ N x₀ e₁ e₂) (sirI β γ N x₀ e₁ e₂) t) =
      k₁ := by
    rw [infectionClock, hint₁]
    have h0 : 0 ≤ K.rate₁ (K.config m p).1 * (t - K.eventTime p m) :=
      mul_nonneg (hK.rate₁_nonneg _) htm
    have harr : 0 ≤ arrival e₁ k₁ :=
      Finset.sum_nonneg fun j _ => (he₁ j).le
    exact clockCount_eq he₁ ((harr.trans hA₁).trans (le_add_of_nonneg_right h0))
      (hA₁.trans (le_add_of_nonneg_right h0)) (by linarith)
  have hc₂ : clockCount e₂ (recoveryClock γ (sirI β γ N x₀ e₁ e₂) t) = k₂ := by
    rw [recoveryClock, hint₂]
    have h0 : 0 ≤ K.rate₂ (K.config m p).1 * (t - K.eventTime p m) :=
      mul_nonneg (hK.rate₂_nonneg _) htm
    have harr : 0 ≤ arrival e₂ k₂ :=
      Finset.sum_nonneg fun j _ => (he₂ j).le
    exact clockCount_eq he₂ ((harr.trans hA₂).trans (le_add_of_nonneg_right h0))
      (hA₂.trans (le_add_of_nonneg_right h0)) (by linarith)
  rw [hc₁, hc₂]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hXS]
    have : (((K.config m p).1.1 : ℕ) : ℝ) + k₁ = ((x₀.1 : ℕ) : ℝ) := by exact_mod_cast hS
    linarith
  · rw [hXI]
    have : (((K.config m p).1.2 : ℕ) : ℝ) + k₂ = ((x₀.2 : ℕ) : ℝ) + k₁ := by exact_mod_cast hI
    linarith
  · rw [hXS, hXI]; exact hSI
  · simp only [sirR, hXS, hXI]
    omega

/-- **Pathwise existence of the SIR chain.** For every pair of unit clocks with positive
interarrival times `e₁` (infection) and `e₂` (recovery), dependent or not, and every initial
state `(S₀, I₀)` with `S₀ + I₀ ≤ N`, the constructed counts `(S, I, R)` solve the random
time-change equations of `IsChainPath`, for all times `t ≥ 0`, with `S(0) = S₀`, `I(0) = I₀`. -/
theorem isChainPath_sir (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hx₀ : (x₀.1 : ℕ) + x₀.2 ≤ N)
    (he₁ : ∀ n, 0 < e₁ n) (he₂ : ∀ n, 0 < e₂ n) :
    IsChainPath β γ N (clockCount e₁) (clockCount e₂) (sirS β γ N x₀ e₁ e₂)
      (sirI β γ N x₀ e₁ e₂) (sirR β γ N x₀ e₁ e₂) := by
  have h0 := sir_timeChange hβ hγ hx₀ he₁ he₂ (t := 0) le_rfl
  simp only [infectionClock, recoveryClock, intervalIntegral.integral_same,
    Real.toNNReal_zero, clockCount_zero he₁, clockCount_zero he₂, Nat.cast_zero, sub_zero,
    add_zero] at h0
  obtain ⟨hS0, hI0, hSI0, hR0⟩ := h0
  have hS0' : sirS β γ N x₀ e₁ e₂ 0 = x₀.1 := by exact_mod_cast hS0
  have hI0' : sirI β γ N x₀ e₁ e₂ 0 = x₀.2 := by exact_mod_cast hI0
  have hmeas : Measurable (sirPath β γ N x₀ e₁ e₂) :=
    (sirChannels β γ N).measurable_realPath x₀ (initClock e₁ e₂)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [sirR]; omega
  · exact (measurable_of_countable (fun x : SIRState N => (x.1 : ℕ))).comp hmeas
  · exact (measurable_of_countable (fun x : SIRState N => (x.2 : ℕ))).comp hmeas
  · exact (measurable_of_countable (fun x : SIRState N => N - (x.1 : ℕ) - x.2)).comp hmeas
  · intro t ht
    rw [(sir_timeChange hβ hγ hx₀ he₁ he₂ ht).1, hS0']
  · intro t ht
    rw [(sir_timeChange hβ hγ hx₀ he₁ he₂ ht).2.1, hI0']
  · intro t ht
    rw [(sir_timeChange hβ hγ hx₀ he₁ he₂ ht).2.2.2, hR0]
    push_cast
    ring

/-- The constructed SIR path starts at the initial state. -/
theorem sirPath_zero (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hx₀ : (x₀.1 : ℕ) + x₀.2 ≤ N)
    (he₁ : ∀ n, 0 < e₁ n) (he₂ : ∀ n, 0 < e₂ n) : sirPath β γ N x₀ e₁ e₂ 0 = x₀ := by
  have h0 := sir_timeChange hβ hγ hx₀ he₁ he₂ (t := 0) le_rfl
  simp only [infectionClock, recoveryClock, intervalIntegral.integral_same,
    Real.toNNReal_zero, clockCount_zero he₁, clockCount_zero he₂, Nat.cast_zero, sub_zero,
    add_zero] at h0
  have hS0 : sirS β γ N x₀ e₁ e₂ 0 = x₀.1 := by exact_mod_cast h0.1
  have hI0 : sirI β γ N x₀ e₁ e₂ 0 = x₀.2 := by exact_mod_cast h0.2.1
  exact Prod.ext (Fin.ext hS0) (Fin.ext hI0)

end Existence

/-! ### Independent exponential clocks -/

section Clocks

/-- The law of two independent unit-rate Poisson clocks, through their interarrival times: all
interarrival times are independent rate-`1` exponentials. -/
noncomputable def clockLaw : Measure ((ℕ → ℝ) × (ℕ → ℝ)) :=
  (Measure.infinitePi fun _ : ℕ => expMeasure 1).prod
    (Measure.infinitePi fun _ : ℕ => expMeasure 1)

instance : IsProbabilityMeasure clockLaw := by
  unfold clockLaw; infer_instance

/-- Independence is preserved by composing with a map that pushes the measure forward to the
law under which the variables are independent. -/
theorem iIndepFun_comp_of_map_eq {Ω Ω' ι : Type*} {β : ι → Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [∀ i, MeasurableSpace (β i)] {μ : Measure Ω} {μ' : Measure Ω'}
    {g : Ω → Ω'} (hg : Measurable g) (hmap : μ.map g = μ') {X : ∀ i, Ω' → β i}
    (hX : ∀ i, Measurable (X i)) (h : iIndepFun X μ') :
    iIndepFun (fun i => X i ∘ g) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have hpre : ∀ i ∈ S, (X i ∘ g) ⁻¹' sets i = g ⁻¹' (X i ⁻¹' sets i) := fun _ _ => rfl
  have hm : ∀ i ∈ S, MeasurableSet (X i ⁻¹' sets i) := fun i hi => hX i (hsets i hi)
  rw [Finset.prod_congr rfl fun i hi => by rw [hpre i hi, ← Measure.map_apply hg (hm i hi), hmap]]
  have : (⋂ i ∈ S, (X i ∘ g) ⁻¹' sets i) = g ⁻¹' (⋂ i ∈ S, X i ⁻¹' sets i) := by
    ext ω; simp
  rw [this, ← Measure.map_apply hg (Finset.measurableSet_biInter S hm), hmap, h S hsets]

theorem ae_pos_infinitePi : ∀ᵐ e ∂(Measure.infinitePi fun _ : ℕ => expMeasure 1), ∀ n, 0 < e n := by
  rw [ae_all_iff]
  intro n
  refine ae_of_ae_map (measurable_pi_apply n).aemeasurable ?_
  rw [Measure.infinitePi_map_eval]
  exact ae_pos_expMeasure

/-- Under `clockLaw`, all interarrival times are positive almost surely. -/
theorem ae_clockLaw_pos : ∀ᵐ ω ∂clockLaw, (∀ n, 0 < ω.1 n) ∧ ∀ n, 0 < ω.2 n := by
  have h1 : ∀ᵐ ω ∂clockLaw, ∀ n, 0 < ω.1 n := by
    refine ae_of_ae_map (f := Prod.fst) (μ := clockLaw) (p := fun e : ℕ → ℝ => ∀ n, 0 < e n)
      measurable_fst.aemeasurable ?_
    rw [clockLaw, Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_pos_infinitePi
  have h2 : ∀ᵐ ω ∂clockLaw, ∀ n, 0 < ω.2 n := by
    refine ae_of_ae_map (f := Prod.snd) (μ := clockLaw) (p := fun e : ℕ → ℝ => ∀ n, 0 < e n)
      measurable_snd.aemeasurable ?_
    rw [clockLaw, Measure.map_snd_prod, measure_univ, one_smul]
    exact ae_pos_infinitePi
  filter_upwards [h1, h2] with ω h1 h2 using ⟨h1, h2⟩

/-- **Almost-sure existence of the SIR chain**: for almost every outcome of two independent
unit Poisson clocks, the constructed counts solve the random time-change equations for all
`t ≥ 0`. -/
theorem ae_isChainPath_sir {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {N : ℕ} {x₀ : SIRState N}
    (hx₀ : (x₀.1 : ℕ) + x₀.2 ≤ N) :
    ∀ᵐ ω ∂clockLaw, IsChainPath β γ N (clockCount ω.1) (clockCount ω.2)
      (sirS β γ N x₀ ω.1 ω.2) (sirI β γ N x₀ ω.1 ω.2) (sirR β γ N x₀ ω.1 ω.2) := by
  filter_upwards [ae_clockLaw_pos] with ω hω
  exact isChainPath_sir hβ hγ hx₀ hω.1 hω.2

theorem hasLaw_clockLaw_fst (n : ℕ) : HasLaw (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ω.1 n)
    (expMeasure ((1 : ℝ≥0) : ℝ)) clockLaw := by
  refine ⟨((measurable_pi_apply n).comp measurable_fst).aemeasurable, ?_⟩
  change Measure.map ((fun f : ℕ → ℝ => f n) ∘ Prod.fst) clockLaw = _
  rw [← Measure.map_map (measurable_pi_apply n) measurable_fst, clockLaw, Measure.map_fst_prod,
    measure_univ, one_smul, Measure.infinitePi_map_eval]
  rfl

theorem hasLaw_clockLaw_snd (n : ℕ) : HasLaw (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ω.2 n)
    (expMeasure ((1 : ℝ≥0) : ℝ)) clockLaw := by
  refine ⟨((measurable_pi_apply n).comp measurable_snd).aemeasurable, ?_⟩
  change Measure.map ((fun f : ℕ → ℝ => f n) ∘ Prod.snd) clockLaw = _
  rw [← Measure.map_map (measurable_pi_apply n) measurable_snd, clockLaw, Measure.map_snd_prod,
    measure_univ, one_smul, Measure.infinitePi_map_eval]
  rfl

/-- The infection clock is a unit-rate Poisson process under `clockLaw`. -/
theorem isPoissonProcess_clockCount_fst :
    IsPoissonProcess (fun u (ω : (ℕ → ℝ) × (ℕ → ℝ)) => clockCount ω.1 u) 1 clockLaw := by
  have hind : iIndepFun (fun n (ω : (ℕ → ℝ) × (ℕ → ℝ)) => ω.1 n) clockLaw :=
    iIndepFun_comp_of_map_eq (X := fun n (e : ℕ → ℝ) => e n) measurable_fst
      (by rw [clockLaw, Measure.map_fst_prod, measure_univ, one_smul])
      (fun n => measurable_pi_apply n)
      (iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id)
  exact PoissonProcess.isPoissonProcess_count one_pos hasLaw_clockLaw_fst hind

/-- The recovery clock is a unit-rate Poisson process under `clockLaw`. -/
theorem isPoissonProcess_clockCount_snd :
    IsPoissonProcess (fun u (ω : (ℕ → ℝ) × (ℕ → ℝ)) => clockCount ω.2 u) 1 clockLaw := by
  have hind : iIndepFun (fun n (ω : (ℕ → ℝ) × (ℕ → ℝ)) => ω.2 n) clockLaw :=
    iIndepFun_comp_of_map_eq (X := fun n (e : ℕ → ℝ) => e n) measurable_snd
      (by rw [clockLaw, Measure.map_snd_prod, measure_univ, one_smul])
      (fun n => measurable_pi_apply n)
      (iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id)
  exact PoissonProcess.isPoissonProcess_count one_pos hasLaw_clockLaw_snd hind

theorem measurable_initClock : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => initClock ω.1 ω.2 := by
  unfold initClock; fun_prop

attribute [local fun_prop] measurable_lintegral_of_uncurry in
/-- The clock configuration of two independent unit clocks has law `clockMeasure`. -/
theorem clockLaw_map_initClock :
    clockLaw.map (fun ω => initClock ω.1 ω.2) = clockMeasure := by
  set ν := expMeasure 1
  set μs := Measure.infinitePi fun _ : ℕ => ν
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF measurable_initClock, TwoChannel.lintegral_clockMeasure hF, clockLaw,
    lintegral_prod (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => F (initClock ω.1 ω.2))
      (hF.comp measurable_initClock).aemeasurable]
  have hstep : ∀ e₁ : ℕ → ℝ, ∫⁻ e₂, F (initClock e₁ e₂) ∂μs =
      ∫⁻ h₂, ∫⁻ t₂, F ((e₁ 0, h₂), (seqTail e₁, t₂)) ∂μs ∂ν := fun e₁ =>
    lintegral_infinitePi_head_tail ν (G := fun q => F ((e₁ 0, q.1), (seqTail e₁, q.2)))
      (by fun_prop)
  refine (lintegral_congr fun e₁ => hstep e₁).trans ?_
  rw [lintegral_infinitePi_head_tail ν
    (G := fun q => ∫⁻ h₂, ∫⁻ t₂, F ((q.1, h₂), (q.2, t₂)) ∂μs ∂ν) (by fun_prop)]
  refine lintegral_congr fun h₁ => ?_
  exact lintegral_lintegral_swap (by fun_prop)

theorem measurable_sirPath {β γ : ℝ} {N : ℕ} (x₀ : SIRState N) (t : ℝ) :
    Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => sirPath β γ N x₀ ω.1 ω.2 t :=
  ((sirChannels β γ N).measurable_path x₀ t.toNNReal).comp measurable_initClock

/-- **Law identification for the SIR chain.** Driven by two independent unit Poisson clocks,
the constructed SIR path has the law of the continuous-time Markov chain with the SIR rate
matrix, built from the jump chain and holding times of
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`. -/
theorem map_sirPath {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {N : ℕ} (x₀ : SIRState N) :
    clockLaw.map (fun ω (t : ℝ≥0) => sirPath β γ N x₀ ω.1 ω.2 t) =
      (ctmcInputMeasure (sirChannels_isValid hβ hγ N).isRateMatrix).map
        (fun ω t => ctmcPath (sirChannels β γ N).rateMatrix x₀ ω t) := by
  have hpath : Measurable fun c : ClockConfig => fun t => (sirChannels β γ N).path x₀ c t :=
    measurable_pi_iff.mpr fun t => (sirChannels β γ N).measurable_path x₀ t
  have heq : (fun ω : (ℕ → ℝ) × (ℕ → ℝ) => fun t : ℝ≥0 => sirPath β γ N x₀ ω.1 ω.2 t) =
      (fun c t => (sirChannels β γ N).path x₀ c t) ∘ fun ω => initClock ω.1 ω.2 := by
    funext ω t
    simp [sirPath, TwoChannel.realPath]
  rw [heq, ← Measure.map_map hpath measurable_initClock, clockLaw_map_initClock,
    (sirChannels_isValid hβ hγ N).map_path x₀]

/-- Law identification on any probability space: if the interarrival times `T ω` of the two
clocks are independent rate-`1` exponentials (law `clockLaw`), the constructed SIR path has the
law of the jump-chain construction. -/
theorem map_sirPath_of_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {T : Ω → (ℕ → ℝ) × (ℕ → ℝ)} (hT : HasLaw T clockLaw P) {β γ : ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {N : ℕ} (x₀ : SIRState N) :
    P.map (fun ω (t : ℝ≥0) => sirPath β γ N x₀ (T ω).1 (T ω).2 t) =
      (ctmcInputMeasure (sirChannels_isValid hβ hγ N).isRateMatrix).map
        (fun ω t => ctmcPath (sirChannels β γ N).rateMatrix x₀ ω t) := by
  have hm : Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => fun t : ℝ≥0 => sirPath β γ N x₀ ω.1 ω.2 t :=
    measurable_pi_iff.mpr fun t => measurable_sirPath x₀ t
  rw [← map_sirPath hβ hγ x₀, ← hT.map_eq, AEMeasurable.map_map_of_aemeasurable
    (hT.map_eq ▸ hm.aemeasurable) hT.aemeasurable]
  rfl

/-- **Transition probabilities of the SIR chain** (Kolmogorov): driven by independent unit
Poisson clocks, `P(X t = j) = exp (t Q) x₀ j` for the SIR rate matrix `Q`. -/
theorem clockLaw_real_sirPath_eq {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {N : ℕ} (x₀ j : SIRState N)
    (t : ℝ≥0) :
    clockLaw.real {ω | sirPath β γ N x₀ ω.1 ω.2 t = j} =
      ctmcTransition (sirChannels β γ N).rateMatrix t x₀ j := by
  have hK := sirChannels_isValid hβ hγ N
  rw [← hK.clockMeasure_real_path_eq x₀ j t, ← clockLaw_map_initClock,
    map_measureReal_apply measurable_initClock
      (measurableSet_eq_fun ((sirChannels β γ N).measurable_path x₀ t) measurable_const)]
  congr 1
  ext ω
  simp [sirPath, TwoChannel.realPath]

end Clocks

end MathlibExt.Biology.Epidemiology.StochasticSIR
