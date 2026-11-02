/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.IVTranslationInvariance
/-!
# Integral shift decay from a dense set of test functions

The integral decay hypothesis for translation invariance needs to be checked only on a dense set
of bounded continuous functions.

## i. Overview

For a sequence of probability measures `μ_n` on the FK configuration space of `ℤ^d`, a shift `g`
and a bounded continuous `f`, let `D_n(f) = ∫ f dμ_n - ∫ f ∘ θ_g dμ_n`. The map `f ↦ D_n(f)` is
linear with `|D_n(f) - D_n(f')| ≤ 2 ‖f - f'‖_∞`, uniformly in `n`. An `ε/3` argument then shows
that if `D_n(f') → 0` for every `f'` in a dense set `D`, then `D_n(f) → 0` for every bounded
continuous `f`. Applied to the wired and free box measures this reduces the integral decay
hypothesis of `ivt_wiredIntegralShiftDecay` to a dense class, and hence translation invariance of
the infinite-volume FK measures to decay on that class.

## ii. Key results

- `isd_decayFun` : the difference `D_n(f)`.
- `isd_decayFun_sub_le` : the uniform Lipschitz bound `|D_n(f) - D_n(f')| ≤ 2 ‖f - f'‖`.
- `isd_tendsto_decay_of_dense` : decay on a dense set implies decay for all `f`.
- `isd_wiredIV_isTranslationInvariant_of_denseDecay`,
  `isd_freeIV_isTranslationInvariant_of_denseDecay` : translation invariance of the
  infinite-volume measures from decay on a dense set.

## iii. Table of contents

- A. The decay functional
- B. Extension from a dense set
- C. Box measures
- D. The identity shift
- E. Translation invariance

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer, 2006, §4.3.
-/

@[expose] public section

open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice

namespace StatMech

namespace FK

variable {d : ℕ}

/-!
## A. The decay functional
-/

/-- The difference `∫ f dμ_n - ∫ f ∘ θ_g dμ_n` between the integrals of `f` and of its shift by
`g` against the `n`-th measure. -/
noncomputable def isd_decayFun (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) (n : ℕ) : ℝ :=
  (∫ x, f x ∂(μ n : Measure _)) - (∫ x, f (shift g x) ∂(μ n : Measure _))

lemma isd_integral_comp_shift (μ : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) :
    (∫ x, (f.compContinuous ⟨shift g, continuous_shift g⟩) x ∂(μ : Measure _))
      = ∫ x, f (shift g x) ∂(μ : Measure _) := by
  simp only [compContinuous_apply, ContinuousMap.coe_mk]

lemma isd_decayFun_sub_le (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (f f' : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) (n : ℕ) :
    |isd_decayFun μ g f n - isd_decayFun μ g f' n| ≤ 2 * ‖f - f'‖ := by
  set T : C(ConfigSpace (Sym2 (Site d)), ConfigSpace (Sym2 (Site d))) :=
    ⟨shift g, continuous_shift g⟩ with hT
  let μn : Measure (ConfigSpace (Sym2 (Site d))) := (μ n : Measure _)
  have hsub1 : (∫ x, f x ∂μn) - (∫ x, f' x ∂μn) = ∫ x, (f - f') x ∂μn := by
    rw [← integral_sub (f.integrable _) (f'.integrable _)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
  have hsub2 : (∫ x, f (shift g x) ∂μn) - (∫ x, f' (shift g x) ∂μn)
      = ∫ x, ((f - f').compContinuous T) x ∂μn := by
    rw [show (fun x => f (shift g x)) = (fun x => (f.compContinuous T) x) from rfl,
      show (fun x => f' (shift g x)) = (fun x => (f'.compContinuous T) x) from rfl,
      ← integral_sub ((f.compContinuous T).integrable _) ((f'.compContinuous T).integrable _)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [BoundedContinuousFunction.compContinuous_apply, BoundedContinuousFunction.coe_sub,
      Pi.sub_apply]
  have hlin : isd_decayFun μ g f n - isd_decayFun μ g f' n
      = (∫ x, (f - f') x ∂μn) - (∫ x, ((f - f').compContinuous T) x ∂μn) := by
    simp only [isd_decayFun]
    rw [← hsub1, ← hsub2]; ring
  rw [hlin]
  calc |(∫ x, (f - f') x ∂μn) - (∫ x, ((f - f').compContinuous T) x ∂μn)|
      ≤ |∫ x, (f - f') x ∂μn| + |∫ x, ((f - f').compContinuous T) x ∂μn| := abs_sub _ _
    _ ≤ ‖f - f'‖ + ‖f - f'‖ := by
        gcongr
        · have := (f - f').norm_integral_le_norm μn
          rwa [Real.norm_eq_abs] at this
        · have h1 := ((f - f').compContinuous T).norm_integral_le_norm μn
          have h2 := (f - f').norm_compContinuous_le T
          rw [Real.norm_eq_abs] at h1
          exact h1.trans h2
    _ = 2 * ‖f - f'‖ := by ring

lemma isd_abs_decay_le (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (f f' : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) (n : ℕ) :
    |isd_decayFun μ g f n| ≤ 2 * ‖f - f'‖ + |isd_decayFun μ g f' n| := by
  have h := isd_decayFun_sub_le μ g f f' n
  have hsplit : |isd_decayFun μ g f n|
      ≤ |isd_decayFun μ g f n - isd_decayFun μ g f' n| + |isd_decayFun μ g f' n| := by
    calc |isd_decayFun μ g f n|
        = |(isd_decayFun μ g f n - isd_decayFun μ g f' n) + isd_decayFun μ g f' n| := by
          ring_nf
      _ ≤ |isd_decayFun μ g f n - isd_decayFun μ g f' n| + |isd_decayFun μ g f' n| :=
          abs_add_le _ _
  linarith [hsplit, h]

/-!
## B. Extension from a dense set
-/

/-- If `D_n(f') → 0` for all `f'` in a dense set of bounded continuous functions, then
`D_n(f) → 0` for every bounded continuous `f`. This is the equicontinuity argument of
`EquicontinuousAt.tendsto_of_mem_closure`, specialized to the uniformly Lipschitz family
`f ↦ D_n(f)`. -/
lemma isd_tendsto_decay_of_dense (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) {D : Set ((ConfigSpace (Sym2 (Site d))) →ᵇ ℝ)}
    (hD : Dense D)
    (hdecay : ∀ f' ∈ D, Tendsto (isd_decayFun μ g f') atTop (𝓝 0))
    (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) :
    Tendsto (isd_decayFun μ g f) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨f', hf'D, hf'close⟩ := hD.exists_dist_lt f (by positivity : (0 : ℝ) < ε / 4)
  have hnorm : ‖f - f'‖ < ε / 4 := by
    rwa [dist_eq_norm] at hf'close
  have hf' := hdecay f' hf'D
  rw [Metric.tendsto_atTop] at hf'
  obtain ⟨N, hN⟩ := hf' (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbound := isd_abs_decay_le μ g f f' n
  have hf'n : |isd_decayFun μ g f' n| < ε / 2 := by
    have := hN n hn
    rwa [Real.dist_eq, sub_zero] at this
  rw [Real.dist_eq, sub_zero]
  calc |isd_decayFun μ g f n|
      ≤ 2 * ‖f - f'‖ + |isd_decayFun μ g f' n| := hbound
    _ < 2 * (ε / 4) + ε / 2 := by gcongr
    _ = ε := by ring

/-!
## C. Box measures
-/

/-- Decay of `D_n` along the wired box measures `φ^1_{Λ_{φ(n)}}` on some dense set of bounded
continuous functions. -/
def isd_wiredDenseDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∃ D : Set ((ConfigSpace (Sym2 (Site d))) →ᵇ ℝ), Dense D ∧
    ∀ f' ∈ D,
      Tendsto (isd_decayFun (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) g f')
        atTop (𝓝 0)

/-- Decay of `D_n` along the free box measures `φ^0_{Λ_{φ(n)}}` on some dense set of bounded
continuous functions. -/
def isd_freeDenseDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∃ D : Set ((ConfigSpace (Sym2 (Site d))) →ᵇ ℝ), Dense D ∧
    ∀ f' ∈ D,
      Tendsto (isd_decayFun (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) g f')
        atTop (𝓝 0)

lemma isd_wiredIntegralShiftDecay_of_dense {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hdense : isd_wiredDenseDecay hp hp1 hq g φ) :
    ivt_wiredIntegralShiftDecay hp hp1 hq g φ := by
  obtain ⟨D, hD, hdecay⟩ := hdense
  intro f
  have := isd_tendsto_decay_of_dense
    (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) g hD hdecay f
  exact this

lemma isd_freeIntegralShiftDecay_of_dense {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hdense : isd_freeDenseDecay hp hp1 hq g φ) :
    ivt_freeIntegralShiftDecay hp hp1 hq g φ := by
  obtain ⟨D, hD, hdecay⟩ := hdense
  intro f
  have := isd_tendsto_decay_of_dense
    (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) g hD hdecay f
  exact this

/-!
## D. The identity shift
-/
lemma isd_decayFun_one (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) (n : ℕ) :
    isd_decayFun μ (1 : Multiplicative (Site d)) f n = 0 := by
  simp only [isd_decayFun, shift_one, id_eq, sub_self]

lemma isd_wiredDenseDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : isd_wiredDenseDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  refine ⟨Set.univ, dense_univ, fun f' _ => ?_⟩
  have hzero : isd_decayFun (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
      (1 : Multiplicative (Site d)) f' = fun _ => (0 : ℝ) := by
    funext n; exact isd_decayFun_one _ f' n
  rw [hzero]
  exact tendsto_const_nhds

lemma isd_freeDenseDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : isd_freeDenseDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  refine ⟨Set.univ, dense_univ, fun f' _ => ?_⟩
  have hzero : isd_decayFun (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
      (1 : Multiplicative (Site d)) f' = fun _ => (0 : ℝ) := by
    funext n; exact isd_decayFun_one _ f' n
  rw [hzero]
  exact tendsto_const_nhds

/-!
## E. Translation invariance
-/

/-- The wired infinite-volume FK measure is translation invariant if, for every shift and every
convergent box subsequence, `D_n` decays on a dense set. See also
`flc_wiredIV_isTranslationInvariant` (unconditional for `q = 2`). -/
lemma isd_wiredIV_isTranslationInvariant_of_denseDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hdense : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        isd_wiredDenseDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  ivt_wiredIV_isTranslationInvariant_of_decay hp hp1 hq
    (fun g φ hφ hconv => isd_wiredIntegralShiftDecay_of_dense hp hp1 hq g φ
      (hdense g φ hφ hconv))

/-- The free infinite-volume FK measure is translation invariant if, for every shift and every
convergent box subsequence, `D_n` decays on a dense set. See also
`bdp_freeIV_isTranslationInvariant` (unconditional for `q = 2`). -/
lemma isd_freeIV_isTranslationInvariant_of_denseDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hdense : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        isd_freeDenseDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  ivt_freeIV_isTranslationInvariant_of_decay hp hp1 hq
    (fun g φ hφ hconv => isd_freeIntegralShiftDecay_of_dense hp hp1 hq g φ
      (hdense g φ hφ hconv))

end FK

end StatMech
