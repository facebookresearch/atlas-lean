/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolumeTranslationInvariance
public import MathlibExt.Probability.Configuration.WeakConvergence
/-!
# Translation invariance of infinite-volume FK measures from integral decay

Translation invariance of the wired and free infinite-volume FK measures follows from decay
of the difference between the box integrals of `f` and of `f ∘ shift g`.

## i. Overview

Fix `p ∈ (0, 1)` and `q > 0`. The wired and free infinite-volume FK measures `φ^ξ_p` on `ℤ^d`
are weak limits of the finite-volume measures `φ^ξ_{Λ_n}` on the centered boxes. For a shift
`g ∈ ℤ^d`, the push-forward of `φ^ξ_{Λ_n}` by the shift `θ_g` integrates `f` to
`∫ f ∘ θ_g dφ^ξ_{Λ_n}`. If, along every subsequence on which the box measures converge to
`φ^ξ_p`, the difference `∫ f dφ^ξ_{Λ_n} - ∫ f ∘ θ_g dφ^ξ_{Λ_n}` tends to zero for every bounded
continuous `f`, then the shifted box measures converge to `φ^ξ_p` as well, and `θ_g` preserves
`φ^ξ_p`. The decay hypothesis holds trivially for the identity shift.

The unconditional translation invariance is `flc_wiredIV_isTranslationInvariant` and
`bdp_freeIV_isTranslationInvariant` (for `q = 2`).

## ii. Key results

- `ivt_wiredIntegralShiftDecay`, `ivt_freeIntegralShiftDecay` : the integral decay hypothesis.
- `ivt_wiredShifted_weakConverges_of_decay` : decay makes the shifted box measures converge to
  the infinite-volume measure.
- `ivt_wiredIV_isTranslationInvariant_of_decay`, `ivt_freeIV_isTranslationInvariant_of_decay` :
  translation invariance from decay for every shift.

## iii. Table of contents

- A. Integrals against shifted box measures
- B. The integral decay hypothesis
- C. Translation invariance from decay
- D. The identity shift

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
## A. Integrals against shifted box measures
-/
lemma ivt_integral_wiredShifted {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (n : ℕ) (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) :
    (∫ x, f x ∂((erg_wiredShiftedFinite hp hp1 hq g n : ProbabilityMeasure _) : Measure _))
      = ∫ x, f (shift g x)
          ∂((wiredFiniteMeasure d n hp hp1 hq : ProbabilityMeasure _) : Measure _) := by
  unfold erg_wiredShiftedFinite
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_shift g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]

lemma ivt_integral_freeShifted {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (n : ℕ) (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) :
    (∫ x, f x ∂((erg_freeShiftedFinite hp hp1 hq g n : ProbabilityMeasure _) : Measure _))
      = ∫ x, f (shift g x)
          ∂((freeFiniteMeasure d n hp hp1 hq : ProbabilityMeasure _) : Measure _) := by
  unfold erg_freeShiftedFinite
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_shift g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]

/-!
## B. The integral decay hypothesis
-/

/-- Along the box sequence `φ`, the wired box integrals of `f` and of `f ∘ θ_g` differ by a
quantity tending to zero, for every bounded continuous `f`. -/
def ivt_wiredIntegralShiftDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ,
    Tendsto (fun n =>
        (∫ x, f x ∂((wiredFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((wiredFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)))
      atTop (𝓝 0)

/-- Along the box sequence `φ`, the free box integrals of `f` and of `f ∘ θ_g` differ by a
quantity tending to zero, for every bounded continuous `f`. -/
def ivt_freeIntegralShiftDecay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ,
    Tendsto (fun n =>
        (∫ x, f x ∂((freeFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((freeFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)))
      atTop (𝓝 0)

/-!
## C. Translation invariance from decay
-/
lemma ivt_wiredShifted_weakConverges_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
        (wiredInfiniteVolume d hp hp1 hq))
    (hdecay : ivt_wiredIntegralShiftDecay hp hp1 hq g φ) :
    WeakConvergesTo (fun n => erg_wiredShiftedFinite hp hp1 hq g (φ n))
        (wiredInfiniteVolume d hp hp1 hq) := by
  apply weakConvergesTo_of_forall_tendsto_integral
  intro f
  have hcentred := hconv.tendsto_integral f
  have key :
      Tendsto (fun n => ∫ x, f (shift g x)
          ∂((wiredFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)) atTop
        (𝓝 (∫ x, f x
          ∂((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure _) : Measure _))) := by
    have hsub := hcentred.sub (hdecay f)
    simp only [sub_zero] at hsub
    exact hsub.congr (fun n => by ring)
  exact key.congr (fun n => (ivt_integral_wiredShifted hp hp1 hq g (φ n) f).symm)

lemma ivt_freeShifted_weakConverges_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
        (freeInfiniteVolume d hp hp1 hq))
    (hdecay : ivt_freeIntegralShiftDecay hp hp1 hq g φ) :
    WeakConvergesTo (fun n => erg_freeShiftedFinite hp hp1 hq g (φ n))
        (freeInfiniteVolume d hp hp1 hq) := by
  apply weakConvergesTo_of_forall_tendsto_integral
  intro f
  have hcentred := hconv.tendsto_integral f
  have key :
      Tendsto (fun n => ∫ x, f (shift g x)
          ∂((freeFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)) atTop
        (𝓝 (∫ x, f x
          ∂((freeInfiniteVolume d hp hp1 hq : ProbabilityMeasure _) : Measure _))) := by
    have hsub := hcentred.sub (hdecay f)
    simp only [sub_zero] at hsub
    exact hsub.congr (fun n => by ring)
  exact key.congr (fun n => (ivt_integral_freeShifted hp hp1 hq g (φ n) f).symm)

lemma ivt_wiredIV_map_shift_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d))
    (hdecay : ∀ φ : ℕ → ℕ, StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        ivt_wiredIntegralShiftDecay hp hp1 hq g φ) :
    Measure.map (shift g)
        (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
      = (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  erg_wiredIV_map_shift hp hp1 hq g
    (fun φ hφ hconv => ivt_wiredShifted_weakConverges_of_decay hp hp1 hq g φ hconv
      (hdecay φ hφ hconv))

lemma ivt_freeIV_map_shift_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d))
    (hdecay : ∀ φ : ℕ → ℕ, StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        ivt_freeIntegralShiftDecay hp hp1 hq g φ) :
    Measure.map (shift g)
        (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
      = (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) :=
  erg_freeIV_map_shift hp hp1 hq g
    (fun φ hφ hconv => ivt_freeShifted_weakConverges_of_decay hp hp1 hq g φ hconv
      (hdecay φ hφ hconv))

/-- The wired infinite-volume FK measure is translation invariant if the integral decay
hypothesis holds for every shift and every convergent box subsequence. See also
`flc_wiredIV_isTranslationInvariant`, which proves invariance for `q = 2` without hypotheses. -/
lemma ivt_wiredIV_isTranslationInvariant_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq)
          (wiredInfiniteVolume d hp hp1 hq) →
        ivt_wiredIntegralShiftDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  exact ⟨measurable_shift g, ivt_wiredIV_map_shift_of_decay hp hp1 hq g (hdecay g)⟩

/-- The free infinite-volume FK measure is translation invariant if the integral decay hypothesis
holds for every shift and every convergent box subsequence. See also
`bdp_freeIV_isTranslationInvariant`, which proves invariance for `q = 2` without hypotheses. -/
lemma ivt_freeIV_isTranslationInvariant_of_decay {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q)
    (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq)
          (freeInfiniteVolume d hp hp1 hq) →
        ivt_freeIntegralShiftDecay hp hp1 hq g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
  intro g
  exact ⟨measurable_shift g, ivt_freeIV_map_shift_of_decay hp hp1 hq g (hdecay g)⟩

/-!
## D. The identity shift
-/

/-- The identity shift satisfies the wired decay hypothesis, so it is not vacuous. -/
lemma ivt_wiredIntegralShiftDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : ivt_wiredIntegralShiftDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  intro f
  have hzero : (fun n =>
      (∫ x, f x ∂((wiredFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _))
        - (∫ x, f (shift (1 : Multiplicative (Site d)) x)
            ∂((wiredFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)))
      = fun _ => (0 : ℝ) := by
    funext n
    simp only [shift_one, id_eq, sub_self]
  rw [hzero]
  exact tendsto_const_nhds

/-- The identity shift satisfies the free decay hypothesis, so it is not vacuous. -/
lemma ivt_freeIntegralShiftDecay_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (φ : ℕ → ℕ) : ivt_freeIntegralShiftDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
  intro f
  have hzero : (fun n =>
      (∫ x, f x ∂((freeFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _))
        - (∫ x, f (shift (1 : Multiplicative (Site d)) x)
            ∂((freeFiniteMeasure d (φ n) hp hp1 hq : ProbabilityMeasure _) : Measure _)))
      = fun _ => (0 : ℝ) := by
    funext n
    simp only [shift_one, id_eq, sub_self]
  rw [hzero]
  exact tendsto_const_nhds

end FK

end StatMech
