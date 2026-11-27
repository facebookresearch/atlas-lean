/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.BrownianMotion.BrownianDyadicApproximation

/-!
# The continuous modification of the coordinate process

The dyadic limits on `[-N, N]` agree for different `N`, so taking `N = ⌈|t|⌉` defines a process
`brownianContinuousModification t ω` on all of `ℝ`. Its paths are continuous on the almost sure
event of `BrownianDyadicControl`. That it is a modification of the coordinate process, and a
standard Brownian motion, is proved in `BrownianModificationLaw`.

## Main definitions

* `StatMech.SLE.brownianContinuousModification`: `t ↦ brownianDyadicLimit ⌈|t|⌉ t ω`.

## Main results

* `StatMech.SLE.continuous_brownianContinuousModification`: on the good event the paths are
  continuous.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace StatMech.SLE

/-- Approximation indices for the windows `[-N, N] ⊆ [-L, L]` differ by a shift. -/
theorem brownianDyadicApproxIndex_eq_add (N L n : Nat) {t : Real}
    (hNL : N ≤ L) (htLower : -(N : Real) ≤ t) :
    brownianDyadicApproxIndex L n t =
      brownianDyadicApproxIndex N n t +
        (L - N) * brownianDyadicDenominator n := by
  have hx : 0 ≤ (t + N) * brownianDyadicDenominator n :=
    mul_nonneg (by linarith) (by positivity)
  have harg : (t + L) * brownianDyadicDenominator n =
      (t + N) * brownianDyadicDenominator n +
        (((L - N) * brownianDyadicDenominator n : Nat) : Real) := by
    push_cast
    have hLN : (L : Real) = N + (L - N : Nat) := by
      exact_mod_cast (Nat.add_sub_of_le hNL).symm
    rw [hLN]
    ring
  unfold brownianDyadicApproxIndex
  rw [harg, Nat.floor_add_natCast hx]

/-- The approximating grid point does not depend on the window. -/
theorem brownianDyadicApproxPoint_eq_of_le (N L n : Nat) {t : Real}
    (hNL : N ≤ L) (htLower : -(N : Real) ≤ t) :
    brownianDyadicApproxPoint L n t = brownianDyadicApproxPoint N n t := by
  unfold brownianDyadicApproxPoint brownianDyadicPoint
  rw [brownianDyadicApproxIndex_eq_add N L n hNL htLower]
  push_cast
  have hD : ((brownianDyadicDenominator n : Nat) : Real) ≠ 0 := by
    exact_mod_cast (brownianDyadicDenominator_pos n).ne'
  have hLN : (L : Real) = N + (L - N : Nat) := by
    exact_mod_cast (Nat.add_sub_of_le hNL).symm
  rw [hLN]
  field_simp [hD]
  ring

/-- The dyadic limit does not depend on the window. -/
theorem brownianDyadicLimit_eq_of_le (omega : Real → Real)
    (N L : Nat) {t : Real} (hNL : N ≤ L) (htLower : -(N : Real) ≤ t) :
    brownianDyadicLimit L t omega = brownianDyadicLimit N t omega := by
  unfold brownianDyadicLimit
  congr 1
  funext n
  rw [brownianDyadicApproxPoint_eq_of_le N L n hNL htLower]

/-- The window radius `⌈|t|⌉` used to define the modification at time `t`. -/
noncomputable def brownianCompactRadius (t : Real) : Nat := Nat.ceil |t|

theorem neg_brownianCompactRadius_le (t : Real) :
    -(brownianCompactRadius t : Real) ≤ t := by
  apply neg_le_of_abs_le
  exact Nat.le_ceil |t|

theorem le_brownianCompactRadius (t : Real) :
    t ≤ brownianCompactRadius t := by
  exact (le_abs_self t).trans (Nat.le_ceil |t|)

/-- The continuous modification of the coordinate process: the dyadic limit at `t` computed in the
window `[-⌈|t|⌉, ⌈|t|⌉]`. -/
noncomputable def brownianContinuousModification (t : Real)
    (omega : Real → Real) : Real :=
  brownianDyadicLimit (brownianCompactRadius t) t omega

/-- On `[-N, N]` the modification equals the dyadic limit for the window `N`. -/
theorem brownianContinuousModification_eq_dyadicLimit
    (omega : Real → Real) (N : Nat) {t : Real}
    (htLower : -(N : Real) ≤ t) (htUpper : t ≤ N) :
    brownianContinuousModification t omega = brownianDyadicLimit N t omega := by
  have hRadius : brownianCompactRadius t ≤ N := by
    unfold brownianCompactRadius
    exact Nat.ceil_le.mpr (abs_le.mpr ⟨htLower, htUpper⟩)
  change brownianDyadicLimit (brownianCompactRadius t) t omega =
    brownianDyadicLimit N t omega
  exact (brownianDyadicLimit_eq_of_le omega (brownianCompactRadius t) N hRadius
    (neg_brownianCompactRadius_le t)).symm

/-- On the good event the paths of the modification are continuous. -/
theorem continuous_brownianContinuousModification
    (omega : Real → Real)
    (hgood : ∀ N : Nat, ∀ᶠ n in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
        edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
            brownianDyadicThreshold n) :
    Continuous (fun t => brownianContinuousModification t omega) := by
  rw [continuous_iff_continuousAt]
  intro t
  let N : Nat := brownianCompactRadius t + 1
  have htLower : -(N : Real) < t := by
    have h := neg_brownianCompactRadius_le t
    dsimp only [N]
    push_cast
    linarith
  have htUpper : t < N := by
    have h := le_brownianCompactRadius t
    dsimp only [N]
    push_cast
    linarith
  have hfixed : ContinuousAt (fun s => brownianDyadicLimit N s omega) t :=
    ((continuousOn_brownianDyadicLimit omega N (hgood N))
      t ⟨htLower.le, htUpper.le⟩).continuousAt (Icc_mem_nhds htLower htUpper)
  apply hfixed.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds htLower htUpper] with s hs
  exact brownianContinuousModification_eq_dyadicLimit omega N hs.1 hs.2

end StatMech.SLE
