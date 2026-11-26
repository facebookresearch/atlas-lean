/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.KestenHalf
public import MathlibExt.Probability.Percolation.Universality.RSWStrip

/-!
# Zhang's lower bound `θ(1/2) = 0`, conditional on the side-union convergence

Harris's theorem `θ(1/2) = 0` for bond percolation on `ℤ²` (equivalently `p_c ≥ 1/2`), in the
form of Zhang's argument: a box-crossing event `A n` that is exchanged with its complement by a
measure-preserving symmetry composed with duality has probability exactly `1/2`; if `θ(1/2) > 0`
forced `ℙ(A n ∪ B n) → 1` for an increasing companion `B n` of equal probability, the square-root
trick would give `ℙ(A n) → 1`, a contradiction.

## Main results

* `StatMech.TwoDim.kzh_crossing_to_one_of_union`: `ℙ(A n ∪ B n) → 1` and `ℙ(A n) = ℙ(B n)` for
  increasing events give `ℙ(A n) → 1`.
* `StatMech.TwoDim.kzh_corLowerBound`: `θ(1/2) = 0`, given the self-dual dichotomy `hdich` and
  the hypothesis `hZhangUnion`.

## Implementation notes

`hZhangUnion` (`θ(1/2) > 0` implies `ℙ(A n ∪ B n) → 1`) carries the geometric content of Zhang's
argument (uniqueness of the infinite cluster and the fourth-root trick applied to the four sides
of a box); it is not proved in the library. `hdich` asks for a measurable measure-preserving map
`R` with `(A n)ᶜ = (R ∘ dualConfig)⁻¹' (A n)`; since `dualConfig` labels dual edges by a quarter
turn about the origin (`StatMech.Lattice.crossEdge`) rather than by the geometric crossing, for a
crossing event `R` must also convert this labelling into the geometric dual rectangle. No
instance of `A`, `B`, `R` satisfying all hypotheses is constructed in the library.

## References

* Y. Zhang, 1988, unpublished; see G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, §11.3.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Cambridge Philos. Soc. 56 (1960), 13–20.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality

/-- `θ(1/2)` as a real number is `halfMeasure.real (percolationEvent 2)`. -/
theorem kzh_theta_real :
    (percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one).toReal
      = halfMeasure.real (percolationEvent 2) := rfl

/-- `halfMeasure.real (percolationEvent 2) = 0` gives `percolationProbability 2 (1/2) = 0`. -/
theorem kzh_percProb_eq_zero_of_thetaReal_zero
    (h : halfMeasure.real (percolationEvent 2) = 0) :
    percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
  unfold percolationProbability
  have hle : halfMeasure (percolationEvent 2) ≤ 1 :=
    le_trans (measure_mono (subset_univ _)) (by simp [measure_univ])
  have hfin : halfMeasure (percolationEvent 2) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  have hr : (halfMeasure (percolationEvent 2)).toReal = 0 := h
  exact (ENNReal.toReal_eq_zero_iff _).mp hr |>.resolve_right hfin

/-- Square-root trick in the limit: for increasing events with `ℙ(A n) = ℙ(B n)` and
`ℙ(A n ∪ B n) → 1` under a positively associated `halfMeasure`, `ℙ(A n) → 1`. -/
theorem kzh_crossing_to_one_of_union
    (hpa : PositivelyAssociated halfMeasure)
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hAinc : ∀ n, IsIncreasing (A n)) (hBinc : ∀ n, IsIncreasing (B n))
    (hAm : ∀ n, MeasurableSet (A n)) (hBm : ∀ n, MeasurableSet (B n))
    (heq : ∀ n, halfMeasure.real (A n) = halfMeasure.real (B n))
    (hunion : Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1)) :
    Tendsto (fun n => halfMeasure.real (A n)) atTop (𝓝 1) := by
  have hlb : ∀ n,
      1 - Real.sqrt (1 - halfMeasure.real (A n ∪ B n)) ≤ halfMeasure.real (A n) :=
    fun n => rsw_sqrt_trick_eq halfMeasure hpa (hAinc n) (hBinc n) (hAm n) (hBm n) (heq n)
  have hub : ∀ n, halfMeasure.real (A n) ≤ 1 := fun _ => measureReal_le_one
  have hlbtends :
      Tendsto (fun n => 1 - Real.sqrt (1 - halfMeasure.real (A n ∪ B n))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n => (1 : ℝ) - halfMeasure.real (A n ∪ B n)) atTop (𝓝 0) := by
      have := hunion.const_sub (1 : ℝ); simpa using this
    have h2 : Tendsto (fun n => Real.sqrt (1 - halfMeasure.real (A n ∪ B n))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h1; simpa [Function.comp_def] using this
    have := h2.const_sub (1 : ℝ); simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlbtends tendsto_const_nhds hlb hub

/-- **Harris's theorem** `θ(1/2) = 0` on `ℤ²` via Zhang's argument (Harris, 1960; Zhang, 1988,
unpublished; see Grimmett, *Percolation*, 1999, §11.3), conditional form.

The content is carried by `hZhangUnion` (if `θ(1/2) > 0`, then `ℙ(A n ∪ B n) → 1`) and by the
self-dual dichotomy `hdich` for `A n`; both are hypotheses, see the module docstring. The
assumption `BoxCrossingProperty halfMeasure 2` is only passed on to `hZhangUnion`. -/
theorem kzh_corLowerBound
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hpa : PositivelyAssociated halfMeasure)
    (hAinc : ∀ n, IsIncreasing (A n)) (hBinc : ∀ n, IsIncreasing (B n))
    (hBm : ∀ n, MeasurableSet (B n))
    (hHm : ∀ n, MeasurableSet (A n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (A n)ᶜ = (R ∘ dualConfig) ⁻¹' (A n))
    (heq : ∀ n, halfMeasure.real (A n) = halfMeasure.real (B n))
    (hZhangUnion : BoxCrossingProperty halfMeasure 2 →
        0 < halfMeasure.real (percolationEvent 2) →
        Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1)) :
    BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
  intro hbxp
  have hbalance : ∀ n : ℕ, halfMeasure.real (A n) = 1 / 2 := fun n =>
    half_crossingProb_of_selfDual_dichotomy (hHm n) hRmeas hRpres (hdich n)
  have hθ0 : halfMeasure.real (percolationEvent 2) = 0 := by
    by_contra hne
    have hpos : 0 < halfMeasure.real (percolationEvent 2) :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    have hunion : Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1) :=
      hZhangUnion hbxp hpos
    have hto1 : Tendsto (fun n => halfMeasure.real (A n)) atTop (𝓝 1) :=
      kzh_crossing_to_one_of_union hpa hAinc hBinc hHm hBm heq hunion
    have hconst : Tendsto (fun n => halfMeasure.real (A n)) atTop (𝓝 (1 / 2 : ℝ)) := by
      have hfun : (fun n => halfMeasure.real (A n)) = fun _ => (1 / 2 : ℝ) := funext hbalance
      rw [hfun]; exact tendsto_const_nhds
    have hbad : (1 / 2 : ℝ) = 1 := tendsto_nhds_unique hconst hto1
    norm_num at hbad
  exact kzh_percProb_eq_zero_of_thetaReal_zero hθ0

end TwoDim

end StatMech
