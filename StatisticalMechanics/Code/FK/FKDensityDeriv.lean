/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































































import Mathlib
import Code.FK.FKPressureDeriv
import Code.FK.AvgDensityCollapse
import Code.FK.FKUniquenessSkeleton

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice




























theorem fdd_avgLimit_le_rightDeriv {κ : Type*} {l : Filter κ} [l.NeBot]
    (gn : κ → ℝ → ℝ) (g : ℝ → ℝ) (dn : κ → ℝ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ univ (gn i))
    (hderiv : ∀ i t, HasDerivAt (gn i) (dn i t) t)
    (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (g x)))
    (t ℓ : ℝ) (hg : ConvexOn ℝ univ g)
    (hℓ : Tendsto (fun i => dn i t) l (𝓝 ℓ)) :
    ℓ ≤ pressureRightDeriv g t := by
  have hr := cdl_rightDeriv_tendsto_slope hg t
  have key : ∀ y, t < y → ℓ ≤ slope g t y := by
    intro y hty
    have hd : ∀ i, dn i t ≤ slope (gn i) t y := by
      intro i
      have hmem : t ∈ interior (univ : Set ℝ) := by rw [interior_univ]; trivial
      have hr' : derivWithin (gn i) (Ioi t) t = dn i t :=
        ((hderiv i t).hasDerivWithinAt (s := Ioi t)).derivWithin (uniqueDiffWithinAt_Ioi t)
      have h3 := (hconv i).rightDeriv_le_slope_of_mem_interior hmem (mem_univ y) hty
      rwa [hr'] at h3
    exact le_of_tendsto_of_tendsto hℓ (cdl_slope_tendsto gn g hlim t y)
      (Filter.Eventually.of_forall hd)
  refine ge_of_tendsto hr ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : t < y)
  exact key y hy










theorem fdd_leftDeriv_le_avgLimit {κ : Type*} {l : Filter κ} [l.NeBot]
    (gn : κ → ℝ → ℝ) (g : ℝ → ℝ) (dn : κ → ℝ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ univ (gn i))
    (hderiv : ∀ i t, HasDerivAt (gn i) (dn i t) t)
    (hlim : ∀ x, Tendsto (fun i => gn i x) l (𝓝 (g x)))
    (t ℓ : ℝ) (hg : ConvexOn ℝ univ g)
    (hℓ : Tendsto (fun i => dn i t) l (𝓝 ℓ)) :
    pressureLeftDeriv g t ≤ ℓ := by
  have hlft := cdl_leftDeriv_tendsto_slope hg t
  have key : ∀ z, z < t → slope g t z ≤ ℓ := by
    intro z hzt
    rw [slope_comm]
    have hd : ∀ i, slope (gn i) z t ≤ dn i t := by
      intro i
      have hmem : t ∈ interior (univ : Set ℝ) := by rw [interior_univ]; trivial
      have hl' : derivWithin (gn i) (Iio t) t = dn i t :=
        ((hderiv i t).hasDerivWithinAt (s := Iio t)).derivWithin (uniqueDiffWithinAt_Iio t)
      have h3 := (hconv i).slope_le_leftDeriv_of_mem_interior (mem_univ z) hmem hzt
      rwa [hl'] at h3
    exact le_of_tendsto_of_tendsto (cdl_slope_tendsto gn g hlim z t) hℓ
      (Filter.Eventually.of_forall hd)
  refine le_of_tendsto hlft ?_
  filter_upwards [self_mem_nhdsWithin] with z (hz : z < t)
  exact key z hz









variable {d : ℕ}





theorem fdd_avgDensity_le_rightDeriv
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : ℕ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (t ℓ : ℝ) (hℓ : Tendsto (fun n => fpd_avgDensity (Gn n) t) atTop (𝓝 ℓ)) :
    ℓ ≤ pressureRightDeriv g t :=
  fdd_avgLimit_le_rightDeriv
    (fun n => ivp2_tiltFreeEnergy (Gn n) 2) g (fun n => fpd_avgDensity (Gn n))
    (fun n => ivp2_tiltFreeEnergy_convexOn (Gn n) 2 (by norm_num) (hE n))
    (fun n s => fpd_tiltFreeEnergy_deriv_eq_avgDensity (Gn n) (hE n) s)
    hlim t ℓ hg hℓ





theorem fdd_leftDeriv_le_avgDensity
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : ℕ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (t ℓ : ℝ) (hℓ : Tendsto (fun n => fpd_avgDensity (Gn n) t) atTop (𝓝 ℓ)) :
    pressureLeftDeriv g t ≤ ℓ :=
  fdd_leftDeriv_le_avgLimit
    (fun n => ivp2_tiltFreeEnergy (Gn n) 2) g (fun n => fpd_avgDensity (Gn n))
    (fun n => ivp2_tiltFreeEnergy_convexOn (Gn n) 2 (by norm_num) (hE n))
    (fun n s => fpd_tiltFreeEnergy_deriv_eq_avgDensity (Gn n) (hE n) s)
    hlim t ℓ hg hℓ

















theorem fdd_freeDensity_le_rightDeriv (N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ≤ pressureRightDeriv g t :=
  fdd_avgDensity_le_rightDeriv Gn hE g hg hlim t _ (hcol e' t)






theorem fdd_leftDeriv_le_freeDensity (N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    pressureLeftDeriv g t ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) :=
  fdd_leftDeriv_le_avgDensity Gn hE g hg hlim t _ (hcol e' t)





theorem fdd_freeDensity_bracket (N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    pressureLeftDeriv g t ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)
      ∧ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ≤ pressureRightDeriv g t :=
  ⟨fdd_leftDeriv_le_freeDensity N Gn hE g hg hlim hcol e' t,
    fdd_freeDensity_le_rightDeriv N Gn hE g hg hlim hcol e' t⟩



















theorem fdd_free_is_leftDeriv_at_diff (N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hdiff : pressureLeftDeriv g t = pressureRightDeriv g t) :
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t :=
  fpd_freeDensity_at_diff_of_collapse d N Gn hE g hg hlim hcol e' t hdiff





















theorem fdd_eq_leftDeriv_of_bracket_leftContinuous {g a : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hbL : ∀ s, pressureLeftDeriv g s ≤ a s) (hbR : ∀ s, a s ≤ pressureRightDeriv g s)
    {t : ℝ} (hlc : ContinuousWithinAt a (Iio t) t) :
    a t = pressureLeftDeriv g t := by
  refine le_antisymm ?_ (hbL t)
  have hbound : ∀ z, z < t → a z ≤ pressureLeftDeriv g t := fun z hzt =>
    (hbR z).trans (pressureRightDeriv_le_leftDeriv_of_lt hg hzt)
  refine le_of_tendsto (show Tendsto a (𝓝[<] t) (𝓝 (a t)) from hlc) ?_
  filter_upwards [self_mem_nhdsWithin] with z (hz : z < t)
  exact hbound z hz










theorem fdd_eq_rightDeriv_of_bracket_rightContinuous {g a : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hbL : ∀ s, pressureLeftDeriv g s ≤ a s) (hbR : ∀ s, a s ≤ pressureRightDeriv g s)
    {t : ℝ} (hrc : ContinuousWithinAt a (Ioi t) t) :
    a t = pressureRightDeriv g t := by
  refine le_antisymm (hbR t) ?_
  have hbound : ∀ y, t < y → pressureRightDeriv g t ≤ a y := fun y hty =>
    (pressureRightDeriv_le_leftDeriv_of_lt hg hty).trans (hbL y)
  refine ge_of_tendsto (show Tendsto a (𝓝[>] t) (𝓝 (a t)) from hrc) ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : t < y)
  exact hbound y hy














theorem fdd_free_is_leftDeriv_of_leftContinuous (N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hlc : ContinuousWithinAt
      (fun s => freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Iio t) t) :
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t :=
  fdd_eq_leftDeriv_of_bracket_leftContinuous hg
    (fun s => fdd_leftDeriv_le_freeDensity N Gn hE g hg hlim hcol e' s)
    (fun s => fdd_freeDensity_le_rightDeriv N Gn hE g hg hlim hcol e' s) hlc






























def fdd_FreeDensityIsLeftDeriv (N : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureLeftDeriv g t










def fdd_WiredDensityIsRightDeriv (N : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureRightDeriv g t
















def fdd_WiredDensityUpperBound (N : ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ),
    wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ≤ pressureRightDeriv g t










theorem fdd_leftDeriv_le_wiredDensity (N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    pressureLeftDeriv g t ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) :=
  (fdd_leftDeriv_le_freeDensity N Gn hE g hg hlim hcol e' t).trans
    (freeEdgeDensity_q2_le_wiredEdgeDensity d N e' (fsc_logistic_pos t) (fsc_logistic_lt_one t))















theorem fdd_wired_is_rightDeriv_of_upperBound_rightContinuous (N : ℕ)
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (hub : fdd_WiredDensityUpperBound (d := d) N g)
    (e' : Sym2 (boxVerts d N)) (t : ℝ)
    (hrc : ContinuousWithinAt
      (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
    wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) = pressureRightDeriv g t :=
  fdd_eq_rightDeriv_of_bracket_rightContinuous hg
    (fun s => fdd_leftDeriv_le_wiredDensity N Gn hE g hg hlim hcol e' s)
    (fun s => hub e' s) hrc






theorem fdd_IVDensityIsOneSidedDeriv_iff (N : ℕ) (g : ℝ → ℝ) :
    fpd_IVDensityIsOneSidedDeriv d N g
      ↔ fdd_WiredDensityIsRightDeriv (d := d) N g ∧ fdd_FreeDensityIsLeftDeriv (d := d) N g :=
  Iff.rfl





theorem fdd_IVDensityIsOneSidedDeriv_of_halves (N : ℕ) (g : ℝ → ℝ)
    (hwired : fdd_WiredDensityIsRightDeriv (d := d) N g)
    (hfree : fdd_FreeDensityIsLeftDeriv (d := d) N g) :
    fpd_IVDensityIsOneSidedDeriv d N g :=
  ⟨hwired, hfree⟩



















theorem fdd_fk_uniqueness (N : ℕ) (eb : Sym2 (boxVerts d N)) {g : ℝ → ℝ}
    (hg : ConvexOn ℝ univ g)
    (hwired : fdd_WiredDensityIsRightDeriv (d := d) N g)
    (hfree : fdd_FreeDensityIsLeftDeriv (d := d) N g) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fpd_fk_uniqueness d N eb hg (fdd_IVDensityIsOneSidedDeriv_of_halves N g hwired hfree)



















theorem fdd_fk_uniqueness_of_primitives (N : ℕ) (eb : Sym2 (boxVerts d N))
    (Gn : ℕ → SimpleGraph (boxVerts d N)) [∀ n, DecidableRel (Gn n).Adj]
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hlim : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpd_AvgDensityCollapse d N Gn)
    (hflc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt
      (fun s => freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Iio t) t)
    (hwub : fdd_WiredDensityUpperBound (d := d) N g)
    (hwrc : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ContinuousWithinAt
      (fun s => wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)) (Ioi t) t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fdd_fk_uniqueness N eb hg
    (fun e' t =>
      fdd_wired_is_rightDeriv_of_upperBound_rightContinuous N Gn hE hg hlim hcol hwub e' t
        (hwrc e' t))
    (fun e' t =>
      fdd_free_is_leftDeriv_of_leftContinuous N Gn hE g hg hlim hcol e' t (hflc e' t))













theorem fdd_halves_imp_fsc (N : ℕ) {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hwired : fdd_WiredDensityIsRightDeriv (d := d) N g)
    (hfree : fdd_FreeDensityIsLeftDeriv (d := d) N g) (e' : Sym2 (boxVerts d N)) :
    fsc_FreeEnergyData d N e' :=
  fpd_densityDeriv_imp_fsc d N hg (fdd_IVDensityIsOneSidedDeriv_of_halves N g hwired hfree) e'

end FK

end StatMech
