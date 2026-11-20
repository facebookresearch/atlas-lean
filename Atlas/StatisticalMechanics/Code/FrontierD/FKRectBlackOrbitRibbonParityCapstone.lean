/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionNonUturn



namespace StatMech.FrontierD

open StatMech.Onsager
open StatMech.Onsager.BaseCase

noncomputable section


def fkRectBlackOrbitFaithfulRibbonSubdivisionDart
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length →
      ons_Dart (fkRectBlackOrbitRibbonSubdivisionSide R) :=
  fun k =>
    let z := fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d (-k)
    (fkRectBlackOrbitRibbonSubdivisionSite R omega d z,
      fkRectBlackOrbitMedialRibbonFlatDirection R omega d z.1)

theorem fkRectBlackOrbitFaithfulRibbonSubdivisionDart_valid
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    ∀ k,
      (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).1 =
        ons_dirStep (fkRectBlackOrbitRibbonSubdivisionSide R)
          (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d (k + 1)).2
          (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d (k + 1)).1 := by
  intro k
  let j := -(k + 1)
  have hj : j + 1 = -k := by
    dsimp [j]
    abel
  change fkRectBlackOrbitRibbonSubdivisionSite R omega d
      (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d (-k)) = _
  rw [← hj, fkRectBlackOrbitRibbonSubdivisionIndexEquiv_add_one]
  exact fkRectBlackOrbitRibbonSubdivisionSite_succ R omega d _

theorem fkRectBlackOrbitFaithfulRibbonSubdivisionDart_site_injective
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    Function.Injective (fun k =>
      (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).1) := by
  intro i j h
  have hz := fkRectBlackOrbitRibbonSubdivisionSite_injective R omega d h
  have hk := (fkRectBlackOrbitRibbonSubdivisionIndexEquiv R omega d).injective hz
  simpa using congrArg Neg.neg hk

@[simp] theorem fkRectBlackOrbitFaithfulRibbonSubdivisionDart_direction
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (k : Fin (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length) :
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).2 =
      (fkRectBlackOrbitRibbonSubdivisionWord R omega d).get (-k) := by
  exact (fkRectBlackOrbitRibbonSubdivisionWord_get R omega d (-k)).symm

theorem fkRectBlackOrbitFaithfulRibbonSubdivisionDart_nonUturn
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    ∀ k,
      (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).2 ≠
        (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d (k + 1)).2 + 2 := by
  intro k
  have h := fkRectBlackOrbitRibbonSubdivisionDirection_nonUturn R omega d
    (-(k + 1))
  have hidx : -(k + 1) + 1 = -k := by abel
  rw [hidx] at h
  exact h

theorem fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentX_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    (∑ k, ons_dirExponentX
      (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).2) =
        (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.1 := by
  simpa using fkRectBlackOrbitRibbonSubdivisionDart_exponentX_sum R omega d

theorem fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentY_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let w := fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)
    (∑ k, ons_dirExponentY
      (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d k).2) =
        (fkRectBlackOrbitRibbonSubdivisionSide R : ℤ) * w.2 := by
  simpa using fkRectBlackOrbitRibbonSubdivisionDart_exponentY_sum R omega d


theorem fkRectBlackBoundaryPrimalCycleWinding_fst_odd
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hy : (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0)
    (hx : (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 ≠ 0) :
    Odd (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 := by
  letI : Fact (2 < fkRectBlackOrbitRibbonSubdivisionSide R) :=
    ⟨fkRectBlackOrbitRibbonSubdivisionSide_gt_two R⟩
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega d)
  apply ons_simpleLoop_horizontal_winding_odd_of_ne_zero
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart R omega d)
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart_valid R omega d)
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart_site_injective R omega d)
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart_nonUturn R omega d)
    w.1
    (fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentX_sum R omega d)
  · rw [fkRectBlackOrbitFaithfulRibbonSubdivisionDart_exponentY_sum]
    simp [w, hy]
  · exact hx

end

end StatMech.FrontierD
