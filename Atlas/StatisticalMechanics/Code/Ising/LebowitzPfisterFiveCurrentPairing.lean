/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReflectedMatchingCut
import Code.Sharpness.GhostCurrentRep










open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.GhostCurrentRep

noncomputable section

variable {W : Type*} [DecidableEq W]


@[ext]
structure LPFiveSourceAllocation (W : Type*) where
  source1 : Finset W
  source2 : Finset W
  source3 : Finset W
  source4 : Finset W
  source5 : Finset W


def lpFiveToggle12 (T : Finset W)
    (a : LPFiveSourceAllocation W) : LPFiveSourceAllocation W where
  source1 := a.source1 ∆ T
  source2 := a.source2 ∆ T
  source3 := a.source3
  source4 := a.source4
  source5 := a.source5


def lpFiveToggle14 (T : Finset W)
    (a : LPFiveSourceAllocation W) : LPFiveSourceAllocation W where
  source1 := a.source1 ∆ T
  source2 := a.source2
  source3 := a.source3
  source4 := a.source4 ∆ T
  source5 := a.source5


def lpFiveToggle23 (T : Finset W)
    (a : LPFiveSourceAllocation W) : LPFiveSourceAllocation W where
  source1 := a.source1
  source2 := a.source2 ∆ T
  source3 := a.source3 ∆ T
  source4 := a.source4
  source5 := a.source5


def LPFiveSourceAllocation.total
    (a : LPFiveSourceAllocation W) : Finset W :=
  lpFiveSourceTotal a.source1 a.source2 a.source3 a.source4 a.source5


def lpFiveOrbitABPos (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si ∆ Sj ∆ T, ∅, ∅, ∅, ∅⟩


def lpFiveOrbitABNeg (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si ∆ Sj, T, ∅, ∅, ∅⟩




theorem lpFiveToggle12_orbitAB
    (Si Sj T : Finset W) :
    lpFiveToggle12 T (lpFiveOrbitABPos Si Sj T) =
      lpFiveOrbitABNeg Si Sj T := by
  apply LPFiveSourceAllocation.ext <;>
    simp only [lpFiveToggle12, lpFiveOrbitABPos, lpFiveOrbitABNeg]
  all_goals
    ext x
    simp only [Finset.mem_symmDiff, Finset.notMem_empty]
    tauto


theorem lpFiveToggle12_involutive (T : Finset W) :
    Function.Involutive (lpFiveToggle12 T) := by
  intro a
  apply LPFiveSourceAllocation.ext <;> simp [lpFiveToggle12]

theorem lpFiveToggle14_involutive (T : Finset W) :
    Function.Involutive (lpFiveToggle14 T) := by
  intro a
  apply LPFiveSourceAllocation.ext <;> simp [lpFiveToggle14]

theorem lpFiveToggle23_involutive (T : Finset W) :
    Function.Involutive (lpFiveToggle23 T) := by
  intro a
  apply LPFiveSourceAllocation.ext <;> simp [lpFiveToggle23]


theorem lpFiveToggle12_total (T : Finset W)
    (a : LPFiveSourceAllocation W) :
    (lpFiveToggle12 T a).total = a.total := by
  change (a.source1 ∆ T ∆ (a.source2 ∆ T) ∆ a.source3 ∆
      a.source4 ∆ a.source5) =
    a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆ a.source5
  calc
    _ = (a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆
        a.source5) ∆ T ∆ T := by ac_rfl
    _ = _ := symmDiff_symmDiff_cancel_right _ _

theorem lpFiveToggle14_total (T : Finset W)
    (a : LPFiveSourceAllocation W) :
    (lpFiveToggle14 T a).total = a.total := by
  change (a.source1 ∆ T ∆ a.source2 ∆ a.source3 ∆
      (a.source4 ∆ T) ∆ a.source5) =
    a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆ a.source5
  calc
    _ = (a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆
        a.source5) ∆ T ∆ T := by ac_rfl
    _ = _ := symmDiff_symmDiff_cancel_right _ _

theorem lpFiveToggle23_total (T : Finset W)
    (a : LPFiveSourceAllocation W) :
    (lpFiveToggle23 T a).total = a.total := by
  change (a.source1 ∆ (a.source2 ∆ T) ∆ (a.source3 ∆ T) ∆
      a.source4 ∆ a.source5) =
    a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆ a.source5
  calc
    _ = (a.source1 ∆ a.source2 ∆ a.source3 ∆ a.source4 ∆
        a.source5) ∆ T ∆ T := by ac_rfl
    _ = _ := symmDiff_symmDiff_cancel_right _ _



def lpFiveOrbitEFNeg (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si ∆ Sj ∆ T, T, T, ∅, ∅⟩

def lpFiveOrbitEFPos (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si ∆ Sj, T, T, T, ∅⟩

theorem lpFiveToggle14_orbitEF
    (Si Sj T : Finset W) :
    lpFiveToggle14 T (lpFiveOrbitEFNeg Si Sj T) =
      lpFiveOrbitEFPos Si Sj T := by
  apply LPFiveSourceAllocation.ext <;>
    simp only [lpFiveToggle14, lpFiveOrbitEFNeg, lpFiveOrbitEFPos]
  all_goals
    ext x
    simp only [Finset.mem_symmDiff, Finset.notMem_empty]
    tauto



def lpFiveOrbitCDNeg (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si, Sj ∆ T, ∅, ∅, ∅⟩

def lpFiveOrbitCDPos (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si, Sj, T, ∅, ∅⟩

theorem lpFiveToggle23_orbitCD
    (Si Sj T : Finset W) :
    lpFiveToggle23 T (lpFiveOrbitCDNeg Si Sj T) =
      lpFiveOrbitCDPos Si Sj T := by
  apply LPFiveSourceAllocation.ext <;>
    simp only [lpFiveToggle23, lpFiveOrbitCDNeg, lpFiveOrbitCDPos]
  all_goals
    ext x
    simp only [Finset.mem_symmDiff, Finset.notMem_empty]
    tauto



def lpFiveOrbitGHNeg (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si, Sj ∆ T, T, T, ∅⟩

def lpFiveOrbitGHPos (Si Sj T : Finset W) : LPFiveSourceAllocation W :=
  ⟨Si ∆ T, Sj ∆ T, T, ∅, ∅⟩

theorem lpFiveToggle14_orbitGH
    (Si Sj T : Finset W) :
    lpFiveToggle14 T (lpFiveOrbitGHNeg Si Sj T) =
      lpFiveOrbitGHPos Si Sj T := by
  apply LPFiveSourceAllocation.ext <;>
    simp only [lpFiveToggle14, lpFiveOrbitGHNeg, lpFiveOrbitGHPos]
  all_goals
    ext x
    simp only [Finset.mem_symmDiff, Finset.notMem_empty]
    tauto





theorem lpMatchingFiveCurrentCoefficient_eq_disconnectionResidues
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1)
    (i j : I) :
    let Si := lpMatchingSeamSource left right i
    let Sj := lpMatchingSeamSource left right j
    let T := lpMatchingGhostSource g0 g1
    let Z := currentSum G beta J ∅
    let C := currentSum G beta J T
    lpMatchingFiveCurrentCoefficient G beta J left right g0 g1 i j =
      sourcePairDisconnSum G beta J (Si ∆ Sj ∆ T) ∅ g0 g1 *
          Z * (Z ^ 2 - C ^ 2) -
        2 * currentSum G beta J Si *
          sourcePairDisconnSum G beta J (Sj ∆ T) ∅ g0 g1 * Z ^ 2 +
        2 * sourcePairDisconnSum G beta J (Si ∆ T) ∅ g0 g1 *
          currentSum G beta J (Sj ∆ T) * C * Z := by
  dsimp only
  let Si := lpMatchingSeamSource left right i
  let Sj := lpMatchingSeamSource left right j
  let T := lpMatchingGhostSource g0 g1
  let Z := currentSum G beta J ∅
  let C := currentSum G beta J T
  have hT : T = ({g0, g1} : Finset W) := by
    ext x
    simp only [T, lpMatchingGhostSource, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hg⟩
      · exact Or.inr ⟨rfl, hg.symm⟩
  have hR := gcr_currentSum_ghostRep G beta J (Si ∆ Sj ∆ T) hg
  have hJ := gcr_currentSum_ghostRep G beta J (Sj ∆ T) hg
  have hI := gcr_currentSum_ghostRep G beta J (Si ∆ T) hg
  rw [← hT, symmDiff_symmDiff_cancel_right] at hR hJ hI
  unfold lpMatchingFiveCurrentCoefficient lpFiveCurrentSourceMass
  dsimp only [Si, Sj, T, Z, C] at hR hJ hI ⊢
  calc
    _ = (currentSum G beta J (Si ∆ Sj ∆ T) * Z -
            currentSum G beta J (Si ∆ Sj) * C) * Z ^ 3 -
          (currentSum G beta J (Si ∆ Sj ∆ T) * Z -
            currentSum G beta J (Si ∆ Sj) * C) * C ^ 2 * Z -
          2 * currentSum G beta J Si *
            (currentSum G beta J (Sj ∆ T) * Z -
              currentSum G beta J Sj * C) * Z ^ 2 +
          2 * (currentSum G beta J (Si ∆ T) * Z -
              currentSum G beta J Si * C) *
            currentSum G beta J (Sj ∆ T) * C * Z := by ring
    _ = _ := by rw [hR, hJ, hI]; ring


noncomputable def lpMatchingDisconnZero
    {I : Type*} [Fintype I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  ∑ i : I, sourcePairDisconnSum G beta J
    (lpMatchingSeamSource left right i) ∅ g0 g1


noncomputable def lpMatchingDisconnOne
    {I : Type*} [Fintype I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  let T := lpMatchingGhostSource g0 g1
  ∑ i : I, sourcePairDisconnSum G beta J
    (lpMatchingSeamSource left right i ∆ T) ∅ g0 g1


noncomputable def lpMatchingDisconnTwo
    {I : Type*} [Fintype I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  let T := lpMatchingGhostSource g0 g1
  ∑ i : I, ∑ j : I, sourcePairDisconnSum G beta J
    (lpMatchingSeamSource left right i ∆
      lpMatchingSeamSource left right j ∆ T) ∅ g0 g1


noncomputable def lpMatchingDisconnTwoOffDiag
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  let T := lpMatchingGhostSource g0 g1
  ∑ i : I, ∑ j : I,
    if i = j then 0 else
      sourcePairDisconnSum G beta J
        (lpMatchingSeamSource left right i ∆
          lpMatchingSeamSource left right j ∆ T) ∅ g0 g1




noncomputable def lpMatchingDisconnCenteredGram
    {I : Type*} [Fintype I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  let T := lpMatchingGhostSource g0 g1
  let dE := sourcePairDisconnSum G beta J ∅ ∅ g0 g1
  ∑ i : I, ∑ j : I, (
    dE * sourcePairDisconnSum G beta J
        (lpMatchingSeamSource left right i ∆
          lpMatchingSeamSource left right j ∆ T) ∅ g0 g1 -
      sourcePairDisconnSum G beta J
          (lpMatchingSeamSource left right i) ∅ g0 g1 *
        sourcePairDisconnSum G beta J
          (lpMatchingSeamSource left right j ∆ T) ∅ g0 g1 -
      sourcePairDisconnSum G beta J
          (lpMatchingSeamSource left right j) ∅ g0 g1 *
        sourcePairDisconnSum G beta J
          (lpMatchingSeamSource left right i ∆ T) ∅ g0 g1)



theorem lpMatchingDisconnCenteredGram_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) :
    lpMatchingDisconnCenteredGram G beta J left right g0 g1 =
      sourcePairDisconnSum G beta J ∅ ∅ g0 g1 *
          lpMatchingDisconnTwo G beta J left right g0 g1 -
        2 * lpMatchingDisconnZero G beta J left right g0 g1 *
          lpMatchingDisconnOne G beta J left right g0 g1 := by
  unfold lpMatchingDisconnCenteredGram lpMatchingDisconnTwo
    lpMatchingDisconnZero lpMatchingDisconnOne
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring



theorem lpMatchingDisconnZero_eq_currentGap
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    lpMatchingDisconnZero G beta J left right g0 g1 =
      (∑ i : I, currentSum G beta J
          (lpMatchingSeamSource left right i)) * currentSum G beta J ∅ -
        (∑ i : I, currentSum G beta J
          (lpMatchingSeamSource left right i ∆ T)) *
            currentSum G beta J T := by
  dsimp only
  let T := lpMatchingGhostSource g0 g1
  have hT : T = ({g0, g1} : Finset W) := by
    ext x
    simp only [T, lpMatchingGhostSource, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hg⟩
      · exact Or.inr ⟨rfl, hg.symm⟩
  unfold lpMatchingDisconnZero
  calc
    _ = ∑ i : I,
        (currentSum G beta J (lpMatchingSeamSource left right i) *
            currentSum G beta J ∅ -
          currentSum G beta J
              (lpMatchingSeamSource left right i ∆ T) *
            currentSum G beta J T) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := gcr_currentSum_ghostRep G beta J
        (lpMatchingSeamSource left right i) hg
      rw [← hT] at h
      exact h.symm
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]



theorem lpMatchingFiveCurrentCoefficient_sum_eq_disconnectionGap
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    let Z := currentSum G beta J ∅
    let C := currentSum G beta J T
    (∑ i : I, ∑ j : I,
        lpMatchingFiveCurrentCoefficient G beta J
          left right g0 g1 i j) =
      Z * ((Z ^ 2 - C ^ 2) *
          lpMatchingDisconnTwo G beta J left right g0 g1 -
        2 * lpMatchingDisconnZero G beta J left right g0 g1 *
          lpMatchingDisconnOne G beta J left right g0 g1) := by
  dsimp only
  simp_rw [lpMatchingFiveCurrentCoefficient_eq_disconnectionResidues
    G beta J left right g0 g1 hg]
  rw [lpMatchingDisconnZero_eq_currentGap
    G beta J left right g0 g1 hg]
  unfold lpMatchingDisconnOne lpMatchingDisconnTwo
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring


theorem lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    let Z := currentSum G beta J ∅
    let C := currentSum G beta J T
    ((∑ i : I, ∑ j : I,
        lpMatchingFiveCurrentCoefficient G beta J
          left right g0 g1 i j) <= 0) <->
      (Z ^ 2 - C ^ 2) *
          lpMatchingDisconnTwo G beta J left right g0 g1 <=
        2 * lpMatchingDisconnZero G beta J left right g0 g1 *
          lpMatchingDisconnOne G beta J left right g0 g1 := by
  dsimp only
  rw [lpMatchingFiveCurrentCoefficient_sum_eq_disconnectionGap
    G beta J left right g0 g1 hg]
  have hZ : 0 < currentSum G beta J ∅ :=
    acr_currentSum_empty_pos G beta J
  constructor
  · intro h
    have hx :
        (currentSum G beta J ∅ ^ 2 -
            currentSum G beta J (lpMatchingGhostSource g0 g1) ^ 2) *
              lpMatchingDisconnTwo G beta J left right g0 g1 -
          2 * lpMatchingDisconnZero G beta J left right g0 g1 *
            lpMatchingDisconnOne G beta J left right g0 g1 <= 0 := by
      nlinarith
    exact sub_nonpos.mp hx
  · intro h
    have hx := sub_nonpos.mpr h
    nlinarith



theorem lpGhostCurrentSquareGap_eq_emptyDisconn
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    currentSum G beta J ∅ ^ 2 - currentSum G beta J T ^ 2 =
      sourcePairDisconnSum G beta J ∅ ∅ g0 g1 := by
  dsimp only
  let T := lpMatchingGhostSource g0 g1
  have hT : T = ({g0, g1} : Finset W) := by
    ext x
    simp only [T, lpMatchingGhostSource, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hg⟩
      · exact Or.inr ⟨rfl, hg.symm⟩
  have h := gcr_currentSum_ghostRep G beta J (∅ : Finset W) hg
  rw [← hT] at h
  have hempty : (∅ : Finset W) ∆ T = T := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hempty] at h
  simpa [pow_two] using h



theorem lpMatchingFiveCurrentCoefficient_sum_nonpos_iff_centeredGram
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1) :
    ((∑ i : I, ∑ j : I,
        lpMatchingFiveCurrentCoefficient G beta J
          left right g0 g1 i j) <= 0) <->
      lpMatchingDisconnCenteredGram G beta J
        left right g0 g1 <= 0 := by
  have hsign := lpMatchingFiveCurrentCoefficient_sum_nonpos_iff
    G beta J left right g0 g1 hg
  dsimp only at hsign
  rw [hsign]
  rw [← sub_nonpos]
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn G beta J g0 g1 hg]
  rw [← lpMatchingDisconnCenteredGram_eq]



theorem lpSourcePairDisconnSum_nonneg
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (A B : Finset W) (u v : W) :
    0 <= sourcePairDisconnSum G beta J A B u v := by
  unfold sourcePairDisconnSum
  apply tsum_nonneg
  rintro ⟨p, q⟩
  by_cases hp : StatMech.Sharpness.sources G (ofEdgeFun G p) = A <;>
    by_cases hq : StatMech.Sharpness.sources G (ofEdgeFun G q) = B <;>
    by_cases hc : ¬ CurrentConnected G
      (ofEdgeFun G (fun e => p e + q e)) u v <;>
    simp [hp, hq, hc]
  exact mul_nonneg
    (acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G p))
    (acw_weight_nonneg G beta J hbeta hJ (ofEdgeFun G q))


theorem lpGhostCurrentSquareGap_nonneg
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    0 <= currentSum G beta J ∅ ^ 2 - currentSum G beta J T ^ 2 := by
  dsimp only
  rw [lpGhostCurrentSquareGap_eq_emptyDisconn G beta J g0 g1 hg]
  exact lpSourcePairDisconnSum_nonneg G beta J hbeta hJ ∅ ∅ g0 g1



theorem lpGhostSourceDisconn_eq_zero
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (g0 g1 : W) (hg : g0 ≠ g1) :
    let T := lpMatchingGhostSource g0 g1
    sourcePairDisconnSum G beta J T ∅ g0 g1 = 0 := by
  dsimp only
  let T := lpMatchingGhostSource g0 g1
  have hT : T = ({g0, g1} : Finset W) := by
    ext x
    simp only [T, lpMatchingGhostSource, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    constructor
    · tauto
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, hg⟩
      · exact Or.inr ⟨rfl, hg.symm⟩
  have h := gcr_currentSum_ghostRep G beta J T hg
  rw [← hT, symmDiff_self] at h
  dsimp only [T] at h ⊢
  calc
    _ = currentSum G beta J (lpMatchingGhostSource g0 g1) *
          currentSum G beta J ∅ -
        currentSum G beta J ∅ *
          currentSum G beta J (lpMatchingGhostSource g0 g1) := h.symm
    _ = 0 := by ring



theorem lpMatchingDisconn_diagonal_le
    {I : Type*} [Fintype I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1)
    (i : I) :
    let Si := lpMatchingSeamSource left right i
    let T := lpMatchingGhostSource g0 g1
    sourcePairDisconnSum G beta J ∅ ∅ g0 g1 *
        sourcePairDisconnSum G beta J (Si ∆ Si ∆ T) ∅ g0 g1 <=
      2 * sourcePairDisconnSum G beta J Si ∅ g0 g1 *
        sourcePairDisconnSum G beta J (Si ∆ T) ∅ g0 g1 := by
  dsimp only
  let Si := lpMatchingSeamSource left right i
  let T := lpMatchingGhostSource g0 g1
  have hsource : Si ∆ Si ∆ T = T := by
    rw [symmDiff_self]
    ext x
    simp [Finset.mem_symmDiff]
  rw [hsource, lpGhostSourceDisconn_eq_zero G beta J g0 g1 hg,
    mul_zero]
  exact mul_nonneg
    (mul_nonneg (by positivity)
      (lpSourcePairDisconnSum_nonneg G beta J hbeta hJ Si ∅ g0 g1))
    (lpSourcePairDisconnSum_nonneg G beta J hbeta hJ (Si ∆ T) ∅ g0 g1)



theorem lpMatchingDisconnTwo_eq_offDiag
    {I : Type*} [Fintype I] [DecidableEq I]
    [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (hg : g0 ≠ g1) :
    lpMatchingDisconnTwo G beta J left right g0 g1 =
      lpMatchingDisconnTwoOffDiag G beta J left right g0 g1 := by
  unfold lpMatchingDisconnTwo lpMatchingDisconnTwoOffDiag
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hsource :
        lpMatchingSeamSource left right i ∆
            lpMatchingSeamSource left right i ∆
            lpMatchingGhostSource g0 g1 =
          lpMatchingGhostSource g0 g1 := by
      rw [symmDiff_self]
      ext x
      simp [Finset.mem_symmDiff]
    rw [hsource, lpGhostSourceDisconn_eq_zero G beta J g0 g1 hg]
  · rw [if_neg hij]

end

end StatMech.Ising
