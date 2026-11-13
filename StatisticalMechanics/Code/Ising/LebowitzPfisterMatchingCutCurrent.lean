/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterTwoGhostVarianceSector
import Code.Ising.CorrelationRatio
import Code.Sharpness.MultiReplica









open Finset
open scoped BigOperators symmDiff

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W I : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]


def lpMatchingSeamSource (left right : I -> W) (i : I) : Finset W :=
  ({left i} : Finset W) ∆ {right i}


def lpMatchingGhostSource (g0 g1 : W) : Finset W :=
  ({g0} : Finset W) ∆ {g1}

noncomputable def lpMatchingCurrentZ
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real) : Real :=
  currentSum G beta J ∅

noncomputable def lpMatchingCurrentA
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) : Real :=
  ∑ i : I, currentSum G beta J (lpMatchingSeamSource left right i)

noncomputable def lpMatchingCurrentB
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  ∑ i : I, currentSum G beta J
    (lpMatchingSeamSource left right i ∆ lpMatchingGhostSource g0 g1)

noncomputable def lpMatchingCurrentC
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real) (g0 g1 : W) : Real :=
  currentSum G beta J (lpMatchingGhostSource g0 g1)

noncomputable def lpMatchingCurrentD
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) : Real :=
  ∑ i : I, ∑ j : I, currentSum G beta J
    (lpMatchingSeamSource left right i ∆ lpMatchingSeamSource left right j)

noncomputable def lpMatchingCurrentE
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) : Real :=
  ∑ i : I, ∑ j : I, currentSum G beta J
    (lpMatchingSeamSource left right i ∆
      lpMatchingSeamSource left right j ∆ lpMatchingGhostSource g0 g1)



def lpMatchingCurrentSkewPolynomial (A B C D E Z : Real) : Real :=
  (Z ^ 2 - C ^ 2) *
      (((E * Z - D * C) * Z) - 2 * A * (B * Z - A * C)) +
    2 * C * (B * Z - A * C) ^ 2


theorem lpMatchingCurrentSkewPolynomial_expanded (A B C D E Z : Real) :
    lpMatchingCurrentSkewPolynomial A B C D E Z =
      E * Z ^ 4 - D * C * Z ^ 3 - 2 * A * B * Z ^ 3 +
        2 * A ^ 2 * C * Z ^ 2 - E * C ^ 2 * Z ^ 2 +
        D * C ^ 3 * Z - 2 * A * B * C ^ 2 * Z +
        2 * B ^ 2 * C * Z ^ 2 := by
  unfold lpMatchingCurrentSkewPolynomial
  ring_nf




noncomputable def lpFiveCurrentSourceMass
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (S1 S2 S3 S4 S5 : Finset W) : Real :=
  currentSum G beta J S1 * currentSum G beta J S2 *
    currentSum G beta J S3 * currentSum G beta J S4 *
    currentSum G beta J S5




theorem lpFiveCurrentSourceMass_eq_sourceTriple_mul_sourcePair
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (S1 S2 S3 S4 S5 : Finset W) :
    lpFiveCurrentSourceMass G beta J S1 S2 S3 S4 S5 =
      sourceTripleSum G beta J S1 S2 S3 *
        sourcePairSum G beta J S4 S5 := by
  rw [sourceTripleSum_eq_mul, sourcePairSum_eq_mul]
  unfold lpFiveCurrentSourceMass
  ring





noncomputable def lpMatchingFiveCurrentCoefficient
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) (i j : I) : Real :=
  let Si := lpMatchingSeamSource left right i
  let Sj := lpMatchingSeamSource left right j
  let T := lpMatchingGhostSource g0 g1
  lpFiveCurrentSourceMass G beta J (Si ∆ Sj ∆ T) ∅ ∅ ∅ ∅ -
    lpFiveCurrentSourceMass G beta J (Si ∆ Sj) T ∅ ∅ ∅ -
    2 * lpFiveCurrentSourceMass G beta J Si (Sj ∆ T) ∅ ∅ ∅ +
    2 * lpFiveCurrentSourceMass G beta J Si Sj T ∅ ∅ -
    lpFiveCurrentSourceMass G beta J (Si ∆ Sj ∆ T) T T ∅ ∅ +
    lpFiveCurrentSourceMass G beta J (Si ∆ Sj) T T T ∅ -
    2 * lpFiveCurrentSourceMass G beta J Si (Sj ∆ T) T T ∅ +
    2 * lpFiveCurrentSourceMass G beta J (Si ∆ T) (Sj ∆ T) T ∅ ∅


def lpFiveSourceTotal
    (S1 S2 S3 S4 S5 : Finset W) : Finset W :=
  S1 ∆ S2 ∆ S3 ∆ S4 ∆ S5



theorem lpMatchingFiveCurrentCoefficient_commonSource
    (Si Sj T : Finset W) :
    lpFiveSourceTotal (Si ∆ Sj ∆ T) ∅ ∅ ∅ ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal (Si ∆ Sj) T ∅ ∅ ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal Si (Sj ∆ T) ∅ ∅ ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal Si Sj T ∅ ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal (Si ∆ Sj ∆ T) T T ∅ ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal (Si ∆ Sj) T T T ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal Si (Sj ∆ T) T T ∅ = Si ∆ Sj ∆ T ∧
    lpFiveSourceTotal (Si ∆ T) (Sj ∆ T) T ∅ ∅ = Si ∆ Sj ∆ T := by
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
    tauto
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
  constructor
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
    tauto
  · ext x
    simp [lpFiveSourceTotal, Finset.mem_symmDiff]
    tauto



theorem lpMatchingCurrentSkewPolynomial_eq_sum_fiveCurrentCoefficient
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) :
    lpMatchingCurrentSkewPolynomial
        (lpMatchingCurrentA G beta J left right)
        (lpMatchingCurrentB G beta J left right g0 g1)
        (lpMatchingCurrentC G beta J g0 g1)
        (lpMatchingCurrentD G beta J left right)
        (lpMatchingCurrentE G beta J left right g0 g1)
        (lpMatchingCurrentZ G beta J) =
      ∑ i : I, ∑ j : I,
        lpMatchingFiveCurrentCoefficient G beta J left right g0 g1 i j := by
  rw [lpMatchingCurrentSkewPolynomial_expanded]
  unfold lpMatchingCurrentA lpMatchingCurrentB lpMatchingCurrentC
    lpMatchingCurrentD lpMatchingCurrentE lpMatchingCurrentZ
    lpMatchingFiveCurrentCoefficient lpFiveCurrentSourceMass
  simp only [pow_two, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring



theorem lpMatching_centeredGhostCovariance_eq_currentPolynomial
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (left right : I -> W) (g0 g1 : W) :
    let a := ∑ i : I,
      expectationJ G beta J (lpMatchingSeamSource left right i)
    let b := ∑ i : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆ lpMatchingGhostSource g0 g1)
    let c := expectationJ G beta J (lpMatchingGhostSource g0 g1)
    let d := ∑ i : I, ∑ j : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆ lpMatchingSeamSource left right j)
    let e := ∑ i : I, ∑ j : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆
        lpMatchingSeamSource left right j ∆ lpMatchingGhostSource g0 g1)
    let A := lpMatchingCurrentA G beta J left right
    let B := lpMatchingCurrentB G beta J left right g0 g1
    let C := lpMatchingCurrentC G beta J g0 g1
    let D := lpMatchingCurrentD G beta J left right
    let E := lpMatchingCurrentE G beta J left right g0 g1
    let Z := lpMatchingCurrentZ G beta J
    (1 - c ^ 2) * ((e - d * c) - 2 * a * (b - a * c)) +
        2 * c * (b - a * c) ^ 2 =
      lpMatchingCurrentSkewPolynomial A B C D E Z / Z ^ 5 := by
  dsimp only
  let Z := currentSum G beta J ∅
  have hZ : Ne Z 0 := ne_of_gt (acr_currentSum_empty_pos G beta J)
  have ha : (∑ i : I,
      expectationJ G beta J (lpMatchingSeamSource left right i)) =
      lpMatchingCurrentA G beta J left right / Z := by
    simp_rw [current_representation]
    unfold lpMatchingCurrentA
    rw [sum_div]
  have hb : (∑ i : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆ lpMatchingGhostSource g0 g1)) =
      lpMatchingCurrentB G beta J left right g0 g1 / Z := by
    simp_rw [current_representation]
    unfold lpMatchingCurrentB
    rw [sum_div]
  have hc : expectationJ G beta J (lpMatchingGhostSource g0 g1) =
      lpMatchingCurrentC G beta J g0 g1 / Z := by
    rw [current_representation]
    unfold lpMatchingCurrentC
    rfl
  have hd : (∑ i : I, ∑ j : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆ lpMatchingSeamSource left right j)) =
      lpMatchingCurrentD G beta J left right / Z := by
    simp_rw [current_representation]
    unfold lpMatchingCurrentD
    rw [sum_div]
    congr 1
    funext i
    rw [sum_div]
  have he : (∑ i : I, ∑ j : I, expectationJ G beta J
      (lpMatchingSeamSource left right i ∆
        lpMatchingSeamSource left right j ∆ lpMatchingGhostSource g0 g1)) =
      lpMatchingCurrentE G beta J left right g0 g1 / Z := by
    simp_rw [current_representation]
    unfold lpMatchingCurrentE
    rw [sum_div]
    congr 1
    funext i
    rw [sum_div]
  rw [ha, hb, hc, hd, he]
  exact lpTwoGhost_centeredCovariance_clear_current
    (lpMatchingCurrentA G beta J left right)
    (lpMatchingCurrentB G beta J left right g0 g1)
    (lpMatchingCurrentC G beta J g0 g1)
    (lpMatchingCurrentD G beta J left right)
    (lpMatchingCurrentE G beta J left right g0 g1) Z hZ

end

end StatMech.Ising
