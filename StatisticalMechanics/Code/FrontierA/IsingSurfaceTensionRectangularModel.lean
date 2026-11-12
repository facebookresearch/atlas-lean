/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.IsingSurfaceTensionFeketeIdentification
import Code.FrontierA.Z2GaugeCubicalGluing
import Code.FrontierA.Z2GaugeCriticalCoupling

namespace StatMech.FrontierA

noncomputable section



def rectangularDobrushinFreeEnergy (beta : Real) (m n : Nat) : Real :=
  cubicalRectangularWilsonFreeEnergy beta m n

theorem rectangularDobrushinFreeEnergy_nonneg
    {beta : Real} (hbeta : 0 < beta) (m n : Nat) :
    0 <= rectangularDobrushinFreeEnergy beta m n :=
  cubicalRectangularWilsonFreeEnergy_nonneg hbeta m n



theorem rectangularDobrushinFreeEnergy_eq_dualIsingDisorder
    {beta : Real} (hbeta : 0 < beta) {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    rectangularDobrushinFreeEnergy beta m n =
      cubicalRectangularDisorderFreeEnergy beta m n :=
  cubicalRectangularWilsonFreeEnergy_eq_disorderFreeEnergy hbeta hm hn


theorem rectangularDobrushinFreeEnergy_areaBound
    {beta : Real} (hbeta : 0 < beta) :
    HasRectangularAreaBound (rectangularDobrushinFreeEnergy beta) := by
  refine ⟨2 * gaugeDualCoupling beta,
    mul_nonneg (by norm_num) (gaugeDualCoupling_pos hbeta).le, ?_⟩
  intro m n
  by_cases hm : m = 0
  · subst m
    rw [rectangularDobrushinFreeEnergy,
      cubicalRectangularWilsonFreeEnergy]
    have hempty : cubicalXYLoop
        (a := 0) (b := n) (c := max 0 n)
        (0 : Fin (max 0 n + 1)) = ∅ := by
      simp [cubicalXYLoop, cubicalXYSheet, gaugeSurfaceBoundary]
    rw [hempty, gaugeWilsonExpectation_empty]
    simp
  by_cases hn : n = 0
  · subst n
    rw [rectangularDobrushinFreeEnergy,
      cubicalRectangularWilsonFreeEnergy]
    have hempty : cubicalXYLoop
        (a := m) (b := 0) (c := max m 0)
        (0 : Fin (max m 0 + 1)) = ∅ := by
      simp [cubicalXYLoop, cubicalXYSheet, gaugeSurfaceBoundary]
    rw [hempty, gaugeWilsonExpectation_empty]
    simp
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hc_pos : 0 < max m n := hm_pos.trans_le (Nat.le_max_left m n)
  have hbound := cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling
    hm_pos hn_pos hc_pos (0 : Fin (max m n + 1)) beta hbeta
  change rectangularDobrushinFreeEnergy beta m n <= _
  rw [rectangularDobrushinFreeEnergy,
    cubicalRectangularWilsonFreeEnergy]
  convert hbound using 1 <;> push_cast <;> ring



theorem rectangularDobrushinFreeEnergy_separatelySubadditive
    {beta : Real} (hbeta : 0 < beta) :
    SeparatelySubadditive (rectangularDobrushinFreeEnergy beta) := by
  simpa [rectangularDobrushinFreeEnergy] using
    cubicalRectangularWilsonFreeEnergy_separatelySubadditive hbeta


def rectangularDobrushinSurfaceRate (beta : Real) : Real :=
  rectangularSurfaceRate (rectangularDobrushinFreeEnergy beta)

theorem rectangularDobrushinSurfaceRate_nonneg
    {beta : Real} (hbeta : 0 < beta) :
    0 <= rectangularDobrushinSurfaceRate beta :=
  rectangularSurfaceRate_nonneg
    (fun m n => rectangularDobrushinFreeEnergy_nonneg hbeta m n)



theorem rectangularDobrushin_square_and_iterated_tendsto
    {beta : Real} (hbeta : 0 < beta) :
    Filter.Tendsto
        (fun n : Nat => rectangularSurfaceDensity
          (rectangularDobrushinFreeEnergy beta) n n)
        Filter.atTop (nhds (rectangularDobrushinSurfaceRate beta)) /\
      Filter.Tendsto
        (fun k : Nat =>
          ((rectangularDobrushinFreeEnergy_separatelySubadditive hbeta).1 k).lim /
            (k : Real))
        Filter.atTop (nhds (rectangularDobrushinSurfaceRate beta)) := by
  exact square_and_iterated_surfaceDensity_tendsto_rate
    (fun m n => rectangularDobrushinFreeEnergy_nonneg hbeta m n)
    (rectangularDobrushinFreeEnergy_separatelySubadditive hbeta)
    (rectangularDobrushinFreeEnergy_areaBound hbeta)



def finiteRectangularIsingDisorderFreeEnergy
    (J : Real) (m n : Nat) : Real :=
  multibondDisorderFreeEnergy
    (cubicalDualEnds (a := m) (b := n) (c := max m n))
    (fun _ : CubicalPlaquette m n (max m n) => J)
    (cubicalXYSheet (a := m) (b := n) (c := max m n)
      (0 : Fin (max m n + 1)))



def rectangularIsingDobrushinFreeEnergy
    (J : Real) (m n : Nat) : Real :=
  rectangularDobrushinFreeEnergy (gaugeCriticalCoupling J) m n




theorem rectangularIsingDobrushinFreeEnergy_eq_disorder
    {J : Real} (hJ : 0 < J) {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    rectangularIsingDobrushinFreeEnergy J m n =
      finiteRectangularIsingDisorderFreeEnergy J m n := by
  rw [rectangularIsingDobrushinFreeEnergy,
    rectangularDobrushinFreeEnergy_eq_dualIsingDisorder
      (gaugeCriticalCoupling_pos hJ) hm hn]
  unfold cubicalRectangularDisorderFreeEnergy
  unfold finiteRectangularIsingDisorderFreeEnergy
  rw [gaugeDualCoupling_gaugeCriticalCoupling hJ]

theorem rectangularIsingDobrushinFreeEnergy_separatelySubadditive
    {J : Real} (hJ : 0 < J) :
    SeparatelySubadditive (rectangularIsingDobrushinFreeEnergy J) := by
  simpa [rectangularIsingDobrushinFreeEnergy] using
    rectangularDobrushinFreeEnergy_separatelySubadditive
      (gaugeCriticalCoupling_pos hJ)

theorem rectangularIsingDobrushinFreeEnergy_areaBound
    {J : Real} (hJ : 0 < J) :
    HasRectangularAreaBound (rectangularIsingDobrushinFreeEnergy J) := by
  simpa [rectangularIsingDobrushinFreeEnergy] using
    rectangularDobrushinFreeEnergy_areaBound (gaugeCriticalCoupling_pos hJ)



def rectangularIsingSurfaceTension (J : Real) : Real :=
  rectangularSurfaceRate (rectangularIsingDobrushinFreeEnergy J)

theorem rectangularIsingSurfaceTension_nonneg
    {J : Real} (hJ : 0 < J) :
    0 <= rectangularIsingSurfaceTension J :=
  rectangularSurfaceRate_nonneg (fun m n =>
    rectangularDobrushinFreeEnergy_nonneg
      (gaugeCriticalCoupling_pos hJ) m n)



theorem rectangularIsingDobrushin_square_and_iterated_tendsto
    {J : Real} (hJ : 0 < J) :
    Filter.Tendsto
        (fun n : Nat => rectangularSurfaceDensity
          (rectangularIsingDobrushinFreeEnergy J) n n)
        Filter.atTop (nhds (rectangularIsingSurfaceTension J)) /\
      Filter.Tendsto
        (fun k : Nat =>
          ((rectangularIsingDobrushinFreeEnergy_separatelySubadditive hJ).1 k).lim /
            (k : Real))
        Filter.atTop (nhds (rectangularIsingSurfaceTension J)) := by
  exact square_and_iterated_surfaceDensity_tendsto_rate
    (fun m n => rectangularDobrushinFreeEnergy_nonneg
      (gaugeCriticalCoupling_pos hJ) m n)
    (rectangularIsingDobrushinFreeEnergy_separatelySubadditive hJ)
    (rectangularIsingDobrushinFreeEnergy_areaBound hJ)

end

end StatMech.FrontierA
