/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionThermodynamic

open Filter Set Topology

namespace StatMech.FrontierA

noncomputable section



def cubicalRectangularWilsonFreeEnergy
    (beta : Real) (m n : Nat) : Real :=
  -Real.log
    (gaugeWilsonExpectation
      (cubicalPlaquetteIncidence (a := m) (b := n) (c := max m n))
      (fun _ : CubicalPlaquette m n (max m n) => beta)
      (cubicalXYLoop (a := m) (b := n) (c := max m n)
        (0 : Fin (max m n + 1))))


def cubicalRectangularDisorderFreeEnergy
    (beta : Real) (m n : Nat) : Real :=
  multibondDisorderFreeEnergy
    (cubicalDualEnds (a := m) (b := n) (c := max m n))
    (fun _ : CubicalPlaquette m n (max m n) => gaugeDualCoupling beta)
    (cubicalXYSheet (a := m) (b := n) (c := max m n)
      (0 : Fin (max m n + 1)))



theorem cubicalRectangularWilsonFreeEnergy_nonneg
    {beta : Real} (hbeta : 0 < beta) (m n : Nat) :
    0 <= cubicalRectangularWilsonFreeEnergy beta m n := by
  have hpos : 0 < gaugeWilsonExpectation
      (cubicalPlaquetteIncidence (a := m) (b := n) (c := max m n))
      (fun _ : CubicalPlaquette m n (max m n) => beta)
      (cubicalXYLoop (a := m) (b := n) (c := max m n)
        (0 : Fin (max m n + 1))) :=
    (gaugeWilsonExpectation_pos_iff_exists_boundary
      cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette m n (max m n) => beta) (fun _ => hbeta)
      (cubicalXYLoop (0 : Fin (max m n + 1)))).mpr
      ⟨cubicalXYSheet (0 : Fin (max m n + 1)),
        cubicalXYSheet_hasWilsonBoundary (0 : Fin (max m n + 1))⟩
  have hle : gaugeWilsonExpectation
      (cubicalPlaquetteIncidence (a := m) (b := n) (c := max m n))
      (fun _ : CubicalPlaquette m n (max m n) => beta)
      (cubicalXYLoop (a := m) (b := n) (c := max m n)
        (0 : Fin (max m n + 1))) <= 1 :=
    (gaugeWilsonExpectation_mem_Icc cubicalPlaquetteIncidence
      (fun _ : CubicalPlaquette m n (max m n) => beta) (fun _ => hbeta)
      (cubicalXYLoop (0 : Fin (max m n + 1)))).2
  rw [cubicalRectangularWilsonFreeEnergy, neg_nonneg]
  exact Real.log_nonpos hpos.le hle



theorem cubicalRectangularWilsonFreeEnergy_eq_disorderFreeEnergy
    {beta : Real} (hbeta : 0 < beta) {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    cubicalRectangularWilsonFreeEnergy beta m n =
      cubicalRectangularDisorderFreeEnergy beta m n := by
  have hc : 0 < max m n := hm.trans_le (Nat.le_max_left m n)
  simpa [cubicalRectangularWilsonFreeEnergy,
    cubicalRectangularDisorderFreeEnergy] using
    (neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy
      hm hn hc (0 : Fin (max m n + 1))
      (fun _ : CubicalPlaquette m n (max m n) => beta) (fun _ => hbeta))



@[simp] theorem cubicalRectangularWilsonFreeEnergy_succ_self
    (beta : Real) (n : Nat) :
    cubicalRectangularWilsonFreeEnergy beta (n + 1) (n + 1) =
      cubicalSquareWilsonFreeEnergy beta n := by
  rw [cubicalRectangularWilsonFreeEnergy, cubicalSquareWilsonFreeEnergy,
    Nat.max_self]



theorem cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate
    {beta : Real} (hbeta : 0 < beta)
    (hglue : HasRectangularBlockGluing
      (cubicalRectangularWilsonFreeEnergy beta)) :
    Tendsto (cubicalSquareWilsonDensity beta) atTop
      (nhds (rectangularSurfaceRate
        (cubicalRectangularWilsonFreeEnergy beta))) := by
  have hfull := rectangularSurfaceDensity_tendsto_rate
    (fun m n => cubicalRectangularWilsonFreeEnergy_nonneg hbeta m n) hglue
  have hshift := hfull.comp (tendsto_add_atTop_nat 1)
  have heq :
      (fun n => rectangularSurfaceDensity
        (cubicalRectangularWilsonFreeEnergy beta) n n) ∘
          (fun n : Nat => n + 1) = cubicalSquareWilsonDensity beta := by
    funext n
    simp [rectangularSurfaceDensity, cubicalSquareWilsonDensity, pow_two]
  rw [heq] at hshift
  exact hshift



theorem cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate
    {beta : Real} (hbeta : 0 < beta)
    (hglue : HasRectangularBlockGluing
      (cubicalRectangularWilsonFreeEnergy beta)) :
    Tendsto (cubicalSquareDisorderDensity beta) atTop
      (nhds (rectangularSurfaceRate
        (cubicalRectangularWilsonFreeEnergy beta))) := by
  apply (cubicalSquareDisorderDensity_tendsto_iff_wilsonDensity hbeta).2
  exact cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate hbeta hglue

end

end StatMech.FrontierA
