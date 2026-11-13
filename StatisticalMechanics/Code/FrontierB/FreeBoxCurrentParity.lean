/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.FreeBoxEvenLimit
import Code.FrontierB.PlusBoxCurrentParity

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice
open StatMech.IsingFK

theorem boxGraph_eq_sctBoxGraph (d n : ℕ) :
    StatMech.FK.boxGraph d n = sctBoxGraph d n := by
  ext x y
  rfl

theorem bond_boxConfig_eq_glue
    (d n : ℕ) (tau : ConfigSpace (StatMech.FK.boxVerts d n))
    (e : Sym2 (StatMech.FK.boxVerts d n)) :
    bond tau e = bond (glue (minusField d) tau)
      (StatMech.FK.edgeIncl d n e) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [bond_mk, StatMech.FK.edgeIncl, Sym2.map_mk, bond_mk]
      simp [spin, glue, x.2, y.2]

theorem edgeSpinSum_boxPullbackEdges_free
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n)
    (tau : ConfigSpace (StatMech.FK.boxVerts d (n + 1))) :
    edgeSpinSum (boxPullbackEdges d n F) tau =
      edgeSpinSum F (glue (minusField d) tau) := by
  unfold edgeSpinSum
  simp_rw [bond_boxConfig_eq_glue]
  rw [← Finset.sum_image
    (StatMech.FK.edgeIncl_injective d (n + 1)).injOn]
  rw [image_boxPullbackEdges d n F hF]

theorem freeSpinExpectation_box_eq_freeIntegral
    (d n : ℕ) (beta : ℝ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) :
    ((∑ s : ConfigSpace (StatMech.FK.boxVerts d (n + 1)),
        boltzmannJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) s *
          Real.exp (-beta * edgeSpinSum (boxPullbackEdges d n F) s)) /
      partitionJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)) =
      ∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(freeMeasure d (n + 1) beta 0 :
          Measure (ConfigSpace (Site d))) := by
  have hprob (tau : ConfigSpace (StatMech.FK.boxVerts d (n + 1))) :
      fvProb (minusField d) (n + 1)
        (bondFinsetInternal d (n + 1)) beta 0 tau =
      isingProb (StatMech.FK.boxGraph d (n + 1)) beta 0 tau := by
    rw [sct_fvProb_eq_isingProb]
    unfold isingProb isingWeight isingZ hamiltonian
    congr 1
  change _ = ∫ omega, Real.exp (-beta * edgeSpinSum F omega)
    ∂fvMeasure (minusField d) (n + 1)
      (bondFinsetInternal d (n + 1)) beta 0
  rw [integral_fvMeasure_eq_sum]
  rw [partitionJ_one_eq_isingZ]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro tau htau
  rw [boltzmannJ_one_eq_isingWeight]
  rw [hprob tau]
  rw [edgeSpinSum_boxPullbackEdges_free d n F hF tau]
  unfold isingProb
  ring

theorem freeBoxCurrentMeasure_parityAvoid_eq_freeIntegral
    (d n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 (Site d))) (hF : F ⊆ bondFinsetTouch d n) :
    (freeBoxCurrentMeasure d (n + 1) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F) =
      ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(freeMeasure d (n + 1) beta 0 :
            Measure (ConfigSpace (Site d)))) *
          Real.cosh beta ^ F.card) := by
  let G := StatMech.FK.boxGraph d (n + 1)
  have hbox : boxPullbackEdges d n F ⊆ G.edgeFinset :=
    boxPullbackEdges_subset d n F
  have hcard : (boxPullbackEdges d n F).card = F.card := by
    have hi := congrArg Finset.card (image_boxPullbackEdges d n F hF)
    rw [Finset.card_image_of_injective _
      (StatMech.FK.edgeIncl_injective d (n + 1))] at hi
    exact hi
  have hmeas : MeasurableSet (currentParityAvoidCylinder F) := by
    have hset : currentParityAvoidCylinder F =
        (restrictCurrent F) ⁻¹' {a : ↑F → ℕ | ∀ e, Even (a e)} := by
      ext m
      simp [currentParityAvoidCylinder, restrictCurrent]
    rw [hset]
    exact (continuous_restrictCurrent F).measurable MeasurableSet.of_discrete
  calc
    (freeBoxCurrentMeasure d (n + 1) beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F) =
      (sourcelessCurrentPMF G beta (fun _ => 1) hbeta
        (fun _ => zero_le_one)).toMeasure
          {m | Disjoint (currentParitySupport G m)
            (boxPullbackEdges d n F)} := by
        change Measure.map (extendBoxCurrent d (n + 1))
          (sourcelessCurrentPMF G beta (fun _ => 1) hbeta
            (fun _ => zero_le_one)).toMeasure
            (currentParityAvoidCylinder F) = _
        rw [Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hmeas,
          preimage_currentParityAvoidCylinder_extendBoxCurrent d n F hF]
    _ = (freeParityPMF G beta hbeta).toMeasure
          {H | Disjoint H (boxPullbackEdges d n F)} := by
        rw [← sourcelessCurrentPMF_map_currentParitySupport]
        rw [PMF.toMeasure_map_apply]
        · rfl
        · exact Measurable.of_discrete
        · exact MeasurableSet.of_discrete
    _ = ENNReal.ofReal
        ((((∑ s : ConfigSpace (StatMech.FK.boxVerts d (n + 1)),
            boltzmannJ G beta (fun _ => 1) s *
              Real.exp (-beta * edgeSpinSum (boxPullbackEdges d n F) s)) /
            partitionJ G beta (fun _ => 1)) *
          Real.cosh beta ^ (boxPullbackEdges d n F).card)) :=
      freeParityMeasure_avoid_eq_spinExpectation G beta hbeta
        (boxPullbackEdges d n F) hbox
    _ = _ := by
      rw [freeSpinExpectation_box_eq_freeIntegral d n beta F hF, hcard]

end StatMech.FrontierB
