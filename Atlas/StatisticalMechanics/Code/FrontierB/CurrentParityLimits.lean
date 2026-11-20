/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.PlusBoxCurrentParity
import Code.FrontierB.FreeBoxCurrentParity

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice

noncomputable def currentEdgeVertexSupport {d : ℕ}
    (F : Finset (Sym2 (Site d))) : Finset (Site d) :=
  F.biUnion Sym2.toFinset

theorem finiteLatticeEdges_subset_bondFinsetTouch
    (d : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    ∃ N, F ⊆ bondFinsetTouch d N := by
  obtain ⟨N, hN⟩ := finite_subset_box
    (↑(currentEdgeVertexSupport F) : Set (Site d))
    (currentEdgeVertexSupport F).finite_toSet
  refine ⟨N, ?_⟩
  intro e heF
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hadj : (hypercubicLattice d).Adj x y := by
        rw [← SimpleGraph.mem_edgeSet]
        exact hF heF
      apply StatMech.Lattice.mk_mem_bondFinsetTouch hadj
      apply Or.inl
      apply hN
      exact Finset.mem_biUnion.mpr ⟨s(x, y), heF, by simp⟩

theorem plusBoxCurrentMeasure_parityAvoid_full_tendsto
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    Tendsto
      (fun n => (plusBoxCurrentMeasure d n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityAvoidCylinder F))
      atTop
      (nhds (ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card))) := by
  obtain ⟨N, hFN⟩ := finiteLatticeEdges_subset_bondFinsetTouch d F hF
  have hFdiag : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hF he)
  have hint := integral_plusMeasure_exp_neg_edgeSpinSum_full_tendsto
    d beta hbeta F hFdiag
  have hreal : Tendsto
      (fun n => (∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card)
      atTop
      (nhds ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card)) :=
    hint.mul_const _
  have hofReal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply (tendsto_add_atTop_iff_nat (f := fun n =>
    (plusBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F)) (N + 1)).mp
  have hofRealTail : Tendsto
      (fun k => ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(plusMeasure d (k + N) beta 0 :
            Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card))
      atTop
      (nhds (ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card))) := by
    apply (tendsto_add_atTop_iff_nat (f := fun n => ENNReal.ofReal
      ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) *
          Real.cosh beta ^ F.card)) N).mpr
    simpa only [Function.comp_apply] using hofReal
  apply hofRealTail.congr'
  filter_upwards with k
  rw [show k + (N + 1) = (k + N) + 1 by omega]
  rw [plusBoxCurrentMeasure_parityAvoid_eq_plusIntegral]
  exact hFN.trans (StatMech.Ising.bondFinsetTouch_subset
    (Nat.le_add_left N k))

theorem freeBoxCurrentMeasure_parityAvoid_full_tendsto
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    Tendsto
      (fun n => (freeBoxCurrentMeasure d n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityAvoidCylinder F))
      atTop
      (nhds (ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card))) := by
  obtain ⟨N, hFN⟩ := finiteLatticeEdges_subset_bondFinsetTouch d F hF
  have hFdiag : ∀ e ∈ F, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hF he)
  have hint := integral_exp_neg_edgeSpinSum_tendsto_freeState
    d beta hbeta F hFdiag
  have hreal : Tendsto
      (fun n => (∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card)
      atTop
      (nhds ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card)) :=
    hint.mul_const _
  have hofReal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply (tendsto_add_atTop_iff_nat (f := fun n =>
    (freeBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F)) (N + 1)).mp
  have hofRealTail : Tendsto
      (fun k => ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(freeMeasure d (k + (N + 1)) beta 0 :
            Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card))
      atTop
      (nhds (ENNReal.ofReal
        ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
            Real.cosh beta ^ F.card))) := by
    apply (tendsto_add_atTop_iff_nat (f := fun n => ENNReal.ofReal
      ((∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) *
          Real.cosh beta ^ F.card)) (N + 1)).mpr
    simpa only [Function.comp_apply] using hofReal
  apply hofRealTail.congr'
  filter_upwards with k
  rw [show k + (N + 1) = (k + N) + 1 by omega]
  rw [freeBoxCurrentMeasure_parityAvoid_eq_freeIntegral]
  exact hFN.trans (StatMech.Ising.bondFinsetTouch_subset
    (Nat.le_add_left N k))

end StatMech.FrontierB
