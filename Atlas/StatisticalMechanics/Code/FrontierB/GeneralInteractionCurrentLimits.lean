/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.BoundaryCurrentTail
import Code.FrontierB.InfiniteCurrentFiniteMarginals
import Code.FrontierB.InfiniteCurrentCompactness
import Code.FK.InfiniteVolume

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Lattice


noncomputable def positiveInteractionGraph {d : Nat}
    (J : Sym2 (Site d) -> Real) (hdiag : forall x, J s(x, x) = 0) :
    SimpleGraph (Site d) where
  Adj x y := 0 < J s(x, y)
  symm := by
    intro x y h
    simpa only [Sym2.eq_swap] using h
  loopless := ⟨by
    intro x h
    rw [hdiag x] at h
    exact (lt_irrefl 0 h)⟩



structure SummableFerromagneticInteraction (d : Nat) where
  coupling : Sym2 (Site d) -> Real
  nonneg : forall e, 0 <= coupling e
  diagonal : forall x, coupling s(x, x) = 0
  translation_invariant : forall (a x y : Site d),
    coupling s(a + x, a + y) = coupling s(x, y)
  summable_origin : Summable (fun y => coupling s((0 : Site d), y))
  irreducible : (positiveInteractionGraph coupling diagonal).Connected


noncomputable def SummableFerromagneticInteraction.strength {d : Nat}
    (I : SummableFerromagneticInteraction d) : Real :=
  ∑' y, I.coupling s((0 : Site d), y)


theorem SummableFerromagneticInteraction.row_comp_addLeft {d : Nat}
    (I : SummableFerromagneticInteraction d) (x : Site d) :
    (fun y => I.coupling s(x, y)) ∘ Equiv.addLeft x =
      fun y => I.coupling s((0 : Site d), y) := by
  funext y
  change I.coupling s(x, x + y) = I.coupling s(0, y)
  simpa using I.translation_invariant x (0 : Site d) y


theorem SummableFerromagneticInteraction.row_summable {d : Nat}
    (I : SummableFerromagneticInteraction d) (x : Site d) :
    Summable (fun y => I.coupling s(x, y)) := by
  apply (Equiv.addLeft x).summable_iff.mp
  simpa only [I.row_comp_addLeft x] using I.summable_origin


theorem SummableFerromagneticInteraction.row_tsum_eq_strength {d : Nat}
    (I : SummableFerromagneticInteraction d) (x : Site d) :
    (∑' y, I.coupling s(x, y)) = I.strength := by
  calc
    (∑' y, I.coupling s(x, y)) =
        ∑' y, I.coupling s(x, Equiv.addLeft x y) :=
      (Equiv.tsum_eq (Equiv.addLeft x)
        (fun y => I.coupling s(x, y))).symm
    _ = I.strength := by
      apply tsum_congr
      intro y
      exact congrFun (I.row_comp_addLeft x) y

theorem SummableFerromagneticInteraction.strength_nonneg {d : Nat}
    (I : SummableFerromagneticInteraction d) : 0 <= I.strength := by
  exact tsum_nonneg fun y => I.nonneg _


theorem SummableFerromagneticInteraction.coupling_le_strength {d : Nat}
    (I : SummableFerromagneticInteraction d) (e : Sym2 (Site d)) :
    I.coupling e <= I.strength := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [← I.row_tsum_eq_strength x]
      exact (I.row_summable x).le_tsum y (fun z _ => I.nonneg s(x, z))


noncomputable def interactionBoxVertices (d n : Nat) : Finset (Site d) :=
  (box_finite d n).toFinset

@[simp] theorem mem_interactionBoxVertices {d n : Nat} {x : Site d} :
    x ∈ interactionBoxVertices d n ↔ x ∈ box d n := by
  simp [interactionBoxVertices]



def interactionBoxGraph (d n : Nat) :
    SimpleGraph (interactionBoxVertices d n) := ⊤

noncomputable instance interactionBoxGraph_decidableAdj (d n : Nat) :
    DecidableRel (interactionBoxGraph d n).Adj := by
  classical
  exact Classical.decRel _


noncomputable def interactionBoxCoupling {d : Nat}
    (J : Sym2 (Site d) -> Real) (n : Nat) :
    Sym2 (interactionBoxVertices d n) -> Real :=
  fun e => J (Sym2.map Subtype.val e)


def interactionBoxEdgeIncl (d n : Nat) :
    (interactionBoxGraph d n).edgeFinset -> Sym2 (Site d) :=
  fun e => Sym2.map Subtype.val e.1

theorem interactionBoxEdgeIncl_injective (d n : Nat) :
    Function.Injective (interactionBoxEdgeIncl d n) := by
  intro e f hef
  apply Subtype.ext
  exact Sym2.map.injective Subtype.val_injective hef


noncomputable def extendInteractionBoxCurrent (d n : Nat)
    (m : EdgeCurrent (interactionBoxGraph d n)) :
    InfiniteCurrentConfig (Sym2 (Site d)) :=
  fun e => if h : e ∈ Set.range (interactionBoxEdgeIncl d n)
    then m h.choose else 0

@[simp] theorem extendInteractionBoxCurrent_included (d n : Nat)
    (m : EdgeCurrent (interactionBoxGraph d n))
    (e : (interactionBoxGraph d n).edgeFinset) :
    extendInteractionBoxCurrent d n m (interactionBoxEdgeIncl d n e) = m e := by
  unfold extendInteractionBoxCurrent
  split
  · rename_i h
    exact congrArg m (interactionBoxEdgeIncl_injective d n h.choose_spec)
  · rename_i h
    exact (h <| Exists.intro e rfl).elim

theorem extendInteractionBoxCurrent_outside (d n : Nat)
    (m : EdgeCurrent (interactionBoxGraph d n)) (e : Sym2 (Site d))
    (he : e ∉ Set.range (interactionBoxEdgeIncl d n)) :
    extendInteractionBoxCurrent d n m e = 0 := by
  simp [extendInteractionBoxCurrent, he]

theorem measurable_extendInteractionBoxCurrent (d n : Nat) :
    Measurable (extendInteractionBoxCurrent d n) :=
  Measurable.of_discrete


noncomputable def generalFreeBoxCurrentMeasure {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  let G := interactionBoxGraph d n
  let Jn := interactionBoxCoupling J n
  let hJn : forall e, 0 <= Jn e := fun e =>
    hJ (Sym2.map Subtype.val e)
  ⟨((sourcelessCurrentPMF G beta Jn hbeta hJn).toMeasure).map
      (extendInteractionBoxCurrent d n),
    Measure.isProbabilityMeasure_map
      (measurable_extendInteractionBoxCurrent d n).aemeasurable⟩



noncomputable def interactionPlusInterior (d n : Nat) :
    Finset (interactionBoxVertices d (2 * n + 1)) := by
  classical
  exact Finset.univ.filter fun x => x.1 ∈ box d n


noncomputable def generalPlusBoxCurrentMeasure {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  let r := 2 * n + 1
  let G := interactionBoxGraph d r
  let Jn := interactionBoxCoupling J r
  let hJn : forall e, 0 <= Jn e := fun e =>
    hJ (Sym2.map Subtype.val e)
  ⟨((boundaryCurrentPMF G beta Jn hbeta hJn
      (interactionPlusInterior d n)).toMeasure).map
      (extendInteractionBoxCurrent d r),
    Measure.isProbabilityMeasure_map
      (measurable_extendInteractionBoxCurrent d r).aemeasurable⟩

set_option maxHeartbeats 800000 in


theorem generalFreeBoxCurrentMeasure_edge_tail {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : (interactionBoxGraph d n).edgeFinset) (K : Nat) :
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K <= m (interactionBoxEdgeIncl d n e)} =
      (sourcelessCurrentMeasure (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta
          (fun e => hJ (Sym2.map Subtype.val e)) :
          Measure (EdgeCurrent (interactionBoxGraph d n)))
        {m | K <= m e} := by
  change Measure.map (extendInteractionBoxCurrent d n)
      ((sourcelessCurrentPMF (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))).toMeasure)
        {m | K <= m (interactionBoxEdgeIncl d n e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K <= m (interactionBoxEdgeIncl d n e)} :=
    (measurable_pi_apply (interactionBoxEdgeIncl d n e)) MeasurableSet.of_discrete
  rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hset]
  congr 1
  ext m
  simp

set_option maxHeartbeats 800000 in


theorem generalPlusBoxCurrentMeasure_edge_tail {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : (interactionBoxGraph d (2 * n + 1)).edgeFinset) (K : Nat) :
    (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K <= m (interactionBoxEdgeIncl d (2 * n + 1) e)} =
      (boundaryCurrentMeasure (interactionBoxGraph d (2 * n + 1)) beta
        (interactionBoxCoupling J (2 * n + 1)) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))
        (interactionPlusInterior d n) :
          Measure (EdgeCurrent (interactionBoxGraph d (2 * n + 1))))
        {m | K <= m e} := by
  change Measure.map (extendInteractionBoxCurrent d (2 * n + 1))
      ((boundaryCurrentPMF (interactionBoxGraph d (2 * n + 1)) beta
        (interactionBoxCoupling J (2 * n + 1)) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))
        (interactionPlusInterior d n)).toMeasure)
        {m | K <= m (interactionBoxEdgeIncl d (2 * n + 1) e)} = _
  have hset : MeasurableSet
      {m : InfiniteCurrentConfig (Sym2 (Site d)) |
        K <= m (interactionBoxEdgeIncl d (2 * n + 1) e)} :=
    (measurable_pi_apply
      (interactionBoxEdgeIncl d (2 * n + 1) e)) MeasurableSet.of_discrete
  rw [Measure.map_apply
    (measurable_extendInteractionBoxCurrent d (2 * n + 1)) hset]
  congr 1
  ext m
  simp

set_option maxHeartbeats 800000 in




theorem generalFreeBoxCurrentMeasure_edge_inverse_tail_le {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : Sym2 (Site d)) (K : Nat) (hK : 0 < K) :
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K <= m e} <=
      ENNReal.ofReal (Real.exp (beta * J e)) / K := by
  by_cases he : e ∈ Set.range (interactionBoxEdgeIncl d n)
  · obtain ⟨f, rfl⟩ := he
    rw [generalFreeBoxCurrentMeasure_edge_tail]
    calc
      (sourcelessCurrentMeasure (interactionBoxGraph d n) beta
          (interactionBoxCoupling J n) hbeta
            (fun e => hJ (Sym2.map Subtype.val e)) :
          Measure (EdgeCurrent (interactionBoxGraph d n)))
          {m | K <= m f} <=
          ENNReal.ofReal
            (Real.exp (beta * interactionBoxCoupling J n f.1) / K) :=
        sourcelessCurrentMeasure_edge_inverse_tail_le
          (interactionBoxGraph d n) beta (interactionBoxCoupling J n)
          hbeta (fun e => hJ (Sym2.map Subtype.val e)) f K hK
      _ = ENNReal.ofReal
          (Real.exp (beta * J (interactionBoxEdgeIncl d n f))) / K := by
        rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 hK)]
        simp [interactionBoxCoupling, interactionBoxEdgeIncl]
  · change Measure.map (extendInteractionBoxCurrent d n)
      ((sourcelessCurrentPMF (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))).toMeasure)
        {m | K <= m e} <= _
    have hset : MeasurableSet
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K <= m e} :=
      (measurable_pi_apply e) MeasurableSet.of_discrete
    rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hset]
    have hempty : extendInteractionBoxCurrent d n ⁻¹'
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K <= m e} = ∅ := by
      ext m
      simp [extendInteractionBoxCurrent_outside d n m e he,
        Nat.not_le_of_lt hK]
    rw [hempty, measure_empty]
    exact bot_le

set_option maxHeartbeats 800000 in




theorem generalPlusBoxCurrentMeasure_edge_inverse_tail_le {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : Sym2 (Site d)) (K : Nat) (hK : 0 < K) :
    (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K <= m e} <=
      ENNReal.ofReal (Real.exp (beta * J e)) / K := by
  let r := 2 * n + 1
  by_cases he : e ∈ Set.range (interactionBoxEdgeIncl d r)
  · obtain ⟨f, rfl⟩ := he
    change (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K <= m (interactionBoxEdgeIncl d (2 * n + 1) f)} <= _
    rw [generalPlusBoxCurrentMeasure_edge_tail]
    calc
      (boundaryCurrentMeasure (interactionBoxGraph d (2 * n + 1)) beta
          (interactionBoxCoupling J (2 * n + 1)) hbeta
            (fun e => hJ (Sym2.map Subtype.val e))
          (interactionPlusInterior d n) :
          Measure (EdgeCurrent (interactionBoxGraph d (2 * n + 1))))
          {m | K <= m f} <=
          ENNReal.ofReal
            (Real.exp (beta * interactionBoxCoupling J (2 * n + 1) f.1) / K) :=
        boundaryCurrentMeasure_edge_inverse_tail_le
          (interactionBoxGraph d (2 * n + 1)) beta
          (interactionBoxCoupling J (2 * n + 1)) hbeta
            (fun e => hJ (Sym2.map Subtype.val e))
          (interactionPlusInterior d n) f K hK
      _ = ENNReal.ofReal
          (Real.exp (beta * J (interactionBoxEdgeIncl d (2 * n + 1) f))) / K := by
        rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 hK)]
        simp [interactionBoxCoupling, interactionBoxEdgeIncl]
  · change Measure.map (extendInteractionBoxCurrent d (2 * n + 1))
      ((boundaryCurrentPMF (interactionBoxGraph d (2 * n + 1)) beta
        (interactionBoxCoupling J (2 * n + 1)) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))
        (interactionPlusInterior d n)).toMeasure) {m | K <= m e} <= _
    have hset : MeasurableSet
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K <= m e} :=
      (measurable_pi_apply e) MeasurableSet.of_discrete
    rw [Measure.map_apply
      (measurable_extendInteractionBoxCurrent d (2 * n + 1)) hset]
    have hempty : extendInteractionBoxCurrent d (2 * n + 1) ⁻¹'
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K <= m e} = ∅ := by
      ext m
      have he' : e ∉ Set.range
          (interactionBoxEdgeIncl d (2 * n + 1)) := by
        simpa only [r] using he
      simp [extendInteractionBoxCurrent_outside d (2 * n + 1) m e he',
        Nat.not_le_of_lt hK]
    rw [hempty, measure_empty]
    exact bot_le


theorem generalFreeBoxCurrentMeasure_uniform_inverse_tail_le {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : Sym2 (Site d)) (K : Nat) (hK : 0 < K) :
    (generalFreeBoxCurrentMeasure I.coupling I.nonneg n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K <= m e} <=
      ENNReal.ofReal (Real.exp (beta * I.strength)) / K := by
  calc
    _ <= ENNReal.ofReal (Real.exp (beta * I.coupling e)) / K :=
      generalFreeBoxCurrentMeasure_edge_inverse_tail_le
        I.coupling I.nonneg n beta hbeta e K hK
    _ <= ENNReal.ofReal (Real.exp (beta * I.strength)) / K := by
      gcongr
      exact I.coupling_le_strength e


theorem generalPlusBoxCurrentMeasure_uniform_inverse_tail_le {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (n : Nat) (beta : Real) (hbeta : 0 <= beta)
    (e : Sym2 (Site d)) (K : Nat) (hK : 0 < K) :
    (generalPlusBoxCurrentMeasure I.coupling I.nonneg n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K <= m e} <=
      ENNReal.ofReal (Real.exp (beta * I.strength)) / K := by
  calc
    _ <= ENNReal.ofReal (Real.exp (beta * I.coupling e)) / K :=
      generalPlusBoxCurrentMeasure_edge_inverse_tail_le
        I.coupling I.nonneg n beta hbeta e K hK
    _ <= ENNReal.ofReal (Real.exp (beta * I.strength)) / K := by
      gcongr
      exact I.coupling_le_strength e


theorem generalFreeBoxCurrentMeasure_tight {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (beta : Real) (hbeta : 0 <= beta) :
    IsTightMeasureSet (Set.range fun n =>
      (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))) := by
  apply isTightMeasureSet_range_of_coordinate_tight
  intro e epsilon hepsilon
  obtain ⟨K, hKpos, hK⟩ := ENNReal.exists_nat_pos_mul_gt
    hepsilon.ne' (ENNReal.ofReal_ne_top :
      ENNReal.ofReal (Real.exp (beta * J e)) ≠ ∞)
  refine ⟨K, fun n => ?_⟩
  exact (generalFreeBoxCurrentMeasure_edge_inverse_tail_le
    J hJ n beta hbeta e K hKpos).trans
      (ENNReal.div_le_of_le_mul' hK.le)


theorem generalPlusBoxCurrentMeasure_tight {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (beta : Real) (hbeta : 0 <= beta) :
    IsTightMeasureSet (Set.range fun n =>
      (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))) := by
  apply isTightMeasureSet_range_of_coordinate_tight
  intro e epsilon hepsilon
  obtain ⟨K, hKpos, hK⟩ := ENNReal.exists_nat_pos_mul_gt
    hepsilon.ne' (ENNReal.ofReal_ne_top :
      ENNReal.ofReal (Real.exp (beta * J e)) ≠ ∞)
  refine ⟨K, fun n => ?_⟩
  exact (generalPlusBoxCurrentMeasure_edge_inverse_tail_le
    J hJ n beta hbeta e K hKpos).trans
      (ENNReal.div_le_of_le_mul' hK.le)



theorem generalFreePlusBoxCurrentMeasure_joint_subsequence {d : Nat}
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 <= J e)
    (beta : Real) (hbeta : 0 <= beta) :
    ∃ (nuFree nuPlus : ProbabilityMeasure
        (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : Nat -> Nat), StrictMono phi ∧
        WeakCurrentConverges
          ((fun n => generalFreeBoxCurrentMeasure J hJ n beta hbeta) ∘ phi)
          nuFree ∧
        WeakCurrentConverges
          ((fun n => generalPlusBoxCurrentMeasure J hJ n beta hbeta) ∘ phi)
          nuPlus := by
  obtain ⟨nuFree, phiFree, hphiFree, hfree⟩ :=
    weakCurrent_subsequence_of_tight
      (fun n => generalFreeBoxCurrentMeasure J hJ n beta hbeta)
      (generalFreeBoxCurrentMeasure_tight J hJ beta hbeta)
  have hplusTight : IsTightMeasureSet
      (Set.range fun n =>
        (generalPlusBoxCurrentMeasure J hJ (phiFree n) beta hbeta :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))) :=
    (generalPlusBoxCurrentMeasure_tight J hJ beta hbeta).subset
      (Set.range_comp_subset_range phiFree
        (fun n => (generalPlusBoxCurrentMeasure J hJ n beta hbeta :
          Measure (InfiniteCurrentConfig (Sym2 (Site d))))))
  obtain ⟨nuPlus, phiPlus, hphiPlus, hplus⟩ :=
    weakCurrent_subsequence_of_tight
      ((fun n => generalPlusBoxCurrentMeasure J hJ n beta hbeta) ∘ phiFree)
      hplusTight
  refine ⟨nuFree, nuPlus, phiFree ∘ phiPlus,
    hphiFree.comp hphiPlus, ?_, hplus⟩
  exact hfree.comp hphiPlus.tendsto_atTop



structure GeneralInteractionCurrentLimitData {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) where
  freeLimit : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))
  plusLimit : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))
  subsequence : Nat -> Nat
  strictMono_subsequence : StrictMono subsequence
  free_tendsto : WeakCurrentConverges
    ((fun n => generalFreeBoxCurrentMeasure
      I.coupling I.nonneg n beta hbeta) ∘ subsequence) freeLimit
  plus_tendsto : WeakCurrentConverges
    ((fun n => generalPlusBoxCurrentMeasure
      I.coupling I.nonneg n beta hbeta) ∘ subsequence) plusLimit


noncomputable def generalInteractionCurrentLimitData {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    GeneralInteractionCurrentLimitData I beta hbeta :=
  Classical.choice (show Nonempty
      (GeneralInteractionCurrentLimitData I beta hbeta) from by
    obtain ⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩ :=
      generalFreePlusBoxCurrentMeasure_joint_subsequence
        I.coupling I.nonneg beta hbeta
    exact ⟨⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩⟩)


noncomputable def generalInfiniteFreeCurrentMeasure {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (generalInteractionCurrentLimitData I beta hbeta).freeLimit


noncomputable def generalInfinitePlusCurrentMeasure {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (generalInteractionCurrentLimitData I beta hbeta).plusLimit


noncomputable def generalCurrentBoxSubsequence {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) : Nat -> Nat :=
  (generalInteractionCurrentLimitData I beta hbeta).subsequence

theorem generalCurrentBoxSubsequence_strictMono {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    StrictMono (generalCurrentBoxSubsequence I beta hbeta) :=
  (generalInteractionCurrentLimitData I beta hbeta).strictMono_subsequence

theorem generalFreeBoxCurrentMeasure_tendsto_infinite {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    WeakCurrentConverges
      ((fun n => generalFreeBoxCurrentMeasure
        I.coupling I.nonneg n beta hbeta) ∘
          generalCurrentBoxSubsequence I beta hbeta)
      (generalInfiniteFreeCurrentMeasure I beta hbeta) :=
  (generalInteractionCurrentLimitData I beta hbeta).free_tendsto

theorem generalPlusBoxCurrentMeasure_tendsto_infinite {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    WeakCurrentConverges
      ((fun n => generalPlusBoxCurrentMeasure
        I.coupling I.nonneg n beta hbeta) ∘
          generalCurrentBoxSubsequence I beta hbeta)
      (generalInfinitePlusCurrentMeasure I beta hbeta) :=
  (generalInteractionCurrentLimitData I beta hbeta).plus_tendsto



theorem generalFreeBoxCurrentMeasure_cylinder_tendsto_infinite {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta)
    (S : Finset (Sym2 (Site d))) (A : Set (S -> Nat)) :
    Tendsto
      (fun k => generalFreeBoxCurrentMeasure I.coupling I.nonneg
        (generalCurrentBoxSubsequence I beta hbeta k) beta hbeta
          (currentCylinder S A)) atTop
      (nhds (generalInfiniteFreeCurrentMeasure I beta hbeta
        (currentCylinder S A))) :=
  (generalFreeBoxCurrentMeasure_tendsto_infinite I beta hbeta).cylinder S A



theorem generalPlusBoxCurrentMeasure_cylinder_tendsto_infinite {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta)
    (S : Finset (Sym2 (Site d))) (A : Set (S -> Nat)) :
    Tendsto
      (fun k => generalPlusBoxCurrentMeasure I.coupling I.nonneg
        (generalCurrentBoxSubsequence I beta hbeta k) beta hbeta
          (currentCylinder S A)) atTop
      (nhds (generalInfinitePlusCurrentMeasure I beta hbeta
        (currentCylinder S A))) :=
  (generalPlusBoxCurrentMeasure_tendsto_infinite I beta hbeta).cylinder S A



structure GeneralInteractionCurrentSubsequencePackage {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) : Prop where
  subsequence_strict : StrictMono (generalCurrentBoxSubsequence I beta hbeta)
  free_weak : WeakCurrentConverges
    ((fun n => generalFreeBoxCurrentMeasure
      I.coupling I.nonneg n beta hbeta) ∘
        generalCurrentBoxSubsequence I beta hbeta)
    (generalInfiniteFreeCurrentMeasure I beta hbeta)
  plus_weak : WeakCurrentConverges
    ((fun n => generalPlusBoxCurrentMeasure
      I.coupling I.nonneg n beta hbeta) ∘
        generalCurrentBoxSubsequence I beta hbeta)
    (generalInfinitePlusCurrentMeasure I beta hbeta)
  free_cylinder : forall (S : Finset (Sym2 (Site d))) (A : Set (S -> Nat)),
    Tendsto
      (fun k => generalFreeBoxCurrentMeasure I.coupling I.nonneg
        (generalCurrentBoxSubsequence I beta hbeta k) beta hbeta
          (currentCylinder S A)) atTop
      (nhds (generalInfiniteFreeCurrentMeasure I beta hbeta
        (currentCylinder S A)))
  plus_cylinder : forall (S : Finset (Sym2 (Site d))) (A : Set (S -> Nat)),
    Tendsto
      (fun k => generalPlusBoxCurrentMeasure I.coupling I.nonneg
        (generalCurrentBoxSubsequence I beta hbeta k) beta hbeta
          (currentCylinder S A)) atTop
      (nhds (generalInfinitePlusCurrentMeasure I beta hbeta
        (currentCylinder S A)))

theorem generalInteractionCurrentSubsequencePackage {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) :
    GeneralInteractionCurrentSubsequencePackage I beta hbeta where
  subsequence_strict := generalCurrentBoxSubsequence_strictMono I beta hbeta
  free_weak := generalFreeBoxCurrentMeasure_tendsto_infinite I beta hbeta
  plus_weak := generalPlusBoxCurrentMeasure_tendsto_infinite I beta hbeta
  free_cylinder := generalFreeBoxCurrentMeasure_cylinder_tendsto_infinite I beta hbeta
  plus_cylinder := generalPlusBoxCurrentMeasure_cylinder_tendsto_infinite I beta hbeta

end StatMech.FrontierB
