/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.CurrentParityDetermination
import Code.FrontierB.PlusBoxCurrentParity

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice
open StatMech.IsingFK

noncomputable def boxPullbackEdgeSubtypes (d n : ℕ)
    (F : Finset (Sym2 (Site d))) :
    Finset (StatMech.FK.boxGraph d (n + 1)).edgeFinset :=
  Finset.univ.filter fun e =>
    StatMech.FK.edgeIncl d (n + 1) e.1 ∈ F

noncomputable def boxPullbackEdgeEquiv
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) :
    ↑(boxPullbackEdgeSubtypes d n F) ≃ ↑F :=
  Equiv.ofBijective
    (fun e => ⟨StatMech.FK.edgeIncl d (n + 1) e.1.1,
      (Finset.mem_filter.mp e.2).2⟩)
    ⟨by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact StatMech.FK.edgeIncl_injective d (n + 1)
        (congrArg Subtype.val hab),
    by
      intro e
      have himage := StatMech.IsingFK.hbx_touch_subset_image d n (hF e.2)
      rw [Finset.mem_image] at himage
      obtain ⟨f, hfedge, hfe⟩ := himage
      let fs : (StatMech.FK.boxGraph d (n + 1)).edgeFinset := ⟨f, hfedge⟩
      let z : ↑(boxPullbackEdgeSubtypes d n F) :=
        ⟨fs, by simp [boxPullbackEdgeSubtypes, fs, hfe, e.2]⟩
      exact ⟨z, Subtype.ext hfe⟩⟩

noncomputable def pullbackCurrentPattern
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) (a : ↑F → ℕ) :
    ↑(boxPullbackEdgeSubtypes d n F) → ℕ :=
  a ∘ boxPullbackEdgeEquiv d n F hF

noncomputable def pushforwardBoxLocalCurrent
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n)
    (a : ↑(boxPullbackEdgeSubtypes d n F) → ℕ) : ↑F → ℕ :=
  a ∘ (boxPullbackEdgeEquiv d n F hF).symm

theorem restrictCurrent_extendBoxCurrent
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n)
    (m : EdgeCurrent (StatMech.FK.boxGraph d (n + 1))) :
    restrictCurrent F (extendBoxCurrent d (n + 1) m) =
      pushforwardBoxLocalCurrent d n F hF
        (restrictCurrent (boxPullbackEdgeSubtypes d n F) m) := by
  funext e
  let f := (boxPullbackEdgeEquiv d n F hF).symm e
  have hincl : StatMech.FK.edgeIncl d (n + 1) f.1.1 = e.1 :=
    congrArg Subtype.val
      ((boxPullbackEdgeEquiv d n F hF).apply_symm_apply e)
  change extendBoxCurrent d (n + 1) m e.1 = m f.1
  rw [← hincl]
  change extendBoxCurrent d (n + 1) m
    (boxCurrentEdgeIncl d (n + 1) f.1) = m f.1
  exact extendBoxCurrent_included d (n + 1) m f.1

theorem finiteParityKernel_pullbackCurrentPattern
    (d n : ℕ) (beta : ℝ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) (a : ↑F → ℕ) :
    finiteParityKernel (boxPullbackEdgeSubtypes d n F) beta
        (currentLocalParity (pullbackCurrentPattern d n F hF a))
        (pullbackCurrentPattern d n F hF a) =
      finiteParityKernel F beta (currentLocalParity a) a := by
  unfold finiteParityKernel
  apply Fintype.prod_equiv (boxPullbackEdgeEquiv d n F hF)
  intro i
  rfl

theorem preimage_currentCylinder_singleton_extendBoxCurrent
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) (a : ↑F → ℕ) :
    extendBoxCurrent d (n + 1) ⁻¹' currentCylinder F {a} =
      {m | restrictCurrent (boxPullbackEdgeSubtypes d n F) m =
        pullbackCurrentPattern d n F hF a} := by
  ext m
  simp only [Set.mem_preimage, currentCylinder, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · intro hm
    funext f
    have hc := congrFun hm (boxPullbackEdgeEquiv d n F hF f)
    change extendBoxCurrent d (n + 1) m
        (boxPullbackEdgeEquiv d n F hF f).1 =
      a (boxPullbackEdgeEquiv d n F hF f) at hc
    change m f.1 = a (boxPullbackEdgeEquiv d n F hF f)
    rw [← hc]
    change m f.1 = extendBoxCurrent d (n + 1) m
      (StatMech.FK.edgeIncl d (n + 1) f.1.1)
    symm
    exact extendBoxCurrent_included d (n + 1) m f.1
  · intro hm
    funext e
    let f := (boxPullbackEdgeEquiv d n F hF).symm e
    have hc := congrFun hm f
    have hincl : StatMech.FK.edgeIncl d (n + 1) f.1.1 = e.1 :=
      congrArg Subtype.val
        ((boxPullbackEdgeEquiv d n F hF).apply_symm_apply e)
    change extendBoxCurrent d (n + 1) m e.1 = a e
    rw [← hincl]
    change extendBoxCurrent d (n + 1) m
      (boxCurrentEdgeIncl d (n + 1) f.1) = a e
    rw [extendBoxCurrent_included d (n + 1) m f.1]
    simpa [pullbackCurrentPattern, f] using hc

theorem currentLocalParity_restrictCurrent_eq_restrictParity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset G.edgeFinset) (m : EdgeCurrent G) :
    currentLocalParity (restrictCurrent S m) =
      restrictParity G S (currentParitySupport G m) := by
  funext e
  simp only [currentLocalParity, restrictCurrent, restrictParity]
  by_cases hodd : Odd (m e.1)
  · have hmem : e.1.1 ∈ currentParitySupport G m :=
      (mem_currentParitySupport G m e.1).2 hodd
    simp [hodd, hmem]
  · have hmem : e.1.1 ∉ currentParitySupport G m := fun h =>
      hodd ((mem_currentParitySupport G m e.1).1 h)
    simp [hodd, hmem]

theorem boundaryCurrentLocalParityPMF
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (hbeta : 0 < beta) (interior : Finset V)
    (S : Finset G.edgeFinset) :
    PMF.map currentLocalParity
        (PMF.map (restrictCurrent S)
          (boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one) interior)) =
      PMF.map (restrictParity G S)
        (boundaryParityPMF G beta hbeta.le interior) := by
  rw [boundaryParityPMF, PMF.map_comp, PMF.map_comp]
  congr 1
  funext m
  exact currentLocalParity_restrictCurrent_eq_restrictParity G S m

theorem sourcelessCurrentLocalParityPMF
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (hbeta : 0 < beta) (S : Finset G.edgeFinset) :
    PMF.map currentLocalParity
        (PMF.map (restrictCurrent S)
          (sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
            (fun _ => zero_le_one))) =
      PMF.map (restrictParity G S) (freeParityPMF G beta hbeta.le) := by
  rw [← sourcelessCurrentPMF_map_currentParitySupport,
    PMF.map_comp, PMF.map_comp]
  congr 1
  funext m
  exact currentLocalParity_restrictCurrent_eq_restrictParity G S m

def currentParityPatternCylinder {E : Type*} (F : Finset E)
    (odd : ↑F → Bool) : Set (InfiniteCurrentConfig E) :=
  currentCylinder F {a | currentLocalParity a = odd}

noncomputable def pullbackParityPattern
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) (odd : ↑F → Bool) :
    ↑(boxPullbackEdgeSubtypes d n F) → Bool :=
  odd ∘ boxPullbackEdgeEquiv d n F hF

theorem currentLocalParity_pushforward_iff
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n)
    (a : ↑(boxPullbackEdgeSubtypes d n F) → ℕ)
    (odd : ↑F → Bool) :
    currentLocalParity (pushforwardBoxLocalCurrent d n F hF a) = odd ↔
      currentLocalParity a = pullbackParityPattern d n F hF odd := by
  constructor
  · intro h
    funext e
    have hc := congrFun h (boxPullbackEdgeEquiv d n F hF e)
    simpa [currentLocalParity, pushforwardBoxLocalCurrent,
      pullbackParityPattern] using hc
  · intro h
    funext e
    have hc := congrFun h ((boxPullbackEdgeEquiv d n F hF).symm e)
    simpa [currentLocalParity, pushforwardBoxLocalCurrent,
      pullbackParityPattern] using hc

theorem preimage_currentParityPatternCylinder_extendBoxCurrent
    (d n : ℕ) (F : Finset (Sym2 (Site d)))
    (hF : F ⊆ bondFinsetTouch d n) (odd : ↑F → Bool) :
    extendBoxCurrent d (n + 1) ⁻¹' currentParityPatternCylinder F odd =
      {m | currentLocalParity
        (restrictCurrent (boxPullbackEdgeSubtypes d n F) m) =
          pullbackParityPattern d n F hF odd} := by
  ext m
  change currentLocalParity
      (restrictCurrent F (extendBoxCurrent d (n + 1) m)) = odd ↔ _
  rw [restrictCurrent_extendBoxCurrent d n F hF m]
  exact currentLocalParity_pushforward_iff d n F hF _ odd


theorem plusBoxCurrentMeasure_pattern_factor
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d))) (hF : F ⊆ bondFinsetTouch d n)
    (a : ↑F → ℕ) :
    (plusBoxCurrentMeasure d (n + 1) beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder F {a}) =
      (plusBoxCurrentMeasure d (n + 1) beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder F (currentLocalParity a)) *
        finiteParityPMF F beta hbeta (currentLocalParity a) a := by
  let G := StatMech.FK.boxGraph d (n + 1)
  let interior := boxCurrentInterior d (n + 1)
  let S := boxPullbackEdgeSubtypes d n F
  let p := boundaryCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one) interior
  let q := PMF.map (restrictParity G S)
    (boundaryParityPMF G beta hbeta.le interior)
  let a' := pullbackCurrentPattern d n F hF a
  have hcurrent : PMF.map (restrictCurrent S) p =
      q.bind (finiteParityPMF S beta hbeta) := by
    exact boundaryCurrentFiniteMarginal_eq_localParity_bind
      G beta hbeta interior S
  have hpoint := congrArg (fun r : PMF (↑S → ℕ) => r a') hcurrent
  change (PMF.map (restrictCurrent S) p) a' =
    q.bind (finiteParityPMF S beta hbeta) a' at hpoint
  rw [bind_finiteParityPMF_apply] at hpoint
  have hparity : currentLocalParity a' =
      pullbackParityPattern d n F hF (currentLocalParity a) := by
    rfl
  have hkernel : finiteParityPMF S beta hbeta
      (currentLocalParity a') a' =
      finiteParityPMF F beta hbeta (currentLocalParity a) a := by
    rw [finiteParityPMF_apply, finiteParityPMF_apply,
      finiteParityKernel_pullbackCurrentPattern]
  have hkernel' : finiteParityPMF S beta hbeta
      (pullbackParityPattern d n F hF (currentLocalParity a)) a' =
      finiteParityPMF F beta hbeta (currentLocalParity a) a := by
    rw [← hparity]
    exact hkernel
  have hsingle : MeasurableSet (currentCylinder F {a}) :=
    measurableSet_currentCylinder F {a}
  have hparMeas : MeasurableSet
      (currentParityPatternCylinder F (currentLocalParity a)) :=
    measurableSet_currentCylinder F _
  change Measure.map (extendBoxCurrent d (n + 1)) p.toMeasure
      (currentCylinder F {a}) =
    Measure.map (extendBoxCurrent d (n + 1)) p.toMeasure
      (currentParityPatternCylinder F (currentLocalParity a)) * _
  rw [Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hsingle,
    preimage_currentCylinder_singleton_extendBoxCurrent d n F hF a,
    Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hparMeas,
    preimage_currentParityPatternCylinder_extendBoxCurrent d n F hF]
  rw [show p.toMeasure {m | restrictCurrent S m = a'} =
      (PMF.map (restrictCurrent S) p) a' by
    rw [← PMF.toMeasure_apply_singleton _ a' (MeasurableSet.singleton a')]
    rw [PMF.toMeasure_map_apply]
    · rfl
    · exact Measurable.of_discrete
    · exact MeasurableSet.singleton a']
  rw [hpoint, hparity, hkernel']
  congr 1
  rw [show p.toMeasure {m | currentLocalParity (restrictCurrent S m) =
        pullbackParityPattern d n F hF (currentLocalParity a)} =
      (PMF.map currentLocalParity (PMF.map (restrictCurrent S) p))
        (pullbackParityPattern d n F hF (currentLocalParity a)) by
    let odd := pullbackParityPattern d n F hF (currentLocalParity a)
    rw [← PMF.toMeasure_apply_singleton _ odd (MeasurableSet.singleton odd)]
    rw [PMF.toMeasure_map_apply currentLocalParity
      (PMF.map (restrictCurrent S) p) {odd}
      Measurable.of_discrete (MeasurableSet.singleton odd)]
    rw [PMF.toMeasure_map_apply (restrictCurrent S) p
      (currentLocalParity ⁻¹' {odd})
      Measurable.of_discrete MeasurableSet.of_discrete]
    rfl]
  rw [boundaryCurrentLocalParityPMF G beta hbeta interior S]

theorem freeBoxCurrentMeasure_pattern_factor
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d))) (hF : F ⊆ bondFinsetTouch d n)
    (a : ↑F → ℕ) :
    (freeBoxCurrentMeasure d (n + 1) beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentCylinder F {a}) =
      (freeBoxCurrentMeasure d (n + 1) beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityPatternCylinder F (currentLocalParity a)) *
        finiteParityPMF F beta hbeta (currentLocalParity a) a := by
  let G := StatMech.FK.boxGraph d (n + 1)
  let S := boxPullbackEdgeSubtypes d n F
  let p := sourcelessCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => zero_le_one)
  let q := PMF.map (restrictParity G S) (freeParityPMF G beta hbeta.le)
  let a' := pullbackCurrentPattern d n F hF a
  have hcurrent : PMF.map (restrictCurrent S) p =
      q.bind (finiteParityPMF S beta hbeta) := by
    exact sourcelessCurrentFiniteMarginal_eq_localParity_bind
      G beta hbeta S
  have hpoint := congrArg (fun r : PMF (↑S → ℕ) => r a') hcurrent
  change (PMF.map (restrictCurrent S) p) a' =
    q.bind (finiteParityPMF S beta hbeta) a' at hpoint
  rw [bind_finiteParityPMF_apply] at hpoint
  have hparity : currentLocalParity a' =
      pullbackParityPattern d n F hF (currentLocalParity a) := by
    rfl
  have hkernel : finiteParityPMF S beta hbeta
      (currentLocalParity a') a' =
      finiteParityPMF F beta hbeta (currentLocalParity a) a := by
    rw [finiteParityPMF_apply, finiteParityPMF_apply,
      finiteParityKernel_pullbackCurrentPattern]
  have hkernel' : finiteParityPMF S beta hbeta
      (pullbackParityPattern d n F hF (currentLocalParity a)) a' =
      finiteParityPMF F beta hbeta (currentLocalParity a) a := by
    rw [← hparity]
    exact hkernel
  have hsingle : MeasurableSet (currentCylinder F {a}) :=
    measurableSet_currentCylinder F {a}
  have hparMeas : MeasurableSet
      (currentParityPatternCylinder F (currentLocalParity a)) :=
    measurableSet_currentCylinder F _
  change Measure.map (extendBoxCurrent d (n + 1)) p.toMeasure
      (currentCylinder F {a}) =
    Measure.map (extendBoxCurrent d (n + 1)) p.toMeasure
      (currentParityPatternCylinder F (currentLocalParity a)) * _
  rw [Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hsingle,
    preimage_currentCylinder_singleton_extendBoxCurrent d n F hF a,
    Measure.map_apply (measurable_extendBoxCurrent d (n + 1)) hparMeas,
    preimage_currentParityPatternCylinder_extendBoxCurrent d n F hF]
  rw [show p.toMeasure {m | restrictCurrent S m = a'} =
      (PMF.map (restrictCurrent S) p) a' by
    rw [← PMF.toMeasure_apply_singleton _ a' (MeasurableSet.singleton a')]
    rw [PMF.toMeasure_map_apply]
    · rfl
    · exact Measurable.of_discrete
    · exact MeasurableSet.singleton a']
  rw [hpoint, hparity, hkernel']
  congr 1
  rw [show p.toMeasure {m | currentLocalParity (restrictCurrent S m) =
        pullbackParityPattern d n F hF (currentLocalParity a)} =
      (PMF.map currentLocalParity (PMF.map (restrictCurrent S) p))
        (pullbackParityPattern d n F hF (currentLocalParity a)) by
    let odd := pullbackParityPattern d n F hF (currentLocalParity a)
    rw [← PMF.toMeasure_apply_singleton _ odd (MeasurableSet.singleton odd)]
    rw [PMF.toMeasure_map_apply currentLocalParity
      (PMF.map (restrictCurrent S) p) {odd}
      Measurable.of_discrete (MeasurableSet.singleton odd)]
    rw [PMF.toMeasure_map_apply (restrictCurrent S) p
      (currentLocalParity ⁻¹' {odd})
      Measurable.of_discrete MeasurableSet.of_discrete]
    rfl]
  rw [sourcelessCurrentLocalParityPMF G beta hbeta S]

end StatMech.FrontierB
