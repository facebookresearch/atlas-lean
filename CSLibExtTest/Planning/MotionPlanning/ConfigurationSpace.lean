/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Planning.MotionPlanning.ConfigurationSpace
import Mathlib.Topology.Path
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UnitInterval
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace CSLibExtTest.Planning.MotionPlanning

open Cslib.Planning.MotionPlanning

open scoped unitInterval

local instance : Fact (Module.finrank ℝ plane = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

def unitSquare : Set plane :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

theorem T1 : ((0 : plane), (0 : Real.Angle)) ∈
    cObs _ _ (planarPlacement _ planeOrientation unitSquare) {(0 : plane)} := by
  rw [mem_cObs_planarPlacement]
  refine ⟨0, fun i => ?_, ?_⟩
  · show (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1
    exact ⟨le_rfl, zero_le_one⟩
  · simp

theorem T2 : ((EuclideanSpace.single (0 : Fin 2) (2 : ℝ) : plane),
    (0 : Real.Angle)) ∈
    cFree _ _ (planarPlacement _ planeOrientation unitSquare) {(0 : plane)} := by
  rw [mem_cFree, Set.eq_empty_iff_forall_notMem]
  intro y hy
  obtain ⟨⟨a, ha, rfl⟩, hy0⟩ := hy
  rw [Set.mem_singleton_iff] at hy0
  have hcongr := congrArg (fun x : plane => x 0) hy0
  simp at hcongr
  have ha0 := (ha 0).1
  linarith [hcongr, ha0]

theorem T3 (qI qG : plane × Real.Angle) :
    (⟨cFree _ _ (planarPlacement _ planeOrientation unitSquare) ∅, qI, qG,
      by simp [cFree_empty], by simp [cFree_empty]⟩ :
      PathProblem (plane × Real.Angle)).Solvable := by
  rw [PathProblem.solvable_iff_joinedIn]
  show JoinedIn (cFree (plane × Real.Angle) plane
    (planarPlacement plane planeOrientation unitSquare) ∅) qI qG
  rw [cFree_empty]
  have : PathConnectedSpace (plane × Real.Angle) := pathConnectedSpace_planar plane
  obtain ⟨γ⟩ := PathConnectedSpace.joined qI qG
  exact ⟨γ, fun t => Set.mem_univ _⟩

theorem pointRobot_free : cFree ℝ ℝ (fun q => {q}) {(0 : ℝ)} = {0}ᶜ := by
  ext q
  simp only [mem_cFree, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro h heq
    subst heq
    rw [Set.inter_self, Set.eq_empty_iff_forall_notMem] at h
    exact h 0 (Set.mem_singleton_iff.mpr rfl)
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [Set.mem_singleton_iff] at hy1 hy2
    exact h (hy1.symm.trans hy2)

theorem T4 :
    ¬ (⟨cFree ℝ ℝ (fun q => {q}) {(0 : ℝ)}, -1, 1,
      by rw [pointRobot_free]; simp, by rw [pointRobot_free]; simp⟩ :
      PathProblem ℝ).Solvable := by
  intro hsolv
  rw [PathProblem.solvable_iff_joinedIn] at hsolv
  have hcore : JoinedIn (cFree ℝ ℝ (fun q => {q}) {(0 : ℝ)}) (-1) 1 := hsolv
  rw [pointRobot_free] at hcore
  obtain ⟨γ, hγ⟩ := hcore
  have himg := (isPreconnected_univ : IsPreconnected (Set.univ : Set I)).image _
    γ.continuous.continuousOn
  rw [Set.image_univ] at himg
  have hord := himg.ordConnected
  have hsub := hord.out (show (-1 : ℝ) ∈ Set.range ⇑γ from ⟨0, γ.source⟩)
    (show (1 : ℝ) ∈ Set.range ⇑γ from ⟨1, γ.target⟩)
  obtain ⟨t, ht⟩ := hsub (show (0 : ℝ) ∈ Set.Icc (-1) 1 by norm_num [Set.mem_Icc])
  exact hγ t (Set.mem_singleton_iff.mpr ht)

theorem T5 :
    ((((0 : plane), (0 : Real.Angle)) ∈
        cObs _ _ (planarPlacement _ planeOrientation unitSquare) {(0 : plane)}) ↔
      ∃ a ∈ unitSquare, planeOrientation.rotation 0 a + (0 : plane) ∈ ({(0 : plane)} : Set plane)) ∧
    ((((EuclideanSpace.single (0 : Fin 2) (2 : ℝ) : plane), (0 : Real.Angle)) ∈
        cObs _ _ (planarPlacement _ planeOrientation unitSquare) {(0 : plane)}) ↔
      ∃ a ∈ unitSquare, planeOrientation.rotation 0 a +
        (EuclideanSpace.single (0 : Fin 2) (2 : ℝ) : plane) ∈ ({(0 : plane)} : Set plane)) :=
  ⟨mem_cObs_planarPlacement _ _ _ _ _ _, mem_cObs_planarPlacement _ _ _ _ _ _⟩

#print axioms PathProblem.solvable_iff_joinedIn
#print axioms mem_cObs_planarPlacement
#print axioms pathConnectedSpace_planar

end CSLibExtTest.Planning.MotionPlanning
