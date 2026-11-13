/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCaratheodoryApproximation










open Filter Metric Set Topology

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section


def reflectComplexSet (S : Set Complex) : Set Complex :=
  (starRingEnd Complex) '' S

@[simp] theorem mem_reflectComplexSet {S : Set Complex} {z : Complex} :
    z ∈ reflectComplexSet S ↔ (starRingEnd Complex) z ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨(starRingEnd Complex) z, hz, by simp⟩

theorem reflectComplexSet_isOpen {S : Set Complex} (hS : IsOpen S) :
    IsOpen (reflectComplexSet S) := by
  simpa [reflectComplexSet, Complex.conjCLE_apply] using
    Complex.conjCLE.toHomeomorph.isOpenMap S hS

theorem reflectComplexSet_isPreconnected {S : Set Complex}
    (hS : IsPreconnected S) : IsPreconnected (reflectComplexSet S) := by
  exact hS.image (starRingEnd Complex) Complex.continuous_conj.continuousOn

theorem reflectComplexSet_isCompact {S : Set Complex} (hS : IsCompact S) :
    IsCompact (reflectComplexSet S) :=
  hS.image Complex.continuous_conj

@[simp] theorem reflectComplexSet_reflectComplexSet (S : Set Complex) :
    reflectComplexSet (reflectComplexSet S) = S := by
  ext z
  simp



theorem tendstoLocallyUniformlyOn_reflect_iff
    {ι : Type*} {p : Filter ι} {F : ι → Complex → Complex}
    {f : Complex → Complex} {S : Set Complex} :
    TendstoLocallyUniformlyOn
        (fun n z ↦ F n ((starRingEnd Complex) z))
        (fun z ↦ f ((starRingEnd Complex) z)) p (reflectComplexSet S) ↔
      TendstoLocallyUniformlyOn F f p S := by
  constructor
  · intro h
    have hcomp := h.comp (starRingEnd Complex)
      (fun _ hz ↦ mem_reflectComplexSet.mpr (by simpa using hz))
      Complex.continuous_conj.continuousOn
    simpa [Function.comp_def] using hcomp
  · intro h
    have hcomp := h.comp (starRingEnd Complex)
      (fun _ hz ↦ mem_reflectComplexSet.mp hz)
      Complex.continuous_conj.continuousOn
    simpa [Function.comp_def] using hcomp

theorem closure_reflectComplexSet (S : Set Complex) :
    closure (reflectComplexSet S) = reflectComplexSet (closure S) := by
  simpa [reflectComplexSet, Complex.conjCLE_apply] using
    (Complex.conjCLE.toHomeomorph.image_closure S).symm



def FKIsingDobrushinDomain.reflect
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M) : FKIsingDobrushinDomain P M where
  wiredArc := D.wiredArc
  markedA := D.markedA
  markedB := D.markedB
  markedA_mem := D.markedA_mem
  markedB_mem := D.markedB_mem
  sourceEdge := D.sourceEdge
  terminalEdge := D.terminalEdge
  medialPosition := fun e ↦ (starRingEnd Complex) (D.medialPosition e)
  exploration := D.exploration
  source_mem := D.source_mem
  terminal_mem := D.terminal_mem
  winding := D.winding
  winding_terminal := D.winding_terminal

@[simp] theorem FKIsingDobrushinDomain.reflect_medialPosition
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M) (e : M) :
    D.reflect.medialPosition e =
      (starRingEnd Complex) (D.medialPosition e) := rfl

@[simp] theorem FKIsingDobrushinDomain.reflect_fermionicObservable
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M) (e : M) :
    D.reflect.fermionicObservable e = D.fermionicObservable e := rfl

@[simp] theorem FKIsingDobrushinDomain.reflect_normalizedFermionicObservable
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M) (mesh : Real) (e : M) :
    D.reflect.normalizedFermionicObservable mesh e =
      D.normalizedFermionicObservable mesh e := rfl

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)




noncomputable def reflect : FKIsingCaratheodoryApproximation where
  U := reflectComplexSet A.U
  root := (starRingEnd Complex) A.root
  root_mem := by simp [A.root_mem]
  isOpen := reflectComplexSet_isOpen A.isOpen
  isPreconnected := reflectComplexSet_isPreconnected A.isPreconnected
  carrier := fun n ↦ reflectComplexSet (A.carrier n)
  mesh := A.mesh
  mesh_pos := A.mesh_pos
  mesh_tendsto_zero := A.mesh_tendsto_zero
  compact_eventually_mem := by
    intro K hK hKU
    have hreflectK : IsCompact (reflectComplexSet K) :=
      reflectComplexSet_isCompact hK
    have hreflectKU : reflectComplexSet K ⊆ A.U := by
      intro z hz
      rw [mem_reflectComplexSet] at hz
      have := hKU hz
      simpa using (mem_reflectComplexSet.mp this)
    filter_upwards [A.compact_eventually_mem
      (reflectComplexSet K) hreflectK hreflectKU] with n hn
    intro z hz
    rw [mem_reflectComplexSet]
    exact hn (mem_reflectComplexSet.mpr (by simpa using hz))
  exterior_eventually_avoided := by
    intro z hz
    have hz' : (starRingEnd Complex) z ∉ closure A.U := by
      intro h
      apply hz
      rw [closure_reflectComplexSet]
      simp [h]
    obtain ⟨r, hr, havoid⟩ :=
      A.exterior_eventually_avoided ((starRingEnd Complex) z) hz'
    refine ⟨r, hr, ?_⟩
    filter_upwards [havoid] with n hn
    rw [Set.disjoint_left]
    intro w hwBall hwCarrier
    rw [mem_reflectComplexSet] at hwCarrier
    have hconjBall : (starRingEnd Complex) w ∈
        ball ((starRingEnd Complex) z) r := by
      simpa [mem_ball, Complex.dist_conj_conj] using hwBall
    exact Set.disjoint_left.1 hn hconjBall hwCarrier
  P := A.P
  M := A.M
  fintypeM := A.fintypeM
  decEqM := A.decEqM
  dobrushin := fun n ↦
    @FKIsingDobrushinDomain.reflect (A.P n) (A.M n)
      (A.fintypeM n) (A.decEqM n) (A.dobrushin n)
  vertexEmbedding := fun n v ↦ (starRingEnd Complex) (A.vertexEmbedding n v)
  medialEmbedding := fun n e ↦ (starRingEnd Complex) (A.medialEmbedding n e)
  vertex_mem_carrier := by
    intro n v
    simp [A.vertex_mem_carrier n v]
  medial_mem_carrier := by
    intro n e
    simp [A.medial_mem_carrier n e]
  carrier_near_medial := by
    intro n z hz
    rw [mem_reflectComplexSet] at hz
    obtain ⟨e, he⟩ :=
      A.carrier_near_medial n ((starRingEnd Complex) z) hz
    refine ⟨e, ?_⟩
    calc
      dist z ((starRingEnd Complex) (A.medialEmbedding n e)) =
          dist ((starRingEnd Complex) z) (A.medialEmbedding n e) := by
        simpa using
          (Complex.dist_conj_comm z (A.medialEmbedding n e)).symm
      _ ≤ A.mesh n := he
  medialEmbedding_eq_position := by
    intro n e
    simp only [FKIsingDobrushinDomain.reflect_medialPosition]
    exact congrArg (starRingEnd Complex) (A.medialEmbedding_eq_position n e)
  rawInterpolant := fun n z ↦ A.rawInterpolant n ((starRingEnd Complex) z)
  rawInterpolant_medial := by
    intro n e
    simpa using A.rawInterpolant_medial n e

@[simp] theorem reflect_U : A.reflect.U = reflectComplexSet A.U := rfl

@[simp] theorem reflect_root :
    A.reflect.root = (starRingEnd Complex) A.root := rfl

@[simp] theorem reflect_carrier (n : Nat) :
    A.reflect.carrier n = reflectComplexSet (A.carrier n) := rfl

@[simp] theorem reflect_mesh (n : Nat) : A.reflect.mesh n = A.mesh n := rfl

@[simp] theorem reflect_medialEmbedding (n : Nat) (e : A.M n) :
    A.reflect.medialEmbedding n e =
      (starRingEnd Complex) (A.medialEmbedding n e) := rfl

@[simp] theorem reflect_rawInterpolant (n : Nat) (z : Complex) :
    A.reflect.rawInterpolant n z =
      A.rawInterpolant n ((starRingEnd Complex) z) := rfl

@[simp] theorem reflect_normalizedInterpolant (n : Nat) (z : Complex) :
    A.reflect.normalizedInterpolant n z =
      A.normalizedInterpolant n ((starRingEnd Complex) z) := rfl

end FKIsingCaratheodoryApproximation

end

end StatMech.Universality
