/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.GeneralInteractionCurrentLimits
import Code.FrontierB.InhomogeneousFiniteVolumeRelabel
import Code.Lattice.UniqueInfiniteComponent










open Filter Topology Set
open scoped BigOperators
open Finset

namespace StatMech.FrontierB

open StatMech.Ising StatMech.Sharpness StatMech.Lattice


def interactionBoxVertexIncl (d : Nat) {n m : Nat} (hnm : n ≤ m) :
    interactionBoxVertices d n ↪ interactionBoxVertices d m where
  toFun x := ⟨x.1, mem_interactionBoxVertices.mpr
    (box_mono d hnm (mem_interactionBoxVertices.mp x.2))⟩
  inj' _ _ h := by
    apply Subtype.ext
    exact congrArg (fun y : interactionBoxVertices d m => y.1) h



def interactionBoxPredEquiv (d : Nat) {n m : Nat} (hnm : n ≤ m) :
    interactionBoxVertices d n ≃
      {x : interactionBoxVertices d m // x.1 ∈ box d n} where
  toFun x :=
    ⟨⟨x.1, mem_interactionBoxVertices.mpr
      (box_mono d hnm (mem_interactionBoxVertices.mp x.2))⟩,
      mem_interactionBoxVertices.mp x.2⟩
  invFun x := ⟨x.1.1, mem_interactionBoxVertices.mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem interactionBoxPredEquiv_val (d : Nat) {n m : Nat}
    (hnm : n ≤ m) (x : interactionBoxVertices d n) :
    (interactionBoxPredEquiv d hnm x).1.1 = x.1 := rfl

private theorem interactionBoxGraph_edge_nonDiag (d n : Nat)
    (e : Sym2 (interactionBoxVertices d n))
    (he : e ∈ (interactionBoxGraph d n).edgeFinset) : ¬e.IsDiag := by
  exact (interactionBoxGraph d n).not_isDiag_of_mem_edgeFinset he

private theorem interactionBox_induced_edges_subset (d : Nat) {n m : Nat}
    (hnm : n ≤ m) :
    sym2FinsetImage
        (StatMech.FK.agl_sumEquiv
          (fun x : interactionBoxVertices d m => x.1 ∈ box d n))
        (sym2FinsetInl
          (sym2FinsetImage (interactionBoxPredEquiv d hnm)
            (interactionBoxGraph d n).edgeFinset) :
          Finset (Sym2
            ({x : interactionBoxVertices d m // x.1 ∈ box d n} ⊕
             {x : interactionBoxVertices d m // x.1 ∉ box d n}))) ⊆
      (interactionBoxGraph d m).edgeFinset := by
  intro e he
  unfold sym2FinsetImage sym2FinsetInl at he
  simp only [Finset.mem_image] at he
  obtain ⟨eSum, heSum, rfl⟩ := he
  obtain ⟨ePred, hePred, rfl⟩ := heSum
  obtain ⟨eSmall, heSmall, rfl⟩ := hePred
  have hnonDiag : ¬(Sym2.map
      (StatMech.FK.agl_sumEquiv
        (fun x : interactionBoxVertices d m => x.1 ∈ box d n))
      (Sym2.map Sum.inl
        (Sym2.map (interactionBoxPredEquiv d hnm) eSmall))).IsDiag := by
    rw [Sym2.isDiag_map
      (StatMech.FK.agl_sumEquiv
        (fun x : interactionBoxVertices d m => x.1 ∈ box d n)).injective]
    rw [Sym2.isDiag_map Sum.inl_injective]
    rw [Sym2.isDiag_map (interactionBoxPredEquiv d hnm).injective]
    exact interactionBoxGraph_edge_nonDiag d n eSmall heSmall
  rw [SimpleGraph.mem_edgeFinset]
  simpa [interactionBoxGraph] using hnonDiag



theorem generalInteractionBox_spinProd_mono {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta) {n m : Nat} (hnm : n ≤ m)
    (A : Finset (interactionBoxVertices d n)) :
    expJ (interactionBoxGraph d n).edgeFinset
        (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
        (spinProd A) ≤
      expJ (interactionBoxGraph d m).edgeFinset
        (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0)
        (spinProd (A.map (interactionBoxVertexIncl d hnm))) := by
  let P : interactionBoxVertices d m → Prop :=
    fun x => x.1 ∈ box d n
  let sigma : interactionBoxVertices d n ≃ {x // P x} :=
    interactionBoxPredEquiv d hnm
  let E : Finset (Sym2 {x // P x}) :=
    sym2FinsetImage sigma (interactionBoxGraph d n).edgeFinset
  let Jm : Sym2 (interactionBoxVertices d m) → ℝ :=
    fun e => beta * interactionBoxCoupling J m e
  let AP : Finset {x // P x} := A.map sigma.toEmbedding
  have hsmall :
      expJ (interactionBoxGraph d n).edgeFinset
          (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
          (spinProd A) =
        expJ E (fun e => Jm (Sym2.map Subtype.val e)) (fun _ => 0)
          (spinProd AP) := by
    have hcouple :
        (fun e => beta * interactionBoxCoupling J n e) =
          (fun e => Jm (Sym2.map Subtype.val (Sym2.map sigma e))) := by
      funext e
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp [Jm, interactionBoxCoupling, sigma,
            interactionBoxPredEquiv]
    rw [hcouple]
    exact expJ_spinProd_sym2FinsetImage_relabel sigma
      (interactionBoxGraph d n).edgeFinset
      (fun e => Jm (Sym2.map Subtype.val e)) (fun _ => 0) A
  rw [hsmall]
  have hmono := expJ_spinProd_induce_le P E
    (interactionBoxGraph d m).edgeFinset Jm
    (by
      simpa only [P, E, sigma] using
        interactionBox_induced_edges_subset d hnm)
    (by
      intro e he
      exact mul_nonneg hbeta (hJ (Sym2.map Subtype.val e)))
    (fun e he => (interactionBoxGraph d m).not_isDiag_of_mem_edgeFinset he)
    AP
  have hsupport :
      AP.map (Function.Embedding.subtype P) =
        A.map (interactionBoxVertexIncl d hnm) := by
    rw [Finset.map_map]
    apply congrArg (fun f : interactionBoxVertices d n ↪
      interactionBoxVertices d m => A.map f)
    apply Function.Embedding.ext
    intro x
    apply Subtype.ext
    rfl
  simpa only [Jm, P, E, AP, hsupport] using hmono



noncomputable def interactionBoxSpinSupport (d n : Nat)
    (A : Finset (Site d)) : Finset (interactionBoxVertices d n) :=
  Finset.univ.filter fun x => x.1 ∈ A

theorem interactionBoxSpinSupport_map_inclusion (d : Nat) {n m : Nat}
    (hnm : n ≤ m) (A : Finset (Site d)) (hA : (A : Set (Site d)) ⊆ box d n) :
    (interactionBoxSpinSupport d n A).map
        (interactionBoxVertexIncl d hnm) =
      interactionBoxSpinSupport d m A := by
  ext x
  simp only [Finset.mem_map, interactionBoxSpinSupport,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    let y : interactionBoxVertices d n :=
      ⟨x.1, mem_interactionBoxVertices.mpr (hA hx)⟩
    refine ⟨y, ?_, ?_⟩
    · exact hx
    · apply Subtype.ext
      rfl


theorem expJ_spinProd_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (K : Sym2 V → ℝ) (hf : V → ℝ)
    (A : Finset V) : expJ E K hf (spinProd A) ≤ 1 := by
  unfold expJ
  apply (div_le_one (ZJ_pos E K hf)).2
  unfold ZJ
  apply Finset.sum_le_sum
  intro s hs
  simpa using mul_le_mul_of_nonneg_right (spinProd_le_one A s)
    (wJ_nonneg E K hf s)


theorem generalInteractionBox_fixed_spinProd_mono {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta) {n m : Nat} (hnm : n ≤ m)
    (A : Finset (Site d)) (hA : (A : Set (Site d)) ⊆ box d n) :
    expJ (interactionBoxGraph d n).edgeFinset
        (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
        (spinProd (interactionBoxSpinSupport d n A)) ≤
      expJ (interactionBoxGraph d m).edgeFinset
        (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0)
        (spinProd (interactionBoxSpinSupport d m A)) := by
  rw [← interactionBoxSpinSupport_map_inclusion d hnm A hA]
  exact generalInteractionBox_spinProd_mono J hJ beta hbeta hnm
    (interactionBoxSpinSupport d n A)



theorem generalInteractionBox_spinProd_tendsto {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta) (A : Finset (Site d)) :
    ∃ L : ℝ, Tendsto
      (fun n =>
        expJ (interactionBoxGraph d n).edgeFinset
          (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
          (spinProd (interactionBoxSpinSupport d n A)))
      atTop (nhds L) := by
  let a : Nat → ℝ := fun n =>
    expJ (interactionBoxGraph d n).edgeFinset
      (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
      (spinProd (interactionBoxSpinSupport d n A))
  obtain ⟨N, hAN⟩ := finite_subset_box (A : Set (Site d)) A.finite_toSet
  have hA_add (k : Nat) : (A : Set (Site d)) ⊆ box d (k + N) :=
    hAN.trans (box_mono d (Nat.le_add_left N k))
  have htail_mono : Monotone (fun k => a (k + N)) := by
    intro k l hkl
    exact generalInteractionBox_fixed_spinProd_mono J hJ beta hbeta
      (Nat.add_le_add_right hkl N) A (hA_add k)
  have htail_bdd : BddAbove (Set.range (fun k => a (k + N))) := by
    refine ⟨1, ?_⟩
    rintro y ⟨k, rfl⟩
    exact expJ_spinProd_le_one (interactionBoxGraph d (k + N)).edgeFinset
      (fun e => beta * interactionBoxCoupling J (k + N) e) (fun _ => 0)
      (interactionBoxSpinSupport d (k + N) A)
  let L : ℝ := ⨆ k, a (k + N)
  have htail : Tendsto (fun k => a (k + N)) atTop (nhds L) := by
    simpa only [L] using tendsto_atTop_ciSup htail_mono htail_bdd
  refine ⟨L, ?_⟩
  exact (tendsto_add_atTop_iff_nat N).1 htail

end StatMech.FrontierB
