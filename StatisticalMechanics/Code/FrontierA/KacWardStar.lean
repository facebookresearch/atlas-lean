/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Mathlib
import Code.Ising.EvenSubgraphDecomp
import Code.Lattice.JordanVeblenPeel

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Ising




noncomputable def kwEvenPolynomial {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V -> ℂ) : ℂ :=
  ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, ∏ e ∈ F, x e



theorem kwEvenPolynomial_eq_one_of_isAcyclic {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (x : Sym2 V -> ℂ) : kwEvenPolynomial G x = 1 := by
  have hfilter : G.edgeFinset.powerset.filter IsEvenSubgraph = {∅} := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨hFsub, hFeven⟩
      rw [<- Finset.not_nonempty_iff_eq_empty]
      rintro ⟨e, he⟩
      have hnoDiag : ∀ e ∈ F, ¬ e.IsDiag := by
        intro edge hedge
        exact evenSubgraphs_no_diag (Gd := G) (F := F) hFsub edge hedge
      have hle : subgraphF F ≤ G := subgraphF_le_of_subset (Gd := G) (F := F) hFsub
      have hac : (subgraphF F).IsAcyclic := hG.anti hle
      have hne : (subgraphF F).edgeSet.Nonempty :=
        ⟨e, (mem_edgeSet_subgraphF F hnoDiag e).mpr he⟩
      exact (Lattice.jvp_not_isAcyclic_of_even_nonempty (subgraphF F)
        (subgraphF_even F hnoDiag hFeven) hne) hac
    · rintro rfl
      simp [IsEvenSubgraph, incCount]
  unfold kwEvenPolynomial
  rw [hfilter]
  simp




def kwStarGraph (ι : Type*) : SimpleGraph (Unit ⊕ ι) :=
  completeBipartiteGraph Unit ι

noncomputable instance kwStarGraph_decidableAdj {ι : Type*} :
    DecidableRel (kwStarGraph ι).Adj := Classical.decRel _


theorem kwStarGraph_isAcyclic (ι : Type) : (kwStarGraph ι).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_edge_isBridge]
  intro e he
  rw [kwStarGraph, SimpleGraph.edgeSet_completeBipartiteGraph] at he
  obtain ⟨p, rfl⟩ := he
  rcases p with ⟨centre, leaf⟩
  letI : Nonempty ι := ⟨leaf⟩
  letI : Nontrivial (Unit ⊕ ι) :=
    ⟨⟨Sum.inl Unit.unit, Sum.inr leaf, by simp⟩⟩
  rw [SimpleGraph.isBridge_iff]
  refine ⟨by simp [kwStarGraph], ?_⟩
  apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty (by simp)
  ext v
  rcases v with centre' | other
  · have hc : centre' = centre := Subsingleton.elim _ _
    subst centre'
    simp [kwStarGraph, SimpleGraph.deleteEdges_adj]
  · simp [kwStarGraph, SimpleGraph.deleteEdges_adj]



abbrev kwStarDart (ι : Type*) := ι × Bool


def kwStarDartTail {ι : Type*} : kwStarDart ι -> Unit ⊕ ι
  | (leaf, false) => Sum.inr leaf
  | (_, true) => Sum.inl Unit.unit


def kwStarDartHead {ι : Type*} : kwStarDart ι -> Unit ⊕ ι
  | (_, false) => Sum.inl Unit.unit
  | (leaf, true) => Sum.inr leaf


theorem kwStarDart_adj {ι : Type*} (d : kwStarDart ι) :
    (kwStarGraph ι).Adj (kwStarDartTail d) (kwStarDartHead d) := by
  rcases d with ⟨leaf, direction⟩
  cases direction <;> simp [kwStarGraph, kwStarDartTail, kwStarDartHead]


def kwStarDartEdge {ι : Type*} (d : kwStarDart ι) : Sym2 (Unit ⊕ ι) :=
  s(kwStarDartTail d, kwStarDartHead d)








noncomputable def kwStarTransition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Sym2 (Unit ⊕ ι) -> ℂ)
    (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
    Matrix (kwStarDart ι) (kwStarDart ι) ℂ :=
  fun d2 d1 =>
    if d1.2 = false ∧ d2.2 = true ∧ d1.1 ≠ d2.1 then
      x (kwStarDartEdge d1) * phase d1 d2
    else 0



theorem kwStarTransition_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : Sym2 (Unit ⊕ ι) -> ℂ}
    {phase : kwStarDart ι -> kwStarDart ι -> ℂ}
    {d1 d2 : kwStarDart ι} (h : kwStarTransition x phase d2 d1 ≠ 0) :
    kwStarDartHead d1 = kwStarDartTail d2 ∧
      kwStarDartHead d2 ≠ kwStarDartTail d1 := by
  by_contra hbad
  rcases d1 with ⟨leaf1, direction1⟩
  rcases d2 with ⟨leaf2, direction2⟩
  cases direction1 <;> cases direction2
  all_goals simp [kwStarTransition, kwStarDartHead, kwStarDartTail] at h hbad
  grind


theorem kwStarTransition_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Sym2 (Unit ⊕ ι) -> ℂ)
    (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
    kwStarTransition x phase ^ 2 = 0 := by
  rw [pow_two]
  ext d2 d1
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  cases hdirection : d.2 <;> simp [kwStarTransition, hdirection]


theorem kwStarTransition_isNilpotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Sym2 (Unit ⊕ ι) -> ℂ)
    (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
    IsNilpotent (kwStarTransition x phase) :=
  ⟨2, kwStarTransition_sq x phase⟩




theorem det_one_sub_eq_one_of_isNilpotent {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι ℂ) (hM : IsNilpotent M) :
    (1 - M).det = 1 := by
  have hpow : ∀ n : ℕ, (M ^ n).toLin' = M.toLin' ^ n := by
    intro n
    induction n with
    | zero => simp [Matrix.toLin'_one, Module.End.one_eq_id]
    | succ n ih =>
        rw [pow_succ, Matrix.toLin'_mul, ih, pow_succ, Module.End.mul_eq_comp]
  have hlin : IsNilpotent M.toLin' := by
    obtain ⟨n, hn⟩ := hM
    refine ⟨n, ?_⟩
    rw [<- hpow, hn]
    ext
    simp
  have hchar := hlin.charpoly_eq_X_pow_finrank
  rw [Matrix.charpoly_toLin'] at hchar
  have heval := Matrix.eval_charpoly M 1
  rw [hchar] at heval
  simpa using heval.symm



theorem kwStarTransition_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Sym2 (Unit ⊕ ι) -> ℂ)
    (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
    (1 - kwStarTransition x phase).det = 1 :=
  det_one_sub_eq_one_of_isNilpotent _ (kwStarTransition_isNilpotent x phase)




theorem kacWard_star {ι : Type} [Fintype ι] [DecidableEq ι]
    (x : Sym2 (Unit ⊕ ι) -> ℂ)
    (phase : kwStarDart ι -> kwStarDart ι -> ℂ) :
    (1 - kwStarTransition x phase).det = (kwEvenPolynomial (kwStarGraph ι) x) ^ 2 := by
  have hpoly : kwEvenPolynomial (kwStarGraph ι) x = 1 :=
    kwEvenPolynomial_eq_one_of_isAcyclic (kwStarGraph ι) (kwStarGraph_isAcyclic ι) x
  rw [kwStarTransition_det, hpoly]
  norm_num

end StatMech.FrontierA
