/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.KacWardStar
import Code.Onsager.TracePowWalk

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Onsager





noncomputable def kwGraphTransition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ) :
    Matrix G.Dart G.Dart ℂ :=
  fun d e =>
    if d.snd = e.fst ∧ d.edge ≠ e.edge then x d.edge * phase d e else 0



theorem kwGraphTransition_support {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {x : Sym2 V -> ℂ} {phase : G.Dart -> G.Dart -> ℂ}
    {d e : G.Dart} (h : kwGraphTransition G x phase d e ≠ 0) :
    G.DartAdj d e ∧ d.edge ≠ e.edge := by
  change d.snd = e.fst ∧ d.edge ≠ e.edge
  by_contra hstep
  simp [kwGraphTransition, hstep] at h



theorem kwForest_no_long_dart_chain {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic)
    (q : Fin (Fintype.card V + 1) -> G.Dart)
    (hadj : ∀ k : Fin (Fintype.card V),
      G.DartAdj (q k.castSucc) (q k.succ))
    (hnb : ∀ k : Fin (Fintype.card V),
      (q k.castSucc).edge ≠ (q k.succ).edge) : False := by
  let l : List G.Dart := List.ofFn q
  have hchain : l.IsChain G.DartAdj := by
    change (List.ofFn q).IsChain G.DartAdj
    rw [List.isChain_ofFn]
    intro i hi
    let k : Fin (Fintype.card V) := ⟨i, by omega⟩
    simpa [k] using hadj k
  have hchainEdges : (l.map Dart.edge).IsChain (· ≠ ·) := by
    rw [List.isChain_map]
    change (List.ofFn q).IsChain (fun a b => a.edge ≠ b.edge)
    rw [List.isChain_ofFn]
    intro i hi
    let k : Fin (Fintype.card V) := ⟨i, by omega⟩
    simpa [k] using hnb k
  have hl : l ≠ [] := by simp [l]
  let w := Walk.ofDarts l hl hchain
  have hwEdges : w.edges.IsChain (· ≠ ·) := by
    simpa [w] using hchainEdges
  have hwPath : w.IsPath := (hG.isPath_iff_isChain w).2 hwEdges
  have hwLength : w.length = Fintype.card V + 1 := by
    simp [w, l]
  have := hwPath.length_lt
  omega



theorem kwGraphTransition_isNilpotent_of_isAcyclic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (x : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ) :
    IsNilpotent (kwGraphTransition G x phase) := by
  refine ⟨Fintype.card V, ?_⟩
  ext i j
  rw [ons_pow_apply_walk]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hend :
      (Fin.cons i p : Fin (Fintype.card V + 1) -> G.Dart)
          (Fin.last (Fintype.card V)) = j
  · simp only [hend, if_true, one_mul]
    by_contra hprod
    have hfactor : ∀ k : Fin (Fintype.card V),
        kwGraphTransition G x phase
          ((Fin.cons i p : Fin (Fintype.card V + 1) -> G.Dart) k.castSucc)
          (p k) ≠ 0 := by
      intro k
      exact Finset.prod_ne_zero_iff.mp hprod k (Finset.mem_univ k)
    let q : Fin (Fintype.card V + 1) -> G.Dart := Fin.cons i p
    have hstep : ∀ k : Fin (Fintype.card V),
        G.DartAdj (q k.castSucc) (q k.succ) ∧
          (q k.castSucc).edge ≠ (q k.succ).edge := by
      intro k
      simpa [q] using kwGraphTransition_support (hfactor k)
    exact kwForest_no_long_dart_chain G hG q
      (fun k => (hstep k).1) (fun k => (hstep k).2)
  · simp [hend]


theorem kwGraphTransition_det_of_isAcyclic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (x : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ) :
    (1 - kwGraphTransition G x phase).det = 1 :=
  det_one_sub_eq_one_of_isNilpotent _
    (kwGraphTransition_isNilpotent_of_isAcyclic G hG x phase)




theorem kacWard_forest {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (x : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ) :
    (1 - kwGraphTransition G x phase).det = (kwEvenPolynomial G x) ^ 2 := by
  rw [kwGraphTransition_det_of_isAcyclic G hG x phase,
    kwEvenPolynomial_eq_one_of_isAcyclic G hG x]
  norm_num

end StatMech.FrontierA
