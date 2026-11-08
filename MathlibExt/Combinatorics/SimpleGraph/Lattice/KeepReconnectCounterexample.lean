/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanWindingConstruct

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# The keep–reconnect residue fails for infinite graphs

The keep–reconnect residue asks that, if `p` and `q` are disconnected in `H`, the faces on both
sides of `pq` are connected in the face-region graph of `H` after deleting the dual edge. It fails
for the infinite graph made of the horizontal axis with the edge `{(0, 0), (1, 0)}` removed: that
graph separates the upper and lower half-planes. Its restriction to graphs with finitely many edges
(`jkr_FiniteKeepReconnectResidue`) is the form proved in `JordanEnclosureDuality`.

## Main definitions

* `StatMech.Lattice.jkr_lineRel`, `StatMech.Lattice.jkr_lineH`: the horizontal axis minus the edge
  `{(0, 0), (1, 0)}`.
* `StatMech.Lattice.jkr_FiniteKeepReconnectResidue`: the keep–reconnect residue for graphs with
  finitely many edges.

## Main results

* `StatMech.Lattice.jkr_lineH_not_finite`: the counterexample has infinitely many edges.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Lattice

/-- Both sites lie on the horizontal axis and the pair is not `{(0, 0), (1, 0)}`. -/
def jkr_lineRel (a b : Site 2) : Prop :=
  a 1 = 0 ∧ b 1 = 0 ∧ ¬ ({a 0, b 0} = ({0, 1} : Finset ℤ))

/-- The horizontal axis of `ℤ²` with the edge from `(0, 0)` to `(1, 0)` removed. -/
def jkr_lineH : SimpleGraph (Site 2) where
  Adj a b := (hypercubicLattice 2).Adj a b ∧ jkr_lineRel a b
  symm := by
    refine ⟨?_⟩
    rintro a b ⟨hadj, h0, h1, hne⟩
    refine ⟨hadj.symm, h1, h0, ?_⟩
    rwa [Finset.pair_comm]
  loopless := ⟨fun a h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem jkr_lineH_adj (a b : Site 2) :
    jkr_lineH.Adj a b ↔ (hypercubicLattice 2).Adj a b ∧
      a 1 = 0 ∧ b 1 = 0 ∧ ¬ ({a 0, b 0} = ({0, 1} : Finset ℤ)) := Iff.rfl

theorem jkr_pair_eq_iff (c d : ℤ) (hne : c ≠ d) :
    ({c, d} = ({0, 1} : Finset ℤ)) ↔ ((c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 0)) := by
  constructor
  · intro h
    have hc : c ∈ ({0, 1} : Finset ℤ) := by rw [← h]; simp
    have hd : d ∈ ({0, 1} : Finset ℤ) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [Finset.pair_comm]

theorem jkr_edge_on_line {a b : Site 2} (h : jkr_lineH.Adj a b) : a 1 = 0 ∧ b 1 = 0 :=
  ⟨h.2.1, h.2.2.1⟩

theorem jkr_line_seg_mem (a : ℤ) :
    s(![a, (0:ℤ)], ![a + 1, 0]) ∈ jkr_lineH.edgeSet ↔ a ≠ 0 := by
  rw [SimpleGraph.mem_edgeSet, jkr_lineH_adj]
  have hy0 : (![a, (0:ℤ)] : Site 2) 1 = 0 := rfl
  have hy1 : (![a + 1, (0:ℤ)] : Site 2) 1 = 0 := rfl
  have hx0 : (![a, (0:ℤ)] : Site 2) 0 = a := rfl
  have hx1 : (![a + 1, (0:ℤ)] : Site 2) 0 = a + 1 := rfl
  rw [hy0, hy1, hx0, hx1]
  constructor
  · rintro ⟨_, _, _, hne⟩ hzero
    subst hzero
    exact hne (by decide)
  · intro ha
    refine ⟨?_, rfl, rfl, ?_⟩
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega
    · rw [jkr_pair_eq_iff a (a + 1) (by omega)]
      push Not; omega

theorem jkr_witness_bot :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧
    ¬ (⊥ : SimpleGraph (Site 2)).Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] :=
  jwn_witness_square

theorem jkr_witness_square :
    (hypercubicLattice 2).Adj (jbc_Pce.emb jbc_v0) (jbc_Pce.emb jbc_v1) ∧
    s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) ∉ (jei_pushGraph jbc_Pce ⊥).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) ∧
    ¬ (jei_pushGraph jbc_Pce ⊥).Reachable (jbc_Pce.emb jbc_v0) (jbc_Pce.emb jbc_v1) ∧
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hna : ¬ (⊥ : SimpleGraph jbc_Pce.V).Adj jbc_v0 jbc_v1 := by
    exact (SimpleGraph.bot_adj _ _).mp
  have hpq : (hypercubicLattice 2).Adj (jbc_Pce.emb jbc_v0) (jbc_Pce.emb jbc_v1) :=
    jbc_Pce.isSub jbc_Pce_Gadj
  refine ⟨hpq, jkd_wall_not_mem_pushGraph jbc_Pce ⊥ hna,
    jbc_latadj (by rw [Fin.sum_univ_two]; norm_num), jkd_shared_bottom, ?_,
    jkd_witness_square_reach⟩
  intro h; replace h := (jei_push_reachable_iff _ _ _ _).mp h
  replace h := SimpleGraph.reachable_bot.mp h; exact jbc_v0_ne_v1 h

theorem jkr_witness_ring :
    jkd_ringP.G.Adj jkd_r0 jkd_r1 ∧
    s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∉ (jei_pushGraph jkd_ringP ⊥).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∧
    ¬ (jei_pushGraph jkd_ringP ⊥).Reachable (jkd_ringP.emb jkd_r0) (jkd_ringP.emb jkd_r1) ∧
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] :=
  jwn_witness_ring

/-- For every graph `H` of `ℤ²` with finitely many edges and every lattice edge `pq` outside `H`
with dual edge `f0g0`: if `p` and `q` are disconnected in `H`, then `f0` and `g0` are
connected in the face-region graph of `H` with `f0g0` deleted. -/
def jkr_FiniteKeepReconnectResidue : Prop :=
  ∀ (H : SimpleGraph (Site 2)) (p q f0 g0 : Site 2),
    H.edgeSet.Finite →
    (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet →
    (hypercubicLattice 2).Adj f0 g0 → sharedPrimalEdge f0 g0 = s(p, q) →
    ¬ H.Reachable p q →
    ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0

theorem jkr_lineH_edgeSet_infinite : jkr_lineH.edgeSet.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => s(![(n : ℤ) + 1, (0:ℤ)], ![(n : ℤ) + 1 + 1, 0])) ?_ ?_
  · intro m n hmn
    simp only at hmn
    rw [Sym2.eq_iff] at hmn
    rcases hmn with ⟨h, _⟩ | ⟨h, hb⟩
    · rw [site2_eq] at h
      have : (m : ℤ) = (n : ℤ) := by omega
      exact_mod_cast this
    · rw [site2_eq] at h hb
      have : (m : ℤ) = (n : ℤ) := by omega
      exact_mod_cast this
  · intro n
    change s(![(n : ℤ) + 1, (0:ℤ)], ![(n : ℤ) + 1 + 1, 0]) ∈ jkr_lineH.edgeSet
    refine (jkr_line_seg_mem ((n : ℤ) + 1)).mpr ?_
    have : (0:ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    omega

theorem jkr_lineH_not_finite : ¬ jkr_lineH.edgeSet.Finite :=
  jkr_lineH_edgeSet_infinite

end Lattice

end StatMech
