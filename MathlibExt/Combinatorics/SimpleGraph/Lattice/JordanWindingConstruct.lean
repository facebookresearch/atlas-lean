/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KeepResidueExamples
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingColoring

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Cut colorings and the keep–reconnect residue

A cut coloring for `H` and a dual edge `f₀g₀` makes the number of cut flips along a walk even
exactly when the colors at its ends agree; so a closed walk with an odd number of cut flips rules
out cut colorings, as for the empty graph around the unit square. A cut coloring exists iff the cut
flip relation has even loops.

## Main definitions

* `StatMech.Lattice.jwn_cutCount H f0 g0 w`: the number of cut flips along `w`, that is
  `wcl_flipCount (wcl_cutFlip H f0 g0) w`.

## Main results

* `StatMech.Lattice.jwn_cutColoring_closedEven`: with a cut coloring, cut-flip parity is the color
  change.
* `StatMech.Lattice.jwn_no_cutColoring_bot`: there is no cut coloring for the empty graph and the
  dual edge below the face `(0, 0)`.
* `StatMech.Lattice.jwn_cutColoring_of_closedEven`: even loops give a cut coloring.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Lattice

/-- The number of cut flips of `H` and `f0g0` along `w`; equal to
`wcl_flipCount (wcl_cutFlip H f0 g0) w`. -/
noncomputable def jwn_cutCount (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  wcl_flipCount (wcl_cutFlip H f0 g0) w

theorem jwn_marked_iff (H : SimpleGraph (Site 2)) (f0 g0 a b : Site 2) :
    (wcl_cutFlip H f0 g0 a b ∨ wcl_cutFlip H f0 g0 b a) ↔ wcl_cutFlip H f0 g0 a b := by
  unfold wcl_cutFlip whc_isCross
  rw [Sym2.eq_swap]; tauto

theorem jwn_cutColoring_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (jwn_cutCount H f0 g0 w) ↔ (φ x ↔ φ y) := by
  classical
  unfold jwn_cutCount
  induction w with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [wcl_flipCount_cons]
    have hkey : wcl_cutFlip H f0 g0 a b ↔ (φ a ↔ ¬ φ b) := hcut a b hab
    have hmk : (wcl_cutFlip H f0 g0 a b ∨ wcl_cutFlip H f0 g0 b a) ↔
        wcl_cutFlip H f0 g0 a b := jwn_marked_iff H f0 g0 a b
    by_cases hm : (wcl_cutFlip H f0 g0 a b ∨ wcl_cutFlip H f0 g0 b a)
    · rw [ite_eq_left hm, add_comm, Nat.even_add_one, ih]
      have := hkey.mp (hmk.mp hm)
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all
    · rw [ite_eq_right hm, zero_add, ih]
      have hnm : ¬ wcl_cutFlip H f0 g0 a b := fun h => hm (Or.inl h)
      have := fun hh => hnm (hkey.mpr hh)
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all

theorem jwn_no_cutColoring_of_oddLoop (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) (hodd : ¬ Even (jwn_cutCount H f0 g0 w)) :
    ¬ ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ := by
  rintro ⟨φ, hcut⟩
  exact hodd ((jwn_cutColoring_closedEven H f0 g0 φ hcut w).mpr Iff.rfl)

theorem jwn_no_cutColoring_bot :
    ¬ ∃ φ : Site 2 → Prop,
      whc_CutColoring (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] φ := by
  refine wcl_no_cutColoring_of_odd_loop (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1]
    wcl_squareLoop ?_
  rw [wcl_squareLoop_flipCount]; decide

theorem jwn_cutColoring_of_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
    ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ :=
  ⟨wcl_windingColoring (wcl_cutFlip H f0 g0) f0,
    wcl_windingColoring_isCutColoring H f0 g0 hce f0⟩

theorem jwn_cutColoring_forces_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) (hcut : whc_CutColoring H f0 g0 φ) :
    wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
  intro x w
  exact (jwn_cutColoring_closedEven H f0 g0 φ hcut w).mpr Iff.rfl

theorem jwn_witness_square :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧
    ¬ (⊥ : SimpleGraph (Site 2)).Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  obtain ⟨hpq, hnpq, hfg, hshared⟩ := wcl_empty_instance_valid
  refine ⟨hpq, hnpq, hfg, hshared, ?_, wcl_faceRegion_bot_reconnect⟩
  intro h; replace h := SimpleGraph.reachable_bot.mp h
  simp only [site2_eq] at h; omega

theorem jwn_witness_ring :
    jkd_ringP.G.Adj jkd_r0 jkd_r1 ∧
    s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∉ (jei_pushGraph jkd_ringP ⊥).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∧
    ¬ (jei_pushGraph jkd_ringP ⊥).Reachable (jkd_ringP.emb jkd_r0) (jkd_ringP.emb jkd_r1) ∧
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hna : ¬ (⊥ : SimpleGraph jkd_ringP.V).Adj jkd_r0 jkd_r1 := by
    exact (SimpleGraph.bot_adj _ _).mp
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] :=
    jbc_latadj (by rw [Fin.sum_univ_two]; norm_num)
  have hnpq : s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∉
      (jei_pushGraph jkd_ringP ⊥).edgeSet := jkd_wall_not_mem_pushGraph jkd_ringP ⊥ hna
  have hnr : ¬ (jei_pushGraph jkd_ringP ⊥).Reachable
      (jkd_ringP.emb jkd_r0) (jkd_ringP.emb jkd_r1) := by
    intro h; replace h := (jei_push_reachable_iff _ _ _ _).mp h
    replace h := SimpleGraph.reachable_bot.mp h; exact jkd_r0_ne_r1 h
  exact ⟨jkd_ring_Gadj, hnpq, hfg, jkd_ring_shared_bottom, hnr, jkd_ring_witness_reach⟩

end Lattice

end StatMech
