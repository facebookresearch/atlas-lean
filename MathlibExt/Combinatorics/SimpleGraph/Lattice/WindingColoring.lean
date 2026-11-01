/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CutColoring
public import Mathlib.Tactic.NormNum.Result
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.RingNF

/-!
# Face colorings from flip relations with even loops

A flip relation marks some lattice steps as color changes. If every closed walk has an even number
of flips (`wcl_ClosedEven`), coloring each face by the parity of flips along any walk from a base
face gives a coloring that changes exactly across the flips. A cut coloring for `H` and a dual edge
`f₀g₀` therefore exists iff the cut flip relation has even loops, and then `f₀` and `g₀` are
separated in the face-region graph of `H` with `f₀g₀` deleted. For the empty graph the cut flip
relation has an odd loop, so cut colorings need not exist; the form conditional on even loops,
`wcl_CorrectColoringResidue`, holds.

## Main definitions

* `StatMech.Lattice.wcl_SymmFlip flip`, `StatMech.Lattice.wcl_flipCount flip w`,
  `StatMech.Lattice.wcl_ClosedEven flip`: symmetric flip relations, flip counts along walks, and
  even loops.
* `StatMech.Lattice.wcl_windingColoring flip o`: the parity of flips along a chosen walk from `o`.
* `StatMech.Lattice.wcl_cutFlip H f0 g0`: flips across the dual edges of `H` and across `f0g0`.
* `StatMech.Lattice.wcl_CorrectColoringResidue`: whenever the cut flip relation has even loops,
  there is a cut coloring separating `f0` from `g0`.

## Main results

* `StatMech.Lattice.wcl_windingColoring_compat`: the winding coloring changes exactly across flips.
* `StatMech.Lattice.wcl_exists_cutColoring_iff_closedEven`: a cut coloring exists iff the cut flip
  relation has even loops.
* `StatMech.Lattice.wcl_correctColoringResidue_holds`: `wcl_CorrectColoringResidue` holds.
* `StatMech.Lattice.wcl_deleted_separated_of_closedEven`: even loops separate the ends of the
  deleted dual edge.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Lattice

/-- The flip relation is symmetric on lattice edges. -/
def wcl_SymmFlip (flip : Site 2 → Site 2 → Prop) : Prop :=
  ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ flip b a)

/-- The number of steps of the walk `w` that are flips (in either direction). -/
noncomputable def wcl_flipCount (flip : Site 2 → Site 2 → Prop) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ := by
  classical
  exact w.edges.countP (fun e => decide (Sym2.lift ⟨fun a b => flip a b ∨ flip b a, by
    intro a b; simp only [eq_iff_iff]; tauto⟩ e))

@[simp] theorem wcl_flipCount_nil (flip : Site 2 → Site 2 → Prop) (x : Site 2) :
    wcl_flipCount flip (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical
  simp [wcl_flipCount]

open Classical in
theorem wcl_flipCount_cons (flip : Site 2 → Site 2 → Prop) {a b c : Site 2}
    (hab : (hypercubicLattice 2).Adj a b) (p : (hypercubicLattice 2).Walk b c) :
    wcl_flipCount flip (Walk.cons hab p) =
      (if (flip a b ∨ flip b a) then 1 else 0) + wcl_flipCount flip p := by
  classical
  rw [wcl_flipCount, wcl_flipCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
  by_cases h : (flip a b ∨ flip b a)
  · rw [ite_eq_left (by exact @decide_eq_true _ (Classical.propDecidable _) h), ite_eq_left h]; ring
  · rw [ite_eq_right (by exact fun h' => h (@of_decide_eq_true _ (Classical.propDecidable _) h')),
      ite_eq_right h]; ring

theorem wcl_flipCount_append (flip : Site 2 → Site 2 → Prop) {x y z : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (q : (hypercubicLattice 2).Walk y z) :
    wcl_flipCount flip (p.append q) = wcl_flipCount flip p + wcl_flipCount flip q := by
  classical
  rw [wcl_flipCount, wcl_flipCount, wcl_flipCount, SimpleGraph.Walk.edges_append,
    List.countP_append]

theorem wcl_flipCount_reverse (flip : Site 2 → Site 2 → Prop) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    wcl_flipCount flip w.reverse = wcl_flipCount flip w := by
  classical
  rw [wcl_flipCount, wcl_flipCount, SimpleGraph.Walk.edges_reverse, List.countP_reverse]

/-- Every closed lattice walk has an even number of flips. -/
def wcl_ClosedEven (flip : Site 2 → Site 2 → Prop) : Prop :=
  ∀ {x : Site 2} (w : (hypercubicLattice 2).Walk x x), Even (wcl_flipCount flip w)

theorem wcl_flipCount_parity_eq_of_closedEven (flip : Site 2 → Site 2 → Prop)
    (hce : wcl_ClosedEven flip) {x y : Site 2}
    (w₁ w₂ : (hypercubicLattice 2).Walk x y) :
    wcl_flipCount flip w₁ % 2 = wcl_flipCount flip w₂ % 2 := by
  have hloop : Even (wcl_flipCount flip (w₁.append w₂.reverse)) := hce _
  rw [wcl_flipCount_append, wcl_flipCount_reverse] at hloop
  rcases hloop with ⟨k, hk⟩
  omega

/-- A fixed lattice walk from `o` to `f`, chosen using connectedness of `ℤ²`. -/
noncomputable def wcl_chosenWalk (o f : Site 2) : (hypercubicLattice 2).Walk o f :=
  (hypercubicLattice_two_reachable o f).some

/-- The face coloring given by the parity of the number of flips along the chosen walk from `o`. -/
noncomputable def wcl_windingColoring (flip : Site 2 → Site 2 → Prop) (o : Site 2) :
    Site 2 → Prop :=
  fun f => Odd (wcl_flipCount flip (wcl_chosenWalk o f))

theorem wcl_windingColoring_eq_of_walk (flip : Site 2 → Site 2 → Prop)
    (hce : wcl_ClosedEven flip) (o : Site 2) {f : Site 2}
    (w : (hypercubicLattice 2).Walk o f) :
    wcl_windingColoring flip o f ↔ Odd (wcl_flipCount flip w) := by
  unfold wcl_windingColoring
  rw [Nat.odd_iff, Nat.odd_iff,
    wcl_flipCount_parity_eq_of_closedEven flip hce (wcl_chosenWalk o f) w]

theorem wcl_windingColoring_compat (flip : Site 2 → Site 2 → Prop)
    (hsymm : wcl_SymmFlip flip) (hce : wcl_ClosedEven flip) (o : Site 2) {a b : Site 2}
    (hab : (hypercubicLattice 2).Adj a b) :
    (flip a b ↔
      (wcl_windingColoring flip o a ↔ ¬ wcl_windingColoring flip o b)) := by
  classical
  set wa := wcl_chosenWalk o a with hwa
  have hA : wcl_windingColoring flip o a ↔ Odd (wcl_flipCount flip wa) := Iff.rfl
  have hB : wcl_windingColoring flip o b ↔ Odd (wcl_flipCount flip (wa.concat hab)) :=
    wcl_windingColoring_eq_of_walk flip hce o (wa.concat hab)
  have hconcat : wcl_flipCount flip (wa.concat hab) =
      wcl_flipCount flip wa + (if (flip a b ∨ flip b a) then 1 else 0) := by
    rw [SimpleGraph.Walk.concat_eq_append, wcl_flipCount_append]
    congr 1
    show wcl_flipCount flip (SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil) = _
    rw [wcl_flipCount_cons, wcl_flipCount_nil, add_zero]
  have hor : (flip a b ∨ flip b a) ↔ flip a b := by
    have := hsymm a b hab; tauto
  rw [hB, hconcat, hA]
  by_cases h : flip a b
  · rw [ite_eq_left (hor.mpr h), Nat.odd_add_one]
    simp only [h, Nat.not_odd_iff_even, Nat.not_even_iff_odd]
  · rw [ite_eq_right (fun hh => h (hor.mp hh)), add_zero]
    simp only [h, false_iff, not_iff]

/-- The cut flip relation: steps across a dual edge of `H` or across the extra dual edge `f0g0`. -/
def wcl_cutFlip (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) (a b : Site 2) : Prop :=
  whc_isCross H a b ∨ s(a, b) = s(f0, g0)

theorem wcl_cutFlip_symm (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) :
    wcl_SymmFlip (wcl_cutFlip H f0 g0) := by
  intro a b _hab
  unfold wcl_cutFlip whc_isCross
  rw [Sym2.eq_swap]
  tauto

theorem wcl_cutColoring_iff_compat (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (φ : Site 2 → Prop) :
    whc_CutColoring H f0 g0 φ ↔
      ∀ a b, (hypercubicLattice 2).Adj a b →
        (wcl_cutFlip H f0 g0 a b ↔ (φ a ↔ ¬ φ b)) := Iff.rfl

theorem wcl_windingColoring_isCutColoring (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) (o : Site 2) :
    whc_CutColoring H f0 g0 (wcl_windingColoring (wcl_cutFlip H f0 g0) o) := by
  rw [wcl_cutColoring_iff_compat]
  intro a b hab
  exact wcl_windingColoring_compat (wcl_cutFlip H f0 g0) (wcl_cutFlip_symm H f0 g0) hce o hab

theorem wcl_flipCount_parity_of_compat (flip : Site 2 → Site 2 → Prop) (φ : Site 2 → Prop)
    (hcompat : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ (φ a ↔ ¬ φ b)))
    {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    Even (wcl_flipCount flip w) ↔ (φ x ↔ φ y) := by
  classical
  induction w with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [wcl_flipCount_cons]
    by_cases hcr : (flip a b ∨ flip b a)
    · rw [ite_eq_left hcr, add_comm, Nat.even_add_one, ih]
      have hab' := (hcompat a b hab)
      have hba' := (hcompat b a hab.symm)
      have hf : flip a b := by
        rcases hcr with h | h
        · exact h
        · exact hab'.mpr (by have := hba'.mp h; tauto)
      have := hab'.mp hf
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all
    · rw [ite_eq_right hcr, zero_add, ih]
      have hnf : ¬ flip a b := fun h => hcr (Or.inl h)
      have := fun hh => hnf ((hcompat a b hab).mpr hh)
      by_cases ha : φ a <;> by_cases hb : φ b <;> by_cases hc : φ c <;> simp_all

theorem wcl_closedEven_of_compat (flip : Site 2 → Site 2 → Prop) (φ : Site 2 → Prop)
    (hcompat : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ (φ a ↔ ¬ φ b))) :
    wcl_ClosedEven flip := by
  intro x w
  rw [wcl_flipCount_parity_of_compat flip φ hcompat w]

theorem wcl_no_cutColoring_of_odd_loop (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) (hodd : ¬ Even (wcl_flipCount (wcl_cutFlip H f0 g0) w)) :
    ¬ ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ := by
  rintro ⟨φ, hcut⟩
  rw [wcl_cutColoring_iff_compat] at hcut
  exact hodd (wcl_closedEven_of_compat (wcl_cutFlip H f0 g0) φ hcut w)

theorem wcl_exists_cutColoring_iff_closedEven (H : SimpleGraph (Site 2)) (f0 g0 : Site 2) :
    (∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ) ↔
      wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
  constructor
  · rintro ⟨φ, hcut⟩
    rw [wcl_cutColoring_iff_compat] at hcut
    exact wcl_closedEven_of_compat (wcl_cutFlip H f0 g0) φ hcut
  · intro hce
    exact ⟨wcl_windingColoring (wcl_cutFlip H f0 g0) ![0, 0],
      wcl_windingColoring_isCutColoring H f0 g0 hce ![0, 0]⟩

/-- The closed walk around the unit square with corners `(0, 0)` and `(1, -1)`. -/
noncomputable def wcl_squareLoop : (hypercubicLattice 2).Walk ![(0:ℤ), 0] ![(0:ℤ), 0] := by
  have a1 : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have a2 : (hypercubicLattice 2).Adj ![(0:ℤ), -1] ![(1:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have a3 : (hypercubicLattice 2).Adj ![(1:ℤ), -1] ![(1:ℤ), 0] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have a4 : (hypercubicLattice 2).Adj ![(1:ℤ), 0] ![(0:ℤ), 0] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  exact .cons a1 (.cons a2 (.cons a3 (.cons a4 .nil)))

theorem wcl_empty_instance_valid :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, not_false_eq_true]
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num

theorem wcl_cutFlip_bot_iff (a b : Site 2) :
    wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] a b ↔
      s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) := by
  unfold wcl_cutFlip whc_isCross
  simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, false_or, or_false]

theorem wcl_squareLoop_flipCount :
    wcl_flipCount (wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1])
      wcl_squareLoop = 1 := by
  classical
  set flip := wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] with hflip
  unfold wcl_squareLoop
  rw [wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons,
    wcl_flipCount_nil]
  rw [ite_eq_left (Or.inl (by
    rw [hflip, wcl_cutFlip_bot_iff]))]
  rw [ite_eq_right (by
    rintro (h | h) <;> · rw [hflip, wcl_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]
  rw [ite_eq_right (by
    rintro (h | h) <;> · rw [hflip, wcl_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]
  rw [ite_eq_right (by
    rintro (h | h) <;> · rw [hflip, wcl_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]

theorem wcl_faceRegion_bot_adj (a b : Site 2) :
    (whb_faceRegion (⊥ : SimpleGraph (Site 2))).Adj a b ↔ (hypercubicLattice 2).Adj a b := by
  rw [whb_faceRegion_adj]
  simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, not_false_eq_true, and_true]

theorem wcl_faceRegion_bot_reconnect :
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  set G := (whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
    {s(![(0:ℤ), 0], ![(0:ℤ), -1])} with hG
  have mk : ∀ u v : Site 2, (hypercubicLattice 2).Adj u v →
      s(u, v) ≠ s(![(0:ℤ), 0], ![(0:ℤ), -1]) → G.Adj u v := by
    intro u v hadj hne
    rw [hG, deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨(wcl_faceRegion_bot_adj u v).mpr hadj, hne⟩
  have e1 : G.Adj ![(0:ℤ), 0] ![(1:ℤ), 0] :=
    mk _ _ (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num)
      (by rw [ne_eq, Sym2.eq_iff]; simp only [site2_eq]; norm_num)
  have e2 : G.Adj ![(1:ℤ), 0] ![(1:ℤ), -1] :=
    mk _ _ (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num)
      (by rw [ne_eq, Sym2.eq_iff]; simp only [site2_eq]; norm_num)
  have e3 : G.Adj ![(1:ℤ), -1] ![(0:ℤ), -1] :=
    mk _ _ (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num)
      (by rw [ne_eq, Sym2.eq_iff]; simp only [site2_eq]; norm_num)
  exact (e1.reachable.trans e2.reachable).trans e3.reachable

theorem wcl_deleted_separated_of_closedEven (H : SimpleGraph (Site 2)) {f0 g0 : Site 2}
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  set φ := wcl_windingColoring (wcl_cutFlip H f0 g0) f0 with hφ
  have hcut : whc_CutColoring H f0 g0 φ :=
    wcl_windingColoring_isCutColoring H f0 g0 hce f0
  have hflank : ¬ (φ f0 ↔ φ g0) := by
    have := hcut f0 g0 hfg
    have hmark : whc_isCross H f0 g0 ∨ s(f0, g0) = s(f0, g0) := Or.inr rfl
    rw [this] at hmark
    tauto
  exact whc_deleted_separated H f0 g0 φ hcut hflank

/-- For every graph `H` of `ℤ²` and dual edge `f0g0` such that the cut flip relation has even
loops, there is a cut coloring distinguishing `f0` from `g0`, and `f0`, `g0` are disconnected
in the face-region graph of `H` with `f0g0` deleted. -/
def wcl_CorrectColoringResidue : Prop :=
  ∀ (H : SimpleGraph (Site 2)) (f0 g0 : Site 2),
    (hypercubicLattice 2).Adj f0 g0 → wcl_ClosedEven (wcl_cutFlip H f0 g0) →
    ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ ∧ ¬ (φ f0 ↔ φ g0) ∧
      ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0

theorem wcl_correctColoringResidue_holds : wcl_CorrectColoringResidue := by
  intro H f0 g0 hfg hce
  refine ⟨wcl_windingColoring (wcl_cutFlip H f0 g0) f0,
    wcl_windingColoring_isCutColoring H f0 g0 hce f0, ?_,
    wcl_deleted_separated_of_closedEven H hfg hce⟩
  set φ := wcl_windingColoring (wcl_cutFlip H f0 g0) f0
  have := (wcl_windingColoring_isCutColoring H f0 g0 hce f0) f0 g0 hfg
  have hmark : whc_isCross H f0 g0 ∨ s(f0, g0) = s(f0, g0) := Or.inr rfl
  rw [this] at hmark
  tauto

theorem wcl_witness_closedEven :
    wcl_ClosedEven (wcl_cutFlip whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1]) :=
  (wcl_exists_cutColoring_iff_closedEven whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1]).mp
    ⟨whc_phiWitness, whc_cutColoring_witness⟩

theorem wcl_witness_residue_fires :
    ∃ φ : Site 2 → Prop, whc_CutColoring whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] φ ∧
      ¬ (φ ![(0:ℤ), 0] ↔ φ ![(0:ℤ), -1]) ∧
      ¬ ((whb_faceRegion whc_Htest).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable
        ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  exact wcl_correctColoringResidue_holds whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] hfg
    wcl_witness_closedEven

theorem wcl_whitney_forward_of_closedEven (H : SimpleGraph (Site 2)) (p q f0 g0 : Site 2)
    (_hpq : (hypercubicLattice 2).Adj p q) (_hnpq : s(p, q) ∉ H.edgeSet)
    (hfg : (hypercubicLattice 2).Adj f0 g0) (_hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
  wcl_deleted_separated_of_closedEven H hfg hce

end Lattice

end StatMech
