/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceBeadIntervals
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceMapOperator
import Mathlib.Data.Finset.Max

/-!
# Actual adjacent-joint coverage of every original necklace

Every consecutive original edge lies in a unique positive original
bead. Every complete scalar simplex then lies in a whole original bead
when the original necklace has positive dimension. The original zero
necklace remains separate.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open CategoryTheory.CoherentRealization.OriginalBeadInterval

/-- Every original consecutive edge is covered by an actual positive bead. -/
theorem exists_bead_at_edge (T : Data) (i : Fin T.dimension) :
    ∃ a b : Fin (T.dimension + 1), IsBead T a b ∧ a ≤ i.castSucc ∧ i.succ ≤ b := by
  classical
  let L := T.joints.filter (fun j => j ≤ i.castSucc)
  have hL : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨T.source_joint, Fin.zero_le _⟩⟩
  let R := T.joints.filter (fun j => i.succ ≤ j)
  have hR : R.Nonempty := ⟨Fin.last T.dimension,
    Finset.mem_filter.mpr ⟨T.target_joint, Fin.le_last _⟩⟩
  let a := L.max' hL
  let b := R.min' hR
  have ha := Finset.mem_filter.mp (L.max'_mem hL)
  have hb := Finset.mem_filter.mp (R.min'_mem hR)
  refine ⟨a, b, ⟨ha.1, hb.1, ?_, ?_⟩, ha.2, hb.2⟩
  · exact ha.2.trans_lt ((by change i.val < i.val + 1; omega : i.castSucc < i.succ).trans_le hb.2)
  · intro j hj
    by_cases hji : j ≤ i.castSucc
    · exact Or.inl (L.le_max' j (Finset.mem_filter.mpr ⟨hj, hji⟩))
    · have hij : i.succ ≤ j := by
        change i.val + 1 ≤ j.val
        change ¬ j.val ≤ i.val at hji
        omega
      exact Or.inr (R.min'_le j (Finset.mem_filter.mpr ⟨hj, hij⟩))

/-- The actual whole bead at a consecutive original edge is unique, retaining both original joints. -/
theorem bead_at_edge_unique {T : Data} {i : Fin T.dimension}
    {a b c d : Fin (T.dimension + 1)} (h : IsBead T a b) (h' : IsBead T c d)
    (ha : a ≤ i.castSucc) (hb : i.succ ≤ b) (hc : c ≤ i.castSucc) (hd : i.succ ≤ d) :
    a = c ∧ b = d := by
  have hi : i.castSucc < i.succ := by change i.val < i.val + 1; omega
  have hab : i.castSucc < b := hi.trans_le hb
  have hcd : i.castSucc < d := hi.trans_le hd
  have hca : c ≤ a := (h.consecutive c h'.source).resolve_right
    (fun hbc => (hab.trans_le (hbc.trans hc)).false)
  have hac : a ≤ c := (h'.consecutive a h.source).resolve_right
    (fun hda => (hcd.trans_le (hda.trans ha)).false)
  have hdb : b ≤ d := (h.consecutive d h'.target).resolve_left
    (fun hda => (hcd.trans_le (hda.trans ha)).false)
  have hbd : d ≤ b := (h'.consecutive b h.target).resolve_left
    (fun hbc => (hab.trans_le (hbc.trans hc)).false)
  exact ⟨le_antisymm hac hca, le_antisymm hdb hbd⟩

/-- Every complete original scalar simplex is contained in an actual whole positive bead. -/
theorem simplex_in_bead (T : Data) (hn : 0 < T.dimension) {d : ℕ}
    (s : (Δ[T.dimension] : SSet.{u}) _⦋d⦌)
    (hs : s ∈ (complex T.joints).obj (op ⦋d⦌)) :
    ∃ a b : Fin (T.dimension + 1), IsBead T a b ∧ ∀ j, a ≤ s j ∧ s j ≤ b := by
  let i : Fin T.dimension := ⟨min (s 0).val (T.dimension - 1), by omega⟩
  obtain ⟨a, b, hab, ha, hb⟩ := exists_bead_at_edge T i
  have ha0 : a ≤ s 0 := by
    apply ha.trans
    change min (s 0).val (T.dimension - 1) ≤ (s 0).val
    exact Nat.min_le_left _ _
  have hb0 : s 0 ≤ b := by
    by_cases h0 : (s 0).val < T.dimension
    · apply le_trans _ hb
      change (s 0).val ≤ min (s 0).val (T.dimension - 1) + 1
      omega
    · have h0 : s 0 = Fin.last T.dimension := by
        apply Fin.ext
        change (s 0).val = T.dimension
        have := (s 0).isLt
        omega
      have hi : i.succ = Fin.last T.dimension := by
        apply Fin.ext
        change min (s 0).val (T.dimension - 1) + 1 = T.dimension
        omega
      simpa only [h0, hi] using hb
  refine ⟨a, b, hab, fun j => ⟨ha0.trans (stdSimplex.monotone_apply s (Fin.zero_le j)), ?_⟩⟩
  have hcut := (mem_complex_iff T.joints s).mp hs b hab.target
  rcases hcut with hcut | hcut
  · exact hcut j
  · have h0 : s 0 = b := le_antisymm hb0 (hcut 0)
    by_cases hn0 : (s 0).val = T.dimension
    · have hbLast : b = Fin.last T.dimension := by
        apply Fin.ext
        change b.val = T.dimension
        have hv := congrArg Fin.val h0
        omega
      exact (Fin.le_last (s j)).trans hbLast.symm.le
    · have h0lt : (s 0).val < T.dimension := by have := (s 0).isLt; omega
      have hi : i.val = (s 0).val := by change min (s 0).val (T.dimension - 1) = _; omega
      have hib : i.succ ≤ s 0 := hb.trans h0.symm.le
      change i.val + 1 ≤ (s 0).val at hib
      omega

end SSet.OriginalNecklace
