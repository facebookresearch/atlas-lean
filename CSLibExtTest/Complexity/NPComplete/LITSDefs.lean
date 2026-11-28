/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.LITSDefs

namespace MetaMathlibExt.Complexity.NPComplete.LITS

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : LITSInstance) :
    litsDec (bitEncode i) = true ↔ WellFormed i ∧ LITSFeasible i := by
  simp [litsDec, bitDecode_bitEncode]

/-- An induced subgraph of a connected grid on a set containing every square is connected. -/
private theorem induce_all_connected {i : LITSInstance} (hG : (Grid i).Connected)
    {S : Set (Fin (rows i) × Fin (cols i))} (hS : ∀ x, x ∈ S) :
    ((Grid i).induce S).Connected := by
  rw [Set.eq_univ_of_forall hS]
  exact (SimpleGraph.induceUnivIso _).connected_iff.2 hG

/-- One region covering a `1 × 4` strip. -/
private abbrev strip : LITSInstance := [[0, 0, 0, 0]]

/-- One region covering a `2 × 2` square. -/
private abbrev square : LITSInstance := [[0, 0], [0, 0]]

private theorem strip_connected : (Grid strip).Connected :=
  (SimpleGraph.connected_pathGraph_add_one 0).boxProd (SimpleGraph.connected_pathGraph_add_one 3)

private theorem square_connected : (Grid square).Connected :=
  (SimpleGraph.connected_pathGraph_add_one 1).boxProd (SimpleGraph.connected_pathGraph_add_one 1)

private theorem strip_region (x : Fin (rows strip) × Fin (cols strip)) : region strip x = 0 := by
  revert x
  unfold region
  decide

private theorem square_region (x : Fin (rows square) × Fin (cols square)) :
    region square x = 0 := by
  revert x
  unfold region
  decide

/-- A single-region grid is well formed: its only nonempty region is the whole grid. -/
private theorem wellFormed_single {i : LITSInstance} (hG : (Grid i).Connected)
    (hreg : ∀ x, region i x = 0) (hr : 0 < rows i) (hc : 0 < cols i)
    (hrows : ∀ row ∈ i, row.length = cols i) : WellFormed i := by
  refine ⟨hr, hc, hrows, fun k => ?_⟩
  by_cases hk : k = 0
  · subst hk
    exact (induce_all_connected hG fun x => hreg x).preconnected
  · intro u
    exact absurd ((hreg u.1).symm.trans u.2) (Ne.symm hk)

/-- A lone continuation bit is a truncated instance encoding. -/
example : litsDec [true] = false := by
  have h : bitDecode (α := LITSInstance) [true] = none := rfl
  simp [litsDec, h]

/-- Shading the whole `1 × 4` strip places an I-tetromino in its single region. -/
example : litsDec (bitEncode strip) = true := by
  apply (accepts_encoding _).2
  refine ⟨wellFormed_single strip_connected strip_region (by decide) (by decide) (by decide),
    fun _ _ => true, induce_all_connected strip_connected fun _ => rfl, fun x => ⟨?_, ?_⟩,
    fun x y _ _ _ hxy => absurd ((strip_region x).trans (strip_region y).symm) hxy, ?_⟩
  · simp only [strip_region, and_true]
    decide
  · exact induce_all_connected strip_connected fun y =>
      ⟨(strip_region y).trans (strip_region x).symm, rfl⟩
  · intro r c hr
    simp [rows] at hr

/-- The `2 × 2` region must be shaded entirely (an O-tetromino), which is a forbidden `2 × 2`
block. -/
example : litsDec (bitEncode square) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, b, -, hreg, -, h22⟩ := (accepts_encoding _).1 hacc
  let x : Fin (rows square) × Fin (cols square) := (⟨0, by decide⟩, ⟨0, by decide⟩)
  have hcard := (hreg x).1
  have huniv : (Finset.univ : Finset (Fin (rows square) × Fin (cols square))).card = 4 := by
    decide
  rw [← huniv] at hcard
  have hall := Finset.filter_card_eq hcard
  have hb : ∀ r c (hr : r < rows square) (hc : c < cols square), b r c = true :=
    fun r c hr hc => (hall (⟨r, hr⟩, ⟨c, hc⟩) (Finset.mem_univ _)).2
  exact h22 0 0 (by decide) (by decide)
    ⟨hb 0 0 (by decide) (by decide), hb 0 1 (by decide) (by decide),
      hb 1 0 (by decide) (by decide), hb 1 1 (by decide) (by decide)⟩

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed square :=
  wellFormed_single square_connected square_region (by decide) (by decide) (by decide)

end MetaMathlibExt.Complexity.NPComplete.LITS
