/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.BagRows

/-!
# Choosing one explicit local table for every color

A clique at the target size contains one row of every color, all from a
single formula. Conversely such a collection of compatible rows is a clique.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows

open Cslib.Complexity.PolynomialEncoding.Comprehension

theorem agrees_iff (a b : Local) : agrees a b ↔
    ∀ e ∈ a, ∀ f ∈ b, e.1 = f.1 → e.2 = f.2 := by
  simp only [agrees, List.all_eq_true, decide_eq_true_eq]

theorem adjacent_iff (v w : Row) : adjacent v w ↔
    v.1.2 = w.1.2 ∧ v.2.1.2 ≠ w.2.1.2 ∧ agrees v.2.2 w.2.2 := by
  simp [adjacent, and_assoc]

private def rowGraph : SimpleGraph Row where
  Adj v w := adjacent v w
  symm := ⟨by
    intro v w h
    obtain ⟨hh, hn, ha⟩ := (adjacent_iff ..).mp h
    exact (adjacent_iff ..).mpr ⟨hh.symm, Ne.symm hn, (agrees_iff ..).mpr
      (fun e he f hf eq => ((agrees_iff ..).mp ha f hf e he eq.symm).symm)⟩⟩
  loopless := ⟨by intro v h; exact ((adjacent_iff ..).mp h).2.1 rfl⟩

private instance : DecidableRel rowGraph.Adj := fun _ _ => inferInstanceAs (Decidable (_ = true))

private theorem rowDecision (v w : Row) : decide (rowGraph.Adj v w) = adjacent v w := by
  change decide (adjacent v w = true) = _
  simp

private theorem mem_vertices (B : ℕ) (slots values : List ℕ) (family : List Formula) (v : Row) :
    v ∈ vertices B slots values family ↔
      v.1 ∈ family.zipIdx ∧ v.2.1 ∈ (tuples slots B).zipIdx ∧
      v.2.2 ∈ tuples (slots.product values) B ∧ allowed slots v.2.1.1 v.1.1 v.2.2 := by
  rcases v with ⟨⟨p, i⟩, ⟨c, j⟩, a⟩
  simp [vertices, candidates, List.mem_flatMap, List.mem_map, and_assoc]

/-- The local witness data recovered by a clique. -/
def Selection (B : ℕ) (slots values : List ℕ) (family : List Formula) : Prop :=
  let colors := tuples slots B
  ∃ p ∈ family, ∃ f : Fin colors.length → Local,
    (∀ c, f c ∈ tuples (slots.product values) B ∧ allowed slots colors[c.val] p (f c)) ∧
      ∀ c j, c ≠ j → agrees (f c) (f j)

theorem query_iff_selection (d : ℕ) (slots values : List ℕ) (family : List Formula) :
    CliqueParam (query d slots values family).1 (query d slots values family).2 ↔
      Selection (max 2 (2 * d)) slots values family := by
  let B := max 2 (2 * d)
  let cs := tuples slots B
  let vs := vertices B slots values family
  let col (v : Fin vs.length) : Fin cs.length := ⟨vs[v.val].2.1.2,
    List.snd_lt_of_mem_zipIdx ((mem_vertices ..).mp (List.getElem_mem v.isLt)).2.1⟩
  let G := rowGraph.comap vs.get
  have proper : ∀ ⦃v w⦄, G.Adj v w → col v ≠ col w := fun _ _ h he =>
    ((adjacent_iff ..).mp h).2.1 (congrArg Fin.val he)
  have repr := GraphWriter.writeGraph_iff_indices vs rowGraph (Fintype.card (Fin cs.length))
  simp only [rowDecision, Fintype.card_fin] at repr
  change CliqueParam (GraphWriter.writeGraph vs adjacent) cs.length ↔ _
  rw [repr, ← Fintype.card_fin cs.length, GraphWriter.clique_iff_choice G col proper]
  have position (i : Fin vs.length) (c : Fin cs.length) (ci : col i = c) :
      vs[i.val].2.1.1 = cs[c.val] := by
    have hz := List.mem_zipIdx_iff_getElem?.mp ((mem_vertices ..).mp (List.getElem_mem i.isLt)).2.1
    change cs[vs[i.val].2.1.2]? = some vs[i.val].2.1.1 at hz
    have he : vs[i.val].2.1.2 = c.val := congrArg Fin.val ci
    simpa only [he, List.getElem?_eq_getElem c.isLt, Option.some.injEq] using hz.symm
  constructor
  · rintro ⟨f, colors, clique⟩
    have emptyMem : ([] : List ℕ) ∈ cs := mem_tuples.mpr (by simp)
    let c₀ : Fin cs.length := ⟨0, List.length_pos_of_mem emptyMem⟩
    let base := vs[(f c₀).val]
    have same (c : Fin cs.length) : vs[(f c).val].1.2 = base.1.2 := by
      by_cases hc : c = c₀
      · subst c; rfl
      · exact ((adjacent_iff ..).mp (clique _ _ hc)).1
    have entry (c : Fin cs.length) := (mem_vertices ..).mp (List.getElem_mem (f c).isLt)
    have formula (c : Fin cs.length) : vs[(f c).val].1.1 = base.1.1 := by
      have h := List.mem_zipIdx_iff_getElem?.mp (entry c).1
      have hb := List.mem_zipIdx_iff_getElem?.mp (entry c₀).1
      rw [same] at h
      exact Option.some.inj (h.symm.trans hb)
    refine ⟨base.1.1, List.fst_mem_of_mem_zipIdx (entry c₀).1, fun c => vs[(f c).val].2.2,
      fun c => ⟨(entry c).2.2.1, ?_⟩, fun c j h => ((adjacent_iff ..).mp (clique c j h)).2.2⟩
    simpa only [position _ c (colors c), formula c] using (entry c).2.2.2
  · rintro ⟨p, hp, tables, ok, pairwise⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hp
    let row (c : Fin cs.length) : Row := ((p, i), (cs[c.val], c.val), tables c)
    have member (c : Fin cs.length) : row c ∈ vs := (mem_vertices ..).mpr
      ⟨List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hi, he]),
        List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem c.isLt), ok c⟩
    choose index ih rhs using fun c => List.mem_iff_getElem.mp (member c)
    let pick (c : Fin cs.length) : Fin vs.length := ⟨index c, ih c⟩
    have reads (c : Fin cs.length) : vs[(pick c).val] = row c := rhs c
    refine ⟨pick, fun c => Fin.ext ?_, fun c j hne => ?_⟩
    · change vs[(pick c).val].2.1.2 = c.val
      rw [reads]
    · change adjacent vs[(pick c).val] vs[(pick j).val]
      rw [reads, reads, adjacent_iff]
      exact ⟨rfl, fun eq => hne (Fin.ext eq), pairwise _ _ hne⟩

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows
