/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Languages.ContextFree.CYKIndexed
public import CSLibExt.Computability.Languages.ContextFree.CYK

/-!
# Correctness of indexed CYK

The invariant refers to canonical `Yields` on factors. Factors appear only
in specifications and proofs, never in the executable table algorithm.
-/

@[expose] public section

namespace Cslib.Language.CYKIndexed

variable {T N : Type*} [DecidableEq T] [DecidableEq N]

omit [DecidableEq T] in
private theorem factor_one (w : List T) (i : ℕ) (a : T) :
    (w.drop i).take 1 = [a] ↔ w.toArray[i]? = some a := by
  rw [List.getElem?_toArray, List.take_one, List.head?_drop]
  cases w[i]? <;> simp

private theorem fits_eq {g : ContextFreeGrammar T} [DecidableEq g.NT]
    (tc nc : ℕ) (w : List T) (tbl : Array (Array (List g.NT)))
    (i len : ℕ) (hbound : i + len ≤ w.length)
    (f : List T → Finset g.NT)
    (hf : ∀ k, 0 < k → k < len → ∀ a,
      (a ∈ lookup tbl i k ↔ a ∈ f ((w.drop i).take k)) ∧
      (a ∈ lookup tbl (i + k) (len - k) ↔
        a ∈ f ((w.drop (i + k)).take (len - k))))
    (out : List (Symbol T g.NT)) :
    (fits tc nc w.toArray tbl i len out).ret = true ↔
      cykFits f ((w.drop i).take len) out = true := by
  have hlen : ((w.drop i).take len).length = len := by simp; omega
  match out with
  | [.terminal a] =>
      simp only [fits, cykFits, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨rfl, h⟩
        exact (factor_one w i a).2 h
      · intro h
        have heq : len = 1 := by simpa [h] using hlen.symm
        exact ⟨heq, (factor_one w i a).1 (heq ▸ h)⟩
  | [.nonterminal b, .nonterminal c] =>
      rw [fits, cykFits_pair_iff, splits_ret, hlen]
      constructor
      · rintro ⟨k, hk, hkl, hb, hc⟩
        have hlt : k < len := by omega
        refine ⟨k, hlt, hk, ?_, ?_⟩
        · simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
            using ((hf k hk hlt b).1).1 hb
        · simpa [List.drop_take, List.drop_drop]
            using ((hf k hk hlt c).2).1 hc
      · rintro ⟨k, hlt, hk, hb, hc⟩
        refine ⟨k, hk, by omega, ?_, ?_⟩
        · apply ((hf k hk hlt b).1).2
          simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)] using hb
        · apply ((hf k hk hlt c).2).2
          simpa [List.drop_take, List.drop_drop] using hc
  | [] | [.nonterminal _] | .terminal _ :: _ :: _ |
      .nonterminal _ :: .terminal _ :: _ |
      .nonterminal _ :: .nonterminal _ :: _ :: _ => simp [fits, cykFits]

private theorem factor_cell {g : ContextFreeGrammar T} [DecidableEq g.NT]
    (hg : IsChomskyNormalForm g) (w : List T) (j m d : ℕ)
    (hm : 0 < m) (hmd : m ≤ d) (hbound : j + m ≤ w.length)
    (a : g.NT) :
    a ∈ cykCell g d ((w.drop j).take m) ↔
      Yields g [.nonterminal a] ((w.drop j).take m) := by
  have hlen : ((w.drop j).take m).length = m := by simp; omega
  apply mem_cykCell_iff hg d
  · intro h
    simp [h] at hlen
    omega
  · omega

/-- A cell is correct once all strictly shorter, valid factors are correct.
The rule enumeration certificate constrains data only, not computation. -/
theorem cell_correct {g : ContextFreeGrammar T} [DecidableEq g.NT]
    (hg : IsChomskyNormalForm g) (tc nc : ℕ) (w : List T)
    (rs : List (ContextFreeRule T g.NT))
    (hrs : ∀ r, r ∈ rs ↔ r ∈ g.rules)
    (tbl : Array (Array (List g.NT))) (i len : ℕ)
    (hpos : 0 < len) (hbound : i + len ≤ w.length)
    (htbl : ∀ j m, 0 < m → m < len → j + m ≤ w.length → ∀ a,
      a ∈ lookup tbl j m ↔
        Yields g [.nonterminal a] ((w.drop j).take m)) (a : g.NT) :
    a ∈ (cell tc nc w.toArray tbl i len rs).ret ↔
      Yields g [.nonterminal a] ((w.drop i).take len) := by
  have hf := fun k (hk : 0 < k) (hkl : k < len) b =>
    And.intro
      ((htbl i k hk hkl (by omega) b).trans
        (factor_cell hg w i k len hk (by omega) (by omega) b).symm)
      ((htbl (i + k) (len - k) (by omega) (by omega) (by omega) b).trans
        (factor_cell hg w (i + k) (len - k) len (by omega)
          (by omega) (by omega) b).symm)
  rw [← factor_cell hg w i len (len + 1) hpos (by omega) hbound a]
  simp only [cykCell, cykCellFrom, Finset.mem_image, Finset.mem_filter,
    mem_cell]
  constructor
  · rintro ⟨r, hr, ha, hfit⟩
    exact ⟨r, ⟨(hrs r).1 hr, (fits_eq tc nc w tbl i len hbound
      (cykCell g len) hf r.output).1 hfit⟩, ha⟩
  · rintro ⟨r, ⟨hr, hfit⟩, ha⟩
    exact ⟨r, (hrs r).2 hr, ha, (fits_eq tc nc w tbl i len hbound
      (cykCell g len) hf r.output).2 hfit⟩

/-- Row construction preserves the exact start-position indexing. -/
theorem row_get (tc nc : ℕ) (w : Array T)
    (tbl : Array (Array (List N))) (len : ℕ)
    (rs : List (ContextFreeRule T N)) (i count j : ℕ) :
    (row tc nc w tbl len rs i count).ret[j]? =
      if j < count then some (cell tc nc w tbl (i + j) len rs).ret
      else none := by
  induction count generalizing i j with
  | zero => simp [row]
  | succ count ih =>
      cases j with
      | zero => simp [row]
      | succ j =>
          simpa [row, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using ih (i + 1) j

/-- The outer table retains its allocated size through every update. -/
@[simp] theorem table_size (tc nc : ℕ) (w : Array T)
    (rs : List (ContextFreeRule T N)) (depth : ℕ) :
    (table tc nc w rs depth).ret.size = w.size + 1 := by
  induction depth with
  | zero => simp [table]
  | succ depth ih => simpa [table] using ih

/-- Updating one length never changes another length's cells. -/
theorem lookup_table_other (tc nc : ℕ) (w : Array T)
    (rs : List (ContextFreeRule T N)) (depth i len : ℕ)
    (h : depth + 1 ≠ len) :
    lookup (table tc nc w rs (depth + 1)).ret i len =
      lookup (table tc nc w rs depth).ret i len := by
  simp [table, lookup, Array.set!, h]

/-- The new length's row contains exactly the cells just computed. -/
theorem lookup_table_new (tc nc : ℕ) (w : Array T)
    (rs : List (ContextFreeRule T N)) (depth i : ℕ)
    (hd : depth < w.size) (hi : i < w.size + 1) :
    lookup (table tc nc w rs (depth + 1)).ret i (depth + 1) =
      (cell tc nc w (table tc nc w rs depth).ret i (depth + 1) rs).ret := by
  simp [table, lookup, Array.set!, table_size, row_get, hd, hi]

/-- Every completed valid cell agrees with canonical grammar derivations. -/
theorem table_correct {g : ContextFreeGrammar T} [DecidableEq g.NT]
    (hg : IsChomskyNormalForm g) (tc nc : ℕ) (w : List T)
    (rs : List (ContextFreeRule T g.NT))
    (hrs : ∀ r, r ∈ rs ↔ r ∈ g.rules) (depth : ℕ) :
    ∀ i len, 0 < len → len ≤ depth → i + len ≤ w.length → ∀ a,
      a ∈ lookup (table tc nc w.toArray rs depth).ret i len ↔
        Yields g [.nonterminal a] ((w.drop i).take len) := by
  induction depth with
  | zero => intros; omega
  | succ depth ih =>
      intro i len hpos hdepth hbound a
      by_cases h : depth + 1 = len
      · subst len
        rw [lookup_table_new tc nc w.toArray rs depth i
          (by simpa using (show depth < w.length by omega))
          (by simpa using (show i < w.length + 1 by omega))]
        exact cell_correct hg tc nc w rs hrs _ i (depth + 1) hpos hbound
          (fun j m hm hmd hj => ih j m hm (by omega) hj) a
      · rw [lookup_table_other tc nc w.toArray rs depth i len h]
        exact ih i len hpos (by omega) hbound a

omit [DecidableEq T] in
/-- Epsilon scanning agrees with existence of a start epsilon production. -/
@[simp] theorem epsilon_ret (nc : ℕ) (start : N)
    (rs : List (ContextFreeRule T N)) :
    (epsilon nc start rs).ret = true ↔
      ∃ r ∈ rs, r.input = start ∧ r.output = [] := by
  induction rs with
  | nil => simp [epsilon]
  | cons r rs ih => simp [epsilon, ih]

/-- The indexed recognizer decides the existing canonical language. -/
theorem recognizes_iff {g : ContextFreeGrammar T} [DecidableEq g.NT]
    (hg : IsChomskyNormalForm g) (tc nc : ℕ)
    (rs : List (ContextFreeRule T g.NT))
    (hrs : ∀ r, r ∈ rs ↔ r ∈ g.rules) (w : List T) :
    (recognizes tc nc g.initial rs w).ret = true ↔ w ∈ g.language := by
  cases w with
  | nil =>
      rw [← cykAccepts_iff hg]
      simp [recognizes, cykAccepts, hrs]
  | cons x xs =>
      rw [mem_language_iff_yields]
      simpa [recognizes, member_ret] using
        table_correct hg tc nc (x :: xs) rs hrs (x :: xs).length
          0 (x :: xs).length (by simp) le_rfl (by simp) g.initial

/-- Exact Boolean correspondence with the existing list-table recognizer. -/
theorem recognizes_eq_cykAccepts {g : ContextFreeGrammar T}
    [DecidableEq g.NT] (hg : IsChomskyNormalForm g) (tc nc : ℕ)
    (rs : List (ContextFreeRule T g.NT))
    (hrs : ∀ r, r ∈ rs ↔ r ∈ g.rules) (w : List T) :
    (recognizes tc nc g.initial rs w).ret = cykAccepts g w := by
  apply Bool.eq_iff_iff.mpr
  exact (recognizes_iff hg tc nc rs hrs w).trans (cykAccepts_iff hg).symm

end Cslib.Language.CYKIndexed
