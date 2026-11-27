/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.Represented

/-!
# Building a table in order from its earlier rows

At each step, a row computation reads the current input row and every output
row already written. A fixed bound on the encoded size of each new output
suffices for a polynomial-time implementation, including malformed input.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.RowTrace

open MetaMathlibExt BitstringEncoding ComplexityTheory BitScan Comprehension Iteration
open TM2Composition

local notation "Bits" => List Bool

private theorem polyTake (n : ℕ) : IsPolyTime (fun x : Bits => x.take n) := by
  induction n with
  | zero => simpa using polyConst []
  | succ n ih =>
    have h := polyIf polyEmpty (polyConst []) (polyAppend polyHead (polyTail.comp ih))
    convert h using 1
    funext x
    cases x <;> rfl

private def addRow (f : Bits → Bits) (B : ℕ) (acc row : Bits) :=
  acc ++ delimit ((f (pack row acc)).take B)

private def state (rows : List Bits) (acc : Bits) := pack (rows.flatMap delimit) acc

private def step (f : Bits → Bits) (B : ℕ) (s : Bits) :=
  if (hd s).isEmpty then false :: tl s
  else true :: pack (tl (hd s)) (addRow f B (tl s) (hd (hd s)))

private theorem polyStep {f : Bits → Bits} (hf : IsPolyTime f) (B : ℕ) : IsPolyTime (step f B) := by
  let hL := polyField true false
  let hR := polyField false true
  let val := (((polyPack (hL.comp hL) hR).comp hf).comp (polyTake B)).comp polyDelimit
  exact polyIf (hL.comp polyEmpty) (polyAppend (polyConst [false]) hR)
    (polyAppend (polyConst [true]) (polyPack (hL.comp hR) (polyAppend hR val)))

private theorem run (f : Bits → Bits) (B N : ℕ) (rs : List Bits) (acc : Bits)
    (hr : (state rs []).length ≤ N) (ha : acc.length + rs.length * (2 * B + 1) ≤ N * (2 * B + 1)) :
    Iterates (step f B) (N + N * (2 * B + 1)) (rs.length + 1) (state rs acc)
      (rs.foldl (addRow f B) acc) := by
  have len (rr : List Bits) (a b : Bits) :
      (state rr a).length = (state rr b).length - b.length + a.length := by simp [state, pack]
  have room : (state rs acc).length ≤ N + N * (2 * B + 1) := by
    rw [len rs acc []]
    simp
    omega
  induction rs generalizing acc with
  | nil => apply Iterates.halt room; simp [step, state]
  | cons r rs ih =>
    have en : (pack r (rs.flatMap delimit)).isEmpty = false := by cases r <;> rfl
    have ht : (state rs []).length ≤ (state (r :: rs) []).length := by
      simp [state, pack, length_delimit]
    have hl : (addRow f B acc r).length ≤ acc.length + (2 * B + 1) := by
      have h : ((f (pack r acc)).take B).length ≤ B := List.length_take_le ..
      simp only [addRow, List.length_append, length_delimit]
      omega
    have ha' : (addRow f B acc r).length + rs.length * (2 * B + 1) ≤ N * (2 * B + 1) := by
      rw [List.length_cons, Nat.succ_mul rs.length] at ha
      omega
    apply Iterates.next room (y := state rs (addRow f B acc r))
    · have eq : (r :: rs).flatMap delimit = pack r (rs.flatMap delimit) := rfl
      simp [step, state, eq, en]
    · apply ih _ (ht.trans hr) ha'
      rw [len _ _ []]
      simp
      omega

/-- A finite bound on the width of each output row turns this left-to-right
table construction into a represented polynomial-time function. -/
theorem represented {α β : Type} (e : α → Bits) (r : β → Bits)
    (f : List β → α → β) (B : ℕ) (bound : ∀ a x, (r (f a x)).length ≤ B)
    (hf : Represented (pair e (frames r)) (fun p => r (f p.2 p.1))) :
    Represented (frames e)
      (fun xs => frames r (xs.foldl (fun a x => a ++ [f a x]) [])) := by
  obtain ⟨g, hg, eq⟩ := hf
  let start (w : Bits) := state (rowsOf w) []
  have hi : IsPolyTime start := polyPack (polyNormalizeRows polyWordId) (polyConst [])
  refine ⟨fun w => (rowsOf w).foldl (addRow g B) [], ?_, ?_⟩
  · let X := Polynomial.X (R := ℕ)
    apply isPolyTime_of_iterates_from hi (polyStep hg B) (X + 1) (X + X * Polynomial.C (2 * B + 1))
    intro w
    let rs := rowsOf w
    let N := (start w).length
    have hn : rs.length ≤ N := (call_count rs).trans (by simp [N, start, state, pack, rs]; omega)
    have h := run g B N rs [] le_rfl (by simpa using Nat.mul_le_mul_right (2 * B + 1) hn)
    exact ⟨rs.length + 1, by simpa [X, N, rs] using Nat.add_le_add_right hn 1,
      by simpa [X, N, rs, start] using h⟩
  · intro xs
    have h (ys : List α) (acc : List β) : (ys.map e).foldl (addRow g B) (frames r acc) =
        frames r (ys.foldl (fun a x => a ++ [f a x]) acc) := by
      induction ys generalizing acc with
      | nil => rfl
      | cons y ys ih =>
        have hg' := eq (y,acc)
        change g (pack (e y) (frames r acc)) = r (f acc y) at hg'
        have ha : addRow g B (frames r acc) (e y) = frames r (acc ++ [f acc y]) := by
          rw [addRow, hg', List.take_of_length_le (bound acc y)]
          simp [frames]
        simp only [List.map_cons, List.foldl_cons, ha, ih]
    change ((rowsOf ((xs.map e).flatMap delimit)).foldl _ []) = _
    rw [rowsOf_frames]
    exact h xs []

end Cslib.Complexity.PolynomialEncoding.RowTrace
