/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.Comprehension

/-!
# Polynomial-time enumeration of framed rows

Each row is paired with its zero-based index in unary. A sequence of input length
$n$ has at most $n$ rows, so all written indices together have quadratic length.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.Comprehension

open MetaMathlibExt BitstringEncoding ComplexityTheory BitScan Iteration

local notation "Bits" => List Bool

/-- Unary words used as bounded row indices. -/
def unary (i : ℕ) := List.replicate i true

@[simp] theorem unary_length (i : ℕ) : (unary i).length = i := by simp [unary]

/-- Each output row has a framed unary index followed by the original payload. -/
def indexed (rs : List Bits) (i : ℕ) : List Bits :=
  (rs.zipIdx i).map fun (r, j) => pack (unary j) r

private def enumState (rs : List Bits) (i : ℕ) (acc : Bits) :=
  pack (rs.flatMap delimit) (pack (unary i) acc)

private def enumStep (s : Bits) :=
  let rows := hd s
  let idx := hd (tl s)
  let acc := tl (tl s)
  if rows.isEmpty then false :: acc
  else true :: pack (tl rows) (pack (true :: idx) (acc ++ delimit (pack idx (hd rows))))

private theorem polyEnumStep : IsPolyTime enumStep := by
  have hhd := polyField true false
  have htl := polyField false true
  have hidx := htl.comp hhd
  have hacc := htl.comp htl
  exact polyIf (hhd.comp polyEmpty) (polyAppend (polyConst [false]) hacc)
    (polyAppend (polyConst [true]) (polyPack (hhd.comp htl)
      (polyPack (polyAppend (polyConst [true]) hidx)
        (polyAppend hacc ((polyPack hidx (hhd.comp hhd)).comp polyDelimit)))))

private theorem enum_finished (i : ℕ) (acc : Bits) :
    enumStep (enumState [] i acc) = false :: acc := by simp [enumStep, enumState]

private theorem enum_more (r : Bits) (rs : List Bits) (i : ℕ) (acc : Bits) :
    enumStep (enumState (r :: rs) i acc) =
      true :: enumState rs (i + 1) (acc ++ delimit (pack (unary i) r)) := by
  have hf : (r :: rs).flatMap delimit = pack r (rs.flatMap delimit) := rfl
  have hn : (pack r (rs.flatMap delimit)).isEmpty = false := by cases r <;> rfl
  simp [enumStep, enumState, hf, hn, unary, List.replicate_succ]

private theorem enum_run (N : ℕ) (rs : List Bits) (i : ℕ) (acc : Bits)
    (hr : (rs.flatMap delimit).length ≤ N) (hi : rs.length + i ≤ N)
    (ha : acc.length + rs.length * (6 * N + 3) ≤ N * (6 * N + 3)) :
    Iterates enumStep (4 * N + 2 + N * (6 * N + 3)) (rs.length + 1) (enumState rs i acc)
      (acc ++ (indexed rs i).flatMap delimit) := by
  have bounded : (enumState rs i acc).length ≤ 4 * N + 2 + N * (6 * N + 3) := by
    simp only [enumState, pack, List.length_append, length_delimit, unary_length]
    omega
  induction rs generalizing i acc with
  | nil => simpa [indexed] using Iterates.halt bounded (enum_finished i acc)
  | cons r rs ih =>
    apply Iterates.next bounded (enum_more r rs i acc)
    have hr' : (rs.flatMap delimit).length ≤ N := by
      simp only [List.flatMap_cons, List.length_append] at hr
      omega
    have hi' : rs.length + (i + 1) ≤ N := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hi
    have ha' : (acc ++ delimit (pack (unary i) r)).length + rs.length * (6 * N + 3) ≤
        N * (6 * N + 3) := by
      simp only [List.flatMap_cons, List.length_append, length_delimit] at hr
      simp only [List.length_cons] at hi ha
      rw [Nat.succ_mul rs.length] at ha
      simp only [pack, List.length_append, length_delimit, unary_length]
      omega
    have hb : (enumState rs (i + 1) (acc ++ delimit (pack (unary i) r))).length ≤
        4 * N + 2 + N * (6 * N + 3) := by
      simp only [enumState, pack, List.length_append, length_delimit, unary_length] at *
      omega
    simpa only [indexed, List.zipIdx_cons, List.map_cons, List.flatMap_cons, List.length_cons,
      List.append_assoc] using ih (i + 1) _ hr' hi' ha' hb

/-- Attach the zero-based unary index to each complete input row. -/
theorem polyEnumerate {rows : Bits → Bits} (hr : IsPolyTime rows) :
    IsPolyTime (fun x => (indexed (rowsOf (rows x)) 0).flatMap delimit) := by
  have hs : IsPolyTime (fun x => enumState (rowsOf (rows x)) 0 []) :=
    polyPack (polyNormalizeRows hr) (polyConst (pack [] []))
  let X : Polynomial ℕ := Polynomial.X
  apply isPolyTime_of_iterates_from hs polyEnumStep (X + 1)
    (4 * X + 2 + X * (6 * X + 3))
  intro x
  let rs := rowsOf (rows x)
  let N := (enumState rs 0 []).length
  have hl : (rs.flatMap delimit).length ≤ N := by
    simp only [N, enumState, pack, List.length_append, length_delimit]
    omega
  have hc := (call_count rs).trans hl
  have h := enum_run N rs 0 [] hl (by simpa using hc)
    (by simpa using Nat.mul_le_mul_right (6 * N + 3) hc)
  exact ⟨rs.length + 1, by simpa [X, N, rs] using Nat.add_le_add_right hc 1,
    by simpa [X, N, rs] using h⟩

end Cslib.Complexity.PolynomialEncoding.Comprehension
