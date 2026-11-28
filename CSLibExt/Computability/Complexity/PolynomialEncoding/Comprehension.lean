/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts
import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Iteration
public import CSLibExt.Computability.Complexity.PolynomialEncoding.BitOperations

/-!
# Polynomial-time list comprehensions

A comprehension passes each framed row and a read-only environment to a given
polynomial-time function. Its outputs are concatenated. Both the input traversal
and every increment of the output length are bounded on the TM2 model.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.Comprehension

open MetaMathlibExt BitstringEncoding ComplexityTheory TM2Composition BitScan Iteration

local notation "Bits" => List Bool

/-- A self-delimiting first word, followed by the raw second word. -/
def pack (a b : Bits) : Bits := delimit a ++ b

theorem polyPack {f g : Bits → Bits} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => pack (f x) (g x)) := polyAppend (hf.comp polyDelimit) hg

theorem polyConst (s : Bits) : IsPolyTime (fun _ : Bits => s) := by
  let step (_ : Unit) (_ : Bool) : Unit × Bits := ((), [])
  have h (x : Bits) : scan step (fun _ => s) () x = s := by
    induction x with
    | nil => rfl
    | cons b x ih => simpa [scan, step] using ih
  exact (funext h) ▸ polyScan step (fun _ => s) ()

private def selectStep : Option (Bool × Option Bool) → Bool → Option (Bool × Option Bool) × Bits
  | none, b => (some (b, some false), [])
  | some (b, q), a =>
    let p := splitStep b (!b) q a
    (some (b, p.1), p.2)

private theorem select_tail (b : Bool) (q : Option Bool) (x : Bits) :
    scan selectStep (fun _ => []) (some (b, q)) x =
      scan (splitStep b (!b)) (fun _ => []) q x := by
  induction x generalizing q with
  | nil => rfl
  | cons a x ih => simp [scan, selectStep, ih]

private theorem select_tag (b : Bool) (y n : Bits) :
    scan selectStep (fun _ => []) none (b :: pack y n) = if b then y else n := by
  simp only [scan, selectStep, List.nil_append, select_tail]
  change field b (!b) (delimit y ++ n) = _
  rw [field_delimit]
  cases b <;> simp

/-- Select between two computed bitstrings on a computed one-bit test. -/
theorem polyIf {pred : Bits → Bool} {yes no : Bits → Bits}
    (ht : IsPolyTime (fun x => [pred x])) (hy : IsPolyTime yes) (hn : IsPolyTime no) :
    IsPolyTime (fun x => if pred x then yes x else no x) := by
  have h := (polyAppend ht (polyPack hy hn)).comp (polyScan selectStep (fun _ => []) none)
  simpa only [Function.comp_def, List.singleton_append, select_tag] using h

/-- The Boolean test for an empty bitstring, written as one output bit. -/
theorem polyEmpty : IsPolyTime (fun x : Bits => [x.isEmpty]) := by
  let step (_ : Bool) (_ : Bool) : Bool × Bits := (false, [])
  have h (x : Bits) (q : Bool) : scan step (fun b => [b]) q x = [q && x.isEmpty] := by
    induction x generalizing q with
    | nil => simp [scan]
    | cons b x ih => simp [scan, step, ih]
  have eqn : scan step (fun b => [b]) true = fun x => [x.isEmpty] := by
    funext x
    simp [h]
  exact eqn ▸ polyScan step (fun b => [b]) true

abbrev hd := field true false
abbrev tl := field false true

@[simp] theorem hd_pack (a b : Bits) : hd (pack a b) = a := by simp [hd, pack, field_delimit]
@[simp] theorem tl_pack (a b : Bits) : tl (pack a b) = b := by simp [tl, pack, field_delimit]

/-- Encoded initial state for a comprehension over framed rows and an environment. -/
def state (rows : List Bits) (ctx acc : Bits) := pack (rows.flatMap delimit) (pack ctx acc)

private def step (emit : Bits → Bits) (s : Bits) : Bits :=
  let rows := hd s
  let ctx := hd (tl s)
  let acc := tl (tl s)
  if rows.isEmpty then false :: acc
  else true :: pack (tl rows) (pack ctx (acc ++ emit (pack (hd rows) ctx)))

private theorem polyStep {emit : Bits → Bits} (he : IsPolyTime emit) : IsPolyTime (step emit) := by
  have hhd := polyField true false
  have htl := polyField false true
  have hctx := htl.comp hhd
  have hacc := htl.comp htl
  have body := (polyPack (hhd.comp hhd) hctx).comp he
  exact polyIf (hhd.comp polyEmpty) (polyAppend (polyConst [false]) hacc)
    (polyAppend (polyConst [true])
      (polyPack (hhd.comp htl) (polyPack hctx (polyAppend hacc body))))

private theorem step_finished (emit : Bits → Bits) (ctx acc : Bits) :
    step emit (state [] ctx acc) = false :: acc := by
  simp [step, state, hd_pack, tl_pack]

private theorem step_more (emit : Bits → Bits) (r : Bits) (rs : List Bits) (ctx acc : Bits) :
    step emit (state (r :: rs) ctx acc) =
      true :: state rs ctx (acc ++ emit (pack r ctx)) := by
  have hn : (pack r (rs.flatMap delimit)).isEmpty = false := by
    cases r <;> rfl
  have hs : (r :: rs).flatMap delimit = pack r (rs.flatMap delimit) := rfl
  simp [step, state, hd_pack, tl_pack, hs, hn]

private theorem state_length (rs : List Bits) (ctx acc : Bits) :
    (state rs ctx acc).length = (state rs ctx []).length + acc.length := by
  simp [state, pack, length_delimit]
  omega

private theorem room_tail (r : Bits) (rs : List Bits) (ctx : Bits) :
    (state rs ctx []).length ≤ (state (r :: rs) ctx []).length := by
  simp only [state, pack, length_delimit, List.length_append, List.flatMap_cons]
  omega

theorem call_count (rs : List Bits) : rs.length ≤ (rs.flatMap delimit).length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.length_cons, List.length_append, length_delimit]
    omega

theorem row_length (rs : List Bits) {r : Bits} (hr : r ∈ rs) :
    (delimit r).length ≤ (rs.flatMap delimit).length := by
  induction rs with
  | nil => simp at hr
  | cons s rs ih =>
    simp only [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hr with rfl | h
    · omega
    · exact (ih h).trans (by omega)

private theorem collect_run (emit : Bits → Bits) (N cap : ℕ) (rs : List Bits) (ctx acc : Bits)
    (hroom : (state rs ctx []).length ≤ N)
    (hacc : acc.length + rs.length * cap ≤ N * cap)
    (hrow : ∀ r ∈ rs, (emit (pack r ctx)).length ≤ cap) :
    Iterates (step emit) (N + N * cap) (rs.length + 1) (state rs ctx acc)
      (acc ++ rs.flatMap (fun r => emit (pack r ctx))) := by
  have bounded : (state rs ctx acc).length ≤ N + N * cap := by
    rw [state_length]
    omega
  induction rs generalizing acc with
  | nil =>
    simpa using Iterates.halt bounded (step_finished emit ctx acc)
  | cons r rs ih =>
    apply Iterates.next bounded (step_more emit r rs ctx acc)
    have ht := (room_tail r rs ctx).trans hroom
    have he := hrow r List.mem_cons_self
    have ha : (acc ++ emit (pack r ctx)).length + rs.length * cap ≤ N * cap := by
      simp only [List.length_cons, Nat.succ_mul] at hacc
      simp only [List.length_append]
      omega
    simpa only [List.length_cons, List.flatMap_cons, List.append_assoc] using
      ih (acc ++ emit (pack r ctx)) ht ha
        (fun u hu => hrow u (List.mem_cons_of_mem _ hu))
        (by rw [state_length]; omega)

/-- Concatenating the results of one polynomial-time computation per row is polynomial time.
The initialization supplies framed rows together with a read-only environment. -/
theorem polyCollect {α : Type} [BitstringEncoding α] {rows : α → List Bits} {ctx : α → Bits}
    {emit : Bits → Bits} (hi : IsPolyTime (fun a => state (rows a) (ctx a) []))
    (he : IsPolyTime emit) :
    IsPolyTime (fun a => (rows a).flatMap (fun r => emit (pack r (ctx a)))) := by
  obtain ⟨p, hp⟩ := he.length_bound
  apply isPolyTime_of_iterates_from hi (polyStep he) (Polynomial.X + 1)
    (Polynomial.X + Polynomial.X * p)
  intro a
  let rs := rows a
  let c := ctx a
  let N := (state rs c []).length
  have hrows : rs.length ≤ N := (call_count rs).trans (by
    simp only [N, state, pack, List.length_append, length_delimit]
    omega)
  have hr (r : Bits) (h : r ∈ rs) : (emit (pack r c)).length ≤ p.eval N := by
    apply (hp _).trans (eval_mono _ ?_)
    have hl := row_length rs h
    simp only [pack, List.length_append, N, state, length_delimit] at *
    omega
  refine ⟨rs.length + 1, by simpa [N, rs, c] using Nat.add_le_add_right hrows 1, ?_⟩
  simpa [N, rs, c] using collect_run emit N (p.eval N) rs c [] le_rfl
    (by simpa using Nat.mul_le_mul_right (p.eval N) hrows) hr


private def frameStep (q : Option Bool) (b : Bool) : Option Bool × Bits :=
  (if q == some true then some false else if b then some true else none, [])

private def frameFinish (q : Option Bool) : Bits := [q.isNone]
private def inside (b : Bool) : Option Bool := if b then some false else none

private theorem scan_frame (p r : Bits) (q : Bool) :
    scan frameStep frameFinish (inside q) (delimit p ++ r) =
      scan frameStep frameFinish none r := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons b p ih => cases q <;> exact ih true

private theorem scan_incomplete (x : Bits) (q : Bool) (hx : undelimit x = none)
    (hn : x ≠ [] ∨ q = true) : scan frameStep frameFinish (inside q) x = [false] := by
  match x with
  | [] =>
    have := hn.resolve_left (by simp)
    subst q
    rfl
  | false :: _ => simp [undelimit] at hx
  | [true] => cases q <;> rfl
  | true :: b :: rest =>
    have hu : undelimit rest = none := by cases h : undelimit rest <;> simp_all [undelimit]
    have hr := scan_incomplete rest true hu (Or.inr rfl)
    cases q <;> exact hr
termination_by x.length

private theorem scan_complete (x : Bits) :
    scan frameStep frameFinish none x = [(undelimitBlocks x).isSome] := by
  cases x with
  | nil => rfl
  | cons b xs =>
    cases hu : undelimit (b :: xs) with
    | none =>
      have he : undelimitBlocks (b :: xs) = none := by
        simp [undelimitBlocks, undelimitBlocksAux, hu]
      rw [he]
      exact scan_incomplete (b :: xs) false hu (Or.inl (by simp))
    | some a =>
      obtain ⟨p,r⟩ := a
      have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
      have ht : r.length < (b :: xs).length := by rw [hx, List.length_append, length_delimit]; omega
      change scan frameStep frameFinish (inside false) _ = _
      rw [hx, blocks_delimit, scan_frame]
      simpa using scan_complete r
termination_by x.length

/-- Test whether every row of a bitstring is a complete frame, accepting the empty list. -/
theorem polyFramesValid : IsPolyTime (fun x : Bits => [(undelimitBlocks x).isSome]) :=
  (funext scan_complete) ▸ polyScan frameStep frameFinish none

private theorem rows_reencode (x : Bits) (rs : List Bits) (hr : undelimitBlocks x = some rs) :
    rs.flatMap delimit = x := by
  cases x with
  | nil => change some [] = some rs at hr; cases hr; rfl
  | cons b xs =>
    cases hu : undelimit (b :: xs) with
    | none => simp [undelimitBlocks, undelimitBlocksAux, hu] at hr
    | some a =>
      obtain ⟨p,r⟩ := a
      have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
      have ht : r.length < (b :: xs).length := by rw [hx, List.length_append, length_delimit]; omega
      rw [hx, blocks_delimit] at hr
      obtain ⟨zs, hz, rfl⟩ := Option.map_eq_some_iff.mp hr
      rw [List.flatMap_cons, rows_reencode r zs hz, hx]
termination_by x.length

/-- Decode a sequence of complete frames, treating an incomplete sequence as empty. -/
def rowsOf (x : Bits) := (undelimitBlocks x).getD []

@[simp] theorem rowsOf_frames (r : List Bits) : rowsOf (r.flatMap delimit) = r := by
  have h := undelimitBlocks_flatten_delimit r
  simpa [rowsOf, List.flatMap_def] using congrArg (fun o : Option (List Bits) => o.getD []) h

theorem polyNormalizeRows {rows : Bits → Bits} (hrows : IsPolyTime rows) :
    IsPolyTime (fun x => (rowsOf (rows x)).flatMap delimit) := by
  have normal := polyIf (hrows.comp polyFramesValid) hrows (polyConst [])
  have hh : (fun x => if (undelimitBlocks (rows x)).isSome then rows x else []) =
      fun x => (rowsOf (rows x)).flatMap delimit := by
    funext x
    cases hu : undelimitBlocks (rows x) with
    | none => simp [rowsOf, hu]
    | some r => simpa [rowsOf, hu] using (rows_reencode _ r hu).symm
  exact hh ▸ normal

/-- The flat-map rule on raw bitstrings can be nested. The row function receives a framed row
followed by the environment. An incomplete sequence of outer frames yields an empty output. -/
theorem polyFlatMap {rows ctx emit : Bits → Bits} (hrows : IsPolyTime rows)
    (hctx : IsPolyTime ctx) (he : IsPolyTime emit) :
    IsPolyTime (fun x => (rowsOf (rows x)).flatMap (fun r => emit (pack r (ctx x)))) := by
  apply polyCollect (rows := fun x => rowsOf (rows x)) (ctx := ctx) _ he
  exact polyPack (polyNormalizeRows hrows) (polyPack hctx (polyConst []))

end Cslib.Complexity.PolynomialEncoding.Comprehension
