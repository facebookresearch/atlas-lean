/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.BagPredicates
import CSLibExt.Computability.Complexity.Parameterized.Identity

/-!
# Polynomial-time graph generation for the local assignment tables

For each fixed width the generator enumerates the branch, color and local assignment
rows, tests admissibility, then writes the graph's ordered pairs and its clique parameter.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows

open MetaMathlibExt BitstringEncoding ComplexityTheory Cslib.Complexity
open PolynomialEncoding PolynomialEncoding.Comprehension

local notation "Bits" => List Bool
local notation "N" => (bitEncode (α := ℕ))
local notation "Entry" => (pair N N)
local notation "Lit" => (pair N (fun b : Bool => [b]))
local notation "F" => (frames (frames Lit))
local notation "S" => (frames N)
local notation "A" => (frames Entry)

private abbrev branchRep := Represented.numbered F
private abbrev colorRep := Represented.numbered S
private abbrev rowRep := pair branchRep (pair colorRep A)

private theorem carried {T D : Type} {r : T → Bits} {e : D → Bits} {f : D → T × ℕ}
    (h : Represented e (fun x => Represented.numbered r (f x))) :
    Represented e (fun x => r (f x).1) :=
  (h.after (BitScan.polyField false true)).transport (fun x => tl_pack (unary (f x).2) _)

private theorem label {T D : Type} {r : T → Bits} {e : D → Bits} {f : D → T × ℕ}
    (h : Represented e (fun x => Represented.numbered r (f x))) :
    Represented e (fun x => N (f x).2) := by
  have hidx := (h.after (BitScan.polyField true false)).transport
    (g := fun x => unary (f x).2) (fun x => hd_pack _ (r (f x).1))
  exact (hidx.after isPolyTime_encodeLength).transport (by simp)

private theorem represented_candidates {D : Type} {e : D → Bits}
    {slots values : D → List ℕ} {family : D → List Formula} (width : ℕ)
    (hs : Represented e (fun x => S (slots x))) (hv : Represented e (fun x => S (values x)))
    (hf : Represented e (fun x => frames F (family x))) :
    Represented e (fun x => frames rowRep (candidates width (slots x) (values x) (family x))) := by
  have branches := hf.enumerate
  have colors := (hs.boundedTuples width).enumerate
  have entry := (((Represented.input N).fst e).snd N).packed
    ((Represented.input N).fst (pair N e))
  have choices : Represented e (fun x => frames Entry ((slots x).product (values x))) := by
    apply (hs.flatMapRows ((hv.snd N).mapped
      (body := fun p : ℕ × (ℕ × D) => (p.2.1, p.1)) (t := Entry) entry)).transport
    intro x
    simp [List.product]
  have locals := choices.boundedTuples width
  let branchCtx := pair branchRep e
  let colorCtx := pair colorRep branchCtx
  have branch := (((Represented.input branchRep).fst e).snd colorRep).snd A
  have color := ((Represented.input colorRep).fst branchCtx).snd A
  have item := (Represented.input A).fst colorCtx
  have row := branch.packed (color.packed item)
  exact branches.flatMapRows ((colors.snd branchRep).flatMapRows
    (((locals.snd branchRep).snd colorRep).mapped (t := rowRep)
      (body := fun p : Local × ((List ℕ × ℕ) × ((Formula × ℕ) × D)) => (p.2.2.1, p.2.1, p.1))
      row))

private theorem branchField : Represented rowRep (fun r => branchRep r.1) :=
  (Represented.input branchRep).fst (pair colorRep A)

private theorem colorField : Represented rowRep (fun r => colorRep r.2.1) :=
  ((Represented.input colorRep).fst A).snd branchRep

private theorem assignmentField : Represented rowRep (fun r => A r.2.2) :=
  ((Represented.input A).snd colorRep).snd branchRep

private theorem represented_vertices {D : Type} {e : D → Bits}
    {slots values : D → List ℕ} {family : D → List Formula} (width : ℕ)
    (hs : Represented e (fun x => S (slots x))) (hv : Represented e (fun x => S (values x)))
    (hf : Represented e (fun x => frames F (family x))) :
    Represented e (fun x => frames rowRep (vertices width (slots x) (values x) (family x))) := by
  have rows := represented_candidates width hs hv hf
  exact rows.filtered (represented_allowed (hs.snd rowRep) ((carried colorField).fst e)
    ((carried branchField).fst e) (assignmentField.fst e))

private theorem represented_adjacent {D : Type} (e : D → Bits) :
    Represented (pair rowRep (pair rowRep e)) (fun p => [adjacent p.2.1 p.1]) := by
  let ctx := pair rowRep e
  have idB := label branchField
  have idC := label colorField
  have same := represented_natEq ((idB.fst e).snd rowRep) (idB.fst ctx)
  have diff := (represented_natEq ((idC.fst e).snd rowRep) (idC.fst ctx)).neg
  have agree := represented_agrees ((assignmentField.fst e).snd rowRep) (assignmentField.fst ctx)
  exact ((same.both diff).both agree).transport (by intro p; simp [adjacent, Bool.beq_eq_decide_eq])

/-- At fixed width, computing the graph field of the signed-CNF query takes polynomial time. -/
theorem represented_queryGraph {D : Type} {e : D → Bits}
    {slots values : D → List ℕ} {family : D → List Formula} (d : ℕ)
    (hs : Represented e (fun x => S (slots x))) (hv : Represented e (fun x => S (values x)))
    (hf : Represented e (fun x => frames F (family x))) :
    Represented e (fun x => (query d (slots x) (values x) (family x)).1) :=
  GraphWriter.represented_writeGraph (represented_vertices (max 2 (2 * d)) hs hv hf)
    (represented_adjacent e)

/-- The parameter is written in binary from the number of generated colors. -/
theorem represented_queryParam {D : Type} {e : D → Bits}
    {slots values : D → List ℕ} {family : D → List Formula} (d : ℕ)
    (hs : Represented e (fun x => S (slots x))) :
    Represented e (fun x => N (query d (slots x) (values x) (family x)).2) :=
  (((hs.boundedTuples (max 2 (2 * d))).count).after isPolyTime_encodeLength).transport
    (by simp [query])

/-- Both fields together, with the graph word explicitly framed as a list of bits. -/
theorem represented_query {D : Type} {e : D → Bits}
    {slots values : D → List ℕ} {family : D → List Formula} (d : ℕ)
    (hs : Represented e (fun x => S (slots x))) (hv : Represented e (fun x => S (values x)))
    (hf : Represented e (fun x => frames F (family x))) :
    Represented e (fun x => bitEncode (query d (slots x) (values x) (family x))) := by
  let write (_ : Unit) (b : Bool) : Unit × Bits := ((), [true, b, false])
  have eqn (x : Bits) : BitScan.scan write (fun _ => []) () x = bitEncode x := by
    induction x with
    | nil => rfl
    | cons b xs ih =>
      change true :: b :: false :: BitScan.scan write (fun _ => []) () xs =
        true :: b :: false :: bitEncode xs
      rw [ih]
  have graph := (represented_queryGraph d hs hv hf).after (BitScan.polyScan write (fun _ => []) ())
  exact (graph.transport
    (g := fun x => bitEncode (query d (slots x) (values x) (family x)).1)
    (fun _ => eqn _)).packed (represented_queryParam d hs)

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows
