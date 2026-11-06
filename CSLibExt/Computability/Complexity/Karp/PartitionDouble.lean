/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Host
public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2

/-!
# Streaming doubling of the PARTITION number list

A finite-state pass adds a low zero bit to every nonempty canonical
payload. Empty payloads (zero) remain empty. This is a bit-level operation,
not a loop bounded by the represented natural number.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Partition.DoubleStream

open BitstringEncoding Computability

/-- **Scan phases of the PARTITION doubling pass.**
Reading the first marker, a later marker, or a payload bit. -/
inductive Phase | start | marker | payload
  deriving DecidableEq

/-- **Phase transition of the PARTITION doubling pass.** Phase after reading one input bit. -/
def next : Phase → Bool → Phase
  | .payload, _ => .marker
  | _, b => if b then .payload else .start

/-- **Output bits per input bit in the doubling pass.**
Output bits for one input bit; at a nonzero block prepend its low zero. -/
def chunk : Phase → Bool → List Bool
  | .start, true => [true, false, true]
  | _, b => [b]

/-- **Finite-state doubling pass on raw bitstrings.**
The raw finite-state pass. Malformed strings have a total output too;
validation belongs to the preceding canonical decoder. -/
def transform : Phase → List Bool → List Bool
  | _, [] => []
  | q, b :: x => chunk q b ++ transform (next q b) x

private theorem marker_delimit (p rest : List Bool) :
    transform .marker (delimit p ++ rest) =
      delimit p ++ transform .start rest := by
  induction p with
  | nil => rfl
  | cons b p ih => simp [delimit, transform, chunk, next, ih]

private theorem encode_double {n : ℕ} (hn : n ≠ 0) :
    encodeNat (n * 2) = false :: encodeNat n := by
  rw [TM2Recursive.encodeNat_eq_cons (by omega : n * 2 ≠ 0)]
  simp

/-- **Doubling pass maps a number block to the block of its double.**
A canonical number block becomes the canonical block of its double. -/
theorem transform_block (n : ℕ) (rest : List Bool) :
    transform .start (delimit (encodeNat n) ++ rest) =
      delimit (encodeNat (n * 2)) ++ transform .start rest := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · rw [encode_double hn]
    cases hp : encodeNat n with
    | nil =>
      have h := decode_encodeNat n
      rw [hp] at h
      exact (hn h.symm).elim
    | cons b p =>
      simp [delimit, transform, chunk, next, marker_delimit]

/-- **Doubling pass doubles every number in a list.**
The stream pass doubles every number and preserves list multiplicity. -/
theorem transform_nums (as : List ℕ) :
    transform .start (as.flatMap fun n => delimit (encodeNat n)) =
      (as.map (· * 2)).flatMap fun n => delimit (encodeNat n) := by
  induction as with
  | nil => rfl
  | cons n as ih =>
    simp only [List.flatMap_cons, transform_block, List.map_cons, ih]

open Turing Function TM2Program

/-- **Stacks of the PARTITION doubling machine.**
Input, reversed output, and output stacks of the doubling pass. -/
inductive K | X | R | O
  deriving DecidableEq

instance : Fintype K := Fintype.ofList [.X, .R, .O]
  (fun k => by cases k <;> simp)

/-- **Control labels of the PARTITION doubling machine.**
Three scan phases followed by reversal and a halting continuation. -/
inductive Lab | scan (q : Phase) | emit | done
  deriving DecidableEq

instance : Fintype Lab :=
  Fintype.ofList [.scan .start, .scan .marker, .scan .payload, .emit, .done]
    (fun l => by cases l with
      | scan q => cases q <;> simp
      | emit => simp
      | done => simp)

/-- **Program of the PARTITION doubling machine.** Finite-stack implementation of `transform`. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .scan q =>
    .peek .X (fun _ o => o.isNone) <| .branch id
      (.goto fun _ => .emit)
      (.pop .X (fun _ o => o.getD false) <| .branch id
        (TM2Program.emit .R (chunk q true) (.scan (next q true)))
        (TM2Program.emit .R (chunk q false) (.scan (next q false))))
  | .emit => moveB .R .O some id .emit .done
  | .done => .halt

private def st (x r o : List Bool) : K → List Bool
  | .X => x | .R => r | .O => o

@[simp] private theorem st_update_X (x r o l : List Bool) :
    update (st x r o) .X l = st l r o := by
  funext k
  cases k <;> rfl

@[simp] private theorem st_update_R (x r o l : List Bool) :
    update (st x r o) .R l = st x l o := by
  funext k
  cases k <;> rfl

@[simp] private theorem st_update_O (x r o l : List Bool) :
    update (st x r o) .O l = st x r l := by
  funext k
  cases k <;> rfl

private theorem scan_run (x : List Bool) :
    ∀ (q : Phase) (v : Bool) (r o : List Bool),
      Run prog (x.length + 1) ⟨some (.scan q), v, st x r o⟩
        ⟨some .emit, true, st [] ((transform q x).reverse ++ r) o⟩ := by
  induction x with
  | nil =>
    intro q v r o
    exact Run.single (by simp [prog, TM2.stepAux, st, transform])
  | cons b x ih =>
    intro q v r o
    have h := ih (next q b) b ((chunk q b).reverse ++ r) o
    simp only [transform, List.reverse_append, List.append_assoc]
    refine Run.head ?_ h
    cases b <;> simp [TM2.step, prog, TM2.stepAux, TM2Program.emit,
      stepAux_pushList, st]

private theorem emit_run (r : List Bool) :
    ∀ (o : List Bool) (v : Bool),
      Run prog (r.length + 1) ⟨some .emit, v, st [] r o⟩
        ⟨some .done, false, st [] [] (r.reverse ++ o)⟩ := by
  induction r with
  | nil =>
    intro o v
    exact Run.single (by
      simp [prog, moveB, TM2.stepAux, isBit, st]
      rfl)
  | cons b r ih =>
    intro o v
    have h := ih (b :: o) b
    simp only [List.reverse_cons, List.append_assoc,
      List.singleton_append]
    refine Run.head ?_ h
    cases b <;>
      simp [TM2.step, prog, moveB, TM2.stepAux, isBit, bitOf, st] <;> rfl

private theorem transform_length (q : Phase) (x : List Bool) :
    (transform q x).length ≤ 3 * x.length := by
  induction x generalizing q with
  | nil => simp [transform]
  | cons b x ih =>
    have h := ih (next q b)
    have hc : (chunk q b).length ≤ 3 := by
      cases q <;> cases b <;> decide
    simp only [transform, List.length_append, List.length_cons]
    omega

/-- **Linear step bound for the PARTITION doubling machine.**
The complete pass takes at most `4 * input.length + 2` steps. -/
theorem run (x : List Bool) (v₀ : Bool := false) :
    ∃ v S', RunLe prog (4 * x.length + 2)
      ⟨some (.scan .start), v₀, update (fun _ => []) .X x⟩
      ⟨some .done, v, S'⟩ ∧ S' .O = transform .start x := by
  have h₁ := scan_run x .start v₀ [] []
  have h₂ := emit_run (transform .start x).reverse [] true
  simp only [List.append_nil, List.reverse_reverse,
    List.length_reverse] at h₁ h₂
  have hi : update (fun _ : K => []) .X x = st x [] [] := by
    funext k
    cases k <;> simp [st]
  rw [hi]
  refine ⟨false, st [] [] (transform .start x), ?_, rfl⟩
  exact (h₁.trans h₂).le (by have := transform_length .start x; omega)

/-- **PARTITION doubling machine as a host component.**
The doubling transducer as a finite component for the canonical host. -/
abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := [.X, .R, .O]
  ks_nodup := by decide
  mem_ks k := by cases k <;> simp

/-- **PARTITION doubling pass is polynomial-time.**
Polynomial time in the canonical bitstring encoding, from the actual
finite-state machine, including malformed raw strings. -/
theorem isPolyTime_transform : ComplexityTheory.IsPolyTime (transform .start) :=
  Cslib.Complexity.Host.isPolyTime_reduction
    (c := comp) (cX := .X) (cO := .O) (gX := id)
    (start := .scan .start) (done := .done) (Equiv.refl Bool)
    (transform .start) (Polynomial.C 4 * Polynomial.X + Polynomial.C 2)
    rfl fun x => by
      simpa using run x

end MetaMathlibExt.Complexity.NPComplete.Partition.DoubleStream
