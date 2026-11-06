/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.FramedCNF.Normalize
public import CSLibExt.Computability.Complexity.Host

/-!
# A linear-time machine for total binary-payload normalization

The machine reads the payload onto a reverse buffer, remembers its last
bit, appends the implicit terminal one if needed, and reverses the buffer
onto the output. No decoded numeric value is used as a loop bound.
-/

@[expose] public section

namespace Cslib.Complexity.FramedCNF.NormalizeMachine

open Turing Function MetaMathlibExt.TM2Program

/-- **Stacks of the payload normalizer machine.** Input, reverse buffer, and output. -/
inductive K | input | buffer | output
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.input, .buffer, .output], by decide⟩
  complete k := by cases k <;> decide

/-- **Control labels of the payload normalizer machine.**
The reader records the last payload bit; `none` means empty input. -/
inductive Lab | read (last : Option Bool) | copy | done
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.read none, .read (some false), .read (some true),
    .copy, .done], by decide⟩
  complete l := by
    rcases l with (_ | (_ | _)) | _ | _ <;> decide

/-- **Program of the payload normalizer machine.**
Normalization using only Boolean stack symbols and finite control. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .read last =>
    .peek .input (fun _ o => o.isSome) <| .branch id
      (.pop .input (fun _ o => o.getD false) <|
        .push .buffer id <| .goto fun b => .read (some b))
      (if last = some false then
        .push .buffer (fun _ => true) (.goto fun _ => .copy)
       else .goto fun _ => .copy)
  | .copy => moveB .buffer .output some id .copy .done
  | .done => .halt

/-- **Stack contents for the payload normalizer invariant.**
The three stack contents used in the run invariant. -/
def st (input buffer output : List Bool) : K → List Bool
  | .input => input
  | .buffer => buffer
  | .output => output

private theorem read_step (b : Bool) (xs pre out : List Bool)
    (last : Option Bool) (v : Bool) :
    Run prog 1 ⟨some (.read last), v, st (b :: xs) pre out⟩
      ⟨some (.read (some b)), b, st xs (b :: pre) out⟩ := by
  apply Run.single
  simp only [prog, TM2.stepAux, st, List.head?_cons,
    Option.isSome_some, id_eq, Option.getD_some, List.tail_cons, ne_eq,
    reduceCtorEq, not_false_eq_true, update_of_ne, cond_eq_ite,
    ↓reduceIte, TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> rfl

private theorem read_end (pre out : List Bool) (v : Bool) :
    Run prog 1 ⟨some (.read pre.getLast?), v, st [] pre.reverse out⟩
      ⟨some .copy, false, st [] (normalizeNat pre).reverse out⟩ := by
  apply Run.single
  by_cases h : pre.getLast? = some false
  · simp only [prog, h, ↓reduceIte, TM2.stepAux, st, List.head?_nil,
      Option.isSome_none, id_eq, Option.getD_none, List.tail_nil, ne_eq,
      reduceCtorEq, not_false_eq_true, update_of_ne, cond_eq_ite,
      Bool.false_eq_true, normalizeNat, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, TM2.Cfg.mk.injEq, true_and]
    funext k
    cases k <;> rfl
  · simp [prog, TM2.stepAux, st, normalizeNat, h]

/-- **Read phase of the payload normalizer consumes each bit once.**
The read phase consumes each input bit once and optionally adds the
implicit terminal one. The prefix records already-consumed input. -/
theorem read_run (xs : List Bool) : ∀ (pre out : List Bool) (v : Bool),
    Run prog (xs.length + 1)
      ⟨some (.read pre.getLast?), v, st xs pre.reverse out⟩
      ⟨some .copy, false, st [] (normalizeNat (pre ++ xs)).reverse out⟩ := by
  induction xs with
  | nil =>
    intro pre out v
    simpa using read_end pre out v
  | cons b xs ih =>
    intro pre out v
    have h := ih (pre ++ [b]) out b
    simp only [List.getLast?_append, List.getLast?_singleton,
      List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.append_assoc] at h
    exact ((read_step b xs pre.reverse out pre.getLast? v).trans h).of_eq
      (by simp; omega)

/-- **Linear step bound for the payload normalizer machine.**
The whole component runs in at most `2 |x| + 3` steps. -/
theorem run (x : List Bool) :
    ∃ v S, RunLe prog (2 * x.length + 3)
      ⟨some (.read none), false, st x [] []⟩
      ⟨some .done, v, S⟩ ∧ S .output = normalizeNat x := by
  let y := normalizeNat x
  have r₁ := read_run x [] [] false
  simp only [List.getLast?_nil, List.reverse_nil, List.nil_append] at r₁
  obtain ⟨v, S, r₂, _, hout, _⟩ := moveB_run
    (M := prog) (a := .buffer) (b := .output) (d := some) (g := id)
    (self := .copy) (next := .done) rfl (by decide)
    y.reverse y.reverse [] false (st [] y.reverse [])
    (by simp [st]) rfl rfl
  refine ⟨v, S, ⟨_, ?_, r₁.trans r₂⟩, ?_⟩
  · have h := length_normalizeNat_le x
    simp only [List.length_reverse]
    dsimp [y]
    omega
  · simpa [st, y] using hout

/-- **Payload normalizer as a host component.**
The normalizer in the canonical component interface. -/
abbrev component : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := [.input, .buffer, .output]
  ks_nodup := by decide
  mem_ks k := by cases k <;> decide

/-- **Payload normalization is polynomial-time.**
Total binary-payload normalization is polynomial-time in the
canonical encoded machine model. -/
theorem isPolyTime_normalizeNat :
    MetaMathlibExt.ComplexityTheory.IsPolyTime normalizeNat := by
  apply Host.isPolyTime_reduction (c := component)
    (cX := K.input) (cO := K.output) (gX := id)
    (start := Lab.read none) (done := Lab.done)
    (Equiv.refl Bool) normalizeNat
    (Polynomial.C 2 * Polynomial.X + Polynomial.C 3) rfl
  intro x
  obtain ⟨v, S, hr, ho⟩ := run x
  have hs : update (fun _ => []) K.input x = st x [] [] := by
    funext k
    cases k <;> simp [st]
  refine ⟨v, S, ?_, ?_⟩
  · simpa [hs] using hr
  · simpa using ho

end Cslib.Complexity.FramedCNF.NormalizeMachine
