/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.DenseSATVerifier

/-!
# From the canonical pair encoding to the `w # y` form

formal-math's `MetaMathlibExt.ComplexityTheory.NP` hands a verifier the canonical
`BitstringEncoding` of a pair `(x, w) : List Bool × List Bool`:

* the pair is `delimit (bitEncode x) ++ bitEncode w`;
* `bitEncode` of a bit list writes each bit `b` as the block `delimit [b] = [true, b, false]`;
* `delimit` doubles every bit (`c ↦ [true, c]`) and appends `false`.

So each bit of `x` takes six input symbols `[true, true, true, b, true, false]`, a single `false`
ends `x`, and each bit of `w` takes three symbols `[true, b, false]`
(`bitEncode_pair_eq`). The verifier machine of
`CSLibExt.Computability.Complexity.DenseSATVerifier` instead reads
`Verifier.pairEncode (x, w) = x.map inl ++ inr none :: w.map (inr ∘ some)`.

This module gives an explicit `Turing.FinTM2`, `Converter.tm`, that rewrites the first form into
the second in `2 |x| + 2 |w| + 5` steps (`Converter.computable`). It reads `x` (one six-symbol
block per step) onto a stash, reads `w` (one three-symbol block per step) onto a second stash,
then pops the stashes onto the output stack, `w` first, so that both come out in order.
-/

@[expose] public section

namespace Cslib.Complexity.DenseSAT.Converter

open Turing Function MetaMathlibExt

/-! ### The canonical encoding of a pair of bit lists -/

/-- **Converter encoding of the first component.** For a bit list $x$, the bit list obtained by
replacing every bit $b$ of $x$, in order, with the six bits true, true, true, $b$, true, false. -/
def encFst (x : List Bool) : List Bool := x.flatMap fun b => [true, true, true, b, true, false]

/-- **Converter encoding of the second component.** For a bit list $w$, the bit list obtained by
replacing every bit $b$ of $w$, in order, with the three bits true, $b$, false. -/
def encSnd (w : List Bool) : List Bool := w.flatMap fun b => [true, b, false]

theorem delimit_eq (l : List Bool) :
    BitstringEncoding.delimit l = l.flatMap (fun c => [true, c]) ++ [false] := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [BitstringEncoding.delimit, ih]

theorem bitEncode_list (x : List Bool) : BitstringEncoding.bitEncode x = encSnd x := by
  change (((x.map BitstringEncoding.bitEncode).map BitstringEncoding.delimit).flatten) = _
  induction x with
  | nil => rfl
  | cons b x ih =>
      simp only [List.map_cons, List.flatten_cons, encSnd, List.flatMap_cons] at ih ⊢
      rw [ih]
      rfl

theorem flatMap_delimit_encSnd (x : List Bool) :
    (encSnd x).flatMap (fun c => [true, c]) = encFst x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      simp only [encSnd, encFst, List.flatMap_cons, List.flatMap_append] at ih ⊢
      rw [ih]
      rfl

/-- **Canonical encoding of a pair of bit lists.** For bit lists $x$ and $w$, the canonical
bitstring encoding of the pair $(x, w)$ is the concatenation of three parts: every bit $b$ of $x$,
in order, written as the six bits true, true, true, $b$, true, false; then a single false; then
every bit $b$ of $w$, in order, written as the three bits true, $b$, false. -/
theorem bitEncode_pair_eq (x w : List Bool) :
    (BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode (x, w) =
      encFst x ++ false :: encSnd w := by
  change BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++
      BitstringEncoding.bitEncode w = _
  rw [bitEncode_list, bitEncode_list, delimit_eq, flatMap_delimit_encSnd]
  simp

/-! ### The machine -/

/-- **Stacks of the pair-encoding converter.** The machine that rewrites the canonical encoding
of a pair of bit lists into the verifier's input form has four stacks: the input stack, the
output stack, and two stash stacks, one for each component of the pair. -/
inductive Stk | inp | out | fst | snd
  deriving DecidableEq

instance : Fintype Stk where
  elems := ⟨↑[Stk.inp, Stk.out, Stk.fst, Stk.snd], by decide⟩
  complete := fun k => by cases k <;> decide

/-- **Stack alphabets of the pair-encoding converter.** The output stack of the converter has as
its alphabet the verifier's work alphabet $G = \{0,1\} \sqcup (\{0,1\} \cup \{\#\})$; the input
stack and the two stash stacks have the bits $\{0,1\}$ as their alphabet. -/
@[reducible] def Γ : Stk → Type
  | .out => Verifier.G
  | _ => Bool

/-- **Labels of the pair-encoding converter.** The five labels of the converter program: read the
first component, read the second component, emit the second component, emit the separator, and
emit the first component. -/
inductive Lab | readFst | readSnd | emitSnd | sep | emitFst
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.readFst, Lab.readSnd, Lab.emitSnd, Lab.sep, Lab.emitFst], by decide⟩
  complete := fun l => by cases l <;> decide

/-- **State of the pair-encoding converter.** The internal state of the converter is an optional
bit: either a bit or nothing. It records the last bit the program stored. -/
abbrev St := Option Bool

/-- **Program of the pair-encoding converter.** The program over the converter's four stacks,
five labels and states (a bit or nothing). Each pop either stores the popped bit in the state
(nothing if the stack is empty) or leaves the state unchanged, and each push of the stored bit
uses false when the state holds nothing.

At *read first*: pop the input, storing; if the state is true, pop the input twice without
storing, once storing and twice without storing, push the stored bit onto the first stash and go
to *read first*; otherwise go to *read second*. At *read second*: pop the input, storing; if the
state is true, pop the input once storing and once without storing, push the stored bit onto the
second stash and go to *read second*; otherwise go to *emit second*. At *emit second*: pop the
second stash, storing; if a bit was popped, push it onto the output as a right-tagged bit and go
to *emit second*; otherwise go to *separator*. At *separator*: push the separator onto the
output and go to *emit first*. At *emit first*: pop the first stash, storing; if a bit was
popped, push it onto the output as a left-tagged bit and go to *emit first*; otherwise halt. -/
def prog : Lab → TM2.Stmt Γ Lab St
  | .readFst =>
      .pop .inp (fun _ o => o) <| .branch (fun s => s == some true)
        (.pop .inp (fun s _ => s) <| .pop .inp (fun s _ => s) <| .pop .inp (fun _ o => o) <|
          .pop .inp (fun s _ => s) <| .pop .inp (fun s _ => s) <|
          .push .fst (fun s => s.getD false) <| .goto fun _ => .readFst)
        (.goto fun _ => .readSnd)
  | .readSnd =>
      .pop .inp (fun _ o => o) <| .branch (fun s => s == some true)
        (.pop .inp (fun _ o => o) <| .pop .inp (fun s _ => s) <|
          .push .snd (fun s => s.getD false) <| .goto fun _ => .readSnd)
        (.goto fun _ => .emitSnd)
  | .emitSnd =>
      .pop .snd (fun _ o => o) <| .branch (fun s => s.isSome)
        (.push .out (fun s => .inr (some (s.getD false))) <| .goto fun _ => .emitSnd)
        (.goto fun _ => .sep)
  | .sep => .push .out (fun _ => .inr none) <| .goto fun _ => .emitFst
  | .emitFst =>
      .pop .fst (fun _ o => o) <| .branch (fun s => s.isSome)
        (.push .out (fun s => .inl (s.getD false)) <| .goto fun _ => .emitFst)
        .halt

/-- **The pair-encoding converter machine.** The converter is the finite multi-stack Turing
machine whose stacks are the input stack, the output stack and the two stash stacks, with bits
as the alphabet of every stack except the output stack, which holds the verifier's symbols. Its
labels are the five phases (read the first component, read the second, emit the second, emit
the separator, emit the first), and it starts in the phase that reads the first component. Its
internal state is an optional bit (the last bit popped), initially empty, and it runs the
converter program. Input is read from the input stack, which holds bits, and output is written
to the output stack. -/
def tm : FinTM2 where
  K := Stk
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := Lab
  main := .readFst
  σ := St
  initialState := none
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := prog

/-! ### Configurations and runs -/

/-- **Stack contents of the pair-encoding converter.** For bit lists $i$, $a$, $b$ and a list $o$ of
verifier symbols, the contents of the converter's four stacks with $i$ on the input stack, $o$ on
the output stack, $a$ on the first stash and $b$ on the second stash. -/
def stk (i : List Bool) (o : List Verifier.G) (a b : List Bool) : ∀ k, List (Γ k)
  | .inp => i
  | .out => o
  | .fst => a
  | .snd => b

@[simp] theorem update_stk_inp (i : List Bool) (o : List Verifier.G) (a b l : List Bool) :
    update (stk i o a b) .inp l = stk l o a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_out (i : List Bool) (o : List Verifier.G) (a b : List Bool)
    (l : List Verifier.G) : update (stk i o a b) .out l = stk i l a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_fst (i : List Bool) (o : List Verifier.G) (a b l : List Bool) :
    update (stk i o a b) .fst l = stk i o l b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_snd (i : List Bool) (o : List Verifier.G) (a b l : List Bool) :
    update (stk i o a b) .snd l = stk i o a l := by
  funext k; cases k <;> rfl

/-- **Runs of the pair-encoding converter.** For $n \in \mathbb{N}$ and configurations $c$ and $d$
of the converter, the statement that $n$ steps of the converter program lead from $c$ to $d$. -/
abbrev Run (n : ℕ) (c d : TM2.Cfg Γ Lab St) : Prop := TM2Program.Run prog n c d

theorem readFst_run (x : List Bool) :
    ∀ (rest : List Bool) (o : List Verifier.G) (a b : List Bool) (v : St),
      Run (x.length + 1) ⟨some .readFst, v, stk (encFst x ++ false :: rest) o a b⟩
        ⟨some .readSnd, some false, stk rest o (x.reverse ++ a) b⟩ := by
  induction x with
  | nil =>
      intro rest o a b v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, encFst])
  | cons c x ih =>
      intro rest o a b v
      have h := ih rest o (c :: a) b (some c)
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, encFst]

theorem readSnd_run (w : List Bool) :
    ∀ (o : List Verifier.G) (a b : List Bool) (v : St),
      Run (w.length + 1) ⟨some .readSnd, v, stk (encSnd w) o a b⟩
        ⟨some .emitSnd, none, stk [] o a (w.reverse ++ b)⟩ := by
  induction w with
  | nil =>
      intro o a b v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, encSnd])
  | cons c w ih =>
      intro o a b v
      have h := ih o a (c :: b) (some c)
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, encSnd]

theorem emitSnd_run (b : List Bool) :
    ∀ (o : List Verifier.G) (a : List Bool) (v : St),
      Run (b.length + 1) ⟨some .emitSnd, v, stk [] o a b⟩
        ⟨some .sep, none, stk [] (b.reverse.map (fun c => .inr (some c)) ++ o) a []⟩ := by
  induction b with
  | nil =>
      intro o a v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk])
  | cons c b ih =>
      intro o a v
      have h := ih (.inr (some c) :: o) a (some c)
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk]

theorem sep_run (o : List Verifier.G) (a : List Bool) :
    Run 1 ⟨some .sep, none, stk [] o a []⟩ ⟨some .emitFst, none, stk [] (.inr none :: o) a []⟩ :=
  TM2Program.Run.single (by simp [prog, TM2.stepAux, stk])

theorem emitFst_run (a : List Bool) :
    ∀ (o : List Verifier.G) (v : St),
      Run (a.length + 1) ⟨some .emitFst, v, stk [] o a []⟩
        ⟨none, none, stk [] (a.reverse.map Sum.inl ++ o) [] []⟩ := by
  induction a with
  | nil =>
      intro o v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk])
  | cons c a ih =>
      intro o v
      have h := ih (.inl c :: o) (some c)
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk]

/-- **Full run of the pair-encoding converter.** For bit lists $x$ and $w$, the converter program
goes in exactly $2|x| + 2|w| + 5$ steps from the configuration at the label *read first*, with
no bit in the state, the input stack holding every bit $b$ of $x$ in order as the six bits true,
true, true, $b$, true, false, then a single false, then every bit $b$ of $w$ in order as the three
bits true, $b$, false, and the other three stacks empty, to the halted configuration with no bit
in the state, the verifier's pair encoding of $(x, w)$ on the output stack and the other three
stacks empty. -/
theorem convert_run (x w : List Bool) :
    Run (2 * x.length + 2 * w.length + 5)
      ⟨some .readFst, none, stk (encFst x ++ false :: encSnd w) [] [] []⟩
      ⟨none, none, stk [] (Verifier.pairEncode (x, w)) [] []⟩ := by
  have h₁ := readFst_run x (encSnd w) [] [] [] none
  have h₂ := readSnd_run w [] (x.reverse ++ []) [] (some false)
  have h₃ := emitSnd_run (w.reverse ++ []) [] (x.reverse ++ []) none
  have h₄ := sep_run ((w.reverse ++ []).reverse.map (fun c => .inr (some c)) ++ [])
    (x.reverse ++ [])
  have h₅ := emitFst_run (x.reverse ++ [])
    (.inr none :: ((w.reverse ++ []).reverse.map (fun c => .inr (some c)) ++ [])) none
  have h := h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
  exact h.of_eq (by omega)

theorem initList_tm (l : List Bool) :
    initList tm l = ⟨some .readFst, none, stk l [] [] []⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_tm (l : List Verifier.G) : haltList tm l = ⟨none, none, stk [] l [] []⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

/-- **Polynomial-time conversion to the verifier's pair encoding.** A polynomial-time computation
of the identity map on pairs $(x, w)$ of bit lists, from the canonical bitstring encoding of
$(x, w)$ to the verifier's pair encoding of $(x, w)$ (the bits of $x$, the separator, then the
bits of $w$), by the converter machine, with the bits and the verifier's symbols themselves as
input and output alphabets and time bound $n + 5$: started on the canonical encoding of $(x, w)$,
a list of length $n$, the converter halts within $n + 5$ steps with no bit in its state, the
verifier's pair encoding of $(x, w)$ on its output stack and every other stack empty. -/
noncomputable def computable :
    TM2ComputableInPolyTime (BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode
      Verifier.pairEncode id where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Verifier.G
  time := Polynomial.X + Polynomial.C 5
  outputsFun := fun p => by
    obtain ⟨x, w⟩ := p
    unfold TM2OutputsInTime
    refine { steps := 2 * x.length + 2 * w.length + 5, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      rw [bitEncode_pair_eq]
      erw [List.map_id, List.map_id, initList_tm, Option.map_some, haltList_tm]
      exact convert_run x w
    · rw [bitEncode_pair_eq]
      simp only [encFst, encSnd, List.length_append, List.length_cons, List.length_flatMap,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_nil]
      omega

end Cslib.Complexity.DenseSAT.Converter
