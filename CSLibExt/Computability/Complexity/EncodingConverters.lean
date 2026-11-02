/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.PairEncodingConverter

/-!
# Encoding converters for the Cook-Levin reduction

Three small explicit `Turing.FinTM2` machines that translate between formal-math's canonical
`BitstringEncoding`s and the raw encodings the ported Cook-Levin construction works with:

* `ToCanonical.computable`: the `w # y` form `Verifier.pairEncode (x, w)` to the canonical
  encoding of the pair `(x, w)` (the inverse direction of `Converter.computable`). Composed in
  front of an NP verifier, it gives a verifier that reads `w # y` with one input symbol per
  certificate bit, which is what the tableau construction expects.
* `DecodeBits.computable`: the canonical encoding of a bit list (three symbols per bit) to the
  raw bits.
* `EncodeBits.computable`: raw bits to the canonical encoding.

With `MetaMathlibExt.tm2ComputableInPolyTime_comp`, the last two turn a polynomial-time machine on
raw bit lists into an `IsPolyTime` witness for the same function.

Each runs in linear time and is checked by exact run lemmas.
-/

@[expose] public section

namespace Cslib.Complexity.DenseSAT

open Turing Function MetaMathlibExt Converter

/-! ## From `w # y` to the canonical pair encoding -/

namespace ToCanonical

/-- **Stacks of the converter to the canonical pair encoding.** The converter has four stacks: the
input stack, whose symbols are left-tagged bits, right-tagged bits and the separator (the input
is the bits of a first bit list tagged left, a separator, then the bits of a second bit list
tagged right); the output stack, holding bits; and two stashes, holding the bits of the first
and of the second list. -/
inductive Stk | inp | out | fst | snd
  deriving DecidableEq

instance : Fintype Stk where
  elems := ⟨↑[Stk.inp, Stk.out, Stk.fst, Stk.snd], by decide⟩
  complete := fun k => by cases k <;> decide

/-- **Stack alphabets of the separator-to-canonical converter.** The input stack of the converter
from the separator form of a pair to its canonical encoding has the verifier's alphabet, and each
of its other three stacks (the output and the two stashes) has the alphabet of bits. -/
@[reducible] def Γ : Stk → Type
  | .inp => Verifier.G
  | _ => Bool

/-- **Labels of the converter to the canonical pair encoding.** The machine that turns the
separated form of a pair $(x, w)$ of bit lists (the bits of $x$ tagged left, a separator, then
the bits of $w$ tagged right) into the canonical encoding of the pair has five labels: reading
the first part, reading the second part, emitting the second part, writing the separator, and
emitting the first part. -/
inductive Lab | readFst | readSnd | emitSnd | sep | emitFst
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.readFst, Lab.readSnd, Lab.emitSnd, Lab.sep, Lab.emitFst], by decide⟩
  complete := fun l => by cases l <;> decide

/-- **States of the converter to the canonical pair encoding.** A state of the converter is
either empty or one symbol of the verifier's input alphabet, that is, a left-tagged bit, a
right-tagged bit or the separator.

The state holds the last symbol popped; bits popped from the stashes are stored as left-tagged
bits. -/
abbrev St := Option Verifier.G

/-- **Left-tagged state test.** For a state $s$ of the pair-to-canonical converter (either empty
or a symbol of the verifier alphabet), the test is true exactly when $s$ is a left-tagged bit
$\mathrm{inl}\,b$ for some bit $b$, and false when $s$ is empty, the separator
$\mathrm{inr}(\mathrm{none})$ or a right-tagged bit. -/
def isFst : St → Bool
  | some (.inl _) => true
  | _ => false

/-- **Right-tagged state test.** For a state $s$ of the pair-to-canonical converter (either empty
or a symbol of the verifier alphabet), the test is true exactly when $s$ is a right-tagged bit
$\mathrm{inr}(\mathrm{some}\,b)$ for some bit $b$, and false when $s$ is empty, the separator
$\mathrm{inr}(\mathrm{none})$ or a left-tagged bit. -/
def isSnd : St → Bool
  | some (.inr (some _)) => true
  | _ => false

/-- **Bit carried by a converter state.** For a state $s$ of the pair-to-canonical converter
(either empty or a symbol of the verifier alphabet), the bit of $s$ is $b$ when $s$ is a
left-tagged bit $\mathrm{inl}\,b$ or a right-tagged bit $\mathrm{inr}(\mathrm{some}\,b)$, and
$\mathrm{false}$ when $s$ is empty or the separator $\mathrm{inr}(\mathrm{none})$. -/
def bit : St → Bool
  | some (.inl b) => b
  | some (.inr (some b)) => b
  | _ => false

/-- **Program of the converter to the canonical pair encoding.** The machine has an input stack
of symbols, each a left-tagged bit, a right-tagged bit or the separator, and three stacks of
bits: the output and two stashes. Its program first pops input symbols and pushes the bit of
each left-tagged one onto the first stash, until the input is empty or the symbol popped is not
a left-tagged bit. It then pops input symbols and pushes the bit of each right-tagged one onto
the second stash, until the input is empty or the symbol popped is not a right-tagged bit. Next
it pops each bit $b$ of the second stash and pushes false, $b$, true onto the output, and then
pushes a single false. Finally it pops each bit $b$ of the first stash and pushes false, true,
$b$, true, true, true onto the output, and halts when the first stash is empty.

Each output block is pushed in reverse, so that it reads true, $b$, false (respectively true,
true, true, $b$, true, false) from the top. -/
def prog : Lab → TM2.Stmt Γ Lab St
  | .readFst =>
      .pop .inp (fun _ o => o) <| .branch isFst
        (.push .fst bit <| .goto fun _ => .readFst)
        (.goto fun _ => .readSnd)
  | .readSnd =>
      .pop .inp (fun _ o => o) <| .branch isSnd
        (.push .snd bit <| .goto fun _ => .readSnd)
        (.goto fun _ => .emitSnd)
  | .emitSnd =>
      .pop .snd (fun _ o => o.map Sum.inl) <| .branch isFst
        (.push .out (fun _ => false) <| .push .out bit <| .push .out (fun _ => true) <|
          .goto fun _ => .emitSnd)
        (.goto fun _ => .sep)
  | .sep => .push .out (fun _ => false) <| .goto fun _ => .emitFst
  | .emitFst =>
      .pop .fst (fun _ o => o.map Sum.inl) <| .branch isFst
        (.push .out (fun _ => false) <| .push .out (fun _ => true) <| .push .out bit <|
          .push .out (fun _ => true) <| .push .out (fun _ => true) <|
          .push .out (fun _ => true) <| .goto fun _ => .emitFst)
        .halt

/-- **Machine converting the separator form of a pair to its canonical encoding.** The
multi-stack Turing machine with the four stacks of the converter to the canonical pair encoding
(input, output and two stashes), whose input stack holds symbols of the verifier's alphabet
(left-tagged bits, right-tagged bits and the separator) and whose other stacks hold bits, reading
its input from the input stack and leaving its output on the output stack, with the five labels
of that converter and start label $\mathrm{readFst}$, the converter's states (empty or one
verifier symbol) as internal states, initially empty, and the program of the converter to the
canonical pair encoding. It pops input symbols, pushing the bit of each left-tagged one onto the
first stash, until the input is empty or the symbol popped is not a left-tagged bit. It then pops
input symbols, pushing the bit of each right-tagged one onto the second stash, until the input is
empty or the symbol popped is not a right-tagged bit. Next it pops each bit $b$ of the second
stash and pushes a block reading true, $b$, false from the top onto the output, pushes a single
false, pops each bit $b$ of the first stash and pushes a block reading true, true, true, $b$,
true, false from the top, and halts when the first stash is empty. -/
def tm : FinTM2 where
  K := Stk
  k₀ := .inp
  k₁ := .out
  Γ := Γ
  Λ := Lab
  main := .readFst
  σ := St
  initialState := none
  Γk₀Fin := (inferInstance : Fintype Verifier.G)
  m := prog

/-- **Stack contents of the converter to the canonical pair encoding.** Given a list $i$ of input
symbols and bit lists $o$, $a$ and $b$, this is the contents of the four stacks of the converter
with $i$ on the input stack, $o$ on the output stack, $a$ on the first stash and $b$ on the
second stash. -/
def stk (i : List Verifier.G) (o a b : List Bool) : ∀ k, List (Γ k)
  | .inp => i
  | .out => o
  | .fst => a
  | .snd => b

@[simp] theorem update_stk_inp (i : List Verifier.G) (o a b : List Bool) (l : List Verifier.G) :
    update (stk i o a b) .inp l = stk l o a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_out (i : List Verifier.G) (o a b l : List Bool) :
    update (stk i o a b) .out l = stk i l a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_fst (i : List Verifier.G) (o a b l : List Bool) :
    update (stk i o a b) .fst l = stk i o l b := by
  funext k; cases k <;> rfl
@[simp] theorem update_stk_snd (i : List Verifier.G) (o a b l : List Bool) :
    update (stk i o a b) .snd l = stk i o a l := by
  funext k; cases k <;> rfl

/-- **Runs of the converter to the canonical pair encoding.** For a natural number $n$ and
configurations $c$ and $d$ of the converter, this is the proposition that $n$ steps of its
program lead from $c$ to $d$: applying the step function $n$ times to $c$ is defined at every
step (no configuration before the last one is halted) and gives $d$. -/
abbrev Run (n : ℕ) (c d : TM2.Cfg Γ Lab St) : Prop := TM2Program.Run prog n c d

theorem readFst_run (x : List Bool) :
    ∀ (rest : List Verifier.G) (o a b : List Bool) (v : St),
      Run (x.length + 1) ⟨some .readFst, v, stk (x.map Sum.inl ++ .inr none :: rest) o a b⟩
        ⟨some .readSnd, some (.inr none), stk rest o (x.reverse ++ a) b⟩ := by
  induction x with
  | nil =>
      intro rest o a b v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, isFst])
  | cons c x ih =>
      intro rest o a b v
      have h := ih rest o (c :: a) b (some (.inl c))
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, isFst, bit]

theorem readSnd_run (w : List Bool) :
    ∀ (o a b : List Bool) (v : St),
      Run (w.length + 1)
        ⟨some .readSnd, v, stk (w.map fun c => .inr (some c)) o a b⟩
        ⟨some .emitSnd, none, stk [] o a (w.reverse ++ b)⟩ := by
  induction w with
  | nil =>
      intro o a b v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, isSnd])
  | cons c w ih =>
      intro o a b v
      have h := ih o a (c :: b) (some (.inr (some c)))
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, isSnd, bit]

theorem emitSnd_run (b : List Bool) :
    ∀ (o a : List Bool) (v : St),
      Run (b.length + 1) ⟨some .emitSnd, v, stk [] o a b⟩
        ⟨some .sep, none, stk [] (encSnd b.reverse ++ o) a []⟩ := by
  induction b with
  | nil =>
      intro o a v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, isFst, encSnd])
  | cons c b ih =>
      intro o a v
      have h := ih (true :: c :: false :: o) a (some (.inl c))
      simp only [List.reverse_cons, encSnd, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_assoc, List.cons_append, List.nil_append,
        List.append_nil] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, isFst, bit]

theorem sep_run (o a : List Bool) :
    Run 1 ⟨some .sep, none, stk [] o a []⟩ ⟨some .emitFst, none, stk [] (false :: o) a []⟩ :=
  TM2Program.Run.single (by simp [prog, TM2.stepAux, stk])

theorem emitFst_run (a : List Bool) :
    ∀ (o : List Bool) (v : St),
      Run (a.length + 1) ⟨some .emitFst, v, stk [] o a []⟩
        ⟨none, none, stk [] (encFst a.reverse ++ o) [] []⟩ := by
  induction a with
  | nil =>
      intro o v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, stk, isFst, encFst])
  | cons c a ih =>
      intro o v
      have h := ih (true :: true :: true :: c :: true :: false :: o) (some (.inl c))
      simp only [List.reverse_cons, encFst, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_assoc, List.cons_append, List.nil_append,
        List.append_nil] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, stk, isFst, bit]

/-- **Run of the pair-to-canonical converter.** Let $x$ and $w$ be bit lists, write $x \# w$ for
the verifier input of the pair $(x, w)$, and read $1$ for true and $0$ for false. Let
$\mathrm{encFst}(x)$ replace each bit $b$ of $x$ by $1, 1, 1, b, 1, 0$ and $\mathrm{encSnd}(w)$
replace each bit $b$ of $w$ by $1, b, 0$. The program of the pair-to-canonical converter goes in
exactly $2|x| + 2|w| + 5$ steps from the configuration at label $\mathrm{readFst}$ with empty
state, $x \# w$ on the input stack and the output stack and both stashes empty, to the halted
configuration with empty state, empty input stack and stashes, and output stack reading
$\mathrm{encFst}(x)$, then $0$, then $\mathrm{encSnd}(w)$ from the top. -/
theorem convert_run (x w : List Bool) :
    Run (2 * x.length + 2 * w.length + 5)
      ⟨some .readFst, none, stk (Verifier.pairEncode (x, w)) [] [] []⟩
      ⟨none, none, stk [] (encFst x ++ false :: encSnd w) [] []⟩ := by
  have h₁ := readFst_run x (w.map fun c => .inr (some c)) [] [] [] none
  have h₂ := readSnd_run w [] (x.reverse ++ []) [] (some (.inr none))
  have h₃ := emitSnd_run (w.reverse ++ []) [] (x.reverse ++ []) none
  have h₄ := sep_run (encSnd (w.reverse ++ []).reverse ++ []) (x.reverse ++ [])
  have h₅ := emitFst_run (x.reverse ++ []) (false :: (encSnd (w.reverse ++ []).reverse ++ []))
    none
  have h := h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
  exact h.of_eq (by omega)

theorem initList_tm (l : List Verifier.G) :
    initList tm l = ⟨some .readFst, none, stk l [] [] []⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_tm (l : List Bool) : haltList tm l = ⟨none, none, stk [] l [] []⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

/-- **Canonical bit-list decoder.** This is a multi-stack Turing machine over the alphabet
$\mathrm{Bool}$, with time bound $n + 2$, such that for every bit list $x$, started on the
canonical bitstring encoding of $x$, it halts within $n + 2$ steps, where $n$ is the length of
that encoding, with $x$ on its output stack and all other stacks empty. So the identity on bit
lists is computable in polynomial time from the canonical encoding to the raw bits. -/
noncomputable def computable :
    TM2ComputableInPolyTime Verifier.pairEncode
      (BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode id where
  tm := tm
  inputAlphabet := Equiv.refl Verifier.G
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun := fun p => by
    obtain ⟨x, w⟩ := p
    unfold TM2OutputsInTime
    refine { steps := 2 * x.length + 2 * w.length + 5, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      erw [List.map_id, List.map_id, id, bitEncode_pair_eq, initList_tm, Option.map_some,
        haltList_tm]
      exact convert_run x w
    · simp only [Verifier.pairEncode, List.length_append, List.length_cons, List.length_map,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      omega

end ToCanonical


/-! ## Bit lists: canonical encoding to raw bits and back -/

/-- **Stacks of the bit-list converters.** The two bit-list converters use three stacks: the
input stack, the output stack and one stash. -/
inductive BStk | inp | out | stash
  deriving DecidableEq

instance : Fintype BStk where
  elems := ⟨↑[BStk.inp, BStk.out, BStk.stash], by decide⟩
  complete := fun k => by cases k <;> decide

/-- **Labels of the bit-list converters.** The two bit-list converters have two program labels,
$\mathrm{read}$ and $\mathrm{emit}$. -/
inductive BLab | read | emit
  deriving DecidableEq

instance : Fintype BLab where
  elems := ⟨↑[BLab.read, BLab.emit], by decide⟩
  complete := fun l => by cases l <;> decide

/-- **Stack contents of the bit-list converters.** For bit lists $i$, $o$ and $a$, this assigns
contents to the three stacks of the bit-list converters: $i$ to the input stack, $o$ to the
output stack and $a$ to the stash. Every stack alphabet is $\mathrm{Bool}$. -/
def bstk (i o a : List Bool) : BStk → List Bool
  | .inp => i
  | .out => o
  | .stash => a

@[simp] theorem update_bstk_inp (i o a l : List Bool) :
    update (bstk i o a) .inp l = bstk l o a := by
  funext k; cases k <;> rfl
@[simp] theorem update_bstk_out (i o a l : List Bool) :
    update (bstk i o a) .out l = bstk i l a := by
  funext k; cases k <;> rfl
@[simp] theorem update_bstk_stash (i o a l : List Bool) :
    update (bstk i o a) .stash l = bstk i o l := by
  funext k; cases k <;> rfl

namespace DecodeBits

/-- **Program of the bit-list decoder.** The program of the machine that decodes the canonical
encoding of a bit list acts on the three stacks of the bit-list converters, all over bits, with an
optional bit as internal state. At label $\mathrm{read}$ it pops a symbol from the input stack into
the state (which becomes empty if the input is empty). If that symbol is true, it pops a second
symbol $b$ into the state, pops and discards a third, pushes $b$ onto the stash (false if the
input ran out before $b$) and returns to $\mathrm{read}$; otherwise it goes to $\mathrm{emit}$. At
label $\mathrm{emit}$ it pops a bit from the stash, pushes it onto the output and returns to
$\mathrm{emit}$, and it halts when the stash is empty. -/
def prog : BLab → TM2.Stmt (fun _ : BStk => Bool) BLab (Option Bool)
  | .read =>
      .pop .inp (fun _ o => o) <| .branch (fun s => s == some true)
        (.pop .inp (fun _ o => o) <| .pop .inp (fun s _ => s) <|
          .push .stash (fun s => s.getD false) <| .goto fun _ => .read)
        (.goto fun _ => .emit)
  | .emit =>
      .pop .stash (fun _ o => o) <| .branch (fun s => s.isSome)
        (.push .out (fun s => s.getD false) <| .goto fun _ => .emit)
        .halt

/-- **Machine decoding the canonical encoding of a bit list.** The multi-stack Turing machine with
the three stacks of the bit-list converters (input, output and a stash), all over bits, reading
its input from the input stack and leaving its output on the output stack, with the two labels
$\mathrm{read}$ and $\mathrm{emit}$ and start label $\mathrm{read}$, an optional bit as internal
state, initially empty, and the program of the bit-list decoder. It repeatedly pops an input
symbol; while that symbol is true, it pops two more and pushes the first of them onto the stash
(false if the input ran out before it). Then it moves the stash, bit by bit, onto the output, and
halts. -/
def tm : FinTM2 where
  K := BStk
  k₀ := .inp
  k₁ := .out
  Γ := fun _ => Bool
  Λ := BLab
  main := .read
  σ := Option Bool
  initialState := none
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := prog

/-- **Runs of the bit-list decoder.** For a natural number $n$ and configurations $c$ and $d$ of
the machine decoding the canonical encoding of a bit list (each an optional label, an optional bit
as internal state and the contents of the three bit stacks), this is the proposition that $n$
steps of its program lead from $c$ to $d$: applying the step function $n$ times to $c$ is defined
at every step (no configuration before the last one is halted) and gives $d$. -/
abbrev Run (n : ℕ) (c d : TM2.Cfg (fun _ : BStk => Bool) BLab (Option Bool)) : Prop :=
  TM2Program.Run prog n c d

theorem read_run (x : List Bool) :
    ∀ (o a : List Bool) (v : Option Bool),
      Run (x.length + 1) ⟨some .read, v, bstk (encSnd x) o a⟩
        ⟨some .emit, none, bstk [] o (x.reverse ++ a)⟩ := by
  induction x with
  | nil =>
      intro o a v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, bstk, encSnd])
  | cons c x ih =>
      intro o a v
      have h := ih o (c :: a) (some c)
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, bstk, encSnd]

theorem emit_run (a : List Bool) :
    ∀ (o : List Bool) (v : Option Bool),
      Run (a.length + 1) ⟨some .emit, v, bstk [] o a⟩ ⟨none, none,
          bstk [] (a.reverse ++ o) []⟩ := by
  induction a with
  | nil =>
      intro o v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, bstk])
  | cons c a ih =>
      intro o v
      have h := ih (c :: o) (some c)
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, bstk]

theorem initList_tm (l : List Bool) : initList tm l = ⟨some .read, none, bstk l [] []⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_tm (l : List Bool) : haltList tm l = ⟨none, none, bstk [] l []⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

/-- **Polynomial-time decoder of the canonical bit-list encoding.** This is a multi-stack Turing
machine whose input and output alphabets are the bits, together with the polynomial time bound
$t(n) = n + 2$, such that for every bit list $x$, whose canonical bitstring encoding has length
$n$, the machine started with that encoding on its input stack and all other stacks empty halts
within $t(n)$ steps with $x$ on its output stack, all other stacks empty and its internal state
back to the initial one. So the identity on bit lists is computable in polynomial time from the
canonical encoding to the raw bits.

The canonical encoding writes each bit $b$ of $x$ as the three bits true, $b$, false. -/
noncomputable def computable :
    TM2ComputableInPolyTime (BitstringEncoding.toEncoding (α := List Bool)).encode
      (fun l : List Bool => l) id where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + Polynomial.C 2
  outputsFun := fun x => by
    unfold TM2OutputsInTime
    refine { steps := 2 * x.length + 2, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      have h := (read_run x [] [] none).trans (emit_run (x.reverse ++ []) [] none)
      simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
      have hx : (BitstringEncoding.toEncoding (α := List Bool)).encode x = encSnd x :=
        bitEncode_list x
      erw [List.map_id, List.map_id, id, hx, initList_tm, Option.map_some, haltList_tm]
      exact h.of_eq (by omega)
    · change 2 * x.length + 2 ≤ (Polynomial.X + Polynomial.C 2).eval
        (BitstringEncoding.bitEncode x).length
      rw [bitEncode_list]
      simp only [encSnd, List.length_flatMap, List.length_cons, List.length_nil,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, List.map_const',
        List.sum_replicate, smul_eq_mul]
      omega

end DecodeBits

namespace EncodeBits

/-- **Program of the bit-list encoder.** The program of the machine that writes the canonical
encoding of a bit list acts on the three stacks of the bit-list converters, all over bits, with an
optional bit as internal state. At label $\mathrm{read}$ it pops a bit from the input stack,
pushes it onto the stash and returns to $\mathrm{read}$; when the input is empty it goes to
$\mathrm{emit}$. At label $\mathrm{emit}$ it pops a bit $b$ from the stash, pushes false, $b$ and
true onto the output, so that the output then reads true, $b$, false from the top, and returns to
$\mathrm{emit}$; it halts when the stash is empty. -/
def prog : BLab → TM2.Stmt (fun _ : BStk => Bool) BLab (Option Bool)
  | .read =>
      .pop .inp (fun _ o => o) <| .branch (fun s => s.isSome)
        (.push .stash (fun s => s.getD false) <| .goto fun _ => .read)
        (.goto fun _ => .emit)
  | .emit =>
      .pop .stash (fun _ o => o) <| .branch (fun s => s.isSome)
        (.push .out (fun _ => false) <| .push .out (fun s => s.getD false) <|
          .push .out (fun _ => true) <| .goto fun _ => .emit)
        .halt

/-- **Machine writing the canonical encoding of a bit list.** The multi-stack Turing machine with
the three stacks of the bit-list converters (input, output and a stash), all over bits, reading
its input from the input stack and leaving its output on the output stack, with the two labels
$\mathrm{read}$ and $\mathrm{emit}$ and start label $\mathrm{read}$, an optional bit as internal
state, initially empty, and the program of the bit-list encoder. It moves the input, bit by bit,
onto the stash. Then it pops the stash bit by bit, pushing for each bit $b$ the three bits false,
$b$, true onto the output, so that each block reads true, $b$, false from the top, and halts. -/
def tm : FinTM2 where
  K := BStk
  k₀ := .inp
  k₁ := .out
  Γ := fun _ => Bool
  Λ := BLab
  main := .read
  σ := Option Bool
  initialState := none
  Γk₀Fin := (inferInstance : Fintype Bool)
  m := prog

/-- **Runs of the bit-list encoder.** For a natural number $n$ and configurations $c$ and $d$ of
the machine writing the canonical encoding of a bit list (each an optional label, an optional bit
as internal state and the contents of the three bit stacks), this is the proposition that $n$
steps of its program lead from $c$ to $d$: applying the step function $n$ times to $c$ is defined
at every step (no configuration before the last one is halted) and gives $d$. -/
abbrev Run (n : ℕ) (c d : TM2.Cfg (fun _ : BStk => Bool) BLab (Option Bool)) : Prop :=
  TM2Program.Run prog n c d

theorem read_run (x : List Bool) :
    ∀ (o a : List Bool) (v : Option Bool),
      Run (x.length + 1) ⟨some .read, v, bstk x o a⟩ ⟨some .emit, none,
          bstk [] o (x.reverse ++ a)⟩ := by
  induction x with
  | nil =>
      intro o a v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, bstk])
  | cons c x ih =>
      intro o a v
      have h := ih o (c :: a) (some c)
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, bstk]

theorem emit_run (a : List Bool) :
    ∀ (o : List Bool) (v : Option Bool),
      Run (a.length + 1) ⟨some .emit, v, bstk [] o a⟩
        ⟨none, none, bstk [] (encSnd a.reverse ++ o) []⟩ := by
  induction a with
  | nil =>
      intro o v
      exact TM2Program.Run.single (by simp [prog, TM2.stepAux, bstk, encSnd])
  | cons c a ih =>
      intro o v
      have h := ih (true :: c :: false :: o) (some c)
      simp only [List.reverse_cons, encSnd, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_assoc, List.cons_append, List.nil_append,
        List.append_nil] at h ⊢
      refine TM2Program.Run.head ?_ h
      simp [TM2.step, prog, TM2.stepAux, bstk]

theorem initList_tm (l : List Bool) : initList tm l = ⟨some .read, none, bstk l [] []⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_tm (l : List Bool) : haltList tm l = ⟨none, none, bstk [] l []⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> rfl

/-- **Polynomial-time encoder to the canonical bit-list encoding.** This is a multi-stack Turing
machine whose input and output alphabets are the bits, together with the polynomial time bound
$t(n) = 2n + 2$, such that for every bit list $x$ of length $n$, the machine started with $x$ on
its input stack and all other stacks empty halts within $t(n)$ steps with the canonical bitstring
encoding of $x$ on its output stack, all other stacks empty and its internal state back to the
initial one. So the identity on bit lists is computable in polynomial time from the raw bits to
the canonical encoding.

The canonical encoding writes each bit $b$ of $x$ as the three bits true, $b$, false. -/
noncomputable def computable :
    TM2ComputableInPolyTime (fun l : List Bool => l)
      (BitstringEncoding.toEncoding (α := List Bool)).encode id where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  outputsFun := fun x => by
    unfold TM2OutputsInTime
    refine { steps := 2 * x.length + 2, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      have h := (read_run x [] [] none).trans (emit_run (x.reverse ++ []) [] none)
      simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
      have hx : (BitstringEncoding.toEncoding (α := List Bool)).encode x = encSnd x :=
        bitEncode_list x
      erw [List.map_id, List.map_id, id, hx, initList_tm, Option.map_some, haltList_tm]
      exact h.of_eq (by omega)
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      omega

end EncodeBits

end Cslib.Complexity.DenseSAT
