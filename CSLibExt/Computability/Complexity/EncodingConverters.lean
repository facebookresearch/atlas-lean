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

/-- Stacks: the input (`w # y` symbols), the output (bits), stashes for the two parts. -/
inductive Stk | inp | out | fst | snd
  deriving DecidableEq

instance : Fintype Stk where
  elems := ⟨↑[Stk.inp, Stk.out, Stk.fst, Stk.snd], by decide⟩
  complete := fun k => by cases k <;> decide

/-- Stack alphabets: the input holds the verifier's symbols, every other stack bits. -/
@[reducible] def Γ : Stk → Type
  | .inp => Verifier.G
  | _ => Bool

/-- Labels. -/
inductive Lab | readFst | readSnd | emitSnd | sep | emitFst
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.readFst, Lab.readSnd, Lab.emitSnd, Lab.sep, Lab.emitFst], by decide⟩
  complete := fun l => by cases l <;> decide

/-- The machine state: the last symbol popped (bits stored as `inl b`). -/
abbrev St := Option Verifier.G

/-- Is the state a left-tagged bit? -/
def isFst : St → Bool
  | some (.inl _) => true
  | _ => false

/-- Is the state a right-tagged bit? -/
def isSnd : St → Bool
  | some (.inr (some _)) => true
  | _ => false

/-- The bit carried by the state. -/
def bit : St → Bool
  | some (.inl b) => b
  | some (.inr (some b)) => b
  | _ => false

/-- The program. Output blocks are pushed in reverse so that they read correctly from the top. -/
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

/-- The machine. -/
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

/-- All four stacks. -/
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

/-- Runs of the program. -/
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

/-- The whole conversion: `2 |x| + 2 |w| + 5` steps. -/
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

/-- The identity from `w # y` to the canonical encoding of the pair, in at most
`2 n + 3` steps for an input of length `n`. -/
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

/-- Stacks of the two bit-list converters: input, output, one stash. -/
inductive BStk | inp | out | stash
  deriving DecidableEq

instance : Fintype BStk where
  elems := ⟨↑[BStk.inp, BStk.out, BStk.stash], by decide⟩
  complete := fun k => by cases k <;> decide

/-- Labels of the two bit-list converters. -/
inductive BLab | read | emit
  deriving DecidableEq

instance : Fintype BLab where
  elems := ⟨↑[BLab.read, BLab.emit], by decide⟩
  complete := fun l => by cases l <;> decide

/-- All three stacks (every alphabet is `Bool`). -/
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

/-- Read three-symbol blocks `[true, b, false]` onto the stash, then emit the stash. -/
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

/-- The machine. -/
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

/-- Exact `n`-step runs of this converter. -/
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

/-- The identity from the canonical encoding of a bit list to its raw bits, in at most `n + 2`
steps for an input of length `n`. -/
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

/-- Stash the raw bits, then emit one block `[true, b, false]` per bit. -/
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

/-- The machine. -/
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

/-- Exact `n`-step runs of this converter. -/
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

/-- The identity from raw bits to the canonical encoding of the bit list, in at most `2 n + 2`
steps for an input of length `n`. -/
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
