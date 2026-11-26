/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Host
public import CSLibExt.Computability.Complexity.Karp.MultipleKnapsack
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatMachine
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy

/-!
# Polynomial-time SUBSET-SUM to MULTIPLE KNAPSACK on all raw bitstrings

`HardnessMachine.isPolyTime_reduceFromSubsetSum`: the bit-string map `reduceFromSubsetSum`, which
sends a canonical SUBSET-SUM instance `(as, t)` to the canonical encoding of the
multiple-knapsack instance `fromSubsetSum as t` and every other bit string to the encoding of
`noInstance`, is computable in polynomial time.

The machine has two parts, both private to this module.

* The emitter (`HardnessCore`) works on a canonical source `encodeSS as t` in linear time. The
  generic product and list encodings nest the frames: writing `dbl l` for `l` with every bit `b`
  replaced by `true, b`, an item `(a, a)` contributes `dbl³ a ++ [1,1,1,0] ++ dbl² a ++ [1,0]` to
  the outer frame of the item list. The emitter first writes the capacity list and the target,
  which come last, onto the bottom of the output stack, then emits the items in order onto a
  reversed buffer, which a final pass moves onto the output.
* The wrapper (`HardnessMachine`) follows the PARTITION hardness wrapper of
  `CSLibExt.Computability.Complexity.Karp.PartitionHardness`: the source codec accepts only
  nonempty canonical List Nat strings, so the wrapper preserves the raw input, normalizes it with
  the shared exact decoder and compares before running the emitter. Every rejection emits the
  fixed no-instance.
-/


namespace MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack.HardnessCore

open Turing Function TM2Program BitstringEncoding Computability
open Cslib.Complexity.Karp

/-! ### The output format -/

/-- Every bit `b` replaced by the pair `true, b`; `delimit l` is `dbl l ++ [false]`. -/
def dbl (l : List Bool) : List Bool := l.flatMap fun b => [true, b]

@[simp] theorem dbl_nil : dbl [] = [] := rfl

@[simp] theorem dbl_cons (b : Bool) (l : List Bool) : dbl (b :: l) = true :: b :: dbl l := rfl

@[simp] theorem dbl_append (l m : List Bool) : dbl (l ++ m) = dbl l ++ dbl m := by
  simp [dbl, List.flatMap_append]

theorem delimit_eq_dbl (l : List Bool) : delimit l = dbl l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, ih]

/-- The contribution of one item `(a, a)` inside the outer frame of the item list. -/
def itemOut (a : ℕ) : List Bool :=
  (encodeNat a).flatMap (fun b => [true, true, true, true, true, true, true, b]) ++
    [true, true, true, false] ++
    (encodeNat a).flatMap (fun b => [true, true, true, b]) ++ [true, false]

theorem dbl_dbl (l : List Bool) : dbl (dbl l) = l.flatMap fun b => [true, true, true, b] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

theorem dbl_dbl_dbl (l : List Bool) :
    dbl (dbl (dbl l)) = l.flatMap fun b => [true, true, true, true, true, true, true, b] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

theorem reverse_flatMap_reverse (l : List Bool) (f : Bool → List Bool) :
    (l.reverse.flatMap f).reverse = l.flatMap fun b => (f b).reverse := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.flatMap_append, ih]

theorem bitEncode_list {α : Type} [BitstringEncoding α] (l : List α) :
    bitEncode l = l.flatMap fun a => delimit (bitEncode a) := by
  change ((l.map bitEncode).map delimit).flatten = _
  simp [List.flatMap_def, Function.comp_def]

theorem dbl_flatMap {α : Type} (l : List α) (f : α → List Bool) :
    dbl (l.flatMap f) = l.flatMap fun a => dbl (f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem dbl_delimit_item (a : ℕ) : dbl (delimit (bitEncode (a, a))) = itemOut a := by
  change dbl (delimit (delimit (encodeNat a) ++ encodeNat a)) = _
  simp only [delimit_eq_dbl, dbl_append, dbl_dbl, dbl_flatMap, dbl_cons, dbl_nil, itemOut,
    List.append_assoc, List.cons_append, List.nil_append]

/-- **The emitted format.** The canonical encoding of `fromSubsetSum as t`, frame by frame. -/
theorem bitEncode_fromSubsetSum (as : List ℕ) (t : ℕ) :
    bitEncode (fromSubsetSum as t) =
      as.flatMap itemOut ++ [false] ++
        (encodeNat t).flatMap (fun b => [true, true, true, b]) ++ [true, false, false] ++
          encodeNat t := by
  have hitems : dbl (bitEncode (as.map fun a => (a, a))) = as.flatMap itemOut := by
    rw [bitEncode_list, dbl_flatMap, List.flatMap_map]
    exact congrArg (List.flatMap · as) (funext dbl_delimit_item)
  change delimit (bitEncode (as.map fun a => (a, a))) ++
    (delimit (bitEncode [t]) ++ bitEncode t) = _
  rw [delimit_eq_dbl, hitems, bitEncode_list, delimit_eq_dbl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, delimit_eq_dbl,
    BinaryNatEncoding.bitEncode_nat, dbl_append, dbl_dbl, dbl_cons, dbl_nil,
    List.append_assoc, List.cons_append, List.nil_append]

/-! ### The machine -/

/-- Input, two copies of the target, two item buffers, the reversed item output, and the
output. -/
inductive K | X | T | T2 | A | A' | R | O
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.X, .T, .T2, .A, .A', .R, .O], by decide⟩
  complete k := by cases k <;> decide

/-- All stacks hold bits. -/
abbrev Γ : K → Type := fun _ => Bool

/-- Read the target; write the target and the capacity list; then the items, one by one. -/
inductive Lab
  | target | vbits | capHead | capBits | item | blk | rev | d2 | d2end | endItems | out | done
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.target, .vbits, .capHead, .capBits, .item, .blk, .rev, .d2, .d2end,
    .endItems, .out, .done], by decide⟩
  complete l := by cases l <;> decide

/-- Pop bits from `a` until it is empty, pushing the word `wd b` onto `o` for each bit `b`. -/
def wordS (a o : K) (wd : Bool → List Bool) (self next : Lab) : TM2.Stmt Γ Lab Bool :=
  .peek a (fun _ x => x.isNone) <| .branch id (.goto fun _ => next) <|
    .pop a (fun _ x => x.getD false) <| .branch id
      (pushList o (wd true) (.goto fun _ => self))
      (pushList o (wd false) (.goto fun _ => self))

/-- The emitter program. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .target =>
    .pop .X (fun _ o => o.getD false) <| .branch id
      (.pop .X (fun _ o => o.getD false) <| .push .T id <| .push .T2 id <|
        .goto fun _ => .target)
      (.goto fun _ => .vbits)
  | .vbits => moveB .T2 .O some id .vbits .capHead
  | .capHead => emit .O [false, false, true] .capBits
  | .capBits => wordS .T .O (fun b => [b, true, true, true]) .capBits .item
  | .item => .peek .X (fun _ o => o.isNone) <| .branch id
      (.goto fun _ => .endItems) (.goto fun _ => .blk)
  | .blk =>
    .pop .X (fun _ o => o.getD false) <| .branch id
      (.pop .X (fun _ o => o.getD false) <|
        pushList .R [true, true, true, true, true, true, true] <| .push .R id <|
          .push .A id <| .goto fun _ => .blk)
      (pushList .R [true, true, true, false] <| .goto fun _ => .rev)
  | .rev => moveB .A .A' some id .rev .d2
  | .d2 => wordS .A' .R (fun b => [true, true, true, b]) .d2 .d2end
  | .d2end => emit .R [true, false] .item
  | .endItems => emit .R [false] .out
  | .out => moveB .R .O some id .out .done
  | .done => .halt

/-- The seven stacks. -/
def st (x t t2 a a' r o : List Bool) : ∀ k, List (Γ k)
  | .X => x | .T => t | .T2 => t2 | .A => a | .A' => a' | .R => r | .O => o

theorem wordS_run {M : Lab → TM2.Stmt Γ Lab Bool} {a o : K} {wd : Bool → List Bool}
    {self next : Lab} (hM : M self = wordS a o wd self next) (hao : a ≠ o) :
    ∀ (L : List Bool) (v : Bool) (S : ∀ k, List (Γ k)), S a = L →
      ∃ v', Run M (L.length + 1) ⟨some self, v, S⟩
        ⟨some next, v', update (update S a []) o ((L.flatMap wd).reverse ++ S o)⟩ := by
  intro L
  induction L with
  | nil =>
    intro v S hS
    refine ⟨true, Run.single ?_⟩
    have h₁ : update S a [] = S := by rw [← hS, update_eq_self]
    simp [hM, wordS, TM2.stepAux, hS, h₁]
  | cons b L ih =>
    intro v S hS
    let S₁ := update (update S a L) o ((wd b).reverse ++ S o)
    obtain ⟨v', hr⟩ := ih b S₁ (by simp [S₁, hao])
    have hstep : TM2.step M ⟨some self, v, S⟩ = some ⟨some self, b, S₁⟩ := by
      cases b <;> simp [TM2.step, hM, wordS, TM2.stepAux, hS, stepAux_pushList, S₁,
        update_of_ne hao.symm]
    have hres : update (update S₁ a []) o ((L.flatMap wd).reverse ++ S₁ o) =
        update (update S a []) o (((b :: L).flatMap wd).reverse ++ S o) := by
      funext k
      by_cases hko : k = o
      · subst hko
        simp [S₁, List.flatMap_cons, List.reverse_append, List.append_assoc]
      · by_cases hka : k = a
        · subst hka
          simp [S₁, hko]
        · simp [S₁, hko, hka]
    refine ⟨v', ?_⟩
    rw [← hres]
    exact Run.head hstep hr

private theorem target_run (p : List Bool) :
    ∀ (rest t t2 r o : List Bool) (v : Bool),
      Run prog (p.length + 1)
        ⟨some .target, v, st (delimit p ++ rest) t t2 [] [] r o⟩
        ⟨some .vbits, false, st rest (p.reverse ++ t) (p.reverse ++ t2) [] [] r o⟩ := by
  induction p with
  | nil =>
    intro rest t t2 r o v
    refine Run.single ?_
    simp only [prog, TM2.stepAux, st, delimit, List.cons_append, List.nil_append,
      List.head?_cons, Option.getD_some, List.tail_cons, id_eq, Bool.cond_false, List.reverse_nil]
    congr 1
    funext k
    cases k <;> rfl
  | cons b p ih =>
    intro rest t t2 r o v
    have h := ih rest (b :: t) (b :: t2) r o b
    have hstep : TM2.step prog ⟨some .target, v, st (delimit (b :: p) ++ rest) t t2 [] [] r o⟩ =
        some ⟨some .target, b, st (delimit p ++ rest) (b :: t) (b :: t2) [] [] r o⟩ := by
      simp only [TM2.step, prog, TM2.stepAux, st, delimit, List.cons_append, List.head?_cons,
        Option.getD_some, List.tail_cons, id_eq, Bool.cond_true]
      congr 2
      funext k
      cases k <;> rfl
    have h' := Run.head hstep h
    simpa [List.reverse_cons, List.append_assoc] using h'

private theorem blk_run (p : List Bool) :
    ∀ (rest t t2 a r o : List Bool) (v : Bool),
      Run prog (p.length + 1)
        ⟨some .blk, v, st (delimit p ++ rest) t t2 a [] r o⟩
        ⟨some .rev, false, st rest t t2 (p.reverse ++ a) []
          (((p.flatMap fun b => [true, true, true, true, true, true, true, b]) ++
            [true, true, true, false]).reverse ++ r) o⟩ := by
  induction p with
  | nil =>
    intro rest t t2 a r o v
    refine Run.single ?_
    simp only [prog, TM2.stepAux, stepAux_pushList, st, delimit, List.cons_append,
      List.nil_append, List.head?_cons, Option.getD_some, List.tail_cons, Bool.cond_false, id_eq]
    congr 1
    funext k
    cases k <;> rfl
  | cons b p ih =>
    intro rest t t2 a r o v
    have h := ih rest t t2 (b :: a) ([b, true, true, true, true, true, true, true] ++ r) o b
    have hstep : TM2.step prog ⟨some .blk, v, st (delimit (b :: p) ++ rest) t t2 a [] r o⟩ =
        some ⟨some .blk, b, st (delimit p ++ rest) t t2 (b :: a) []
          ([b, true, true, true, true, true, true, true] ++ r) o⟩ := by
      simp only [TM2.step, prog, TM2.stepAux, stepAux_pushList, st, delimit,
        List.cons_append, List.head?_cons, Option.getD_some, List.tail_cons, id_eq,
        Bool.cond_true]
      congr 2
      funext k
      cases k <;> rfl
    have h' := Run.head hstep h
    simpa [List.reverse_cons, List.append_assoc] using h'

private theorem item_run (n : ℕ) (rest t t2 r o : List Bool) (v : Bool) :
    ∃ v', Run prog (3 * (encodeNat n).length + 5)
      ⟨some .item, v, st (delimit (encodeNat n) ++ rest) t t2 [] [] r o⟩
      ⟨some .item, v', st rest t t2 [] [] ((itemOut n).reverse ++ r) o⟩ := by
  set p := encodeNat n with hp
  have h₁ : Run prog 1 ⟨some .item, v, st (delimit p ++ rest) t t2 [] [] r o⟩
      ⟨some .blk, false, st (delimit p ++ rest) t t2 [] [] r o⟩ := by
    refine Run.single ?_
    cases p <;> simp [prog, TM2.stepAux, st, delimit]
  have h₂ := blk_run p rest t t2 [] r o false
  set r₁ := ((p.flatMap fun b => [true, true, true, true, true, true, true, b]) ++
    [true, true, true, false]).reverse ++ r with hr₁
  obtain ⟨v₃, S₃, h₃, hA, hA', hk⟩ := moveB_run (M := prog) (a := K.A) (b := K.A')
    (d := some) (g := id) (self := Lab.rev) (next := Lab.d2) rfl (by decide)
    p.reverse p.reverse [] false (st rest t t2 (p.reverse ++ []) [] r₁ o) (by simp [st])
    (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hS₃ : S₃ = st rest t t2 [] p r₁ o := by
    funext k
    cases k with
    | A => exact hA
    | A' => simpa [st] using hA'
    | X | T | T2 | R | O => exact hk _ (by decide) (by decide)
  rw [hS₃] at h₃
  obtain ⟨v₄, h₄⟩ := wordS_run (M := prog) (a := K.A') (o := K.R)
    (wd := fun b => [true, true, true, b]) (self := .d2) (next := .d2end) rfl (by decide)
    p v₃ (st rest t t2 [] p r₁ o) rfl
  have hS₄ : update (update (st rest t t2 [] p r₁ o) K.A' []) K.R
      ((p.flatMap fun b => [true, true, true, b]).reverse ++ st rest t t2 [] p r₁ o K.R) =
      st rest t t2 [] [] ((p.flatMap fun b => [true, true, true, b]).reverse ++ r₁) o := by
    funext k
    cases k <;> rfl
  rw [hS₄] at h₄
  have h₅ := emit_run (M := prog) (self := Lab.d2end) (next := Lab.item) (k := K.R)
    (xs := [true, false]) rfl v₄
    (st rest t t2 [] [] ((p.flatMap fun b => [true, true, true, b]).reverse ++ r₁) o)
  have hS₅ : update (st rest t t2 [] []
      ((p.flatMap fun b => [true, true, true, b]).reverse ++ r₁) o) K.R
      ([true, false].reverse ++ st rest t t2 [] []
        ((p.flatMap fun b => [true, true, true, b]).reverse ++ r₁) o K.R) =
      st rest t t2 [] [] ((itemOut n).reverse ++ r) o := by
    funext k
    cases k <;> simp [st, itemOut, hr₁, ← hp, List.reverse_append, List.append_assoc]
  rw [hS₅] at h₅
  refine ⟨v₄, ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).of_eq ?_⟩
  simp only [List.length_reverse]
  omega

private theorem items_run (as : List ℕ) :
    ∀ (t t2 r o : List Bool) (v : Bool),
      ∃ v', RunLe prog (5 * (as.flatMap fun a => delimit (encodeNat a)).length + 1)
        ⟨some .item, v, st (as.flatMap fun a => delimit (encodeNat a)) t t2 [] [] r o⟩
        ⟨some .endItems, v', st [] t t2 [] [] ((as.flatMap itemOut).reverse ++ r) o⟩ := by
  induction as with
  | nil =>
    intro t t2 r o v
    exact ⟨true, (Run.single (by simp [prog, TM2.stepAux, st])).le le_rfl⟩
  | cons a as ih =>
    intro t t2 r o v
    obtain ⟨v₁, h₁⟩ := item_run a (as.flatMap fun a => delimit (encodeNat a)) t t2 r o v
    obtain ⟨v₂, h₂⟩ := ih t t2 ((itemOut a).reverse ++ r) o v₁
    refine ⟨v₂, ?_⟩
    have h := ((h₁.le le_rfl).trans h₂).mono (B' := 5 * ((a :: as).flatMap fun a =>
      delimit (encodeNat a)).length + 1) (by
        simp only [List.flatMap_cons, List.length_append, length_delimit]
        omega)
    simpa [List.flatMap_cons, List.reverse_append, List.append_assoc] using h

theorem length_flatMap_itemOut (as : List ℕ) :
    (as.flatMap itemOut).length = 6 * (as.flatMap fun a => delimit (encodeNat a)).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, ih, itemOut, length_delimit,
      List.length_flatMap, List.length_cons, List.length_nil, List.map_const', List.sum_replicate,
      smul_eq_mul]
    omega

/-- **The emitter is correct and linear.** On a canonical SUBSET-SUM instance the machine
writes the canonical encoding of `fromSubsetSum as t` within a linear number of steps. -/
theorem run (as : List ℕ) (t : ℕ) :
    ∃ v S, RunLe prog (30 * ((encodeSS as t).length + 1))
      ⟨some .target, false, update (fun _ => []) .X (encodeSS as t)⟩
      ⟨some .done, v, S⟩ ∧ S .O = bitEncode (fromSubsetSum as t) := by
  set p := encodeNat t with hp
  set q := as.flatMap fun a => delimit (encodeNat a) with hq
  have hstart : update (fun _ => []) K.X (encodeSS as t) =
      st (delimit p ++ q) [] [] [] [] [] [] := by
    funext k
    cases k <;> rfl
  rw [hstart]
  have h₁ := target_run p q [] [] [] [] false
  simp only [List.append_nil] at h₁
  obtain ⟨v₂, S₂, h₂, hT2, hO, hk₂⟩ := moveB_run (M := prog) (a := K.T2) (b := K.O)
    (d := some) (g := id) (self := Lab.vbits) (next := Lab.capHead) rfl (by decide)
    p.reverse p.reverse [] false (st q p.reverse p.reverse [] [] [] []) (by simp [st])
    (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hS₂ : S₂ = st q p.reverse [] [] [] [] p := by
    funext k
    cases k with
    | T2 => exact hT2
    | O => simpa [st] using hO
    | X | T | A | A' | R => exact hk₂ _ (by decide) (by decide)
  rw [hS₂] at h₂
  have h₃ := emit_run (M := prog) (self := Lab.capHead) (next := Lab.capBits) (k := K.O)
    (xs := [false, false, true]) rfl v₂ (st q p.reverse [] [] [] [] p)
  have hS₃ : update (st q p.reverse [] [] [] [] p) K.O
      ([false, false, true].reverse ++ st q p.reverse [] [] [] [] p K.O) =
      st q p.reverse [] [] [] [] ([true, false, false] ++ p) := by
    funext k
    cases k <;> rfl
  rw [hS₃] at h₃
  obtain ⟨v₄, h₄⟩ := wordS_run (M := prog) (a := K.T) (o := K.O)
    (wd := fun b => [b, true, true, true]) (self := .capBits) (next := .item) rfl (by decide)
    p.reverse v₂ (st q p.reverse [] [] [] [] ([true, false, false] ++ p)) rfl
  set o₄ := (p.flatMap fun b => [true, true, true, b]) ++ [true, false, false] ++ p with ho₄
  have hS₄ : update (update (st q p.reverse [] [] [] [] ([true, false, false] ++ p)) K.T [])
      K.O ((p.reverse.flatMap fun b => [b, true, true, true]).reverse ++
        st q p.reverse [] [] [] [] ([true, false, false] ++ p) K.O) =
      st q [] [] [] [] [] o₄ := by
    funext k
    cases k <;> simp [st, ho₄, reverse_flatMap_reverse]
  rw [hS₄] at h₄
  obtain ⟨v₅, h₅⟩ := items_run as [] [] [] o₄ v₄
  set r₆ := (as.flatMap itemOut ++ [false]).reverse with hr₆
  have h₆ := emit_run (M := prog) (self := Lab.endItems) (next := Lab.out) (k := K.R)
    (xs := [false]) rfl v₅ (st [] [] [] [] [] ((as.flatMap itemOut).reverse ++ []) o₄)
  have hS₆ : update (st [] [] [] [] [] ((as.flatMap itemOut).reverse ++ []) o₄) K.R
      ([false].reverse ++ st [] [] [] [] [] ((as.flatMap itemOut).reverse ++ []) o₄ K.R) =
      st [] [] [] [] [] r₆ o₄ := by
    funext k
    cases k <;> simp [st, hr₆, List.reverse_append]
  rw [hS₆] at h₆
  obtain ⟨v₇, S₇, h₇, hR, hO₇, hk₇⟩ := moveB_run (M := prog) (a := K.R) (b := K.O)
    (d := some) (g := id) (self := Lab.out) (next := Lab.done) rfl (by decide)
    r₆ r₆ [] v₅ (st [] [] [] [] [] r₆ o₄) (by simp [st])
    (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hA := ((h₁.trans h₂).trans h₃).trans h₄
  have hB := ((hA.le le_rfl).trans h₅).trans ((h₆.trans h₇).le le_rfl)
  refine ⟨v₇, S₇, hB.mono ?_, ?_⟩
  · have hx : (encodeSS as t).length = 2 * p.length + 1 + q.length := by
      simp only [encodeSS, List.length_append, length_delimit, hp, hq]
    have hio := length_flatMap_itemOut as
    rw [← hq] at hio
    have hc : (as.flatMap fun a => delimit (encodeNat a)).length = q.length := by rw [hq]
    simp only [List.length_reverse, hr₆, List.length_append, List.length_cons,
      List.length_nil, hio, hx]
    omega
  · rw [hO₇, bitEncode_fromSubsetSum]
    simp [st, hr₆, ho₄, hp, List.reverse_append, List.append_assoc]

end MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack.HardnessCore


namespace MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack.HardnessMachine

open Turing Function TM2Program TM2Embedding BitstringEncoding
open Cslib.Complexity.Karp Cslib.Complexity.PolynomialEncoding

/-- Disjoint workspaces, a preserved input, and comparison scratch stacks. -/
inductive K
  | norm (k : ListNatMachine.K) | core (k : HardnessCore.K)
  | raw | buffer | left | right
  deriving DecidableEq

/-- All stacks hold bits. -/
abbrev Γ : K → Type := fun _ => Bool

/-- Copy, exact normalization, canonicality check, and numeric computation. -/
inductive Lab
  | copy1 | copy2 | norm (l : ListNatMachine.Lab) | nonempty | compare
  | restore | start | core (l : HardnessCore.Lab) | bad | done
  deriving DecidableEq

def normEmb : SEmb (fun _ : ListNatMachine.K => Bool) Γ where
  e := K.norm
  inj _ _ h := K.norm.inj h
  ι _ := Equiv.refl _

def coreEmb : SEmb HardnessCore.Γ Γ where
  e := K.core
  inj _ _ h := K.core.inj h
  ι _ := Equiv.refl _

def normLabel : ListNatMachine.Lab → Lab
  | .good => .nonempty
  | .bad => .bad
  | l => .norm l

def coreLabel : HardnessCore.Lab → Lab
  | .done => .done
  | l => .core l

/-- A total finite-stack transducer for the exact source codec. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .copy1 => moveB .raw .buffer some id .copy1 .copy2
  | .copy2 => splitB .buffer .raw (.norm .input) some id id .copy2 (.norm .loop)
  | .norm l => mapS normEmb normLabel (ListNatMachine.prog l)
  | .nonempty => .peek (.norm .output) (fun _ o => o.isSome) <|
      .branch id (.goto fun _ => .compare) (.goto fun _ => .bad)
  | .compare => cmpB .raw (.norm .output) .left .right some some id id
      .compare .restore .bad
  | .restore => moveB .left (.core .X) some id .restore .start
  | .start => .load (fun _ => false) <| .goto fun _ => .core .target
  | .core l => mapS coreEmb coreLabel (HardnessCore.prog l)
  | .bad => emitR (.core .O) (bitEncode noInstance) .done
  | .done => .halt

private theorem embeds_norm :
    Embeds normEmb normLabel ListNatMachine.prog prog := by
  intro l
  cases l <;> simp [normLabel, prog, ListNatMachine.prog]

private theorem embeds_core :
    Embeds coreEmb coreLabel HardnessCore.prog prog := by
  intro l
  cases l <;> simp [coreLabel, prog, HardnessCore.prog]

private theorem encode_cons (as : List ℕ) (t : ℕ) :
    bitEncode (t :: as) = encodeSS as t := by
  change delimit (Computability.encodeNat t) ++
    ((as.map Computability.encodeNat).map delimit).flatten = _
  simp [encodeSS, List.flatMap_def, List.map_map, Function.comp_def]

private theorem decode_of_ss {x : List Bool} {as : List ℕ} {t : ℕ}
    (h : SSVerify.decodeSS x = some (as, t)) :
    bitDecode (α := List ℕ) x = some (t :: as) := by
  rw [← SSVerify.decodeSS_eq_some.mp h, ← encode_cons]
  exact bitDecode_bitEncode _

private theorem core_run (as : List ℕ) (t : ℕ) (v : Bool)
    (S : ∀ k, List (Γ k)) (hl : S .left = (encodeSS as t).reverse)
    (hc : ∀ k, S (.core k) = []) :
    ∃ v' S', RunLe prog (35 * ((encodeSS as t).length + 1) ^ 2)
      ⟨some .restore, v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core .O) = bitEncode (fromSubsetSum as t) := by
  obtain ⟨v₁, S₁, h₁, _, hx, hk⟩ := moveB_run
    (M := prog) (self := Lab.restore) (next := .start)
    (a := K.left) (b := K.core .X) (d := some) (g := id)
    rfl (by decide) (encodeSS as t).reverse (encodeSS as t).reverse
    [] v S (by simpa using hl) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hstart : Run prog 1 ⟨some .start, v₁, S₁⟩
      ⟨some (.core .target), false, S₁⟩ := Run.single rfl
  obtain ⟨v₂, C₂, h₂, ho₂⟩ := HardnessCore.run as t
  obtain ⟨S₂, hrun, ha, _⟩ := runLe_embed coreLabel embeds_core h₂ (by
    intro k
    change S₁ (.core k) = (update
      (fun j : HardnessCore.K => ([] : List (HardnessCore.Γ j)))
      .X (encodeSS as t) k).map id
    rw [List.map_id]
    by_cases h : k = .X
    · subst k
      simpa [hc] using hx
    · rw [hk (.core k) (by simp) (by simpa), hc]
      simp [h])
  refine ⟨v₂, S₂, ((h₁.trans hstart).le le_rfl |>.trans hrun).mono ?_, ?_⟩
  · simp only [List.length_reverse]
    nlinarith
  · have h := ha HardnessCore.K.O
    change S₂ (.core .O) = (C₂ .O).map id at h
    simpa only [List.map_id, ho₂] using h

private theorem compare_equal (as : List ℕ) (t : ℕ) (v : Bool)
    (S : ∀ k, List (Γ k)) (ha : S .raw = encodeSS as t)
    (hb : S (.norm .output) = encodeSS as t) (hl : S .left = [])
    (hc : ∀ k, S (.core k) = []) :
    ∃ v' S', RunLe prog (40 * ((encodeSS as t).length + 1) ^ 2)
      ⟨some .compare, v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core .O) = bitEncode (fromSubsetSum as t) := by
  have hp : prog .compare = cmpB .raw (.norm .output) .left .right
      some some id id .compare .restore .bad := rfl
  obtain ⟨v₁, S₁, h₁, hraw, hout, hleft, _, hk⟩ := cmpB_prefix hp
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (encodeSS as t) (encodeSS as t) [] (encodeSS as t) [] v S
    (by simpa using ha) (by simpa using hb)
    (by simp [IsBitBlock]) (by simp [IsBitBlock])
  obtain ⟨v₂, h₂⟩ := cmpB_last hp v₁ S₁ (by simp [hraw, hout])
  have h₂' : Run prog 1 ⟨some .compare, v₁, S₁⟩
      ⟨some .restore, v₂, S₁⟩ := by simpa [hraw, hout] using h₂
  obtain ⟨v₃, S₃, h₃, ho⟩ := core_run as t v₂ S₁
    (by simpa [hl] using hleft) (by
      intro k
      rw [hk (.core k) (by simp) (by simp) (by simp) (by simp), hc])
  exact ⟨v₃, S₃, ((h₁.trans h₂').le le_rfl |>.trans h₃).mono (by nlinarith), ho⟩

private theorem compare_unequal (x y : List Bool) (hne : x ≠ y)
    (v : Bool) (S : ∀ k, List (Γ k)) (ha : S .raw = x)
    (hb : S (.norm .output) = y) (ho : S (.core .O) = []) :
    ∃ v' S', RunLe prog (x.length + 2)
      ⟨some .compare, v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core .O) = bitEncode noInstance := by
  obtain ⟨c, v₁, S₁, hp, _, _, hr, _, _, _, _, hk⟩ := cmpB_run
    (M := prog) (self := Lab.compare) (eqL := .restore) (neL := .bad)
    (a := K.raw) (b := K.norm .output) (ta := K.left) (tb := K.right)
    (da := some) (db := some) (ea := id) (eb := id) rfl
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    x y x [] y [] v S (by simpa using ha) (by simpa using hb)
    (by simp [IsBitBlock]) (by simp [IsBitBlock])
    (by simp [EndsBitBlock]) (by simp [EndsBitBlock])
  simp only [hne, ↓reduceIte] at hr
  have he : S₁ (.core .O) = [] := by
    rw [hk (.core .O) (by simp) (by simp) (by simp) (by simp), ho]
  have hbad := emitR_run (M := prog) (self := Lab.bad) (next := .done)
    (k := K.core .O) (ys := bitEncode noInstance) rfl v₁ S₁
  refine ⟨v₁, _, (hr.trans hbad).le (by have := hp.length_le; omega), ?_⟩
  simp [he]

private theorem decodeSS_reject {x : List Bool} {ns : List ℕ}
    (hd : bitDecode x = some ns) (h : ns = [] ∨ bitEncode ns ≠ x) :
    SSVerify.decodeSS x = none := by
  cases hs : SSVerify.decodeSS x with
  | none => rfl
  | some q =>
    obtain ⟨as, t⟩ := q
    have he : ns = t :: as := by
      simpa [hd] using decode_of_ss hs
    have hc : bitEncode ns = x := by
      rw [he, encode_cons]
      exact SSVerify.decodeSS_eq_some.mp hs
    rcases h with h | h
    · simp [h] at he
    · exact (h hc).elim

private theorem accepted_run (x : List Bool) (ns : List ℕ)
    (hd : bitDecode x = some ns) (v : Bool) (S : ∀ k, List (Γ k))
    (hraw : S .raw = x) (hout : S (.norm .output) = bitEncode ns)
    (hl : S .left = []) (hc : ∀ k, S (.core k) = []) :
    ∃ v' S', RunLe prog (45 * (x.length + 1) ^ 2)
      ⟨some .nonempty, v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core .O) = reduceFromSubsetSum x := by
  have hpos : 0 < (x.length + 1) ^ 2 := by positivity
  cases ns with
  | nil =>
    change S (.norm .output) = [] at hout
    have hs : Run prog 1 ⟨some .nonempty, v, S⟩
        ⟨some .bad, false, S⟩ := by
      apply Run.single
      simp [prog, TM2.stepAux, hout]
    have hr := emitR_run (M := prog) (self := Lab.bad) (next := .done)
      (k := K.core .O) (ys := bitEncode noInstance) rfl false S
    refine ⟨false, _, (hs.trans hr).le (by nlinarith), ?_⟩
    simp [reduceFromSubsetSum, decodeSS_reject hd (Or.inl rfl), hc]
  | cons t as =>
    have hs : Run prog 1 ⟨some .nonempty, v, S⟩
        ⟨some .compare, true, S⟩ := by
      apply Run.single
      simp only [prog, TM2.stepAux, hout, encode_cons, encodeSS]
      cases Computability.encodeNat t <;> rfl
    by_cases he : encodeSS as t = x
    · obtain ⟨v', S', hr, ho⟩ := compare_equal as t true S
        (by simpa [he] using hraw) (by simpa [encode_cons] using hout) hl hc
      rw [he] at hr
      refine ⟨v', S', (hs.le le_rfl |>.trans hr).mono (by nlinarith), ?_⟩
      simpa [reduceFromSubsetSum, SSVerify.decodeSS_eq_some.mpr he] using ho
    · have hne : bitEncode (t :: as) ≠ x := by simpa [encode_cons] using he
      obtain ⟨v', S', hr, ho⟩ := compare_unequal x (bitEncode (t :: as))
        hne.symm true S hraw hout (hc .O)
      refine ⟨v', S', (hs.le le_rfl |>.trans hr).mono (by nlinarith), ?_⟩
      simpa [reduceFromSubsetSum, decodeSS_reject hd (Or.inr hne)] using ho

private theorem normalized_run (x : List Bool) (v : Bool)
    (S : ∀ k, List (Γ k))
    (hn : Agree normEmb (ListNatMachine.st x [] []
      (Cslib.Complexity.FramedCNF.NormalizeMachine.st [] [] [])) S)
    (hraw : S .raw = x) (hl : S .left = []) (hc : ∀ k, S (.core k) = []) :
    ∃ v' S', RunLe prog (70 * (x.length + 1) ^ 2)
      ⟨some (.norm .loop), v, S⟩ ⟨some .done, v', S'⟩ ∧
      S' (.core .O) = reduceFromSubsetSum x := by
  obtain ⟨v₁, S₁, hr, hf, ha⟩ := ListNatMachine.run_embedded
    normEmb normLabel embeds_norm x v S hn
  have hc' : ∀ k, S₁ (.core k) = [] := by
    intro k
    rw [hf (.core k) (fun j => by simp [normEmb]), hc]
  cases hd : bitDecode (α := List ℕ) x with
  | none =>
    have hss : SSVerify.decodeSS x = none := by
      cases hs : SSVerify.decodeSS x with
      | none => rfl
      | some q =>
        obtain ⟨as, t⟩ := q
        have h := decode_of_ss hs
        simp [hd] at h
    simp only [hd, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, normLabel] at hr
    have hbad := emitR_run (M := prog) (self := Lab.bad) (next := .done)
      (k := K.core .O) (ys := bitEncode noInstance) rfl v₁ S₁
    refine ⟨v₁, _, (hr.trans (hbad.le le_rfl)).mono (by nlinarith), ?_⟩
    simp [reduceFromSubsetSum, hss, hc']
  | some ns =>
    simp only [hd, Option.isSome_some, ↓reduceIte, normLabel] at hr
    have hout := ha ns hd ListNatMachine.K.output
    change S₁ (.norm .output) = (bitEncode ns).map id at hout
    rw [List.map_id] at hout
    obtain ⟨v₂, S₂, h₂, ho⟩ := accepted_run x ns hd v₁ S₁
      (by rw [hf .raw (fun j => by simp [normEmb]), hraw]) hout
      (by rw [hf .left (fun j => by simp [normEmb]), hl]) hc'
    exact ⟨v₂, S₂, (hr.trans h₂).mono (by nlinarith), ho⟩

/-- Total raw-input hardness reduction, with exact source rejection and
an explicit bound polynomial in encoded length, not numeric magnitude. -/
theorem run (x : List Bool) :
    ∃ v S, RunLe prog (80 * (x.length + 1) ^ 2)
      ⟨some .copy1, false, update (fun _ => []) .raw x⟩
      ⟨some .done, v, S⟩ ∧ S (.core .O) = reduceFromSubsetSum x := by
  obtain ⟨S₁, hr, hraw, _, hx, hk⟩ := copyB_run
    (M := prog) (a := K.raw) (b := K.norm .input) (t := K.buffer)
    (da := some) (dt := some) (ga := id) (gb := id) (gt := id)
    (first := .copy1) (second := .copy2) (next := .norm .loop)
    rfl rfl (by decide) (by decide) (by decide) (fun _ => rfl) (fun _ => rfl)
    x [] false (update (fun _ => []) .raw x) (by simp)
    (by simp [EndsBitBlock]) (by simp [EndsBitBlock])
  have hn : ∀ k, k ≠ ListNatMachine.K.input → S₁ (.norm k) = [] := by
    intro k h
    rw [hk (.norm k) (by simp) (by simpa) (by simp)]
    simp
  obtain ⟨v₂, S₂, h₂, ho⟩ := normalized_run x false S₁ (by
    intro k
    change S₁ (.norm k) = (ListNatMachine.st x [] []
      (Cslib.Complexity.FramedCNF.NormalizeMachine.st [] [] []) k).map id
    rw [List.map_id]
    cases k with
    | input => simpa [ListNatMachine.st] using hx
    | acc => simpa [ListNatMachine.st] using hn .acc (by decide)
    | output => simpa [ListNatMachine.st] using hn .output (by decide)
    | nat k =>
      rw [hn (.nat k) (by simp)]
      cases k <;> rfl)
    (by simpa using hraw)
    (by rw [hk .left (by simp) (by simp) (by simp)]; simp)
    (by intro k; rw [hk (.core k) (by simp) (by simp) (by simp)]; simp)
  exact ⟨v₂, S₂, (hr.le le_rfl |>.trans h₂).mono (by nlinarith), ho⟩

noncomputable instance : Fintype K := Fintype.ofList
  ([.raw, .buffer, .left, .right] ++ Finset.univ.toList.map K.norm ++
    Finset.univ.toList.map K.core) (by intro k; cases k <;> simp)

noncomputable instance : Fintype Lab := Fintype.ofList
  ([.copy1, .copy2, .nonempty, .compare, .restore, .start, .bad, .done] ++
    Finset.univ.toList.map Lab.norm ++ Finset.univ.toList.map Lab.core)
  (by intro l; cases l <;> simp)

/-- **The hardness machine as a host component.** -/
noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ k := by
    cases k with
    | norm _ | raw | buffer | left | right => infer_instance
    | core k => infer_instance
  L := Lab
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

end MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack.HardnessMachine

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack.HardnessMachine

open Cslib.Complexity.Karp

/-- **The SUBSET-SUM to MULTIPLE KNAPSACK map is polynomial-time.** The map on bit strings sending
the SUBSET-SUM encoding of numbers $a_1, \dots, a_n$ and a target $t$ to the canonical encoding of
the multiple-knapsack instance with items $(a_i, a_i)$, one knapsack of capacity $t$ and target
$t$, and every other bit string to the encoding of a fixed no-instance, is computable in
polynomial time, within a quadratic number of steps of a multi-stack Turing machine.

Source: original to this formalization; the input check follows the PARTITION hardness machine
of this library. -/
theorem isPolyTime_reduceFromSubsetSum : ComplexityTheory.IsPolyTime
    reduceFromSubsetSum :=
  Cslib.Complexity.Host.isPolyTime_reduction
    (c := comp) (cX := .raw) (cO := .core .O)
    (gX := id) (start := .copy1) (done := .done) (Equiv.refl Bool)
    reduceFromSubsetSum (Polynomial.C 80 * (Polynomial.X + 1) ^ 2)
    rfl fun x => by simpa using run x

end MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack.HardnessMachine

end
