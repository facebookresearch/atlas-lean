/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KNAPSACK is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness* (1979), KNAPSACK (MP9).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
import CSLibExt.Computability.Complexity.Karp.SubsetSumComplete
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatPairPair
import CSLibExt.Computability.Complexity.SSVerifierSum


/-!
# KNAPSACK is NP-complete

This module proves NP-completeness for binary-encoded 0/1 knapsack.

A 0/1 knapsack instance is a list of items, each a `(weight, value)` pair of natural numbers,
together with a capacity and a target value. The question is whether some sublist of the items
has total weight at most the capacity and total value at least the target. Variant: nonnegative
integers (the Garey-Johnson formulation uses positive integers). Duplicate items are distinct
occurrences, the empty selection is permitted, and a target of zero is always achievable by a
successfully decoded instance. Binary encoding matters: with unary numbers the problem is
solvable in pseudo-polynomial time, hence in P.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Knapsack

/-- **Knapsack instances.** A 0/1 knapsack instance is a triple $(I, C, T)$ of a list $I$ of items,
each a pair $(w, v)$ of natural numbers giving its weight $w$ and value $v$, a natural-number
capacity $C$, and a natural-number target value $T$. -/
abbrev KnapsackInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- **Feasible knapsack instances.** A knapsack instance $(I, C, T)$, with item list $I$, capacity
$C$ and target value $T$, is feasible when some subsequence of $I$, possibly empty, has total
weight at most $C$ and total value at least $T$. Repeated items in $I$ are distinct occurrences
that can be selected separately. -/
def KnapsackFeasible
    (i : KnapsackInstance) : Prop :=
  ∃ chosen : List (ℕ × ℕ), chosen.Sublist i.1 ∧
    (chosen.map Prod.fst).sum ≤ i.2.1 ∧ i.2.2 ≤ (chosen.map Prod.snd).sum

open Classical in
/-- **The KNAPSACK decision problem.** KNAPSACK is the decision problem that accepts a bitstring
$x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a knapsack instance
$(I, C, T)$ for which some subsequence of the item list $I$, possibly empty, has total weight at
most $C$ and total value at least $T$. Bitstrings that do not decode are rejected. -/
noncomputable def knapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KnapsackInstance) x with
  | some i => decide (KnapsackFeasible i)
  | none => false

open BitstringEncoding ComplexityTheory Cslib.Complexity Cslib.Complexity.Karp

/-! ### Mask certificates -/

private def selectItems (as : List (ℕ × ℕ)) (w : List Bool) : List (ℕ × ℕ) :=
  match as with
  | [] => []
  | a :: as => if w.headD false then a :: selectItems as w.tail else selectItems as w.tail

private theorem selectItems_sublist (as : List (ℕ × ℕ)) (w : List Bool) :
    (selectItems as w).Sublist as := by
  induction as generalizing w with
  | nil => exact .slnil
  | cons a as ih =>
    unfold selectItems
    split
    · exact (ih w.tail).cons_cons a
    · exact (ih w.tail).cons a

private theorem exists_selectItems {chosen as : List (ℕ × ℕ)} (h : chosen.Sublist as) :
    ∃ w : List Bool, w.length = as.length ∧ selectItems as w = chosen := by
  induction h with
  | slnil => exact ⟨[], rfl, rfl⟩
  | cons a _ ih =>
    obtain ⟨w, hw, rfl⟩ := ih
    exact ⟨false :: w, by simp [hw], rfl⟩
  | cons_cons a _ ih =>
    obtain ⟨w, hw, rfl⟩ := ih
    exact ⟨true :: w, by simp [hw], rfl⟩

private theorem map_selectItems (f : ℕ × ℕ → ℕ) (as : List (ℕ × ℕ)) (w : List Bool) :
    (selectItems as w).map f = SSVerify.pick (as.map f) w := by
  induction as generalizing w with
  | nil => rfl
  | cons a as ih =>
    simp only [selectItems, List.map_cons, SSVerify.pick]
    split <;> simp [ih]

private def verify (x w : List Bool) : Bool :=
  match bitDecode (α := KnapsackInstance) x with
  | none => false
  | some (as, c, t) =>
    decide ((SSVerify.pick (as.map Prod.fst) w).sum ≤ c) &&
      decide (t ≤ (SSVerify.pick (as.map Prod.snd) w).sum)

private theorem exists_certificate (x : List Bool) :
    knapsackDec x ↔ ∃ w : List Bool, w.length ≤ x.length ∧ verify x w := by
  cases h : bitDecode (α := KnapsackInstance) x with
  | none => simp [knapsackDec, verify, h]
  | some i =>
    obtain ⟨as, c, t⟩ := i
    simp only [knapsackDec, verify, h, decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨chosen, hsub, hc, ht⟩
      obtain ⟨w, hw, rfl⟩ := exists_selectItems hsub
      refine ⟨w, hw.le.trans ?_, ?_⟩
      · exact PolynomialEncoding.decoded_fst_list_length_le h
      · simpa only [← map_selectItems] using And.intro hc ht
    · rintro ⟨w, -, hc, ht⟩
      exact ⟨selectItems as w, selectItems_sublist as w,
        by simpa only [map_selectItems] using hc, by simpa only [map_selectItems] using ht⟩

private theorem diagonal_feasible (as : List ℕ) (t : ℕ) :
    KnapsackFeasible (as.map (fun a => (a, a)), t, t) ↔
      ∃ chosen : List ℕ, chosen.Sublist as ∧ chosen.sum = t := by
  constructor
  · rintro ⟨chosen, hsub, hc, ht⟩
    obtain ⟨w, -, rfl⟩ := exists_selectItems hsub
    simp only [map_selectItems, List.map_map, Function.comp_def, List.map_id_fun', id_eq]
      at hc ht
    exact ⟨SSVerify.pick as w, SSVerify.pick_sublist as w, Nat.le_antisymm hc ht⟩
  · rintro ⟨chosen, hsub, rfl⟩
    exact ⟨chosen.map (fun a => (a, a)), hsub.map _,
      by simp [List.map_map, Function.comp_def], by simp [List.map_map, Function.comp_def]⟩

/-! ### Polynomial-time verification -/

namespace BinaryComparison

open Turing Function TM2Program TM2Recursive
open EmitSS (bitsVal_cons bitsVal_nil)

private def step (tie b c : Bool) : Bool :=
  if b = c then tie else c

private def answer (tie : Bool) (a b : ℕ) : Bool :=
  decide (a < b ∨ a = b ∧ tie)

private theorem answer_bit (tie b c : Bool) (m n : ℕ) :
    answer tie (b.toNat + 2 * m) (c.toNat + 2 * n) =
      answer (step tie b c) m n := by
  apply Bool.eq_iff_iff.mpr
  cases tie <;> cases b <;> cases c <;> simp [answer, step, Bool.toNat] <;> omega

variable {K Λ : Type} [DecidableEq K] {Γ : K → Type}

/-- Compare padded little-endian operands, retaining the last differing bit. -/
private def cmp (a b : K) (da : Γ a → Option Bool) (db : Γ b → Option Bool)
    (self next : Bool → Λ) (tie : Bool) :
    TM2.Stmt Γ Λ Bool :=
  .peek a (fun _ o => !isBit da o) <|
    .peek b (fun s o => s && !isBit db o) <|
    .branch id (.goto fun _ => next tie)
      (.pop a (fun _ oa => bitOf da oa) <|
        .pop b (fun x ob => step tie x (bitOf db ob)) <| .goto self)

private theorem value_head_tail (xs : List Bool) :
    bitsVal xs = (xs.headD false).toNat + 2 * bitsVal xs.tail := by
  cases xs <;> simp

private theorem run {M : Λ → TM2.Stmt Γ Λ Bool} {a b : K}
    {da : Γ a → Option Bool} {db : Γ b → Option Bool} {ga : Bool → Γ a} {gb : Bool → Γ b}
    {self next : Bool → Λ} (hp : ∀ tie, M (self tie) = cmp a b da db self next tie)
    (hab : a ≠ b) (hga : ∀ v, da (ga v) = some v) (hgb : ∀ v, db (gb v) = some v)
    (xs ys : List Bool) (tie v : Bool) (S : ∀ k, List (Γ k))
    (ha : S a = xs.map ga) (hb : S b = ys.map gb) :
    ∃ z T, RunLe M (xs.length + ys.length + 1)
      ⟨some (self tie), v, S⟩
      ⟨some (next (answer tie (bitsVal xs) (bitsVal ys))), z, T⟩ ∧
      T a = [] ∧ T b = [] ∧ ∀ k, k ≠ a → k ≠ b → T k = S k := by
  by_cases he : xs = [] ∧ ys = []
  · obtain ⟨rfl, rfl⟩ := he
    refine ⟨true, S, (Run.single ?_).le (by simp), ha, hb, fun _ _ _ => rfl⟩
    cases tie <;> simp [hp, cmp, TM2.stepAux, isBit, ha, hb, answer]
  · let xa := xs.headD false
    let yb := ys.headD false
    let t := step tie xa yb
    let U := update (update S a (xs.tail.map ga)) b (ys.tail.map gb)
    have first : Run M 1 ⟨some (self tie), v, S⟩ ⟨some (self t), t, U⟩ := by
      apply Run.single
      rw [hp]
      cases xs <;> cases ys
      · exact (he ⟨rfl, rfl⟩).elim
      all_goals simp [cmp, TM2.stepAux, isBit, bitOf, ha, hb, hga, hgb, U, t, xa, yb,
        hab.symm]
    have hlen : xs.tail.length + ys.tail.length + 1 < xs.length + ys.length + 1 := by
      cases xs <;> cases ys <;> simp_all
      omega
    obtain ⟨z, T, rest, hTa, hTb, hT⟩ :=
      run hp hab hga hgb xs.tail ys.tail t t U (by simp [U, hab]) (by simp [U])
    have hout : answer tie (bitsVal xs) (bitsVal ys) =
        answer t (bitsVal xs.tail) (bitsVal ys.tail) := by
      rw [value_head_tail xs, value_head_tail ys, answer_bit]
    rw [hout]
    exact ⟨z, T, ((first.le le_rfl).trans rest).mono (by omega), hTa, hTb,
      fun k hka hkb => (hT k hka hkb).trans (by simp [U, hka, hkb])⟩
termination_by xs.length + ys.length

end BinaryComparison

namespace Verifier

open Turing Function TM2Program TM2Embedding Computability TM2Recursive
open Cslib.Complexity.SatVerifier (Sym)
open Cslib.Complexity.PolynomialEncoding

private inductive Stack
  | decode (k : ListNatPairPair.K)
  | sum (values : Bool) (k : SSVerify.K)
  | mask | scratch | bits
  deriving DecidableEq, Fintype

@[reducible] private def Alphabet : Stack → Type
  | .sum _ _ => Sym
  | _ => Bool

private inductive Label
  | decode (l : ListNatPairPair.Lab)
  | copy | split
  | transfer (values : Bool) | restore (values : Bool)
  | sum (values : Bool) (l : SSVerify.Lab)
  | reverse (values : Bool) | compare (values tie : Bool)
  | accept | reject
  deriving DecidableEq, Fintype

private def decodeEmb : SEmb (fun _ : ListNatPairPair.K => Bool) Alphabet where
  e := Stack.decode
  inj _ _ h := Stack.decode.inj h
  ι _ := Equiv.refl Bool

private def sumEmb (b : Bool) : SEmb (fun _ : SSVerify.K => Sym) Alphabet where
  e := Stack.sum b
  inj _ _ h := (Stack.sum.inj h).2
  ι _ := Equiv.refl Sym

private def decodeLabel : ListNatPairPair.Lab → Label
  | .good => .copy
  | .bad => .reject
  | l => .decode l

private def sumLabel (b : Bool) : SSVerify.Lab → Label
  | .yes | .no => .reverse b
  | l => .sum b l

@[reducible] private def items (b : Bool) : Stack := .decode (.items (.output b))

@[reducible] private def endpoint (b : Bool) : Stack :=
  .decode (.pair (if b then .right else .left))

private def afterCompare (b yes : Bool) : Label :=
  if yes then if b then .accept else .transfer true else .reject

private def program : Label → TM2.Stmt Alphabet Label Bool
  | .decode l => mapS decodeEmb decodeLabel (ListNatPairPair.prog l)
  | .copy => moveB .mask .scratch some id .copy .split
  | .split => splitB .scratch (.sum false .W) (.sum true .W) some Sym.bit Sym.bit
      .split (.transfer false)
  | .transfer b => moveB (items b) .scratch some id (.transfer b) (.restore b)
  | .restore b => moveB .scratch (.sum b .X) some Sym.bit (.restore b) (.sum b .next)
  | .sum b l => mapS (sumEmb b) (sumLabel b) (SSVerify.prog l)
  | .reverse b => moveB (.sum b .B) .bits Sym.bit? id (.reverse b) (.compare b true)
  | .compare false tie => BinaryComparison.cmp .bits (endpoint false) some some
      (.compare false) (afterCompare false) tie
  | .compare true tie => BinaryComparison.cmp (endpoint true) .bits some some
      (.compare true) (afterCompare true) tie
  | .accept | .reject => .halt

private theorem embeds_decode : Embeds decodeEmb decodeLabel ListNatPairPair.prog program := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem embeds_sum (b : Bool) : Embeds (sumEmb b) (sumLabel b) SSVerify.prog program := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

private theorem copy_mask (w : List Bool) (v : Bool) (S : ∀ k, List (Alphabet k))
    (hm : S .mask = w) (ht : S .scratch = []) (hW : ∀ b, S (.sum b .W) = []) :
    ∃ T, Run program (2 * w.length + 2)
      ⟨some .copy, v, S⟩ ⟨some (.transfer false), false, T⟩ ∧
      T .scratch = [] ∧ (∀ b, T (.sum b .W) = w.map Sym.bit) ∧
      ∀ k, k ≠ .mask → k ≠ .scratch → (∀ b, k ≠ .sum b .W) → T k = S k := by
  obtain ⟨z, U, h₁, _, hrev, hframe⟩ := moveB_run
    (M := program) (a := Stack.mask) (b := .scratch) (d := some) (g := id)
    (self := Label.copy) (next := .split) rfl (by decide) w w [] v S
    (by simpa using hm) (by simp [IsBitBlock]) rfl
  obtain ⟨T, h₂, hclear, hfalse, htrue, hother⟩ := splitB_run
    (M := program) (a := Stack.scratch) (b := .sum false .W) (c := .sum true .W)
    (d := some) (gb := Sym.bit) (gc := Sym.bit) (self := Label.split)
    (next := .transfer false) rfl (by decide) (by decide) (by decide) id (fun _ => rfl)
    w.reverse [] z U rfl (by simpa [ht] using hrev)
  refine ⟨T, (h₁.trans h₂).of_eq (by simp; omega), hclear, ?_, ?_⟩
  · intro b
    cases b
    · simpa [List.map_reverse, hframe (.sum false .W) (by decide) (by decide), hW] using hfalse
    · simpa [List.map_reverse, hframe (.sum true .W) (by decide) (by decide), hW] using htrue
  · intro k h₁ h₂ hs
    rw [hother k h₂ (hs false) (hs true), hframe k h₁ h₂]

private theorem sum_run (b : Bool) (as : List ℕ) (w : List Bool) (v : Bool)
    (S : ∀ k, List (Alphabet k))
    (hs : S (items b) = bitEncode as) (ht : S .scratch = []) (hb : S .bits = [])
    (hw : S (.sum b .W) = w.map Sym.bit) (he : ∀ k, k ≠ .W → S (.sum b k) = []) :
    let n := (bitEncode as).length
    let result := encodeNat (SSVerify.pick as w).sum
    ∃ z T, RunLe program (n * (2 * n + 10) + 6)
      ⟨some (.transfer b), v, S⟩ ⟨some (.compare b true), z, T⟩ ∧
      T .bits = result ∧ T .scratch = [] ∧ result.length ≤ n ∧
      ∀ k, k ≠ items b → k ≠ .bits → k ≠ .scratch →
        (∀ j, k ≠ .sum b j) → T k = S k := by
  intro n result
  obtain ⟨v₁, S₁, r₁, _, hs₁, hx, hf₁⟩ := Host.move2_run
    (M := program) (a := items b) (t := Stack.scratch) (b := .sum b .X)
    (d := some) (gt := id) (dt := some) (g := Sym.bit)
    (l₁ := .transfer b) (l₂ := .restore b) (l₃ := .sum b .next)
    rfl rfl (by simp [items]) (by simp) (by simp [items]) (fun _ => rfl)
    (bitEncode as) (bitEncode as) [] v S (hs.trans (List.append_nil _).symm)
    (by unfold IsBitBlock; rfl) rfl ht
  have henc : bitEncode as = as.flatMap (fun a => delimit (encodeNat a)) := by
    change ((as.map encodeNat).map delimit).flatten = _
    simp only [List.flatMap_def, List.map_map, Function.comp_def]
  obtain ⟨v₂, _, S₂, r₂, hsum, hf₂⟩ := SSVerifierSum.sum_embed (sumEmb b)
    (sumLabel b) program (embeds_sum b) rfl as w v₁ S₁ (by
      intro k
      change S₁ (.sum b k) = (SSVerify.st _ _ [] [] [] k).map id
      rw [List.map_id]
      cases k with
      | X => rw [hx, he .X (by decide), List.append_nil, henc]; rfl
      | W =>
        rw [hf₁ _ (by simp [items]) (by simp) (by simp), hw]
        rfl
      | T | A | B | P | Q =>
        rw [hf₁ _ (by simp [items]) (by simp) (by simp), he _ (by decide)]
        rfl)
  have hres : S₂ (.sum b .B) = result.reverse.map Sym.bit := by
    have h := hsum SSVerify.K.B
    change S₂ (.sum b .B) = ((result.map Sym.bit).reverse).map id at h
    simpa [List.map_reverse] using h
  have hbits : S₂ .bits = [] := by
    rw [hf₂ _ (by simp [sumEmb]), hf₁ _ (by simp [items]) (by simp) (by simp), hb]
  obtain ⟨z, T, r₃, _, hT, hf₃⟩ := moveB_run
    (M := program) (a := Stack.sum b .B) (b := .bits) (d := Sym.bit?) (g := id)
    (self := Label.reverse b) (next := .compare b true) rfl (by simp)
    result.reverse (result.reverse.map Sym.bit) [] v₂ S₂
    (by simpa using hres) (by simp [IsBitBlock, Sym.bit?]) rfl
  have hlen : result.length ≤ n := by
    have hd := (SSVerify.numsAux_eq_some n (bitEncode as) as le_rfl).mpr henc
    obtain ⟨_, _, _, hrun⟩ := SSVerify.loop_run n [] n (bitEncode as) w 0 v₁
      le_rfl (by simp [n, TM2Recursive.encodeNat_zero])
    simpa [result] using (hrun as hd).1
  rw [← henc] at r₂
  refine ⟨z, T, (((r₁.le le_rfl).trans r₂).trans (r₃.le le_rfl)).mono ?_,
    by simpa [hbits] using hT, ?_, hlen, ?_⟩
  · simp only [List.length_reverse]
    change (2 * n + 2 + (n * (2 * n + 6) + n + 3)) + (result.length + 1) ≤ _
    nlinarith
  · rw [hf₃ _ (by simp) (by simp), hf₂ _ (by simp [sumEmb]), hs₁]
  · intro k hi hb ht hsum
    rw [hf₃ k (hsum .B) hb, hf₂ k (fun j => (hsum j).symm),
      hf₁ k hi ht (hsum .X)]

private theorem answer_le (m n : ℕ) : BinaryComparison.answer true m n = decide (m ≤ n) := by
  apply Bool.eq_iff_iff.mpr
  simp [BinaryComparison.answer, Nat.le_iff_lt_or_eq]

private theorem compare_run (b : Bool) (m n : ℕ) (v : Bool) (S : ∀ k, List (Alphabet k))
    (hm : S .bits = encodeNat m) (hn : S (endpoint b) = encodeNat n) :
    ∃ z T, RunLe program ((encodeNat m).length + (encodeNat n).length + 1)
      ⟨some (.compare b true), v, S⟩
      ⟨some (afterCompare b (if b then decide (n ≤ m) else decide (m ≤ n))), z, T⟩ ∧
      T .bits = [] ∧
      ∀ k, k ≠ .bits → k ≠ endpoint b → T k = S k := by
  cases b
  · obtain ⟨z, T, hr, ht, _, hf⟩ := BinaryComparison.run
      (M := program) (a := Stack.bits) (b := endpoint false)
      (ga := id) (gb := id) (da := some) (db := some)
      (self := Label.compare false) (next := afterCompare false)
      (fun _ => rfl) (by decide) (fun _ => rfl) (fun _ => rfl)
      (encodeNat m) (encodeNat n) true v S (by simpa using hm) (by simpa using hn)
    exact ⟨z, T, by simpa [bitsVal_encodeNat, answer_le] using hr, ht, hf⟩
  · obtain ⟨z, T, hr, _, ht, hf⟩ := BinaryComparison.run
      (M := program) (a := endpoint true) (b := Stack.bits)
      (ga := id) (gb := id) (da := some) (db := some)
      (self := Label.compare true) (next := afterCompare true)
      (fun _ => rfl) (by decide) (fun _ => rfl) (fun _ => rfl)
      (encodeNat n) (encodeNat m) true v S (by simpa using hn) (by simpa using hm)
    exact ⟨z, T, by simpa [bitsVal_encodeNat, answer_le, Nat.add_comm] using hr,
      ht, fun k hk hke => hf k hke hk⟩

private def projection (b : Bool) (as : List (ℕ × ℕ)) : List ℕ :=
  as.map (if b then Prod.snd else Prod.fst)

private theorem run_decoded (as : List (ℕ × ℕ)) (c t : ℕ) (w : List Bool) (v : Bool)
    (S : ∀ k, List (Alphabet k))
    (hi : ∀ b, S (items b) = bitEncode (projection b as))
    (hc : S (endpoint false) = encodeNat c) (hv : S (endpoint true) = encodeNat t)
    (hs : S .scratch = []) (hb : S .bits = []) (hw : S .mask = w)
    (he : ∀ b k, S (.sum b k) = []) :
    let n := (bitEncode (projection false as)).length +
      (bitEncode (projection true as)).length + (encodeNat c).length + (encodeNat t).length
    let weight := (SSVerify.pick (projection false as) w).sum
    let value := (SSVerify.pick (projection true as) w).sum
    ∃ z T, RunLe program (10 * (n + 1) ^ 2 + 2 * w.length + 20)
      ⟨some .copy, v, S⟩ ⟨some (if weight ≤ c ∧ t ≤ value then .accept else .reject), z, T⟩ :=
  by
    intro n weight value
    obtain ⟨U, copy, hscratch, hmask, hcopy⟩ := copy_mask w v S hw hs (fun b => he b .W)
    have hcopy_decode (k : ListNatPairPair.K) : U (.decode k) = S (.decode k) :=
      hcopy _ (by simp) (by simp) (by simp)
    have hu (b : Bool) (k : SSVerify.K) (hk : k ≠ .W) : U (.sum b k) = [] := by
      rw [hcopy _ (by simp) (by simp) (by simp [hk]), he]
    have hu_bits : U .bits = [] := by rw [hcopy _ (by simp) (by simp) (by simp), hb]
    obtain ⟨v₁, U₁, weightRun, hwbits, hwscratch, hwlen, hwframe⟩ :=
      sum_run false (projection false as) w false U
        ((hcopy_decode _).trans (hi false)) hscratch hu_bits (hmask false) (hu false)
    have hcapacity : U₁ (endpoint false) = encodeNat c := by
      rw [hwframe _ (by simp [items, endpoint]) (by decide) (by decide) (by simp [endpoint])]
      exact (hcopy_decode (.pair .left)).trans hc
    obtain ⟨v₂, U₂, weightCmp, hclear, hcframe⟩ :=
      compare_run false weight c v₁ U₁ hwbits hcapacity
    have first := ((copy.le le_rfl).trans weightRun).trans weightCmp
    by_cases hweight : weight ≤ c
    · simp only [hweight, decide_true, Bool.false_eq_true, ↓reduceIte, afterCompare] at first
      have hpass (k : Stack) (hb : k ≠ Stack.bits) (hc : k ≠ endpoint false)
          (hi : k ≠ items false) (ht : k ≠ Stack.scratch) (hj : ∀ j, k ≠ Stack.sum false j) :
          U₂ k = U k := by
        rw [hcframe k hb hc, hwframe k hi hb ht hj]
      have hvals : U₂ (items true) = bitEncode (projection true as) := by
        rw [hpass _ (by decide) (by decide) (by decide) (by decide) (by simp [items]),
          hcopy_decode (.items (.output true)), hi]
      have htarget : U₂ (endpoint true) = encodeNat t := by
        rw [hpass _ (by decide) (by decide) (by decide) (by decide) (by simp [endpoint])]
        exact (hcopy_decode (.pair .right)).trans hv
      have hs₂ : U₂ .scratch = [] :=
        (hcframe _ (by decide) (by decide)).trans hwscratch
      have hside (k : SSVerify.K) : U₂ (.sum true k) = U (.sum true k) :=
        hpass _ (by simp) (by simp [endpoint]) (by simp [items]) (by simp) (by simp)
      obtain ⟨v₃, U₃, valueRun, hvbits, _, hvlen, hvframe⟩ :=
        sum_run true (projection true as) w v₂ U₂ hvals hs₂ hclear
          ((hside .W).trans (hmask true)) (fun k hk => (hside k).trans (hu true k hk))
      have ht₃ : U₃ (endpoint true) = encodeNat t := by
        rw [hvframe _ (by decide) (by decide) (by decide) (by simp [endpoint]), htarget]
      obtain ⟨z, T, valueCmp, _, _⟩ := compare_run true value t v₃ U₃ hvbits ht₃
      refine ⟨z, T, ?_⟩
      have both := (first.trans valueRun).trans valueCmp
      simp only [↓reduceIte, afterCompare, decide_eq_true_eq, hweight, true_and] at both ⊢
      change (encodeNat weight).length ≤ (bitEncode (projection false as)).length at hwlen
      change (encodeNat value).length ≤ (bitEncode (projection true as)).length at hvlen
      have hleft : (bitEncode (projection false as)).length ≤ n := by dsimp [n]; omega
      have hright : (bitEncode (projection true as)).length ≤ n := by dsimp [n]; omega
      have hcost₁ := Nat.mul_le_mul hleft
        (show 2 * (bitEncode (projection false as)).length + 10 ≤ 2 * n + 10 by omega)
      have hcost₂ := Nat.mul_le_mul hright
        (show 2 * (bitEncode (projection true as)).length + 10 ≤ 2 * n + 10 by omega)
      have hlength : (encodeNat weight).length + (encodeNat value).length +
          (encodeNat c).length + (encodeNat t).length ≤ n := by dsimp [n]; omega
      exact both.mono (by nlinarith only [hcost₁, hcost₂, hlength, Nat.zero_le n])
    · simp only [hweight, decide_false, Bool.false_eq_true, ↓reduceIte, afterCompare] at first
      refine ⟨v₂, U₂, ?_⟩
      simp only [hweight, false_and, ↓reduceIte]
      change (encodeNat weight).length ≤ (bitEncode (projection false as)).length at hwlen
      have hleft : (bitEncode (projection false as)).length ≤ n := by dsimp [n]; omega
      have hcost := Nat.mul_le_mul hleft
        (show 2 * (bitEncode (projection false as)).length + 10 ≤ 2 * n + 10 by omega)
      have hlength : (encodeNat weight).length + (encodeNat c).length ≤ n := by
        dsimp [n]; omega
      exact first.mono (by nlinarith only [hcost, hlength, Nat.zero_le n])

private instance alphabetFintype (k : Stack) : Fintype (Alphabet k) := by
  cases k <;> infer_instance

private noncomputable abbrev comp : Host.Comp where
  K := Stack
  Γ := Alphabet
  L := Label
  prog := program
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

private theorem isPolyTime_verify :
    IsPolyTime (fun q : List Bool × List Bool => verify q.1 q.2) := by
  apply Host.isPolyTime_verifier (c := comp)
    (cX := .decode (.pair (.pair .input))) (cW := .mask) (gX := id) (gW := id)
    (start := .decode (.split .read)) (yes := .accept) (no := .reject)
    verify (Polynomial.C 100 * (Polynomial.X + 1) ^ 2)
    (by decide) (by decide) rfl rfl
  intro x w
  let S := update (update (fun k : Stack => ([] : List (Alphabet k)))
    (.decode (.pair (.pair .input))) x) .mask w
  have hin : Agree decodeEmb (ListNatPairPair.st [] x [] [] [] []) S := by
    intro k
    change S (.decode k) = (ListNatPairPair.st [] x [] [] [] [] k).map id
    rw [List.map_id]
    cases k with
    | items k =>
      cases k with
      | input | acc _ | output _ => simp [S, ListNatPairPair.st, ListNatPair.st]
      | pair k =>
        change [] = NatPair.st [] [] [] [] [] [] k
        cases k with
        | pair k => cases k <;> rfl
        | buffer | left | right => rfl
    | pair k =>
      cases k with
      | pair k => cases k <;>
          simp [S, ListNatPairPair.st, NatPair.st]
      | buffer | left | right => simp [S, ListNatPairPair.st, NatPair.st]
  obtain ⟨v₁, T, decode, hframe, hfields⟩ := ListNatPairPair.run_embedded
    decodeEmb decodeLabel embeds_decode x [] [] [] [] false S hin
  cases hd : bitDecode (α := KnapsackInstance) x with
  | none =>
    refine ⟨v₁, T, ?_⟩
    simpa only [List.map_id, hd, verify, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      decodeLabel, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      using decode.mono (show 9 * x.length + 2 ≤ 100 * (x.length + w.length + 1) ^ 2 by
        have hn := Nat.le_self_pow (a := x.length + w.length + 1) (n := 2) (by decide)
        omega)
  | some i =>
    obtain ⟨as, c, t⟩ := i
    have fields := hfields as c t hd
    have hitems (b : Bool) : T (items b) = bitEncode (projection b as) := by
      have h := fields (.items (.output b))
      change T (items b) = (ListNatPairPair.st [] [] (bitEncode (as.map Prod.fst) ++ [])
        (bitEncode (as.map Prod.snd) ++ []) (encodeNat c ++ []) (encodeNat t ++ [])
        (.items (.output b))).map id at h
      cases b <;> simpa [projection, ListNatPairPair.st, ListNatPair.st] using h
    have hc : T (endpoint false) = encodeNat c := by
      have h := fields (.pair .left)
      change T (endpoint false) = (encodeNat c ++ []).map id at h
      simpa using h
    have hv : T (endpoint true) = encodeNat t := by
      have h := fields (.pair .right)
      change T (endpoint true) = (encodeNat t ++ []).map id at h
      simpa using h
    have hother (k : Stack) (hk : ∀ d, Stack.decode d ≠ k) : T k = S k :=
      hframe k hk
    obtain ⟨z, U, hr⟩ := run_decoded as c t w v₁ T hitems hc hv
      (by rw [hother _ (by simp)]; rfl)
      (by rw [hother _ (by simp)]; rfl)
      (by rw [hother _ (by simp)]; rfl)
      (fun b k => by rw [hother _ (by simp)]; rfl)
    simp only [hd, Option.isSome_some, ↓reduceIte, decodeLabel] at decode
    have hlen := ListNatPairPair.output_length_le hd
    refine ⟨z, U, ?_⟩
    simp only [List.map_id, verify, hd, Bool.and_eq_true, decide_eq_true_eq, projection,
      Bool.false_eq_true, ↓reduceIte, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at *
    exact (decode.trans hr).mono (by
      let n := (bitEncode (as.map Prod.fst)).length + (bitEncode (as.map Prod.snd)).length +
        (encodeNat c).length + (encodeNat t).length
      have hbound : n + 1 ≤ 2 * (x.length + w.length + 1) := by
        change n ≤ 2 * x.length at hlen
        omega
      have hp := Nat.pow_le_pow_left hbound 2
      change 9 * x.length + 2 + (10 * (n + 1) ^ 2 + 2 * w.length + 20) ≤ _
      have hn := Nat.le_self_pow (a := x.length + w.length + 1) (n := 2) (by decide)
      nlinarith only [hp, hn, Nat.zero_le x.length, Nat.zero_le w.length])

end Verifier

/-! ### Reduction using equal weights and values

The bitstring transducer duplicates binary payloads while changing their framing. The
VERTEX-COVER reduction supplies canonical SUBSET-SUM strings even on malformed inputs,
so correctness of the transducer on encodings suffices for the composed reduction.
-/

namespace Reduction

open Turing Function TM2Program Computability BitstringEncoding ComplexityTheory
open Cslib.Complexity Cslib.Complexity.Karp Cslib.Complexity.PolynomialEncoding

private def pair (p : List Bool) : List Bool := delimit p ++ p

private def encodeItems (x : List Bool) : List Bool :=
  match _h : undelimit x with
  | none => []
  | some (p, r) => delimit (pair p) ++ encodeItems r
termination_by x.length
decreasing_by
  have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp _h
  rw [hx, List.length_append, length_delimit]
  omega

private def transform (x : List Bool) : List Bool :=
  match undelimit x with
  | none => []
  | some (p, r) => delimit (encodeItems r) ++ pair p

private inductive Stack | input | rev | left | right | pair | payload | acc | out
  deriving DecidableEq

private inductive Label
  | read (item : Bool) | split (item : Bool)
  | first (item : Bool) | second (item : Bool) | pair (item : Bool)
  | frame | loop | finish | outer | output | done
  deriving DecidableEq, Fintype

private def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Bool
  | .read b => FramedCNF.Block.read .input .rev some id (.read b) (.split b)
      (if b then .finish else .done)
  | .split b => splitB .rev .left .right some id id (.split b) (.first b)
  | .first b => emitFrame .left .pair some id (.first b) (.second b)
  | .second b => moveB .right .pair some id (.second b) (.pair b)
  | .pair false => moveB .pair .out some id (.pair false) .loop
  | .pair true => moveB .pair .payload some id (.pair true) .frame
  | .frame => emitFrame .payload .acc some id .frame .loop
  | .loop => .peek .input (fun _ o => o.isSome) <| .goto fun b =>
      if b then .read true else .finish
  | .finish => moveB .acc .payload some id .finish .outer
  | .outer => emitFrame .payload .acc some id .outer .output
  | .output => moveB .acc .out some id .output .done
  | .done => .halt

private def contents (x r a b p l acc out : List Bool) : Stack → List Bool
  | .input => x
  | .rev => r
  | .left => a
  | .right => b
  | .pair => p
  | .payload => l
  | .acc => acc
  | .out => out

private def ready (x acc out : List Bool) : Stack → List Bool :=
  contents x [] [] [] [] [] acc out

private theorem read_pair (item : Bool) (p r acc out : List Bool) (v : Bool) :
    ∃ z, Run program (4 * p.length + 4)
      ⟨some (.read item), v, ready (delimit p ++ r) acc out⟩
      ⟨some (.pair item), z, contents r [] [] [] (pair p).reverse [] acc out⟩ := by
  obtain ⟨S₁, h₁, hx₁, hr₁, hf₁⟩ := FramedCNF.Block.run_delimit
    (M := program) (a := Stack.input) (b := .rev) (d := some) (g := id)
    (self := Label.read item) (good := .split item) (bad := if item then .finish else .done)
    rfl (by decide) id (fun _ => rfl) p r v (ready (delimit p ++ r) acc out)
    (by simp [ready, contents])
  have e₁ : S₁ = contents r p.reverse [] [] [] [] acc out := by
    funext k
    cases k with
    | input => exact hx₁
    | rev => simpa [ready, contents] using hr₁
    | left | right | pair | payload | acc | out => exact hf₁ _ (by decide) (by decide)
  subst S₁
  obtain ⟨S₂, h₂, hr₂, hl₂, hright₂, hf₂⟩ := splitB_run
    (M := program) (a := Stack.rev) (b := .left) (c := .right) (d := some)
    (gb := id) (gc := id) (self := Label.split item) (next := .first item)
    rfl (by decide) (by decide) (by decide) id (fun _ => rfl)
    p.reverse [] false (contents r p.reverse [] [] [] [] acc out) rfl (by simp [contents])
  have e₂ : S₂ = contents r [] p p [] [] acc out := by
    funext k
    cases k with
    | rev => exact hr₂
    | left => simpa [contents] using hl₂
    | right => simpa [contents] using hright₂
    | input | pair | payload | acc | out => exact hf₂ _ (by decide) (by decide) (by decide)
  subst S₂
  obtain ⟨S₃, h₃, hl₃, hp₃, hf₃⟩ := emitFrame_run
    (M := program) (a := Stack.left) (b := .pair) (d := some) (g := id)
    (self := Label.first item) (next := .second item)
    rfl (by decide) id (fun _ => rfl) p [] false (contents r [] p p [] [] acc out)
    rfl (by simp [contents])
  have e₃ : S₃ = contents r [] [] p (delimit p).reverse [] acc out := by
    funext k
    cases k with
    | left => exact hl₃
    | pair => simpa [contents] using hp₃
    | input | rev | right | payload | acc | out => exact hf₃ _ (by decide) (by decide)
  subst S₃
  obtain ⟨z, S₄, h₄, hm₄, hp₄, hf₄⟩ := moveB_run
    (M := program) (a := Stack.right) (b := .pair) (d := some) (g := id)
    (self := Label.second item) (next := .pair item) rfl (by decide) p p [] false
    (contents r [] [] p (delimit p).reverse [] acc out)
    (by simp [contents]) (by simp [IsBitBlock]) rfl
  have e₄ : S₄ = contents r [] [] [] (pair p).reverse [] acc out := by
    funext k
    cases k with
    | right => exact hm₄
    | pair => simpa [contents, pair, List.reverse_append] using hp₄
    | input | rev | left | payload | acc | out => exact hf₄ _ (by decide) (by decide)
  subst S₄
  exact ⟨z, (((h₁.trans h₂).trans h₃).trans h₄).of_eq (by simp; omega)⟩

private theorem emit_target (p r : List Bool) (v : Bool) :
    ∃ z, Run program ((pair p).length + 1)
      ⟨some (.pair false), v, contents r [] [] [] (pair p).reverse [] [] []⟩
      ⟨some .loop, z, ready r [] (pair p)⟩ := by
  obtain ⟨z, S, hr, hclear, hout, hf⟩ := moveB_run
    (M := program) (a := Stack.pair) (b := .out) (d := some) (g := id)
    (self := Label.pair false) (next := .loop) rfl (by decide)
    (pair p).reverse (pair p).reverse [] v (contents r [] [] [] (pair p).reverse [] [] [])
    (by simp [contents]) (by simp [IsBitBlock]) rfl
  have he : S = ready r [] (pair p) := by
    funext k
    cases k with
    | pair => exact hclear
    | out => simpa [contents, ready] using hout
    | input | rev | left | right | payload | acc => exact hf _ (by decide) (by decide)
  exact ⟨z, he ▸ hr.of_eq (by simp)⟩

private theorem emit_item (p r acc out : List Bool) (v : Bool) :
    Run program (2 * (pair p).length + 2)
      ⟨some (.pair true), v, contents r [] [] [] (pair p).reverse [] acc out⟩
      ⟨some .loop, false, ready r ((delimit (pair p)).reverse ++ acc) out⟩ := by
  obtain ⟨z, S, hr, hclear, hp, hf⟩ := moveB_run
    (M := program) (a := Stack.pair) (b := .payload) (d := some) (g := id)
    (self := Label.pair true) (next := .frame) rfl (by decide)
    (pair p).reverse (pair p).reverse [] v
    (contents r [] [] [] (pair p).reverse [] acc out)
    (by simp [contents]) (by simp [IsBitBlock]) rfl
  have he : S = contents r [] [] [] [] (pair p) acc out := by
    funext k
    cases k with
    | pair => exact hclear
    | payload => simpa [contents] using hp
    | input | rev | left | right | acc | out => exact hf _ (by decide) (by decide)
  subst S
  obtain ⟨T, hframe, hclear, ha, hrest⟩ := emitFrame_run
    (M := program) (a := Stack.payload) (b := .acc) (d := some) (g := id)
    (self := Label.frame) (next := .loop) rfl (by decide) id (fun _ => rfl)
    (pair p) [] z (contents r [] [] [] [] (pair p) acc out) rfl (by simp [contents])
  have he : T = ready r ((delimit (pair p)).reverse ++ acc) out := by
    funext k
    cases k with
    | payload => exact hclear
    | acc => simpa [contents, ready] using ha
    | input | rev | left | right | pair | out => exact hrest _ (by decide) (by decide)
  exact he ▸ (hr.trans hframe).of_eq (by simp; omega)

private theorem finish_run (acc out : List Bool) (v : Bool) (S : Stack → List Bool)
    (ha : S .acc = acc) (hp : S .payload = []) (ho : S .out = out) :
    ∃ z T, Run program (4 * acc.length + 4) ⟨some .finish, v, S⟩ ⟨some .done, z, T⟩ ∧
      T .out = delimit acc.reverse ++ out := by
  obtain ⟨v₁, S₁, r₁, ha₁, hp₁, hf₁⟩ := moveB_run
    (M := program) (a := Stack.acc) (b := .payload) (d := some) (g := id)
    (self := Label.finish) (next := .outer) rfl (by decide)
    acc acc [] v S (ha.trans (List.append_nil _).symm) (by unfold IsBitBlock; rfl) rfl
  obtain ⟨S₂, r₂, _, ha₂, hf₂⟩ := emitFrame_run
    (M := program) (a := Stack.payload) (b := .acc) (d := some) (g := id)
    (self := Label.outer) (next := .output) rfl (by decide) id (fun _ => rfl)
    acc.reverse [] v₁ S₁ rfl (by simpa [hp] using hp₁)
  have he : S₂ .acc = (delimit acc.reverse).reverse := by
    simpa [ha₁] using ha₂
  obtain ⟨z, T, r₃, _, hout, _⟩ := moveB_run
    (M := program) (a := Stack.acc) (b := .out) (d := some) (g := id)
    (self := Label.output) (next := .done) rfl (by decide)
    (delimit acc.reverse).reverse (delimit acc.reverse).reverse [] false S₂
    (he.trans (List.append_nil _).symm) (by unfold IsBitBlock; rfl) rfl
  refine ⟨z, T, ((r₁.trans r₂).trans r₃).of_eq ?_, ?_⟩
  · simp [length_delimit]; omega
  · simpa [hf₂ .out (by decide) (by decide), hf₁ .out (by decide) (by decide), ho]
      using hout

private theorem read_failure (item : Bool) (x rev acc out : List Bool) (v : Bool)
    (h : undelimit x = none) :
    ∃ z y b, RunLe program (x.length + 1)
      ⟨some (.read item), v, contents x rev [] [] [] [] acc out⟩
      ⟨some (if item then .finish else .done), z, contents y b [] [] [] [] acc out⟩ := by
  cases x with
  | nil =>
    refine ⟨false, [], rev, (Run.single ?_).le (by simp)⟩
    simp [program, FramedCNF.Block.read, TM2.stepAux, contents, isBit]
  | cons tag rest =>
    cases tag with
    | false => simp [undelimit] at h
    | true =>
      cases rest with
      | nil =>
        refine ⟨false, [], rev, (Run.single ?_).le (by simp)⟩
        simp only [program, FramedCNF.Block.read, isBit, Option.bind_fun_some, bitOf,
          TM2.stepAux, contents, List.head?_cons, Option.isSome_some, id_eq, Option.getD_some,
          List.tail_cons, update_self, List.head?_nil, Option.isSome_none, Option.getD_none,
          List.tail_nil, update_idem, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne,
          cond_eq_ite, Bool.false_eq_true, ↓reduceIte, TM2.Cfg.mk.injEq, true_and]
        funext k
        cases k <;> simp [contents]
      | cons bit tail =>
        have step : Run program 1
            ⟨some (.read item), v, contents (true :: bit :: tail) rev [] [] [] [] acc out⟩
            ⟨some (.read item), bit, contents tail (bit :: rev) [] [] [] [] acc out⟩ := by
          apply Run.single
          simp only [program, FramedCNF.Block.read, isBit, Option.bind_fun_some, bitOf,
            TM2.stepAux, contents, List.head?_cons, Option.isSome_some, id_eq, Option.getD_some,
            List.tail_cons, update_self, update_idem, ne_eq, reduceCtorEq, not_false_eq_true,
            update_of_ne, cond_eq_ite, ↓reduceIte, TM2.Cfg.mk.injEq, true_and]
          funext k
          cases k <;> simp [contents]
        have ht : undelimit tail = none := by simpa [undelimit] using h
        obtain ⟨z, y, b, hr⟩ := read_failure item tail (bit :: rev) acc out bit ht
        exact ⟨z, y, b, ((step.le le_rfl).trans hr).mono (by simp; omega)⟩
termination_by x.length

private theorem pair_length (p : List Bool) : (pair p).length = 3 * p.length + 1 := by
  simp only [pair, List.length_append, length_delimit]
  omega

private theorem loop_run (x acc out : List Bool) (v : Bool) :
    ∃ z T, RunLe program (30 * x.length + 4 * acc.length + 6)
      ⟨some .loop, v, ready x acc out⟩ ⟨some .done, z, T⟩ ∧
      T .out = delimit (acc.reverse ++ encodeItems x) ++ out := by
  by_cases hx : x = []
  · subst x
    have step : Run program 1 ⟨some .loop, v, ready [] acc out⟩
        ⟨some .finish, false, ready [] acc out⟩ := Run.single rfl
    obtain ⟨z, T, hr, hout⟩ := finish_run acc out false (ready [] acc out) rfl rfl rfl
    refine ⟨z, T, (step.trans hr).le (by simp; omega), ?_⟩
    have hempty : encodeItems [] = [] := by rw [encodeItems]; rfl
    simpa [hempty] using hout
  · have step : Run program 1 ⟨some .loop, v, ready x acc out⟩
        ⟨some (.read true), true, ready x acc out⟩ := by
      obtain ⟨b, r, rfl⟩ := List.exists_cons_of_ne_nil hx
      exact Run.single rfl
    cases hd : undelimit x with
    | none =>
      obtain ⟨v₁, y, b, hb⟩ := read_failure true x [] acc out true hd
      obtain ⟨z, T, hf, hout⟩ := finish_run acc out v₁
        (contents y b [] [] [] [] acc out) rfl rfl rfl
      refine ⟨z, T, (((step.le le_rfl).trans hb).trans (hf.le le_rfl)).mono (by omega), ?_⟩
      have hempty : encodeItems x = [] := by rw [encodeItems, hd]
      simpa [hempty] using hout
    | some pr =>
      obtain ⟨p, r⟩ := pr
      have hs := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hd
      have step' : Run program 1 ⟨some .loop, v, ready x acc out⟩
          ⟨some (.read true), true, ready (delimit p ++ r) acc out⟩ := by simpa [hs] using step
      obtain ⟨v₁, hread⟩ := read_pair true p r acc out true
      have hemit := emit_item p r acc out v₁
      have hlen : r.length < x.length := by
        rw [hs, List.length_append, length_delimit]
        omega
      obtain ⟨z, T, hr, hout⟩ := loop_run r ((delimit (pair p)).reverse ++ acc) out false
      refine ⟨z, T, ((((step'.trans hread).trans hemit).le le_rfl).trans hr).mono ?_, ?_⟩
      · simp only [hs, List.length_append, List.length_reverse, length_delimit, pair_length]
        omega
      · have hstep : encodeItems x = delimit (pair p) ++ encodeItems r := by
          rw [encodeItems, hd]
        simpa [hstep, List.reverse_append, List.append_assoc] using hout
termination_by x.length

private theorem run (x : List Bool) :
    ∃ z T, RunLe program (40 * x.length + 12)
      ⟨some (.read false), false, ready x [] []⟩ ⟨some .done, z, T⟩ ∧ T .out = transform x := by
  cases hx : undelimit x with
  | none =>
    obtain ⟨z, y, b, hr⟩ := read_failure false x [] [] [] false hx
    exact ⟨z, _, hr.mono (by omega), by simp [transform, hx, contents]⟩
  | some pr =>
    obtain ⟨p, r⟩ := pr
    have he := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hx
    obtain ⟨v₁, hread⟩ := read_pair false p r [] [] false
    obtain ⟨v₂, htgt⟩ := emit_target p r v₁
    obtain ⟨z, T, hr, hout⟩ := loop_run r [] (pair p) v₂
    refine ⟨z, T, ?_, by simpa [transform, hx] using hout⟩
    rw [he]
    exact (((hread.trans htgt).le le_rfl).trans hr).mono (by
      simp [length_delimit, pair_length]; omega)

private instance stackFintype : Fintype Stack := Fintype.ofList
  [.input, .rev, .left, .right, .pair, .payload, .acc, .out] (by intro k; cases k <;> simp)

private noncomputable abbrev comp : Host.Comp where
  K := Stack
  Γ := fun _ => Bool
  L := Label
  prog := program
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

private theorem isPolyTime_transform : IsPolyTime transform := by
  apply Host.isPolyTime_reduction (c := comp) (cX := .input) (cO := .out)
    (gX := id) (start := .read false) (done := .done) (Equiv.refl Bool) transform
    (Polynomial.C 40 * Polynomial.X + Polynomial.C 12) rfl
  intro x
  have hready : ready x [] [] = update (fun _ => []) Stack.input x := by
    funext k
    cases k <;> simp [ready, contents]
  obtain ⟨z, T, hr, ho⟩ := run x
  refine ⟨z, T, ?_, ?_⟩
  · simpa [hready] using hr
  · change T .out = (transform x).map id
    simpa using ho

private theorem encodeItems_encodeSS (as : List ℕ) :
    encodeItems (as.flatMap (fun a => delimit (encodeNat a))) =
      bitEncode (as.map fun a => (a, a)) := by
  induction as with
  | nil => rw [List.flatMap_nil, encodeItems]; rfl
  | cons a as ih =>
    rw [List.flatMap_cons, encodeItems, undelimit_delimit]
    change delimit (pair (encodeNat a)) ++
        encodeItems (as.flatMap (fun a => delimit (encodeNat a))) =
      delimit (pair (encodeNat a)) ++ bitEncode (as.map fun a => (a, a))
    rw [ih]

private theorem transform_encodeSS (as : List ℕ) (t : ℕ) :
    transform (encodeSS as t) = bitEncode (as.map (fun a => (a, a)), t, t) := by
  simp only [transform, encodeSS, undelimit_delimit]
  rw [encodeItems_encodeSS]
  rfl

private theorem correct_on_encoded (as : List ℕ) (t : ℕ) :
    subsetSumDec (encodeSS as t) = knapsackDec (transform (encodeSS as t)) := by
  apply Bool.eq_iff_iff.mpr
  rw [transform_encodeSS, subsetSumDec_encodeSS_eq_true]
  simp only [knapsackDec, bitDecode_bitEncode, decide_eq_true_eq]
  exact (diagonal_feasible as t).symm

private theorem reduceSS_range (x : List Bool) : ∃ as t, reduceSS x = encodeSS as t := by
  unfold reduceSS
  split
  · split
    · exact ⟨_, _, rfl⟩
    · exact ⟨[], 1, rfl⟩
  · exact ⟨[], 1, rfl⟩

private theorem fromVertexCover : PolyManyOneRed vertexCoverDec knapsackDec := by
  refine ⟨transform ∘ reduceSS, IsPolyTime.comp isPolyTime_reduceSS isPolyTime_transform, ?_⟩
  intro x
  rw [vertexCoverDec_eq_subsetSumDec_reduceSS, Function.comp_apply]
  obtain ⟨as, t, h⟩ := reduceSS_range x
  rw [h]
  exact correct_on_encoded as t

end Reduction

/-- **KNAPSACK is NP-complete.** The KNAPSACK decision problem is in NP, and every decision
problem in NP has a polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability: A Guide to the Theory of NP-Completeness* (1979), KNAPSACK (MP9). -/
theorem knapsack_npComplete :
    knapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L knapsackDec := by
  refine ⟨?_, NPHard.of_polyManyOneRed vertexCoverDec_npHard Reduction.fromVertexCover⟩
  exact ⟨Polynomial.X, fun q => verify q.1 q.2, Verifier.isPolyTime_verify,
    fun x => by simpa using exists_certificate x⟩

end MetaMathlibExt.Complexity.NPComplete.Knapsack
