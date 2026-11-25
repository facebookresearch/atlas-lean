/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.BoolClosure
import Mathlib.Data.List.OfFn

/-!
# RP is contained in BPP

Two independent runs of an RP verifier, combined by OR, give a BPP verifier.
The two runs read the even and odd positions of a single random string.
-/

public section

namespace MetaMathlibExt.Complexity.KeyTheorems.RPSubsetBPP

open Cslib.Complexity Cslib.Complexity.Classes Cslib.Complexity.DenseSAT
open ComplexityTheory BitstringEncoding Turing TM2Program

/-! A finite-state scan extracts a field from the encoded verifier input. Each transition
consumes one bit and optionally emits one bit. The machine collects the emitted bits on a
stack, then reverses that stack onto the output. -/

private def scan {Q : Type} (δ : Q → Bool → Q × Option Bool) (q : Q) :
    List Bool → List Bool
  | [] => []
  | b :: bs => (δ q b).2.toList ++ scan δ (δ q b).1 bs

private theorem scan_length {Q : Type} (δ : Q → Bool → Q × Option Bool)
    (q : Q) (bs : List Bool) : (scan δ q bs).length ≤ bs.length := by
  induction bs generalizing q with
  | nil => rfl
  | cons b bs ih =>
    have h := ih (δ q b).1
    cases e : (δ q b).2 <;> simp [scan, e] <;> omega

private def scanProg {Q : Type} (δ : Q → Bool → Q × Option Bool) :
    Option Q → TM2.Stmt (fun _ : BStk => Bool) (Option Q) (Option Bool)
  | some q =>
    let next := TM2.Stmt.goto fun s : Option Bool => some (δ q (s.getD false)).1
    .pop .inp (fun _ o => o) <| .branch Option.isSome
      (.branch (fun s => (δ q (s.getD false)).2.isSome)
        (.push .stash (fun s => (δ q (s.getD false)).2.getD false) next) next)
      (.goto fun _ => none)
  | none =>
    .pop .stash (fun _ o => o) <| .branch Option.isSome
      (.push .out (fun s => s.getD false) (.goto fun _ => none)) .halt

private theorem scan_run {Q : Type} (δ : Q → Bool → Q × Option Bool)
    (q : Q) (bs acc : List Bool) (v : Option Bool) :
    Run (scanProg δ) (bs.length + 1)
      ⟨some (some q), v, bstk bs [] acc⟩
      ⟨some none, none, bstk [] [] ((scan δ q bs).reverse ++ acc)⟩ := by
  induction bs generalizing q acc v with
  | nil => exact Run.single (by simp [scanProg, TM2.stepAux, bstk, scan])
  | cons b bs ih =>
    cases e : (δ q b).2 with
    | none =>
      simpa [scan, e] using (ih (δ q b).1 acc (some b)).head
        (c := ⟨some (some q), v, bstk (b :: bs) [] acc⟩)
        (by simp [TM2.step, scanProg, TM2.stepAux, bstk, e])
    | some a =>
      simpa [scan, e, List.append_assoc] using (ih (δ q b).1 (a :: acc) (some b)).head
        (c := ⟨some (some q), v, bstk (b :: bs) [] acc⟩)
        (by simp [TM2.step, scanProg, TM2.stepAux, bstk, e])

private theorem flush_run {Q : Type} (δ : Q → Bool → Q × Option Bool)
    (acc out : List Bool) (v : Option Bool) :
    Run (scanProg δ) (acc.length + 1) ⟨some none, v, bstk [] out acc⟩
      ⟨none, none, bstk [] (acc.reverse ++ out) []⟩ := by
  induction acc generalizing out v with
  | nil => exact Run.single (by simp [scanProg, TM2.stepAux, bstk])
  | cons a acc ih =>
    simpa [List.append_assoc] using (ih (a :: out) (some a)).head
      (c := ⟨some none, v, bstk [] out (a :: acc)⟩)
      (by simp [TM2.step, scanProg, TM2.stepAux, bstk])

private abbrev scanTM {Q : Type} [Fintype Q] (δ : Q → Bool → Q × Option Bool) (q : Q) :
    FinTM2 where
  K := BStk
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := Option Q
  main := some q
  σ := Option Bool
  initialState := none
  m := scanProg δ

private noncomputable def scanComputable {Q : Type} [Fintype Q]
    (δ : Q → Bool → Q × Option Bool) (q : Q) :
    TM2ComputableInPolyTime id id (scan δ q) where
  tm := scanTM δ q
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
  outputsFun bs := by
    let ys := scan δ q bs
    have hs := scan_run δ q bs [] none
    simp only [List.append_nil] at hs
    have h := hs.trans (flush_run δ ys.reverse [] none)
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h
    refine ⟨⟨bs.length + 1 + (ys.length + 1), ?_⟩, ?_⟩
    · change Run (scanProg δ) _ (initList (scanTM δ q) (bs.map id))
        (haltList (scanTM δ q) (ys.map id))
      have hi : initList (scanTM δ q) bs = ⟨some (some q), none, bstk bs [] []⟩ := by
        unfold initList
        congr 1
        funext k
        cases k <;> rfl
      have ho : haltList (scanTM δ q) ys = ⟨none, none, bstk [] ys []⟩ := by
        unfold haltList
        congr 1
        funext k
        cases k <;> rfl
      simpa only [List.map_id, hi, ho] using h
    · have := scan_length δ q bs
      simp [ys]
      omega

private theorem poly_scan {Q : Type} [Finite Q] (δ : Q → Bool → Q × Option Bool) (q : Q) :
    IsPolyTime (scan δ q) := by
  let _ := Fintype.ofFinite Q
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp DecodeBits.computable (scanComputable δ q)
  exact tm2ComputableInPolyTime_comp (f := scan δ q) (g := id) h EncodeBits.computable

/-! The canonical pair encoding has six bits per input bit, a separator, and three bits per
random bit. In the random field we alternate between the two trials after every bit. -/

private inductive Phase
  | start | x₁ | x₂ | xBit | x₄ | x₅
  | random (odd : Bool) | randomBit (odd : Bool) | randomEnd (odd : Bool)
  deriving DecidableEq, Fintype

-- The field is either the original input (none) or one parity of the coins.
private def readField (field : Option Bool) : Phase → Bool → Phase × Option Bool
  | .start, true => (.x₁, none)
  | .start, false => (.random false, none)
  | .x₁, _ => (.x₂, none)
  | .x₂, _ => (.xBit, none)
  | .xBit, b => (.x₄, if field.isNone then some b else none)
  | .x₄, _ => (.x₅, none)
  | .x₅, _ => (.start, none)
  | .random k, _ => (.randomBit k, none)
  | .randomBit k, b => (.randomEnd k, if field = some k then some b else none)
  | .randomEnd k, _ => (.random (!k), none)

private abbrev fieldBits (field : Option Bool) := scan (readField field) .start

private def interleave (pairs : List (Bool × Bool)) : List Bool :=
  pairs.flatMap fun p => [p.1, p.2]

private theorem read_coins (field : Option Bool) (pairs : List (Bool × Bool)) :
    scan (readField field) (.random false) (Converter.encSnd (interleave pairs)) =
      match field with
      | none => []
      | some false => pairs.map Prod.fst
      | some true => pairs.map Prod.snd := by
  induction pairs with
  | nil => rcases field with _ | (_ | _) <;> rfl
  | cons p pairs ih =>
    cases field with
    | none => simpa [interleave, Converter.encSnd, scan, readField] using ih
    | some k =>
      cases k <;> simp_all [interleave, Converter.encSnd, scan, readField]

private theorem fields_correct (field : Option Bool) (x : List Bool) (pairs : List (Bool × Bool)) :
    fieldBits field (bitEncode (x, interleave pairs)) =
      match field with
      | none => x
      | some false => pairs.map Prod.fst
      | some true => pairs.map Prod.snd := by
  change scan (readField field) .start ((toEncoding (α := List Bool × List Bool)).encode _) = _
  rw [Converter.bitEncode_pair_eq]
  induction x with
  | nil =>
    cases field with
    | none => exact read_coins none pairs
    | some k => cases k <;> exact read_coins _ pairs
  | cons b x ih =>
    cases field with
    | none => simpa [Converter.encFst, scan, readField] using congrArg (b :: ·) ih
    | some k => cases k <;> simpa [Converter.encFst, scan, readField] using ih

private theorem poly_encodePair : IsPolyTime (bitEncode (α := List Bool × List Bool)) :=
  ⟨{ EncodeBits.computable with
      outputsFun := fun q => EncodeBits.computable.outputsFun (bitEncode q) }⟩

private def twice (R : List Bool × List Bool → Bool) (q : List Bool × List Bool) : Bool :=
  let run := fun k => R (fieldBits none (bitEncode q), fieldBits (some k) (bitEncode q))
  run false || run true

private theorem poly_twice {R : List Bool × List Bool → Bool} (hR : IsPolyTime R) :
    IsPolyTime (twice R) := by
  have run (k : Bool) :
      IsPolyTime (fun s => R (fieldBits none s, fieldBits (some k) s)) :=
    (((isPolyTime_dup.comp (poly_scan (readField (some k)) .start).map_fst).comp
      isPolyTime_swap).comp (poly_scan (readField none) .start).map_fst).comp hR
  exact poly_encodePair.comp (IsPolyTime.combine Bool.or (run false) (run true))

private theorem twice_interleave (R : List Bool × List Bool → Bool) (x : List Bool)
    (pairs : List (Bool × Bool)) :
    twice R (x, interleave pairs) = (R (x, pairs.map Prod.fst) || R (x, pairs.map Prod.snd)) := by
  simp only [twice, fields_correct]

private def splitCoins (n : ℕ) :
    (Fin (n * 2) → Bool) ≃ (Fin n → Bool) × (Fin n → Bool) :=
  (finProdFinEquiv.symm.arrowCongr (Equiv.refl Bool)).trans <|
    (Equiv.curry (Fin n) (Fin 2) Bool).trans <|
    (Equiv.piCongrRight fun _ => finTwoArrowEquiv Bool).trans <|
    Equiv.arrowProdEquivProdArrow _ _ _

private theorem twice_ofFn (R : List Bool × List Bool → Bool) (x : List Bool)
    {n : ℕ} (r : Fin (n * 2) → Bool) :
    twice R (x, List.ofFn r) =
      (R (x, List.ofFn ((splitCoins n r).1)) || R (x, List.ofFn ((splitCoins n r).2))) := by
  let pair := fun i : Fin n => ((splitCoins n r).1 i, (splitCoins n r).2 i)
  have he : List.ofFn r = interleave (List.ofFn pair) := by
    rw [List.ofFn_mul, interleave, List.flatMap_def, List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext i
    simp only [List.ofFn_succ, List.ofFn_zero, Function.comp_apply]
    change [r _, r _] = [r (finProdFinEquiv (i, 0)), r (finProdFinEquiv (i, 1))]
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [he, twice_interleave]
  simp [List.map_ofFn, pair, Function.comp_def]

private theorem count_twice (R : List Bool × List Bool → Bool) (x : List Bool) (n : ℕ) :
    let A := {r : Fin n → Bool | R (x, List.ofFn r) = true}
    let B := {r : Fin (n * 2) → Bool | twice R (x, List.ofFn r) = true}
    Bᶜ.ncard = Aᶜ.ncard * Aᶜ.ncard := by
  intro A B
  have h : Bᶜ = (splitCoins n) ⁻¹' (Aᶜ ×ˢ Aᶜ) := by
    ext r
    simp [A, B, twice_ofFn]
  rw [h, Set.ncard_preimage_of_injective_subset_range (splitCoins n).injective,
    Set.ncard_prod]
  simp [(splitCoins n).surjective.range_eq]

/-- **RP is contained in BPP.** Every decision problem in the class $\mathsf{RP}$ of
one-sided-error randomized polynomial-time decision problems also belongs to the class
$\mathsf{BPP}$ of bounded-error probabilistic polynomial-time decision problems.

Source: S. Arora and B. Barak, Computational Complexity:
A Modern Approach, 2009, Chapter 7 (error reduction for RP); M. Sipser,
Introduction to the Theory of Computation, 3rd ed., 2013, Theorem 10.13
(RP ⊆ BPP via amplification). -/
public theorem rp_subset_bpp :
    RP ⊆ BPP := by
  rintro L ⟨p, R, hR, hL⟩
  refine ⟨p * 2, twice R, poly_twice hR, fun x => ?_⟩
  rw [Polynomial.eval_mul, Polynomial.eval_ofNat]
  let n := p.eval x.length
  let A := {r : Fin n → Bool | R (x, List.ofFn r) = true}
  let B := {r : Fin (n * 2) → Bool | twice R (x, List.ofFn r) = true}
  have hA : A.ncard + Aᶜ.ncard = 2 ^ n := by simpa using A.ncard_add_ncard_compl
  have hB : B.ncard + Aᶜ.ncard * Aᶜ.ncard = (2 ^ n) ^ 2 := by
    have h : Bᶜ.ncard = Aᶜ.ncard * Aᶜ.ncard := count_twice R x n
    rw [← h, B.ncard_add_ncard_compl]
    simp [pow_mul]
  change (L x = true → 2 * 2 ^ (n * 2) ≤ 3 * B.ncard) ∧
    (L x = false → 3 * B.ncard ≤ 2 ^ (n * 2))
  rw [pow_mul]
  constructor
  · intro hx
    have hyes : 2 ^ n ≤ 2 * A.ncard := (hL x).1 hx
    have hmiss : 2 * Aᶜ.ncard ≤ 2 ^ n := by omega
    nlinarith [Nat.mul_le_mul hmiss hmiss]
  · intro hx
    have hno : A.ncard = 0 := (hL x).2 hx
    rw [hno, zero_add] at hA
    rw [hA, ← sq] at hB
    omega

end MetaMathlibExt.Complexity.KeyTheorems.RPSubsetBPP
