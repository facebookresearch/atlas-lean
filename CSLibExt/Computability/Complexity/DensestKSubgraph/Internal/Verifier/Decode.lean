/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.DensestKSubgraph.Defs
public import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatPairPair
public import CSLibExt.Computability.Complexity.PolynomialEncoding.NormalizeRun
import CSLibExt.Computability.CookLevin

/-! # Finite-stack decoder for the exact DENSEST k-SUBGRAPH encoding -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.Decode

open Turing MetaMathlibExt MetaMathlibExt.TM2Embedding MetaMathlibExt.TM2Program
open MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.PolynomialEncoding Cslib.Complexity.FramedCNF
open MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph (DensestKSubgraphInstance)

/- Stacks for the outer split and normalization of `n`, then the existing `(E,k,m)` decoder. -/
inductive K | rest (k : ListNatPairPair.K) | n (k : NormalizeMachine.K) | scratch
  deriving DecidableEq

instance : Fintype K where
  elems := {K.scratch} ∪ Finset.univ.image K.rest ∪ Finset.univ.image K.n
  complete k := by cases k <;> simp

/- Continuations of the three existing machine components. -/
inductive Lab
  | split (l : PairSplit.Lab) | n (l : NormalizeMachine.Lab) | rest (l : ListNatPairPair.Lab)
  | good | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.good, .bad} ∪ Finset.univ.image Lab.split ∪ Finset.univ.image Lab.n ∪
    Finset.univ.image Lab.rest
  complete l := by cases l <;> simp

/- The outer input stack becomes the input of the suffix decoder. -/
abbrev input : K := .rest (.pair (.pair .input))

/- Send the outer first field to the normalizer and keep the second in place. -/
def splitEmb : SEmb (fun _ : PairSplit.K => Bool) (fun _ : K => Bool) where
  e
    | .input => input
    | .left => .n .input
    | .scratch => .scratch
  inj a b h := by cases a <;> cases b <;> cases h <;> rfl
  ι _ := Equiv.refl Bool

/- The `n` normalizer has its own workspace. -/
def nEmb : SEmb (fun _ : NormalizeMachine.K => Bool) (fun _ : K => Bool) where
  e := K.n
  inj _ _ h := K.n.inj h
  ι _ := Equiv.refl Bool

/- The suffix decoder has its own workspace. -/
def restEmb : SEmb (fun _ : ListNatPairPair.K => Bool) (fun _ : K => Bool) where
  e := K.rest
  inj _ _ h := K.rest.inj h
  ι _ := Equiv.refl Bool

/- Start normalization only on successful outer framing. -/
def splitLabel : PairSplit.Lab → Lab
  | .good => .n (.read none)
  | .bad => .bad
  | l => .split l

/- Continue to the edge list and both threshold fields. -/
def nLabel : NormalizeMachine.Lab → Lab
  | .done => .rest (.split .read)
  | l => .n l

/- Propagate the suffix decoder's success or failure. -/
def restLabel : ListNatPairPair.Lab → Lab
  | .good => .good
  | .bad => .bad
  | l => .rest l

/- The composed parser uses only these fixed stacks and labels. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .split l => mapS splitEmb splitLabel (PairSplit.prog l)
  | .n l => mapS nEmb nLabel (NormalizeMachine.prog l)
  | .rest l => mapS restEmb restLabel (ListNatPairPair.prog l)
  | .good | .bad => .halt

private theorem embeds_split : Embeds splitEmb splitLabel PairSplit.prog prog := by
  intro l
  cases l with
  | read | copy => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem embeds_n : Embeds nEmb nLabel NormalizeMachine.prog prog := by
  intro l
  cases l with
  | read | copy => exact Or.inl rfl
  | done => exact Or.inr rfl

private theorem embeds_rest : Embeds restEmb restLabel ListNatPairPair.prog prog := by
  intro l
  cases l with
  | split | items | pair => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

/- Exact configuration of the input, `n` workspace and the preserved output suffix. -/
def st (raw p n : List Bool) : K → List Bool
  | .rest k => ListNatPairPair.st [] raw [] [] [] [] k
  | .n k => NormalizeMachine.st p [] n k
  | .scratch => []

private theorem agree_split (x : List Bool) :
    Agree splitEmb (PairSplit.st x [] []) (st x [] []) := by
  intro k
  cases k <;> simp [splitEmb, PairSplit.st, st, ListNatPairPair.st, NatPair.st, NormalizeMachine.st]

private theorem agree_n_after_split {x p r : List Bool} {S : K → List Bool}
    (ha : Agree splitEmb (PairSplit.st r p []) S) (hf : Frame splitEmb (st x [] []) S) :
    Agree nEmb (NormalizeMachine.st p [] []) S := by
  intro k
  cases k with
  | input => simpa [nEmb, splitEmb, PairSplit.st, NormalizeMachine.st] using ha .left
  | buffer =>
    simpa [nEmb, st, NormalizeMachine.st] using hf (.n .buffer) (by intro k; cases k <;> decide)
  | output =>
    simpa [nEmb, st, NormalizeMachine.st] using hf (.n .output) (by intro k; cases k <;> decide)

private theorem agree_rest_after_split {x p r : List Bool} {S : K → List Bool}
    (ha : Agree splitEmb (PairSplit.st r p []) S) (hf : Frame splitEmb (st x [] []) S) :
    Agree restEmb (ListNatPairPair.st [] r [] [] [] []) S := by
  intro k
  by_cases h : K.rest k = input
  · have h' : k = .pair (.pair .input) := K.rest.inj h
    subst k
    simpa [restEmb, splitEmb, ListNatPairPair.st, NatPair.st, PairSplit.st] using ha .input
  · have hs := hf (.rest k) (by intro j; cases j <;> simp_all [splitEmb, eq_comm])
    change S (.rest k) = ListNatPairPair.st [] x [] [] [] [] k at hs
    change S (.rest k) = List.map id (ListNatPairPair.st [] r [] [] [] [] k)
    rw [hs, List.map_id]
    cases k with
    | items k => rfl
    | pair k =>
      cases k with
      | pair k => cases k <;> simp_all [input, ListNatPairPair.st, NatPair.st]
      | buffer | left | right => rfl

private theorem decode_fields (x : List Bool) :
    bitDecode (α := DensestKSubgraphInstance) x =
      (undelimit x).bind fun (p, r) =>
        (bitDecode (α := List (ℕ × ℕ) × ℕ × ℕ) r).map (Computability.decodeNat p, ·) := by
  have h : bitDecode (α := DensestKSubgraphInstance) x =
      (match undelimit x with
      | none => none
      | some (p, r) => match bitDecode (α := ℕ) p,
          bitDecode (α := List (ℕ × ℕ) × ℕ × ℕ) r with
        | some n, some rest => some (n, rest)
        | _, _ => none) := by
    rfl'
  rw [h]
  cases undelimit x with
  | none => rfl
  | some pr =>
    obtain ⟨p, r⟩ := pr
    change (match bitDecode (α := ℕ) p, bitDecode (α := List (ℕ × ℕ) × ℕ × ℕ) r with
      | some n, some rest => some (n, rest)
      | _, _ => none) =
        (bitDecode (α := List (ℕ × ℕ) × ℕ × ℕ) r).map (Computability.decodeNat p, ·)
    have hn : bitDecode (α := ℕ) p = some (Computability.decodeNat p) := rfl
    rw [hn]
    cases bitDecode (α := List (ℕ × ℕ) × ℕ × ℕ) r <;> rfl

/- A linear-time total run for the exact decoder, including noncanonical Nat payloads.
On success the four suffix outputs agree with `ListNatPairPair` and the normalized `n` is saved. -/
theorem run (x : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (10 * x.length + 6)
      ⟨some (.split .read), v, st x [] []⟩
      ⟨some (if (bitDecode (α := DensestKSubgraphInstance) x).isSome then .good else .bad), w, S⟩ ∧
      ∀ (i : DensestKSubgraphInstance), bitDecode x = some i →
        S (.n .output) = Computability.encodeNat i.1 ∧
        Agree restEmb (ListNatPairPair.st [] [] (bitEncode (i.2.1.map Prod.fst))
          (bitEncode (i.2.1.map Prod.snd)) (Computability.encodeNat i.2.2.1)
          (Computability.encodeNat i.2.2.2)) S := by
  obtain ⟨v₁, S₁, h₁, f₁, a₁⟩ := PairSplit.run_embedded splitEmb splitLabel embeds_split x v
    (st x [] []) (agree_split x)
  cases hu : undelimit x with
  | none =>
    have hd : bitDecode (α := DensestKSubgraphInstance) x = none := by simp [decode_fields, hu]
    refine ⟨v₁, S₁, ?_, fun i hi => by rw [hd] at hi; cases hi⟩
    simpa [hu, hd, splitLabel] using h₁.mono (show x.length + 1 ≤ 10 * x.length + 6 by omega)
  | some pr =>
    obtain ⟨p, r⟩ := pr
    have hst : x = delimit p ++ r := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
    have hsize : x.length = 2 * p.length + 1 + r.length := by
      rw [hst, List.length_append, length_delimit]
    have hfirst : RunLe prog (x.length + 1) ⟨some (.split .read), v, st x [] []⟩
        ⟨some (.n (.read none)), v₁, S₁⟩ := by simpa [hu, splitLabel] using h₁
    have ha := a₁ p r hu
    obtain ⟨v₂, h₂⟩ := normalizeNat_run_frame p [] v₁
    obtain ⟨S₂, hmiddle, a₂, f₂⟩ := runLe_embed nLabel embeds_n h₂ (agree_n_after_split ha f₁)
    have hA : Agree restEmb (ListNatPairPair.st [] r [] [] [] []) S₂ := by
      intro k
      change S₂ (.rest k) = _
      rw [f₂ (.rest k) (by intro j; simp [nEmb])]
      exact agree_rest_after_split ha f₁ k
    obtain ⟨w, S, h₃, f₃, a₃⟩ := ListNatPairPair.run_embedded restEmb restLabel embeds_rest
      r [] [] [] [] v₂ S₂ hA
    let rt := bitDecode (α := List (ℕ × ℕ) × ℕ × ℕ) r
    have hd : bitDecode (α := DensestKSubgraphInstance) x = rt.map (Computability.decodeNat p, ·) :=
      by simp [decode_fields, hu, rt]
    have hl : restLabel (if rt.isSome then .good else .bad) =
        (if (bitDecode (α := DensestKSubgraphInstance) x).isSome then .good else .bad) := by
      rw [hd]
      cases rt <;> rfl
    change RunLe prog _ _ ⟨some (restLabel (if rt.isSome then .good else .bad)), w, S⟩ at h₃
    rw [hl] at h₃
    refine ⟨w, S, ((hfirst.trans hmiddle).trans h₃).mono (by omega), ?_⟩
    rintro ⟨n, es, k, m⟩ hi
    rw [hd, Option.map_eq_some_iff] at hi
    obtain ⟨a, hdec, heq⟩ := hi
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    constructor
    · rw [f₃ (.n .output) (by intro j; simp [restEmb])]
      simpa [nEmb, NormalizeMachine.st, normalizeNat_eq_encode_decode] using a₂ .output
    · simpa using a₃ es k m hdec

end Cslib.Complexity.DensestKSubgraph.Internal.Decode
