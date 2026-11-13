/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.PairSplit
public import CSLibExt.Computability.Complexity.PolynomialEncoding.NormalizeRun

/-!
# Projecting and normalizing a pair of binary naturals

The actual pair-frame component separates raw payloads. Two calls to the
actual Nat normalizer produce canonical LSB-first payloads. Every complete
Nat payload is accepted, including the total decoder's noncanonical forms.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.NatPair

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding FramedCNF

/-- Pair workspace, one reusable Nat buffer, and two canonical outputs. -/
inductive K | pair (k : PairSplit.K) | buffer | left | right
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.pair .input, .pair .left, .pair .scratch,
    .buffer, .left, .right], by decide⟩
  complete k := by
    rcases k with k | _ | _ | _ <;> try decide
    cases k <;> decide

/-- Pair projection followed by normalization of the two fields. -/
inductive Lab | pair (l : PairSplit.Lab)
  | norm (second : Bool) (l : NormalizeMachine.Lab) | good | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := ⟨↑[Lab.pair .read, .pair .copy, .pair .good, .pair .bad,
    .norm false (.read none), .norm false (.read (some false)),
    .norm false (.read (some true)), .norm false .copy, .norm false .done,
    .norm true (.read none), .norm true (.read (some false)),
    .norm true (.read (some true)), .norm true .copy, .norm true .done,
    .good, .bad], by decide⟩
  complete l := by
    rcases l with l | ⟨s, l⟩ | _ | _ <;> try decide
    · cases l <;> decide
    · cases s <;> rcases l with (_ | (_ | _)) | _ | _ <;> decide

/-- The pair-frame component acts only on its three own stacks. -/
def pairEmb : SEmb (fun _ : PairSplit.K => Bool) (fun _ : K => Bool) where
  e := K.pair
  inj _ _ h := K.pair.inj h
  ι _ := Equiv.refl Bool

/-- Each normalizer consumes its raw field, sharing only an empty buffer. -/
def normEmb (second : Bool) :
    SEmb (fun _ : NormalizeMachine.K => Bool) (fun _ : K => Bool) where
  e
    | .input => if second then .pair .input else .pair .left
    | .buffer => .buffer
    | .output => if second then .right else .left
  inj a b h := by cases second <;> cases a <;> cases b <;> simp_all
  ι _ := Equiv.refl Bool

/-- Only actual pair halt labels are redirected. -/
def pairLabel : PairSplit.Lab → Lab
  | .good => .norm false (.read none)
  | .bad => .bad
  | l => .pair l

/-- Normalizing the first field continues with the second. -/
def normLabel (second : Bool) : NormalizeMachine.Lab → Lab
  | .done => if second then .good else .norm true (.read none)
  | l => .norm second l

/-- All work is performed by the two existing finite components. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .pair l => mapS pairEmb pairLabel (PairSplit.prog l)
  | .norm s l => mapS (normEmb s) (normLabel s) (NormalizeMachine.prog l)
  | .good | .bad => .halt

/-- Explicit six-stack invariant. -/
def st (input first scratch buffer left right : List Bool) : K → List Bool
  | .pair .input => input
  | .pair .left => first
  | .pair .scratch => scratch
  | .buffer => buffer
  | .left => left
  | .right => right

private theorem embeds_pair :
    Embeds pairEmb pairLabel PairSplit.prog prog := by
  intro l
  cases l with
  | read | copy => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem embeds_norm (second : Bool) :
    Embeds (normEmb second) (normLabel second) NormalizeMachine.prog prog := by
  intro l
  cases l with
  | read _ | copy => exact Or.inl rfl
  | done => exact Or.inr rfl

private theorem pair_run (p r left right : List Bool) (v : Bool) :
    ∃ v', Run prog (2 * p.length + 2)
      ⟨some (.pair .read), v, st (delimit p ++ r) [] [] [] left right⟩
      ⟨some (.norm false (.read none)), v', st r p [] [] left right⟩ := by
  obtain ⟨v', hr⟩ := PairSplit.run_delimit p r [] v
  obtain ⟨T, ht, ha, hf⟩ := MetaMathlibExt.TM2Embedding.run_embed pairLabel
    embeds_pair _ _ _ _ _ _ _ (st (delimit p ++ r) [] [] [] left right)
    hr (by intro k; cases k <;> simp [pairEmb, st, PairSplit.st])
  have he : T = st r p [] [] left right := by
    funext k
    cases k with
    | pair k =>
      cases k <;> simpa [pairEmb, st, PairSplit.st] using ha _
    | buffer => exact hf K.buffer (by intro k; simp [pairEmb])
    | left => exact hf K.left (by intro k; simp [pairEmb])
    | right => exact hf K.right (by intro k; simp [pairEmb])
  exact ⟨v', he ▸ ht⟩

private theorem first_run (p r left right : List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * p.length + 3)
      ⟨some (.norm false (.read none)), v, st r p [] [] left right⟩
      ⟨some (.norm true (.read none)), v',
        st r [] [] [] (normalizeNat p ++ left) right⟩ := by
  obtain ⟨v', hr⟩ := normalizeNat_run_frame p left v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed (normLabel false)
    (embeds_norm false) hr (S' := st r p [] [] left right)
    (by intro k; cases k <;> simp [normEmb, st, NormalizeMachine.st])
  have he : T = st r [] [] [] (normalizeNat p ++ left) right := by
    funext k
    cases k with
    | buffer => simpa [normEmb, st, NormalizeMachine.st] using ha .buffer
    | left => simpa [normEmb, st, NormalizeMachine.st] using ha .output
    | right => exact hf K.right (by intro k; cases k <;> simp [normEmb])
    | pair k =>
      cases k with
      | input =>
        exact hf (.pair .input) (by intro k; cases k <;> simp [normEmb])
      | left => simpa [normEmb, st, NormalizeMachine.st] using ha .input
      | scratch =>
        exact hf (.pair .scratch) (by intro k; cases k <;> simp [normEmb])
  exact ⟨v', he ▸ ht⟩

private theorem second_run (r left right : List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * r.length + 3)
      ⟨some (.norm true (.read none)), v, st r [] [] [] left right⟩
      ⟨some .good, v', st [] [] [] [] left (normalizeNat r ++ right)⟩ := by
  obtain ⟨v', hr⟩ := normalizeNat_run_frame r right v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed (normLabel true)
    (embeds_norm true) hr (S' := st r [] [] [] left right)
    (by intro k; cases k <;> simp [normEmb, st, NormalizeMachine.st])
  have he : T = st [] [] [] [] left (normalizeNat r ++ right) := by
    funext k
    cases k with
    | buffer => simpa [normEmb, st, NormalizeMachine.st] using ha .buffer
    | right => simpa [normEmb, st, NormalizeMachine.st] using ha .output
    | left => exact hf K.left (by intro k; cases k <;> simp [normEmb])
    | pair k =>
      cases k with
      | input => simpa [normEmb, st, NormalizeMachine.st] using ha .input
      | left =>
        exact hf (.pair .left) (by intro k; cases k <;> simp [normEmb])
      | scratch =>
        exact hf (.pair .scratch) (by intro k; cases k <;> simp [normEmb])
  exact ⟨v', he ▸ ht⟩

/-- Every raw pair frame is projected and normalized without changing
the total Nat decoding semantics. Previous output suffixes survive. -/
theorem run_delimit (p r left right : List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * (delimit p ++ r).length + 6)
      ⟨some (.pair .read), v, st (delimit p ++ r) [] [] [] left right⟩
      ⟨some .good, v',
        st [] [] [] [] (normalizeNat p ++ left) (normalizeNat r ++ right)⟩ := by
  obtain ⟨v₁, h₁⟩ := pair_run p r left right v
  obtain ⟨v₂, h₂⟩ := first_run p r left right v₁
  obtain ⟨v₃, h₃⟩ := second_run r (normalizeNat p ++ left) right v₂
  refine ⟨v₃, ((h₁.le le_rfl).trans h₂ |>.trans h₃).mono ?_⟩
  simp only [List.length_append, length_delimit]
  omega

/-- Pair Nat decoding fails exactly when the first frame is malformed;
both raw field payloads use Mathlib's total Nat decoder. -/
theorem decode_pair_nat (x : List Bool) :
    bitDecode (α := Nat × Nat) x = (undelimit x).map (fun p =>
      (Computability.decodeNat p.1, Computability.decodeNat p.2)) := by
  change (match undelimit x with
    | none => none
    | some (p, r) =>
      some (Computability.decodeNat p, Computability.decodeNat r)) = _
  cases h : undelimit x <;> rfl

/-- A successful pair decode produces both canonical binary payloads,
with all scratch empty and arbitrary previous output suffixes preserved. -/
theorem run_some {x : List Bool} {m n : Nat}
    (h : bitDecode x = some (m, n)) (left right : List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * x.length + 6)
      ⟨some (.pair .read), v, st x [] [] [] left right⟩
      ⟨some .good, v', st [] [] [] [] (Computability.encodeNat m ++ left)
        (Computability.encodeNat n ++ right)⟩ := by
  obtain ⟨p, r, hx, hp, hr⟩ := decoded_pair_parts h
  have hm : Computability.decodeNat p = m := Option.some.inj hp
  have hn : Computability.decodeNat r = n := Option.some.inj hr
  obtain ⟨v', run⟩ := run_delimit p r left right v
  rw [normalizeNat_eq_encode_decode, normalizeNat_eq_encode_decode,
    hm, hn, ← hx] at run
  exact ⟨v', run⟩

/-- Malformed pair framing fails in linear time. Private partial
workspace contents must be cleared before another invocation. -/
theorem run_none {x : List Bool} (h : bitDecode (α := Nat × Nat) x = none)
    (left right : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (x.length + 1)
      ⟨some (.pair .read), v, st x [] [] [] left right⟩
      ⟨some .bad, v', S⟩ := by
  rw [decode_pair_nat, Option.map_eq_none_iff] at h
  obtain ⟨v', S, hr⟩ := PairSplit.run_none h [] v
  obtain ⟨T, ht, _, _⟩ := runLe_embed pairLabel embeds_pair hr
    (S' := st x [] [] [] left right)
    (by intro k; cases k <;> simp [pairEmb, st, PairSplit.st])
  exact ⟨v', T, ht⟩

/-- The concrete two-Nat projector in the existing Host interface. -/
abbrev component : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := [.pair .input, .pair .left, .pair .scratch, .buffer, .left, .right]
  ks_nodup := by decide
  mem_ks k := by
    rcases k with k | _ | _ | _ <;> try decide
    cases k <;> decide

/-- Canonical output payload sizes are bounded by the raw input size,
even when either field had a noncanonical final zero bit. -/
theorem decoded_payload_length_le {x : List Bool} {m n : Nat}
    (h : bitDecode x = some (m, n)) :
    (Computability.encodeNat m).length + (Computability.encodeNat n).length ≤
      x.length + 1 := by
  obtain ⟨p, r, hx, hp, hr⟩ := decoded_pair_parts h
  have hm : Computability.decodeNat p = m := Option.some.inj hp
  have hn : Computability.decodeNat r = n := Option.some.inj hr
  have h₁ := length_normalizeNat_le p
  have h₂ := length_normalizeNat_le r
  rw [normalizeNat_eq_encode_decode, hm] at h₁
  rw [normalizeNat_eq_encode_decode, hn] at h₂
  rw [hx, List.length_append, length_delimit]
  omega

/-- Total decoder outcome with exact successful output and empty
private scratch. Failure does not promise reusable workspace contents. -/
theorem run (x : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (2 * x.length + 6)
      ⟨some (.pair .read), v, st x [] [] [] [] []⟩
      ⟨some (if (bitDecode (α := Nat × Nat) x).isSome
        then .good else .bad), v', S⟩ ∧
      ∀ m n : Nat, bitDecode x = some (m, n) →
        S = st [] [] [] [] (Computability.encodeNat m)
          (Computability.encodeNat n) := by
  cases h : bitDecode (α := Nat × Nat) x with
  | none =>
    obtain ⟨v', S, hr⟩ := run_none h [] [] v
    refine ⟨v', S, hr.mono (by omega), ?_⟩
    intro m n hm
    simp at hm
  | some mn =>
    obtain ⟨m, n⟩ := mn
    obtain ⟨v', hr⟩ := run_some h [] [] v
    refine ⟨v', st [] [] [] [] (Computability.encodeNat m)
      (Computability.encodeNat n), by simpa using hr, ?_⟩
    intro a b hab
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hab)
    rfl

/-- Callers may embed this concrete projector without disturbing
outside stacks. A failed workspace must be cleared before reuse. -/
theorem run_embedded {J L : Type} [DecidableEq J] {Γ : J → Type}
    (E : SEmb (fun _ : K => Bool) Γ) (φ : Lab → L)
    {M : L → TM2.Stmt Γ L Bool} (hm : Embeds E φ prog M)
    (x : List Bool) (v : Bool) (S : ∀ j, List (Γ j))
    (hs : Agree E (st x [] [] [] [] []) S) :
    ∃ v' T, RunLe M (2 * x.length + 6)
      ⟨some (φ (.pair .read)), v, S⟩
      ⟨some (φ (if (bitDecode (α := Nat × Nat) x).isSome
        then .good else .bad)), v', T⟩ ∧ Frame E S T ∧
      ∀ m n : Nat, bitDecode x = some (m, n) →
        Agree E (st [] [] [] [] (Computability.encodeNat m)
          (Computability.encodeNat n)) T := by
  obtain ⟨v', U, hr, hu⟩ := run x v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed φ hm hr hs
  refine ⟨v', T, ht, hf, ?_⟩
  intro m n h
  rw [hu m n h] at ha
  exact ha

end Cslib.Complexity.PolynomialEncoding.NatPair
