/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Host
public import CSLibExt.Computability.Complexity.Karp.MultipleKnapsack
import CSLibExt.Computability.Complexity.Karp.PartitionSizes
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListCount
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatMachine
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatPair
import CSLibExt.Computability.Complexity.PolynomialEncoding.NormalizeRun
import CSLibExt.Computability.Complexity.SSVerifierSum
import CSLibExt.Computability.CookLevin
import MathlibExt.Computability.TuringMachine.Cleanup
import Mathlib.Tactic.Ring

/-!
# The MULTIPLE KNAPSACK verifier machine

`Verify.isPolyTime_mkCheck`: the certificate check `mkCheck` of `MultipleKnapsack` is computed
by a finite-stack machine in cubic time. The machine is private to this module.

* Decoding (`CapsTarget`, `Decode`): the raw encoding of `List (ℕ × ℕ) × List ℕ × ℕ` is decoded
  by the existing pair splitter, Nat-pair list projector, List Nat canonicalizer and Nat
  normalizer, following `ListNatPairPair`; noncanonical Nat payloads are accepted with Mathlib's
  total decoder and normalized. A decodable input leaves the canonical weight, value and capacity
  lists and the canonical target on four stacks.
* Checking (`Verify`): the existing frame counter initializes one unused flag per item. Each
  knapsack pass turns the next `k` certificate bits into the knapsack's mask and updates the
  flags, the existing SUBSET-SUM summing component adds the masked weights, and a
  least-significant-bit-first comparator checks the sum against the capacity. After the last
  knapsack the same summing component adds the values of the used items, which are compared with
  the target. The summing component consumes its mask stack; `sum_embed_suffix` shows that it
  never pushes onto it, which bounds the cleanup of the mask it leaves behind.
-/

namespace MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack

namespace CapsTarget

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.FramedCNF

/-- Pair workspace, the list canonicalizer's accumulator and Nat workspace, the target buffer,
and the two canonical outputs. -/
inductive K | pair (k : PairSplit.K) | acc | left | nat (k : NormalizeMachine.K) | buffer | right
  deriving DecidableEq

instance : Fintype K where
  elems := ⟨↑[K.pair .input, .pair .left, .pair .scratch, .acc, .left,
    .nat .input, .nat .buffer, .nat .output, .buffer, .right], by decide⟩
  complete k := by
    rcases k with k | _ | _ | k | _ | _ <;> try decide
    · cases k <;> decide
    · cases k <;> decide

/-- Pair projection, list canonicalization of the first field, normalization of the second. -/
inductive Lab | pair (l : PairSplit.Lab) | list (l : ListNatMachine.Lab)
  | norm (l : NormalizeMachine.Lab) | good | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.good, .bad} ∪ Finset.univ.image Lab.pair ∪ Finset.univ.image Lab.list ∪
    Finset.univ.image Lab.norm
  complete l := by cases l <;> simp

/-- The pair-frame component acts on its three own stacks. -/
def pairEmb : SEmb (fun _ : PairSplit.K => Bool) (fun _ : K => Bool) where
  e := K.pair
  inj _ _ h := K.pair.inj h
  ι _ := Equiv.refl Bool

/-- The list canonicalizer reads the first raw field. -/
def listEmb : SEmb (fun _ : ListNatMachine.K => Bool) (fun _ : K => Bool) where
  e
    | .input => .pair .left
    | .acc => .acc
    | .output => .left
    | .nat k => .nat k
  inj a b h := by
    cases a <;> cases b <;> simp_all
  ι _ := Equiv.refl Bool

/-- The Nat normalizer reads the second raw field. -/
def normEmb : SEmb (fun _ : NormalizeMachine.K => Bool) (fun _ : K => Bool) where
  e
    | .input => .pair .input
    | .buffer => .buffer
    | .output => .right
  inj a b h := by cases a <;> cases b <;> simp_all
  ι _ := Equiv.refl Bool

/-- Successful pair framing enters the list canonicalizer. -/
def pairLabel : PairSplit.Lab → Lab
  | .good => .list .loop
  | .bad => .bad
  | l => .pair l

/-- A canonicalized list continues with the target. -/
def listLabel : ListNatMachine.Lab → Lab
  | .good => .norm (.read none)
  | .bad => .bad
  | l => .list l

/-- The normalized target ends the decoder. -/
def normLabel : NormalizeMachine.Lab → Lab
  | .done => .good
  | l => .norm l

/-- All work is performed by the three existing finite components. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .pair l => mapS pairEmb pairLabel (PairSplit.prog l)
  | .list l => mapS listEmb listLabel (ListNatMachine.prog l)
  | .norm l => mapS normEmb normLabel (NormalizeMachine.prog l)
  | .good | .bad => .halt

/-- Raw input, first raw field and the two outputs; every other stack is empty. -/
def st (input first left right : List Bool) : K → List Bool
  | .pair .input => input
  | .pair .left => first
  | .left => left
  | .right => right
  | _ => []

/-- Pair decoding of a delimited first field. -/
theorem decode_delimit_append {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (p r : List Bool) :
    bitDecode (α := α × β) (delimit p ++ r) =
      (bitDecode (α := α) p).bind fun a => (bitDecode (α := β) r).map fun b => (a, b) := by
  change (match undelimit (delimit p ++ r) with
    | none => none
    | some (p, r) => match bitDecode (α := α) p, bitDecode (α := β) r with
      | some a, some b => some (a, b)
      | _, _ => none) = _
  rw [undelimit_delimit]
  dsimp only
  cases bitDecode (α := α) p <;> cases bitDecode (α := β) r <;> rfl

private theorem embeds_pair : Embeds pairEmb pairLabel PairSplit.prog prog := by
  intro l
  cases l with
  | read | copy => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem embeds_list : Embeds listEmb listLabel ListNatMachine.prog prog := by
  intro l
  cases l with
  | loop | block | back | nat _ | emit | finish => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem embeds_norm : Embeds normEmb normLabel NormalizeMachine.prog prog := by
  intro l
  cases l with
  | read _ | copy => exact Or.inl rfl
  | done => exact Or.inr rfl

private theorem pair_run (p r left right : List Bool) (v : Bool) :
    ∃ v', Run prog (2 * p.length + 2)
      ⟨some (.pair .read), v, st (delimit p ++ r) [] left right⟩
      ⟨some (.list .loop), v', st r p left right⟩ := by
  obtain ⟨v', hr⟩ := PairSplit.run_delimit p r [] v
  obtain ⟨T, ht, ha, hf⟩ := run_embed pairLabel embeds_pair _ _ _ _ _ _ _
    (st (delimit p ++ r) [] left right) hr
    (by intro k; cases k <;> simp [pairEmb, st, PairSplit.st])
  have he : T = st r p left right := by
    funext k
    rcases k with k | _ | _ | k | _ | _
    · cases k <;> simpa [pairEmb, st, PairSplit.st] using ha _
    all_goals exact hf _ (by intro j; cases j <;> simp [pairEmb])
  exact ⟨v', he ▸ ht⟩

private theorem list_run {p : List Bool} {cs : List ℕ} (h : bitDecode p = some cs)
    (r left right : List Bool) (v : Bool) :
    ∃ v', RunLe prog (11 * p.length + 2)
      ⟨some (.list .loop), v, st r p left right⟩
      ⟨some (.norm (.read none)), v', st r [] (bitEncode cs ++ left) right⟩ := by
  obtain ⟨v', hr⟩ := ListNatMachine.run_some h left v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed listLabel embeds_list hr
    (S' := st r p left right) (by
      intro k
      cases k with
      | nat k => cases k <;> rfl
      | _ => simp [listEmb, st, ListNatMachine.st])
  have he : T = st r [] (bitEncode cs ++ left) right := by
    funext k
    rcases k with k | _ | _ | k | _ | _
    · cases k with
      | left => simpa [listEmb, st, ListNatMachine.st] using ha .input
      | input | scratch => exact hf _ (by intro j; cases j <;> simp [listEmb])
    · simpa [listEmb, st, ListNatMachine.st] using ha .acc
    · simpa [listEmb, st, ListNatMachine.st] using ha .output
    · cases k <;> simpa [listEmb, st, ListNatMachine.st, NormalizeMachine.st] using ha (.nat _)
    all_goals exact hf _ (by intro j; cases j <;> simp [listEmb])
  exact ⟨v', he ▸ ht⟩

private theorem list_bad {p : List Bool} (h : bitDecode (α := List ℕ) p = none)
    (r left right : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (11 * p.length + 2)
      ⟨some (.list .loop), v, st r p left right⟩ ⟨some .bad, v', S⟩ := by
  obtain ⟨v', S, hr⟩ := ListNatMachine.run_none h [] left v
  obtain ⟨T, ht, _, _⟩ := runLe_embed listLabel embeds_list hr
    (S' := st r p left right) (by
      intro k
      cases k with
      | nat k => cases k <;> rfl
      | _ => simp [listEmb, st, ListNatMachine.st])
  exact ⟨v', T, ht.mono (by omega)⟩

private theorem norm_run (r left right : List Bool) (v : Bool) :
    ∃ v', RunLe prog (2 * r.length + 3)
      ⟨some (.norm (.read none)), v, st r [] left right⟩
      ⟨some .good, v', st [] [] left (normalizeNat r ++ right)⟩ := by
  obtain ⟨v', hr⟩ := normalizeNat_run_frame r right v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed normLabel embeds_norm hr
    (S' := st r [] left right)
    (by intro k; cases k <;> simp [normEmb, st, NormalizeMachine.st])
  have he : T = st [] [] left (normalizeNat r ++ right) := by
    funext k
    rcases k with k | _ | _ | k | _ | _
    · cases k with
      | input => simpa [normEmb, st, NormalizeMachine.st] using ha .input
      | left | scratch => exact hf _ (by intro j; cases j <;> simp [normEmb])
    · exact hf _ (by intro j; cases j <;> simp [normEmb])
    · exact hf _ (by intro j; cases j <;> simp [normEmb])
    · exact hf _ (by intro j; cases j <;> simp [normEmb])
    · simpa [normEmb, st, NormalizeMachine.st] using ha .buffer
    · simpa [normEmb, st, NormalizeMachine.st] using ha .output
  exact ⟨v', he ▸ ht⟩

/-- A successful decode of `List ℕ × ℕ` leaves the canonical list and target encodings, with
all scratch empty and previous output suffixes preserved. -/
theorem run_some {x : List Bool} {cs : List ℕ} {t : ℕ}
    (h : bitDecode x = some (cs, t)) (left right : List Bool) (v : Bool) :
    ∃ v', RunLe prog (12 * x.length + 7)
      ⟨some (.pair .read), v, st x [] left right⟩
      ⟨some .good, v', st [] [] (bitEncode cs ++ left)
        (Computability.encodeNat t ++ right)⟩ := by
  obtain ⟨p, r, hx, hp, hr⟩ := decoded_pair_parts h
  have ht : Computability.decodeNat r = t := Option.some.inj hr
  obtain ⟨v₁, h₁⟩ := pair_run p r left right v
  obtain ⟨v₂, h₂⟩ := list_run hp r left right v₁
  obtain ⟨v₃, h₃⟩ := norm_run r (bitEncode cs ++ left) right v₂
  rw [normalizeNat_eq_encode_decode, ht] at h₃
  rw [hx]
  refine ⟨v₃, (((h₁.le le_rfl).trans h₂).trans h₃).mono ?_⟩
  simp only [List.length_append, length_delimit]
  omega

/-- Malformed framing of the pair or of the capacity list reaches `bad` in linear time. -/
theorem run_none {x : List Bool} (h : bitDecode (α := List ℕ × ℕ) x = none)
    (left right : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (12 * x.length + 7)
      ⟨some (.pair .read), v, st x [] left right⟩ ⟨some .bad, v', S⟩ := by
  cases hu : undelimit x with
  | none =>
    obtain ⟨v', S, hr⟩ := PairSplit.run_none hu [] v
    obtain ⟨T, ht, _, _⟩ := runLe_embed pairLabel embeds_pair hr
      (S' := st x [] left right)
      (by intro k; cases k <;> simp [pairEmb, st, PairSplit.st])
    exact ⟨v', T, ht.mono (by omega)⟩
  | some pr =>
    obtain ⟨p, r⟩ := pr
    have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
    have hp : bitDecode (α := List ℕ) p = none := by
      rw [hx, decode_delimit_append] at h
      cases hp : bitDecode (α := List ℕ) p with
      | none => rfl
      | some cs =>
        rw [hp] at h
        have hr : bitDecode (α := ℕ) r = some (Computability.decodeNat r) := rfl
        simp [hr] at h
    obtain ⟨v₁, h₁⟩ := pair_run p r left right v
    obtain ⟨v₂, S, h₂⟩ := list_bad hp r left right v₁
    rw [hx]
    refine ⟨v₂, S, ((h₁.le le_rfl).trans h₂).mono ?_⟩
    simp only [List.length_append, length_delimit]
    omega

/-- The canonical outputs are bounded by the raw input length. -/
theorem output_length_le {x : List Bool} {cs : List ℕ} {t : ℕ}
    (h : bitDecode x = some (cs, t)) :
    (bitEncode cs).length + (Computability.encodeNat t).length ≤ 2 * x.length + 1 := by
  obtain ⟨p, r, hx, hp, hr⟩ := decoded_pair_parts h
  have ht : Computability.decodeNat r = t := Option.some.inj hr
  have h₁ := decoded_list_nat_encode_length_le hp
  have h₂ := length_normalizeNat_le r
  rw [normalizeNat_eq_encode_decode, ht] at h₂
  rw [hx, List.length_append, length_delimit]
  omega

end CapsTarget

namespace Decode

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding Cslib.Complexity.PolynomialEncoding

/-- The item-list projector's workspace and the second-field decoder's workspace; the second
field's target buffer also serves the initial outer split. -/
inductive K | items (k : ListNatPair.K) | caps (k : CapsTarget.K)
  deriving DecidableEq

instance : Fintype K where
  elems := Finset.univ.image K.items ∪ Finset.univ.image K.caps
  complete k := by cases k <;> simp

/-- The outer split, the item-list projector and the second-field decoder. -/
inductive Lab | split (l : PairSplit.Lab) | items (l : ListNatPair.Lab)
  | caps (l : CapsTarget.Lab) | good | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.good, .bad} ∪ Finset.univ.image Lab.split ∪
    Finset.univ.image Lab.items ∪ Finset.univ.image Lab.caps
  complete l := by cases l <;> simp

/-- The outer splitter reuses the second field's input and empty target buffer. -/
def splitEmb : SEmb (fun _ : PairSplit.K => Bool) (fun _ : K => Bool) where
  e
    | .input => .caps (.pair .input)
    | .left => .items .input
    | .scratch => .caps .buffer
  inj a b h := by cases a <;> cases b <;> simp_all
  ι _ := Equiv.refl Bool

/-- The list projector has its own workspace. -/
def itemsEmb : SEmb (fun _ : ListNatPair.K => Bool) (fun _ : K => Bool) where
  e := K.items
  inj _ _ h := K.items.inj h
  ι _ := Equiv.refl Bool

/-- The second-field decoder has its own workspace. -/
def capsEmb : SEmb (fun _ : CapsTarget.K => Bool) (fun _ : K => Bool) where
  e := K.caps
  inj _ _ h := K.caps.inj h
  ι _ := Equiv.refl Bool

/-- Successful outer framing enters the item-list projector. -/
def splitLabel : PairSplit.Lab → Lab
  | .good => .items .loop
  | .bad => .bad
  | l => .split l

/-- Successful item projection enters the second-field decoder. -/
def itemsLabel : ListNatPair.Lab → Lab
  | .good => .caps (.pair .read)
  | .bad => .bad
  | l => .items l

/-- The second-field decoder's halts are the whole decoder's outcomes. -/
def capsLabel : CapsTarget.Lab → Lab
  | .good => .good
  | .bad => .bad
  | l => .caps l

/-- The decoder is a composition of existing components. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .split l => mapS splitEmb splitLabel (PairSplit.prog l)
  | .items l => mapS itemsEmb itemsLabel (ListNatPair.prog l)
  | .caps l => mapS capsEmb capsLabel (CapsTarget.prog l)
  | .good | .bad => .halt

/-- Raw fields and the four outputs, with empty scratch. At entry the item field is empty and
the whole raw input is `capsRaw`. -/
def st (itemsRaw capsRaw weights values caps target : List Bool) : K → List Bool
  | .items k => ListNatPair.st itemsRaw [] [] weights values (NatPair.st [] [] [] [] [] []) k
  | .caps k => CapsTarget.st capsRaw [] caps target k

private theorem embeds_split : Embeds splitEmb splitLabel PairSplit.prog prog := by
  intro l
  cases l with
  | read | copy => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem embeds_items : Embeds itemsEmb itemsLabel ListNatPair.prog prog := by
  intro l
  cases l with
  | loop | block | back | pair l | emit b | finish b => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem embeds_caps : Embeds capsEmb capsLabel CapsTarget.prog prog := by
  intro l
  cases l with
  | pair l | list l | norm l => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem split_run (p r weights values caps target : List Bool) (v : Bool) :
    ∃ w, Run prog (2 * p.length + 2)
      ⟨some (.split .read), v, st [] (delimit p ++ r) weights values caps target⟩
      ⟨some (.items .loop), w, st p r weights values caps target⟩ := by
  obtain ⟨w, hr⟩ := PairSplit.run_delimit p r [] v
  obtain ⟨T, ht, ha, hf⟩ := run_embed splitLabel embeds_split
    _ _ _ _ _ _ _ (st [] (delimit p ++ r) weights values caps target)
    hr (by intro k; cases k <;>
      simp [splitEmb, st, ListNatPair.st, CapsTarget.st, PairSplit.st])
  have he : T = st p r weights values caps target := by
    funext k
    cases k with
    | items k =>
      cases k with
      | input =>
        simpa [splitEmb, st, ListNatPair.st, PairSplit.st] using ha .left
      | acc b | output b | pair k =>
        exact hf _ (by intro j; cases j <;> simp [splitEmb])
    | caps k =>
      cases k with
      | pair k =>
        cases k with
        | input =>
          simpa [splitEmb, st, CapsTarget.st, PairSplit.st] using ha .input
        | left | scratch =>
          exact hf _ (by intro j; cases j <;> simp [splitEmb])
      | buffer =>
        simpa [splitEmb, st, CapsTarget.st, PairSplit.st] using ha .scratch
      | acc | left | nat _ | right =>
        exact hf _ (by intro j; cases j <;> simp [splitEmb])
  exact ⟨w, he ▸ ht⟩

private theorem items_run {p : List Bool} {as : List (ℕ × ℕ)}
    (h : bitDecode p = some as)
    (r weights values caps target : List Bool) (v : Bool) :
    ∃ w, RunLe prog (16 * p.length + 3)
      ⟨some (.items .loop), v, st p r weights values caps target⟩
      ⟨some (.caps (.pair .read)), w,
        st [] r (bitEncode (as.map Prod.fst) ++ weights)
          (bitEncode (as.map Prod.snd) ++ values) caps target⟩ := by
  obtain ⟨w, hr⟩ := ListNatPair.run_some h weights values v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed itemsLabel embeds_items hr
    (S' := st p r weights values caps target)
    (by intro k; simp [itemsEmb, st])
  have he : T = st [] r (bitEncode (as.map Prod.fst) ++ weights)
      (bitEncode (as.map Prod.snd) ++ values) caps target := by
    funext k
    cases k with
    | items k => simpa [itemsEmb, st] using ha k
    | caps k => exact hf _ (by intro j; simp [itemsEmb])
  exact ⟨w, he ▸ ht⟩

private theorem caps_run {r : List Bool} {cs : List ℕ} {t : ℕ}
    (h : bitDecode r = some (cs, t))
    (weights values caps target : List Bool) (v : Bool) :
    ∃ w, RunLe prog (12 * r.length + 7)
      ⟨some (.caps (.pair .read)), v, st [] r weights values caps target⟩
      ⟨some .good, w, st [] [] weights values (bitEncode cs ++ caps)
        (Computability.encodeNat t ++ target)⟩ := by
  obtain ⟨w, hr⟩ := CapsTarget.run_some h caps target v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed capsLabel embeds_caps hr
    (S' := st [] r weights values caps target)
    (by intro k; simp [capsEmb, st])
  have he : T = st [] [] weights values (bitEncode cs ++ caps)
      (Computability.encodeNat t ++ target) := by
    funext k
    cases k with
    | items k => exact hf _ (by intro j; simp [capsEmb])
    | caps k => simpa [capsEmb, st] using ha k
  exact ⟨w, he ▸ ht⟩

/-- **The decoder on decodable inputs.** A decodable raw instance yields the canonical
encodings of the weight, value and capacity lists and of the target, preserving output
suffixes and emptying every input and scratch stack. -/
theorem run_some {x : List Bool} {items : List (ℕ × ℕ)} {cs : List ℕ} {t : ℕ}
    (h : bitDecode (α := MultipleKnapsackInstance) x = some (items, cs, t))
    (weights values caps target : List Bool) (v : Bool) :
    ∃ w, RunLe prog (20 * x.length + 12)
      ⟨some (.split .read), v, st [] x weights values caps target⟩
      ⟨some .good, w,
        st [] [] (bitEncode (items.map Prod.fst) ++ weights)
          (bitEncode (items.map Prod.snd) ++ values) (bitEncode cs ++ caps)
          (Computability.encodeNat t ++ target)⟩ := by
  obtain ⟨p, r, hx, hp, hr⟩ := decoded_pair_parts h
  obtain ⟨w, first⟩ := split_run p r weights values caps target v
  obtain ⟨z, middle⟩ := items_run hp r weights values caps target w
  obtain ⟨u, last⟩ := caps_run hr (bitEncode (items.map Prod.fst) ++ weights)
    (bitEncode (items.map Prod.snd) ++ values) caps target z
  rw [hx]
  refine ⟨u, (((first.le le_rfl).trans middle).trans last).mono ?_⟩
  simp only [List.length_append, length_delimit]
  omega

/-- The four canonical outputs are bounded by twice the raw input length. -/
theorem output_length_le {x : List Bool} {items : List (ℕ × ℕ)} {cs : List ℕ} {t : ℕ}
    (h : bitDecode (α := MultipleKnapsackInstance) x = some (items, cs, t)) :
    (bitEncode (items.map Prod.fst)).length + (bitEncode (items.map Prod.snd)).length +
      (bitEncode cs).length + (Computability.encodeNat t).length ≤ 2 * x.length := by
  obtain ⟨p, r, hx, hp, hr⟩ := decoded_pair_parts h
  have hi := ListNatPair.projection_length_le hp
  have hc := CapsTarget.output_length_le hr
  rw [hx, List.length_append, length_delimit]
  omega

/-- **The decoder on undecodable inputs.** Every failed decode reaches `bad` within the same
linear bound. -/
theorem run_none {x : List Bool}
    (h : bitDecode (α := MultipleKnapsackInstance) x = none)
    (weights values caps target : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (20 * x.length + 12)
      ⟨some (.split .read), v, st [] x weights values caps target⟩
      ⟨some .bad, w, S⟩ := by
  cases hu : undelimit x with
  | none =>
    obtain ⟨w, S, hr⟩ := PairSplit.run_none hu [] v
    obtain ⟨T, ht, _, _⟩ := runLe_embed splitLabel embeds_split hr
      (S' := st [] x weights values caps target)
      (by intro k; cases k <;>
        simp [splitEmb, st, ListNatPair.st, CapsTarget.st, PairSplit.st])
    exact ⟨w, T, ht.mono (by omega)⟩
  | some pr =>
    obtain ⟨p, r⟩ := pr
    have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
    obtain ⟨w, first⟩ := split_run p r weights values caps target v
    rw [hx, CapsTarget.decode_delimit_append] at h
    cases hi : bitDecode (α := List (ℕ × ℕ)) p with
    | none =>
      obtain ⟨z, S, hr⟩ := ListNatPair.run_none hi [] [] weights values w
      obtain ⟨T, ht, _, _⟩ := runLe_embed itemsLabel embeds_items hr
        (S' := st p r weights values caps target)
        (by intro k; simp [itemsEmb, st])
      rw [hx]
      refine ⟨z, T, ((first.le le_rfl).trans ht).mono ?_⟩
      simp only [List.length_append, length_delimit]
      omega
    | some as =>
      have hn : bitDecode (α := List ℕ × ℕ) r = none := by
        cases ht : bitDecode (α := List ℕ × ℕ) r with
        | none => rfl
        | some ct => simp [hi, ht] at h
      obtain ⟨z, middle⟩ := items_run hi r weights values caps target w
      obtain ⟨u, S, hr⟩ := CapsTarget.run_none hn caps target z
      obtain ⟨T, ht, _, _⟩ := runLe_embed capsLabel embeds_caps hr
        (S' := st [] r (bitEncode (as.map Prod.fst) ++ weights)
          (bitEncode (as.map Prod.snd) ++ values) caps target)
        (by intro k; simp [capsEmb, st])
      rw [hx]
      refine ⟨u, T, (((first.le le_rfl).trans middle).trans ht).mono ?_⟩
      simp only [List.length_append, length_delimit]
      omega

/-- **Total decoder contract.** The decoder reaches `good` exactly on decodable inputs, with the
four canonical outputs, and `bad` otherwise. -/
theorem run (x : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (20 * x.length + 12)
      ⟨some (.split .read), v, st [] x [] [] [] []⟩
      ⟨some (if (bitDecode (α := MultipleKnapsackInstance) x).isSome then .good else .bad),
        w, S⟩ ∧
      ∀ (items : List (ℕ × ℕ)) (cs : List ℕ) (t : ℕ),
        bitDecode (α := MultipleKnapsackInstance) x = some (items, cs, t) →
        S = st [] [] (bitEncode (items.map Prod.fst)) (bitEncode (items.map Prod.snd))
          (bitEncode cs) (Computability.encodeNat t) := by
  cases h : bitDecode (α := MultipleKnapsackInstance) x with
  | none =>
    obtain ⟨w, S, hr⟩ := run_none h [] [] [] [] v
    refine ⟨w, S, hr, ?_⟩
    intro items cs t ha
    simp at ha
  | some i =>
    obtain ⟨items, cs, t⟩ := i
    obtain ⟨w, hr⟩ := run_some h [] [] [] [] v
    refine ⟨w, _, by simpa using hr, ?_⟩
    intro items' cs' t' h'
    obtain ⟨rfl, h₂⟩ := Prod.mk.inj (Option.some.inj h')
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
    simp

/-- Embedded execution preserves every outside stack on both outcomes. -/
theorem run_embedded {J L : Type} [DecidableEq J] {Γ : J → Type}
    (E : SEmb (fun _ : K => Bool) Γ) (φ : Lab → L)
    {M : L → TM2.Stmt Γ L Bool} (hm : Embeds E φ prog M)
    (x : List Bool) (v : Bool) (S : ∀ j, List (Γ j))
    (hs : Agree E (st [] x [] [] [] []) S) :
    ∃ w T, RunLe M (20 * x.length + 12)
      ⟨some (φ (.split .read)), v, S⟩
      ⟨some (φ (if (bitDecode (α := MultipleKnapsackInstance) x).isSome
        then .good else .bad)), w, T⟩ ∧ Frame E S T ∧
      ∀ (items : List (ℕ × ℕ)) (cs : List ℕ) (t : ℕ),
        bitDecode (α := MultipleKnapsackInstance) x = some (items, cs, t) →
        Agree E (st [] [] (bitEncode (items.map Prod.fst)) (bitEncode (items.map Prod.snd))
          (bitEncode cs) (Computability.encodeNat t)) T := by
  obtain ⟨w, U, hr, hu⟩ := run x v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed φ hm hr hs
  refine ⟨w, T, ht, hf, ?_⟩
  intro items cs t h
  rw [hu items cs t h] at ha
  exact ha

end Decode

end MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack

namespace MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack.Verify

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.BitstringEncoding Computability
open Cslib.Complexity.Karp Cslib.Complexity.SatVerifier Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.FramedCNF

/-! ### Comparing binary numbers, least significant bit first -/

/-- **Comparison flag.** Reading two bit lists from the least significant bit, missing bits
counting as false, the flag records whether the first number exceeds the second on the bits read
so far; a higher differing bit overrides the flag. -/
def gtB : Bool → List Bool → List Bool → Bool
  | g, [], [] => g
  | g, [], b :: bs => gtB (if false = b then g else false) [] bs
  | g, a :: as, [] => gtB (if a = false then g else a) as []
  | g, a :: as, b :: bs => gtB (if a = b then g else a) as bs

theorem gtB_nil_encodeNat (g : Bool) (n : ℕ) (hn : 0 < n) : gtB g [] (encodeNat n) = false := by
  induction n using Nat.strong_induction_on generalizing g with
  | _ n ih =>
    rw [TM2Recursive.encodeNat_eq_cons hn.ne', gtB]
    rcases Nat.eq_zero_or_pos (n / 2) with h0 | h0
    · have h1 : n % 2 = 1 := by omega
      rw [h0, TM2Recursive.encodeNat_zero, gtB]
      simp [h1]
    · exact ih _ (Nat.div_lt_self hn one_lt_two) _ h0

theorem gtB_encodeNat_nil (g : Bool) (m : ℕ) (hm : 0 < m) : gtB g (encodeNat m) [] = true := by
  induction m using Nat.strong_induction_on generalizing g with
  | _ m ih =>
    rw [TM2Recursive.encodeNat_eq_cons hm.ne', gtB]
    rcases Nat.eq_zero_or_pos (m / 2) with h0 | h0
    · have h1 : m % 2 = 1 := by omega
      rw [h0, TM2Recursive.encodeNat_zero, gtB]
      simp [h1]
    · exact ih _ (Nat.div_lt_self hm one_lt_two) _ h0

/-- **The comparator is correct on canonical numbers.** -/
theorem gtB_encodeNat (g : Bool) (m n : ℕ) :
    gtB g (encodeNat m) (encodeNat n) = if m = n then g else decide (n < m) := by
  induction m using Nat.strong_induction_on generalizing g n with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [TM2Recursive.encodeNat_zero, gtB]
      · rw [TM2Recursive.encodeNat_zero, gtB_nil_encodeNat g n hn, ite_eq_right (by omega)]
        simp
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [TM2Recursive.encodeNat_zero, gtB_encodeNat_nil g m hm, ite_eq_right (by omega)]
        simp [hm]
      · rw [TM2Recursive.encodeNat_eq_cons hm.ne', TM2Recursive.encodeNat_eq_cons hn.ne', gtB,
          ih _ (Nat.div_lt_self hm one_lt_two)]
        by_cases hq : m / 2 = n / 2
        · rw [ite_eq_left hq]
          by_cases hr : m % 2 = n % 2
          · rw [ite_eq_left (by rw [hr]), ite_eq_left (by omega)]
          · rw [ite_eq_right (by simp only [decide_eq_decide]; omega), ite_eq_right (by omega)]
            exact decide_eq_decide.mpr (by omega)
        · rw [ite_eq_right hq, ite_eq_right (by omega)]
          exact decide_eq_decide.mpr (by omega)

/-! ### Stacks never pushed by the summing component -/

/-- A statement that never pushes onto stack `k`. -/
def NoPush {K Λ σ : Type} {Γ : K → Type} (k : K) : TM2.Stmt Γ Λ σ → Prop
  | .push k' _ q => k' ≠ k ∧ NoPush k q
  | .peek _ _ q => NoPush k q
  | .pop _ _ q => NoPush k q
  | .load _ q => NoPush k q
  | .branch _ q₁ q₂ => NoPush k q₁ ∧ NoPush k q₂
  | .goto _ => True
  | .halt => True

theorem stepAux_suffix {K Λ σ : Type} [DecidableEq K] {Γ : K → Type} (k : K) :
    ∀ (q : TM2.Stmt Γ Λ σ), NoPush k q → ∀ (v : σ) (S : ∀ k, List (Γ k)),
      ((TM2.stepAux q v S).stk k) <:+ S k
  | .push k' f q, ⟨hk, hq⟩, v, S => by
    refine (stepAux_suffix k q hq v _).trans ?_
    rw [update_of_ne (Ne.symm hk)]
  | .peek k' f q, hq, v, S => stepAux_suffix k q hq _ S
  | .pop k' f q, hq, v, S => by
    refine (stepAux_suffix k q hq _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [update_self]
      exact List.tail_suffix _
    · rw [update_of_ne h]
  | .load a q, hq, v, S => stepAux_suffix k q hq _ S
  | .branch f q₁ q₂, ⟨h₁, h₂⟩, v, S => by
    simp only [TM2.stepAux]
    cases f v
    · exact stepAux_suffix k q₂ h₂ v S
    · exact stepAux_suffix k q₁ h₁ v S
  | .goto f, _, v, S => List.suffix_refl _
  | .halt, _, v, S => List.suffix_refl _

theorem run_suffix {K Λ σ : Type} [DecidableEq K] {Γ : K → Type} {M : Λ → TM2.Stmt Γ Λ σ}
    (k : K) (hM : ∀ l, NoPush k (M l)) :
    ∀ (n : ℕ) (c d : TM2.Cfg Γ Λ σ), Run M n c d → d.stk k <:+ c.stk k := by
  intro n
  induction n with
  | zero =>
    intro c d h
    simp only [Run, iterate_zero, id_eq, Option.some.injEq] at h
    subst h
    exact List.suffix_refl _
  | succ n ih =>
    intro c d h
    unfold Run at h
    rw [iterate_succ_apply] at h
    rcases c with ⟨_ | l, v, S⟩
    · have : (flip bind (TM2.step M)) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none := rfl
      rw [this, iter_none] at h
      exact absurd h (by simp)
    · have e : (flip bind (TM2.step M)) (some (⟨some l, v, S⟩ : TM2.Cfg Γ Λ σ)) =
          some (TM2.stepAux (M l) v S) := rfl
      rw [e] at h
      exact (ih _ _ h).trans (stepAux_suffix k (M l) (hM l) v S)

theorem ss_noPush_W (l : SSVerify.Lab) : NoPush SSVerify.K.W (SSVerify.prog l) := by
  cases l <;>
    simp [SSVerify.prog, NoPush, SSVerify.rdS, SSVerify.addS, SSVerify.finS, SSVerify.nextS,
      moveB, cmpB]
  all_goals split <;> simp [NoPush]

/-- **The summing component in a host, with the mask it leaves behind.** As
`SSVerifierSum.sum_embed`, and the leftover mask is a suffix of the original mask. -/
theorem sum_embed_suffix {K Λ : Type} [DecidableEq K] {Γ : K → Type}
    (E : SEmb (fun _ : SSVerify.K => Sym) Γ)
    (φ : SSVerify.Lab → Λ) (M : Λ → TM2.Stmt Γ Λ Bool)
    (hM : Embeds E φ SSVerify.prog M) (hφ : φ .yes = φ .no)
    (as : List ℕ) (w : List Bool) (v : Bool) (S : ∀ k, List (Γ k))
    (hS : Agree E (SSVerify.st
      ((as.flatMap fun a => delimit (encodeNat a)).map .bit) (w.map .bit) [] [] []) S) :
    let n := (as.flatMap fun a => delimit (encodeNat a)).length
    ∃ v' w' S', RunLe M (n * (2 * n + 6) + n + 3)
      ⟨some (φ .next), v, S⟩ ⟨some (φ .yes), v', S'⟩ ∧
      Agree E (SSVerify.st [] w' [] []
        ((encodeNat (SSVerify.pick as w).sum).map .bit).reverse) S' ∧ Frame E S S' ∧
      w'.length ≤ w.length := by
  intro n
  obtain ⟨v', w', hr⟩ := Cslib.Complexity.SSVerifierSum.sum_component_run as w v
  have hsuf : w' <:+ w.map Sym.bit := by
    obtain ⟨m, -, hm⟩ := hr
    have := run_suffix SSVerify.K.W ss_noPush_W m _ _ hm
    simpa [SSVerify.st] using this
  obtain ⟨S', hrun, hagree, hframe⟩ := runLe_embed φ hM hr hS
  refine ⟨v', w', S', ?_, hagree, hframe, by simpa using hsuf.length_le⟩
  have he : φ (if encodeNat (SSVerify.pick as w).sum = []
      then .yes else .no) = φ .yes := by
    split <;> simp_all
  rwa [he] at hrun

/-! ### The machine -/

/-- Stacks: the decoder's workspace, the frame counter's input and scratch, the summing
component's stacks, the certificate, the unused flags, the new flags, the reversed mask, a
buffer and the two comparator operands. -/
inductive K
  | dec (k : Decode.K) | cin | cscr | sum (k : SSVerify.K)
  | W | U | U' | M' | Z | P | Q
  deriving DecidableEq

instance : Fintype K where
  elems := {K.cin, .cscr, .W, .U, .U', .M', .Z, .P, .Q} ∪ Finset.univ.image K.dec ∪
    Finset.univ.image K.sum
  complete k := by cases k <;> simp

/-- The summing component's stacks hold its symbols; all other stacks hold bits. -/
@[reducible] def Γ : K → Type
  | .sum _ => Sym
  | _ => Bool

/-- Decoding, flag initialization, one pass per knapsack, the value check. -/
inductive Lab
  | dec (l : Decode.Lab) | cw1 | cw2 | cnt (l : Cslib.Complexity.PolynomialEncoding.ListCount.Lab)
  | knap | orp | revU | revM | sw1 | sw2 | sum (f : Bool) (l : SSVerify.Lab)
  | clw (f : Bool) | mvB (f : Bool) | rdC | mvC
  | cmp (f g : Bool) | cmpA (f g a : Bool)
  | fu1 | fu2 | sv1 | sv2 | tv1 | tv2 | yes | no
  deriving DecidableEq

/-- The decoded weight list. -/
abbrev WS : K := .dec (.items (.output false))
/-- The decoded value list. -/
abbrev VS : K := .dec (.items (.output true))
/-- The remaining capacity list. -/
abbrev CS : K := .dec (.caps .left)
/-- The decoded target. -/
abbrev TV : K := .dec (.caps .right)

/-- The decoder's own workspace. -/
def decEmb : SEmb (fun _ : Decode.K => Bool) Γ where
  e := K.dec
  inj _ _ h := K.dec.inj h
  ι _ := Equiv.refl Bool

/-- The frame counter counts into the unused flags. -/
def cntEmb : SEmb (fun _ : Cslib.Complexity.PolynomialEncoding.ListCount.K => Bool) Γ where
  e
    | .input => .cin
    | .scratch => .cscr
    | .count => .U
  inj a b h := by cases a <;> cases b <;> simp_all
  ι k := match k with
    | .input => Equiv.refl Bool
    | .scratch => Equiv.refl Bool
    | .count => Equiv.refl Bool

/-- The summing component's own stacks. -/
def sumEmb : SEmb (fun _ : SSVerify.K => Sym) Γ where
  e := K.sum
  inj _ _ h := K.sum.inj h
  ι _ := Equiv.refl Sym

/-- A decoded instance initializes the flags; an undecodable one is rejected. -/
def decLabel : Decode.Lab → Lab
  | .good => .cw1
  | .bad => .no
  | l => .dec l

/-- After counting, the knapsack loop starts. -/
def cntLabel : Cslib.Complexity.PolynomialEncoding.ListCount.Lab → Lab
  | .good => .knap
  | .bad => .no
  | l => .cnt l

/-- Both halts of the summing component continue with the cleanup of its mask. -/
def sumLabel (f : Bool) : SSVerify.Lab → Lab
  | .yes => .clw f
  | .no => .clw f
  | l => .sum f l

/-- One step of the flag update: pop a flag and a certificate bit, push the new flag and the
mask bit. -/
def orpS : TM2.Stmt Γ Lab Bool :=
  .peek .U (fun _ o => o.isSome) <| .branch id
    (.pop .U (fun _ o => o.getD false) <| .branch id
      (.pop .W (fun _ o => o.getD false) <| .push .U' (fun m => !m) <| .push .M' id <|
        .goto fun _ => .orp)
      (.pop .W (fun _ o => o.getD false) <| .push .U' (fun _ => false) <| .push .M' id <|
        .goto fun _ => .orp))
    (.goto fun _ => .revU)

/-- One step of the comparison of `P` with `Q`, least significant bit first. -/
def cmpS (f g : Bool) : TM2.Stmt Γ Lab Bool :=
  .peek .P (fun _ o => o.isSome) <| .branch id
    (.pop .P (fun _ o => o.getD false) <| .goto fun a => .cmpA f g a)
    (.peek .Q (fun _ o => o.isSome) <| .branch id
      (.goto fun _ => .cmpA f g false)
      (.goto fun _ => if g then .no else if f then .yes else .knap))

/-- **The verifier program.** -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .dec l => mapS decEmb decLabel (Decode.prog l)
  | .cw1 => moveB WS .Z some id .cw1 .cw2
  | .cw2 => splitB .Z WS .cin some id id .cw2 (.cnt .loop)
  | .cnt l => mapS cntEmb cntLabel (Cslib.Complexity.PolynomialEncoding.ListCount.prog l)
  | .knap => .peek CS (fun _ o => o.isSome) <| .branch id
      (.goto fun _ => .orp) (.goto fun _ => .fu1)
  | .orp => orpS
  | .revU => moveB .U' .U some id .revU .revM
  | .revM => moveB .M' (.sum .W) some Sym.bit .revM .sw1
  | .sw1 => moveB WS .Z some id .sw1 .sw2
  | .sw2 => splitB .Z WS (.sum .X) some id Sym.bit .sw2 (.sum false .next)
  | .sum f l => mapS sumEmb (sumLabel f) (SSVerify.prog l)
  | .clw f => cleanS [.sum .W] (.clw f) (.mvB f)
  | .mvB false => moveB (.sum .B) .P Sym.bit? id (.mvB false) .rdC
  | .mvB true => moveB (.sum .B) .Q Sym.bit? id (.mvB true) .tv1
  | .rdC => Block.read CS .Z some id .rdC .mvC .no
  | .mvC => moveB .Z .Q some id .mvC (.cmp false false)
  | .cmp f g => cmpS f g
  | .cmpA f g a => .pop .Q (fun _ o => o.getD false) <|
      .goto fun b => .cmp f (if a = b then g else a)
  | .fu1 => moveB .U .Z some id .fu1 .fu2
  | .fu2 => moveB .Z (.sum .W) some (fun b => Sym.bit (!b)) .fu2 .sv1
  | .sv1 => moveB VS .Z some id .sv1 .sv2
  | .sv2 => splitB .Z VS (.sum .X) some id Sym.bit .sv2 (.sum true .next)
  | .tv1 => moveB TV .Z some id .tv1 .tv2
  | .tv2 => moveB .Z .P some id .tv2 (.cmp true false)
  | .yes | .no => .halt

/-- Explicit stack contents: the decoder's outputs, the summing component's stacks, and the
verifier's own stacks; the counter's stacks are empty. -/
def ist (ws vs cs tv u w u' m' z p q : List Bool) (sm : ∀ _ : SSVerify.K, List Sym) :
    ∀ k, List (Γ k)
  | .dec k => Decode.st [] [] ws vs cs tv k
  | .cin => []
  | .cscr => []
  | .sum k => sm k
  | .W => w
  | .U => u
  | .U' => u'
  | .M' => m'
  | .Z => z
  | .P => p
  | .Q => q

/-- Empty summing component stacks. -/
abbrev noSum : ∀ _ : SSVerify.K, List Sym := fun _ => []

theorem orp_run (ws vs cs tv : List Bool) :
    ∀ (us wr u' m' : List Bool) (v : Bool),
      ∃ v', Run prog (us.length + 1)
        ⟨some .orp, v, ist ws vs cs tv us wr u' m' [] [] [] noSum⟩
        ⟨some .revU, v', ist ws vs cs tv [] (wr.drop us.length)
          ((orStep us wr).reverse ++ u') ((maskTake us wr).reverse ++ m') [] [] [] noSum⟩ := by
  intro us
  induction us with
  | nil =>
    intro wr u' m' v
    refine ⟨false, Run.single ?_⟩
    simp [prog, orpS, TM2.stepAux, ist, orStep, maskTake]
  | cons u us ih =>
    intro wr u' m' v
    obtain ⟨v', h⟩ := ih wr.tail ((u && !wr.headD false) :: u') (wr.headD false :: m')
      (wr.headD false)
    have hstep : TM2.step prog ⟨some .orp, v, ist ws vs cs tv (u :: us) wr u' m' [] [] [] noSum⟩ =
        some ⟨some .orp, wr.headD false, ist ws vs cs tv us wr.tail
          ((u && !wr.headD false) :: u') (wr.headD false :: m') [] [] [] noSum⟩ := by
      cases u <;> cases wr <;>
      · simp only [TM2.step, prog, orpS, TM2.stepAux, ist, List.head?_cons,
          Option.isSome_some, id_eq, Bool.cond_true, Bool.cond_false, Option.getD_some,
          List.tail_cons, List.tail_nil, List.headD_cons, List.headD_nil, Bool.true_and,
          Bool.false_and, Bool.not_false]
        congr 2
        funext k
        cases k <;> rfl
    refine ⟨v', ?_⟩
    have h' := Run.head hstep h
    simpa [orStep, maskTake, List.reverse_cons, List.append_assoc, List.drop_tail] using h'

theorem cmp_run (ws vs cs tv u w : List Bool) (f : Bool) :
    ∀ (as bs : List Bool) (g v : Bool),
      ∃ v', Run prog (2 * max as.length bs.length + 1)
        ⟨some (.cmp f g), v, ist ws vs cs tv u w [] [] [] as bs noSum⟩
        ⟨some (if gtB g as bs then .no else if f then .yes else .knap), v',
          ist ws vs cs tv u w [] [] [] [] [] noSum⟩
  | [], [], g, v => ⟨false, Run.single (by simp [prog, cmpS, TM2.stepAux, ist, gtB])⟩
  | [], b :: bs, g, v => by
    obtain ⟨v', h⟩ := cmp_run ws vs cs tv u w f [] bs (if false = b then g else false) b
    refine ⟨v', ?_⟩
    simp only [gtB]
    have h₁ : TM2.step prog ⟨some (.cmp f g), v, ist ws vs cs tv u w [] [] [] [] (b :: bs) noSum⟩
        = some ⟨some (.cmpA f g false), true, ist ws vs cs tv u w [] [] [] [] (b :: bs) noSum⟩ := by
      simp [TM2.step, prog, cmpS, TM2.stepAux, ist]
    have h₂ : TM2.step prog ⟨some (.cmpA f g false), true,
        ist ws vs cs tv u w [] [] [] [] (b :: bs) noSum⟩ =
        some ⟨some (.cmp f (if false = b then g else false)), b,
          ist ws vs cs tv u w [] [] [] [] bs noSum⟩ := by
      simp only [TM2.step, prog, TM2.stepAux, ist, List.head?_cons,
        Option.getD_some, List.tail_cons]
      congr 2
      funext k
      cases k <;> rfl
    have := Run.head h₁ (Run.head h₂ h)
    refine this.of_eq ?_
    simp only [List.length_nil, List.length_cons]
    omega
  | a :: as, [], g, v => by
    obtain ⟨v', h⟩ := cmp_run ws vs cs tv u w f as [] (if a = false then g else a) false
    refine ⟨v', ?_⟩
    simp only [gtB]
    have h₁ : TM2.step prog ⟨some (.cmp f g), v, ist ws vs cs tv u w [] [] [] (a :: as) [] noSum⟩
        = some ⟨some (.cmpA f g a), a, ist ws vs cs tv u w [] [] [] as [] noSum⟩ := by
      simp only [TM2.step, prog, cmpS, TM2.stepAux, ist, List.head?_cons,
        Option.isSome_some, id_eq, Bool.cond_true, Option.getD_some, List.tail_cons]
      congr 2
      funext k
      cases k <;> rfl
    have h₂ : TM2.step prog ⟨some (.cmpA f g a), a, ist ws vs cs tv u w [] [] [] as [] noSum⟩ =
        some ⟨some (.cmp f (if a = false then g else a)), false,
          ist ws vs cs tv u w [] [] [] as [] noSum⟩ := by
      simp only [TM2.step, prog, TM2.stepAux, ist, List.head?_nil,
        Option.getD_none, List.tail_nil]
      congr 2
      funext k
      cases k <;> rfl
    have := Run.head h₁ (Run.head h₂ h)
    refine this.of_eq ?_
    simp only [List.length_nil, List.length_cons]
    omega
  | a :: as, b :: bs, g, v => by
    obtain ⟨v', h⟩ := cmp_run ws vs cs tv u w f as bs (if a = b then g else a) b
    refine ⟨v', ?_⟩
    simp only [gtB]
    have h₁ : TM2.step prog
        ⟨some (.cmp f g), v, ist ws vs cs tv u w [] [] [] (a :: as) (b :: bs) noSum⟩
        = some ⟨some (.cmpA f g a), a, ist ws vs cs tv u w [] [] [] as (b :: bs) noSum⟩ := by
      simp only [TM2.step, prog, cmpS, TM2.stepAux, ist, List.head?_cons,
        Option.isSome_some, id_eq, Bool.cond_true, Option.getD_some, List.tail_cons]
      congr 2
      funext k
      cases k <;> rfl
    have h₂ : TM2.step prog
        ⟨some (.cmpA f g a), a, ist ws vs cs tv u w [] [] [] as (b :: bs) noSum⟩ =
        some ⟨some (.cmp f (if a = b then g else a)), b,
          ist ws vs cs tv u w [] [] [] as bs noSum⟩ := by
      simp only [TM2.step, prog, TM2.stepAux, ist, List.head?_cons,
        Option.getD_some, List.tail_cons]
      congr 2
      funext k
      cases k <;> rfl
    have := Run.head h₁ (Run.head h₂ h)
    refine this.of_eq ?_
    simp only [List.length_cons]
    omega

/-! ### One knapsack pass -/

section Pass

variable (ws vs cs tv : List Bool)

private theorem knap_orp_run (cs : List Bool) (hcs : cs ≠ []) (u w : List Bool) (v : Bool) :
    ∃ v', Run prog (u.length + 2)
      ⟨some .knap, v, ist ws vs cs tv u w [] [] [] [] [] noSum⟩
      ⟨some .revU, v', ist ws vs cs tv [] (w.drop u.length)
        (orStep u w).reverse (maskTake u w).reverse [] [] [] noSum⟩ := by
  have h₁ : Run prog 1 ⟨some .knap, v, ist ws vs cs tv u w [] [] [] [] [] noSum⟩
      ⟨some .orp, true, ist ws vs cs tv u w [] [] [] [] [] noSum⟩ := by
    refine Run.single ?_
    obtain ⟨b, cs', rfl⟩ := List.exists_cons_of_ne_nil hcs
    simp [prog, TM2.stepAux, ist, Decode.st, CapsTarget.st]
  obtain ⟨v', h₂⟩ := orp_run ws vs cs tv u w [] [] true
  simp only [List.append_nil] at h₂
  exact ⟨v', (h₁.trans h₂).of_eq (by omega)⟩

private theorem rev_run (u' m' w : List Bool) (v : Bool) :
    ∃ v', Run prog (u'.length + m'.length + 2)
      ⟨some .revU, v, ist ws vs cs tv [] w u'.reverse m'.reverse [] [] [] noSum⟩
      ⟨some .sw1, v', ist ws vs cs tv u' w [] [] [] [] []
        (update noSum .W (m'.map Sym.bit))⟩ := by
  obtain ⟨v₁, S₁, h₁, ha₁, hb₁, hk₁⟩ := moveB_run (M := prog) (a := K.U') (b := K.U)
    (d := some) (g := id) (self := Lab.revU) (next := Lab.revM) rfl (by decide)
    u'.reverse u'.reverse [] v (ist ws vs cs tv [] w u'.reverse m'.reverse [] [] [] noSum)
    (by simp [ist]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hS₁ : S₁ = ist ws vs cs tv u' w [] m'.reverse [] [] [] noSum := by
    funext k
    cases k with
    | U' => exact ha₁
    | U => simpa [ist] using hb₁
    | _ => exact hk₁ _ (by simp) (by simp)
  rw [hS₁] at h₁
  obtain ⟨v₂, S₂, h₂, ha₂, hb₂, hk₂⟩ := moveB_run (M := prog) (a := K.M') (b := K.sum .W)
    (d := some) (g := Sym.bit) (self := Lab.revM) (next := Lab.sw1) rfl (by decide)
    m'.reverse m'.reverse [] v₁ (ist ws vs cs tv u' w [] m'.reverse [] [] [] noSum)
    (by simp [ist]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hS₂ : S₂ = ist ws vs cs tv u' w [] [] [] [] [] (update noSum .W (m'.map Sym.bit)) := by
    funext k
    cases k with
    | M' => exact ha₂
    | sum j =>
      by_cases hj : j = .W
      · subst hj
        simpa [ist, List.map_reverse] using hb₂
      · rw [hk₂ _ (by simp) (by simpa using hj)]
        simp [ist, hj]
    | _ => exact hk₂ _ (by simp) (by simp)
  rw [hS₂] at h₂
  exact ⟨v₂, (h₁.trans h₂).of_eq (by simp; omega)⟩

private theorem copyW_run (u w : List Bool) (sm : ∀ _ : SSVerify.K, List Sym)
    (hX : sm .X = []) (v : Bool) :
    Run prog (2 * ws.length + 2)
      ⟨some .sw1, v, ist ws vs cs tv u w [] [] [] [] [] sm⟩
      ⟨some (.sum false .next), false, ist ws vs cs tv u w [] [] [] [] []
        (update sm .X (ws.map Sym.bit))⟩ := by
  obtain ⟨S', h, ha, ht, hb, hk⟩ := copyB_run (M := prog) (a := WS) (b := K.sum .X)
    (t := K.Z) (da := some) (dt := some) (ga := id) (gb := Sym.bit) (gt := id)
    (first := .sw1) (second := .sw2) (next := .sum false .next) rfl rfl (by decide)
    (by decide) (by decide) (fun _ => rfl) (fun _ => rfl) ws [] v
    (ist ws vs cs tv u w [] [] [] [] [] sm) (by simp [ist, Decode.st, ListNatPair.st])
    (by simp [EndsBitBlock]) (by simp [ist, EndsBitBlock])
  have hS : S' = ist ws vs cs tv u w [] [] [] [] [] (update sm .X (ws.map Sym.bit)) := by
    funext k
    cases k with
    | dec j =>
      by_cases hj : j = .items (.output false)
      · subst hj
        exact ha
      · rw [hk _ (by simpa using hj) (by simp) (by simp)]
        rfl
    | sum j =>
      by_cases hj : j = .X
      · subst hj
        simpa [ist, hX] using hb
      · rw [hk _ (by simp) (by simpa using hj) (by simp)]
        simp [ist, hj]
    | Z => exact ht
    | _ => exact hk _ (by simp) (by simp) (by simp)
  rw [hS] at h
  exact h

theorem embeds_sum (f : Bool) : Embeds sumEmb (sumLabel f) SSVerify.prog prog := by
  intro l
  cases l <;> simp [sumLabel, prog, SSVerify.prog]

private theorem sum_clean_run (f : Bool) (as : List ℕ) (mask u w p q : List Bool) (v : Bool) :
    ∃ v', RunLe prog ((as.flatMap fun a => delimit (encodeNat a)).length *
        (2 * (as.flatMap fun a => delimit (encodeNat a)).length + 6) +
        (as.flatMap fun a => delimit (encodeNat a)).length + 3 + (mask.length + 1))
      ⟨some (.sum f .next), v, ist ws vs cs tv u w [] [] [] p q
        (SSVerify.st ((as.flatMap fun a => delimit (encodeNat a)).map Sym.bit)
          (mask.map Sym.bit) [] [] [])⟩
      ⟨some (.mvB f), v', ist ws vs cs tv u w [] [] [] p q
        (SSVerify.st [] [] [] []
          ((encodeNat (SSVerify.pick as mask).sum).map Sym.bit).reverse)⟩ := by
  obtain ⟨v₁, w', S₁, h₁, hA, hF, hlen⟩ := sum_embed_suffix sumEmb (sumLabel f) prog
    (embeds_sum f) rfl as mask v
    (ist ws vs cs tv u w [] [] [] p q
      (SSVerify.st ((as.flatMap fun a => delimit (encodeNat a)).map Sym.bit)
        (mask.map Sym.bit) [] [] []))
    (by intro k; exact (List.map_id _).symm)
  have hS₁ : S₁ = ist ws vs cs tv u w [] [] [] p q
      (SSVerify.st [] w' [] [] ((encodeNat (SSVerify.pick as mask).sum).map Sym.bit).reverse) := by
    funext k
    cases k with
    | sum j => exact (hA j).trans (List.map_id _)
    | _ => exact hF _ (by intro j; simp [sumEmb])
  rw [hS₁] at h₁
  have h₂ := clean_run (M := prog) (ks := [K.sum .W]) (self := Lab.clw f) (next := Lab.mvB f)
    rfl (by simp) mask.length v₁
    (ist ws vs cs tv u w [] [] [] p q
      (SSVerify.st [] w' [] [] ((encodeNat (SSVerify.pick as mask).sum).map Sym.bit).reverse))
    (by intro k hk; simp only [List.mem_singleton] at hk; subst hk; simpa [ist, SSVerify.st])
  have he : (fun k => if k ∈ [K.sum .W] then [] else
      ist ws vs cs tv u w [] [] [] p q
        (SSVerify.st [] w' [] [] ((encodeNat (SSVerify.pick as mask).sum).map Sym.bit).reverse)
        k) =
      ist ws vs cs tv u w [] [] [] p q
        (SSVerify.st [] [] [] []
          ((encodeNat (SSVerify.pick as mask).sum).map Sym.bit).reverse) := by
    funext k
    cases k with
    | sum j => cases j <;> simp [ist, SSVerify.st]
    | _ => simp [ist]
  rw [he] at h₂
  exact ⟨false, h₁.trans h₂⟩

private theorem mvB_false_run (bs u w : List Bool) (v : Bool) :
    ∃ v', Run prog (bs.length + 1)
      ⟨some (.mvB false), v, ist ws vs cs tv u w [] [] [] [] []
        (SSVerify.st [] [] [] [] (bs.map Sym.bit).reverse)⟩
      ⟨some .rdC, v', ist ws vs cs tv u w [] [] [] bs [] noSum⟩ := by
  obtain ⟨v', S', h, ha, hb, hk⟩ := moveB_run (M := prog) (a := K.sum .B) (b := K.P)
    (d := Sym.bit?) (g := id) (self := Lab.mvB false) (next := Lab.rdC) rfl (by decide)
    bs.reverse (bs.map Sym.bit).reverse [] v
    (ist ws vs cs tv u w [] [] [] [] [] (SSVerify.st [] [] [] [] (bs.map Sym.bit).reverse))
    (by simp [ist, SSVerify.st]) (by simp [IsBitBlock, List.map_reverse, Sym.bit?])
    (by simp [EndsBitBlock])
  have hS : S' = ist ws vs cs tv u w [] [] [] bs [] noSum := by
    funext k
    cases k with
    | sum j =>
      by_cases hj : j = .B
      · subst hj
        exact ha
      · rw [hk _ (by simpa using hj) (by simp)]
        cases j <;> simp_all [ist, SSVerify.st]
    | P => simpa [ist] using hb
    | _ => exact hk _ (by simp) (by simp)
  exact ⟨v', (hS ▸ h).of_eq (by simp)⟩

private theorem mvB_true_run (bs u w : List Bool) (v : Bool) :
    ∃ v', Run prog (bs.length + 1)
      ⟨some (.mvB true), v, ist ws vs cs tv u w [] [] [] [] []
        (SSVerify.st [] [] [] [] (bs.map Sym.bit).reverse)⟩
      ⟨some .tv1, v', ist ws vs cs tv u w [] [] [] [] bs noSum⟩ := by
  obtain ⟨v', S', h, ha, hb, hk⟩ := moveB_run (M := prog) (a := K.sum .B) (b := K.Q)
    (d := Sym.bit?) (g := id) (self := Lab.mvB true) (next := Lab.tv1) rfl (by decide)
    bs.reverse (bs.map Sym.bit).reverse [] v
    (ist ws vs cs tv u w [] [] [] [] [] (SSVerify.st [] [] [] [] (bs.map Sym.bit).reverse))
    (by simp [ist, SSVerify.st]) (by simp [IsBitBlock, List.map_reverse, Sym.bit?])
    (by simp [EndsBitBlock])
  have hS : S' = ist ws vs cs tv u w [] [] [] [] bs noSum := by
    funext k
    cases k with
    | sum j =>
      by_cases hj : j = .B
      · subst hj
        exact ha
      · rw [hk _ (by simpa using hj) (by simp)]
        cases j <;> simp_all [ist, SSVerify.st]
    | Q => simpa [ist] using hb
    | _ => exact hk _ (by simp) (by simp)
  exact ⟨v', (hS ▸ h).of_eq (by simp)⟩

theorem decode_st_ne_caps {j : Decode.K} (hj : j ≠ .caps .left) (a b ws vs cs cs' tv : List Bool) :
    Decode.st a b ws vs cs tv j = Decode.st a b ws vs cs' tv j := by
  rcases j with j | ((_ | _ | _) | _ | _ | (_ | _ | _) | _ | _) <;>
    first | rfl | exact absurd rfl hj

private theorem cap_run (c : ℕ) (rest u w p : List Bool) (v : Bool) :
    ∃ v', Run prog (2 * (encodeNat c).length + 2)
      ⟨some .rdC, v, ist ws vs (delimit (encodeNat c) ++ rest) tv u w [] [] [] p [] noSum⟩
      ⟨some (.cmp false false), v', ist ws vs rest tv u w [] [] [] p (encodeNat c) noSum⟩ := by
  obtain ⟨S₁, h₁, ha₁, hb₁, hk₁⟩ := Block.run_delimit (M := prog) (a := CS) (b := K.Z)
    (d := some) (g := id) (self := Lab.rdC) (good := Lab.mvC) (bad := Lab.no) rfl (by decide)
    id (fun _ => rfl) (encodeNat c) rest v
    (ist ws vs (delimit (encodeNat c) ++ rest) tv u w [] [] [] p [] noSum)
    (by simp [ist, Decode.st, CapsTarget.st])
  have hS₁ : S₁ = ist ws vs rest tv u w [] [] (encodeNat c).reverse p [] noSum := by
    funext k
    cases k with
    | dec j =>
      by_cases hj : j = .caps .left
      · subst hj
        simpa [ist, Decode.st, CapsTarget.st] using ha₁
      · rw [hk₁ _ (by simpa using hj) (by simp)]
        exact decode_st_ne_caps hj _ _ _ _ _ _ _
    | Z => simpa [ist] using hb₁
    | _ => exact hk₁ _ (by simp) (by simp)
  rw [hS₁] at h₁
  obtain ⟨v₂, S₂, h₂, ha₂, hb₂, hk₂⟩ := moveB_run (M := prog) (a := K.Z) (b := K.Q)
    (d := some) (g := id) (self := Lab.mvC) (next := Lab.cmp false false) rfl (by decide)
    (encodeNat c).reverse (encodeNat c).reverse [] false
    (ist ws vs rest tv u w [] [] (encodeNat c).reverse p [] noSum)
    (by simp [ist]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hS₂ : S₂ = ist ws vs rest tv u w [] [] [] p (encodeNat c) noSum := by
    funext k
    cases k with
    | Z => exact ha₂
    | Q => simpa [ist] using hb₂
    | _ => exact hk₂ _ (by simp) (by simp)
  rw [hS₂] at h₂
  exact ⟨v₂, (h₁.trans h₂).of_eq (by simp; omega)⟩

private theorem copyV_run (u w p q : List Bool) (sm : ∀ _ : SSVerify.K, List Sym)
    (hX : sm .X = []) (v : Bool) :
    Run prog (2 * vs.length + 2)
      ⟨some .sv1, v, ist ws vs cs tv u w [] [] [] p q sm⟩
      ⟨some (.sum true .next), false, ist ws vs cs tv u w [] [] [] p q
        (update sm .X (vs.map Sym.bit))⟩ := by
  obtain ⟨S', h, ha, ht, hb, hk⟩ := copyB_run (M := prog) (a := VS) (b := K.sum .X)
    (t := K.Z) (da := some) (dt := some) (ga := id) (gb := Sym.bit) (gt := id)
    (first := .sv1) (second := .sv2) (next := .sum true .next) rfl rfl (by decide)
    (by decide) (by decide) (fun _ => rfl) (fun _ => rfl) vs [] v
    (ist ws vs cs tv u w [] [] [] p q sm) (by simp [ist, Decode.st, ListNatPair.st])
    (by simp [EndsBitBlock]) (by simp [ist, EndsBitBlock])
  have hS : S' = ist ws vs cs tv u w [] [] [] p q (update sm .X (vs.map Sym.bit)) := by
    funext k
    cases k with
    | dec j =>
      by_cases hj : j = .items (.output true)
      · subst hj
        exact ha
      · rw [hk _ (by simpa using hj) (by simp) (by simp)]
        rfl
    | sum j =>
      by_cases hj : j = .X
      · subst hj
        simpa [ist, hX] using hb
      · rw [hk _ (by simp) (by simpa using hj) (by simp)]
        simp [ist, hj]
    | Z => exact ht
    | _ => exact hk _ (by simp) (by simp) (by simp)
  rw [hS] at h
  exact h

end Pass

/-! ### The knapsack loop -/

theorem bitEncode_list_nat (l : List ℕ) :
    bitEncode l = l.flatMap fun a => delimit (encodeNat a) := by
  change ((l.map encodeNat).map delimit).flatten = _
  simp [List.flatMap_def, Function.comp_def]

theorem length_bitEncode_le_of_sublist {l l' : List ℕ} (h : l.Sublist l') :
    (bitEncode l).length ≤ (bitEncode l').length := by
  rw [bitEncode_list_nat, bitEncode_list_nat]
  induction h with
  | slnil => exact le_rfl
  | cons a _ ih =>
    simp only [List.flatMap_cons, List.length_append]
    omega
  | cons_cons a _ ih =>
    simp only [List.flatMap_cons, List.length_append]
    omega

theorem length_encodeNat_pick_le (as : List ℕ) (w : List Bool) :
    (encodeNat (SSVerify.pick as w).sum).length ≤ (bitEncode as).length :=
  (Partition.sum_encoding_length_le _).trans
    (length_bitEncode_le_of_sublist (SSVerify.pick_sublist as w))

theorem length_le_bitEncode (as : List ℕ) : as.length ≤ (bitEncode as).length := by
  rw [bitEncode_list_nat]
  exact SSVerify.length_le_flatMap as

theorem length_maskTake : ∀ (u w : List Bool), (maskTake u w).length = u.length
  | [], _ => rfl
  | _ :: us, w => by simp [maskTake, length_maskTake us w.tail]

theorem length_orStep : ∀ (u w : List Bool), (orStep u w).length = u.length
  | [], _ => rfl
  | _ :: us, w => by simp [orStep, length_orStep us w.tail]

private theorem sum_st_eq (as : List ℕ) (mask : List Bool) :
    update (update noSum .W (mask.map Sym.bit)) .X ((bitEncode as).map Sym.bit) =
      SSVerify.st ((as.flatMap fun a => delimit (encodeNat a)).map Sym.bit)
        (mask.map Sym.bit) [] [] [] := by
  rw [bitEncode_list_nat]
  funext j
  cases j <;> rfl

/-- **One knapsack pass.** From the loop head with a nonempty capacity list, the machine reads
the next mask, sums the selected weights and compares the sum with the capacity, reaching the
loop head again when the sum fits and the rejecting label otherwise. -/
theorem iter_run (ws vs : List ℕ) (V c : ℕ) (caps : List ℕ) (u w : List Bool) (v : Bool)
    (N : ℕ) (hu : u.length = ws.length) (hN₁ : (bitEncode ws).length ≤ N)
    (hN₂ : (bitEncode (c :: caps)).length ≤ N) :
    ∃ v', RunLe prog (20 * (N + 1) ^ 2)
      ⟨some .knap, v, ist (bitEncode ws) (bitEncode vs) (bitEncode (c :: caps)) (encodeNat V)
        u w [] [] [] [] [] noSum⟩
      ⟨some (if (SSVerify.pick ws (maskTake u w)).sum ≤ c then .knap else .no), v',
        ist (bitEncode ws) (bitEncode vs) (bitEncode caps) (encodeNat V) (orStep u w)
          (w.drop u.length) [] [] [] [] [] noSum⟩ := by
  set WSb := bitEncode ws with hWSb
  set VSb := bitEncode vs
  set TVb := encodeNat V
  have hCS : bitEncode (c :: caps) = delimit (encodeNat c) ++ bitEncode caps := by
    rw [bitEncode_list_nat, bitEncode_list_nat, List.flatMap_cons]
  set M := maskTake u w with hM
  set s := (SSVerify.pick ws M).sum with hs
  obtain ⟨v₁, h₁⟩ := knap_orp_run WSb VSb TVb (bitEncode (c :: caps))
    (by rw [hCS]; exact List.append_ne_nil_of_left_ne_nil (SSVerify.delimit_ne_nil _) _) u w v
  obtain ⟨v₂, h₂⟩ := rev_run WSb VSb (bitEncode (c :: caps)) TVb (orStep u w) M
    (w.drop u.length) v₁
  have h₃ := copyW_run WSb VSb (bitEncode (c :: caps)) TVb (orStep u w) (w.drop u.length)
    (update noSum .W (M.map Sym.bit)) (by simp) v₂
  rw [sum_st_eq ws M] at h₃
  obtain ⟨v₄, h₄⟩ := sum_clean_run WSb VSb (bitEncode (c :: caps)) TVb false ws M (orStep u w)
    (w.drop u.length) [] [] false
  obtain ⟨v₅, h₅⟩ := mvB_false_run WSb VSb (bitEncode (c :: caps)) TVb (encodeNat s)
    (orStep u w) (w.drop u.length) v₄
  rw [hCS] at h₁ h₂ h₃ h₄ h₅
  obtain ⟨v₆, h₆⟩ := cap_run WSb VSb TVb c (bitEncode caps) (orStep u w) (w.drop u.length)
    (encodeNat s) v₅
  obtain ⟨v₇, h₇⟩ := cmp_run WSb VSb (bitEncode caps) TVb (orStep u w) (w.drop u.length) false
    (encodeNat s) (encodeNat c) false v₆
  have hlabel : (if gtB false (encodeNat s) (encodeNat c) = true then Lab.no
      else if false = true then Lab.yes else Lab.knap) =
      if s ≤ c then Lab.knap else Lab.no := by
    rw [gtB_encodeNat]
    by_cases hsc : s ≤ c
    · rw [ite_eq_right (by split <;> simp_all), ite_eq_left hsc]
      rfl
    · rw [ite_eq_left (by split <;> simp_all), ite_eq_right hsc]
  rw [hlabel] at h₇
  refine ⟨v₇, ((((((h₁.le le_rfl).trans (h₂.le le_rfl)).trans (h₃.le le_rfl)).trans
    h₄).trans (h₅.le le_rfl)).trans (h₆.le le_rfl) |>.trans (h₇.le le_rfl)).mono ?_⟩
  have hk : u.length ≤ N := hu ▸ (length_le_bitEncode ws).trans hN₁
  have hsN : (encodeNat s).length ≤ N := (length_encodeNat_pick_le ws M).trans hN₁
  have hcN : 2 * (encodeNat c).length + 1 ≤ N := by
    have := hN₂
    rw [hCS, List.length_append, length_delimit] at this
    omega
  have hn : (ws.flatMap fun a => delimit (encodeNat a)).length ≤ N := by
    rw [← bitEncode_list_nat]
    exact hN₁
  have hmax : max (encodeNat s).length (encodeNat c).length ≤ N := max_le hsN (by omega)
  simp only [length_orStep, length_maskTake, hM]
  have hWSbN : WSb.length ≤ N := hN₁
  nlinarith [hn, hk, hsN, hcN, hmax, hWSbN]

theorem decode_st_ne_right {j : Decode.K} (hj : j ≠ .caps .right)
    (a b ws vs cs tv tv' : List Bool) :
    Decode.st a b ws vs cs tv j = Decode.st a b ws vs cs tv' j := by
  rcases j with j | ((_ | _ | _) | _ | _ | (_ | _ | _) | _ | _) <;>
    first | rfl | exact absurd rfl hj

private theorem tv_run (ws vs q : List Bool) (V : ℕ) (w : List Bool) (v : Bool) :
    ∃ v', Run prog (2 * (encodeNat V).length + 2)
      ⟨some .tv1, v, ist ws vs [] (encodeNat V) [] w [] [] [] [] q noSum⟩
      ⟨some (.cmp true false), v', ist ws vs [] [] [] w [] [] [] (encodeNat V) q noSum⟩ := by
  obtain ⟨v₁, S₁, h₁, ha₁, hb₁, hk₁⟩ := moveB_run (M := prog) (a := TV) (b := K.Z)
    (d := some) (g := id) (self := Lab.tv1) (next := Lab.tv2) rfl (by decide)
    (encodeNat V) (encodeNat V) [] v (ist ws vs [] (encodeNat V) [] w [] [] [] [] q noSum)
    (by simp [ist, Decode.st, CapsTarget.st]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hS₁ : S₁ = ist ws vs [] [] [] w [] [] (encodeNat V).reverse [] q noSum := by
    funext k
    cases k with
    | dec j =>
      by_cases hj : j = .caps .right
      · subst hj
        simpa [ist, Decode.st, CapsTarget.st] using ha₁
      · rw [hk₁ _ (by simpa using hj) (by simp)]
        exact decode_st_ne_right hj _ _ _ _ _ _ _
    | Z => simpa [ist] using hb₁
    | _ => exact hk₁ _ (by simp) (by simp)
  rw [hS₁] at h₁
  obtain ⟨v₂, S₂, h₂, ha₂, hb₂, hk₂⟩ := moveB_run (M := prog) (a := K.Z) (b := K.P)
    (d := some) (g := id) (self := Lab.tv2) (next := Lab.cmp true false) rfl (by decide)
    (encodeNat V).reverse (encodeNat V).reverse [] v₁
    (ist ws vs [] [] [] w [] [] (encodeNat V).reverse [] q noSum)
    (by simp [ist]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hS₂ : S₂ = ist ws vs [] [] [] w [] [] [] (encodeNat V) q noSum := by
    funext k
    cases k with
    | Z => exact ha₂
    | P => simpa [ist] using hb₂
    | _ => exact hk₂ _ (by simp) (by simp)
  rw [hS₂] at h₂
  exact ⟨v₂, (h₁.trans h₂).of_eq (by simp; omega)⟩

private theorem fu_run (ws vs tv u w : List Bool) (v : Bool) :
    ∃ v', Run prog (2 * u.length + 3)
      ⟨some .knap, v, ist ws vs [] tv u w [] [] [] [] [] noSum⟩
      ⟨some .sv1, v', ist ws vs [] tv [] w [] [] [] [] []
        (update noSum .W ((u.map not).map Sym.bit))⟩ := by
  have h₁ : Run prog 1 ⟨some .knap, v, ist ws vs [] tv u w [] [] [] [] [] noSum⟩
      ⟨some .fu1, false, ist ws vs [] tv u w [] [] [] [] [] noSum⟩ :=
    Run.single (by simp [prog, TM2.stepAux, ist, Decode.st, CapsTarget.st])
  obtain ⟨v₂, S₂, h₂, ha₂, hb₂, hk₂⟩ := moveB_run (M := prog) (a := K.U) (b := K.Z)
    (d := some) (g := id) (self := Lab.fu1) (next := Lab.fu2) rfl (by decide)
    u u [] false (ist ws vs [] tv u w [] [] [] [] [] noSum)
    (by simp [ist]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hS₂ : S₂ = ist ws vs [] tv [] w [] [] u.reverse [] [] noSum := by
    funext k
    cases k with
    | U => exact ha₂
    | Z => simpa [ist] using hb₂
    | _ => exact hk₂ _ (by simp) (by simp)
  rw [hS₂] at h₂
  obtain ⟨v₃, S₃, h₃, ha₃, hb₃, hk₃⟩ := moveB_run (M := prog) (a := K.Z) (b := K.sum .W)
    (d := some) (g := fun b => Sym.bit (!b)) (self := Lab.fu2) (next := Lab.sv1) rfl (by decide)
    u.reverse u.reverse [] v₂ (ist ws vs [] tv [] w [] [] u.reverse [] [] noSum)
    (by simp [ist]) (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  have hS₃ : S₃ = ist ws vs [] tv [] w [] [] [] [] []
      (update noSum .W ((u.map not).map Sym.bit)) := by
    funext k
    cases k with
    | Z => exact ha₃
    | sum j =>
      by_cases hj : j = .W
      · subst hj
        simpa [ist, List.map_reverse, List.map_map, Function.comp_def] using hb₃
      · rw [hk₃ _ (by simp) (by simpa using hj)]
        simp [ist, hj]
    | _ => exact hk₃ _ (by simp) (by simp)
  rw [hS₃] at h₃
  exact ⟨v₃, ((h₁.trans h₂).trans h₃).of_eq (by simp; omega)⟩

/-- **The value check.** From the loop head with no capacity left, the machine sums the values
of the used items and compares the sum with the target. -/
theorem fin_run (ws vs : List ℕ) (V : ℕ) (u w : List Bool) (v : Bool) (N : ℕ)
    (hu : u.length = vs.length) (hN₁ : (bitEncode vs).length ≤ N)
    (hN₂ : (encodeNat V).length ≤ N) :
    ∃ v' S', RunLe prog (20 * (N + 1) ^ 2)
      ⟨some .knap, v, ist (bitEncode ws) (bitEncode vs) (bitEncode ([] : List ℕ)) (encodeNat V)
        u w [] [] [] [] [] noSum⟩
      ⟨some (if V ≤ (SSVerify.pick vs (u.map not)).sum then .yes else .no), v', S'⟩ := by
  set WSb := bitEncode ws
  set VSb := bitEncode vs
  set TVb := encodeNat V
  set s := (SSVerify.pick vs (u.map not)).sum with hs
  obtain ⟨v₁, h₁⟩ := fu_run WSb VSb TVb u w v
  have h₂ := copyV_run WSb VSb [] TVb [] w [] []
    (update noSum .W ((u.map not).map Sym.bit)) (by simp) v₁
  rw [sum_st_eq vs (u.map not)] at h₂
  obtain ⟨v₃, h₃⟩ := sum_clean_run WSb VSb [] TVb true vs (u.map not) [] w [] [] false
  obtain ⟨v₄, h₄⟩ := mvB_true_run WSb VSb [] TVb (encodeNat s) [] w v₃
  obtain ⟨v₅, h₅⟩ := tv_run WSb VSb (encodeNat s) V w v₄
  obtain ⟨v₆, h₆⟩ := cmp_run WSb VSb [] [] [] w true (encodeNat V) (encodeNat s) false v₅
  have hlabel : (if gtB false (encodeNat V) (encodeNat s) = true then Lab.no
      else if true = true then Lab.yes else Lab.knap) =
      if V ≤ s then Lab.yes else Lab.no := by
    rw [gtB_encodeNat]
    by_cases hVs : V ≤ s
    · rw [ite_eq_right (by split <;> simp_all), ite_eq_left hVs]
      rfl
    · rw [ite_eq_left (by split <;> simp_all), ite_eq_right hVs]
  rw [hlabel] at h₆
  refine ⟨v₆, _, (((((h₁.le le_rfl).trans (h₂.le le_rfl)).trans h₃).trans
    (h₄.le le_rfl)).trans (h₅.le le_rfl) |>.trans (h₆.le le_rfl)).mono ?_⟩
  have hk : u.length ≤ N := hu ▸ (length_le_bitEncode vs).trans hN₁
  have hsN : (encodeNat s).length ≤ N := (length_encodeNat_pick_le vs _).trans hN₁
  have hn : (vs.flatMap fun a => delimit (encodeNat a)).length ≤ N := by
    rw [← bitEncode_list_nat]
    exact hN₁
  have hmax : max (encodeNat V).length (encodeNat s).length ≤ N := max_le hN₂ hsN
  have hVSbN : VSb.length ≤ N := hN₁
  simp only [List.length_map]
  nlinarith [hn, hk, hsN, hmax, hVSbN, hN₂]

/-- **The knapsack loop.** From the loop head, the machine reaches the accepting label exactly
when the knapsack loop of the certificate check accepts, within a cubic number of steps. -/
theorem loop_run (ws vs : List ℕ) (V N : ℕ) (hvs : vs.length = ws.length)
    (hN₁ : (bitEncode ws).length ≤ N) (hN₂ : (bitEncode vs).length ≤ N)
    (hN₃ : (encodeNat V).length ≤ N) :
    ∀ (caps : List ℕ) (u w : List Bool) (v : Bool), u.length = ws.length →
      (bitEncode caps).length ≤ N →
      ∃ v' S', RunLe prog ((caps.length + 1) * (20 * (N + 1) ^ 2))
        ⟨some .knap, v, ist (bitEncode ws) (bitEncode vs) (bitEncode caps) (encodeNat V)
          u w [] [] [] [] [] noSum⟩
        ⟨some (if loopCheck ws vs V caps w u then .yes else .no), v', S'⟩ := by
  intro caps
  induction caps with
  | nil =>
    intro u w v hu _
    obtain ⟨v', S', h⟩ := fin_run ws vs V u w v N (by rw [hu, hvs]) hN₂ hN₃
    refine ⟨v', S', ?_⟩
    simpa [loopCheck] using h
  | cons c caps ih =>
    intro u w v hu hc
    obtain ⟨v₁, h₁⟩ := iter_run ws vs V c caps u w v N hu hN₁ hc
    have hc' : (bitEncode caps).length ≤ N := by
      refine le_trans ?_ hc
      rw [bitEncode_list_nat, bitEncode_list_nat, List.flatMap_cons, List.length_append]
      omega
    by_cases hok : (SSVerify.pick ws (maskTake u w)).sum ≤ c
    · rw [ite_eq_left hok] at h₁
      obtain ⟨v₂, S₂, h₂⟩ := ih (orStep u w) (w.drop u.length) v₁
        (by rw [length_orStep, hu]) hc'
      have hl : loopCheck ws vs V (c :: caps) w u =
          loopCheck ws vs V caps (w.drop u.length) (orStep u w) := by
        simp [loopCheck, hok]
      rw [hl]
      refine ⟨v₂, S₂, (h₁.trans h₂).mono ?_⟩
      simp only [List.length_cons]
      nlinarith
    · rw [ite_eq_right hok] at h₁
      have hl : loopCheck ws vs V (c :: caps) w u = false := by
        simp [loopCheck, hok]
      rw [hl]
      refine ⟨v₁, _, h₁.mono ?_⟩
      simp only [List.length_cons]
      nlinarith

/-! ### Decoding and initialization -/

theorem embeds_dec : Embeds decEmb decLabel Decode.prog prog := by
  intro l
  cases l with
  | split l | items l | caps l => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

theorem embeds_cnt : Embeds cntEmb cntLabel
    Cslib.Complexity.PolynomialEncoding.ListCount.prog prog := by
  intro l
  cases l with
  | loop | block | bump | clear => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

/-- The start configuration of the verifier: the instance on the decoder's input stack and the
certificate on `W`. -/
def startStk (x w : List Bool) : ∀ k, List (Γ k) :=
  update (update (fun _ => []) (K.dec (.caps (.pair .input))) x) K.W w

private theorem copyC_run (ws vs cs tv w : List Bool) (v : Bool) :
    Run prog (2 * ws.length + 2)
      ⟨some .cw1, v, ist ws vs cs tv [] w [] [] [] [] [] noSum⟩
      ⟨some (.cnt .loop), false, update (ist ws vs cs tv [] w [] [] [] [] [] noSum) .cin ws⟩ := by
  obtain ⟨S', h, ha, ht, hb, hk⟩ := copyB_run (M := prog) (a := WS) (b := K.cin)
    (t := K.Z) (da := some) (dt := some) (ga := id) (gb := id) (gt := id)
    (first := .cw1) (second := .cw2) (next := .cnt .loop) rfl rfl (by decide)
    (by decide) (by decide) (fun _ => rfl) (fun _ => rfl) ws [] v
    (ist ws vs cs tv [] w [] [] [] [] [] noSum) (by simp [ist, Decode.st, ListNatPair.st])
    (by simp [EndsBitBlock]) (by simp [ist, EndsBitBlock])
  have hS : S' = update (ist ws vs cs tv [] w [] [] [] [] [] noSum) .cin ws := by
    funext k
    cases k with
    | dec j =>
      by_cases hj : j = .items (.output false)
      · subst hj
        exact ha
      · rw [hk _ (by simpa using hj) (by simp) (by simp)]
        simp [ist]
    | cin => simpa [ist] using hb
    | Z => simpa [ist] using ht
    | _ => rw [hk _ (by simp) (by simp) (by simp)]; simp [ist]
  rw [hS] at h
  exact h

/-- **Start of the verifier.** An undecodable instance is rejected; otherwise the machine reaches
the loop head with the decoded instance and every item unused. -/
theorem start_run (x w : List Bool) :
    ∃ v S, RunLe prog (40 * x.length + 16)
      ⟨some (.dec (.split .read)), false, startStk x w⟩
      ⟨some (if (bitDecode (α := MultipleKnapsackInstance) x).isSome then .knap else .no),
        v, S⟩ ∧
      ∀ (items : List (ℕ × ℕ)) (cs : List ℕ) (t : ℕ),
        bitDecode (α := MultipleKnapsackInstance) x = some (items, cs, t) →
        S = ist (bitEncode (items.map Prod.fst)) (bitEncode (items.map Prod.snd)) (bitEncode cs)
          (encodeNat t) (List.replicate items.length true) w [] [] [] [] [] noSum := by
  obtain ⟨v₁, T₁, h₁, hF₁, hA₁⟩ := Decode.run_embedded decEmb decLabel embeds_dec x false
    (startStk x w) (by
      intro k
      refine Eq.trans ?_ (List.map_id _).symm
      rcases k with (_ | _ | _ | ((_ | _ | _) | _ | _ | _)) |
        ((_ | _ | _) | _ | _ | (_ | _ | _) | _ | _) <;>
        simp [startStk, Decode.st, CapsTarget.st, ListNatPair.st, NatPair.st, decEmb])
  cases hd : bitDecode (α := MultipleKnapsackInstance) x with
  | none =>
    simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
    refine ⟨v₁, T₁, h₁.mono (by omega), ?_⟩
    intro items cs t h
    simp at h
  | some i =>
    obtain ⟨items, cs, t⟩ := i
    simp only [hd, Option.isSome_some, ↓reduceIte] at h₁ ⊢
    set WSb := bitEncode (items.map Prod.fst)
    have hT₁ : T₁ = ist WSb (bitEncode (items.map Prod.snd)) (bitEncode cs) (encodeNat t)
        [] w [] [] [] [] [] noSum := by
      funext k
      cases k with
      | dec j => exact ((hA₁ items cs t hd) j).trans (List.map_id _)
      | _ =>
        rw [hF₁ _ (by intro j; simp [decEmb])]
        simp [startStk, ist]
    rw [hT₁] at h₁
    have h₂ := copyC_run WSb (bitEncode (items.map Prod.snd)) (bitEncode cs) (encodeNat t) w
      v₁
    obtain ⟨v₃, T₃, h₃, hF₃, hA₃⟩ := Cslib.Complexity.PolynomialEncoding.ListCount.run_embedded
      cntEmb cntLabel embeds_cnt WSb false
      (update (ist WSb (bitEncode (items.map Prod.snd)) (bitEncode cs) (encodeNat t)
        [] w [] [] [] [] [] noSum) .cin WSb) (by
        intro k
        cases k <;> refine Eq.trans ?_ (List.map_id _).symm <;>
          simp [cntEmb, ist, Cslib.Complexity.PolynomialEncoding.ListCount.st])
    have hws : bitDecode (α := List ℕ) WSb = some (items.map Prod.fst) := bitDecode_bitEncode _
    simp only [hws, Option.isSome_some, ↓reduceIte] at h₃
    refine ⟨v₃, T₃, ((h₁.trans (h₂.le le_rfl)).trans h₃).mono ?_, ?_⟩
    · have := Decode.output_length_le hd
      have : WSb.length = (bitEncode (items.map Prod.fst)).length := rfl
      omega
    · intro items' cs' t' h'
      obtain ⟨rfl, h₂'⟩ := Prod.mk.inj (Option.some.inj h')
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂'
      have hA := hA₃ (items.map Prod.fst) hws
      funext k
      cases k with
      | cin => exact (hA .input).trans (List.map_id _)
      | cscr => exact (hA .scratch).trans (List.map_id _)
      | U => exact (hA .count).trans (by rw [List.length_map]; exact List.map_id _)
      | _ =>
        rw [hF₃ _ (by intro j; cases j <;> simp [cntEmb])]
        rfl

/-! ### The verifier is polynomial-time -/

/-- **The verifier decides the certificate check in cubic time.** -/
theorem run (x w : List Bool) :
    ∃ v S, RunLe prog (200 * (x.length + 1) ^ 3)
      ⟨some (.dec (.split .read)), false, startStk x w⟩
      ⟨some (if mkCheck x w then .yes else .no), v, S⟩ := by
  obtain ⟨v₁, S₁, h₁, hS₁⟩ := start_run x w
  cases hd : bitDecode (α := MultipleKnapsackInstance) x with
  | none =>
    simp only [hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h₁
    have hm : mkCheck x w = false := by simp [mkCheck, hd]
    rw [hm]
    have h4 : x.length + 1 ≤ (x.length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    exact ⟨v₁, S₁, h₁.mono (by omega)⟩
  | some i =>
    obtain ⟨items, cs, t⟩ := i
    simp only [hd, Option.isSome_some, ↓reduceIte] at h₁
    rw [hS₁ items cs t hd] at h₁
    have hlen := Decode.output_length_le hd
    set N := 2 * x.length
    obtain ⟨v₂, S₂, h₂⟩ := loop_run (items.map Prod.fst) (items.map Prod.snd) t N (by simp)
      (by omega) (by omega) (by omega) cs (List.replicate items.length true) w v₁ (by simp)
      (by omega)
    have hm : mkCheck x w = loopCheck (items.map Prod.fst) (items.map Prod.snd) t cs w
        (List.replicate items.length true) := by
      simp [mkCheck, hd]
    rw [hm]
    have hcs : cs.length ≤ N := (length_le_bitEncode cs).trans (by omega)
    refine ⟨v₂, S₂, (h₁.trans h₂).mono ?_⟩
    have h3 : (cs.length + 1) * (20 * (N + 1) ^ 2) ≤ 160 * (x.length + 1) ^ 3 := by
      have hN : N + 1 ≤ 2 * (x.length + 1) := by omega
      have hc : cs.length + 1 ≤ 2 * (x.length + 1) := by omega
      calc (cs.length + 1) * (20 * (N + 1) ^ 2)
          ≤ (2 * (x.length + 1)) * (20 * (2 * (x.length + 1)) ^ 2) := by
            apply Nat.mul_le_mul hc
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_left hN 2
        _ = 160 * (x.length + 1) ^ 3 := by ring
    have h4 : x.length + 1 ≤ (x.length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega

noncomputable instance : Fintype Lab := Fintype.ofList
  ([.cw1, .cw2, .knap, .orp, .revU, .revM, .sw1, .sw2, .rdC, .mvC, .fu1, .fu2, .sv1, .sv2,
    .tv1, .tv2, .yes, .no, .clw false, .clw true, .mvB false, .mvB true,
    .cmp false false, .cmp false true, .cmp true false, .cmp true true] ++
    (Finset.univ : Finset (Bool × Bool × Bool)).toList.map
      (fun p => Lab.cmpA p.1 p.2.1 p.2.2) ++
    Finset.univ.toList.map Lab.dec ++ Finset.univ.toList.map Lab.cnt ++
    (Finset.univ : Finset (Bool × SSVerify.Lab)).toList.map (fun p => Lab.sum p.1 p.2))
  (by
    intro l
    cases l with
    | clw f | mvB f => cases f <;> simp
    | cmp f g => cases f <;> cases g <;> simp
    | _ => simp)

/-- **The verifier as a host component.** -/
noncomputable abbrev comp : Cslib.Complexity.Host.Comp where
  K := K
  Γ := Γ
  finΓ k := by cases k <;> infer_instance
  L := Lab
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks k := by simp

end MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack.Verify

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack.Verify

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding

/-- **The MULTIPLE KNAPSACK certificate check is polynomial-time.** The map sending a pair of bit
strings $(x, w)$ to the certificate check, which decodes $x$ as a multiple-knapsack instance with
$k$ items and $m$ knapsacks and reads $w$ as $m$ masks of $k$ bits (missing bits count as false,
and the bits of $w$ after the first $mk$ are ignored), is computable in polynomial time for the
canonical bitstring encodings, within a cubic number of steps of a multi-stack Turing machine.

Source: original to this formalization. -/
theorem isPolyTime_mkCheck :
    ComplexityTheory.IsPolyTime fun q : List Bool × List Bool => mkCheck q.1 q.2 :=
  Cslib.Complexity.Host.isPolyTime_verifier (c := comp) (cX := K.dec (.caps (.pair .input)))
    (cW := K.W) (gX := id) (gW := id) (start := .dec (.split .read)) (yes := .yes) (no := .no)
    mkCheck (Polynomial.C 200 * (Polynomial.X + 1) ^ 3) (by decide) (by decide) rfl rfl
    fun x w => by
      obtain ⟨v, S, h⟩ := run x w
      have hst : (update (update (fun _ => []) (K.dec (.caps (.pair .input))) (x.map id)) K.W
          (w.map id) : ∀ k, List (Γ k)) = startStk x w := by
        simp only [List.map_id]
        rfl
      refine ⟨v, S, ?_⟩
      rw [hst]
      refine h.mono ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

end MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack.Verify

end
