/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNatPair
import CSLibExt.Computability.CookLevin

/-!
# Four canonical outputs from a Nat-pair list and a Nat pair

The fixed carrier is `List (Nat × Nat) × (Nat × Nat)`, used by KNAPSACK.
Existing finite components split the raw outer pair, project its item list,
and normalize the final pair. Final Nat payloads use the total canonical
codec's decoder, without a separate trailing-bit or exhaustion check.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.ListNatPairPair

open Turing Function MetaMathlibExt.BitstringEncoding
open MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding

/-- Two disjoint existing workspaces; the pair buffer also serves the
initial outer-frame split and is cleared before normalization starts. -/
inductive K | items (k : ListNatPair.K) | pair (k : NatPair.K)
  deriving DecidableEq

instance : Fintype K where
  elems := Finset.univ.image K.items ∪ Finset.univ.image K.pair
  complete k := by cases k <;> simp

/-- The existing split, list projector, and final pair normalizer. -/
inductive Lab | split (l : PairSplit.Lab) | items (l : ListNatPair.Lab)
  | pair (l : NatPair.Lab) | good | bad
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.good, .bad} ∪ Finset.univ.image Lab.split ∪
    Finset.univ.image Lab.items ∪ Finset.univ.image Lab.pair
  complete l := by cases l <;> simp

/-- The outer splitter reuses the final pair's input and empty buffer. -/
def splitEmb : SEmb (fun _ : PairSplit.K => Bool) (fun _ : K => Bool) where
  e
    | .input => .pair (.pair .input)
    | .left => .items .input
    | .scratch => .pair .buffer
  inj a b h := by cases a <;> cases b <;> simp_all
  ι _ := Equiv.refl Bool

/-- The list projector has its own disjoint workspace. -/
def itemsEmb : SEmb (fun _ : ListNatPair.K => Bool) (fun _ : K => Bool) where
  e := K.items
  inj _ _ h := K.items.inj h
  ι _ := Equiv.refl Bool

/-- The final pair projector has its own disjoint workspace. -/
def pairEmb : SEmb (fun _ : NatPair.K => Bool) (fun _ : K => Bool) where
  e := K.pair
  inj _ _ h := K.pair.inj h
  ι _ := Equiv.refl Bool

/-- Successful outer framing enters the item-list projector. -/
def splitLabel : PairSplit.Lab → Lab
  | .good => .items .loop
  | .bad => .bad
  | l => .split l

/-- Successful item projection enters the final pair decoder. -/
def itemsLabel : ListNatPair.Lab → Lab
  | .good => .pair (.pair .read)
  | .bad => .bad
  | l => .items l

/-- The final pair's actual halts are the whole decoder's outcomes. -/
def pairLabel : NatPair.Lab → Lab
  | .good => .good
  | .bad => .bad
  | l => .pair l

/-- The whole finite program is a composition of existing components. -/
def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .split l => mapS splitEmb splitLabel (PairSplit.prog l)
  | .items l => mapS itemsEmb itemsLabel (ListNatPair.prog l)
  | .pair l => mapS pairEmb pairLabel (NatPair.prog l)
  | .good | .bad => .halt

/-- Exact raw-field and four-output invariant, with empty private scratch.
At entry the item field is empty and the entire raw input is `pairRaw`. -/
def st (itemsRaw pairRaw weights values capacity threshold : List Bool) :
    K → List Bool
  | .items k => ListNatPair.st itemsRaw [] [] weights values
      (NatPair.st [] [] [] [] [] []) k
  | .pair k => NatPair.st pairRaw [] [] [] capacity threshold k

private theorem embeds_split :
    Embeds splitEmb splitLabel PairSplit.prog prog := by
  intro l
  cases l with
  | read | copy => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem embeds_items :
    Embeds itemsEmb itemsLabel ListNatPair.prog prog := by
  intro l
  cases l with
  | loop | block | back | pair l | emit b | finish b => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem embeds_pair :
    Embeds pairEmb pairLabel NatPair.prog prog := by
  intro l
  cases l with
  | pair l | norm b l => exact Or.inl rfl
  | good | bad => exact Or.inr rfl

private theorem split_run (p r weights values capacity threshold : List Bool)
    (v : Bool) :
    ∃ w, Run prog (2 * p.length + 2)
      ⟨some (.split .read), v,
        st [] (delimit p ++ r) weights values capacity threshold⟩
      ⟨some (.items .loop), w, st p r weights values capacity threshold⟩ := by
  obtain ⟨w, hr⟩ := PairSplit.run_delimit p r [] v
  obtain ⟨T, ht, ha, hf⟩ := run_embed splitLabel embeds_split
    _ _ _ _ _ _ _ (st [] (delimit p ++ r) weights values capacity threshold)
    hr (by intro k; cases k <;>
      simp [splitEmb, st, ListNatPair.st, NatPair.st, PairSplit.st])
  have he : T = st p r weights values capacity threshold := by
    funext k
    cases k with
    | items k =>
      cases k with
      | input =>
        simpa [splitEmb, st, ListNatPair.st, PairSplit.st] using ha .left
      | acc b | output b | pair k =>
        exact hf _ (by intro j; cases j <;> simp [splitEmb])
    | pair k =>
      cases k with
      | pair k =>
        cases k with
        | input =>
          simpa [splitEmb, st, NatPair.st, PairSplit.st] using ha .input
        | left | scratch =>
          exact hf _ (by intro j; cases j <;> simp [splitEmb])
      | buffer =>
        simpa [splitEmb, st, NatPair.st, PairSplit.st] using ha .scratch
      | left | right =>
        exact hf _ (by intro j; cases j <;> simp [splitEmb])
  exact ⟨w, he ▸ ht⟩

private theorem items_run {p : List Bool} {as : List (Nat × Nat)}
    (h : bitDecode p = some as)
    (r weights values capacity threshold : List Bool) (v : Bool) :
    ∃ w, RunLe prog (16 * p.length + 3)
      ⟨some (.items .loop), v, st p r weights values capacity threshold⟩
      ⟨some (.pair (.pair .read)), w,
        st [] r (bitEncode (as.map Prod.fst) ++ weights)
          (bitEncode (as.map Prod.snd) ++ values) capacity threshold⟩ := by
  obtain ⟨w, hr⟩ := ListNatPair.run_some h weights values v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed itemsLabel embeds_items hr
    (S' := st p r weights values capacity threshold)
    (by intro k; simp [itemsEmb, st])
  have he : T = st [] r (bitEncode (as.map Prod.fst) ++ weights)
      (bitEncode (as.map Prod.snd) ++ values) capacity threshold := by
    funext k
    cases k with
    | items k => simpa [itemsEmb, st] using ha k
    | pair k => exact hf _ (by intro j; simp [itemsEmb])
  exact ⟨w, he ▸ ht⟩

private theorem pair_run {r : List Bool} {c t : Nat}
    (h : bitDecode r = some (c, t))
    (weights values capacity threshold : List Bool) (v : Bool) :
    ∃ w, RunLe prog (2 * r.length + 6)
      ⟨some (.pair (.pair .read)), v,
        st [] r weights values capacity threshold⟩
      ⟨some .good, w, st [] [] weights values
        (Computability.encodeNat c ++ capacity)
        (Computability.encodeNat t ++ threshold)⟩ := by
  obtain ⟨w, hr⟩ := NatPair.run_some h capacity threshold v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed pairLabel embeds_pair hr
    (S' := st [] r weights values capacity threshold)
    (by intro k; simp [pairEmb, st])
  have he : T = st [] [] weights values
      (Computability.encodeNat c ++ capacity)
      (Computability.encodeNat t ++ threshold) := by
    funext k
    cases k with
    | items k => exact hf _ (by intro j; simp [pairEmb])
    | pair k => simpa [pairEmb, st] using ha k
  exact ⟨w, he ▸ ht⟩

/-- The entire raw decoder emits four canonical outputs, preserving
caller suffixes and emptying all input and private scratch on success. -/
theorem run_some {x : List Bool} {as : List (Nat × Nat)} {c t : Nat}
    (h : bitDecode x = some (as, (c, t)))
    (weights values capacity threshold : List Bool) (v : Bool) :
    ∃ w, RunLe prog (9 * x.length + 2)
      ⟨some (.split .read), v, st [] x weights values capacity threshold⟩
      ⟨some .good, w,
        st [] [] (bitEncode (as.map Prod.fst) ++ weights)
          (bitEncode (as.map Prod.snd) ++ values)
          (Computability.encodeNat c ++ capacity)
          (Computability.encodeNat t ++ threshold)⟩ := by
  obtain ⟨p, r, hx, hp, hr⟩ := decoded_pair_parts h
  obtain ⟨w, first⟩ := split_run p r weights values capacity threshold v
  obtain ⟨z, middle⟩ := items_run hp r weights values capacity threshold w
  obtain ⟨u, last⟩ := pair_run hr (bitEncode (as.map Prod.fst) ++ weights)
    (bitEncode (as.map Prod.snd) ++ values) capacity threshold z
  rw [hx]
  refine ⟨u, (((first.le le_rfl).trans middle).trans last).mono ?_⟩
  simp only [List.length_append, length_delimit]
  omega

/-- The combined newly emitted output size is at most twice raw input
length, independently of decoded magnitudes and caller output suffixes. -/
theorem output_length_le {x : List Bool} {as : List (Nat × Nat)} {c t : Nat}
    (h : bitDecode x = some (as, (c, t))) :
    (bitEncode (as.map Prod.fst)).length +
      (bitEncode (as.map Prod.snd)).length +
      (Computability.encodeNat c).length +
      (Computability.encodeNat t).length ≤ 2 * x.length := by
  obtain ⟨p, r, hx, hp, hr⟩ := decoded_pair_parts h
  have hi := ListNatPair.projection_length_le hp
  have hn := NatPair.decoded_payload_length_le hr
  rw [hx, List.length_append, length_delimit]
  omega

private theorem decode_fields (x : List Bool) :
    bitDecode (α := List (Nat × Nat) × (Nat × Nat)) x =
      (match undelimit x with
      | none => none
      | some (p, r) => match bitDecode (α := List (Nat × Nat)) p,
          bitDecode (α := Nat × Nat) r with
        | some as, some ct => some (as, ct)
        | _, _ => none) := by
  rfl'

private theorem split_bad {x : List Bool} (h : undelimit x = none)
    (weights values capacity threshold : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (x.length + 1)
      ⟨some (.split .read), v, st [] x weights values capacity threshold⟩
      ⟨some .bad, w, S⟩ := by
  obtain ⟨w, S, hr⟩ := PairSplit.run_none h [] v
  obtain ⟨T, ht, _, _⟩ := runLe_embed splitLabel embeds_split hr
    (S' := st [] x weights values capacity threshold)
    (by intro k; cases k <;>
      simp [splitEmb, st, ListNatPair.st, NatPair.st, PairSplit.st])
  exact ⟨w, T, ht⟩

private theorem items_bad {p : List Bool}
    (h : bitDecode (α := List (Nat × Nat)) p = none)
    (r weights values capacity threshold : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (12 * p.length + 2)
      ⟨some (.items .loop), v, st p r weights values capacity threshold⟩
      ⟨some .bad, w, S⟩ := by
  obtain ⟨w, S, hr⟩ := ListNatPair.run_none h [] [] weights values v
  obtain ⟨T, ht, _, _⟩ := runLe_embed itemsLabel embeds_items hr
    (S' := st p r weights values capacity threshold)
    (by intro k; simp [itemsEmb, st])
  exact ⟨w, T, ht⟩

private theorem pair_bad {r : List Bool}
    (h : bitDecode (α := Nat × Nat) r = none)
    (weights values capacity threshold : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (r.length + 1)
      ⟨some (.pair (.pair .read)), v,
        st [] r weights values capacity threshold⟩
      ⟨some .bad, w, S⟩ := by
  obtain ⟨w, S, hr⟩ := NatPair.run_none h capacity threshold v
  obtain ⟨T, ht, _, _⟩ := runLe_embed pairLabel embeds_pair hr
    (S' := st [] r weights values capacity threshold)
    (by intro k; simp [pairEmb, st])
  exact ⟨w, T, ht⟩

/-- Every failed raw decode reaches `bad` within the same whole-input
bound. Failed owned workspace can be partial and must be discarded
or cleared. -/
theorem run_none {x : List Bool}
    (h : bitDecode (α := List (Nat × Nat) × (Nat × Nat)) x = none)
    (weights values capacity threshold : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (9 * x.length + 2)
      ⟨some (.split .read), v, st [] x weights values capacity threshold⟩
      ⟨some .bad, w, S⟩ := by
  cases hu : undelimit x with
  | none =>
    obtain ⟨w, S, hr⟩ := split_bad hu weights values capacity threshold v
    exact ⟨w, S, hr.mono (by omega)⟩
  | some pr =>
    obtain ⟨p, r⟩ := pr
    have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu
    obtain ⟨w, first⟩ := split_run p r weights values capacity threshold v
    rw [decode_fields, hu] at h
    cases hi : bitDecode (α := List (Nat × Nat)) p with
    | none =>
      obtain ⟨z, S, last⟩ := items_bad hi r weights values capacity threshold w
      rw [hx]
      refine ⟨z, S, ((first.le le_rfl).trans last).mono ?_⟩
      simp only [List.length_append, length_delimit]
      omega
    | some as =>
      have hn : bitDecode (α := Nat × Nat) r = none := by
        cases ht : bitDecode (α := Nat × Nat) r with
        | none => rfl
        | some ct => simp [hi, ht] at h
      obtain ⟨z, middle⟩ := items_run hi r weights values capacity threshold w
      obtain ⟨u, S, last⟩ := pair_bad hn
        (bitEncode (as.map Prod.fst) ++ weights)
        (bitEncode (as.map Prod.snd) ++ values) capacity threshold z
      rw [hx]
      refine ⟨u, S, (((first.le le_rfl).trans middle).trans last).mono ?_⟩
      simp only [List.length_append, length_delimit]
      omega

/-- The fixed seventeen-stack decoder in the existing Host interface. -/
abbrev component : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := ListNatPair.component.ks.map K.items ++ NatPair.component.ks.map K.pair
  ks_nodup := by decide
  mem_ks k := by
    simp only [List.mem_append]
    cases k with
    | items k =>
      exact Or.inl (List.mem_map.mpr
        ⟨k, ListNatPair.component.mem_ks k, rfl⟩)
    | pair k =>
      exact Or.inr (List.mem_map.mpr ⟨k, NatPair.component.mem_ks k, rfl⟩)

/-- Total raw decoder contract with four output suffixes. Exactly the
canonical decoder's success/failure label is reached, with empty
scratch on success. -/
theorem run (x weights values capacity threshold : List Bool) (v : Bool) :
    ∃ w S, RunLe prog (9 * x.length + 2)
      ⟨some (.split .read), v, st [] x weights values capacity threshold⟩
      ⟨some (if (bitDecode (α := List (Nat × Nat) × (Nat × Nat)) x).isSome
        then .good else .bad), w, S⟩ ∧
      ∀ (as : List (Nat × Nat)) (c t : Nat),
        bitDecode x = some (as, (c, t)) →
        S = st [] [] (bitEncode (as.map Prod.fst) ++ weights)
          (bitEncode (as.map Prod.snd) ++ values)
          (Computability.encodeNat c ++ capacity)
          (Computability.encodeNat t ++ threshold) := by
  cases h : bitDecode (α := List (Nat × Nat) × (Nat × Nat)) x with
  | none =>
    obtain ⟨w, S, hr⟩ := run_none h weights values capacity threshold v
    refine ⟨w, S, hr, ?_⟩
    intro as c t ha
    simp at ha
  | some act =>
    obtain ⟨as, c, t⟩ := act
    obtain ⟨w, hr⟩ := run_some h weights values capacity threshold v
    refine ⟨w, st [] [] (bitEncode (as.map Prod.fst) ++ weights)
      (bitEncode (as.map Prod.snd) ++ values)
      (Computability.encodeNat c ++ capacity)
      (Computability.encodeNat t ++ threshold), hr, ?_⟩
    intro bs d u hb
    obtain ⟨rfl, hct⟩ := Prod.mk.inj (Option.some.inj hb)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hct
    rfl

/-- Embedded execution preserves every outside stack on both outcomes.
Successful output suffixes survive and private scratch is empty. Failed
workspace may be partial. Callers establish continuation-label separation. -/
theorem run_embedded {J L : Type} [DecidableEq J] {Γ : J → Type}
    (E : SEmb (fun _ : K => Bool) Γ) (φ : Lab → L)
    {M : L → TM2.Stmt Γ L Bool} (hm : Embeds E φ prog M)
    (x weights values capacity threshold : List Bool) (v : Bool)
    (S : ∀ j, List (Γ j))
    (hs : Agree E (st [] x weights values capacity threshold) S) :
    ∃ w T, RunLe M (9 * x.length + 2)
      ⟨some (φ (.split .read)), v, S⟩
      ⟨some (φ (if (bitDecode (α := List (Nat × Nat) × (Nat × Nat)) x).isSome
        then .good else .bad)), w, T⟩ ∧ Frame E S T ∧
      ∀ (as : List (Nat × Nat)) (c t : Nat),
        bitDecode x = some (as, (c, t)) →
        Agree E (st [] [] (bitEncode (as.map Prod.fst) ++ weights)
          (bitEncode (as.map Prod.snd) ++ values)
          (Computability.encodeNat c ++ capacity)
          (Computability.encodeNat t ++ threshold)) T := by
  obtain ⟨w, U, hr, hu⟩ := run x weights values capacity threshold v
  obtain ⟨T, ht, ha, hf⟩ := runLe_embed φ hm hr hs
  refine ⟨w, T, ht, hf, ?_⟩
  intro as c t h
  rw [hu as c t h] at ha
  exact ha

end Cslib.Complexity.PolynomialEncoding.ListNatPairPair
