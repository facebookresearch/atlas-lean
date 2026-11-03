/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin

/-!
# Size bounds for the canonical framed codecs

These structural bounds hold for every successful raw-input decode,
including noncanonical binary Nat payloads. They justify list-bounded
loops and certificates for the concrete undergraduate decision problems.
They assert no running-time property of an arbitrary element codec.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding

open MetaMathlibExt BitstringEncoding

/-- Each decoded block consumes at least its delimiter bit. -/
theorem blocks_length_le {fuel : Nat} {x : List Bool}
    {blocks : List (List Bool)}
    (h : undelimitBlocksAux fuel x = some blocks) :
    blocks.length ≤ x.length := by
  induction fuel generalizing x blocks with
  | zero =>
    cases x <;> simp_all [undelimitBlocksAux]
  | succ fuel ih =>
    cases x with
    | nil => simp_all [undelimitBlocksAux]
    | cons b xs =>
      change ((undelimit (b :: xs)).bind fun p =>
        (undelimitBlocksAux fuel p.2).map (p.1 :: ·)) = _ at h
      obtain ⟨⟨p, r⟩, hp, hs⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨bs, hb, rfl⟩ := Option.map_eq_some_iff.mp hs
      have hr : bs.length ≤ r.length := ih hb
      have he := congrArg List.length
        ((Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hp)
      simp only [List.length_cons, List.length_append,
        length_delimit] at he ⊢
      omega

private theorem mapM_length {α β : Type} (f : α → Option β)
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys) :
    ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simpa using h.symm
  | cons a xs ih =>
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hb : xs.mapM f with
      | none => simp [ha, hb] at h
      | some bs =>
        have he : b :: bs = ys := by simpa [ha, hb] using h
        subst ys
        simp [ih hb]

/-- A successfully decoded list has at most one element per input bit.
No canonicality assumption on the element payloads is needed. -/
theorem decoded_list_length_le {α : Type} [BitstringEncoding α]
    {x : List Bool} {as : List α}
    (h : bitDecode x = some as) : as.length ≤ x.length := by
  change (undelimitBlocks x).bind (List.mapM bitDecode) = _ at h
  obtain ⟨blocks, hb, ha⟩ := Option.bind_eq_some_iff.mp h
  rw [mapM_length bitDecode ha]
  exact blocks_length_le hb

/-- Successful pair decoding exposes the exact raw component payloads.
This includes payloads which are not canonical encodings. -/
theorem decoded_pair_parts {α β : Type}
    [BitstringEncoding α] [BitstringEncoding β]
    {x : List Bool} {a : α} {b : β}
    (h : bitDecode x = some (a, b)) :
    ∃ p r, x = delimit p ++ r ∧
      bitDecode p = some a ∧ bitDecode r = some b := by
  change (match undelimit x with
    | none => none
    | some (p, r) => match bitDecode (α := α) p, bitDecode (α := β) r with
      | some a, some b => some (a, b)
      | _, _ => none) = _ at h
  cases hu : undelimit x with
  | none => simp [hu] at h
  | some pr =>
    obtain ⟨p, r⟩ := pr
    cases hp : bitDecode (α := α) p <;>
      cases hr : bitDecode (α := β) r <;>
        simp only [hu, hp, hr, Option.some.injEq, Prod.mk.injEq,
          reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨p, r, (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp hu,
      hp, hr⟩

/-- A list in the first field of a decoded pair is raw-input bounded. -/
theorem decoded_fst_list_length_le {α β : Type}
    [BitstringEncoding α] [BitstringEncoding β]
    {x : List Bool} {as : List α} {b : β}
    (h : bitDecode x = some (as, b)) : as.length ≤ x.length := by
  obtain ⟨p, r, rfl, hp, _⟩ := decoded_pair_parts h
  have hl := decoded_list_length_le hp
  simp only [List.length_append, length_delimit]
  omega

/-- A list in the second field of a decoded pair is raw-input bounded. -/
theorem decoded_snd_list_length_le {α β : Type}
    [BitstringEncoding α] [BitstringEncoding β]
    {x : List Bool} {a : α} {bs : List β}
    (h : bitDecode x = some (a, bs)) : bs.length ≤ x.length := by
  obtain ⟨p, r, rfl, _, hr⟩ := decoded_pair_parts h
  have hl := decoded_list_length_le hr
  simp only [List.length_append, length_delimit]
  omega

/-- The middle list of a right-associated triple is raw-input bounded.
Used for TSP matrix rows and SET COVER set occurrences. -/
theorem decoded_middle_list_length_le {α β γ : Type}
    [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    {x : List Bool} {a : α} {bs : List β} {c : γ}
    (h : bitDecode x = some (a, bs, c)) : bs.length ≤ x.length := by
  obtain ⟨p, r, rfl, _, hr⟩ := decoded_pair_parts h
  have hl := decoded_fst_list_length_le hr
  simp only [List.length_append, length_delimit]
  omega

/-- A list of binary naturals with at most `m` bits per entry has the
stated framed length bound. -/
theorem list_nat_encode_length_le (as : List Nat) (m : Nat)
    (h : ∀ a ∈ as, a.size ≤ m) :
    (bitEncode as).length ≤ as.length * (2 * m + 1) := by
  induction as with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    rfl
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    change (delimit (bitEncode a) ++ bitEncode as).length ≤ _
    simp only [List.length_append, length_delimit,
      BinaryNatEncoding.length_bitEncode, List.length_cons, Nat.add_mul]
    omega

/-- Lists of vertices below `n` have a quadratic certificate bound
when their length is at most `n`; no unary Nat encoding is used. -/
theorem bounded_nat_list_encode_length_le (as : List Nat) (n : Nat)
    (hlen : as.length ≤ n) (h : ∀ a ∈ as, a < n) :
    (bitEncode as).length ≤ n * (2 * n + 1) := by
  have hn : n < 2 ^ n := by
    clear hlen h
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; omega
  have hb := list_nat_encode_length_le as n (fun a ha =>
    Nat.size_le.mpr ((h a ha).trans hn))
  exact hb.trans (Nat.mul_le_mul_right _ hlen)

end Cslib.Complexity.PolynomialEncoding
