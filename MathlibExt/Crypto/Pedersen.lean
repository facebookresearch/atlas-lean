/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.LinearCombination

@[expose] public section



private theorem pow_val_bijective {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (x : G) (hx : orderOf x = Fintype.card G) :
    Function.Bijective (fun r : ZMod (Fintype.card G) => x ^ r.val) := by
  haveI : Nonempty G := ⟨1⟩
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  haveI : NeZero (Fintype.card G) := ⟨ne_of_gt hpos⟩
  have hinj : Function.Injective (fun r : ZMod (Fintype.card G) => x ^ r.val) := by
    intro r s hrs
    change x ^ r.val = x ^ s.val at hrs
    have hmod : r.val ≡ s.val [MOD orderOf x] := pow_eq_pow_iff_modEq.mp hrs
    rw [hx] at hmod
    have heq : r.val = s.val :=
      hmod.eq_of_lt_of_lt (ZMod.val_lt r) (ZMod.val_lt s)
    exact ZMod.val_injective _ heq
  have hcard : Fintype.card (ZMod (Fintype.card G)) = Fintype.card G := ZMod.card _
  have hsurj : Function.Surjective (fun r : ZMod (Fintype.card G) => x ^ r.val) := by
    intro y
    have himg : (Finset.univ.image
        (fun r : ZMod (Fintype.card G) => x ^ r.val)).card = Fintype.card G := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard]
    have huniv : Finset.univ.image
        (fun r : ZMod (Fintype.card G) => x ^ r.val) = Finset.univ :=
      Finset.eq_univ_of_card _ himg
    have hy : y ∈ Finset.univ.image
        (fun r : ZMod (Fintype.card G) => x ^ r.val) := by
      rw [huniv]
      exact Finset.mem_univ y
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hy
    exact ⟨r, hr⟩
  exact ⟨hinj, hsurj⟩

/-- Pedersen commitments in a finite group `G` with two
generators `g, h` of maximal order `N = |G|`: the commitment to
message `m` with randomness `r` (both in `ZMod N`) is
`g^m * h^r`. Perfect hiding: for every message and every group
element, exactly one randomness opens the commitment to it, so
the commitment distribution is independent of the message. -/
theorem pedersen_hiding {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (g h : G)
    (hg : orderOf g = Fintype.card G) (hh : orderOf h = Fintype.card G)
    (m : ZMod (Fintype.card G)) (c : G) :
    (Finset.univ.filter (fun r : ZMod (Fintype.card G) =>
      g ^ m.val * h ^ r.val = c)).card = 1 := by
  have hb : Function.Bijective (fun r : ZMod (Fintype.card G) => h ^ r.val) :=
    pow_val_bijective h hh
  obtain ⟨r₀, hr₀⟩ := hb.2 ((g ^ m.val)⁻¹ * c)
  have h0 : h ^ r₀.val = (g ^ m.val)⁻¹ * c := hr₀
  have hmem : g ^ m.val * h ^ r₀.val = c := by
    rw [h0, ← mul_assoc, mul_inv_cancel, one_mul]
  have hex : ∃! r : ZMod (Fintype.card G), g ^ m.val * h ^ r.val = c :=
    ⟨r₀, hmem, fun s hs => hb.1 (mul_left_cancel (show
      g ^ m.val * h ^ s.val = g ^ m.val * h ^ r₀.val from by rw [hs, hmem]))⟩
  obtain ⟨r₁, hr₁, huniq⟩ := hex
  have hfilter : Finset.univ.filter (fun r : ZMod (Fintype.card G) =>
      g ^ m.val * h ^ r.val = c) = {r₁} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hx => huniq x hx, fun hx => by rw [hx]; exact hr₁⟩
  rw [hfilter, Finset.card_singleton]

/-- Computational binding, extraction form: if one commitment
opens to two different messages with different randomness, then
`h` is a power of `g` whose discrete logarithm is extractable:
there is `a : ZMod N` with `h = g ^ a.val`, and `a` solves
`a * (r - r') = m' - m` in `ZMod N` (so finding two openings
computes `log_g h` whenever `r - r'` is a unit; in particular
two distinct openings cannot exist if `log_g h` is unknown). -/
theorem pedersen_binding_extract {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (g h : G)
    (hg : orderOf g = Fintype.card G) (hh : orderOf h = Fintype.card G)
    {m m' r r' : ZMod (Fintype.card G)}
    (hopen : g ^ m.val * h ^ r.val = g ^ m'.val * h ^ r'.val)
    (hr : r ≠ r') :
    ∃ a : ZMod (Fintype.card G), h = g ^ a.val ∧
      a * (r - r') = m' - m := by
  haveI : Nonempty G := ⟨1⟩
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  haveI : NeZero (Fintype.card G) := ⟨ne_of_gt hpos⟩
  obtain ⟨a, ha⟩ := (pow_val_bijective g hg).2 h
  have ha' : g ^ a.val = h := ha
  refine ⟨a, ha'.symm, ?_⟩
  have hopen' := hopen
  rw [← ha'] at hopen'
  simp only [← pow_mul, ← pow_add] at hopen'
  have hmod : m.val + a.val * r.val ≡ m'.val + a.val * r'.val [MOD orderOf g] :=
    pow_eq_pow_iff_modEq.mp hopen'
  rw [hg] at hmod
  have heq : ((m.val + a.val * r.val : ℕ) : ZMod (Fintype.card G)) =
      ((m'.val + a.val * r'.val : ℕ) : ZMod (Fintype.card G)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id] at heq
  linear_combination heq
