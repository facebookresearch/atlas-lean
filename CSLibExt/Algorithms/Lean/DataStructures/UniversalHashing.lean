/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Universal hashing

A finite family of hash functions `H ⊆ (α → Fin m)` is *universal* in the sense of
CLRS (Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*, fourth
edition), Section 11.3, if for every two distinct keys `x ≠ y` the number of functions in
the family under which `x` and `y` collide is at most `|H| / m`. Thus a uniformly chosen
function from the family collides on `x` and `y` with probability at most `1 / m`, the
probability for a completely random function. To stay inside `Nat` and avoid rationals,
`IsUniversal` states the bound as `collisionCount H x y * m ≤ H.card`.

The main construction is the mod-prime family of CLRS, fourth edition,
Section 11.3.3 (Theorem 11.5). For a prime `p`,
identifying keys and coefficients with the field `ZMod p`, the function indexed by
`a ≠ 0` and arbitrary `b` is `h_{a,b}(x) = ((a * x + b) mod p) mod m`, here
`modPrimeHash`. CLRS counts this family as having `p * (p - 1)` members, that is, one
member per index pair `(a, b)`. Distinct pairs can induce the same function after the
final reduction modulo `m`, so the counting result `modPrime_isUniversalOn` is stated
for the indexed family (`IsUniversalOn`), exactly matching the `p * (p - 1)` count in
the CLRS proof. The `Finset` of distinct functions is `modPrimeFamily`.

## Main statements

* `pairEquiv`: for fixed `x ≠ y` in `ZMod p`, the map `(a, b) ↦ (a * x + b, a * y + b)`
  is an equivalence between the index set and the ordered pairs `(r, s)` with `r ≠ s`.
  This is the counting heart of the CLRS argument: as `(a, b)` ranges over all indices,
  `(a * x + b, a * y + b)` ranges over all unequal pairs exactly once.
* `modPrime_collision_mul_le`: at most a `1 / m` fraction, in the multiplied-out `Nat`
  form, of the indices collide on two fixed distinct keys.
* `modPrime_isUniversalOn`: the indexed mod-prime family is universal.

The collision count reduces, through `pairEquiv`, to counting pairs `(r, s)` with
`r ≠ s` and `r.val % m = s.val % m`. For fixed `r` those `s` are determined by the
quotient `s.val / m`, which takes at most `(p - 1) / m` values different from the
quotient of `r`; hence each `r` contributes at most `(p - 1) / m` colliding partners,
and `((p - 1) / m) * m ≤ p - 1` finishes the estimate. This is the CLRS argument that
pairs collapsing modulo `m` number at most `⌈p / m⌉ - 1` for fixed `r`, phrased
without ceilings.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UniversalHashing

universe u v

section General

variable {α : Type u} {m : Nat}

/-- The number of functions in the family `H` under which `x` and `y` collide. -/
public def collisionCount (H : Finset (α → Fin m)) (x y : α) : Nat :=
  (H.filter fun h => h x = h y).card

/--
A finite hash family is universal if it is nonempty (so that choosing a member
uniformly at random, the reading behind the bound, makes sense) and every two
distinct keys collide under at most a `1 / m` fraction of its members, stated
without division as `collisionCount H x y * m ≤ H.card`.
-/
public def IsUniversal (H : Finset (α → Fin m)) : Prop :=
  0 < m ∧ H.Nonempty ∧ ∀ x y : α, x ≠ y → collisionCount H x y * m ≤ H.card

/--
Indexed universality: the family `h` ranges over the nonempty finite index set `s`,
counting each index separately even when two indices give the same function. This is
the form in which the classical counting arguments, including the mod-prime family
below, are carried out. Nonemptiness is part of the predicate for the same reason as
in `IsUniversal`: there is no uniform random choice from an empty family.
-/
public def IsUniversalOn {ι : Type v} (s : Finset ι) (h : ι → α → Fin m) : Prop :=
  0 < m ∧ s.Nonempty ∧
    ∀ x y : α, x ≠ y → (s.filter fun i => h i x = h i y).card * m ≤ s.card

/-- The collision count never exceeds the size of the family. -/
public theorem collisionCount_le_card (H : Finset (α → Fin m)) (x y : α) :
    collisionCount H x y ≤ H.card :=
  Finset.card_filter_le _ _

/-- A key collides with itself under every function in the family. -/
@[simp]
public theorem collisionCount_self (H : Finset (α → Fin m)) (x : α) :
    collisionCount H x x = H.card := by
  simp [collisionCount]

/-- The empty family is not universal: universality includes nonemptiness, since
its meaning is a bound on the collision probability for a uniformly chosen member. -/
public theorem not_isUniversal_empty : ¬ IsUniversal (∅ : Finset (α → Fin m)) :=
  fun h => by
    obtain ⟨f, hf⟩ := h.2.1
    simp at hf

/-- The empty indexed family is not universal, for the same reason. -/
public theorem not_isUniversalOn_empty {ι : Type v} (h : ι → α → Fin m) :
    ¬ IsUniversalOn (∅ : Finset ι) h :=
  fun hh => by
    obtain ⟨i, hi⟩ := hh.2.1
    simp at hi

/-- The collision bound part of universality, without nonemptiness. The empty
family satisfies this bound vacuously; `IsUniversal` is this bound together with
`H.Nonempty` and a positive range size `0 < m`. -/
public theorem isUniversal_bound_empty :
    ∀ x y : α, x ≠ y →
      collisionCount (∅ : Finset (α → Fin m)) x y * m ≤
        (∅ : Finset (α → Fin m)).card := by
  intro x y _
  simp [collisionCount]

end General

section ModPrime

/--
The mod-prime hash function `h_{a,b}(x) = ((a * x + b) mod p) mod m` of CLRS
Section 11.3.3: the inner reduction modulo `p` is the arithmetic of `ZMod p`, and the
outer reduction is `Nat` remainder of the canonical representative.
-/
public def modPrimeHash (p m : Nat) (hm : 0 < m) (a b x : ZMod p) : Fin m :=
  ⟨(a * x + b).val % m, Nat.mod_lt _ hm⟩

/-- The index set of the mod-prime family: pairs `(a, b)` with `a ≠ 0`. -/
public abbrev ModPrimeIndex (p : Nat) : Type :=
  { a : ZMod p // a ≠ 0 } × ZMod p

/-- The mod-prime family as functions indexed by pairs `(a, b)` with `a ≠ 0`. -/
public def modPrimeHashes (p m : Nat) (hm : 0 < m) (ab : ModPrimeIndex p) :
    ZMod p → Fin m :=
  fun x => modPrimeHash p m hm ab.1.1 ab.2 x

/--
The mod-prime family as a `Finset` of distinct functions. The universality result
below is proved for the indexed family `modPrimeHashes`, matching the `p * (p - 1)`
count of indices in CLRS; the image here can be smaller, since distinct index pairs
may agree as functions after the final reduction modulo `m`.
-/
public def modPrimeFamily (p m : Nat) [NeZero p] (hm : 0 < m) :
    Finset (ZMod p → Fin m) :=
  Finset.univ.image (modPrimeHashes p m hm)

/-- The value of a mod-prime hash is the displayed double remainder. -/
@[simp]
public theorem modPrimeHash_val (p m : Nat) (hm : 0 < m) (a b x : ZMod p) :
    (modPrimeHash p m hm a b x).val = (a * x + b).val % m :=
  rfl

/-- Two keys collide under `h_{a,b}` exactly when the inner values agree modulo `m`. -/
public theorem modPrimeHash_eq_iff (p m : Nat) (hm : 0 < m) (a b x y : ZMod p) :
    modPrimeHash p m hm a b x = modPrimeHash p m hm a b y ↔
      (a * x + b).val % m = (a * y + b).val % m := by
  simp [Fin.ext_iff]

/--
The pair map of the CLRS counting argument: it sends an index `(a, b)` to the pair of
inner values `(a * x + b, a * y + b)` at two fixed keys.
-/
public def pairMap {p : Nat} (x y : ZMod p) (ab : ModPrimeIndex p) : ZMod p × ZMod p :=
  (ab.1.1 * x + ab.2, ab.1.1 * y + ab.2)

/-- Extensionality form of `pairMap`. -/
@[simp]
public theorem pairMap_apply {p : Nat} (x y : ZMod p) (ab : ModPrimeIndex p) :
    pairMap x y ab = (ab.1.1 * x + ab.2, ab.1.1 * y + ab.2) :=
  rfl

/--
For distinct keys `x ≠ y` in the field `ZMod p`, the two components of `pairMap`
differ: their difference is `a * (x - y)` with both factors nonzero.
-/
public theorem pairMap_fst_ne_snd {p : Nat} [Fact p.Prime] {x y : ZMod p}
    (hxy : x ≠ y) (ab : ModPrimeIndex p) :
    (pairMap x y ab).1 ≠ (pairMap x y ab).2 := by
  intro h
  dsimp only [pairMap] at h
  have hdiff : ab.1.1 * (x - y) = 0 := by
    have h' : ab.1.1 * (x - y) = (ab.1.1 * x + ab.2) - (ab.1.1 * y + ab.2) := by ring
    rw [h', h, sub_self]
  rcases mul_eq_zero.mp hdiff with ha | hs
  · exact ab.1.2 ha
  · exact hxy (sub_eq_zero.mp hs)

/--
The core bijection of the CLRS counting argument. For fixed distinct keys `x ≠ y` in
the field `ZMod p`, solving the linear system `a * x + b = r`, `a * y + b = s` gives
`a = (r - s) / (x - y)` and `b = r - a * x`; this inverts `pairMap`. Hence the indices
`(a, b)` with `a ≠ 0` are in bijection with the ordered pairs `(r, s)` with `r ≠ s`.
-/
public def pairEquiv {p : Nat} [Fact p.Prime] {x y : ZMod p} (hxy : x ≠ y) :
    ModPrimeIndex p ≃ { rs : ZMod p × ZMod p // rs.1 ≠ rs.2 } where
  toFun ab := ⟨pairMap x y ab, pairMap_fst_ne_snd hxy ab⟩
  invFun rs :=
    (⟨(rs.1.1 - rs.1.2) / (x - y),
      div_ne_zero (sub_ne_zero.mpr rs.2) (sub_ne_zero.mpr hxy)⟩,
    rs.1.1 - ((rs.1.1 - rs.1.2) / (x - y)) * x)
  left_inv := by
    intro ab
    obtain ⟨⟨a, ha⟩, b⟩ := ab
    have hxy' : (x - y) ≠ 0 := sub_ne_zero.mpr hxy
    have haeq : ((a * x + b) - (a * y + b)) / (x - y) = a := by
      have hnum : (a * x + b) - (a * y + b) = a * (x - y) := by ring
      rw [hnum]
      exact mul_div_cancel_right₀ a hxy'
    apply Prod.ext
    · exact Subtype.ext haeq
    · show (a * x + b) - (((a * x + b) - (a * y + b)) / (x - y)) * x = b
      rw [haeq]
      ring
  right_inv := by
    intro rs
    obtain ⟨⟨r, s⟩, hrs⟩ := rs
    have hxy' : (x - y) ≠ 0 := sub_ne_zero.mpr hxy
    have hkey : ((r - s) / (x - y)) * (x - y) = r - s := div_mul_cancel₀ _ hxy'
    apply Subtype.ext
    apply Prod.ext
    · show ((r - s) / (x - y)) * x + (r - ((r - s) / (x - y)) * x) = r
      ring
    · show ((r - s) / (x - y)) * y + (r - ((r - s) / (x - y)) * x) = s
      linear_combination -hkey

/-- The forward direction of `pairEquiv` is `pairMap` on first components. -/
@[simp]
public theorem pairEquiv_apply_fst {p : Nat} [Fact p.Prime] {x y : ZMod p}
    (hxy : x ≠ y) (ab : ModPrimeIndex p) :
    (pairEquiv hxy ab).1 = pairMap x y ab :=
  rfl

/-- In particular `pairMap` is injective for distinct keys. -/
public theorem pairMap_injective {p : Nat} [Fact p.Prime] {x y : ZMod p}
    (hxy : x ≠ y) : Function.Injective (pairMap x y) := by
  intro ab₁ ab₂ h
  have h' : pairEquiv hxy ab₁ = pairEquiv hxy ab₂ := Subtype.ext h
  exact (pairEquiv hxy).injective h'

/--
The pairs of inner values that collide modulo `m`: unequal pairs `(r, s)` whose
canonical representatives agree modulo `m`. Through `pairEquiv`, counting these pairs
counts the colliding indices `(a, b)`.
-/
private def collidingPairs (p m : Nat) [NeZero p] : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun rs => rs.1 ≠ rs.2 ∧ rs.1.val % m = rs.2.val % m

/--
Quotient bound: every `s : ZMod p` satisfies `s.val / m ≤ (p - 1) / m`, since
`s.val ≤ p - 1`.
-/
private theorem val_div_le {p m : Nat} [NeZero p] (s : ZMod p) :
    s.val / m ≤ (p - 1) / m :=
  Nat.div_le_div_right (by have h := ZMod.val_lt s; omega)

/-- Equal quotients and equal remainders modulo `m` give equal values. -/
private theorem val_eq_of_div_eq_of_mod_eq {p m : Nat} [NeZero p] {s t : ZMod p}
    (hdiv : s.val / m = t.val / m) (hmod : s.val % m = t.val % m) : s = t := by
  apply ZMod.val_injective p
  conv_lhs => rw [← Nat.mod_add_div s.val m]
  conv_rhs => rw [← Nat.mod_add_div t.val m]
  rw [hmod, hdiv]

/--
Fibre bound: for fixed `r`, the number of colliding partners `s ≠ r` with
`s.val % m = r.val % m`, multiplied by `m`, is at most `p - 1`. The map
`s ↦ s.val / m` injects those partners into the `(p - 1) / m` quotients different
from `r.val / m`, because quotient and remainder together determine `s.val`, and
`((p - 1) / m) * m ≤ p - 1`.
-/
private theorem fiber_mul_le {p m : Nat} [NeZero p] (r : ZMod p) :
    ((collidingPairs p m).filter fun rs => rs.1 = r).card * m ≤ p - 1 := by
  have hcard :
      ((collidingPairs p m).filter fun rs => rs.1 = r).card ≤
        ((Finset.range ((p - 1) / m + 1)).erase (r.val / m)).card := by
    apply Finset.card_le_card_of_injOn (fun rs => rs.2.val / m)
    · intro rs hrs
      simp only [Finset.mem_coe, Finset.mem_filter, collidingPairs,
        Finset.mem_univ, true_and] at hrs
      obtain ⟨⟨hne, hres⟩, hr⟩ := hrs
      show rs.2.val / m ∈ (Finset.range ((p - 1) / m + 1)).erase (r.val / m)
      rw [Finset.mem_erase, Finset.mem_range]
      constructor
      · intro hdiv
        have hdiv' : rs.2.val / m = rs.1.val / m := by rw [hr]; exact hdiv
        have heq : rs.2 = rs.1 :=
          val_eq_of_div_eq_of_mod_eq hdiv' hres.symm
        exact hne heq.symm
      · have hle := val_div_le (p := p) (m := m) rs.2
        omega
    · intro rs₁ hrs₁ rs₂ hrs₂ hdiv
      simp only [Finset.mem_coe, Finset.mem_filter, collidingPairs,
        Finset.mem_univ, true_and] at hrs₁ hrs₂
      obtain ⟨⟨_, hres₁⟩, hr₁⟩ := hrs₁
      obtain ⟨⟨_, hres₂⟩, hr₂⟩ := hrs₂
      have hmod : rs₁.2.val % m = rs₂.2.val % m := by
        calc rs₁.2.val % m = rs₁.1.val % m := hres₁.symm
          _ = r.val % m := by rw [hr₁]
          _ = rs₂.1.val % m := by rw [hr₂]
          _ = rs₂.2.val % m := hres₂
      have hsnd : rs₁.2 = rs₂.2 := val_eq_of_div_eq_of_mod_eq hdiv hmod
      exact Prod.ext (by rw [hr₁, hr₂]) hsnd
  have herase :
      ((Finset.range ((p - 1) / m + 1)).erase (r.val / m)).card = (p - 1) / m := by
    rw [Finset.card_erase_of_mem
      (Finset.mem_range.mpr (by have hle := val_div_le (p := p) (m := m) r; omega)),
      Finset.card_range, Nat.add_sub_cancel]
  calc ((collidingPairs p m).filter fun rs => rs.1 = r).card * m
      ≤ ((p - 1) / m) * m := Nat.mul_le_mul (herase ▸ hcard) (Nat.le_refl m)
    _ ≤ p - 1 := Nat.div_mul_le_self _ _

/-- Counting colliding pairs fibre by fibre over the first component. -/
private theorem collidingPairs_mul_le {p m : Nat} [NeZero p] :
    (collidingPairs p m).card * m ≤ p * (p - 1) := by
  have hsum : (collidingPairs p m).card =
      ∑ r : ZMod p, ((collidingPairs p m).filter fun rs => rs.1 = r).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  calc (collidingPairs p m).card * m
      = (∑ r : ZMod p, ((collidingPairs p m).filter fun rs => rs.1 = r).card) * m := by
        rw [hsum]
    _ = ∑ r : ZMod p, ((collidingPairs p m).filter fun rs => rs.1 = r).card * m :=
        Finset.sum_mul _ _ _
    _ ≤ ∑ _r : ZMod p, (p - 1) := Finset.sum_le_sum fun r _ => fiber_mul_le r
    _ = p * (p - 1) := by
        simp [Finset.sum_const, Finset.card_univ, ZMod.card]

/-- Applying `pairMap` to the inverse index of `rs` recovers `rs`. -/
private theorem pairMap_pairEquiv_symm {p : Nat} [Fact p.Prime] {x y : ZMod p}
    (hxy : x ≠ y) (rs : { rs : ZMod p × ZMod p // rs.1 ≠ rs.2 }) :
    pairMap x y ((pairEquiv hxy).symm rs) = rs.1 := by
  have h : (pairEquiv hxy ((pairEquiv hxy).symm rs)).1 = rs.1 :=
    congrArg Subtype.val ((pairEquiv hxy).apply_symm_apply rs)
  rw [pairEquiv_apply_fst] at h
  exact h

/--
The key counting lemma (CLRS Theorem 11.5, counting step): for distinct keys `x ≠ y`,
the number of indices `(a, b)`, `a ≠ 0`, for which `h_{a,b}` collides on `x` and `y`,
multiplied by `m`, is at most `p * (p - 1)`, the total number of indices. The
bijection `pairEquiv` identifies colliding indices with the colliding pairs counted
in `collidingPairs_mul_le`.
-/
public theorem modPrime_collision_mul_le {p m : Nat} [Fact p.Prime]
    (hm : 0 < m) {x y : ZMod p} (hxy : x ≠ y) :
    (Finset.univ.filter fun ab : ModPrimeIndex p =>
      modPrimeHashes p m hm ab x = modPrimeHashes p m hm ab y).card * m ≤
      p * (p - 1) := by
  haveI : NeZero p := ⟨by
    have h2 := (Fact.out : p.Prime).two_le
    omega⟩
  have hcard :
      (Finset.univ.filter fun ab : ModPrimeIndex p =>
        modPrimeHashes p m hm ab x = modPrimeHashes p m hm ab y).card =
        (collidingPairs p m).card := by
    refine Finset.card_bij' (fun ab _ => pairMap x y ab) (fun rs hrs => ?_) ?_ ?_ ?_ ?_
    · have hrs' : rs ∈ Finset.univ.filter
          (fun rs => rs.1 ≠ rs.2 ∧ rs.1.val % m = rs.2.val % m) := hrs
      exact (pairEquiv hxy).symm ⟨rs, (Finset.mem_filter.mp hrs').2.1⟩
    · intro ab hab
      have hab' : modPrimeHashes p m hm ab x = modPrimeHashes p m hm ab y :=
        (Finset.mem_filter.mp hab).2
      have hres : (ab.1.1 * x + ab.2).val % m = (ab.1.1 * y + ab.2).val % m :=
        (modPrimeHash_eq_iff p m hm ab.1.1 ab.2 x y).mp hab'
      show pairMap x y ab ∈ collidingPairs p m
      simp only [collidingPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨pairMap_fst_ne_snd hxy ab, hres⟩
    · intro rs hrs
      have hrs' : rs ∈ Finset.univ.filter
          (fun rs => rs.1 ≠ rs.2 ∧ rs.1.val % m = rs.2.val % m) := hrs
      obtain ⟨hne, hres⟩ := (Finset.mem_filter.mp hrs').2
      show (pairEquiv hxy).symm ⟨rs, hne⟩ ∈ Finset.univ.filter
        (fun ab : ModPrimeIndex p =>
          modPrimeHashes p m hm ab x = modPrimeHashes p m hm ab y)
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      set ab' := (pairEquiv hxy).symm ⟨rs, hne⟩ with hab'
      have hpair : pairMap x y ab' = rs := pairMap_pairEquiv_symm hxy ⟨rs, hne⟩
      have e₁ : (ab'.1.1 * x + ab'.2).val % m = rs.1.val % m :=
        congrArg (fun q : ZMod p × ZMod p => q.1.val % m) hpair
      have e₂ : (ab'.1.1 * y + ab'.2).val % m = rs.2.val % m :=
        congrArg (fun q : ZMod p × ZMod p => q.2.val % m) hpair
      show modPrimeHash p m hm ab'.1.1 ab'.2 x = modPrimeHash p m hm ab'.1.1 ab'.2 y
      rw [modPrimeHash_eq_iff, e₁, e₂]
      exact hres
    · intro ab _
      show (pairEquiv hxy).symm ⟨pairMap x y ab, pairMap_fst_ne_snd hxy ab⟩ = ab
      exact (pairEquiv hxy).symm_apply_apply ab
    · intro rs hrs
      have hrs' : rs ∈ Finset.univ.filter
          (fun rs => rs.1 ≠ rs.2 ∧ rs.1.val % m = rs.2.val % m) := hrs
      obtain ⟨hne, _⟩ := (Finset.mem_filter.mp hrs').2
      show pairMap x y ((pairEquiv hxy).symm ⟨rs, hne⟩) = rs
      exact pairMap_pairEquiv_symm hxy ⟨rs, hne⟩
  rw [hcard]
  exact collidingPairs_mul_le

/-- The mod-prime family has `p * (p - 1)` indices. -/
public theorem modPrimeIndex_card {p : Nat} [NeZero p] :
    Fintype.card (ModPrimeIndex p) = p * (p - 1) := by
  have hsub : Fintype.card { a : ZMod p // a ≠ 0 } = p - 1 := by
    rw [Fintype.card_subtype_compl (· = 0), Fintype.card_subtype_eq, ZMod.card]
  rw [Fintype.card_prod, hsub, ZMod.card, Nat.mul_comm]

/--
Universality of the mod-prime family (CLRS Theorem 11.5): the indexed family
`modPrimeHashes` over all `(a, b)` with `a ≠ 0` is universal. A uniformly random
index therefore collides on any two distinct keys with probability at most `1 / m`.
-/
public theorem modPrime_isUniversalOn {p m : Nat} [Fact p.Prime]
    (hm : 0 < m) :
    IsUniversalOn Finset.univ (modPrimeHashes p m hm) := by
  haveI : NeZero p := ⟨by
    have h2 := (Fact.out : p.Prime).two_le
    omega⟩
  refine ⟨hm, ⟨(⟨1, one_ne_zero⟩, 0), Finset.mem_univ _⟩, fun x y hxy => ?_⟩
  calc (Finset.univ.filter fun ab : ModPrimeIndex p =>
        modPrimeHashes p m hm ab x = modPrimeHashes p m hm ab y).card * m
      ≤ p * (p - 1) := modPrime_collision_mul_le hm hxy
    _ = (Finset.univ : Finset (ModPrimeIndex p)).card := by
        rw [Finset.card_univ, modPrimeIndex_card]

/-- Membership in the `Finset` of distinct mod-prime functions. -/
@[simp]
public theorem mem_modPrimeFamily {p m : Nat} [NeZero p] (hm : 0 < m)
    (h : ZMod p → Fin m) :
    h ∈ modPrimeFamily p m hm ↔ ∃ ab : ModPrimeIndex p, modPrimeHashes p m hm ab = h := by
  simp [modPrimeFamily]

end ModPrime

end Cslib.Algorithms.Lean.UniversalHashing
