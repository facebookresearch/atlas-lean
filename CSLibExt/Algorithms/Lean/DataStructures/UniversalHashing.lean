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

/-- **Collision count.** For a finite family $H$ of functions from a set $\alpha$ to
$\{0, 1, \dots, m - 1\}$ and keys $x, y \in \alpha$, the collision count of $x$ and $y$ in $H$
is the number of functions $h \in H$ with $h(x) = h(y)$. -/
public def collisionCount (H : Finset (α → Fin m)) (x y : α) : Nat :=
  (H.filter fun h => h x = h y).card

/--
**Universal hash family.** A finite family $H$ of functions from a set $\alpha$ to
$\{0, 1, \dots, m - 1\}$ is universal if $m > 0$, $H$ is nonempty, and for all distinct keys
$x \ne y$ in $\alpha$ the number of functions $h \in H$ with $h(x) = h(y)$, multiplied by $m$,
is at most $|H|$; that is, $x$ and $y$ collide under at most a $1/m$ fraction of the members
of $H$.

Nonemptiness makes sense of choosing a member of $H$ uniformly at random, the reading behind
the bound.
-/
public def IsUniversal (H : Finset (α → Fin m)) : Prop :=
  0 < m ∧ H.Nonempty ∧ ∀ x y : α, x ≠ y → collisionCount H x y * m ≤ H.card

/--
**Indexed universal hash family.** Let $s$ be a finite set of indices from a type $\iota$,
and let $h$ assign to each index $i \in \iota$ a function $h_i$ from a set $\alpha$ to
$\{0, 1, \dots, m - 1\}$. The family $h$ is universal on $s$ if $m > 0$, $s$ is nonempty,
and for all distinct keys $x \ne y$ in $\alpha$ the number of indices $i \in s$ with
$h_i(x) = h_i(y)$, multiplied by $m$, is at most $|s|$.

Each index is counted separately, even when two indices give the same function; this is the
form in which the classical counting arguments, including the one for the mod-prime family,
are carried out. Nonemptiness is required because there is no uniform random choice from an
empty family.
-/
public def IsUniversalOn {ι : Type v} (s : Finset ι) (h : ι → α → Fin m) : Prop :=
  0 < m ∧ s.Nonempty ∧
    ∀ x y : α, x ≠ y → (s.filter fun i => h i x = h i y).card * m ≤ s.card

/-- **Collision count is at most the family size.** For every finite family $H$ of functions
from a set $\alpha$ to $\{0, 1, \dots, m - 1\}$ and all keys $x, y \in \alpha$, the number of
functions $h \in H$ with $h(x) = h(y)$ is at most $|H|$. -/
public theorem collisionCount_le_card (H : Finset (α → Fin m)) (x y : α) :
    collisionCount H x y ≤ H.card :=
  Finset.card_filter_le _ _

/-- **A key collides with itself under the whole family.** For every finite family $H$ of
functions from a set $\alpha$ to $\{0, 1, \dots, m - 1\}$ and every key $x \in \alpha$, the
collision count of $x$ with itself in $H$ equals $|H|$: $x$ collides with itself under every
function in $H$. -/
@[simp]
public theorem collisionCount_self (H : Finset (α → Fin m)) (x : α) :
    collisionCount H x x = H.card := by
  simp [collisionCount]

/-- **The empty hash family is not universal.** For every type of keys $\alpha$ and every natural
number $m$, the empty family of functions $\alpha \to \{0, \dots, m - 1\}$ is not universal:
universality includes nonemptiness, since its meaning is a bound on the collision probability for
a uniformly chosen member. -/
public theorem not_isUniversal_empty : ¬ IsUniversal (∅ : Finset (α → Fin m)) :=
  fun h => by
    obtain ⟨f, hf⟩ := h.2.1
    simp at hf

/-- **The empty indexed family is not universal.** For every index type $\iota$, every type of
keys $\alpha$, every natural number $m$ and every family $(h_i)_{i \in \iota}$ of functions
$h_i \colon \alpha \to \{0, \dots, m - 1\}$, the family is not universal over the empty index
set: indexed universality includes nonemptiness of the index set, since there is no uniform
random choice from an empty family. -/
public theorem not_isUniversalOn_empty {ι : Type v} (h : ι → α → Fin m) :
    ¬ IsUniversalOn (∅ : Finset ι) h :=
  fun hh => by
    obtain ⟨i, hi⟩ := hh.2.1
    simp at hi

/-- **The empty family satisfies the collision bound.** For every natural number $m$ and all
distinct keys $x \ne y$ in a set $\alpha$, the collision count of $x$ and $y$ in the empty
family of functions from $\alpha$ to $\{0, 1, \dots, m - 1\}$, multiplied by $m$, is at most
the size of the empty family, which is $0$.

This is the collision bound of universality without its other conditions; universality also
requires the family to be nonempty and $m > 0$, so the empty family is not universal. -/
public theorem isUniversal_bound_empty :
    ∀ x y : α, x ≠ y →
      collisionCount (∅ : Finset (α → Fin m)) x y * m ≤
        (∅ : Finset (α → Fin m)).card := by
  intro x y _
  simp [collisionCount]

end General

section ModPrime

/--
**Mod-prime hash function.** For natural numbers $p$ and $m$ with $m > 0$ and elements $a, b$
of $\mathbb{Z}/p\mathbb{Z}$, the mod-prime hash function
$h_{a,b} \colon \mathbb{Z}/p\mathbb{Z} \to \{0, \dots, m - 1\}$ is
$h_{a,b}(x) = \operatorname{val}(ax + b) \bmod m$, where $ax + b$ is computed in
$\mathbb{Z}/p\mathbb{Z}$ and $\operatorname{val}(z)$ is the canonical natural-number
representative of $z$ (the residue in $\{0, \dots, p - 1\}$ when $p > 0$, and $|z|$ when
$p = 0$). This is the function $h_{a,b}(x) = ((ax + b) \bmod p) \bmod m$ of CLRS
Section 11.3.3.
-/
public def modPrimeHash (p m : Nat) (hm : 0 < m) (a b x : ZMod p) : Fin m :=
  ⟨(a * x + b).val % m, Nat.mod_lt _ hm⟩

/-- **Mod-prime index set.** For a natural number $p$, the index set of the mod-prime family is
the set of pairs $(a, b)$ with $a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \neq 0$. -/
public abbrev ModPrimeIndex (p : Nat) : Type :=
  { a : ZMod p // a ≠ 0 } × ZMod p

/-- **Indexed mod-prime family.** For natural numbers $p$ and $m$ with $m > 0$, the indexed
mod-prime family assigns to each index $(a, b)$, with $a, b \in \mathbb{Z}/p\mathbb{Z}$ and
$a \neq 0$, the mod-prime hash function
$h_{a,b} \colon \mathbb{Z}/p\mathbb{Z} \to \{0, \dots, m - 1\}$. -/
public def modPrimeHashes (p m : Nat) (hm : 0 < m) (ab : ModPrimeIndex p) :
    ZMod p → Fin m :=
  fun x => modPrimeHash p m hm ab.1.1 ab.2 x

/--
**Mod-prime family of distinct functions.** For $p > 0$ and $m > 0$, the mod-prime family
is the finite set of all functions $h_{a,b}$ from $\mathbb{Z}/p\mathbb{Z}$ to
$\{0, 1, \dots, m - 1\}$ with $a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \ne 0$, where
$h_{a,b}$ is the mod-prime hash function with index $(a, b)$.

Universality is proved for the indexed family of mod-prime hash functions, matching the
$p(p - 1)$ count of indices in CLRS; this set of distinct functions can be smaller, since
distinct index pairs may give the same function after the final reduction modulo $m$.
-/
public def modPrimeFamily (p m : Nat) [NeZero p] (hm : 0 < m) :
    Finset (ZMod p → Fin m) :=
  Finset.univ.image (modPrimeHashes p m hm)

/-- **Value of the mod-prime hash.** For natural numbers $p$ and $m$ with $m > 0$ and elements
$a, b, x$ of $\mathbb{Z}/p\mathbb{Z}$, the mod-prime hash value
$h_{a,b}(x) \in \{0, \dots, m - 1\}$, read as a natural number, equals
$\operatorname{val}(ax + b) \bmod m$. Here $ax + b$ is computed in $\mathbb{Z}/p\mathbb{Z}$, and
$\operatorname{val}(z)$ is the canonical natural-number representative of $z$: the residue in
$\{0, \dots, p - 1\}$ when $p > 0$, and $|z|$ when $p = 0$. -/
@[simp]
public theorem modPrimeHash_val (p m : Nat) (hm : 0 < m) (a b x : ZMod p) :
    (modPrimeHash p m hm a b x).val = (a * x + b).val % m :=
  rfl

/-- **Collisions of a mod-prime hash function.** Let $p$ be a natural number, $m > 0$ and
$a, b \in \mathbb{Z}/p\mathbb{Z}$, and write $\operatorname{val}(z)$ for the canonical
natural-number representative of $z \in \mathbb{Z}/p\mathbb{Z}$ (for $p = 0$, where
$\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$, its absolute value), so that the mod-prime hash
function is $h_{a,b}(x) = \operatorname{val}(ax + b) \bmod m$. For all keys
$x, y \in \mathbb{Z}/p\mathbb{Z}$, we have $h_{a,b}(x) = h_{a,b}(y)$ exactly when
$\operatorname{val}(ax + b) \bmod m = \operatorname{val}(ay + b) \bmod m$. -/
public theorem modPrimeHash_eq_iff (p m : Nat) (hm : 0 < m) (a b x y : ZMod p) :
    modPrimeHash p m hm a b x = modPrimeHash p m hm a b y ↔
      (a * x + b).val % m = (a * y + b).val % m := by
  simp [Fin.ext_iff]

/--
**The pair map of the mod-prime family.** Let $p$ be a natural number and fix two keys
$x, y \in \mathbb{Z}/p\mathbb{Z}$. The pair map at $x$ and $y$ sends an index $(a, b)$ of the
mod-prime family, that is, $a, b \in \mathbb{Z}/p\mathbb{Z}$ with $a \ne 0$, to the pair
$(ax + b, ay + b) \in (\mathbb{Z}/p\mathbb{Z})^2$ of inner hash values at $x$ and $y$.

This is the map of the CLRS counting argument for the mod-prime family.
-/
public def pairMap {p : Nat} (x y : ZMod p) (ab : ModPrimeIndex p) : ZMod p × ZMod p :=
  (ab.1.1 * x + ab.2, ab.1.1 * y + ab.2)

/--
**Evaluating the pair map.** Let $p$ be a natural number, let $x, y \in \mathbb{Z}/p\mathbb{Z}$,
and let $(a, b)$ be an index of the mod-prime family, so that $a, b \in \mathbb{Z}/p\mathbb{Z}$
and $a \ne 0$. Then the pair map at $x$ and $y$ sends $(a, b)$ to $(ax + b, ay + b)$.
-/
@[simp]
public theorem pairMap_apply {p : Nat} (x y : ZMod p) (ab : ModPrimeIndex p) :
    pairMap x y ab = (ab.1.1 * x + ab.2, ab.1.1 * y + ab.2) :=
  rfl

/--
**The two values of the pair map differ.** Let $p$ be a prime and let $x \ne y$ be keys in the
field $\mathbb{Z}/p\mathbb{Z}$. For every index $(a, b)$ of the mod-prime family, that is,
$a, b \in \mathbb{Z}/p\mathbb{Z}$ with $a \ne 0$, we have $ax + b \ne ay + b$.

Indeed, the difference $(ax + b) - (ay + b) = a(x - y)$ is a product of two nonzero factors.
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
**Pair bijection of the CLRS counting argument.** Let $p$ be a prime and let $x \neq y$ be
elements of the field $\mathbb{Z}/p\mathbb{Z}$. The pair bijection for $x, y$ is the bijection
from the indices $(a, b)$, with $a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \neq 0$, to the ordered
pairs $(r, s)$ of elements of $\mathbb{Z}/p\mathbb{Z}$ with $r \neq s$ that sends $(a, b)$ to
the pair map value $(ax + b, ay + b)$. Its inverse solves the linear system $ax + b = r$,
$ay + b = s$: it sends $(r, s)$ to $(a, b)$ with $a = (r - s)/(x - y)$ and $b = r - ax$.
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

/-- **The pair bijection is given by the pair map.** Let $p$ be a prime and let $x \neq y$ be
elements of $\mathbb{Z}/p\mathbb{Z}$. For every index $(a, b)$ with
$a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \neq 0$, the image of $(a, b)$ under the pair bijection
for $x, y$, viewed as an element of $\mathbb{Z}/p\mathbb{Z} \times \mathbb{Z}/p\mathbb{Z}$, is the
value of the pair map at $(a, b)$, namely $(ax + b, ay + b)$. -/
@[simp]
public theorem pairEquiv_apply_fst {p : Nat} [Fact p.Prime] {x y : ZMod p}
    (hxy : x ≠ y) (ab : ModPrimeIndex p) :
    (pairEquiv hxy ab).1 = pairMap x y ab :=
  rfl

/--
**The pair map is injective.** Let $p$ be a prime and let $x \ne y$ be keys in
$\mathbb{Z}/p\mathbb{Z}$. Then the pair map at $x$ and $y$, which sends an index $(a, b)$ of the
mod-prime family (so $a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \ne 0$) to $(ax + b, ay + b)$,
is injective.
-/
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
**Collision bound for the mod-prime hash functions.** Let $p$ be a prime and $m > 0$, and
for $a, b \in \mathbb{Z}/p\mathbb{Z}$ with $a \ne 0$ let
$h_{a,b}(x) = ((ax + b) \bmod p) \bmod m$ be the mod-prime hash function. For distinct keys
$x \ne y$ in $\mathbb{Z}/p\mathbb{Z}$, the number of index pairs $(a, b)$ with $a \ne 0$ and
$h_{a,b}(x) = h_{a,b}(y)$, multiplied by $m$, is at most $p(p - 1)$, the total number of
index pairs.

This is the counting step of CLRS Theorem 11.5. The bijection
$(a, b) \mapsto (ax + b, ay + b)$ identifies the colliding index pairs with the pairs $(r, s)$
of distinct residues modulo $p$ whose representatives in $\{0, \dots, p - 1\}$ are congruent
modulo $m$.
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

/-- **Number of mod-prime indices.** For every positive natural number $p$, the set of pairs
$(a, b)$ of elements of $\mathbb{Z}/p\mathbb{Z}$ with $a \neq 0$ has exactly $p(p - 1)$
elements. -/
public theorem modPrimeIndex_card {p : Nat} [NeZero p] :
    Fintype.card (ModPrimeIndex p) = p * (p - 1) := by
  have hsub : Fintype.card { a : ZMod p // a ≠ 0 } = p - 1 := by
    rw [Fintype.card_subtype_compl (· = 0), Fintype.card_subtype_eq, ZMod.card]
  rw [Fintype.card_prod, hsub, ZMod.card, Nat.mul_comm]

/--
**Universality of the mod-prime family.** Let $p$ be a prime and $m$ a positive natural number.
The indexed mod-prime family, whose member at the index $(a, b)$, with
$a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \neq 0$, is the mod-prime hash function $h_{a,b}$, is
universal over the set of all such indices: this set is nonempty, and for all distinct keys
$x \neq y$ in $\mathbb{Z}/p\mathbb{Z}$, the number of indices $(a, b)$ with
$h_{a,b}(x) = h_{a,b}(y)$, multiplied by $m$, is at most the number of indices. This is CLRS
Theorem 11.5.

A uniformly random index therefore collides on any two distinct keys with probability at most
$1/m$.
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

/-- **Members of the mod-prime family.** Let $p > 0$ and $m > 0$. A function $h$ from
$\mathbb{Z}/p\mathbb{Z}$ to $\{0, 1, \dots, m - 1\}$ belongs to the mod-prime family of
distinct functions exactly when $h = h_{a,b}$ for some index $(a, b)$ with
$a, b \in \mathbb{Z}/p\mathbb{Z}$ and $a \ne 0$, where $h_{a,b}$ is the mod-prime hash
function with index $(a, b)$. -/
@[simp]
public theorem mem_modPrimeFamily {p m : Nat} [NeZero p] (hm : 0 < m)
    (h : ZMod p → Fin m) :
    h ∈ modPrimeFamily p m hm ↔ ∃ ab : ModPrimeIndex p, modPrimeHashes p m hm ab = h := by
  simp [modPrimeFamily]

end ModPrime

end Cslib.Algorithms.Lean.UniversalHashing
