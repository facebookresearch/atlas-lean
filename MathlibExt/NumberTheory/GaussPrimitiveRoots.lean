/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Gauss's theorem on the primitive roots modulo `p^ℓ`

Results from V. P. Ramesh and S. Sivakumar, "A Note on Gauss's
Theorem on the Primitive Roots Modulo `p^ℓ`", *INTEGERS* 26 (2026),
Article A111 (<https://math.colgate.edu/~integers/aa111/aa111.pdf>,
DOI 10.5281/zenodo.23216790).

Throughout, `p` is an odd prime. The paper's `ord_n(a)`, the order
of `a` in `(ℤ/nℤ)*`, is `mulOrdMod n a` below (defined as `0` when
`a` is not coprime to `n`, a case the paper never uses), and a
*primitive root* of `n` is a generator of `(ℤ/nℤ)*`, here
Mathlib's `IsPrimitiveRoot ((g : ZMod n)) (Nat.totient n)`, i.e.
by `IsPrimitiveRoot.iff_orderOf` a residue of maximal order
`φ(n)`. The paper's fiber `P_a = {x ∈ (ℤ/p²ℤ)* : x ≡ a (mod p)}`
is `liftFiber p a`, defined through the reduction homomorphism
`unitReduceSq p : (ZMod (p^2))ˣ →* (ZMod p)ˣ`.

The proofs rest on one observation: the kernel of `unitReduceSq p`
has `p` elements, so it has exponent `p`. Hence the order of
`x : (ZMod (p^2))ˣ` is that of its reduction, or `p` times it, and
it equals that of its reduction exactly when `x ^ (p - 1) = 1`.
Each fiber contains exactly one such element, namely `x₀ ^ p` for
any `x₀` in the fiber. For the lift to every `p^ℓ`, if
`h ^ (p - 1) = 1 + t p` with `p ∤ t`, then Mathlib's
`ZMod.orderOf_one_add_mul_prime` gives the order `p^(ℓ-1)` of
`h ^ (p - 1)` modulo `p^ℓ`.

Only Theorems 1 and 3 need `p ≠ 2`, since `(ZMod 8)ˣ` is not
cyclic; they get it through the lifting criterion
`isPrimitiveRoot_prime_pow`, which passes it to
`ZMod.orderOf_one_add_mul_prime`. Lemma 1, Theorem 2 and
Corollary 1 (both forms of each), Lemma 3 and Lemma 4 hold for
every prime `p`. They
keep the paper's hypothesis `p ≠ 2` for faithfulness: the proofs of
Lemma 1, Theorem 2 and Lemma 3 do not use it, and those of
Corollary 1 and Lemma 4 use it only to call Theorem 2 and Lemma 3.

Lemma 2 of the paper (a finite cyclic group of order `n` has
exactly `φ(ℓ)` elements of order `ℓ` for `ℓ ∣ n`) is already in
Mathlib as `IsCyclic.card_orderOf_eq_totient` and is not restated.
The sentence about Robbins (1975) following Corollary 1 in the
introduction is a narrative citation, not part of any numbered
statement, and is not formalized.

## Main results

* `order_add_mul_prime_eq_or_mul` (Lemma 1): `ord_{p²}(a + kp)` is
  `ord_p(a)` or `p · ord_p(a)`.
* `existsUnique_order_add_mul_prime_eq`,
  `existsUnique_mem_liftFiber_order_eq` (Theorem 2): each fiber has
  exactly one element whose order does not grow.
* `exists_primitiveRoot_add_mul_prime_pow` (Theorem 1, Gauss): a
  primitive root of `p` lifts to a primitive root of every `p^ℓ`.
* `existsUnique_not_primitiveRoot_add_mul_prime`,
  `existsUnique_mem_liftFiber_order_eq_sub_one` (Corollary 1).
* `primitiveRoot_pow_add_mul_prime_pow` (Theorem 3): `g^p + kp` is a
  primitive root of every `p^ℓ` when `p ∤ k`.
* `monoidHom_image_liftFiber_subset` (Lemma 3) and
  `pow_injectiveOn_liftFiber_and_order_eq` (Lemma 4).
* `isPrimitiveRoot_prime_pow`: the lifting criterion behind
  Theorems 1 and 3. A primitive root `h` of `p` with
  `h ^ (p - 1) ≢ 1 (mod p^2)` is a primitive root of every `p^ℓ`,
  `ℓ ≥ 2`.

## References

* V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem on the
  Primitive Roots Modulo `p^ℓ`", *INTEGERS* 26 (2026), Article A111.
* K. Ireland and M. Rosen, *A Classical Introduction to Modern
  Number Theory*, 2nd ed., Springer, 1990, chapter 4.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.GaussPrimitiveRoots

/-- The paper's `ord_n(a)`: the multiplicative order of the residue
class of `a` in `(ZMod n)ˣ`, and `0` when `a` is not coprime to
`n`. -/
noncomputable def mulOrdMod (n a : ℕ) : ℕ :=
  if h : Nat.Coprime a n then orderOf (ZMod.unitOfCoprime a h) else 0

/-- Reduction of units modulo `p^2` to units modulo `p`. -/
def unitReduceSq (p : ℕ) : (ZMod (p ^ 2))ˣ →* (ZMod p)ˣ :=
  Units.map (ZMod.castHom (⟨p, by ring⟩ : p ∣ p ^ 2) (ZMod p)).toMonoidHom

/-- The paper's fiber `P_a = {x ∈ (ℤ/p²ℤ)* : x ≡ a (mod p)}`. -/
def liftFiber (p : ℕ) (a : (ZMod (p ^ 2))ˣ) : Set (ZMod (p ^ 2))ˣ :=
  {x | unitReduceSq p x = unitReduceSq p a}

section Helpers

variable {p : ℕ} [hp : Fact p.Prime]

private theorem card_units_sq : Nat.card (ZMod (p ^ 2))ˣ = p * (p - 1) := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    show p ^ 2 = p ^ (1 + 1) from rfl, Nat.totient_prime_pow_succ hp.out,
    pow_one]

private theorem card_units_prime : Nat.card (ZMod p)ˣ = p - 1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units]

/-- The kernel of `unitReduceSq p` has exponent `p`. -/
private theorem pow_prime_eq_one_of_unitReduceSq_eq_one {z : (ZMod (p ^ 2))ˣ}
    (hz : unitReduceSq p z = 1) : z ^ p = 1 := by
  have hsurj : Function.Surjective (unitReduceSq p) :=
    ZMod.unitsMap_surjective (dvd_pow_self p two_ne_zero)
  have hcard : Nat.card (unitReduceSq p).ker = p := by
    have h := (unitReduceSq p).ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj] at h
    rw [Subgroup.card_top, card_units_prime, card_units_sq] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hp.out.one_lt) h
  have h := Subgroup.orderOf_dvd_natCard _ (MonoidHom.mem_ker.mpr hz)
  rw [hcard] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

private theorem unitReduceSq_pow_sub_one (x : (ZMod (p ^ 2))ˣ) :
    unitReduceSq p x ^ (p - 1) = 1 := by
  rw [← card_units_prime]
  exact pow_card_eq_one'

/-- **Lemma 1**, group form: the order of a unit modulo `p^2` is the
order of its reduction modulo `p`, or `p` times it. -/
private theorem orderOf_eq_or_eq_mul (x : (ZMod (p ^ 2))ˣ) :
    orderOf x = orderOf (unitReduceSq p x) ∨
      orderOf x = p * orderOf (unitReduceSq p x) := by
  obtain ⟨e, he⟩ := orderOf_map_dvd (unitReduceSq p) x
  have hdvd : orderOf x ∣ orderOf (unitReduceSq p x) * p := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_mul]
    refine pow_prime_eq_one_of_unitReduceSq_eq_one ?_
    rw [map_pow, pow_orderOf_eq_one]
  have hpos := orderOf_pos (unitReduceSq p x)
  rw [he, Nat.mul_dvd_mul_iff_left hpos, Nat.dvd_prime hp.out] at hdvd
  rcases hdvd with rfl | rfl
  · exact Or.inl (by rw [he, mul_one])
  · exact Or.inr (by rw [he, mul_comm])

/-- A unit modulo `p^2` has the order of its reduction exactly when
its `(p - 1)`-th power is `1`. -/
private theorem orderOf_eq_orderOf_unitReduceSq_iff (x : (ZMod (p ^ 2))ˣ) :
    orderOf x = orderOf (unitReduceSq p x) ↔ x ^ (p - 1) = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    rw [h, orderOf_dvd_iff_pow_eq_one]
    exact unitReduceSq_pow_sub_one x
  · intro h
    have hcop : (orderOf x).Coprime p :=
      Nat.Coprime.coprime_dvd_left h <|
        (Nat.coprime_self_sub_left hp.out.one_lt.le).mpr
          (Nat.coprime_one_left p)
    refine Nat.dvd_antisymm ?_ (orderOf_map_dvd (unitReduceSq p) x)
    rcases orderOf_eq_or_eq_mul x with hx | hx
    · exact dvd_of_eq hx
    · exact hcop.dvd_mul_left.mp (dvd_of_eq hx)

/-- Two units in the same fiber whose `(p - 1)`-th powers are `1` are
equal. -/
private theorem eq_of_unitReduceSq_eq {x y : (ZMod (p ^ 2))ˣ}
    (hxy : unitReduceSq p x = unitReduceSq p y) (hx : x ^ (p - 1) = 1)
    (hy : y ^ (p - 1) = 1) : x = y := by
  have hz : unitReduceSq p (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hzp := pow_prime_eq_one_of_unitReduceSq_eq_one hz
  have hz1 : (x * y⁻¹) ^ (p - 1) = 1 := by
    rw [mul_pow, inv_pow, hx, hy, inv_one, one_mul]
  have h : x * y⁻¹ = 1 := by
    rwa [← pow_sub_one_mul hp.out.ne_zero, hz1, one_mul] at hzp
  exact mul_inv_eq_one.mp h

/-- `x ^ p` lies in the fiber of `x` and has `(x ^ p) ^ (p - 1) = 1`. -/
private theorem unitReduceSq_pow_prime (x : (ZMod (p ^ 2))ˣ) :
    unitReduceSq p (x ^ p) = unitReduceSq p x ∧ (x ^ p) ^ (p - 1) = 1 := by
  constructor
  · rw [map_pow, ← pow_sub_one_mul hp.out.ne_zero, unitReduceSq_pow_sub_one,
      one_mul]
  · rw [← pow_mul, ← card_units_sq]
    exact pow_card_eq_one'

private theorem eq_one_of_unitReduceSq_pow_prime {x : (ZMod (p ^ 2))ˣ}
    (hx : unitReduceSq p x ^ p = 1) : unitReduceSq p x = 1 := by
  rwa [← pow_sub_one_mul hp.out.ne_zero, unitReduceSq_pow_sub_one,
    one_mul] at hx

/-- An order bound: `ord_{p²}(x) ∣ p · ord_p(x)`. -/
private theorem orderOf_dvd_mul (x : (ZMod (p ^ 2))ˣ) :
    orderOf x ∣ p * orderOf (unitReduceSq p x) := by
  rcases orderOf_eq_or_eq_mul x with hx | hx
  · exact hx ▸ dvd_mul_left _ p
  · exact dvd_of_eq hx

private theorem unitReduceSq_unitOfCoprime {n : ℕ} (h : n.Coprime (p ^ 2))
    (h' : n.Coprime p) :
    unitReduceSq p (ZMod.unitOfCoprime n h) = ZMod.unitOfCoprime n h' := by
  ext
  simp only [unitReduceSq, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, ZMod.coe_unitOfCoprime, ZMod.castHom_apply,
    ZMod.cast_natCast (dvd_pow_self p two_ne_zero)]

private theorem natCast_add_mul_prime (a k : ℕ) :
    ((a + k * p : ℕ) : ZMod p) = a := by
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]

omit hp in
private theorem coprime_add_mul_sq {a : ℕ} (ha : a.Coprime p) (k : ℕ) :
    (a + k * p).Coprime (p ^ 2) :=
  ((Nat.coprime_add_mul_right_left a p k).mpr ha).pow_right 2

private theorem unitReduceSq_unitOfCoprime_add_mul {a : ℕ} (ha : a.Coprime p)
    (k : ℕ) :
    unitReduceSq p (ZMod.unitOfCoprime (a + k * p) (coprime_add_mul_sq ha k)) =
      ZMod.unitOfCoprime a ha := by
  rw [unitReduceSq_unitOfCoprime _
    ((Nat.coprime_add_mul_right_left a p k).mpr ha)]
  ext
  simp only [ZMod.coe_unitOfCoprime, natCast_add_mul_prime]

private theorem mulOrdMod_eq {n a : ℕ} (h : a.Coprime n) :
    mulOrdMod n a = orderOf (ZMod.unitOfCoprime a h) :=
  dite_eq_left h

private theorem isPrimitiveRoot_natCast_iff {n N k : ℕ} (h : n.Coprime N) :
    IsPrimitiveRoot (n : ZMod N) k ↔ orderOf (ZMod.unitOfCoprime n h) = k := by
  rw [IsPrimitiveRoot.iff_orderOf, ← ZMod.coe_unitOfCoprime n h, orderOf_units]

private theorem unitOfCoprime_pow_eq_one_iff {n N k : ℕ} (h : n.Coprime N) :
    ZMod.unitOfCoprime n h ^ k = 1 ↔ (n : ZMod N) ^ k = 1 := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    Units.val_one]

/-- The order of `a + kp` modulo `p^2` equals that of `a` modulo `p`
exactly when `(a + kp) ^ (p - 1) ≡ 1 (mod p^2)`. -/
private theorem mulOrdMod_add_mul_eq_iff {a : ℕ} (ha : a.Coprime p) (k : ℕ) :
    mulOrdMod (p ^ 2) (a + k * p) = mulOrdMod p a ↔
      ((a + k * p : ℕ) : ZMod (p ^ 2)) ^ (p - 1) = 1 := by
  rw [mulOrdMod_eq (coprime_add_mul_sq ha k), mulOrdMod_eq ha,
    ← unitReduceSq_unitOfCoprime_add_mul ha k,
    orderOf_eq_orderOf_unitReduceSq_iff, unitOfCoprime_pow_eq_one_iff]

/-- If `a ^ (p - 1)` and `(a + kp) ^ (p - 1)` are both `1` modulo
`p^2`, then `p ∣ k`. -/
private theorem dvd_of_pow_sub_one_eq_one {a k : ℕ} (ha : a.Coprime p)
    (hk : ((a + k * p : ℕ) : ZMod (p ^ 2)) ^ (p - 1) = 1)
    (h0 : (a : ZMod (p ^ 2)) ^ (p - 1) = 1) : p ∣ k := by
  have h0' : ((a + 0 * p : ℕ) : ZMod (p ^ 2)) ^ (p - 1) = 1 := by
    rwa [zero_mul, add_zero]
  have h := eq_of_unitReduceSq_eq
    ((unitReduceSq_unitOfCoprime_add_mul ha k).trans
      (unitReduceSq_unitOfCoprime_add_mul ha 0).symm)
    ((unitOfCoprime_pow_eq_one_iff _).mpr hk)
    ((unitOfCoprime_pow_eq_one_iff _).mpr h0')
  rw [Units.ext_iff, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, zero_mul,
    add_zero, Nat.cast_add, add_eq_left, ZMod.natCast_eq_zero_iff, sq] at h
  exact Nat.dvd_of_mul_dvd_mul_right hp.out.pos h

/-- Every element of the fiber of `a` is `a + mp` for some `m` modulo `p`. -/
private theorem exists_natCast_add_val_mul_eq {a : ℕ} (ha : a.Coprime p)
    {y : (ZMod (p ^ 2))ˣ} (hy : unitReduceSq p y = ZMod.unitOfCoprime a ha) :
    ∃ m : ZMod p, ((a + m.val * p : ℕ) : ZMod (p ^ 2)) = y := by
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  set z := (y : ZMod (p ^ 2)) - a with hz
  have hz0 : ((z.val : ℕ) : ZMod p) = 0 := by
    have hy' := congrArg Units.val hy
    simp only [unitReduceSq, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, ZMod.castHom_apply, ZMod.coe_unitOfCoprime] at hy'
    rw [ZMod.natCast_val, hz, ZMod.cast_sub hdvd, hy',
      ZMod.cast_natCast hdvd, sub_self]
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hz0
  have htp : t < p := by
    have := z.val_lt
    rw [ht, sq] at this
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨t, ?_⟩
  rw [ZMod.val_cast_of_lt htp, mul_comm t p, ← ht, Nat.cast_add,
    ZMod.natCast_zmod_val, hz, add_sub_cancel]

private theorem eq_of_natCast_add_val_mul_eq {a : ℕ} {m m' : ZMod p}
    (h : ((a + m.val * p : ℕ) : ZMod (p ^ 2)) = ((a + m'.val * p : ℕ))) :
    m = m' := by
  have hlt : ∀ m : ZMod p, m.val * p < p ^ 2 := fun m => by
    rw [sq]
    exact Nat.mul_lt_mul_of_pos_right m.val_lt hp.out.pos
  rw [Nat.cast_add, Nat.cast_add, add_right_inj, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt (hlt m), Nat.mod_eq_of_lt (hlt m')] at h
  exact ZMod.val_injective p (Nat.eq_of_mul_eq_mul_right hp.out.pos h)

/-- For a unit whose reduction has order `p - 1`, having the maximal
order `φ(p²)` is the same as having an order different from that of
the reduction. -/
private theorem orderOf_eq_totient_sq_iff {x : (ZMod (p ^ 2))ˣ}
    (hx : orderOf (unitReduceSq p x) = p - 1) :
    orderOf x = Nat.totient (p ^ 2) ↔
      orderOf x ≠ orderOf (unitReduceSq p x) := by
  have hne : p * (p - 1) ≠ p - 1 := fun h =>
    hp.out.one_lt.ne' (Nat.eq_of_mul_eq_mul_right
      (Nat.sub_pos_of_lt hp.out.one_lt) (h.trans (one_mul _).symm))
  rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card, card_units_sq,
    hx]
  rcases orderOf_eq_or_eq_mul x with h | h <;> rw [hx] at h <;> rw [h]
  · exact iff_of_false hne.symm (not_not.mpr rfl)
  · exact iff_of_true rfl hne

/-- The lifting criterion in the form used inside the proofs, with
`p - 1` for `φ(p)`; see `isPrimitiveRoot_prime_pow`. -/
private theorem isPrimitiveRoot_prime_pow_aux (hpo : p ≠ 2) {h : ℕ}
    (hh : IsPrimitiveRoot (h : ZMod p) (p - 1))
    (hne : (h : ZMod (p ^ 2)) ^ (p - 1) ≠ 1) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    IsPrimitiveRoot (h : ZMod (p ^ ℓ)) (Nat.totient (p ^ ℓ)) := by
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.out.one_lt
  obtain ⟨t, ht⟩ : (p : ℤ) ∣ (h : ℤ) ^ (p - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_pow,
      Int.cast_natCast, Int.cast_one,
      ZMod.pow_card_sub_one_eq_one (hh.ne_zero hp1), sub_self]
  have key : ∀ n : ℕ, (h : ZMod (p ^ n)) ^ (p - 1) = 1 + p * t := by
    intro n
    have e := congrArg (Int.cast : ℤ → ZMod (p ^ n)) (eq_add_of_sub_eq' ht)
    rwa [Int.cast_pow, Int.cast_natCast, Int.cast_add, Int.cast_one,
      Int.cast_mul, Int.cast_natCast] at e
  have htp : ¬ (p : ℤ) ∣ t := by
    rintro ⟨s, rfl⟩
    apply hne
    rw [key 2, Int.cast_mul, Int.cast_natCast, ← mul_assoc, ← sq,
      ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
  have hn : orderOf ((h : ZMod (p ^ (n + 1))) ^ (p - 1)) = p ^ n := by
    rw [key, ZMod.orderOf_one_add_mul_prime hp.out hpo t htp n]
  have hdvd : p - 1 ∣ orderOf (h : ZMod (p ^ (n + 1))) := by
    have := orderOf_map_dvd
      (ZMod.castHom (dvd_pow_self p n.succ_ne_zero) (ZMod p)).toMonoidHom
      (h : ZMod (p ^ (n + 1)))
    rwa [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_natCast,
      ← hh.eq_orderOf] at this
  rw [orderOf_pow_of_dvd hp1 hdvd] at hn
  rw [IsPrimitiveRoot.iff_orderOf, Nat.totient_prime_pow_succ hp.out, ← hn,
    Nat.div_mul_cancel hdvd]

end Helpers

/-- **Lifting criterion**: if `g` is a primitive root of the odd
prime `p` and `g ^ (p - 1) ≢ 1 (mod p^2)`, then `g` is a primitive
root of `p^ℓ` for every `ℓ ≥ 2`. This is the common step of
Theorems 1 and 3.

The hypothesis `p ≠ 2` is necessary: `3` is a primitive root of `2`
and `3 ≢ 1 (mod 4)`, but `3` is not a primitive root of `8`, since
`(ZMod 8)ˣ` is not cyclic. -/
theorem isPrimitiveRoot_prime_pow
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p))
    (hne : (g : ZMod (p ^ 2)) ^ (p - 1) ≠ 1) :
    ∀ ℓ : ℕ, 2 ≤ ℓ →
      IsPrimitiveRoot ((g : ZMod (p ^ ℓ))) (Nat.totient (p ^ ℓ)) := by
  have := Fact.mk hp
  rw [Nat.totient_prime hp] at hg
  exact fun ℓ hℓ => isPrimitiveRoot_prime_pow_aux hpo hg hne hℓ

set_option linter.unusedVariables false in
/-- **Lemma 1**: for `a` coprime to the odd prime `p` and any `k`,
`ord_{p²}(a + kp) = ord_p(a)` or `p · ord_p(a)`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Lemma 1.
Proves `Wanted` entry `order_add_mul_prime_eq_or_mul`. -/
theorem order_add_mul_prime_eq_or_mul
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (a k : ℕ)
    (ha : Nat.Coprime a p) :
    mulOrdMod (p ^ 2) (a + k * p) = mulOrdMod p a ∨
      mulOrdMod (p ^ 2) (a + k * p) = p * mulOrdMod p a := by
  have := Fact.mk hp
  rw [mulOrdMod_eq (coprime_add_mul_sq ha k), mulOrdMod_eq ha,
    ← unitReduceSq_unitOfCoprime_add_mul ha k]
  exact orderOf_eq_or_eq_mul _

set_option linter.unusedVariables false in
/-- **Theorem 2**: for `a` coprime to the odd prime `p`, there
exists a unique `m` modulo `p` such that
`ord_{p²}(a + mp) = ord_p(a)`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 2.
Proves `Wanted` entry `existsUnique_order_add_mul_prime_eq`. -/
theorem existsUnique_order_add_mul_prime_eq
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (a : ℕ)
    (ha : Nat.Coprime a p) :
    ∃! m : ZMod p, mulOrdMod (p ^ 2) (a + m.val * p) = mulOrdMod p a := by
  have := Fact.mk hp
  set x₀ := ZMod.unitOfCoprime a (ha.pow_right 2)
  have hx₀ : unitReduceSq p (x₀ ^ p) = ZMod.unitOfCoprime a ha := by
    rw [(unitReduceSq_pow_prime x₀).1, unitReduceSq_unitOfCoprime]
  obtain ⟨m, hm⟩ := exists_natCast_add_val_mul_eq ha hx₀
  refine ⟨m, ?_, fun m' hm' => ?_⟩
  · beta_reduce
    rw [mulOrdMod_add_mul_eq_iff ha, hm, ← Units.val_pow_eq_pow_val,
      (unitReduceSq_pow_prime x₀).2, Units.val_one]
  · beta_reduce at hm'
    rw [mulOrdMod_add_mul_eq_iff ha] at hm'
    have h := eq_of_unitReduceSq_eq
      ((unitReduceSq_unitOfCoprime_add_mul ha m'.val).trans hx₀.symm)
      ((unitOfCoprime_pow_eq_one_iff _).mpr hm') (unitReduceSq_pow_prime x₀).2
    rw [Units.ext_iff, ZMod.coe_unitOfCoprime, ← hm] at h
    exact eq_of_natCast_add_val_mul_eq h

set_option linter.unusedVariables false in
/-- **Theorem 2**, fiber form: for every `P_a` there exists a
unique `x ∈ P_a` such that `ord_{p²}(x) = ord_p(x)`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 2.
Proves `Wanted` entry `existsUnique_mem_liftFiber_order_eq`. -/
theorem existsUnique_mem_liftFiber_order_eq
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (x₀ : (ZMod (p ^ 2))ˣ) :
    ∃! x, x ∈ liftFiber p x₀ ∧ orderOf x = orderOf (unitReduceSq p x) := by
  have := Fact.mk hp
  obtain ⟨hfib, hpow⟩ := unitReduceSq_pow_prime x₀
  refine ⟨x₀ ^ p, ⟨hfib, (orderOf_eq_orderOf_unitReduceSq_iff _).mpr hpow⟩, ?_⟩
  rintro y ⟨hy, hyo⟩
  exact eq_of_unitReduceSq_eq (hy.trans hfib.symm)
    ((orderOf_eq_orderOf_unitReduceSq_iff y).mp hyo) hpow

/-- **Theorem 1** (Gauss): if `g` is a primitive root of the odd
prime `p`, then there exists `k` such that `g + kp` is a primitive
root of `p^ℓ` for all `ℓ ≥ 2`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 1.
Proves `Wanted` entry `exists_primitiveRoot_add_mul_prime_pow`. -/
theorem exists_primitiveRoot_add_mul_prime_pow
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p)) :
    ∃ k : ℕ, ∀ ℓ : ℕ, 2 ≤ ℓ →
      IsPrimitiveRoot (((g + k * p : ℕ) : ZMod (p ^ ℓ)))
        (Nat.totient (p ^ ℓ)) := by
  have := Fact.mk hp
  rw [Nat.totient_prime hp] at hg
  have hg' : g.Coprime p := (ZMod.isUnit_iff_coprime g p).mp
    (hg.isUnit (Nat.sub_ne_zero_of_lt hp.one_lt))
  have hh : ∀ k : ℕ, IsPrimitiveRoot (((g + k * p : ℕ) : ZMod p)) (p - 1) :=
    fun k => by rwa [natCast_add_mul_prime]
  by_cases h0 : (g : ZMod (p ^ 2)) ^ (p - 1) = 1
  · refine ⟨1, fun ℓ hℓ => isPrimitiveRoot_prime_pow_aux hpo (hh 1) ?_ hℓ⟩
    exact fun h1 => hp.not_dvd_one (dvd_of_pow_sub_one_eq_one hg' h1 h0)
  · refine ⟨0, fun ℓ hℓ => isPrimitiveRoot_prime_pow_aux hpo (hh 0) ?_ hℓ⟩
    rwa [zero_mul, add_zero]

/-- **Corollary 1**: if `g` is a primitive root of the odd prime
`p`, then there exists a unique `m` modulo `p` such that `g + mp`
is not a primitive root of `p²`, and `g + kp` is a primitive root
of `p²` for every other `k` modulo `p`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Corollary 1.
Proves `Wanted` entry `existsUnique_not_primitiveRoot_add_mul_prime`. -/
theorem existsUnique_not_primitiveRoot_add_mul_prime
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p)) :
    ∃! m : ZMod p,
      ¬ IsPrimitiveRoot (((g + m.val * p : ℕ) : ZMod (p ^ 2)))
          (Nat.totient (p ^ 2)) ∧
        ∀ k : ZMod p, k ≠ m →
          IsPrimitiveRoot (((g + k.val * p : ℕ) : ZMod (p ^ 2)))
            (Nat.totient (p ^ 2)) := by
  have := Fact.mk hp
  rw [Nat.totient_prime hp] at hg
  have hg' : g.Coprime p := (ZMod.isUnit_iff_coprime g p).mp
    (hg.isUnit (Nat.sub_ne_zero_of_lt hp.one_lt))
  have hprim : ∀ k : ZMod p,
      IsPrimitiveRoot (((g + k.val * p : ℕ) : ZMod (p ^ 2)))
          (Nat.totient (p ^ 2)) ↔
        mulOrdMod (p ^ 2) (g + k.val * p) ≠ mulOrdMod p g := by
    intro k
    rw [isPrimitiveRoot_natCast_iff (coprime_add_mul_sq hg' _),
      mulOrdMod_eq (coprime_add_mul_sq hg' _), mulOrdMod_eq hg',
      ← unitReduceSq_unitOfCoprime_add_mul hg' k.val]
    refine orderOf_eq_totient_sq_iff ?_
    rw [unitReduceSq_unitOfCoprime_add_mul]
    exact (isPrimitiveRoot_natCast_iff hg').mp hg
  obtain ⟨m, hm, huniq⟩ := existsUnique_order_add_mul_prime_eq p hp hpo g hg'
  refine ⟨m, ⟨fun h => (hprim m).mp h hm, fun k hk => (hprim k).mpr
    fun h => hk (huniq k h)⟩, fun m' hm' => huniq m' ?_⟩
  by_contra h
  exact hm'.1 ((hprim m').mpr h)

/-- **Corollary 1**, fiber form: if `g` is a primitive root of the
odd prime `p`, then there exists a unique `x ∈ P_g` such that
`ord_{p²}(x) = p - 1`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Corollary 1.
Proves `Wanted` entry `existsUnique_mem_liftFiber_order_eq_sub_one`. -/
theorem existsUnique_mem_liftFiber_order_eq_sub_one
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p)) :
    ∃! x, x ∈ liftFiber p (ZMod.unitOfCoprime g
        (((ZMod.isUnit_iff_coprime g p).mp
          (hg.isUnit (Nat.totient_pos.mpr hp.pos).ne')).pow_right 2)) ∧
      orderOf x = p - 1 := by
  have := Fact.mk hp
  have hg' : g.Coprime p := (ZMod.isUnit_iff_coprime g p).mp
    (hg.isUnit (Nat.totient_pos.mpr hp.pos).ne')
  have hord : orderOf (ZMod.unitOfCoprime g hg') = p - 1 := by
    rw [← Nat.totient_prime hp]
    exact (isPrimitiveRoot_natCast_iff hg').mp hg
  refine (existsUnique_congr fun x => and_congr_right fun hx => ?_).mp
    (existsUnique_mem_liftFiber_order_eq p hp hpo _)
  rw [hx, unitReduceSq_unitOfCoprime _ hg', hord]

/-- **Theorem 3**: if `g` is a primitive root of the odd prime `p`
and `k ≢ 0 (mod p)`, then `g^p + kp` is a primitive root of `p^ℓ`
for all `ℓ > 1`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Theorem 3.
Proves `Wanted` entry `primitiveRoot_pow_add_mul_prime_pow`. -/
theorem primitiveRoot_pow_add_mul_prime_pow
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (g k : ℕ)
    (hg : IsPrimitiveRoot ((g : ZMod p)) (Nat.totient p))
    (hk : ¬ p ∣ k) :
    ∀ ℓ : ℕ, 1 < ℓ →
      IsPrimitiveRoot (((g ^ p + k * p : ℕ) : ZMod (p ^ ℓ)))
        (Nat.totient (p ^ ℓ)) := by
  have := Fact.mk hp
  rw [Nat.totient_prime hp] at hg
  have hg' : g.Coprime p := (ZMod.isUnit_iff_coprime g p).mp
    (hg.isUnit (Nat.sub_ne_zero_of_lt hp.one_lt))
  intro ℓ hℓ
  refine isPrimitiveRoot_prime_pow_aux hpo ?_ ?_ hℓ
  · rwa [natCast_add_mul_prime, Nat.cast_pow, ZMod.pow_card]
  · refine fun hk' => hk (dvd_of_pow_sub_one_eq_one (hg'.pow_left p) hk' ?_)
    have hu := (unitReduceSq_pow_prime
      (ZMod.unitOfCoprime g (hg'.pow_right 2))).2
    rw [← pow_mul, unitOfCoprime_pow_eq_one_iff] at hu
    rwa [Nat.cast_pow, ← pow_mul]

set_option linter.unusedVariables false in
/-- **Lemma 3**: for any endomorphism `f` of `(ZMod (p^2))ˣ` and
any `a`, `f '' P_a ⊆ P_{f a}`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Lemma 3.
Proves `Wanted` entry `monoidHom_image_liftFiber_subset`. -/
theorem monoidHom_image_liftFiber_subset
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2)
    (f : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ) (a : (ZMod (p ^ 2))ˣ) :
    f '' liftFiber p a ⊆ liftFiber p (f a) := by
  have := Fact.mk hp
  rintro _ ⟨x, hx, rfl⟩
  have hz : unitReduceSq p (x * a⁻¹) = 1 := by
    rw [map_mul, map_inv, hx, mul_inv_cancel]
  have h1 : unitReduceSq p (f (x * a⁻¹)) = 1 := by
    refine eq_one_of_unitReduceSq_pow_prime ?_
    rw [← map_pow, ← map_pow, pow_prime_eq_one_of_unitReduceSq_eq_one hz,
      map_one, map_one]
  change unitReduceSq p (f x) = unitReduceSq p (f a)
  rw [← inv_mul_cancel_right x a, map_mul f, map_mul, h1, one_mul]

/-- **Lemma 4**: for `n` coprime to both the odd prime `p` and
`ord_{p²}(a)`, the power map `x ↦ x^n` is injective on `P_a`,
maps `P_a` onto `P_{a^n}`, and preserves the order of every
element of `P_a`.

Source: V. P. Ramesh and S. Sivakumar, "A Note on Gauss's Theorem
on the Primitive Roots Modulo `p^ℓ`", Lemma 4.
Proves `Wanted` entry `pow_injectiveOn_liftFiber_and_order_eq`. -/
theorem pow_injectiveOn_liftFiber_and_order_eq
    (p : ℕ) (hp : p.Prime) (hpo : p ≠ 2) (a : (ZMod (p ^ 2))ˣ)
    (n : ℕ) (hnp : Nat.Coprime n p) (hno : Nat.Coprime n (orderOf a)) :
    Set.InjOn (fun x => x ^ n) (liftFiber p a) ∧
      (fun x => x ^ n) '' liftFiber p a = liftFiber p (a ^ n) ∧
      ∀ b ∈ liftFiber p a, orderOf (b ^ n) = orderOf b := by
  have := Fact.mk hp
  refine ⟨fun x hx y hy hxy => ?_, ?_, fun b hb => ?_⟩
  · have hz : unitReduceSq p (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, show unitReduceSq p x = unitReduceSq p y from
        hx.trans hy.symm, mul_inv_cancel]
    have hzn : (x * y⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, show x ^ n = y ^ n from hxy, mul_inv_cancel]
    have h := pow_gcd_eq_one.mpr
      ⟨hzn, pow_prime_eq_one_of_unitReduceSq_eq_one hz⟩
    rw [hnp.gcd_eq_one, pow_one] at h
    exact mul_inv_eq_one.mp h
  · refine (monoidHom_image_liftFiber_subset p hp hpo (powMonoidHom n)
      a).antisymm fun y hy => ?_
    set z := (a ^ n)⁻¹ * y
    have hz : unitReduceSq p z = 1 := by
      rw [map_mul, map_inv,
        show unitReduceSq p y = unitReduceSq p (a ^ n) from hy, inv_mul_cancel]
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := z) <|
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one
        (pow_prime_eq_one_of_unitReduceSq_eq_one hz)) hnp
    refine ⟨a * z ^ m, ?_, ?_⟩
    · change unitReduceSq p (a * z ^ m) = unitReduceSq p a
      rw [map_mul, map_pow, hz, one_pow, mul_one]
    · change (a * z ^ m) ^ n = y
      rw [mul_pow, pow_right_comm, hm, mul_inv_cancel_left]
  · have hdvd := orderOf_dvd_mul b
    rw [show unitReduceSq p b = unitReduceSq p a from hb] at hdvd
    exact Nat.Coprime.orderOf_pow (Nat.Coprime.symm
      (Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.mul_right hnp
        (Nat.Coprime.coprime_dvd_right (orderOf_map_dvd _ a) hno))))

end MathlibExt.NumberTheory.GaussPrimitiveRoots
