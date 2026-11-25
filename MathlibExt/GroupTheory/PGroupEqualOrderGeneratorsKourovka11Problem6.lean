/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Generating sets of equal orders in p-groups (Kourovka Notebook Problem 11.6)

Kourovka Notebook, Archive of Solved Problems, Problem 11.6 (C. Bagiński): let `p` be an odd prime.
Does every finite `p`-group have a set of generators of equal orders?

The main result, `pGroupEqualOrderGenerators_refuted`, answers this in the negative: it gives a
group of order `3 ^ 17` and exponent `81` none of whose generating sets consists of elements of
equal order.

The construction is elementary and self-contained; it does not rely on the paper cited below. For
`k ≥ 1` let `B_k = (ZMod (3 ^ (k + 1)))²`, read as `ℤ[ω] / 3 ^ (k + 1)` in the basis `1, ω - 1`,
where `ω` is a primitive cube root of unity, and let `ℤ/3` act on `B_k` through multiplication by
`ω`. In `B_k ⋊ ℤ/3` every element outside `B_k` has order `3`, because `1 + ω + ω² = 0`, while an
element of `B_k` whose first coordinate is a unit has order `3 ^ (k + 1)`. Let `s` be the first
coordinate of the `B_k`-part reduced modulo `3` and `t` the `ℤ/3`-part; both are homomorphisms to
`ℤ/3`. The group is the subgroup of `(B_1 ⋊ ℤ/3) × (B_2 ⋊ ℤ/3) × (B_3 ⋊ ℤ/3)` of the triples
with a common `s` whose `t`-coordinates are `t`, `t - s` and `t - 2 s`. Over a nonzero vector
`(s, t)` of `(ℤ/3)²` its elements have order `3` if `s = 0`, and order `3 ^ (λ + 2)` if `s ≠ 0`
and `t = λ s` with `λ ∈ {0, 1, 2}`: then exactly the component in `B_{λ+1} ⋊ ℤ/3` lies in
`B_{λ+1}`. A generating set maps onto a spanning set of `(ℤ/3)²`, so it contains elements over two
different lines, and these have different orders.

The exponent `81 = 3 ^ (3 + 1)` is the least possible for `p = 3`. A finite `p`-group is not a
union of `p` proper subgroups, while in a counterexample the elements of each order lie in a proper
subgroup; so a counterexample has elements of at least `p + 1` orders `p ^ i` with `i ≥ 1`, and
exponent at least `p ^ (p + 1)`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupEqualOrderGeneratorsKourovka11Problem6Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.6 (C.
Bagiński). UnsolvedMath record UM-00700699 (`KOU-11.6`), dataset ulamai/UnsolvedMath v1.8.0.

The prime is universally quantified over odd primes, so the refutation asserts a counterexample for
some odd prime. A generating set is any subset `S` with `closure S = ⊤` whose elements all have the
same order.
-/

/-- **Generating sets of equal order in finite p-groups (Kourovka 11.6).** The statement that for
every odd prime $p$, every finite $p$-group $G$ has a generating set $S$ all of whose elements have
the same order. -/
def pGroupEqualOrderGenerators : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∃ S : Set G, Subgroup.closure S = ⊤ ∧ ∃ m : ℕ, ∀ x ∈ S, orderOf x = m

namespace Counterexample

open Multiplicative

/-! ### The factors `(ZMod (3 ^ (k + 1)))² ⋊ ℤ/3` -/

/-- Multiplication by a primitive cube root of unity `ω` on `ℤ[ω] / n`, written in the basis
`1, ω - 1`: `ω (x + y (ω - 1)) = (x - 3 y) + (x - 2 y) (ω - 1)`. -/
private def mulOmega (n : ℕ) : ZMod n × ZMod n ≃+ ZMod n × ZMod n where
  toFun v := (v.1 - 3 * v.2, v.1 - 2 * v.2)
  invFun v := (-2 * v.1 + 3 * v.2, -v.1 + v.2)
  left_inv v := by ext <;> simp <;> ring
  right_inv v := by ext <;> simp <;> ring
  map_add' v w := by ext <;> simp <;> ring

/-- Multiplication by `ω` as an automorphism of the multiplicative group. -/
private def omegaAut (n : ℕ) : MulAut (Multiplicative (ZMod n × ZMod n)) :=
  AddEquiv.toMultiplicative (mulOmega n)

private lemma omegaAut_apply (n : ℕ) (v : Multiplicative (ZMod n × ZMod n)) :
    omegaAut n v = ofAdd ((toAdd v).1 - 3 * (toAdd v).2, (toAdd v).1 - 2 * (toAdd v).2) :=
  rfl

private lemma omegaAut_pow_three (n : ℕ) : omegaAut n ^ 3 = 1 := by
  ext v
  · simp [pow_succ, omegaAut_apply]
    ring
  · simp [pow_succ, omegaAut_apply]
    ring

/-- The norm `1 + ω + ω²` vanishes. -/
private lemma mul_omegaAut_mul_omegaAut_sq (n : ℕ) (v : Multiplicative (ZMod n × ZMod n)) :
    v * omegaAut n v * (omegaAut n ^ 2) v = 1 := by
  apply toAdd.injective
  ext <;> simp [pow_two, omegaAut_apply] <;> ring

/-- The action of `ℤ/3` on `ℤ[ω] / n` through multiplication by `ω`. -/
private def omegaAction (n : ℕ) :
    Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod n × ZMod n)) where
  toFun j := omegaAut n ^ (toAdd j).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ (omegaAut_pow_three n)]

private lemma omegaAction_apply (n : ℕ) (j : Multiplicative (ZMod 3))
    (v : Multiplicative (ZMod n × ZMod n)) :
    omegaAction n j v = (omegaAut n ^ (toAdd j).val) v :=
  rfl

private lemma omegaAction_ofAdd_one (n : ℕ) : omegaAction n (ofAdd 1) = omegaAut n := by
  change omegaAut n ^ (1 : ZMod 3).val = omegaAut n
  rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]

private lemma omegaAction_ofAdd_two (n : ℕ) : omegaAction n (ofAdd 2) = omegaAut n ^ 2 := by
  ext1 v
  rw [omegaAction_apply]
  rfl

/-- The factor `(ZMod (3 ^ (k + 1)))² ⋊ ℤ/3`, with `ℤ/3` acting by multiplication by `ω`. -/
private abbrev Factor (k : ℕ) :=
  Multiplicative (ZMod (3 ^ (k + 1)) × ZMod (3 ^ (k + 1))) ⋊[omegaAction (3 ^ (k + 1))]
    Multiplicative (ZMod 3)

private instance instFiniteFactor (k : ℕ) : Finite (Factor k) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

variable {k : ℕ}

/-- Reduction modulo `3`. -/
private def reduce (k : ℕ) : ZMod (3 ^ (k + 1)) →+* ZMod 3 :=
  ZMod.castHom (dvd_pow_self 3 k.succ_ne_zero) (ZMod 3)

private lemma reduce_three : reduce k 3 = 0 := by
  rw [map_ofNat]
  rfl

/-- The coordinate `t` of an element of a factor: its image in `ℤ/3`. -/
private def tCoord (x : Factor k) : ZMod 3 := toAdd x.right

/-- The coordinate `s` of an element of a factor: the first coordinate of its normal part,
reduced modulo `3`. -/
private def sCoord (x : Factor k) : ZMod 3 := reduce k (toAdd x.left).1

private lemma reduce_omegaAut (w : Multiplicative (ZMod (3 ^ (k + 1)) × ZMod (3 ^ (k + 1)))) :
    reduce k (toAdd (omegaAut (3 ^ (k + 1)) w)).1 = reduce k (toAdd w).1 := by
  rw [omegaAut_apply, toAdd_ofAdd, map_sub, map_mul, reduce_three, zero_mul, sub_zero]

private lemma reduce_omegaAction (j : Multiplicative (ZMod 3))
    (v : Multiplicative (ZMod (3 ^ (k + 1)) × ZMod (3 ^ (k + 1)))) :
    reduce k (toAdd (omegaAction (3 ^ (k + 1)) j v)).1 = reduce k (toAdd v).1 := by
  rw [omegaAction_apply]
  induction (toAdd j).val with
  | zero => simp
  | succ m ih =>
    rw [pow_succ' (omegaAut (3 ^ (k + 1))) m, MulAut.mul_apply, reduce_omegaAut, ih]

private lemma tCoord_mul (x y : Factor k) : tCoord (x * y) = tCoord x + tCoord y := by
  simp [tCoord]

private lemma sCoord_mul (x y : Factor k) : sCoord (x * y) = sCoord x + sCoord y := by
  simp only [sCoord, SemidirectProduct.mul_left, toAdd_mul, Prod.fst_add, map_add,
    reduce_omegaAction]

private lemma sCoord_one : sCoord (1 : Factor k) = 0 := by
  simp [sCoord]

private lemma tCoord_one : tCoord (1 : Factor k) = 0 := by
  simp [tCoord]

private lemma sCoord_inv (x : Factor k) : sCoord x⁻¹ = -sCoord x :=
  eq_neg_of_add_eq_zero_left (by rw [← sCoord_mul, inv_mul_cancel, sCoord_one])

private lemma tCoord_inv (x : Factor k) : tCoord x⁻¹ = -tCoord x :=
  eq_neg_of_add_eq_zero_left (by rw [← tCoord_mul, inv_mul_cancel, tCoord_one])

private lemma right_eq_one_iff (x : Factor k) : x.right = 1 ↔ tCoord x = 0 := by
  rw [tCoord, ← toAdd_one, toAdd.injective.eq_iff]

/-! ### Orders of elements of a factor -/

/-- Every element outside the normal subgroup `(ZMod (3 ^ (k + 1)))²` has cube `1`. -/
private lemma pow_three_of_right_ne_one (x : Factor k) (hx : x.right ≠ 1) : x ^ 3 = 1 := by
  obtain ⟨v, j⟩ := x
  obtain ⟨j, rfl⟩ := ofAdd.surjective j
  have hj : j = 1 ∨ j = 2 :=
    (by decide : ∀ j : ZMod 3, j ≠ 0 → j = 1 ∨ j = 2) j fun h => hx (by simp [h])
  rw [pow_three']
  rcases hj with rfl | rfl
  · refine SemidirectProduct.ext ?_ ?_
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, ← ofAdd_add,
        show (1 + 1 : ZMod 3) = 2 from rfl, omegaAction_ofAdd_one, omegaAction_ofAdd_two,
        mul_omegaAut_mul_omegaAut_sq, SemidirectProduct.one_left]
    · simp only [SemidirectProduct.mul_right, ← ofAdd_add, SemidirectProduct.one_right]
      rfl
  · refine SemidirectProduct.ext ?_ ?_
    · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, ← ofAdd_add,
        show (2 + 2 : ZMod 3) = 1 from rfl, omegaAction_ofAdd_one, omegaAction_ofAdd_two,
        SemidirectProduct.one_left]
      rw [mul_right_comm, mul_omegaAut_mul_omegaAut_sq]
    · simp only [SemidirectProduct.mul_right, ← ofAdd_add, SemidirectProduct.one_right]
      rfl

private lemma eq_inl_of_right_eq_one (x : Factor k) (hx : x.right = 1) :
    x = SemidirectProduct.inl x.left :=
  SemidirectProduct.ext rfl hx

private lemma nsmul_pow_succ_eq_zero (w : ZMod (3 ^ (k + 1)) × ZMod (3 ^ (k + 1))) :
    (3 ^ (k + 1)) • w = 0 := by
  rw [nsmul_eq_mul]
  ext <;> simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_natCast, Prod.snd_natCast,
    ZMod.natCast_self, zero_mul, Prod.fst_zero, Prod.snd_zero]

/-- If `3 ^ k * a = 0` in `ZMod (3 ^ (k + 1))`, then `a` is divisible by `3`. -/
private lemma reduce_eq_zero_of_mul_eq_zero (a : ZMod (3 ^ (k + 1)))
    (h : (3 : ZMod (3 ^ (k + 1))) ^ k * a = 0) : reduce k a = 0 := by
  rw [← ZMod.natCast_zmod_val a] at h ⊢
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  have h' : ((3 ^ k * a.val : ℕ) : ZMod (3 ^ (k + 1))) = 0 := by
    push_cast
    exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  generalize a.val = m at h' ⊢
  rw [pow_succ] at h'
  exact Nat.dvd_of_mul_dvd_mul_left (pow_pos (by decide) k) h'

private lemma pow_pow_succ_eq_one (x : Factor k) : x ^ (3 ^ (k + 1)) = 1 := by
  by_cases hx : x.right = 1
  · rw [eq_inl_of_right_eq_one x hx, ← map_pow, ← map_one SemidirectProduct.inl]
    congr 1
    apply toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_pow_succ_eq_zero]
  · have h : x ^ (3 ^ (k + 1)) = (x ^ 3) ^ (3 ^ k) := by rw [← pow_mul, ← pow_succ']
    rw [h, pow_three_of_right_ne_one x hx, one_pow]

/-- An element of the normal subgroup whose first coordinate is a unit has order `3 ^ (k + 1)`;
this is the half `x ^ (3 ^ k) ≠ 1`. -/
private lemma pow_pow_ne_one (x : Factor k) (hx : x.right = 1) (hs : sCoord x ≠ 0) :
    x ^ (3 ^ k) ≠ 1 := by
  rw [eq_inl_of_right_eq_one x hx, ← map_pow, ← map_one SemidirectProduct.inl, Ne,
    SemidirectProduct.inl_inj]
  intro h
  apply hs
  have h1 := congrArg (fun w => (toAdd w).1) h
  simp only [toAdd_pow, toAdd_one, Prod.fst_zero, nsmul_eq_mul] at h1
  push_cast at h1
  exact reduce_eq_zero_of_mul_eq_zero _ h1

private lemma pow_pow_succ_of_right_ne_one (x : Factor k) (hx : x.right ≠ 1) (n : ℕ) :
    x ^ (3 ^ (n + 1)) = 1 := by
  have h : x ^ (3 ^ (n + 1)) = (x ^ 3) ^ (3 ^ n) := by rw [← pow_mul, ← pow_succ']
  rw [h, pow_three_of_right_ne_one x hx, one_pow]

private lemma pow_pow_eq_one_of_le (x : Factor k) {n : ℕ} (hn : k + 1 ≤ n) :
    x ^ (3 ^ n) = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h : x ^ (3 ^ (k + 1 + j)) = (x ^ (3 ^ (k + 1))) ^ (3 ^ j) := by
    rw [← pow_mul, ← pow_add]
  rw [h, pow_pow_succ_eq_one, one_pow]

/-! ### The fibre product -/

/-- The fibre product of the factors for `k = 1, 2, 3` over `(ℤ/3)²`: the triples with common
coordinate `s` whose coordinates `t` are `t`, `t - s` and `t - 2 s`. -/
private def fibre : Subgroup (Factor 1 × Factor 2 × Factor 3) where
  carrier := {x | sCoord x.2.1 = sCoord x.1 ∧ sCoord x.2.2 = sCoord x.1 ∧
    tCoord x.2.1 = tCoord x.1 - sCoord x.1 ∧ tCoord x.2.2 = tCoord x.1 - 2 * sCoord x.1}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3, ha4⟩ ⟨hb1, hb2, hb3, hb4⟩
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, sCoord_mul, tCoord_mul]
    exact ⟨by linear_combination ha1 + hb1, by linear_combination ha2 + hb2,
      by linear_combination ha3 + hb3, by linear_combination ha4 + hb4⟩
  one_mem' := by simp [sCoord_one, tCoord_one]
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3, ha4⟩
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv, sCoord_inv, tCoord_inv]
    exact ⟨by linear_combination -ha1, by linear_combination -ha2,
      by linear_combination -ha3, by linear_combination -ha4⟩

private lemma isPGroup_fibre : IsPGroup 3 fibre := fun _ =>
  ⟨4, Subtype.ext (Prod.ext (pow_pow_eq_one_of_le _ (by decide))
    (Prod.ext (pow_pow_eq_one_of_le _ (by decide)) (pow_pow_eq_one_of_le _ (by decide))))⟩

private lemma orderOf_eq_three (y : Factor 1 × Factor 2 × Factor 3) (h1 : y.1.right ≠ 1)
    (h2 : y.2.1.right ≠ 1) (h3 : y.2.2.right ≠ 1) : orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · exact Prod.ext (pow_three_of_right_ne_one _ h1)
      (Prod.ext (pow_three_of_right_ne_one _ h2) (pow_three_of_right_ne_one _ h3))
  · rintro rfl
    exact h1 rfl

private lemma orderOf_eq_nine (y : Factor 1 × Factor 2 × Factor 3) (h1 : y.1.right = 1)
    (hs : sCoord y.1 ≠ 0) (h2 : y.2.1.right ≠ 1) (h3 : y.2.2.right ≠ 1) :
    orderOf y = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime_pow (n := 1) ?_ ?_
  · intro h
    have h' := congrArg Prod.fst h
    rw [Prod.pow_fst, Prod.fst_one] at h'
    exact pow_pow_ne_one y.1 h1 hs h'
  · exact Prod.ext (pow_pow_succ_eq_one _)
      (Prod.ext (pow_pow_succ_of_right_ne_one _ h2 1) (pow_pow_succ_of_right_ne_one _ h3 1))

private lemma orderOf_eq_twentySeven (y : Factor 1 × Factor 2 × Factor 3) (h1 : y.1.right ≠ 1)
    (h2 : y.2.1.right = 1) (hs : sCoord y.2.1 ≠ 0) (h3 : y.2.2.right ≠ 1) :
    orderOf y = 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime_pow (n := 2) ?_ ?_
  · intro h
    have h' := congrArg (fun z => z.2.1) h
    simp only [Prod.pow_snd, Prod.pow_fst, Prod.snd_one, Prod.fst_one] at h'
    exact pow_pow_ne_one y.2.1 h2 hs h'
  · exact Prod.ext (pow_pow_succ_of_right_ne_one _ h1 2)
      (Prod.ext (pow_pow_succ_eq_one _) (pow_pow_succ_of_right_ne_one _ h3 2))

private lemma orderOf_eq_eightyOne (y : Factor 1 × Factor 2 × Factor 3) (h1 : y.1.right ≠ 1)
    (h2 : y.2.1.right ≠ 1) (h3 : y.2.2.right = 1) (hs : sCoord y.2.2 ≠ 0) :
    orderOf y = 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime_pow (n := 3) ?_ ?_
  · intro h
    have h' := congrArg (fun z => z.2.2) h
    simp only [Prod.pow_snd, Prod.snd_one] at h'
    exact pow_pow_ne_one y.2.2 h3 hs h'
  · exact Prod.ext (pow_pow_succ_of_right_ne_one _ h1 3)
      (Prod.ext (pow_pow_succ_of_right_ne_one _ h2 3) (pow_pow_succ_eq_one _))

/-- The order of the elements of the fibre product over a nonzero vector `(s, t)` of `(ℤ/3)²`. -/
private def lineOrder (s t : ZMod 3) : ℕ :=
  if s = 0 then 3 else if t = 0 then 3 ^ 2 else if t = s then 3 ^ 3 else 3 ^ 4

private lemma zmod_three_facts (s : ZMod 3) (hs : s ≠ 0) : 0 - s ≠ 0 ∧ 0 - 2 * s ≠ 0 ∧
    s - s = 0 ∧ s - 2 * s ≠ 0 ∧ 2 * s - s ≠ 0 ∧ 2 * s - 2 * s = 0 ∧ 2 * s ≠ 0 ∧ 2 * s ≠ s := by
  revert s
  decide

private lemma zmod_three_trichotomy : ∀ s t : ZMod 3, s ≠ 0 → t = 0 ∨ t = s ∨ t = 2 * s := by
  decide

/-- The order of an element of the fibre product depends only on the line of its image
`(s, t)` in `(ℤ/3)²`. -/
private lemma orderOf_fibre (x : fibre) (hx : sCoord (x : Factor 1 × Factor 2 × Factor 3).1 ≠ 0 ∨
    tCoord (x : Factor 1 × Factor 2 × Factor 3).1 ≠ 0) :
    orderOf x = lineOrder (sCoord (x : Factor 1 × Factor 2 × Factor 3).1)
      (tCoord (x : Factor 1 × Factor 2 × Factor 3).1) := by
  obtain ⟨y, hy⟩ := x
  rw [Subgroup.orderOf_mk]
  obtain ⟨h1, h2, h3, h4⟩ := hy
  obtain ⟨y1, y2, y3⟩ := y
  simp only at h1 h2 h3 h4 hx ⊢
  generalize hs : sCoord y1 = s at *
  generalize ht : tCoord y1 = t at *
  by_cases hs0 : s = 0
  · subst hs0
    have ht0 : t ≠ 0 := hx.resolve_left (not_not.2 rfl)
    rw [lineOrder, ite_eq_left rfl]
    apply orderOf_eq_three
    · change y1.right ≠ 1
      rw [Ne, right_eq_one_iff, ht]
      exact ht0
    · change y2.right ≠ 1
      rw [Ne, right_eq_one_iff, h3, sub_zero]
      exact ht0
    · change y3.right ≠ 1
      rw [Ne, right_eq_one_iff, h4, mul_zero, sub_zero]
      exact ht0
  · obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := zmod_three_facts s hs0
    rcases zmod_three_trichotomy s t hs0 with rfl | rfl | rfl
    · rw [lineOrder, ite_eq_right hs0, ite_eq_left rfl]
      apply orderOf_eq_nine
      · change y1.right = 1
        rw [right_eq_one_iff, ht]
      · change sCoord y1 ≠ 0
        rw [hs]
        exact hs0
      · change y2.right ≠ 1
        rw [Ne, right_eq_one_iff, h3]
        exact f1
      · change y3.right ≠ 1
        rw [Ne, right_eq_one_iff, h4]
        exact f2
    · rw [lineOrder, ite_eq_right hs0, ite_eq_right hs0, ite_eq_left rfl]
      apply orderOf_eq_twentySeven
      · change y1.right ≠ 1
        rw [Ne, right_eq_one_iff, ht]
        exact hs0
      · change y2.right = 1
        rw [right_eq_one_iff, h3, f3]
      · change sCoord y2 ≠ 0
        rw [h1]
        exact hs0
      · change y3.right ≠ 1
        rw [Ne, right_eq_one_iff, h4]
        exact f4
    · rw [lineOrder, ite_eq_right hs0, ite_eq_right f7, ite_eq_right f8]
      apply orderOf_eq_eightyOne
      · change y1.right ≠ 1
        rw [Ne, right_eq_one_iff, ht]
        exact f7
      · change y2.right ≠ 1
        rw [Ne, right_eq_one_iff, h3]
        exact f5
      · change y3.right = 1
        rw [right_eq_one_iff, h4, f6]
      · change sCoord y3 ≠ 0
        rw [h2]
        exact hs0

/-! ### The proper subgroups over the lines of `(ℤ/3)²` -/

/-- The preimage in the fibre product of the line `a s + b t = 0` of `(ℤ/3)²`. -/
private def lineSubgroup (a b : ZMod 3) : Subgroup fibre :=
  (MonoidHom.mk' (fun x : fibre => ofAdd (a * sCoord (x : Factor 1 × Factor 2 × Factor 3).1 +
      b * tCoord (x : Factor 1 × Factor 2 × Factor 3).1))
    (fun x y => by
      simp only [Subgroup.coe_mul, Prod.fst_mul, sCoord_mul, tCoord_mul, ← ofAdd_add]
      ring_nf)).ker

private lemma mem_lineSubgroup {a b : ZMod 3} {x : fibre} :
    x ∈ lineSubgroup a b ↔ a * sCoord (x : Factor 1 × Factor 2 × Factor 3).1 +
      b * tCoord (x : Factor 1 × Factor 2 × Factor 3).1 = 0 := by
  rw [lineSubgroup, MonoidHom.mem_ker, MonoidHom.mk'_apply, ofAdd_eq_one]

/-- An element of the fibre product over `(1, 0)`. -/
private def elemS : fibre :=
  ⟨(⟨ofAdd (1, 0), 1⟩, ⟨ofAdd (1, 0), ofAdd (-1)⟩, ⟨ofAdd (1, 0), ofAdd (-2)⟩), by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sCoord, tCoord]⟩

/-- An element of the fibre product over `(0, 1)`. -/
private def elemT : fibre :=
  ⟨(⟨1, ofAdd 1⟩, ⟨1, ofAdd 1⟩, ⟨1, ofAdd 1⟩), by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sCoord, tCoord]⟩

private lemma elemS_coords : sCoord (elemS : Factor 1 × Factor 2 × Factor 3).1 = 1 ∧
    tCoord (elemS : Factor 1 × Factor 2 × Factor 3).1 = 0 := by
  simp [elemS, sCoord, tCoord]

private lemma elemT_coords : sCoord (elemT : Factor 1 × Factor 2 × Factor 3).1 = 0 ∧
    tCoord (elemT : Factor 1 × Factor 2 × Factor 3).1 = 1 := by
  simp [elemT, sCoord, tCoord]

/-- The coefficients `(a, b)` of the line `a s + b t = 0` that contains the images of all elements
of order `m`. -/
private def lineCoeffs (m : ℕ) : ZMod 3 × ZMod 3 :=
  if m = 3 ^ 2 then (0, 1) else if m = 3 ^ 3 then (-1, 1) else if m = 3 ^ 4 then (-2, 1)
  else (1, 0)

private lemma lineCoeffs_ne_zero (m : ℕ) : (lineCoeffs m).1 ≠ 0 ∨ (lineCoeffs m).2 ≠ 0 := by
  unfold lineCoeffs
  split_ifs <;> decide

private lemma lineCoeffs_lineOrder : ∀ s t : ZMod 3, (s ≠ 0 ∨ t ≠ 0) →
    (lineCoeffs (lineOrder s t)).1 * s + (lineCoeffs (lineOrder s t)).2 * t = 0 := by
  decide

/-- All elements of order `m` of the fibre product lie in the proper subgroup over one line. -/
private lemma subset_lineSubgroup (m : ℕ) (S : Set fibre) (hm : ∀ x ∈ S, orderOf x = m) :
    S ⊆ lineSubgroup (lineCoeffs m).1 (lineCoeffs m).2 := by
  intro x hx
  rw [SetLike.mem_coe, mem_lineSubgroup]
  by_cases h0 : sCoord (x : Factor 1 × Factor 2 × Factor 3).1 ≠ 0 ∨
      tCoord (x : Factor 1 × Factor 2 × Factor 3).1 ≠ 0
  · rw [← hm x hx, orderOf_fibre x h0]
    exact lineCoeffs_lineOrder _ _ h0
  · simp only [not_or, not_not] at h0
    rw [h0.1, h0.2, mul_zero, mul_zero, add_zero]

private lemma lineSubgroup_ne_top (m : ℕ) :
    lineSubgroup (lineCoeffs m).1 (lineCoeffs m).2 ≠ ⊤ := by
  intro htop
  rcases lineCoeffs_ne_zero m with hc | hc
  · have h := htop ▸ Subgroup.mem_top elemS
    rw [mem_lineSubgroup, elemS_coords.1, elemS_coords.2, mul_one, mul_zero, add_zero] at h
    exact hc h
  · have h := htop ▸ Subgroup.mem_top elemT
    rw [mem_lineSubgroup, elemT_coords.1, elemT_coords.2, mul_one, mul_zero, zero_add] at h
    exact hc h

end Counterexample

/--
**Finite p-groups without a generating set of elements of equal order.** For some odd prime $p$
there is a finite $p$-group $G$ such that no generating set of $G$ consists of elements that all
have the same order. This answers Kourovka Problem 11.6 (Bagiński) in the negative (O'Brien,
Scoppola and Vaughan-Lee).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.6
(C. Bagiński); resolution: E. A. O'Brien, C. M. Scoppola and M. R. Vaughan-Lee, Proc. Amer. Math.
Soc. 134, no. 12 (2006), 3457-3464, Kourovka Archive, Problem 11.6: "No, it is not true",
https://arxiv.org/abs/1401.0300v49.
-/
theorem pGroupEqualOrderGenerators_refuted : ¬ pGroupEqualOrderGenerators := by
  intro h
  obtain ⟨S, hS, m, hm⟩ :=
    h 3 Nat.prime_three (by decide) Counterexample.fibre Counterexample.isPGroup_fibre
  apply Counterexample.lineSubgroup_ne_top m
  rw [eq_top_iff, ← hS, Subgroup.closure_le]
  exact Counterexample.subset_lineSubgroup m S hm

end MathlibExt.GroupTheory.PGroupEqualOrderGeneratorsKourovka11Problem6Wanted
