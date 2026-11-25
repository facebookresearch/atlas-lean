/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum.Prime

/-!
# Solubility is not determined by the type (Kourovka Notebook Problem 12.37)

Kourovka Notebook, Problem 12.37 (J. G. Thompson; A. S. Kondratiev, W. J. Shi), marked solved in the
21st issue: for a finite group `G` let the type of `G` be the function `n ↦ |{x ∈ G | xⁿ = 1}|`. Is
a finite group soluble if its type is the same as that of a soluble group?

The answer is negative: `solubleOfSameTypeAsSoluble_refuted` proves that the statement
`solubleOfSameTypeAsSoluble` fails. Following P. Piwek's construction, it exhibits a soluble group
and a non-soluble group, both of order `2 ^ 365 * 3 ^ 105 * 7 ^ 104`, that have the same type.

## Proof outline

* The number of solutions of `x ^ n = 1` is multiplicative over direct products, and in a group
  of exponent dividing `168` it only depends on `gcd n 168`.
* Piwek's groups are direct products of `18` small groups each, with multiplicities. The
  non-soluble group contains three copies of `GL(3, 2)`; every factor of the other group is soluble.
  For each factor we compute the number of solutions of `x ^ d = 1` at the divisors `d` of `168`,
  and the two products agree at every such `d`: this is a check on integers.
* Each factor is a concrete group with the counts of the corresponding group of Piwek's tables:
  a cyclic, dihedral or generalized quaternion group of Mathlib, a semidirect product by a cyclic
  group, the group `𝔽₈ ⋊ (C₇ ⋊ C₃) = AΓL(1, 8)`, the group `GL(3, 2)`, realized as the
  `xor`-linear permutations of `Fin 8`, or a semidirect product `C_p ⋊_χ G` with `G` acting on
  `C_p` through a character `χ : G →* (ZMod p)ˣ`. In the last case the counts are sums over `G`:
  for `g ^ d = 1`, the elements `(a, g)` with `(a, g) ^ d = 1` are all `p` of them when `χ g ≠ 1`,
  because `∑ i < d, χ(g) ^ i = 0`, and the solutions of `d • a = 0` when `χ g = 1`.
* `GL(3, 2)` is not soluble because a nontrivial element is a commutator of two of its
  conjugates, so it lies in every term of the derived series.

## Implementation notes

The finite computations are checked by the kernel with `decide +kernel`. Only the counts matter
for the type, so a factor need not be the group named in Piwek's tables, only a group with the same
counts; the counts are those listed in Tables 2 and 4 of the paper. The declarations keep the full
names they had in the former wanted module, so the namespace still reads `...Wanted`.

## References

* P. Piwek, *Solvable and non-solvable finite groups of the same order type*, arXiv:2403.02197v2
  (2024), Theorem A and Tables 1, 2 and 4; Algebra Number Theory 19 (2025), no. 8, 1663-1670.
* E. I. Khukhro and V. D. Mazurov (eds.), *Unsolved Problems in Group Theory: The Kourovka
  Notebook*, 21st issue, arXiv:1401.0300v49 (2026), Problem 12.37.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SolubleTypeRecognitionKourovka12Problem37Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 12.37 (J. G. Thompson; A. S. Kondratiev, W.
J. Shi). UnsolvedMath record UM-00700856 (`KOU-12.37`), dataset ulamai/UnsolvedMath v1.8.0.

The types are compared at every `n ≥ 1` (at `n = 0` both values are the group orders, which already
agree at `n = |G| |H|`). Groups are finite and in `Type`.
-/

/-- **Groups of the same type.** Two groups $G$ and $H$ have the same type when, for every integer
$n \ge 1$, the equation $x^n = 1$ has the same number of solutions in $G$ as in $H$, where an
infinite set of solutions counts as having $0$ elements. -/
def SameType (G H : Type*) [Group G] [Group H] : Prop :=
  ∀ n : ℕ, 0 < n → Nat.card {x : G // x ^ n = 1} = Nat.card {x : H // x ^ n = 1}

/-- **Kourovka Problem 12.37 (J. G. Thompson).** Every finite group of the same type as a finite
soluble group is soluble: if $G$ and $H$ are finite groups of the same type and $H$ is soluble,
then $G$ is soluble. -/
def solubleOfSameTypeAsSoluble : Prop :=
  ∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H],
    Group.IsSolvable H → SameType G H → Group.IsSolvable G

open Multiplicative
open scoped commutatorElement

/-! ### Counting solutions of `x ^ n = 1` -/

private theorem card_pow_eq_one_prod (G H : Type*) [Group G] [Group H] (n : ℕ) :
    Nat.card {x : G × H // x ^ n = 1} =
      Nat.card {x : G // x ^ n = 1} * Nat.card {x : H // x ^ n = 1} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun x => by simp [Prod.ext_iff]).trans
    Equiv.subtypeProdEquivProd)

private theorem card_pow_eq_one_pi (G : Type*) [Group G] (m n : ℕ) :
    Nat.card {f : Fin m → G // f ^ n = 1} = Nat.card {x : G // x ^ n = 1} ^ m := by
  rw [← Nat.card_fin m, ← Nat.card_fun, Nat.card_fin]
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun f => by simp [funext_iff]).trans
    Equiv.subtypePiEquivPi)

/-- In a group of exponent dividing `E`, the number of solutions of `x ^ n = 1` only depends on
`gcd n E`. -/
private theorem card_pow_eq_one_gcd {G : Type*} [Group G] {E : ℕ} (hE : ∀ x : G, x ^ E = 1)
    (n : ℕ) : Nat.card {x : G // x ^ n = 1} = Nat.card {x : G // x ^ Nat.gcd n E = 1} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [hE])

private theorem forall_pow_eq_one_of_card {G : Type*} [Group G] [Finite G] {E : ℕ}
    (h : Nat.card {x : G // x ^ E = 1} = Nat.card G) (x : G) : x ^ E = 1 := by
  obtain ⟨y, hy⟩ := (Subtype.val_injective.bijective_of_nat_card_le h.ge).2 x
  exact hy ▸ y.2

/-- The divisors of `168`, a multiple of the exponent of every group used below. -/
private def divs168 : List ℕ := [1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168]

/-- A function on the divisors of `168`, given by its list of values. -/
private def tbl (l : List ℕ) (d : ℕ) : ℕ := l.getD (divs168.idxOf d) 0

/-- The number of solutions of `x ^ n = 1` in a group of exponent dividing `E ∣ 168` is read off
a table of its values at the divisors of `168`, which only needs checking at the divisors
of `E`. -/
private theorem card_pow_eq_one_eq_tbl {G : Type*} [Group G] [Finite G] (E : ℕ) (l : List ℕ)
    (hE : E ∣ 168) (hl : ∀ d ∈ Nat.divisors 168, tbl l d = tbl l (Nat.gcd d E))
    (ht : ∀ d ∈ Nat.divisors E, Nat.card {x : G // x ^ d = 1} = tbl l d)
    (hG : Nat.card G = tbl l E) (n : ℕ) :
    Nat.card {x : G // x ^ n = 1} = tbl l (Nat.gcd n 168) := by
  have hE0 : E ≠ 0 := by rintro rfl; norm_num at hE
  have hpow : ∀ x : G, x ^ E = 1 :=
    forall_pow_eq_one_of_card ((ht E (Nat.mem_divisors_self E hE0)).trans hG.symm)
  rw [card_pow_eq_one_gcd hpow n, ht _ (Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right n E, hE0⟩),
    hl _ (Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right n 168, by norm_num⟩), Nat.gcd_assoc,
    Nat.gcd_eq_right hE]

/-- If every element satisfies `x ^ a = 1` or `x ^ b = 1`, then `x ^ d = 1` exactly when
`x ^ gcd d a = 1` or `x ^ gcd d b = 1`. -/
private theorem card_pow_eq_one_cover {G : Type*} [Group G] {a b : ℕ}
    (hab : ∀ x : G, x ^ a = 1 ∨ x ^ b = 1) (d : ℕ) :
    Nat.card {x : G // x ^ d = 1} =
      Nat.card {x : G // x ^ Nat.gcd d a = 1 ∨ x ^ Nat.gcd d b = 1} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨fun h => ?_, ?_⟩)
  · rcases hab x with ha | hb
    · exact Or.inl (pow_gcd_eq_one.2 ⟨h, ha⟩)
    · exact Or.inr (pow_gcd_eq_one.2 ⟨h, hb⟩)
  · rintro (h | h) <;> exact (pow_gcd_eq_one.1 h).1

/-! ### Semidirect products `C_p ⋊ G` -/

/-- The units of `ZMod n` act on `Multiplicative (ZMod n)` by multiplication. -/
private def unitsMulAut (n : ℕ) : (ZMod n)ˣ →* MulAut (Multiplicative (ZMod n)) where
  toFun u :=
    { toFun := fun x => ofAdd ((u : ZMod n) * x.toAdd)
      invFun := fun x => ofAdd (((u⁻¹ : (ZMod n)ˣ) : ZMod n) * x.toAdd)
      left_inv := fun x => by simp [← mul_assoc]
      right_inv := fun x => by simp [← mul_assoc]
      map_mul' := fun x y => by simp [mul_add] }
  map_one' := by ext; simp
  map_mul' u v := by ext; simp [mul_assoc]

private theorem unitsMulAut_apply (n : ℕ) (u : (ZMod n)ˣ) (x : Multiplicative (ZMod n)) :
    unitsMulAut n u x = ofAdd ((u : ZMod n) * x.toAdd) := rfl

/-- The semidirect product `C_n ⋊_χ G`, where `G` acts on `C_n` through `χ : G →* (ZMod n)ˣ`. -/
private abbrev Ext (n : ℕ) (G : Type) [Group G] (χ : G →* (ZMod n)ˣ) : Type :=
  Multiplicative (ZMod n) ⋊[(unitsMulAut n).comp χ] G

private theorem ext_pow (n : ℕ) {G : Type} [Group G] (χ : G →* (ZMod n)ˣ)
    (a : Multiplicative (ZMod n)) (g : G) (d : ℕ) :
    (⟨a, g⟩ : Ext n G χ) ^ d =
      ⟨ofAdd ((∑ i ∈ Finset.range d, ((χ g : (ZMod n)ˣ) : ZMod n) ^ i) * a.toAdd), g ^ d⟩ := by
  induction d with
  | zero =>
    rw [pow_zero, pow_zero]
    refine SemidirectProduct.ext ?_ rfl
    simp only [SemidirectProduct.one_left, Finset.range_zero, Finset.sum_empty, zero_mul,
      ofAdd_zero]
  | succ d ih =>
    rw [pow_succ, ih]
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, MonoidHom.comp_apply, unitsMulAut_apply, map_pow,
        Units.val_pow_eq_pow_val, ← ofAdd_add, Finset.sum_range_succ, add_mul]
    · simp only [SemidirectProduct.mul_right, pow_succ]

private theorem card_zmod_mul_eq_zero (p : ℕ) [Fact p.Prime] (d : ℕ) :
    Nat.card {a : ZMod p // (d : ZMod p) * a = 0} = if p ∣ d then p else 1 := by
  by_cases h : p ∣ d
  · rw [ite_eq_left h, (ZMod.natCast_eq_zero_iff d p).2 h]
    simp
  · have hd : (d : ZMod p) ≠ 0 := fun h' => h ((ZMod.natCast_eq_zero_iff d p).1 h')
    rw [ite_eq_right h]
    simp [hd]

/-- **Counting solutions of `x ^ d = 1` in `C_p ⋊_χ G`.** For `g ∈ G` with `g ^ d = 1`, the
elements `(a, g)` with `(a, g) ^ d = 1` are all `p` of them when `χ g ≠ 1`, by the geometric sum
`∑ χ(g) ^ i = 0`, and the solutions of `d • a = 0` when `χ g = 1`. -/
private theorem card_ext_pow_eq_one (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    [DecidableEq G] (χ : G →* (ZMod p)ˣ) (d : ℕ) :
    Nat.card {x : Ext p G χ // x ^ d = 1} =
      ∑ g : G, if g ^ d = 1 then (if χ g = 1 then (if p ∣ d then p else 1) else p) else 0 := by
  classical
  let S : G → ZMod p := fun g => ∑ i ∈ Finset.range d, ((χ g : (ZMod p)ˣ) : ZMod p) ^ i
  have key : ∀ (a : Multiplicative (ZMod p)) (g : G),
      (⟨a, g⟩ : Ext p G χ) ^ d = 1 ↔ S g * a.toAdd = 0 ∧ g ^ d = 1 := by
    intro a g
    rw [ext_pow, SemidirectProduct.ext_iff, SemidirectProduct.one_left,
      SemidirectProduct.one_right]
    exact and_congr_left' ofAdd_eq_one
  let e : {x : Ext p G χ // x ^ d = 1} ≃ Σ g : G, {a : ZMod p // S g * a = 0 ∧ g ^ d = 1} :=
    { toFun := fun x => ⟨x.1.right, x.1.left.toAdd, (key x.1.left x.1.right).1 x.2⟩
      invFun := fun y => ⟨⟨ofAdd y.2.1, y.1⟩, (key (ofAdd y.2.1) y.1).2 y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : g ^ d = 1
  · rw [ite_eq_left hg]
    by_cases hχ : χ g = 1
    · rw [ite_eq_left hχ, ← card_zmod_mul_eq_zero p d]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
      simp [S, hχ, hg]
    · rw [ite_eq_right hχ]
      have hu : ((χ g : (ZMod p)ˣ) : ZMod p) ^ d = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← map_pow, hg, map_one, Units.val_one]
      have hne : ((χ g : (ZMod p)ˣ) : ZMod p) - 1 ≠ 0 := by
        rw [sub_ne_zero]
        exact fun h => hχ (Units.ext h)
      have hs : S g = 0 := by
        have := geom_sum_mul ((χ g : (ZMod p)ˣ) : ZMod p) d
        rw [hu, sub_self] at this
        exact (mul_eq_zero.1 this).resolve_right hne
      simp [hs, hg]
  · rw [ite_eq_right hg]
    simp [hg]

/-- `card_ext_pow_eq_one`, where `g ^ d = 1` is tested as `g ^ gcd d E = 1` for a multiple `E`
of the exponent of `G`. -/
private theorem card_ext_pow_eq_one_gcd (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    [DecidableEq G] (χ : G →* (ZMod p)ˣ) {E : ℕ} (hE : ∀ g : G, g ^ E = 1) (d : ℕ) :
    Nat.card {x : Ext p G χ // x ^ d = 1} =
      ∑ g : G, if g ^ Nat.gcd d E = 1 then (if χ g = 1 then (if p ∣ d then p else 1) else p)
        else 0 := by
  simp only [pow_gcd_eq_one, hE, and_true]
  exact card_ext_pow_eq_one p χ d

/-! ### Solubility -/

private theorem isSolvable_multiplicative (A : Type*) [AddCommGroup A] :
    Group.IsSolvable (Multiplicative A) :=
  Group.isSolvable_of_comm mul_comm

private theorem isSolvable_semidirectProduct {N G : Type*} [Group N] [Group G]
    {φ : G →* MulAut N} [Group.IsSolvable N] [Group.IsSolvable G] :
    Group.IsSolvable (N ⋊[φ] G) :=
  Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
    SemidirectProduct.range_inl_eq_ker_rightHom.ge

/-- The rotations of `DihedralGroup n`. -/
private def dihedralRot (n : ℕ) : Multiplicative (ZMod n) →* DihedralGroup n where
  toFun i := .r i.toAdd
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The sign of `DihedralGroup n`: rotations are even, reflections odd. -/
private def dihedralSign (n : ℕ) : DihedralGroup n →* Multiplicative (ZMod 2) where
  toFun
    | .r _ => 1
    | .sr _ => ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr] <;> decide

private theorem isSolvable_dihedral (n : ℕ) : Group.IsSolvable (DihedralGroup n) := by
  have := isSolvable_multiplicative (ZMod n)
  have := isSolvable_multiplicative (ZMod 2)
  refine Group.isSolvable_of_ker_le_range (dihedralRot n) (dihedralSign n) ?_
  rintro (i | i) h
  · exact ⟨ofAdd i, rfl⟩
  · exact absurd (h : dihedralSign n (.sr i) = 1) (by change ¬ ofAdd (1 : ZMod 2) = 1; decide)

/-- The cyclic subgroup of index two of `QuaternionGroup n`. -/
private def quaternionRot (n : ℕ) : Multiplicative (ZMod (2 * n)) →* QuaternionGroup n where
  toFun i := .a i.toAdd
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The quotient of `QuaternionGroup n` by its cyclic subgroup of index two. -/
private def quaternionSign (n : ℕ) : QuaternionGroup n →* Multiplicative (ZMod 2) where
  toFun
    | .a _ => 1
    | .xa _ => ofAdd 1
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      simp only [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a,
        QuaternionGroup.xa_mul_xa] <;> decide

private theorem isSolvable_quaternion (n : ℕ) : Group.IsSolvable (QuaternionGroup n) := by
  have := isSolvable_multiplicative (ZMod (2 * n))
  have := isSolvable_multiplicative (ZMod 2)
  refine Group.isSolvable_of_ker_le_range (quaternionRot n) (quaternionSign n) ?_
  rintro (i | i) h
  · exact ⟨ofAdd i, rfl⟩
  · exact absurd (h : quaternionSign n (.xa i) = 1)
      (by change ¬ ofAdd (1 : ZMod 2) = 1; decide)

/-- Extension by `1` at `0`. -/
private def consOne (K : Type*) [Group K] (m : ℕ) : (Fin m → K) →* (Fin (m + 1) → K) where
  toFun f := Fin.cons 1 f
  map_one' := by ext i; cases i using Fin.cases <;> simp
  map_mul' f g := by ext i; cases i using Fin.cases <;> simp

private theorem isSolvable_pi (K : Type*) [Group K] [Group.IsSolvable K] :
    ∀ m : ℕ, Group.IsSolvable (Fin m → K)
  | 0 => inferInstance
  | m + 1 => by
    have := isSolvable_pi K m
    refine Group.isSolvable_of_ker_le_range (consOne K m) (Pi.evalMonoidHom (fun _ => K) 0) ?_
    intro f hf
    refine ⟨Fin.tail f, ?_⟩
    rw [MonoidHom.mem_ker, Pi.evalMonoidHom_apply] at hf
    simp only [consOne, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← hf]
    exact Fin.cons_self_tail f

attribute [local instance] isSolvable_multiplicative isSolvable_semidirectProduct
  isSolvable_dihedral isSolvable_quaternion isSolvable_pi

/-! ### The small groups of Piwek's construction -/

private theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {u : M} {m : ℕ} (hu : u ^ m = 1)
    (k : ℕ) : u ^ (k % m) = u ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k m, pow_add, pow_mul, hu, one_pow, one_mul]

/-- The homomorphism `Multiplicative (ZMod m) →* M` sending the generator to `u`, where
`u ^ m = 1`. -/
private def zmodPowHom {M : Type*} [Monoid M] (m : ℕ) [NeZero m] (u : M) (hu : u ^ m = 1) :
    Multiplicative (ZMod m) →* M where
  toFun j := u ^ j.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, pow_mod_of_pow_eq_one hu, pow_add]

/-- The cyclic group of order `n`. -/
private abbrev C (n : ℕ) : Type := Multiplicative (ZMod n)

@[instance_reducible]
private def fintypeSemidirectProduct {N G : Type*} [Group N] [Group G] [Fintype N]
    [Fintype G] {φ : G →* MulAut N} : Fintype (N ⋊[φ] G) :=
  Fintype.ofEquiv (N × G) SemidirectProduct.equivProd.symm

attribute [local instance] fintypeSemidirectProduct

private theorem fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

attribute [local instance] fact_prime_seven

private def neg1Seven : (ZMod 7)ˣ := ⟨6, 6, by decide, by decide⟩
private def twoSeven : (ZMod 7)ˣ := ⟨2, 4, by decide, by decide⟩
private def threeSeven : (ZMod 7)ˣ := ⟨3, 5, by decide, by decide⟩
private def neg1Three : (ZMod 3)ˣ := ⟨2, 2, by decide, by decide⟩
private def threeEight : (ZMod 8)ˣ := ⟨3, 3, by decide, by decide⟩

/-- The character of `DihedralGroup n` with `r 1 ↦ a` and `sr 0 ↦ b`. -/
private def dihedralChar {n : ℕ} {M : Type*} [Monoid M] (a b : M) : DihedralGroup n → M
  | .r i => a ^ i.val
  | .sr i => b * a ^ i.val

private def rNegD4 : DihedralGroup 4 →* (ZMod 7)ˣ :=
  MonoidHom.mk' (dihedralChar neg1Seven 1) (by decide)
private def sNegD4 : DihedralGroup 4 →* (ZMod 7)ˣ :=
  MonoidHom.mk' (dihedralChar 1 neg1Seven) (by decide)
private def rsNegD4 : DihedralGroup 4 →* (ZMod 7)ˣ :=
  MonoidHom.mk' (dihedralChar neg1Seven neg1Seven) (by decide)
private def rNegD4Three : DihedralGroup 4 →* (ZMod 3)ˣ :=
  MonoidHom.mk' (dihedralChar neg1Three 1) (by decide)
private def sNegD7 : DihedralGroup 7 →* (ZMod 7)ˣ :=
  MonoidHom.mk' (dihedralChar 1 neg1Seven) (by decide)
private def rNegD12 : DihedralGroup 12 →* (ZMod 7)ˣ :=
  MonoidHom.mk' (dihedralChar neg1Seven 1) (by decide +kernel)
private def rNegD24 : DihedralGroup 24 →* (ZMod 7)ˣ :=
  MonoidHom.mk' (dihedralChar neg1Seven 1) (by decide +kernel)

/-- `C₇ ⋊ C₃`, the Frobenius group of order `21`. -/
private abbrev F21 : Type := Ext 7 (C 3) (zmodPowHom 3 twoSeven (by decide))
/-- `C₇ ⋊ C₆`, the Frobenius group of order `42`. -/
private abbrev F7 : Type := Ext 7 (C 6) (zmodPowHom 6 threeSeven (by decide))
/-- `C₈ ⋊ C₂` with `x ↦ x ^ 3`, the semidihedral group of order `16`. -/
private abbrev SD16 : Type := Ext 8 (C 2) (zmodPowHom 2 threeEight (by decide))
/-- `C₃ ⋊ SD₁₆ ≅ C₂₄ ⋊ C₂` (with `x ↦ x ^ 11`), of order `48`. -/
private abbrev P48 : Type :=
  Ext 3 SD16 ((zmodPowHom 2 neg1Three (by decide)).comp SemidirectProduct.rightHom)
/-- `C₃ ⋊ D₄`, of order `24`. -/
private abbrev C3sD4 : Type := Ext 3 (DihedralGroup 4) rNegD4Three

/-- An automorphism of order `3` of `Q₈`. -/
private def sigmaQ8Fun : QuaternionGroup 2 → QuaternionGroup 2
  | .a i => if i.val % 2 = 0 then .a i else .xa (i - 1)
  | .xa i => if i.val % 2 = 0 then .xa (i + 1) else .a i

private def sigmaQ8 : MulAut (QuaternionGroup 2) where
  toFun := sigmaQ8Fun
  invFun x := sigmaQ8Fun (sigmaQ8Fun x)
  left_inv x := by revert x; decide
  right_inv x := by revert x; decide
  map_mul' := by decide

/-- `Q₈ ⋊ C₃ ≅ SL(2, 3)`. -/
private abbrev SL23 : Type :=
  QuaternionGroup 2 ⋊[zmodPowHom 3 sigmaQ8 (MulEquiv.ext fun x => by revert x; decide)] C 3

/-- An automorphism of order `3` of `C₂ × C₂`. -/
private def tauV4 : MulAut (Multiplicative (ZMod 2 × ZMod 2)) where
  toFun x := ofAdd (x.toAdd.2, x.toAdd.1 + x.toAdd.2)
  invFun x := ofAdd (x.toAdd.1 + x.toAdd.2, x.toAdd.1)
  left_inv x := by revert x; decide
  right_inv x := by revert x; decide
  map_mul' := by decide

/-- `(C₂ × C₂) ⋊ C₃ ≅ A₄`. -/
private abbrev A4 : Type :=
  Multiplicative (ZMod 2 × ZMod 2) ⋊[zmodPowHom 3 tauV4 (MulEquiv.ext fun x => by
    revert x; decide)] C 3

/-- The automorphism `r i ↦ r (3 i)`, `sr i ↦ sr (3 i)` of `D₈`. -/
private def alphaD8Fun : DihedralGroup 8 → DihedralGroup 8
  | .r i => .r (3 * i)
  | .sr i => .sr (3 * i)

private def alphaD8 : MulAut (DihedralGroup 8) where
  toFun := alphaD8Fun
  invFun := alphaD8Fun
  left_inv x := by revert x; decide
  right_inv x := by revert x; decide
  map_mul' := by decide

/-- `D₈ ⋊ C₂`, of order `32`. -/
private abbrev P32 : Type :=
  DihedralGroup 8 ⋊[zmodPowHom 2 alphaD8 (MulEquiv.ext fun x => by revert x; decide)] C 2

private abbrev V8 : Type := Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)

/-- Multiplication by a generator `ω` of `𝔽₈ˣ`, with `ω ^ 3 = ω + 1`, in the basis `1, ω, ω²`. -/
private def mulOmegaFun (x : V8) : V8 :=
  ofAdd (x.toAdd.2.2, x.toAdd.1 + x.toAdd.2.2, x.toAdd.2.1)

/-- The Frobenius map `x ↦ x ^ 2` of `𝔽₈`, in the basis `1, ω, ω²`. -/
private def frobFun (x : V8) : V8 :=
  ofAdd (x.toAdd.1, x.toAdd.2.2, x.toAdd.2.1 + x.toAdd.2.2)

/-- The semilinear map `x ↦ ω ^ k * x ^ (2 ^ j)` of `𝔽₈`. -/
private def aglFun (k j : ℕ) (x : V8) : V8 := mulOmegaFun^[k] (frobFun^[j] x)

private def aglEquiv (g : F21) : MulAut V8 where
  toFun := aglFun g.left.toAdd.val g.right.toAdd.val
  invFun := aglFun 0 (3 - g.right.toAdd.val) ∘ aglFun (7 - g.left.toAdd.val) 0
  left_inv x := by revert g x; decide +kernel
  right_inv x := by revert g x; decide +kernel
  map_mul' := by revert g; decide +kernel

/-- `F21 = C₇ ⋊ C₃` acts on `𝔽₈` by `x ↦ ω ^ k * x ^ (2 ^ j)`. -/
private def aglAct : F21 →* MulAut V8 :=
  MonoidHom.mk' aglEquiv (fun a b => MulEquiv.ext fun x => by revert a b x; decide +kernel)

/-- `𝔽₈ ⋊ (C₇ ⋊ C₃) = AΓL(1, 8)`, of order `168`. -/
private abbrev AGL18 : Type := V8 ⋊[aglAct] F21

private theorem agl18_cover : ∀ x : AGL18, x ^ 6 = 1 ∨ x ^ 7 = 1 := by decide +kernel

/-- `(-1) ^ b` on `SD₁₆ = C₈ ⋊ C₂`. -/
private def signSD16 : SD16 →* (ZMod 7)ˣ :=
  MonoidHom.mk' (fun x => neg1Seven ^ x.left.toAdd.val) (by decide +kernel)

/-! The groups `C₇ ⋊_χ G`; their names follow the rows of Piwek's tables whose counts they have. -/

/-- `C₇ ⋊ D₄`, where `r` acts by inversion and `s` trivially. -/
private abbrev C7sD4 : Type := Ext 7 (DihedralGroup 4) rNegD4
/-- `C₇ ⋊ C₁₂`, where the generator acts by `x ↦ x ^ 3`. -/
private abbrev C7sC12 : Type := Ext 7 (C 12) (zmodPowHom 12 threeSeven (by decide))
/-- `C₇ ⋊ A₄`, where `A₄` acts through its quotient `C₃` by `x ↦ x ^ 2`. -/
private abbrev C7sA4 : Type :=
  Ext 7 A4 ((zmodPowHom 3 twoSeven (by decide)).comp SemidirectProduct.rightHom)
/-- `C₇ ⋊ D₇`, where `r` acts trivially and `s` by inversion. -/
private abbrev C7sD7 : Type := Ext 7 (DihedralGroup 7) sNegD7
/-- `C₇ ⋊ (D₄ × C₃)`, where `s` acts by inversion, `r` trivially and `C₃` by `x ↦ x ^ 2`: the
counts of Piwek's `C₄ ⋊ F₇`. -/
private abbrev C4sF7 : Type :=
  Ext 7 (DihedralGroup 4 × C 3)
    (sNegD4.comp (MonoidHom.fst _ _) * (zmodPowHom 3 twoSeven (by decide)).comp (MonoidHom.snd _ _))
/-- `C₇ ⋊ (C₃ ⋊ D₄)`, where `r` and `s` act by inversion: the counts of Piwek's `C₂₁ ⋊ D₄`. -/
private abbrev C21sD4 : Type := Ext 7 C3sD4 (rsNegD4.comp SemidirectProduct.rightHom)
/-- `C₇ ⋊ D₁₂`, where `r` acts by inversion and `s` trivially. -/
private abbrev C7sD12 : Type := Ext 7 (DihedralGroup 12) rNegD12
/-- `C₇ ⋊ (D₈ ⋊ C₂)`, where `C₂` acts by inversion and `D₈` trivially: the counts of Piwek's
`D₈ ⋊ D₇`. -/
private abbrev D8sD7 : Type :=
  Ext 7 P32 ((zmodPowHom 2 neg1Seven (by decide)).comp SemidirectProduct.rightHom)
/-- `C₇ ⋊ D₂₄`, where `r` acts by inversion and `s` trivially. -/
private abbrev C7sD24 : Type := Ext 7 (DihedralGroup 24) rNegD24
/-- `C₇ ⋊ (D₄ × C₃)`, where `r` acts by inversion, `s` trivially and `C₃` by `x ↦ x ^ 2`: the
counts of Piwek's `Dic₇ ⋊ C₆`. -/
private abbrev Dic7sC6 : Type :=
  Ext 7 (DihedralGroup 4 × C 3)
    (rNegD4.comp (MonoidHom.fst _ _) * (zmodPowHom 3 twoSeven (by decide)).comp (MonoidHom.snd _ _))
/-- `C₇ ⋊ SL(2, 3)`, where `SL(2, 3)` acts through its quotient `C₃` by `x ↦ x ^ 2`: the counts
of Piwek's `C₁₄ : A₄`. -/
private abbrev C14A4 : Type :=
  Ext 7 SL23 ((zmodPowHom 3 twoSeven (by decide)).comp SemidirectProduct.rightHom)
/-- `C₇ ⋊ F₇`, where `F₇` acts through its quotient `C₂` by inversion. -/
private abbrev C7sF7 : Type :=
  Ext 7 F7 ((zmodPowHom 6 neg1Seven (by decide)).comp SemidirectProduct.rightHom)
/-- `C₇ ⋊ (C₃ ⋊ SD₁₆)`, where `(a, (b, j))` acts by `(-1) ^ b`: the counts of Piwek's
`D₁₂ : D₇`. -/
private abbrev D12D7 : Type := Ext 7 P48 (signSD16.comp SemidirectProduct.rightHom)

/-! ### `GL(3, 2)` -/

/-- The `xor`-linear permutations of `Fin 8 ≃ 𝔽₂³`: a copy of `GL(3, 2)`. -/
private def gl32 : Subgroup (Equiv.Perm (Fin 8)) where
  carrier := {σ | ∀ x y : Fin 8, σ (x ^^^ y) = σ x ^^^ σ y}
  mul_mem' {σ τ} hσ hτ x y := by
    simp only [Set.mem_ofPred_eq] at hσ hτ ⊢
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hτ, hσ]
  one_mem' x y := rfl
  inv_mem' {σ} hσ x y := by
    simp only [Set.mem_ofPred_eq] at hσ ⊢
    apply σ.injective
    rw [hσ]
    simp

/-- The bit `i` of `x : Fin 8`. -/
private def bit (i : ℕ) (x : Fin 8) : Bool := x.val.testBit i

/-- `a` if `b` holds, `0` otherwise. -/
private def sel (b : Bool) (a : Fin 8) : Fin 8 := if b then a else 0

/-- The map of `Fin 8 ≃ 𝔽₂³` sending the basis `1, 2, 4` to `t`, extended by `xor`. -/
private def linFun (t : Fin 8 × Fin 8 × Fin 8) (x : Fin 8) : Fin 8 :=
  sel (bit 0 x) t.1 ^^^ sel (bit 1 x) t.2.1 ^^^ sel (bit 2 x) t.2.2

private theorem xor_self_fin8 : ∀ z : Fin 8, z ^^^ z = 0 := by decide

private theorem eq_of_xor_eq_zero_fin8 : ∀ a b : Fin 8, a ^^^ b = 0 → a = b := by decide

private theorem xor_assoc_fin8 : ∀ a b c : Fin 8, a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := by
  decide +kernel

private theorem xor_comm_fin8 : ∀ a b : Fin 8, a ^^^ b = b ^^^ a := by decide

private theorem std_associative_xor_fin8 : Std.Associative (α := Fin 8) (· ^^^ ·) :=
  ⟨xor_assoc_fin8⟩

private theorem std_commutative_xor_fin8 : Std.Commutative (α := Fin 8) (· ^^^ ·) :=
  ⟨xor_comm_fin8⟩

attribute [local instance] std_associative_xor_fin8 std_commutative_xor_fin8

private theorem bit_xor : ∀ x y : Fin 8, bit 0 (x ^^^ y) = (bit 0 x ^^ bit 0 y) ∧
    bit 1 (x ^^^ y) = (bit 1 x ^^ bit 1 y) ∧ bit 2 (x ^^^ y) = (bit 2 x ^^ bit 2 y) := by
  decide

private theorem sel_xor : ∀ (b c : Bool) (a : Fin 8), sel (b ^^ c) a = sel b a ^^^ sel c a := by
  decide

private theorem linFun_xor (t : Fin 8 × Fin 8 × Fin 8) (x y : Fin 8) :
    linFun t (x ^^^ y) = linFun t x ^^^ linFun t y := by
  obtain ⟨h0, h1, h2⟩ := bit_xor x y
  simp only [linFun, h0, h1, h2, sel_xor]
  ac_rfl

private theorem linFun_basis : ∀ x : Fin 8, linFun (1, 2, 4) x = x := by decide

private theorem linFun_apply_basis : ∀ t : Fin 8 × Fin 8 × Fin 8,
    (linFun t 1, linFun t 2, linFun t 4) = t := by
  decide +kernel

private theorem map_zero_of_xor {f : Fin 8 → Fin 8} (hf : ∀ x y, f (x ^^^ y) = f x ^^^ f y) :
    f 0 = 0 := by
  have := hf 0 0
  rw [xor_self_fin8] at this
  rw [this, xor_self_fin8]

private theorem map_linFun {f : Fin 8 → Fin 8} (hf : ∀ x y, f (x ^^^ y) = f x ^^^ f y)
    (t : Fin 8 × Fin 8 × Fin 8) (x : Fin 8) :
    f (linFun t x) = linFun (f t.1, f t.2.1, f t.2.2) x := by
  have hsel : ∀ (b : Bool) (a : Fin 8), f (sel b a) = sel b (f a) := by
    rintro (_ | _) a
    · exact map_zero_of_xor hf
    · rfl
  simp only [linFun, hf, hsel]

private theorem eq_linFun (σ : gl32) (x : Fin 8) :
    (σ : Equiv.Perm (Fin 8)) x = linFun (σ.1 1, σ.1 2, σ.1 4) x := by
  conv_lhs => rw [← linFun_basis x]
  exact map_linFun σ.2 _ x

/-- `t` is the image of a basis: `linFun t` has trivial kernel. -/
private def IsBasisImage (t : Fin 8 × Fin 8 × Fin 8) : Prop := ∀ x, linFun t x = 0 → x = 0

private instance : DecidablePred IsBasisImage := fun t =>
  inferInstanceAs (Decidable (∀ x, linFun t x = 0 → x = 0))

private theorem injective_linFun {t : Fin 8 × Fin 8 × Fin 8} (ht : IsBasisImage t) :
    Function.Injective (linFun t) := by
  intro x y h
  refine eq_of_xor_eq_zero_fin8 x y (ht _ ?_)
  rw [linFun_xor, h, xor_self_fin8]

private noncomputable def toPerm (t : {t // IsBasisImage t}) : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective (linFun t.1) (Finite.injective_iff_bijective.1 (injective_linFun t.2))

private noncomputable def gl32Equiv : gl32 ≃ {t // IsBasisImage t} where
  toFun σ := ⟨(σ.1 1, σ.1 2, σ.1 4), fun x hx => σ.1.injective <| by
    rw [← eq_linFun σ x] at hx
    rw [hx, map_zero_of_xor σ.2]⟩
  invFun t := ⟨toPerm t, linFun_xor t.1⟩
  left_inv σ := Subtype.ext (Equiv.ext fun x => (eq_linFun σ x).symm)
  right_inv t := Subtype.ext (linFun_apply_basis t.1)

private theorem gl32_pow_eq_one_iff (σ : gl32) (k : ℕ) :
    σ ^ k = 1 ↔ ∀ x, (linFun (gl32Equiv σ).1)^[k] x = x := by
  have : ⇑(σ : Equiv.Perm (Fin 8)) = linFun (gl32Equiv σ).1 := funext (eq_linFun σ)
  rw [← this, Equiv.Perm.iterate_eq_pow, ← Subgroup.coe_pow, Subtype.ext_iff, Subgroup.coe_one,
    Equiv.ext_iff]
  rfl

/-- The order of the element of `GL(3, 2)` sending the basis `1, 2, 4` to `(a, b, c)`, and `0`
when `(a, b, c)` is not a basis. -/
private def gl32OrdTable : Fin 8 → Fin 8 → Fin 8 → ℕ := ![
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 2, 2, 2],
    ![0, 0, 0, 0, 2, 2, 4, 4], ![0, 0, 2, 4, 0, 0, 3, 3], ![0, 0, 4, 2, 0, 0, 3, 3],
    ![0, 0, 3, 3, 2, 4, 0, 0], ![0, 0, 3, 3, 2, 4, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 4, 4, 2], ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 3, 3, 3, 3], ![0, 3, 0, 7, 0, 7, 0, 4], ![0, 7, 0, 3, 4, 0, 7, 0],
    ![0, 7, 0, 4, 0, 7, 0, 3], ![0, 4, 0, 7, 3, 0, 7, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 3, 3, 3, 3], ![0, 0, 0, 0, 2, 4, 2, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 4, 0, 0, 7, 3, 0], ![0, 4, 7, 0, 3, 0, 0, 7],
    ![0, 7, 3, 0, 4, 0, 0, 7], ![0, 3, 7, 0, 0, 7, 4, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 3, 7, 0, 0, 7, 4], ![0, 2, 0, 4, 0, 3, 0, 3],
    ![0, 4, 7, 0, 0, 3, 7, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 3, 0, 0, 4, 7],
    ![0, 4, 0, 7, 0, 3, 0, 7], ![0, 2, 4, 0, 0, 3, 3, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 4, 0, 0, 7, 3], ![0, 3, 0, 3, 2, 0, 4, 0],
    ![0, 3, 7, 0, 4, 0, 0, 7], ![0, 0, 4, 7, 0, 0, 3, 7], ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 3, 3, 0, 2, 0, 0, 4], ![0, 3, 0, 7, 4, 0, 7, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 3, 4, 7, 0, 0], ![0, 4, 0, 2, 0, 3, 0, 3],
    ![0, 7, 4, 0, 3, 0, 0, 7], ![0, 7, 0, 3, 0, 4, 0, 7], ![0, 3, 3, 0, 2, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 4, 3, 7, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 4, 7, 3, 7, 0, 0], ![0, 3, 0, 3, 2, 0, 4, 0],
    ![0, 7, 3, 0, 0, 4, 7, 0], ![0, 4, 2, 0, 0, 3, 3, 0], ![0, 7, 0, 4, 3, 0, 7, 0],
    ![0, 0, 3, 7, 4, 7, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]]

private def gl32Ord (t : Fin 8 × Fin 8 × Fin 8) : ℕ := gl32OrdTable t.1 t.2.1 t.2.2

private theorem isBasisImage_iff : ∀ t, IsBasisImage t ↔ gl32Ord t ≠ 0 := by
  decide +kernel

private theorem gl32Ord_spec : ∀ t, gl32Ord t ≠ 0 →
    (∀ x, (linFun t)^[gl32Ord t] x = x) ∧
      ∀ m < gl32Ord t, 0 < m → ¬ ∀ x, (linFun t)^[m] x = x := by
  decide +kernel

private theorem orderOf_gl32 (σ : gl32) : orderOf σ = gl32Ord (gl32Equiv σ).1 := by
  have h0 := (isBasisImage_iff _).1 (gl32Equiv σ).2
  obtain ⟨hpow, hmin⟩ := gl32Ord_spec _ h0
  rw [orderOf_eq_iff (Nat.pos_of_ne_zero h0)]
  exact ⟨(gl32_pow_eq_one_iff σ _).2 hpow,
    fun m hm hm0 h => hmin m hm hm0 ((gl32_pow_eq_one_iff σ m).1 h)⟩

private theorem card_gl32_pow_eq_one (d : ℕ) :
    Nat.card {σ : gl32 // σ ^ d = 1} =
      (Finset.univ.filter fun t => gl32Ord t ≠ 0 ∧ gl32Ord t ∣ d).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have e1 : {σ : gl32 // σ ^ d = 1} ≃ {t : {t // IsBasisImage t} // gl32Ord t.1 ∣ d} :=
    gl32Equiv.subtypeEquiv fun σ => by rw [← orderOf_dvd_iff_pow_eq_one, orderOf_gl32]
  have e2 : {t : {t // IsBasisImage t} // gl32Ord t.1 ∣ d} ≃
      {t // IsBasisImage t ∧ gl32Ord t ∣ d} :=
    Equiv.subtypeSubtypeEquivSubtypeInter (fun t => IsBasisImage t) (fun t => gl32Ord t ∣ d)
  exact Nat.card_congr (e1.trans (e2.trans (Equiv.subtypeEquivRight fun t => by
    rw [isBasisImage_iff])))

private theorem card_gl32 : Nat.card gl32 = 168 := by
  rw [Nat.card_congr (gl32Equiv.trans (Equiv.subtypeEquivRight isBasisImage_iff)),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private def gl32x : gl32 :=
  ⟨⟨![0, 1, 2, 3, 5, 4, 7, 6], ![0, 1, 2, 3, 5, 4, 7, 6], by decide, by decide⟩,
    fun x y => by revert x y; decide⟩
private def gl32y : gl32 :=
  ⟨⟨![0, 2, 4, 6, 1, 3, 5, 7], ![0, 4, 1, 5, 2, 6, 3, 7], by decide, by decide⟩,
    fun x y => by revert x y; decide⟩
private def gl32z : gl32 :=
  ⟨⟨![0, 2, 1, 3, 4, 6, 5, 7], ![0, 2, 1, 3, 4, 6, 5, 7], by decide, by decide⟩,
    fun x y => by revert x y; decide⟩

/-- `GL(3, 2)` is not soluble: a nontrivial element is a commutator of two of its conjugates. -/
private theorem not_isSolvable_gl32 : ¬ Group.IsSolvable gl32 := by
  have key : gl32x = gl32z * ⁅gl32x, gl32y * gl32x * gl32y⁻¹⁆ * gl32z⁻¹ := by decide
  refine Group.not_isSolvable_of_mem_derivedSeries (show gl32x ≠ 1 by decide) fun n => ?_
  induction n with
  | zero => exact Subgroup.mem_top gl32x
  | succ n ih =>
    rw [key, (Subgroup.derivedSeries_normal _ _).mem_comm_iff, inv_mul_cancel_left]
    exact Subgroup.commutator_mem_commutator ih
      ((Subgroup.derivedSeries_normal _ _).conj_mem _ ih _)

/-! ### The types of the small groups

The values at the divisors of `168` are those of Tables 2 and 4 of Piwek's paper. -/

private theorem card_GL32 (n : ℕ) : Nat.card {x : gl32 // x ^ n = 1} =
    tbl [1, 22, 57, 64, 78, 49, 64, 120, 70, 105, 120, 112, 126, 112, 168, 168]
      (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 84 _ (by norm_num) (by decide) ?_ ?_ n
  · intro d hd
    rw [card_gl32_pow_eq_one]
    revert d
    decide +kernel
  · rw [card_gl32]
    decide +kernel

private theorem card_C2 (n : ℕ) : Nat.card {x : C 2 // x ^ n = 1} =
    tbl [1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 2 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C3 (n : ℕ) : Nat.card {x : C 3 // x ^ n = 1} =
    tbl [1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 3] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 3 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_Dic3 (n : ℕ) : Nat.card {x : QuaternionGroup 3 // x ^ n = 1} =
    tbl [1, 2, 3, 8, 6, 1, 8, 12, 2, 3, 12, 8, 6, 8, 12, 12] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 12 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_A4 (n : ℕ) : Nat.card {x : A4 // x ^ n = 1} =
    tbl [1, 4, 9, 4, 12, 1, 4, 12, 4, 9, 12, 4, 12, 4, 12, 12] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 6 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_SD16 (n : ℕ) : Nat.card {x : SD16 // x ^ n = 1} =
    tbl [1, 6, 1, 12, 6, 1, 16, 12, 6, 1, 16, 12, 6, 16, 12, 16] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 8 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C7sC3 (n : ℕ) : Nat.card {x : F21 // x ^ n = 1} =
    tbl [1, 1, 15, 1, 15, 7, 1, 15, 7, 21, 15, 7, 21, 7, 21, 21] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 21 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : C 3, g ^ 3 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_D12 (n : ℕ) : Nat.card {x : DihedralGroup 12 // x ^ n = 1} =
    tbl [1, 14, 3, 16, 18, 1, 16, 24, 14, 3, 24, 16, 18, 16, 24, 24] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 12 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C3sD4 (n : ℕ) : Nat.card {x : C3sD4 // x ^ n = 1} =
    tbl [1, 10, 3, 16, 18, 1, 16, 24, 10, 3, 24, 16, 18, 16, 24, 24] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 12 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : DihedralGroup 4, g ^ 4 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_Dic7 (n : ℕ) : Nat.card {x : QuaternionGroup 7 // x ^ n = 1} =
    tbl [1, 2, 1, 16, 2, 7, 16, 16, 14, 7, 16, 28, 14, 28, 28, 28] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 28 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_F7 (n : ℕ) : Nat.card {x : F7 // x ^ n = 1} =
    tbl [1, 8, 15, 8, 36, 7, 8, 36, 14, 21, 36, 14, 42, 14, 42, 42] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 42 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : C 6, g ^ 6 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_D21 (n : ℕ) : Nat.card {x : DihedralGroup 21 // x ^ n = 1} =
    tbl [1, 22, 3, 22, 24, 7, 22, 24, 28, 21, 24, 28, 42, 28, 42, 42] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 42 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_D24 (n : ℕ) : Nat.card {x : DihedralGroup 24 // x ^ n = 1} =
    tbl [1, 26, 3, 28, 30, 1, 32, 36, 26, 3, 48, 28, 30, 32, 36, 48] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 24 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_D28 (n : ℕ) : Nat.card {x : DihedralGroup 28 // x ^ n = 1} =
    tbl [1, 30, 1, 32, 30, 7, 32, 32, 42, 7, 32, 56, 42, 56, 56, 56] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 28 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_Dic7sC6 (n : ℕ) : Nat.card {x : Dic7sC6 // x ^ n = 1} =
    tbl [1, 18, 15, 32, 102, 7, 32, 144, 42, 21, 144, 56, 126, 56, 168, 168] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 84 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : DihedralGroup 4 × C 3, g ^ 12 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C14A4 (n : ℕ) : Nat.card {x : C14A4 // x ^ n = 1} =
    tbl [1, 2, 57, 8, 114, 7, 8, 120, 14, 63, 120, 56, 126, 56, 168, 168] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 84 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : SL23, g ^ 12 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C7sF7 (n : ℕ) : Nat.card {x : C7sF7 // x ^ n = 1} =
    tbl [1, 50, 15, 50, 162, 49, 50, 162, 98, 147, 162, 98, 294, 98, 294, 294] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 42 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : F7, g ^ 42 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_D12D7 (n : ℕ) : Nat.card {x : D12D7 // x ^ n = 1} =
    tbl [1, 14, 3, 100, 18, 7, 128, 108, 98, 21, 192, 196, 126, 224, 252, 336] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 168 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : P48, g ^ 24 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C4 (n : ℕ) : Nat.card {x : C 4 // x ^ n = 1} =
    tbl [1, 2, 1, 4, 2, 1, 4, 4, 2, 1, 4, 4, 2, 4, 4, 4] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 4 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_D3 (n : ℕ) : Nat.card {x : DihedralGroup 3 // x ^ n = 1} =
    tbl [1, 4, 3, 4, 6, 1, 4, 6, 4, 3, 6, 4, 6, 4, 6, 6] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 6 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C7 (n : ℕ) : Nat.card {x : C 7 // x ^ n = 1} =
    tbl [1, 1, 1, 1, 1, 7, 1, 1, 7, 7, 1, 7, 7, 7, 7, 7] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 7 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_D4 (n : ℕ) : Nat.card {x : DihedralGroup 4 // x ^ n = 1} =
    tbl [1, 6, 1, 8, 6, 1, 8, 8, 6, 1, 8, 8, 6, 8, 8, 8] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 4 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_D7 (n : ℕ) : Nat.card {x : DihedralGroup 7 // x ^ n = 1} =
    tbl [1, 8, 1, 8, 8, 7, 8, 8, 14, 7, 8, 14, 14, 14, 14, 14] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 14 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_SL23 (n : ℕ) : Nat.card {x : SL23 // x ^ n = 1} =
    tbl [1, 2, 9, 8, 18, 1, 8, 24, 2, 9, 24, 8, 18, 8, 24, 24] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 12 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C24sC2 (n : ℕ) : Nat.card {x : P48 // x ^ n = 1} =
    tbl [1, 14, 3, 28, 18, 1, 32, 36, 14, 3, 48, 28, 18, 32, 36, 48] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 24 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : SD16, g ^ 8 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C7sD4 (n : ℕ) : Nat.card {x : C7sD4 // x ^ n = 1} =
    tbl [1, 18, 1, 32, 18, 7, 32, 32, 42, 7, 32, 56, 42, 56, 56, 56] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 28 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : DihedralGroup 4, g ^ 4 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C7sC12 (n : ℕ) : Nat.card {x : C7sC12 // x ^ n = 1} =
    tbl [1, 2, 15, 16, 30, 7, 16, 72, 14, 21, 72, 28, 42, 28, 84, 84] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 84 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : C 12, g ^ 12 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_Dic21 (n : ℕ) : Nat.card {x : QuaternionGroup 21 // x ^ n = 1} =
    tbl [1, 2, 3, 44, 6, 7, 44, 48, 14, 21, 48, 56, 42, 56, 84, 84] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 84 _ (by norm_num) (by decide) ?_ ?_ n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C7sA4 (n : ℕ) : Nat.card {x : C7sA4 // x ^ n = 1} =
    tbl [1, 4, 57, 4, 60, 7, 4, 60, 28, 63, 60, 28, 84, 28, 84, 84] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 42 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : A4, g ^ 6 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C7sD7 (n : ℕ) : Nat.card {x : C7sD7 // x ^ n = 1} =
    tbl [1, 50, 1, 50, 50, 49, 50, 50, 98, 49, 50, 98, 98, 98, 98, 98] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 14 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : DihedralGroup 7, g ^ 14 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C4sF7 (n : ℕ) : Nat.card {x : C4sF7 // x ^ n = 1} =
    tbl [1, 30, 15, 32, 114, 7, 32, 144, 42, 21, 144, 56, 126, 56, 168, 168] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 84 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : DihedralGroup 4 × C 3, g ^ 12 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C21sD4 (n : ℕ) : Nat.card {x : C21sD4 // x ^ n = 1} =
    tbl [1, 22, 3, 64, 54, 7, 64, 96, 70, 21, 96, 112, 126, 112, 168, 168] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 84 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : C3sD4, g ^ 12 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C7sD12 (n : ℕ) : Nat.card {x : C7sD12 // x ^ n = 1} =
    tbl [1, 50, 3, 64, 54, 7, 64, 96, 98, 21, 96, 112, 126, 112, 168, 168] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 84 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : DihedralGroup 12, g ^ 12 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_F8sC3 (n : ℕ) : Nat.card {x : AGL18 // x ^ n = 1} =
    tbl [1, 8, 57, 8, 120, 49, 8, 120, 56, 105, 120, 56, 168, 56, 168, 168] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 42 _ (by norm_num) (by decide) ?_ ?_ n
  · intro d hd
    rw [card_pow_eq_one_cover agl18_cover d, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    revert d
    decide +kernel
  · rw [Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_D8sD7 (n : ℕ) : Nat.card {x : D8sD7 // x ^ n = 1} =
    tbl [1, 52, 1, 96, 52, 7, 128, 96, 112, 7, 128, 168, 112, 224, 168, 224] (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 56 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : P32, g ^ 8 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

private theorem card_C7sD24 (n : ℕ) : Nat.card {x : C7sD24 // x ^ n = 1} =
    tbl [1, 98, 3, 100, 102, 7, 128, 108, 182, 21, 192, 196, 210, 224, 252, 336]
      (Nat.gcd n 168) := by
  refine card_pow_eq_one_eq_tbl 168 _ (by norm_num) (by decide) ?_ ?_ n
  · have hG : ∀ g : DihedralGroup 24, g ^ 24 = 1 := by decide +kernel
    simp only [card_ext_pow_eq_one_gcd _ _ hG]
    decide +kernel
  · rw [SemidirectProduct.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide +kernel

/-! ### Piwek's groups -/

/-- Piwek's group that is not soluble: three copies of `GL(3, 2)` and the other groups of his
Table 1b, with their multiplicities. -/
private abbrev NonSoluble : Type :=
  (Fin 3 → gl32) × (Fin 21 → C 2) × (Fin 3 → C 3) × (Fin 6 → QuaternionGroup 3) × (Fin 21 → A4) ×
    (Fin 3 → SD16) × (Fin 4 → F21) × (Fin 6 → DihedralGroup 12) × (Fin 6 → C3sD4) ×
    (Fin 15 → QuaternionGroup 7) × (Fin 18 → F7) × (Fin 6 → DihedralGroup 21) ×
    (Fin 3 → DihedralGroup 24) × (Fin 27 → DihedralGroup 28) × (Fin 3 → Dic7sC6) ×
    (Fin 21 → C14A4) × (Fin 2 → C7sF7) × (Fin 3 → D12D7)

/-- Piwek's soluble group: the groups of his Table 1a, with their multiplicities. -/
private abbrev Soluble : Type :=
  (Fin 9 → C 4) × (Fin 6 → DihedralGroup 3) × (Fin 1 → C 7) × (Fin 9 → DihedralGroup 4) ×
    (Fin 18 → DihedralGroup 7) × (Fin 21 → SL23) × (Fin 3 → P48) × (Fin 3 → C7sD4) ×
    (Fin 6 → C7sC12) × (Fin 6 → QuaternionGroup 21) × (Fin 21 → C7sA4) × (Fin 2 → C7sD7) ×
    (Fin 21 → C4sF7) × (Fin 9 → C21sD4) × (Fin 6 → C7sD12) × (Fin 3 → AGL18) × (Fin 3 → D8sD7) ×
    (Fin 3 → C7sD24)

private theorem sameType_nonSoluble_soluble : SameType NonSoluble Soluble := by
  intro n _
  simp only [card_pow_eq_one_prod, card_pow_eq_one_pi,
    card_GL32, card_C2, card_C3, card_Dic3, card_A4, card_SD16, card_C7sC3, card_D12, card_C3sD4,
    card_Dic7, card_F7, card_D21, card_D24, card_D28, card_Dic7sC6, card_C14A4, card_C7sF7,
    card_D12D7, card_C4, card_D3, card_C7, card_D4, card_D7, card_SL23, card_C24sC2, card_C7sD4,
    card_C7sC12, card_Dic21, card_C7sA4, card_C7sD7, card_C4sF7, card_C21sD4, card_C7sD12,
    card_F8sC3, card_D8sD7, card_C7sD24]
  have hd : Nat.gcd n 168 ∈ Nat.divisors 168 :=
    Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right n 168, by norm_num⟩
  generalize Nat.gcd n 168 = d at hd ⊢
  revert d
  decide +kernel

private theorem not_isSolvable_nonSoluble : ¬ Group.IsSolvable NonSoluble := by
  intro h
  apply not_isSolvable_gl32
  have h1 : Group.IsSolvable (Fin 3 → gl32) :=
    Group.isSolvable_of_surjective (G := NonSoluble) (f := MonoidHom.fst _ _)
      fun x => ⟨(x, 1), rfl⟩
  exact Group.isSolvable_of_surjective (f := Pi.evalMonoidHom (fun _ : Fin 3 => gl32) 0)
    fun g => ⟨fun _ => g, rfl⟩

set_option synthInstance.maxSize 1024 in
private theorem finite_nonSoluble : Finite NonSoluble := inferInstance

set_option synthInstance.maxSize 1024 in
private theorem finite_soluble : Finite Soluble := inferInstance

set_option synthInstance.maxSize 1024 in
private theorem isSolvable_soluble : Group.IsSolvable Soluble := inferInstance

/--
**Solubility is not determined by the type.** The answer to Kourovka Problem 12.37 is negative:
there are finite groups $G$ and $H$ of the same type such that $H$ is soluble and $G$ is not
soluble.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 12.37 (J. G. Thompson; A. S. Kondratiev,
W. J. Shi); resolution: P. Piwek, Algebra Number Theory 19 (2025), no. 8, 1663-1670, the Kourovka
Notebook (21st issue) marks 12.37 solved: No, not always.
-/
theorem solubleOfSameTypeAsSoluble_refuted : ¬ solubleOfSameTypeAsSoluble := fun h =>
  not_isSolvable_nonSoluble (@h NonSoluble Soluble _ finite_nonSoluble _ finite_soluble
    isSolvable_soluble sameType_nonSoluble_soluble)

end MathlibExt.GroupTheory.SolubleTypeRecognitionKourovka12Problem37Wanted
