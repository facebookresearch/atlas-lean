/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.Aut
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Ring

/-!
# Nonabelian subgroups of p-th powers for odd primes

An affine group over the truncated polynomial ring over `ZMod p` gives a counterexample to the
odd-prime form of Kourovka Problem 21.137. Its exponent is `p ^ 2`, and its literal set of
`p`-th powers forms a nonabelian subgroup.
-/

namespace MathlibExt.GroupTheory.PthPowersSubgroupPowerfulKourovka21Problem137Wanted

/-- **Kourovka 21.137, odd-prime form.** The proposition that there is an odd prime $p$ such that
for every finite $p$-group $G$ of exponent $p^2$ and every subgroup $P$ of $G$ whose underlying
set is exactly the set $\{x^p : x \in G\}$ of $p$-th powers in $G$, the subgroup $P$ is abelian.

Kourovka Problem 21.137 (L. Wilson) asks this for each odd prime; it is stated here for some odd
prime, so that its refutation covers all of them. -/
@[expose] public def pthPowersSubgroupAbelianExponentPSq : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    Monoid.exponent G = p ^ 2 → ∀ P : Subgroup G, (P : Set G) = {g | ∃ x : G, x ^ p = g} →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x

open Polynomial
open scoped BigOperators

noncomputable section

variable (p : ℕ) [Fact p.Prime]

local notation "F" => ZMod p
local notation "f" => (X ^ (2 * p) : (ZMod p)[X])
local notation "A" => AdjoinRoot (X ^ (2 * p) : (ZMod p)[X])

private abbrev t : A := AdjoinRoot.root f

private lemma t_nil : t p ^ (2 * p) = 0 := by
  rw [show t p = AdjoinRoot.root f from rfl, ← AdjoinRoot.mk_X, ← map_pow]
  exact AdjoinRoot.mk_self

private lemma t_pow_ne (n : ℕ) (hn : n < 2 * p) : t p ^ n ≠ 0 := by
  rw [show t p = AdjoinRoot.root f from rfl, ← AdjoinRoot.mk_X, ← map_pow]
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_X_pow _) (pow_ne_zero _ X_ne_zero)
  simpa

private lemma prime_pos : 0 < p := (Fact.out : p.Prime).pos

private def atZero : A →+* F :=
  AdjoinRoot.lift (RingHom.id _) 0 (by simp [zero_pow (show 2 * p ≠ 0 by
    have := prime_pos p
    omega)])

@[simp] private lemma atZero_of (a : F) : atZero p (AdjoinRoot.of f a) = a :=
  AdjoinRoot.lift_of _

@[simp] private lemma atZero_t : atZero p (t p) = 0 := AdjoinRoot.lift_root _

private local instance ringChar : CharP A p :=
  charP_of_injective_ringHom
    (Function.LeftInverse.injective (atZero_of p)) p

private local instance ringFinite : Finite A := by
  let b := AdjoinRoot.powerBasisAux' (monic_X_pow (R := F) (2 * p))
  exact Finite.of_equiv _ b.equivFun.toEquiv.symm

-- Substitution is given by t ↦ t / (1 + a * t).
private def linearUnit (a : F) : Aˣ :=
  ((show IsNilpotent (AdjoinRoot.of f a * t p) from
    ⟨2 * p, by rw [mul_pow, t_nil, mul_zero]⟩).isUnit_one_add).unit

@[simp] private lemma linearUnit_val (a : F) :
    (linearUnit p a : A) = 1 + AdjoinRoot.of f a * t p :=
  IsUnit.unit_spec _

private def shiftHom (a : F) : A →+* A :=
  AdjoinRoot.lift (AdjoinRoot.of f) (t p * ↑(linearUnit p a)⁻¹) (by
    simp [mul_pow, t_nil])

@[simp] private lemma shiftHom_t (a : F) :
    shiftHom p a (t p) = t p * ↑(linearUnit p a)⁻¹ := AdjoinRoot.lift_root _

@[simp] private lemma shiftHom_of (a b : F) :
    shiftHom p a (AdjoinRoot.of f b) = AdjoinRoot.of f b := AdjoinRoot.lift_of _

private lemma hom_ext {S : Type} [Semiring S] {g h : A →+* S}
    (hC : ∀ c : F, g (AdjoinRoot.of f c) = h (AdjoinRoot.of f c))
    (ht : g (t p) = h (t p)) : g = h := by
  apply RingHom.ext
  intro x
  induction x using AdjoinRoot.induction_on with
  | ih q =>
    have he : g.comp (AdjoinRoot.mk f) = h.comp (AdjoinRoot.mk f) :=
      Polynomial.ringHom_ext (by simpa [AdjoinRoot.mk_C] using hC) ht
    exact DFunLike.congr_fun he q

@[simp] private lemma linearUnit_zero : linearUnit p 0 = 1 := by
  ext
  simp

private lemma shiftHom_unit (a b : F) :
    Units.map (shiftHom p a).toMonoidHom (linearUnit p b) =
      linearUnit p (a + b) / linearUnit p a := by
  apply eq_div_iff_mul_eq'.2
  apply Units.ext
  change shiftHom p a (↑(linearUnit p b)) * ↑(linearUnit p a) = ↑(linearUnit p (a + b))
  simp only [linearUnit_val, map_add, map_one, map_mul, shiftHom_of, shiftHom_t]
  rw [show (1 + AdjoinRoot.of f a * t p) = ↑(linearUnit p a) from (linearUnit_val p a).symm]
  calc
    _ = (linearUnit p a : A) + AdjoinRoot.of f b * t p := by
      rw [add_mul, one_mul, mul_assoc (AdjoinRoot.of f b), mul_assoc (t p),
        Units.inv_mul, mul_one]
    _ = _ := by rw [linearUnit_val]; ring

@[simp] private lemma shiftHom_zero : shiftHom p 0 = RingHom.id A := by
  apply hom_ext p <;> simp

private lemma shiftHom_add (a b : F) :
    (shiftHom p a).comp (shiftHom p b) = shiftHom p (a + b) := by
  apply hom_ext p
  · simp
  · simp only [RingHom.comp_apply, shiftHom_t, map_mul]
    have h := congrArg (fun v : Aˣ => ((v⁻¹ : Aˣ) : A)) (shiftHom_unit p a b)
    simp only [← map_inv, Units.coe_map] at h
    change shiftHom p a (↑(linearUnit p b)⁻¹) = _ at h
    rw [h, inv_div, div_eq_mul_inv, Units.val_mul]
    calc
      _ = t p * (↑(linearUnit p a)⁻¹ * ↑(linearUnit p a)) *
          ↑(linearUnit p (a + b))⁻¹ := by ring
      _ = _ := by rw [Units.inv_mul, mul_one]

private def shift (a : F) : RingAut A :=
  RingEquiv.ofRingHom (shiftHom p a) (shiftHom p (-a))
    (by rw [shiftHom_add, add_neg_cancel, shiftHom_zero])
    (by rw [shiftHom_add, neg_add_cancel, shiftHom_zero])

@[simp] private lemma shift_apply (a : F) (x : A) :
    shift p a x = shiftHom p a x := rfl

private lemma shift_add (a b : F) (x : A) :
    shift p a (shift p b x) = shift p (a + b) x :=
  DFunLike.congr_fun (shiftHom_add p a b) x

private def shiftUnit (a : F) : Aˣ →* Aˣ :=
  Units.map (shiftHom p a).toMonoidHom

@[simp] private lemma shiftUnit_val (a : F) (u : Aˣ) :
    (shiftUnit p a u : A) = shiftHom p a u := rfl

@[simp] private lemma shiftUnit_zero (u : Aˣ) : shiftUnit p 0 u = u := by
  apply Units.ext
  simp [shiftUnit_val]

private lemma shiftUnit_add (a b : F) (u : Aˣ) :
    shiftUnit p a (shiftUnit p b u) = shiftUnit p (a + b) u := by
  apply Units.ext
  exact shift_add p a b u

private def unitAction : Multiplicative F →* MulAut Aˣ where
  toFun a :=
    { shiftUnit p a.toAdd with
      invFun := shiftUnit p (-a.toAdd)
      left_inv u := by exact (shiftUnit_add p _ _ _).trans (by simp)
      right_inv u := by exact (shiftUnit_add p _ _ _).trans (by simp) }
  map_one' := by
    apply MulEquiv.ext
    exact shiftUnit_zero p
  map_mul' a b := by
    apply MulEquiv.ext
    intro u
    exact (shiftUnit_add p a.toAdd b.toAdd u).symm

local notation "L" => (Aˣ ⋊[unitAction p] Multiplicative F)

@[simp] private lemma unitAction_apply (a : Multiplicative F) (u : Aˣ) :
    unitAction p a u = shiftUnit p a.toAdd u := rfl

private def scalarAction (u : Aˣ) : A ≃+ A where
  toFun x := (u : A) * x
  invFun x := (↑u⁻¹ : A) * x
  left_inv x := by
    change (↑u⁻¹ : A) * ((u : A) * x) = x
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    change (u : A) * ((↑u⁻¹ : A) * x) = x
    rw [← mul_assoc, Units.mul_inv, one_mul]
  map_add' := mul_add _

private def affineAction : L →* MulAut (Multiplicative A) where
  toFun l := ((shift p l.right.toAdd).toAddEquiv.trans (scalarAction p l.left)).toMultiplicative
  map_one' := by
    ext x
    change (1 : A) * shiftHom p 0 x.toAdd = x.toAdd
    simp
  map_mul' a b := by
    ext x
    change ((a.left * unitAction p a.right b.left : Aˣ) : A) *
      shiftHom p (a.right.toAdd + b.right.toAdd) x.toAdd =
        (a.left : A) * shiftHom p a.right.toAdd
          ((b.left : A) * shiftHom p b.right.toAdd x.toAdd)
    rw [Units.val_mul, unitAction_apply, shiftUnit_val, map_mul, ← mul_assoc]
    rw [← DFunLike.congr_fun (shiftHom_add p a.right.toAdd b.right.toAdd) x.toAdd]
    rfl

local notation "H" => (Multiplicative A ⋊[affineAction p] L)

private def affine (v : A) (u : Aˣ) (a : F) : H :=
  ⟨Multiplicative.ofAdd v, ⟨u, Multiplicative.ofAdd a⟩⟩

@[simp] private lemma affine_mul (v w : A) (u z : Aˣ) (a b : F) :
    affine p v u a * affine p w z b =
      affine p (v + (u : A) * shiftHom p a w) (u * shiftUnit p a z) (a + b) := rfl

private lemma affine_one : affine p 0 1 0 = 1 := rfl

-- Restrict the affine group to linear multipliers of norm one under substitution.
private def norm : Aˣ →* Aˣ where
  toFun u := ∏ a : F, shiftUnit p a u
  map_one' := by simp
  map_mul' u v := by simp [Finset.prod_mul_distrib]

private lemma norm_shift (a : F) (u : Aˣ) : norm p (shiftUnit p a u) = norm p u := by
  change (∏ b : F, shiftUnit p b (shiftUnit p a u)) = ∏ b : F, shiftUnit p b u
  simp only [shiftUnit_add]
  exact Fintype.prod_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

@[to_additive]
private lemma prod_zmod {M : Type} [CommMonoid M] (g : F → M) :
    (∏ n ∈ Finset.range p, g n) = ∏ a : F, g a := by
  rw [← Fin.prod_univ_eq_prod_range]
  exact Fintype.prod_equiv (ZMod.finEquiv p).toEquiv _ _ (fun i => by
    congr 1
    cases p with
    | zero => exact Fin.elim0 i
    | succ q => exact ZMod.natCast_zmod_val ((ZMod.finEquiv (q + 1)) i))

private lemma norm_linear (a : F) : norm p (linearUnit p a) = 1 := by
  change (∏ b : F, shiftUnit p b (linearUnit p a)) = 1
  simp only [shiftUnit, shiftHom_unit]
  rw [Finset.prod_div_distrib]
  exact div_eq_one.mpr (Fintype.prod_equiv (Equiv.addRight a) _ _ (fun _ => rfl))

private def fullNorm : H →* Aˣ where
  toFun g := norm p g.right.left
  map_one' := (norm p).map_one
  map_mul' a b := by
    change norm p (a.right.left * shiftUnit p a.right.right.toAdd b.right.left) = _
    rw [map_mul, norm_shift]

local notation "G" => MonoidHom.ker (fullNorm p)

private local instance finiteGroup : Finite H := by
  have : Finite L := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  exact Finite.of_equiv _ SemidirectProduct.equivProd.symm

private def actionEnd (u : Aˣ) (a : F) : AddMonoid.End A :=
  ((shift p a).toAddEquiv.trans (scalarAction p u)).toAddMonoidHom

@[simp] private lemma actionEnd_apply (u : Aˣ) (a : F) (x : A) :
    actionEnd p u a x = (u : A) * shiftHom p a x := rfl

private def iterUnit (u : Aˣ) (a : F) (n : ℕ) : Aˣ :=
  ∏ i ∈ Finset.range n, shiftUnit p ((i : F) * a) u

private lemma actionEnd_pow (u : Aˣ) (a : F) (n : ℕ) (x : A) :
    (actionEnd p u a ^ n) x =
      (iterUnit p u a n : A) * shiftHom p ((n : F) * a) x := by
  induction n generalizing x with
  | zero => simp [iterUnit]
  | succ n ih =>
    rw [pow_succ]
    change (actionEnd p u a ^ n) (actionEnd p u a x) = _
    have hiter : iterUnit p u a (n + 1) =
        iterUnit p u a n * shiftUnit p ((n : F) * a) u := Finset.prod_range_succ _ _
    rw [ih, actionEnd_apply, map_mul,
      ← mul_assoc, hiter, Units.val_mul, shiftUnit_val,
      Nat.cast_succ, add_mul, one_mul]
    congr 1
    exact shift_add p _ _ _

private lemma affine_pow (v : A) (u : Aˣ) (a : F) (n : ℕ) :
    affine p v u a ^ n =
      affine p (∑ i ∈ Finset.range n, (actionEnd p u a ^ i) v)
        (iterUnit p u a n) ((n : F) * a) := by
  induction n with
  | zero => simp [iterUnit, affine_one]
  | succ n ih =>
    rw [pow_succ, ih, affine_mul, Finset.sum_range_succ, actionEnd_pow,
      Nat.cast_succ, add_mul, one_mul]
    congr 1
    exact (Finset.prod_range_succ _ _).symm

private lemma iterUnit_zero (u : Aˣ) (n : ℕ) : iterUnit p u 0 n = u ^ n := by
  simp [iterUnit]

private lemma iterUnit_prime (u : Aˣ) (a : F) (ha : a ≠ 0) :
    iterUnit p u a p = norm p u := by
  calc
    _ = ∏ b : F, shiftUnit p (b * a) u :=
      prod_zmod p (fun b => shiftUnit p (b * a) u)
    _ = _ := Fintype.prod_equiv (Equiv.mulRight₀ a ha) _ _ (fun _ => rfl)

private lemma iterUnit_linear (n k : ℕ) :
    iterUnit p (linearUnit p 1 ^ k) 1 n = linearUnit p n ^ k := by
  simp only [iterUnit, mul_one, map_pow, shiftUnit, shiftHom_unit, ← Nat.cast_succ]
  let g (i : ℕ) := linearUnit p (i : F)
  change (∏ i ∈ Finset.range n, powMonoidHom k (g (i + 1) / g i)) = (g n) ^ k
  rw [← map_prod (powMonoidHom k), Finset.prod_range_div]
  simp [g]

private lemma atZero_shift (a : F) (x : A) : atZero p (shiftHom p a x) = atZero p x := by
  have he : (atZero p).comp (shiftHom p a) = atZero p := by
    apply hom_ext p <;> simp
  exact DFunLike.congr_fun he x

private lemma atZero_eq_zero_iff (x : A) : atZero p x = 0 ↔ t p ∣ x := by
  constructor
  · induction x using AdjoinRoot.induction_on with
    | ih q =>
      intro h
      have hq : X ∣ q := X_dvd_iff.mpr (by
        simpa [atZero, AdjoinRoot.lift_mk, eval₂_at_zero] using h)
      obtain ⟨r, hr⟩ := hq
      refine ⟨AdjoinRoot.mk f r, ?_⟩
      rw [hr, map_mul, AdjoinRoot.mk_X]
  · rintro ⟨y, rfl⟩
    simp

private lemma atZero_norm (u : Aˣ) : atZero p (norm p u) = atZero p u := by
  change ((atZero p).toMonoidHom.comp (Units.coeHom A)) (∏ a : F, shiftUnit p a u) = _
  rw [map_prod]
  simp [atZero_shift]

private lemma atZero_eq_one (u : Aˣ) (hu : norm p u = 1) : atZero p (u : A) = 1 := by
  rw [← atZero_norm p u, hu, Units.val_one, map_one]

private lemma sub_const_dvd (x : A) : t p ∣ x - AdjoinRoot.of f (atZero p x) := by
  rw [← atZero_eq_zero_iff]
  simp

private lemma unit_pow_prime (u : Aˣ) (hu : norm p u = 1) :
    ∃ c : F, u ^ p = linearUnit p c ^ p := by
  obtain ⟨y, hy⟩ := sub_const_dvd p u
  obtain ⟨z, hz⟩ := sub_const_dvd p y
  simp only [atZero_eq_one p u hu, map_one] at hy
  refine ⟨atZero p y, Units.ext ?_⟩
  simp only [Units.val_pow_eq_pow_val, linearUnit_val]
  have hy' : (u : A) = 1 + t p * y := by linear_combination hy
  have hz' : y = AdjoinRoot.of f (atZero p y) + t p * z := by linear_combination hz
  have ht : (t p ^ p : A) * t p ^ p = 0 := by
    rw [← pow_add, ← two_mul, t_nil p]
  nth_rw 1 [hy', hz']
  simp only [add_pow_char _ _ p, mul_pow, mul_add, mul_comm (t p ^ p)]
  rw [mul_assoc (z ^ p), ht, mul_zero, add_zero]

private lemma linearUnit_pow (c : F) :
    (↑(linearUnit p c ^ p) : A) = 1 + AdjoinRoot.of f c * t p ^ p := by
  simp [linearUnit_val, add_pow_char _ _ p, mul_pow, ← map_pow, ZMod.pow_card]

private lemma iterUnit_prime_sq (c : F) : (linearUnit p c ^ p) ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, linearUnit_pow, add_pow_char _ _ p, mul_pow,
    ← pow_mul, pow_eq_zero_of_le (m := 2 * p) _ (t_nil p), mul_zero, one_pow,
    add_zero, Units.val_one]
  have hp := (Fact.out : p.Prime).two_le
  exact Nat.mul_le_mul_right p hp

private local instance endChar : CharP (AddMonoid.End A) p where
  cast_eq_zero_iff n := by
    rw [← CharP.cast_eq_zero_iff A p n]
    constructor
    · intro h
      have he := DFunLike.congr_fun h (1 : A)
      simpa [nsmul_eq_mul] using he
    · intro h
      ext x
      simp [nsmul_eq_mul, h]

-- In characteristic p, the geometric sum is the (p − 1)-st power of the difference.
private lemma geom_sum_end (T : AddMonoid.End A) :
    (∑ i ∈ Finset.range p, T ^ i) = (T - 1) ^ (p - 1) := by
  have hX : (X : F[X]) - 1 ≠ 0 := sub_ne_zero.mpr (X_ne_C (1 : F))
  have hp := prime_pos p
  have hpoly : (∑ i ∈ Finset.range p, (X : F[X]) ^ i) = (X - 1) ^ (p - 1) := by
    apply mul_right_cancel₀ hX
    rw [geom_sum_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p),
      sub_pow_char (p := p) _ _, one_pow]
  let ofF := ZMod.castHom (dvd_refl p) (AddMonoid.End A)
  have hc (a : F) : Commute (ofF a) T := by
    rw [← ZMod.natCast_zmod_val a, map_natCast]
    exact Nat.cast_commute _ _
  have h := congrArg (Polynomial.eval₂RingHom' ofF T hc) hpoly
  simpa only [map_sum, map_pow, map_sub, map_one, eval₂RingHom'_apply, eval₂_X] using h

private lemma translation_sum (u : Aˣ) (a : F) (v : A) :
    (∑ i ∈ Finset.range p, (actionEnd p u a ^ i) v) =
      ((actionEnd p u a - 1) ^ (p - 1)) v := by
  rw [← geom_sum_end]
  exact (AddMonoidHom.finsetSum_apply _ _ _).symm

private lemma diff_preserves (u : Aˣ) (hu : norm p u = 1) (a : F) {n : ℕ} {x : A}
    (hx : t p ^ n ∣ x) : t p ^ (n + 1) ∣ (actionEnd p u a - 1) x := by
  obtain ⟨y, rfl⟩ := hx
  have h1 : atZero p (↑(linearUnit p a)⁻¹ : A) = 1 := by
    have hh := congrArg (atZero p) (Units.inv_mul (linearUnit p a))
    rw [map_mul, linearUnit_val, map_add, map_one, map_mul, atZero_t, mul_zero,
      add_zero, mul_one] at hh
    exact hh
  have hd : t p ∣ (u : A) * (↑(linearUnit p a)⁻¹ : A) ^ n * shiftHom p a y - y := by
    rw [← atZero_eq_zero_iff]
    simp [h1, atZero_eq_one p u hu, atZero_shift]
  obtain ⟨z, hz⟩ := hd
  refine ⟨z, ?_⟩
  change (u : A) * shiftHom p a (t p ^ n * y) - t p ^ n * y = _
  rw [map_mul, map_pow, shiftHom_t, mul_pow, pow_succ]
  linear_combination (t p ^ n) * hz

private lemma translation_dvd (u : Aˣ) (hu : norm p u = 1) (a : F) (v : A) :
    t p ^ (p - 1) ∣ ∑ i ∈ Finset.range p, (actionEnd p u a ^ i) v := by
  rw [translation_sum]
  suffices ∀ n : ℕ, t p ^ n ∣ ((actionEnd p u a - 1) ^ n) v from this _
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (actionEnd p u a - 1)]
    exact diff_preserves p u hu a ih

private lemma sum_top_pow : (∑ c : F, c ^ (p - 1)) = -1 := by
  classical
  have hp := (Fact.out : p.Prime).one_lt
  rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, zero_pow (by omega), zero_add]
  rw [← Fintype.sum_equiv unitsEquivNeZero (fun u : Fˣ => (u ^ (p - 1) : F))
    (fun c => c.val ^ (p - 1)) (fun _ => rfl)]
  rw [FiniteField.sum_pow_units, ZMod.card, ite_eq_left_iff]
  exact fun h => False.elim (h (dvd_refl _))

private lemma sum_linearUnit_pow :
    (∑ c : F, (linearUnit p c : A) ^ (p - 1)) = -(t p ^ (p - 1)) := by
  classical
  simp only [linearUnit_val, add_comm (1 : A), add_pow, one_pow, mul_pow, mul_one]
  rw [Finset.sum_comm]
  have hp := (Fact.out : p.Prime).one_lt
  calc
    _ = ∑ i ∈ Finset.range (p - 1 + 1),
        AdjoinRoot.of f (∑ c : F, c ^ i) * t p ^ i * ((p - 1).choose i : A) := by
      simp only [map_sum, map_pow, Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_range_succ]
      have hsmall : (∑ i ∈ Finset.range (p - 1),
          AdjoinRoot.of f (∑ c : F, c ^ i) * t p ^ i * ((p - 1).choose i : A)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hcard : i < Fintype.card F - 1 := by simpa using Finset.mem_range.mp hi
        rw [FiniteField.sum_pow_lt_card_sub_one _ i hcard, map_zero, zero_mul, zero_mul]
      simp only [hsmall, sum_top_pow, map_neg, map_one, neg_mul, one_mul, Nat.choose_self,
        Nat.cast_one, zero_add, mul_one]

-- A twisted substitution has a trace supported at one prescribed monomial.
private lemma actionEnd_pow_monomial (m n : ℕ) :
    (actionEnd p (linearUnit p 1 ^ (m + (p - 1))) 1 ^ n) (t p ^ m) =
      t p ^ m * (linearUnit p n : A) ^ (p - 1) := by
  rw [actionEnd_pow, iterUnit_linear, mul_one, map_pow, shiftHom_t, mul_pow,
    Units.val_pow_eq_pow_val, pow_add, mul_comm (t p ^ m), ← mul_assoc]
  calc
    _ = t p ^ m * ((↑(linearUnit p n) : A) ^ (p - 1) *
        ((↑(linearUnit p n) : A) ^ m * (↑(linearUnit p n)⁻¹ : A) ^ m)) := by ring
    _ = _ := by rw [← mul_pow, Units.mul_inv, one_pow, mul_one]

private lemma affine_pow_monomial (m : ℕ) :
    affine p (-(t p ^ m)) (linearUnit p 1 ^ (m + (p - 1))) 1 ^ p =
      affine p (t p ^ (m + (p - 1))) 1 0 := by
  rw [affine_pow, iterUnit_linear, ZMod.natCast_self, linearUnit_zero, one_pow, zero_mul]
  congr 1
  simp only [map_neg, actionEnd_pow_monomial, Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hz := sum_zmod p (fun c => (linearUnit p c : A) ^ (p - 1))
  rw [hz, sum_linearUnit_pow, mul_neg, neg_neg, pow_add]

private lemma isUnit_or_dvd (x : A) : IsUnit x ∨ t p ∣ x := by
  by_cases hx : atZero p x = 0
  · exact Or.inr ((atZero_eq_zero_iff p x).1 hx)
  · left
    obtain ⟨y, hy⟩ := sub_const_dvd p x
    obtain ⟨u, hu⟩ := (isUnit_iff_ne_zero.mpr hx).map (AdjoinRoot.of f)
    have hnil : IsNilpotent ((↑u⁻¹ : A) * t p * y) := by
      exact ⟨2 * p, by rw [mul_pow, mul_pow, t_nil, mul_zero, zero_mul]⟩
    rw [show x = (u : A) * (1 + (↑u⁻¹ : A) * t p * y) by
      rw [mul_add, mul_one, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, hu]
      linear_combination hy]
    exact u.isUnit.mul hnil.isUnit_one_add

private lemma exists_unit_factor (x : A) (hx : x ≠ 0) {n : ℕ} (hn : t p ^ n ∣ x) :
    ∃ m : ℕ, ∃ u : Aˣ, x = t p ^ (m + n) * (u : A) := by
  have h : ∀ k (j : ℕ), k + j = 2 * p → t p ^ j ∣ x →
      ∃ m : ℕ, ∃ u : Aˣ, x = t p ^ (m + j) * (u : A) := by
    intro k
    induction k with
    | zero =>
      intro j hj hd
      obtain ⟨y, hy⟩ := hd
      simp only [zero_add] at hj
      rw [hj, t_nil, zero_mul] at hy
      exact (hx hy).elim
    | succ k ih =>
      intro j hj hd
      obtain ⟨y, hy⟩ := hd
      rcases isUnit_or_dvd p y with ⟨u, rfl⟩ | ⟨z, hz⟩
      · exact ⟨0, u, by simpa using hy⟩
      · obtain ⟨m, u, hu⟩ := ih (j + 1) (by omega)
          ⟨z, by rw [hy, hz, pow_succ, mul_assoc]⟩
        exact ⟨m + 1, u, by simpa only [add_right_comm m 1 j, add_assoc] using hu⟩
  have hnlt : n < 2 * p := by
    by_contra! hle
    obtain ⟨y, hy⟩ := hn
    exact hx (by rw [hy, pow_eq_zero_of_le hle (t_nil p), zero_mul])
  exact h (2 * p - n) n (by omega) hn

local notation:max "linPow" c:arg => (linearUnit p c ^ p)

private lemma linPow_add (c d : F) :
    linPow (c + d) = linPow c * linPow d := by
  apply Units.ext
  simp only [Units.val_mul, linearUnit_pow, map_add]
  have ht : (t p ^ p : A) * t p ^ p = 0 := by
    rw [← pow_add, ← two_mul, t_nil p]
  linear_combination -(AdjoinRoot.of f c * AdjoinRoot.of f d) * ht

private lemma linPow_zero : linPow (0 : F) = 1 := by
  simp

private lemma linPow_neg (c : F) : linPow (-c) = (linPow c)⁻¹ := by
  apply (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← linPow_add, add_neg_cancel, linPow_zero]

private lemma affine_mul_zero_shift (v w : A) (u z : Aˣ) :
    affine p v u 0 * affine p w z 0 =
      affine p (v + (u : A) * w) (u * z) 0 := by
  simp

private lemma affine_inv_zero_shift (v : A) (u : Aˣ) :
    (affine p v u 0)⁻¹ = affine p (-(↑u⁻¹ * v)) u⁻¹ 0 := by
  apply inv_eq_of_mul_eq_one_right
  rw [affine_mul_zero_shift, mul_neg, ← mul_assoc, Units.mul_inv, one_mul,
    add_neg_cancel, mul_inv_cancel, affine_one]

-- These are precisely the affine maps obtained by taking p-th powers.
private def powerSubgroup : Subgroup H where
  carrier := {g | ∃ (v : A) (c : F), t p ^ (p - 1) ∣ v ∧ g = affine p v (linPow c) 0}
  one_mem' := ⟨0, 0, dvd_zero _, by rw [linPow_zero, affine_one]⟩
  mul_mem' := by
    rintro _ _ ⟨v, c, hv, rfl⟩ ⟨w, d, hw, rfl⟩
    refine ⟨v + (↑(linPow c) : A) * w, c + d, hv.add (dvd_mul_of_dvd_right hw _), ?_⟩
    rw [affine_mul_zero_shift, linPow_add]
  inv_mem' := by
    rintro _ ⟨v, c, hv, rfl⟩
    refine ⟨-(↑(linPow c)⁻¹ * v), -c, dvd_neg.mpr (dvd_mul_of_dvd_right hv _), ?_⟩
    rw [affine_inv_zero_shift, linPow_neg]

private lemma affine_prime_power (v : A) (u : Aˣ) (a : F) (hu : norm p u = 1) :
    affine p v u a ^ p ∈ powerSubgroup p := by
  rw [affine_pow, ZMod.natCast_self, zero_mul]
  have htrans := translation_dvd p u hu a v
  by_cases ha : a = 0
  · subst a
    obtain ⟨c, hc⟩ := unit_pow_prime p u hu
    rw [iterUnit_zero, hc]
    exact ⟨_, _, htrans, rfl⟩
  · rw [iterUnit_prime p u a ha, hu, ← linPow_zero p]
    exact ⟨_, _, htrans, rfl⟩

private lemma scalar_diff_pow (u : Aˣ) (n : ℕ) (v : A) :
    ((actionEnd p u 0 - 1) ^ n) v = ((u : A) - 1) ^ n * v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (actionEnd p u 0 - 1)]
    change (u : A) * shiftHom p 0 (((actionEnd p u 0 - 1) ^ n) v) -
      ((actionEnd p u 0 - 1) ^ n) v = _
    rw [ih, shiftHom_zero, RingHom.id_apply, pow_succ']
    ring

private lemma affine_pow_zero_shift (v : A) (u : Aˣ) :
    affine p v u 0 ^ p = affine p (((u : A) - 1) ^ (p - 1) * v) (u ^ p) 0 := by
  rw [affine_pow, iterUnit_zero, mul_zero, translation_sum, scalar_diff_pow]

private lemma mem_kernel (v : A) (u : Aˣ) (a : F) (hu : norm p u = 1) :
    affine p v u a ∈ G := hu

-- In the zero-shift fiber, conjugation scales a pure translation by any unit of the ring.
private lemma exists_translation_pow (v : A) (hv : t p ^ (p - 1) ∣ v) :
    ∃ x : G, (x : H) ^ p = affine p v 1 0 := by
  by_cases h : v = 0
  · exact ⟨1, by simp [h, affine_one]⟩
  · obtain ⟨m, u, hfactor⟩ := exists_unit_factor p v h hv
    let x := affine p (-(t p ^ m)) (linearUnit p 1 ^ (m + (p - 1))) 1
    let a := affine p 0 u 0
    have hx : fullNorm p x = 1 := by
      change norm p (linearUnit p 1 ^ (m + (p - 1))) = 1
      rw [map_pow, norm_linear, one_pow]
    refine ⟨⟨a * x * a⁻¹, ?_⟩, ?_⟩
    · change fullNorm p (a * x * a⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hx, mul_one, mul_inv_cancel]
    · change (a * x * a⁻¹) ^ p = _
      rw [conj_pow, show x ^ p = _ from affine_pow_monomial p m, show a⁻¹ =
        affine p 0 u⁻¹ 0 by rw [affine_inv_zero_shift]; simp]
      simp [a, hfactor, mul_comm (u : A)]

private lemma exists_affine_pow (v : A) (c : F) (hv : t p ^ (p - 1) ∣ v) :
    ∃ x : G, (x : H) ^ p = affine p v (linPow c) 0 := by
  by_cases hc : c = 0
  · rw [hc, linPow_zero]
    exact exists_translation_pow p v hv
  · obtain ⟨w, rfl⟩ := hv
    refine ⟨⟨affine p w (linearUnit p c) 0, mem_kernel p _ _ _ (norm_linear p c)⟩, ?_⟩
    change affine p w (linearUnit p c) 0 ^ p = _
    rw [affine_pow_zero_shift, linearUnit_val, add_sub_cancel_left, mul_pow,
      ← map_pow, ZMod.pow_card_sub_one_eq_one hc, map_one, one_mul]

private lemma coe_pow_mem (g : G) : (g : H) ^ p ∈ powerSubgroup p := by
  rcases g with ⟨⟨v, ⟨u, a⟩⟩, hg⟩
  exact affine_prime_power p v.toAdd u a.toAdd hg

private lemma powers_eq :
    ((powerSubgroup p).comap (MonoidHom.ker (fullNorm p)).subtype : Set G) =
      {g | ∃ x : G, x ^ p = g} := by
  ext g
  constructor
  · rintro ⟨v, c, hv, he⟩
    obtain ⟨x, hx⟩ := exists_affine_pow p v c hv
    exact ⟨x, Subtype.ext (hx.trans he.symm)⟩
  · rintro ⟨x, rfl⟩
    exact coe_pow_mem p x

private lemma powerSubgroup_pow (hp2 : 2 < p) {g : H} (hg : g ∈ powerSubgroup p) :
    g ^ p = 1 := by
  obtain ⟨v, c, _, rfl⟩ := hg
  have ht : t p ^ (p * (p - 1)) = 0 := by
    apply pow_eq_zero_of_le _ (t_nil p)
    calc
      2 * p = p * 2 := Nat.mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  rw [affine_pow_zero_shift, linearUnit_pow, add_sub_cancel_left, mul_pow, ← pow_mul,
    ht, mul_zero, zero_mul, iterUnit_prime_sq, affine_one]

private lemma exponent_dvd (hp2 : 2 < p) : Monoid.exponent G ∣ p ^ 2 := by
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro g
  apply Subtype.ext
  change (g : H) ^ (p ^ 2) = 1
  calc
    (g : H) ^ (p ^ 2) = (g : H) ^ (p * p) := congrArg (fun n : ℕ => (g : H) ^ n) (pow_two p)
    _ = ((g : H) ^ p) ^ p := pow_mul _ _ _
    _ = 1 := powerSubgroup_pow p hp2 (coe_pow_mem p g)

private lemma exponent_eq (hp2 : 2 < p) : Monoid.exponent G = p ^ 2 := by
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 (exponent_dvd p hp2)
  suffices k = 2 by rwa [this] at he
  by_contra! h
  have hd : Monoid.exponent G ∣ p := by
    rw [he]
    simpa only [pow_one] using (pow_dvd_pow p (show k ≤ 1 by omega))
  let x : G := ⟨affine p 0 (linearUnit p 1) 0, mem_kernel p _ _ _ (norm_linear p 1)⟩
  have hx := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hd x
  have hu := congrArg (fun g : G => ((g : H).right.left : A)) hx
  change ((affine p 0 (linearUnit p 1) 0 ^ p).right.left : A) = 1 at hu
  rw [affine_pow_zero_shift] at hu
  change ((linPow (1 : F) : Aˣ) : A) = 1 at hu
  rw [linearUnit_pow, map_one, one_mul, add_eq_left] at hu
  exact t_pow_ne p p (by omega) hu

private lemma exists_noncommuting :
    ∃ x ∈ (powerSubgroup p).comap (MonoidHom.ker (fullNorm p)).subtype,
    ∃ y ∈ (powerSubgroup p).comap (MonoidHom.ker (fullNorm p)).subtype,
      (x : G) * y ≠ y * x := by
  let u := linPow (1 : F)
  let v := t p ^ (p - 1)
  let x : G := ⟨affine p 0 u 0, mem_kernel p _ _ _ (by
    simp [u, norm_linear])⟩
  let y : G := ⟨affine p v 1 0, mem_kernel p _ _ _ (map_one _)⟩
  refine ⟨x, ⟨0, 1, dvd_zero _, rfl⟩, y, ⟨v, 0, dvd_refl _, ?_⟩, ?_⟩
  · rw [linPow_zero]
    rfl
  intro h
  have he := congrArg (fun g : G => (g : H).left.toAdd) h
  change (affine p 0 u 0 * affine p v 1 0).left.toAdd =
    (affine p v 1 0 * affine p 0 u 0).left.toAdd at he
  rw [affine_mul_zero_shift, affine_mul_zero_shift] at he
  change 0 + (u : A) * v = v + (1 : A) * 0 at he
  have hp := prime_pos p
  simp only [u, v, linearUnit_pow, map_one, one_mul, zero_add, mul_zero, add_zero,
    add_mul, ← pow_add, add_eq_left] at he
  exact t_pow_ne p _ (by omega) he

private theorem not_abelian_for_odd_prime (hp2 : 2 < p)
    (h : ∀ (K : Type) [Group K] [Finite K], IsPGroup p K →
        Monoid.exponent K = p ^ 2 → ∀ P : Subgroup K,
        (P : Set K) = {g | ∃ x : K, x ^ p = g} → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    False := by
  obtain ⟨x, hx, y, hy, hne⟩ := exists_noncommuting p
  exact hne (h G (IsPGroup.of_exponent_dvd_pow (exponent_dvd p hp2))
    (exponent_eq p hp2) _ (powers_eq p) x hx y hy)


/--
**Kourovka 21.137 fails for every odd prime.** For every odd prime $p$ there is a finite
$p$-group $G$ of exponent $p^2$ with a subgroup $P$ whose underlying set is exactly the set
$\{x^p : x \in G\}$ of $p$-th powers in $G$, such that $P$ is not abelian.

Muliarchyk's counterexample has order $p^{3p+1}$, and its subgroup of $p$-th powers is isomorphic
to $\mathrm{UT}_3(\mathbb{F}_p) \times C_p^{p-1}$. The 21st issue of the Kourovka Notebook marks
Problem 21.137 solved ("No, it need not be"), citing this preprint for all odd primes.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
21.137 (L. Wilson); resolution: K. Muliarchyk, A counterexample to Kourovka Problem 21.137 for p =
3, preprint (2026), and A non-powerful subgroup of p-th powers for every odd prime, preprint (2026),
Kourovka Notebook site; letter of A. Chang of 1 August 2026, Muliarchyk (every odd prime), abstract
and Section 1: for each odd prime p an affine group V ⋊ B_p (V = F_p[r]/(r^(2p))) of order p^(3p+1)
and exponent p² whose set of p-th powers is a subgroup isomorphic to UT₃(F_p) × C_p^(p-1),
non-abelian of exponent p, hence not powerful; Kourovka Notebook (21st issue), Problem 21.137: No,
it need not be (p = 3: Muliarchyk, order 3^15; p = 2: the Sylow 2-subgroup of S₈ has exponent 8 and
its squares form the non-abelian, non-powerful subgroup C₂ × D₈, letter of A. Chang),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_21.137_solution.pdf.
-/
public theorem pthPowersSubgroupAbelianExponentPSq_refuted :
    ¬ pthPowersSubgroupAbelianExponentPSq := by
  rintro ⟨p, hp, hpne, h⟩
  have : Fact p.Prime := ⟨hp⟩
  exact not_abelian_for_odd_prime p (lt_of_le_of_ne hp.two_le hpne.symm) h

end

end MathlibExt.GroupTheory.PthPowersSubgroupPowerfulKourovka21Problem137Wanted
