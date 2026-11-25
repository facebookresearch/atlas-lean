/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.StrongPseudoprime
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Counting strong pseudoprime bases

Monier's formula counts the bases of an odd composite passing the strong pseudoprime test
by combining the power equations in its prime-power residue rings.
-/

namespace MetaMathlibExt

namespace card_strongPseudoprime_bases

private def powerFiber {R : Type*} [Monoid R] (m : ℕ) (a : R) : Set R :=
  {x | x ^ m = a}

-- In a cyclic unit group the power map has a kernel of size gcd(φ(q), m).
private theorem card_one_fiber {q m : ℕ} [NeZero q] [IsCyclic (ZMod q)ˣ] (hm : m ≠ 0) :
    (powerFiber m (1 : ZMod q)).ncard = q.totient.gcd m := by
  let K := (powMonoidHom m : (ZMod q)ˣ →* (ZMod q)ˣ).ker
  have unit (x : powerFiber m (1 : ZMod q)) : IsUnit x.val :=
    IsUnit.of_pow_eq_one x.prop hm
  let e : powerFiber m (1 : ZMod q) ≃ K :=
    { toFun := fun x => ⟨(unit x).unit, Units.ext (by
        change ((unit x).unit : ZMod q) ^ m = 1
        rw [IsUnit.unit_spec]
        exact x.prop)⟩
      invFun := fun u => ⟨(u.val : ZMod q), congrArg Units.val u.prop⟩
      left_inv := fun x => Subtype.ext (unit x).unit_spec
      right_inv := fun u =>
        Subtype.ext (Units.ext (unit ⟨_, congrArg Units.val u.prop⟩).unit_spec) }
  calc
    _ = Nat.card K := Nat.card_congr e
    _ = _ := by
      dsimp only [K]
      rw [IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

-- Modulo an odd prime power the two square roots of one exhaust the kernel of squaring.
private theorem square_fiber {q : ℕ} [NeZero q] [Fact (2 < q)] [IsCyclic (ZMod q)ˣ] :
    powerFiber 2 (1 : ZMod q) = {1, -1} := by
  symm
  apply Set.eq_of_subset_of_ncard_le
  · exact Set.insert_subset (by simp [powerFiber]) (Set.singleton_subset_iff.mpr (by
      simp [powerFiber]))
  · rw [card_one_fiber (by decide), Set.ncard_pair ZMod.neg_one_ne_one.symm]
    exact Nat.gcd_le_right _ (by decide)
  · exact Set.toFinite _

private theorem card_neg_fiber {q m : ℕ} [NeZero q] [Fact (2 < q)] [IsCyclic (ZMod q)ˣ]
    (hm : m ≠ 0) :
    (powerFiber m (-1 : ZMod q)).ncard =
      q.totient.gcd (2 * m) - q.totient.gcd m := by
  have hunion : powerFiber (2 * m) (1 : ZMod q) =
      powerFiber m 1 ∪ powerFiber m (-1) := by
    ext x
    change x ^ (2 * m) = 1 ↔ x ^ m = 1 ∨ x ^ m = -1
    rw [mul_comm, pow_mul]
    change x ^ m ∈ powerFiber 2 (1 : ZMod q) ↔ _
    rw [square_fiber]
    rfl
  have hd : Disjoint (powerFiber m (1 : ZMod q)) (powerFiber m (-1)) :=
    Set.disjoint_left.mpr fun _ hx hy => ZMod.neg_one_ne_one (hy.symm.trans hx)
  have h := congrArg Set.ncard hunion
  rw [Set.ncard_union_eq hd, card_one_fiber hm, card_one_fiber (mul_ne_zero (by decide) hm)] at h
  omega

-- The Chinese remainder isomorphism identifies a power fiber with a product of local fibers.
private theorem card_power_fiber_crt {n : ℕ} (hn : n ≠ 0) (m : ℕ) (a : ZMod n) :
    (powerFiber m a).ncard =
      ∏ p : n.primeFactors, (powerFiber m (ZMod.equivPi n hn a p)).ncard := by
  let e := ZMod.equivPi n hn
  calc
    _ = Nat.card {y : ∀ p : n.primeFactors, ZMod (p.val ^ n.factorization p) //
          ∀ p, (y p) ^ m = e a p} := by
      refine Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)
      change x ^ m = a ↔ ∀ p, (e x p) ^ m = e a p
      rw [← e.injective.eq_iff, map_pow]
      exact funext_iff
    _ = Nat.card (∀ p : n.primeFactors, powerFiber m (e a p)) :=
      Nat.card_congr (Equiv.subtypePiEquivPi
        (p := fun (p : n.primeFactors) (x : ZMod (p.val ^ n.factorization p)) => x ^ m = e a p))
    _ = _ := Nat.card_pi

private theorem gcd_odd_parts {a b i d : ℕ} (hb : Odd b) (hd : Odd d) :
    (2 ^ a * b).gcd (2 ^ i * d) = 2 ^ min i a * d.gcd b := by
  have hpow : (2 ^ a).gcd (2 ^ i) = 2 ^ min i a := by
    rcases le_total i a with h | h
    · rw [min_eq_left h, Nat.gcd_eq_right (pow_dvd_pow 2 h)]
    · rw [min_eq_right h, Nat.gcd_eq_left (pow_dvd_pow 2 h)]
  rw [((Nat.coprime_two_left.mpr hd).pow_left i).gcd_mul,
    ((Nat.coprime_two_left.mpr hd).pow_left a).gcd_mul_left_cancel,
    mul_comm (2 ^ a) b, ((Nat.coprime_two_right.mpr hb).pow_right i).gcd_mul_left_cancel,
    hpow, Nat.gcd_comm b d]

private theorem local_gcd {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p ∈ n.primeFactors)
    (i : ℕ) :
    (p ^ n.factorization p).totient.gcd (2 ^ i * ordCompl[2] (n - 1)) =
      2 ^ min i ((p - 1).factorization 2) *
        (ordCompl[2] (n - 1)).gcd (ordCompl[2] (p - 1)) := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  have hodd := ho.of_dvd_nat hdvd
  have hcop : n.Coprime (n - 1) :=
    (Nat.coprime_self_sub_right hn.le).mpr (Nat.coprime_one_right n)
  have hpd := (hcop.coprime_dvd_left hdvd).coprime_dvd_right (Nat.ordCompl_dvd (n - 1) 2)
  have hpm : p.Coprime (2 ^ i * ordCompl[2] (n - 1)) :=
    ((Nat.coprime_two_right.mpr hodd).pow_right _).mul_right hpd
  rw [Nat.totient_prime_pow hprime (hprime.factorization_pos_of_dvd (by omega) hdvd),
    (hpm.pow_left _).gcd_mul_left_cancel]
  convert gcd_odd_parts (a := (p - 1).factorization 2) (i := i)
    (Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (n := p - 1)
      (by have := hprime.one_lt; omega)))
    (Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (n := n - 1) (by omega)))
    using 1
  rw [Nat.ordProj_mul_ordCompl_eq_self]

private theorem local_fibers {n : ℕ} (hn : 1 < n) (ho : Odd n) (p : n.primeFactors) :
    let q := p.val ^ n.factorization p
    let d := ordCompl[2] (n - 1)
    let g := d.gcd (ordCompl[2] (p.val - 1))
    (powerFiber d (1 : ZMod q)).ncard = g ∧ ∀ i : ℕ,
      (powerFiber (2 ^ i * d) (-1 : ZMod q)).ncard =
        if i < (p.val - 1).factorization 2 then 2 ^ i * g else 0 := by
  dsimp only
  have hp := Nat.prime_of_mem_primeFactors p.prop
  have hdvd := Nat.dvd_of_mem_primeFactors p.prop
  have hp2 := (ho.of_dvd_nat hdvd).ne_two_of_dvd_nat (dvd_refl _)
  have hfac := hp.factorization_pos_of_dvd (show n ≠ 0 by omega) hdvd
  have hq : 2 < p.val ^ n.factorization p :=
    lt_of_lt_of_le (by have := hp.two_le; omega : 2 < p.val)
      (Nat.le_self_pow hfac.ne' _)
  have : NeZero (p.val ^ n.factorization p) := ⟨by omega⟩
  have : Fact (2 < p.val ^ n.factorization p) := ⟨hq⟩
  have : IsCyclic (ZMod (p.val ^ n.factorization p))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p.val hp hp2 (n.factorization p)
  have hd := (Nat.ordCompl_pos 2 (n := n - 1) (by omega)).ne'
  constructor
  · rw [card_one_fiber hd]
    simpa using local_gcd hn ho p.prop 0
  · intro i
    rw [card_neg_fiber (mul_ne_zero (pow_ne_zero _ (by decide)) hd), ← mul_assoc, ← pow_succ',
      local_gcd hn ho p.prop, local_gcd hn ho p.prop]
    split_ifs with hi
    · rw [min_eq_left (Nat.succ_le_of_lt hi), min_eq_left hi.le, pow_succ', Nat.mul_assoc,
        two_mul, Nat.add_sub_cancel]
    · rw [min_eq_right (by omega), min_eq_right (by omega), Nat.sub_self]

private noncomputable abbrev leastVal (n : ℕ) :=
  sInf ((fun p => (p - 1).factorization 2) '' (n.primeFactors : Set ℕ))

private abbrev oddPartProduct (n : ℕ) :=
  ∏ p ∈ n.primeFactors, (ordCompl[2] (n - 1)).gcd (ordCompl[2] (p - 1))

private theorem leastVal_le {n p : ℕ} (hp : p ∈ n.primeFactors) :
    leastVal n ≤ (p - 1).factorization 2 :=
  Nat.sInf_le ⟨p, hp, rfl⟩

-- Every prime factor is one modulo 2^v, so their product with multiplicities is too.
private theorem leastVal_le_split {n : ℕ} (hn : 1 < n) :
    leastVal n ≤ (n - 1).factorization 2 := by
  apply (Nat.prime_two.pow_dvd_iff_le_factorization (by omega : n - 1 ≠ 0)).mp
  apply (Nat.modEq_iff_dvd' hn.le).mp
  have hp (p : ℕ) (hp : p ∈ n.primeFactors) : 1 ≡ p [MOD 2 ^ leastVal n] := by
    have h := (Nat.prime_of_mem_primeFactors hp).one_lt
    exact (Nat.modEq_iff_dvd' h.le).mpr ((Nat.prime_two.pow_dvd_iff_le_factorization
      (by omega : p - 1 ≠ 0)).mpr (leastVal_le hp))
  simpa only [one_pow, Finset.prod_const_one,
    ← Nat.prod_primeFactors_pow_factorization (by omega : n ≠ 0)] using
    (Nat.ModEq.prod fun p h => (hp p h).pow (n.factorization p))

private theorem global_fibers {n : ℕ} (hn : 1 < n) (ho : Odd n) :
    let d := ordCompl[2] (n - 1)
    (powerFiber d (1 : ZMod n)).ncard = oddPartProduct n ∧ ∀ i : ℕ,
      (powerFiber (2 ^ i * d) (-1 : ZMod n)).ncard =
        if i < leastVal n then (2 ^ n.primeFactors.card) ^ i * oddPartProduct n else 0 := by
  dsimp only
  have hn0 : n ≠ 0 := by omega
  have hprod := Finset.prod_coe_sort n.primeFactors
    (fun p => (ordCompl[2] (n - 1)).gcd (ordCompl[2] (p - 1)))
  constructor
  · rw [card_power_fiber_crt hn0, map_one]
    simpa only [Pi.one_apply, (local_fibers hn ho _).1] using hprod
  · intro i
    rw [card_power_fiber_crt hn0, map_neg, map_one]
    simp only [Pi.neg_apply, Pi.one_apply, (local_fibers hn ho _).2]
    split_ifs with hi
    · simp only [ite_eq_left (hi.trans_le (leastVal_le (n := n) (Subtype.prop _)))]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
        ← pow_mul, mul_comm i, pow_mul, hprod]
    · obtain ⟨p, hp, hv⟩ := Nat.sInf_mem
        ((Nat.nonempty_primeFactors.mpr hn).to_set.image (fun p => (p - 1).factorization 2))
      have hzero : ¬i < (p - 1).factorization 2 := by
        rwa [show (p - 1).factorization 2 = leastVal n from hv]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨p, hp⟩ : n.primeFactors)) (ite_eq_right hzero)

private def passing (n d k : ℕ) : Set (ZMod n) :=
  {x | x ^ d = 1 ∨ ∃ i < k, x ^ (2 ^ i * d) = -1}

-- Earlier negative powers become one after the next squaring, so each stage adds a disjoint fiber.
private theorem card_passing {n : ℕ} [NeZero n] [Fact (2 < n)] (d k : ℕ) :
    (passing n d k).ncard = (powerFiber d (1 : ZMod n)).ncard +
      ∑ i ∈ Finset.range k, (powerFiber (2 ^ i * d) (-1 : ZMod n)).ncard := by
  induction k with
  | zero => simp [passing, powerFiber]
  | succ k ih =>
    have hun : passing n d (k + 1) = passing n d k ∪ powerFiber (2 ^ k * d) (-1) := by
      ext x
      change (_ ∨ ∃ i < k + 1, _) ↔ (_ ∨ ∃ i < k, _) ∨ _
      constructor
      · rintro (h | ⟨i, hi, he⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
          · exact Or.inl (Or.inr ⟨i, h, he⟩)
          · exact Or.inr he
      · rintro ((h | ⟨i, hi, he⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨i, hi.trans (Nat.lt_succ_self _), he⟩
        · exact Or.inr ⟨k, Nat.lt_succ_self k, h⟩
    have hd : Disjoint (passing n d k) (powerFiber (2 ^ k * d) (-1)) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      apply ZMod.neg_one_ne_one (n := n)
      change x ^ (2 ^ k * d) = -1 at hy
      rw [← hy]
      rcases hx with h | ⟨j, hj, h⟩
      · rw [mul_comm, pow_mul, h, one_pow]
      · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
        rw [pow_add, pow_succ, show 2 ^ j * 2 * 2 ^ l * d = (2 ^ j * d) * 2 * 2 ^ l by ring,
          pow_mul, pow_mul, h, neg_one_sq, one_pow]
    rw [hun, Set.ncard_union_eq hd, ih, Finset.sum_range_succ, Nat.add_assoc]

private theorem passing_iff {n : ℕ} (hn : 1 < n) (hc : ¬n.Prime) (ho : Odd n) (x : ZMod n) :
    IsStrongPseudoprime n x ↔ x ∈ passing n (ordCompl[2] (n - 1)) ((n - 1).factorization 2) := by
  constructor
  · rintro ⟨_, _, _, k, d, hkd, hd, hx⟩
    have hk : (n - 1).factorization 2 = k := by
      rw [hkd, Nat.factorization_mul (pow_ne_zero _ (by decide)) hd.pos.ne', Finsupp.add_apply,
        Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd
          hd.not_two_dvd_nat, add_zero]
    have hd' : ordCompl[2] (n - 1) = d := by
      rw [hkd, Nat.ordCompl_pow_mul_of_not_dvd k Nat.prime_two hd.not_two_dvd_nat]
    rwa [hd', hk]
  · intro hx
    exact ⟨hn, hc, ho, _, _, (Nat.ordProj_mul_ordCompl_eq_self (n - 1) 2).symm,
      Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two (by omega)), hx⟩

private theorem card_base_representatives {n : ℕ} (hn : 1 < n) (hc : ¬n.Prime) (ho : Odd n) :
    {b : ℕ | 1 ≤ b ∧ b < n ∧ IsStrongPseudoprime n b}.ncard =
      (passing n (ordCompl[2] (n - 1)) ((n - 1).factorization 2)).ncard := by
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨hn⟩
  refine Set.ncard_congr (fun b _ => (b : ZMod n)) (fun b hb => (passing_iff hn hc ho b).mp hb.2.2)
    (fun a b ha hb eq => ?_) (fun x hx => ?_)
  · simpa only [ZMod.val_natCast_of_lt ha.2.1, ZMod.val_natCast_of_lt hb.2.1] using
      congrArg ZMod.val eq
  · have hd := (Nat.ordCompl_pos 2 (n := n - 1) (by omega)).ne'
    have hne : x ≠ 0 := by
      rintro rfl
      rcases hx with h | ⟨j, _, h⟩
      · simp [zero_pow hd] at h
      · simp [zero_pow (mul_ne_zero (Nat.two_pow_pos j).ne' hd)] at h
    have hpos := (ZMod.val_eq_zero x).not.mpr hne
    exact ⟨x.val, ⟨by omega, x.val_lt, by rwa [ZMod.natCast_zmod_val, passing_iff hn hc ho]⟩,
      ZMod.natCast_zmod_val x⟩

end card_strongPseudoprime_bases

open card_strongPseudoprime_bases in
/-- **Monier's formula for the number of strong pseudoprime bases.** Let $n$ be an odd composite
natural number, let $r$ be the number of distinct prime divisors of $n$, and let $v$ be the least
of the $2$-adic valuations of $p - 1$ over the prime divisors $p$ of $n$. Write $d$ for the odd
part of $n - 1$ and $d_p$ for the odd part of $p - 1$. Then the number of integers $b$ with
$1 \le b < n$ such that $n$ is a strong pseudoprime to the base $b$ equals, as a rational number,
$$\left(1 + \frac{2^{vr} - 1}{2^r - 1}\right) \prod_p \gcd(d, d_p),$$
where the product runs over the distinct prime divisors $p$ of $n$.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 3, Formula (5) (`integers-2024-A23-thm-3`). -/
public theorem card_strongPseudoprime_bases {n : ℕ} (hn : 1 < n) (hcomp : ¬n.Prime)
    (hodd : Odd n) :
    let r := n.primeFactors.card
    let v := sInf ((fun p => (p - 1).factorization 2) '' (n.primeFactors : Set ℕ))
    ({b : ℕ | 1 ≤ b ∧ b < n ∧ IsStrongPseudoprime n b}.ncard : ℚ) =
      (1 + (2 ^ (v * r) - 1) / (2 ^ r - 1)) *
        ∏ p ∈ n.primeFactors, (Nat.gcd (ordCompl[2] (n - 1)) (ordCompl[2] (p - 1)) : ℚ) := by
  classical
  let k := (n - 1).factorization 2
  let v := leastVal n
  let r := n.primeFactors.card
  have : NeZero n := ⟨by omega⟩
  have : Fact (2 < n) := ⟨by have := Nat.odd_iff.mp hodd; omega⟩
  have hcut : (Finset.range k).filter (· < v) = Finset.range v := by
    have hvk : v ≤ k := leastVal_le_split hn
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  obtain ⟨hpos, hneg⟩ := global_fibers hn hodd
  have hcount : {b : ℕ | 1 ≤ b ∧ b < n ∧ IsStrongPseudoprime n b}.ncard =
      (1 + ∑ i ∈ Finset.range v, (2 ^ r) ^ i) * oddPartProduct n := by
    rw [card_base_representatives hn hcomp hodd, card_passing, hpos]
    simp_rw [hneg]
    rw [← Finset.sum_filter, hcut, ← Finset.sum_mul, add_mul, one_mul]
  have hr : 0 < r := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hn)
  have hratio : (2 : ℚ) ^ r ≠ 1 := (one_lt_pow₀ (by norm_num) hr.ne').ne'
  dsimp only
  rw [hcount]
  push_cast [oddPartProduct]
  rw [geom_sum_eq hratio, ← pow_mul, mul_comm r v]

end MetaMathlibExt
