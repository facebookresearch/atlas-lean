/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MultipleHarmonic
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private theorem icc_sum_eq_nonzero_sum (p : ℕ) (m : ℕ) [NeZero p] :
    (∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))^m) =
    ∑ x ∈ (Finset.univ : Finset (ZMod p)) \ {0}, x^m := by
  refine Finset.sum_bij (fun k _ => ((k : ZMod p))) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    intro hz
    have hdvd : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp hz
    have hple : p ≤ k := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro a ha b hb hab
    rw [Finset.mem_Icc] at ha hb
    have ha_lt : a < p := by omega
    have hb_lt : b < p := by omega
    have h1 : ((a : ZMod p)).val = a := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt]
    have h2 : ((b : ZMod p)).val = b := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt]
    have h3 := congrArg ZMod.val hab
    omega
  · intro y hy
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hy
    refine ⟨y.val, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      have hlt := ZMod.val_lt y (n := p)
      have hne := (ZMod.val_ne_zero y).mpr hy
      omega
    · exact ZMod.natCast_zmod_val y
  · intro k hk
    rfl

private theorem pow_sum_small (p m : ℕ) (hp : p.Prime) (hm : m < p - 1) :
    (∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))^m) = if m = 0 then -1 else 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [icc_sum_eq_nonzero_sum]
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  by_cases hm0 : m = 0
  · subst hm0
    have hcard_nonzero : ((Finset.univ : Finset (ZMod p)) \ {0}).card = p - 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
        Finset.card_univ, hcard, Finset.card_singleton]
    have hsum1 : (∑ x ∈ (Finset.univ : Finset (ZMod p)) \ {0}, (1 : ZMod p)) = (((p - 1 : ℕ)) : ZMod p) := by
      rw [Finset.sum_const, hcard_nonzero, nsmul_eq_mul]
      simp
    have hp1 : p ≥ 1 := hp.one_lt.le
    have hcast : ((((p - 1 : ℕ))) : ZMod p) = -1 := by
      have h1 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
      have h2 : (p - 1 : ℕ) + 1 = p := Nat.sub_add_cancel hp1
      have h3 : (((((p - 1 : ℕ) + 1 : ℕ))) : ZMod p) = 0 := by rw [h2, h1]
      push_cast at h3
      have := eq_neg_of_add_eq_zero_left h3
      simpa using this
    simp only [pow_zero]
    rw [hsum1, hcast]
    simp
  · have huniv : ∑ x : ZMod p, x^m = 0 :=
      FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) m (by omega)
    have hsplit : (∑ x ∈ (Finset.univ : Finset (ZMod p)) \ {0}, x^m) + (0 : ZMod p)^m = ∑ x : ZMod p, x^m := by
      have hunion : ((Finset.univ : Finset (ZMod p)) \ {0}) ∪ {0} = Finset.univ := Finset.sdiff_union_of_subset (Finset.subset_univ _)
      have hdisj : Disjoint ((Finset.univ : Finset (ZMod p)) \ {0}) ({0} : Finset (ZMod p)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_sdiff] at hx1
        have hx2' : x ∈ ({0} : Finset (ZMod p)) := hx2
        rw [Finset.mem_singleton] at hx2'
        exact hx1.2 (Finset.mem_singleton.mpr hx2')
      conv_rhs => rw [← hunion, Finset.sum_union hdisj]
      simp [add_comm]
    have h0pow : (0 : ZMod p)^m = 0 := zero_pow hm0
    have hA : (∑ x ∈ (Finset.univ : Finset (ZMod p)) \ {0}, x^m) = 0 := by
      rw [h0pow, add_zero] at hsplit
      rw [huniv] at hsplit
      exact hsplit
    rw [hA]
    rw [ite_eq_right hm0]
private theorem powersetCard_succ_insert {α : Type} [DecidableEq α] (a : α) (s : Finset α) (n : ℕ) (h : a ∉ s) :
    (insert a s).powersetCard (n+1) = s.powersetCard (n+1) ∪ (s.powersetCard n).image (insert a) := by
  ext t
  simp only [Finset.mem_powersetCard, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hsub, hcard⟩
    by_cases ha : a ∈ t
    · right
      refine ⟨t.erase a, ⟨?_, ?_⟩, (Finset.insert_erase ha)⟩
      · have : t.erase a ⊆ (insert a s).erase a := Finset.erase_subset_erase _ hsub
        rwa [Finset.erase_insert h] at this
      · have hcard' : (t.erase a).card = t.card - 1 := Finset.card_erase_of_mem ha
        omega
    · left
      refine ⟨?_, hcard⟩
      intro x hx
      have hx' := hsub hx
      rw [Finset.mem_insert] at hx'
      rcases hx' with rfl | hm
      · exact absurd hx ha
      · exact hm
  · rintro (⟨hsub, hcard⟩ | ⟨u, ⟨hsubu, hcardu⟩, rfl⟩)
    · refine ⟨?_, hcard⟩
      exact Finset.Subset.trans hsub (Finset.subset_insert _ _)
    · have hau : a ∉ u := fun hm => h (hsubu hm)
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with hxx | hm
        · subst hxx; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hsubu hm)
      · rw [Finset.card_insert_of_notMem hau, hcardu]
private theorem powersetCard_succ_insert_disjoint {α : Type} [DecidableEq α] (a : α) (s : Finset α) (n : ℕ) (h : a ∉ s) :
    Disjoint (s.powersetCard (n+1)) ((s.powersetCard n).image (insert a)) := by
  rw [Finset.disjoint_left]
  intro t ht1 ht2
  rw [Finset.mem_powersetCard] at ht1
  rw [Finset.mem_image] at ht2
  obtain ⟨u, _, rfl⟩ := ht2
  have hau : a ∈ insert a u := Finset.mem_insert_self a u
  have hat : a ∉ insert a u := by
    have : insert a u ⊆ s := ht1.1
    exact fun hm => h (this hm)
  exact hat hau
private theorem sum_powersetCard_succ_insert {M : Type} [CommSemiring M] {α : Type} [DecidableEq α]
    (a : α) (s : Finset α) (n : ℕ) (h : a ∉ s) (f : α → M) :
    (∑ t ∈ (insert a s).powersetCard (n+1), ∏ i ∈ t, f i) =
    (∑ t ∈ s.powersetCard (n+1), ∏ i ∈ t, f i) +
    f a * (∑ u ∈ s.powersetCard n, ∏ i ∈ u, f i) := by
  rw [powersetCard_succ_insert a s n h,
    Finset.sum_union (powersetCard_succ_insert_disjoint a s n h)]
  congr 1
  have hinj : ∀ u ∈ s.powersetCard n, ∀ v ∈ s.powersetCard n, insert a u = insert a v → u = v := by
    intro u hu v hv huv
    rw [Finset.mem_powersetCard] at hu hv
    have hau : a ∉ u := fun hm => h (hu.1 hm)
    have hav : a ∉ v := fun hm => h (hv.1 hm)
    have : (insert a u).erase a = (insert a v).erase a := by rw [huv]
    rwa [Finset.erase_insert hau, Finset.erase_insert hav] at this
  rw [Finset.sum_image hinj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mem_powersetCard] at hu
  have hau : a ∉ u := fun hm => h (hu.1 hm)
  rw [Finset.prod_insert hau]
private theorem multipleHarmonic_zero (p r : ℕ) : multipleHarmonic p r 0 = 1 := by
  unfold multipleHarmonic
  rw [Finset.powersetCard_zero]
  simp
private theorem multipleHarmonic_succ (p r n : ℕ) :
    multipleHarmonic p (r+1) (n+1) =
    multipleHarmonic p r (n+1) + ((((r+1 : ℕ)) : ZMod p))⁻¹ * multipleHarmonic p r n := by
  unfold multipleHarmonic
  have hIcc : Finset.Icc 1 (r+1) = insert (r+1) (Finset.Icc 1 r) := by
    ext x; simp [Finset.mem_Icc]; omega
  have hmem : (r+1) ∉ Finset.Icc 1 r := by simp [Finset.mem_Icc]
  rw [hIcc]
  exact sum_powersetCard_succ_insert (r+1) (Finset.Icc 1 r) n hmem (fun i => ((i : ZMod p))⁻¹)
private theorem zmod_inv_eq_pow (p : ℕ) [Fact (Nat.Prime p)] (a : ZMod p) (ha : a ≠ 0) :
    a⁻¹ = a ^ (p - 2) := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hunit : IsUnit a := isUnit_iff_ne_zero.mpr ha
  have h1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit a hunit
  have h2 : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hps : p - 1 = (p - 2) + 1 := by omega
  rw [hps, pow_succ] at h2
  -- h2 : a ^ (p-2) * a = 1
  calc a⁻¹ = 1 * a⁻¹ := by rw [one_mul]
    _ = (a ^ (p-2) * a) * a⁻¹ := by rw [h2]
    _ = a ^ (p-2) * (a * a⁻¹) := by ring
    _ = a ^ (p-2) * 1 := by rw [h1]
    _ = a ^ (p-2) := by rw [mul_one]

private theorem choose_mul_identity (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    k.choose j * j = k * ((k-1).choose (j-1)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j-1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hjk' : j' ≤ k' := by omega
  have e1 := Nat.choose_mul_factorial_mul_factorial (n := k'+1) (k := j'+1) (by omega : j'+1 ≤ k'+1)
  have e2 := Nat.choose_mul_factorial_mul_factorial (n := k') (k := j') hjk'
  have hfact1 : (j' + 1).factorial = (j' + 1) * j'.factorial := Nat.factorial_succ j'
  have hfact2 : (k' + 1).factorial = (k' + 1) * k'.factorial := Nat.factorial_succ k'
  have hsub : k' + 1 - (j' + 1) = k' - j' := by omega
  rw [hsub] at e1
  rw [hfact1] at e1
  have hpos : 0 < j'.factorial * (k' - j').factorial := by positivity
  have e1' : ((k'+1).choose (j'+1) * (j'+1)) * (j'.factorial * (k'-j').factorial) = ((k'+1) * k'.choose j') * (j'.factorial * (k'-j').factorial) := by
    calc ((k'+1).choose (j'+1) * (j'+1)) * (j'.factorial * (k'-j').factorial)
        = (k'+1).choose (j'+1) * ((j'+1) * j'.factorial) * (k'-j').factorial := by ring
      _ = (k'+1).factorial := e1
      _ = (k'+1) * k'.factorial := hfact2
      _ = (k'+1) * (k'.choose j' * j'.factorial * (k'-j').factorial) := by rw [e2]
      _ = ((k'+1) * k'.choose j') * (j'.factorial * (k'-j').factorial) := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos e1'

private theorem zmod_pow_mod_reduction (p : ℕ) [Fact (Nat.Prime p)] (a : ZMod p) (ha : a ≠ 0) (e : ℕ) :
    a ^ e = a ^ (e % (p - 1)) := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have h1 : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hdiv : e = (p - 1) * (e / (p - 1)) + e % (p - 1) := (Nat.div_add_mod e (p - 1)).symm
  conv_lhs => rw [hdiv, pow_add, pow_mul, h1, one_pow, one_mul]

private theorem pow_sum_general (p e : ℕ) (hp : p.Prime) :
    (∑ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))^e) = if (p - 1) ∣ e then -1 else 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hne : NeZero p := ⟨hp.ne_zero⟩
  have hp1 : 1 < p := hp.one_lt
  have hp1' : 0 < p - 1 := by omega
  -- reduce each term mod p-1
  have hred : ∀ k ∈ Finset.Icc 1 (p-1), ((k : ZMod p))^e = ((k : ZMod p))^(e % (p-1)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 : ((k : ZMod p)) ≠ 0 := by
      intro h0
      have hdvd : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp h0
      have hple : p ≤ k := Nat.le_of_dvd (by omega) hdvd
      omega
    exact zmod_pow_mod_reduction p ((k : ZMod p)) hk0 e
  rw [Finset.sum_congr rfl hred]
  have hsmall := pow_sum_small p (e % (p-1)) hp (Nat.mod_lt e hp1')
  rw [hsmall]
  by_cases hdvd : (p - 1) ∣ e
  · have hmod : e % (p - 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
    rw [hmod]
    simp [hdvd]
  · have hmod : e % (p - 1) ≠ 0 := fun h => hdvd (Nat.dvd_iff_mod_eq_zero.mpr h)
    rw [ite_eq_right hmod, ite_eq_right hdvd]

private theorem inv_pow_sum_general (p m : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (∑ k ∈ Finset.Icc 1 (p-1), ((((k : ZMod p))⁻¹)^m)) = if (p - 1) ∣ m then -1 else 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hne : NeZero p := ⟨hp.ne_zero⟩
  -- each term: (k⁻¹)^m = k^(m*(p-2))
  have hterm : ∀ k ∈ Finset.Icc 1 (p-1), ((((k : ZMod p))⁻¹)^m) = ((k : ZMod p))^(m * (p - 2)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 : ((k : ZMod p)) ≠ 0 := by
      intro h0
      have hdvd : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp h0
      have hple : p ≤ k := Nat.le_of_dvd (by omega) hdvd
      omega
    have hinv := zmod_inv_eq_pow p ((k : ZMod p)) hk0
    rw [hinv, ← pow_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm]
  rw [pow_sum_general p (m * (p - 2)) hp]
  -- (p-1) ∣ m ↔ (p-1) ∣ m*(p-2)
  have hcop : Nat.Coprime (p - 1) (p - 2) := by
    have h1 : (p - 1) = 1 + (p - 2) := by omega
    rw [h1, Nat.coprime_add_self_left]
    exact Nat.coprime_one_left _
  by_cases hdm : (p - 1) ∣ m
  · have : (p - 1) ∣ m * (p - 2) := Dvd.dvd.mul_right hdm _
    rw [ite_eq_left hdm, ite_eq_left this]
  · have : ¬ (p - 1) ∣ m * (p - 2) := fun hd => hdm (hcop.dvd_of_dvd_mul_right hd)
    rw [ite_eq_right hdm, ite_eq_right this]


private theorem choose_mod_prime (p j : ℕ) (hp : p.Prime) (hj : j < p) :
    (((p - 1).choose j : ℕ) : ZMod p) = (-1 : ZMod p) ^ j := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  induction j with
  | zero => simp
  | succ j ih =>
    have hjp : j < p := by omega
    have hpascal : (p.choose (j+1) : ℕ) = (p-1).choose j + (p-1).choose (j+1) := by
      have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.one_lt.le).symm
      conv_lhs => rw [hp1]
      exact Nat.choose_succ_succ (p-1) j
    have hvanish : ((p.choose (j+1) : ℕ) : ZMod p) = 0 := by
      by_cases hj0 : j + 1 = 0
      · omega
      · have hdvd := hp.dvd_choose_self hj0 (by omega : j + 1 < p)
        exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have hcast : (((p-1).choose j : ℕ) : ZMod p) + (((p-1).choose (j+1) : ℕ) : ZMod p) = 0 := by
      have hcc := congrArg (fun n : ℕ => ((n : ℕ) : ZMod p)) hpascal
      simp only [Nat.cast_add] at hcc
      rw [hvanish] at hcc
      exact hcc.symm
    have ih' := ih hjp
    rw [ih'] at hcast
    have hnext : (((p-1).choose (j+1) : ℕ) : ZMod p) = -((-1 : ZMod p)^j) := eq_neg_of_add_eq_zero_right hcast
    rw [hnext, pow_succ, mul_neg, mul_one]

private theorem coeff_one_sub_X_pow (p k j : ℕ) :
    (((1 - (Polynomial.X : Polynomial (ZMod p)))^k).coeff j) = (-1 : ZMod p)^j * ((k.choose j : ℕ) : ZMod p) := by
  have hC : (-1 : Polynomial (ZMod p)) = Polynomial.C (-1 : ZMod p) := by rw [map_neg, Polynomial.C_1]
  have h1 : (1 - (Polynomial.X : Polynomial (ZMod p))) = -((Polynomial.X + Polynomial.C (-1 : ZMod p))) := by
    simp [sub_eq_add_neg, add_comm]
  rw [h1, neg_pow, hC, ← map_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  by_cases hjk : j ≤ k
  · have hpow : (-1 : ZMod p)^k * (-1 : ZMod p)^(k - j) = (-1 : ZMod p)^j := by
      have e1 : (-1 : ZMod p)^k * (-1)^(k-j) = (-1)^(k + (k - j)) := by rw [← pow_add]
      have e2 : k + (k - j) = j + 2 * (k - j) := by omega
      rw [e1, e2, pow_add]
      have hsq : (-1 : ZMod p)^(2 * (k - j)) = 1 := by
        have heven : Even (2 * (k - j)) := even_two.mul_right _
        exact Even.neg_one_pow heven
      rw [hsq, mul_one]
    calc (-1 : ZMod p)^k * ((-1)^(k-j) * _) = ((-1)^k * (-1)^(k-j)) * _ := by ring
      _ = (-1)^j * _ := by rw [hpow]
  · push Not at hjk
    have hchoose : k.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hchoose]

private theorem multipleHarmonic_eq_zero_of_pos (p m : ℕ) (hm : 0 < m) :
    multipleHarmonic p 0 m = 0 := by
  unfold multipleHarmonic
  have hicc : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
  rw [hicc]
  have hempty : (∅ : Finset ℕ).powersetCard m = ∅ := Finset.powersetCard_eq_empty.mpr (by simpa using hm)
  rw [hempty, Finset.sum_empty]

private theorem S_recurrence (p j m : ℕ) (hp : p.Prime) (hj1 : 1 ≤ j) (hjp1 : j + 1 ≤ p - 1) (hm1 : 1 ≤ m) :
    (∑ k ∈ Finset.Icc (j+1) (p - 1), ((((k : ZMod p))⁻¹) ^ m) * (((k - 1).choose j : ℕ) : ZMod p)) =
    ((((j : ZMod p))⁻¹) * ∑ k ∈ Finset.Icc j (p - 1), ((((k : ZMod p))⁻¹) ^ (m - 1)) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) -
    (∑ k ∈ Finset.Icc j (p - 1), ((((k : ZMod p))⁻¹) ^ m) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hjp : j < p := by omega
  have hj0 : ((j : ZMod p)) ≠ 0 := by
    intro h0
    have hdvd : p ∣ j := (ZMod.natCast_eq_zero_iff j p).mp h0
    have hle : p ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega
  have hunit_j : IsUnit ((j : ZMod p)) := isUnit_iff_ne_zero.mpr hj0
  have hm_eq : m = (m - 1) + 1 := by omega
  have hj_eq : j = (j - 1) + 1 := by omega
  -- term identity
  have hterm : ∀ k ∈ Finset.Icc j (p - 1),
      ((((j : ZMod p))⁻¹) * ((((k : ZMod p))⁻¹) ^ (m - 1)) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) -
      ((((k : ZMod p))⁻¹) ^ m) * (((k - 1).choose (j - 1) : ℕ) : ZMod p) =
      ((((k : ZMod p))⁻¹) ^ m) * (((k - 1).choose j : ℕ) : ZMod p) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := by omega
    have hkp : k < p := by omega
    have hjk : j ≤ k := by omega
    have hk0 : ((k : ZMod p)) ≠ 0 := by
      intro h0
      have hdvd : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp h0
      have hle : p ≤ k := Nat.le_of_dvd (by omega) hdvd
      omega
    have hunit_k : IsUnit ((k : ZMod p)) := isUnit_iff_ne_zero.mpr hk0
    have hcm : k.choose j * j = k * ((k-1).choose (j-1)) := choose_mul_identity k j hj1 hjk
    have hcm_cast : (((k.choose j : ℕ)) : ZMod p) * ((j : ZMod p)) = ((k : ZMod p)) * (((k-1).choose (j-1) : ℕ) : ZMod p) := by
      have h := congrArg (fun n : ℕ => ((n : ℕ) : ZMod p)) hcm
      push_cast at h
      simpa using h
    have hJK : ((((j : ZMod p))⁻¹) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) =
        ((((k : ZMod p))⁻¹) * (((k.choose j : ℕ)) : ZMod p)) := by
      have eL : ((((j : ZMod p))⁻¹) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) * (((j : ZMod p)) * ((k : ZMod p))) =
          (((k - 1).choose (j - 1) : ℕ) : ZMod p) * ((k : ZMod p)) := by
        calc ((((j : ZMod p))⁻¹) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) * (((j : ZMod p)) * ((k : ZMod p))) =
            (((k - 1).choose (j - 1) : ℕ) : ZMod p) * ((((j : ZMod p))⁻¹) * ((j : ZMod p))) * ((k : ZMod p)) := by ring
          _ = (((k - 1).choose (j - 1) : ℕ) : ZMod p) * 1 * ((k : ZMod p)) := by rw [ZMod.inv_mul_of_unit _ hunit_j]
          _ = (((k - 1).choose (j - 1) : ℕ) : ZMod p) * ((k : ZMod p)) := by ring
      have eR : ((((k : ZMod p))⁻¹) * (((k.choose j : ℕ)) : ZMod p)) * (((j : ZMod p)) * ((k : ZMod p))) =
          (((k.choose j : ℕ)) : ZMod p) * ((j : ZMod p)) := by
        calc ((((k : ZMod p))⁻¹) * (((k.choose j : ℕ)) : ZMod p)) * (((j : ZMod p)) * ((k : ZMod p))) =
            (((k.choose j : ℕ)) : ZMod p) * ((((k : ZMod p))⁻¹) * ((k : ZMod p))) * ((j : ZMod p)) := by ring
          _ = (((k.choose j : ℕ)) : ZMod p) * 1 * ((j : ZMod p)) := by rw [ZMod.inv_mul_of_unit _ hunit_k]
          _ = (((k.choose j : ℕ)) : ZMod p) * ((j : ZMod p)) := by ring
      have e_eq : (((k - 1).choose (j - 1) : ℕ) : ZMod p) * ((k : ZMod p)) =
          (((k.choose j : ℕ)) : ZMod p) * ((j : ZMod p)) := by
        calc (((k - 1).choose (j - 1) : ℕ) : ZMod p) * ((k : ZMod p)) = ((k : ZMod p)) * (((k - 1).choose (j - 1) : ℕ) : ZMod p) := by ring
          _ = (((k.choose j : ℕ)) : ZMod p) * ((j : ZMod p)) := hcm_cast.symm
      have e1 : ((((j : ZMod p))⁻¹) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) * (((j : ZMod p)) * ((k : ZMod p))) =
        ((((k : ZMod p))⁻¹) * (((k.choose j : ℕ)) : ZMod p)) * (((j : ZMod p)) * ((k : ZMod p))) :=
        eL.trans (e_eq.trans eR.symm)
      have hne : ((j : ZMod p)) * ((k : ZMod p)) ≠ 0 := mul_ne_zero hj0 hk0
      exact mul_right_cancel₀ hne e1
    have hA : ((((j : ZMod p))⁻¹) * ((((k : ZMod p))⁻¹) ^ (m - 1)) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) =
        (((((k : ZMod p))⁻¹) ^ (m - 1)) * ((((k : ZMod p))⁻¹))) * (((k.choose j : ℕ)) : ZMod p) := by
      calc ((((j : ZMod p))⁻¹) * ((((k : ZMod p))⁻¹) ^ (m - 1)) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) =
          ((((k : ZMod p))⁻¹) ^ (m - 1)) * ((((j : ZMod p))⁻¹) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) := by ring
        _ = ((((k : ZMod p))⁻¹) ^ (m - 1)) * ((((k : ZMod p))⁻¹) * (((k.choose j : ℕ)) : ZMod p)) := by rw [hJK]
        _ = (((((k : ZMod p))⁻¹) ^ (m - 1)) * ((((k : ZMod p))⁻¹))) * (((k.choose j : ℕ)) : ZMod p) := by ring
    have hpow : ((((k : ZMod p))⁻¹) ^ (m - 1)) * ((((k : ZMod p))⁻¹)) = ((((k : ZMod p))⁻¹) ^ m) := by
      conv_lhs => rw [← pow_succ]
      congr 1
      omega
    rw [hA, hpow]
    have hpascal : k.choose j = (k - 1).choose (j - 1) + (k - 1).choose j := by
      have e := Nat.choose_succ_succ (k - 1) (j - 1)
      simp only [Nat.succ_eq_add_one] at e
      have hk1' : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
      have hj1' : (j - 1) + 1 = j := Nat.sub_add_cancel hj1
      rw [hk1', hj1'] at e
      exact e
    have hcast : (((k.choose j : ℕ)) : ZMod p) = (((k - 1).choose (j - 1) : ℕ) : ZMod p) + (((k - 1).choose j : ℕ) : ZMod p) := by
      have h := congrArg (fun n : ℕ => ((n : ℕ) : ZMod p)) hpascal
      simpa using h
    rw [hcast]
    ring
  -- sum manipulation
  have hsum_eq : ((((j : ZMod p))⁻¹) * ∑ k ∈ Finset.Icc j (p - 1), ((((k : ZMod p))⁻¹) ^ (m - 1)) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) -
      (∑ k ∈ Finset.Icc j (p - 1), ((((k : ZMod p))⁻¹) ^ m) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) =
      ∑ k ∈ Finset.Icc j (p - 1), ((((k : ZMod p))⁻¹) ^ m) * (((k - 1).choose j : ℕ) : ZMod p) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have h := hterm k hk
    rwa [mul_assoc] at h
  rw [hsum_eq]
  -- restrict from Icc j to Icc (j+1) since k=j term is zero
  have hsplit : Finset.Icc j (p - 1) = insert j (Finset.Icc (j + 1) (p - 1)) := by
    have hle : j ≤ p - 1 := by omega
    have hsucc : Order.succ j = j + 1 := rfl
    have h := Finset.insert_Icc_succ_left_eq_Icc (a := j) (b := p - 1) hle
    rw [hsucc] at h
    exact h.symm
  have hnotmem : j ∉ Finset.Icc (j + 1) (p - 1) := by simp [Finset.mem_Icc]
  have hterm_j : ((((j : ZMod p))⁻¹) ^ m) * ((((j - 1).choose j : ℕ)) : ZMod p) = 0 := by
    have h0 : (j - 1).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h0, Nat.cast_zero, mul_zero]
  have hsum_split : (∑ k ∈ Finset.Icc j (p - 1), ((((k : ZMod p))⁻¹) ^ m) * (((k - 1).choose j : ℕ) : ZMod p)) =
      (∑ k ∈ Finset.Icc (j + 1) (p - 1), ((((k : ZMod p))⁻¹) ^ m) * (((k - 1).choose j : ℕ) : ZMod p)) := by
    rw [hsplit, Finset.sum_insert hnotmem, hterm_j, zero_add]
  exact hsum_split.symm

private theorem key_aux (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (j : ℕ) (hj1 : 1 ≤ j) :
    ∀ (hjp : j ≤ p - 1) (m : ℕ) (hm : m < p - 1),
    multipleHarmonic p (j - 1) m =
    (-1 : ZMod p) ^ (m + j) * ∑ k ∈ Finset.Icc j (p - 1), ((((k : ZMod p))⁻¹) ^ m) * (((k - 1).choose (j - 1) : ℕ) : ZMod p) := by
  induction j, hj1 using Nat.le_induction with
  | base =>
    intro hjp m hm
    -- j = 1, so j-1 = 0, Icc j (p-1) = Icc 1 (p-1), (j-1)=0 so choose =1
    simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
    -- goal: H p 0 m = (-1)^(m+1) * ∑ (k⁻¹)^m
    have hsum := inv_pow_sum_general p m hp hp2
    rw [hsum]
    have hdvd_iff : ((p - 1) ∣ m ↔ m = 0) := by
      constructor
      · intro hdvd
        by_cases hm0 : m = 0
        · exact hm0
        · have hle : p - 1 ≤ m := Nat.le_of_dvd (by omega) hdvd
          omega
      · intro hm0
        subst hm0
        exact dvd_zero _
    by_cases hm0 : m = 0
    · subst hm0
      simp only [Nat.zero_add] at ⊢
      rw [multipleHarmonic_zero]
      have hpos : (0 : ZMod p) + 1 = 1 := by simp
      -- (-1)^(0+1) * -1 = 1
      have hdvd0 : (p - 1) ∣ 0 := dvd_zero _
      rw [ite_eq_left hdvd0]
      simp
    · have hH0 : multipleHarmonic p 0 m = 0 := multipleHarmonic_eq_zero_of_pos p m (by omega)
      rw [hH0]
      have hndvd : ¬ (p - 1) ∣ m := fun hd => hm0 ((hdvd_iff).mp hd)
      rw [ite_eq_right hndvd, mul_zero]
  | succ j hj IH =>
    intro hjp m hm
    have hj_le : j ≤ p - 1 := by omega
    have hp_ge : 2 < p := by omega
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have hjp_lt : j + 1 < p + 1 := by omega
    have hj_sub : (j + 1) - 1 = j := by omega
    rw [hj_sub]
    by_cases hm0 : m = 0
    · -- m = 0 case: H = 1, RHS via hockey-stick
      subst hm0
      rw [multipleHarmonic_zero]
      simp only [pow_zero, one_mul]
      -- hockey-stick with shift
      have hstick : (∑ k ∈ Finset.Icc (j+1) (p - 1), (((k - 1).choose j : ℕ) : ZMod p)) =
          (((p - 1).choose (j+1) : ℕ) : ZMod p) := by
        have hbij : ∀ t ∈ Finset.Icc j (p - 2), ∃ k ∈ Finset.Icc (j+1) (p - 1), k - 1 = t := by
          intro t ht
          rw [Finset.mem_Icc] at ht
          refine ⟨t + 1, by rw [Finset.mem_Icc]; omega, by omega⟩
        have hsum_nat : ∑ k ∈ Finset.Icc (j+1) (p - 1), (k-1).choose j = (p-1).choose (j+1) := by
          have h1 : ∑ k ∈ Finset.Icc (j+1) (p - 1), (k-1).choose j = ∑ t ∈ Finset.Icc j (p-2), t.choose j := by
            apply Finset.sum_bij (fun k _ => k - 1)
            · intro k hk
              rw [Finset.mem_Icc] at hk ⊢
              omega
            · intro a ha b hb hab
              rw [Finset.mem_Icc] at ha hb
              omega
            · intro t ht
              rw [Finset.mem_Icc] at ht
              refine ⟨t + 1, by rw [Finset.mem_Icc]; omega, by omega⟩
            · intro k hk
              rfl
          rw [h1]
          have h2 := Nat.sum_Icc_choose (p-2) j
          -- Nat.sum_Icc_choose n k: ∑ m ∈ Icc k n, m.choose k = (n+1).choose (k+1)
          -- with n=p-2, k=j: ∑_{m∈Icc j (p-2)} = (p-2+1).choose (j+1) = (p-1).choose (j+1)
          have hp2 : p - 2 + 1 = p - 1 := by omega
          rw [hp2] at h2
          exact h2
        have hcast : (∑ k ∈ Finset.Icc (j+1) (p - 1), (((k - 1).choose j : ℕ) : ZMod p)) =
            ((((∑ k ∈ Finset.Icc (j+1) (p - 1), (k-1).choose j : ℕ)) : ZMod p)) := by
          push_cast
          rfl
        rw [hcast, hsum_nat]
      rw [hstick, choose_mod_prime p (j+1) hp (by omega)]
      -- (-1)^(0+(j+1)) * (-1)^(j+1) = 1
      have hpow : (-1 : ZMod p) ^ (0 + (j+1)) * (-1 : ZMod p) ^ (j+1) = 1 := by
        rw [Nat.zero_add, ← pow_add]
        have heven : Even ((j+1) + (j+1)) := ⟨j+1, rfl⟩
        exact Even.neg_one_pow heven
      -- goal: 1 = (-1)^(0+(j+1)) * (-1)^(j+1) ? Actually LHS=1 (from H), RHS=... ; need 1 = ...
      -- Our goal after rw: 1 = (-1)^(0+(j+1)) * (-1)^(j+1) ? Let's see: LHS H=1, RHS = (-1)^... * C, C=(-1)^..., so RHS = (-1)^...*(-1)^... =1 via hpow. So goal 1 = ... becomes ... =1? Actually goal is H = RHS, H=1, RHS=... , so 1 = ... . Use hpow.symm.
      exact hpow.symm
    · -- m ≥ 1 case
      obtain ⟨mt, rfl⟩ : ∃ mt, m = mt + 1 := ⟨m-1, by omega⟩
      have hm1 : 1 ≤ mt + 1 := by omega
      have hmt_lt : mt < p - 1 := by omega
      have hj1' : 1 ≤ j := hj
      have hj_eq : j = (j - 1) + 1 := (Nat.sub_add_cancel hj1').symm
      -- H recurrence: H_j^{mt+1} = H_{j-1}^{mt+1} + j⁻¹ * H_{j-1}^{mt}
      have hHrec : multipleHarmonic p j (mt + 1) =
          multipleHarmonic p (j - 1) (mt + 1) + ((((j : ℕ)) : ZMod p))⁻¹ * multipleHarmonic p (j - 1) mt := by
        have e := multipleHarmonic_succ p (j - 1) mt
        have hjc : (j - 1) + 1 = j := Nat.sub_add_cancel hj1'
        rw [hjc] at e
        -- e has ((((j-1)+1 : ℕ)):ZMod)⁻¹, need ((j:ZMod))⁻¹ ; they are equal since (j-1)+1=j as Nats
        simpa [hjc] using e
      rw [hHrec]
      have IH1 := IH hj_le (mt + 1) (by omega : mt + 1 < p - 1)
      have IH0 := IH hj_le mt hmt_lt
      rw [IH1, IH0]
      have hS := S_recurrence p j (mt + 1) hp hj hjp hm1
      -- hS : S(j+1) = j⁻¹*S(j,mt) - S(j,mt+1)  (with appropriate sums)
      -- Goal: H_{j-1}^{mt+1} + j⁻¹*H_{j-1}^{mt} = (-1)^{(mt+1)+(j+1)} * S(j+1)
      -- Substitute IH1, IH0: LHS = c1*S1 + j⁻¹*(c0*S0) where c1=(-1)^{(mt+1)+j}, c0=(-1)^{mt+j}, S1=S(j,mt+1), S0=S(j,mt)
      -- RHS = c2*S(j+1) where c2=(-1)^{(mt+1)+(j+1)}, S(j+1)=j⁻¹*S0 - S1 (via hS)
      -- Sign: c1 = -c2? Since (mt+1)+j+1 = (mt+1)+(j+1)? Actually c1 exponent (mt+1)+j, c2 exponent (mt+1)+(j+1) = c1 exponent +1, so c2 = -c1. Similarly c0 exponent mt+j, c1 exponent (mt+1)+j = c0 exponent +1, so c1 = -c0. Good.
      -- Then LHS = c1*S1 + j⁻¹*c0*S0 = c1*S1 - j⁻¹*c1*S0 (since c0 = -c1) = -c1*(j⁻¹*S0 - S1) = c2*(j⁻¹*S0 - S1) = RHS. Good!
      have hsign1 : (-1 : ZMod p) ^ ((mt + 1) + (j + 1)) = -((-1 : ZMod p) ^ ((mt + 1) + j)) := by
        have e : (mt + 1) + (j + 1) = ((mt + 1) + j) + 1 := by omega
        rw [e, pow_succ]
        ring
      have hsign0 : (-1 : ZMod p) ^ (mt + j) = -((-1 : ZMod p) ^ ((mt + 1) + j)) := by
        have e : (mt + 1) + j = (mt + j) + 1 := by omega
        rw [e, pow_succ]
        ring
        -- (-1)^{t+1} = (-1)^t * (-1) = -(-1)^t, so (-1)^t = -(-1)^{t+1}? Actually from e: c1 = c0*(-1) = -c0, so c0 = -c1. Good.
      simp only [Nat.add_sub_cancel] at hS
      rw [hS, hsign1, hsign0]
      ring

private theorem inv_mul_choose_identity (p k j : ℕ) (hp : p.Prime) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hkp : k < p) :
    ((((j : ZMod p))⁻¹) * ((((k - 1).choose (j - 1) : ℕ)) : ZMod p)) =
    ((((k : ZMod p))⁻¹) * ((((k.choose j : ℕ))) : ZMod p)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hjp : j < p := by omega
  have hk0 : ((k : ZMod p)) ≠ 0 := by
    intro h0
    have hdvd : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp h0
    have hle : p ≤ k := Nat.le_of_dvd (by omega) hdvd
    omega
  have hj0 : ((j : ZMod p)) ≠ 0 := by
    intro h0
    have hdvd : p ∣ j := (ZMod.natCast_eq_zero_iff j p).mp h0
    have hle : p ≤ j := Nat.le_of_dvd (by omega) hdvd
    omega
  have hunit_k : IsUnit ((k : ZMod p)) := isUnit_iff_ne_zero.mpr hk0
  have hunit_j : IsUnit ((j : ZMod p)) := isUnit_iff_ne_zero.mpr hj0
  have hcm : k.choose j * j = k * ((k - 1).choose (j - 1)) :=
    choose_mul_identity k j hj1 hjk
  have hcm_cast : (((k.choose j : ℕ)) : ZMod p) * ((j : ZMod p)) =
      ((k : ZMod p)) * (((k - 1).choose (j - 1) : ℕ) : ZMod p) := by
    have h := congrArg (fun nn : ℕ => ((nn : ℕ) : ZMod p)) hcm
    push_cast at h
    simpa using h
  have eL : ((((j : ZMod p))⁻¹) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) *
        (((j : ZMod p)) * ((k : ZMod p))) =
        (((k - 1).choose (j - 1) : ℕ) : ZMod p) * ((k : ZMod p)) := by
    calc ((((j : ZMod p))⁻¹) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) *
            (((j : ZMod p)) * ((k : ZMod p))) =
          (((k - 1).choose (j - 1) : ℕ) : ZMod p) *
            ((((j : ZMod p))⁻¹) * ((j : ZMod p))) * ((k : ZMod p)) := by ring
      _ = (((k - 1).choose (j - 1) : ℕ) : ZMod p) * 1 * ((k : ZMod p)) := by
          rw [ZMod.inv_mul_of_unit _ hunit_j]
      _ = (((k - 1).choose (j - 1) : ℕ) : ZMod p) * ((k : ZMod p)) := by ring
  have eR : ((((k : ZMod p))⁻¹) * (((k.choose j : ℕ)) : ZMod p)) *
        (((j : ZMod p)) * ((k : ZMod p))) =
        (((k.choose j : ℕ)) : ZMod p) * ((j : ZMod p)) := by
    calc ((((k : ZMod p))⁻¹) * (((k.choose j : ℕ)) : ZMod p)) *
            (((j : ZMod p)) * ((k : ZMod p))) =
          (((k.choose j : ℕ)) : ZMod p) * ((((k : ZMod p))⁻¹) * ((k : ZMod p))) *
            ((j : ZMod p)) := by ring
      _ = (((k.choose j : ℕ)) : ZMod p) * 1 * ((j : ZMod p)) := by
          rw [ZMod.inv_mul_of_unit _ hunit_k]
      _ = (((k.choose j : ℕ)) : ZMod p) * ((j : ZMod p)) := by ring
  have e_eq : (((k - 1).choose (j - 1) : ℕ) : ZMod p) * ((k : ZMod p)) =
      (((k.choose j : ℕ)) : ZMod p) * ((j : ZMod p)) := by
    calc (((k - 1).choose (j - 1) : ℕ) : ZMod p) * ((k : ZMod p)) =
          ((k : ZMod p)) * (((k - 1).choose (j - 1) : ℕ) : ZMod p) := by ring
      _ = (((k.choose j : ℕ)) : ZMod p) * ((j : ZMod p)) := hcm_cast.symm
  have e1 : ((((j : ZMod p))⁻¹) * (((k - 1).choose (j - 1) : ℕ) : ZMod p)) *
          (((j : ZMod p)) * ((k : ZMod p))) =
        ((((k : ZMod p))⁻¹) * (((k.choose j : ℕ)) : ZMod p)) *
          (((j : ZMod p)) * ((k : ZMod p))) :=
    eL.trans (e_eq.trans eR.symm)
  have hne : ((j : ZMod p)) * ((k : ZMod p)) ≠ 0 := mul_ne_zero hj0 hk0
  exact mul_right_cancel₀ hne e1


/-- **Mattarei–Tauraso polynomial congruence for multiple harmonic sums.** Let $n \ge 1$ and let
$p$ be a prime with $p > n + 1$, write $H_r^{(m)}$ for the multiple harmonic sum modulo $p$, and
write $k^{-1}$ for the inverse of $k$ in $\mathbb{Z}/p\mathbb{Z}$. Then, as polynomials in $x$
over $\mathbb{Z}/p\mathbb{Z}$,
$$\sum_{k=1}^{p-1} H_{k-1}^{(n-1)} k^{-1} x^k = (-1)^{n-1} \sum_{k=1}^{p-1} (k^{-1})^n (1 - x)^k.$$

Proves `Wanted` entry `multiple_harmonic_polynomial_congruence`.

Source: `https://cs.uwaterloo.ca/journals/JIS/VOL13/Tauraso/tauraso22.tex`, Lemma `Gg`,
semantic concept `jis_sem_1e299eb15a144f108cb2fe31`,
statement `jis_9e5865a09e42b4fb025d838d`.
-/
theorem multiple_harmonic_polynomial_congruence (n p : ℕ) (hn : 0 < n)
    (hp : p.Prime) (hpp : n + 1 < p) :
    (∑ k ∈ Finset.Icc 1 (p - 1),
      Polynomial.C (multipleHarmonic p (k - 1) (n - 1) * (((k : ZMod p))⁻¹)) *
        (Polynomial.X : Polynomial (ZMod p)) ^ k) =
    Polynomial.C ((-1 : ZMod p) ^ (n - 1)) *
      ∑ k ∈ Finset.Icc 1 (p - 1),
        Polynomial.C (((((k : ZMod p))⁻¹) ^ n)) *
          (1 - (Polynomial.X : Polynomial (ZMod p))) ^ k := by
  have hp2 : 2 < p := by omega
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hmlt : m < p - 1 := by omega
  have hndvd : ¬ (p - 1) ∣ (m + 1) := by
    intro hdvd
    have hle : p - 1 ≤ m + 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  have hsum_n : (∑ k ∈ Finset.Icc 1 (p - 1), ((((k : ZMod p))⁻¹) ^ (m + 1))) = 0 := by
    have h := inv_pow_sum_general p (m + 1) hp hp2
    rw [ite_eq_right hndvd] at h
    exact h
  apply Polynomial.ext
  intro j
  have hLHS : (((∑ k ∈ Finset.Icc 1 (p - 1),
      Polynomial.C (multipleHarmonic p (k - 1) m * (((k : ZMod p))⁻¹)) *
        (Polynomial.X : Polynomial (ZMod p)) ^ k) : Polynomial (ZMod p)).coeff j) =
      (if j ∈ Finset.Icc 1 (p - 1) then multipleHarmonic p (j - 1) m * (((j : ZMod p))⁻¹) else 0) := by
    rw [Polynomial.finset_sum_coeff]
    have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
        ((Polynomial.C (multipleHarmonic p (k - 1) m * (((k : ZMod p))⁻¹)) *
          (Polynomial.X : Polynomial (ZMod p)) ^ k).coeff j) =
        (if j = k then multipleHarmonic p (k - 1) m * (((k : ZMod p))⁻¹) else 0) := by
      intro k _
      rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_congr rfl hterm]
    exact Finset.sum_ite_eq _ _ _
  have hRHS : ((Polynomial.C ((-1 : ZMod p) ^ m) *
      (∑ k ∈ Finset.Icc 1 (p - 1),
        Polynomial.C (((((k : ZMod p))⁻¹) ^ (m + 1))) *
          (1 - (Polynomial.X : Polynomial (ZMod p))) ^ k) : Polynomial (ZMod p)).coeff j) =
      (-1 : ZMod p) ^ m * ∑ k ∈ Finset.Icc 1 (p - 1),
        ((((k : ZMod p))⁻¹) ^ (m + 1)) * ((-1 : ZMod p) ^ j * (((k.choose j : ℕ)) : ZMod p)) := by
    rw [Polynomial.coeff_C_mul]
    congr 1
    rw [Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.coeff_C_mul, coeff_one_sub_X_pow]
  rw [hLHS, hRHS]
  by_cases hj0 : j = 0
  · subst hj0
    have hnot : (0 : ℕ) ∉ Finset.Icc 1 (p - 1) := by simp
    rw [ite_eq_right hnot]
    have hsum0 : (∑ k ∈ Finset.Icc 1 (p - 1),
          ((((k : ZMod p))⁻¹) ^ (m + 1)) *
          ((-1 : ZMod p) ^ (0 : ℕ) * (((k.choose 0 : ℕ)) : ZMod p))) =
        ∑ k ∈ Finset.Icc 1 (p - 1), ((((k : ZMod p))⁻¹) ^ (m + 1)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp
    rw [hsum0, hsum_n, mul_zero]
  · by_cases hjmem : j ∈ Finset.Icc 1 (p - 1)
    · rw [Finset.mem_Icc] at hjmem
      obtain ⟨hj1, hjp⟩ := hjmem
      rw [ite_eq_left (Finset.mem_Icc.mpr ⟨hj1, hjp⟩)]
      have hkey := key_aux p hp hp2 j hj1 hjp m hmlt
      have hsub : Finset.Icc j (p - 1) ⊆ Finset.Icc 1 (p - 1) :=
        Finset.Icc_subset_Icc (by omega) le_rfl
      have hpoint : ∀ k ∈ Finset.Icc j (p - 1),
          ((((k : ZMod p))⁻¹) ^ (m + 1)) * ((((k.choose j : ℕ))) : ZMod p) =
          ((((j : ZMod p))⁻¹)) * (((((k : ZMod p))⁻¹) ^ m) * ((((k - 1).choose (j - 1) : ℕ)) : ZMod p)) := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hkp : k < p := by omega
        have hjk : j ≤ k := by omega
        have hJK := inv_mul_choose_identity p k j hp hj1 hjk hkp
        have hpow : ((((k : ZMod p))⁻¹) ^ (m + 1)) =
            ((((k : ZMod p))⁻¹) ^ m) * ((((k : ZMod p))⁻¹)) := pow_succ _ _
        rw [hpow]
        calc ((((k : ZMod p))⁻¹) ^ m * (((k : ZMod p))⁻¹)) * ((((k.choose j : ℕ))) : ZMod p)
            = ((((k : ZMod p))⁻¹) ^ m) * (((((k : ZMod p))⁻¹) * ((((k.choose j : ℕ))) : ZMod p))) := by ring
          _ = ((((k : ZMod p))⁻¹) ^ m) * (((((j : ZMod p))⁻¹) * ((((k - 1).choose (j - 1) : ℕ)) : ZMod p))) := by rw [← hJK]
          _ = ((((j : ZMod p))⁻¹)) * (((((k : ZMod p))⁻¹) ^ m) * ((((k - 1).choose (j - 1) : ℕ)) : ZMod p)) := by ring
      have hvan : ∀ k ∈ Finset.Icc 1 (p - 1), k ∉ Finset.Icc j (p - 1) →
          ((((k : ZMod p))⁻¹) ^ (m + 1)) * ((-1 : ZMod p) ^ j * (((k.choose j : ℕ)) : ZMod p)) = 0 := by
        intro k hk hkout
        rw [Finset.mem_Icc] at hk
        rw [Finset.mem_Icc] at hkout
        push_neg at hkout
        have hkj : k < j := by omega
        have hC : k.choose j = 0 := Nat.choose_eq_zero_of_lt hkj
        rw [hC, Nat.cast_zero, mul_zero, mul_zero]
      have hrestr : (∑ k ∈ Finset.Icc 1 (p - 1),
            ((((k : ZMod p))⁻¹) ^ (m + 1)) * ((-1 : ZMod p) ^ j * (((k.choose j : ℕ)) : ZMod p))) =
          ∑ k ∈ Finset.Icc j (p - 1),
            ((((k : ZMod p))⁻¹) ^ (m + 1)) * ((-1 : ZMod p) ^ j * (((k.choose j : ℕ)) : ZMod p)) := by
        have h := Finset.sum_subset hsub (fun k hk hkout => hvan k hk hkout)
        exact h.symm
      rw [hrestr]
      have hfact : (∑ k ∈ Finset.Icc j (p - 1),
            ((((k : ZMod p))⁻¹) ^ (m + 1)) * ((-1 : ZMod p) ^ j * (((k.choose j : ℕ)) : ZMod p))) =
          ((-1 : ZMod p) ^ j * ((((j : ZMod p))⁻¹))) *
            (∑ k ∈ Finset.Icc j (p - 1),
              ((((k : ZMod p))⁻¹) ^ m) * ((((k - 1).choose (j - 1) : ℕ)) : ZMod p)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hp_k := hpoint k hk
        calc ((((k : ZMod p))⁻¹) ^ (m + 1)) * ((-1 : ZMod p) ^ j * ((((k.choose j : ℕ))) : ZMod p))
            = ((-1 : ZMod p) ^ j) * (((((k : ZMod p))⁻¹) ^ (m + 1)) * ((((k.choose j : ℕ))) : ZMod p)) := by ring
          _ = ((-1 : ZMod p) ^ j) * (((((j : ZMod p))⁻¹)) * (((((k : ZMod p))⁻¹) ^ m) * ((((k - 1).choose (j - 1) : ℕ)) : ZMod p))) := by rw [hp_k]
          _ = ((-1 : ZMod p) ^ j * ((((j : ZMod p))⁻¹))) * (((((k : ZMod p))⁻¹) ^ m) * ((((k - 1).choose (j - 1) : ℕ)) : ZMod p)) := by ring
      rw [hfact, hkey]
      have hpow : (-1 : ZMod p) ^ (m + j) = (-1 : ZMod p) ^ m * (-1 : ZMod p) ^ j := pow_add _ _ _
      rw [hpow]
      ring
    · rw [ite_eq_right hjmem]
      have hjgt : p - 1 < j := by
        rw [Finset.mem_Icc] at hjmem
        push_neg at hjmem
        omega
      have hzero : ∀ k ∈ Finset.Icc 1 (p - 1),
          ((((k : ZMod p))⁻¹) ^ (m + 1)) * ((-1 : ZMod p) ^ j * (((k.choose j : ℕ)) : ZMod p)) = 0 := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hC : k.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hC, Nat.cast_zero, mul_zero, mul_zero]
      rw [Finset.sum_eq_zero hzero, mul_zero]

end MetaMathlibExt
