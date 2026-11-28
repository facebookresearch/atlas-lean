/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set

@[expose] public section

/-!
# Carlitz block harmonic sum

The block harmonic sum used in the classical application of Carlitz's
generalization of Wolstenholme's theorem vanishes modulo `p ^ 2`.
-/

/-- Sum of two inverses as a product inverse, for units in `ZMod n`. -/
private theorem ZMod.inv_add_inv_of_isUnit {n : ℕ} {a b : ZMod n}
    (ha : IsUnit a) (hb : IsUnit b) :
    a⁻¹ + b⁻¹ = (a + b) * (a * b)⁻¹ := by
  have hmul : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
    apply ZMod.inv_eq_of_mul_eq_one _ _ _
    have e1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit _ ha
    have e2 : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit _ hb
    calc (a * b) * (a⁻¹ * b⁻¹)
        = (a * a⁻¹) * (b * b⁻¹) := by ring
      _ = 1 := by rw [e1, e2, mul_one]
  rw [hmul]
  have e1 : a * a⁻¹ = 1 := ZMod.mul_inv_of_unit _ ha
  have e2 : b * b⁻¹ = 1 := ZMod.mul_inv_of_unit _ hb
  have r1 : a * (a⁻¹ * b⁻¹) = b⁻¹ := by rw [← mul_assoc, e1, one_mul]
  have r2 : b * (a⁻¹ * b⁻¹) = a⁻¹ := by
    have h : b * (a⁻¹ * b⁻¹) = a⁻¹ * (b * b⁻¹) := by ring
    rw [h, e2, mul_one]
  calc a⁻¹ + b⁻¹ = b⁻¹ + a⁻¹ := by ring
    _ = a * (a⁻¹ * b⁻¹) + b * (a⁻¹ * b⁻¹) := by rw [r1, r2]
    _ = (a + b) * (a⁻¹ * b⁻¹) := by ring

/-- A ring hom out of `ZMod n` sends a unit inverse to the inverse. -/
private theorem ZMod.map_inv_of_isUnit {n : ℕ} {F : Type*} [Field F]
    (π : ZMod n →+* F) {x : ZMod n} (hx : IsUnit x) :
    π (x⁻¹) = (π x)⁻¹ := by
  have h : π x * π (x⁻¹) = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit _ hx, map_one]
  have h2 := eq_inv_of_mul_eq_one_left h
  rw [h2, inv_inv]

/-- A sum over `Finset.range p` of a cast function equals the sum over `ZMod p`. -/
private theorem ZMod.sum_range_cast {M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p]
    (φ : ZMod p → M) :
    ∑ i ∈ Finset.range p, φ ((i : ℕ) : ZMod p) = ∑ x, φ x := by
  apply Finset.sum_bij (fun i _ => ((i : ℕ) : ZMod p))
  · intro i _
    exact Finset.mem_univ _
  · intro i hi j hj h
    simp only [Finset.mem_range] at hi hj
    have h' : ((i : ℕ) : ZMod p) = ((j : ℕ) : ZMod p) := h
    have hmod : i ≡ j [MOD p] := (ZMod.natCast_eq_natCast_iff i j p).mp h'
    exact Nat.ModEq.eq_of_lt_of_lt hmod hi hj
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
  · intro i _
    rfl

/-- A sum over `Finset.Ico 1 p` of a cast function vanishing at `0`
equals the sum over `ZMod p`. -/
private theorem ZMod.sum_Ico_cast {M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p]
    (φ : ZMod p → M) (hφ0 : φ 0 = 0) :
    ∑ r ∈ Finset.Ico 1 p, φ ((r : ℕ) : ZMod p) = ∑ x, φ x := by
  have hrange := ZMod.sum_range_cast p φ
  have h0mem : 0 ∈ Finset.range p :=
    Finset.mem_range.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have herase := Finset.add_sum_erase (Finset.range p)
    (fun i => φ ((i : ℕ) : ZMod p)) h0mem
  have heq : (Finset.range p).erase 0 = Finset.Ico 1 p := by
    ext r
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [heq] at herase
  have hφ0' : φ (((0 : ℕ)) : ZMod p) = 0 := by
    rw [Nat.cast_zero]
    exact hφ0
  rw [hφ0', zero_add] at herase
  rw [herase]
  exact hrange

/-- The kernel fact: an element of `ZMod (p ^ 2)` mapping to `0` in `ZMod p`
is a multiple of `p`. -/
private theorem ZMod.eq_mul_p_of_castHom_eq_zero {p : ℕ} [NeZero (p ^ 2)]
    (H : ZMod (p ^ 2))
    (hH : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) H = 0) :
    ∃ H' : ZMod (p ^ 2), H = ((p : ℕ) : ZMod (p ^ 2)) * H' := by
  set v := H.val with hv
  have hH2 : H = (((v : ℕ)) : ZMod (p ^ 2)) := (ZMod.natCast_zmod_val H).symm
  have hmap : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (((v : ℕ)) : ZMod (p ^ 2))
      = (((v : ℕ)) : ZMod p) := map_natCast _ _
  have hcast : ((((v : ℕ))) : ZMod p) = 0 := by
    rw [← hmap, ← hH2]
    exact hH
  have hdvd : p ∣ v := (CharP.cast_eq_zero_iff (ZMod p) p v).mp hcast
  obtain ⟨t, ht⟩ := hdvd
  exact ⟨(((t : ℕ)) : ZMod (p ^ 2)), by rw [hH2, ht, Nat.cast_mul]⟩

/-- **Carlitz's block harmonic congruence.** Let $p \ge 5$ be a prime and let $k \in \mathbb{N}$.
Then in $\mathbb{Z}/p^2\mathbb{Z}$
$$\sum_{r=1}^{p-1} (kp + r)^{-1} = 0.$$

Each $kp + r$ with $1 \le r \le p - 1$ is prime to $p$, so these inverses are genuine inverses
modulo $p^2$.

Cited original: L. Carlitz, "A note on Wolstenholme's theorem", American
Mathematical Monthly 61 (1954), 174–176.

Source: Jerry Metzger and Thomas Richards, "A Prisoner Problem Variation",
`https://cs.uwaterloo.ca/journals/JIS/VOL18/Metzger/metz1.tex`, lines 657–662
(live file SHA-256
`660bfcb06fb3e08814f30b24659410fba256effd4161ec1cca7ea9fc3d20b0ec`;
exact source-span SHA-256
`0aa191b703844e65e7e2fd1c181532b3409c2720e7317d93f130d66c66f34d0f`;
concept `jis_dep_8bfbdf778d8b84efc2cbaafc`).
-/
theorem ZMod.carlitz_sum_inv_block_Ico_eq_zero_of_five_le
    (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Finset.Ico 1 p).sum
      (fun r => (((k * p + r : ℕ) : ZMod (p ^ 2))⁻¹)) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hcopA : ∀ r : ℕ, 1 ≤ r → r < p → Nat.Coprime (k * p + r) (p ^ 2) := by
    intro r hr1 hr2
    rw [Nat.coprime_pow_right_iff (by norm_num : 0 < 2)]
    apply Nat.Coprime.symm
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have hkp : p ∣ k * p := dvd_mul_left p k
    have hpr : p ∣ r := (Nat.dvd_add_right hkp).mp hd
    have hr0 : r = 0 := Nat.eq_zero_of_dvd_of_lt hpr hr2
    omega
  have hcopB : ∀ r : ℕ, 1 ≤ r → r < p → Nat.Coprime (k * p + (p - r)) (p ^ 2) := by
    intro r hr1 hr2
    rw [Nat.coprime_pow_right_iff (by norm_num : 0 < 2)]
    apply Nat.Coprime.symm
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have hkp : p ∣ k * p := dvd_mul_left p k
    have hpr : p ∣ (p - r) := (Nat.dvd_add_right hkp).mp hd
    have hlt : p - r < p := by omega
    have h0 : p - r = 0 := Nat.eq_zero_of_dvd_of_lt hpr hlt
    omega
  have hUA : ∀ r : ℕ, 1 ≤ r → r < p →
      IsUnit ((k * p + r : ℕ) : ZMod (p ^ 2)) := by
    intro r hr1 hr2
    exact ⟨ZMod.unitOfCoprime _ (hcopA r hr1 hr2), ZMod.coe_unitOfCoprime _ _⟩
  have hUB : ∀ r : ℕ, 1 ≤ r → r < p →
      IsUnit ((k * p + (p - r) : ℕ) : ZMod (p ^ 2)) := by
    intro r hr1 hr2
    exact ⟨ZMod.unitOfCoprime _ (hcopB r hr1 hr2), ZMod.coe_unitOfCoprime _ _⟩
  have hpair : ∀ r : ℕ, 1 ≤ r → r < p →
      ((k * p + r : ℕ) : ZMod (p ^ 2))⁻¹ + ((k * p + (p - r) : ℕ) : ZMod (p ^ 2))⁻¹
        = ((p : ℕ) : ZMod (p ^ 2)) * (((2 * k + 1 : ℕ) : ZMod (p ^ 2)) *
          (((k * p + r : ℕ) : ZMod (p ^ 2)) * ((k * p + (p - r) : ℕ) : ZMod (p ^ 2)))⁻¹) := by
    intro r hr1 hr2
    have hAB : ((k * p + r : ℕ) : ZMod (p ^ 2)) + ((k * p + (p - r) : ℕ) : ZMod (p ^ 2))
        = ((p : ℕ) : ZMod (p ^ 2)) * ((2 * k + 1 : ℕ) : ZMod (p ^ 2)) := by
      have hnat : k * p + r + (k * p + (p - r)) = (2 * k + 1) * p := by
        have hr : r ≤ p := le_of_lt hr2
        have e : (2 * k + 1) * p = 2 * (k * p) + p := by ring
        omega
      have hcast : ((k * p + r + (k * p + (p - r)) : ℕ) : ZMod (p ^ 2))
          = (((2 * k + 1) * p : ℕ) : ZMod (p ^ 2)) := by rw [hnat]
      have e1 : ((k * p + r : ℕ) : ZMod (p ^ 2)) + ((k * p + (p - r) : ℕ) : ZMod (p ^ 2))
          = ((k * p + r + (k * p + (p - r)) : ℕ) : ZMod (p ^ 2)) := by
        push_cast
        ring
      have e2 : (((2 * k + 1) * p : ℕ) : ZMod (p ^ 2))
          = ((p : ℕ) : ZMod (p ^ 2)) * ((2 * k + 1 : ℕ) : ZMod (p ^ 2)) := by
        push_cast
        ring
      rw [e1, hcast, e2]
    rw [ZMod.inv_add_inv_of_isUnit (hUA r hr1 hr2) (hUB r hr1 hr2), hAB, mul_assoc]
  have hSrange : (Finset.Ico 1 p).sum
        (fun r => (((k * p + r : ℕ) : ZMod (p ^ 2))⁻¹))
      = ∑ j ∈ Finset.range (p - 1),
        ((k * p + (1 + j) : ℕ) : ZMod (p ^ 2))⁻¹ := by
    rw [Finset.sum_Ico_eq_sum_range]
  have hSmirror : (Finset.Ico 1 p).sum
        (fun r => (((k * p + r : ℕ) : ZMod (p ^ 2))⁻¹))
      = ∑ j ∈ Finset.range (p - 1),
        ((k * p + (p - (1 + j)) : ℕ) : ZMod (p ^ 2))⁻¹ := by
    rw [hSrange, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have e : 1 + (p - 1 - 1 - j) = p - (1 + j) := by
      simp only [Finset.mem_range] at hj
      omega
    show ((k * p + (1 + (p - 1 - 1 - j)) : ℕ) : ZMod (p ^ 2))⁻¹
      = ((k * p + (p - (1 + j)) : ℕ) : ZMod (p ^ 2))⁻¹
    rw [e]
  have h2S : (2 : ZMod (p ^ 2)) * (Finset.Ico 1 p).sum
        (fun r => (((k * p + r : ℕ) : ZMod (p ^ 2))⁻¹))
      = ((p : ℕ) : ZMod (p ^ 2)) * ∑ j ∈ Finset.range (p - 1),
          ((2 * k + 1 : ℕ) : ZMod (p ^ 2)) *
            (((k * p + (1 + j) : ℕ) : ZMod (p ^ 2)) *
              ((k * p + (p - (1 + j)) : ℕ) : ZMod (p ^ 2)))⁻¹ := by
    rw [two_mul]
    nth_rewrite 1 [hSrange]
    rw [hSmirror, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hr1 : 1 ≤ 1 + j := Nat.le_add_right 1 j
    have hr2 : 1 + j < p := by omega
    exact hpair (1 + j) hr1 hr2
  have hπA : ∀ r : ℕ,
      ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
        ((k * p + r : ℕ) : ZMod (p ^ 2)) = ((r : ℕ) : ZMod p) := by
    intro r
    rw [map_natCast]
    have h0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
    have hsplit : ((k * p + r : ℕ) : ZMod p)
        = ((k : ℕ) : ZMod p) * ((p : ℕ) : ZMod p) + ((r : ℕ) : ZMod p) := by
      push_cast
      ring
    rw [hsplit, h0, mul_zero, zero_add]
  have hπB : ∀ r : ℕ, 1 ≤ r → r < p →
      ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
        ((k * p + (p - r) : ℕ) : ZMod (p ^ 2)) = -((r : ℕ) : ZMod p) := by
    intro r hr1 hr2
    rw [map_natCast]
    have h0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
    have hrp : r ≤ p := le_of_lt hr2
    have hsub : ((p - r : ℕ) : ZMod p)
        = ((p : ℕ) : ZMod p) - ((r : ℕ) : ZMod p) :=
      Nat.cast_sub hrp
    have hsplit : ((k * p + (p - r) : ℕ) : ZMod p)
        = ((k : ℕ) : ZMod p) * ((p : ℕ) : ZMod p) + ((p - r : ℕ) : ZMod p) := by
      push_cast
      ring
    rw [hsplit, hsub, h0, mul_zero, zero_add, zero_sub]
  have hπh : ∀ r : ℕ, 1 ≤ r → r < p →
      ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
        (((2 * k + 1 : ℕ) : ZMod (p ^ 2)) *
          (((k * p + r : ℕ) : ZMod (p ^ 2)) * ((k * p + (p - r) : ℕ) : ZMod (p ^ 2)))⁻¹)
        = ((2 * k + 1 : ℕ) : ZMod p) * (-(((r : ℕ) : ZMod p) ^ 2))⁻¹ := by
    intro r hr1 hr2
    rw [map_mul, map_natCast,
      ZMod.map_inv_of_isUnit _ ((hUA r hr1 hr2).mul (hUB r hr1 hr2)),
      map_mul, hπA, hπB r hr1 hr2]
    congr 1
    congr 1
    ring
  have hfield : (∑ x : ZMod p, ((2 * k + 1 : ℕ) : ZMod p) * (-(x ^ 2))⁻¹) = 0 := by
    have h2 : (∑ x : ZMod p, (x ^ 2)⁻¹) = (∑ x : ZMod p, x ^ 2) :=
      Fintype.sum_equiv (Equiv.inv (ZMod p)) _ _ (fun x => (inv_pow x 2).symm)
    have h0 : (∑ x : ZMod p, x ^ 2) = 0 := by
      have hlt : 2 < Fintype.card (ZMod p) - 1 := by
        rw [ZMod.card p]
        omega
      exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 hlt
    have hneg : (∑ x : ZMod p, (-(x ^ 2))⁻¹) = -(∑ x : ZMod p, (x ^ 2)⁻¹) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact (neg_inv).symm
    calc (∑ x : ZMod p, ((2 * k + 1 : ℕ) : ZMod p) * (-(x ^ 2))⁻¹)
        = ((2 * k + 1 : ℕ) : ZMod p) * (∑ x : ZMod p, (-(x ^ 2))⁻¹) := by
          rw [Finset.mul_sum]
      _ = 0 := by rw [hneg, h2, h0, mul_neg, mul_zero, neg_zero]
  have hφ0 : (fun x : ZMod p => ((2 * k + 1 : ℕ) : ZMod p) * (-(x ^ 2))⁻¹) 0 = 0 := by
    simp
  have huniv := ZMod.sum_Ico_cast p
    (fun x : ZMod p => ((2 * k + 1 : ℕ) : ZMod p) * (-(x ^ 2))⁻¹) hφ0
  have hπH : ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
        (∑ j ∈ Finset.range (p - 1),
          ((2 * k + 1 : ℕ) : ZMod (p ^ 2)) *
            (((k * p + (1 + j) : ℕ) : ZMod (p ^ 2)) *
              ((k * p + (p - (1 + j)) : ℕ) : ZMod (p ^ 2)))⁻¹) = 0 := by
    rw [map_sum]
    have hsum : (∑ j ∈ Finset.range (p - 1),
          ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
            (((2 * k + 1 : ℕ) : ZMod (p ^ 2)) *
              (((k * p + (1 + j) : ℕ) : ZMod (p ^ 2)) *
                ((k * p + (p - (1 + j)) : ℕ) : ZMod (p ^ 2)))⁻¹))
        = ∑ j ∈ Finset.range (p - 1),
          ((2 * k + 1 : ℕ) : ZMod p) * (-((((1 + j : ℕ) : ZMod p) ^ 2)))⁻¹ :=
      Finset.sum_congr rfl (fun j hj => by
        simp only [Finset.mem_range] at hj
        exact hπh (1 + j) (Nat.le_add_right 1 j) (by omega))
    rw [hsum]
    have hico : (∑ r ∈ Finset.Ico 1 p,
          (fun x : ZMod p => ((2 * k + 1 : ℕ) : ZMod p) * (-(x ^ 2))⁻¹)
            (((r : ℕ)) : ZMod p))
        = ∑ j ∈ Finset.range (p - 1),
          ((2 * k + 1 : ℕ) : ZMod p) * (-((((1 + j : ℕ) : ZMod p) ^ 2)))⁻¹ := by
      rw [Finset.sum_Ico_eq_sum_range]
    rw [← hico, huniv]
    exact hfield
  obtain ⟨H', hH'⟩ := ZMod.eq_mul_p_of_castHom_eq_zero _ hπH
  have hpp : ((p : ℕ) : ZMod (p ^ 2)) * ((p : ℕ) : ZMod (p ^ 2)) = 0 := by
    have h2 : (((p ^ 2 : ℕ)) : ZMod (p ^ 2))
        = ((p : ℕ) : ZMod (p ^ 2)) * ((p : ℕ) : ZMod (p ^ 2)) := by
      push_cast
      ring
    rw [← h2, ZMod.natCast_self]
  have h2S0 : (2 : ZMod (p ^ 2)) * (Finset.Ico 1 p).sum
      (fun r => (((k * p + r : ℕ) : ZMod (p ^ 2))⁻¹)) = 0 := by
    rw [h2S, hH', ← mul_assoc, hpp, zero_mul]
  have hU2 : IsUnit (2 : ZMod (p ^ 2)) := by
    have hcop2 : Nat.Coprime 2 (p ^ 2) := by
      rw [Nat.coprime_pow_right_iff (by norm_num : 0 < 2)]
      apply Nat.Coprime.symm
      rw [hp.coprime_iff_not_dvd]
      intro hd
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      omega
    have h := ZMod.coe_unitOfCoprime 2 hcop2
    rw [Nat.cast_ofNat] at h
    exact ⟨ZMod.unitOfCoprime 2 hcop2, h⟩
  have hinv : (2 : ZMod (p ^ 2))⁻¹ * 2 = 1 := ZMod.inv_mul_of_unit _ hU2
  calc (Finset.Ico 1 p).sum
        (fun r => (((k * p + r : ℕ) : ZMod (p ^ 2))⁻¹))
      = (2 : ZMod (p ^ 2))⁻¹ * ((2 : ZMod (p ^ 2)) * (Finset.Ico 1 p).sum
        (fun r => (((k * p + r : ℕ) : ZMod (p ^ 2))⁻¹))) := by
          rw [← mul_assoc, hinv, one_mul]
    _ = 0 := by rw [h2S0, mul_zero]
