/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.Sylow

/-!
# A counting condition forcing prime-power element orders (Kourovka Notebook Problem 18.112)

Kourovka Notebook, Archive of Solved Problems, Problem 18.112 (W. J. Shi): is it true that the
orders of all elements of a finite group `G` are powers of primes if, for every divisor `d > 1` of
`|G|` and for every subgroup `H` of `G` of order coprime to `d`, the order `|H|` divides the number
of elements of `G` of order `d`? (The converse is true (Shi).)

We prove that the stated divisibility condition forces every nonidentity element to have
prime-power order.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.112 (W. J.
Shi). UnsolvedMath record UM-00701540 (`KOU-18.112`), dataset ulamai/UnsolvedMath v1.8.0.

Element orders are `orderOf`; the identity has order `1 = p⁰`, so the conclusion is stated for
non-identity elements (`IsPrimePow` excludes `1`).
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ElementOrderCountPrimePowerKourovka18Problem112Wanted

/-- **Shi's question on element-order counts (Kourovka 18.112).** The proposition that if a
finite group $G$ has the property that, for every divisor $d > 1$ of $|G|$ and every subgroup $H$
of $G$ whose order is coprime to $d$, $|H|$ divides the number of elements of $G$ of order $d$,
then every non-identity element of $G$ has prime-power order. -/
def elementOrderCountPrimePowerOrders : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ d : ℕ, 1 < d → d ∣ Nat.card G → ∀ H : Subgroup G, Nat.Coprime (Nat.card H) d →
      Nat.card H ∣ Nat.card {g : G // orderOf g = d}) →
    ∀ g : G, g ≠ 1 → IsPrimePow (orderOf g)

open MulAction

variable {G : Type*} [Group G]

-- Burnside's lemma on ordered tuples, with fixed tuples counted coordinate by coordinate.
private theorem dvd_sum_fixedBy_pow [Fintype G] (X : Type*) [MulAction G X] [Finite X] (n : ℕ) :
    Nat.card G ∣ ∑ g : G, Nat.card (fixedBy X g) ^ n := by
  classical
  let Y := Fin n → X
  let := Fintype.ofFinite (Quotient (orbitRel G Y))
  let (g : G) := Fintype.ofFinite (fixedBy Y g)
  have h (g : G) : Fintype.card (fixedBy Y g) = Nat.card (fixedBy X g) ^ n := by
    let e : fixedBy Y g ≃ (Fin n → fixedBy X g) :=
      (Equiv.subtypeEquivRight fun _ => funext_iff).trans
        (Equiv.subtypePiEquivPi (p := fun (_ : Fin n) (x : X) => g • x = x))
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_fun, Nat.card_fin]
  rw [← funext h, sum_card_fixedBy_eq_card_orbits_mul_card_group, Nat.card_eq_fintype_card]
  exact dvd_mul_left _ _

-- The number of Sylow cosets fixed by a p-element is prime to p.
private theorem coprime_fixed_cosets [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (g : G) (hg : ∃ k : ℕ, orderOf g = p ^ k) :
    p.Coprime (Nat.card (fixedBy (G ⧸ P.toSubgroup) g)) := by
  let X := G ⧸ P.toSubgroup
  obtain ⟨k, hk⟩ := hg
  have hcyc : IsPGroup p (Subgroup.zpowers g) := IsPGroup.of_card ((Nat.card_zpowers g).trans hk)
  have hfix : fixedPoints (Subgroup.zpowers g) X = fixedBy X g := by
    ext x
    constructor
    · intro hx
      exact hx ⟨g, Subgroup.mem_zpowers g⟩
    · intro hx a
      obtain ⟨j, hj⟩ := a.property
      change (a : G) • x = x
      rw [← hj]
      exact mem_fixedBy_zpow hx j
  have hc := hcyc.card_modEq_card_fixedPoints X
  rw [hfix] at hc
  refine hp.out.coprime_iff_not_dvd.mpr fun hd => P.not_dvd_index ?_
  exact Nat.modEq_zero_iff_dvd.mp (hc.trans hd.modEq_zero_nat)

private theorem orderOf_eq_pow_of_fixed_coset {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (g : G) (x : G ⧸ P.toSubgroup) (hx : x ∈ fixedBy (G ⧸ P.toSubgroup) g) :
    ∃ k : ℕ, orderOf g = p ^ k := by
  induction x using QuotientGroup.induction_on with
  | _ a =>
    change (↑(g * a) : G ⧸ P.toSubgroup) = ↑a at hx
    have ha : (MulAut.conj a⁻¹) g ∈ P.toSubgroup := by
      simpa [MulAut.conj_apply, mul_assoc] using QuotientGroup.eq.mp hx.symm
    simpa only [Subgroup.orderOf_mk, MulEquiv.orderOf_eq] using
      P.isPGroup.exists_orderOf_eq_pow ⟨(MulAut.conj a⁻¹) g, ha⟩

-- Taking a totient power turns the fixed-point count into the indicator of p-elements
-- modulo each power of p dividing the group order.
open Classical in
private theorem dvd_card_p_elements [Fintype G] {p k : ℕ} [hp : Fact p.Prime]
    (hd : p ^ k ∣ Nat.card G) :
    p ^ k ∣ (Finset.univ.filter fun g : G => ∃ i : ℕ, orderOf g = p ^ i).card := by
  classical
  let P : Sylow p G := Classical.arbitrary _
  let X := G ⧸ P.toSubgroup
  let n := (p ^ k).totient
  have hn : n ≠ 0 := (Nat.totient_pos.mpr (pow_pos hp.out.pos k)).ne'
  have h (g : G) : Nat.card (fixedBy X g) ^ n ≡
      (if ∃ i : ℕ, orderOf g = p ^ i then 1 else 0) [MOD p ^ k] := by
    split_ifs with hg
    · exact Nat.ModEq.pow_totient ((coprime_fixed_cosets P g hg).symm.pow_right _)
    · have : IsEmpty (fixedBy X g) := ⟨fun x => hg (orderOf_eq_pow_of_fixed_coset P g x x.2)⟩
      simp [hn, Nat.ModEq.refl]
  have hs := Nat.ModEq.sum (s := Finset.univ) (fun g _ => h g)
  rw [Finset.sum_boole] at hs
  exact Nat.modEq_zero_iff_dvd.mp
    (hs.symm.trans (hd.trans (dvd_sum_fixedBy_pow X n)).modEq_zero_nat)

private theorem one_or_isPrimePow_of_pow {p d : ℕ} (hp : p.Prime) (hd : ∃ i : ℕ, d = p ^ i) :
    d = 1 ∨ IsPrimePow d := by
  obtain ⟨i, rfl⟩ := hd
  cases i with
  | zero => simp
  | succ i => exact Or.inr (hp.isPrimePow.pow (Nat.succ_ne_zero i))

private theorem other_prime_powers {p d : ℕ} (hp : p.Prime) :
    ((d = 1 ∨ IsPrimePow d) ∧ ¬ ∃ i : ℕ, d = p ^ i) ↔ IsPrimePow d ∧ p.Coprime d := by
  constructor
  · rintro ⟨rfl | hd, h⟩
    · exact (h ⟨0, (pow_zero p).symm⟩).elim
    · obtain ⟨q, i, hq, _, rfl⟩ := (isPrimePow_nat_iff _).mp hd
      have hne : p ≠ q := fun e => h ⟨i, by rw [e]⟩
      exact ⟨hd, ((Nat.coprime_primes hp hq).mpr hne).pow_right i⟩
  · rintro ⟨hd, hcop⟩
    refine ⟨Or.inr hd, ?_⟩
    rintro ⟨i, rfl⟩
    cases i with
    | zero => simpa using hd.one_lt
    | succ i => exact hp.coprime_iff_not_dvd.mp hcop (dvd_pow_self _ (Nat.succ_ne_zero _))

/--
**Counting elements of each order forces prime-power orders.** Let $G$ be a finite group such
that for every divisor $d > 1$ of $|G|$ and every subgroup $H$ of $G$ whose order is coprime to
$d$, the order $|H|$ divides the number of elements of $G$ of order $d$. Then every non-identity
element of $G$ has prime-power order.

Buturlakin, Shen and Shi proved this in 2017, answering Kourovka Problem 18.112 (W. J. Shi); the
Kourovka Archive answers 18.112 "Yes, it is true".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.112
(W. J. Shi); resolution: A. A. Buturlakin, R. Shen and W. Shi, Siberian Math. J. 58 (2017), 405-407,
Kourovka Archive, Problem 18.112 (Yes, it is true).
-/
public theorem elementOrderCountPrimePowerOrders_holds : elementOrderCountPrimePowerOrders := by
  classical
  intro G _ _ hcount
  let := Fintype.ofFinite G
  let good := Finset.univ.filter fun g : G => orderOf g = 1 ∨ IsPrimePow (orderOf g)
  have hpos : 0 < good.card := Finset.card_pos.mpr ⟨1, by simp [good]⟩
  have hdvd : Nat.card G ∣ good.card := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p k hp hk
    have : Fact p.Prime := ⟨hp⟩
    let primary := Finset.univ.filter fun g : G => ∃ i : ℕ, orderOf g = p ^ i
    have hsub : primary ⊆ good := by
      intro g hg
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, one_or_isPrimePow_of_pow hp (Finset.mem_filter.mp hg).2⟩
    rw [← Finset.card_sdiff_add_card_eq_card hsub]
    refine dvd_add ?_ (dvd_card_p_elements hk)
    -- Group the remaining elements by their exact order to apply the hypothesis.
    let orders := (Nat.card G).divisors.filter fun d => IsPrimePow d ∧ p.Coprime d
    have hrest : good \ primary = Finset.univ.filter (fun g : G => orderOf g ∈ orders) := by
      ext g
      have hg : orderOf g ∈ (Nat.card G).divisors :=
        Nat.mem_divisors.mpr ⟨orderOf_dvd_natCard g, Nat.card_pos.ne'⟩
      simp only [good, primary, orders, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, hg,
        true_and, other_prime_powers hp]
    rw [hrest, ← Finset.sum_card_fiberwise_eq_card_filter]
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p hk
    apply Finset.dvd_sum
    intro d hd
    obtain ⟨hdvd, hprime, hcop⟩ := Finset.mem_filter.mp hd
    have h := hcount d hprime.one_lt (Nat.mem_divisors.mp hdvd).1 H
      (hH ▸ hcop.pow_left k)
    simpa only [hH, Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  have hall : good = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    (by simpa [Nat.card_eq_fintype_card] using Nat.le_of_dvd hpos hdvd)
  intro g hg
  have h : g ∈ good := hall ▸ Finset.mem_univ g
  exact (Finset.mem_filter.mp h).2.resolve_left (fun he => hg (orderOf_eq_one_iff.mp he))

end MathlibExt.GroupTheory.ElementOrderCountPrimePowerKourovka18Problem112Wanted
