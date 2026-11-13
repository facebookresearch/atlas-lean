/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.CharP.Defs
import Mathlib.LinearAlgebra.LinearPMap

@[expose] public section

namespace MetaMathlibExt

private theorem hmoebius_sum (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.moebius_mul_coe_zeta
  have h2 := congrArg (fun f : ArithmeticFunction ℤ => f n) h
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h2
  exact h2

private theorem hcount_aux (ℓ m d : ℕ) (h : ℓ ≤ m) :
    ((Finset.Ioc ℓ m).filter (fun x => d ∣ x)).card = m / d - ℓ / d := by
  have h1 : (Finset.Ioc (0:ℕ) m).filter (fun x => d ∣ x) =
      (Finset.Ioc (0:ℕ) ℓ).filter (fun x => d ∣ x) ∪ (Finset.Ioc ℓ m).filter (fun x => d ∣ x) := by
    rw [← Finset.filter_union]
    congr 1
    exact (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le ℓ) h).symm
  have hdisj : Disjoint ((Finset.Ioc (0:ℕ) ℓ).filter (fun x => d ∣ x))
      ((Finset.Ioc ℓ m).filter (fun x => d ∣ x)) := by
    apply Finset.disjoint_filter_filter
    · exact Finset.disjoint_left.mpr (fun x hx1 hx2 => by
        simp only [Finset.mem_Ioc] at hx1 hx2
        omega)
  have hcard : ((Finset.Ioc (0:ℕ) m).filter (fun x => d ∣ x)).card =
      ((Finset.Ioc (0:ℕ) ℓ).filter (fun x => d ∣ x)).card +
      ((Finset.Ioc ℓ m).filter (fun x => d ∣ x)).card := by
    rw [h1, Finset.card_union_of_disjoint hdisj]
  have hm : ((Finset.Ioc (0:ℕ) m).filter (fun x => d ∣ x)).card = m / d :=
    Nat.Ioc_filter_dvd_card_eq_div m d
  have hℓ : ((Finset.Ioc (0:ℕ) ℓ).filter (fun x => d ∣ x)).card = ℓ / d :=
    Nat.Ioc_filter_dvd_card_eq_div ℓ d
  omega

private theorem hcard_nonempty_aux (ℓ m d : ℕ) :
    ((Finset.powerset (Finset.Ioc ℓ m)).filter
      (fun H => H.Nonempty ∧ d ∣ H.gcd id)).card =
    2 ^ ((Finset.Ioc ℓ m).filter (fun x => d ∣ x)).card - 1 := by
  have heq : ((Finset.powerset (Finset.Ioc ℓ m)).filter
      (fun H => H.Nonempty ∧ d ∣ H.gcd id)) =
      ((Finset.powerset ((Finset.Ioc ℓ m).filter (fun x => d ∣ x))).filter
        (fun H => H.Nonempty)) := by
    ext H
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powerset]
    constructor
    · rintro ⟨hsub, hne, hdvd⟩
      rw [Finset.dvd_gcd_iff] at hdvd
      simp only [id] at hdvd
      exact ⟨fun x hx => Finset.mem_filter.mpr ⟨hsub hx, hdvd x hx⟩, hne⟩
    · rintro ⟨hsub, hne⟩
      refine ⟨fun x hx => (Finset.mem_filter.mp (hsub hx)).1, hne, ?_⟩
      rw [Finset.dvd_gcd_iff]
      simp only [id]
      exact fun x hx => (Finset.mem_filter.mp (hsub hx)).2
  rw [heq]
  have h1 := Finset.card_filter_add_card_filter_not
    (s := Finset.powerset ((Finset.Ioc ℓ m).filter (fun x => d ∣ x)))
    (p := fun H => H.Nonempty)
  have hneg : ((Finset.powerset ((Finset.Ioc ℓ m).filter (fun x => d ∣ x))).filter
      (fun H => ¬H.Nonempty)).card = 1 := by
    have hempty : ((Finset.powerset ((Finset.Ioc ℓ m).filter (fun x => d ∣ x))).filter
        (fun H => ¬H.Nonempty)) = {∅} := by
      ext H
      rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hne⟩
        exact Finset.not_nonempty_iff_eq_empty.mp hne
      · rintro rfl
        exact ⟨Finset.empty_subset _, Finset.not_nonempty_empty⟩
    rw [hempty, Finset.card_singleton]
  rw [Finset.card_powerset] at h1
  omega

private theorem hcard_k_aux (ℓ m d k : ℕ) :
    ((Finset.powerset (Finset.Ioc ℓ m)).filter
      (fun H => H.card = k ∧ d ∣ H.gcd id)).card =
    (((Finset.Ioc ℓ m).filter (fun x => d ∣ x)).card.choose k) := by
  have heq : ((Finset.powerset (Finset.Ioc ℓ m)).filter
      (fun H => H.card = k ∧ d ∣ H.gcd id)) =
      Finset.powersetCard k ((Finset.Ioc ℓ m).filter (fun x => d ∣ x)) := by
    ext H
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hcard, hdvd⟩
      rw [Finset.dvd_gcd_iff] at hdvd
      simp only [id] at hdvd
      exact ⟨fun x hx => Finset.mem_filter.mpr ⟨hsub hx, hdvd x hx⟩, hcard⟩
    · rintro ⟨hsub, hcard⟩
      refine ⟨fun x hx => (Finset.mem_filter.mp (hsub hx)).1, hcard, ?_⟩
      rw [Finset.dvd_gcd_iff]
      simp only [id]
      exact fun x hx => (Finset.mem_filter.mp (hsub hx)).2
  rw [heq, Finset.card_powersetCard]

/-!
# Relatively prime subset counts
-/

/--
**Relatively prime subset counts.** Let $\ell < m$ and $k \ge 1$ be natural numbers, and let
$\mu$ be the Möbius function. The number of nonempty subsets of $\{\ell + 1, \dots, m\}$ whose
elements have greatest common divisor $1$ is
$$\sum_{d=1}^{m} \mu(d) \left(2^{\lfloor m/d \rfloor - \lfloor \ell/d \rfloor} - 1\right),$$
and the number of $k$-element subsets of $\{\ell + 1, \dots, m\}$ whose elements have greatest
common divisor $1$ is
$$\sum_{d=1}^{m} \mu(d) \binom{\lfloor m/d \rfloor - \lfloor \ell/d \rfloor}{k}.$$

Proves `Wanted` entry `mobius_formula_relatively_prime_subset_counts_interval`.

Source: M. Ayad, V. Coia, and O. Kihel, “The Number of Relatively Prime Subsets of a Finite Union of Sets of Consecutive Integers”, Journal of Integer Sequences 17 (2014), Article 14.3.7, Theorem 1, lines 138-151, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Kihel/kihel10.tex>.
-/
theorem mobius_formula_relatively_prime_subset_counts_interval
    (ℓ m k : ℕ) (h_lt : ℓ < m) (h_k : 1 ≤ k) :
    (((Finset.powerset (Finset.Ioc ℓ m)).filter
      (fun H => H.Nonempty ∧ Finset.gcd H id = 1)).card : ℤ) =
      ∑ d ∈ Finset.Icc 1 m,
        ArithmeticFunction.moebius d * ((2 : ℤ) ^ (m / d - ℓ / d) - 1) ∧
    (((Finset.powerset (Finset.Ioc ℓ m)).filter
      (fun H => H.card = k ∧ Finset.gcd H id = 1)).card : ℤ) =
      ∑ d ∈ Finset.Icc 1 m,
        ArithmeticFunction.moebius d * (Nat.choose (m / d - ℓ / d) k : ℤ) := by
  classical
  have hle : ℓ ≤ m := h_lt.le
  have hSpos : ∀ x ∈ Finset.Ioc ℓ m, 1 ≤ x := by
    intro x hx
    simp only [Finset.mem_Ioc] at hx
    omega
  have hgcd_ne : ∀ H ∈ Finset.powerset (Finset.Ioc ℓ m), H.Nonempty →
      H.gcd id ≠ 0 := by
    intro H hH hne
    rw [Finset.gcd_ne_zero_iff]
    obtain ⟨a, ha⟩ := hne
    refine ⟨a, ha, ?_⟩
    have hsub : H ⊆ Finset.Ioc ℓ m := Finset.mem_powerset.mp hH
    have hpos := hSpos a (hsub ha)
    have hne0 : a ≠ 0 := by omega
    exact hne0
  have hgcd_le : ∀ H ∈ Finset.powerset (Finset.Ioc ℓ m), H.Nonempty →
      H.gcd id ≤ m := by
    intro H hH hne
    obtain ⟨a, ha⟩ := hne
    have hsub : H ⊆ Finset.Ioc ℓ m := Finset.mem_powerset.mp hH
    have haS := hsub ha
    simp only [Finset.mem_Ioc] at haS
    have hdvd : H.gcd id ∣ a := Finset.gcd_dvd ha
    have ha_pos : 0 < a := by omega
    calc H.gcd id ≤ a := Nat.le_of_dvd ha_pos hdvd
      _ ≤ m := haS.2
  constructor
  · -- First formula: nonempty relatively prime subsets.
    have hLHS : (((Finset.powerset (Finset.Ioc ℓ m)).filter
        (fun H => H.Nonempty ∧ Finset.gcd H id = 1)).card : ℤ) =
        ∑ H ∈ Finset.powerset (Finset.Ioc ℓ m),
          (if H.Nonempty ∧ Finset.gcd H id = 1 then (1:ℤ) else 0) := by
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro H _
      simp
    rw [hLHS]
    have hHrw : ∀ H ∈ Finset.powerset (Finset.Ioc ℓ m),
        (if H.Nonempty ∧ Finset.gcd H id = 1 then (1:ℤ) else 0) =
        ∑ d ∈ Finset.Icc 1 m,
          ArithmeticFunction.moebius d *
            (if H.Nonempty ∧ d ∣ H.gcd id then (1:ℤ) else 0) := by
      intro H hH
      by_cases hne : H.Nonempty
      · have hgne : H.gcd id ≠ 0 := hgcd_ne H hH hne
        have hpos : 0 < H.gcd id := Nat.pos_of_ne_zero hgne
        have hle2 : H.gcd id ≤ m := hgcd_le H hH hne
        have hbase := hmoebius_sum (H.gcd id)
        have hLHS2 : (if H.Nonempty ∧ Finset.gcd H id = 1 then (1:ℤ) else 0) =
            ∑ d ∈ (H.gcd id).divisors, ArithmeticFunction.moebius d := by
          rw [hbase]
          by_cases hg : Finset.gcd H id = 1
          · simp [hne, hg]
          · simp [hg]
        rw [hLHS2]
        have hsub : (H.gcd id).divisors ⊆ Finset.Icc 1 m := by
          intro d hd
          rw [Nat.mem_divisors] at hd
          simp only [Finset.mem_Icc]
          exact ⟨Nat.pos_of_dvd_of_pos hd.1 hpos, le_trans (Nat.le_of_dvd hpos hd.1) hle2⟩
        have heq_on : ∀ d ∈ (H.gcd id).divisors,
            ArithmeticFunction.moebius d =
            ArithmeticFunction.moebius d *
              (if H.Nonempty ∧ d ∣ H.gcd id then (1:ℤ) else 0) := by
          intro d hd
          have hdvd : d ∣ H.gcd id := (Nat.mem_divisors.mp hd).1
          simp [hne, hdvd]
        have hvan : ∀ d ∈ Finset.Icc 1 m, d ∉ (H.gcd id).divisors →
            ArithmeticFunction.moebius d *
              (if H.Nonempty ∧ d ∣ H.gcd id then (1:ℤ) else 0) = 0 := by
          intro d _ hdNot
          have hnot : ¬ (H.Nonempty ∧ d ∣ H.gcd id) := by
            intro hcon
            apply hdNot
            rw [Nat.mem_divisors]
            exact ⟨hcon.2, hgne⟩
          simp [hnot]
        have hstep : (∑ d ∈ (H.gcd id).divisors, ArithmeticFunction.moebius d) =
            ∑ d ∈ (H.gcd id).divisors, (ArithmeticFunction.moebius d *
              (if H.Nonempty ∧ d ∣ H.gcd id then (1:ℤ) else 0)) :=
          Finset.sum_congr rfl heq_on
        rw [hstep]
        exact Finset.sum_subset hsub hvan
      · have hLHS0 : (if H.Nonempty ∧ Finset.gcd H id = 1 then (1:ℤ) else 0) = 0 := by
          simp [hne]
        rw [hLHS0]
        exact Eq.symm (Finset.sum_eq_zero (fun d _ => by
          have hnot : ¬ (H.Nonempty ∧ d ∣ H.gcd id) := fun hcon => hne hcon.1
          simp [hnot]))
    rw [Finset.sum_congr rfl hHrw]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    have hcard : ((((Finset.powerset (Finset.Ioc ℓ m)).filter
            (fun H => H.Nonempty ∧ d ∣ H.gcd id)).card : ℕ) : ℤ) =
        ∑ H ∈ Finset.powerset (Finset.Ioc ℓ m),
          (if H.Nonempty ∧ d ∣ H.gcd id then (1:ℤ) else 0) := by
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro H _
      simp
    have hfactor : (∑ H ∈ Finset.powerset (Finset.Ioc ℓ m),
          ArithmeticFunction.moebius d *
            (if H.Nonempty ∧ d ∣ H.gcd id then (1:ℤ) else 0)) =
        ArithmeticFunction.moebius d *
          ((((Finset.powerset (Finset.Ioc ℓ m)).filter
            (fun H => H.Nonempty ∧ d ∣ H.gcd id)).card : ℕ) : ℤ) := by
      rw [hcard, ← Finset.mul_sum]
    rw [hfactor, hcard_nonempty_aux, hcount_aux _ _ _ hle]
    have h1le : 1 ≤ 2 ^ (m / d - ℓ / d) := Nat.one_le_two_pow
    rw [Nat.cast_sub h1le]
    push_cast
    ring
  · -- Second formula: fixed-cardinality relatively prime subsets.
    have hLHS : (((Finset.powerset (Finset.Ioc ℓ m)).filter
        (fun H => H.card = k ∧ Finset.gcd H id = 1)).card : ℤ) =
        ∑ H ∈ Finset.powerset (Finset.Ioc ℓ m),
          (if H.card = k ∧ Finset.gcd H id = 1 then (1:ℤ) else 0) := by
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro H _
      simp
    rw [hLHS]
    have hHrw : ∀ H ∈ Finset.powerset (Finset.Ioc ℓ m),
        (if H.card = k ∧ Finset.gcd H id = 1 then (1:ℤ) else 0) =
        ∑ d ∈ Finset.Icc 1 m,
          ArithmeticFunction.moebius d *
            (if H.card = k ∧ d ∣ H.gcd id then (1:ℤ) else 0) := by
      intro H hH
      by_cases hck : H.card = k
      · have hne : H.Nonempty := by
          rw [← Finset.card_pos]
          omega
        have hgne : H.gcd id ≠ 0 := hgcd_ne H hH hne
        have hpos : 0 < H.gcd id := Nat.pos_of_ne_zero hgne
        have hle2 : H.gcd id ≤ m := hgcd_le H hH hne
        have hbase := hmoebius_sum (H.gcd id)
        have hLHS2 : (if H.card = k ∧ Finset.gcd H id = 1 then (1:ℤ) else 0) =
            ∑ d ∈ (H.gcd id).divisors, ArithmeticFunction.moebius d := by
          rw [hbase]
          by_cases hg : Finset.gcd H id = 1
          · simp [hck, hg]
          · simp [hg]
        rw [hLHS2]
        have hsub : (H.gcd id).divisors ⊆ Finset.Icc 1 m := by
          intro d hd
          rw [Nat.mem_divisors] at hd
          simp only [Finset.mem_Icc]
          exact ⟨Nat.pos_of_dvd_of_pos hd.1 hpos, le_trans (Nat.le_of_dvd hpos hd.1) hle2⟩
        have heq_on : ∀ d ∈ (H.gcd id).divisors,
            ArithmeticFunction.moebius d =
            ArithmeticFunction.moebius d *
              (if H.card = k ∧ d ∣ H.gcd id then (1:ℤ) else 0) := by
          intro d hd
          have hdvd : d ∣ H.gcd id := (Nat.mem_divisors.mp hd).1
          simp [hck, hdvd]
        have hvan : ∀ d ∈ Finset.Icc 1 m, d ∉ (H.gcd id).divisors →
            ArithmeticFunction.moebius d *
              (if H.card = k ∧ d ∣ H.gcd id then (1:ℤ) else 0) = 0 := by
          intro d _ hdNot
          have hnot : ¬ (H.card = k ∧ d ∣ H.gcd id) := by
            intro hcon
            apply hdNot
            rw [Nat.mem_divisors]
            exact ⟨hcon.2, hgne⟩
          simp [hnot]
        have hstep : (∑ d ∈ (H.gcd id).divisors, ArithmeticFunction.moebius d) =
            ∑ d ∈ (H.gcd id).divisors, (ArithmeticFunction.moebius d *
              (if H.card = k ∧ d ∣ H.gcd id then (1:ℤ) else 0)) :=
          Finset.sum_congr rfl heq_on
        rw [hstep]
        exact Finset.sum_subset hsub hvan
      · have hLHS0 : (if H.card = k ∧ Finset.gcd H id = 1 then (1:ℤ) else 0) = 0 := by
          simp [hck]
        rw [hLHS0]
        exact Eq.symm (Finset.sum_eq_zero (fun d _ => by
          have hnot : ¬ (H.card = k ∧ d ∣ H.gcd id) := fun hcon => hck hcon.1
          simp [hnot]))
    rw [Finset.sum_congr rfl hHrw]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    have hcard : ((((Finset.powerset (Finset.Ioc ℓ m)).filter
            (fun H => H.card = k ∧ d ∣ H.gcd id)).card : ℕ) : ℤ) =
        ∑ H ∈ Finset.powerset (Finset.Ioc ℓ m),
          (if H.card = k ∧ d ∣ H.gcd id then (1:ℤ) else 0) := by
      rw [Finset.card_filter, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro H _
      simp
    have hfactor : (∑ H ∈ Finset.powerset (Finset.Ioc ℓ m),
          ArithmeticFunction.moebius d *
            (if H.card = k ∧ d ∣ H.gcd id then (1:ℤ) else 0)) =
        ArithmeticFunction.moebius d *
          ((((Finset.powerset (Finset.Ioc ℓ m)).filter
            (fun H => H.card = k ∧ d ∣ H.gcd id)).card : ℕ) : ℤ) := by
      rw [hcard, ← Finset.mul_sum]
    rw [hfactor, hcard_k_aux, hcount_aux _ _ _ hle]

end MetaMathlibExt
