/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Counting integers with a given least prime factor in an interval

The count of integers in an interval that are divisible by a prime `p` and by no smaller
prime is close to the heuristic main term: `card_leastPrimeFactor_interval_error` bounds the
error by `2 ^ π (p - 1)` via inclusion-exclusion over the primes below `p`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 6 (`lem:Dp`).
-/

namespace MetaMathlibExt

open Finset

/-- Multiples of `d` in `(a, a + t]` are counted by the difference of the quotients. -/
private theorem card_Icc_filter_dvd (a t d : ℕ) :
    ((Icc (a + 1) (a + t)).filter (fun m => d ∣ m)).card = (a + t) / d - a / d := by
  have hIcc : Icc (a + 1) (a + t) = Ioc a (a + t) := by
    ext x
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hIcc]
  have hunion : Ioc (0 : ℕ) (a + t) = Ioc 0 a ∪ Ioc a (a + t) := by
    ext x
    simp only [mem_Ioc, mem_union]
    omega
  have hdisj : Disjoint (Ioc (0 : ℕ) a) (Ioc a (a + t)) := by
    rw [disjoint_left]
    intro x hx1 hx2
    simp only [mem_Ioc] at hx1 hx2
    omega
  have h1 : ((Ioc 0 (a + t)).filter (fun m => d ∣ m)).card = (a + t) / d :=
    Nat.Ioc_filter_dvd_card_eq_div (a + t) d
  have h2 : ((Ioc 0 a).filter (fun m => d ∣ m)).card = a / d :=
    Nat.Ioc_filter_dvd_card_eq_div a d
  have hdisj' : Disjoint ((Ioc 0 a).filter (fun m => d ∣ m))
      ((Ioc a (a + t)).filter (fun m => d ∣ m)) :=
    Disjoint.mono (filter_subset _ _) (filter_subset _ _) hdisj
  have hfu : (Ioc (0 : ℕ) (a + t)).filter (fun m => d ∣ m) =
      (Ioc 0 a).filter (fun m => d ∣ m) ∪ (Ioc a (a + t)).filter (fun m => d ∣ m) := by
    rw [hunion, filter_union]
  have hcard := congrArg card hfu
  rw [card_union_of_disjoint hdisj', h1, h2] at hcard
  omega

/-- The count of multiples of a positive `d` in `(a, a + t]` is within `1` of `t / d`. -/
private theorem abs_card_Icc_filter_dvd_sub (a t d : ℕ) (hd : 0 < d) :
    |((((Icc (a + 1) (a + t)).filter (fun m => d ∣ m)).card : ℕ) : ℝ) - t / (d : ℝ)| ≤ 1 := by
  rw [card_Icc_filter_dvd]
  have hle : a / d ≤ (a + t) / d := Nat.div_le_div_right (Nat.le_add_right a t)
  rw [Nat.cast_sub hle]
  have h1 : (d : ℝ) * (a / d : ℕ) + (a % d : ℕ) = (a : ℝ) := by
    exact_mod_cast Nat.div_add_mod a d
  have h2 : (d : ℝ) * ((a + t) / d : ℕ) + ((a + t) % d : ℕ) = (a : ℝ) + (t : ℝ) := by
    exact_mod_cast Nat.div_add_mod (a + t) d
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hr1 : ((a % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt _ hd
  have hr2 : (((a + t) % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt _ hd
  have hdeq : ((a + t) / d : ℕ) - (a / d : ℕ) - (t : ℝ) / (d : ℝ)
      = (((a % d : ℕ) : ℝ) - ((a + t) % d : ℕ)) / (d : ℝ) := by
    field_simp
    linear_combination h2 - h1
  rw [hdeq, abs_div, abs_of_pos hdpos, div_le_one hdpos, abs_le]
  constructor <;> linarith

/-- Inclusion-exclusion over `Q`: the sieve count is within `2 ^ Q.card` of the main term. -/
private theorem card_filter_not_dvd_sub (a t : ℕ) (Q : Finset ℕ) :
    (∀ r ∈ Q, r.Prime) →
    ∀ (d : ℕ), 0 < d → (∀ r ∈ Q, Nat.Coprime d r) →
    |((((Icc (a + 1) (a + t)).filter
        (fun m => d ∣ m ∧ ∀ r ∈ Q, ¬ r ∣ m)).card : ℕ) : ℝ) -
      t * (1 / (d : ℝ)) * ∏ r ∈ Q, (1 - 1 / (r : ℝ))| ≤ 2 ^ Q.card := by
  induction Q using Finset.induction with
  | empty =>
    intro hQ d hd hcop
    have hfilter : (Icc (a + 1) (a + t)).filter
          (fun m => d ∣ m ∧ ∀ r ∈ (∅ : Finset ℕ), ¬ r ∣ m)
        = (Icc (a + 1) (a + t)).filter (fun m => d ∣ m) := by
      apply filter_congr
      intro m _
      exact ⟨fun h => h.1, fun h => ⟨h, fun r hr => absurd hr (notMem_empty r)⟩⟩
    rw [hfilter, prod_empty, mul_one, card_empty, pow_zero, mul_one_div]
    exact abs_card_Icc_filter_dvd_sub a t d hd
  | insert q s hnot ih =>
    intro hQ d hd hcop
    have hq : q.Prime := hQ q (mem_insert_self q s)
    have hQ' : ∀ r ∈ s, r.Prime := fun r hr => hQ r (mem_insert_of_mem hr)
    have hcop' : ∀ r ∈ s, Nat.Coprime d r := fun r hr => hcop r (mem_insert_of_mem hr)
    have hcopd : Nat.Coprime d q := hcop q (mem_insert_self q s)
    have hqpos : 0 < q := hq.pos
    have hdq : 0 < d * q := Nat.mul_pos hd hqpos
    have hcopdq : ∀ r ∈ s, Nat.Coprime (d * q) r := by
      intro r hr
      rw [Nat.coprime_mul_iff_left]
      refine ⟨hcop' r hr, ?_⟩
      exact (Nat.coprime_primes hq (hQ' r hr)).mpr (fun heq => hnot (heq ▸ hr))
    have ih1 := ih hQ' d hd hcop'
    have ih2 := ih hQ' (d * q) hdq hcopdq
    have hforall : ∀ m : ℕ, (∀ r ∈ insert q s, ¬ r ∣ m) ↔ (∀ r ∈ s, ¬ r ∣ m) ∧ ¬ q ∣ m := by
      intro m
      constructor
      · intro h
        exact ⟨fun r hr => h r (mem_insert_of_mem hr), h q (mem_insert_self q s)⟩
      · intro h r hr
        rw [mem_insert] at hr
        rcases hr with rfl | hmem
        · exact h.2
        · exact h.1 r hmem
    have hdvd : ∀ m : ℕ, (d ∣ m ∧ q ∣ m) ↔ d * q ∣ m := by
      intro m
      constructor
      · intro h
        exact hcopd.mul_dvd_of_dvd_of_dvd h.1 h.2
      · intro h
        exact ⟨(dvd_mul_right d q).trans h, (dvd_mul_left q d).trans h⟩
    have hA : (Icc (a + 1) (a + t)).filter (fun m => d ∣ m ∧ ∀ r ∈ s, ¬ r ∣ m) =
        (Icc (a + 1) (a + t)).filter (fun m => d ∣ m ∧ ∀ r ∈ insert q s, ¬ r ∣ m) ∪
        (Icc (a + 1) (a + t)).filter (fun m => d * q ∣ m ∧ ∀ r ∈ s, ¬ r ∣ m) := by
      ext m
      simp only [mem_filter, mem_union, hforall]
      constructor
      · rintro ⟨hb, hdm, hs⟩
        by_cases hqm : q ∣ m
        · exact Or.inr ⟨hb, (hdvd m).mp ⟨hdm, hqm⟩, hs⟩
        · exact Or.inl ⟨hb, hdm, hs, hqm⟩
      · rintro (⟨hb, hdm, hs, -⟩ | ⟨hb, hdmq, hs⟩)
        · exact ⟨hb, hdm, hs⟩
        · exact ⟨hb, ((hdvd m).mpr hdmq).1, hs⟩
    have hdisj : Disjoint
        ((Icc (a + 1) (a + t)).filter (fun m => d ∣ m ∧ ∀ r ∈ insert q s, ¬ r ∣ m))
        ((Icc (a + 1) (a + t)).filter (fun m => d * q ∣ m ∧ ∀ r ∈ s, ¬ r ∣ m)) := by
      rw [disjoint_left]
      intro m hmS hmB
      rw [mem_filter] at hmS hmB
      obtain ⟨-, -, hS⟩ := hmS
      obtain ⟨-, hmqB, -⟩ := hmB
      rw [hforall m] at hS
      exact hS.2 ((dvd_mul_left q d).trans hmqB)
    have hcardS : ((((Icc (a + 1) (a + t)).filter
            (fun m => d ∣ m ∧ ∀ r ∈ insert q s, ¬ r ∣ m)).card : ℕ) : ℝ)
        = ((((Icc (a + 1) (a + t)).filter
            (fun m => d ∣ m ∧ ∀ r ∈ s, ¬ r ∣ m)).card : ℕ) : ℝ)
        - ((((Icc (a + 1) (a + t)).filter
            (fun m => d * q ∣ m ∧ ∀ r ∈ s, ¬ r ∣ m)).card : ℕ) : ℝ) := by
      have h := congrArg card hA
      rw [card_union_of_disjoint hdisj] at h
      have h' := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast at h'
      linarith
    have hM : (t : ℝ) * (1 / (d : ℝ)) * ∏ r ∈ insert q s, (1 - 1 / (r : ℝ))
        = (t : ℝ) * (1 / (d : ℝ)) * ∏ r ∈ s, (1 - 1 / (r : ℝ))
          - (t : ℝ) * (1 / ((d * q : ℕ) : ℝ)) * ∏ r ∈ s, (1 - 1 / (r : ℝ)) := by
      rw [prod_insert hnot]
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
      have hdq0 : (d : ℝ) * q ≠ 0 := mul_ne_zero hd0 hq0
      push_cast
      field_simp
    have htri : ∀ X Y : ℝ, |X - Y| ≤ |X| + |Y| := by
      intro X Y
      simpa [sub_eq_add_neg] using abs_add_le X (-Y)
    have heq : ((((Icc (a + 1) (a + t)).filter
              (fun m => d ∣ m ∧ ∀ r ∈ insert q s, ¬ r ∣ m)).card : ℕ) : ℝ)
          - (t : ℝ) * (1 / (d : ℝ)) * ∏ r ∈ insert q s, (1 - 1 / (r : ℝ))
        = (((((Icc (a + 1) (a + t)).filter
              (fun m => d ∣ m ∧ ∀ r ∈ s, ¬ r ∣ m)).card : ℕ) : ℝ)
          - (t : ℝ) * (1 / (d : ℝ)) * ∏ r ∈ s, (1 - 1 / (r : ℝ)))
        - (((((Icc (a + 1) (a + t)).filter
              (fun m => d * q ∣ m ∧ ∀ r ∈ s, ¬ r ∣ m)).card : ℕ) : ℝ)
          - (t : ℝ) * (1 / ((d * q : ℕ) : ℝ)) * ∏ r ∈ s, (1 - 1 / (r : ℝ))) := by
      linarith [hcardS, hM]
    rw [card_insert_of_notMem hnot, pow_succ, heq]
    refine (htri _ _).trans ?_
    have h2 : (2 : ℝ) ^ s.card * 2 = 2 ^ s.card + 2 ^ s.card := by ring
    rw [h2]
    exact add_le_add ih1 ih2

/-- **Counting integers with a given least prime factor in an interval.** Let $a$ and $t$ be
positive integers and let $p$ be a prime. Let $N$ be the number of integers $m$ with
$a + 1 \le m \le a + t$ that are divisible by $p$ and by no prime $q < p$. Then

$$\left| N - \frac{t}{p} \prod_{q < p,\ q \text{ prime}} \left(1 - \frac{1}{q}\right) \right|
\le 2^{\pi(p-1)}$$

where $\pi$ is the prime-counting function.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 6 (`lem:Dp`). -/
public theorem card_leastPrimeFactor_interval_error {a t p : ℕ} (ha : 0 < a)
    (ht : 0 < t) (hp : p.Prime) :
    |((((Finset.Icc (a + 1) (a + t)).filter
          (fun m => p ∣ m ∧ ∀ q < p, q.Prime → ¬ q ∣ m)).card : ℕ) : ℝ) -
        t * (1 / (p : ℝ)) * ∏ q ∈ (Finset.range p).filter Nat.Prime, (1 - 1 / (q : ℝ))| ≤
      2 ^ Nat.primeCounting (p - 1)
    := by
  have _ := ha
  have _ := ht
  have hp2 : 2 ≤ p := hp.two_le
  have hQ' : ∀ r ∈ (Finset.range p).filter Nat.Prime, r.Prime :=
    fun r hr => (Finset.mem_filter.mp hr).2
  have hcop' : ∀ r ∈ (Finset.range p).filter Nat.Prime, Nat.Coprime p r := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hlt : r < p := Finset.mem_range.mp hr'.1
    exact (Nat.coprime_primes hp hr'.2).mpr (by omega)
  have hmain := card_filter_not_dvd_sub a t ((Finset.range p).filter Nat.Prime) hQ' p hp.pos hcop'
  have hfilter : (Finset.Icc (a + 1) (a + t)).filter
        (fun m => p ∣ m ∧ ∀ r ∈ (Finset.range p).filter Nat.Prime, ¬ r ∣ m)
      = (Finset.Icc (a + 1) (a + t)).filter
        (fun m => p ∣ m ∧ ∀ q < p, q.Prime → ¬ q ∣ m) := by
    apply Finset.filter_congr
    intro m _
    constructor
    · intro h
      refine ⟨h.1, fun q hqp hqprime => h.2 q ?_⟩
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hqp, hqprime⟩
    · intro h
      refine ⟨h.1, fun r hr => ?_⟩
      rw [Finset.mem_filter, Finset.mem_range] at hr
      exact h.2 r hr.1 hr.2
  have hcardQ : ((Finset.range p).filter Nat.Prime).card = Nat.primeCounting (p - 1) := by
    have hp1 : p - 1 + 1 = p := by omega
    calc ((Finset.range p).filter Nat.Prime).card
        = (Nat.primesLE (p - 1)).card := by unfold Nat.primesLE Nat.primesBelow; rw [hp1]
      _ = Nat.primeCounting (p - 1) := Nat.primesLE_card_eq_primeCounting (p - 1)
  rw [hfilter, hcardQ] at hmain
  exact hmain

end MetaMathlibExt
