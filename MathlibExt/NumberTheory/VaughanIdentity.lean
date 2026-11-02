/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Tactic.LinearCombination

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

private lemma log_eq_sum_Lambda {R : Type*} [CommRing R]
    (μ Λ : ArithmeticFunction R) (logW : ℕ → R)
    (hLambda : ∀ m, Λ m =
      ∑ d ∈ (Finset.range (m + 1)).filter (fun d => d ∣ m), μ d * logW (m / d))
    (hMu : ∀ m, ∑ d ∈ (Finset.range (m + 1)).filter (fun d => d ∣ m), μ d =
      if m = 1 then 1 else 0)
    (m : ℕ) (hm : 1 ≤ m) :
    logW m = ∑ c ∈ (Finset.range (m + 1)).filter (fun c => c ∣ m), Λ c := by
  have hm0 : m ≠ 0 := by omega
  have step1 : (∑ c ∈ (Finset.range (m + 1)).filter (fun c => c ∣ m), Λ c)
      = ∑ c ∈ (Finset.range (m + 1)).filter (fun c => c ∣ m),
        ∑ d ∈ (Finset.range (c + 1)).filter (fun d => d ∣ c),
          μ d * logW (c / d) := by
    apply Finset.sum_congr rfl
    intro c _
    exact hLambda c
  rw [step1]
  have step2 : (∑ c ∈ (Finset.range (m + 1)).filter (fun c => c ∣ m),
        ∑ d ∈ (Finset.range (c + 1)).filter (fun d => d ∣ c),
          μ d * logW (c / d))
      = ∑ t ∈ (Finset.range (m + 1)).filter (fun t => t ∣ m),
        ∑ d ∈ (Finset.range (m / t + 1)).filter (fun d => d ∣ m / t),
          μ d * logW t := by
    simp only [Finset.sum_sigma']
    refine Finset.sum_bij'
      (fun a _ => (⟨a.1 / a.2, a.2⟩ : Sigma fun _ => ℕ))
      (fun a _ => (⟨a.2 * a.1, a.2⟩ : Sigma fun _ => ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨c, d⟩ := a
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at ha ⊢
      obtain ⟨⟨hcm, hcdvd⟩, ⟨hdc, hddvd⟩⟩ := ha
      have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hcdvd (by omega)
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddvd hcpos
      obtain ⟨k, rfl⟩ := hddvd
      obtain ⟨j, rfl⟩ := hcdvd
      have hmpos : 0 < d * k * j := by omega
      have hjpos : 0 < j := Nat.pos_of_dvd_of_pos ⟨d * k, by ring⟩ hmpos
      have hkpos : 0 < k := Nat.pos_of_dvd_of_pos ⟨d * j, by ring⟩ hmpos
      have hdiv : d * k * j / k = d * j :=
        Nat.div_eq_of_eq_mul_right hkpos (by ring)
      rw [Nat.mul_div_cancel_left _ hdpos]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · have hkle : k ≤ d * k * j :=
          le_trans (Nat.le_mul_of_pos_left k hdpos)
            (Nat.le_mul_of_pos_right _ hjpos)
        omega
      · exact ⟨d * j, by ring⟩
      · rw [hdiv]
        have hle : d ≤ d * j := Nat.le_mul_of_pos_right d hjpos
        omega
      · rw [hdiv]; exact dvd_mul_right d j
    · intro a ha
      obtain ⟨t, e⟩ := a
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at ha ⊢
      obtain ⟨⟨htm, htdvd⟩, ⟨hem, hedvd⟩⟩ := ha
      have htpos : 0 < t := Nat.pos_of_dvd_of_pos htdvd (by omega)
      have hmtpos : 0 < m / t := Nat.div_pos (Nat.le_of_dvd (by omega) htdvd) htpos
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos hedvd hmtpos
      obtain ⟨s, hs⟩ := hedvd
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · have hle : e * t ≤ m := by
          have h1 : e * t ∣ m := ⟨s, by rw [← Nat.mul_div_cancel' htdvd, hs]; ring⟩
          exact Nat.le_of_dvd (by omega) h1
        omega
      · exact ⟨s, by rw [← Nat.mul_div_cancel' htdvd, hs]; ring⟩
      · have hle2 : e ≤ e * t := Nat.le_mul_of_pos_right e htpos
        omega
      · exact dvd_mul_right e t
    · intro a ha
      obtain ⟨c, d⟩ := a
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at ha
      obtain ⟨⟨hcm, hcdvd⟩, ⟨hdc, hddvd⟩⟩ := ha
      change (⟨d * (c / d), d⟩ : Sigma fun _ => ℕ) = _
      rw [Nat.mul_div_cancel' hddvd]
    · intro a ha
      obtain ⟨t, e⟩ := a
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at ha
      obtain ⟨⟨htm, htdvd⟩, ⟨hem, hedvd⟩⟩ := ha
      have hmtpos : 0 < m / t := Nat.div_pos (Nat.le_of_dvd (by omega) htdvd)
        (Nat.pos_of_dvd_of_pos htdvd (by omega))
      have hepos : 0 < e := Nat.pos_of_dvd_of_pos hedvd hmtpos
      change (⟨e * t / e, e⟩ : Sigma fun _ => ℕ) = _
      rw [Nat.mul_div_cancel_left _ hepos]
    · intro a ha
      rfl
  rw [step2]
  have step3 : ∀ t ∈ (Finset.range (m + 1)).filter (fun t => t ∣ m),
      (∑ d ∈ (Finset.range (m / t + 1)).filter (fun d => d ∣ m / t),
        μ d * logW t)
      = (if m / t = 1 then logW t else 0) := by
    intro t _
    rw [← Finset.sum_mul, hMu]
    split_ifs <;> simp [*]
  rw [Finset.sum_congr rfl step3]
  have hmem : m ∈ (Finset.range (m + 1)).filter (fun c => c ∣ m) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_self m, dvd_rfl⟩
  have hvan : ∀ t ∈ (Finset.range (m + 1)).filter (fun t => t ∣ m),
      t ≠ m → (if m / t = 1 then logW t else 0) = 0 := by
    intro t ht htm
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨_, htdvd⟩ := ht
    have hne : m / t ≠ 1 := by
      intro hcon
      apply htm
      have htm2 : t * (m / t) = m := Nat.mul_div_cancel' htdvd
      rw [hcon, mul_one] at htm2
      exact htm2
    simp [hne]
  have hmm : m / m = 1 := Nat.div_self (by omega)
  calc logW m = (if m / m = 1 then logW m else 0) := by simp [hmm]
  _ = ∑ x ∈ (Finset.range (m + 1)).filter (fun x => x ∣ m),
        (if m / x = 1 then logW x else 0) :=
      (Finset.sum_eq_single m hvan (by intro hcon; exact absurd hmem hcon)).symm

private lemma filter_div_eq (b n : ℕ) (hbn : b ∣ n)
    (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range (n / b + 1)).filter (fun c => c ∣ n / b)).filter P
    = (Finset.range (n + 1)).filter (fun c => P c ∧ b * c ∣ n) := by
  have hbnb : b * (n / b) = n := Nat.mul_div_cancel' hbn
  ext c
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    obtain ⟨⟨hlt, hcdvd⟩, hP⟩ := h
    have hle : n / b ≤ n := Nat.div_le_self n b
    obtain ⟨k, hk⟩ := hcdvd
    exact ⟨by omega, hP, ⟨k, by rw [← hbnb, hk]; ring⟩⟩
  · intro h
    obtain ⟨hlt, hP, hbc⟩ := h
    have hbc' := hbc
    obtain ⟨k, hk⟩ := hbc
    by_cases hn0 : n = 0
    · subst hn0
      rw [Nat.zero_div]
      exact ⟨⟨hlt, dvd_zero c⟩, hP⟩
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
      have hb0 : b ≠ 0 := by
        intro hb0
        apply hn0
        rw [hb0, zero_mul, zero_mul] at hk
        exact hk
      have hb1' : 1 ≤ b := Nat.pos_of_ne_zero hb0
      have hc1 : 1 ≤ c :=
        Nat.pos_of_dvd_of_pos (dvd_trans (dvd_mul_left c b) hbc') hn1
      have hkdvd : k ∣ n := ⟨b * c, by rw [hk]; ring⟩
      have hk1 : 1 ≤ k := Nat.pos_of_dvd_of_pos hkdvd hn1
      have hdiv : n / b = c * k :=
        Nat.div_eq_of_eq_mul_right hb1' (by rw [hk]; ring)
      have hcle : c ≤ c * k := Nat.le_mul_of_pos_right c hk1
      refine ⟨⟨by omega, ?_⟩, hP⟩
      · rw [hdiv]; exact ⟨k, rfl⟩

private lemma inner_le_eq (b n V : ℕ) (hbn : b ∣ n) :
    ((Finset.range (n / b + 1)).filter (fun c => c ∣ n / b)).filter
      (fun c => c ≤ V)
    = (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n) :=
  filter_div_eq b n hbn _

private lemma inner_gt_eq (b n V : ℕ) (hbn : b ∣ n) :
    ((Finset.range (n / b + 1)).filter (fun c => c ∣ n / b)).filter
      (fun c => V < c)
    = (Finset.range (n + 1)).filter (fun c => V < c ∧ b * c ∣ n) :=
  filter_div_eq b n hbn _

private lemma double_swap {R : Type*} [CommRing R] (μ Λ : ArithmeticFunction R)
    (n V : ℕ) (hn1 : 1 ≤ n) :
    (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n),
      ∑ c ∈ ((Finset.range (n / b + 1)).filter (fun c => c ∣ n / b)).filter
        (fun c => c ≤ V),
        μ b * Λ c)
    = ∑ c ∈ ((Finset.range (n + 1)).filter (fun b => b ∣ n)).filter
        (fun c => c ≤ V),
      ∑ b ∈ (Finset.range (n / c + 1)).filter (fun b => b ∣ n / c),
        μ b * Λ c := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun a _ => (⟨a.2, a.1⟩ : Sigma fun _ => ℕ))
    (fun a _ => (⟨a.2, a.1⟩ : Sigma fun _ => ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨b, c⟩ := a
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at ha ⊢
    have hbdvd : b ∣ n := ha.1.2
    have hcdvd : c ∣ n / b := (ha.2.1).2
    have hcV : c ≤ V := ha.2.2
    have hb1 : 1 ≤ b := Nat.pos_of_dvd_of_pos hbdvd hn1
    have hnb : 1 ≤ n / b := Nat.div_pos (Nat.le_of_dvd (by omega) hbdvd) hb1
    have hc1 : 1 ≤ c := Nat.pos_of_dvd_of_pos hcdvd hnb
    have hcle : c ≤ n / b := Nat.le_of_dvd hnb hcdvd
    obtain ⟨k, hk⟩ := hcdvd
    have hcn : c ∣ n := ⟨b * k, by rw [← Nat.mul_div_cancel' hbdvd, hk]; ring⟩
    have hbcn : b * c ∣ n := ⟨k, by rw [← Nat.mul_div_cancel' hbdvd, hk]; ring⟩
    obtain ⟨j, hj⟩ := hbcn
    have hbnc : b ∣ n / c :=
      ⟨j, Nat.div_eq_of_eq_mul_right hc1 (by rw [hj]; ring)⟩
    have hjdvd : j ∣ n := ⟨b * c, by rw [hj]; ring⟩
    have hj1 : 1 ≤ j := Nat.pos_of_dvd_of_pos hjdvd hn1
    have hdiv : n / c = b * j :=
      Nat.div_eq_of_eq_mul_right hc1 (by rw [hj]; ring)
    have hle2 : n / b ≤ n := Nat.div_le_self n b
    have hble : b ≤ b * j := Nat.le_mul_of_pos_right b hj1
    have hle3 : n / c ≤ n := Nat.div_le_self n c
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · omega
    · exact hcn
    · exact hcV
    · omega
    · exact hbnc
  · intro a ha
    obtain ⟨c, e⟩ := a
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at ha ⊢
    have hcdvd : c ∣ n := (ha.1.1).2
    have hcV : c ≤ V := ha.1.2
    have hedvd : e ∣ n / c := ha.2.2
    have hc1 : 1 ≤ c := Nat.pos_of_dvd_of_pos hcdvd hn1
    have hnc : 1 ≤ n / c := Nat.div_pos (Nat.le_of_dvd (by omega) hcdvd) hc1
    have he1 : 1 ≤ e := Nat.pos_of_dvd_of_pos hedvd hnc
    have hele : e ≤ n / c := Nat.le_of_dvd hnc hedvd
    obtain ⟨k, hk⟩ := hedvd
    have hen : e ∣ n := ⟨c * k, by rw [← Nat.mul_div_cancel' hcdvd, hk]; ring⟩
    have hecn : e * c ∣ n := ⟨k, by rw [← Nat.mul_div_cancel' hcdvd, hk]; ring⟩
    obtain ⟨j, hj⟩ := hecn
    have hecn2 : c ∣ n / e :=
      ⟨j, Nat.div_eq_of_eq_mul_right he1 (by rw [hj]; ring)⟩
    have hjdvd : j ∣ n := ⟨e * c, by rw [hj]; ring⟩
    have hj1 : 1 ≤ j := Nat.pos_of_dvd_of_pos hjdvd hn1
    have hdiv : n / e = c * j :=
      Nat.div_eq_of_eq_mul_right he1 (by rw [hj]; ring)
    have hle2 : n / c ≤ n := Nat.div_le_self n c
    have hcle : c ≤ c * j := Nat.le_mul_of_pos_right c hj1
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · omega
    · exact hen
    · omega
    · exact hecn2
    · exact hcV
  · intro a ha
    obtain ⟨x, y⟩ := a
    rfl
  · intro a ha
    obtain ⟨x, y⟩ := a
    rfl
  · intro a ha
    rfl

/-- **Vaughan's identity in a commutative ring.** Let $R$ be a commutative ring, let $\mu$ and
$\Lambda$ be arithmetic functions with values in $R$ (so $\mu(0) = \Lambda(0) = 0$), and let
$L : \mathbb{N} \to R$ be any function. Suppose that for every natural number $m$,
$\sum_{d \mid m} \mu(d)$ is $1$ if $m = 1$ and $0$ otherwise, and
$\Lambda(m) = \sum_{d \mid m} \mu(d) \, L(m/d)$, where both sums run over the $d$ with
$0 \le d \le m$ and $d \mid m$. Then for all natural numbers $U$, $V$ and $n$ with $V < n$,

$$\Lambda(n) = \sum_{b \mid n,\ b \le U} \mu(b) \, L(n/b) -
\sum_{b \mid n,\ b \le U} \ \sum_{c \le V,\ bc \mid n} \mu(b) \, \Lambda(c) +
\sum_{b \mid n,\ b > U} \ \sum_{c > V,\ bc \mid n} \mu(b) \, \Lambda(c),$$

where $b$ and $c$ range over $0, 1, \dots, n$.

When $R = \mathbb{R}$, $\mu$ is the Möbius function, $L = \log$ and $\Lambda$ is the von Mangoldt
function, the hypotheses hold and this is the classical Vaughan identity. -/
theorem vaughan_identity_general {R : Type*} [CommRing R]
    (μ Λ : ArithmeticFunction R) (logW : ℕ → R)
    (U V n : ℕ) (hn : V < n)
    (hLambda : ∀ m, Λ m =
      ∑ d ∈ (Finset.range (m + 1)).filter (fun d => d ∣ m), μ d * logW (m / d))
    (hMu : ∀ m, ∑ d ∈ (Finset.range (m + 1)).filter (fun d => d ∣ m), μ d =
      if m = 1 then 1 else 0) :
    Λ n = (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
        μ b * logW (n / b))
      - (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
          ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
            μ b * Λ c)
      + (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
          ∑ c ∈ (Finset.range (n + 1)).filter (fun c => V < c ∧ b * c ∣ n),
            μ b * Λ c) := by
  have hn1 : 1 ≤ n := by omega
  have hTset : ((Finset.range (n + 1)).filter (fun b => b ∣ n)).filter
      (fun b => U < b)
      = (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b) := by
    rw [Finset.filter_filter]
  have hS1 : ((Finset.range (n + 1)).filter (fun b => b ∣ n)).filter
      (fun b => ¬ U < b)
      = (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, not_lt, and_assoc]
  have hnest : (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n),
        μ b * logW (n / b))
      = (∑ b ∈ ((Finset.range (n + 1)).filter
          (fun b => b ∣ n)).filter (fun b => ¬ U < b), μ b * logW (n / b))
      + (∑ b ∈ ((Finset.range (n + 1)).filter
          (fun b => b ∣ n)).filter (fun b => U < b), μ b * logW (n / b)) := by
    have h := Finset.sum_filter_add_sum_filter_not
      ((Finset.range (n + 1)).filter (fun b => b ∣ n)) (fun b => U < b)
      (fun b => μ b * logW (n / b))
    rw [add_comm] at h
    exact h.symm
  have h1 : Λ n
      = (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
          μ b * logW (n / b))
      + (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
          μ b * logW (n / b)) := by
    rw [hLambda n, ← hS1, ← hTset]
    exact hnest
  have h2 : (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
          μ b * logW (n / b))
      = (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
          ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
            μ b * Λ c)
      + (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
          ∑ c ∈ (Finset.range (n + 1)).filter (fun c => V < c ∧ b * c ∣ n),
            μ b * Λ c) := by
    have per_b : ∀ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
        μ b * logW (n / b)
        = (∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
            μ b * Λ c)
        + (∑ c ∈ (Finset.range (n + 1)).filter (fun c => V < c ∧ b * c ∣ n),
            μ b * Λ c) := by
      intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨hbmem, hbdvd, -⟩ := hb
      have hb1 : 1 ≤ b := Nat.pos_of_dvd_of_pos hbdvd hn1
      have hnb : 1 ≤ n / b :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hbdvd) hb1
      rw [log_eq_sum_Lambda μ Λ logW hLambda hMu (n / b) hnb,
        Finset.mul_sum, ← inner_le_eq b n V hbdvd,
        ← inner_gt_eq b n V hbdvd]
      have h := Finset.sum_filter_add_sum_filter_not
        ((Finset.range (n / b + 1)).filter (fun c => c ∣ n / b))
        (fun c => c ≤ V) (fun c => μ b * Λ c)
      simp only [not_le] at h
      exact h.symm
    exact (Finset.sum_congr rfl per_b).trans Finset.sum_add_distrib
  have hcancel : (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
          ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
            μ b * Λ c)
      + (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
          ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
            μ b * Λ c)
      = 0 := by
    have e1 : (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
            ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
              μ b * Λ c)
        = ∑ b ∈ ((Finset.range (n + 1)).filter
            (fun b => b ∣ n)).filter (fun b => U < b),
          ∑ c ∈ ((Finset.range (n / b + 1)).filter
            (fun c => c ∣ n / b)).filter (fun c => c ≤ V),
            μ b * Λ c := by
      rw [← hTset]
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨hbD, -⟩ := hb
      rw [Finset.mem_filter, Finset.mem_range] at hbD
      obtain ⟨-, hbdvd⟩ := hbD
      rw [← inner_le_eq b n V hbdvd]
    have e2 : (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
            ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
              μ b * Λ c)
        = ∑ b ∈ ((Finset.range (n + 1)).filter
            (fun b => b ∣ n)).filter (fun b => ¬ U < b),
          ∑ c ∈ ((Finset.range (n / b + 1)).filter
            (fun c => c ∣ n / b)).filter (fun c => c ≤ V),
            μ b * Λ c := by
      rw [← hS1]
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [Finset.mem_filter] at hb
      obtain ⟨hbD, -⟩ := hb
      rw [Finset.mem_filter, Finset.mem_range] at hbD
      obtain ⟨-, hbdvd⟩ := hbD
      rw [← inner_le_eq b n V hbdvd]
    have hcomb : (∑ b ∈ ((Finset.range (n + 1)).filter
            (fun b => b ∣ n)).filter (fun b => U < b),
          ∑ c ∈ ((Finset.range (n / b + 1)).filter
            (fun c => c ∣ n / b)).filter (fun c => c ≤ V),
            μ b * Λ c)
        + (∑ b ∈ ((Finset.range (n + 1)).filter
            (fun b => b ∣ n)).filter (fun b => ¬ U < b),
          ∑ c ∈ ((Finset.range (n / b + 1)).filter
            (fun c => c ∣ n / b)).filter (fun c => c ≤ V),
            μ b * Λ c)
        = ∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n),
          ∑ c ∈ ((Finset.range (n / b + 1)).filter
            (fun c => c ∣ n / b)).filter (fun c => c ≤ V),
            μ b * Λ c :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    rw [e1, e2, hcomb, double_swap μ Λ n V hn1]
    refine Finset.sum_eq_zero ?_
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hcD, hcV⟩ := hc
    rw [Finset.mem_filter, Finset.mem_range] at hcD
    obtain ⟨-, hcdvd⟩ := hcD
    have hcn : c < n := lt_of_le_of_lt hcV hn
    have hnc : n / c ≠ 1 := by
      intro hcon
      have h1 : c * (n / c) = n := Nat.mul_div_cancel' hcdvd
      rw [hcon, mul_one] at h1
      omega
    rw [← Finset.sum_mul, hMu]
    simp [hnc]
  calc Λ n = (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
          μ b * logW (n / b))
        + (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
          μ b * logW (n / b)) := h1
    _ = (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
          μ b * logW (n / b))
        + ((∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
            ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
              μ b * Λ c)
          + (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
            ∑ c ∈ (Finset.range (n + 1)).filter (fun c => V < c ∧ b * c ∣ n),
              μ b * Λ c)) := by rw [h2]
    _ = (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
          μ b * logW (n / b))
        - (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
            ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
              μ b * Λ c)
        + (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
            ∑ c ∈ (Finset.range (n + 1)).filter (fun c => V < c ∧ b * c ∣ n),
              μ b * Λ c) := by linear_combination hcancel

set_option linter.unusedVariables false in
/-- **Vaughan's identity.** Let $R$ be a commutative ring, let $\mu$ and $\Lambda$ be arithmetic
functions with values in $R$ (so $\mu(0) = \Lambda(0) = 0$), and let $L : \mathbb{N} \to R$ be
any function. Suppose that for every natural number $m$, $\sum_{d \mid m} \mu(d)$ is $1$ if
$m = 1$ and $0$ otherwise, and $\Lambda(m) = \sum_{d \mid m} \mu(d) \, L(m/d)$, where both sums
run over the $d$ with $0 \le d \le m$ and $d \mid m$. Then for all natural numbers $U \ge 1$,
$V \ge 1$ and $n > V$,

$$\Lambda(n) = \sum_{b \mid n,\ b \le U} \mu(b) \, L(n/b) -
\sum_{b \mid n,\ b \le U} \ \sum_{c \le V,\ bc \mid n} \mu(b) \, \Lambda(c) +
\sum_{b \mid n,\ b > U} \ \sum_{c > V,\ bc \mid n} \mu(b) \, \Lambda(c),$$

where $b$ and $c$ range over $0, 1, \dots, n$.

When $R = \mathbb{R}$, $\mu$ is the Möbius function, $L = \log$ and $\Lambda$ is the von Mangoldt
function, the hypotheses hold and this is the classical Vaughan identity.

Source: https://en.wikipedia.org/wiki/Vaughan%27s_identity
It follows from `vaughan_identity_general`; the hypotheses `hU` and `hV` are unused and keep the
source's shape.
Proves `Wanted` entry `vaughan_identity`.
-/
theorem vaughan_identity {R : Type*} [CommRing R]
    (μ Λ : ArithmeticFunction R) (logW : ℕ → R)
    (U V n : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hn : V < n)
    (hLambda : ∀ m, Λ m =
      ∑ d ∈ (Finset.range (m + 1)).filter (fun d => d ∣ m), μ d * logW (m / d))
    (hMu : ∀ m, ∑ d ∈ (Finset.range (m + 1)).filter (fun d => d ∣ m), μ d =
      if m = 1 then 1 else 0) :
    Λ n = (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
        μ b * logW (n / b))
      - (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
          ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
            μ b * Λ c)
      + (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
          ∑ c ∈ (Finset.range (n + 1)).filter (fun c => V < c ∧ b * c ∣ n),
            μ b * Λ c) := by
  exact vaughan_identity_general μ Λ logW U V n hn hLambda hMu

end MetaMathlibExt

end
