/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import MathlibExt.NumberTheory.LucasSequence

@[expose] public section

namespace MetaMathlibExt

/-! In the docstrings below, `U n` is `(lucasU params n : ZMod m)` and `Q` is `params.q`. -/

private theorem lucasU_cast_zero (m : ℕ) (params : LucasSequenceParams) :
    (lucasU params 0 : ZMod m) = 0 := by simp [lucasU]
private theorem lucasU_cast_one (m : ℕ) (params : LucasSequenceParams) :
    (lucasU params 1 : ZMod m) = 1 := by simp [lucasU]
private theorem lucasU_cast_succ_succ (m : ℕ) (params : LucasSequenceParams) (n : ℕ) :
    (lucasU params (n + 2) : ZMod m)
      = params.p * (lucasU params (n + 1) : ZMod m) - params.q * (lucasU params n : ZMod m) := by
  simp [lucasU]

/-- Addition formula: U (s+t+1) = U (s+1) * U (t+1) - Q * (U s * U t). -/
private theorem lucasU_cast_add (m : ℕ) (params : LucasSequenceParams) (s t : ℕ) :
    (lucasU params (s + t + 1) : ZMod m)
      = (lucasU params (s + 1) : ZMod m) * (lucasU params (t + 1) : ZMod m)
        - params.q * ((lucasU params s : ZMod m) * (lucasU params t : ZMod m)) := by
  refine Nat.twoStepInduction (motive := fun t => (lucasU params (s + t + 1) : ZMod m)
      = (lucasU params (s + 1) : ZMod m) * (lucasU params (t + 1) : ZMod m)
        - params.q * ((lucasU params s : ZMod m) * (lucasU params t : ZMod m))) ?_ ?_ ?_ t
  · simp [lucasU_cast_zero, lucasU_cast_one]
  · have h2 : (lucasU params (1 + 1) : ZMod m) = params.p := by
      rw [show (1 : ℕ) + 1 = 0 + 2 from rfl, lucasU_cast_succ_succ, lucasU_cast_one,
        lucasU_cast_zero]
      ring
    have eL : s + 1 + 1 = s + 2 := by omega
    rw [eL, lucasU_cast_succ_succ, h2, lucasU_cast_one]
    ring
  · intro n ih1 ih2
    have gL : s + (n + 2) + 1 = s + n + 1 + 2 := by omega
    have gM : s + n + 1 + 1 = s + (n + 1) + 1 := by omega
    have gR : n + 2 + 1 = (n + 1) + 2 := by omega
    rw [gL, lucasU_cast_succ_succ m params (s + n + 1), gM, ih2, ih1,
      gR, lucasU_cast_succ_succ m params (n + 1), lucasU_cast_succ_succ m params n]
    ring

/-- Doubling: U (2*t+1) = U (t+1)^2 - Q * U t^2. -/
private theorem lucasU_cast_double (m : ℕ) (params : LucasSequenceParams) (t : ℕ) :
    (lucasU params (2 * t + 1) : ZMod m)
      = (lucasU params (t + 1) : ZMod m) ^ 2 - params.q * (lucasU params t : ZMod m) ^ 2 := by
  have h := lucasU_cast_add m params t t
  have e : t + t + 1 = 2 * t + 1 := by omega
  rw [e] at h
  linear_combination h

/-- Shift: if U s = 0 then U (s+t) = U (s+1) * U t. -/
private theorem lucasU_cast_shift (m : ℕ) (params : LucasSequenceParams) (s t : ℕ)
    (hs : (lucasU params s : ZMod m) = 0) :
    (lucasU params (s + t) : ZMod m)
      = (lucasU params (s + 1) : ZMod m) * (lucasU params t : ZMod m) := by
  refine Nat.twoStepInduction (motive := fun t => (lucasU params (s + t) : ZMod m)
      = (lucasU params (s + 1) : ZMod m) * (lucasU params t : ZMod m)) ?_ ?_ ?_ t
  · simp [hs, lucasU_cast_zero]
  · simp [lucasU_cast_one]
  · intro n ih1 ih2
    have g : s + (n + 2) = (s + n) + 2 := by omega
    have gM : s + n + 1 = s + (n + 1) := by omega
    rw [g, lucasU_cast_succ_succ m params (s + n), gM, ih2, ih1,
      lucasU_cast_succ_succ m params n]
    ring

/-- Backward recurrence: Q * U n = P * U (n+1) - U (n+2), solved for U n when Q is a unit. -/
private theorem lucasU_cast_back_step (m : ℕ) (params : LucasSequenceParams)
    {Qi : ZMod m} (hQi : (params.q : ZMod m) * Qi = 1) (n : ℕ) :
    (lucasU params n : ZMod m)
      = Qi * (params.p * (lucasU params (n + 1) : ZMod m) - (lucasU params (n + 2) : ZMod m)) := by
  linear_combination Qi * lucasU_cast_succ_succ m params n - (lucasU params n : ZMod m) * hQi

/-- Consecutive terms are jointly a unit. -/
private theorem lucasU_cast_unimodular (m : ℕ) (params : LucasSequenceParams)
    (hQ : IsUnit (params.q : ZMod m)) (n : ℕ) :
    ∃ x y, x * (lucasU params n : ZMod m) + y * (lucasU params (n + 1) : ZMod m) = 1 := by
  obtain ⟨Qi, hQi⟩ := isUnit_iff_exists_inv.mp hQ
  induction n with
  | zero => exact ⟨0, 1, by simp [lucasU_cast_zero, lucasU_cast_one]⟩
  | succ n ih =>
    obtain ⟨x, y, hxy⟩ := ih
    refine ⟨x * Qi * params.p + y, -(x * Qi), ?_⟩
    rw [lucasU_cast_back_step m params hQi n] at hxy
    linear_combination hxy

/-- If U s = 0 then U (s+1) is a unit. -/
private theorem lucasU_cast_isUnit_succ (m : ℕ) (params : LucasSequenceParams)
    (hQ : IsUnit (params.q : ZMod m)) (s : ℕ) (hs : (lucasU params s : ZMod m) = 0) :
    IsUnit (lucasU params (s + 1) : ZMod m) := by
  obtain ⟨x, y, hxy⟩ := lucasU_cast_unimodular m params hQ s
  rw [hs, mul_zero, zero_add] at hxy
  exact isUnit_iff_exists_inv.mpr ⟨y, by rw [mul_comm]; exact hxy⟩

/-- One backward step: equal pairs at (k+1,k+2) give equality at k. -/
private theorem lucasU_cast_step_back (m : ℕ) (params : LucasSequenceParams)
    (hQ : IsUnit (params.q : ZMod m)) (k k' : ℕ)
    (h1 : (lucasU params (k + 1) : ZMod m) = (lucasU params (k' + 1) : ZMod m))
    (h2 : (lucasU params (k + 2) : ZMod m) = (lucasU params (k' + 2) : ZMod m)) :
    (lucasU params k : ZMod m) = (lucasU params k' : ZMod m) := by
  obtain ⟨Qi, hQi⟩ := isUnit_iff_exists_inv.mp hQ
  rw [lucasU_cast_back_step m params hQi k, lucasU_cast_back_step m params hQi k', h1, h2]

/-- From equal consecutive pairs, the difference index is a zero. -/
private theorem lucasU_cast_back (m : ℕ) (params : LucasSequenceParams)
    (hQ : IsUnit (params.q : ZMod m)) (i j : ℕ) (hij : i ≤ j)
    (h0 : (lucasU params i : ZMod m) = (lucasU params j : ZMod m))
    (h1 : (lucasU params (i + 1) : ZMod m) = (lucasU params (j + 1) : ZMod m)) :
    (lucasU params (j - i) : ZMod m) = 0 := by
  have key : ∀ t, t ≤ i → (lucasU params (i - t) : ZMod m) = (lucasU params (j - t) : ZMod m)
      ∧ (lucasU params (i - t + 1) : ZMod m) = (lucasU params (j - t + 1) : ZMod m) := by
    intro t
    induction t with
    | zero => intro _; simpa using ⟨h0, h1⟩
    | succ t ih =>
      intro ht
      have ht' : t ≤ i := by omega
      obtain ⟨e1, e2⟩ := ih ht'
      have hi1 : i - t = (i - (t + 1)) + 1 := by omega
      have hi2 : i - t + 1 = (i - (t + 1)) + 2 := by omega
      have hj1 : j - t = (j - (t + 1)) + 1 := by omega
      have hj2 : j - t + 1 = (j - (t + 1)) + 2 := by omega
      rw [hi1, hj1] at e1
      rw [hi2, hj2] at e2
      exact ⟨lucasU_cast_step_back m params hQ _ _ e1 e2, e1⟩
  have hfin := (key i le_rfl).1
  have hi0 : i - i = 0 := Nat.sub_self i
  rw [hi0, lucasU_cast_zero] at hfin
  exact hfin.symm

/-- **Zero indices of a generalized bi-periodic Fibonacci sequence with $c = d$.** Let
$a, b, c, d$ be natural numbers with $c = d$, and let $m \ge 2$ be a natural number coprime to $a$
and to $c$. Let $(F_n)_{n \ge 0}$ be a sequence of natural numbers with $F_0 = 0$, $F_1 = 1$,
$F_{2n+2} = a F_{2n+1} + c F_{2n}$ and $F_{2n+3} = b F_{2n+2} + d F_{2n+1}$ for all $n \ge 0$.
Then there is an integer $l > 0$ such that, for every $n \ge 0$, $m$ divides $F_n$ if and only
if $l$ divides $n$, and $l \le r$ for every $r > 0$ such that $m$ divides $F_r$. -/
theorem generalized_biperiodic_fibonacci_zero_indices_general
    {a b c d m : ℕ}
    (hm : 2 ≤ m)
    (hacoprime : Nat.Coprime a m)
    (hccoprime : Nat.Coprime c m)
    (hcd : c = d)
    (F : ℕ → ℕ)
    (hF_zero : F 0 = 0)
    (hF_one : F 1 = 1)
    (hF_even : ∀ n : ℕ,
      F (2 * n + 2) = a * F (2 * n + 1) + c * F (2 * n))
    (hF_odd : ∀ n : ℕ,
      F (2 * n + 3) = b * F (2 * n + 2) + d * F (2 * n + 1)) :
    ∃ l : ℕ,
      0 < l ∧
      (∀ n : ℕ, m ∣ F n ↔ l ∣ n) ∧
      (∀ r : ℕ, 0 < r → m ∣ F r → l ≤ r) := by
  classical
  subst hcd
  have haU : IsUnit (a : ZMod m) := (ZMod.isUnit_iff_coprime a m).mpr hacoprime
  have hcU : IsUnit (c : ZMod m) := (ZMod.isUnit_iff_coprime c m).mpr hccoprime
  have hNe : NeZero m := ⟨by omega⟩
  have hc0 : (c : ℤ) ≠ 0 := by
    rintro hc
    rw [Nat.cast_eq_zero.mp hc, Nat.coprime_zero_left] at hccoprime
    omega
  obtain ⟨params, hp, hq⟩ : ∃ params : LucasSequenceParams,
      params.p = a * b + 2 * c ∧ params.q = c * c :=
    ⟨⟨a * b + 2 * c, c * c, mul_ne_zero hc0 hc0⟩, rfl, rfl⟩
  have hP : (params.p : ZMod m) = (a : ZMod m) * b + 2 * c := by rw [hp]; push_cast; ring
  have hQc : (params.q : ZMod m) = (c : ZMod m) * c := by rw [hq]; push_cast; ring
  have hQ : IsUnit (params.q : ZMod m) := hQc ▸ hcU.mul hcU
  have hcast : ∀ n : ℕ, m ∣ F n ↔ ((F n : ℕ) : ZMod m) = 0 :=
    fun n => (ZMod.natCast_eq_zero_iff (F n) m).symm
  have hz : ((F 0 : ℕ) : ZMod m) = 0 := by rw [hF_zero, Nat.cast_zero]
  have hone : ((F 1 : ℕ) : ZMod m) = 1 := by rw [hF_one, Nat.cast_one]
  have heven : ∀ n : ℕ, ((F (2 * n + 2) : ℕ) : ZMod m)
      = (a : ZMod m) * ((F (2 * n + 1) : ℕ) : ZMod m)
        + (c : ZMod m) * ((F (2 * n) : ℕ) : ZMod m) := by
    intro n
    have h := hF_even n
    rw [h]
    push_cast
    ring
  have hodd : ∀ n : ℕ, ((F (2 * n + 3) : ℕ) : ZMod m)
      = (b : ZMod m) * ((F (2 * n + 2) : ℕ) : ZMod m)
        + (c : ZMod m) * ((F (2 * n + 1) : ℕ) : ZMod m) := by
    intro n
    have h := hF_odd n
    rw [h]
    push_cast
    ring
  have hErec : ∀ k : ℕ, ((F (2 * k + 4) : ℕ) : ZMod m)
      = ((a : ZMod m) * b + 2 * c) * ((F (2 * k + 2) : ℕ) : ZMod m)
        - ((c : ZMod m) * c) * ((F (2 * k) : ℕ) : ZMod m) := by
    intro k
    have h1 := heven (k + 1)
    have h2 := hodd k
    have h3 := heven k
    rw [show 2 * (k + 1) + 2 = 2 * k + 4 from by omega,
      show 2 * (k + 1) + 1 = 2 * k + 3 from by omega,
      show 2 * (k + 1) = 2 * k + 2 from by omega] at h1
    linear_combination h1 + (a : ZMod m) * h2 - (c : ZMod m) * h3
  have hEU : ∀ k : ℕ, ((F (2 * k) : ℕ) : ZMod m)
      = (a : ZMod m) * (lucasU params k : ZMod m) := by
    intro k
    refine Nat.twoStepInduction (motive := fun k => ((F (2 * k) : ℕ) : ZMod m)
        = (a : ZMod m) * (lucasU params k : ZMod m)) ?_ ?_ ?_ k
    · simp [hz, lucasU_cast_zero]
    · have h2 : ((F (2 * 0 + 2) : ℕ) : ZMod m)
          = (a : ZMod m) * ((F (2 * 0 + 1) : ℕ) : ZMod m)
            + (c : ZMod m) * ((F (2 * 0) : ℕ) : ZMod m) := heven 0
      have r1 : (2 : ℕ) * 0 + 2 = 2 := by omega
      have r2 : (2 : ℕ) * 0 + 1 = 1 := by omega
      have r3 : (2 : ℕ) * 0 = 0 := by omega
      rw [r1, r2, r3, hone, hz] at h2
      have g : (2 : ℕ) * 1 = 2 := by omega
      rw [g, lucasU_cast_one]
      linear_combination h2
    · intro n ih0 ih1
      have g : 2 * (n + 2) = 2 * n + 4 := by omega
      have g1 : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [g]
      have hrec := hErec n
      rw [g1] at ih1
      have hU := lucasU_cast_succ_succ m params n
      rw [hP, hQc] at hU
      linear_combination hrec + ((a : ZMod m) * b + 2 * c) * ih1
        - ((c : ZMod m) * c) * ih0 - (a : ZMod m) * hU
  have hOU : ∀ k : ℕ, ((F (2 * k + 1) : ℕ) : ZMod m)
      = (lucasU params (k + 1) : ZMod m)
        - (c : ZMod m) * (lucasU params k : ZMod m) := by
    intro k
    have h := heven k
    have e1 := hEU (k + 1)
    have e0 := hEU k
    rw [show 2 * (k + 1) = 2 * k + 2 from by omega] at e1
    have hmul : (a : ZMod m) * (((F (2 * k + 1) : ℕ) : ZMod m)
        - ((lucasU params (k + 1) : ZMod m)
          - (c : ZMod m) * (lucasU params k : ZMod m))) = 0 := by
      linear_combination -h + e1 - (c : ZMod m) * e0
    have hX := (haU.mul_right_eq_zero).mp hmul
    linear_combination hX
  have hex : ∃ k : ℕ, 0 < k
      ∧ (lucasU params k : ZMod m) = 0 := by
    set N := Fintype.card (ZMod m × ZMod m) with hN
    obtain ⟨a', b', hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (N + 1) =>
        ((lucasU params i.val : ZMod m),
         (lucasU params (i.val + 1) : ZMod m)))
      (by rw [Fintype.card_fin]; omega)
    have ha1 : (lucasU params a'.val : ZMod m)
        = (lucasU params b'.val : ZMod m) :=
      congrArg Prod.fst heq
    have ha2 : (lucasU params (a'.val + 1) : ZMod m)
        = (lucasU params (b'.val + 1) : ZMod m) :=
      congrArg Prod.snd heq
    have hne : a'.val ≠ b'.val := fun h => hab (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨b'.val - a'.val, by omega, ?_⟩
      exact lucasU_cast_back m params hQ a'.val b'.val (le_of_lt hlt) ha1 ha2
    · refine ⟨a'.val - b'.val, by omega, ?_⟩
      exact lucasU_cast_back m params hQ b'.val a'.val (le_of_lt hgt) ha1.symm ha2.symm
  set e := Nat.find hex with he
  have hepos : 0 < e := by rw [he]; exact (Nat.find_spec hex).1
  have heU0 : (lucasU params e : ZMod m) = 0 := by
    rw [he]; exact (Nat.find_spec hex).2
  have hemin : ∀ k : ℕ, 0 < k
      → (lucasU params k : ZMod m) = 0
      → e ≤ k := by
    intro k hk0 hkU
    rw [he]
    exact Nat.find_min' hex ⟨hk0, hkU⟩
  have hUe1 : IsUnit (lucasU params (e + 1) : ZMod m) :=
    lucasU_cast_isUnit_succ m params hQ e heU0
  have hmul : ∀ q r : ℕ,
      (lucasU params (e * q + r) : ZMod m)
        = (lucasU params (e + 1) : ZMod m) ^ q * (lucasU params r : ZMod m) := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      have hqq : e * (q + 1) + r = e + (e * q + r) := by ring
      rw [hqq, lucasU_cast_shift m params e (e * q + r) heU0, ih]
      ring
  have hUchar : ∀ k : ℕ,
      (lucasU params k : ZMod m) = 0 ↔ e ∣ k := by
    intro k
    constructor
    · intro hUk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · exact dvd_zero e
      · have hkm := Nat.div_add_mod k e
        have hlt : k % e < e := Nat.mod_lt k hepos
        have hUr := hmul (k / e) (k % e)
        rw [hkm] at hUr
        rw [hUk] at hUr
        have hpow : IsUnit
            ((lucasU params (e + 1) : ZMod m) ^ (k / e)) :=
          hUe1.pow (k / e)
        have hUr0 : (lucasU params (k % e) : ZMod m)
            = 0 := (hpow.mul_right_eq_zero).mp hUr.symm
        rcases Nat.eq_zero_or_pos (k % e) with h0 | hpos
        · exact Nat.dvd_of_mod_eq_zero h0
        · have hle := hemin (k % e) hpos hUr0
          omega
    · intro h
      obtain ⟨t, rfl⟩ := h
      have h0 := hmul t 0
      rwa [Nat.add_zero, lucasU_cast_zero, mul_zero] at h0
  have hEchar : ∀ k : ℕ, ((F (2 * k) : ℕ) : ZMod m) = 0 ↔ e ∣ k := by
    intro k
    rw [hEU k, haU.mul_right_eq_zero]
    exact hUchar k
  have hdouble : ∀ t : ℕ, ((F (2 * t + 1) : ℕ) : ZMod m) = 0
      → (lucasU params (2 * t + 1) : ZMod m) = 0 := by
    intro t hf0
    have hUc : (lucasU params (t + 1) : ZMod m)
        = (c : ZMod m) * (lucasU params t : ZMod m) := by
      linear_combination hf0 - hOU t
    have hd := lucasU_cast_double m params t
    rw [hUc, hQc] at hd
    linear_combination hd
  have hOsingle : ∀ v : ℕ, ((F (2 * (v + e) + 1) : ℕ) : ZMod m)
      = (lucasU params (e + 1) : ZMod m)
        * ((F (2 * v + 1) : ℕ) : ZMod m) := by
    intro v
    have s1 := lucasU_cast_shift m params e (v + 1) heU0
    have s2 := lucasU_cast_shift m params e v heU0
    rw [show e + (v + 1) = (v + e) + 1 from by omega] at s1
    rw [show e + v = v + e from by omega] at s2
    rw [hOU (v + e), hOU v, s1, s2]
    ring
  by_cases hodd : ∃ k : ℕ, ((F (2 * k + 1) : ℕ) : ZMod m) = 0
  · obtain ⟨t0, ht0⟩ := hodd
    have hdvd : e ∣ 2 * t0 + 1 := (hUchar (2 * t0 + 1)).mp (hdouble t0 ht0)
    have hOdde : Odd e := by
      rcases Nat.even_or_odd e with hev | hod
      · exfalso
        have h2e : 2 ∣ e := even_iff_two_dvd.mp hev
        have h2n : 2 ∣ 2 * t0 + 1 := dvd_trans h2e hdvd
        have hev2 : Even (2 * t0 + 1) := even_iff_two_dvd.mpr h2n
        exact (Nat.not_even_iff_odd.mpr ⟨t0, rfl⟩) hev2
      · exact hod
    obtain ⟨u, hu⟩ := hOdde
    have he2 : Nat.Coprime e 2 := Odd.coprime_two_right ⟨u, hu⟩
    obtain ⟨j', hj'⟩ := hdvd
    have hOj' : Odd (e * j') := by rw [← hj']; exact ⟨t0, rfl⟩
    have hoddj' : Odd j' := by
      rcases Nat.even_or_odd j' with hevj | hodj
      · exfalso
        exact (Nat.not_even_iff_odd.mpr hOj') (hevj.mul_left e)
      · exact hodj
    obtain ⟨i0, rfl⟩ := hoddj'
    have hexp : e * (2 * i0 + 1) = 2 * (u + e * i0) + 1 := by rw [hu]; ring
    rw [hexp] at hj'
    have htu : t0 = u + e * i0 := by omega
    have hOshift : ∀ i : ℕ, ((F (2 * (u + e * i) + 1) : ℕ) : ZMod m)
        = (lucasU params (e + 1) : ZMod m) ^ i
          * ((F (2 * u + 1) : ℕ) : ZMod m) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have eee : u + e * (i + 1) = (u + e * i) + e := by ring
        rw [eee, hOsingle, ih]
        ring
    have hO := hOshift i0
    rw [← htu] at hO
    rw [ht0] at hO
    have hU1pow : IsUnit
        ((lucasU params (e + 1) : ZMod m) ^ i0) :=
      hUe1.pow i0
    have hOu0 : ((F (2 * u + 1) : ℕ) : ZMod m) = 0 :=
      (hU1pow.mul_right_eq_zero).mp hO.symm
    have hiff : ∀ n : ℕ, ((F n : ℕ) : ZMod m) = 0 ↔ e ∣ n := by
      intro n
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have e2 : k + k = 2 * k := by omega
        rw [e2, hEchar k]
        exact ⟨fun h => by
          have h' : e ∣ k * 2 := dvd_mul_of_dvd_left h 2
          rwa [mul_comm k 2] at h',
          fun h => he2.dvd_of_dvd_mul_left h⟩
      · constructor
        · intro h
          exact (hUchar (2 * k + 1)).mp (hdouble k h)
        · intro h
          obtain ⟨j, hj⟩ := h
          have hOj : Odd (e * j) := by rw [← hj]; exact ⟨k, rfl⟩
          have hoddj : Odd j := by
            rcases Nat.even_or_odd j with hevj | hodj
            · exfalso
              exact (Nat.not_even_iff_odd.mpr hOj) (hevj.mul_left e)
            · exact hodj
          obtain ⟨j1, rfl⟩ := hoddj
          have hexp2 : e * (2 * j1 + 1) = 2 * (u + e * j1) + 1 := by rw [hu]; ring
          rw [hexp2] at hj
          have hkj : k = u + e * j1 := by omega
          have hOj1 := hOshift j1
          rw [hOu0, mul_zero] at hOj1
          rw [hkj]
          exact hOj1
    have hiffDvd : ∀ n : ℕ, m ∣ F n ↔ e ∣ n := by
      intro n
      rw [hcast n]
      exact hiff n
    exact ⟨e, hepos, hiffDvd,
      fun r hr0 hrm => Nat.le_of_dvd hr0 ((hiffDvd r).mp hrm)⟩
  · have hiff : ∀ n : ℕ, ((F n : ℕ) : ZMod m) = 0 ↔ 2 * e ∣ n := by
      intro n
      rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have e2 : k + k = 2 * k := by omega
        rw [e2, hEchar k, Nat.mul_dvd_mul_iff_left (show 0 < 2 by omega)]
      · have hne : ((F (2 * k + 1) : ℕ) : ZMod m) = 0 → False :=
          fun h => hodd ⟨k, h⟩
        have hnd : ¬ (2 * e ∣ 2 * k + 1) := by
          intro h
          have h2 : 2 ∣ 2 * k + 1 := dvd_trans (dvd_mul_right 2 e) h
          exact (Nat.not_even_iff_odd.mpr ⟨k, rfl⟩) (even_iff_two_dvd.mpr h2)
        exact iff_of_false hne hnd
    have hiffDvd : ∀ n : ℕ, m ∣ F n ↔ 2 * e ∣ n := by
      intro n
      rw [hcast n]
      exact hiff n
    refine ⟨2 * e, by omega, hiffDvd, ?_⟩
    intro r hr0 hrm
    exact Nat.le_of_dvd hr0 ((hiffDvd r).mp hrm)

set_option linter.unusedVariables false in
/-- **Belbachir–Salhi theorem on zero indices of generalized bi-periodic Fibonacci sequences.**
Let $a, b, c, d$ be positive natural numbers with $c = d$, and let $m \ge 2$ be a natural number
coprime to $a$, to $c$ and to $d$. Let $(F_n)_{n \ge 0}$ be a sequence of natural numbers with
$F_0 = 0$, $F_1 = 1$, $F_{2n+2} = a F_{2n+1} + c F_{2n}$ and
$F_{2n+3} = b F_{2n+2} + d F_{2n+1}$ for all $n \ge 0$. Then there is a natural number $l > 0$
such that, for every $n \ge 0$, $m$ divides $F_n$ if and only if $l$ divides $n$, and
$l \le r$ for every $r > 0$ such that $m$ divides $F_r$.

The recurrence is $F_n = a F_{n-1} + c F_{n-2}$ for even $n \ge 2$ and
$F_n = b F_{n-1} + d F_{n-2}$ for odd $n \ge 3$. The conditions $c = d$ and $\gcd(a, m) = 1$ are
the standing assumptions of the source's section, and coprimality of $c$ and $d$ with $m$ is its
global hypothesis on the modulus; the positivity of $a, b, c, d$ and the coprimality of $d$ with
$m$ are not needed for the conclusion.

Source: Hacène Belbachir and Celia Salhi, "The Generalized Bi-Periodic
Fibonacci Sequence Modulo m," Journal of Integer Sequences 24 (2021),
Article 21.9.4, Theorem (label TH2), lines 445–448,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Salhi/salhi4.tex
-/
theorem generalized_biperiodic_fibonacci_zero_indices
    {a b c d m : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hm : 2 ≤ m)
    (hacoprime : Nat.Coprime a m)
    (hccoprime : Nat.Coprime c m)
    (hdcoprime : Nat.Coprime d m)
    (hcd : c = d)
    (F : ℕ → ℕ)
    (hF_zero : F 0 = 0)
    (hF_one : F 1 = 1)
    (hF_even : ∀ n : ℕ,
      F (2 * n + 2) = a * F (2 * n + 1) + c * F (2 * n))
    (hF_odd : ∀ n : ℕ,
      F (2 * n + 3) = b * F (2 * n + 2) + d * F (2 * n + 1)) :
    ∃ l : ℕ,
      0 < l ∧
      (∀ n : ℕ, m ∣ F n ↔ l ∣ n) ∧
      (∀ r : ℕ, 0 < r → m ∣ F r → l ≤ r) :=
  generalized_biperiodic_fibonacci_zero_indices_general hm hacoprime hccoprime hcd F
    hF_zero hF_one hF_even hF_odd

end MetaMathlibExt
