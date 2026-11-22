/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped Rat

namespace Farey

/-!
# Farey sequences

Source: [Hamada, arXiv:2308.11999v6](https://arxiv.org/abs/2308.11999v6),
lines 283-290.
`F_n` is `a/b` with `0 ≤ a ≤ b ≤ n`, `gcd(a,b)=1`, ordered.
Consecutive elements are a Farey pair. Mediant is `(a+c)/(b+d)`.
-/

/-- **Farey set.** For a natural number $n$, the Farey set $F_n$ of order $n$ is the finite set of
rationals $a/d$ with $a$ and $d$ natural numbers, $1 \le d \le n$ and $0 \le a \le d$.

Equivalently, $F_n$ consists of the rationals $q$ with $0 \le q \le 1$ whose denominator in lowest
terms is at most $n$. In particular $F_0$ is empty. -/
def fareyFinset (n : ℕ) : Finset ℚ :=
  ((Finset.Icc 1 n).biUnion fun d : ℕ =>
    ((Finset.Icc 0 d).image fun a : ℕ => ((a : ℤ) /. (d : ℤ) : ℚ)))

/-- **Farey sequence.** For a natural number $n$, the Farey sequence of order $n$ is the list of the
elements of the Farey set $F_n$ in increasing order. -/
def fareySeq (n : ℕ) : List ℚ :=
  (fareyFinset n).sort (· ≤ ·)

lemma fareySeq_sorted (n : ℕ) : (fareySeq n).SortedLT :=
  Finset.sortedLT_sort _

lemma fareySeq_nodup (n : ℕ) : List.Nodup (fareySeq n) :=
  Finset.sort_nodup _ _

@[simp] lemma mem_fareySeq_iff (n : ℕ) (q : ℚ) :
    q ∈ fareySeq n ↔ q ∈ fareyFinset n := by
  simp [fareySeq, Finset.mem_sort]

/-- **Membership in the Farey set.** For a natural number $n$ and a rational number $q$, $q$
belongs to the Farey set $F_n$ of order $n$ if and only if $0 \le q \le 1$ and the denominator of
$q$ in lowest terms is at most $n$. -/
@[simp] theorem mem_fareyFinset_iff (n : ℕ) (q : ℚ) :
    q ∈ fareyFinset n ↔ 0 ≤ q ∧ q ≤ 1 ∧ q.den ≤ n := by
  constructor
  · intro h
    simp only [fareyFinset, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image] at h
    obtain ⟨d, ⟨hd1, hdn⟩, a, ⟨ha0, had⟩, rfl⟩ := h
    have h0 : (0 : ℚ) ≤ ((a : ℤ) /. (d : ℤ) : ℚ) := by
      rw [Rat.divInt_eq_div]
      positivity
    have h1 : ((a : ℤ) /. (d : ℤ) : ℚ) ≤ 1 := by
      rw [Rat.divInt_eq_div, div_le_one (by positivity)]
      exact_mod_cast had
    have hden_dvd : (((a : ℤ) /. (d : ℤ) : ℚ)).den ∣ d := by
      exact_mod_cast Rat.den_dvd (a : ℤ) (d : ℤ)
    have hden : (((a : ℤ) /. (d : ℤ) : ℚ)).den ≤ d :=
      Nat.le_of_dvd (by omega) hden_dvd
    exact ⟨h0, h1, hden.trans hdn⟩
  · intro ⟨h0, h1, hden⟩
    simp only [fareyFinset, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    have hnum_nn : 0 ≤ q.num := Rat.num_nonneg.mpr h0
    have hnum_le : q.num.natAbs ≤ q.den := by
      have h_le_one : q.num ≤ (q.den : ℤ) := Rat.num_le_denom_iff.mpr h1
      omega
    refine ⟨q.den, ⟨q.pos, hden⟩,
      q.num.natAbs, ⟨Nat.zero_le _, hnum_le⟩, ?_⟩
    have h_cast : ((q.num.natAbs : ℕ) : ℤ) = q.num := by omega
    rw [h_cast, Rat.num_divInt_den]

/-- **Farey sets grow with the order.** If $m \le n$ are natural numbers, then every element of the
Farey set $F_m$ belongs to $F_n$, that is, $F_m \subseteq F_n$. -/
theorem fareyFinset_mono {m n : ℕ} (hmn : m ≤ n) : fareyFinset m ⊆ fareyFinset n := by
  intro q hq
  rw [mem_fareyFinset_iff] at hq ⊢
  exact ⟨hq.1, hq.2.1, hq.2.2.trans hmn⟩

/-- **Farey neighbors.** For a natural number $n$, rationals $x$ and $y$ are Farey neighbors of
order $n$ when both lie in the Farey set $F_n$, $x < y$, and no element $z$ of $F_n$ satisfies
$x < z < y$. -/
def IsFareyNeighbor (n : ℕ) (x y : ℚ) : Prop :=
  x ∈ fareyFinset n ∧ y ∈ fareyFinset n ∧ x < y ∧
  ∀ z ∈ fareyFinset n, ¬(x < z ∧ z < y)

/-- **Mediant.** For rational numbers $x = a/b$ and $y = c/d$ written in lowest terms with
$b, d > 0$, the mediant of $x$ and $y$ is the rational number $(a + c)/(b + d)$. -/
def mediant (x y : ℚ) : ℚ :=
  ((x.num + y.num) /. ((x.den + y.den : ℕ) : ℤ) : ℚ)

lemma mediant_def (x y : ℚ) :
    mediant x y = ((x.num + y.num) /. ((x.den + y.den : ℕ) : ℤ) : ℚ) := rfl

private lemma divInt_lt_divInt {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d) :
    (a /. b : ℚ) < c /. d ↔ a * d < c * b := by
  constructor
  · intro h
    have hle := (Rat.divInt_le_divInt hb hd).mp h.le
    have hnle : ¬ (c /. d : ℚ) ≤ a /. b := Rat.not_le.mpr h
    have hnle' : ¬ c * b ≤ a * d := by
      simpa only [Rat.divInt_le_divInt hd hb] using hnle
    omega
  · intro h
    apply Rat.not_le.mp
    intro hle
    have hcross := (Rat.divInt_le_divInt hd hb).mp hle
    omega

lemma mediant_between (x y : ℚ) (hxy : x < y) :
    x < mediant x y ∧ mediant x y < y := by
  have hx_den_pos : (0 : ℤ) < x.den := by exact_mod_cast x.pos
  have hy_den_pos : (0 : ℤ) < y.den := by exact_mod_cast y.pos
  have hsum_pos : (0 : ℤ) < x.den + y.den := by omega
  have hcross : x.num * y.den < y.num * x.den := (Rat.lt_iff x y).mp hxy
  constructor
  · calc
      x = (x.num /. (x.den : ℤ) : ℚ) := (Rat.num_divInt_den x).symm
      _ < mediant x y := by
        apply (divInt_lt_divInt hx_den_pos hsum_pos).2
        nlinarith
  · calc
      mediant x y < (y.num /. (y.den : ℤ) : ℚ) := by
        apply (divInt_lt_divInt hsum_pos hy_den_pos).2
        nlinarith
      _ = y := Rat.num_divInt_den y

lemma mediant_mem_next_of_sum_eq (n : ℕ) (x y : ℚ)
    (hx : x ∈ fareyFinset n) (hy : y ∈ fareyFinset n)
    (hsum : x.den + y.den = n + 1) :
    mediant x y ∈ fareyFinset (n + 1) := by
  have h0 : 0 ≤ mediant x y := by
    have hx0 : 0 ≤ x := (mem_fareyFinset_iff n x |>.mp hx).1
    have hy0 : 0 ≤ y := (mem_fareyFinset_iff n y |>.mp hy).1
    have hx_num_nn : 0 ≤ x.num := Rat.num_nonneg.mpr hx0
    have hy_num_nn : 0 ≤ y.num := Rat.num_nonneg.mpr hy0
    rw [mediant, Rat.divInt_eq_div]
    exact div_nonneg (by exact_mod_cast add_nonneg hx_num_nn hy_num_nn) (by positivity)
  have h1 : mediant x y ≤ 1 := by
    have hx1 : x ≤ 1 := (mem_fareyFinset_iff n x |>.mp hx).2.1
    have hy1 : y ≤ 1 := (mem_fareyFinset_iff n y |>.mp hy).2.1
    have hx_le : (x.num : ℚ) ≤ (x.den : ℚ) := by
      have : (x.num /. (x.den : ℤ) : ℚ) ≤ 1 := by
        simpa only [Rat.num_divInt_den] using hx1
      rw [Rat.divInt_eq_div, div_le_one (by positivity)] at this
      exact this
    have hy_le : (y.num : ℚ) ≤ (y.den : ℚ) := by
      have : (y.num /. (y.den : ℤ) : ℚ) ≤ 1 := by
        simpa only [Rat.num_divInt_den] using hy1
      rw [Rat.divInt_eq_div, div_le_one (by positivity)] at this
      exact this
    unfold mediant
    rw [Rat.divInt_eq_div]
    rw [div_le_one (by positivity)]
    push_cast
    linarith
  have hden_le : (mediant x y).den ≤ n + 1 := by
    have h_le_sum : (mediant x y).den ≤ x.den + y.den := by
      unfold mediant
      have h_dvd : (mediant x y).den ∣ x.den + y.den := by
        exact_mod_cast Rat.den_dvd (x.num + y.num) ((x.den + y.den : ℕ) : ℤ)
      exact Nat.le_of_dvd (Nat.add_pos_left x.pos _) h_dvd
    omega
  exact (mem_fareyFinset_iff (n + 1) _).mpr ⟨h0, h1, hden_le⟩

lemma mediant_strict_between_of_neighbor (n : ℕ) (x y : ℚ)
    (h : IsFareyNeighbor n x y) :
    x < mediant x y ∧ mediant x y < y :=
  mediant_between x y h.2.2.1

lemma neighbor_den_le (n : ℕ) (x y : ℚ) (h : IsFareyNeighbor n x y) :
    x.den ≤ n ∧ y.den ≤ n :=
  ⟨(mem_fareyFinset_iff n x |>.mp h.1).2.2, (mem_fareyFinset_iff n y |>.mp h.2.1).2.2⟩

/-- **Farey neighbors have denominator sum exceeding the order.** Let $n$ be a natural number
and let $F_n$ be the Farey set of order $n$. If $x < y$ are neighbors in $F_n$, meaning that
$x, y \in F_n$ and no element of $F_n$ lies strictly between them, then the denominators $b$ of
$x$ and $d$ of $y$ in lowest terms satisfy $b + d > n$. -/
lemma neighbor_den_sum_gt (n : ℕ) (x y : ℚ) (h : IsFareyNeighbor n x y) :
    n < x.den + y.den := by
  by_contra hle
  have hle' : x.den + y.den ≤ n := by omega
  have hx := h.1
  have hy := h.2.1
  have hmed_mem : mediant x y ∈ fareyFinset n := by
    have h0 : 0 ≤ mediant x y :=
      (mem_fareyFinset_iff n x).mp h.1 |>.1 |>.trans (mediant_between x y h.2.2.1).1.le
    have h1 : mediant x y ≤ 1 :=
      (mediant_between x y h.2.2.1).2.le.trans ((mem_fareyFinset_iff n y).mp h.2.1).2.1
    have hden : (mediant x y).den ≤ n := by
      have h_le_sum : (mediant x y).den ≤ x.den + y.den := by
        unfold mediant
        have h_dvd : (mediant x y).den ∣ x.den + y.den := by
          exact_mod_cast Rat.den_dvd (x.num + y.num) ((x.den + y.den : ℕ) : ℤ)
        exact Nat.le_of_dvd (Nat.add_pos_left x.pos _) h_dvd
      omega
    exact (mem_fareyFinset_iff n _).mpr ⟨by linarith [(mem_fareyFinset_iff n x |>.mp hx).1],
      by linarith [(mem_fareyFinset_iff n y |>.mp hy).2.1], hden⟩
  exact h.2.2.2 (mediant x y) hmed_mem (mediant_between x y h.2.2.1)

/-- **Determinant one and large denominator sum give Farey neighbors.** Let $n$ be a natural
number and let $x = a/b$ and $y = c/d$ be elements of the Farey set $F_n$, written in lowest
terms with $b, d > 0$. If $bc = ad + 1$ and $n < b + d$, then $x$ and $y$ are Farey neighbors of
order $n$. -/
theorem det_one_and_sum_gt_imp_neighbor (n : ℕ) (x y : ℚ)
    (hx : x ∈ fareyFinset n) (hy : y ∈ fareyFinset n)
    (hdet : y.num * (x.den : ℤ) = x.num * (y.den : ℤ) + 1)
    (hsum : n < x.den + y.den) :
    IsFareyNeighbor n x y := by
  have hxy : x < y := (Rat.lt_iff x y).2 (by omega)
  refine ⟨hx, hy, hxy, ?_⟩
  intro z hz ⟨hxz, hzy⟩
  have hxz' : x.num * (z.den : ℤ) < z.num * (x.den : ℤ) :=
    (Rat.lt_iff x z).mp hxz
  have hzy' : z.num * (y.den : ℤ) < y.num * (z.den : ℤ) :=
    (Rat.lt_iff z y).mp hzy
  have hz_le : z.den ≤ n := (mem_fareyFinset_iff n z |>.mp hz).2.2
  have hleft : 1 ≤ z.num * (x.den : ℤ) - x.num * (z.den : ℤ) := by omega
  have hright : 1 ≤ y.num * (z.den : ℤ) - z.num * (y.den : ℤ) := by omega
  have hid : (z.den : ℤ) =
      (y.den : ℤ) * (z.num * x.den - x.num * z.den) +
        (x.den : ℤ) * (y.num * z.den - z.num * y.den) := by
    calc
      (z.den : ℤ) = (z.den : ℤ) * 1 := by ring
      _ = (z.den : ℤ) * (y.num * x.den - x.num * y.den) := by rw [hdet]; ring
      _ = _ := by ring
  have h_ge_sum : (x.den + y.den : ℕ) ≤ z.den := by
    exact_mod_cast (show (x.den : ℤ) + y.den ≤ z.den by
      rw [hid]
      nlinarith [show (0 : ℤ) < x.den by exact_mod_cast x.pos,
        show (0 : ℤ) < y.den by exact_mod_cast y.pos])
  omega

set_option maxHeartbeats 800000 in
-- The constructive denominator argument requires several nonlinear integer normalizations.
/-- **Consecutive Farey fractions have determinant one.** Let $n$ be a natural number. If $x$ and
$y$ are Farey neighbors of order $n$, written in lowest terms as $x = a/b$ and $y = c/d$ with
$b, d > 0$, then $bc = ad + 1$. -/
theorem IsFareyNeighbor.det_eq_one {n : ℕ} {x y : ℚ}
    (h : IsFareyNeighbor n x y) :
    y.num * (x.den : ℤ) = x.num * (y.den : ℤ) + 1 := by
  have hx0 : 0 ≤ x := (mem_fareyFinset_iff n x).mp h.1 |>.1
  have hx1 : x ≤ 1 := (mem_fareyFinset_iff n x).mp h.1 |>.2.1
  have hxb : x.den ≤ n := (mem_fareyFinset_iff n x).mp h.1 |>.2.2
  have hyb : y.den ≤ n := (mem_fareyFinset_iff n y).mp h.2.1 |>.2.2
  let a := x.num.natAbs
  let b := x.den
  let c := y.num.natAbs
  let d := y.den
  have ha_nn : 0 ≤ x.num := Rat.num_nonneg.mpr hx0
  have hc_nn : 0 ≤ y.num := Rat.num_nonneg.mpr ((mem_fareyFinset_iff n y).mp h.2.1 |>.1)
  have ha_eq : (a : ℤ) = x.num := by simp [a, Int.natAbs_of_nonneg ha_nn]
  have hc_eq : (c : ℤ) = y.num := by simp [c, Int.natAbs_of_nonneg hc_nn]
  have hx_eq : x = ((a : ℤ) /. (b : ℤ) : ℚ) := by
    calc
      x = (x.num /. (x.den : ℤ) : ℚ) := (Rat.num_divInt_den x).symm
      _ = ((a : ℤ) /. (b : ℤ) : ℚ) := by rw [ha_eq]
  have hy_eq : y = ((c : ℤ) /. (d : ℤ) : ℚ) := by
    calc
      y = (y.num /. (y.den : ℤ) : ℚ) := (Rat.num_divInt_den y).symm
      _ = ((c : ℤ) /. (d : ℤ) : ℚ) := by rw [hc_eq]
  have hab_lt : a < b := by
    have hxlt : x < 1 := h.2.2.1.trans_le ((mem_fareyFinset_iff n y).mp h.2.1).2.1
    have : x.num < (x.den : ℤ) := Rat.num_lt_denom_iff.mpr hxlt
    omega
  have hpos_b : 0 < b := x.pos
  have hpos_d : 0 < d := y.pos
  have hcop_ab : Nat.Coprime a b := by simpa [a, b] using x.reduced
  obtain ⟨p0, q0, hq0_pos, hq0_le, hp0_eq⟩ :
      ∃ p0 q0 : ℕ, 1 ≤ q0 ∧ q0 ≤ b ∧
        (b : ℤ) * (p0 : ℤ) = (a : ℤ) * (q0 : ℤ) + 1 := by
    by_cases hb1 : b = 1
    · refine ⟨1, 1, by omega, by omega, ?_⟩
      have ha0 : a = 0 := by omega
      simp [ha0, hb1]
    · have hb_gt : 1 < b := by omega
      obtain ⟨u, hu_lt, hu_eq⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop_ab hb_gt
      let q0 := b - u
      have hu_pos : 0 < u := by
        by_contra hu
        have : u = 0 := by omega
        simp [this] at hu_eq
      have hq0_pos : 1 ≤ q0 := by simp [q0]; omega
      have hq0_le : q0 ≤ b := Nat.sub_le _ _
      have hdvd : b ∣ a * q0 + 1 := by
        have hmod : a * u ≡ 1 [MOD b] := by
          change a * u % b = 1 % b
          simpa [Nat.mod_eq_of_lt hb_gt] using hu_eq
        have hsum : a * q0 + a * u = a * b := by
          simp only [q0]
          rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hu_lt)]
        have hzero : a * q0 + a * u ≡ 0 [MOD b] := by
          rw [hsum]
          simpa [Nat.mul_comm] using (dvd_mul_right b a).modEq_zero_nat
        exact Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.rfl.add hmod.symm).trans hzero)
      let p0 := (a * q0 + 1) / b
      have hp0_eq_nat : b * p0 = a * q0 + 1 := by
        rw [Nat.mul_comm]
        exact Nat.div_mul_cancel hdvd
      exact ⟨p0, q0, hq0_pos, hq0_le, by exact_mod_cast hp0_eq_nat⟩
  let k := (n - q0) / b
  let q := q0 + k * b
  let p := p0 + k * a
  have hq_le : q ≤ n := by
    simp only [q, k]
    have hmul := Nat.div_mul_le_self (n - q0) b
    omega
  have hn_lt : n < q + b := by
    have hq0n : q0 ≤ n := hq0_le.trans (show b ≤ n from hxb)
    have hlt : n - q0 < (n - q0) / b * b + b := Nat.lt_div_mul_add hpos_b
    simp only [q, k]
    omega
  have hp_eq : (b : ℤ) * (p : ℤ) = (a : ℤ) * (q : ℤ) + 1 := by
    simp only [p, q]
    push_cast
    nlinarith
  have hq_pos : 0 < q := by simp [q]; omega
  have hp_eq_nat : b * p = a * q + 1 := by exact_mod_cast hp_eq
  have hcop_pq : Nat.Coprime p q := by
    apply Nat.coprime_of_mul_modEq_one b
    change p * b % q = 1 % q
    rw [Nat.mul_comm, hp_eq_nat]
    simp
  have hp_le_q : p ≤ q := by
    have ha_int : (a : ℤ) ≤ (b : ℤ) - 1 := by omega
    have hp_int : (p : ℤ) ≤ q := by
      have hq_int : (1 : ℤ) ≤ q := by exact_mod_cast hq_pos
      nlinarith
    exact_mod_cast hp_int
  have hab_lt_pq : ((a : ℤ) /. (b : ℤ) : ℚ) < ((p : ℤ) /. (q : ℤ) : ℚ) := by
    apply (divInt_lt_divInt (by exact_mod_cast hpos_b) (by exact_mod_cast hq_pos)).2
    nlinarith
  have hpq_mem : ((p : ℤ) /. (q : ℤ) : ℚ) ∈ fareyFinset n := by
    rw [mem_fareyFinset_iff]
    refine ⟨Rat.divInt_nonneg (by omega) (by omega), ?_, ?_⟩
    · have hle : ((p : ℤ) /. (q : ℤ) : ℚ) ≤ (1 /. 1 : ℚ) :=
        (Rat.divInt_le_divInt (by exact_mod_cast hq_pos) (by norm_num)).2
          (by
            have : (p : ℤ) ≤ q := by exact_mod_cast hp_le_q
            simpa using this)
      simpa using hle
    · have h_dvd_int : ((((p : ℤ) /. (q : ℤ) : ℚ)).den : ℤ) ∣ (q : ℤ) :=
        Rat.den_dvd (p : ℤ) (q : ℤ)
      have h_dvd : (((p : ℤ) /. (q : ℤ) : ℚ)).den ∣ q := by exact_mod_cast h_dvd_int
      exact (Nat.le_of_dvd hq_pos h_dvd).trans hq_le
  have h_y_le_pq : ((c : ℤ) /. (d : ℤ) : ℚ) ≤ ((p : ℤ) /. (q : ℤ) : ℚ) := by
    by_contra hlt
    have hpq_lt_y : ((p : ℤ) /. (q : ℤ) : ℚ) < ((c : ℤ) /. (d : ℤ) : ℚ) :=
      Rat.not_le.mp hlt
    exact h.2.2.2 _ hpq_mem ⟨by rwa [hx_eq], by rwa [hy_eq]⟩
  have hDelta_pos : 1 ≤ (b : ℤ) * c - (a : ℤ) * d := by
    have hcross : (a : ℤ) * d < (c : ℤ) * b := by
      simpa [b, d, ha_eq, hc_eq] using (Rat.lt_iff x y).mp h.2.2.1
    nlinarith
  let E : ℤ := (p : ℤ) * d - (c : ℤ) * q
  let Delta : ℤ := (b : ℤ) * c - (a : ℤ) * d
  have hE_nonneg : 0 ≤ E := by
    have := (Rat.divInt_le_divInt (by exact_mod_cast hpos_d)
      (by exact_mod_cast hq_pos)).mp h_y_le_pq
    simp only [E]
    omega
  have hDelta_ge1 : 1 ≤ Delta := by simpa [Delta] using hDelta_pos
  have h_identity : (d : ℤ) = (b : ℤ) * E + (q : ℤ) * Delta := by
    simp only [E, Delta]
    nlinarith
  have hE_zero : E = 0 := by
    by_contra hne
    have hE_ge1 : 1 ≤ E := by omega
    have hd_ge : (b : ℤ) + q ≤ d := by
      rw [h_identity]
      nlinarith [show (0 : ℤ) < b by exact_mod_cast hpos_b,
        show (0 : ℤ) < q by exact_mod_cast hq_pos]
    have : n < d := by exact_mod_cast (show n < d by omega)
    exact (not_lt_of_ge hyb) this
  have hd_eq : (d : ℤ) = q * Delta := by
    rw [hE_zero, mul_zero, zero_add] at h_identity
    exact h_identity
  have hcross_eq : (p : ℤ) * d = (c : ℤ) * q := by
    simp only [E] at hE_zero
    omega
  have hpq_eq : ((p : ℤ) /. (q : ℤ) : ℚ) = ((c : ℤ) /. (d : ℤ) : ℚ) := by
    apply (Rat.divInt_eq_divInt_iff (by exact_mod_cast hq_pos.ne')
      (by exact_mod_cast hpos_d.ne')).2
    omega
  have hcop_cd : Nat.Coprime c d := by simpa [c, d] using y.reduced
  have hq_eq_d : q = d := by
    have hdiv_eq : (p : ℚ) / (q : ℤ) = (c : ℚ) / (d : ℤ) := by
      simpa only [Rat.divInt_eq_div, Int.cast_natCast] using hpq_eq
    have hpair := Rat.div_int_inj (by exact_mod_cast hq_pos) (by exact_mod_cast hpos_d)
      (by simpa using hcop_pq) (by simpa using hcop_cd) hdiv_eq
    exact_mod_cast hpair.2
  have hDelta_one : Delta = 1 := by
    have hmul : (d : ℤ) = (d : ℤ) * Delta := by simpa [hq_eq_d] using hd_eq
    have hzero : (d : ℤ) * (Delta - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hzero with hd | hdelta
    · have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast hpos_d.ne'
      exact False.elim (hdne hd)
    · omega
  simp only [Delta] at hDelta_one
  calc
    y.num * (x.den : ℤ) = (c : ℤ) * b := by simp [b, hc_eq]
    _ = (a : ℤ) * d + 1 := by nlinarith
    _ = x.num * (y.den : ℤ) + 1 := by simp [d, ha_eq]

/-- **Arithmetic characterization of Farey neighbors.** Let $n$ be a natural number and let
$x = a/b$ and $y = c/d$ be elements of the Farey set $F_n$, written in lowest terms with
$b, d > 0$. Then $x$ and $y$ are Farey neighbors of order $n$ if and only if $bc = ad + 1$ and
$n < b + d$. -/
theorem isFareyNeighbor_iff_det_and_sum {n : ℕ} {x y : ℚ}
    (hx : x ∈ fareyFinset n) (hy : y ∈ fareyFinset n) :
    IsFareyNeighbor n x y ↔
      y.num * (x.den : ℤ) = x.num * (y.den : ℤ) + 1 ∧ n < x.den + y.den := by
  constructor
  · intro h
    exact ⟨h.det_eq_one, neighbor_den_sum_gt n x y h⟩
  · rintro ⟨hdet, hsum⟩
    exact det_one_and_sum_gt_imp_neighbor n x y hx hy hdet hsum

/-- **The mediant of Farey neighbors is not in the Farey set.** Let $n$ be a natural number. If
$x$ and $y$ are Farey neighbors of order $n$, then the mediant of $x$ and $y$ does not belong to
the Farey set $F_n$. -/
theorem IsFareyNeighbor.mediant_not_mem {n : ℕ} {x y : ℚ}
    (h : IsFareyNeighbor n x y) : mediant x y ∉ fareyFinset n := by
  intro hmem
  exact h.2.2.2 _ hmem (mediant_between x y h.2.2.1)

/-- **Mediants that enter the next Farey set.** Let $n$ be a natural number and let $x$ and $y$
be Farey neighbors of order $n$ whose denominators in lowest terms sum to $n + 1$. Then the
mediant of $x$ and $y$ belongs to the Farey set $F_{n+1}$ and does not belong to $F_n$. -/
theorem IsFareyNeighbor.mediant_mem_succ {n : ℕ} {x y : ℚ}
    (h : IsFareyNeighbor n x y) (hsum : x.den + y.den = n + 1) :
    mediant x y ∈ fareyFinset (n + 1) ∧ mediant x y ∉ fareyFinset n :=
  ⟨mediant_mem_next_of_sum_eq n x y h.1 h.2.1 hsum, h.mediant_not_mem⟩

set_option maxHeartbeats 800000 in
-- The successor proof combines extremal finite-set choices with integer normalization.
/-- **Mediants generate the next Farey set.** Let $n \ge 1$ be a natural number. A rational
number $q$ belongs to the Farey set $F_{n+1}$ if and only if $q$ belongs to $F_n$, or there are
Farey neighbors $x$ and $y$ of order $n$ whose denominators in lowest terms sum to $n + 1$ such
that $q$ is the mediant of $x$ and $y$. -/
theorem farey_succ_generation {n : ℕ} (hn : 0 < n) (q : ℚ) :
    q ∈ fareyFinset (n + 1) ↔
      q ∈ fareyFinset n ∨
        ∃ x y : ℚ, IsFareyNeighbor n x y ∧ x.den + y.den = n + 1 ∧ q = mediant x y := by
  constructor
  · intro hq_succ
    by_cases hq_n : q ∈ fareyFinset n
    · exact Or.inl hq_n
    · right
      have hq0 : 0 ≤ q := (mem_fareyFinset_iff (n + 1) q).mp hq_succ |>.1
      have hq1 : q ≤ 1 := (mem_fareyFinset_iff (n + 1) q).mp hq_succ |>.2.1
      have hqden_le : q.den ≤ n + 1 := (mem_fareyFinset_iff (n + 1) q).mp hq_succ |>.2.2
      have hqden_gt : n < q.den := by
        by_contra hle
        have : q.den ≤ n := by omega
        exact hq_n ((mem_fareyFinset_iff n q).mpr ⟨hq0, hq1, this⟩)
      have hqden_eq : q.den = n + 1 := by omega
      have hq_ne_zero : q ≠ 0 := by
        intro hqz
        subst q
        apply hq_n
        rw [mem_fareyFinset_iff]
        simp
        omega
      have hq_ne_one : q ≠ 1 := by
        intro hqo
        subst q
        apply hq_n
        rw [mem_fareyFinset_iff]
        simp
        omega
      have hq_pos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq_ne_zero)
      have hq_lt_one : q < 1 := lt_of_le_of_ne hq1 hq_ne_one
      have h0_mem : (0 : ℚ) ∈ fareyFinset n := by
        rw [mem_fareyFinset_iff]
        simp
        omega
      have h1_mem : (1 : ℚ) ∈ fareyFinset n := by
        rw [mem_fareyFinset_iff]
        simp
        omega
      let lower := (fareyFinset n).filter (· < q)
      have hlower : lower.Nonempty := ⟨0, by simp [lower, h0_mem, hq_pos]⟩
      let x := lower.max' hlower
      have hx_lower : x ∈ lower := Finset.max'_mem _ _
      have hx_mem : x ∈ fareyFinset n := (Finset.mem_filter.mp hx_lower).1
      have hx_lt_q : x < q := (Finset.mem_filter.mp hx_lower).2
      have hx_max : ∀ r ∈ fareyFinset n, r < q → r ≤ x := by
        intro r hr hrq
        exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hr, hrq⟩)
      let upper := (fareyFinset n).filter (q < ·)
      have hupper : upper.Nonempty := ⟨1, by simp [upper, h1_mem, hq_lt_one]⟩
      let y := upper.min' hupper
      have hy_upper : y ∈ upper := Finset.min'_mem _ _
      have hy_mem : y ∈ fareyFinset n := (Finset.mem_filter.mp hy_upper).1
      have hq_lt_y : q < y := (Finset.mem_filter.mp hy_upper).2
      have hy_min : ∀ r ∈ fareyFinset n, q < r → y ≤ r := by
        intro r hr hqr
        exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hr, hqr⟩)
      have hxy_neighbor : IsFareyNeighbor n x y := by
        refine ⟨hx_mem, hy_mem, hx_lt_q.trans hq_lt_y, ?_⟩
        intro z hz ⟨hxz, hzy⟩
        rcases lt_trichotomy z q with hzq | rfl | hqz
        · exact (not_lt_of_ge (hx_max z hz hzq)) hxz
        · exact hq_n hz
        · exact (not_lt_of_ge (hy_min z hz hqz)) hzy
      have hdet_xy := hxy_neighbor.det_eq_one
      have hsum_gt := neighbor_den_sum_gt n x y hxy_neighbor
      have hA : 1 ≤ q.num * (x.den : ℤ) - x.num * (q.den : ℤ) := by
        have := (Rat.lt_iff x q).mp hx_lt_q
        omega
      have hB : 1 ≤ y.num * (q.den : ℤ) - q.num * (y.den : ℤ) := by
        have := (Rat.lt_iff q y).mp hq_lt_y
        omega
      have hid : (q.den : ℤ) *
          (y.num * (x.den : ℤ) - x.num * (y.den : ℤ)) =
          (y.den : ℤ) * (q.num * (x.den : ℤ) - x.num * (q.den : ℤ)) +
            (x.den : ℤ) * (y.num * (q.den : ℤ) - q.num * (y.den : ℤ)) := by
        ring
      have hdet : y.num * (x.den : ℤ) - x.num * (y.den : ℤ) = 1 := by omega
      have hxden_pos : (0 : ℤ) < x.den := by exact_mod_cast x.pos
      have hyden_pos : (0 : ℤ) < y.den := by exact_mod_cast y.pos
      have hle : (x.den : ℤ) + y.den ≤ q.den := by
        rw [hdet, mul_one] at hid
        nlinarith
      have hge : (q.den : ℤ) ≤ x.den + y.den := by
        exact_mod_cast (show q.den ≤ x.den + y.den by omega)
      have hsum_eq : x.den + y.den = n + 1 := by omega
      have hAeq : q.num * (x.den : ℤ) - x.num * (q.den : ℤ) = 1 := by
        rw [hdet, mul_one] at hid
        nlinarith
      have hq_num_eq : q.num = x.num + y.num := by
        have hqden : (q.den : ℤ) = (x.den : ℤ) + (y.den : ℤ) := by
          exact_mod_cast hqden_eq.trans hsum_eq.symm
        rw [hqden] at hAeq
        have hmul : (q.num - x.num - y.num) * (x.den : ℤ) = 0 := by
          nlinarith [hAeq, hdet]
        rcases mul_eq_zero.mp hmul with hnum | hden
        · omega
        · have : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_ne_zero
          exact False.elim (this hden)
      have hq_eq_mediant : q = mediant x y := by
        calc
          q = (q.num /. (q.den : ℤ) : ℚ) := (Rat.num_divInt_den q).symm
          _ = ((x.num + y.num) /. ((x.den + y.den : ℕ) : ℤ) : ℚ) := by
            rw [hq_num_eq, hqden_eq, hsum_eq]
          _ = mediant x y := rfl
      exact ⟨x, y, hxy_neighbor, hsum_eq, hq_eq_mediant⟩
  · rintro (hq | ⟨x, y, hxy, hsum, rfl⟩)
    · exact fareyFinset_mono (Nat.le_succ n) hq
    · exact mediant_mem_next_of_sum_eq n x y hxy.1 hxy.2.1 hsum

end Farey

end
