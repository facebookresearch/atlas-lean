/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.NumberTheory.QAnalogCollatz
public import MathlibExt.NumberTheory.QCollatzParityFlip
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Conjugacy between the q-Collatz map and the 2-adic 3x+1 map

This module proves `qCollatz_conjugate_twoAdicCollatz`: for odd $A$ and $B$,
the $q$-analog of the $3x+1$ map on $\mathbb{F}_2[[q]]$ is conjugate to the
$3x+1$ map on the $2$-adic integers $\mathbb{Z}_2$. The proof goes through
parity sequences: both maps induce bijections onto binary sequences, and the
bijection matching parity sequences intertwines the two maps.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*,
Journal of Integer Sequences 28 (2025), Article 25.6.8, Theorem 2.
-/

namespace MetaMathlibExt

@[expose] public section

open PowerSeries

/-- Parity sequence of the q-Collatz map: `qParitySeq A B y k` is the constant
coefficient of the `k`-th iterate of `qCollatz A B` applied to `y`. -/
private noncomputable def qParitySeq (A B y : PowerSeries (ZMod 2)) : ℕ → ZMod 2 :=
  fun k => constantCoeff ((qCollatz A B)^[k] y)

/-- Parity sequence of the 2-adic Collatz map: `zParitySeq x k` is the residue
modulo `2` of the `k`-th iterate of `twoAdicCollatz` applied to `x`. -/
private noncomputable def zParitySeq (x : ℤ_[2]) : ℕ → ZMod 2 :=
  fun k => PadicInt.toZMod (twoAdicCollatz^[k] x)

/-- In `ZMod 2`, two elements both different from a third are equal. -/
private theorem zmod_two_eq_of_ne {a b c : ZMod 2} (h1 : a ≠ b) (h2 : c ≠ b) : a = c := by
  have h : ∀ a b c : ZMod 2, a ≠ b → c ≠ b → a = c := by decide
  exact h a b c h1 h2

/-- Every element of `ZMod 2` is `0` or `1`. -/
private theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h a

/-- The parity sequence of `T_{A,B}(y)` is the tail of that of `y`. -/
private theorem qParitySeq_shift (A B y : PowerSeries (ZMod 2)) (k : ℕ) :
    qParitySeq A B (qCollatz A B y) k = qParitySeq A B y (k + 1) := by
  simp only [qParitySeq, ← Function.iterate_succ_apply]

/-- The parity sequence of `T(x)` is the tail of that of `x`. -/
private theorem zParitySeq_shift (x : ℤ_[2]) (k : ℕ) :
    zParitySeq (twoAdicCollatz x) k = zParitySeq x (k + 1) := by
  simp only [zParitySeq, ← Function.iterate_succ_apply]

/-- The shift of `u + X * v` is the shift of `u` plus `v`. -/
private theorem qShift_add_X_mul' (u v : PowerSeries (ZMod 2)) :
    qShift (u + X * v) = qShift u + v := by
  ext i
  simp [qShift, coeff_succ_X_mul]

/-- `T_{A,B}` applied to `u + X * v` splits over the two summands. -/
private theorem qCollatz_add_X_mul' (A B u v : PowerSeries (ZMod 2)) :
    qCollatz A B (u + X * v) =
      qCollatz A B u + (if constantCoeff u = 0 then 1 else A) * v := by
  by_cases hu : constantCoeff u = 0
  · simp [qCollatz, hu, qShift_add_X_mul']
  · have h : A * (u + X * v) + B = (A * u + B) + X * (A * v) := by ring
    simp [qCollatz, hu, h, qShift_add_X_mul']

/-- Iterates of `T_{A,B}` preserve the parity of a perturbation. This generalizes
`qCollatz_iterate_add_X_pow_mul` by tracking the exact constant term instead of
requiring the perturbation to be odd. -/
private theorem qCollatz_iterate_add_X_pow_mul' (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (n : ℕ) (U V : PowerSeries (ZMod 2))
    (k : ℕ) (hk : k ≤ n + 1) :
    ∃ W : PowerSeries (ZMod 2), constantCoeff W = constantCoeff V ∧
      (qCollatz A B)^[k] (U + X ^ (n + 1) * V) =
        (qCollatz A B)^[k] U + X ^ (n + 1 - k) * W := by
  induction k with
  | zero => exact ⟨V, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨W, hW, heq⟩ := ih (by omega)
    have hdeg : n + 1 - k = (n - k) + 1 := by omega
    have hA1 : constantCoeff A = 1 := by
      rcases zmod_two_eq_zero_or_one (constantCoeff A) with h | h
      · exact absurd h hA
      · exact h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', heq, hdeg, pow_succ',
      mul_assoc, qCollatz_add_X_mul']
    by_cases hu : constantCoeff ((qCollatz A B)^[k] U) = 0
    · exact ⟨W, hW, by simp [hu]⟩
    · exact ⟨A * W, by simp [map_mul, hA1, hW], by simp [hu, mul_left_comm]⟩

/-- Congruence modulo `q^{k+1}` determines the `k`-th parity. -/
private theorem qParitySeq_det (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (k : ℕ) (a b : PowerSeries (ZMod 2))
    (h : X ^ (k + 1) ∣ a - b) :
    qParitySeq A B a k = qParitySeq A B b k := by
  obtain ⟨e, he⟩ := h
  have ha : a = b + X ^ (k + 1) * e := by rw [← he]; abel
  obtain ⟨W, _, heq⟩ :=
    qCollatz_iterate_add_X_pow_mul' A B hA k b e k (Nat.le_add_right k 1)
  have hexp : k + 1 - k = 1 := by omega
  simp only [qParitySeq, ha, heq, map_add, hexp, pow_one, map_mul, constantCoeff_X,
    zero_mul, add_zero]

/-- Agreement of the first `k+1` parities gives congruence modulo `q^{k+1}`. -/
private theorem qParitySeq_det_conv (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (k : ℕ) (a b : PowerSeries (ZMod 2))
    (h : ∀ j ≤ k, qParitySeq A B a j = qParitySeq A B b j) :
    X ^ (k + 1) ∣ a - b := by
  induction k generalizing a b with
  | zero =>
    have h0 := h 0 le_rfl
    simp only [qParitySeq, Function.iterate_zero_apply] at h0
    have hexp : X ^ (0 + 1) = (X : PowerSeries (ZMod 2)) := by simp
    rw [hexp, X_dvd_iff, map_sub, sub_eq_zero]
    exact h0
  | succ k ih =>
    have hlow : ∀ j ≤ k, qParitySeq A B a j = qParitySeq A B b j :=
      fun j hj => h j (by omega)
    obtain ⟨e, he⟩ := ih a b hlow
    have ha : a = b + X ^ (k + 1) * e := by rw [← he]; abel
    have htop := h (k + 1) le_rfl
    rw [ha] at htop
    obtain ⟨W, hW, heq⟩ :=
      qCollatz_iterate_add_X_pow_mul' A B hA k b e (k + 1) le_rfl
    simp only [qParitySeq, heq, map_add, Nat.sub_self, pow_zero, one_mul, hW] at htop
    have he0 : constantCoeff e = 0 := add_eq_left.mp htop
    obtain ⟨e', he'⟩ := X_dvd_iff.mpr he0
    have hexp : X ^ (k + 1 + 1) = X ^ (k + 1) * (X : PowerSeries (ZMod 2)) :=
      pow_succ _ _
    exact ⟨e', by rw [he, he', hexp]; ring⟩

/-- Any target bit occurs as the `k`-th parity of a series congruent to `a`
modulo `q^k`. -/
private theorem qParitySeq_flip (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0)
    (k : ℕ) (a : PowerSeries (ZMod 2)) (t : ZMod 2) :
    ∃ a' : PowerSeries (ZMod 2), X ^ k ∣ a' - a ∧ qParitySeq A B a' k = t := by
  by_cases h : qParitySeq A B a k = t
  · exact ⟨a, by simp, h⟩
  · refine ⟨a + X ^ k * 1, by rw [add_sub_cancel_left]; exact dvd_mul_right _ _, ?_⟩
    have hne := qCollatz_iterate_parity_flip A B hA hB k a 1 (by simp)
    simp only [qParitySeq] at h ⊢
    exact zmod_two_eq_of_ne hne (Ne.symm h)

/-- Every finite parity pattern occurs. -/
private theorem qParitySeq_fin_realize (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0)
    (d : ℕ → ZMod 2) (n : ℕ) :
    ∃ a : PowerSeries (ZMod 2), ∀ j < n, qParitySeq A B a j = d j := by
  induction n with
  | zero => exact ⟨0, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨a', hdiv, htop⟩ := qParitySeq_flip A B hA hB n a (d n)
    refine ⟨a', fun j hj => ?_⟩
    by_cases hjn : j < n
    · have hdiv' : X ^ (j + 1) ∣ a' - a :=
        dvd_trans (pow_dvd_pow _ (by omega : j + 1 ≤ n)) hdiv
      rw [qParitySeq_det A B hA j a' a hdiv']
      exact ha j hjn
    · have hjn' : j = n := by omega
      rw [hjn']
      exact htop

/-- Coefficients below `n` vanish for multiples of `q^n`. -/
private theorem coeff_eq_zero_of_X_pow_dvd {d : PowerSeries (ZMod 2)} {n j : ℕ}
    (h : X ^ n ∣ d) (hj : j < n) : coeff j d = 0 := by
  obtain ⟨w, rfl⟩ := h
  have hle : ¬ n ≤ j := Nat.not_le.mpr hj
  simp [coeff_X_pow_mul', hle]

/-- A series whose first `n` coefficients vanish is a multiple of `q^n`. -/
private theorem X_pow_dvd_of_coeff_eq_zero (d : PowerSeries (ZMod 2)) (n : ℕ)
    (h : ∀ j < n, coeff j d = 0) : X ^ n ∣ d := by
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
    have h0 : constantCoeff d = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact h 0 (by omega)
    obtain ⟨e, rfl⟩ := X_dvd_iff.mpr h0
    have he : ∀ j < n, coeff j e = 0 := fun j hj => by
      have h' := h (j + 1) (by omega)
      rwa [coeff_succ_X_mul] at h'
    obtain ⟨e', he'⟩ := ih e he
    exact ⟨e', by rw [he', pow_succ']; ring⟩

/-- Power series are separated for the `q`-adic topology. -/
private theorem qSep (a b : PowerSeries (ZMod 2))
    (h : ∀ n, X ^ n ∣ a - b) : a = b := by
  apply PowerSeries.ext
  intro m
  have h' := coeff_eq_zero_of_X_pow_dvd (h (m + 1)) (by omega : m < m + 1)
  simpa [sub_eq_zero] using h'

/-- Consecutive coherence gives pairwise coherence. -/
private theorem qCoherent_pairwise (s : ℕ → PowerSeries (ZMod 2))
    (hcoh : ∀ n, X ^ n ∣ s (n + 1) - s n) (p q : ℕ) (h : p ≤ q) :
    X ^ p ∣ s q - s p := by
  induction q, h using Nat.le_induction with
  | base => simp
  | succ q hq ih =>
    have h1 : X ^ p ∣ s (q + 1) - s q :=
      dvd_trans (pow_dvd_pow _ hq) (hcoh q)
    have h2 : s (q + 1) - s p = (s (q + 1) - s q) + (s q - s p) := by abel
    rw [h2]
    exact dvd_add h1 ih

/-- Every coherent sequence of power series has a limit. -/
private theorem qCoherent_limit (s : ℕ → PowerSeries (ZMod 2))
    (hcoh : ∀ n, X ^ n ∣ s (n + 1) - s n) :
    ∃ a : PowerSeries (ZMod 2), ∀ n, X ^ n ∣ a - s n := by
  refine ⟨PowerSeries.mk (fun i => coeff i (s (i + 1))), fun n => ?_⟩
  apply X_pow_dvd_of_coeff_eq_zero
  intro j hj
  have hdiv := qCoherent_pairwise s hcoh (j + 1) n hj
  have hvan := coeff_eq_zero_of_X_pow_dvd hdiv (by omega : j < j + 1)
  have hmk : coeff j (PowerSeries.mk (fun i => coeff i (s (i + 1)))) =
      coeff j (s (j + 1)) := PowerSeries.coeff_mk _ _
  simp only [map_sub, hmk] at hvan ⊢
  rw [sub_eq_zero] at hvan ⊢
  exact hvan.symm

/-- The q-parity sequence map is injective. -/
private theorem qParitySeq_injective (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) : Function.Injective (qParitySeq A B) := by
  intro a b h
  apply qSep
  intro n
  cases n with
  | zero => simp
  | succ n =>
    refine qParitySeq_det_conv A B hA n a b fun j _ => ?_
    exact congrFun h j

/-- The q-parity sequence map is surjective. -/
private theorem qParitySeq_surjective (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    Function.Surjective (qParitySeq A B) := by
  intro d
  choose s hs using fun n => qParitySeq_fin_realize A B hA hB d n
  have hcoh : ∀ n, X ^ n ∣ s (n + 1) - s n := by
    intro n
    cases n with
    | zero => simp
    | succ n =>
      refine qParitySeq_det_conv A B hA n _ _ fun j hj => ?_
      rw [hs (n + 1 + 1) j (by omega), hs (n + 1) j (by omega)]
  obtain ⟨a, ha⟩ := qCoherent_limit s hcoh
  refine ⟨a, funext fun k => ?_⟩
  have hdiv := ha (k + 1)
  have hdet := qParitySeq_det A B hA k a (s (k + 1)) hdiv
  rw [hdet]
  exact hs (k + 1) k (by omega)

/-- The q-parity sequence map is bijective. -/
private theorem qParitySeq_bijective (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    Function.Bijective (qParitySeq A B) :=
  ⟨qParitySeq_injective A B hA, qParitySeq_surjective A B hA hB⟩

/-- Congruence modulo `2^n` in `ℤ₂` as divisibility. -/
private theorem toZModPow_eq_iff_dvd (n : ℕ) (x y : ℤ_[2]) :
    PadicInt.toZModPow n x = PadicInt.toZModPow n y ↔ (2 : ℤ_[2]) ^ n ∣ x - y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton]
  simp only [Nat.cast_ofNat]

/-- Congruence modulo `2^{n+1}` determines parity. -/
private theorem toZMod_eq_of_toZModPow_eq {n : ℕ} {x y : ℤ_[2]}
    (h : PadicInt.toZModPow (n + 1) x = PadicInt.toZModPow (n + 1) y) :
    PadicInt.toZMod x = PadicInt.toZMod y := by
  have hdvd : (2 : ℤ_[2]) ^ (n + 1) ∣ x - y :=
    (toZModPow_eq_iff_dvd _ _ _).mp h
  have h2 : (2 : ℤ_[2]) ∣ x - y :=
    dvd_trans (dvd_pow_self _ (by omega)) hdvd
  have hker : x - y ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    exact_mod_cast h2
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
  exact hker

/-- Three is a unit in `ℤ₂`. -/
private theorem isUnit_three : IsUnit (3 : ℤ_[2]) := by
  have h3 : PadicInt.toZMod (3 : ℤ_[2]) ≠ 0 := by rw [map_ofNat]; decide
  have hmem : (3 : ℤ_[2]) ∉ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [RingHom.mem_ker]
    exact h3
  rw [PadicInt.ker_toZMod] at hmem
  exact IsLocalRing.notMem_maximalIdeal.mp hmem

/-- The 2-adic Collatz map preserves congruence, losing one bit. -/
private theorem twoAdicCollatz_cong (n : ℕ) (x y : ℤ_[2])
    (h : PadicInt.toZModPow (n + 1) x = PadicInt.toZModPow (n + 1) y) :
    PadicInt.toZModPow n (twoAdicCollatz x) =
      PadicInt.toZModPow n (twoAdicCollatz y) := by
  have hpar : PadicInt.toZMod x = PadicInt.toZMod y :=
    toZMod_eq_of_toZModPow_eq h
  have hdvd : (2 : ℤ_[2]) ^ (n + 1) ∣ x - y := (toZModPow_eq_iff_dvd _ _ _).mp h
  have h2dvd : (2 : ℤ_[2]) ^ (n + 1) ∣ 2 * (twoAdicCollatz x - twoAdicCollatz y) := by
    by_cases hx : PadicInt.toZMod x = 0
    · have hy : PadicInt.toZMod y = 0 := by rw [← hpar]; exact hx
      have hxx := two_mul_twoAdicCollatz_of_even hx
      have hyy := two_mul_twoAdicCollatz_of_even hy
      have heq : 2 * (twoAdicCollatz x - twoAdicCollatz y) = x - y := by
        linear_combination hxx - hyy
      rw [heq]
      exact hdvd
    · have hy : PadicInt.toZMod y ≠ 0 := by rw [← hpar]; exact hx
      have hxx := two_mul_twoAdicCollatz_of_odd hx
      have hyy := two_mul_twoAdicCollatz_of_odd hy
      have heq : 2 * (twoAdicCollatz x - twoAdicCollatz y) = 3 * (x - y) := by
        linear_combination hxx - hyy
      rw [heq]
      exact dvd_mul_of_dvd_right hdvd _
  have hexp : (2 : ℤ_[2]) ^ (n + 1) = 2 * 2 ^ n := pow_succ' _ _
  rw [hexp] at h2dvd
  rw [toZModPow_eq_iff_dvd]
  exact (mul_dvd_mul_iff_left two_ne_zero).mp h2dvd

/-- Iterates of the 2-adic Collatz map preserve congruence, losing one bit per
iterate. -/
private theorem twoAdicCollatz_iter_cong (k m : ℕ) (x y : ℤ_[2])
    (h : PadicInt.toZModPow (m + k) x = PadicInt.toZModPow (m + k) y) :
    PadicInt.toZModPow m (twoAdicCollatz^[k] x) =
      PadicInt.toZModPow m (twoAdicCollatz^[k] y) := by
  induction k generalizing m x y with
  | zero => simpa using h
  | succ k ih =>
    have hexp : m + 1 + k = m + (k + 1) := by omega
    have h' := ih (m + 1) x y (by rw [hexp]; exact h)
    have h'' := twoAdicCollatz_cong m
      (twoAdicCollatz^[k] x) (twoAdicCollatz^[k] y) h'
    simpa [Function.iterate_succ_apply'] using h''

/-- The first `n` parities determine the residue modulo `2^n`. -/
private theorem zParitySeq_det (n : ℕ) (x y : ℤ_[2])
    (h : ∀ j < n, zParitySeq x j = zParitySeq y j) :
    PadicInt.toZModPow n x = PadicInt.toZModPow n y := by
  induction n generalizing x y with
  | zero =>
    rw [toZModPow_eq_iff_dvd]
    simp
  | succ n ih =>
    have h0 : PadicInt.toZMod x = PadicInt.toZMod y := by
      have h00 := h 0 (by omega)
      simpa [zParitySeq] using h00
    have htail : ∀ j < n, zParitySeq (twoAdicCollatz x) j =
        zParitySeq (twoAdicCollatz y) j := by
      intro j hj
      rw [zParitySeq_shift, zParitySeq_shift]
      exact h (j + 1) (by omega)
    have hcong := ih _ _ htail
    rw [toZModPow_eq_iff_dvd] at hcong ⊢
    obtain ⟨c, hc⟩ := hcong
    have hexp : (2 : ℤ_[2]) ^ (n + 1) = 2 * 2 ^ n := pow_succ' _ _
    by_cases hx : PadicInt.toZMod x = 0
    · have hy : PadicInt.toZMod y = 0 := by rw [← h0]; exact hx
      have hxx := two_mul_twoAdicCollatz_of_even hx
      have hyy := two_mul_twoAdicCollatz_of_even hy
      have hxy : x - y = 2 * (twoAdicCollatz x - twoAdicCollatz y) := by
        linear_combination -hxx + hyy
      refine ⟨c, ?_⟩
      rw [hxy, hc, hexp]
      ring
    · have hy : PadicInt.toZMod y ≠ 0 := by rw [← h0]; exact hx
      have hxx := two_mul_twoAdicCollatz_of_odd hx
      have hyy := two_mul_twoAdicCollatz_of_odd hy
      have h2 : 2 * (twoAdicCollatz x - twoAdicCollatz y) = 3 * (x - y) := by
        linear_combination hxx - hyy
      obtain ⟨u, hu⟩ := isUnit_three
      have hux : (↑(u⁻¹) : ℤ_[2]) * (3 * (x - y)) = x - y := by
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
      refine ⟨(↑(u⁻¹) : ℤ_[2]) * c, ?_⟩
      rw [← hux, ← h2, hc, hexp]
      ring

/-- Every finite parity pattern occurs for the 2-adic Collatz map. -/
private theorem zParitySeq_fin_realize (d : ℕ → ZMod 2) (n : ℕ) :
    ∃ x : ℤ_[2], ∀ j < n, zParitySeq x j = d j := by
  induction n generalizing d with
  | zero => exact ⟨0, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih (fun j => d (j + 1))
    have h2 : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by rw [map_ofNat]; decide
    rcases zmod_two_eq_zero_or_one (d 0) with hd0 | hd0
    · refine ⟨2 * y, fun j hj => ?_⟩
      have h2y : PadicInt.toZMod (2 * y) = 0 := by rw [map_mul, h2, zero_mul]
      have hTy : twoAdicCollatz (2 * y) = y :=
        mul_left_cancel₀ two_ne_zero (two_mul_twoAdicCollatz_of_even h2y)
      cases j with
      | zero => simp [zParitySeq, Function.iterate_zero_apply, h2y, hd0]
      | succ j =>
        rw [← zParitySeq_shift, hTy]
        exact hy j (by omega)
    · obtain ⟨u, hu⟩ := isUnit_three
      set x : ℤ_[2] := (↑(u⁻¹) : ℤ_[2]) * (2 * y - 1) with hx_def
      have hx3 : 3 * x = 2 * y - 1 := by
        rw [hx_def, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
      have h3 : PadicInt.toZMod (3 : ℤ_[2]) = 1 := by rw [map_ofNat]; decide
      have h10 : (0 : ZMod 2) - 1 = 1 := by decide
      have h2y : PadicInt.toZMod (2 * y) = 0 := by rw [map_mul, h2, zero_mul]
      have htx : PadicInt.toZMod x = 1 := by
        have hmap := congrArg PadicInt.toZMod hx3
        rw [map_mul, map_sub, h2y, map_one, h3, h10, one_mul] at hmap
        exact hmap
      have htx' : PadicInt.toZMod x ≠ 0 := by rw [htx]; decide
      have h3x1 : 3 * x + 1 = 2 * y := by linear_combination hx3
      have hTx : twoAdicCollatz x = y := by
        have hodd := two_mul_twoAdicCollatz_of_odd htx'
        rw [h3x1] at hodd
        exact mul_left_cancel₀ two_ne_zero hodd
      refine ⟨x, fun j hj => ?_⟩
      cases j with
      | zero => simp [zParitySeq, Function.iterate_zero_apply, htx, hd0]
      | succ j =>
        rw [← zParitySeq_shift, hTx]
        exact hy j (by omega)

/-- The 2-adic parity sequence map is injective. -/
private theorem zParitySeq_injective : Function.Injective zParitySeq := by
  intro x y h
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  apply zParitySeq_det
  intro j _
  exact congrFun h j

/-- The 2-adic parity sequence map is surjective. -/
private theorem zParitySeq_surjective : Function.Surjective zParitySeq := by
  intro d
  choose s hs using fun n => zParitySeq_fin_realize d n
  have hcoh : ∀ n, PadicInt.toZModPow n (s (n + 1)) =
      PadicInt.toZModPow n (s n) := by
    intro n
    apply zParitySeq_det
    intro j hj
    rw [hs (n + 1) j (by omega), hs n j hj]
  set f : ℕ → ℤ := fun n => ((PadicInt.toZModPow n (s n)).val : ℤ) with hf_def
  have e1 : ∀ i, ((f i : ℤ) : ZMod (2 ^ i)) = PadicInt.toZModPow i (s i) := by
    intro i
    have : NeZero (2 ^ i) := ⟨by positivity⟩
    simp only [hf_def]
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val (PadicInt.toZModPow i (s i))
  have e2 : ∀ i, ((f (i + 1) : ℤ) : ZMod (2 ^ i)) =
      PadicInt.toZModPow i (s i) := by
    intro i
    have : NeZero (2 ^ (i + 1)) := ⟨by positivity⟩
    have h1 : ((f (i + 1) : ℤ) : ZMod (2 ^ i)) =
        ZMod.cast (PadicInt.toZModPow (i + 1) (s (i + 1))) := by
      simp only [hf_def]
      rw [Int.cast_natCast]
      exact ZMod.natCast_val (R := ZMod (2 ^ i))
        (PadicInt.toZModPow (i + 1) (s (i + 1)))
    have hcc : ZMod.cast (PadicInt.toZModPow (i + 1) (s (i + 1))) =
        PadicInt.toZModPow i (s (i + 1)) :=
      PadicInt.cast_toZModPow _ _ (Nat.le_succ _) _
    rw [h1, hcc]
    exact hcoh i
  have hdiv : ∀ i, ((2 : ℕ) : ℤ) ^ i ∣ f (i + 1) - f i := by
    intro i
    have hcast : ((f i : ℤ) : ZMod (2 ^ i)) = ((f (i + 1) : ℤ) : ZMod (2 ^ i)) := by
      rw [e1, e2]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
    exact_mod_cast hcast
  have hseq := PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub f 2 hdiv
  obtain ⟨x, hx⟩ : ∃ x : ℤ_[2], ∀ n, PadicInt.toZModPow n x =
      PadicInt.toZModPow n (s n) := by
    refine ⟨PadicInt.ofIntSeq f hseq, fun n => ?_⟩
    have hspec := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub f 2 hdiv n
    exact hspec.trans (e1 n)
  refine ⟨x, funext fun k => ?_⟩
  have hmod : PadicInt.toZModPow (1 + k) x =
      PadicInt.toZModPow (1 + k) (s (1 + k)) := hx (1 + k)
  have hTk := twoAdicCollatz_iter_cong k 1 x (s (1 + k)) hmod
  have hpar : PadicInt.toZMod (twoAdicCollatz^[k] x) =
      PadicInt.toZMod (twoAdicCollatz^[k] (s (1 + k))) :=
    toZMod_eq_of_toZModPow_eq (n := 0) hTk
  have hsk : zParitySeq (s (1 + k)) k = d k := hs (1 + k) k (by omega)
  simp only [zParitySeq] at hsk ⊢
  rw [hpar]
  exact hsk

/-- The 2-adic parity sequence map is bijective. -/
private theorem zParitySeq_bijective : Function.Bijective zParitySeq :=
  ⟨zParitySeq_injective, zParitySeq_surjective⟩

/-- The conjugacy between the 2-adic Collatz map and the q-Collatz map:
transport the parity sequence from `ℤ₂` to `𝔽₂[[q]]`. -/
private noncomputable def conjEquiv (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    ℤ_[2] ≃ PowerSeries (ZMod 2) :=
  (Equiv.ofBijective zParitySeq zParitySeq_bijective).trans
    (Equiv.ofBijective (qParitySeq A B) (qParitySeq_bijective A B hA hB)).symm

/-- The conjugacy matches parity sequences. -/
private theorem conjEquiv_apply (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) (x : ℤ_[2]) :
    qParitySeq A B ((conjEquiv A B hA hB) x) = zParitySeq x := by
  have h := Equiv.ofBijective_apply_symm_apply (qParitySeq A B)
    (qParitySeq_bijective A B hA hB)
    ((Equiv.ofBijective zParitySeq zParitySeq_bijective) x)
  simpa [conjEquiv] using h

/-- The inverse conjugacy matches parity sequences. -/
private theorem conjEquiv_symm_apply (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0)
    (y : PowerSeries (ZMod 2)) :
    zParitySeq ((conjEquiv A B hA hB).symm y) = qParitySeq A B y := by
  have h := Equiv.ofBijective_apply_symm_apply zParitySeq zParitySeq_bijective
    ((Equiv.ofBijective (qParitySeq A B) (qParitySeq_bijective A B hA hB)) y)
  simpa [conjEquiv, Equiv.symm_trans_apply] using h

/-- **The $q$-Collatz map is conjugate to the $2$-adic $3x+1$ map.** Let $A$ and $B$ be odd
power series in $\mathbb{F}_2[[q]]$ (constant term $1$), let $T_{A,B}$ be the $q$-analog of the
$3x+1$ map on $\mathbb{F}_2[[q]]$, and let $T$ be the $3x+1$ map on the $2$-adic integers
$\mathbb{Z}_2$. Then there is a bijection $h : \mathbb{Z}_2 \to \mathbb{F}_2[[q]]$ with
$h^{-1}(T_{A,B}(h(x))) = T(x)$ for every $x \in \mathbb{Z}_2$.

Source: Kenneth G. Monks, *On q-Analogs of the 3x+1 Dynamical System*, Journal of Integer
Sequences 28 (2025), Article 25.6.8, Theorem 2 (`jis-2025-25.6.8-thm-2`). -/
public theorem qCollatz_conjugate_twoAdicCollatz (A B : PowerSeries (ZMod 2))
    (hA : constantCoeff A ≠ 0) (hB : constantCoeff B ≠ 0) :
    ∃ h : ℤ_[2] ≃ PowerSeries (ZMod 2),
      ∀ x, h.symm (qCollatz A B (h x)) = twoAdicCollatz x := by
  refine ⟨conjEquiv A B hA hB, fun x => ?_⟩
  apply zParitySeq_injective
  rw [conjEquiv_symm_apply]
  funext k
  rw [qParitySeq_shift, zParitySeq_shift, conjEquiv_apply]

end

end MetaMathlibExt
