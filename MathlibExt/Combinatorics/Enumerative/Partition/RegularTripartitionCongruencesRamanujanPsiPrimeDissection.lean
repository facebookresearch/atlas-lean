/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import MathlibExt.Combinatorics.Enumerative.Partition.RegularTripartitionCongruences
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Cui–Gu `p`-dissection of `ψ(q)`

This file proves the Cui–Gu `p`-dissection of Ramanujan's `ψ` function at odd primes:
`ψ(q) = f(q, q^3)` splits into `(p-1)/2` theta-function terms plus a `ψ(q^{p^2})` term,
and no triangular number `(m^2+m)/2` with `m ≤ (p-3)/2` is congruent to `(p^2-1)/8`
modulo `p`.

## Main results

* `ramanujanPsi_prime_dissection` — the dissection identity and non-congruence above.

Statements from Mohammed L. Nadji and Moussa Ahmia, *Congruences for `l`-Regular
Tripartitions for `l` in `{2,3}`*, INTEGERS 24 (2024), Article A86.
Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 4, eq. (7) (`integers-2024-A86-lem-4`),
quoting S. Cui and N. Gu, *Arithmetic Properties of ℓ-Regular Partitions*, Adv. Appl. Math. 51
(2013), 507–523, Theorem 2.1.
-/

namespace MetaMathlibExt

@[expose] public section

/-! ## Triangular index equivalence. -/

private def triIndexFun (n : ℤ) : ℕ :=
  if 1 ≤ n then (2 * n - 1).toNat else (-2 * n).toNat

private def triIndexInv (j : ℕ) : ℤ :=
  if j % 2 = 0 then -(j / 2 : ℕ) else ((j + 1) / 2 : ℕ)

private theorem triIndex_left_inv (n : ℤ) : triIndexInv (triIndexFun n) = n := by
  unfold triIndexFun triIndexInv
  split_ifs <;> omega

private theorem triIndex_right_inv (j : ℕ) : triIndexFun (triIndexInv j) = j := by
  unfold triIndexFun triIndexInv
  split_ifs <;> omega

private def triIndex : ℤ ≃ ℕ where
  toFun := triIndexFun
  invFun := triIndexInv
  left_inv := triIndex_left_inv
  right_inv := triIndex_right_inv

/-! ## Halving lemmas. -/

/-- Twice the natural half of an even nonnegative integer is the integer. -/
private theorem two_mul_toNat_ediv_two {a : ℤ} (h0 : 0 ≤ a) (h2 : 2 ∣ a) :
    2 * ((((a / 2).toNat : ℕ)) : ℤ) = a := by
  have hnn : 0 ≤ a / 2 := Int.ediv_nonneg h0 (by norm_num)
  rw [Int.toNat_of_nonneg hnn]
  exact Int.mul_ediv_cancel' h2

private theorem nn_mul_succ (m : ℤ) : 0 ≤ m * (m + 1) := by
  by_cases h : 0 ≤ m
  · exact mul_nonneg h (by omega)
  · push Not at h
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h) (by omega)

private theorem nn_mul_pred (m : ℤ) : 0 ≤ m * (m - 1) := by
  by_cases h : 0 ≤ m
  · by_cases h0 : m = 0
    · simp [h0]
    · have h1 : 1 ≤ m := by omega
      exact mul_nonneg h (by omega)
  · push Not at h
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt h) (by omega)

private theorem ev_mul_succ (m : ℤ) : Even (m * (m + 1)) := by
  have h : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rw [even_iff_two_dvd]
  rcases h with h | h
  · exact Dvd.dvd.mul_right (by omega : (2 : ℤ) ∣ m) _
  · exact Dvd.dvd.mul_left (by omega : (2 : ℤ) ∣ m + 1) _

private theorem ev_mul_pred (m : ℤ) : Even (m * (m - 1)) := by
  have h : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rw [even_iff_two_dvd]
  rcases h with h | h
  · exact Dvd.dvd.mul_right (by omega : (2 : ℤ) ∣ m) _
  · exact Dvd.dvd.mul_left (by omega : (2 : ℤ) ∣ m - 1) _

/-! ## The `ψ` summand is a triangular power of `q`. -/

/-- The exponent of the `ψ` summand equals the triangular number of the index. -/
private theorem thetaExp_eq (n : ℤ) :
    (n * (n + 1) / 2).toNat + 3 * (n * (n - 1) / 2).toNat
      = triIndexFun n * (triIndexFun n + 1) / 2 := by
  have h1 := two_mul_toNat_ediv_two (nn_mul_succ n) (even_iff_two_dvd.mp (ev_mul_succ n))
  have h2 := two_mul_toNat_ediv_two (nn_mul_pred n) (even_iff_two_dvd.mp (ev_mul_pred n))
  have hdiv : 2 ∣ triIndexFun n * (triIndexFun n + 1) :=
    even_iff_two_dvd.mp (Nat.even_mul_succ_self _)
  have hmul : 2 * (triIndexFun n * (triIndexFun n + 1) / 2)
      = triIndexFun n * (triIndexFun n + 1) := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdiv
  have hcast : (2 : ℤ) * (((triIndexFun n * (triIndexFun n + 1) / 2 : ℕ)) : ℤ)
      = ((triIndexFun n : ℕ) : ℤ) * (((triIndexFun n : ℕ) : ℤ) + 1) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) hmul
    simpa [Nat.cast_mul, Nat.cast_add] using h
  have hE : (2 : ℤ) * (((((n * (n + 1) / 2).toNat
      + 3 * (n * (n - 1) / 2).toNat : ℕ))) : ℤ) = 4 * n * n - 2 * n := by
    push_cast
    linear_combination h1 + 3 * h2
  have hT : (2 : ℤ) * (((triIndexFun n * (triIndexFun n + 1) / 2 : ℕ)) : ℤ)
      = 4 * n * n - 2 * n := by
    by_cases hn : 1 ≤ n
    · have hif : triIndexFun n = (2 * n - 1).toNat := by
        unfold triIndexFun
        simp [hn]
      have hφ : ((triIndexFun n : ℕ) : ℤ) = 2 * n - 1 := by
        rw [hif]
        exact Int.toNat_of_nonneg (by omega)
      rw [hφ] at hcast
      linear_combination hcast
    · have hif : triIndexFun n = (-2 * n).toNat := by
        unfold triIndexFun
        simp [hn]
      have hφ : ((triIndexFun n : ℕ) : ℤ) = -2 * n := by
        rw [hif]
        exact Int.toNat_of_nonneg (by omega)
      rw [hφ] at hcast
      linear_combination hcast
  have hEq : (((((n * (n + 1) / 2).toNat
      + 3 * (n * (n - 1) / 2).toNat : ℕ))) : ℤ)
      = (((triIndexFun n * (triIndexFun n + 1) / 2 : ℕ)) : ℤ) := by
    linarith
  exact Nat.cast_injective hEq

private theorem thetaTerm_psi_pow (q : ℂ) (n : ℤ) :
    ramanujanThetaTerm q (q ^ 3) n
      = q ^ (triIndexFun n * (triIndexFun n + 1) / 2) := by
  unfold ramanujanThetaTerm
  rw [← pow_mul, ← pow_add]
  congr 1
  exact thetaExp_eq n

/-! ## Summability of the `ψ` series. -/

private theorem summable_natAbs_pow (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => r ^ n.natAbs) := by
  apply Summable.of_nat_of_neg
  · have hgeom := summable_geometric_of_lt_one hr0 hr1
    refine Summable.congr hgeom (fun n => ?_)
    rw [Int.natAbs_natCast]
  · have hgeom := summable_geometric_of_lt_one hr0 hr1
    refine Summable.congr hgeom (fun n => ?_)
    rw [Int.natAbs_neg, Int.natAbs_natCast]

/-- The `ψ` exponent dominates the absolute value of the index. -/
private theorem thetaExp_ge_natAbs (n : ℤ) :
    n.natAbs ≤ (n * (n + 1) / 2).toNat + 3 * (n * (n - 1) / 2).toNat := by
  have h1 := two_mul_toNat_ediv_two (nn_mul_succ n) (even_iff_two_dvd.mp (ev_mul_succ n))
  have h2 := two_mul_toNat_ediv_two (nn_mul_pred n) (even_iff_two_dvd.mp (ev_mul_pred n))
  by_cases hn0 : n = 0
  · subst hn0
    decide
  · by_cases hnneg : 0 ≤ n
    · have hn1 : 1 ≤ n := by omega
      have hnat : ((n.natAbs : ℕ) : ℤ) = n := Int.natAbs_of_nonneg hnneg
      have h3 : (0 : ℤ) ≤ n * (n - 1) := mul_nonneg hnneg (by omega)
      have h4 : n * (n + 1) + 3 * (n * (n - 1)) - 2 * n = 4 * (n * (n - 1)) := by
        ring
      have hle : ((n.natAbs : ℕ) : ℤ)
          ≤ (((n * (n + 1) / 2).toNat + 3 * (n * (n - 1) / 2).toNat : ℕ) : ℤ) := by
        rw [hnat]
        push_cast
        linarith
      exact Nat.cast_le.mp hle
    · push Not at hnneg
      have hnat : ((n.natAbs : ℕ) : ℤ) = -n := by
        have h := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ -n by omega)
        rwa [Int.natAbs_neg] at h
      have hsq : (0 : ℤ) ≤ n * n := mul_self_nonneg n
      have h4 : n * (n + 1) + 3 * (n * (n - 1)) + 2 * n = 4 * (n * n) := by ring
      have hle : ((n.natAbs : ℕ) : ℤ)
          ≤ (((n * (n + 1) / 2).toNat + 3 * (n * (n - 1) / 2).toNat : ℕ) : ℤ) := by
        rw [hnat]
        push_cast
        linarith
      exact Nat.cast_le.mp hle

private theorem summable_psi (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (ramanujanThetaTerm q (q ^ 3)) := by
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg _
  refine Summable.of_norm_bounded (summable_natAbs_pow _ hr0 hq) (fun n => ?_)
  have hE := thetaExp_ge_natAbs n
  have hnorm : ‖ramanujanThetaTerm q (q ^ 3) n‖
      = ‖q‖ ^ ((n * (n + 1) / 2).toNat + 3 * (n * (n - 1) / 2).toNat) := by
    unfold ramanujanThetaTerm
    rw [norm_mul, norm_pow, norm_pow, norm_pow, ← pow_mul, ← pow_add]
  rw [hnorm]
  exact pow_le_pow_of_le_one hr0 hq.le hE

/-! ## The dissection equivalence. -/

/-- Forward map of the dissection: split `j` by its remainder mod `p`. -/
private def dissectToFun (p t : ℕ) (hpt : p = 2 * t + 1) (j : ℕ) :
    (Fin t × ℤ) ⊕ ℤ :=
  if _h1 : j % p < t then Sum.inl (⟨j % p, _h1⟩, ((j / p : ℕ) : ℤ))
  else if _h2 : j % p = t then Sum.inr (triIndexInv (j / p))
  else Sum.inl (⟨p - 1 - j % p, by
    have hrp : j % p < p := Nat.mod_lt j (by omega)
    omega⟩, (-1 - ((j / p : ℕ) : ℤ)))

/-- Backward map of the dissection. -/
private def dissectInvFun (p t : ℕ) (x : (Fin t × ℤ) ⊕ ℤ) : ℕ :=
  match x with
  | Sum.inl (k, m) =>
    if 0 ≤ m then p * m.toNat + k.val else p * (-1 - m).toNat + (p - 1 - k.val)
  | Sum.inr n => p * triIndexFun n + t

private theorem dissectDivAdd (p X Y : ℕ) (hp0 : 0 < p) (hY : Y < p) :
    (p * X + Y) / p = X ∧ (p * X + Y) % p = Y := by
  constructor
  · have h := Nat.add_mul_div_left Y X hp0
    rw [show p * X + Y = Y + p * X from add_comm _ _, h,
      Nat.div_eq_of_lt hY, zero_add]
  · have h := Nat.add_mul_mod_self_left Y p X
    rw [show p * X + Y = Y + p * X from add_comm _ _, h, Nat.mod_eq_of_lt hY]

private theorem dissect_left_inv (p t : ℕ) (hpt : p = 2 * t + 1) (j : ℕ) :
    dissectInvFun p t (dissectToFun p t hpt j) = j := by
  have hp0 : 0 < p := by omega
  unfold dissectToFun
  split_ifs with h1 h2
  · unfold dissectInvFun
    dsimp only
    split_ifs with h3
    · rw [Int.toNat_natCast]
      exact Nat.div_add_mod j p
    · exact False.elim (h3 (Nat.cast_nonneg _))
  · unfold dissectInvFun
    dsimp only
    rw [triIndex_right_inv]
    have hdm := Nat.div_add_mod j p
    omega
  · unfold dissectInvFun
    dsimp only
    split_ifs with h3
    · have hnn : (0 : ℤ) ≤ ((j / p : ℕ) : ℤ) := Nat.cast_nonneg _
      omega
    · have hm : (-1 - (-1 - (((j / p : ℕ)) : ℤ))) = (((j / p : ℕ)) : ℤ) := by ring
      rw [hm, Int.toNat_natCast]
      have hrp : j % p < p := Nat.mod_lt j hp0
      have hsub : p - 1 - (p - 1 - j % p) = j % p := by omega
      rw [hsub]
      exact Nat.div_add_mod j p

private theorem dissect_right_inv (p t : ℕ) (hpt : p = 2 * t + 1)
    (x : (Fin t × ℤ) ⊕ ℤ) :
    dissectToFun p t hpt (dissectInvFun p t x) = x := by
  have hp0 : 0 < p := by omega
  have htp : t < p := by omega
  cases x with
  | inl y =>
    obtain ⟨k, m⟩ := y
    have hklt := k.isLt
    unfold dissectInvFun
    dsimp only
    split_ifs with hm
    · have hkp : k.val < p := lt_trans hklt htp
      have hdiv := (dissectDivAdd p m.toNat k.val hp0 hkp).1
      have hmod := (dissectDivAdd p m.toNat k.val hp0 hkp).2
      unfold dissectToFun
      split_ifs with h1 h2
      · have hF : (⟨(p * m.toNat + k.val) % p, h1⟩ : Fin t) = k := by
          apply Fin.ext
          exact hmod
        have hM : (↑((p * m.toNat + k.val) / p) : ℤ) = m := by
          rw [hdiv]
          exact Int.toNat_of_nonneg hm
        rw [hF, hM]
      · rw [hmod] at h2
        exact False.elim (hklt.ne h2)
      · rw [hmod] at h1
        exact False.elim (h1 hklt)
    · have hkp1 : p - 1 - k.val < p := by omega
      have hdiv := (dissectDivAdd p (-1 - m).toNat (p - 1 - k.val) hp0 hkp1).1
      have hmod := (dissectDivAdd p (-1 - m).toNat (p - 1 - k.val) hp0 hkp1).2
      have hgt : t < p - 1 - k.val := by omega
      unfold dissectToFun
      split_ifs with h1 h2
      · rw [hmod] at h1
        exact absurd h1 (not_lt.mpr hgt.le)
      · rw [hmod] at h2
        exact absurd h2 (ne_of_gt hgt)
      · have hval : p - 1 - (p * (-1 - m).toNat + (p - 1 - k.val)) % p = k.val := by
          rw [hmod]
          omega
        have hneg : (0 : ℤ) ≤ -1 - m := by omega
        have htonat : ((((-1 - m).toNat : ℕ)) : ℤ) = -1 - m :=
          Int.toNat_of_nonneg hneg
        have hM : (-1 - (↑((p * (-1 - m).toNat + (p - 1 - k.val)) / p) : ℤ)) = m := by
          rw [hdiv, htonat]
          ring
        refine congrArg Sum.inl (Prod.ext_iff.mpr ⟨?_, ?_⟩)
        · apply Fin.ext
          exact hval
        · exact hM
  | inr n =>
    have hdiv := (dissectDivAdd p (triIndexFun n) t hp0 htp).1
    have hmod := (dissectDivAdd p (triIndexFun n) t hp0 htp).2
    unfold dissectInvFun
    dsimp only
    unfold dissectToFun
    split_ifs with h1
    · rw [hmod] at h1
      exact absurd h1 (lt_irrefl t)
    · congr 1
      rw [hdiv]
      exact triIndex_left_inv n

/-- The dissection equivalence `ℕ ≃ (Fin t × ℤ) ⊕ ℤ`. -/
private def dissectEquiv (p t : ℕ) (hpt : p = 2 * t + 1) :
    ℕ ≃ (Fin t × ℤ) ⊕ ℤ where
  toFun := dissectToFun p t hpt
  invFun := dissectInvFun p t
  left_inv := dissect_left_inv p t hpt
  right_inv := dissect_right_inv p t hpt

/-! ## Theta terms with `q`-power bases are `q`-powers. -/

private theorem thetaTerm_pow_base (q : ℂ) (A B : ℕ) (m : ℤ) :
    ramanujanThetaTerm (q ^ A) (q ^ B) m
      = q ^ (A * (m * (m + 1) / 2).toNat + B * (m * (m - 1) / 2).toNat) := by
  unfold ramanujanThetaTerm
  rw [← pow_mul, ← pow_mul, ← pow_add]

/-! ## Exponent identities. -/

/-- Combine doubled-exponent equations into a triangular identity. -/
private theorem exp_combine {C A B E1 E2 T : ℕ} {R P P' Q1 Q2 S : ℤ}
    (hc : (2 : ℤ) * (C : ℤ) = R)
    (hA : (2 : ℤ) * (A : ℤ) = P)
    (hB : (2 : ℤ) * (B : ℤ) = P')
    (hE1 : (2 : ℤ) * (E1 : ℤ) = Q1)
    (hE2 : (2 : ℤ) * (E2 : ℤ) = Q2)
    (hT : (2 : ℤ) * (T : ℤ) = S)
    (hpoly : 2 * R + P * Q1 + P' * Q2 - 2 * S = 0) :
    C + (A * E1 + B * E2) = T := by
  have h4 : (4 : ℤ) * ((C + (A * E1 + B * E2) : ℕ) : ℤ)
      = (4 : ℤ) * ((T : ℕ) : ℤ) := by
    push_cast
    linear_combination 2 * hc + (2 * (E1 : ℤ)) * hA + P * hE1
      + (2 * (E2 : ℤ)) * hB + P' * hE2 - 2 * hT + hpoly
  have hEq : ((C + (A * E1 + B * E2) : ℕ) : ℤ) = ((T : ℕ) : ℤ) := by
    linarith
  exact Nat.cast_injective hEq

/-- Case `r < t`: the `(r, a)` exponent with `a ≥ 0` is triangular. -/
private theorem caseA_exp (p t r a j : ℕ) (hpt : p = 2 * t + 1) (hodd : Odd p)
    (hr : r < t) (hj : p * a + r = j) :
    r * (r + 1) / 2
        + ((p ^ 2 + (2 * r + 1) * p) / 2 * ((a : ℤ) * ((a : ℤ) + 1) / 2).toNat
          + (p ^ 2 - (2 * r + 1) * p) / 2 * (((a : ℤ) * ((a : ℤ) - 1) / 2).toNat))
      = j * (j + 1) / 2 := by
  have h2rp : 2 * r + 1 ≤ p := by omega
  have hle : (2 * r + 1) * p ≤ p ^ 2 := by
    calc (2 * r + 1) * p ≤ p * p := by gcongr
      _ = p ^ 2 := by ring
  have hoddP2 : Odd (p ^ 2) := hodd.pow
  have hoddX : Odd ((2 * r + 1) * p) := Odd.mul ⟨r, rfl⟩ hodd
  have hdvdA : 2 ∣ p ^ 2 + (2 * r + 1) * p :=
    even_iff_two_dvd.mp (Odd.add_odd hoddP2 hoddX)
  have hdvdC : 2 ∣ r * (r + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self r)
  have hdvdT : 2 ∣ j * (j + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self j)
  obtain ⟨a2, ha2⟩ := hoddP2
  obtain ⟨b2, hb2⟩ := hoddX
  have hdvdB : 2 ∣ p ^ 2 - (2 * r + 1) * p := ⟨a2 - b2, by omega⟩
  have hmulC : 2 * (r * (r + 1) / 2) = r * (r + 1) := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdC
  have hc : (2 : ℤ) * ((r * (r + 1) / 2 : ℕ) : ℤ)
      = (r : ℤ) * ((r : ℤ) + 1) := by
    exact_mod_cast hmulC
  have hmulA : 2 * ((p ^ 2 + (2 * r + 1) * p) / 2) = p ^ 2 + (2 * r + 1) * p := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdA
  have hA : (2 : ℤ) * (((p ^ 2 + (2 * r + 1) * p) / 2 : ℕ) : ℤ)
      = (p : ℤ) ^ 2 + (2 * (r : ℤ) + 1) * (p : ℤ) := by
    exact_mod_cast hmulA
  have hmulB : 2 * ((p ^ 2 - (2 * r + 1) * p) / 2) = p ^ 2 - (2 * r + 1) * p := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdB
  have hB : (2 : ℤ) * (((p ^ 2 - (2 * r + 1) * p) / 2 : ℕ) : ℤ)
      = (p : ℤ) ^ 2 - (2 * (r : ℤ) + 1) * (p : ℤ) := by
    have hcast := congrArg (Nat.cast : ℕ → ℤ) hmulB
    rw [Nat.cast_sub hle] at hcast
    push_cast at hcast
    exact hcast
  have hmulT : 2 * (j * (j + 1) / 2) = j * (j + 1) := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdT
  have hT0 : (2 : ℤ) * ((j * (j + 1) / 2 : ℕ) : ℤ)
      = (j : ℤ) * ((j : ℤ) + 1) := by
    exact_mod_cast hmulT
  have hjZ : ((j : ℕ) : ℤ) = (p : ℤ) * (a : ℤ) + (r : ℤ) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) hj.symm
    push_cast at h
    exact h
  have hT : (2 : ℤ) * ((j * (j + 1) / 2 : ℕ) : ℤ)
      = ((p : ℤ) * (a : ℤ) + (r : ℤ)) * (((p : ℤ) * (a : ℤ) + (r : ℤ)) + 1) := by
    rw [hjZ] at hT0
    exact hT0
  have hE1 := two_mul_toNat_ediv_two (nn_mul_succ ((a : ℤ)))
    (even_iff_two_dvd.mp (ev_mul_succ ((a : ℤ))))
  have hE2 := two_mul_toNat_ediv_two (nn_mul_pred ((a : ℤ)))
    (even_iff_two_dvd.mp (ev_mul_pred ((a : ℤ))))
  have hpoly : 2 * ((r : ℤ) * ((r : ℤ) + 1))
      + ((p : ℤ) ^ 2 + (2 * (r : ℤ) + 1) * (p : ℤ)) * ((a : ℤ) * (((a : ℤ)) + 1))
      + ((p : ℤ) ^ 2 - (2 * (r : ℤ) + 1) * (p : ℤ)) * ((a : ℤ) * (((a : ℤ)) - 1))
      - 2 * (((p : ℤ) * (a : ℤ) + (r : ℤ))
        * (((p : ℤ) * (a : ℤ) + (r : ℤ)) + 1)) = 0 := by
    ring
  exact exp_combine hc hA hB hE1 hE2 hT hpoly

/-- Case `r > t`: the complementary exponent with `m < 0` is triangular. -/
private theorem caseB_exp (p t r a j k : ℕ) (hpt : p = 2 * t + 1) (hodd : Odd p)
    (hr : t < r) (hk : k + r + 1 = p) (hj : p * a + r = j) :
    k * (k + 1) / 2
        + ((p ^ 2 + (2 * k + 1) * p) / 2
            * ((-1 - (a : ℤ)) * ((-1 - (a : ℤ)) + 1) / 2).toNat
          + (p ^ 2 - (2 * k + 1) * p) / 2
            * (((-1 - (a : ℤ)) * ((-1 - (a : ℤ)) - 1) / 2).toNat))
      = j * (j + 1) / 2 := by
  have hkt : k < t := by omega
  have h2kp : 2 * k + 1 ≤ p := by omega
  have hle : (2 * k + 1) * p ≤ p ^ 2 := by
    calc (2 * k + 1) * p ≤ p * p := by gcongr
      _ = p ^ 2 := by ring
  have hoddP2 : Odd (p ^ 2) := hodd.pow
  have hoddX : Odd ((2 * k + 1) * p) := Odd.mul ⟨k, rfl⟩ hodd
  have hdvdA : 2 ∣ p ^ 2 + (2 * k + 1) * p :=
    even_iff_two_dvd.mp (Odd.add_odd hoddP2 hoddX)
  have hdvdC : 2 ∣ k * (k + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self k)
  have hdvdT : 2 ∣ j * (j + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self j)
  obtain ⟨a2, ha2⟩ := hoddP2
  obtain ⟨b2, hb2⟩ := hoddX
  have hdvdB : 2 ∣ p ^ 2 - (2 * k + 1) * p := ⟨a2 - b2, by omega⟩
  have hmulC : 2 * (k * (k + 1) / 2) = k * (k + 1) := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdC
  have hc : (2 : ℤ) * ((k * (k + 1) / 2 : ℕ) : ℤ)
      = (k : ℤ) * ((k : ℤ) + 1) := by
    exact_mod_cast hmulC
  have hmulA : 2 * ((p ^ 2 + (2 * k + 1) * p) / 2) = p ^ 2 + (2 * k + 1) * p := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdA
  have hA : (2 : ℤ) * (((p ^ 2 + (2 * k + 1) * p) / 2 : ℕ) : ℤ)
      = (p : ℤ) ^ 2 + (2 * (k : ℤ) + 1) * (p : ℤ) := by
    exact_mod_cast hmulA
  have hmulB : 2 * ((p ^ 2 - (2 * k + 1) * p) / 2) = p ^ 2 - (2 * k + 1) * p := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdB
  have hB : (2 : ℤ) * (((p ^ 2 - (2 * k + 1) * p) / 2 : ℕ) : ℤ)
      = (p : ℤ) ^ 2 - (2 * (k : ℤ) + 1) * (p : ℤ) := by
    have hcast := congrArg (Nat.cast : ℕ → ℤ) hmulB
    rw [Nat.cast_sub hle] at hcast
    push_cast at hcast
    exact hcast
  have hmulT : 2 * (j * (j + 1) / 2) = j * (j + 1) := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdT
  have hT0 : (2 : ℤ) * ((j * (j + 1) / 2 : ℕ) : ℤ)
      = (j : ℤ) * ((j : ℤ) + 1) := by
    exact_mod_cast hmulT
  have hjZ : ((j : ℕ) : ℤ) = (p : ℤ) * (a : ℤ) + (r : ℤ) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) hj.symm
    push_cast at h
    exact h
  have hT : (2 : ℤ) * ((j * (j + 1) / 2 : ℕ) : ℤ)
      = ((p : ℤ) * (a : ℤ) + (r : ℤ)) * (((p : ℤ) * (a : ℤ) + (r : ℤ)) + 1) := by
    rw [hjZ] at hT0
    exact hT0
  have hE1 := two_mul_toNat_ediv_two (nn_mul_succ (-1 - (a : ℤ)))
    (even_iff_two_dvd.mp (ev_mul_succ (-1 - (a : ℤ))))
  have hE2 := two_mul_toNat_ediv_two (nn_mul_pred (-1 - (a : ℤ)))
    (even_iff_two_dvd.mp (ev_mul_pred (-1 - (a : ℤ))))
  have hkEq : (k : ℤ) = (p : ℤ) - (r : ℤ) - 1 := by omega
  have hpoly : 2 * ((k : ℤ) * ((k : ℤ) + 1))
      + ((p : ℤ) ^ 2 + (2 * (k : ℤ) + 1) * (p : ℤ))
        * ((-1 - (a : ℤ)) * ((-1 - (a : ℤ)) + 1))
      + ((p : ℤ) ^ 2 - (2 * (k : ℤ) + 1) * (p : ℤ))
        * ((-1 - (a : ℤ)) * ((-1 - (a : ℤ)) - 1))
      - 2 * (((p : ℤ) * (a : ℤ) + (r : ℤ))
        * (((p : ℤ) * (a : ℤ) + (r : ℤ)) + 1)) = 0 := by
    rw [hkEq]
    ring
  exact exp_combine hc hA hB hE1 hE2 hT hpoly

/-- Combine doubled middle-class equations into a triangular identity. -/
private theorem inr_combine {C Ta Tj P2n : ℕ} {P8 P2 PTa Q : ℤ}
    (h8c : (8 : ℤ) * (C : ℤ) = P8)
    (hTa : (2 : ℤ) * (Ta : ℤ) = PTa)
    (h8Tj : (8 : ℤ) * (Tj : ℤ) = Q)
    (hP2 : ((P2n : ℕ) : ℤ) = P2)
    (hpoly : P8 + 4 * P2 * PTa - Q = 0) :
    C + P2n * Ta = Tj := by
  have h8 : (8 : ℤ) * ((C + P2n * Ta : ℕ) : ℤ) = (8 : ℤ) * ((Tj : ℕ) : ℤ) := by
    push_cast
    linear_combination h8c + (4 * P2) * hTa - h8Tj + (8 * (Ta : ℤ)) * hP2 + hpoly
  have hEq : ((C + P2n * Ta : ℕ) : ℤ) = ((Tj : ℕ) : ℤ) := by
    linarith
  exact Nat.cast_injective hEq

/-- The middle-class exponent is triangular. -/
private theorem inrExpEq (p t a j : ℕ) (hpt : p = 2 * t + 1) (hodd : Odd p)
    (hj : p * a + t = j) :
    (p ^ 2 - 1) / 8 + p ^ 2 * (a * (a + 1) / 2) = j * (j + 1) / 2 := by
  have hp1 : 1 ≤ p := by omega
  have hle1 : 1 ≤ p ^ 2 := by
    calc (1 : ℕ) = 1 ^ 2 := by ring
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp1 2
  have hdiv8 : 8 ∣ p ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd hodd
  have hmul8 : 8 * ((p ^ 2 - 1) / 8) = p ^ 2 - 1 := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdiv8
  have h8c : (8 : ℤ) * (((p ^ 2 - 1) / 8 : ℕ) : ℤ) = (p : ℤ) ^ 2 - 1 := by
    have hcast := congrArg (Nat.cast : ℕ → ℤ) hmul8
    rw [Nat.cast_sub hle1] at hcast
    push_cast at hcast
    exact hcast
  have hdvdTa : 2 ∣ a * (a + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self a)
  have hmulTa : 2 * (a * (a + 1) / 2) = a * (a + 1) := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdTa
  have hTa : (2 : ℤ) * ((a * (a + 1) / 2 : ℕ) : ℤ)
      = (a : ℤ) * ((a : ℤ) + 1) := by
    exact_mod_cast hmulTa
  have hdvdTj : 2 ∣ j * (j + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self j)
  have hmulTj : 2 * (j * (j + 1) / 2) = j * (j + 1) := by
    rw [mul_comm]
    exact Nat.div_mul_cancel hdvdTj
  have hTj : (2 : ℤ) * ((j * (j + 1) / 2 : ℕ) : ℤ)
      = (j : ℤ) * ((j : ℤ) + 1) := by
    exact_mod_cast hmulTj
  have hjZ : ((j : ℕ) : ℤ) = (p : ℤ) * (a : ℤ) + (t : ℤ) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) hj.symm
    push_cast at h
    exact h
  have h2t : (2 : ℤ) * ((t : ℕ) : ℤ) + 1 = ((p : ℕ) : ℤ) := by
    have h := congrArg (Nat.cast : ℕ → ℤ) hpt.symm
    push_cast at h
    exact h
  have h2j1 : (2 : ℤ) * ((j : ℕ) : ℤ) + 1
      = (p : ℤ) * (2 * (a : ℤ) + 1) := by
    linear_combination 2 * hjZ + h2t
  have h8Tj : (8 : ℤ) * ((j * (j + 1) / 2 : ℕ) : ℤ)
      = ((p : ℤ) * (2 * (a : ℤ) + 1)) ^ 2 - 1 := by
    linear_combination 4 * hTj
      + (2 * ((j : ℕ) : ℤ) + 1 + (p : ℤ) * (2 * (a : ℤ) + 1)) * h2j1
  have hP2 : (((p ^ 2 : ℕ)) : ℤ) = (p : ℤ) ^ 2 := by norm_cast
  have hpoly : ((p : ℤ) ^ 2 - 1)
      + 4 * ((p : ℤ) ^ 2) * ((a : ℤ) * ((a : ℤ) + 1))
      - (((p : ℤ) * (2 * (a : ℤ) + 1)) ^ 2 - 1) = 0 := by
    ring
  exact inr_combine h8c hTa h8Tj hP2 hpoly

/-- Case `r = t`: the middle-class exponent is triangular. -/
private theorem caseC_exp (p t a j : ℕ) (n' : ℤ) (hpt : p = 2 * t + 1)
    (hodd : Odd p) (hj : p * a + t = j) (ha : triIndexFun n' = a) :
    (p ^ 2 - 1) / 8
        + (p ^ 2 * (n' * (n' + 1) / 2).toNat + 3 * p ^ 2 * (n' * (n' - 1) / 2).toNat)
      = j * (j + 1) / 2 := by
  have hE := thetaExp_eq n'
  rw [ha] at hE
  have hfactor : p ^ 2 * (n' * (n' + 1) / 2).toNat
      + 3 * p ^ 2 * (n' * (n' - 1) / 2).toNat
      = p ^ 2 * ((n' * (n' + 1) / 2).toNat + 3 * (n' * (n' - 1) / 2).toNat) := by
    ring
  rw [hfactor, hE]
  exact inrExpEq p t a j hpt hodd hj

/-! ## The term identity. -/

/-- The right-hand summand family over the dissection index type. -/
private noncomputable def RhsTerm (p t : ℕ) (q : ℂ) (x : (Fin t × ℤ) ⊕ ℤ) : ℂ :=
  match x with
  | Sum.inl (k, m) => q ^ (k.val * (k.val + 1) / 2)
      * ramanujanThetaTerm (q ^ ((p ^ 2 + (2 * k.val + 1) * p) / 2))
        (q ^ ((p ^ 2 - (2 * k.val + 1) * p) / 2)) m
  | Sum.inr n => q ^ ((p ^ 2 - 1) / 8)
      * ramanujanThetaTerm (q ^ (p ^ 2)) (q ^ (3 * p ^ 2)) n

private theorem term_identity (p t : ℕ) (hpt : p = 2 * t + 1) (hodd : Odd p)
    (q : ℂ) (n : ℤ) :
    ramanujanThetaTerm q (q ^ 3) n
      = RhsTerm p t q (dissectToFun p t hpt (triIndexFun n)) := by
  have hL := thetaTerm_psi_pow q n
  set j := triIndexFun n
  have hp0 : 0 < p := by omega
  unfold dissectToFun
  split_ifs with h1 h2
  · have hj : p * (j / p) + j % p = j := Nat.div_add_mod j p
    have hexp := caseA_exp p t (j % p) (j / p) j hpt hodd h1 hj
    have hR : RhsTerm p t q (Sum.inl (⟨j % p, h1⟩, ((j / p : ℕ) : ℤ)))
        = q ^ ((j % p) * ((j % p) + 1) / 2)
          * ramanujanThetaTerm (q ^ ((p ^ 2 + (2 * (j % p) + 1) * p) / 2))
            (q ^ ((p ^ 2 - (2 * (j % p) + 1) * p) / 2)) (((j / p : ℕ)) : ℤ) := by
      rfl
    rw [hR, hL, thetaTerm_pow_base, ← pow_add]
    congr 1
    exact hexp.symm
  · have hj : p * (j / p) + t = j := by
      have hdm := Nat.div_add_mod j p
      omega
    have ha : triIndexFun (triIndexInv (j / p)) = j / p :=
      triIndex_right_inv (j / p)
    have hexp := caseC_exp p t (j / p) j (triIndexInv (j / p)) hpt hodd hj ha
    have hR : RhsTerm p t q (Sum.inr (triIndexInv (j / p)))
        = q ^ ((p ^ 2 - 1) / 8)
          * ramanujanThetaTerm (q ^ (p ^ 2)) (q ^ (3 * p ^ 2))
            (triIndexInv (j / p)) := by
      rfl
    rw [hR, hL, thetaTerm_pow_base, ← pow_add]
    congr 1
    exact hexp.symm
  · have hrp : j % p < p := Nat.mod_lt j hp0
    have htr : t < j % p := by omega
    have hj : p * (j / p) + j % p = j := Nat.div_add_mod j p
    have hk : p - 1 - j % p + j % p + 1 = p := by omega
    have hexp := caseB_exp p t (j % p) (j / p) j (p - 1 - j % p)
      hpt hodd htr hk hj
    have hR : ∀ _h : p - 1 - j % p < t, RhsTerm p t q
          (Sum.inl (⟨p - 1 - j % p, _h⟩, (-1 - ((j / p : ℕ) : ℤ))))
        = q ^ ((p - 1 - j % p) * ((p - 1 - j % p) + 1) / 2)
          * ramanujanThetaTerm (q ^ ((p ^ 2 + (2 * (p - 1 - j % p) + 1) * p) / 2))
            (q ^ ((p ^ 2 - (2 * (p - 1 - j % p) + 1) * p) / 2))
            (-1 - ((j / p : ℕ) : ℤ)) := fun _ => rfl
    rw [hR, hL, thetaTerm_pow_base, ← pow_add]
    congr 1
    exact hexp.symm

/-! ## Assembly. -/

/-- The combined index equivalence. -/
private def fullEquiv (p t : ℕ) (hpt : p = 2 * t + 1) : ℤ ≃ (Fin t × ℤ) ⊕ ℤ :=
  triIndex.trans (dissectEquiv p t hpt)

private theorem dissectionEq (p t : ℕ) (hpt : p = 2 * t + 1) (hodd : Odd p)
    (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 3) =
      ∑ k ∈ Finset.range t, q ^ (k * (k + 1) / 2) *
          ramanujanThetaRaw (q ^ ((p ^ 2 + (2 * k + 1) * p) / 2))
            (q ^ ((p ^ 2 - (2 * k + 1) * p) / 2)) +
        q ^ ((p ^ 2 - 1) / 8) * ramanujanThetaRaw (q ^ (p ^ 2)) (q ^ (3 * p ^ 2)) := by
  have hsumL := summable_psi q hq
  have happ : ∀ n : ℤ, fullEquiv p t hpt n = dissectToFun p t hpt (triIndexFun n) :=
    fun n => rfl
  have hterm : ∀ n : ℤ, ramanujanThetaTerm q (q ^ 3) n
      = RhsTerm p t q (fullEquiv p t hpt n) := by
    intro n
    rw [happ n]
    exact term_identity p t hpt hodd q n
  have hsumR : Summable (RhsTerm p t q) := by
    have hcomp : Summable ((ramanujanThetaTerm q (q ^ 3)) ∘ (fullEquiv p t hpt).symm) :=
      ((fullEquiv p t hpt).symm.summable_iff).mpr hsumL
    refine Summable.congr hcomp (fun x => ?_)
    have h := hterm ((fullEquiv p t hpt).symm x)
    have h2 : fullEquiv p t hpt ((fullEquiv p t hpt).symm x) = x :=
      Equiv.apply_symm_apply (fullEquiv p t hpt) x
    rw [h2] at h
    exact h
  have hsumInl : Summable ((RhsTerm p t q) ∘ Sum.inl) :=
    hsumR.comp_injective Sum.inl_injective
  have hsumInr : Summable ((RhsTerm p t q) ∘ Sum.inr) :=
    hsumR.comp_injective Sum.inr_injective
  have hsplit : (∑' _x : (Fin t × ℤ) ⊕ ℤ, RhsTerm p t q _x)
      = (∑' y : Fin t × ℤ, RhsTerm p t q (Sum.inl y))
        + (∑' z : ℤ, RhsTerm p t q (Sum.inr z)) :=
    Summable.tsum_sum hsumInl hsumInr
  have hprod : (∑' y : Fin t × ℤ, RhsTerm p t q (Sum.inl y))
      = ∑' (k : Fin t) (m : ℤ), RhsTerm p t q (Sum.inl (k, m)) :=
    Summable.tsum_prod hsumInl
  have hLHS : ramanujanThetaRaw q (q ^ 3)
      = ∑' _x : (Fin t × ℤ) ⊕ ℤ, RhsTerm p t q _x := by
    unfold ramanujanThetaRaw
    have htsum := Equiv.tsum_eq (fullEquiv p t hpt) (RhsTerm p t q)
    rw [← htsum]
    exact tsum_congr hterm
  have hinner : ∀ k : Fin t, (∑' m : ℤ, RhsTerm p t q (Sum.inl (k, m)))
      = q ^ (k.val * (k.val + 1) / 2) * ramanujanThetaRaw
        (q ^ ((p ^ 2 + (2 * k.val + 1) * p) / 2))
        (q ^ ((p ^ 2 - (2 * k.val + 1) * p) / 2)) := by
    intro k
    have hfun : (fun m : ℤ => RhsTerm p t q (Sum.inl (k, m)))
        = (fun m : ℤ => q ^ (k.val * (k.val + 1) / 2) * ramanujanThetaTerm
          (q ^ ((p ^ 2 + (2 * k.val + 1) * p) / 2))
          (q ^ ((p ^ 2 - (2 * k.val + 1) * p) / 2)) m) := rfl
    rw [hfun, tsum_mul_left]
    rfl
  have hlast : (∑' z : ℤ, RhsTerm p t q (Sum.inr z))
      = q ^ ((p ^ 2 - 1) / 8)
        * ramanujanThetaRaw (q ^ (p ^ 2)) (q ^ (3 * p ^ 2)) := by
    have hfun : (fun z : ℤ => RhsTerm p t q (Sum.inr z))
        = (fun z : ℤ => q ^ ((p ^ 2 - 1) / 8) * ramanujanThetaTerm
          (q ^ (p ^ 2)) (q ^ (3 * p ^ 2)) z) := rfl
    rw [hfun, tsum_mul_left]
    rfl
  have hfin : (∑ k : Fin t, q ^ (k.val * (k.val + 1) / 2) * ramanujanThetaRaw
        (q ^ ((p ^ 2 + (2 * k.val + 1) * p) / 2))
        (q ^ ((p ^ 2 - (2 * k.val + 1) * p) / 2)))
      = ∑ k ∈ Finset.range t, q ^ (k * (k + 1) / 2) * ramanujanThetaRaw
        (q ^ ((p ^ 2 + (2 * k + 1) * p) / 2))
        (q ^ ((p ^ 2 - (2 * k + 1) * p) / 2)) :=
    Fin.sum_univ_eq_sum_range (fun n : ℕ => q ^ (n * (n + 1) / 2)
      * ramanujanThetaRaw (q ^ ((p ^ 2 + (2 * n + 1) * p) / 2))
        (q ^ ((p ^ 2 - (2 * n + 1) * p) / 2))) t
  rw [hLHS, hsplit, hprod]
  simp only [tsum_fintype, hinner]
  rw [hfin, hlast]

/-! ## The congruence part. -/

private theorem two_dvd_sq_add_self (m : ℕ) : 2 ∣ m ^ 2 + m := by
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self m
  refine ⟨t, ?_⟩
  have hring : m ^ 2 + m = m * (m + 1) := by ring
  rw [hring, ht]
  ring

private theorem cong_part (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ m ≤ (p - 3) / 2, ¬ (m ^ 2 + m) / 2 ≡ (p ^ 2 - 1) / 8 [MOD p] := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have h8 : 8 ∣ p ^ 2 - 1 :=
    Nat.eight_dvd_sq_sub_one_of_odd (hp.odd_of_ne_two hp2)
  have h8eq : 8 * ((p ^ 2 - 1) / 8) = p ^ 2 - 1 := by
    rw [mul_comm]
    exact Nat.div_mul_cancel h8
  have hfact : Fact p.Prime := ⟨hp⟩
  intro m hm hcon
  have h2 : 2 ∣ m ^ 2 + m := two_dvd_sq_add_self m
  have h2eq : 2 * ((m ^ 2 + m) / 2) = m ^ 2 + m := by
    rw [mul_comm]
    exact Nat.div_mul_cancel h2
  have hcast : (Nat.cast (((m ^ 2 + m) / 2 : ℕ)) : ZMod p)
      = (Nat.cast (((p ^ 2 - 1) / 8 : ℕ)) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcon
  have h8c : (8 : ZMod p) * (Nat.cast (((p ^ 2 - 1) / 8 : ℕ)) : ZMod p)
      = (Nat.cast ((p ^ 2 - 1 : ℕ)) : ZMod p) := by
    have h := congrArg (Nat.cast : ℕ → ZMod p) h8eq
    simpa [Nat.cast_mul] using h
  have h2c : (2 : ZMod p) * (Nat.cast (((m ^ 2 + m) / 2 : ℕ)) : ZMod p)
      = (Nat.cast ((m ^ 2 + m : ℕ)) : ZMod p) := by
    have h := congrArg (Nat.cast : ℕ → ZMod p) h2eq
    simpa [Nat.cast_mul] using h
  have hp0 : (p : ZMod p) = 0 := ZMod.natCast_self p
  have h1 : 1 ≤ p ^ 2 := by
    have h := Nat.pow_le_pow_left hp.one_lt.le 2
    simpa using h
  have hkey : (4 : ZMod p) * ((m ^ 2 + m : ℕ) : ZMod p) = -1 := by
    have h8cc := congrArg (fun x : ZMod p => 8 * x) hcast
    have h8X : (8 : ZMod p) * (Nat.cast (((m ^ 2 + m) / 2 : ℕ)) : ZMod p)
        = 4 * ((m ^ 2 + m : ℕ) : ZMod p) := by
      linear_combination 4 * h2c
    have h8Y : (8 : ZMod p) * (Nat.cast (((p ^ 2 - 1) / 8 : ℕ)) : ZMod p) = -1 := by
      rw [h8c, Nat.cast_sub h1]
      push_cast
      rw [hp0]
      ring
    rw [h8X, h8Y] at h8cc
    exact h8cc
  have hsq : ((2 * (m : ZMod p) + 1) ^ 2) = 0 := by
    have hpush : ((m ^ 2 + m : ℕ) : ZMod p) = (m : ZMod p) ^ 2 + (m : ZMod p) := by
      push_cast
      ring
    rw [hpush] at hkey
    linear_combination hkey
  have hsqN : p ∣ (2 * m + 1) ^ 2 := by
    have hcast2 : ((((2 * m + 1) ^ 2 : ℕ)) : ZMod p) = 0 := by
      push_cast
      linear_combination hsq
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast2
  have hdvd : p ∣ 2 * m + 1 := hp.dvd_of_dvd_pow hsqN
  have hpos : 0 < 2 * m + 1 := by omega
  have hle : p ≤ 2 * m + 1 := Nat.le_of_dvd hpos hdvd
  omega

/-! ## Main theorem. -/

/-- **Cui–Gu $p$-dissection of $\psi(q)$.** Let $p$ be an odd prime and $q$ a complex number with
$|q| < 1$, let $f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta
function, and let $\psi(q) = f(q, q^3)$. Then
$$
\psi(q) = \sum_{k=0}^{(p-3)/2} q^{k(k+1)/2}
f\bigl(q^{(p^2 + (2k+1)p)/2}, q^{(p^2 - (2k+1)p)/2}\bigr) + q^{(p^2-1)/8} \psi(q^{p^2}),
$$
and $(m^2 + m)/2 \not\equiv (p^2 - 1)/8 \pmod p$ for every integer $m$ with
$0 \le m \le (p - 3)/2$. All the divisions are exact.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 4, eq. (7) (`integers-2024-A86-lem-4`),
quoting S. Cui and N. Gu, *Arithmetic Properties of ℓ-Regular Partitions*, Adv. Appl. Math. 51
(2013), 507–523, Theorem 2.1. -/
public theorem ramanujanPsi_prime_dissection (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 3) =
        ∑ k ∈ Finset.range ((p - 1) / 2), q ^ (k * (k + 1) / 2) *
            ramanujanThetaRaw (q ^ ((p ^ 2 + (2 * k + 1) * p) / 2))
              (q ^ ((p ^ 2 - (2 * k + 1) * p) / 2)) +
          q ^ ((p ^ 2 - 1) / 8) * ramanujanThetaRaw (q ^ (p ^ 2)) (q ^ (3 * p ^ 2)) ∧
      ∀ m ≤ (p - 3) / 2, ¬ (m ^ 2 + m) / 2 ≡ (p ^ 2 - 1) / 8 [MOD p] := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpt : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  constructor
  · exact dissectionEq p ((p - 1) / 2) hpt hodd q hq
  · exact cong_part p hp hp2

end

end MetaMathlibExt
