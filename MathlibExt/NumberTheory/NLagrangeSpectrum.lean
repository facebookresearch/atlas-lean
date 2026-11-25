/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.ContinuedFractions.BoundedPartialQuotients

/-!
# Convergents and the Lagrange approximability

For an irrational real number, the signed quality of each continued fraction
convergent equals the corresponding complete-quotient expression, and the
$1$-Lagrange approximability is the extended-real limsup of those expressions.
The main result is `MetaMathlibExt.convergent_quality_and_lagrange_limsup`.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter Topology

/-- **$n$-Lagrange approximability.** For a natural number $n$ and a real number $\xi$, the
$n$-Lagrange approximability of $\xi$ is the element of the extended reals
$$\lambda_n(\xi) = \limsup_{s/t \to \xi} \frac{\gcd(t, n)}{t^2 \, |s/t - \xi|},$$
where the limsup is over rational numbers $s/t \ne \xi$, written in lowest terms with $t > 0$,
tending to $\xi$. For $n = 1$ this is the classical Lagrange approximability $\lambda(\xi)$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (3). -/
noncomputable def nLagrangeApproximability (n : ℕ) (ξ : ℝ) : EReal :=
  limsup (fun q : ℚ => (((Nat.gcd q.den n : ℝ) / ((q.den : ℝ) ^ 2 * |(q : ℝ) - ξ|) : ℝ) : EReal))
    (comap ((↑) : ℚ → ℝ) (𝓝[≠] ξ))

/-- **The $1$-Lagrange approximability is the classical one.** For every real number $\xi$, the
$1$-Lagrange approximability of $\xi$ is
$$\lambda_1(\xi) = \limsup_{s/t \to \xi} \frac{1}{t^2 \, |s/t - \xi|},$$
taken in the extended reals, where the limsup is over rational numbers $s/t \ne \xi$, written in
lowest terms with $t > 0$, tending to $\xi$. That is, the factor $\gcd(t, 1)$ in the definition
equals $1$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equations (1) and (3). -/
theorem nLagrangeApproximability_one (ξ : ℝ) :
    nLagrangeApproximability 1 ξ =
      limsup (fun q : ℚ => ((1 / ((q.den : ℝ) ^ 2 * |(q : ℝ) - ξ|) : ℝ) : EReal))
        (comap ((↑) : ℚ → ℝ) (𝓝[≠] ξ)) := by
  simp [nLagrangeApproximability]

namespace convergent_quality_and_lagrange_limsup

open Filter Topology
open GenContFract
open GenContFract (of)

private noncomputable def cq (ξ : ℝ) : ℕ → ℝ :=
  fun k => (fun x : ℝ => (Int.fract x)⁻¹)^[k] ξ

private theorem irr_fract (y : ℝ) (hy : Irrational y) : Irrational (Int.fract y) := by
  unfold Irrational
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  apply hy
  exact ⟨(⌊y⌋ : ℚ) + q, by
    push_cast
    rw [hq]
    exact Int.floor_add_fract y⟩

private theorem cq_irr {ξ : ℝ} (hξ : Irrational ξ) (k : ℕ) : Irrational (cq ξ k) := by
  induction k with
  | zero => exact hξ
  | succ k ih =>
    have hstep : cq ξ (k + 1) = (Int.fract (cq ξ k))⁻¹ := by
      simp [cq, Function.iterate_succ_apply']
    rw [hstep]
    exact (irr_fract _ ih).inv

private theorem fract_cq_ne {ξ : ℝ} (hξ : Irrational ξ) (k : ℕ) :
    Int.fract (cq ξ k) ≠ 0 := by
  intro h0
  apply (cq_irr hξ k)
  exact ⟨(⌊cq ξ k⌋ : ℚ), by
    push_cast
    have h1 := Int.floor_add_fract (cq ξ k)
    rw [h0, add_zero] at h1
    exact h1⟩

private theorem stream_eq {ξ : ℝ} (hξ : Irrational ξ) (k : ℕ) :
    GenContFract.IntFractPair.stream ξ k =
      some ⟨⌊cq ξ k⌋, Int.fract (cq ξ k)⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h0 : Int.fract (cq ξ k) ≠ 0 := fract_cq_ne hξ k
    have hstep : cq ξ (k + 1) = (Int.fract (cq ξ k))⁻¹ := by
      simp [cq, Function.iterate_succ_apply']
    rw [GenContFract.IntFractPair.stream_succ_of_some ih h0, hstep]
    rfl

private theorem s_eq {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) :
    (of ξ).s.get? n = some ⟨1, (⌊cq ξ (n + 1)⌋ : ℝ)⟩ := by
  have hs := stream_eq hξ (n + 1)
  have h1 := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hs
  simpa using h1

-- integer-valued continuants
private theorem contsAux_int {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) :
    ∃ a b : ℤ, (of ξ).contsAux n = ⟨(a : ℝ), (b : ℝ)⟩ := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨1, 0, by simp [GenContFract.contsAux]⟩
  | one => exact ⟨⌊ξ⌋, 1, by simp [GenContFract.contsAux, GenContFract.of_h_eq_floor]⟩
  | more n ih0 ih1 =>
    obtain ⟨a0, b0, h0⟩ := ih0
    obtain ⟨a1, b1, h1⟩ := ih1
    have hs := s_eq hξ n
    have hrec := GenContFract.contsAux_recurrence hs h0 h1
    refine ⟨⌊cq ξ (n + 1)⌋ * a1 + a0, ⌊cq ξ (n + 1)⌋ * b1 + b0, ?_⟩
    rw [hrec]
    simp only [Pair.mk.injEq, Int.cast_add, Int.cast_mul]
    constructor <;> ring

private theorem hinf {ξ : ℝ} (hξ : Irrational ξ) (k : ℕ) : ¬(of ξ).TerminatedAt k := by
  intro hk
  obtain ⟨r, hr⟩ := GenContFract.exists_rat_eq_of_terminates ⟨k, hk⟩
  exact hξ ⟨r, hr.symm⟩

private theorem dens_pos {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) : 0 < (of ξ).dens n := by
  have := GenContFract.zero_le_of_den (v := ξ) (n := n)
  -- dens >= fib (n+1) > 0 via succ_nth_fib_le_of_nth_den
  have hle := GenContFract.succ_nth_fib_le_of_nth_den (v := ξ) (n := n) (by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl rfl
    · exact Or.inr (hinf hξ (n - 1)))
  have hpos : (0:ℝ) < (Nat.fib (n+1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
  exact hpos.trans_le hle

private theorem den_eq_dens {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) :
    ((ξ.convergent n).den : ℝ) = (of ξ).dens n := by
  obtain ⟨a, b, hab⟩ := contsAux_int hξ (n + 1)
  have hB : (of ξ).dens n = (b : ℝ) := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
    rw [hab]
  have hA : (of ξ).convs n = (a : ℝ) / (b : ℝ) := by
    rw [GenContFract.conv_eq_conts_a_div_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, hab]
  have hbpos : 0 < b := by
    have := dens_pos hξ n
    rw [hB] at this
    exact_mod_cast this
  -- coprime from determinant
  obtain ⟨a0, b0, hab0⟩ := contsAux_int hξ n
  obtain ⟨a2, b2, hab2⟩ := contsAux_int hξ (n + 2)
  have hdet : (a : ℤ) * b2 - b * a2 = (-1 : ℤ) ^ (n + 1) := by
    have hd : (of ξ).nums n * (of ξ).dens (n + 1) - (of ξ).dens n * (of ξ).nums (n + 1)
        = (-1 : ℝ) ^ (n + 1) := (SimpContFract.of ξ).determinant (hinf hξ n)
    have hnums : (of ξ).nums n = (a : ℝ) := by
      rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux, hab]
    have hnums1 : (of ξ).nums (n + 1) = (a2 : ℝ) := by
      rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux, hab2]
    have hdens1 : (of ξ).dens (n + 1) = (b2 : ℝ) := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, hab2]
    rw [hnums, hnums1, hdens1, hB] at hd
    have hd' : (a : ℝ) * (b2 : ℝ) - (b : ℝ) * (a2 : ℝ) = (-1 : ℝ) ^ (n + 1) := hd
    exact_mod_cast hd'
  have hcop : IsCoprime a b := by
    refine ⟨(-1 : ℤ) ^ (n + 1) * b2, -((-1 : ℤ) ^ (n + 1) * a2), ?_⟩
    have hs : ((-1 : ℤ) ^ (n + 1)) * ((-1 : ℤ) ^ (n + 1)) = 1 := by
      rw [← pow_add]
      simp
    calc ((-1 : ℤ) ^ (n + 1) * b2) * a + -((-1 : ℤ) ^ (n + 1) * a2) * b
        = (-1 : ℤ) ^ (n + 1) * (a * b2 - b * a2) := by ring
      _ = 1 := by rw [hdet, hs]
  have hcopNat : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_nat_coprime.mp hcop
  have hr_eq : ξ.convergent n = (a : ℚ) / (b : ℚ) := by
    apply Rat.cast_inj (α := ℝ) |>.mp
    push_cast
    rw [← Real.convs_eq_convergent, hA]
  have hdenℤ : ((ξ.convergent n).den : ℤ) = b := by
    rw [hr_eq]
    exact Rat.den_div_eq_of_coprime hbpos hcopNat
  rw [hB]
  exact_mod_cast hdenℤ


private noncomputable def revFn (a : ℕ → ℤ) : ℕ → ℝ := fun k =>
  ((List.range (k - 1)).reverse.map (fun i => a (i + 1))).foldr
    (fun b acc => 1 / ((b : ℝ) + acc)) 0

private theorem revFn_one (a : ℕ → ℤ) : revFn a 1 = 0 := rfl

private theorem revFn_succ {a : ℕ → ℤ} (k : ℕ) :
    revFn a (k + 2) = 1 / ((a (k + 1) : ℝ) + revFn a (k + 1)) := by
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 1 - 1 = k := by omega
  simp only [revFn, e1, e2, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.cons_append, List.nil_append, List.map_cons]
  rfl


private theorem dens_rec {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) :
    (of ξ).dens (n + 2) = ((⌊cq ξ (n + 2)⌋ : ℝ)) * (of ξ).dens (n + 1) + (of ξ).dens n := by
  have hs := s_eq hξ (n + 1)
  have hrec := GenContFract.contsAux_recurrence hs rfl rfl
  have hb := congrArg Pair.b hrec
  have h1 : (of ξ).dens (n + 2) = ((of ξ).contsAux (n + 3)).b := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
  have h2 : (of ξ).dens (n + 1) = ((of ξ).contsAux (n + 2)).b := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
  have h3 : (of ξ).dens n = ((of ξ).contsAux (n + 1)).b := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
  rw [h1, h2, h3]
  simpa using hb

private theorem cq_gt_one {ξ : ℝ} (hξ : Irrational ξ) {k : ℕ} (hk : 1 ≤ k) :
    1 < cq ξ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hstep : cq ξ (k + 1) = (Int.fract (cq ξ k))⁻¹ := by
    simp [cq, Function.iterate_succ_apply']
  rw [hstep]
  have h0 : 0 < Int.fract (cq ξ k) :=
    lt_of_le_of_ne' (Int.fract_nonneg _) (fract_cq_ne hξ k)
  have h1 : Int.fract (cq ξ k) < 1 := Int.fract_lt_one _
  exact one_lt_inv_iff₀.mpr ⟨h0, h1⟩

private theorem floor_cq_ge_one {ξ : ℝ} (hξ : Irrational ξ) {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ ⌊cq ξ k⌋ := by
  rw [Int.le_floor]
  simpa using (cq_gt_one hξ hk).le

private theorem rev_nonneg {ξ : ℝ} (hξ : Irrational ξ) (k : ℕ) :
    0 ≤ revFn (fun i => ⌊cq ξ i⌋) k := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih0 ih1 =>
    rw [revFn_succ k]
    have ha : (1 : ℝ) ≤ ((⌊cq ξ (k + 1)⌋ : ℤ) : ℝ) := by
      exact_mod_cast floor_cq_ge_one hξ (by omega : 1 ≤ k + 1)
    exact one_div_nonneg.mpr (by linarith)

private theorem ratio_eq {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) (hn : 1 ≤ n) :
    revFn (fun i => ⌊cq ξ i⌋) (n + 1) = (of ξ).dens (n - 1) / (of ξ).dens n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hrev : revFn (fun i => ⌊cq ξ i⌋) 2 = 1 / ((⌊cq ξ 1⌋ : ℝ) + 0) := by
      rw [revFn_succ 0]
      simp [revFn_one]
    have hd0 : (of ξ).dens 0 = 1 := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux,
        GenContFract.first_contAux_eq_h_one]
    have hd1 : (of ξ).dens 1 = (⌊cq ξ 1⌋ : ℝ) := by
      have hrec := GenContFract.contsAux_recurrence (s_eq hξ 0) rfl rfl
      have hb := congrArg Pair.b hrec
      have h1 : (of ξ).dens 1 = ((of ξ).contsAux 2).b := by
        rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
      rw [h1]
      simpa [GenContFract.contsAux] using hb
    rw [hrev, hd0, hd1]
    simp
  | succ n hn ih =>
    show revFn (fun i => ⌊cq ξ i⌋) (n + 2) = (of ξ).dens n / (of ξ).dens (n + 1)
    have hDn : (of ξ).dens n ≠ 0 := (dens_pos hξ n).ne'
    have hrec := dens_rec hξ (n - 1)
    rw [show n - 1 + 2 = n + 1 by omega, show n - 1 + 1 = n by omega] at hrec
    have hDnp1 : (of ξ).dens (n + 1) ≠ 0 := (dens_pos hξ (n + 1)).ne'
    rw [revFn_succ n, ih, hrec]
    field_simp


private theorem part_a {ξ : ℝ} (hξ : Irrational ξ) (k : ℕ) (hk : 1 ≤ k) :
    (-1 : ℝ) ^ k / (((ξ.convergent (k - 1)).den : ℝ) ^ 2 *
        ((ξ.convergent (k - 1) : ℝ) - ξ)) =
      (⌊cq ξ k⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) k + Int.fract (cq ξ k) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  show (-1 : ℝ) ^ (n + 1) / (((ξ.convergent n).den : ℝ) ^ 2 *
        ((ξ.convergent n : ℝ) - ξ)) =
      (⌊cq ξ (n + 1)⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) (n + 1) + Int.fract (cq ξ (n + 1))
  have hstep : cq ξ (n + 1) = (Int.fract (cq ξ n))⁻¹ := by
    simp [cq, Function.iterate_succ_apply']
  have hsub := GenContFract.sub_convs_eq (v := ξ) (n := n) (ifp := ⟨⌊cq ξ n⌋, Int.fract (cq ξ n)⟩)
    (stream_eq hξ n)
  have hfr : Int.fract (cq ξ n) ≠ 0 := fract_cq_ne hξ n
  dsimp only at hsub
  rw [ite_eq_right hfr] at hsub
  have hBc : ((of ξ).contsAux (n + 1)).b = (of ξ).dens n := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
  rw [hBc, ← hstep] at hsub
  have hB : (of ξ).dens n = ((ξ.convergent n).den : ℝ) := (den_eq_dens hξ n).symm
  have hconv : ((ξ.convergent n : ℚ) : ℝ) = (of ξ).convs n := by
    rw [Real.convs_eq_convergent]
  have hBpos : 0 < (of ξ).dens n := dens_pos hξ n
  have hpB : ((of ξ).contsAux n).b = (of ξ).dens n * revFn (fun i => ⌊cq ξ i⌋) (n + 1) := by
    cases n with
    | zero => simp [GenContFract.contsAux, revFn_one]
    | succ m =>
      have hr := ratio_eq hξ (m + 1) (by omega)
      rw [Nat.add_sub_cancel] at hr
      rw [hr]
      have h1 : ((of ξ).contsAux (m + 1)).b = (of ξ).dens m := by
        rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
      rw [h1]
      field_simp
  have hcut : (⌊cq ξ (n + 1)⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) (n + 1) +
      Int.fract (cq ξ (n + 1)) = cq ξ (n + 1) + revFn (fun i => ⌊cq ξ i⌋) (n + 1) := by
    linear_combination Int.floor_add_fract (cq ξ (n + 1))
  rw [hcut]
  have hcq : cq ξ (n + 1) + revFn (fun i => ⌊cq ξ i⌋) (n + 1) ≠ 0 := by
    have h1 : 1 < cq ξ (n + 1) := cq_gt_one hξ (by omega)
    have h2 := rev_nonneg hξ (n + 1)
    positivity
  -- rewrite the goal in terms of B, convs, t
  have hgoal : (-1 : ℝ) ^ (n + 1) / (((ξ.convergent n).den : ℝ) ^ 2 *
        ((ξ.convergent n : ℝ) - ξ)) =
      cq ξ (n + 1) + revFn (fun i => ⌊cq ξ i⌋) (n + 1) := by
    rw [← hB, hconv]
    have hdiff : (of ξ).convs n - ξ = -((-1 : ℝ) ^ n /
        ((of ξ).dens n * (cq ξ (n + 1) * (of ξ).dens n + ((of ξ).contsAux n).b))) := by
      have hneg : (of ξ).convs n - ξ = -(ξ - (of ξ).convs n) := by ring
      rw [hneg, hsub]
    rw [hdiff, hpB]
    field_simp
    ring
  exact hgoal


private theorem det_int {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) :
    ∃ CA CB PA PB : ℤ,
      (of ξ).contsAux (n + 1) = ⟨(CA : ℝ), (CB : ℝ)⟩ ∧
      (of ξ).contsAux n = ⟨(PA : ℝ), (PB : ℝ)⟩ ∧
      CA * PB - PA * CB = (-1 : ℤ) ^ (n + 1) := by
  obtain ⟨CA, CB, hC⟩ := contsAux_int hξ (n + 1)
  obtain ⟨PA, PB, hP⟩ := contsAux_int hξ n
  refine ⟨CA, CB, PA, PB, hC, hP, ?_⟩
  have hpart : ∀ i, ((of ξ).partNums.get? i).getD (0 : ℝ) = 1 := by
    intro i
    have hs := s_eq hξ i
    have hp := GenContFract.partNum_eq_s_a hs
    rw [hp]
    rfl
  cases n with
  | zero =>
    have hC1 : (CA : ℝ) = ⌊ξ⌋ ∧ (CB : ℝ) = 1 := by
      rw [GenContFract.first_contAux_eq_h_one] at hC
      have h1 := Pair.mk.inj hC.symm
      rw [GenContFract.of_h_eq_floor] at h1
      exact h1
    have hP0 : (PA : ℝ) = 1 ∧ (PB : ℝ) = 0 := by
      have : (of ξ).contsAux 0 = ⟨(1 : ℝ), (0 : ℝ)⟩ := rfl
      rw [this] at hP
      exact Pair.mk.inj hP.symm
    have hCA : CA = ⌊ξ⌋ := by exact_mod_cast hC1.1
    have hCB : CB = 1 := by exact_mod_cast hC1.2
    have hPA : PA = 1 := by exact_mod_cast hP0.1
    have hPB : PB = 0 := by exact_mod_cast hP0.2
    rw [hCA, hCB, hPA, hPB]
    simp
  | succ m =>
    have hdet := GenContFract.determinant (g := of ξ) (n := m)
    have hprod : ∏ i ∈ Finset.range (m + 1), -((of ξ).partNums.get? i).getD (0 : ℝ)
        = (-1 : ℝ) ^ (m + 1) := by
      simp only [hpart, Finset.prod_const, Finset.card_range]
    rw [hprod] at hdet
    have hnums0 : (of ξ).nums m = (PA : ℝ) := by
      rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux, hP]
    have hnums1 : (of ξ).nums (m + 1) = (CA : ℝ) := by
      rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux, hC]
    have hdens0 : (of ξ).dens m = (PB : ℝ) := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, hP]
    have hdens1 : (of ξ).dens (m + 1) = (CB : ℝ) := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, hC]
    rw [hnums0, hnums1, hdens0, hdens1] at hdet
    -- hdet : PA*CB - PB*CA = (-1)^(m+1)
    have hdetℤ : PA * CB - PB * CA = (-1 : ℤ) ^ (m + 1) := by exact_mod_cast hdet
    have hgoal : CA * PB - PA * CB = (-1 : ℤ) ^ (m + 1 + 1) := by
      have h2 : CA * PB - PA * CB = -(PA * CB - PB * CA) := by ring
      rw [h2, hdetℤ, pow_succ]
      ring
    exact hgoal

private theorem exists_coeff {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) (p q : ℤ) :
    ∃ a b : ℤ,
      (p : ℝ) = (a : ℝ) * ((of ξ).contsAux (n + 1)).a + (b : ℝ) * ((of ξ).contsAux n).a ∧
      (q : ℝ) = (a : ℝ) * ((of ξ).contsAux (n + 1)).b + (b : ℝ) * ((of ξ).contsAux n).b := by
  obtain ⟨CA, CB, PA, PB, hC, hP, hdet⟩ := det_int hξ n
  have hΔsq : (CA * PB - PA * CB) * (CA * PB - PA * CB) = 1 := by
    rw [hdet, ← pow_add, show n + 1 + (n + 1) = 2 * (n + 1) by ring, pow_mul]
    norm_num
  refine ⟨(CA * PB - PA * CB) * (p * PB - q * PA),
    (CA * PB - PA * CB) * (CA * q - CB * p), ?_, ?_⟩
  · have hident : ((CA * PB - PA * CB) * (p * PB - q * PA)) * CA +
        ((CA * PB - PA * CB) * (CA * q - CB * p)) * PA = p := by
      have h1 : ((CA * PB - PA * CB) * (p * PB - q * PA)) * CA +
          ((CA * PB - PA * CB) * (CA * q - CB * p)) * PA =
            (CA * PB - PA * CB) * (CA * PB - PA * CB) * p := by ring
      rw [h1, hΔsq, one_mul]
    rw [hC, hP]
    show (p : ℝ) = (((CA * PB - PA * CB) * (p * PB - q * PA) : ℤ) : ℝ) * (CA : ℝ) +
      (((CA * PB - PA * CB) * (CA * q - CB * p) : ℤ) : ℝ) * (PA : ℝ)
    exact_mod_cast hident.symm
  · have hident : ((CA * PB - PA * CB) * (p * PB - q * PA)) * CB +
        ((CA * PB - PA * CB) * (CA * q - CB * p)) * PB = q := by
      have h1 : ((CA * PB - PA * CB) * (p * PB - q * PA)) * CB +
          ((CA * PB - PA * CB) * (CA * q - CB * p)) * PB =
            (CA * PB - PA * CB) * (CA * PB - PA * CB) * q := by ring
      rw [h1, hΔsq, one_mul]
    rw [hC, hP]
    show (q : ℝ) = (((CA * PB - PA * CB) * (p * PB - q * PA) : ℤ) : ℝ) * (CB : ℝ) +
      (((CA * PB - PA * CB) * (CA * q - CB * p) : ℤ) : ℝ) * (PB : ℝ)
    exact_mod_cast hident.symm


private theorem cut_eq {ξ : ℝ} (k : ℕ) :
    (⌊cq ξ k⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) k + Int.fract (cq ξ k) =
      cq ξ k + revFn (fun i => ⌊cq ξ i⌋) k := by
  linear_combination Int.floor_add_fract (cq ξ k)

private theorem dens_succ_eq {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) :
    (of ξ).dens (n + 1) = ((⌊cq ξ (n + 1)⌋ : ℝ)) * (of ξ).dens n + ((of ξ).contsAux n).b := by
  cases n with
  | zero =>
    have hrec := GenContFract.contsAux_recurrence (s_eq hξ 0) rfl rfl
    have hb := congrArg Pair.b hrec
    have h1 : (of ξ).dens 1 = ((of ξ).contsAux 2).b := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
    have h0 : (of ξ).dens 0 = 1 := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux,
        GenContFract.first_contAux_eq_h_one]
    rw [h1, h0]
    simpa [GenContFract.contsAux] using hb
  | succ m =>
    have h := dens_rec hξ m
    have h1 : ((of ξ).contsAux (m + 1)).b = (of ξ).dens m := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
    rw [h1]
    exact h

private theorem hexact {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) :
    ξ = (cq ξ (n + 1) * ((of ξ).contsAux (n + 1)).a + ((of ξ).contsAux n).a) /
      (cq ξ (n + 1) * ((of ξ).contsAux (n + 1)).b + ((of ξ).contsAux n).b) := by
  have h0 := GenContFract.compExactValue_correctness_of_stream_eq_some (stream_eq hξ n)
  have hfr : Int.fract (cq ξ n) ≠ 0 := fract_cq_ne hξ n
  have hstep : cq ξ (n + 1) = (Int.fract (cq ξ n))⁻¹ := by
    simp [cq, Function.iterate_succ_apply']
  simpa [GenContFract.compExactValue, hfr, GenContFract.nextConts, GenContFract.nextNum,
    GenContFract.nextDen, ← hstep] using h0


set_option maxHeartbeats 800000 in
private theorem quality_le_max {ξ : ℝ} (hξ : Irrational ξ) (q : ℚ) (_hq : (q : ℝ) ≠ ξ)
    (n : ℕ) (hn1 : (of ξ).dens n ≤ (q.den : ℝ)) (hn2 : (q.den : ℝ) < (of ξ).dens (n + 1)) :
    1 / ((q.den : ℝ) ^ 2 * |(q : ℝ) - ξ|) ≤
      max (cq ξ (n + 1) + revFn (fun i => ⌊cq ξ i⌋) (n + 1))
        (cq ξ (n + 2) + revFn (fun i => ⌊cq ξ i⌋) (n + 2)) := by
  set C := (of ξ).contsAux (n + 1) with hCdef
  set P := (of ξ).contsAux n with hPdef
  have hCb : C.b = (of ξ).dens n := by
    rw [hCdef, GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
  have hCbpos : 0 < C.b := by rw [hCb]; exact dens_pos hξ n
  have hPb0 : 0 ≤ P.b := by
    rw [hPdef]; exact GenContFract.zero_le_of_contsAux_b
  have hdenpos : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  obtain ⟨α, β, hp, hd⟩ := exists_coeff hξ n q.num (q.den : ℤ)
  have hd' : (q.den : ℝ) = (α : ℝ) * C.b + (β : ℝ) * P.b := by
    have := hd
    rw [← hCdef, ← hPdef] at this
    push_cast at this ⊢
    linarith [this]
  have hp' : (q.num : ℝ) = (α : ℝ) * C.a + (β : ℝ) * P.a := by
    have := hp
    rw [← hCdef, ← hPdef] at this
    exact this
  -- complete quotient, digit, fractional part
  set t : ℝ := cq ξ (n + 1) with htdef
  have ht1 : 1 < t := cq_gt_one hξ (by omega)
  have htirr : Irrational t := cq_irr hξ (n + 1)
  set δ : ℝ := Int.fract t with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    refine lt_of_le_of_ne' (Int.fract_nonneg _) ?_
    intro h0
    apply htirr
    refine ⟨(⌊t⌋ : ℚ), ?_⟩
    push_cast
    have h1 := Int.floor_add_fract t
    rw [h0, add_zero] at h1
    exact h1
  have hδ1 : δ < 1 := Int.fract_lt_one _
  have hdecomp : ((⌊t⌋ : ℤ) : ℝ) + δ = t := by
    rw [hδdef]; exact Int.floor_add_fract t
  have ha1 : 1 ≤ ⌊t⌋ := floor_cq_ge_one hξ (by omega)
  have ha1ℝ : (1 : ℝ) ≤ ((⌊t⌋ : ℤ) : ℝ) := by exact_mod_cast ha1
  set r : ℝ := P.b / C.b with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one hCbpos]
    cases n with
    | zero =>
      have hPb : P.b = 0 := by rw [hPdef]; rfl
      rw [hPb]; exact hCbpos.le
    | succ m =>
      have h1 : P.b = (of ξ).dens m := by
        rw [hPdef, GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
      rw [h1, hCb]
      have hmono : Monotone (of ξ).dens :=
        monotone_nat_of_le_succ fun m => GenContFract.of_den_mono
      exact hmono (by omega)
  set R : ℝ := ((⌊t⌋ : ℤ) : ℝ) + r with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; linarith [ha1ℝ, hr0]
  have hRpos : 0 < R := by linarith [hR1]
  have hReq : R * C.b = (of ξ).dens (n + 1) := by
    have h := dens_succ_eq hξ n
    rw [← hCb, ← hPdef, ← htdef] at h
    rw [hRdef, add_mul, div_mul_cancel₀ _ hCbpos.ne', h]
  set c : ℝ := t + r with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith [ht1, hr0]
  -- coefficients s and u
  set s : ℝ := (α : ℝ) + (β : ℝ) * r with hsdef
  have hrCb : r * C.b = P.b := by rw [hrdef]; exact div_mul_cancel₀ _ hCbpos.ne'
  have hs_eq : s * C.b = (q.den : ℝ) := by rw [hsdef, add_mul, hd', mul_assoc, hrCb]
  have hs1 : 1 ≤ s := by
    have hsd : s = (q.den : ℝ) / C.b := by rw [eq_div_iff hCbpos.ne']; exact hs_eq
    rw [hsd, le_div_iff₀ hCbpos, one_mul, hCb]
    exact hn1
  have hsR : s < R := by
    have hsd : s = (q.den : ℝ) / C.b := by rw [eq_div_iff hCbpos.ne']; exact hs_eq
    rw [hsd, div_lt_iff₀ hCbpos, hReq]
    exact hn2
  set u : ℝ := (α : ℝ) - (β : ℝ) * t with hudef
  have hu_ne : u ≠ 0 := by
    intro h0
    by_cases hβ : β = 0
    · rw [hudef] at h0
      rw [hβ] at h0
      simp at h0
      have hα : α = 0 := by exact_mod_cast h0
      have h0den : (q.den : ℝ) = 0 := by rw [hd', hα, hβ]; simp
      exact hdenpos.ne' h0den
    · apply htirr
      refine ⟨(α : ℚ) / (β : ℚ), ?_⟩
      have hβℝ : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
      have hαt : (α : ℝ) = (β : ℝ) * t := by rw [hudef] at h0; linarith [h0]
      push_cast
      rw [div_eq_iff hβℝ]
      linarith [hαt]
  -- exact value and error relation
  have hdenne : t * C.b + P.b ≠ 0 := by positivity
  have hrel : P.a - P.b * ξ = -t * (C.a - C.b * ξ) := by
    have hx := hexact hξ n
    rw [← hCdef, ← hPdef] at hx
    linear_combination -(eq_div_iff hdenne).mp hx
  have herr : (q.num : ℝ) - (q.den : ℝ) * ξ = u * (C.a - C.b * ξ) := by
    linear_combination hp' - ξ * hd' + (β : ℝ) * hrel
  have hsub := GenContFract.sub_convs_eq (v := ξ) (n := n)
    (ifp := ⟨⌊cq ξ n⌋, Int.fract (cq ξ n)⟩) (stream_eq hξ n)
  have hfr : Int.fract (cq ξ n) ≠ 0 := fract_cq_ne hξ n
  dsimp only at hsub
  rw [ite_eq_right hfr] at hsub
  have hBc : ((of ξ).contsAux (n + 1)).b = (of ξ).dens n := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
  rw [hBc] at hsub
  have hstep : cq ξ (n + 1) = (Int.fract (cq ξ n))⁻¹ := by
    simp [cq, Function.iterate_succ_apply']
  rw [← hstep, ← htdef, ← hCb, ← hPdef] at hsub
  have hconv2 : (of ξ).convs n = C.a / C.b := by
    rw [hCdef, GenContFract.conv_eq_conts_a_div_conts_b,
      GenContFract.nth_cont_eq_succ_nth_contAux]
  have hdenpos2 : 0 < C.b * (t * C.b + P.b) := by positivity
  have habs : |ξ - (of ξ).convs n| = 1 / (C.b * (t * C.b + P.b)) := by
    rw [hsub, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hdenpos2]
  have herrC : |C.a - C.b * ξ| = 1 / (t * C.b + P.b) := by
    have hCe : C.a - C.b * ξ = -C.b * (ξ - (of ξ).convs n) := by
      rw [hconv2]; field_simp; ring
    rw [hCe, abs_mul, abs_neg, abs_of_pos hCbpos, habs]
    field_simp
  have hqr : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    have h := Rat.num_div_den q
    exact_mod_cast h.symm
  have habs2 : |(q : ℝ) - ξ| = |u| / ((q.den : ℝ) * (t * C.b + P.b)) := by
    have h1 : (q : ℝ) - ξ = ((q.num : ℝ) - (q.den : ℝ) * ξ) / (q.den : ℝ) := by
      rw [hqr]; field_simp
    rw [h1, abs_div, abs_of_pos hdenpos, herr, abs_mul, herrC, mul_one_div, div_div,
      mul_comm (t * C.b + P.b) ((q.den : ℝ))]
  have hspos : 0 < s := by linarith [hs1]
  have htc : t * C.b + P.b = C.b * c := by rw [hcdef, hrdef]; field_simp
  have hF : 1 / ((q.den : ℝ) ^ 2 * |(q : ℝ) - ξ|) = c / (s * |u|) := by
    rw [habs2, htc, ← hs_eq]
    field_simp [hspos.ne', hCbpos.ne', hcpos.ne', abs_ne_zero.mpr hu_ne]

  -- ratio of previous denominator to current one
  have hrev_eq : revFn (fun i => ⌊cq ξ i⌋) (n + 1) = r := by
    cases n with
    | zero =>
      have hPb : P.b = 0 := by rw [hPdef]; rfl
      simp [revFn_one, hPb, hrdef]
    | succ m =>
      have hr := ratio_eq hξ (m + 1) (by omega)
      rw [Nat.add_sub_cancel] at hr
      have h1 : P.b = (of ξ).dens m := by
        rw [hPdef, GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
      rw [hrdef, h1]
      rw [← hCb] at hr
      exact hr
  have hcq2 : cq ξ (n + 2) = δ⁻¹ := by
    have hstep : cq ξ (n + 2) = (Int.fract (cq ξ (n + 1)))⁻¹ := by
      simp [cq, Function.iterate_succ_apply']
    rw [hstep, ← htdef, ← hδdef]
  have hrev2 : revFn (fun i => ⌊cq ξ i⌋) (n + 2) = R⁻¹ := by
    rw [revFn_succ n, hrev_eq, ← htdef, ← hRdef, one_div]
  have hcR : c = R + δ := by rw [hcdef, hRdef]; linarith [hdecomp]
  have hcut_next : cq ξ (n + 2) + revFn (fun i => ⌊cq ξ i⌋) (n + 2) = c / (δ * R) := by
    rw [hcq2, hrev2, hcR, inv_add_inv hδ0.ne' hRpos.ne', add_comm δ R]
  -- integer part of the coefficient combination
  set m : ℤ := α - β * ⌊t⌋ with hmdef
  have hm_s : (m : ℝ) + (β : ℝ) * R = s := by
    rw [hmdef]; push_cast; rw [hsdef, hRdef]; ring
  have hm_u : (m : ℝ) - (β : ℝ) * δ = u := by
    rw [hmdef]; push_cast; rw [hudef]; linear_combination -(β : ℝ) * hdecomp
  have hc_eq : c = cq ξ (n + 1) + revFn (fun i => ⌊cq ξ i⌋) (n + 1) := by
    rw [hcdef, ← htdef, hrev_eq]
  by_cases hD1 : 1 ≤ s * |u|
  · rw [hF, ← hc_eq]
    exact (div_le_self hcpos.le hD1).trans (le_max_left _ _)
  · push Not at hD1
    have hDge : δ * R ≤ s * |u| := by
      rcases le_or_gt 0 β with hβ0 | hβneg
      · rcases eq_or_lt_of_le hβ0 with hβeq | hβpos
        have hβeq : β = 0 := hβeq.symm
        · -- β = 0 : D = α^2 ≥ 1, contradiction with D < 1
          exfalso
          have hαge : (1 : ℝ) ≤ (α : ℝ) := by
            have hs1' := hs1
            rw [hsdef, hβeq] at hs1'
            simpa using hs1'
          have hseq : s = (α : ℝ) := by rw [hsdef, hβeq]; simp
          have hueq : u = (α : ℝ) := by rw [hudef, hβeq]; simp
          rw [hseq, hueq, abs_of_nonneg (by linarith : (0:ℝ) ≤ (α:ℝ))] at hD1
          nlinarith [hαge]
        · -- β ≥ 1
          have hβ1 : (1 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβpos
          have hβR : R ≤ (β : ℝ) * R := le_mul_of_one_le_left hRpos.le hβ1
          have hmneg : (m : ℝ) < 0 := by linarith [hm_s, hsR, hβR]
          have hm0 : m < 0 := by exact_mod_cast hmneg
          set j : ℤ := -m with hjdef
          have hj1 : 1 ≤ j := by omega
          have hj1ℝ : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
          have hj_eq : (j : ℝ) = (β : ℝ) * R - s := by
            rw [← hm_s]; push_cast [hjdef]; ring
          have habsu : |u| = (j : ℝ) + (β : ℝ) * δ := by
            have hpos : 0 < (j : ℝ) + (β : ℝ) * δ := by
              have hβδ : 0 < (β : ℝ) * δ := by positivity
              linarith [hj1ℝ, hβδ]
            rw [show u = -((j : ℝ) + (β : ℝ) * δ) by rw [← hm_u]; push_cast [hjdef]; ring,
              abs_neg, abs_of_pos hpos]
          rw [habsu]
          have h1 : (s - 1) * (1 + δ) ≤ (s - 1) * ((j : ℝ) + (β : ℝ) * δ) :=
            mul_le_mul_of_nonneg_left (by
              have hβδ : δ ≤ (β : ℝ) * δ := by
                have := mul_le_mul_of_nonneg_right hβ1 hδ0.le
                simpa using this
              linarith [hj1ℝ, hβδ]) (by linarith [hs1])
          have hB : ((β : ℝ) - δ) * 1 ≤ ((β : ℝ) - δ) * R :=
            mul_le_mul_of_nonneg_left hR1 (by linarith [hβ1, hδ1])
          have hsδ : δ ≤ s * δ := by
            have := mul_le_mul_of_nonneg_right hs1 hδ0.le
            simpa using this
          have hprod : 0 ≤ ((β : ℝ) - 1) * (1 + δ) :=
            mul_nonneg (by linarith [hβ1]) (by linarith [hδ0])
          have hident : s * ((j : ℝ) + (β : ℝ) * δ) - δ * R =
              (s - 1) * ((j : ℝ) + (β : ℝ) * δ) + ((β : ℝ) - δ) * R - s + (β : ℝ) * δ := by
            rw [hj_eq]; ring
          have htotal : 0 ≤ (s - 1) * ((j : ℝ) + (β : ℝ) * δ) + ((β : ℝ) - δ) * R - s +
              (β : ℝ) * δ := by linarith [h1, hB, hsδ, hprod, hβ1, hδ1, hδ0, hs1]
          linarith [hident, htotal]
      · -- β ≤ -1
        have hβ1 : (1 : ℝ) ≤ -(β : ℝ) := by
          have hβle : β ≤ -1 := by omega
          have h1r : (1 : ℝ) ≤ (-(β : ℤ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ -β)
          exact h1r
        have h1R : R ≤ (-(β : ℝ)) * R := le_mul_of_one_le_left hRpos.le hβ1
        have hum : (m : ℝ) ≥ 1 + (-(β : ℝ)) * R := by linarith [hm_s, hs1]
        have huPos : 0 < u := by
          rw [← hm_u]
          have hβδ : 0 ≤ (-(β : ℝ)) * δ := by positivity
          linarith [hum, hβδ, hRpos]
        have habsu : |u| = u := abs_of_pos huPos
        rw [habsu]
        have hu_ge : (-(β : ℝ)) * R ≤ u := by
          rw [← hm_u]
          have hβδ : 0 ≤ (-(β : ℝ)) * δ := by positivity
          linarith [hum, hβδ]
        have hDge' : δ * R ≤ u := by
          have h2 : δ * R < 1 * R := by
            apply mul_lt_mul_of_pos_right hδ1 hRpos
          linarith [hu_ge, h1R, h2, hRpos]
        calc δ * R ≤ u := hDge'
          _ ≤ s * u := by
            have := mul_le_mul_of_nonneg_right hs1 huPos.le
            simpa using this
    rw [hF]
    have hDpos : 0 < s * |u| := mul_pos hspos (abs_pos.mpr hu_ne)
    have hδRpos : 0 < δ * R := mul_pos hδ0 hRpos
    calc c / (s * |u|) ≤ c / (δ * R) := by
          rw [div_le_div_iff₀ hDpos hδRpos]
          exact mul_le_mul_of_nonneg_left hDge hcpos.le
      _ = cq ξ (n + 2) + revFn (fun i => ⌊cq ξ i⌋) (n + 2) := hcut_next.symm
      _ ≤ max (cq ξ (n + 1) + revFn (fun i => ⌊cq ξ i⌋) (n + 1))
            (cq ξ (n + 2) + revFn (fun i => ⌊cq ξ i⌋) (n + 2)) := le_max_right _ _


private theorem dens_ge_one {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) : 1 ≤ (of ξ).dens n := by
  obtain ⟨a, b, hab⟩ := contsAux_int hξ (n + 1)
  have hB : (of ξ).dens n = (b : ℝ) := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, hab]
  have hbpos : 0 < (b : ℝ) := by rw [← hB]; exact dens_pos hξ n
  have : 1 ≤ b := by exact_mod_cast hbpos
  rw [hB]; exact_mod_cast this

private theorem dens_ge {ξ : ℝ} (hξ : Irrational ξ) (m : ℕ) :
    (m : ℝ) + 1 ≤ (of ξ).dens (m + 1) := by
  induction m with
  | zero =>
    have h := dens_succ_eq hξ 0
    simp only [Nat.zero_add] at h
    rw [h]
    have h0 : (of ξ).dens 0 = 1 := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux,
        GenContFract.first_contAux_eq_h_one]
    have h1 : ((of ξ).contsAux 0).b = 0 := rfl
    rw [h0, h1]
    have ha : (1 : ℝ) ≤ ((⌊cq ξ 1⌋ : ℤ) : ℝ) := by exact_mod_cast floor_cq_ge_one hξ (by omega)
    simp [ha]
  | succ m ih =>
    have h := dens_succ_eq hξ (m + 1)
    have h1 : ((of ξ).contsAux (m + 1)).b = (of ξ).dens m := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
    rw [h1] at h
    rw [h]
    have ha : (1 : ℝ) ≤ ((⌊cq ξ (m + 2)⌋ : ℤ) : ℝ) := by
      exact_mod_cast floor_cq_ge_one hξ (by omega)
    have hpos : 0 < (of ξ).dens (m + 1) := dens_pos hξ (m + 1)
    have hge1 : 1 ≤ (of ξ).dens m := dens_ge_one hξ m
    have hmul : (of ξ).dens (m + 1) ≤ ((⌊cq ξ (m + 2)⌋ : ℤ) : ℝ) * (of ξ).dens (m + 1) :=
      le_mul_of_one_le_left hpos.le ha
    push_cast
    linarith [ih, hmul, hge1]

private theorem exists_dens_interval {ξ : ℝ} (hξ : Irrational ξ) (N : ℕ) (d : ℝ)
    (_hd : 0 < d) (hNd : (of ξ).dens N ≤ d) :
    ∃ n : ℕ, N ≤ n ∧ (of ξ).dens n ≤ d ∧ d < (of ξ).dens (n + 1) := by
  have hmono : Monotone (of ξ).dens :=
    monotone_nat_of_le_succ fun m => GenContFract.of_den_mono
  have hex : ∃ m : ℕ, d < (of ξ).dens m := by
    refine ⟨Nat.ceil d + 1, ?_⟩
    have h1 : d < (Nat.ceil d : ℝ) + 1 := by
      have hle := Nat.le_ceil d
      linarith [hle]
    have h2 : ((Nat.ceil d : ℝ)) + 1 ≤ (of ξ).dens (Nat.ceil d + 1) :=
      dens_ge hξ (Nat.ceil d)
    linarith [h1, h2]
  have hd1 : 1 ≤ d := (dens_ge_one hξ N).trans hNd
  classical
  set m0 := Nat.find hex with hm0def
  have hm0 : d < (of ξ).dens m0 := Nat.find_spec hex
  have hm0pos : 1 ≤ m0 := by
    by_contra h
    push Not at h
    interval_cases m0
    have h0 : (of ξ).dens 0 = 1 := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux,
        GenContFract.first_contAux_eq_h_one]
    rw [h0] at hm0
    linarith [hd1, hm0]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m0 = n + 1 := ⟨m0 - 1, by omega⟩
  rw [hn] at hm0
  have hmin : ¬ d < (of ξ).dens n := Nat.find_min hex (by omega)
  refine ⟨n, ?_, by linarith [hmin], hm0⟩
  by_contra hlt
  push Not at hlt
  have hle : (of ξ).dens (n + 1) ≤ (of ξ).dens N := hmono (by omega)
  linarith [hle, hNd, hm0]


/-- Close rationals have large denominators: for `N ≥ 1` there is a positive
distance `δ` such that every rational within `δ` of `ξ` has denominator at
least the `N`th continuant denominator. -/
private theorem exists_pos_forall_den_ge {ξ : ℝ} (hξ : Irrational ξ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℚ, (q : ℝ) ≠ ξ → |(q : ℝ) - ξ| < δ →
      (of ξ).dens N ≤ (q.den : ℝ) := by
  obtain ⟨QA, QB, hQ⟩ := contsAux_int hξ (N + 1)
  have hQB : (of ξ).dens N = (QB : ℝ) := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, hQ]
  have hQpos : 0 < QB := by
    have := dens_pos hξ N
    rw [hQB] at this
    exact_mod_cast this
  set M : ℕ := QB.toNat with hMdef
  have hMcast : (M : ℝ) = (QB : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hQpos.le
  have hMpos : 0 < M := by
    rw [hMdef]
    have hne : QB.toNat ≠ 0 := by
      rw [ne_eq, Int.toNat_eq_zero]
      omega
    exact Nat.pos_of_ne_zero hne
  set aM : ℝ := 1 + ∑ j ∈ Finset.range (N + 2), |(⌊cq ξ j⌋ : ℝ)| with haMdef
  have haMpos : 0 < aM := by
    rw [haMdef]
    have : 0 ≤ ∑ j ∈ Finset.range (N + 2), |(⌊cq ξ j⌋ : ℝ)| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg _)
    linarith [this]
  refine ⟨1 / ((aM + 2) * (M : ℝ) ^ 2), by positivity, ?_⟩
  intro q hq hclose
  by_contra hle
  push Not at hle
  have hdenM : q.den < M := by
    have h1 : (q.den : ℝ) < (M : ℝ) := by rw [hMcast]; rw [hQB] at hle; exact hle
    exact_mod_cast h1
  have hNM : (of ξ).dens N ≤ (M : ℝ) := by rw [hMcast, hQB]
  have hMN : (M : ℝ) < (of ξ).dens (N + 1) := by
    rw [hMcast]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    have h1 : ((of ξ).contsAux (m + 1)).b = (of ξ).dens m := by
      rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
    have h := dens_succ_eq hξ (m + 1)
    rw [h1] at h
    rw [h, hQB]
    have ha : (1 : ℝ) ≤ ((⌊cq ξ (m + 2)⌋ : ℤ) : ℝ) := by
      exact_mod_cast floor_cq_ge_one hξ (by omega)
    have hge1 : 1 ≤ (of ξ).dens m := dens_ge_one hξ m
    have hpos : 0 < (of ξ).dens (m + 1) := dens_pos hξ (m + 1)
    have hmul : (of ξ).dens (m + 1) ≤ ((⌊cq ξ (m + 2)⌋ : ℤ) : ℝ) * (of ξ).dens (m + 1) :=
      le_mul_of_one_le_left hpos.le ha
    rw [hQB] at hmul
    linarith [hmul, hge1]
  have ha0 : ((⌊ξ⌋ : ℤ) : ℝ) ≤ aM := by
    rw [haMdef]
    have hmem : 0 ∈ Finset.range (N + 2) := Finset.mem_range.mpr (by omega)
    have h1 := Finset.single_le_sum (f := fun j => |(⌊cq ξ j⌋ : ℝ)|)
      (fun i _ => abs_nonneg _) hmem
    have h2 : (⌊cq ξ 0⌋ : ℝ) ≤ |(⌊cq ξ 0⌋ : ℝ)| := le_abs_self _
    show ((⌊cq ξ 0⌋ : ℤ) : ℝ) ≤ 1 + ∑ j ∈ Finset.range (N + 2), |(⌊cq ξ j⌋ : ℝ)|
    linarith [h1, h2]
  have ha : ∀ j ≤ N, ∀ b : ℝ, (of ξ).partDens.get? j = some b → b ≤ aM := by
    intro j hj b hb
    have hpd : (of ξ).partDens.get? j = some ((⌊cq ξ (j + 1)⌋ : ℤ) : ℝ) :=
      GenContFract.partDen_eq_s_b (s_eq hξ j)
    rw [hpd] at hb
    have hbj : b = ((⌊cq ξ (j + 1)⌋ : ℤ) : ℝ) := (Option.some.inj hb).symm
    rw [hbj, haMdef]
    have hmem : j + 1 ∈ Finset.range (N + 2) := Finset.mem_range.mpr (by omega)
    have h1 := Finset.single_le_sum (f := fun j => |(⌊cq ξ j⌋ : ℝ)|)
      (fun i _ => abs_nonneg _) hmem
    have h2 : ((⌊cq ξ (j + 1)⌋ : ℤ) : ℝ) ≤ |(⌊cq ξ (j + 1)⌋ : ℝ)| := le_abs_self _
    linarith [h1, h2]
  have hbound := MetaMathlibExt.one_div_partialQuotient_bound_lt_abs_sub (x := ξ) hξ
    (M := M) (N := N) (by omega : 0 < M) hNM hMN ha0 ha
    (p := q.num) (q := (q.den : ℤ)) (by exact_mod_cast q.pos) (by exact_mod_cast hdenM)
  have hqr : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    have h := Rat.num_div_den q
    exact_mod_cast h.symm
  have habs : |(q : ℝ) - ξ| = |ξ - (q.num : ℝ) / (q.den : ℝ)| := by
    rw [hqr, abs_sub_comm]
  have hlt : 1 / ((aM + 2) * (M : ℝ) ^ 2) < 1 / ((aM + 2) * (q.den : ℝ) ^ 2) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    have hdenlt : (q.den : ℝ) < (M : ℝ) := by exact_mod_cast hdenM
    have hpow : (q.den : ℝ) ^ 2 < (M : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hdenlt (by positivity) (by norm_num)
    have hpos2 : 0 < aM + 2 := by linarith [haMpos]
    exact mul_lt_mul_of_pos_left hpow hpos2
  push_cast at hbound
  rw [← habs] at hbound
  linarith [hlt, hbound, hclose]


private theorem tendsto_convergent {ξ : ℝ} (hξ : Irrational ξ) :
    Filter.Tendsto (fun k : ℕ => ((ξ.convergent k : ℚ) : ℝ)) Filter.atTop (𝓝[≠] ξ) := by
  have hne : ∀ k : ℕ, ((ξ.convergent k : ℚ) : ℝ) ≠ ξ := by
    intro k h
    apply hξ
    exact ⟨ξ.convergent k, h⟩
  have hbound : ∀ᶠ k : ℕ in Filter.atTop,
      dist ((ξ.convergent k : ℚ) : ℝ) ξ ≤ 1 / (k : ℝ) := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun k hk => ?_⟩
    have h1 := GenContFract.abs_sub_convs_le (v := ξ) (n := k) (hinf hξ k)
    rw [Real.dist_eq, ← Real.convs_eq_convergent]
    calc |(of ξ).convs k - ξ| ≤ 1 / ((of ξ).dens k * (of ξ).dens (k + 1)) := by
            rw [abs_sub_comm]; exact h1
      _ ≤ 1 / (k : ℝ) := by
            apply one_div_le_one_div_of_le (by exact_mod_cast hk)
            have hk1 : (k : ℝ) ≤ (of ξ).dens k := by
              have h := dens_ge hξ (k - 1)
              rw [show k - 1 + 1 = k by omega] at h
              have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
                rw [Nat.cast_sub (by omega : 1 ≤ k)]
                norm_num
              rw [hcast] at h
              linarith [h]
            have h2 : 1 ≤ (of ξ).dens (k + 1) := dens_ge_one hξ (k + 1)
            calc (k : ℝ) = (k : ℝ) * 1 := by ring
              _ ≤ (of ξ).dens k * (of ξ).dens (k + 1) :=
                mul_le_mul hk1 h2 (by norm_num) (dens_pos hξ k).le
  have hg : Filter.Tendsto (fun k : ℕ => 1 / (k : ℝ)) Filter.atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hto : Filter.Tendsto (fun k : ℕ => ((ξ.convergent k : ℚ) : ℝ)) Filter.atTop (𝓝 ξ) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) hbound hg
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hto
    (Filter.Eventually.of_forall fun k => hne k)



private theorem coe_max_ereal (a b : ℝ) :
    ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]

private theorem quality_convergent {ξ : ℝ} (hξ : Irrational ξ) (k : ℕ) :
    ((1 / (((ξ.convergent k).den : ℝ) ^ 2 * |((ξ.convergent k : ℚ) : ℝ) - ξ|) : ℝ) : EReal) =
      ((cq ξ (k + 1) + revFn (fun i => ⌊cq ξ i⌋) (k + 1) : ℝ) : EReal) := by
  have h := part_a hξ (k + 1) (by omega)
  have hcut : (⌊cq ξ (k + 1)⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) (k + 1) +
      Int.fract (cq ξ (k + 1)) = cq ξ (k + 1) + revFn (fun i => ⌊cq ξ i⌋) (k + 1) :=
    cut_eq (k + 1)
  rw [Nat.add_sub_cancel] at h
  have hpos : 0 < (⌊cq ξ (k + 1)⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) (k + 1) +
      Int.fract (cq ξ (k + 1)) := by
    have h1 : 1 < cq ξ (k + 1) := cq_gt_one hξ (by omega)
    have h2 := rev_nonneg hξ (k + 1)
    have h3 : 0 ≤ Int.fract (cq ξ (k + 1)) := Int.fract_nonneg _
    rw [hcut]
    linarith [h1, h2]
  have hdenpos : 0 < ((ξ.convergent k).den : ℝ) := by exact_mod_cast (ξ.convergent k).pos
  have hreal : 1 / (((ξ.convergent k).den : ℝ) ^ 2 * |((ξ.convergent k : ℚ) : ℝ) - ξ|) =
      (⌊cq ξ (k + 1)⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) (k + 1) +
        Int.fract (cq ξ (k + 1)) := by
    rw [← abs_of_pos hpos, ← h, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_mul,
      abs_of_pos (pow_pos hdenpos 2)]
  rw [hreal, hcut]

end convergent_quality_and_lagrange_limsup

section

open convergent_quality_and_lagrange_limsup

/-- **Convergents and the Lagrange approximability.** Let $\xi$ be an irrational real number,
with complete quotients $\xi_0 = \xi$ and $\xi_{k+1} = 1/\{\xi_k\}$, where $\{x\}$ is the
fractional part of $x$, and digits $a_k = \lfloor \xi_k \rfloor$, so that
$\xi = [a_0; a_1, a_2, \dots]$. For $k \ge 1$ let
$c_k = a_k + [0; a_{k-1}, \dots, a_1] + \{\xi_k\}$, where the middle term is $0$ when $k = 1$.
Then for every $k \ge 1$ the convergent $p/q = [a_0; a_1, \dots, a_{k-1}]$, written in lowest terms
with $q > 0$, satisfies $(-1)^k / (q^2 (p/q - \xi)) = c_k$. Moreover, the $1$-Lagrange
approximability $\lambda_1(\xi)$ equals $\limsup_{k \to \infty} c_k$, taken in the extended reals.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 4 (`integers-2025-A47-prop-4`), parts (a) and (c), quoted from Cusick and Flahive,
Appendix 1. -/
public theorem convergent_quality_and_lagrange_limsup (ξ : ℝ) (hξ : Irrational ξ) :
    let cq : ℕ → ℝ := fun k => (fun x : ℝ => (Int.fract x)⁻¹)^[k] ξ
    let a : ℕ → ℤ := fun k => ⌊cq k⌋
    let rev : ℕ → ℝ := fun k =>
      ((List.range (k - 1)).reverse.map (fun i => a (i + 1))).foldr
        (fun b acc => 1 / ((b : ℝ) + acc)) 0
    let cut : ℕ → ℝ := fun k => (a k : ℝ) + rev k + Int.fract (cq k)
    (∀ k : ℕ, 1 ≤ k →
        (-1 : ℝ) ^ k / (((ξ.convergent (k - 1)).den : ℝ) ^ 2 *
          ((ξ.convergent (k - 1) : ℝ) - ξ)) = cut k) ∧
      nLagrangeApproximability 1 ξ = limsup (fun k => ((cut k : ℝ) : EReal)) atTop := by
  show (∀ k : ℕ, 1 ≤ k →
        (-1 : ℝ) ^ k / (((ξ.convergent (k - 1)).den : ℝ) ^ 2 *
          ((ξ.convergent (k - 1) : ℝ) - ξ)) =
            (⌊cq ξ k⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) k + Int.fract (cq ξ k)) ∧
      MetaMathlibExt.nLagrangeApproximability 1 ξ =
        limsup (fun k => ((((⌊cq ξ k⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) k +
          Int.fract (cq ξ k) : ℝ)) : EReal)) atTop
  refine ⟨fun k hk => part_a hξ k hk, ?_⟩
  rw [MetaMathlibExt.nLagrangeApproximability_one]
  have hC : (fun k => ((((⌊cq ξ k⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) k +
        Int.fract (cq ξ k) : ℝ)) : EReal)) =
      fun k => (((cq ξ k + revFn (fun i => ⌊cq ξ i⌋) k : ℝ)) : EReal) := by
    funext k
    rw [cut_eq]
  rw [hC]
  apply le_antisymm
  · refine (limsup_le_iff').mpr ?_
    intro y hy
    have hevC : ∀ᶠ k in Filter.atTop,
        (((cq ξ k + revFn (fun i => ⌊cq ξ i⌋) k : ℝ)) : EReal) < y :=
      Filter.eventually_lt_of_limsup_lt hy
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hevC
    set N := max N0 1 with hNdef
    have hN1 : 1 ≤ N := le_max_right _ _
    have hNge : ∀ k ≥ N, (((cq ξ k + revFn (fun i => ⌊cq ξ i⌋) k : ℝ)) : EReal) < y :=
      fun k hk => hN0 k (le_trans (le_max_left _ _) hk)
    obtain ⟨δ, hδpos, hδ⟩ := exists_pos_forall_den_ge hξ N hN1
    have hev1 : ∀ᶠ x in 𝓝[≠] ξ, |x - ξ| < δ := by
      have hmem : Metric.ball ξ δ ∈ 𝓝 ξ := Metric.ball_mem_nhds ξ hδpos
      have hev : ∀ᶠ x in 𝓝 ξ, |x - ξ| < δ := by
        filter_upwards [hmem] with x hx
        rw [Metric.mem_ball, Real.dist_eq] at hx
        exact hx
      exact hev.filter_mono nhdsWithin_le_nhds
    have hne_ev : ∀ᶠ x in 𝓝[≠] ξ, x ≠ ξ := by
      rw [eventually_nhdsWithin_iff]
      exact Filter.Eventually.of_forall fun x hx => hx
    have hevQ : ∀ᶠ x in 𝓝[≠] ξ, |x - ξ| < δ ∧ x ≠ ξ := hev1.and hne_ev
    have hevQ' : ∀ᶠ q : ℚ in Filter.comap ((↑) : ℚ → ℝ) (𝓝[≠] ξ),
        |(q : ℝ) - ξ| < δ ∧ (q : ℝ) ≠ ξ :=
      Filter.preimage_mem_comap hevQ
    filter_upwards [hevQ'] with q hq
    obtain ⟨hqδ, hqne⟩ := hq
    have hden := hδ q hqne hqδ
    obtain ⟨n, hnN, hn1, hn2⟩ := exists_dens_interval hξ N (q.den : ℝ)
      (by exact_mod_cast q.pos) hden
    have hbound := quality_le_max hξ q hqne n hn1 hn2
    have hFle : (((1 / (((q.den : ℝ)) ^ 2 * |(q : ℝ) - ξ|) : ℝ)) : EReal) ≤ y := by
      have h1 : (((1 / (((q.den : ℝ)) ^ 2 * |(q : ℝ) - ξ|) : ℝ)) : EReal) ≤
          (((max (cq ξ (n + 1) + revFn (fun i => ⌊cq ξ i⌋) (n + 1))
            (cq ξ (n + 2) + revFn (fun i => ⌊cq ξ i⌋) (n + 2)) : ℝ)) : EReal) := by
        exact_mod_cast hbound
      have h2 : (((max (cq ξ (n + 1) + revFn (fun i => ⌊cq ξ i⌋) (n + 1))
            (cq ξ (n + 2) + revFn (fun i => ⌊cq ξ i⌋) (n + 2)) : ℝ)) : EReal) =
          max (((cq ξ (n + 1) + revFn (fun i => ⌊cq ξ i⌋) (n + 1) : ℝ)) : EReal)
            (((cq ξ (n + 2) + revFn (fun i => ⌊cq ξ i⌋) (n + 2) : ℝ)) : EReal) :=
        coe_max_ereal _ _
      rw [h2] at h1
      exact (h1.trans_lt (max_lt (hNge (n + 1) (by omega)) (hNge (n + 2) (by omega)))).le
    exact hFle
  · apply Filter.le_limsup_of_le
    · isBoundedDefault
    intro b hb
    apply Filter.limsup_le_of_le
    · isBoundedDefault
    have htQ : Filter.Tendsto (fun k : ℕ => ξ.convergent k) Filter.atTop
        (Filter.comap ((↑) : ℚ → ℝ) (𝓝[≠] ξ)) := by
      rw [Filter.tendsto_comap_iff]
      exact tendsto_convergent hξ
    have hev : ∀ᶠ k : ℕ in Filter.atTop,
        (((1 / ((((ξ.convergent k).den : ℝ)) ^ 2 *
          |((ξ.convergent k : ℚ) : ℝ) - ξ|) : ℝ)) : EReal) ≤ b :=
      htQ.eventually hb
    rw [Filter.eventually_atTop] at hev ⊢
    obtain ⟨N0, hN0⟩ := hev
    refine ⟨max (N0 + 1) 1, fun k hk => ?_⟩
    have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
    have hQC := quality_convergent hξ (k - 1)
    have hk' : k - 1 + 1 = k := by omega
    rw [hk'] at hQC
    have hle := hN0 (k - 1) (by omega)
    rw [hQC] at hle
    exact hle

end

end

end MetaMathlibExt
