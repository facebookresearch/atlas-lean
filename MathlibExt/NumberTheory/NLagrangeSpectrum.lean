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
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.NumberTheory.DiophantineApproximation.Hurwitz
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination

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

private theorem dens_eq_contsAux_b (ξ : ℝ) (n : ℕ) :
    (of ξ).dens n = ((of ξ).contsAux (n + 1)).b := rfl

private theorem den_eq_dens {ξ : ℝ} (hξ : Irrational ξ) (n : ℕ) :
    ((ξ.convergent n).den : ℝ) = (of ξ).dens n := by
  obtain ⟨a, b, hab⟩ := contsAux_int hξ (n + 1)
  have hB : (of ξ).dens n = (b : ℝ) := by
    rw [dens_eq_contsAux_b, hab]
  have hA : (of ξ).convs n = (a : ℝ) / (b : ℝ) := by
    rw [GenContFract.conv_eq_conts_a_div_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, hab]
  have hbpos : 0 < b := by
    have := dens_pos hξ n
    rw [hB] at this
    exact_mod_cast this
  -- The determinant identity gives coprimality.
  obtain ⟨a2, b2, hab2⟩ := contsAux_int hξ (n + 2)
  have hdet : (a : ℤ) * b2 - b * a2 = (-1 : ℤ) ^ (n + 1) := by
    have hd : (of ξ).nums n * (of ξ).dens (n + 1) - (of ξ).dens n * (of ξ).nums (n + 1)
        = (-1 : ℝ) ^ (n + 1) := (SimpContFract.of ξ).determinant (hinf hξ n)
    have hnums : (of ξ).nums n = (a : ℝ) := by
      rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux, hab]
    have hnums1 : (of ξ).nums (n + 1) = (a2 : ℝ) := by
      rw [GenContFract.num_eq_conts_a, GenContFract.nth_cont_eq_succ_nth_contAux, hab2]
    have hdens1 : (of ξ).dens (n + 1) = (b2 : ℝ) := by
      rw [dens_eq_contsAux_b, hab2]
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
  simpa only [dens_eq_contsAux_b, one_mul] using hb

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
    have hd1 : (of ξ).dens 1 = (⌊cq ξ 1⌋ : ℝ) :=
      GenContFract.first_den_eq (s_eq hξ 0)
    rw [hrev, hd1, Nat.sub_self, GenContFract.zeroth_den_eq_one]
    simp
  | succ n hn ih =>
    change revFn (fun i => ⌊cq ξ i⌋) (n + 2) = (of ξ).dens n / (of ξ).dens (n + 1)
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
  change (-1 : ℝ) ^ (n + 1) / (((ξ.convergent n).den : ℝ) ^ 2 *
        ((ξ.convergent n : ℝ) - ξ)) =
      (⌊cq ξ (n + 1)⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) (n + 1) + Int.fract (cq ξ (n + 1))
  have hstep : cq ξ (n + 1) = (Int.fract (cq ξ n))⁻¹ := by
    simp [cq, Function.iterate_succ_apply']
  have hsub := GenContFract.sub_convs_eq (v := ξ) (n := n) (ifp := ⟨⌊cq ξ n⌋, Int.fract (cq ξ n)⟩)
    (stream_eq hξ n)
  have hfr : Int.fract (cq ξ n) ≠ 0 := fract_cq_ne hξ n
  dsimp only at hsub
  rw [ite_eq_right hfr] at hsub
  rw [← dens_eq_contsAux_b, ← hstep] at hsub
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
      rw [← dens_eq_contsAux_b]
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


private theorem cut_eq {ξ : ℝ} (k : ℕ) :
    (⌊cq ξ k⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) k + Int.fract (cq ξ k) =
      cq ξ k + revFn (fun i => ⌊cq ξ i⌋) k := by
  linear_combination Int.floor_add_fract (cq ξ k)

private theorem tendsto_convergent {ξ : ℝ} (hξ : Irrational ξ) :
    Filter.Tendsto (fun k : ℕ => ((ξ.convergent k : ℚ) : ℝ)) Filter.atTop (𝓝[≠] ξ) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (GenContFract.of_convergence ξ).congr (Real.convs_eq_convergent ξ)
  · exact Filter.Eventually.of_forall fun k heq => hξ ⟨ξ.convergent k, heq⟩

private noncomputable def quality (ξ : ℝ) (q : ℚ) : ℝ :=
  1 / ((q.den : ℝ) ^ 2 * |(q : ℝ) - ξ|)

private theorem lt_quality_iff {ξ c : ℝ} (hξ : Irrational ξ) (hc : 0 < c) (q : ℚ) :
    c < quality ξ q ↔ |ξ - q| < 1 / (c * (q.den : ℝ) ^ 2) := by
  have hdist := abs_pos.mpr (sub_ne_zero.mpr (hξ.ne_rat q))
  rw [quality, abs_sub_comm (q : ℝ), lt_div_iff₀ (by positivity), lt_div_iff₀ (by positivity)]
  ring_nf

private theorem quality_convergent {ξ : ℝ} (hξ : Irrational ξ) (k : ℕ) :
    quality ξ (ξ.convergent k) =
      (⌊cq ξ (k + 1)⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) (k + 1) + Int.fract (cq ξ (k + 1)) := by
  have h := part_a hξ (k + 1) (by omega)
  rw [Nat.add_sub_cancel] at h
  have hpos : 0 < (⌊cq ξ (k + 1)⌋ : ℝ) + revFn (fun i => ⌊cq ξ i⌋) (k + 1) +
      Int.fract (cq ξ (k + 1)) := by
    have h1 : 1 < cq ξ (k + 1) := cq_gt_one hξ (by omega)
    have h2 := rev_nonneg hξ (k + 1)
    rw [cut_eq]
    linarith [h1, h2]
  have hdenpos : 0 < ((ξ.convergent k).den : ℝ) := by exact_mod_cast (ξ.convergent k).pos
  rw [quality, ← abs_of_pos hpos, ← h, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_mul,
    abs_of_pos (pow_pos hdenpos 2)]

/-- Hurwitz approximants occur beyond every finite prefix of the convergents. -/
private theorem sqrt_five_le_limsup {ξ : ℝ} (hξ : Irrational ξ) :
    (Real.sqrt 5 : EReal) ≤ limsup (fun n => (quality ξ (ξ.convergent n) : EReal)) atTop := by
  refine le_limsup_of_frequently_le ?_
  rw [frequently_atTop]
  intro N
  have hinf := Real.infinite_rat_abs_sub_lt_one_div_sqrt_five_mul_den_sq_of_irrational hξ
  obtain ⟨q, hq, hprefix⟩ := hinf.exists_notMem_finset ((Finset.range N).image ξ.convergent)
  have hgood := (lt_quality_iff hξ (by positivity : 0 < Real.sqrt 5) q).2 hq
  have htwo : (2 : ℝ) < Real.sqrt 5 := by norm_num [Real.lt_sqrt]
  obtain ⟨n, rfl⟩ := Real.exists_rat_eq_convergent ((lt_quality_iff hξ zero_lt_two q).1
    (htwo.trans hgood))
  refine ⟨n, ?_, EReal.coe_le_coe_iff.mpr hgood.le⟩
  exact le_of_not_gt fun hn => hprefix (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hn))

private theorem limsup_quality_convergent {ξ : ℝ} (hξ : Irrational ξ) :
    nLagrangeApproximability 1 ξ =
      limsup (fun n => (quality ξ (ξ.convergent n) : EReal)) atTop := by
  rw [nLagrangeApproximability_one]
  let F := comap ((↑) : ℚ → ℝ) (𝓝[≠] ξ)
  change limsup (fun q => (quality ξ q : EReal)) F = _
  apply le_antisymm
  · refine (limsup_le_iff).mpr fun b hb => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_limsup_lt hb)
    -- Near ξ we can exclude all convergents before the tail bounded by b.
    have havoid : ∀ᶠ x in 𝓝[≠] ξ, ∀ i ∈ Finset.range N, x ≠ (ξ.convergent i : ℝ) :=
      (eventually_all_finset _).2 fun i _ => eventually_ne_nhdsWithin (hξ.ne_rat _)
    filter_upwards [preimage_mem_comap (m := ((↑) : ℚ → ℝ)) havoid] with q hq
    by_cases hgood : 2 < quality ξ q
    · obtain ⟨n, rfl⟩ := Real.exists_rat_eq_convergent ((lt_quality_iff hξ zero_lt_two q).1 hgood)
      exact hN n (le_of_not_gt fun hn => hq n (Finset.mem_range.mpr hn) rfl)
    · have hle : quality ξ q ≤ Real.sqrt 5 :=
        (le_of_not_gt hgood).trans (by norm_num [Real.le_sqrt])
      exact (EReal.coe_le_coe_iff.mpr hle).trans_lt ((sqrt_five_le_limsup hξ).trans_lt hb)
  · have ht : Tendsto ξ.convergent atTop F := tendsto_comap_iff.mpr (tendsto_convergent hξ)
    exact ht.limsup_comp_le_limsup (u := fun q => (quality ξ q : EReal))

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
  dsimp only
  refine ⟨part_a hξ, ?_⟩
  rw [limsup_quality_convergent hξ]
  refine Eq.trans ?_ (limsup_nat_add _ 1)
  exact limsup_congr (.of_forall fun k => congrArg Real.toEReal (quality_convergent hξ k))

end

end

end MetaMathlibExt
