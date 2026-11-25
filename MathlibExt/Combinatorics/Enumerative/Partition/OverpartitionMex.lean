/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import MathlibExt.Combinatorics.Enumerative.Partition.OverpartitionMexSum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanPsiFChi
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# Minimal excludants of overpartitions

The sum of the least missing non-overlined parts of the overpartitions of a positive integer
equals the number of its partitions into distinct parts in three colors, and it is odd exactly at
triangular numbers.

For the first statement, the sum is the coefficient of the overpartition series times Gauss's
triangular series `ψ(q) = ∑ q^{k(k+1)/2}`. Gauss's identity `ψ(q) f(q) = f(q²)²`, with
`f(q) = ∏ (1 - q^m)`, is transferred to integer power series from its form on the unit disk, and
the product is the cube of the distinct-part series `∏ (1 + q^m)`.
-/

namespace MetaMathlibExt

@[expose] public section

/--
**Three-colored distinct-part partitions.** For a natural number $n$, $D_3(n)$ is the number of
triples $(A, B, C)$ of subsets of $\{1, \dots, n\}$ such that the sum of the elements of $A$, the
sum of the elements of $B$ and the sum of the elements of $C$ add up to $n$. Here $A$, $B$, $C$
are the parts of the three colors of a partition of $n$ whose parts of each color are distinct.

A size may occur in several colors but at most once in each, as in the product
$\prod_{m \ge 1} (1 + q^m)^3$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public def D3 (n : ℕ) : ℕ :=
  ((((Finset.Icc 1 n).powerset.product (Finset.Icc 1 n).powerset).product
    (Finset.Icc 1 n).powerset).filter fun p =>
      p.1.1.sum id + p.1.2.sum id + p.2.sum id = n).card

/--
**Three-colored distinct-part partitions of $0$.** The number $D_3(0)$ of partitions of $0$ into
parts of three colors, with the parts of each color distinct, equals $1$: the empty partition is
the only one.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_zero : D3 0 = 1 := by
  decide

/--
**Three-colored distinct-part partitions of $1$.** The number $D_3(1)$ of partitions of $1$ into
parts of three colors, with the parts of each color distinct, equals $3$: the single part $1$
takes one of the three colors.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_one : D3 1 = 3 := by
  decide

/--
**Three-colored distinct-part partitions of $2$.** The number $D_3(2)$ of partitions of $2$ into
parts of three colors, with the parts of each color distinct, equals $6$: the single part $2$ in
one of three colors, or two parts $1$ in two different colors.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Definition of `D_3(n)`.
-/
public theorem D3_two : D3 2 = 6 := by
  decide

namespace sigmaMexOverpartition_parity

open Finset

private theorem count_even {n : ℕ} (hn : 0 < n) : overpartitionCount n ≡ 0 [MOD 2] := by
  unfold overpartitionCount Nat.Overpartition.instFintype
  rw [Fintype.ofEquiv_card, Fintype.card_sigma]
  apply Nat.ModEq.sum_zero
  intro p _
  rw [Fintype.card_coe, card_powerset]
  apply Nat.modEq_zero_iff_dvd.mpr
  apply dvd_pow_self
  intro h
  have hempty : p.parts = 0 := by simpa using card_eq_zero.mp h
  have := p.parts_sum
  simp [hempty] at this
  omega

end sigmaMexOverpartition_parity

open sigmaMexOverpartition_parity Finset in
/--
**Parity of the overpartition mex sum.** For an overpartition $\pi$, let
$\overline{\mathrm{mex}}(\pi)$ be the least positive integer that does not occur among the
non-overlined parts of $\pi$, and let $\sigma\overline{\mathrm{mex}}(n)$ be the sum of
$\overline{\mathrm{mex}}(\pi)$ over all overpartitions $\pi$ of $n$. For every positive integer
$n$, $\sigma\overline{\mathrm{mex}}(n)$ is odd if $n = j(j+1)/2$ is a triangular number for some
natural number $j$, and even otherwise.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 4.
-/
public theorem sigmaMexOverpartition_parity (n : ℕ) (hn : 0 < n) :
    ((∃ j : ℕ, n = (j * (j + 1) / 2)) →
      Nat.ModEq 2 (sigmaMexOverpartition 1 n) 1) ∧
    ((¬∃ j : ℕ, n = (j * (j + 1) / 2)) →
      Nat.ModEq 2 (sigmaMexOverpartition 1 n) 0) := by
  let triangular (k : ℕ) := k * (k + 1) / 2
  have triangular_strictMono : StrictMono triangular := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h : triangular (k + 1) = triangular k + (k + 1) := by
      simpa [triangular, Nat.mul_comm] using Nat.triangle_succ (k + 1)
    omega
  have shifted_count_parity (m : ℕ) :
      (if m ≤ n then overpartitionCount (n - m) else 0) ≡ (if n = m then 1 else 0) [MOD 2] := by
    split_ifs with h heq heq
    · rw [heq, Nat.sub_self, overpartitionCount_zero]
    · exact count_even (by omega)
    · omega
    · rfl
  have hsum : sigmaMexOverpartition 1 n ≡
      ∑ k ∈ range (n + 1), (if n = triangular k then 1 else 0) [MOD 2] := by
    rw [← sigmaMexOverpartition_eq_sum_shifted_count n 1 le_rfl, sum_filter]
    simp only [one_mul]
    exact Nat.ModEq.sum fun k _ => shifted_count_parity (triangular k)
  constructor
  · rintro ⟨j | j, hj⟩
    · have : n = 0 := hj.trans (by decide)
      omega
    · have hmem : j + 1 ∈ range (n + 1) := mem_range.mpr
        (Nat.lt_succ_of_le (hj ▸ triangular_strictMono.id_le (j + 1)))
      have heq (k : ℕ) : n = triangular k ↔ j + 1 = k := by
        rw [hj, triangular_strictMono.injective.eq_iff]
      simpa only [heq, sum_ite_eq, hmem, ite_true] using hsum
  · intro h
    have hne (k : ℕ) : n ≠ triangular k := fun hk => h ⟨k, hk⟩
    simpa only [ite_eq_right (hne _), sum_const_zero] using hsum

namespace sigmaMexOverpartition_eq_D3

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

/-! ### Gauss's triangular series -/

private def tri (k : ℕ) : ℕ := k * (k + 1) / 2

private theorem tri_strictMono : StrictMono tri := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h : tri (k + 1) = tri k + (k + 1) := by
    simpa [tri, Nat.mul_comm] using Nat.triangle_succ (k + 1)
  omega

private theorem le_tri (k : ℕ) : k ≤ tri k := tri_strictMono.id_le k

/-- The series `ψ = ∑_{k ≥ 0} X^{k(k+1)/2}` of the triangular numbers. -/
private noncomputable def triSeries : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => Set.indicator (Set.range tri) 1 n

private theorem coeff_triSeries_tri (k : ℕ) : coeff (tri k) triSeries = 1 := by
  simp [triSeries]

private theorem coeff_triSeries_of_notMem {n : ℕ} (h : n ∉ Set.range tri) :
    coeff n triSeries = 0 := by
  simp [triSeries, Set.indicator_of_notMem h]

private theorem summable_pow_of_le {q : ℂ} (hq : ‖q‖ < 1) (g : ℕ → ℕ) (hg : ∀ j, j ≤ g j) :
    Summable fun j => q ^ g j := by
  refine (summable_geometric_of_lt_one (norm_nonneg q) hq).of_norm_bounded fun j => ?_
  rw [norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) hq.le (hg j)

-- The summand of `f(q³, q)` at `n` is `q^(2n² + n)`, a triangular power of `q`.
private theorem tri_exponent (n : ℤ) (m : ℕ) (h : 4 * n * n + 2 * n = (m : ℤ) * (m + 1)) :
    3 * (n * (n + 1) / 2).toNat + (n * (n - 1) / 2).toNat = tri m := by
  have h1 : 2 * (n * (n + 1) / 2) = n * (n + 1) :=
    Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self n)
  have h2 : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
    Int.two_mul_ediv_two_of_even (Int.even_mul_pred_self n)
  have h3 : 2 * tri m = m * (m + 1) := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self m)
  have hn1 : 0 ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with h | h
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos h.le (by omega)
  have hn2 : 0 ≤ n * (n - 1) := by
    rcases le_or_gt n 0 with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
    · exact mul_nonneg h.le (by omega)
  apply Nat.eq_of_mul_eq_mul_left two_pos
  have h3' : ((2 * tri m : ℕ) : ℤ) = (m : ℤ) * (m + 1) := by exact_mod_cast h3
  zify
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn1 (by norm_num)),
    Int.toNat_of_nonneg (Int.ediv_nonneg hn2 (by norm_num))]
  push_cast at h3'
  linear_combination 3 * h1 + h2 + h - h3'

private theorem term_nat (q : ℂ) (j : ℕ) :
    ramanujanThetaTerm (q ^ 3) q j = q ^ tri (2 * j) := by
  rw [ramanujanThetaTerm, ← pow_mul, ← pow_add]
  congr 1
  apply tri_exponent
  push_cast
  ring

private theorem term_neg (q : ℂ) (j : ℕ) :
    ramanujanThetaTerm (q ^ 3) q (-((j : ℤ) + 1)) = q ^ tri (2 * j + 1) := by
  rw [ramanujanThetaTerm, ← pow_mul, ← pow_add]
  congr 1
  apply tri_exponent
  push_cast
  ring

-- Even triangular indices come from `n ≥ 0`, odd ones from `n < 0`.
private theorem hasSum_tri {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun k => q ^ tri k) (ramanujanThetaRaw (q ^ 3) q) := by
  have he := (summable_pow_of_le hq (fun j => tri (2 * j))
    fun j => (Nat.le_mul_of_pos_left j two_pos).trans (le_tri _)).hasSum
  have ho := (summable_pow_of_le hq (fun j => tri (2 * j + 1))
    fun j => (by omega : j ≤ 2 * j + 1).trans (le_tri _)).hasSum
  have hz := HasSum.of_nat_of_neg_add_one (f := ramanujanThetaTerm (q ^ 3) q)
    (he.congr_fun fun j => term_nat q j) (ho.congr_fun fun j => term_neg q j)
  rw [ramanujanThetaRaw, hz.tsum_eq]
  exact he.even_add_odd ho

private theorem qPochhammerInfRaw_self {a : ℂ} (ha : ‖a‖ < 1) :
    QPochhammer.qPochhammerInfRaw a a = eulerFunction a := by
  rw [eulerFunction_eq_tprod ha, QPochhammer.qPochhammerInfRaw]
  exact tprod_congr fun n => by rw [pow_succ']

private theorem eulerFunction_ne_zero {q : ℂ} (h : ‖q‖ < 1) : eulerFunction q ≠ 0 := by
  rw [eulerFunction_eq_tprod h]
  simp_rw [sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro n he
    have he' : q ^ (n + 1) = 1 := by linear_combination -he
    have := pow_lt_one₀ (norm_nonneg q) h (Nat.succ_ne_zero n)
    rwa [← norm_pow, he', norm_one, lt_self_iff_false] at this
  · simpa [pow_succ, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) h).mul_right ‖q‖

/-- Gauss's identity `ψ(q) f(q) = f(q²)²` on the unit disk, from `ψ(q) = f(q, q³) = f₂² / f₁`. -/
private theorem gauss_analytic {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw (q ^ 3) q * eulerFunction q =
      eulerFunction (q ^ 2) * eulerFunction (q ^ 2) := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have h := (ramanujan_psi_f_chi_eq_qPochhammer q hq).1
  rw [qPochhammerInfRaw_self hq, qPochhammerInfRaw_self hq2] at h
  rw [ramanujanThetaRaw_symm, h, div_mul_cancel₀ _ (eulerFunction_ne_zero hq), sq]

/-! ### From functions on the disk to integer power series -/

section Transfer

open UpperHalfPlane Function

local notation "𝕢" => Periodic.qParam 1

/-- A complex function represented by an integer power series on the punctured unit disk. -/
private def Represents (F : ℤ⟦X⟧) (f : ℂ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ ↦ (F.coeff n : ℂ) * 𝕢 τ ^ n) (f (𝕢 τ))

private theorem Represents.mul {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g) :
    Represents (F * G) (fun q ↦ f q * g q) := by
  intro τ
  let ι := Int.castRingHom ℂ
  simpa [← map_mul, coeff_map, ι] using
    ModularCurve.hasSum_qParam_mul 1 one_pos (map ι F) (map ι G)
      (fun z ↦ f (𝕢 z)) (fun z ↦ g (𝕢 z))
      (by simpa [coeff_map, ι, Represents] using hf)
      (by simpa [coeff_map, ι, Represents] using hg) τ

private theorem Represents.eq_of_eval {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g)
    (heq : ∀ q : ℂ, ‖q‖ < 1 → f q = g q) : F = G := by
  have hzero : cuspFunction 1 (0 : ℍ → ℂ) = 0 := by
    simp [cuspFunction, Pi.zero_comp, Periodic.cuspFunction_zero]
  have han : AnalyticAt ℂ (cuspFunction 1 (0 : ℍ → ℂ)) 0 := hzero ▸ analyticAt_const
  let c (m : ℕ) : ℂ := (F.coeff m : ℂ) - G.coeff m
  have hh := hasFPowerSeriesOnBall_cuspFunction (c := c) one_pos han (fun τ ↦ by
    have he := heq _ (Periodic.norm_qParam_lt_one one_pos τ.im_pos)
    simpa [c, smul_eq_mul, sub_mul, he] using (hf τ).sub (hg τ))
  rw [hzero] at hh
  have hz := hh.hasFPowerSeriesAt.eq_zero_of_eventually (Filter.EventuallyEq.refl _ _)
  apply PowerSeries.ext
  intro n
  have hc := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp
    (congrFun hz n)
  simpa [c, sub_eq_zero] using hc

private theorem represents_pentagonal : Represents (pentagonalSeries ℤ) eulerFunction := by
  intro τ
  have lt1 : ‖𝕢 τ‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  refine (hasSum_eulerFunction_pentagonalSeries lt1).congr_fun fun n ↦ ?_
  congr 1
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨m, rfl⟩ := hn
    simp [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
  · simp [coeff_pentagonalSeries_eq_zero _ hn]

private theorem represents_expand_two :
    Represents (expand 2 two_ne_zero (pentagonalSeries ℤ)) (fun q ↦ eulerFunction (q ^ 2)) := by
  intro τ
  have lt1 : ‖𝕢 τ‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hk1 : ‖𝕢 τ ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) lt1 two_ne_zero
  have inj : Function.Injective (2 * ·) := mul_right_injective₀ two_ne_zero
  apply (inj.hasSum_iff ?_).mp
  · refine (hasSum_eulerFunction_pentagonalSeries hk1).congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, coeff_expand_mul, pow_mul]
    congr 1
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨m, rfl⟩ := hn
      simp [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  · intro n hn
    have hd : ¬ 2 ∣ n := fun ⟨c, hc⟩ => hn ⟨c, hc.symm⟩
    simp [coeff_expand_of_not_dvd _ _ _ hd]

private theorem represents_triSeries :
    Represents triSeries (fun q ↦ ramanujanThetaRaw (q ^ 3) q) := by
  intro τ
  have lt1 : ‖𝕢 τ‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  apply (tri_strictMono.injective.hasSum_iff ?_).mp
  · refine (hasSum_tri lt1).congr_fun fun k ↦ ?_
    simp [coeff_triSeries_tri]
  · intro n hn
    simp [coeff_triSeries_of_notMem hn]

/-- Gauss's identity `ψ(q) f(q) = f(q²)²` in `ℤ⟦X⟧`. -/
private theorem triSeries_mul_pentagonal :
    triSeries * pentagonalSeries ℤ =
      expand 2 two_ne_zero (pentagonalSeries ℤ) * expand 2 two_ne_zero (pentagonalSeries ℤ) :=
  (represents_triSeries.mul represents_pentagonal).eq_of_eval
    (represents_expand_two.mul represents_expand_two) fun _ hq => gauss_analytic hq

end Transfer

/-! ### Overpartitions and distinct parts -/

/-- The generating function `∑ p̄(n) X^n = ∏_{m ≥ 1} (1 + X^m) / (1 - X^m)` of overpartitions. -/
private noncomputable abbrev opSeries : ℤ⟦X⟧ := Nat.Partition.genFun fun _ _ => (2 : ℤ)

private theorem coeff_opSeries (n : ℕ) : coeff n opSeries = overpartitionCount n := by
  rw [Nat.Partition.coeff_genFun]
  unfold overpartitionCount Nat.Overpartition.instFintype
  rw [Fintype.ofEquiv_card, Fintype.card_sigma]
  push_cast
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.card_coe, Finset.card_powerset]
  simp [Finsupp.prod, Multiset.toFinsupp_support]

-- Each factor `1 + 2 ∑_{j ≥ 1} X^{mj}` of `opSeries` times `1 - X^m` is `1 + X^m`.
private theorem hasProd_distinct :
    HasProd (fun i : ℕ => (1 : ℤ⟦X⟧) + X ^ (i + 1)) (opSeries * pentagonalSeries ℤ) := by
  refine ((Nat.Partition.hasProd_genFun fun _ _ => (2 : ℤ)).mul
    (WithPiTopology.hasProd_one_sub_X_pow ℤ)).congr_fun fun i => ?_
  have hc : constantCoeff (X ^ (i + 1) : ℤ⟦X⟧) = 0 := by simp
  have hS := WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hc
  have hA : ∑' j : ℕ, (2 * X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧) =
      2 * X ^ (i + 1) * ∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j := by
    rw [← (WithPiTopology.summable_pow_of_constantCoeff_eq_zero hc).tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [pow_mul, pow_succ]
    ring
  simp only [smul_eq_C_mul, map_ofNat, hA]
  linear_combination (-2 * X ^ (i + 1) : ℤ⟦X⟧) * hS

private theorem continuous_expand (k : ℕ) (hk : k ≠ 0) :
    Continuous (expand k hk : ℤ⟦X⟧ → ℤ⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro F
  rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  by_cases hd : k ∣ n
  · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto F
  · simp [coeff_expand, hd]

private theorem hasProd_expand_two :
    HasProd (fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (2 * (i + 1)))
      (expand 2 two_ne_zero (pentagonalSeries ℤ)) := by
  have h := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand 2 two_ne_zero)
    (continuous_expand 2 two_ne_zero)
  simpa [Function.comp_def, pow_mul] using h

/-- The distinct-part series `opSeries * f(q)` satisfies `D(q) f(q) = f(q²)`. -/
private theorem distinct_mul_pentagonal :
    opSeries * pentagonalSeries ℤ * pentagonalSeries ℤ =
      expand 2 two_ne_zero (pentagonalSeries ℤ) :=
  (hasProd_distinct.mul (WithPiTopology.hasProd_one_sub_X_pow ℤ)).unique
    (hasProd_expand_two.congr_fun fun i => by ring)

-- Factors that are `1` modulo `X^(n+1)` do not change a product below degree `n + 1`.
private theorem X_pow_dvd_sub_prod {u : ℕ → ℤ⟦X⟧} {P : ℤ⟦X⟧} (hP : HasProd u P) (n : ℕ)
    (hu : ∀ i, n ≤ i → X ^ (n + 1) ∣ u i - 1) :
    X ^ (n + 1) ∣ P - ∏ i ∈ range n, u i := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto] at hP
  have hev : ∀ᶠ s in Filter.atTop, ∀ d ∈ range (n + 1),
      coeff d (∏ i ∈ s, u i) = coeff d P := by
    refine (Filter.eventually_all_finset _).2 fun d _ => ?_
    have h := hP d
    rw [nhds_discrete, Filter.tendsto_pure] at h
    exact h
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.1 hev
  have h1 : X ^ (n + 1) ∣ P - ∏ i ∈ s₀ ∪ range n, u i := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [map_sub, hs₀ _ subset_union_left d (mem_range.2 hd), sub_self]
  have h2 : X ^ (n + 1) ∣ ∏ i ∈ s₀ ∪ range n, u i - ∏ i ∈ range n, u i := by
    rw [← prod_sdiff (subset_union_right : range n ⊆ s₀ ∪ range n)]
    have h3 : X ^ (n + 1) ∣ ∏ i ∈ (s₀ ∪ range n) \ range n, u i - 1 := by
      refine Finset.prod_induction _ (fun x => X ^ (n + 1) ∣ x - 1) (fun a b ha hb => ?_)
        (by simp) fun i hi => hu i ?_
      · have e : a * b - 1 = (a - 1) * b + (b - 1) := by ring
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_left ha _) hb
      · simpa using (mem_sdiff.1 hi).2
    have e : (∏ i ∈ (s₀ ∪ range n) \ range n, u i) * ∏ i ∈ range n, u i -
        ∏ i ∈ range n, u i = (∏ i ∈ (s₀ ∪ range n) \ range n, u i - 1) * ∏ i ∈ range n, u i := by
      ring
    rw [e]
    exact dvd_mul_of_dvd_left h3 _
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

private theorem X_pow_dvd_distinct_sub (n : ℕ) :
    X ^ (n + 1) ∣ opSeries * pentagonalSeries ℤ - ∏ m ∈ Icc 1 n, ((1 : ℤ⟦X⟧) + X ^ m) := by
  have h := X_pow_dvd_sub_prod hasProd_distinct n fun i hi => by
    rw [add_sub_cancel_left]
    exact pow_dvd_pow X (by omega)
  have e : ∏ i ∈ range n, ((1 : ℤ⟦X⟧) + X ^ (i + 1)) =
      ∏ m ∈ Icc 1 n, ((1 : ℤ⟦X⟧) + X ^ m) := by
    rw [range_eq_Ico, prod_Ico_add' (fun m => (1 : ℤ⟦X⟧) + X ^ m), zero_add,
      Ico_add_one_right_eq_Icc]
  rwa [e] at h

-- Expanding `∏_{m ≤ n} (1 + X^m)` over subsets reads off the triples counted by `D3`.
private theorem coeff_prod_cube (n : ℕ) :
    coeff n ((∏ m ∈ Icc 1 n, ((1 : ℤ⟦X⟧) + X ^ m)) ^ 3) = (D3 n : ℤ) := by
  have hF : ∏ m ∈ Icc 1 n, ((1 : ℤ⟦X⟧) + X ^ m) =
      ∑ t ∈ (Icc 1 n).powerset, X ^ (t.sum id) := by
    rw [prod_one_add]
    exact sum_congr rfl fun t _ => prod_pow_eq_pow_sum t id (X : ℤ⟦X⟧)
  rw [hF, pow_three, sum_mul_sum, sum_mul, D3, card_filter]
  simp only [Finset.product_eq_sprod, sum_product, mul_sum, ← pow_add, map_sum, coeff_X_pow,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  refine sum_congr rfl fun A _ => sum_congr rfl fun B _ => sum_congr rfl fun C _ => ?_
  simp only [eq_comm, add_assoc]

-- The coefficients of `opSeries * triSeries` are the shifted overpartition sums.
private theorem coeff_opSeries_mul_triSeries (n : ℕ) :
    coeff n (opSeries * triSeries) = sigmaMexOverpartition 1 n := by
  classical
  rw [← sigmaMexOverpartition_eq_sum_shifted_count n 1 le_rfl, mul_comm, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i triSeries * coeff j opSeries)]
  simp only [one_mul, coeff_opSeries, triSeries, coeff_mk, Set.indicator_apply, Pi.one_apply,
    ite_mul, zero_mul, Nat.cast_sum]
  rw [← sum_filter]
  have himage : ((range (n + 1)).filter fun k => k * (k + 1) / 2 ≤ n).image tri =
      (range (n + 1)).filter fun j => j ∈ Set.range tri := by
    ext j
    simp only [mem_image, mem_filter, mem_range, Set.mem_range]
    constructor
    · rintro ⟨k, ⟨-, hk⟩, rfl⟩
      exact ⟨by unfold tri; omega, k, rfl⟩
    · rintro ⟨hj, k, rfl⟩
      exact ⟨k, ⟨by have := le_tri k; omega, by unfold tri at hj; omega⟩, rfl⟩
  rw [← himage, sum_image fun a _ b _ h => tri_strictMono.injective h]
  rfl

end sigmaMexOverpartition_eq_D3

open sigmaMexOverpartition_eq_D3 PowerSeries in
/--
**The overpartition mex sum counts three-colored distinct-part partitions.** For an
overpartition $\pi$, let $\overline{\mathrm{mex}}(\pi)$ be the least positive integer that does
not occur among the non-overlined parts of $\pi$, and let $\sigma\overline{\mathrm{mex}}(n)$ be
the sum of $\overline{\mathrm{mex}}(\pi)$ over all overpartitions $\pi$ of $n$. For every
positive integer $n$, $\sigma\overline{\mathrm{mex}}(n) = D_3(n)$, the number of partitions of
$n$ into distinct parts in three colors: the number of triples $(A, B, C)$ of subsets of
$\{1, \dots, n\}$ whose three element sums add up to $n$.

Source: Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*,
Journal of Integer Sequences 27 (2024), Article 24.7.1, Theorem 2.
-/
public theorem sigmaMexOverpartition_eq_D3 (n : ℕ) (hn : 0 < n) :
    sigmaMexOverpartition 1 n = D3 n := by
  -- The argument works for every `n`; the source states the identity for positive `n`.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  have hE : pentagonalSeries ℤ ≠ 0 := by
    intro h
    have h0 := coeff_pentagonalSeries_pentagonal (R := ℤ) 0
    rw [h] at h0
    simp at h0
  -- With `D = opSeries * f(q)`, Gauss's identity gives `ψ = D² f(q)`, so `opSeries * ψ = D³`.
  have htri : triSeries = (opSeries * pentagonalSeries ℤ) ^ 2 * pentagonalSeries ℤ := by
    apply mul_right_cancel₀ hE
    rw [triSeries_mul_pentagonal, ← distinct_mul_pentagonal]
    ring
  have hcube : opSeries * triSeries = (opSeries * pentagonalSeries ℤ) ^ 3 := by
    rw [htri]
    ring
  have h3 := (X_pow_dvd_distinct_sub (m + 1)).trans (sub_dvd_pow_sub_pow _ _ 3)
  rw [X_pow_dvd_iff] at h3
  have h := h3 (m + 1) (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero, ← hcube, coeff_opSeries_mul_triSeries, coeff_prod_cube] at h
  exact_mod_cast h

end

end MetaMathlibExt
