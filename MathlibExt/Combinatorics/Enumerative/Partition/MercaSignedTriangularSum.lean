/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.MercaDistinctPartsSum
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanPsiFChi
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# Merca's signed triangular identity

Gauss's triangular series at `-q`, multiplied by the ordinary partition generating function,
is the series for partitions into distinct parts with all sizes doubled. Multiplying by the
residue-class weight series gives Ballantine's identity.
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

namespace sumDistinctPartsModEq_triangular_eq_distinct_half

/-- The series with weight `w k` at degree `d k`, when `d` is injective and `k ≤ d k`. -/
private noncomputable def indexedSeries (d : ℕ → ℕ) (w : ℕ → ℤ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => ∑ k ∈ range (n + 1), if d k = n then w k else 0

private lemma coeff_indexedSeries_at {d : ℕ → ℕ} (hinj : Function.Injective d)
    (hle : ∀ k, k ≤ d k) (w : ℕ → ℤ) (k : ℕ) :
    coeff (d k) (indexedSeries d w) = w k := by
  rw [indexedSeries, coeff_mk, sum_eq_single_of_mem k (mem_range_succ_iff.mpr (hle k))]
  · simp
  · intro j _ hj
    exact ite_eq_right (fun h => hj (hinj h))

private lemma coeff_indexedSeries_off {d : ℕ → ℕ} (w : ℕ → ℤ) {n : ℕ}
    (hn : n ∉ Set.range d) : coeff n (indexedSeries d w) = 0 := by
  rw [indexedSeries, coeff_mk]
  exact sum_eq_zero fun k _ => ite_eq_right (fun h => hn ⟨k, h⟩)

private lemma coeff_indexedSeries_mul {d : ℕ → ℕ} (hinj : Function.Injective d)
    (hle : ∀ k, k ≤ d k) (w : ℕ → ℤ) (G : ℤ⟦X⟧) (n : ℕ) :
    coeff n (indexedSeries d w * G) =
      ∑ k ∈ (range (n + 1)).filter (fun k => d k ≤ n), w k * coeff (n - d k) G := by
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  refine sum_of_injOn d hinj.injOn (fun k hk => mem_range_succ_iff.mpr (mem_filter.mp hk).2)
    (fun i hi hm => ?_) (fun k _ => ?_)
  · have h : i ∉ Set.range d := by
      rintro ⟨k, rfl⟩
      have hkn := mem_range_succ_iff.mp hi
      exact hm ⟨k, mem_filter.mpr ⟨mem_range_succ_iff.mpr ((hle k).trans hkn), hkn⟩, rfl⟩
    rw [coeff_indexedSeries_off w h, zero_mul]
  · rw [coeff_indexedSeries_at hinj hle]

private def triangle (k : ℕ) : ℕ := k * (k + 1) / 2

private lemma twice_triangle (k : ℕ) : 2 * triangle k = k * (k + 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self k)

private lemma triangle_injective : Function.Injective triangle := by
  refine (show StrictMono triangle from ?_).injective
  intro a b hab
  nlinarith [twice_triangle a, twice_triangle b]

private lemma le_triangle (k : ℕ) : k ≤ triangle k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · decide
  · nlinarith [twice_triangle k]

private noncomputable def signedTriangular : ℤ⟦X⟧ :=
  indexedSeries triangle fun k => (-1) ^ triangle k

/-! ### Gauss's identity at `-q` -/

open QPochhammer

private lemma norm_pow_lt {q : ℂ} (hq : ‖q‖ < 1) {k : ℕ} (hk : k ≠ 0) : ‖q ^ k‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq hk

private lemma diagonal_eq_euler {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q = eulerFunction q := by
  rw [eulerFunction_eq_tprod hq]
  simp only [qPochhammerInfRaw, pow_succ' q]

private lemma diagonal_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : qPochhammerInfRaw q q ≠ 0 := by
  rw [diagonal_eq_euler hq, eulerFunction_eq_tprod hq]
  simp_rw [sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro k hk
    have he : q ^ (k + 1) = 1 := by linear_combination -hk
    simpa [he] using norm_pow_lt hq (Nat.succ_ne_zero k)
  · simpa [pow_succ, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right ‖q‖

private lemma gauss_negative {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw (-q) ((-q) ^ 3) * eulerFunction (q ^ 2) =
      eulerFunction q * eulerFunction (q ^ 4) := by
  have hneg : ‖-q‖ < 1 := by simpa using hq
  have h₂ := norm_pow_lt hq two_ne_zero
  have h₄ := norm_pow_lt hq (by decide : (4 : ℕ) ≠ 0)
  have hs := HasProd.even_mul_odd (f := fun k : ℕ => 1 - (-q) * (-q) ^ k)
    ((hasProd_qPochhammerInf (-q) (q ^ 2) h₂).congr_fun fun k => by
      rw [pow_mul, neg_sq])
    ((hasProd_qPochhammerInf (q ^ 2) (q ^ 2) h₂).congr_fun fun k => by
      rw [pow_succ, pow_mul, neg_sq]; ring)
  have hsplit : qPochhammerInfRaw (-q) (-q) =
      qPochhammerInfRaw (-q) (q ^ 2) * qPochhammerInfRaw (q ^ 2) (q ^ 2) :=
    (hasProd_qPochhammerInf (-q) (-q) hneg).unique hs
  have hψ := (ramanujan_psi_f_chi_eq_qPochhammer (-q) hneg).1
  rw [neg_sq, eq_div_iff (diagonal_ne_zero hneg)] at hψ
  have hχ := (ramanujan_psi_f_chi_eq_qPochhammer q hq).2.2.1
  rw [eq_div_iff (mul_ne_zero (diagonal_ne_zero hq) (diagonal_ne_zero h₄))] at hχ
  rw [← diagonal_eq_euler hq, ← diagonal_eq_euler h₂, ← diagonal_eq_euler h₄]
  apply mul_right_cancel₀ (diagonal_ne_zero hneg)
  calc
    _ = (ramanujanThetaRaw (-q) ((-q) ^ 3) * qPochhammerInfRaw (-q) (-q)) *
        qPochhammerInfRaw (q ^ 2) (q ^ 2) := by ac_rfl
    _ = (qPochhammerInfRaw (-q) (q ^ 2) *
        (qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 4) (q ^ 4))) *
        qPochhammerInfRaw (q ^ 2) (q ^ 2) := by rw [hψ, hχ]
    _ = _ := by rw [hsplit]; ac_rfl

/-- Interleave the nonpositive and positive theta indices, in triangular-degree order. -/
private def thetaIndex (k : ℕ) : ℤ :=
  if k % 2 = 0 then -((k / 2 : ℕ) : ℤ) else (k / 2 : ℕ) + 1

private lemma thetaIndex_bijective : Function.Bijective thetaIndex := by
  constructor
  · intro a b hab
    unfold thetaIndex at hab
    split at hab <;> split at hab <;> omega
  · intro z
    by_cases hz : z ≤ 0
    · refine ⟨2 * (-z).toNat, ?_⟩
      simp [thetaIndex]; omega
    · refine ⟨2 * (z - 1).toNat + 1, ?_⟩
      simp [thetaIndex]; omega

private lemma thetaTerm_eq_pow (x : ℂ) (k : ℕ) :
    ramanujanThetaTerm x (x ^ 3) (thetaIndex k) = x ^ triangle k := by
  let z := thetaIndex k
  have ha : 0 ≤ z * (z + 1) := by
    rcases le_or_gt 0 z with hz | hz
    · exact mul_nonneg hz (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos hz.le (by omega)
  have hb : 0 ≤ z * (z - 1) := by
    rcases le_or_gt z 0 with hz | hz
    · exact mul_nonneg_of_nonpos_of_nonpos hz (by omega)
    · exact mul_nonneg hz.le (by omega)
  have hcalc : (k : ℤ) = -2 * z ∨ (k : ℤ) = 2 * z - 1 := by
    dsimp [z, thetaIndex]
    split <;> omega
  change x ^ (z * (z + 1) / 2).toNat * (x ^ 3) ^ (z * (z - 1) / 2).toNat = _
  rw [← pow_mul, ← pow_add]
  congr 1
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg ha (by decide : (0 : ℤ) ≤ 2)),
    Int.toNat_of_nonneg (Int.ediv_nonneg hb (by decide : (0 : ℤ) ≤ 2))]
  have htri : 2 * (triangle k : ℤ) = (k : ℤ) * (k + 1) := by exact_mod_cast twice_triangle k
  rcases hcalc with hx | hx <;> rw [hx] at htri <;>
    nlinarith only [htri, Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self z),
      Int.two_mul_ediv_two_of_even (Int.even_mul_pred_self z)]

private lemma hasSum_signedTriangular {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (signedTriangular.coeff n : ℂ) * q ^ n)
      (ramanujanThetaRaw (-q) ((-q) ^ 3)) := by
  let e := Equiv.ofBijective thetaIndex thetaIndex_bijective
  have hs : Summable (fun k : ℕ => (-q) ^ triangle k) := by
    apply Summable.of_norm
    refine (summable_geometric_of_lt_one (norm_nonneg q) hq).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun k => ?_
    rw [norm_pow, norm_neg]
    exact pow_le_pow_of_le_one (norm_nonneg q) hq.le (le_triangle k)
  have hterm (k : ℕ) : (signedTriangular.coeff (triangle k) : ℂ) * q ^ triangle k =
      (-q) ^ triangle k := by
    rw [signedTriangular, coeff_indexedSeries_at triangle_injective le_triangle]
    simp [← mul_pow]
  have hraw : ramanujanThetaRaw (-q) ((-q) ^ 3) = ∑' k : ℕ, (-q) ^ triangle k := by
    rw [ramanujanThetaRaw, ← e.tsum_eq (ramanujanThetaTerm (-q) ((-q) ^ 3))]
    exact tsum_congr (thetaTerm_eq_pow (-q))
  rw [hraw]
  apply (triangle_injective.hasSum_iff ?_).mp
  · exact hs.hasSum.congr_fun hterm
  · intro n hn
    simp [signedTriangular, coeff_indexedSeries_off _ hn]

/-! ### Transfer to formal series -/

private lemma hasProd_expand {f : ℕ → ℤ⟦X⟧} {F : ℤ⟦X⟧} (h : HasProd f F)
    (k : ℕ) (hk : k ≠ 0) : HasProd (fun i => (f i).expand k hk) (F.expand k hk) := by
  refine h.map (expand k hk) ?_
  rw [continuous_iff_continuousAt]
  intro G
  rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  by_cases hd : k ∣ n
  · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto G
  · simp [coeff_expand, hd]

private lemma hasProd_euler_expand (k : ℕ) (hk : k ≠ 0) :
    HasProd (fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (k * (i + 1))) (expand k hk (pentagonalSeries ℤ)) := by
  refine (hasProd_expand (WithPiTopology.hasProd_one_sub_X_pow ℤ) k hk).congr_fun fun i => ?_
  simp [pow_mul]

private lemma hasProd_eulerSeries (k : ℕ) (hk : k ≠ 0) :
    HasProd (fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (k * (i + 1))) (qEulerProduct k) :=
  (hasProd_euler_expand k hk).multipliable.hasProd

private lemma eulerSeries_eq_expand (k : ℕ) (hk : k ≠ 0) :
    qEulerProduct k = expand k hk (pentagonalSeries ℤ) :=
  (hasProd_euler_expand k hk).tprod_eq

open UpperHalfPlane Function

local notation "𝕢" => Periodic.qParam 1

/-- A complex function represented by an integer power series on the punctured disk. -/
private def Represents (F : ℤ⟦X⟧) (f : ℂ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ => (F.coeff n : ℂ) * 𝕢 τ ^ n) (f (𝕢 τ))

private lemma Represents.mul {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g) : Represents (F * G) (fun q => f q * g q) := by
  intro τ
  let ι := Int.castRingHom ℂ
  simpa [← map_mul, coeff_map, ι] using
    ModularCurve.hasSum_qParam_mul 1 one_pos (map ι F) (map ι G)
      (fun z => f (𝕢 z)) (fun z => g (𝕢 z))
      (by simpa [coeff_map, ι, Represents] using hf)
      (by simpa [coeff_map, ι, Represents] using hg) τ

private lemma represents_euler (k : ℕ) (hk : k ≠ 0) :
    Represents (qEulerProduct k) (fun q => eulerFunction (q ^ k)) := by
  rw [eulerSeries_eq_expand k hk]
  intro τ
  have hq : ‖𝕢 τ‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  apply ((mul_right_injective₀ hk : Function.Injective (k * · : ℕ → ℕ)).hasSum_iff ?_).mp
  · refine (hasSum_eulerFunction_pentagonalSeries (norm_pow_lt hq hk)).congr_fun fun n => ?_
    simp only [Function.comp_apply, coeff_expand_mul, pow_mul]
    congr 1
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨m, rfl⟩ := hn
      simp [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  · intro n hn
    have hd : ¬ k ∣ n := by simpa [dvd_def, eq_comm] using hn
    simp [coeff_expand_of_not_dvd _ _ _ hd]

private lemma Represents.eq_of_eval {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g)
    (heq : ∀ q : ℂ, ‖q‖ < 1 → f q = g q) : F = G := by
  have hzero : cuspFunction 1 (0 : ℍ → ℂ) = 0 := by
    simp [cuspFunction, Pi.zero_comp, Periodic.cuspFunction_zero]
  have han : AnalyticAt ℂ (cuspFunction 1 (0 : ℍ → ℂ)) 0 := hzero ▸ analyticAt_const
  let c (m : ℕ) : ℂ := (F.coeff m : ℂ) - G.coeff m
  have hh := hasFPowerSeriesOnBall_cuspFunction (c := c) one_pos han fun τ => by
    have he := heq _ (Periodic.norm_qParam_lt_one one_pos τ.im_pos)
    simpa [c, smul_eq_mul, sub_mul, he] using (hf τ).sub (hg τ)
  rw [hzero] at hh
  have hz := hh.hasFPowerSeriesAt.eq_zero_of_eventually (Filter.EventuallyEq.refl _ _)
  apply PowerSeries.ext
  intro n
  have hc := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp (congrFun hz n)
  simpa [c, sub_eq_zero] using hc

private lemma signedTriangular_mul_euler_two :
    signedTriangular * qEulerProduct 2 = qEulerProduct 1 * qEulerProduct 4 := by
  have hT : Represents signedTriangular (fun q => ramanujanThetaRaw (-q) ((-q) ^ 3)) :=
    fun τ => hasSum_signedTriangular (Periodic.norm_qParam_lt_one one_pos τ.im_pos)
  exact (hT.mul (represents_euler 2 two_ne_zero)).eq_of_eval
    ((represents_euler 1 one_ne_zero).mul (represents_euler 4 (by decide))) fun q hq => by
      simpa using gauss_negative hq

/-! ### Partition products and coefficient extraction -/

private noncomputable def partitions : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => (Fintype.card (Nat.Partition n) : ℤ)

private lemma partitions_mul_euler : partitions * qEulerProduct 1 = 1 := by
  have hP : Nat.Partition.genFun (fun _ _ => (1 : ℤ)) = partitions := by
    ext n
    simp [partitions, Nat.Partition.coeff_genFun, Finsupp.prod]
  have h := (Nat.Partition.hasProd_genFun (fun _ _ => (1 : ℤ))).mul
    (hasProd_eulerSeries 1 one_ne_zero)
  rw [hP] at h
  refine h.unique (hasProd_one.congr_fun fun i => ?_)
  let Y := (X : ℤ⟦X⟧) ^ (i + 1)
  have hY : constantCoeff Y = 0 := by simp [Y]
  have hs := WithPiTopology.summable_pow_of_constantCoeff_eq_zero hY
  simp_rw [PowerSeries.smul_eq_C_mul, map_one, one_mul]
  simpa [Y, pow_mul, ← hs.sum_add_tsum_nat_add 1] using
    WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hY

private noncomputable def distinct : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => ((Nat.Partition.distincts n).card : ℤ)

private lemma coeff_distinct_expand (n : ℕ) :
    coeff n (distinct.expand 2 two_ne_zero) =
      if Even n then ((Nat.Partition.distincts (n / 2)).card : ℤ) else 0 := by
  rw [coeff_expand]
  by_cases hn : Even n
  · simp [hn, even_iff_two_dvd.mp hn, distinct]
  · have hd : ¬ 2 ∣ n := fun hd => hn (even_iff_two_dvd.mpr hd)
    rw [ite_eq_right hn, ite_eq_right hd]

private lemma distinct_mul_euler : distinct * qEulerProduct 1 = qEulerProduct 2 := by
  have hd : HasProd (fun i : ℕ => (1 : ℤ⟦X⟧) + X ^ (i + 1)) distinct := by
    simpa [distinct, Nat.Partition.countRestricted_two, sum_range_succ] using
      Nat.Partition.hasProd_powerSeriesMk_card_countRestricted ℤ (m := 2) (by decide)
  refine ((hd.mul (hasProd_eulerSeries 1 one_ne_zero)).congr_fun fun i => ?_).unique
    (hasProd_eulerSeries 2 two_ne_zero)
  simp only [one_mul, pow_mul]
  ring

private lemma signedTriangular_mul_partitions : signedTriangular * partitions =
    distinct.expand 2 two_ne_zero := by
  have h₂ : qEulerProduct 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [constantCoeff_qEulerProduct (by decide : 1 ≤ 2)] at h'
  -- Expanding `f₁` and `f₂` doubles each exponent.
  have h4 : (qEulerProduct 2).expand 2 two_ne_zero = qEulerProduct 4 := by
    rw [eulerSeries_eq_expand 2 two_ne_zero, ← expand_mul, ← eulerSeries_eq_expand 4 (by decide)]
  have hd := congrArg (expand 2 two_ne_zero) distinct_mul_euler
  rw [map_mul, qEulerProduct_one, ← eulerSeries_eq_expand 2 two_ne_zero, h4] at hd
  apply mul_right_cancel₀ h₂
  calc
    _ = (signedTriangular * qEulerProduct 2) * partitions := by ac_rfl
    _ = qEulerProduct 4 * (partitions * qEulerProduct 1) := by
      rw [signedTriangular_mul_euler_two]; ac_rfl
    _ = qEulerProduct 4 := by rw [partitions_mul_euler, mul_one]
    _ = _ := hd.symm

private noncomputable def progression (m r : ℕ) : ℤ⟦X⟧ :=
  indexedSeries (fun j => m * j + r) (fun j => ((m * j + r : ℕ) : ℤ))

private lemma coeff_progression_mul (m r n : ℕ) (hrm : r < m) (G : ℤ⟦X⟧) :
    coeff n (progression m r * G) =
      ∑ j ∈ (range (n + 1)).filter (fun j => m * j + r ≤ n),
        ((m * j + r : ℕ) : ℤ) * coeff (n - (m * j + r)) G := by
  have hm : 0 < m := Nat.zero_le r |>.trans_lt hrm
  exact coeff_indexedSeries_mul
    (fun _ _ h => Nat.eq_of_mul_eq_mul_left hm (Nat.add_right_cancel h))
    (fun j => by nlinarith) _ _ _

private lemma coeff_progression_mul_partitions (m r n : ℕ) (hrm : r < m) :
    coeff n (progression m r * partitions) = (sumDistinctPartsModEq m r n : ℤ) := by
  -- For `r = 0`, the index `j = 0` is present but its weight is zero.
  rw [coeff_progression_mul m r n hrm, sumDistinctPartsModEq_eq_sum_partition m r n hrm,
    Nat.cast_sum]
  simp [partitions]

end sumDistinctPartsModEq_triangular_eq_distinct_half

open sumDistinctPartsModEq_triangular_eq_distinct_half in
/-- **Signed triangular sum of $a_{r,m}$ and distinct partitions.** Let $m, r, n$ be natural
numbers with $r < m$. Write $a_{r,m}(k)$ for the sum of the different parts congruent to $r$
modulo $m$ in all partitions of $k$, $q(k)$ for the number of partitions of $k$ into distinct
parts, and $\tilde q(\ell)$ for $q(\ell/2)$ when $\ell$ is even and for $0$ when $\ell$ is odd.
Then
$$
\sum_{k \ge 0,\ k(k+1)/2 \le n} (-1)^{k(k+1)/2} a_{r,m}\bigl(n - k(k+1)/2\bigr)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, \tilde q(n - mj - r).
$$

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 6 (`integers-2024-A15-thm-6`). -/
public theorem sumDistinctPartsModEq_triangular_eq_distinct_half (m r n : ℕ)
    (hrm : r < m) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
        (-1 : ℤ) ^ (k * (k + 1) / 2) * (sumDistinctPartsModEq m r (n - k * (k + 1) / 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
          ((m * j + r : ℕ) : ℤ) *
            if Even (n - (m * j + r)) then
              ((Nat.Partition.distincts ((n - (m * j + r)) / 2)).card : ℤ)
            else 0 := by
  have h : signedTriangular * (progression m r * partitions) =
      progression m r * distinct.expand 2 two_ne_zero := by
    rw [← signedTriangular_mul_partitions]
    ac_rfl
  have hc := congrArg (coeff n) h
  rw [signedTriangular, coeff_indexedSeries_mul triangle_injective le_triangle,
    coeff_progression_mul m r n hrm] at hc
  simp only [coeff_progression_mul_partitions m r _ hrm, triangle] at hc
  -- The expansion has zero coefficients in odd degrees.
  refine hc.trans (sum_congr rfl fun j _ => ?_)
  rw [coeff_distinct_expand]

end MetaMathlibExt
