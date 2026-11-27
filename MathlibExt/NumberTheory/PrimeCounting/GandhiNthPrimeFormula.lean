/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

open scoped BigOperators

namespace MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted

@[expose] public section

/-- Möbius divisor-sum indicator: `∑_{d ∣ m} μ(d) = [m = 1]`. -/
private theorem gandhi_moebius_sum_divisors (m : ℕ) :
    ∑ d ∈ Nat.divisors m, ArithmeticFunction.moebius d
      = if m = 1 then 1 else 0 := by
  have h : ((ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℤ) m
      = (1 : ArithmeticFunction ℤ) m) := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- Geometric expansion of one divisor term:
`μ(d) / (2^d - 1) = ∑' k, μ(d) * (1/2)^(d*(k+1))` as a `HasSum`. -/
private theorem gandhi_hasSum_geom (d : ℕ) (hd : 1 ≤ d) :
    HasSum (fun k : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (1/2 : ℝ)^(d*(k+1)))
      (((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2:ℝ)^d - 1)) := by
  have hd0 : d ≠ 0 := by omega
  have hr0 : (0:ℝ) ≤ (1/2)^d := by positivity
  have hr1 : (1/2 : ℝ)^d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hd0
  have h2d : ((2:ℝ)^d) ≠ 0 := by positivity
  have h2d1 : ((2:ℝ)^d - 1) ≠ 0 := by
    have hlt : (1:ℝ) < 2^d := one_lt_pow₀ (by norm_num) hd0
    exact ne_of_gt (sub_pos.mpr hlt)
  have base := hasSum_geometric_of_lt_one hr0 hr1
  have scaled := base.mul_left (((ArithmeticFunction.moebius d : ℤ) : ℝ) * (1/2 : ℝ)^d)
  have hterm : ∀ k : ℕ, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (1/2 : ℝ)^(d*(k+1))
      = (((ArithmeticFunction.moebius d : ℤ) : ℝ) * (1/2 : ℝ)^d) * (((1/2 : ℝ)^d)^k) := by
    intro k
    rw [show d * (k + 1) = d * k + d by ring, pow_add, pow_mul]
    ring
  have hval : (((ArithmeticFunction.moebius d : ℤ) : ℝ) * (1/2 : ℝ)^d)
        * (1 - (1/2 : ℝ)^d)⁻¹
      = (((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2:ℝ)^d - 1)) := by
    have h1r : (1:ℝ) - (1/2)^d ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
    have hhalf : (1/2 : ℝ)^d = ((2:ℝ)^d)⁻¹ := by rw [one_div, inv_pow]
    rw [hhalf]
    field_simp
  rw [← hval]
  exact Filter.Tendsto.congr (fun s => Finset.sum_congr rfl (fun k _ => (hterm k).symm)) scaled

/-- Each divisor term is summable. -/
private theorem gandhi_summable_geom (d : ℕ) (hd : 1 ≤ d) :
    Summable (fun k : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (1/2 : ℝ)^(d*(k+1))) :=
  (gandhi_hasSum_geom d hd).summable

/-- Swap: the divisor sum equals the iterated tsum. -/
private theorem gandhi_swap (P : ℕ) :
    ∑ d ∈ P.divisors, (((ArithmeticFunction.moebius d : ℤ):ℝ) / ((2:ℝ)^d - 1))
    = ∑' k : ℕ, ∑ d ∈ P.divisors,
        (((ArithmeticFunction.moebius d : ℤ):ℝ) * (1/2:ℝ)^(d*(k+1))) := by
  calc ∑ d ∈ P.divisors, (((ArithmeticFunction.moebius d : ℤ):ℝ) / ((2:ℝ)^d - 1))
      = ∑ d ∈ P.divisors, ∑' k : ℕ,
          (((ArithmeticFunction.moebius d : ℤ):ℝ) * (1/2:ℝ)^(d*(k+1))) := by
        apply Finset.sum_congr rfl
        intro d hd
        exact (gandhi_hasSum_geom d (Nat.pos_of_mem_divisors hd)).unique
          (gandhi_summable_geom d (Nat.pos_of_mem_divisors hd)).hasSum
    _ = ∑' k : ℕ, ∑ d ∈ P.divisors,
          (((ArithmeticFunction.moebius d : ℤ):ℝ) * (1/2:ℝ)^(d*(k+1))) :=
        (Summable.tsum_finsetSum
          (fun d hd => gandhi_summable_geom d (Nat.pos_of_mem_divisors hd))).symm

/-- The summand is summable over the product `divisors × ℕ`. -/
private theorem gandhi_prod_summable (P : ℕ) :
    Summable (fun p : ↥P.divisors × ℕ =>
      ((ArithmeticFunction.moebius p.1.1 : ℤ):ℝ) * (1/2:ℝ)^(p.1.1*(p.2+1))) := by
  have hsig : Summable (fun q : Σ _ : ↥P.divisors, ℕ =>
      ((ArithmeticFunction.moebius q.1.1 : ℤ):ℝ) * (1/2:ℝ)^(q.1.1*(q.2+1))) := by
    apply Summable.of_norm
    refine (summable_sigma_of_nonneg (fun x => norm_nonneg _)).mpr ⟨?_, ?_⟩
    · rintro ⟨d, hd⟩
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
      have hr0 : (0:ℝ) ≤ (1/2)^d := by positivity
      have hr1 : (1/2:ℝ)^d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
      have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left ((1/2:ℝ)^d)
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hgeom
      intro k
      show ‖(((ArithmeticFunction.moebius d : ℤ)):ℝ)
        * (1/2:ℝ)^(d*(k+1))‖ ≤ (1/2:ℝ)^d * (((1/2:ℝ)^d)^k)
      rw [norm_mul]
      have hmu : ‖(((ArithmeticFunction.moebius d : ℤ)):ℝ)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, ← Int.cast_abs, ← Int.cast_one]
        exact Int.cast_le.mpr ArithmeticFunction.abs_moebius_le_one
      calc ‖(((ArithmeticFunction.moebius d : ℤ)):ℝ)‖ * ‖(1/2:ℝ)^(d*(k+1))‖
          ≤ 1 * ((1/2:ℝ)^d * (((1/2:ℝ)^d)^k)) := by
            apply mul_le_mul _ _ (norm_nonneg _) (by positivity)
            · exact hmu
            · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
              rw [show d*(k+1) = d + d*k by ring, pow_add, pow_mul]
          _ = (1/2:ℝ)^d * (((1/2:ℝ)^d)^k) := one_mul _
    · exact (hasSum_fintype _).summable
  exact (Equiv.sigmaEquivProd ↥P.divisors ℕ).summable_iff.mp hsig

/-- Fiber finset over `m`: pairs `(d, m/d - 1)` for `d ∣ P`, `d ∣ m` (empty if `m = 0`). -/
private def gandhiFiber (P m : ℕ) : Finset (↥P.divisors × ℕ) :=
  if m = 0 then ∅
  else ((P.divisors.filter (· ∣ m)).attach.image
    (fun d => ((⟨d.1, (Finset.mem_filter.mp d.2).1⟩, m / d.1 - 1) : ↥P.divisors × ℕ)))

/-- Membership in the fiber finset. -/
private theorem gandhiFiber_mem (P m : ℕ) (p : ↥P.divisors × ℕ) :
    p ∈ gandhiFiber P m ↔ m ≠ 0 ∧ p.1.1 ∣ m ∧ p.2 = m / p.1.1 - 1 := by
  unfold gandhiFiber
  split_ifs with hm
  · subst hm
    simp
  · rw [Finset.mem_image]
    constructor
    · rintro ⟨d, _, hdp⟩
      have h1 : ((⟨d.1, (Finset.mem_filter.mp d.2).1⟩ : ↥P.divisors)) = p.1 :=
        congrArg Prod.fst hdp
      have h2 : m / d.1 - 1 = p.2 := congrArg Prod.snd hdp
      have hd_eq : d.1 = p.1.1 := congrArg Subtype.val h1
      obtain ⟨-, hdivm⟩ := Finset.mem_filter.mp d.2
      refine ⟨hm, hd_eq ▸ hdivm, ?_⟩
      rw [hd_eq] at h2
      exact h2.symm
    · rintro ⟨-, hdiv, hk⟩
      refine ⟨⟨p.1.1, Finset.mem_filter.mpr ⟨p.1.2, hdiv⟩⟩,
        Finset.mem_attach _ _, Prod.ext (Subtype.ext rfl) hk.symm⟩

/-- Every pair lies in the fiber over its product. -/
private theorem gandhiFiber_self_mem (P : ℕ) (p : ↥P.divisors × ℕ) :
    p ∈ gandhiFiber P (p.1.1 * (p.2 + 1)) := by
  rw [gandhiFiber_mem]
  have hpos : 0 < p.1.1 := Nat.pos_of_mem_divisors p.1.2
  refine ⟨mul_ne_zero (ne_of_gt hpos) (by omega), dvd_mul_right _ _, ?_⟩
  rw [mul_comm p.1.1 (p.2 + 1), Nat.mul_div_cancel (p.2 + 1) hpos, Nat.add_sub_cancel]

/-- Points in a nonzero fiber project back to the fiber index. -/
private theorem gandhiFiber_proj (P : ℕ) (m : ℕ) (hm : m ≠ 0) (p : ↥P.divisors × ℕ)
    (hpm : p ∈ gandhiFiber P m) : p.1.1 * (p.2 + 1) = m := by
  rw [gandhiFiber_mem] at hpm
  obtain ⟨-, hdiv, hk⟩ := hpm
  have hpos : 0 < p.1.1 := Nat.pos_of_mem_divisors p.1.2
  have hle : 1 ≤ m / p.1.1 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdiv) hpos
  have hkk : p.2 + 1 = m / p.1.1 := by omega
  rw [hkk]
  exact Nat.mul_div_cancel' hdiv

/-- The filter `{d ∈ divisors P : d ∣ m}` is the divisors of `gcd m P`. -/
private theorem gandhi_filter_gcd (P : ℕ) (hP : P ≠ 0) (m : ℕ) :
    P.divisors.filter (· ∣ m) = (Nat.gcd m P).divisors := by
  have hgcd0 : Nat.gcd m P ≠ 0 := fun h => hP ((Nat.gcd_eq_zero_iff.mp h).2)
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdP, -⟩, hdm⟩
    exact ⟨Nat.dvd_gcd hdm hdP, hgcd0⟩
  · rintro ⟨hdG, -⟩
    exact ⟨⟨hdG.trans (Nat.gcd_dvd_right m P), hP⟩, hdG.trans (Nat.gcd_dvd_left m P)⟩

/-- The sum over one fiber equals the coprimality indicator times `(1/2)^m`. -/
private theorem gandhiFiber_sum (P : ℕ) (hP : 1 < P) (m : ℕ) :
    ∑ x ∈ gandhiFiber P m, (((ArithmeticFunction.moebius x.1.1 : ℤ):ℝ) * (1/2:ℝ)^(x.1.1*(x.2+1)))
    = (if Nat.gcd m P = 1 then (1/2:ℝ)^m else 0) := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hS : gandhiFiber P 0 = ∅ := by simp [gandhiFiber]
    have hP1 : P ≠ 1 := by omega
    simp [hS, Nat.gcd_zero_left, hP1]
  · have hS : gandhiFiber P m
        = ((P.divisors.filter (· ∣ m)).attach.image
          (fun d => ((⟨d.1, (Finset.mem_filter.mp d.2).1⟩, m / d.1 - 1) : ↥P.divisors × ℕ))) := by
      unfold gandhiFiber
      simp [hm]
    have hinj : Function.Injective
        (fun d : ↥(P.divisors.filter (· ∣ m)) =>
          ((⟨d.1, (Finset.mem_filter.mp d.2).1⟩, m / d.1 - 1) : ↥P.divisors × ℕ)) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      obtain ⟨h1, -⟩ := hab
      simp only [Subtype.mk.injEq] at h1
      exact Subtype.ext h1
    have hterm : ∀ x ∈ (P.divisors.filter (· ∣ m)).attach,
        (((ArithmeticFunction.moebius (↑x : ℕ) : ℤ):ℝ) * (1/2:ℝ)^(x.1 * (m / x.1 - 1 + 1)))
        = (((ArithmeticFunction.moebius (↑x : ℕ) : ℤ):ℝ) * (1/2:ℝ)^m) := by
      intro x _
      obtain ⟨hdP, hdiv⟩ := Finset.mem_filter.mp x.2
      have hdpos : 0 < x.1 := Nat.pos_of_mem_divisors hdP
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      have hle : 1 ≤ m / x.1 := Nat.div_pos (Nat.le_of_dvd hmpos hdiv) hdpos
      have hexp : x.1 * (m / x.1 - 1 + 1) = m := by
        rw [Nat.sub_add_cancel hle, Nat.mul_div_cancel' hdiv]
      rw [hexp]
    calc ∑ x ∈ gandhiFiber P m,
            (((ArithmeticFunction.moebius x.1.1 : ℤ):ℝ) * (1/2:ℝ)^(x.1.1*(x.2+1)))
        = ∑ x ∈ (P.divisors.filter (· ∣ m)).attach,
            (((ArithmeticFunction.moebius (↑x : ℕ) : ℤ):ℝ) * (1/2:ℝ)^m) := by
          rw [hS, Finset.sum_image (fun a _ b _ hab => hinj hab)]
          refine (Finset.sum_congr rfl (fun x _ => rfl)).trans (Finset.sum_congr rfl hterm)
      _ = (∑ x ∈ (P.divisors.filter (· ∣ m)).attach,
            (((ArithmeticFunction.moebius (↑x : ℕ) : ℤ)):ℝ)) * (1/2:ℝ)^m := by
          rw [Finset.sum_mul]
      _ = (if Nat.gcd m P = 1 then (1/2:ℝ)^m else 0) := by
          have hI := gandhi_moebius_sum_divisors (Nat.gcd m P)
          have hcast := congrArg (fun z : ℤ => (z : ℝ)) hI
          rw [Int.cast_sum] at hcast
          rw [← gandhi_filter_gcd P (by omega) m] at hcast
          have hatt : (∑ x ∈ (P.divisors.filter (· ∣ m)).attach,
              (((ArithmeticFunction.moebius (↑x : ℕ) : ℤ)):ℝ))
              = ∑ d ∈ P.divisors.filter (· ∣ m), (((ArithmeticFunction.moebius d : ℤ)):ℝ) :=
            Finset.sum_attach _ (fun d : ℕ => (((ArithmeticFunction.moebius d : ℤ)):ℝ))
          rw [hatt, hcast]
          split_ifs <;> simp

/-- The equivalence between the sigma of fibers and the product. -/
private def gandhiEquiv (P : ℕ) : (Σ m : ℕ, ↥(gandhiFiber P m)) ≃ (↥P.divisors × ℕ) where
  toFun q := q.2.1
  invFun p := ⟨p.1.1 * (p.2 + 1), ⟨p, gandhiFiber_self_mem P p⟩⟩
  left_inv := by
    rintro ⟨m, p, hpm⟩
    rcases eq_or_ne m 0 with rfl | hm
    · have hS : gandhiFiber P 0 = ∅ := by simp [gandhiFiber]
      rw [hS] at hpm
      exact (Finset.notMem_empty p hpm).elim
    · have hFm : p.1.1 * (p.2 + 1) = m := gandhiFiber_proj P m hm p hpm
      subst hFm
      rfl
  right_inv := fun p => rfl

/-- The divisor sum equals the tsum of the coprimality indicator. -/
private theorem gandhi_divisor_sum_eq (P : ℕ) (hP : 1 < P) :
    ∑ d ∈ P.divisors, (((ArithmeticFunction.moebius d : ℤ):ℝ) / ((2:ℝ)^d - 1))
    = ∑' m : ℕ, (if Nat.gcd m P = 1 then (1/2:ℝ)^m else 0) := by
  have hprod := gandhi_prod_summable P
  have step1 : (∑' p : ↥P.divisors × ℕ,
      (((ArithmeticFunction.moebius p.1.1 : ℤ):ℝ) * (1/2:ℝ)^(p.1.1*(p.2+1))))
      = ∑ d ∈ P.divisors, (((ArithmeticFunction.moebius d : ℤ):ℝ) / ((2:ℝ)^d - 1)) := by
    rw [hprod.tsum_prod, tsum_fintype, Finset.univ_eq_attach P.divisors,
      Finset.sum_attach _ (fun d : ℕ => (∑' k : ℕ,
        (((ArithmeticFunction.moebius d : ℤ):ℝ) * (1/2:ℝ)^(d*(k+1)))))]
    apply Finset.sum_congr rfl
    intro d hd
    exact (gandhi_summable_geom d (Nat.pos_of_mem_divisors hd)).hasSum.unique
      (gandhi_hasSum_geom d (Nat.pos_of_mem_divisors hd))
  have hsig := (gandhiEquiv P).summable_iff.mpr hprod
  have hsplit := hsig.tsum_sigma
  have hLHS : (∑' q : Σ m : ℕ, ↥(gandhiFiber P m),
        (((ArithmeticFunction.moebius ((gandhiEquiv P q).1.1) : ℤ):ℝ)
          * (1/2:ℝ)^((gandhiEquiv P q).1.1 * ((gandhiEquiv P q).2 + 1))))
      = (∑' p : ↥P.divisors × ℕ,
        (((ArithmeticFunction.moebius p.1.1 : ℤ):ℝ) * (1/2:ℝ)^(p.1.1*(p.2+1)))) :=
    Equiv.tsum_eq (gandhiEquiv P)
      (fun p : ↥P.divisors × ℕ =>
        (((ArithmeticFunction.moebius p.1.1 : ℤ):ℝ) * (1/2:ℝ)^(p.1.1*(p.2+1))))
  calc ∑ d ∈ P.divisors, (((ArithmeticFunction.moebius d : ℤ):ℝ) / ((2:ℝ)^d - 1))
      = ∑' p : ↥P.divisors × ℕ,
        (((ArithmeticFunction.moebius p.1.1 : ℤ):ℝ) * (1/2:ℝ)^(p.1.1*(p.2+1))) :=
        step1.symm
    _ = ∑' q : Σ m : ℕ, ↥(gandhiFiber P m),
        (((ArithmeticFunction.moebius ((gandhiEquiv P q).1.1) : ℤ):ℝ)
          * (1/2:ℝ)^((gandhiEquiv P q).1.1 * ((gandhiEquiv P q).2 + 1))) := hLHS.symm
    _ = ∑' m : ℕ, ∑' x : ↥(gandhiFiber P m),
        (((ArithmeticFunction.moebius ((gandhiEquiv P ⟨m, x⟩).1.1) : ℤ):ℝ)
          * (1/2:ℝ)^((gandhiEquiv P ⟨m, x⟩).1.1 * ((gandhiEquiv P ⟨m, x⟩).2 + 1))) :=
        hsplit
    _ = ∑' m : ℕ, ∑ x ∈ gandhiFiber P m,
        (((ArithmeticFunction.moebius x.1.1 : ℤ):ℝ) * (1/2:ℝ)^(x.1.1*(x.2+1))) := by
        apply tsum_congr
        intro m
        exact Finset.tsum_subtype' (gandhiFiber P m)
          (fun y : ↥P.divisors × ℕ =>
            (((ArithmeticFunction.moebius y.1.1 : ℤ):ℝ) * (1/2:ℝ)^(y.1.1*(y.2+1))))
    _ = ∑' m : ℕ, (if Nat.gcd m P = 1 then (1/2:ℝ)^m else 0) := by
        apply tsum_congr
        intro m
        exact gandhiFiber_sum P hP m

/-- `logb 2 (1 / 2) = -1`, the numeric value at the heart of the `n = 1` case. -/
private theorem gandhi_logb_half : Real.logb 2 (1 / 2 : ℝ) = -1 := by
  have h2 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [h2, Real.logb_inv]
  have hself : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  rw [hself]

/-- Every value of `Nat.nth Nat.Prime` is at least `2`. -/
private theorem gandhi_prime_ge_two (n : ℕ) :
    2 ≤ Nat.nth Nat.Prime n :=
  (Nat.prime_nth_prime n).two_le

/-- The primorial `Pₙ₋₁` is positive. -/
private theorem gandhi_primorial_pos (n : ℕ) :
    0 < ∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1) := by
  apply Finset.prod_pos
  intro i _
  exact (Nat.prime_nth_prime (i - 1)).pos

/-- `2` divides the primorial for `n ≥ 2`. -/
private theorem gandhi_two_dvd_primorial (n : ℕ) (hn : 2 ≤ n) :
    2 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1) := by
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) :=
    Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩
  have hdvd := Finset.dvd_prod_of_mem (fun i => Nat.nth Nat.Prime (i - 1)) hmem
  have h10 : (1 : ℕ) - 1 = 0 := by omega
  rwa [h10, Nat.nth_prime_zero_eq_two] at hdvd

/-- The `n = 1` instance of Gandhi's formula: the empty primorial is `1`,
so the divisor sum is `μ(1) / (2^1 - 1) = 1`, giving `⌊1 - log₂(1/2)⌋ = 2 = p₁`. -/
private theorem gandhi_n_one :
    ((Nat.nth Nat.Prime (1 - 1) : ℕ) : ℤ) =
      ⌊1 - Real.logb 2 (-1 / 2 +
        ∑ d ∈ Nat.divisors
          (∏ i ∈ Finset.Icc 1 (1 - 1), Nat.nth Nat.Prime (i - 1)),
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1)))⌋ := by
  have h1 : Nat.nth Nat.Prime (1 - 1) = 2 := Nat.nth_prime_zero_eq_two
  have hP : (∏ i ∈ Finset.Icc 1 (1 - 1), Nat.nth Nat.Prime (i - 1)) = 1 := by
    norm_num
  rw [h1, hP, Nat.divisors_one]
  simp only [Finset.sum_singleton, ArithmeticFunction.moebius_apply_one]
  norm_num [gandhi_logb_half]

/-- Every `1 < m < pₙ` shares a factor with the primorial `Pₙ₋₁`. -/
private theorem gandhi_not_coprime_of_lt (n m : ℕ) (hm1 : 1 < m)
    (hm : m < Nat.nth Nat.Prime (n - 1)) :
    ¬ Nat.Coprime m (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) := by
  intro hcop
  have hgcd : Nat.gcd m (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) = 1 :=
    hcop
  obtain ⟨q, hqprime, hqdiv⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hq2 : 2 ≤ q := hqprime.two_le
  have hqm : q ≤ m := Nat.le_of_dvd (by omega) hqdiv
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hqrange : q ∈ Set.range (Nat.nth Nat.Prime) := by
    rw [Nat.range_nth_of_infinite hinf]
    exact hqprime
  obtain ⟨j, hj⟩ := Set.mem_range.mp hqrange
  have hlt : Nat.nth Nat.Prime j < Nat.nth Nat.Prime (n - 1) := by
    rw [hj]
    exact lt_of_le_of_lt hqm hm
  have hjn : j < n - 1 := (Nat.nth_lt_nth hinf).mp hlt
  have hmem : j + 1 ∈ Finset.Icc 1 (n - 1) :=
    Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 j, by omega⟩
  have hdvdP := Finset.dvd_prod_of_mem (fun i => Nat.nth Nat.Prime (i - 1)) hmem
  rw [Nat.add_sub_cancel, hj] at hdvdP
  have hqgcd : q ∣ Nat.gcd m (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) :=
    Nat.dvd_gcd hqdiv hdvdP
  rw [hgcd] at hqgcd
  have hq1 : q = 1 := Nat.dvd_one.mp hqgcd
  omega

/-- Primes from `pₙ` on are coprime to the primorial `Pₙ₋₁`. -/
private theorem gandhi_coprime_nth_ge (n j : ℕ) (hj : n - 1 ≤ j) :
    Nat.Coprime (Nat.nth Nat.Prime j)
      (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hpp : Nat.Prime (Nat.nth Nat.Prime j) := Nat.prime_nth_prime j
  have hgcd_dvd : Nat.gcd (Nat.nth Nat.Prime j)
      (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1))
      ∣ Nat.nth Nat.Prime j := Nat.gcd_dvd_left _ _
  rcases (Nat.dvd_prime hpp).mp hgcd_dvd with h1 | hp_eq
  · show Nat.gcd (Nat.nth Nat.Prime j)
      (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) = 1
    exact h1
  · have hpP : Nat.nth Nat.Prime j
        ∣ ∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1) :=
      hp_eq ▸ Nat.gcd_dvd_right _ _
    have hprime : Prime (Nat.nth Nat.Prime j) := Nat.prime_iff.mp hpp
    rw [Prime.dvd_finsetProd_iff hprime] at hpP
    obtain ⟨i, hi, hdiv⟩ := hpP
    have hppi : Nat.Prime (Nat.nth Nat.Prime (i - 1)) := Nat.prime_nth_prime _
    have heq : Nat.nth Nat.Prime j = Nat.nth Nat.Prime (i - 1) :=
      (Nat.prime_dvd_prime_iff_eq hpp hppi).mp hdiv
    have hidx : j = i - 1 := Nat.nth_injective hinf heq
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    omega

/-- `pₙ + 1` shares the factor `2` with the primorial. -/
private theorem gandhi_not_coprime_succ (n : ℕ) (hn : 2 ≤ n) :
    ¬ Nat.Coprime (Nat.nth Nat.Prime (n - 1) + 1)
      (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) := by
  intro hcop
  have hgcd : Nat.gcd (Nat.nth Nat.Prime (n - 1) + 1)
      (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) = 1 := hcop
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have h01 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 :=
    (Nat.nth_lt_nth hinf).mpr (by norm_num)
  rw [Nat.nth_prime_zero_eq_two] at h01
  have h1n : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime (n - 1) :=
    (Nat.nth_le_nth hinf).mpr (by omega)
  have hne : Nat.nth Nat.Prime (n - 1) ≠ 2 := by omega
  have hodd := Nat.Prime.odd_of_ne_two (Nat.prime_nth_prime (n - 1)) hne
  have h2p : 2 ∣ Nat.nth Nat.Prime (n - 1) + 1 :=
    even_iff_two_dvd.mp hodd.add_one
  have h2P := gandhi_two_dvd_primorial n hn
  have h2gcd : 2 ∣ Nat.gcd (Nat.nth Nat.Prime (n - 1) + 1)
      (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) :=
    Nat.dvd_gcd h2p h2P
  rw [hgcd] at h2gcd
  exact absurd (Nat.dvd_one.mp h2gcd) (by norm_num)

/-- Splitting the indicator tsum into `1/2 + 2⁻ᵖ + R`. -/
private theorem gandhi_split (P p : ℕ) (hP1 : 1 < P) (hp1 : 1 < p)
    (hpP : Nat.Coprime p P)
    (hchar : ∀ m : ℕ, 1 < m → m < p → ¬ Nat.Coprime m P) :
    (∑' m : ℕ, (if Nat.gcd m P = 1 then (1/2:ℝ)^m else 0))
    = 1/2 + (1/2:ℝ)^p
      + (∑' m : ℕ, (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)) := by
  have hFG : ∀ m : ℕ, (if Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)
      = ((if m = 1 then (1/2:ℝ) else 0) + (if m = p then (1/2:ℝ)^p else 0)
        + (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)) := by
    intro m
    by_cases h1 : m = 1
    · subst h1
      have hg : Nat.gcd 1 P = 1 := Nat.coprime_one_left P
      rw [ite_eq_left hg, ite_eq_left rfl, ite_eq_right (by omega : ¬ (1 : ℕ) = p),
        ite_eq_right (fun h => by omega : ¬ (p < 1 ∧ Nat.gcd 1 P = 1))]
      simp
    · by_cases hpm : m = p
      · have hg : Nat.gcd p P = 1 := hpP
        rw [hpm, ite_eq_left hg, ite_eq_right (by omega : ¬ (p : ℕ) = 1),
          ite_eq_left rfl, ite_eq_right (fun h => lt_irrefl p h.1)]
        simp
      · by_cases hg : Nat.gcd m P = 1
        · have hm0 : m ≠ 0 := by
            intro h0
            subst h0
            rw [Nat.gcd_zero_left] at hg
            omega
          have hcop : Nat.Coprime m P := hg
          have hmp : p < m := by
            by_contra hle
            push Not at hle
            have hm1 : 1 < m := by omega
            have hlt : m < p := by omega
            exact (hchar m hm1 hlt) hcop
          rw [ite_eq_left hg, ite_eq_right h1, ite_eq_right hpm, ite_eq_left ⟨hmp, hg⟩]
          simp
        · rw [ite_eq_right hg, ite_eq_right h1, ite_eq_right hpm,
            ite_eq_right (fun h => hg h.2)]
          simp
  have hA : Summable (fun m : ℕ => (if m = 1 then (1/2:ℝ) else 0)) :=
    (hasSum_ite_eq 1 (1/2 : ℝ)).summable
  have hB : Summable (fun m : ℕ => (if m = p then (1/2:ℝ)^p else 0)) :=
    (hasSum_ite_eq p ((1/2:ℝ)^p)).summable
  have hC : Summable
      (fun m : ℕ => (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
      summable_geometric_two
    · split_ifs with h <;> positivity
    · split_ifs with h
      · exact le_rfl
      · positivity
  have hABC : Summable (fun m : ℕ =>
      ((if m = 1 then (1/2:ℝ) else 0) + (if m = p then (1/2:ℝ)^p else 0)
        + (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0))) :=
    (hA.add hB).add hC
  have hsplit2 : (∑' m : ℕ,
        (((if m = 1 then (1/2:ℝ) else 0) + (if m = p then (1/2:ℝ)^p else 0))
          + (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)))
      = (∑' m : ℕ, (if m = 1 then (1/2:ℝ) else 0))
        + (∑' m : ℕ, (if m = p then (1/2:ℝ)^p else 0))
        + (∑' m : ℕ, (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)) := by
    rw [← hA.tsum_add hB, ← (hA.add hB).tsum_add hC]
  rw [tsum_congr hFG, hsplit2, tsum_ite_eq 1 (fun _ => (1/2:ℝ)),
    tsum_ite_eq p (fun _ => (1/2:ℝ)^p)]

/-- Geometric tail: `∑' m, (if K < m then (1/2)^m else 0) = (1/2)^K`. -/
private theorem gandhi_tail (K : ℕ) :
    (∑' m : ℕ, (if K < m then (1/2:ℝ)^m else 0)) = (1/2:ℝ)^K := by
  have hgeo := summable_geometric_two
  have hfull : (∑' n : ℕ, (1/2:ℝ)^n) = 2 := tsum_geometric_two
  have hfin : Summable (fun m : ℕ => (if m ≤ K then (1/2:ℝ)^m else 0)) := by
    apply summable_of_ne_finset_zero (s := Finset.range (K + 1))
    intro b hb
    simp only [Finset.mem_range] at hb
    rw [ite_eq_right (by omega : ¬ b ≤ K)]
  have hEF : ∀ m : ℕ, (if K < m then (1/2:ℝ)^m else 0)
      = (1/2:ℝ)^m - (if m ≤ K then (1/2:ℝ)^m else 0) := by
    intro m
    by_cases h : K < m
    · rw [ite_eq_left h, ite_eq_right (by omega : ¬ m ≤ K), sub_zero]
    · rw [ite_eq_right h, ite_eq_left (by omega : m ≤ K), sub_self]
  have hif : ∀ b ∈ Finset.range (K + 1),
      (if b ≤ K then (1/2:ℝ)^b else 0) = (1/2:ℝ)^b := by
    intro b hb
    rw [ite_eq_left (by have := Finset.mem_range.mp hb; omega : b ≤ K)]
  have hS : (∑ b ∈ Finset.range (K + 1), (1/2:ℝ)^b) = 2 - (1/2:ℝ)^K := by
    have hgs := geom_sum_eq (show (1/2:ℝ) ≠ 1 by norm_num) (K + 1)
    have h2 : (1/2:ℝ)^(K+1) = (1/2)^K / 2 := by rw [pow_succ]; ring
    have hne : (1/2:ℝ) - 1 ≠ 0 := by norm_num
    rw [hgs, h2, div_eq_iff hne]
    ring
  calc (∑' m : ℕ, (if K < m then (1/2:ℝ)^m else 0))
      = (∑' m : ℕ, ((1/2:ℝ)^m - (if m ≤ K then (1/2:ℝ)^m else 0))) :=
        tsum_congr hEF
    _ = (∑' m : ℕ, (1/2:ℝ)^m)
        - (∑' m : ℕ, (if m ≤ K then (1/2:ℝ)^m else 0)) :=
        hgeo.tsum_sub hfin
    _ = 2 - (∑ b ∈ Finset.range (K + 1), (1/2:ℝ)^b) := by
        rw [hfull, tsum_eq_sum (s := Finset.range (K + 1)) (fun b hb => by
          simp only [Finset.mem_range] at hb
          rw [ite_eq_right (by omega : ¬ b ≤ K)]),
          Finset.sum_congr rfl hif]
    _ = (1/2:ℝ)^K := by rw [hS]; ring

/-- The tail `R` is summable. -/
private theorem gandhi_R_summable (P p : ℕ) :
    Summable (fun m : ℕ => (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)) := by
  apply Summable.of_nonneg_of_le _ _ summable_geometric_two
  · intro m
    split_ifs with h <;> positivity
  · intro m
    split_ifs with h
    · exact le_rfl
    · positivity

/-- Upper bound on the tail: `R < (1/2)^p`. -/
private theorem gandhi_R_lt (P p : ℕ) (hE6 : ¬ Nat.Coprime (p + 1) P) :
    (∑' m : ℕ, (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0))
      < (1/2:ℝ)^p := by
  have hC_le : ∀ m : ℕ, (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)
      ≤ (if p + 1 < m then (1/2:ℝ)^m else 0) := by
    intro m
    by_cases h : p < m ∧ Nat.gcd m P = 1
    · rw [ite_eq_left h]
      obtain ⟨hlt, hcop⟩ := h
      have hm : p + 1 < m := by
        by_contra hle
        push Not at hle
        have hmeq : m = p + 1 := by omega
        subst hmeq
        have hcop2 : Nat.Coprime (p + 1) P := hcop
        exact hE6 hcop2
      rw [ite_eq_left hm]
    · rw [ite_eq_right h]
      by_cases h2 : p + 1 < m
      · rw [ite_eq_left h2]; positivity
      · rw [ite_eq_right h2]
  have hE_sum : Summable (fun m : ℕ => (if p + 1 < m then (1/2:ℝ)^m else 0)) := by
    apply Summable.of_nonneg_of_le _ _ summable_geometric_two
    · intro m
      split_ifs with h <;> positivity
    · intro m
      split_ifs with h
      · exact le_rfl
      · positivity
  calc (∑' m : ℕ, (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0))
      ≤ (∑' m : ℕ, (if p + 1 < m then (1/2:ℝ)^m else 0)) :=
        Summable.tsum_le_tsum (fun m => hC_le m)
          (gandhi_R_summable P p) hE_sum
    _ = (1/2:ℝ)^(p+1) := gandhi_tail (p + 1)
    _ < (1/2:ℝ)^p := by
        have hX : (0:ℝ) < (1/2)^p := by positivity
        rw [pow_succ']
        linarith

/-- Lower bound on the tail: `0 < R` via a witness `q`. -/
private theorem gandhi_R_pos (P p q : ℕ) (hpq : p < q) (hqP : Nat.Coprime q P) :
    0 < (∑' m : ℕ, (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)) := by
  have hq : Nat.gcd q P = 1 := hqP
  have hterm : (if p < q ∧ Nat.gcd q P = 1 then (1/2:ℝ)^q else 0) = (1/2:ℝ)^q :=
    ite_eq_left ⟨hpq, hq⟩
  calc (0:ℝ) < (1/2:ℝ)^q := by positivity
    _ = (if p < q ∧ Nat.gcd q P = 1 then (1/2:ℝ)^q else 0) := hterm.symm
    _ ≤ (∑' m : ℕ, (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)) :=
        Summable.le_tsum (gandhi_R_summable P p) q (fun j _ => by
          by_cases h : p < j ∧ Nat.gcd j P = 1
          · rw [ite_eq_left h]
            positivity
          · rw [ite_eq_right h])

/-- Bridge: `⌊1 - logb 2 S⌋ = p` from real bounds. -/
private theorem gandhi_floor_eq (S : ℝ) (p : ℕ)
    (hSlo : (1/2:ℝ)^p < S) (hShi : S < 2 * (1/2:ℝ)^p) :
    ⌊1 - Real.logb 2 S⌋ = (p : ℤ) := by
  have hA : (0:ℝ) < (1/2)^p := by positivity
  have hSpos : (0:ℝ) < S := lt_trans hA hSlo
  have hlogA : Real.logb 2 ((1/2:ℝ)^p) = -(p:ℝ) := by
    rw [Real.logb_pow, gandhi_logb_half]
    ring
  have h1 : -(p:ℝ) < Real.logb 2 S := by
    rw [← hlogA]
    exact Real.logb_lt_logb (by norm_num) hA hSlo
  have h2 : Real.logb 2 S < 1 - (p:ℝ) := by
    have h2A : Real.logb 2 (2 * (1/2:ℝ)^p) = 1 - (p:ℝ) := by
      rw [Real.logb_mul (by norm_num) (by positivity : ((1/2:ℝ)^p) ≠ 0),
        Real.logb_self_eq_one (by norm_num), hlogA]
      ring
    rw [← h2A]
    exact Real.logb_lt_logb (by norm_num) hSpos hShi
  rw [Int.floor_eq_iff]
  constructor <;> (push_cast; linarith)

/-- Main bound: the floor-log formula from the divisor-sum identity and bounds. -/
private theorem gandhi_main_bound (P p : ℕ) (hP1 : 1 < P) (hp1 : 1 < p)
    (hpP : Nat.Coprime p P)
    (hchar : ∀ m : ℕ, 1 < m → m < p → ¬ Nat.Coprime m P)
    (hE6 : ¬ Nat.Coprime (p + 1) P)
    (hq : ∃ q : ℕ, p < q ∧ Nat.Coprime q P) :
    ⌊1 - Real.logb 2 (-1 / 2 +
      ∑ d ∈ Nat.divisors P, (((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1)))⌋
      = (p : ℤ) := by
  have hTR : (∑ d ∈ Nat.divisors P,
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1)))
      = 1 / 2 + (1 / 2 : ℝ) ^ p
        + (∑' m : ℕ, (if p < m ∧ Nat.gcd m P = 1 then (1/2:ℝ)^m else 0)) := by
    rw [gandhi_divisor_sum_eq P hP1]
    exact gandhi_split P p hP1 hp1 hpP hchar
  obtain ⟨q, hpq, hqP⟩ := hq
  have hRpos := gandhi_R_pos P p q hpq hqP
  have hRlt := gandhi_R_lt P p hE6
  have hSlo : (1/2:ℝ)^p < -1 / 2 +
      (∑ d ∈ Nat.divisors P, (((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1))) := by
    rw [hTR]
    linarith
  have hShi : -1 / 2 +
      (∑ d ∈ Nat.divisors P, (((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1)))
      < 2 * (1/2:ℝ)^p := by
    rw [hTR]
    linarith
  exact gandhi_floor_eq _ _ hSlo hShi

/-- **Gandhi's formula for the $n$th prime.** For $i \ge 1$ let $p_i$ be the $i$th prime, so that
$p_1 = 2$, and for $n \ge 1$ let $P_{n-1} = p_1 p_2 \cdots p_{n-1}$, the empty product $1$ when
$n = 1$. Let $\mu$ be the Möbius function. Then for every $n \ge 1$,
$$p_n = \left\lfloor 1 - \log_2 \left( -\frac{1}{2} + \sum_{d \mid P_{n-1}} \frac{\mu(d)}{2^d - 1}
\right) \right\rfloor.$$

Source: J. M. Gandhi, "Formulae for the nth prime," Proc. Washington State
University Conference on Number Theory (1971), 96--107. The displayed formula
and indexing follow the secondary source Eric S. Rowland, "A Natural
Prime-Generating Recurrence," Journal of Integer Sequences 11 (2008),
Article 08.2.8, lines 90--103 of the official TeX,
https://cs.uwaterloo.ca/journals/JIS/VOL11/Rowland/rowland21.tex,
where `f(n)` is the `n`th prime `pₙ` and `Pₙ = p₁ p₂ ⋯ pₙ`.
Proves `Wanted` entry `gandhi_nthPrimeFormula`.
-/
theorem gandhi_nthPrimeFormula (n : ℕ) (hn : 0 < n) :
    ((Nat.nth Nat.Prime (n - 1) : ℕ) : ℤ) =
      ⌊1 - Real.logb 2 (-1 / 2 +
        ∑ d ∈ Nat.divisors
          (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)),
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1)))⌋ := by
  rcases eq_or_ne n 1 with rfl | hne
  · exact gandhi_n_one
  · have hn2 : 2 ≤ n := by omega
    have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
    have hP1 : 1 < ∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1) :=
      lt_of_lt_of_le (by norm_num)
        (Nat.le_of_dvd (gandhi_primorial_pos n) (gandhi_two_dvd_primorial n hn2))
    have hp1 : 1 < Nat.nth Nat.Prime (n - 1) := by
      have h01 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 :=
        (Nat.nth_lt_nth hinf).mpr (by norm_num)
      rw [Nat.nth_prime_zero_eq_two] at h01
      have h1n : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime (n - 1) :=
        (Nat.nth_le_nth hinf).mpr (by omega)
      omega
    have hpP : Nat.Coprime (Nat.nth Nat.Prime (n - 1))
        (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) :=
      gandhi_coprime_nth_ge n (n - 1) le_rfl
    have hchar : ∀ m : ℕ, 1 < m → m < Nat.nth Nat.Prime (n - 1) →
        ¬ Nat.Coprime m
          (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) :=
      fun m hm1 hmp => gandhi_not_coprime_of_lt n m hm1 hmp
    have hE6 : ¬ Nat.Coprime (Nat.nth Nat.Prime (n - 1) + 1)
        (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) :=
      gandhi_not_coprime_succ n hn2
    have hq : ∃ q : ℕ, Nat.nth Nat.Prime (n - 1) < q ∧ Nat.Coprime q
        (∏ i ∈ Finset.Icc 1 (n - 1), Nat.nth Nat.Prime (i - 1)) :=
      ⟨Nat.nth Nat.Prime n, (Nat.nth_lt_nth hinf).mpr (by omega),
        gandhi_coprime_nth_ge n n (by omega)⟩
    exact (gandhi_main_bound _ _ hP1 hp1 hpP hchar hE6 hq).symm

end

end MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted
