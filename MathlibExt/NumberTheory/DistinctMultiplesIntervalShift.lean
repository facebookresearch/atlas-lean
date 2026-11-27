/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.NumberTheory.DistinctMultiplesInterval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.PrimeNumberTheorem

/-!
# Shifting an interval containing distinct multiples

For all sufficiently large `n`, shifting the interval can increase the least length by more than
`0.36 * n * log n / log (log n)`. This is Theorem 1 of Wouter van Doorn's *On the Length of an
Interval That Contains Distinct Multiples of the First n Positive Integers*.

The proof uses the prime number theorem twice. For the shifted interval, encode each prime near
`n` in base `b` and prescribe its residue by the Chinese remainder theorem. In row `j` of possible
multiples the `j`-th digit cancels, leaving fewer possible values than primes. For the diagonal
interval, use a common multiplier for large indices and Hall's theorem on prime multiples for
small indices.
-/

open Filter Finset Real

namespace MetaMathlibExt
namespace exists_distinctMultiplesIntervalLength_sub_gt

private def primesBetween (a b : ℕ) := b.primesLE \ a.primesLE

private lemma mem_between {p a b : ℕ} :
    p ∈ primesBetween a b ↔ p.Prime ∧ a < p ∧ p ≤ b := by
  rw [primesBetween, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
  grind

-- Encode the residue modulo each prime by weighting each base-b digit by its position.
-- On the j-th multiple, the j-th digit cancels, leaving one fewer free digit per row.
private lemma obstruction {n h b d L : ℕ} (hb : 0 < b)
    (hlen : L + (d + 1) * (n - h) ≤ (d + 1) * h)
    (hcard : (d + 1) * ((n / b ^ (d + 1) + 1) * b ^ d) < (primesBetween h n).card) :
    ∃ m > 0, L < distinctMultiplesIntervalLength n m := by
  classical
  let P := primesBetween h n
  let B := b ^ (d + 1)
  have hB : 0 < B := pow_pos hb _
  -- The top block and the low digits reconstruct p - h.
  let z (p : ℕ) := (p - h) / B
  let digits (p : ℕ) : Fin (d + 1) → Fin b :=
    finFunctionFinEquiv.symm ⟨(p - h) % B, Nat.mod_lt _ hB⟩
  let w (p : ℕ) (i : Fin (d + 1)) := (digits p i : ℕ) * b ^ (i : ℕ)
  have hexpand (p : ℕ) : p - h = B * z p + ∑ i, w p i := by
    have hd : ∑ i, w p i = (p - h) % B := by
      simp only [w, digits, ← finFunctionFinEquiv_apply, Equiv.apply_symm_apply]
    simpa only [hd, Nat.add_comm] using (Nat.mod_add_div (p - h) B).symm
  let S (p : ℕ) := ∑ i : Fin (d + 1), (i : ℕ) * w p i
  have hS (p : ℕ) : S p ≤ (d + 1) * (p - h) := calc
    S p ≤ ∑ i, (d + 1) * w p i :=
      sum_le_sum fun i _ => Nat.mul_le_mul_right _ i.isLt.le
    _ ≤ _ := by rw [← mul_sum]; exact Nat.mul_le_mul_left _ (by have := hexpand p; omega)
  have hp (p) (hp : p ∈ P) := (mem_between.mp hp).1
  let sol := Nat.chineseRemainderOfFinset S id P (fun p hp' => (hp p hp').ne_zero)
    (fun p hp' q hq' hne => (Nat.coprime_primes (hp p hp') (hp q hq')).2 hne)
  let m := sol.val + ∏ p ∈ P, p
  have hm : 0 < m := Nat.add_pos_right _ (prod_pos fun p hp' => (hp p hp').pos)
  have hmod (p) (hp' : p ∈ P) : m ≡ S p [MOD p] := by
    have hd : p ∣ ∏ q ∈ P, q := dvd_prod_of_mem id hp'
    simpa using (sol.property p hp').add (Nat.modEq_zero_iff_dvd.mpr hd)
  -- In row j only the top block and the other d digits affect the value.
  let row (j : Fin (d + 1)) (u : Fin (n / B + 1) × (Fin d → Fin b)) : ℤ :=
    (m : ℤ) + j.val * ((h : ℤ) + B * u.1.val) +
      ∑ i : Fin d, ((j.val : ℤ) - (j.succAbove i).val) * (u.2 i).val * (b : ℤ) ^ (j.succAbove i).val
  let grid := univ.biUnion fun j => univ.image (row j)
  have hg : grid.card ≤ (d + 1) * ((n / B + 1) * b ^ d) := calc
    _ ≤ ∑ j, (univ.image (row j)).card := card_biUnion_le
    _ ≤ ∑ _j : Fin (d + 1), (n / B + 1) * b ^ d :=
      sum_le_sum fun j _ => card_image_le.trans (by simp)
    _ = _ := by simp
  refine ⟨m, hm, lt_of_not_ge fun hl => ?_⟩
  obtain ⟨a, ha, ha'⟩ := distinctMultiplesIntervalLength_le_iff.mp hl
  let idx (p : P) : Fin n := ⟨p.val - 1, by
    have := (hp _ p.property).pos
    have := (mem_between.mp p.property).2.2
    omega⟩
  have inj : Function.Injective idx := by
    intro p q eq
    have := congrArg Fin.val eq
    dsimp [idx] at this
    have := (hp _ p.property).pos
    have := (hp _ q.property).pos
    exact Subtype.ext (by omega)
  -- An assigned multiple determines a row since its displacement plus S p is divisible by p.
  have hin (p : P) : ((a (idx p) : ℕ) : ℤ) ∈ grid := by
    obtain ⟨hlo, hhi, hd⟩ := ha' (idx p)
    have ⟨_, hhp, hpn⟩ := mem_between.mp p.property
    have hidx : (idx p).val + 1 = p.val := by dsimp [idx]; omega
    rw [hidx] at hd
    let A := a (idx p)
    change m < A at hlo
    change A ≤ m + L at hhi
    have hdvd : (p.val : ℤ) ∣ (A : ℤ) + S p - m := by
      convert dvd_add (show (p.val : ℤ) ∣ (A : ℤ) by exact_mod_cast hd)
        (hmod _ p.property).dvd using 1
      ring
    obtain ⟨c, hc⟩ := hdvd
    have hpz : 0 < (p.val : ℤ) := by exact_mod_cast (hp _ p.property).pos
    have hc0 : 0 ≤ c := by
      by_contra! h
      linarith [mul_neg_of_pos_of_neg hpz h, (show (m : ℤ) < A by exact_mod_cast hlo),
        (show (0 : ℤ) ≤ S p by positivity)]
    have hcsmall : c < (d + 1 : ℕ) := by
      by_contra! hu
      have hs := (hS p).trans (Nat.mul_le_mul_left (d + 1) (Nat.sub_le_sub_right hpn h))
      have hn : A + S p ≤ m + (d + 1) * h := by omega
      have hh : (d + 1) * h < (d + 1) * p.val := Nat.mul_lt_mul_of_pos_left hhp (by omega)
      have hnz : (A : ℤ) + S p ≤ m + (d + 1 : ℕ) * h := by exact_mod_cast hn
      have hhz : ((d + 1 : ℕ) : ℤ) * h < (d + 1 : ℕ) * p.val := by exact_mod_cast hh
      linarith [mul_le_mul_of_nonneg_left hu hpz.le]
    let j : Fin (d + 1) := ⟨c.toNat, by omega⟩
    have hj : (j.val : ℤ) = c := Int.toNat_of_nonneg hc0
    let top : Fin (n / B + 1) := ⟨z p, by
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (le_trans (Nat.sub_le _ _) hpn))⟩
    apply mem_biUnion.mpr
    refine ⟨j, mem_univ _, mem_image.mpr ⟨(top, fun i => digits p (j.succAbove i)), mem_univ _, ?_⟩⟩
    have he : p.val = h + B * z p + ∑ i, w p i := by have := hexpand p; omega
    have hez : (p.val : ℤ) = h + (B : ℤ) * z p + ∑ i, (w p i : ℤ) := by exact_mod_cast he
    have hs' : (S p : ℤ) = ∑ i : Fin (d + 1), (i.val : ℤ) * w p i := by simp [S]
    rw [← hj, hez, hs', add_mul, add_mul, sum_mul] at hc
    rw [Fin.sum_univ_succAbove _ j, Fin.sum_univ_succAbove _ j] at hc
    dsimp only [row, top]
    change _ = (A : ℤ)
    have heq : (∑ i : Fin d, ((j.val : ℤ) - (j.succAbove i).val) *
        (digits p (j.succAbove i)).val * (b : ℤ) ^ (j.succAbove i).val) =
        (∑ i : Fin d, (w p (j.succAbove i) : ℤ) * j.val) -
        ∑ i : Fin d, ((j.succAbove i).val : ℤ) * w p (j.succAbove i) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      simp [w]
      ring
    rw [heq]
    linarith only [hc, mul_comm (j.val : ℤ) ((h : ℤ) + B * z p),
      mul_comm (j.val : ℤ) (w p j)]
  have hc := card_le_card_of_injOn (fun p : P => (a (idx p) : ℤ))
    (s := univ) (t := grid) (fun p _ => hin p)
    (fun _ _ _ _ he => inj (ha (Int.ofNat_inj.mp he)))
  simp only [card_univ, Fintype.card_coe] at hc
  exact (hcard.not_ge (hc.trans hg)).elim

-- A fixed positive fraction of the primes up to v lie in (u,v] if u/v is bounded
-- away from one and u is at least v/2.
private lemma enough_primes : ∃ N : ℕ, ∀ {u v : ℕ}, N ≤ u → u ≤ v → v ≤ 2 * u →
    (u : ℝ) ≤ 0.97 * v → 0.01 * v / log v ≤ (primesBetween u v).card := by
  have h := MathlibExt.NumberTheory.PrimeNumberTheoremWanted.prime_number_theorem.isLittleO.bound
    (show (0 : ℝ) < 0.001 by norm_num)
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.and (hl.eventually_ge_atTop 1000))
  refine ⟨N, fun {u v} hu huv hvu hratio => ?_⟩
  obtain ⟨hu', hlogu⟩ := hN u hu
  obtain ⟨hv', hlogv⟩ := hN v (hu.trans huv)
  change ‖(u.primeCounting : ℝ) - u / log u‖ ≤ _ at hu'
  change ‖(v.primeCounting : ℝ) - v / log v‖ ≤ _ at hv'
  change 1000 ≤ log (u : ℝ) at hlogu
  change 1000 ≤ log (v : ℝ) at hlogv
  have hul : 0 < log (u : ℝ) := by linarith
  have hvl : 0 < log (v : ℝ) := by linarith
  have hur : 0 < (u : ℝ) := by
    apply lt_of_le_of_ne u.cast_nonneg
    rintro e
    rw [← e, log_zero] at hul
    linarith
  have hvr : 0 < (v : ℝ) := hur.trans_le (by exact_mod_cast huv)
  have hlogdiff : log (v : ℝ) ≤ log u + 1 := calc
    _ ≤ log (2 * (u : ℝ)) := log_le_log hvr (by exact_mod_cast hvu)
    _ ≤ _ := by
      rw [log_mul (by norm_num) hur.ne']
      linarith [log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))]
  have herr (w : ℕ) (hw : 0 < log (w : ℝ))
      (he : ‖(w.primeCounting : ℝ) - w / log w‖ ≤ 0.001 * ‖(w : ℝ) / log w‖) :
      0.999 * w ≤ (w.primeCounting : ℝ) * log w ∧
      (w.primeCounting : ℝ) * log w ≤ 1.001 * w := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg w.cast_nonneg hw.le),
      abs_le] at he
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right he.1 hw.le,
      mul_le_mul_of_nonneg_right he.2 hw.le, div_mul_cancel₀ (w : ℝ) hw.ne']
  have hU := (herr u hul hu').2
  have hV := (herr v hvl hv').1
  rw [primesBetween, card_sdiff_of_subset (Nat.primesLE_mono huv),
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting,
    Nat.cast_sub (Nat.monotone_primeCounting huv), div_le_iff₀ hvl]
  have hp : 0 ≤ (u.primeCounting : ℝ) := by positivity
  have hd : log (v : ℝ) ≤ 1.002 * log u := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hd hp]

-- Use K*i for large indices. Each small index has many prime multiples in (Kn,2Kn].
-- A value in this interval has at most C distinct prime factors, so Hall applies.
private lemma diagonal {n K C : ℕ} (hK : 0 < K) (hC : 0 < C)
    (hrow : ∀ u, K ^ 2 ≤ u → C ≤ (primesBetween u (2 * u)).card)
    (hcol : ∀ y, 0 < y → y ≤ 2 * (K * n) → y.primeFactors.card ≤ C) :
    distinctMultiplesIntervalLength n n ≤ 2 * (K * n) := by
  classical
  let I := {i : Fin n // (i.val + 1) * K ≤ n}
  let v (i : I) := i.val.val + 1
  have hv (i : I) : 0 < v i := Nat.succ_pos _
  let u (i : I) := K * n / v i
  have hu (i : I) : K ^ 2 ≤ u i := (Nat.le_div_iff_mul_le (hv i)).2 (by
    have := Nat.mul_le_mul_left K i.property
    dsimp [v]
    nlinarith)
  let R (i : I) := (primesBetween (u i) (2 * u i)).image (fun p => p * v i)
  have hmem {i : I} {y : ℕ} (hy : y ∈ R i) :
      K * n < y ∧ y ≤ 2 * (K * n) ∧ y / v i ∈ y.primeFactors ∧ y / v i * v i = y := by
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
    obtain ⟨hpp, hl, hh⟩ := mem_between.mp hp
    have hle := Nat.mul_le_mul_right (v i) hh
    have hfl := Nat.div_mul_le_self (K * n) (v i)
    rw [Nat.mul_div_cancel _ (hv i)]
    exact ⟨(Nat.div_lt_iff_lt_mul (hv i)).mp hl,
      by dsimp [u] at hle; nlinarith,
      Nat.mem_primeFactors.mpr ⟨hpp, dvd_mul_right _ _, (Nat.mul_pos hpp.pos (hv i)).ne'⟩, rfl⟩
  obtain ⟨f, hf, hfR⟩ := (all_card_le_biUnion_card_iff_existsInjective' R).1 (by
    intro s
    apply (Nat.mul_le_mul_right_iff hC).mp
    apply card_mul_le_card_mul (fun i y => y ∈ R i)
    · intro i hi
      apply (hrow _ (hu i)).trans
      calc
        _ = (R i).card := (card_image_of_injective _ (mul_left_injective₀ (hv i).ne')).symm
        _ ≤ _ := card_le_card fun y hy => mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, hi, hy⟩, hy⟩
    · intro y hy
      obtain ⟨i, -, hi⟩ := mem_biUnion.mp hy
      apply le_trans _ (hcol y ((Nat.zero_le _).trans_lt (hmem hi).1) (hmem hi).2.1)
      apply card_le_card_of_injOn (fun a : I => y / v a)
      · intro a ha
        exact (hmem (mem_filter.mp ha).2).2.2.1
      · intro a ha b hb he
        have h₁ := hmem (mem_filter.mp ha).2
        have h₂ := hmem (mem_filter.mp hb).2
        change y / v a = y / v b at he
        have heq := h₁.2.2.2.trans h₂.2.2.2.symm
        rw [he] at heq
        have hd := (Nat.prime_of_mem_primeFactors h₂.2.2.1).pos
        exact Subtype.ext (Fin.ext (Nat.succ.inj (Nat.eq_of_mul_eq_mul_left hd heq))))
  have hlarge (i : Fin n) : (i.val + 1) * K ≤ K * n := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ i.isLt
  apply distinctMultiplesIntervalLength_le_iff.mpr
  refine ⟨fun i => if h : (i.val + 1) * K ≤ n then f ⟨i, h⟩ else (i.val + 1) * K, ?_, ?_⟩
  · intro i j he
    dsimp only at he
    split at he <;> split at he
    · exact congrArg Subtype.val (hf he)
    · exact False.elim ((hmem (hfR _)).1.not_ge (he.le.trans (hlarge j)))
    · exact False.elim ((hmem (hfR _)).1.not_ge (he.ge.trans (hlarge i)))
    · exact Fin.ext (Nat.succ.inj (Nat.eq_of_mul_eq_mul_right hK he))
  · intro i
    dsimp only
    split
    · rename_i hi
      have hm := hmem (hfR ⟨i, hi⟩)
      exact ⟨(Nat.le_mul_of_pos_left n hK).trans_lt hm.1, by omega,
        ⟨_, by rw [mul_comm]; exact hm.2.2.2.symm⟩⟩
    · exact ⟨by omega, by have := hlarge i; omega, dvd_mul_right _ _⟩

private lemma prime_factor_count {y : ℕ} (hy : 0 < y) :
    (y.primeFactors.card : ℝ) * log 2 ≤ log y := by
  have hpow : 2 ^ y.primeFactors.card ≤ y := calc
    _ = ∏ _ ∈ y.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ y.primeFactors, p :=
      prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ y := Nat.le_of_dvd hy (Nat.prod_primeFactors_dvd y)
  have hr := log_le_log (by positivity : 0 < (2 : ℝ) ^ y.primeFactors.card)
    (show (2 : ℝ) ^ y.primeFactors.card ≤ y by exact_mod_cast hpow)
  rwa [log_pow] at hr

-- For K of order log n / (1000 log log n), even the smallest dyadic interval
-- of prime multipliers contributes more primes than an output can have prime factors.
private lemma diagonal_estimate {n K N : ℕ} {x y : ℝ}
    (hx : x = log n) (hy : y = log x) (hn : 2 ≤ n) (hybig : 1000 ≤ y)
    (hNK : N ≤ K ^ 2) (hKx : (K : ℝ) ≤ x) (hKbig : 2000000 * y ^ 2 ≤ K)
    (hKlo : 0.001 * x ≤ K * y)
    (hpr : ∀ {u v : ℕ}, N ≤ u → u ≤ v → v ≤ 2 * u →
      (u : ℝ) ≤ 0.97 * v → 0.01 * v / log v ≤ (primesBetween u v).card) :
    distinctMultiplesIntervalLength n n ≤ 2 * (K * n) := by
  have hypos : 0 < y := by linarith
  have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hKr : 3 ≤ (K : ℝ) := by linarith
  have hK : 0 < K := by exact_mod_cast (show 0 < (K : ℝ) by linarith)
  have hxpos : 1 ≤ x := by linarith
  let C := ⌈6 * x⌉₊
  have hC : 0 < C := Nat.one_le_ceil_iff.2 (by linarith)
  have hChi : (C : ℝ) ≤ 7 * x := by
    dsimp only [C]; linarith [Nat.ceil_lt_add_one (show 0 ≤ 6 * x by linarith)]
  apply diagonal hK hC
  · intro u hu
    have hden := hpr (hNK.trans hu) (Nat.le_mul_of_pos_left u (by decide : 0 < 2))
      (le_refl (2 * u)) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) u])
    suffices (C : ℝ) ≤ 0.01 * (2 * u) / log (2 * u) by
      push_cast at hden
      exact_mod_cast this.trans hden
    have h₁ : exp 1 ≤ (K : ℝ) ^ 2 := by nlinarith [exp_one_lt_three, sq_nonneg ((K : ℝ) - 2)]
    have h₂ : (K : ℝ) ^ 2 ≤ 2 * u := by
      have hr : (K : ℝ) ^ 2 ≤ u := by exact_mod_cast hu
      linarith [Nat.cast_nonneg (α := ℝ) u]
    have hlogK : 0 < log ((K : ℝ) ^ 2) := log_pos (by nlinarith [sq_nonneg ((K : ℝ) - 2)])
    have hlogu : 0 < log (2 * (u : ℝ)) := log_pos (by linarith [exp_one_gt_two])
    have hlogKhi : log ((K : ℝ) ^ 2) ≤ 2 * y := by
      rw [log_pow, hy]
      have := log_le_log (by positivity : (0 : ℝ) < K) hKx
      norm_num
      linarith
    have hkey : (C : ℝ) * log ((K : ℝ) ^ 2) ≤ 0.01 * (K : ℝ) ^ 2 := by
      have h₃ := mul_le_mul hChi hlogKhi hlogK.le (by linarith : 0 ≤ 7 * x)
      nlinarith [mul_le_mul_of_nonneg_right hKlo hypos.le,
        mul_le_mul_of_nonneg_right hKbig (show 0 ≤ (K : ℝ) by positivity)]
    have hanti := log_div_self_antitoneOn h₁ (h₁.trans h₂) h₂
    change log (2 * (u : ℝ)) / (2 * u) ≤ log ((K : ℝ) ^ 2) / (K : ℝ) ^ 2 at hanti
    have hrat := inv_anti₀ (div_pos hlogu ((exp_pos 1).trans_le (h₁.trans h₂))) hanti
    simp only [inv_div] at hrat
    calc
      _ ≤ 0.01 * ((K : ℝ) ^ 2 / log ((K : ℝ) ^ 2)) := by
        rw [← mul_div_assoc, le_div_iff₀ hlogK]; exact hkey
      _ ≤ _ := by rw [mul_div_assoc]; gcongr
  · intro a ha htop
    have hnr : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    have hKn : (K : ℝ) ≤ n :=
      hKx.trans (hx ▸ (log_le_sub_one_of_pos (by positivity)).trans (by linarith))
    have htop' : (a : ℝ) ≤ 2 * ((K : ℝ) * n) := by exact_mod_cast htop
    have hA : (a : ℝ) ≤ (n : ℝ) ^ 3 := htop'.trans (by
      nlinarith [mul_le_mul_of_nonneg_right hKn n.cast_nonneg,
        mul_nonneg (show (0 : ℝ) ≤ n - 2 by linarith) (sq_nonneg (n : ℝ))])
    have hlogA := log_le_log (by exact_mod_cast ha : 0 < (a : ℝ)) hA
    rw [log_pow, ← hx] at hlogA
    have hc := prime_factor_count ha
    norm_num at hlogA
    have hhalf : (1 / 2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
    have hfac : (a.primeFactors.card : ℝ) ≤ 6 * x := by
      linarith [mul_le_mul_of_nonneg_left hhalf a.primeFactors.card.cast_nonneg]
    exact_mod_cast hfac.trans (Nat.le_ceil _)

-- Use d+1 rows and base roughly (log n)^2. The grid then has at most
-- 2*(d+1)*n/b cells, fewer than the primes between n-n/25 and n.
private lemma shift_estimate {n N d : ℕ} {x y : ℝ} (hx : x = log n) (hy : y = log x)
    (hn : 100 + 2 * N ≤ n) (hxpos : 2 ≤ x) (hybig : 1000 ≤ y)
    (ht : ((d + 1 : ℕ) : ℝ) * y ≤ 0.45 * x)
    (hpr : ∀ {u v : ℕ}, N ≤ u → u ≤ v → v ≤ 2 * u →
      (u : ℝ) ≤ 0.97 * v → 0.01 * v / log v ≤ (primesBetween u v).card) :
    ∃ m > 0, (d + 1) * (n - 2 * (n / 25)) < distinctMultiplesIntervalLength n m := by
  let t := d + 1
  let h := n - n / 25
  let b := ⌈x⌉₊ ^ 2
  have hceil := Nat.le_ceil x
  have hbr : (b : ℝ) = (⌈x⌉₊ : ℝ) ^ 2 := by simp [b]
  have hb : 0 < b := by
    dsimp only [b]
    exact pow_pos (Nat.one_le_ceil_iff.2 (by linarith)) _
  have hbx : x ^ 2 ≤ (b : ℝ) := by rw [hbr]; gcongr
  have hbu : (⌈x⌉₊ : ℝ) ≤ 2 * x := by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ x)]
  have hlogb : log (b : ℝ) ≤ 2.1 * y := calc
    _ = 2 * log (⌈x⌉₊ : ℝ) := by rw [hbr, log_pow]; norm_num
    _ ≤ 2 * log (2 * x) := by gcongr
    _ ≤ _ := by
      rw [log_mul (by norm_num) (by linarith), ← hy]
      linarith [log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))]
  have hpow : b ^ t ≤ n := by
    have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
    suffices (b : ℝ) ^ t ≤ n by exact_mod_cast this
    apply (log_le_log_iff (pow_pos hb' _) hnr).mp
    rw [log_pow, ← hx]
    change (t : ℝ) * y ≤ 0.45 * x at ht
    nlinarith [mul_le_mul_of_nonneg_left hlogb (Nat.cast_nonneg (α := ℝ) t)]
  have hdens := hpr (u := h) (v := n) (by dsimp [h]; omega) (by dsimp [h]; omega)
    (by dsimp [h]; omega) (by
      have he : 100 * h ≤ 97 * n := by dsimp [h]; omega
      have hr : 100 * (h : ℝ) ≤ 97 * n := by exact_mod_cast he
      linarith)
  apply obstruction (h := h) (b := b) hb
  · have he : (n - 2 * (n / 25)) + (n - h) = h := by dsimp [h]; omega
    rw [← Nat.mul_add, he]
  · let g := t * ((n / b ^ t + 1) * b ^ d)
    have heg : g * b ≤ 2 * t * n := calc
      _ = t * ((n / b ^ t + 1) * b ^ t) := by dsimp only [g]; dsimp only [t]; rw [pow_succ]; ring
      _ ≤ t * (2 * n) := by
        apply Nat.mul_le_mul_left
        rw [Nat.add_mul, one_mul]
        have := Nat.div_mul_le_self n (b ^ t)
        omega
      _ = _ := by ring
    have htr : (t : ℝ) ≤ 0.001 * x := by
      change (t : ℝ) * y ≤ 0.45 * x at ht
      nlinarith [mul_le_mul_of_nonneg_left hybig (Nat.cast_nonneg (α := ℝ) t)]
    have hratio : 2 * (t : ℝ) * x < 0.01 * b := by
      nlinarith [mul_le_mul_of_nonneg_right htr (show 0 ≤ x by linarith),
        sq_pos_of_pos (by linarith : 0 < x)]
    have hgr : (g : ℝ) * b ≤ 2 * t * n := by exact_mod_cast heg
    suffices (g : ℝ) < 0.01 * n / x by rw [hx] at this; exact_mod_cast this.trans_le hdens
    apply (lt_div_iff₀ (by linarith)).2
    apply lt_of_mul_lt_mul_right (a := (b : ℝ))
    · nlinarith only [mul_le_mul_of_nonneg_right hgr (show 0 ≤ x by linarith),
        mul_lt_mul_of_pos_right hratio (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))]
    · positivity

end exists_distinctMultiplesIntervalLength_sub_gt

open exists_distinctMultiplesIntervalLength_sub_gt

/-- **Shifting the interval can greatly increase the least length.** For natural numbers $n$ and
$m$, let $f(n, m)$ be the least natural number $L$ such that the interval $(m, m + L]$ contains
distinct multiples of $1, \dots, n$. For all sufficiently large natural numbers $n$ there is a
positive integer $m$ with
$$
f(n, m) - f(n, n) > \frac{0.36\, n \log n}{\log \log n}.
$$

Since $f(n, m)$ is periodic in $m$ with period $\operatorname{lcm}(1, \dots, n)$, this says that
$\max_{m \ge 1} f(n, m) - f(n, n) > 0.36\, n \log n / \log \log n$ for all large $n$, the form
stated in the source.

Source: Wouter van Doorn, *On the Length of an Interval That Contains Distinct Multiples of the
First n Positive Integers*, INTEGERS 26 (2026), Article A7, Theorem 1
(`integers-2026-A7-thm-1`). -/
public theorem exists_distinctMultiplesIntervalLength_sub_gt :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ m : ℕ, 0 < m ∧
      0.36 * (n : ℝ) * Real.log n / Real.log (Real.log n) <
        (distinctMultiplesIntervalLength n m : ℝ) - distinctMultiplesIntervalLength n n := by
  obtain ⟨N, hpr⟩ := enough_primes
  have hl : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (isLittleO_log_rpow_rpow_atTop 3 (s := 1) zero_lt_one).bound
    (show (0 : ℝ) < 1 / 10 ^ 11 by norm_num)
  filter_upwards [eventually_ge_atTop (100 + 2 * N), hl.eventually_ge_atTop 2,
    (tendsto_log_atTop.comp hl).eventually_ge_atTop (1000 + (N : ℝ)),
    hl.eventually hsmall] with n hn hx₀ hy₀ hsmall
  let x := log (n : ℝ)
  let y := log x
  change 2 ≤ x at hx₀
  change 1000 + (N : ℝ) ≤ y at hy₀
  change ‖y ^ (3 : ℝ)‖ ≤ _ * ‖x ^ (1 : ℝ)‖ at hsmall
  have hybig : 1000 ≤ y := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hypos : 0 < y := by linarith
  rw [rpow_ofNat, rpow_one, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by linarith)] at hsmall
  have hy₂ : y ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hy₃ : y ^ 2 ≤ y ^ 3 := by nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ y - 1 by linarith)]
  have hyx : y ≤ 0.001 * x := by linarith
  let K := ⌈0.001 * x / y⌉₊
  have hKlo : 0.001 * x ≤ (K : ℝ) * y := (div_le_iff₀ hypos).mp (Nat.le_ceil _)
  have hKhi : (K : ℝ) * y ≤ 0.002 * x := by
    have he := Nat.ceil_lt_add_one (show 0 ≤ 0.001 * x / y by positivity)
    change (K : ℝ) < _ at he
    linarith [mul_lt_mul_of_pos_right he hypos, div_mul_cancel₀ (0.001 * x) hypos.ne']
  have hKbig : 2000000 * y ^ 2 ≤ K := by
    apply (mul_le_mul_iff_left₀ hypos).mp
    nlinarith only [hKlo, hsmall, hypos.le, pow_nonneg hypos.le 3]
  have hKN : N ≤ K ^ 2 := by
    have hNK : (N : ℝ) ≤ K := by linarith
    have hk : 0 < K := Nat.one_le_ceil_iff.2 (by positivity)
    exact (show N ≤ K by exact_mod_cast hNK).trans (by rw [sq]; exact Nat.le_mul_of_pos_right K hk)
  have hKx : (K : ℝ) ≤ x := by
    nlinarith [mul_le_mul_of_nonneg_left hybig (Nat.cast_nonneg (α := ℝ) K)]
  have hdiag := diagonal_estimate rfl rfl (by omega : 2 ≤ n) hybig hKN hKx hKbig hKlo hpr
  let d := ⌊0.44 * x / y⌋₊
  have hdlo : 0.44 * x ≤ ((d + 1 : ℕ) : ℝ) * y := by
    have := Nat.lt_floor_add_one (0.44 * x / y)
    push_cast
    exact ((div_lt_iff₀ hypos).mp this).le
  have hdhi : ((d + 1 : ℕ) : ℝ) * y ≤ 0.45 * x := by
    have hf : (d : ℝ) * y ≤ 0.44 * x := (le_div_iff₀ hypos).mp (Nat.floor_le (by positivity))
    push_cast
    linarith
  obtain ⟨m, hm, hshift⟩ := shift_estimate rfl rfl hn hx₀ hybig hdhi hpr
  refine ⟨m, hm, ?_⟩
  have hn' : 23 * n ≤ 25 * (n - 2 * (n / 25)) := by omega
  have hlen : 0.92 * (n : ℝ) ≤ (n - 2 * (n / 25) : ℕ) := by
    have : 23 * (n : ℝ) ≤ 25 * ((n - 2 * (n / 25) : ℕ) : ℝ) := by exact_mod_cast hn'
    linarith
  have hs : ((d + 1 : ℕ) : ℝ) * (n - 2 * (n / 25) : ℕ) < distinctMultiplesIntervalLength n m := by
    exact_mod_cast hshift
  have hu : (distinctMultiplesIntervalLength n n : ℝ) ≤ 2 * ((K : ℝ) * n) := by exact_mod_cast hdiag
  change 0.36 * (n : ℝ) * x / y < _
  apply (div_lt_iff₀ hypos).2
  have H := mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg (α := ℝ) (d + 1))
  nlinarith only [mul_lt_mul_of_pos_right (H.trans_lt hs) hypos,
    mul_le_mul_of_nonneg_right hdlo (Nat.cast_nonneg (α := ℝ) n),
    mul_le_mul_of_nonneg_right hu hypos.le,
    mul_le_mul_of_nonneg_right hKhi (Nat.cast_nonneg (α := ℝ) n),
    mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (show 0 ≤ x by linarith)]

end MetaMathlibExt
