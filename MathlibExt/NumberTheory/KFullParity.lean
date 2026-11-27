/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.KFull

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Parity of `k`-full numbers

We prove that the ratio of the odd and even `k`-full counting functions tends to
`2 - 2 ^ (1 - 1 / k)` for `k ≥ 2`. The odd count uses a unique decomposition
into a `k`th power and a factor with bounded prime exponents. The even count
then follows by grouping according to the exponent of two.
-/

namespace MetaMathlibExt

open Filter Topology

namespace tendsto_card_odd_kFull_div_card_even_kFull

open scoped BigOperators

private def remainder (k e : ℕ) : ℕ := if e % k = 0 then 0 else k + e % k

private def quotient (k e : ℕ) : ℕ := e / k - if e % k = 0 then 0 else 1

private lemma remainder_lt {k e : ℕ} (hk : 0 < k) :
    remainder k e = 0 ∨ k < remainder k e ∧ remainder k e < 2 * k := by
  unfold remainder
  split_ifs with h
  · exact Or.inl rfl
  · have := Nat.mod_lt e hk
    omega

private lemma exp_split {k e : ℕ} (hk : 0 < k) (he : e = 0 ∨ k ≤ e) :
    k * quotient k e + remainder k e = e := by
  unfold quotient remainder
  have h := Nat.div_add_mod e k
  split_ifs with hz
  · simpa [hz] using h
  · have hq : 1 ≤ e / k := Nat.le_div_iff_mul_le hk |>.2 (by omega)
    rw [Nat.mul_sub_left_distrib, mul_one]
    have hle := Nat.le_mul_of_pos_right k hq
    omega

private lemma remainder_eq {k a b : ℕ}
    (hb : b = 0 ∨ k < b ∧ b < 2 * k) :
    remainder k (k * a + b) = b := by
  unfold remainder
  rw [Nat.mul_add_mod]
  rcases hb with rfl | ⟨hlo, hhi⟩
  · simp
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hlo.le
    have hi : i < k := by omega
    have hi₀ : i ≠ 0 := by omega
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hi, ite_eq_right hi₀]

private abbrev Kernel (k : ℕ) :=
  {b : ℕ // Odd b ∧ ∀ p : ℕ, b.factorization p = 0 ∨
    k < b.factorization p ∧ b.factorization p < 2 * k}

private lemma odd_ne_zero {n : ℕ} (hn : Odd n) : n ≠ 0 := by
  rintro rfl
  simp at hn

private lemma kernel_ne_zero {k : ℕ} (b : Kernel k) : b.val ≠ 0 :=
  odd_ne_zero b.property.1

-- The nonzero remainder exponents lie strictly between k and 2k.
private lemma decompose {k n : ℕ} (hk : 0 < k) (hn : Nat.IsKFull k n) (ho : Odd n) :
    ∃ (b : Kernel k) (a : ℕ), Odd a ∧ a ^ k * b.val = n := by
  let f := n.factorization.mapRange (quotient k) (by simp [quotient])
  let g := n.factorization.mapRange (remainder k) (by simp [remainder])
  let a := f.prod (· ^ ·)
  let b := g.prod (· ^ ·)
  have ha₀ : a ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)).ne_zero
  have hb₀ : b ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)).ne_zero
  have ha : a.factorization = f :=
    Nat.factorization_prod_pow_eq_self_of_le_factorization (by
      intro p
      exact (Nat.sub_le ..).trans (Nat.div_le_self ..))
  have hb : b.factorization = g := Nat.factorization_prod_pow_eq_self fun p hp =>
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have hab : a ^ k * b = n := by
    apply Nat.eq_of_factorization_eq (mul_ne_zero (pow_ne_zero _ ha₀) hb₀) hn.1
    rw [Nat.factorization_mul (pow_ne_zero _ ha₀) hb₀, Nat.factorization_pow, ha, hb]
    intro p
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, f, g, Finsupp.mapRange_apply]
    apply exp_split hk
    by_cases hp : p ∈ n.primeFactors
    · exact Or.inr ((Nat.isKFull_iff_factorization hn.1).mp hn _ (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp))
    · exact Or.inl (Finsupp.notMem_support_iff.mp hp)
  have ho' : Odd (a ^ k) ∧ Odd b := Nat.odd_mul.mp (hab ▸ ho)
  refine ⟨⟨b, ho'.2, fun p => ?_⟩, a, (Nat.odd_pow_iff hk.ne').mp ho'.1, hab⟩
  rw [hb]
  exact remainder_lt hk

private lemma full_mul {k : ℕ} (b : Kernel k) {a : ℕ} (ha : Odd a) :
    Nat.IsKFull k (a ^ k * b.val) := by
  have hne := mul_ne_zero (pow_ne_zero k (odd_ne_zero ha)) (kernel_ne_zero b)
  apply (Nat.isKFull_iff_factorization hne).2
  intro p hp hd
  have hpos : 0 < (a ^ k * b.val).factorization p :=
    (hp.dvd_iff_one_le_factorization hne).mp hd
  rw [Nat.factorization_mul (pow_ne_zero _ (odd_ne_zero ha)) (kernel_ne_zero b),
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hpos ⊢
  rcases b.property.2 p with h | h
  · rw [h, add_zero] at hpos ⊢
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left hpos)
  · omega

private lemma decompose_inj {k : ℕ} (hk : 0 < k) {b c : Kernel k} {a d : ℕ}
    (ha : Odd a) (hd : Odd d) (h : a ^ k * b.val = d ^ k * c.val) :
    b = c ∧ a = d := by
  have hb : b = c := by
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq (kernel_ne_zero b) (kernel_ne_zero c)
    intro p
    have he := congrArg (fun n : ℕ => n.factorization p) h
    simp only [Nat.factorization_mul (pow_ne_zero _ (odd_ne_zero ha)) (kernel_ne_zero b),
      Nat.factorization_mul (pow_ne_zero _ (odd_ne_zero hd)) (kernel_ne_zero c),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at he
    simpa only [remainder_eq (b.property.2 p), remainder_eq (c.property.2 p)]
      using congrArg (remainder k) he
  subst c
  exact ⟨rfl, Nat.pow_left_injective hk.ne' (Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero (kernel_ne_zero b)) h)⟩

private noncomputable def weight (k n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / (k : ℝ)))

private lemma weight_pos {k n : ℕ} (hn : n ≠ 0) : 0 < weight k n := by
  unfold weight
  positivity

private lemma weight_mul (k a b : ℕ) : weight k (a * b) = weight k a * weight k b := by
  simp only [weight, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

private lemma weight_pow (k a e : ℕ) :
    weight k (a ^ e) = (a : ℝ) ^ ((e : ℝ) * (-(1 / (k : ℝ)))) := by
  rw [weight, Nat.cast_pow, Real.rpow_natCast_mul (Nat.cast_nonneg _)]

private lemma summable_primePowers (k : ℕ) (hk : 0 < k) :
    Summable (fun pi : ℕ × Fin k => weight k (pi.1 ^ (k + 1 + pi.2.val))) := by
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hr : (0 : ℝ) < 1 / (k : ℝ) := one_div_pos.mpr hk'
  have hp : Summable (fun p : ℕ => (p : ℝ) ^ (-(1 + 1 / (k : ℝ)))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht : Summable (fun pi : ℕ × Fin k => (pi.1 : ℝ) ^ (-(1 + 1 / (k : ℝ)))) := by
    simpa only [mul_one] using hp.mul_of_nonneg
      (hasSum_fintype (fun _ : Fin k => (1 : ℝ))).summable
      (fun _ => by positivity) (fun _ => by positivity)
  apply ht.of_nonneg_of_le (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rintro ⟨p, i⟩
  change weight k (p ^ (k + 1 + i.val)) ≤ (p : ℝ) ^ (-(1 + 1 / (k : ℝ)))
  rw [weight_pow]
  rcases p.eq_zero_or_pos with rfl | hp'
  · rw [Nat.cast_zero, Real.zero_rpow (ne_of_lt (mul_neg_of_pos_of_neg (by positivity)
      (neg_lt_zero.mpr hr))), Real.zero_rpow (by linarith : -(1 + 1 / (k : ℝ)) ≠ 0)]
  · apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp')
    have hcancel : (k : ℝ) * (1 / (k : ℝ)) = 1 := by
      simp [div_eq_mul_inv, hk'.ne']
    push_cast
    rw [add_mul, add_mul, one_mul, mul_neg (k : ℝ), hcancel]
    have hi := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) i.val)
      (neg_nonpos.mpr hr.le)
    linarith

private lemma kernel_exp {k : ℕ} (b : Kernel k) {p : ℕ} (hp : p ∈ b.val.primeFactors) :
    k < b.val.factorization p ∧ b.val.factorization p < 2 * k := by
  have he : b.val.factorization p ≠ 0 := by
    apply Finsupp.mem_support_iff.mp
    simpa only [Nat.support_factorization] using hp
  exact (b.property.2 p).resolve_left he

private def encode {k : ℕ} (b : Kernel k) : Finset (ℕ × Fin k) :=
  b.val.primeFactors.attach.map
    ⟨fun p => (p.val, ⟨b.val.factorization p.val - (k + 1), by
      have := kernel_exp b p.property
      omega⟩), fun _ _ h => Subtype.ext (congrArg Prod.fst h)⟩

private lemma prod_encode {k : ℕ} (b : Kernel k) :
    (∏ pi ∈ encode b, pi.1 ^ (k + 1 + pi.2.val)) = b.val := by
  calc
    _ = ∏ p ∈ b.val.primeFactors.attach, p.val ^ b.val.factorization p.val := by
      rw [encode, Finset.prod_map]
      apply Finset.prod_congr rfl
      intro p _
      change p.val ^ (k + 1 + (b.val.factorization p.val - (k + 1))) = _
      rw [Nat.add_sub_of_le (kernel_exp b p.property).1]
    _ = b.val := by
      exact (Finset.prod_attach b.val.primeFactors (fun n : ℕ => n ^ b.val.factorization n)).trans
        (Nat.prod_factorization_pow_eq_self (kernel_ne_zero b))

-- Each bounded-exponent factor embeds into a finite set of prime powers.
private lemma summable_weight (k : ℕ) (hk : 0 < k) :
    Summable (fun b : Kernel k => weight k b.val) := by
  classical
  let w := fun pi : ℕ × Fin k => weight k (pi.1 ^ (k + 1 + pi.2.val))
  have hinj : Function.Injective (encode (k := k)) := by
    intro b c h
    apply Subtype.ext
    rw [← prod_encode b, ← prod_encode c, h]
  have hw (s : Finset (ℕ × Fin k)) :
      weight k (∏ pi ∈ s, pi.1 ^ (k + 1 + pi.2.val)) = ∏ pi ∈ s, w pi := by
    induction s using Finset.induction_on with
    | empty => simp [weight]
    | insert p s hp ih => simp [Finset.prod_insert hp, weight_mul, ih, w]
  have hs : Summable (fun s : Finset (ℕ × Fin k) => ∏ pi ∈ s, w pi) :=
    summable_finsetProd_of_summable_nonneg (fun _ =>
      Real.rpow_nonneg (Nat.cast_nonneg _) _) (summable_primePowers k hk)
  convert hs.comp_injective hinj using 1
  ext b
  change weight k b.val = ∏ pi ∈ encode b, w pi
  rw [← hw, prod_encode]

-- A finite set of admissible pairs contributes the sum of the sizes of its fibers.
private lemma count_fibers {ι : Type} (S : ι → Set ℕ) {f : ι × ℕ → ℕ} {T : Set ℕ}
    (hT : T.Finite) (h : Set.BijOn f {p | p.2 ∈ S p.1} T) :
    (T.ncard : ℝ) = ∑' i, ((S i).ncard : ℝ) := by
  classical
  let A := (h.finite_iff_finite.mpr hT).toFinset
  have hA (p : ι × ℕ) : p ∈ A ↔ p.2 ∈ S p.1 := Set.Finite.mem_toFinset _
  have hfiber (i : ι) :
      (((A.filter (fun p => p.1 = i)).card : ℕ) : ℝ) = ((S i).ncard : ℝ) := by
    have heq : (↑(A.filter (fun p => p.1 = i)) : Set (ι × ℕ)) =
        (fun a => (i, a)) '' S i := by
      ext ⟨j, a⟩
      simp only [Finset.mem_coe, Finset.mem_filter, hA, Set.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨ha, rfl⟩
        exact ⟨a, ha, rfl, rfl⟩
      · rintro ⟨b, hb, rfl, rfl⟩
        exact ⟨hb, rfl⟩
    rw [← Set.ncard_coe_finset, heq, Set.ncard_image_of_injective _ (fun _ _ h' =>
      congrArg Prod.snd h')]
  have hout (i : ι) (hi : i ∉ A.image Prod.fst) : ((S i).ncard : ℝ) = 0 := by
    rw [← hfiber]
    have hempty : A.filter (fun p => p.1 = i) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun p hp hpi => hi (Finset.mem_image.mpr ⟨p, hp, hpi⟩)
    simp [hempty]
  rw [← h.ncard_eq, Set.ncard_eq_toFinset_card _ (h.finite_iff_finite.mpr hT)]
  change (A.card : ℝ) = _
  rw [Finset.card_eq_sum_card_image (f := Prod.fst), Nat.cast_sum, tsum_eq_sum hout]
  exact Finset.sum_congr rfl fun i _ => hfiber i

private def counted (k : ℕ) (P : ℕ → Prop) (x : ℝ) : Set ℕ :=
  {n | (n : ℝ) ≤ x ^ k ∧ Nat.IsKFull k n ∧ P n}

private lemma counted_finite (k : ℕ) (P : ℕ → Prop) {x : ℝ} (hx : 0 ≤ x) :
    (counted k P x).Finite :=
  (Set.finite_Iic ⌊x ^ k⌋₊).subset fun _ hn => (Nat.le_floor_iff (pow_nonneg hx k)).2 hn.1

private lemma weight_pow_k {k b : ℕ} (hk : 0 < k) :
    (weight k b) ^ k = (b : ℝ)⁻¹ := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  rw [weight, ← Real.rpow_mul_natCast (Nat.cast_nonneg _), neg_mul,
    one_div_mul_cancel hk', Real.rpow_neg_one]

private lemma le_scale_iff {k b : ℕ} (hk : 0 < k) (hb : b ≠ 0) {x : ℝ} (hx : 0 ≤ x)
    {y : ℝ} (hy : 0 ≤ y) :
    y ^ k * (b : ℝ) ≤ x ^ k ↔ y ≤ x * weight k b := by
  have hb' : (0 : ℝ) < (b : ℝ) := by positivity
  rw [← le_div_iff₀ hb', ← pow_le_pow_iff_left₀ hy
    (mul_nonneg hx (weight_pos (k := k) hb).le) hk.ne', mul_pow, weight_pow_k hk, div_eq_mul_inv]

private lemma count_odd_base {y : ℝ} (hy : 0 ≤ y) :
    {a : ℕ | (a : ℝ) ≤ y ∧ Odd a}.ncard = ⌊(y + 1) / 2⌋₊ := by
  let f (j : ℕ) := 2 * j + 1
  have h : Set.BijOn f (Set.Iio ⌊(y + 1) / 2⌋₊) {a : ℕ | (a : ℝ) ≤ y ∧ Odd a} := by
    have hle (j : ℕ) : (f j : ℝ) ≤ y ↔ j < ⌊(y + 1) / 2⌋₊ := by
      rw [← Nat.succ_le_iff, Nat.le_floor_iff (by positivity)]
      push_cast [f]
      constructor <;> intro hj <;> linarith
    refine ⟨fun j hj => ⟨(hle j).2 hj, Nat.odd_iff.mpr (by dsimp [f]; omega)⟩, ?_, ?_⟩
    · intro a _ b _ hab
      dsimp [f] at hab
      omega
    · rintro a ⟨ha, ⟨j, rfl⟩⟩
      exact ⟨j, (hle j).1 (by simpa [f, two_mul, add_assoc] using ha), by simp [f, two_mul]⟩
  rw [← h.ncard_eq, ← show (↑(Finset.range ⌊(y + 1) / 2⌋₊) : Set ℕ) =
    Set.Iio ⌊(y + 1) / 2⌋₊ by ext j; simp]
  rw [Set.ncard_coe_finset, Finset.card_range]

private lemma odd_count {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 ≤ x) :
    ((counted k Odd x).ncard : ℝ) = ∑' b : Kernel k, (⌊(x * weight k b.val + 1) / 2⌋₊ : ℝ) := by
  let S (b : Kernel k) := {a : ℕ | (a : ℝ) ≤ x * weight k b.val ∧ Odd a}
  let f (p : Kernel k × ℕ) := p.2 ^ k * p.1.val
  have hle (b : Kernel k) (a : ℕ) : ((a ^ k * b.val : ℕ) : ℝ) ≤ x ^ k ↔
      (a : ℝ) ≤ x * weight k b.val := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      (le_scale_iff hk (kernel_ne_zero b) hx (Nat.cast_nonneg a))
  have h : Set.BijOn f {p | p.2 ∈ S p.1} (counted k Odd x) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨b, a⟩ ⟨hle', ha⟩
      exact ⟨(hle b a).2 hle', full_mul b ha,
        Nat.odd_mul.mpr ⟨(Nat.odd_pow_iff hk.ne').mpr ha, b.property.1⟩⟩
    · rintro ⟨b, a⟩ ⟨_, ha⟩ ⟨c, d⟩ ⟨_, hd⟩ he
      obtain ⟨rfl, rfl⟩ := decompose_inj hk ha hd he
      rfl
    · rintro n ⟨hn, hkfull, hnodd⟩
      obtain ⟨b, a, ha, rfl⟩ := decompose hk hkfull hnodd
      exact ⟨(b, a), ⟨(hle b a).1 hn, ha⟩, rfl⟩
  rw [count_fibers S (counted_finite k Odd hx) h]
  refine tsum_congr fun b => ?_
  dsimp only [S]
  rw [count_odd_base (mul_nonneg hx (weight_pos (k := k) (kernel_ne_zero b)).le)]

private lemma floor_half_le {y : ℝ} (hy : 0 ≤ y) : (⌊(y + 1) / 2⌋₊ : ℝ) ≤ y := by
  rcases lt_or_ge y 1 with h | h
  · rw [Nat.floor_eq_zero.mpr (by linarith), Nat.cast_zero]
    exact hy
  · have := Nat.floor_le (show 0 ≤ (y + 1) / 2 by positivity)
    linarith

private lemma tendsto_floor_half {w : ℝ} (hw : 0 < w) :
    Tendsto (fun x : ℝ => (⌊(x * w + 1) / 2⌋₊ : ℝ) / x) atTop (𝓝 (w / 2)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (g := fun x : ℝ => x⁻¹)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs, inv_eq_one_div, div_sub' hx.ne', abs_div, abs_of_pos hx,
      div_le_div_iff_of_pos_right hx, abs_le]
    have h₁ := Nat.floor_le (show 0 ≤ (x * w + 1) / 2 by positivity)
    have h₂ := Nat.lt_floor_add_one ((x * w + 1) / 2)
    constructor <;> linarith
  · exact tendsto_inv_atTop_zero

private noncomputable def oddConstant (k : ℕ) : ℝ :=
  ∑' b : Kernel k, weight k b.val

private lemma oddConstant_pos {k : ℕ} (hk : 0 < k) : 0 < oddConstant k := by
  apply (summable_weight k hk).tsum_pos (fun b => (weight_pos (kernel_ne_zero b)).le)
    (⟨1, by simp⟩ : Kernel k)
  exact weight_pos one_ne_zero

private lemma odd_count_le {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 ≤ x) :
    ((counted k Odd x).ncard : ℝ) ≤ x * oddConstant k := by
  rw [odd_count hk hx, oddConstant, ← (summable_weight k hk).tsum_mul_left]
  have h (b : Kernel k) := floor_half_le (mul_nonneg hx (weight_pos (k := k) (kernel_ne_zero b)).le)
  let hs := (summable_weight k hk).mul_left x
  exact (hs.of_nonneg_of_le (fun _ => Nat.cast_nonneg _) h).tsum_le_tsum h hs

private lemma tendsto_odd_count {k : ℕ} (hk : 0 < k) :
    Tendsto (fun x : ℝ => ((counted k Odd x).ncard : ℝ) / x) atTop (𝓝 (oddConstant k / 2)) := by
  rw [oddConstant, ← tsum_div_const]
  refine (tendsto_tsum_of_dominated_convergence (summable_weight k hk)
    (fun b => tendsto_floor_half (weight_pos (kernel_ne_zero b))) ?_).congr' ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx b
    rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hx.le), div_le_iff₀ hx,
      mul_comm (weight k b.val) x]
    exact floor_half_le (mul_nonneg hx.le (weight_pos (kernel_ne_zero b)).le)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [odd_count hk hx.le]
    exact tsum_div_const

private lemma two_factorization {e m : ℕ} (hm : Odd m) :
    (2 ^ e * m).factorization 2 = e := by
  have hm' : ¬ 2 ∣ m := fun h => Nat.not_even_iff_odd.mpr hm (even_iff_two_dvd.mpr h)
  rw [Nat.factorization_mul (by positivity) (odd_ne_zero hm), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm', add_zero]

private lemma full_two_pow_mul {k e m : ℕ} (hke : k ≤ e) (hm : Nat.IsKFull k m) :
    Nat.IsKFull k (2 ^ e * m) := by
  refine ⟨mul_ne_zero (by positivity) hm.1, fun p hp hd => ?_⟩
  rcases eq_or_ne p 2 with rfl | hne
  · exact (pow_dvd_pow 2 hke).trans (dvd_mul_right ..)
  · have hpm : p ∣ m := (hp.dvd_mul.mp hd).resolve_left fun h => hne
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two |>.mp (hp.dvd_of_dvd_pow h))
    exact (hm.2 p hp hpm).trans (dvd_mul_left ..)

private lemma full_ordCompl {k n : ℕ} (hn : Nat.IsKFull k n) :
    Nat.IsKFull k (ordCompl[2] n) := by
  apply (Nat.isKFull_iff_factorization (Nat.ordCompl_pos 2 hn.1).ne').mpr
  intro p hp hd
  have hne : p ≠ 2 := fun h => Nat.not_dvd_ordCompl Nat.prime_two hn.1 (h ▸ hd)
  rw [Nat.factorization_ordCompl, Finsupp.erase_ne hne]
  exact (Nat.isKFull_iff_factorization hn.1).mp hn p hp (hd.trans (Nat.ordCompl_dvd n 2))

-- Removing the entire power of two leaves an odd k-full number.
private lemma even_count {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 0 ≤ x) :
    ((counted k Even x).ncard : ℝ) =
      ∑' j : ℕ, ((counted k Odd (x * weight k (2 ^ (k + j)))).ncard : ℝ) := by
  let S (j : ℕ) := counted k Odd (x * weight k (2 ^ (k + j)))
  let f (p : ℕ × ℕ) := 2 ^ (k + p.1) * p.2
  have hle (j m : ℕ) : (f (j, m) : ℝ) ≤ x ^ k ↔
      (m : ℝ) ≤ (x * weight k (2 ^ (k + j))) ^ k := by
    have hpos : (0 : ℝ) < ((2 ^ (k + j) : ℕ) : ℝ) := by positivity
    simp only [f, Nat.cast_mul, mul_pow, weight_pow_k hk]
    rw [mul_comm (((2 ^ (k + j) : ℕ) : ℝ)), ← le_div_iff₀ hpos, div_eq_mul_inv]
  have h : Set.BijOn f {p | p.2 ∈ S p.1} (counted k Even x) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨j, m⟩ ⟨hm, hfull, _⟩
      exact ⟨(hle j m).2 hm, full_two_pow_mul (Nat.le_add_right k j) hfull,
        even_iff_two_dvd.mpr ((dvd_pow_self 2 (by omega : k + j ≠ 0)).trans (dvd_mul_right ..))⟩
    · rintro ⟨i, a⟩ ⟨_, _, ha⟩ ⟨j, b⟩ ⟨_, _, hb⟩ he
      have hval := congrArg (fun n : ℕ => n.factorization 2) he
      change (2 ^ (k + i) * a).factorization 2 = (2 ^ (k + j) * b).factorization 2 at hval
      rw [two_factorization ha, two_factorization hb] at hval
      have hij : i = j := by omega
      subst j
      exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left (by positivity) he)
    · rintro n ⟨hn, hfull, he⟩
      let e := n.factorization 2
      let m := ordCompl[2] n
      have hk' : k ≤ e :=
        (Nat.isKFull_iff_factorization hfull.1).mp hfull 2 Nat.prime_two (even_iff_two_dvd.mp he)
      let j := e - k
      have hfm : f (j, m) = n := by
        change 2 ^ (k + (e - k)) * m = n
        rw [Nat.add_sub_of_le hk']
        exact Nat.ordProj_mul_ordCompl_eq_self n 2
      refine ⟨(j, m), ⟨(hle j m).1 (hfm ▸ hn), full_ordCompl hfull, ?_⟩, hfm⟩
      exact Nat.not_even_iff_odd.mp fun hm =>
        Nat.not_dvd_ordCompl Nat.prime_two hfull.1 (even_iff_two_dvd.mp hm)
  exact count_fibers S (counted_finite k Even hx) h

private lemma weight_two_pow {k : ℕ} (hk : 0 < k) (j : ℕ) :
    weight k (2 ^ (k + j)) = (weight k 2) ^ j / 2 := by
  have hp (e : ℕ) : weight k (2 ^ e) = (weight k 2) ^ e := by
    rw [weight_pow, mul_comm, Real.rpow_mul_natCast (by positivity)]
    rfl
  rw [pow_add, weight_mul, hp k, hp j, weight_pow_k hk]
  ring

private lemma weight_two_lt_one {k : ℕ} (hk : 0 < k) : weight k 2 < 1 := by
  unfold weight
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr (by positivity))

private lemma tendsto_even_count {k : ℕ} (hk : 0 < k) :
    Tendsto (fun x : ℝ => ((counted k Even x).ncard : ℝ) / x) atTop
      (𝓝 (oddConstant k / 2 / (2 * (1 - weight k 2)))) := by
  let q := weight k 2
  let w (j : ℕ) := weight k (2 ^ (k + j))
  have hw (j : ℕ) : 0 < w j := weight_pos (by positivity)
  have hsum : HasSum w ((1 - q)⁻¹ / 2) := by
    simpa only [w, weight_two_pow hk] using
      (hasSum_geometric_of_lt_one (weight_pos (k := k) two_ne_zero).le
        (weight_two_lt_one hk)).div_const (2 : ℝ)
  have hlim (j : ℕ) : Tendsto
      (fun x : ℝ => ((counted k Odd (x * w j)).ncard : ℝ) / x) atTop
        (𝓝 (oddConstant k / 2 * w j)) := by
    have h := (tendsto_odd_count hk).comp (tendsto_id.atTop_mul_const (hw j))
    refine (h.mul_const (w j)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply, id_eq, div_mul_eq_div_div, div_mul_cancel₀ _ (hw j).ne']
  have h := tendsto_tsum_of_dominated_convergence (hsum.summable.mul_left (oddConstant k)) hlim
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx j
      rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hx.le), div_le_iff₀ hx]
      calc
        _ ≤ x * w j * oddConstant k := odd_count_le hk (mul_nonneg hx.le (hw j).le)
        _ = _ := by ring)
  rw [(hsum.mul_left (oddConstant k / 2)).tsum_eq] at h
  have heq : oddConstant k / 2 * ((1 - q)⁻¹ / 2) =
      oddConstant k / 2 / (2 * (1 - weight k 2)) := by
    simp only [q, div_eq_mul_inv, mul_inv_rev]
  rw [heq] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [even_count hk hx.le]
  exact tsum_div_const

end tendsto_card_odd_kFull_div_card_even_kFull

open tendsto_card_odd_kFull_div_card_even_kFull

/-- **Odd-to-even ratio of $k$-full numbers.** Let $k \ge 2$. For a natural number $N$ let
$K_o(N)$ and $K_e(N)$ be the numbers of odd and of even $k$-full numbers $n \le N$. Then
$K_o(N)/K_e(N) \to 2 - 2^{1 - 1/k}$ as $N \to \infty$.

The counts up to a real $x$ depend only on $\lfloor x \rfloor$, so this is the same as the limit
as $x \to \infty$ through the reals.

Source: Sunanta Srisopha and Teerapat Srichan, *The Odd/Even Dichotomy for the Set of
Numbers That Are Both k-Full and l-Free*, INTEGERS 24 (2024), Article A106, Corollary 2
(`integers-2024-A106-cor-2`). -/
public theorem tendsto_card_odd_kFull_div_card_even_kFull {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun N : ℕ =>
        ({n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ Odd n}.ncard : ℝ) /
          {n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ Even n}.ncard)
      atTop (𝓝 (2 - (2 : ℝ) ^ (1 - 1 / (k : ℝ)))) := by
  have hk₀ : 0 < k := by omega
  have hden : 0 < 2 * (1 - weight k 2) := by linarith [weight_two_lt_one hk₀]
  have ho : 0 < oddConstant k / 2 := by linarith [oddConstant_pos hk₀]
  have h := (tendsto_odd_count hk₀).div (tendsto_even_count hk₀) (div_pos ho hden).ne'
  have hlimit : oddConstant k / 2 / (oddConstant k / 2 / (2 * (1 - weight k 2))) =
      2 - (2 : ℝ) ^ (1 - 1 / (k : ℝ)) := by
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ ho.ne']
    rw [sub_eq_add_neg (1 : ℝ) (1 / (k : ℝ)),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    change 2 * (1 - weight k 2) = 2 - 2 * weight k 2
    ring
  rw [hlimit] at h
  let root (N : ℕ) := (N : ℝ) ^ (1 / (k : ℝ))
  have hroot : Tendsto root atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  refine (h.comp hroot).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hpos : 0 < root N := by dsimp [root]; positivity
  have hpow : root N ^ k = (N : ℝ) := by
    have hk' : (k : ℝ) ≠ 0 := by positivity
    change ((N : ℝ) ^ (1 / (k : ℝ))) ^ k = (N : ℝ)
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N), one_div_mul_cancel hk', Real.rpow_one]
  simp only [Function.comp_apply, Pi.div_apply]
  rw [div_div_div_cancel_right₀ hpos.ne']
  simp only [counted, hpow, Nat.cast_le]

end MetaMathlibExt
