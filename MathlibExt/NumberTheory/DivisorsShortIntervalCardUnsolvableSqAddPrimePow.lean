/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Residues where `x ^ 2 + p ^ v * u` is not a square

For a prime `p ≥ 3` and an integer `u` not divisible by `p`, the main result,
`card_unsolvable_sq_add_primePow`, counts the `x` modulo `p ^ (v + 1)` for which
`x ^ 2 + p ^ v * u` is not a square modulo `p ^ (v + 1)`. This is Lemma 4 of Patrick Letendre,
*Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026), Article A115.
-/

namespace MetaMathlibExt

private noncomputable def pairEquiv {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (u : ZMod p) (hu : u ≠ 0) :
    {z : ZMod p × ZMod p // z.2 ^ 2 = z.1 ^ 2 + u} ≃ {a : ZMod p // a ≠ 0} := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact (Nat.le_of_dvd (by norm_num) hd).not_gt (by omega)
  refine
    { toFun := fun z => ⟨z.1.2 - z.1.1, ?_⟩
      invFun := fun a => ⟨((u / a - a) / 2, (u / a + a) / 2), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    have he : z.1.2 = z.1.1 := sub_eq_zero.mp h
    have hz := z.2
    rw [he] at hz
    exact hu (by linear_combination -hz)
  · field_simp [a.2, h2]
    ring
  · intro z
    have ha : z.1.2 - z.1.1 ≠ 0 := by
      intro he
      have hz := z.2
      rw [sub_eq_zero.mp he] at hz
      exact hu (by linear_combination -hz)
    have he : u / (z.1.2 - z.1.1) = z.1.2 + z.1.1 := by
      apply (div_eq_iff ha).mpr
      linear_combination -z.2
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> rw [he] <;> field_simp <;> ring
  · intro a
    apply Subtype.ext
    dsimp
    field_simp [a.2, h2]
    ring

private theorem base_field {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    2 * (((Finset.univ : Finset (ZMod p)).filter fun x =>
      ¬ IsSquare (x ^ 2 + (u : ZMod p))).card : ℤ) = p - legendreSym p (-u) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hu' : (u : ZMod p) ≠ 0 :=
    fun h => hu ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp h)
  have hpairs : Fintype.card {z : ZMod p × ZMod p //
      z.2 ^ 2 = z.1 ^ 2 + (u : ZMod p)} = p - 1 := by
    rw [Fintype.card_congr (pairEquiv hp (u : ZMod p) hu')]
    simp [Fintype.card_subtype_compl, ZMod.card]
  have hsum : (∑ x : ZMod p, ((Finset.univ.filter fun y : ZMod p =>
      y ^ 2 = x ^ 2 + (u : ZMod p)).card : ℤ)) = (p : ℤ) - 1 := by
    have hs := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun x y : ZMod p => y ^ 2 = x ^ 2 + (u : ZMod p)))
    rw [hpairs, Fintype.card_sigma] at hs
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hs
    simpa [Fintype.card_subtype, Nat.cast_sum, Nat.cast_sub (by omega : 1 ≤ p)] using hcast.symm
  have hzero : (((Finset.univ : Finset (ZMod p)).filter fun x =>
      x ^ 2 + (u : ZMod p) = 0).card : ℤ) = legendreSym p (-u) + 1 := by
    have h := legendreSym.card_sqrts p hp2 (-u)
    simpa [Set.toFinset_ofPred, eq_neg_iff_add_eq_zero] using h
  have hpoint (x : ZMod p) :
      ((Finset.univ.filter fun y : ZMod p => y ^ 2 = x ^ 2 + (u : ZMod p)).card : ℤ) +
        2 * (if ¬ IsSquare (x ^ 2 + (u : ZMod p)) then 1 else 0) +
        (if x ^ 2 + (u : ZMod p) = 0 then 1 else 0) = 2 := by
    have h := quadraticChar_card_sqrts hchar (x ^ 2 + (u : ZMod p))
    simp only [Set.toFinset_ofPred] at h
    by_cases h0 : x ^ 2 + (u : ZMod p) = 0
    · simp [h0, Finset.filter_eq']
    · by_cases hs : IsSquare (x ^ 2 + (u : ZMod p))
      · rw [(quadraticChar_one_iff_isSquare h0).mpr hs] at h
        simpa [h0, hs] using h
      · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hs] at h
        simpa [h0, hs] using h
  have htotal := Finset.sum_congr rfl (fun x (_ : x ∈ (Finset.univ : Finset (ZMod p))) => hpoint x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, hsum, hzero] at htotal
  linarith

private def solvable (p v : ℕ) (u x : ℤ) : Prop :=
  ∃ y : ℤ, x ^ 2 + (p : ℤ) ^ v * u ≡ y ^ 2 [ZMOD (p : ℤ) ^ (v + 1)]

private theorem solvable_unit {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (v : ℕ) (hv : 1 ≤ v) (u x : ℤ) (hx : ¬ (p : ℤ) ∣ x) : solvable p v u x := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact (Nat.le_of_dvd (by norm_num) hd).not_gt (by omega)
  have hx' : (x : ZMod p) ≠ 0 :=
    fun h => hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h)
  obtain ⟨t, ht⟩ := ZMod.intCast_surjective ((u : ZMod p) / (2 * (x : ZMod p)))
  have ht' : (p : ℤ) ∣ u - 2 * x * t := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ht, mul_div_cancel₀ _ (mul_ne_zero h2 hx'), sub_self]
  have hvv : v + 1 ≤ v + v := by omega
  refine ⟨x + (p : ℤ) ^ v * t, Int.modEq_iff_dvd.mpr ?_⟩
  have hmain : (p : ℤ) ^ (v + 1) ∣ (p : ℤ) ^ v * (2 * x * t - u) := by
    obtain ⟨k, hk⟩ := (dvd_neg.mpr ht' : (p : ℤ) ∣ -(u - 2 * x * t))
    refine ⟨k, ?_⟩
    rw [pow_succ]
    rw [show 2 * x * t - u = (p : ℤ) * k by linear_combination hk]
    ring
  have htail : (p : ℤ) ^ (v + 1) ∣ (p : ℤ) ^ (v + v) * t ^ 2 :=
    dvd_mul_of_dvd_left (pow_dvd_pow _ hvv) _
  convert dvd_add hmain htail using 1; ring

private theorem root_dvd {p : ℕ} [Fact p.Prime] (v : ℕ) (hv : 1 ≤ v)
    (u x y : ℤ) (hx : (p : ℤ) ∣ x)
    (h : x ^ 2 + (p : ℤ) ^ v * u ≡ y ^ 2 [ZMOD (p : ℤ) ^ (v + 1)]) :
    (p : ℤ) ∣ y := by
  have hmod := h.of_dvd (show (p : ℤ) ∣ (p : ℤ) ^ (v + 1) from
    dvd_pow_self _ (by omega))
  have hzero : (p : ℤ) ∣ x ^ 2 + (p : ℤ) ^ v * u :=
    dvd_add (dvd_pow hx (by norm_num)) (dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _)
  have hy : (p : ℤ) ∣ y ^ 2 := by
    have hd := hmod.dvd
    convert dvd_add hd hzero using 1; ring
  exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_of_dvd_pow hy

private theorem solvable_one_iff {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (x : ℤ) :
    solvable p 1 u x ↔ ¬ (p : ℤ) ∣ x := by
  constructor
  · rintro ⟨y, hy⟩ hx
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, hb⟩ := root_dvd 1 le_rfl u ((p : ℤ) * a) y (dvd_mul_right _ _) hy
    rw [hb] at hy
    have hd := hy.dvd
    have hsub : (p : ℤ) ^ 2 ∣ (p : ℤ) * u := by
      have hs : (p : ℤ) ^ 2 ∣ ((p : ℤ) * b) ^ 2 - ((p : ℤ) * a) ^ 2 := by
        refine ⟨b ^ 2 - a ^ 2, ?_⟩
        ring
      convert dvd_sub hs hd using 1; simp
    apply hu
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    simpa only [pow_two, mul_dvd_mul_iff_left hp0] using hsub
  · exact solvable_unit hp 1 le_rfl u x

private theorem solvable_mul_iff {p : ℕ} [Fact p.Prime] (u x : ℤ) (v : ℕ) :
    solvable p (v + 2) u ((p : ℤ) * x) ↔ solvable p v u x := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hm : (p : ℤ) ^ (v + 2 + 1) = (p : ℤ) ^ 2 * (p : ℤ) ^ (v + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have he : ((p : ℤ) * x) ^ 2 + (p : ℤ) ^ (v + 2) * u =
      (p : ℤ) ^ 2 * (x ^ 2 + (p : ℤ) ^ v * u) := by
    rw [pow_add]
    ring
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := root_dvd (v + 2) (by omega) u ((p : ℤ) * x) y
      (dvd_mul_right _ _) hy
    refine ⟨z, ?_⟩
    rw [he, hm, mul_pow] at hy
    exact Int.ModEq.mul_left_cancel' (pow_ne_zero _ hp0) hy
  · rintro ⟨y, hy⟩
    refine ⟨(p : ℤ) * y, ?_⟩
    rw [he, hm, mul_pow]
    exact hy.mul_left'

private theorem solvable_mod (p v : ℕ) (u x : ℤ) :
    solvable p v u (x % (p : ℤ) ^ (v + 1)) ↔ solvable p v u x := by
  have h : x % (p : ℤ) ^ (v + 1) ≡ x [ZMOD (p : ℤ) ^ (v + 1)] := Int.mod_modEq x _
  have h' := h.pow 2 |>.add_right ((p : ℤ) ^ v * u)
  exact ⟨fun ⟨y, hy⟩ => ⟨y, h'.symm.trans hy⟩,
    fun ⟨y, hy⟩ => ⟨y, h'.trans hy⟩⟩

private theorem card_filter_multiples (p n : ℕ) (hp : 0 < p) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ x, P x → p ∣ x) :
    ((Finset.range (p * n)).filter P).card =
      ((Finset.range n).filter fun x => P (p * x)).card := by
  symm
  apply Finset.card_bij (fun x _ => p * x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨Nat.mul_lt_mul_of_pos_left hx.1 hp, hx.2⟩
  · intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro x hx
    obtain ⟨hxlt, hxP⟩ := Finset.mem_filter.mp hx
    obtain ⟨z, rfl⟩ := hP x hxP
    refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hxP⟩, rfl⟩
    exact (Nat.mul_lt_mul_left hp).mp (Finset.mem_range.mp hxlt)

private theorem card_filter_periodic (n k : ℕ) (hn : 0 < n) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ x, P (x % n) ↔ P x) :
    ((Finset.range (k * n)).filter P).card = k * ((Finset.range n).filter P).card := by
  calc
    _ = ((Finset.range k).product ((Finset.range n).filter P)).card := by
      symm
      apply Finset.card_bij (fun a _ => a.1 * n + a.2)
      · intro a ha
        obtain ⟨ha, hb⟩ := Finset.mem_product.mp ha
        obtain ⟨hb, hPb⟩ := Finset.mem_filter.mp hb
        have hal := Finset.mem_range.mp ha
        have hbl := Finset.mem_range.mp hb
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
        · calc
            a.1 * n + a.2 < a.1 * n + n := Nat.add_lt_add_left hbl _
            _ = (a.1 + 1) * n := by ring
            _ ≤ k * n := Nat.mul_le_mul_right n hal
        · apply (hP _).mp
          simpa [Nat.add_mod, Nat.mod_eq_of_lt hbl] using hPb
      · intro a ha b hb he
        have ha2 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_product.mp ha).2).1
        have hb2 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_product.mp hb).2).1
        have hfirst := congrArg (fun x => x / n) he
        have hsecond := congrArg (fun x => x % n) he
        apply Prod.ext
        · simpa [Nat.add_div, Nat.div_eq_of_lt ha2, Nat.div_eq_of_lt hb2,
            Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2, hn, hn.ne',
            not_le.mpr ha2, not_le.mpr hb2] using hfirst
        · simpa [Nat.add_mod, Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] using hsecond
      · intro x hx
        obtain ⟨hxl, hPx⟩ := Finset.mem_filter.mp hx
        have hxm : x % n < n := Nat.mod_lt _ hn
        refine ⟨(x / n, x % n), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hn).mpr
            (by simpa [mul_comm] using Finset.mem_range.mp hxl))
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxm, (hP x).mpr hPx⟩
        · simpa [mul_comm] using Nat.div_add_mod x n
    _ = _ := by simp

open scoped Classical in
private theorem count_one {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    ((Finset.range (p ^ (1 + 1))).filter fun x : ℕ => ¬ solvable p 1 u x).card = p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hP (x : ℕ) (hx : ¬ solvable p 1 u x) : p ∣ x := by
    have h : (p : ℤ) ∣ (x : ℤ) := by simpa [solvable_one_iff hp u hu] using hx
    exact_mod_cast h
  rw [show p ^ (1 + 1) = p * p by ring, card_filter_multiples p p hp0 _ hP]
  simp [solvable_one_iff hp u hu]

open scoped Classical in
private theorem count_rec {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (u : ℤ) (v : ℕ) :
    ((Finset.range (p ^ (v + 2 + 1))).filter fun x : ℕ => ¬ solvable p (v + 2) u x).card =
      p * ((Finset.range (p ^ (v + 1))).filter fun x : ℕ => ¬ solvable p v u x).card := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hP (x : ℕ) (hx : ¬ solvable p (v + 2) u x) : p ∣ x := by
    by_contra h
    apply hx
    exact solvable_unit hp (v + 2) (by omega) u x (by exact_mod_cast h)
  rw [show p ^ (v + 2 + 1) = p * p ^ (v + 2) by rw [pow_succ]; ring,
    card_filter_multiples p (p ^ (v + 2)) hp0 _ hP]
  simp only [Nat.cast_mul, solvable_mul_iff]
  have hvpow : p ^ (v + 2) = p * p ^ (v + 1) := by
    rw [show v + 2 = v + 1 + 1 by omega, pow_succ]
    ring
  rw [hvpow]
  apply card_filter_periodic _ _ (pow_pos hp0 _) _
  intro x
  have h := solvable_mod p v u x
  norm_cast at h
  exact not_congr h

private theorem solvable_zero_iff {p : ℕ} [Fact p.Prime] (u x : ℤ) :
    solvable p 0 u x ↔ IsSquare ((x : ZMod p) ^ 2 + (u : ZMod p)) := by
  simp only [solvable, pow_zero, Nat.zero_add, pow_one, one_mul]
  rw [isSquare_iff_exists_sq]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(y : ZMod p), ?_⟩
    have h := (ZMod.intCast_eq_intCast_iff (x ^ 2 + u) (y ^ 2) p).mpr hy
    push_cast at h
    exact h
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy⟩ := ZMod.intCast_surjective z
    refine ⟨y, (ZMod.intCast_eq_intCast_iff (x ^ 2 + u) (y ^ 2) p).mp ?_⟩
    push_cast
    simpa [hy] using hz

open scoped Classical in
private theorem count_zero {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    2 * (((Finset.range (p ^ (0 + 1))).filter fun x : ℕ =>
      ¬ solvable p 0 u x).card : ℤ) = p - legendreSym p (-u) := by
  have hcard : ((Finset.range p).filter fun x : ℕ => ¬ solvable p 0 u x).card =
      ((Finset.univ : Finset (ZMod p)).filter fun x =>
        ¬ IsSquare (x ^ 2 + (u : ZMod p))).card := by
    apply Finset.card_bij (fun (x : ℕ) _ => (x : ZMod p))
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      simpa [solvable_zero_iff] using hx.2
    · intro x hx y hy he
      have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hylt := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
      have h := congrArg ZMod.val he
      simpa [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] using h
    · intro x hx
      have hxP := (Finset.mem_filter.mp hx).2
      refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩, ?_⟩
      · simpa [solvable_zero_iff] using hxP
      · exact ZMod.natCast_zmod_val x
  simpa [hcard] using base_field hp u hu

open scoped Classical in
/-- **Counting $x$ with $x^2 + p^v u$ not a square modulo $p^{v+1}$.** Let $p \ge 3$ be a prime
and let $u$ be an integer not divisible by $p$. For $v \ge 0$ let $S_v$ be the number of integers
$0 \le x < p^{v+1}$ for which there is no integer $y$ with
$x^2 + p^v u \equiv y^2 \pmod{p^{v+1}}$. Then $2 S_0 = p - \left(\frac{-u}{p}\right)$, where
$\left(\frac{-u}{p}\right)$ is the Legendre symbol, $S_1 = p$, and $S_v = p S_{v-2}$ for every
$v \ge 2$.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 4 (`integers-2026-A115-lem-4`). -/
public theorem card_unsolvable_sq_add_primePow {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) :
    let S : ℕ → ℕ := fun v => ((Finset.range (p ^ (v + 1))).filter fun x : ℕ =>
      ¬ ∃ y : ℤ, (x : ℤ) ^ 2 + (p : ℤ) ^ v * u ≡ y ^ 2 [ZMOD (p : ℤ) ^ (v + 1)]).card
    2 * (S 0 : ℤ) = p - legendreSym p (-u) ∧ S 1 = p ∧ ∀ v ≥ 2, S v = p * S (v - 2)
    := by
  dsimp only
  refine ⟨count_zero hp u hu, count_one hp u hu, ?_⟩
  intro v hv
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 2 := ⟨v - 2, by omega⟩
  exact count_rec hp u w

end MetaMathlibExt
