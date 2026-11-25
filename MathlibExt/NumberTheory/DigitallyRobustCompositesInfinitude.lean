/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DigitallyRobustComposites
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Infinitely many digitally robust composites

This module proves infinitude by growing a block of zeros between two fixed decimal blocks.
A finite covering certificate handles digit edits in the zero block and among leading zeros.
Each edit to a fixed block has a divisor that persists along an arithmetic progression
of zero-block lengths.

The certificate uses the covering-system and Chinese remainder method of Filaseta and Juillerat
in *Consecutive primes which are widely digitally delicate* (<https://arxiv.org/abs/2101.08898>).
-/

namespace MetaMathlibExt.infinitelyMany_digitallyRobustComposites

private def Composite (x : ℕ) : Prop := 1 < x ∧ ¬ x.Prime

private theorem composite_of_dvd {p x : ℕ} (hp : 1 < p) (hpx : p < x) (hd : p ∣ x) :
    Composite x := by
  refine ⟨hp.trans hpx, fun h => ?_⟩
  rcases h.eq_one_or_self_of_dvd p hd with h | h <;> omega

-- For finitely many expressions of the form a * 10^n + b, the prime divisors
-- at n = 1 persist along a common progression of exponents.
private theorem composite_progression {u a b v : ℕ} (ha : a ≤ u) (hb : b ≤ u)
    (hv : 11 * u < v) (h : a = 0 → Composite b) :
    Composite (a * 10 ^ (1 + (11 * u).factorial * v) + b) := by
  by_cases ha₀ : a = 0
  · simpa [ha₀] using h ha₀
  have hseed : 1 < a * 10 + b := by omega
  let p := (a * 10 + b).minFac
  have hp : p.Prime := Nat.minFac_prime hseed.ne'
  have hpd : p ∣ a * 10 + b := Nat.minFac_dvd _
  have hpu : p ≤ 11 * u := (Nat.le_of_dvd (by omega) hpd).trans (by omega)
  have hpow : 10 ^ (1 + (11 * u).factorial * v) ≡ 10 [MOD p] := by
    by_cases hten : p ∣ 10
    · have hz := Nat.modEq_zero_iff_dvd.mpr hten
      have hz' : 10 ^ (1 + (11 * u).factorial * v) ≡ 0 [MOD p] := by
        simpa [pow_add] using hz.pow (1 + (11 * u).factorial * v)
      exact hz'.trans hz.symm
    · have hcop := (hp.coprime_iff_not_dvd.mpr hten).symm
      have htot : 10 ^ p.totient ≡ 1 [MOD p] :=
        (Nat.pow_totient_mod_eq_one hp.one_lt hcop).trans (Nat.mod_eq_of_lt hp.one_lt).symm
      obtain ⟨q, hq⟩ := Nat.dvd_factorial (Nat.totient_pos.mpr hp.pos)
        ((Nat.totient_le p).trans hpu)
      rw [hq, mul_assoc, pow_add, pow_mul, pow_one]
      simpa using (htot.pow (q * v)).mul_left 10
  refine composite_of_dvd hp.one_lt ?_
    ((((hpow.mul_left a).add_right b).dvd_iff (dvd_refl p)).mpr hpd)
  have hnv : v ≤ 1 + (11 * u).factorial * v := by
    have hfac : 1 ≤ (11 * u).factorial := Nat.factorial_pos _
    nlinarith
  have hl : 1 + (11 * u).factorial * v < 10 ^ (1 + (11 * u).factorial * v) :=
    Nat.lt_pow_self (by decide)
  have ham : 10 ^ (1 + (11 * u).factorial * v) ≤
      a * 10 ^ (1 + (11 * u).factorial * v) :=
    Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero ha₀)
  exact (hpu.trans_lt hv).trans_le ((hnv.trans hl.le).trans (ham.trans (Nat.le_add_right ..)))

private theorem pow_pos_ten (n : ℕ) : 0 < (10 : ℕ) ^ n := pow_pos (by decide) _

private theorem split_above {a b k j : ℕ} (hb : b < 10 ^ k) :
    (a * 10 ^ k + b) / 10 ^ (k + j) = a / 10 ^ j ∧
      (a * 10 ^ k + b) % 10 ^ (k + j) = (a % 10 ^ j) * 10 ^ k + b := by
  have hdiv : (a * 10 ^ k + b) / 10 ^ k = a := by
    rw [mul_comm a, Nat.mul_add_div (pow_pos_ten k), Nat.div_eq_of_lt hb, add_zero]
  have hq : (a * 10 ^ k + b) / 10 ^ (k + j) = a / 10 ^ j := by
    rw [pow_add, ← Nat.div_div_eq_div_mul, hdiv]
  refine ⟨hq, ?_⟩
  have hc := Nat.div_add_mod (a * 10 ^ k + b) (10 ^ (k + j))
  rw [hq] at hc
  have hd : a * 10 ^ k + b =
      10 ^ (k + j) * (a / 10 ^ j) + ((a % 10 ^ j) * 10 ^ k + b) := by
    rw [pow_add]
    calc
      _ = (10 ^ j * (a / 10 ^ j) + a % 10 ^ j) * 10 ^ k + b :=
        (congrArg (fun x => x * 10 ^ k + b) (Nat.div_add_mod a (10 ^ j))).symm
      _ = _ := by ring
  omega

private theorem split_below {a b k j : ℕ} (hj : j ≤ k) :
    (a * 10 ^ k + b) / 10 ^ j = a * 10 ^ (k - j) + b / 10 ^ j ∧
      (a * 10 ^ k + b) % 10 ^ j = b % 10 ^ j := by
  have hk : 10 ^ k = 10 ^ j * 10 ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  have hx : a * 10 ^ k + b = 10 ^ j * (a * 10 ^ (k - j)) + b := by
    rw [hk]
    ring
  rw [hx, Nat.mul_add_div (pow_pos_ten j), Nat.mul_add_mod]
  exact ⟨rfl, rfl⟩

private theorem edits_below {a b n i : ℕ} (hi : i ≤ n) (d : ℕ) :
    replaceDigit (a * 10 ^ (n + 1) + b) i d =
        a * 10 ^ (n + 1) + replaceDigit b i d ∧
    deleteDigit (a * 10 ^ (n + 1) + b) i =
        a * 10 ^ n + deleteDigit b i ∧
    insertDigit (a * 10 ^ (n + 1) + b) i d =
        a * 10 ^ (n + 2) + insertDigit b i d := by
  have h := split_below (a := a) (b := b) (k := n + 1) (j := i + 1) (by omega)
  have h' := split_below (a := a) (b := b) (k := n + 1) (j := i) (by omega)
  have e₁ : n + 1 - (i + 1) + (i + 1) = n + 1 := by omega
  have e₂ : n + 1 - (i + 1) + i = n := by omega
  have e₃ : n + 1 - i + (i + 1) = n + 2 := by omega
  constructor
  · unfold replaceDigit
    rw [h.1, h'.2]
    conv_rhs => rw [← e₁, pow_add]
    ring
  constructor
  · unfold deleteDigit
    rw [h.1, h'.2]
    conv_rhs => rw [← e₂, pow_add]
    ring
  · unfold insertDigit
    rw [h'.1, h'.2]
    conv_rhs => rw [← e₃, pow_add]
    ring

private theorem edits_above {a b k : ℕ} (hb : b < 10 ^ k) (j d : ℕ) :
    replaceDigit (a * 10 ^ k + b) (k + j) d =
        replaceDigit a j d * 10 ^ k + b ∧
    deleteDigit (a * 10 ^ k + b) (k + j) =
        deleteDigit a j * 10 ^ k + b ∧
    insertDigit (a * 10 ^ k + b) (k + j) d =
        insertDigit a j d * 10 ^ k + b := by
  have h := split_above (a := a) (j := j) hb
  have h' := split_above (a := a) (j := j + 1) hb
  constructor
  · unfold replaceDigit
    rw [Nat.add_assoc k j 1, h'.1, h.2, pow_add, pow_add]
    ring
  constructor
  · unfold deleteDigit
    rw [Nat.add_assoc k j 1, h'.1, h.2, pow_add]
    ring
  · unfold insertDigit
    rw [Nat.add_assoc k j 1, h.1, h.2, pow_add, pow_add]
    ring

private theorem edits_leading {a j : ℕ} (ha : a < 10 ^ j) (d : ℕ) :
    replaceDigit a j d = a + d * 10 ^ j ∧
    deleteDigit a j = a ∧
    insertDigit a j d = a + d * 10 ^ j := by
  have ha' : a < 10 ^ (j + 1) := ha.trans (Nat.pow_lt_pow_right (by decide) (by omega))
  simp [replaceDigit, deleteDigit, insertDigit, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt ha',
    Nat.mod_eq_of_lt ha, Nat.add_comm]


private theorem edit_bounds {x s i d : ℕ} (hx : x < 10 ^ s) (hi : i < s) (hd : d < 10) :
    replaceDigit x i d ≤ 20 * 10 ^ s ∧
      deleteDigit x i ≤ 20 * 10 ^ s ∧
      insertDigit x i d ≤ 20 * 10 ^ s := by
  have hdigit : d * 10 ^ i ≤ 9 * 10 ^ s :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) hi.le)
  have hhi := Nat.div_mul_le_self x (10 ^ (i + 1))
  have hrem := Nat.mod_le x (10 ^ i)
  have hdel : x / 10 ^ (i + 1) * 10 ^ i ≤ x :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))).trans hhi
  have hins : x / 10 ^ i * 10 ^ (i + 1) ≤ 10 * x := by
    rw [pow_succ', ← mul_assoc, mul_comm (x / 10 ^ i) 10, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self ..)
  unfold replaceDigit deleteDigit insertDigit
  omega

-- The fixed initial and terminal blocks can be arbitrary once the terminal block
-- supplies a proper divisor for each digit added at a zero position.
private theorem unbounded_of_cover {a b : ℕ} (ha : 0 < a) (hb : Nat.Coprime b 10)
    (hcover : ∀ i d, d < 10 → ∃ p, 1 < p ∧ p < b ∧ p ∣ a ∧ p ∣ b + d * 10 ^ i) :
    {N : ℕ | IsDigitallyRobustComposite N}.Infinite := by
  let s := (Nat.digits 10 b).length
  let t := (Nat.digits 10 a).length
  have hs : b < 10 ^ s := (Nat.digits_length_le_iff (by decide) b).mp le_rfl
  have ht : a < 10 ^ t := (Nat.digits_length_le_iff (by decide) a).mp le_rfl
  have hbpow {i : ℕ} (hi : s ≤ i) : b < 10 ^ i :=
    hs.trans_le (Nat.pow_le_pow_right (by decide) hi)
  have hapow {j : ℕ} (hj : t ≤ j) : a < 10 ^ j :=
    ht.trans_le (Nat.pow_le_pow_right (by decide) hj)
  let u := 20 * (10 ^ s + 10 ^ t)
  have hau : a ≤ u := by dsimp [u]; omega
  have hbu : b ≤ u := by dsimp [u]; omega
  have hcover' (k i d : ℕ) (hd : d < 10) : Composite (a * 10 ^ k + (b + d * 10 ^ i)) := by
    obtain ⟨p, hp, hpb, hpa, hpd⟩ := hcover i d hd
    exact composite_of_dvd hp (by omega) (dvd_add (dvd_mul_of_dvd_left hpa _) hpd)
  have hcompb : Composite b := by
    obtain ⟨p, hp, hpb, _, hd⟩ := hcover 0 0 (by decide)
    exact composite_of_dvd hp hpb (by simpa using hd)
  apply Set.infinite_of_forall_exists_gt
  intro bound
  let v := 1100 * u + bound + s + 1
  let n := 1 + (11 * (100 * u)).factorial * v
  have hvn : v ≤ n := by
    dsimp [n]
    have hfac : 1 ≤ (11 * (100 * u)).factorial := Nat.factorial_pos _
    nlinarith
  have hsn : s ≤ n := (show s ≤ v by dsimp [v]; omega).trans hvn
  have hbn : b < 10 ^ (n + 1) := hbpow (by omega)
  have hn : bound < a * 10 ^ (n + 1) + b := by
    have hh : bound ≤ n := (show bound ≤ v by dsimp [v]; omega).trans hvn
    have hp : n + 1 < 10 ^ (n + 1) := Nat.lt_pow_self (by decide)
    nlinarith
  have hprog {c e k : ℕ} (hc : c ≤ u) (he : e ≤ u) (hk : k ≤ 2)
      (hz : c = 0 → Composite e) : Composite (c * 10 ^ (n + k) + e) := by
    have hk' : 10 ^ k ≤ 100 := Nat.pow_le_pow_right (by decide) hk
    have h := composite_progression (a := c * 10 ^ k) (b := e) (u := 100 * u)
      ((Nat.mul_le_mul hc hk').trans_eq (mul_comm ..)) (by omega)
      (show 11 * (100 * u) < v by dsimp [v]; omega)
      (fun h => hz ((mul_eq_zero.mp h).resolve_right (pow_pos_ten k).ne'))
    rw [show c * 10 ^ (n + k) = c * 10 ^ k * 10 ^ n by rw [add_comm n, pow_add]; ring]
    exact h
  have hleading (j d : ℕ) (hd : d < 10) :
      Composite ((a + d * 10 ^ j) * 10 ^ (n + 1) + b) := by
    have heq : (a + d * 10 ^ j) * 10 ^ (n + 1) + b =
        a * 10 ^ (n + 1) + (b + d * 10 ^ (n + 1 + j)) := by
      rw [pow_add (10 : ℕ) (n + 1) j]
      ring
    rw [heq]
    exact hcover' (n + 1) (n + 1 + j) d hd
  have hdlen : (Nat.digits 10 (a * 10 ^ (n + 1) + b)).length ≤ n + 1 + t := by
    apply (Nat.digits_length_le_iff (by decide) _).mpr
    calc
      a * 10 ^ (n + 1) + b < (a + 1) * 10 ^ (n + 1) := by
        rw [add_mul, one_mul]
        omega
      _ ≤ _ := by
        calc
          _ ≤ 10 ^ t * 10 ^ (n + 1) := Nat.mul_le_mul_right _ ht
          _ = 10 ^ (n + 1 + t) := by
            rw [add_comm (n + 1)]
            exact (pow_add ..).symm
  refine ⟨a * 10 ^ (n + 1) + b, ?_, hn⟩
  have hcomposite : Composite (a * 10 ^ (n + 1) + b) := by
    simpa using hcover' (n + 1) 0 0 (by decide)
  refine ⟨hcomposite, ?_, ?_, ?_, ?_⟩
  · have hh : a * 10 ^ (n + 1) + b ≡ b [MOD 10] := by
      have hten : 10 ∣ a * 10 ^ (n + 1) := by
        rw [pow_succ, ← mul_assoc]
        exact dvd_mul_left ..
      simpa using (Nat.modEq_zero_iff_dvd.mpr hten).add_right b
    change Nat.gcd _ _ = 1
    calc
      Nat.gcd _ 10 = Nat.gcd ((a * 10 ^ (n + 1) + b) % 10) 10 :=
        (Nat.gcd_comm _ _).trans (Nat.gcd_rec 10 _)
      _ = Nat.gcd (b % 10) 10 := congrArg (fun x => Nat.gcd x 10) hh
      _ = 1 := (Nat.gcd_rec 10 b).symm.trans ((Nat.gcd_comm _ _).trans hb)
  · intro i d hd _
    by_cases hi : i ≤ n
    · rw [(edits_below hi d).1]
      by_cases his : i < s
      · exact hprog hau ((edit_bounds hs his hd).1.trans (by dsimp [u]; omega))
          (by decide) (fun h => (ha.ne' h).elim)
      · have h0 := edits_leading (hbpow (le_of_not_gt his)) d
        rw [h0.1]
        exact hcover' (n + 1) i d hd
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show n + 1 ≤ i by omega)
      rw [(edits_above hbn j d).1]
      by_cases hj : j < t
      · exact hprog ((edit_bounds ht hj hd).1.trans (by dsimp [u]; omega)) hbu (by decide)
          (fun _ => hcompb)
      · have h0 := edits_leading (hapow (le_of_not_gt hj)) d
        rw [h0.1]
        exact hleading j d hd
  · intro i hi'
    by_cases hi : i ≤ n
    · rw [(edits_below hi 0).2.1]
      by_cases his : i < s
      · exact hprog (k := 0) hau ((edit_bounds hs his (by decide : 0 < 10)).2.1.trans
          (by dsimp [u]; omega)) (by decide : 0 ≤ 2) (fun h => (ha.ne' h).elim)
      · have h0 := edits_leading (hbpow (le_of_not_gt his)) 0
        rw [h0.2.1]
        simpa only [Composite, zero_mul, add_zero] using hcover' n 0 0 (by decide)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show n + 1 ≤ i by omega)
      rw [(edits_above hbn j 0).2.1]
      have hj : j < t := by omega
      exact hprog ((edit_bounds ht hj (by decide : 0 < 10)).2.1.trans
        (by dsimp [u]; omega)) hbu (by decide) (fun _ => hcompb)
  · intro i d hd
    by_cases hi : i ≤ n
    · rw [(edits_below hi d).2.2]
      by_cases his : i < s
      · exact hprog hau ((edit_bounds hs his hd).2.2.trans (by dsimp [u]; omega))
          (by decide) (fun h => (ha.ne' h).elim)
      · have h0 := edits_leading (hbpow (le_of_not_gt his)) d
        rw [h0.2.2]
        exact hcover' (n + 2) i d hd
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show n + 1 ≤ i by omega)
      rw [(edits_above hbn j d).2.2]
      by_cases hj : j < t
      · exact hprog ((edit_bounds ht hj hd).2.2.trans (by dsimp [u]; omega)) hbu (by decide)
          (fun _ => hcompb)
      · have h0 := edits_leading (hapow (le_of_not_gt hj)) d
        rw [h0.2.2]
        exact hleading j d hd

-- Each region refines i = offset + period * k using residue classes for k.
private structure DivisorClass where
  offset : ℕ
  period : ℕ
  divisor : ℕ

private structure Region where
  offset : ℕ
  period : ℕ
  classes : List DivisorClass

private structure DigitCover where
  digit : ℕ
  regions : List Region

private def single (offset period divisor : ℕ) : Region :=
  ⟨offset, period, [⟨0, 1, divisor⟩]⟩

-- A quotient of products of 10^k - 1 gives a compact representation of
-- the larger divisors in the certificate. The checks use the resulting integers.
private def factorQuotient (numerator denominator : List ℕ) (factor : ℕ) : ℕ :=
  (numerator.map fun k => 10 ^ k - 1).prod /
    ((denominator.map fun k => 10 ^ k - 1).prod * factor)

private def covers {α : Type} (offset period : α → ℕ) (xs : List α) : Bool :=
  let modulus := (xs.map period).foldl Nat.lcm 1
  decide (0 < modulus) && xs.all (fun x => decide (period x ∣ modulus)) &&
    (List.range modulus).all (fun i => xs.any fun x => i % period x == offset x)

private theorem find_class {α : Type} {offset period : α → ℕ} {xs : List α}
    (h : covers offset period xs = true) (i : ℕ) : ∃ x ∈ xs, i % period x = offset x := by
  let m := (xs.map period).foldl Nat.lcm 1
  simp only [covers, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨x, hx, hclass⟩ := h.2 (i % m) (Nat.mod_lt _ h.1.1)
  have hmod := ((Nat.mod_modEq i m).of_dvd (h.1.2 x hx)).symm
  exact ⟨x, hx, (show i % period x = i % m % period x from hmod).trans hclass⟩

private def regionValid (region : Region) : Bool :=
  covers DivisorClass.offset DivisorClass.period region.classes &&
    region.classes.all (fun cls => decide (1 < cls.divisor) &&
      (10 ^ (region.period * cls.period)) % cls.divisor == 1)

private def digitValid (cover : DigitCover) : Bool :=
  covers Region.offset Region.period cover.regions && cover.regions.all regionValid

private def residue (d : ℕ) (region : Region) (cls : DivisorClass) : ℕ :=
  cls.divisor - (d * 10 ^ (region.offset + region.period * cls.offset)) % cls.divisor

private def reservations (data : List DigitCover) : List (ℕ × ℕ) :=
  ((10, 1) :: (3, 0) :: (7, 0) :: (data.flatMap fun cover =>
    cover.regions.flatMap fun region =>
      region.classes.map fun cls => (cls.divisor, residue cover.digit region cls))).eraseDups

private theorem reservation_mem {data : List DigitCover} {cover : DigitCover} {region : Region}
    {cls : DivisorClass} (hc : cover ∈ data) (hr : region ∈ cover.regions)
    (hl : cls ∈ region.classes) :
    (cls.divisor, residue cover.digit region cls) ∈ reservations data := by
  apply List.mem_eraseDups.mpr
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨cover, hc, List.mem_flatMap.mpr ⟨region, hr, List.mem_map_of_mem hl⟩⟩)))

private theorem covered_dvd {b i : ℕ} {cover : DigitCover} (h : digitValid cover = true)
    (hb : ∀ region ∈ cover.regions, ∀ cls ∈ region.classes,
      b ≡ residue cover.digit region cls [MOD cls.divisor]) :
    ∃ region ∈ cover.regions, ∃ cls ∈ region.classes,
      1 < cls.divisor ∧ cls.divisor ∣ b + cover.digit * 10 ^ i := by
  obtain ⟨hcover, hregions⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨region, hregion, hi⟩ := find_class hcover i
  obtain ⟨hrefined, hdivisors⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hregions _ hregion)
  obtain ⟨cls, hcls, hq⟩ := find_class hrefined (i / region.period)
  have hv := List.all_eq_true.mp hdivisors _ hcls
  have hp : 1 < cls.divisor := of_decide_eq_true (Bool.and_eq_true_iff.mp hv).1
  have hpow : 10 ^ (region.period * cls.period) ≡ 1 [MOD cls.divisor] :=
    (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hv).2).trans (Nat.mod_eq_of_lt hp).symm
  have hexp : i = (region.offset + region.period * cls.offset) +
      (region.period * cls.period) * (i / region.period / cls.period) := by
    calc
      i = region.offset + region.period * (i / region.period) := by
        rw [← hi]
        exact (Nat.mod_add_div ..).symm
      _ = _ := by
        conv_lhs => rw [← Nat.mod_add_div (i / region.period) cls.period, hq]
        ring
  have hc : 10 ^ i ≡ 10 ^ (region.offset + region.period * cls.offset) [MOD cls.divisor] := by
    conv_lhs => rw [hexp, pow_add, pow_mul]
    simpa using (hpow.pow (i / region.period / cls.period)).mul_left
      (10 ^ (region.offset + region.period * cls.offset))
  refine ⟨region, hregion, cls, hcls, hp, Nat.modEq_zero_iff_dvd.mp ?_⟩
  apply ((hb region hregion cls hcls).add (hc.mul_left cover.digit)).trans
  let x := cover.digit * 10 ^ (region.offset + region.period * cls.offset)
  unfold residue
  have hsum : cls.divisor - x % cls.divisor + x % cls.divisor = cls.divisor :=
    Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt _ (by omega)))
  have h := (Nat.mod_modEq x cls.divisor).symm.add_left (cls.divisor - x % cls.divisor)
  exact h.trans (show cls.divisor - x % cls.divisor + x % cls.divisor ≡ 0 [MOD cls.divisor] by
    rw [hsum]
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl _))

private theorem cover_witness {data : List DigitCover}
    (hc : data.all digitValid = true)
    (hds : ∀ d < 10, ¬3 ∣ d → d ≠ 7 → ∃ c ∈ data, c.digit = d)
    (hpair : (reservations data).Pairwise (fun x y => x.1.Coprime y.1))
    (hpos : (reservations data).all (fun x => decide (0 < x.1)) = true) :
    ∃ a b : ℕ, 0 < a ∧ Nat.Coprime b 10 ∧
      ∀ i d, d < 10 → ∃ p, 1 < p ∧ p < b ∧ p ∣ a ∧ p ∣ b + d * 10 ^ i := by
  obtain ⟨r, hr⟩ := Nat.chineseRemainderOfList Prod.snd Prod.fst (reservations data) hpair
  let a := ((reservations data).map Prod.fst).prod
  let b := r + 2 * a
  have ha : 0 < a := List.prod_pos_iff_forall_pos_nat.mpr (by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact of_decide_eq_true (List.all_eq_true.mp hpos _ hx))
  have hdiv {x : ℕ × ℕ} (hx : x ∈ reservations data) : x.1 ∣ a :=
    List.dvd_prod (List.mem_map_of_mem hx)
  have hbound {x : ℕ × ℕ} (hx : x ∈ reservations data) : x.1 < b := by
    have := Nat.le_of_dvd ha (hdiv hx)
    dsimp [b]
    omega
  have hmod {x : ℕ × ℕ} (hx : x ∈ reservations data) : b ≡ x.2 [MOD x.1] := by
    have hz := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right (hdiv hx) 2)
    simpa [b] using (hr x hx).add hz
  have h10 : (10, 1) ∈ reservations data := List.mem_eraseDups.mpr List.mem_cons_self
  have h3 : (3, 0) ∈ reservations data :=
    List.mem_eraseDups.mpr (List.mem_cons_of_mem _ List.mem_cons_self)
  have h7 : (7, 0) ∈ reservations data :=
    List.mem_eraseDups.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hcop : Nat.Coprime b 10 := Nat.coprime_of_mul_modEq_one 1 (by simpa using hmod h10)
  refine ⟨a, b, ha, hcop, fun i d hd => ?_⟩
  by_cases hd3 : 3 ∣ d
  · exact ⟨3, by decide, hbound h3, hdiv h3,
      dvd_add (Nat.modEq_zero_iff_dvd.mp (hmod h3)) (dvd_mul_of_dvd_left hd3 _)⟩
  by_cases hd7 : d = 7
  · subst d
    exact ⟨7, by decide, hbound h7, hdiv h7,
      dvd_add (Nat.modEq_zero_iff_dvd.mp (hmod h7)) (dvd_mul_right ..)⟩
  obtain ⟨c, hcmem, rfl⟩ := hds d hd hd3 hd7
  obtain ⟨region, hregion, cls, hcls, hp, hpd⟩ :=
    covered_dvd (i := i) (List.all_eq_true.mp hc _ hcmem)
      (fun region hr cls hl => hmod (reservation_mem hcmem hr hl))
  exact ⟨cls.divisor, hp, hbound (reservation_mem hcmem hregion hcls),
    hdiv (reservation_mem hcmem hregion hcls), hpd⟩

-- The digit 7 uses divisor 7, and digits 0, 3, 6 and 9 use divisor 3.
-- The other digits have the following refinements of small residue classes.
private def coverData : List DigitCover := [
  ⟨1, [
    single 0 2 11,
    ⟨1, 2, [
      ⟨0, 2, 101⟩,
      ⟨1, 4, 137⟩,
      ⟨7, 8, 17⟩,
      ⟨3, 16, 1409⟩,
      ⟨11, 32, 19841⟩,
      ⟨59, 64, (factorQuotient [128] [64] 1265011073)⟩,
      ⟨27, 192, 12289⟩,
      ⟨91, 192, 3457⟩,
      ⟨155, 192, (factorQuotient [384, 64] [192, 128] 17788762509376897)⟩
    ]⟩
  ]⟩,
  ⟨2, [
    ⟨0, 2, [
      ⟨2, 3, 13⟩,
      ⟨4, 6, 9901⟩,
      ⟨6, 9, 52579⟩,
      ⟨1, 12, 99990001⟩,
      ⟨9, 18, 999999000001⟩,
      ⟨12, 27, 14175966169⟩,
      ⟨21, 27, 70541929⟩,
      ⟨19, 36, 98641⟩,
      ⟨31, 36, 3199044596370769⟩,
      ⟨0, 54, (factorQuotient [108, 18] [54, 36] 16728121)⟩,
      ⟨18, 54, 153469⟩,
      ⟨36, 54, 109⟩,
      ⟨43, 72, 8929⟩,
      ⟨3, 81, 1459⟩,
      ⟨57, 81, (factorQuotient [162, 27] [81, 54] 1459)⟩,
      ⟨7, 144, 1067329⟩,
      ⟨30, 162, (factorQuotient [324, 54] [162, 108] 2925721)⟩,
      ⟨111, 162, 2925721⟩,
      ⟨79, 288, (factorQuotient [576, 96] [288, 192] 577)⟩,
      ⟨223, 288, 577⟩
    ]⟩,
    ⟨1, 2, [
      ⟨0, 4, 73⟩,
      ⟨2, 8, 17⟩,
      ⟨3, 8, 5882353⟩,
      ⟨5, 16, 449⟩,
      ⟨7, 16, 353⟩,
      ⟨15, 16, 69857⟩,
      ⟨9, 24, 9999999900000001⟩,
      ⟨13, 32, 834427406578561⟩,
      ⟨14, 32, 976193⟩,
      ⟨29, 32, 6187457⟩,
      ⟨22, 48, (factorQuotient [96, 16] [48, 32] 20002273)⟩,
      ⟨25, 48, 97⟩,
      ⟨38, 48, 206209⟩,
      ⟨65, 72, (factorQuotient [144, 24] [72, 48] 8929)⟩,
      ⟨1, 96, 769⟩,
      ⟨49, 96, 193⟩,
      ⟨54, 96, (factorQuotient [192, 32] [96, 64] 148417)⟩,
      ⟨30, 128, 453377⟩,
      ⟨62, 128, 15361⟩,
      ⟨94, 128, 257⟩,
      ⟨126, 128, (factorQuotient [256] [128] 1789831292929)⟩,
      ⟨17, 144, 13249⟩,
      ⟨89, 144, (factorQuotient [288, 48] [144, 96] 14141041921)⟩,
      ⟨6, 192, 418725889⟩,
      ⟨41, 216, 433⟩,
      ⟨185, 216, (factorQuotient [432, 72] [216, 144] 433)⟩,
      ⟨102, 384, 859393⟩,
      ⟨294, 384, (factorQuotient [768, 128] [384, 256] 373568683777)⟩,
      ⟨113, 432, (factorQuotient [864, 144] [432, 288] 196482241)⟩,
      ⟨329, 432, 196482241⟩
    ]⟩
  ]⟩,
  ⟨4, [
    single 0 7 4649,
    ⟨1, 7, [
      ⟨2, 5, 102598800232111471⟩,
      ⟨4, 5, 71⟩,
      ⟨3, 10, 265212793249617641⟩,
      ⟨8, 10, 4147571⟩,
      ⟨1, 15, (factorQuotient [105, 7, 5, 3] [35, 21, 15, 1] 1)⟩,
      ⟨0, 20, 13489841⟩,
      ⟨10, 20, 3471301⟩,
      ⟨15, 20, 421⟩,
      ⟨11, 30, (factorQuotient [210, 35, 21, 15, 14, 10, 6, 1] [105, 70, 42, 30, 7, 5, 3, 2] 1)⟩,
      ⟨5, 40, (factorQuotient [280, 28, 20, 8] [140, 56, 40, 4] 851761)⟩,
      ⟨6, 45, (factorQuotient [315, 21, 15, 9] [105, 63, 45, 3] 631)⟩,
      ⟨21, 45, 631⟩,
      ⟨26, 60,
        (factorQuotient [420, 70, 42, 30, 28, 20, 12, 2] [210, 140, 84, 60, 14, 10, 6, 4] 1)⟩,
      ⟨25, 80, 1378721⟩,
      ⟨65, 80, (factorQuotient [560, 56, 40, 16] [280, 112, 80, 8] 1378721)⟩,
      ⟨36, 90,
        (factorQuotient [630, 105, 63, 45, 42, 30, 18, 3]
          [315, 210, 126, 90, 21, 15, 9, 6] 330354361)⟩,
      ⟨81, 90, 2521⟩,
      ⟨56, 120,
        (factorQuotient [840, 140, 84, 60, 56, 40, 24, 4]
          [420, 280, 168, 120, 28, 20, 12, 8] 77387397049201)⟩,
      ⟨116, 120, 134401⟩
    ]⟩,
    ⟨2, 7, [
      ⟨1, 3, 43⟩,
      ⟨2, 3, 10838689⟩,
      ⟨0, 6, 459691⟩,
      ⟨3, 18, 5274739⟩,
      ⟨9, 18, (factorQuotient [126, 21, 9, 6] [63, 42, 18, 3] 5274739)⟩,
      ⟨15, 36, 1009⟩,
      ⟨33, 36, (factorQuotient [252, 42, 18, 12] [126, 84, 36, 6] 1009)⟩
    ]⟩,
    ⟨3, 7, [
      ⟨2, 3, 1933⟩,
      ⟨1, 6, 127⟩,
      ⟨4, 6, 2689⟩,
      ⟨0, 9, 10837⟩,
      ⟨3, 9, 1921436048294281⟩,
      ⟨6, 9, 45613⟩
    ]⟩,
    ⟨4, 7, [
      ⟨1, 4, 121499449⟩,
      ⟨2, 4, 281⟩,
      ⟨3, 4, 29⟩,
      ⟨0, 12, 226549⟩,
      ⟨8, 12, 4458192223320340849⟩,
      ⟨16, 24, (factorQuotient [168, 28, 12, 8] [84, 56, 24, 4] 1)⟩,
      ⟨4, 48, (factorQuotient [336, 56, 24, 16] [168, 112, 48, 8] 337)⟩,
      ⟨28, 48, 337⟩
    ]⟩,
    ⟨5, 7, [
      ⟨0, 2, 909091⟩,
      ⟨1, 8, 127522001020150503761⟩,
      ⟨3, 8, 7841⟩,
      ⟨13, 16, (factorQuotient [112, 8] [56, 16] 113)⟩,
      ⟨15, 16, 113⟩,
      ⟨7, 32, (factorQuotient [224, 16] [112, 32] 673)⟩,
      ⟨21, 32, 673⟩,
      ⟨23, 64, (factorQuotient [448, 32] [224, 64] 1)⟩,
      ⟨5, 96, (factorQuotient [672, 112, 48, 32] [336, 224, 96, 16] 13664586842593)⟩,
      ⟨37, 96, 1454209⟩,
      ⟨69, 96, 9396577⟩,
      ⟨55, 128, 105528193⟩,
      ⟨119, 128, (factorQuotient [896, 64] [448, 128] 105528193)⟩
    ]⟩,
    single 6 7 239
  ]⟩,
  ⟨5, [
    ⟨0, 3, [
      ⟨1, 5, 31⟩,
      ⟨2, 5, 41⟩,
      ⟨4, 5, 2906161⟩,
      ⟨3, 10, 2161⟩,
      ⟨8, 10, 211⟩,
      ⟨0, 15, 238681⟩,
      ⟨5, 15, 4185502830133110721⟩,
      ⟨10, 45, 16357951⟩,
      ⟨25, 45, (factorQuotient [135, 9] [45, 27] 25797650141521)⟩,
      ⟨85, 135, 40435201⟩,
      ⟨130, 135, 61561⟩,
      ⟨40, 270, 811⟩,
      ⟨175, 270, (factorQuotient [810, 135, 81, 54] [405, 270, 162, 27] 811)⟩
    ]⟩,
    single 1 3 37,
    ⟨2, 3, [
      ⟨0, 3, 333667⟩,
      ⟨2, 6, 13⟩,
      ⟨5, 6, 19⟩,
      ⟨4, 9, 440334654777631⟩,
      ⟨7, 9, 757⟩,
      ⟨1, 27, 163⟩,
      ⟨10, 27, 2462401⟩,
      ⟨19, 27, 9397⟩
    ]⟩
  ]⟩,
  ⟨8, [
    ⟨0, 5, [
      ⟨0, 2, 9091⟩,
      ⟨7, 8, 5964848081⟩,
      ⟨1, 12, 39526741⟩,
      ⟨5, 12, 4188901⟩,
      ⟨3, 16, (factorQuotient [80, 8] [40, 16] 5070721)⟩,
      ⟨11, 32, 1634881⟩,
      ⟨27, 32, (factorQuotient [160, 16] [80, 32] 30169703237441)⟩,
      ⟨9, 60, (factorQuotient [300, 50, 30, 20] [150, 100, 60, 10] 613076034355801)⟩,
      ⟨33, 60, 261301⟩,
      ⟨45, 60, 601⟩,
      ⟨57, 60, 3903901⟩,
      ⟨21, 120, 32401⟩,
      ⟨81, 120, (factorQuotient [600, 100, 60, 40] [300, 200, 120, 20] 32401)⟩
    ]⟩,
    ⟨1, 5, [
      ⟨1, 4, 27961⟩,
      ⟨3, 4, 3541⟩,
      ⟨4, 8, 1676321⟩,
      ⟨6, 12, 61⟩,
      ⟨10, 24, (factorQuotient [120, 20, 12, 8] [60, 40, 24, 4] 1)⟩,
      ⟨2, 36, 181⟩,
      ⟨26, 36, (factorQuotient [180, 30, 18, 12] [90, 60, 36, 6] 181)⟩,
      ⟨0, 40, (factorQuotient [200, 20] [100, 40] 771043201)⟩,
      ⟨8, 40, 401⟩,
      ⟨16, 40, 1601⟩,
      ⟨32, 40, 1201⟩,
      ⟨22, 48, (factorQuotient [240, 40, 24, 16] [120, 80, 48, 8] 1)⟩,
      ⟨14, 72, (factorQuotient [360, 60, 36, 24] [180, 120, 72, 12] 265183201)⟩,
      ⟨50, 72, 265183201⟩,
      ⟨64, 80, (factorQuotient [400, 40] [200, 80] 1)⟩,
      ⟨46, 96, 177601⟩,
      ⟨94, 96, (factorQuotient [480, 80, 48, 32] [240, 160, 96, 16] 177601)⟩,
      ⟨24, 160, (factorQuotient [800, 80] [400, 160] 203425974788801)⟩,
      ⟨104, 160, 43201⟩
    ]⟩,
    single 2 5 271,
    ⟨3, 5, [
      ⟨1, 5, 182521213001⟩,
      ⟨2, 5, 25601⟩,
      ⟨4, 5, 21401⟩,
      ⟨3, 10, 251⟩,
      ⟨5, 10, 78875943472201⟩,
      ⟨8, 10, 5051⟩,
      ⟨0, 20, (factorQuotient [100, 10] [50, 20] 421897059901)⟩,
      ⟨10, 20, 7019801⟩
    ]⟩,
    single 4 5 41
  ]⟩
]

set_option maxRecDepth 30000 in
private theorem cover_valid : coverData.all digitValid = true := by decide +kernel

set_option maxRecDepth 30000 in
private theorem reservations_pairwise :
    (reservations coverData).Pairwise (fun x y => x.1.Coprime y.1) := by decide +kernel

set_option maxRecDepth 30000 in
private theorem reservations_positive :
    (reservations coverData).all (fun x => decide (0 < x.1)) = true := by decide +kernel

private theorem certified_cover :
    ∃ a b : ℕ, 0 < a ∧ Nat.Coprime b 10 ∧
      ∀ i d, d < 10 → ∃ p, 1 < p ∧ p < b ∧ p ∣ a ∧ p ∣ b + d * 10 ^ i := by
  apply cover_witness cover_valid _ reservations_pairwise reservations_positive
  intro d hd hd3 hd7
  have hmem : d ∈ ([1, 2, 4, 5, 8] : List ℕ) := by
    interval_cases d <;> first | contradiction | decide
  have hcheck : ([1, 2, 4, 5, 8] : List ℕ).all
      (fun i => coverData.any (fun cover => cover.digit == i)) = true := by decide +kernel
  simpa only [List.any_eq_true, beq_iff_eq] using List.all_eq_true.mp hcheck _ hmem

end MetaMathlibExt.infinitelyMany_digitallyRobustComposites

namespace MetaMathlibExt

/--
**Infinitely many digitally robust composites.** There are infinitely many natural numbers that
are digitally robust composites: composite numbers coprime to $10$ that stay composite after
replacing any one base-ten digit (including a leading zero) by a different digit, after deleting
any one of their digits, and after inserting any digit in any position.

Source: Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When
Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
-/
public theorem infinitelyMany_digitallyRobustComposites :
    {N : ℕ | IsDigitallyRobustComposite N}.Infinite := by
  obtain ⟨a, b, ha, hb, hcover⟩ :=
    infinitelyMany_digitallyRobustComposites.certified_cover
  exact infinitelyMany_digitallyRobustComposites.unbounded_of_cover ha hb hcover

end MetaMathlibExt
