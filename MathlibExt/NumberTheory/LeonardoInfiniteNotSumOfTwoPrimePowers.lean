/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GenLeonardo
public import MathlibExt.NumberTheory.ThirdOrderPrimePowers
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq

/-!
# Infinitely many Leonardo numbers are not sums of two prime powers

On the progression from Table 7, a covering of the exponent of $2$ forces the other prime
in a putative decomposition to be one of $3, 5, 7, 13, 19, 37, 73$. We replace the source's
S-unit argument with finite congruence obstructions modulo $91$, $51$, and $3$.

## References

* Daniel Baczkowski and Bruce Keener, *Third-Order Recurrence Sequences with Infinitely Many
  Terms not Equal to the Sum of Two Prime Powers*, Journal of Integer Sequences 29 (2026),
  Article 26.2.3, pp. 1–11. The covering argument is from Section 2, Theorem 1 (pp. 2–3),
  and the progression and prime residues are from Section 7, Theorem 6 and Table 7 (pp. 8–9).
-/

namespace MetaMathlibExt

namespace leonardo_infinite_not_isSumOfTwoPrimePowers

private abbrev firstIndex : ℕ := 539073

private abbrev progressionStep : ℕ := 3543120

/-- One step of the affine Leonardo recurrence modulo `m`. -/
private def stepOf (m : ℤ) (s : ℤ × ℤ) : ℤ × ℤ :=
  (s.2, (s.2 + s.1 + 1) % m)

/-- Consecutive Leonardo terms, computed with reduction at each step. -/
private def pairs (m : ℤ) (n : ℕ) : ℤ × ℤ :=
  (stepOf m)^[n] (1 % m, 1 % m)

private theorem pairs_eq (m : ℤ) (n : ℕ) :
    pairs m n = (genLeonardo 1 n % m, genLeonardo 1 (n + 1) % m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs : pairs m (n + 1) = stepOf m (pairs m n) := Function.iterate_succ_apply' _ _ _
    rw [hs, ih]
    change (_, (genLeonardo 1 (n + 1) % m + genLeonardo 1 n % m + 1) % m) = _
    rw [genLeonardo.eq_3]
    congr 1
    exact ((Int.mod_modEq _ _).add (Int.mod_modEq _ _)).add_right 1

private theorem pairs_add_period {m : ℤ} {P : ℕ} (hP : pairs m P = pairs m 0) (n : ℕ) :
    pairs m (n + P) = pairs m n := by
  unfold pairs at *
  rw [Function.iterate_add_apply, hP]
  rfl

private theorem pairs_add_mul_period {m : ℤ} {P : ℕ} (hP : pairs m P = pairs m 0) (n q : ℕ) :
    pairs m (n + P * q) = pairs m n := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, pairs_add_period hP, ih]

private theorem pairs_mod {m : ℤ} {P : ℕ} (hP : pairs m P = pairs m 0) (n : ℕ) :
    pairs m n = pairs m (n % P) := by
  calc
    pairs m n = pairs m (n % P + P * (n / P)) := congrArg (pairs m) (Nat.mod_add_div n P).symm
    _ = pairs m (n % P) := pairs_add_mul_period hP _ _

/-- Read off the Leonardo residue by reducing the index before evaluating the recurrence. -/
private theorem progression_modEq (t : ℕ) (m : ℤ) (P : ℕ) (v : ℤ)
    (hP : pairs m P = pairs m 0) (hdiv : P ∣ progressionStep)
    (hv : (pairs m (firstIndex % P)).1 = v % m) :
    genLeonardo 1 (firstIndex + progressionStep * t) ≡ v [ZMOD m] := by
  obtain ⟨c, hc⟩ := hdiv
  have hindex : (firstIndex + progressionStep * t) % P = firstIndex % P := by
    rw [hc, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  change genLeonardo 1 (firstIndex + progressionStep * t) % m = v % m
  calc
    _ = (pairs m (firstIndex + progressionStep * t)).1 :=
      (congrArg Prod.fst (pairs_eq m _)).symm
    _ = (pairs m (firstIndex % P)).1 := by rw [pairs_mod hP, hindex]
    _ = v % m := hv

/-- The classes in Table 7 cover every residue modulo 36. -/
private theorem covering (a : ℕ) :
    (a ≡ 0 [MOD 2]) ∨ (a ≡ 3 [MOD 4]) ∨ (a ≡ 0 [MOD 3]) ∨ (a ≡ 5 [MOD 12]) ∨
      (a ≡ 7 [MOD 18]) ∨ (a ≡ 13 [MOD 36]) ∨ (a ≡ 1 [MOD 9]) := by
  have h : ∀ r : Fin 36,
      ((r : ℕ) ≡ 0 [MOD 2]) ∨ ((r : ℕ) ≡ 3 [MOD 4]) ∨ ((r : ℕ) ≡ 0 [MOD 3]) ∨
        ((r : ℕ) ≡ 5 [MOD 12]) ∨ ((r : ℕ) ≡ 7 [MOD 18]) ∨ ((r : ℕ) ≡ 13 [MOD 36]) ∨
        ((r : ℕ) ≡ 1 [MOD 9]) := by decide
  simpa only [Nat.ModEq, Fin.val_mk, Nat.mod_mod,
    Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 36), Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 36),
    Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 36), Nat.mod_mod_of_dvd _ (by decide : 12 ∣ 36),
    Nat.mod_mod_of_dvd _ (by decide : 18 ∣ 36), Nat.mod_mod_of_dvd _ (by decide : 9 ∣ 36)]
    using h ⟨a % 36, Nat.mod_lt _ (by decide)⟩

private theorem pow_mod_period {x m : ℤ} {P : ℕ} (h : x ^ P ≡ 1 [ZMOD m]) (a : ℕ) :
    x ^ a ≡ x ^ (a % P) [ZMOD m] := by
  conv_lhs => rw [← Nat.div_add_mod a P, pow_add, pow_mul]
  simpa only [one_pow, one_mul] using (h.pow (a / P)).mul_right (x ^ (a % P))

/-- In a covering row the odd prime divides the other summand. This rules out the summand `1`
(from exponent zero) and otherwise identifies its prime base. -/
private theorem prime_of_cover {n : ℤ} {q p a b r P : ℕ} (hq : q.Prime) (hp : p.Prime)
    (he : n = 2 ^ a + (q : ℤ) ^ b) (hn : n ≡ 2 ^ r [ZMOD (p : ℤ)])
    (hcycle : (2 : ℤ) ^ P ≡ 1 [ZMOD (p : ℤ)]) (ha : a ≡ r [MOD P]) : q = p := by
  have hpow : (2 : ℤ) ^ a ≡ 2 ^ r [ZMOD (p : ℤ)] := by
    exact (pow_mod_period hcycle a).trans (ha ▸ (pow_mod_period hcycle r).symm)
  have hz : (2 : ℤ) ^ a + (q : ℤ) ^ b ≡ 2 ^ a + 0 [ZMOD (p : ℤ)] := by
    simpa only [add_zero, he] using hn.trans hpow.symm
  have hd : p ∣ q ^ b := by
    exact_mod_cast Int.modEq_zero_iff_dvd.mp (Int.ModEq.add_left_cancel' _ hz)
  by_cases hb : b = 0
  · exact (hp.ne_one (Nat.dvd_one.mp (by simpa [hb] using hd))).elim
  · exact (Nat.prime_eq_prime_of_dvd_pow hp hq hd).symm

private theorem restrict_prime {n : ℤ}
    (h3 : n ≡ 1 [ZMOD 3]) (h5 : n ≡ 3 [ZMOD 5]) (h7 : n ≡ 1 [ZMOD 7])
    (h13 : n ≡ 6 [ZMOD 13]) (h19 : n ≡ 14 [ZMOD 19]) (h37 : n ≡ 15 [ZMOD 37])
    (h73 : n ≡ 2 [ZMOD 73]) {q a b : ℕ} (hq : q.Prime) (he : n = 2 ^ a + (q : ℤ) ^ b) :
    q = 3 ∨ (q = 5 ∧ a ≡ 3 [MOD 4]) ∨ q ≡ 1 [MOD 3] := by
  have row {p r P : ℕ} (hp : p.Prime) (hn : n ≡ 2 ^ r [ZMOD (p : ℤ)])
      (hcycle : (2 : ℤ) ^ P ≡ 1 [ZMOD (p : ℤ)]) (ha : a ≡ r [MOD P]) : q = p :=
    prime_of_cover hq hp he hn hcycle ha
  rcases covering a with ha | ha | ha | ha | ha | ha | ha
  · exact Or.inl (row (p := 3) (by decide) h3 (by decide) ha)
  · exact Or.inr (Or.inl ⟨row (p := 5) (by decide) (h5.trans (by decide)) (by decide) ha, ha⟩)
  · refine Or.inr (Or.inr ?_)
    rw [row (p := 7) (by decide) h7 (by decide) ha]
    decide
  · refine Or.inr (Or.inr ?_)
    rw [row (p := 13) (by decide) (h13.trans (by decide)) (by decide) ha]
    decide
  · refine Or.inr (Or.inr ?_)
    rw [row (p := 19) (by decide) (h19.trans (by decide)) (by decide) ha]
    decide
  · refine Or.inr (Or.inr ?_)
    rw [row (p := 37) (by decide) (h37.trans (by decide)) (by decide) ha]
    decide
  · refine Or.inr (Or.inr ?_)
    rw [row (p := 73) (by decide) h73 (by decide) ha]
    decide

private theorem exclude_three {n : ℤ} {a b : ℕ} (hn : n ≡ 71 [ZMOD 91])
    (h : n = 2 ^ a + 3 ^ b) : False := by
  have hcheck : ∀ i : Fin 12, ∀ j : Fin 6,
      ¬ (71 : ℤ) ≡ 2 ^ (i : ℕ) + 3 ^ (j : ℕ) [ZMOD 91] := by decide
  have ha := pow_mod_period (by decide : (2 : ℤ) ^ (12 : ℕ) ≡ 1 [ZMOD 91]) a
  have hb := pow_mod_period (by decide : (3 : ℤ) ^ (6 : ℕ) ≡ 1 [ZMOD 91]) b
  exact hcheck ⟨a % 12, Nat.mod_lt _ (by decide)⟩ ⟨b % 6, Nat.mod_lt _ (by decide)⟩
    (hn.symm.trans (h ▸ ha.add hb))

private theorem exclude_five {n : ℤ} {a b : ℕ} (hn : n ≡ 7 [ZMOD 51])
    (hr : a ≡ 3 [MOD 4]) (h : n = 2 ^ a + 5 ^ b) : False := by
  have hcheck : ∀ i : Fin 8, ∀ j : Fin 16, (i : ℕ) ≡ 3 [MOD 4] →
      ¬ (7 : ℤ) ≡ 2 ^ (i : ℕ) + 5 ^ (j : ℕ) [ZMOD 51] := by decide
  have ha := pow_mod_period (by decide : (2 : ℤ) ^ (8 : ℕ) ≡ 1 [ZMOD 51]) a
  have hb := pow_mod_period (by decide : (5 : ℤ) ^ (16 : ℕ) ≡ 1 [ZMOD 51]) b
  have hr' := ((Nat.mod_modEq a 8).of_dvd (by decide : 4 ∣ 8)).trans hr
  exact hcheck ⟨a % 8, Nat.mod_lt _ (by decide)⟩ ⟨b % 16, Nat.mod_lt _ (by decide)⟩ hr'
    (hn.symm.trans (h ▸ ha.add hb))

private theorem exclude_mod_three {n : ℤ} {q a b : ℕ} (hn : n ≡ 1 [ZMOD 3])
    (hq : q ≡ 1 [MOD 3]) (h : n = 2 ^ a + (q : ℤ) ^ b) : False := by
  have hcheck : ∀ i : Fin 2, ¬ (1 : ℤ) ≡ 2 ^ (i : ℕ) + 1 [ZMOD 3] := by decide
  have ha := pow_mod_period (by decide : (2 : ℤ) ^ (2 : ℕ) ≡ 1 [ZMOD 3]) a
  have hq' : (q : ℤ) ≡ 1 [ZMOD 3] := Int.natCast_modEq_iff.mpr hq
  have hb : (q : ℤ) ^ b ≡ 1 [ZMOD 3] := by
    simpa only [one_pow] using hq'.pow b
  exact hcheck ⟨a % 2, Nat.mod_lt _ (by decide)⟩ (hn.symm.trans (h ▸ ha.add hb))

private theorem exclude_sum {n : ℤ} (h2 : n ≡ 1 [ZMOD 2])
    (h3 : n ≡ 1 [ZMOD 3]) (h5 : n ≡ 3 [ZMOD 5]) (h7 : n ≡ 1 [ZMOD 7])
    (h13 : n ≡ 6 [ZMOD 13]) (h19 : n ≡ 14 [ZMOD 19]) (h37 : n ≡ 15 [ZMOD 37])
    (h73 : n ≡ 2 [ZMOD 73]) (h91 : n ≡ 71 [ZMOD 91]) (h51 : n ≡ 7 [ZMOD 51]) :
    ¬ IsSumOfTwoPrimePowers n := by
  have exclude_two_pow {q a b : ℕ} (hq : q.Prime) (he : n = 2 ^ a + (q : ℤ) ^ b) : False := by
    rcases restrict_prime h3 h5 h7 h13 h19 h37 h73 hq he with rfl | ⟨rfl, ha⟩ | hq3
    · exact exclude_three h91 he
    · exact exclude_five h51 ha he
    · exact exclude_mod_three h3 hq3 he
  rintro ⟨p, q, a, b, hp, hq, he⟩
  rcases hp.eq_two_or_odd with rfl | hop
  · exact exclude_two_pow hq he
  rcases hq.eq_two_or_odd with rfl | hoq
  · exact exclude_two_pow hp (he.trans (add_comm _ _))
  have hp' : (p : ℤ) ≡ 1 [ZMOD 2] := Int.natCast_modEq_iff.mpr hop
  have hq' : (q : ℤ) ≡ 1 [ZMOD 2] := Int.natCast_modEq_iff.mpr hoq
  have hEven : n ≡ 1 + 1 [ZMOD 2] := by
    rw [he]
    simpa only [one_pow] using (hp'.pow a).add (hq'.pow b)
  exact (by decide : ¬ (1 + 1 : ℤ) ≡ 1 [ZMOD 2]) (hEven.symm.trans h2)

set_option maxRecDepth 4096 in
private theorem progression_excluded (t : ℕ) :
    ¬ IsSumOfTwoPrimePowers (genLeonardo 1 (firstIndex + progressionStep * t)) := by
  apply exclude_sum
  · exact progression_modEq t 2 1 1 (by decide) (by decide) (by decide)
  · exact progression_modEq t 3 8 1 (by decide) (by decide) (by decide)
  · exact progression_modEq t 5 20 3 (by decide) (by decide) (by decide)
  · exact progression_modEq t 7 16 1 (by decide) (by decide) (by decide)
  · exact progression_modEq t 13 28 6 (by decide) (by decide) (by decide)
  · exact progression_modEq t 19 18 14 (by decide) (by decide) (by decide)
  · exact progression_modEq t 37 76 15 (by decide) (by decide) (by decide)
  · exact progression_modEq t 73 148 2 (by decide) (by decide) (by decide)
  -- Auxiliary congruences that exclude the bases 3 and 5.
  · exact progression_modEq t 91 112 71 (by decide) (by decide) (by decide)
  · exact progression_modEq t 51 72 7 (by decide) (by decide) (by decide)

end leonardo_infinite_not_isSumOfTwoPrimePowers

open leonardo_infinite_not_isSumOfTwoPrimePowers in
/-- **Infinitely many Leonardo numbers are not sums of two prime powers.** Let $(L_n)_{n \ge 0}$
be the Leonardo numbers, the generalized Leonardo numbers $L_{1,n}$ with parameter $1$, given
by $L_0 = L_1 = 1$ and $L_{n+2} = L_{n+1} + L_n + 1$. There are infinitely many natural numbers
$k$ such that $L_k$ is not a sum of two prime powers.

The paper, which indexes the sequence in the same way, proves the stronger statement that this
holds for every sufficiently large $k \equiv 539073 \pmod{3543120}$; that form is not stated
here.

Source: Baczkowski and Keener, *Third-Order Recurrence Sequences with
Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal
of Integer Sequences 29 (2026), Article 26.2.3, Theorem 6
(`jis-2026-26.2.3-thm-6`). -/
public theorem leonardo_infinite_not_isSumOfTwoPrimePowers :
    Set.Infinite {k : ℕ | ¬ IsSumOfTwoPrimePowers (genLeonardo 1 k)} := by
  apply Set.infinite_of_injective_forall_mem (f := fun t => firstIndex + progressionStep * t)
  · intro t s h
    exact Nat.mul_left_cancel (by decide) (Nat.add_left_cancel h)
  · exact progression_excluded

end MetaMathlibExt
