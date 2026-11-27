/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Weakly prime-additive multiples of length at most four

The Fang–Chen theorem characterizes positive integers with infinitely many weakly prime-additive
multiples of length three as those not divisible by 8. Under Leung's primitive-root hypothesis,
every positive integer has infinitely many weakly prime-additive multiples of length at most four.

We adapt Leung's four-prime construction. For the power-of-two part of the modulus we choose
residues 5, 3 and −9 for the primes $q, r, s$, respectively. In particular, −2 is a nonsquare
modulo $s$. The discrete logarithm of −2 to the primitive base $r$ is therefore odd, so we
can preserve this logarithm while making the exponent of $r$ congruent to 1 modulo both the
power of two and $q-1$.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Sums of powers of distinct prime divisors.** For natural numbers $n$ and $t$, $n$ is a sum
of positive powers of $t$ distinct prime divisors of $n$ when there are a set $s$ of $t$ distinct
primes, each dividing $n$, and positive integers $e_p$ for $p \in s$ such that
$n = \sum_{p \in s} p^{e_p}$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition (after Erdős and Hegyvári). -/
public def IsPrimeDivisorPowerSum (n t : ℕ) : Prop :=
  ∃ s : Finset ℕ, s.card = t ∧ (∀ p ∈ s, p.Prime ∧ p ∣ n) ∧
    ∃ e : ℕ → ℕ, (∀ p ∈ s, 0 < e p) ∧ n = ∑ p ∈ s, p ^ e p

/-- **Weakly prime-additive numbers.** A natural number $n$ is weakly prime-additive if it has at
least two distinct prime divisors and is a sum $n = \sum_{p \in s} p^{e_p}$ of positive powers
$p^{e_p}$, $e_p \ge 1$, over some set $s$ of distinct prime divisors of $n$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public def IsWeaklyPrimeAdditive (n : ℕ) : Prop :=
  2 ≤ n.primeFactors.card ∧ ∃ t, IsPrimeDivisorPowerSum n t

/-- **Weakly prime-additive length.** For a natural number $n$, the length $\kappa_n$ is the least
$t$ such that $n$ is a sum of positive powers of $t$ distinct prime divisors of $n$, and
$\kappa_n = 0$ when $n$ has no such representation.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public noncomputable def weaklyPrimeAdditiveLength (n : ℕ) : ℕ :=
  sInf {t | IsPrimeDivisorPowerSum n t}

/-- **Thirty is a sum of powers of three of its prime divisors.** The number $30$ is a sum of
positive powers of three distinct prime divisors of $30$, namely $30 = 2 + 3 + 5^2$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public theorem isPrimeDivisorPowerSum_thirty : IsPrimeDivisorPowerSum 30 3 := by
  refine ⟨{2, 3, 5}, by decide, ?_, fun p => if p = 5 then 2 else 1, ?_, by decide⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨Nat.prime_two, by norm_num⟩
    · exact ⟨Nat.prime_three, by norm_num⟩
    · exact ⟨Nat.prime_five, by norm_num⟩
  · intro p _
    dsimp only
    split_ifs <;> norm_num

/-- **Thirty is weakly prime-additive.** The number $30$ is weakly prime-additive.

Indeed, $30$ has the distinct prime divisors $2$, $3$, $5$ and $30 = 2 + 3 + 5^2$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public theorem isWeaklyPrimeAdditive_thirty : IsWeaklyPrimeAdditive 30 := by
  refine ⟨?_, 3, isPrimeDivisorPowerSum_thirty⟩
  have h : ({2, 3} : Finset ℕ) ⊆ (30 : ℕ).primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by norm_num, by norm_num⟩
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by norm_num, by norm_num⟩
  simpa using Finset.card_le_card h

/-- **The length is at most the size of any representation.** For natural numbers $n$ and $t$,
if $n$ is a sum of positive powers of $t$ distinct prime divisors of $n$, then the length
$\kappa_n$ of $n$ is at most $t$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition (minimality of `κ_n`). -/
public theorem weaklyPrimeAdditiveLength_le {n t : ℕ} (h : IsPrimeDivisorPowerSum n t) :
    weaklyPrimeAdditiveLength n ≤ t :=
  Nat.sInf_le h

namespace WeaklyPrimeAdditive

/-- A reduced residue class all of whose representatives satisfy the given conditions. -/
private def Progression (d : ℕ) (P : ℕ → Prop) : Prop :=
  ∃ u : (ZMod d)ˣ, ∀ n : ℕ, (n : ZMod d) = u → P n

private theorem residue {d : ℕ} {x : ZMod d} (hx : IsUnit x) :
    Progression d (fun n => (n : ZMod d) = x) :=
  ⟨hx.unit, fun _ h => h.trans hx.unit_spec⟩

private theorem combine {d e : ℕ} {P Q : ℕ → Prop} (h : d.Coprime e)
    (hd : Progression d P) (he : Progression e Q) :
    Progression (d * e) (fun n => P n ∧ Q n) := by
  obtain ⟨u, hu⟩ := hd
  obtain ⟨v, hv⟩ := he
  let E := ZMod.chineseRemainder h
  have huv : IsUnit ((u : ZMod d), (v : ZMod e)) := Prod.isUnit_iff.mpr ⟨u.isUnit, v.isUnit⟩
  obtain ⟨w, hw⟩ := huv.map E.symm.toMonoidHom
  refine ⟨w, fun n hn => ?_⟩
  have H := congrArg E (hn.trans hw)
  change E (n : ZMod (d * e)) = E (E.symm _) at H
  rw [map_natCast, E.apply_symm_apply] at H
  exact ⟨hu n (congrArg Prod.fst H), hv n (congrArg Prod.snd H)⟩

private theorem primeIn {d : ℕ} [NeZero d] {P : ℕ → Prop}
    (hd : Progression d P) (B : ℕ) : ∃ p > B, p.Prime ∧ P p := by
  obtain ⟨u, hu⟩ := hd
  obtain ⟨p, hB, hp, h⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit B
  exact ⟨p, hB, hp, hu p h⟩

private theorem reduce {d e x : ℕ} {z : ℤ} (h : d ∣ e)
    (hx : (x : ZMod e) = z) : (x : ZMod d) = z := by
  simpa using congrArg (ZMod.castHom h (ZMod d)) hx

private theorem modEight {d x : ℕ} {z : ℤ} {a : ℕ} (h : 8 ∣ d)
    (hx : (x : ZMod d) = z) (hz : (z : ZMod 8) = a) (ha : a < 8) : x % 8 = a := by
  have he := (reduce h hx).trans hz
  simpa [Nat.mod_eq_of_lt ha] using (ZMod.natCast_eq_natCast_iff' ..).mp he

private theorem jacobi_congr {d n : ℕ} {z : ℤ} (h : (n : ZMod d) = z) :
    jacobiSym n d = jacobiSym z d := by
  exact jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff ..).mp (by exact_mod_cast h))

private theorem jacobi_root {r a : ℕ} (hr : r % 8 = 3) (ha : a % 8 = 7)
    (har : (a : ZMod r) = -2) : jacobiSym r a = -1 := by
  rw [jacobiSym.quadratic_reciprocity_three_mod_four (by omega) (by omega),
    jacobi_congr (z := -2) (by simpa using har),
    jacobiSym.at_neg_two (by rw [Nat.odd_iff]; omega), ZMod.χ₈'_nat_eq_if_mod_eight]
  simp [hr, show r % 2 = 1 by omega]

private theorem jacobi_five {q : ℕ} (hq : q % 4 = 1) (hq5 : (q : ZMod 5) = -1) :
    jacobiSym (-5) q = 1 := by
  rw [show (-5 : ℤ) = -1 * (5 : ℕ) by norm_num, jacobiSym.mul_left,
    jacobiSym.at_neg_one (by rw [Nat.odd_iff]; omega), ZMod.χ₄_nat_one_mod_four hq,
    one_mul, jacobiSym.quadratic_reciprocity_one_mod_four (by decide) (by rw [Nat.odd_iff]; omega),
    jacobi_congr (z := -1) (by simpa using hq5)]
  rw [jacobiSym.at_neg_one (by decide), ZMod.χ₄_nat_one_mod_four (by decide)]

private theorem pow_half {q l : ℕ} [Fact l.Prime] (hj : jacobiSym q l = 1) :
    (q : ZMod l) ^ (l / 2) = 1 := by
  have h := legendreSym.eq_pow l (q : ℤ)
  rw [jacobiSym.legendreSym.to_jacobiSym] at h
  simpa [hj] using h.symm

private abbrev twoPart (k : ℕ) := 2 ^ (k + 3)

private theorem eight_dvd (k : ℕ) : 8 ∣ twoPart k := by
  exact pow_dvd_pow 2 (show 3 ≤ k + 3 by omega)

private theorem coprime_pred {x d : ℕ} (hx : 0 < x) (hd : Odd d)
    (h : (x : ZMod d) = -1) : (x - 1).Coprime d := by
  apply (ZMod.isUnit_iff_coprime ..).mp
  have ht := (ZMod.isUnit_iff_coprime 2 d).mpr hd.coprime_two_left
  rw [Nat.cast_sub (by omega : 1 ≤ x), Nat.cast_one, h, show (-1 : ZMod d) - 1 = -2 by ring]
  exact ht.neg

private abbrev RootHypothesis :=
  ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
    g ∣ f → jacobiSym g a = -1 →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1)

private theorem primeWithRoot (H : RootHypothesis) {f r : ℕ} [NeZero f] {P : ℕ → Prop}
    (prog : Progression f P) (hf : 8 ∣ f) (hr : r.Prime) (hr8 : r % 8 = 3)
    (hrf : r ∣ f) (hP : ∀ a, P a → a % 8 = 7 ∧ (a : ZMod r) = -2) :
    ∃ s : ℕ, s.Prime ∧ P s ∧ IsPrimitiveRoot (r : ZMod s) (s - 1) := by
  obtain ⟨u, hu⟩ := prog
  let a := (u : ZMod f).val
  have ha : (a : ZMod f) = u := ZMod.natCast_zmod_val _
  obtain ⟨ha8, har⟩ := hP a (hu a ha)
  have hcop := (ZMod.isUnit_iff_coprime a f).mp (ha ▸ u.isUnit)
  obtain ⟨s, hs, hsa, hroot⟩ := H a f r (by omega) (ZMod.val_lt _).le hcop
    (dvd_trans (by decide : 4 ∣ 8) hf) hr (by rw [Nat.odd_iff]; omega) hrf
    (jacobi_root hr8 ha8 har)
  exact ⟨s, hs, hu s (((ZMod.natCast_eq_natCast_iff ..).mpr hsa).trans ha), hroot⟩

private structure Primes (k M : ℕ) where
  p : ℕ
  q : ℕ
  r : ℕ
  s : ℕ
  hp : p.Prime
  hq : q.Prime
  hr : r.Prime
  hs : s.Prime
  p_gt : M + 5 < p
  pq : p < q
  qr : q < r
  q_two : (q : ZMod (twoPart k)) = 5
  q_odd : (q : ZMod M) = -1
  q_p : (q : ZMod p) = -1
  q_five : (q : ZMod 5) = -1
  r_two : (r : ZMod (twoPart k)) = 3
  r_odd : (r : ZMod M) = 1
  r_p : (r : ZMod p) = -1
  r_q : (r : ZMod q) = 4
  s_two : (s : ZMod (twoPart k)) = -9
  s_odd : (s : ZMod M) = -1
  s_period : (s : ZMod (q / 4)) = -1
  s_p : (s : ZMod p) = 2
  s_q : (s : ZMod q) = -5
  s_r : (s : ZMod r) = -2
  root : IsPrimitiveRoot (r : ZMod s) (s - 1)

private theorem choosePrimes (H : RootHypothesis) (k M B : ℕ) (hM : Odd M) :
    ∃ F : Primes k M, B < F.p := by
  let T := twoPart k
  have hT : 0 < T := pow_pos (by decide) _
  have hM0 := hM.pos
  obtain ⟨p, hB, hp⟩ := Nat.exists_infinite_primes (B + M + 6)
  have p5 : M + 5 < p := by omega
  have hpO := hp.odd_of_ne_two (by omega)
  let D := 5 * M * p
  have hD : Odd D := ((show Odd 5 by decide).mul hM).mul hpO
  let : NeZero (T * D) := ⟨Nat.ne_of_gt (Nat.mul_pos hT hD.pos)⟩
  -- The first two primes can be taken arbitrarily large by Dirichlet's theorem.
  have qProg := combine (hD.coprime_two_left.pow_left (k + 3))
    (residue (d := T) (x := 5) ((ZMod.isUnit_iff_coprime 5 T).mpr
      ((show Nat.Coprime 5 2 by decide).pow_right _)))
    (residue (d := D) (x := -1) isUnit_one.neg)
  obtain ⟨q, hpq, hq, hqT, hqD⟩ := primeIn qProg p
  have negD (d : ℕ) (hd : d ∣ D) : (q : ZMod d) = -1 := by
    simpa using reduce (z := -1) hd (by simpa using hqD)
  have qM := negD M (by dsimp [D]; exact Dvd.dvd.mul_right (dvd_mul_left ..) _)
  have qp := negD p (dvd_mul_left ..)
  have q5 := negD 5 (by dsimp [D]; exact Dvd.dvd.mul_right (dvd_mul_right ..) _)
  have q8 : q % 8 = 5 := modEight (z := 5) (eight_dvd k) (by simpa using hqT)
    (by decide) (by decide)
  have hqO := hq.odd_of_ne_two (by omega)
  have pM := Nat.coprime_of_lt_prime hM0.ne' (by omega : M < p) hp
  have qM' := Nat.coprime_of_lt_prime hM0.ne' (by omega : M < q) hq
  have cpq := (Nat.coprime_primes hp hq).mpr hpq.ne
  have rProg := combine (e := q) (by
      simp only [Nat.coprime_mul_iff_left]
      exact ⟨⟨hqO.coprime_two_left.pow_left _, qM'.symm⟩, cpq⟩)
    (combine (e := p) (Nat.coprime_mul_iff_left.mpr ⟨hpO.coprime_two_left.pow_left _, pM.symm⟩)
      (combine (hM.coprime_two_left.pow_left (k + 3))
        (residue (d := T) (x := 3) ((ZMod.isUnit_iff_coprime 3 T).mpr
          ((show Nat.Coprime 3 2 by decide).pow_right _)))
        (residue (d := M) isUnit_one))
      (residue (d := p) isUnit_one.neg))
    (residue (d := q) (x := 4) ((ZMod.isUnit_iff_coprime 4 q).mpr
      (Nat.coprime_of_lt_prime (by decide) (by omega : 4 < q) hq).symm))
  let : NeZero (T * M * p * q) := ⟨by simp [hT.ne', hM0.ne', hp.ne_zero, hq.ne_zero]⟩
  obtain ⟨r, hqr, hr, ⟨⟨⟨hrT, hrM⟩, hrp⟩, hrq⟩⟩ := primeIn rProg q
  have hrO := hr.odd_of_ne_two (by omega)
  have r8 : r % 8 = 3 := modEight (z := 3) (eight_dvd k) (by simpa using hrT)
    (by decide) (by decide)
  let L := M * (q / 4)
  have hj : Odd (q / 4) := by rw [Nat.odd_iff]; omega
  have hL : Odd L := hM.mul hj
  have hjdvd : q / 4 ∣ q - 1 := ⟨4, by omega⟩
  have Lp : L.Coprime p :=
    Nat.coprime_mul_iff_left.mpr ⟨pM.symm, (coprime_pred hq.pos hpO qp).of_dvd_left hjdvd⟩
  have Lq : L.Coprime q := Nat.coprime_mul_iff_left.mpr ⟨qM'.symm,
    (Nat.coprime_of_lt_prime (by omega) (by omega : q / 4 < q) hq).symm⟩
  have Lr : L.Coprime r := Nat.coprime_mul_iff_left.mpr
    ⟨(Nat.coprime_of_lt_prime hM0.ne' (by omega : M < r) hr).symm,
     (Nat.coprime_of_lt_prime (by omega) (by omega : q / 4 < r) hr).symm⟩
  let f := T * L * p * q * r
  -- The extra condition s = -1 modulo q / 4 makes the odd parts of q - 1 and s - 1 coprime.
  have sProg := combine (e := r) (by
      simp only [Nat.coprime_mul_iff_left]
      exact ⟨⟨⟨hrO.coprime_two_left.pow_left _, Lr⟩,
        (Nat.coprime_primes hp hr).mpr (hpq.trans hqr).ne⟩, (Nat.coprime_primes hq hr).mpr hqr.ne⟩)
    (combine (e := q) (by
        simp only [Nat.coprime_mul_iff_left]
        exact ⟨⟨hqO.coprime_two_left.pow_left _, Lq⟩, cpq⟩)
      (combine (e := p) (Nat.coprime_mul_iff_left.mpr ⟨hpO.coprime_two_left.pow_left _, Lp⟩)
        (combine (hL.coprime_two_left.pow_left (k + 3))
          (residue (d := T) (x := -9) (((ZMod.isUnit_iff_coprime 9 T).mpr
            ((show Nat.Coprime 9 2 by decide).pow_right _)).neg))
          (residue (d := L) isUnit_one.neg))
        (residue (d := p) (x := 2) ((ZMod.isUnit_iff_coprime 2 p).mpr hpO.coprime_two_left)))
      (residue (d := q) (x := -5) (((ZMod.isUnit_iff_coprime 5 q).mpr
        (Nat.coprime_of_lt_prime (by decide) (by omega : 5 < q) hq).symm).neg)))
    (residue (d := r) (x := -2) (((ZMod.isUnit_iff_coprime 2 r).mpr hrO.coprime_two_left).neg))
  have hLpos := hL.pos
  let : NeZero f := ⟨by simp [f, hT.ne', hLpos.ne', hp.ne_zero, hq.ne_zero, hr.ne_zero]⟩
  have hf : 8 ∣ f := by
    dsimp [f]
    exact ((((eight_dvd k).mul_right L).mul_right p).mul_right q).mul_right r
  obtain ⟨s, hs, ⟨⟨⟨⟨hsT, hsL⟩, hsp⟩, hsq⟩, hsr⟩, hroot⟩ :=
    primeWithRoot H sProg hf hr r8 (dvd_mul_left ..) (by
      rintro a ⟨⟨⟨⟨ha, _⟩, _⟩, _⟩, har⟩
      exact ⟨modEight (z := -9) (eight_dvd k) (by simpa using ha) (by decide) (by decide), har⟩)
  have negL (d : ℕ) (hd : d ∣ L) : (s : ZMod d) = -1 := by
    simpa using reduce (z := -1) hd (by simpa using hsL)
  exact ⟨⟨p, q, r, s, hp, hq, hr, hs, p5, hpq, hqr, hqT, qM, qp, q5, hrT, hrM, hrp, hrq,
    hsT, negL M (dvd_mul_right ..), negL _ (dvd_mul_left ..), hsp, hsq, hsr, hroot⟩,
    show B < p by omega⟩

private theorem pow_of_period_dvd {G : Type*} [Monoid G] {x : G} {t e : ℕ}
    (ht : x ^ t = 1) (h : t ∣ e) : x ^ e = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one ht).trans h)

private theorem pow_at_twoPart {k x e : ℕ} (hx : Odd x) (h : e ≡ 1 [MOD twoPart k]) :
    (x : ZMod (twoPart k)) ^ e = x := by
  have heuler := (ZMod.natCast_eq_natCast_iff ..).mpr
    (Nat.ModEq.pow_totient (hx.coprime_two_right.pow_right (k + 3)))
  have hd : (twoPart k).totient ∣ twoPart k := by
    change (2 ^ ((k + 2) + 1)).totient ∣ 2 ^ ((k + 2) + 1)
    refine ⟨2, ?_⟩
    rw [Nat.totient_prime_pow_succ Nat.prime_two]
    simpa only [Nat.reduceSub, mul_one] using pow_succ 2 (k + 2)
  simpa using pow_eq_pow_of_modEq (h.of_dvd hd) (by simpa using heuler :
    (x : ZMod (twoPart k)) ^ (twoPart k).totient = 1)

private theorem odd_of_one_mod {k t : ℕ} (ht : t ≡ 1 [MOD twoPart k]) : Odd t := by
  exact Nat.odd_iff.mpr (ht.of_dvd ((by decide : 2 ∣ 8).trans (eight_dvd k)))

private theorem secondExponent {k q r s : ℕ} (q8 : q % 8 = 5) (r8 : r % 8 = 3)
    (s8 : s % 8 = 7) [Fact r.Prime] [Fact s.Prime]
    (rq : (r : ZMod q) = 4) (sq : (s : ZMod q) = -5) (q5 : (q : ZMod 5) = -1) :
    ∃ b : ℕ, Odd b ∧ (q : ZMod (twoPart k)) ^ b = q ∧
      (q : ZMod r) ^ b = 1 ∧ (q : ZMod s) ^ b = 1 := by
  have qO : Odd q := Nat.odd_iff.mpr (by omega)
  have rO : Odd (r / 2) := Nat.odd_iff.mpr (by omega)
  have sO : Odd (s / 2) := Nat.odd_iff.mpr (by omega)
  obtain ⟨b, hbT, hb⟩ := Nat.chineseRemainder ((rO.mul sO).coprime_two_left.pow_left (k + 3)) 1 0
  have hd := Nat.modEq_zero_iff_dvd.mp hb
  refine ⟨b, odd_of_one_mod hbT, pow_at_twoPart qO hbT,
    pow_of_period_dvd (pow_half ?_) ((dvd_mul_right ..).trans hd),
    pow_of_period_dvd (pow_half ?_) ((dvd_mul_left ..).trans hd)⟩
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four (by omega) (Nat.odd_iff.mpr (by omega)),
      jacobi_congr (z := 4) (by simpa using rq), show (4 : ℤ) = 2 ^ 2 by norm_num]
    apply jacobiSym.sq_one'
    exact qO.coprime_two_left
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four (by omega) (Nat.odd_iff.mpr (by omega)),
      jacobi_congr (z := -5) (by simpa using sq)]
    exact jacobi_five (by omega) q5

private theorem thirdExponent {k q r s : ℕ} [Fact q.Prime] [Fact s.Prime]
    (q8 : q % 8 = 5) (r8 : r % 8 = 3) (s8 : s % 8 = 7)
    (sq : (s : ZMod (q / 4)) = -1) (rq : (r : ZMod q) = 4) (hq : 5 < q)
    (hroot : IsPrimitiveRoot (r : ZMod s) (s - 1)) :
    ∃ c : ℕ, Odd c ∧ (r : ZMod (twoPart k)) ^ c = r ∧
      (r : ZMod q) ^ c = 4 ∧ (r : ZMod s) ^ c = -2 := by
  -- Since -2 is a nonsquare at s, its discrete logarithm to the base r is odd.
  let : NeZero (s - 1) := ⟨by omega⟩
  have htwo : (2 : ZMod s) ≠ 0 :=
    fun h => Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < s)
      ((ZMod.natCast_eq_zero_iff 2 s).mp h)
  obtain ⟨i, _, hi⟩ := hroot.eq_pow_of_pow_eq_one
    (ZMod.pow_card_sub_one_eq_one (neg_ne_zero.mpr htwo))
  have hj : jacobiSym (-2) s = -1 := by
    rw [jacobiSym.at_neg_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈'_nat_eq_if_mod_eight]
    simp [s8, show s % 2 = 1 by omega]
  have hiO : Odd i := by
    apply Nat.not_even_iff_odd.mp
    intro he
    apply ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp hj
    simpa [hi] using he.isSquare_pow (r : ZMod s)
  -- Impose c = 1 modulo both periods, while preserving the logarithm modulo s - 1.
  have hJ : Odd (q / 4) := Nat.odd_iff.mpr (by omega)
  have hS : Odd (s / 2) := Nat.odd_iff.mpr (by omega)
  have hJS : (q / 4).Coprime (s / 2) :=
    (coprime_pred (by omega) hJ sq).symm.of_dvd_right (show s / 2 ∣ s - 1 from ⟨2, by omega⟩)
  have hQS : (q - 1).Coprime (s / 2) := by
    rw [show q - 1 = 2 ^ 2 * (q / 4) by omega]
    exact Nat.coprime_mul_iff_left.mpr ⟨hS.coprime_two_left.pow_left _, hJS⟩
  obtain ⟨c, hc, hci⟩ := Nat.chineseRemainder
    (Nat.coprime_mul_iff_left.mpr ⟨hS.coprime_two_left.pow_left (k + 3), hQS⟩) 1 i
  have hcT := hc.of_dvd (dvd_mul_right ..)
  have hcO : Odd c := odd_of_one_mod hcT
  have hcS : c ≡ i [MOD s - 1] := by
    rw [show s - 1 = 2 * (s / 2) by omega, ← Nat.modEq_and_modEq_iff_modEq_mul hS.coprime_two_left]
    exact ⟨(Nat.odd_iff.mp hcO).trans (Nat.odd_iff.mp hiO).symm, hci⟩
  have hfour : (4 : ZMod q) ≠ 0 :=
    fun h => Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 4 < q)
      ((ZMod.natCast_eq_zero_iff 4 q).mp h)
  refine ⟨c, hcO, pow_at_twoPart (Nat.odd_iff.mpr (by omega)) hcT, ?_,
    (pow_eq_pow_of_modEq hcS hroot.pow_eq_one).trans hi⟩
  simpa [rq] using pow_eq_pow_of_modEq (hc.of_dvd (dvd_mul_left ..))
    (ZMod.pow_card_sub_one_eq_one hfour)

private theorem commonExponent {p D : ℕ} (hD : 0 < D) (hp : p.Coprime D) :
    ∃ a > 0, ∀ d, d ∣ D → (p : ZMod d) ^ a = 1 := by
  refine ⟨D.totient, Nat.totient_pos.mpr hD, fun d hd => ?_⟩
  simpa using (ZMod.natCast_eq_natCast_iff ..).mpr ((Nat.ModEq.pow_totient hp).of_dvd hd)

private theorem fourTermSum {p q r s a b c n : ℕ} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hp : p.Prime ∧ p ∣ n) (hq : q.Prime ∧ q ∣ n)
    (hr : r.Prime ∧ r ∣ n) (hs : s.Prime ∧ s ∣ n)
    (hn : n = p ^ a + q ^ b + r ^ c + s) : IsPrimeDivisorPowerSum n 4 := by
  refine ⟨{p, q, r, s}, by simp [hpq, hpr, hps, hqr, hqs, hrs], ?_,
    fun x => if x = p then a else if x = q then b else if x = r then c else 1, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · intro x _
    dsimp only
    split_ifs <;> omega
  · simpa [hpq, hpr, hps, hqr, hqs, hrs, hpq.symm, hpr.symm, hps.symm, hqr.symm,
      hqs.symm, hrs.symm, add_assoc] using hn

private theorem small_nonzero {d t : ℕ} (ht : 0 < t) (hd : t < d) : (t : ZMod d) ≠ 0 :=
  fun h => Nat.not_dvd_of_pos_of_lt ht hd ((ZMod.natCast_eq_zero_iff ..).mp h)

private theorem distinct_of_residue {d x : ℕ} {z : ZMod d} (hz : z ≠ 0) (h : (x : ZMod d) = z) :
    d ≠ x := by
  rintro rfl
  exact hz (h.symm.trans (ZMod.natCast_self d))

private theorem multiple {k M : ℕ} (hM : Odd M) (F : Primes k M) :
    ∃ n ≥ F.p, twoPart k * M ∣ n ∧ IsWeaklyPrimeAdditive n ∧
      weaklyPrimeAdditiveLength n ≤ 4 := by
  obtain ⟨p, q, r, s, hp, hq, hr, hs, p5, hpq, hqr, qT, qM, qp, q5, rT, rM, rp, rq,
    sT, sM, sJ, sp, sq, sr, root⟩ := F
  change ∃ n ≥ p, _
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact s.Prime := ⟨hs⟩
  have q8 : q % 8 = 5 := modEight (z := 5) (eight_dvd k) (by simpa using qT)
    (by decide) (by decide)
  have r8 : r % 8 = 3 := modEight (z := 3) (eight_dvd k) (by simpa using rT)
    (by decide) (by decide)
  have s8 : s % 8 = 7 := modEight (z := -9) (eight_dvd k) (by simpa using sT)
    (by decide) (by decide)
  have hps := distinct_of_residue (small_nonzero (by decide) (by omega : 2 < p)) sp
  have hqs := distinct_of_residue
    (neg_ne_zero.mpr (small_nonzero (by decide) (by omega : 5 < q))) sq
  have hrs := distinct_of_residue
    (neg_ne_zero.mpr (small_nonzero (by decide) (by omega : 2 < r))) sr
  let D := twoPart k * M * q * r * s
  have hD : 0 < D := by
    dsimp [D, twoPart]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by positivity) hM.pos) hq.pos)
      hr.pos) hs.pos
  have pD : p.Coprime D := by
    simp only [D, Nat.coprime_mul_iff_right]
    exact ⟨⟨⟨⟨(hp.odd_of_ne_two (by omega)).coprime_two_right.pow_right _,
      Nat.coprime_of_lt_prime hM.pos.ne' (by omega) hp⟩, (Nat.coprime_primes hp hq).mpr hpq.ne⟩,
      (Nat.coprime_primes hp hr).mpr (hpq.trans hqr).ne⟩, (Nat.coprime_primes hp hs).mpr hps⟩
  obtain ⟨a, ha, hA⟩ := commonExponent hD pD
  obtain ⟨b, hb, bT, br, bs⟩ := secondExponent (k := k) q8 r8 s8 rq sq q5
  obtain ⟨c, hc, cT, cq, cs⟩ := thirdExponent (k := k) q8 r8 s8 sJ rq (by omega) root
  let n := p ^ a + q ^ b + r ^ c + s
  have zeroMod (d : ℕ) (h : (p : ZMod d) ^ a + (q : ZMod d) ^ b + (r : ZMod d) ^ c + s = 0) :
      d ∣ n := (ZMod.natCast_eq_zero_iff ..).mp (by simpa [n] using h)
  have hT : twoPart k ∣ n := by
    apply zeroMod
    rw [hA _ ((((dvd_mul_right ..).mul_right q).mul_right r).mul_right s), bT, cT, qT, rT, sT]
    ring
  have hOdd : M ∣ n := by
    apply zeroMod
    rw [hA _ ((((dvd_mul_left ..).mul_right q).mul_right r).mul_right s),
      qM, hb.neg_one_pow, rM, one_pow, sM]
    ring
  have hpN : p ∣ n := by
    apply zeroMod
    rw [ZMod.natCast_self, zero_pow ha.ne', qp, hb.neg_one_pow, rp, hc.neg_one_pow, sp]
    ring
  have hqN : q ∣ n := by
    apply zeroMod
    rw [hA _ (((dvd_mul_left ..).mul_right r).mul_right s),
      ZMod.natCast_self, zero_pow hb.pos.ne', cq, sq]
    ring
  have hrN : r ∣ n := by
    apply zeroMod
    rw [hA _ ((dvd_mul_left ..).mul_right s), br, ZMod.natCast_self, zero_pow hc.pos.ne', sr]
    ring
  have hsN : s ∣ n := by
    apply zeroMod
    rw [hA _ (dvd_mul_left ..), bs, cs, ZMod.natCast_self]
    ring
  have hsum := fourTermSum hpq.ne (hpq.trans hqr).ne hps hqr.ne hqs hrs ha hb.pos hc.pos
    ⟨hp, hpN⟩ ⟨hq, hqN⟩ ⟨hr, hrN⟩ ⟨hs, hsN⟩ rfl
  have hpn : p ≤ n := (le_self_pow hp.one_lt.le ha.ne').trans (by dsimp [n]; omega)
  refine ⟨n, hpn, (hM.coprime_two_left.pow_left _).mul_dvd_of_dvd_of_dvd hT hOdd,
    ⟨?_, 4, hsum⟩, weaklyPrimeAdditiveLength_le hsum⟩
  obtain ⟨t, ht, hprimes, _⟩ := hsum
  have hsub : t ⊆ n.primeFactors := fun x hx =>
    Nat.mem_primeFactors.mpr ⟨(hprimes x hx).1, (hprimes x hx).2, (hp.pos.trans_le hpn).ne'⟩
  have := Finset.card_le_card hsub
  omega

end WeaklyPrimeAdditive

/-- **Weakly prime-additive multiples of length at most four.** Assume $(\ast)$: for all natural
numbers $a$, $f$, $g$ with $1 \le a \le f$, $\gcd(a, f) = 1$ and $4 \mid f$, and $g$ an odd prime
dividing $f$ with Jacobi symbol $\left(\frac{g}{a}\right) = -1$, there is a prime
$\ell \equiv a \pmod f$ such that $g$ is a primitive root modulo $\ell$. Then for every positive
integer $m$ there are infinitely many weakly prime-additive numbers $n$ with $m \mid n$ and
length $\kappa_n \le 4$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 6. -/
public theorem infinite_weaklyPrimeAdditive_length_le_four_dvd
    (hstar : ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
      g ∣ f → jacobiSym g a = -1 →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1))
    (m : ℕ) (hm : 0 < m) :
    {n : ℕ | m ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n ≤ 4}.Infinite := by
  obtain ⟨k, M, hM, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨F, hB⟩ := WeaklyPrimeAdditive.choosePrimes hstar k M B hM
  obtain ⟨n, hpn, hn, hw, hl⟩ := WeaklyPrimeAdditive.multiple hM F
  have hd : 2 ^ k * M ∣ WeaklyPrimeAdditive.twoPart k * M :=
    mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) M
  exact ⟨n, ⟨hd.trans hn, hw, hl⟩, hB.trans_le hpn⟩

namespace WeaklyPrimeAdditive

/-- Replacing an exponent by one of 1, 2, 3, 4 preserves its parity and the power of 2
modulo 8. -/
private theorem exponent_mod_eight {a : ℕ} (ha : 0 < a) :
    ∃ k : Fin 5, 0 < k.val ∧ k.val ≡ a [MOD 2] ∧ 2 ^ k.val ≡ 2 ^ a [MOD 8] := by
  by_cases h : a ≤ 2
  · exact ⟨⟨a, by omega⟩, ha, .refl _, .refl _⟩
  have hz (i : ℕ) (hi : 3 ≤ i) : 2 ^ i ≡ 0 [MOD 8] :=
    Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 hi)
  let k : Fin 5 := ⟨3 + (a + 1) % 2, by omega⟩
  exact ⟨k, by dsimp [k]; omega, by change (3 + (a + 1) % 2) % 2 = a % 2; omega,
    (hz _ (by dsimp [k]; omega)).trans (hz a (by omega)).symm⟩

/-- Evaluate the Jacobi symbol of the negative power of two from the two supplementary laws. -/
private theorem symbol_neg_pow_two {u a k : ℕ} (hu : Odd u) (hk : k ≡ a [MOD 2]) :
    jacobiSym (-(2 : ℤ) ^ a) u =
      ZMod.χ₄ (u % 8 : ℕ) * ZMod.χ₈ (u % 8 : ℕ) ^ k := by
  have h₄ : ZMod.χ₄ (u % 8 : ℕ) = ZMod.χ₄ u := by
    rw [ZMod.χ₄_nat_mod_four (u % 8), Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 8),
      ← ZMod.χ₄_nat_mod_four]
  have h₂ : ZMod.χ₈ u ^ 2 = 1 := by
    rw [← jacobiSym.at_two hu]
    exact jacobiSym.sq_one (show Nat.Coprime 2 u from hu.coprime_two_left)
  rw [jacobiSym.neg _ hu, jacobiSym.pow_left, jacobiSym.at_two hu, h₄,
    ← ZMod.χ₈_nat_mod_eight, pow_eq_pow_of_modEq hk h₂]

/-- Reciprocity at the two odd prime powers is incompatible with divisibility by 8. -/
private theorem eight_obstruction {a u v : ℕ} (ha : 0 < a) (hu : Odd u) (hv : Odd v)
    (huv : jacobiSym v u = jacobiSym (-(2 : ℤ) ^ a) u)
    (hvu : jacobiSym u v = jacobiSym (-(2 : ℤ) ^ a) v) : ¬ 8 ∣ 2 ^ a + u + v := by
  intro h
  obtain ⟨k, hk, hka, hk8⟩ := exponent_mod_eight ha
  let x : Fin 8 := ⟨u % 8, Nat.mod_lt _ (by decide)⟩
  let y : Fin 8 := ⟨v % 8, Nat.mod_lt _ (by decide)⟩
  have table : ∀ x y : Fin 8, ∀ k : Fin 5, Odd x.val → Odd y.val → 0 < k.val →
      8 ∣ 2 ^ k.val + x.val + y.val →
      ZMod.χ₄ x.val * ZMod.χ₈ x.val ^ k.val ≠
        (-1) ^ (x.val / 2 * (y.val / 2)) * (ZMod.χ₄ y.val * ZMod.χ₈ y.val ^ k.val) := by
    decide
  have half (z : ℕ) : z / 2 ≡ z % 8 / 2 [MOD 2] := by unfold Nat.ModEq; omega
  have hs := pow_eq_pow_of_modEq ((half u).mul (half v)) (neg_one_sq (R := ℤ))
  have hr := jacobiSym.quadratic_reciprocity hv hu
  rw [huv, hvu, symbol_neg_pow_two hu hka, symbol_neg_pow_two hv hka, mul_comm (v / 2), hs] at hr
  apply table x y k (Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hu; dsimp [x]; omega))
    (Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hv; dsimp [y]; omega)) hk _ hr
  exact Nat.modEq_zero_iff_dvd.mp (((hk8.add (Nat.mod_modEq ..)).add (Nat.mod_modEq ..)).trans
    (Nat.modEq_zero_iff_dvd.mpr h))

private theorem symbol_of_prime_dvd_sum {p a b v : ℕ} (hb : 0 < b)
    (hd : p ∣ 2 ^ a + p ^ b + v) :
    jacobiSym v (p ^ b) = jacobiSym (-(2 : ℤ) ^ a) (p ^ b) := by
  have h := (ZMod.natCast_eq_zero_iff ..).mpr hd
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_self, zero_pow hb.ne',
    add_zero] at h
  rw [jacobiSym.pow_right, jacobiSym.pow_right]
  congr 1
  apply jacobi_congr
  push_cast
  linear_combination h

private theorem not_eight_dvd_sum_three {n : ℕ} (hsum : IsPrimeDivisorPowerSum n 3) : ¬ 8 ∣ n := by
  intro h₈
  obtain ⟨s, hcard, primes, e, pos, hn⟩ := hsum
  have htwo : 2 ∈ s := by
    by_contra h
    have ho (x : ℕ) (hx : x ∈ s) : Odd (x ^ e x) :=
      ((primes x hx).1.odd_of_ne_two (fun he => h (he ▸ hx))).pow
    have hnOdd : Odd n := by
      rw [hn, Finset.odd_sum_iff_odd_card_odd, Finset.filter_true_of_mem ho, hcard]
      decide
    have := Nat.odd_iff.mp hnOdd
    omega
  obtain ⟨p, q, hpq, hpqs⟩ := Finset.card_eq_two.mp
    (show (s.erase 2).card = 2 by rw [Finset.card_erase_of_mem htwo, hcard])
  have hne : 2 ∉ ({p, q} : Finset ℕ) := hpqs ▸ Finset.notMem_erase 2 s
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
  have hs : s = {2, p, q} := by rw [← hpqs, Finset.insert_erase htwo]
  have hp := primes p (by simp [hs])
  have hq := primes q (by simp [hs])
  have hb := pos p (by simp [hs])
  have hc := pos q (by simp [hs])
  have ha := pos 2 htwo
  have he : n = 2 ^ e 2 + p ^ e p + q ^ e q := by
    simpa [hs, hne.1, hne.2, hpq, add_assoc] using hn
  rw [he] at hp hq h₈
  exact eight_obstruction ha (hp.1.odd_of_ne_two (Ne.symm hne.1)).pow
    (hq.1.odd_of_ne_two (Ne.symm hne.2)).pow (symbol_of_prime_dvd_sum hb hp.2)
    (symbol_of_prime_dvd_sum hc (by simpa [add_right_comm] using hq.2)) h₈

/-- Every weakly prime-additive number has length at least three. -/
private theorem three_le_length {n : ℕ} (hw : IsWeaklyPrimeAdditive n) :
    3 ≤ weaklyPrimeAdditiveLength n := by
  have hcard := hw.1
  obtain ⟨t, ht, htprimes, e, pos, he⟩ :=
    Nat.sInf_mem (s := {k | IsPrimeDivisorPowerSum n k}) hw.2
  change t.card = weaklyPrimeAdditiveLength n at ht
  by_contra! hlt
  have cases : t.card = 0 ∨ t.card = 1 ∨ t.card = 2 := by omega
  rcases cases with h₀ | h₁ | h₂
  · simp [Finset.card_eq_zero.mp h₀] at he
    simp [he] at hcard
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp h₁
    simp only [Finset.sum_singleton] at he
    rw [he, Nat.primeFactors_prime_pow (pos p (by simp)).ne' (htprimes p (by simp)).1] at hcard
    simp at hcard
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp h₂
    obtain ⟨hp, hpn⟩ := htprimes p (by simp)
    have hq := (htprimes q (by simp)).1
    simp only [Finset.mem_singleton, hpq, not_false_eq_true, Finset.sum_insert,
      Finset.sum_singleton] at he
    rw [he] at hpn
    have hd := (Nat.dvd_add_right (dvd_pow_self p (pos p (by simp)).ne')).mp hpn
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd))

/-- A sum of three powers witnessing weak prime-additivity already has minimum length. -/
private theorem length_three {n : ℕ} (hn : 0 < n) (h : IsPrimeDivisorPowerSum n 3) :
    IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 3 := by
  have hcard : 3 ≤ n.primeFactors.card := by
    obtain ⟨s, hs, primes, _⟩ := h
    rw [← hs]
    exact Finset.card_le_card fun p hp =>
      (primes p hp).1.mem_primeFactors (primes p hp).2 hn.ne'
  have hw : IsWeaklyPrimeAdditive n := ⟨by omega, 3, h⟩
  exact ⟨hw, le_antisymm (weaklyPrimeAdditiveLength_le h) (three_le_length hw)⟩

/-- Choose the two odd primes so that the half period of the second is coprime to both
periods needed for the power of two. -/
private theorem shortest_primes (M B : ℕ) (hM : Odd M) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ B + 2 < p ∧ p < q ∧ p % 8 = 1 ∧ q % 8 = 3 ∧
      (p : ZMod M) = -1 ∧ (q : ZMod M) = -1 ∧ (q : ZMod p) = -2 ∧
      (q / 2).Coprime ((p - 1) * M.totient) := by
  have Mpos := hM.pos
  let : NeZero (8 * M) := ⟨by omega⟩
  have pProg := combine (show Nat.Coprime 8 M from hM.coprime_two_left.pow_left 3)
    (residue (d := 8) isUnit_one) (residue (d := M) isUnit_one.neg)
  obtain ⟨p, hpB, hp, hp8, hpM⟩ := primeIn pProg (B + M + 8)
  have p8 : p % 8 = 1 := modEight (z := 1) dvd_rfl (by simpa using hp8) (by decide) (by decide)
  have pOdd := hp.odd_of_ne_two (by omega)
  let T := (p - 1) * M.totient
  have hφ := Nat.totient_pos.mpr Mpos
  have hT : 0 < T := Nat.mul_pos (by omega) hφ
  obtain ⟨j, U, hU, hTU⟩ := Nat.exists_eq_two_pow_mul_odd hT.ne'
  have pT : p.Coprime T := Nat.coprime_mul_iff_right.mpr
    ⟨Nat.coprime_of_lt_prime (by omega) (by omega) hp,
      Nat.coprime_of_lt_prime hφ.ne' ((Nat.totient_le M).trans_lt (by omega)) hp⟩
  have pU := pT.of_dvd_right (show U ∣ T by rw [hTU]; exact dvd_mul_left ..)
  let L := M * U
  have hL : Odd L := hM.mul hU
  have pL : L.Coprime p := (Nat.coprime_mul_iff_right.mpr
    ⟨Nat.coprime_of_lt_prime Mpos.ne' (by omega) hp, pU⟩).symm
  have qProg := combine (Nat.coprime_mul_iff_left.mpr ⟨pOdd.coprime_two_left.pow_left 3, pL⟩)
    (combine (show Nat.Coprime 8 L from hL.coprime_two_left.pow_left 3)
      (residue (d := 8) (x := 3) ((ZMod.isUnit_iff_coprime 3 8).mpr (by decide)))
      (residue (d := L) isUnit_one.neg))
    (residue (d := p) (x := -2) (((ZMod.isUnit_iff_coprime 2 p).mpr pOdd.coprime_two_left).neg))
  let : NeZero (8 * L * p) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (by decide) hL.pos.ne') hp.ne_zero⟩
  obtain ⟨q, hpq, hq, ⟨hq8, hqL⟩, hqp⟩ := primeIn qProg p
  have q8 : q % 8 = 3 := modEight (z := 3) dvd_rfl (by simpa using hq8) (by decide) (by decide)
  have negL (d : ℕ) (hd : d ∣ L) : (q : ZMod d) = -1 := by
    simpa using reduce (z := -1) hd (by simpa using hqL)
  have hb : Odd (q / 2) := Nat.odd_iff.mpr (by omega)
  refine ⟨p, q, hp, hq, by omega, hpq, p8, q8, hpM, negL M (dvd_mul_right ..), hqp, ?_⟩
  change (q / 2).Coprime T
  rw [hTU, Nat.coprime_mul_iff_right]
  have hpred := coprime_pred hq.pos hU (negL U (dvd_mul_left ..))
  exact ⟨hb.coprime_two_right.pow_right _, hpred.of_dvd_left ⟨2, by omega⟩⟩

/-- For odd M, construct arbitrarily large three-term sums divisible by 4M. -/
private theorem shortest_multiple (M B : ℕ) (hM : Odd M) :
    ∃ n > B, 4 * M ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 3 := by
  obtain ⟨p, q, hp, hq, hB, hpq, p8, q8, pM, qM, qp, hcop⟩ := shortest_primes M B hM
  let : Fact q.Prime := ⟨hq⟩
  let b := q / 2
  have hb : Odd b := Nat.odd_iff.mpr (by dsimp [b]; omega)
  -- Reciprocity makes p a square at q. At the same prime, 2 is a nonsquare.
  have hjp : jacobiSym p q = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four (by omega) (hq.odd_of_ne_two (by omega)),
      jacobi_congr (z := -2) (by simpa using qp),
      jacobiSym.at_neg_two (hp.odd_of_ne_two (by omega)), ZMod.χ₈'_nat_eq_if_mod_eight]
    simp [p8, show p % 2 = 1 by omega]
  have hj2 : jacobiSym 2 q = -1 := by
    rw [jacobiSym.at_two (hq.odd_of_ne_two (by omega)), ZMod.χ₈_nat_eq_if_mod_eight]
    simp [q8, show q % 2 = 1 by omega]
  have h2q : (2 : ZMod q) ^ b = -1 := by
    have he := legendreSym.eq_pow q 2
    rw [jacobiSym.legendreSym.to_jacobiSym, hj2] at he
    simpa [b] using he.symm
  -- Euler's theorem gives a ≡ 1 modulo T, while a is an odd multiple of b.
  let T := (p - 1) * M.totient
  have hT : 0 < T := Nat.mul_pos (by omega) (Nat.totient_pos.mpr hM.pos)
  let a := b ^ T.totient
  have haT : a ≡ 1 [MOD T] := Nat.ModEq.pow_totient hcop
  have ht := Nat.totient_pos.mpr hT
  have hba : b ≤ a := le_self_pow (by dsimp [b]; omega) ht.ne'
  have ha : 2 ≤ a := by dsimp [b] at hba; omega
  have h2aq : (2 : ZMod q) ^ a = -1 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    dsimp [a]
    rw [hj, pow_succ', pow_mul, h2q, (hb.pow (n := j)).neg_one_pow]
  have two_pow (d : ℕ) (hd : d.totient ∣ T) (ho : Odd d) : (2 : ZMod d) ^ a = 2 := by
    have he := (ZMod.natCast_eq_natCast_iff ..).mpr (Nat.ModEq.pow_totient ho.coprime_two_left)
    simpa using pow_eq_pow_of_modEq (haT.of_dvd hd) (by simpa using he :
      (2 : ZMod d) ^ d.totient = 1)
  let n := 2 ^ a + p ^ b + q
  have zeroMod (d : ℕ) (h : (2 : ZMod d) ^ a + (p : ZMod d) ^ b + q = 0) : d ∣ n :=
    (ZMod.natCast_eq_zero_iff ..).mp (by simpa [n] using h)
  have hMdiv := zeroMod M (by rw [two_pow M (dvd_mul_left ..) hM, pM, hb.neg_one_pow, qM]; ring)
  have hpdiv := zeroMod p (by
    rw [two_pow p (by rw [Nat.totient_prime hp]; exact dvd_mul_right ..)
      (hp.odd_of_ne_two (by omega)), ZMod.natCast_self, zero_pow hb.pos.ne', qp]
    ring)
  have hqdiv := zeroMod q (by rw [h2aq, pow_half hjp, ZMod.natCast_self]; ring)
  have h₄ := zeroMod 4 (by
    have hp4 : (p : ZMod 4) = 1 := (ZMod.natCast_eq_natCast_iff p 1 4).mpr (by
      change p % 4 = 1; omega)
    have hq4 : (q : ZMod 4) = -1 := by
      have h : (q : ZMod 4) = (3 : ℕ) := (ZMod.natCast_eq_natCast_iff q 3 4).mpr (by
        change q % 4 = 3; omega)
      exact h.trans (by decide)
    have hpow : (2 : ZMod 4) ^ a = 0 := by
      exact pow_eq_zero_of_le ha (by decide : (2 : ZMod 4) ^ 2 = 0)
    rw [hpow, hp4, one_pow, hq4]; ring)
  have hqn : q ≤ n := Nat.le_add_left ..
  have hsum : IsPrimeDivisorPowerSum n 3 := by
    have h2p : 2 ≠ p := by omega
    have h2q' : 2 ≠ q := by omega
    refine ⟨{2, p, q}, by simp [h2p, h2q', hpq.ne], ?_,
      fun x => if x = 2 then a else if x = p then b else 1, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨Nat.prime_two, dvd_trans (by decide : 2 ∣ 4) h₄⟩
      · exact ⟨hp, hpdiv⟩
      · exact ⟨hq, hqdiv⟩
    · intro x _
      have := hb.pos
      dsimp only
      split_ifs <;> omega
    · simp [n, h2p, h2q', hpq.ne, h2p.symm, h2q'.symm, hpq.ne', add_assoc]
  exact ⟨n, by omega, (hM.coprime_two_left.pow_left 2).mul_dvd_of_dvd_of_dvd h₄ hMdiv,
    length_three (hq.pos.trans_le hqn) hsum⟩

end WeaklyPrimeAdditive

/-- **Fang–Chen theorem on shortest weakly prime-additive multiples.** For every positive integer
$m$, there are infinitely many weakly prime-additive numbers $n$ with $m \mid n$ and length
$\kappa_n = 3$ if and only if $8 \nmid m$.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 5 (Fang and Chen, Corollary 1.1). -/
public theorem infinite_shortest_weaklyPrimeAdditive_dvd_iff (m : ℕ) (hm : 0 < m) :
    {n : ℕ | m ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 3}.Infinite ↔
      ¬ 8 ∣ m := by
  constructor
  · intro h hm₈
    obtain ⟨n, hn⟩ := h.nonempty
    obtain ⟨hmn, hw, hl⟩ := hn
    have hsum : IsPrimeDivisorPowerSum n (weaklyPrimeAdditiveLength n) :=
      Nat.sInf_mem (s := {k | IsPrimeDivisorPowerSum n k}) hw.2
    rw [hl] at hsum
    exact WeaklyPrimeAdditive.not_eight_dvd_sum_three hsum (hm₈.trans hmn)
  · intro hm₈
    obtain ⟨k, M, hM, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
    have hk : k ≤ 2 := by
      by_contra! h
      exact hm₈ ((show 8 ∣ 2 ^ k from pow_dvd_pow 2 h).mul_right M)
    apply Set.infinite_iff_exists_gt.mpr
    intro B
    obtain ⟨n, hB, hdiv, hlen⟩ := WeaklyPrimeAdditive.shortest_multiple M B hM
    have hd : 2 ^ k * M ∣ 4 * M := mul_dvd_mul_right (pow_dvd_pow 2 hk) M
    exact ⟨n, ⟨hd.trans hdiv, hlen⟩, hB⟩

/-- **Weakly prime-additive multiples of length four.** Assume $(\ast)$: for all natural numbers
$a$, $f$, $g$ with $1 \le a \le f$, $\gcd(a, f) = 1$ and $4 \mid f$, and $g$ an odd prime dividing
$f$ with Jacobi symbol $\left(\frac{g}{a}\right) = -1$, there is a prime $\ell \equiv a \pmod f$
such that $g$ is a primitive root modulo $\ell$. Then for every positive integer $m$ there are
infinitely many weakly prime-additive numbers $n$ with $m \mid n$ and length $\kappa_n = 4$.

The paper states $(\ast)$ with the Kronecker symbol; since $a$ is coprime to $f$ and $4 \mid f$,
$a$ is odd, so it is the Jacobi symbol.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 1. -/
public theorem infinite_weaklyPrimeAdditive_length_four_dvd
    (hstar : ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
      g ∣ f → jacobiSym g a = -1 →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1))
    (m : ℕ) (hm : 0 < m) :
    {n : ℕ | m ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 4}.Infinite := by
  refine (infinite_weaklyPrimeAdditive_length_le_four_dvd hstar (8 * m)
    (Nat.mul_pos (by decide) hm)).mono ?_
  rintro n ⟨hd, hw, hl⟩
  refine ⟨(dvd_mul_left m 8).trans hd, hw, le_antisymm hl ?_⟩
  have h₃ := WeaklyPrimeAdditive.three_le_length hw
  by_contra! hlt
  have he : weaklyPrimeAdditiveLength n = 3 := by omega
  have hsum : IsPrimeDivisorPowerSum n (weaklyPrimeAdditiveLength n) :=
    Nat.sInf_mem (s := {k | IsPrimeDivisorPowerSum n k}) hw.2
  rw [he] at hsum
  exact WeaklyPrimeAdditive.not_eight_dvd_sum_three hsum ((dvd_mul_right 8 m).trans hd)

end

end MetaMathlibExt
