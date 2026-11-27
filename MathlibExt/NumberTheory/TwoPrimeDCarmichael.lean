/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula

/-!
# Two-prime absolute Lucas pseudoprimes

For an odd prime dividing the product, the quotient of the two characteristic roots of a Lucas
sequence has order dividing the prime minus the Jacobi symbol. For the converse bound we realize
a primitive root of that order as such a quotient, keeping the integer discriminant fixed.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **$D$-Carmichael number.** Let $D$ be an integer. A natural number $n$ is a $D$-Carmichael
number when $D \equiv 0$ or $1 \pmod 4$, $n > 1$ is odd and composite, $D$ and $n$ are coprime,
and for all integers $P$ and $Q \ne 0$ with $P$ and $Q$ coprime, $P^2 - 4Q = D$ and $Q$ coprime
to $n$, the number $n$ divides the term $U_{n - \varepsilon_n}(P, Q)$ of the Lucas sequence
$U(P, Q)$, where $\varepsilon_n = \left(\frac{D}{n}\right)$ is the Jacobi symbol.

These are Williams' absolute Lucas $D$-pseudoprimes. The condition on $D$ is the paper's standing
assumption; for other $D$ no Lucas sequence has discriminant $D$, so the last clause would be
vacuous.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1 (definition of absolute Lucas `D`-pseudoprimes, after [17]). -/
def IsDCarmichael (D : ℤ) (n : ℕ) : Prop :=
  (D % 4 = 0 ∨ D % 4 = 1) ∧ Odd n ∧ 1 < n ∧ ¬ n.Prime ∧ IsCoprime D n ∧
    ∀ params : LucasSequenceParams, params.IsCoprime → params.p ^ 2 - 4 * params.q = D →
      IsCoprime params.q n → (n : ℤ) ∣ lucasU params (n - jacobiSym D n).toNat

namespace isDCarmichael_mul_iff

/-- Along one progression of traces of step $4D$, the parameters are integral and coprime. -/
private lemma trace_progression {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ B : ℤ, ∀ t : ℤ, ∃ Q : ℤ,
      (B + 4 * D * t) ^ 2 - 4 * Q = D ∧ IsCoprime (B + 4 * D * t) Q := by
  let d := D / 4
  rcases hD with h | h
  · have hd : D = 4 * d := by dsimp [d]; omega
    refine ⟨2 * (1 + d), fun t => ?_⟩
    let u := 1 + d * (1 + 8 * t)
    have hu : 2 * (1 + d) + 4 * D * t = 2 * u := by rw [hd]; dsimp [u]; ring
    rw [hu]
    refine ⟨u ^ 2 - d, by rw [hd]; ring, IsCoprime.mul_left ?_ ?_⟩
    · rw [Int.isCoprime_two_left, Int.odd_iff]
      dsimp [u]
      have hd2 : d % 2 = 0 ∨ d % 2 = 1 := by omega
      rcases hd2 with h2 | h2 <;> simp [Int.sub_emod, Int.add_emod, Int.mul_emod, pow_two, h2]
    · have hc : IsCoprime u d := by simp [u, isCoprime_one_left]
      simpa only [pow_two, IsCoprime.mul_sub_left_right_iff] using hc
  · have hd : D = 4 * d + 1 := by dsimp [d]; omega
    refine ⟨1, fun t => ?_⟩
    let P := 1 + 4 * D * t
    let Q := -d + 2 * D * t + 4 * D ^ 2 * t ^ 2
    have hdisc : P ^ 2 - 4 * Q = D := by dsimp [P, Q]; linear_combination -hd
    refine ⟨Q, hdisc, ?_⟩
    have hc : IsCoprime P D := by
      dsimp [P]
      rw [show 4 * D * t = D * (4 * t) by ring]
      simp [isCoprime_one_left]
    obtain ⟨a, b, hab⟩ := hc
    refine ⟨a + b * P, -4 * b, ?_⟩
    linear_combination hab + b * hdisc

private lemma cast_ne_zero_iff_coprime {r : ℕ} [Fact r.Prime] {K : Type*}
    [Field K] [CharP K r] (a : ℤ) : (a : K) ≠ 0 ↔ IsCoprime a r := by
  rw [ne_eq, CharP.intCast_eq_zero_iff K r, isCoprime_comm,
    (Nat.prime_iff_prime_int.mp Fact.out).coprime_iff_not_dvd]

private lemma two_ne_zero {r : ℕ} [Fact r.Prime] {K : Type*} [Field K] [CharP K r]
    (hr : r ≠ 2) : (2 : K) ≠ 0 :=
  Ring.two_ne_zero (by rwa [ringChar.eq K r])

/-- Lift a trace at the prime, forcing trace zero modulo its complementary factor. -/
private lemma lift_trace {p q : ℕ} [Fact q.Prime]
    (hp : Odd p) (hq : q ≠ 2) (hpq : p.Coprime q) {D : ℤ}
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hDp : IsCoprime D p) (hDq : IsCoprime D q)
    (x : ℤ) (hx : (x : ZMod q) ^ 2 ≠ (D : ZMod q)) :
    ∃ s : LucasSequenceParams, s.IsCoprime ∧ s.p ^ 2 - 4 * s.q = D ∧
      IsCoprime s.q (↑(p * q) : ℤ) ∧ (s.p : ZMod q) = (x : ZMod q) := by
  obtain ⟨B, hB⟩ := trace_progression hD
  have four {m : ℕ} (hm : Odd m) : IsCoprime (4 : ℤ) m := by
    have h : IsCoprime (2 : ℤ) m := Int.isCoprime_two_left.mpr (by exact_mod_cast hm)
    simpa using h.mul_left h
  obtain ⟨u, v, huv⟩ := (four hp).mul_left hDp
  obtain ⟨w, z, hwz⟩ :=
    ((four ((Fact.out : q.Prime).odd_of_ne_two hq)).mul_left hDq).mul_left hpq.isCoprime
  -- The first correction makes the trace divisible by p. The second, a multiple
  -- of p, prescribes its residue x modulo q.
  let t₀ := -u * B
  let P₀ := B + 4 * D * t₀
  have hP₀ : P₀ = p * (v * B) := by dsimp [P₀, t₀]; linear_combination -B * huv
  let t := t₀ + p * w * (x - P₀)
  let P := B + 4 * D * t
  have hPp : (p : ℤ) ∣ P := by
    refine ⟨v * B + 4 * D * w * (x - P₀), ?_⟩
    dsimp [P, t]
    linear_combination hP₀
  have hPq : (P : ZMod q) = x := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mpr
    refine ⟨z * (x - P₀), ?_⟩
    dsimp [P, t, P₀]
    linear_combination -(x - (B + 4 * D * t₀)) * hwz
  obtain ⟨Q, hdisc : P ^ 2 - 4 * Q = D, hc⟩ := hB t
  have hQp : IsCoprime Q p := by
    obtain ⟨k, hk⟩ := hPp
    have h : IsCoprime (-(4 * Q) + (p : ℤ) * (k * P)) p := by
      convert hDp using 1
      linear_combination hdisc - P * hk
    exact h.of_add_mul_left_left.of_isCoprime_of_dvd_left (dvd_neg.mpr (dvd_mul_left Q 4))
  have hQq : (Q : ZMod q) ≠ 0 := by
    intro hz
    apply hx
    simpa [hPq, hz] using congrArg (fun y : ℤ => (y : ZMod q)) hdisc
  refine ⟨⟨P, Q, fun h => hQq (by simp [h])⟩, hc, hdisc, ?_, hPq⟩
  simpa only [Nat.cast_mul] using hQp.mul_right ((cast_ne_zero_iff_coprime Q).mp hQq)

section Local

variable {r : ℕ} [Fact r.Prime] {K : Type*} [Field K] [CharP K r]

/-- Frobenius acts on a square root of the discriminant by its Jacobi sign. -/
private lemma discriminant_root (K : Type*) [Field K] [CharP K r] [IsAlgClosed K]
    {D : ℤ} (hr : r ≠ 2) (hD : IsCoprime D r) :
    ∃ s : K, s ≠ 0 ∧ s ^ 2 = D ∧ frobenius K r s = (jacobiSym D r : K) * s := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (D : K) (n := 2) (by decide)
  have hs0 : s ≠ 0 := fun h => (cast_ne_zero_iff_coprime D).mpr hD (by rw [← hs, h]; simp)
  refine ⟨s, hs0, hs, ?_⟩
  have he := congrArg (ZMod.castHom (m := r) dvd_rfl K) (legendreSym.eq_pow r D)
  simp only [map_intCast, map_pow, jacobiSym.legendreSym.to_jacobiSym] at he
  have h : r = 2 * (r / 2) + 1 := by
    obtain ⟨k, hk⟩ := (Fact.out : r.Prime).odd_of_ne_two hr
    omega
  calc
    s ^ r = s ^ (2 * (r / 2) + 1) := congrArg (s ^ ·) h
    _ = _ := by rw [pow_succ, pow_mul, hs, he]

omit [Fact r.Prime] in
private lemma dvd_lucas_iff {a b : K} (s : LucasSequenceParams)
    (hs : a + b = s.p) (hp : a * b = s.q) (hab : a ≠ b) (hb : b ≠ 0) (n : ℕ) :
    (r : ℤ) ∣ lucasU s n ↔ (a / b) ^ n = 1 := by
  rw [← CharP.intCast_eq_zero_iff K r,
    ((lucas_binet_formulas_of_field s a b hs hp).1 hab n).1, div_pow,
    div_eq_one_iff_eq (pow_ne_zero _ hb), div_eq_zero_iff, sub_eq_zero, sub_eq_zero,
    or_iff_left hab]

/-- Every admissible sequence vanishes locally at multiples of the prime minus its sign. -/
private lemma prime_dvd_lucas (K : Type*) [Field K] [CharP K r] [IsAlgClosed K]
    {D : ℤ} (hr : r ≠ 2) (hD : IsCoprime D r)
    (s : LucasSequenceParams) (hdisc : s.p ^ 2 - 4 * s.q = D) (hQ : IsCoprime s.q r)
    {k n : ℕ} (hk : (k : ℤ) = r - jacobiSym D r) (hn : k ∣ n) :
    (r : ℤ) ∣ lucasU s n := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero hr
  obtain ⟨δ, hδ0, hδ, hf⟩ := discriminant_root K hr hD
  let a : K := (s.p + δ) / 2
  let b : K := (s.p - δ) / 2
  have hsum : a + b = s.p := by dsimp [a, b]; field_simp [h2]; ring
  have hprod : a * b = s.q := by
    have hd := congrArg (fun z : ℤ => (z : K)) hdisc
    push_cast at hd
    dsimp [a, b]
    field_simp [h2]
    linear_combination hd - hδ
  have hprod0 : a * b ≠ 0 := by
    rw [hprod]
    exact (cast_ne_zero_iff_coprime s.q).mpr hQ
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hprod0
  have hab : a ≠ b := by
    have hdiff : a - b = δ := by dsimp [a, b]; field_simp [h2]; ring
    simpa only [← hdiff, sub_ne_zero] using hδ0
  rw [dvd_lucas_iff s hsum hprod hab hb]
  obtain ⟨m, rfl⟩ := hn
  rw [pow_mul]
  suffices h : (a / b) ^ k = 1 by simp [h]
  let F := frobenius K r
  change F δ = _ at hf
  rcases jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp hD) with hj | hj
  · have h : F (a / b) = a / b := by simp [a, b, map_div₀, map_ofNat, hf, hj]
    change (a / b) ^ r = a / b at h
    have hkr : r = k + 1 := by omega
    rw [congrArg ((a / b) ^ ·) hkr, pow_succ, mul_eq_right₀ (div_ne_zero ha hb)] at h
    exact h
  · have h : F (a / b) = b / a := by simp [a, b, map_div₀, map_ofNat, hf, hj, sub_eq_add_neg]
    change (a / b) ^ r = b / a at h
    have hkr : k = r + 1 := by omega
    rw [hkr, pow_succ, h]
    field_simp [ha, hb]

end Local

/-- Realize a primitive root of order $q-(D\mid q)$ as the quotient of characteristic roots. -/
private lemma local_order_dvd {p q : ℕ} [Fact q.Prime]
    (K : Type*) [Field K] [CharP K q] [IsAlgClosed K]
    (hp : Odd p) (hq : q ≠ 2) (hpq : p.Coprime q) {D : ℤ}
    (hD : D % 4 = 0 ∨ D % 4 = 1) (hDp : IsCoprime D p) (hDq : IsCoprime D q)
    {k n : ℕ} (hk : (k : ℤ) = q - jacobiSym D q)
    (hn : ∀ s : LucasSequenceParams, s.IsCoprime → s.p ^ 2 - 4 * s.q = D →
      IsCoprime s.q (↑(p * q) : ℤ) → (q : ℤ) ∣ lucasU s n) :
    k ∣ n := by
  have hq2 := (Fact.out : q.Prime).two_le
  have h2 : (2 : K) ≠ 0 := two_ne_zero hq
  have hsign := jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp hDq)
  have hk1 : 1 < k := by rcases hsign with h | h <;> omega
  have : NeZero (k : K) := by
    have h := congrArg (fun x : ℤ => (x : K)) hk
    push_cast at h
    rw [CharP.cast_eq_zero K q, zero_sub] at h
    constructor
    rcases hsign with hj | hj <;> simp [h, hj]
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K k
  have hz0 := hz.ne_zero (by omega : k ≠ 0)
  have hz1 := sub_ne_zero.mpr (hz.ne_one hk1)
  obtain ⟨δ, hδ0, hδ, hf⟩ := discriminant_root K hq hDq
  -- Prescribe both the difference δ and the ratio z of the two roots.
  let b := δ / (z - 1)
  let a := z * b
  have hb : b ≠ 0 := div_ne_zero hδ0 hz1
  have ha : a ≠ 0 := mul_ne_zero hz0 hb
  have hab : a - b = δ := by dsimp [a, b]; field_simp
  let F := frobenius K q
  change F δ = _ at hf
  have htrace : F (a + b) = a + b := by
    rcases hsign with hj | hj
    · have hqk : q = k + 1 := by omega
      have hzq : F z = z := by
        change z ^ q = z
        rw [hqk, pow_succ, hz.pow_eq_one, one_mul]
      simp [a, b, map_div₀, hzq, hf, hj]
    · have hkq : k = q + 1 := by omega
      have hzq : F z = z⁻¹ := by
        rw [← one_div]
        apply (eq_div_iff hz0).2
        change z ^ q * z = 1
        rw [← pow_succ, ← hkq, hz.pow_eq_one]
      have hi : z⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hz.ne_one hk1)
      simp only [a, b, map_add, map_mul, map_div₀, map_sub, map_one, hzq, hf, hj,
        Int.cast_neg, Int.cast_one, neg_one_mul]
      field_simp [hi, hz1, hz0, sub_ne_zero.mpr (hz.ne_one hk1).symm]
      ring
  -- The Frobenius-fixed trace lies in the prime field, so it has an integer lift.
  obtain ⟨x, hx⟩ := (mem_bot_iff_intCast q K).mp
    ((Subfield.mem_bot_iff_pow_eq_self K q).mpr htrace)
  have hxD : (x : ZMod q) ^ 2 ≠ D := by
    intro he
    have hh := congrArg (ZMod.castHom (m := q) dvd_rfl K) he
    simp only [map_pow, map_intCast, hx, ← hδ, ← hab] at hh
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h2) ha) hb
    linear_combination hh
  obtain ⟨s, hc, hd, hQ, hs⟩ := lift_trace hp hq hpq hD hDp hDq x hxD
  have hsum : a + b = s.p := by
    have h := congrArg (ZMod.castHom (m := q) dvd_rfl K) hs
    simpa only [map_intCast, hx] using h.symm
  have hprod : a * b = s.q := by
    have he := congrArg (fun y : ℤ => (y : K)) hd
    push_cast at he
    rw [← hsum, ← hδ, ← hab] at he
    have hzero : (2 : K) ^ 2 * (a * b - (s.q : K)) = 0 := by linear_combination he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ h2))
  have hne : a ≠ b := sub_ne_zero.mp (hab ▸ hδ0 : a - b ≠ 0)
  have hzpow := (dvd_lucas_iff s hsum hprod hne hb n).mp (hn s hc hd hQ)
  exact hz.dvd_of_pow_eq_one n (by simpa [a, hb] using hzpow)

end isDCarmichael_mul_iff

open isDCarmichael_mul_iff

namespace threeQR_isDCarmichael_iff

/-- Let $D$ be an integer and let $m$ and $p$ be natural numbers. If $p$ is prime, $m$ is
coprime to $p$, and $mp$ is a $D$-Carmichael number, then
$p - \left(\frac{D}{p}\right)$ divides $m - \left(\frac{D}{m}\right)$ in the integers,
where $\left(\frac{D}{k}\right)$ denotes the Jacobi symbol. -/
lemma cofactor_dvd {m p : ℕ} (hp : p.Prime) (hmp : m.Coprime p) {D : ℤ}
    (h : IsDCarmichael D (m * p)) :
    (p : ℤ) - jacobiSym D p ∣ (m : ℤ) - jacobiSym D m := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hD, hodd, hgt, _, hc, hall⟩ := h
  obtain ⟨hm, ho⟩ := Nat.odd_mul.mp hodd
  have hp₂ : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) ho
  rw [Nat.cast_mul, IsCoprime.mul_right_iff] at hc
  have hsp := jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp hc.2)
  have hsm := jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp hc.1)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hgt
  have hj := jacobiSym.mul_right' D hm0 hp.ne_zero
  let k := ((p : ℤ) - jacobiSym D p).toNat
  let n := ((↑(m * p) : ℤ) - jacobiSym D (m * p)).toNat
  have hk : (k : ℤ) = p - jacobiSym D p := Int.toNat_of_nonneg (by have := hp.two_le; omega)
  have hn : (n : ℤ) = ↑(m * p) - jacobiSym D (m * p) := by
    apply Int.toNat_of_nonneg
    rcases hsm with hs | hs <;> rcases hsp with ht | ht <;> simp [hj, hs, ht] <;> omega
  have hd : k ∣ n := by
    apply local_order_dvd (AlgebraicClosure (ZMod p)) hm hp₂ hmp hD hc.1 hc.2 hk
    intro s hs he hQ
    exact dvd_trans (by exact_mod_cast dvd_mul_left p m) (hall s hs he hQ)
  have hd' : (k : ℤ) ∣ (n : ℤ) := by exact_mod_cast hd
  rw [hk, hn, hj, Nat.cast_mul] at hd'
  have he : (p : ℤ) - jacobiSym D p ∣ ((m : ℤ) - jacobiSym D m) * jacobiSym D p := by
    convert dvd_sub hd' (dvd_mul_left ((p : ℤ) - jacobiSym D p) (m : ℤ)) using 1
    ring
  rcases hsp with hs | hs
  · simpa only [hs, mul_one] using he
  · simpa only [hs, mul_neg_one, dvd_neg] using he

/-- Let $p$ be an odd prime and $D$ an integer coprime to $p$. Let $(P,Q)$ be integer Lucas
parameters with $Q \ne 0$, $P^2 - 4Q = D$, and $Q$ coprime to $p$. For every natural number $n$,
if $p - \left(\frac{D}{p}\right)$ divides $n$, then $p$ divides the Lucas term $U_n(P,Q)$,
where $\left(\frac{D}{p}\right)$ denotes the Jacobi symbol. -/
lemma dvd_lucas_of_local_order_dvd {p n : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2)
    {D : ℤ} (hDp : IsCoprime D p) (s : LucasSequenceParams) (hd : s.p ^ 2 - 4 * s.q = D)
    (hQ : IsCoprime s.q p) (hn : ((p : ℤ) - jacobiSym D p).toNat ∣ n) :
    (p : ℤ) ∣ lucasU s n := by
  have : Fact p.Prime := ⟨hp⟩
  apply prime_dvd_lucas (AlgebraicClosure (ZMod p)) hp₂ hDp s hd hQ _ hn
  have hs := jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp hDp)
  exact Int.toNat_of_nonneg (by have := hp.two_le; omega)

end threeQR_isDCarmichael_iff

open threeQR_isDCarmichael_iff

/-- **Williams' characterization of two-prime $D$-Carmichael numbers.** Let $D$ be an integer
with $D \equiv 0$ or $1 \pmod 4$ and let $p_1 < p_2$ be primes. Then $p_1 p_2$ is a
$D$-Carmichael number if and only if $p_2 = p_1 + 2$, $\left(\frac{D}{p_1}\right) = -1$ and
$\left(\frac{D}{p_2}\right) = 1$, where $\left(\frac{D}{p}\right)$ is the Jacobi symbol.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Proposition 1 (`integers-2026-A102-prop-1`). -/
public theorem isDCarmichael_mul_iff {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {p₁ p₂ : ℕ}
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h12 : p₁ < p₂) :
    IsDCarmichael D (p₁ * p₂) ↔ p₂ = p₁ + 2 ∧ jacobiSym D p₁ = -1 ∧ jacobiSym D p₂ = 1 := by
  have : Fact p₁.Prime := ⟨h₁⟩
  have : Fact p₂.Prime := ⟨h₂⟩
  have hcop := (Nat.coprime_primes h₁ h₂).mpr h12.ne
  have hp := h₁.two_le
  have hq := h₂.two_le
  have hprod := jacobiSym.mul_right' D h₁.ne_zero h₂.ne_zero
  constructor
  · intro h
    have hDc := h.2.2.2.2.1
    rw [Nat.cast_mul, IsCoprime.mul_right_iff] at hDc
    obtain ⟨ho₁, ho₂⟩ := Nat.odd_mul.mp h.2.1
    have hj₁ := jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp hDc.1)
    have hj₂ := jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp hDc.2)
    have hdiv' := cofactor_dvd h₂ hcop h
    have hle := Int.le_of_dvd (by omega : 0 < (p₁ : ℤ) - jacobiSym D p₁) hdiv'
    obtain ⟨u, hu⟩ := ho₁
    obtain ⟨v, hv⟩ := ho₂
    omega
  · rintro ⟨hgap, hj₁, hj₂⟩
    have hp₂ : p₁ ≠ 2 := by
      rintro rfl
      subst p₂
      exact (by decide : ¬ Nat.Prime (2 + 2)) h₂
    have hq₂ : p₂ ≠ 2 := by omega
    have cop {r : ℕ} (hr : r.Prime) (hj : jacobiSym D r ≠ 0) : IsCoprime D r := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      by_contra h
      exact hj (jacobiSym.eq_zero_iff.mpr ⟨hr.ne_zero, h⟩)
    have hc₁ := cop h₁ (by omega : jacobiSym D p₁ ≠ 0)
    have hc₂ := cop h₂ (by omega : jacobiSym D p₂ ≠ 0)
    refine ⟨hD, (h₁.odd_of_ne_two hp₂).mul (h₂.odd_of_ne_two hq₂),
      Nat.one_lt_mul_iff.mpr (by omega), ?_, ?_, ?_⟩
    · simp [Nat.prime_mul_iff, h₁.ne_one, h₂.ne_one]
    · simpa only [Nat.cast_mul] using hc₁.mul_right hc₂
    · intro s _ hd hQ
      rw [Nat.cast_mul, IsCoprime.mul_right_iff] at hQ
      have hn : p₁ + 1 ∣ p₁ * p₂ + 1 := ⟨p₁ + 1, by rw [hgap]; ring⟩
      have he : (↑(p₁ * p₂) - jacobiSym D (p₁ * p₂)).toNat = p₁ * p₂ + 1 := by
        rw [hprod, hj₁, hj₂, mul_one, sub_neg_eq_add]
        rfl
      rw [he, Nat.cast_mul]
      apply hcop.isCoprime.mul_dvd
      · apply prime_dvd_lucas (AlgebraicClosure (ZMod p₁)) hp₂ hc₁ s hd hQ.1 _ hn
        omega
      · apply prime_dvd_lucas (AlgebraicClosure (ZMod p₂)) hq₂ hc₂ s hd hQ.2 _ hn
        omega

end

end MetaMathlibExt
