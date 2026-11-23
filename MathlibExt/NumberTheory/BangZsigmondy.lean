/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimitiveDivisor
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

@[expose] public section

/-!
# Bang–Zsigmondy theorem

This file proves the general Bang–Zsigmondy existence of a primitive prime divisor
of `a ^ n - b ^ n` (mathematical integer subtraction), with a concrete exceptional-case
predicate. The existing primitive-divisor predicate quantifies over exactly the earlier
positive indices `1 ≤ m < n`.

## Sources

* Gombodorj Bayarmagnai, "A Note on a Theorem of Rotkiewicz,"
  Journal of Integer Sequences 18 (2015),
  <https://cs.uwaterloo.ca/journals/JIS/VOL18/Bayarmagnai/bayar4.tex>.
* Live and bundled source-file SHA-256:
  `45424a5bf963088269996fcf9ada29f1b6d4eb268f44ad29587d86826e91430b`.
* Lines 133–137 invoke the general Zsigmondy theorem in the paper's proof;
  exact newline-terminated span SHA-256:
  `d66cbabd292cc311ee194cf1b6730baa16f07761b0e14105885d72f332a60f53`.
* Lenny Jones, "Variations on a Theme of Sierpiński,"
  Journal of Integer Sequences 10 (2007),
  <https://cs.uwaterloo.ca/journals/JIS/VOL10/Jones/jones67.tex>.
* Live and bundled source-file SHA-256:
  `deef2828ed90318f0eef3881368d4cd22acd58e85274688a556b75e5d7f3d19a`.
* Lines 211–215 state the `b = 1` Bang specialization and both exception families;
  exact newline-terminated span SHA-256:
  `c69c3d5dc542944ece21b7a0d61de6263e5a989f84ff2bd2cc05b1d166160615`.
* Bayarmagnai's brief invocation writes only the sporadic exception and is not itself
  a sound complete statement at exponent two; the formal declaration deliberately restores
  the classical missing family `n = 2` with `a + b` a power of two.
* The positivity/order/coprimality normalization is supported by Bayarmagnai lines 101–103.
* Archive task id: `jis_grounded_502e7a5f72ef9732d2cd2896`.
* G. D. Birkhoff and H. S. Vandiver, *On the integral divisors of aⁿ − bⁿ*,
  Ann. of Math. (2) 5 (1903–1904), 173–180.
-/

namespace MetaMathlibExt

/-- **Exceptional cases of Zsigmondy's theorem.** A triple $(a, b, n)$ of natural numbers is a
Bang–Zsigmondy exceptional case when either $(a, b, n) = (2, 1, 6)$, or $n = 2$ and $a + b = 2^k$
for some natural number $k$. -/
public def IsBangZsigmondyExceptional (a b n : ℕ) : Prop :=
  (a = 2 ∧ b = 1 ∧ n = 6) ∨ (n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k)

/-- The homogenized cyclotomic value `b ^ φ(n) · Φ_n (a / b)`, as an integer. -/
private noncomputable def zsPhi (n a b : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (Nat.totient n + 1),
    (Polynomial.cyclotomic n ℤ).coeff i * (a : ℤ) ^ i * (b : ℤ) ^ (Nat.totient n - i)

/-- The cast of `zsPhi` is `b ^ φ(n)` times the cyclotomic evaluation at `a / b`. -/
private theorem zsPhi_cast {n a b : ℕ} {K : Type*} [Field K] (hb : (b : K) ≠ 0) :
    ((zsPhi n a b : ℤ) : K) = (b : K) ^ Nat.totient n *
      Polynomial.eval ((a : K) / (b : K)) (Polynomial.cyclotomic n K) := by
  unfold zsPhi
  rw [Int.cast_sum, Polynomial.eval_eq_sum_range, Polynomial.natDegree_cyclotomic,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hle : i ≤ Nat.totient n := Nat.lt_succ_iff.mp hi
  have hcoeff : (Polynomial.cyclotomic n K).coeff i =
      (((Polynomial.cyclotomic n ℤ).coeff i : ℤ) : K) := by
    conv_lhs => rw [← Polynomial.map_cyclotomic n (Int.castRingHom K)]
    rw [Polynomial.coeff_map]
    rfl
  rw [hcoeff, div_pow]
  push_cast
  have key : (b : K) ^ Nat.totient n * ((a : K) ^ i / (b : K) ^ i)
      = (a : K) ^ i * (b : K) ^ (Nat.totient n - i) := by
    rw [pow_sub₀ _ hb hle, div_eq_mul_inv]
    ring
  calc ((Polynomial.cyclotomic n ℤ).coeff i : K) * (a : K) ^ i *
        (b : K) ^ (Nat.totient n - i)
      = ((Polynomial.cyclotomic n ℤ).coeff i : K) *
        ((a : K) ^ i * (b : K) ^ (Nat.totient n - i)) := by ring
    _ = ((Polynomial.cyclotomic n ℤ).coeff i : K) *
        ((b : K) ^ Nat.totient n * ((a : K) ^ i / (b : K) ^ i)) := by rw [key]
    _ = (b : K) ^ Nat.totient n *
        (((Polynomial.cyclotomic n ℤ).coeff i : K) * ((a : K) ^ i / (b : K) ^ i)) := by
        ring

/-- Bridge: for `m ≥ 1` with `b ≤ a`, the integer difference is the cast of the
natural-number difference. -/
private theorem zsCastSub {a b m : ℕ} (hle : b ≤ a) :
    ((a ^ m - b ^ m : ℕ) : ℤ) = (a : ℤ) ^ m - (b : ℤ) ^ m := by
  rw [Nat.cast_sub (Nat.pow_le_pow_left hle m), Nat.cast_pow, Nat.cast_pow]

/-- A prime dividing `a ^ m - b ^ m` in ℤ (with `m ≥ 1`) cannot divide `b`. -/
private theorem zsCoprime_notDvdB {a b m p : ℕ} (hp : Nat.Prime p)
    (hcop : Nat.Coprime a b)
    (hdvd : (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m) (hm : 1 ≤ m) : ¬ p ∣ b := by
  intro hpb
  have hpbm : (p : ℤ) ∣ (b : ℤ) ^ m :=
    dvd_pow (Int.natCast_dvd_natCast.mpr hpb) (by omega)
  have hpam : (p : ℤ) ∣ (a : ℤ) ^ m := by
    have h := dvd_add hdvd hpbm
    rwa [sub_add_cancel] at h
  have hpa : p ∣ a ^ m := Int.natCast_dvd_natCast.mp (by simpa using hpam)
  have hpa' : p ∣ a := hp.dvd_of_dvd_pow hpa
  have hgcd : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa' hpb
  have h1 : Nat.gcd a b = 1 := hcop
  rw [h1] at hgcd
  exact hp.not_dvd_one hgcd

/-- A prime dividing `a ^ m - b ^ m` in ℤ (with `m ≥ 1`) cannot divide `a` either,
once it does not divide `b`. -/
private theorem zsCoprime_notDvdA {a b m p : ℕ} (hp : Nat.Prime p)
    (hdvd : (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m) (hm : 1 ≤ m)
    (hpb : ¬ p ∣ b) : ¬ p ∣ a := by
  intro hpa
  have hpam : (p : ℤ) ∣ (a : ℤ) ^ m :=
    dvd_pow (Int.natCast_dvd_natCast.mpr hpa) (by omega)
  have hpbm : (p : ℤ) ∣ (b : ℤ) ^ m := by
    have h : (b : ℤ) ^ m = (a : ℤ) ^ m - ((a : ℤ) ^ m - (b : ℤ) ^ m) := by ring
    rw [h]
    exact dvd_sub hpam hdvd
  have hpbm' : p ∣ b ^ m := Int.natCast_dvd_natCast.mp (by simpa using hpbm)
  exact hpb (hp.dvd_of_dvd_pow hpbm')

/-- `a ^ n - b ^ n` is the product of `zsPhi d a b` over the divisors of `n`. -/
private theorem zsProd {a b n : ℕ} (hn : 1 ≤ n) (hb : 1 ≤ b) :
    (a : ℤ) ^ n - (b : ℤ) ^ n = ∏ d ∈ n.divisors, zsPhi d a b := by
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hpos : 0 < n := hn
  have hpoly := Polynomial.prod_cyclotomic_eq_X_pow_sub_one hpos ℚ
  have heval := congrArg (Polynomial.eval ((a : ℚ) / (b : ℚ))) hpoly
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one] at heval
  have hsum : ∑ d ∈ n.divisors, Nat.totient d = n := Nat.sum_totient n
  have hbn : (b : ℚ) ^ n = ∏ d ∈ n.divisors, (b : ℚ) ^ Nat.totient d := by
    conv_lhs => rw [← hsum]
    rw [Finset.prod_pow_eq_pow_sum]
  have hQ : (a : ℚ) ^ n - (b : ℚ) ^ n
      = ((∏ d ∈ n.divisors, zsPhi d a b : ℤ) : ℚ) := by
    rw [Int.cast_prod]
    simp_rw [zsPhi_cast hbQ]
    rw [Finset.prod_mul_distrib, ← hbn, heval, div_pow, mul_sub,
      mul_div_cancel₀ _ (pow_ne_zero n hbQ), mul_one]
  exact_mod_cast hQ

/-- `zsPhi n a b` is positive for `n ≥ 2` and `a, b ≥ 1`. -/
private theorem zsPhi_pos {n a b : ℕ} (hn : 2 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 < zsPhi n a b := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hcast := zsPhi_cast (n := n) (a := a) (b := b) (K := ℝ) hbR
  have hpos : (0 : ℝ) < ((zsPhi n a b : ℤ) : ℝ) := by
    rw [hcast]
    apply mul_pos
    · exact pow_pos (Nat.cast_pos.mpr hb) _
    · by_cases hn2 : n = 2
      · subst hn2
        rw [Polynomial.cyclotomic_two, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_one]
        have hab : (0 : ℝ) < (a : ℝ) / (b : ℝ) :=
          div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb)
        linarith
      · exact Polynomial.cyclotomic_pos (by omega) _
  exact_mod_cast hpos

/-- For a prime `p ∤ b`, `p ∣ a ^ m - b ^ m` in ℤ iff `c ^ m = 1`
where `c = a * b⁻¹` in `ZMod p`. -/
private theorem zsDvd_iff_order {a b m p : ℕ} [Fact p.Prime] (hpb : ¬ p ∣ b) :
    (p : ℤ) ∣ (a : ℤ) ^ m - (b : ℤ) ^ m ↔
      ((a : ZMod p) * ((b : ZMod p))⁻¹) ^ m = 1 := by
  have hp : Nat.Prime p := Fact.out
  have hb0 : (b : ZMod p) ≠ 0 := fun h => hpb ((ZMod.natCast_eq_zero_iff b p).mp h)
  have hcb : (a : ZMod p) = ((a : ZMod p) * ((b : ZMod p))⁻¹) * (b : ZMod p) := by
    rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  have halg : (a : ZMod p) ^ m - (b : ZMod p) ^ m
      = (b : ZMod p) ^ m * (((a : ZMod p) * ((b : ZMod p))⁻¹) ^ m - 1) := by
    conv_lhs => rw [hcb]
    rw [mul_pow, mul_sub, mul_one, mul_comm ((b : ZMod p) ^ m) _]
  have hpush : ((((a : ℤ) ^ m - (b : ℤ) ^ m : ℤ)) : ZMod p)
      = (a : ZMod p) ^ m - (b : ZMod p) ^ m := by
    push_cast
    ring
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hpush, halg, mul_eq_zero, sub_eq_zero]
  exact ⟨fun h => h.resolve_left (pow_ne_zero m hb0), Or.inr⟩

/-- If `p ∣ zsPhi n a b` with `n = p ^ k * n'` and `p ∤ n'`,
then `orderOf c = n'` where `c = a * b⁻¹` in `ZMod p`. -/
private theorem zsOrder_of_dvd_phi {a b n p k n' : ℕ} [Fact p.Prime]
    (hpb : ¬ p ∣ b) (heq : n = p ^ k * n') (hndvd : ¬ p ∣ n')
    (hdvd : (p : ℤ) ∣ zsPhi n a b) :
    orderOf ((a : ZMod p) * ((b : ZMod p))⁻¹) = n' := by
  have hp : Nat.Prime p := Fact.out
  have hb0 : (b : ZMod p) ≠ 0 := fun h => hpb ((ZMod.natCast_eq_zero_iff b p).mp h)
  have hcast := zsPhi_cast (n := n) (a := a) (b := b) (K := ZMod p) hb0
  have hzero : (((zsPhi n a b : ℤ)) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  rw [hcast, heq] at hzero
  have heval0 : Polynomial.eval ((a : ZMod p) / (b : ZMod p))
      (Polynomial.cyclotomic (p ^ k * n') (ZMod p)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hb0)
  have hroot : Polynomial.IsRoot (Polynomial.cyclotomic (p ^ k * n') (ZMod p))
      ((a : ZMod p) * ((b : ZMod p))⁻¹) := by
    change Polynomial.eval ((a : ZMod p) * ((b : ZMod p))⁻¹) _ = 0
    rw [div_eq_mul_inv] at heval0
    exact heval0
  have : NeZero ((n' : ℕ) : ZMod p) :=
    ⟨fun h => hndvd ((ZMod.natCast_eq_zero_iff n' p).mp h)⟩
  have hprim : IsPrimitiveRoot ((a : ZMod p) * ((b : ZMod p))⁻¹) n' :=
    Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hroot
  exact hprim.eq_orderOf.symm

/-- `orderOf c = n` gives a primitive prime divisor at index `n`. -/
private theorem zsPrimitive_of_order {a b n p : ℕ} [Fact p.Prime]
    (hp : Nat.Prime p) (hpb : ¬ p ∣ b) (hn : 1 ≤ n)
    (hord : orderOf ((a : ZMod p) * ((b : ZMod p))⁻¹) = n) :
    IntegerSequence.IsPrimitivePrimeDivisor
      (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p := by
  refine ⟨hp, hn, hp.two_le, ?_, ?_⟩
  · change (p : ℤ) ∣ (a : ℤ) ^ n - (b : ℤ) ^ n
    rw [zsDvd_iff_order hpb, ← hord, pow_orderOf_eq_one]
  · intro s hs1 hsn hdvd
    have hs : (p : ℤ) ∣ (a : ℤ) ^ s - (b : ℤ) ^ s := hdvd
    rw [zsDvd_iff_order hpb] at hs
    have hds : orderOf ((a : ZMod p) * ((b : ZMod p))⁻¹) ∣ s :=
      orderOf_dvd_iff_pow_eq_one.mpr hs
    rw [hord] at hds
    have hle : n ≤ s := Nat.le_of_dvd (by omega) hds
    omega

/-- If no prime is primitive at index `n` and prime `p ∣ zsPhi n a b`,
then `p ∤ b`, `p ∤ a`, `p ∣ n`, and for `n = p ^ k * n'` with `p ∤ n'`,
we have `k ≥ 1` and `n' ∣ p - 1`. -/
private theorem zsNoPrim_structure {a b n p k n' : ℕ} [Fact p.Prime]
    (hp : Nat.Prime p) (hn : 2 ≤ n)
    (hcop : Nat.Coprime a b) (hb : 1 ≤ b) (_hba : b < a)
    (hno : ∀ q, Nat.Prime q →
      ¬ IntegerSequence.IsPrimitivePrimeDivisor
        (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q)
    (hdvd : (p : ℤ) ∣ zsPhi n a b)
    (heq : n = p ^ k * n') (hndvd : ¬ p ∣ n') :
    ¬ p ∣ b ∧ ¬ p ∣ a ∧ p ∣ n ∧ 1 ≤ k ∧ n' ∣ p - 1 := by
  have h1n : 1 ≤ n := by omega
  have hdvdZ : (p : ℤ) ∣ (a : ℤ) ^ n - (b : ℤ) ^ n := by
    have hmem : zsPhi n a b ∣ (a : ℤ) ^ n - (b : ℤ) ^ n := by
      rw [zsProd h1n hb]
      exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors_self n (by omega))
    exact dvd_trans hdvd hmem
  have hpb : ¬ p ∣ b := zsCoprime_notDvdB hp hcop hdvdZ h1n
  have hpa : ¬ p ∣ a := zsCoprime_notDvdA hp hdvdZ h1n hpb
  have hord : orderOf ((a : ZMod p) * ((b : ZMod p))⁻¹) = n' :=
    zsOrder_of_dvd_phi hpb heq hndvd hdvd
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exfalso
      have hn' : n' = n := by
        rw [pow_zero, one_mul] at heq
        exact heq.symm
      subst hn'
      exact hno p hp (zsPrimitive_of_order hp hpb h1n hord)
    · exact hpos
  have hpn : p ∣ n := by
    rw [heq]
    exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) n'
  have hc0 : ((a : ZMod p) * ((b : ZMod p))⁻¹) ≠ 0 :=
    mul_ne_zero (fun h => hpa ((ZMod.natCast_eq_zero_iff a p).mp h))
      (inv_ne_zero (fun h => hpb ((ZMod.natCast_eq_zero_iff b p).mp h)))
  have hndvd' : n' ∣ p - 1 := by
    rw [← hord]
    exact ZMod.orderOf_dvd_card_sub_one hc0
  exact ⟨hpb, hpa, hpn, hk, hndvd'⟩

/-- Any two primes dividing `zsPhi n a b` are equal when no prime is primitive at index `n`. -/
private theorem zsUnique_prime {a b n p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hn : 2 ≤ n) (hcop : Nat.Coprime a b) (hb : 1 ≤ b) (hba : b < a)
    (hno : ∀ r, Nat.Prime r →
      ¬ IntegerSequence.IsPrimitivePrimeDivisor
        (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n r)
    (hpdvd : (p : ℤ) ∣ zsPhi n a b) (hqdvd : (q : ℤ) ∣ zsPhi n a b) :
    p = q := by
  by_contra hne
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  obtain ⟨kp, np', hnp'dvd, heqp⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
  obtain ⟨kq, nq', hnq'dvd, heqq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) q hq.ne_one
  obtain ⟨-, -, hpn, -, hnp'⟩ :=
    zsNoPrim_structure hp hn hcop hb hba hno hpdvd heqp hnp'dvd
  obtain ⟨-, -, hqn, -, hnq'⟩ :=
    zsNoPrim_structure hq hn hcop hb hba hno hqdvd heqq hnq'dvd
  have hqp : q < p := by
    have hqnp : q ∣ np' := by
      have hqn' : q ∣ p ^ kp * np' := heqp ▸ hqn
      rcases (Nat.Prime.dvd_mul hq).mp hqn' with h | h
      · have hqp' : q ∣ p := hq.dvd_of_dvd_pow h
        have heq' : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp'
        exact absurd heq'.symm hne
      · exact h
    have hqdvd' : q ∣ p - 1 := dvd_trans hqnp hnp'
    have hle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hqdvd'
    omega
  have hpq : p < q := by
    have hpnq : p ∣ nq' := by
      have hpn' : p ∣ q ^ kq * nq' := heqq ▸ hpn
      rcases (Nat.Prime.dvd_mul hp).mp hpn' with h | h
      · have hpq' : p ∣ q := hp.dvd_of_dvd_pow h
        have heq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq'
        exact absurd heq' hne
      · exact h
    have hpdvd' : p ∣ q - 1 := dvd_trans hpnq hnq'
    have hle : p ≤ q - 1 := Nat.le_of_dvd (by omega) hpdvd'
    omega
  omega

/-- `zsPhi n a b * (a ^ N - b ^ N)` divides `a ^ n - b ^ n` in ℤ
when `N ∣ n` and `N < n`. -/
private theorem zsPhi_mul_dvd {a b n N : ℕ} (hn : 1 ≤ n) (hN1 : 1 ≤ N)
    (hb : 1 ≤ b) (hNn : N ∣ n) (hNlt : N < n) :
    zsPhi n a b * ((a : ℤ) ^ N - (b : ℤ) ^ N) ∣ (a : ℤ) ^ n - (b : ℤ) ^ n := by
  have hn0 : n ≠ 0 := by omega
  have hmem_n : n ∈ n.divisors := Nat.mem_divisors_self n hn0
  have hsub : N.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd hn0 hNn
  have hnotmem : n ∉ N.divisors := by
    intro hmem
    have hdvd : n ∣ N := (Nat.mem_divisors.mp hmem).1
    have hle : n ≤ N := Nat.le_of_dvd (by omega) hdvd
    omega
  have hNsub : N.divisors ⊆ n.divisors.erase n := by
    intro d hd
    rw [Finset.mem_erase]
    refine ⟨?_, hsub hd⟩
    intro heq
    rw [heq] at hd
    exact hnotmem hd
  have hproddvd : (∏ d ∈ N.divisors, zsPhi d a b)
      ∣ ∏ d ∈ n.divisors.erase n, zsPhi d a b :=
    Finset.prod_dvd_prod_of_subset _ _ _ hNsub
  have hfac : ∏ d ∈ n.divisors, zsPhi d a b
      = zsPhi n a b * ∏ d ∈ n.divisors.erase n, zsPhi d a b :=
    (Finset.mul_prod_erase _ _ hmem_n).symm
  have hmain : zsPhi n a b * (∏ d ∈ N.divisors, zsPhi d a b)
      ∣ ∏ d ∈ n.divisors, zsPhi d a b := by
    rw [hfac]
    exact mul_dvd_mul_left _ hproddvd
  rw [zsProd hn hb, zsProd hN1 hb]
  exact hmain

/-- Odd `p`: `p ^ 2 ∤ zsPhi n a b` when no prime is primitive at index `n ≥ 3`. -/
private theorem zsVal_odd {a b n p : ℕ} [Fact p.Prime]
    (hp : Nat.Prime p) (hodd : Odd p) (hn : 3 ≤ n)
    (hcop : Nat.Coprime a b) (hb : 1 ≤ b) (hba : b < a)
    (hno : ∀ q, Nat.Prime q →
      ¬ IntegerSequence.IsPrimitivePrimeDivisor
        (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q)
    (hdvd : (p : ℤ) ∣ zsPhi n a b) :
    ¬ (p : ℤ) ^ 2 ∣ zsPhi n a b := by
  obtain ⟨k, n', hndvd, heq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
  obtain ⟨hpb, hpa, -, hk, -⟩ :=
    zsNoPrim_structure hp (by omega) hcop hb hba hno hdvd heq hndvd
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set N : ℕ := p ^ k' * n' with hN
  have hn_eq : n = p * N := by
    rw [heq, hN, pow_succ', mul_assoc]
  have hn'0 : n' ≠ 0 := by
    intro h
    apply (by omega : n ≠ 0)
    rw [heq, h, mul_zero]
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hn'0)
  have hNlt : N < n := by
    have h2 : 2 * N ≤ p * N := by
      rw [mul_comm 2 N, mul_comm p N]
      exact mul_le_mul_right hp.two_le N
    omega
  have hNn : N ∣ n := ⟨p, by rw [mul_comm]; exact hn_eq⟩
  have hdivInt : zsPhi n a b * ((a : ℤ) ^ N - (b : ℤ) ^ N)
      ∣ (a : ℤ) ^ n - (b : ℤ) ^ n :=
    zsPhi_mul_dvd (by omega) hN1 hb hNn hNlt
  have hZpos : 0 < zsPhi n a b := zsPhi_pos (by omega) (by omega) hb
  have hdivNat : (zsPhi n a b).toNat * (a ^ N - b ^ N) ∣ (a ^ n - b ^ n) := by
    have h2 : ((((zsPhi n a b).toNat * (a ^ N - b ^ N) : ℕ)) : ℤ)
        ∣ (((a ^ n - b ^ n : ℕ)) : ℤ) := by
      rw [Nat.cast_mul, Int.toNat_of_nonneg (le_of_lt hZpos),
        zsCastSub (le_of_lt hba), zsCastSub (le_of_lt hba)]
      exact hdivInt
    exact Int.natCast_dvd_natCast.mp h2
  have hZ0 : (zsPhi n a b).toNat ≠ 0 :=
    fun h => not_le_of_gt hZpos (Int.toNat_eq_zero.mp h)
  have hDN0 : a ^ N - b ^ N ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hba (by omega : N ≠ 0))
  have hDn0 : a ^ n - b ^ n ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hba (by omega : n ≠ 0))
  obtain ⟨t, ht⟩ := hdivNat
  have ht0 : t ≠ 0 := by
    intro h
    apply hDn0
    rw [ht, h, mul_zero]
  have hval : padicValNat p (zsPhi n a b).toNat + padicValNat p (a ^ N - b ^ N)
      ≤ padicValNat p (a ^ n - b ^ n) := by
    have e1 : padicValNat p (a ^ n - b ^ n)
        = padicValNat p ((zsPhi n a b).toNat * (a ^ N - b ^ N))
          + padicValNat p t := by
      conv_lhs => rw [ht]
      exact padicValNat.mul (mul_ne_zero hZ0 hDN0) ht0
    have e2 : padicValNat p ((zsPhi n a b).toNat * (a ^ N - b ^ N))
        = padicValNat p (zsPhi n a b).toNat + padicValNat p (a ^ N - b ^ N) :=
      padicValNat.mul hZ0 hDN0
    omega
  have hord : orderOf ((a : ZMod p) * ((b : ZMod p))⁻¹) = n' :=
    zsOrder_of_dvd_phi hpb heq hndvd hdvd
  have hc1 : ((a : ZMod p) * ((b : ZMod p))⁻¹) ^ n' = 1 := by
    rw [← hord, pow_orderOf_eq_one]
  have hyx : b ^ n' < a ^ n' := Nat.pow_lt_pow_left hba hn'0
  have hxy : p ∣ a ^ n' - b ^ n' := by
    have h1 : (p : ℤ) ∣ (a : ℤ) ^ n' - (b : ℤ) ^ n' :=
      (zsDvd_iff_order hpb).mpr hc1
    rw [← zsCastSub (le_of_lt hba)] at h1
    exact Int.natCast_dvd_natCast.mp h1
  have hxp : ¬ p ∣ a ^ n' := fun h => hpa (hp.dvd_of_dvd_pow h)
  have hpow_n : ∀ c : ℕ, c ^ n = (c ^ n') ^ (p ^ (k' + 1)) := fun c => by
    rw [heq, mul_comm (p ^ (k' + 1)) n', pow_mul]
  have hpow_N : ∀ c : ℕ, c ^ N = (c ^ n') ^ (p ^ k') := fun c => by
    rw [hN, mul_comm (p ^ k') n', pow_mul]
  have hpk0 : p ^ (k' + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hpk'0 : p ^ k' ≠ 0 := pow_ne_zero _ hp.ne_zero
  have eDn : a ^ n - b ^ n = (a ^ n') ^ (p ^ (k' + 1)) - (b ^ n') ^ (p ^ (k' + 1)) := by
    rw [hpow_n a, hpow_n b]
  have eDN : a ^ N - b ^ N = (a ^ n') ^ (p ^ k') - (b ^ n') ^ (p ^ k') := by
    rw [hpow_N a, hpow_N b]
  have e1 : padicValNat p ((a ^ n') ^ (p ^ (k' + 1)) - (b ^ n') ^ (p ^ (k' + 1)))
      = padicValNat p (a ^ n' - b ^ n') + (k' + 1) := by
    rw [padicValNat.pow_sub_pow hodd hyx hxy hxp hpk0, padicValNat.prime_pow]
  have e2 : padicValNat p ((a ^ n') ^ (p ^ k') - (b ^ n') ^ (p ^ k'))
      = padicValNat p (a ^ n' - b ^ n') + k' := by
    rw [padicValNat.pow_sub_pow hodd hyx hxy hxp hpk'0, padicValNat.prime_pow]
  rw [eDn, eDN] at hval
  have hvZ : padicValNat p (zsPhi n a b).toNat ≤ 1 := by omega
  intro hsq
  have hsqNat : p ^ 2 ∣ (zsPhi n a b).toNat := by
    have h2 : ((((p ^ 2 : ℕ))) : ℤ) ∣ (((zsPhi n a b).toNat : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg (le_of_lt hZpos)]
      exact hsq
    exact Int.natCast_dvd_natCast.mp h2
  have h2le : 2 ≤ padicValNat p (zsPhi n a b).toNat :=
    (padicValNat_dvd_iff_le hZ0).mp hsqNat
  omega

/-- `p = 2`: `2 ^ 2 ∤ zsPhi n a b` when no prime is primitive at index `n ≥ 3`. -/
private theorem zsVal_two {a b n : ℕ} [Fact (Nat.Prime 2)]
    (hn : 3 ≤ n)
    (hcop : Nat.Coprime a b) (hb : 1 ≤ b) (hba : b < a)
    (hno : ∀ q, Nat.Prime q →
      ¬ IntegerSequence.IsPrimitivePrimeDivisor
        (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q)
    (hdvd : (2 : ℤ) ∣ zsPhi n a b) :
    ¬ (2 : ℤ) ^ 2 ∣ zsPhi n a b := by
  have hp : Nat.Prime 2 := Fact.out
  obtain ⟨k, n', hndvd, heq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 2 hp.ne_one
  obtain ⟨hpb, hpa, -, hk, hn'dvd⟩ :=
    zsNoPrim_structure hp (by omega) hcop hb hba hno hdvd heq hndvd
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hn'1 : n' = 1 := by
    have h1 : n' ∣ 2 - 1 := hn'dvd
    simpa using Nat.dvd_one.mp h1
  set N : ℕ := 2 ^ k' * n' with hN
  have hn_eq : n = 2 * N := by
    rw [heq, hN, pow_succ', mul_assoc]
  have hn_eq2 : n = 2 ^ (k' + 1) := by
    rw [heq, hn'1, mul_one]
  have hN_eq : N = 2 ^ k' := by
    rw [hN, hn'1, mul_one]
  have hk' : 1 ≤ k' := by
    rcases Nat.eq_zero_or_pos k' with rfl | hpos
    · exfalso
      have h2 : (2 : ℕ) ^ (0 + 1) = 2 := by decide
      rw [h2] at hn_eq2
      omega
    · exact hpos
  have hN1 : 1 ≤ N := by
    rw [hN_eq]
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have hNlt : N < n := by omega
  have hNn : N ∣ n := ⟨2, by rw [mul_comm]; exact hn_eq⟩
  have hdivInt : zsPhi n a b * ((a : ℤ) ^ N - (b : ℤ) ^ N)
      ∣ (a : ℤ) ^ n - (b : ℤ) ^ n :=
    zsPhi_mul_dvd (by omega) hN1 hb hNn hNlt
  have hZpos : 0 < zsPhi n a b := zsPhi_pos (by omega) (by omega) hb
  have hdivNat : (zsPhi n a b).toNat * (a ^ N - b ^ N) ∣ (a ^ n - b ^ n) := by
    have h2 : ((((zsPhi n a b).toNat * (a ^ N - b ^ N) : ℕ)) : ℤ)
        ∣ (((a ^ n - b ^ n : ℕ)) : ℤ) := by
      rw [Nat.cast_mul, Int.toNat_of_nonneg (le_of_lt hZpos),
        zsCastSub (le_of_lt hba), zsCastSub (le_of_lt hba)]
      exact hdivInt
    exact Int.natCast_dvd_natCast.mp h2
  have hZ0 : (zsPhi n a b).toNat ≠ 0 :=
    fun h => not_le_of_gt hZpos (Int.toNat_eq_zero.mp h)
  have hDN0 : a ^ N - b ^ N ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hba (by omega : N ≠ 0))
  have hDn0 : a ^ n - b ^ n ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hba (by omega : n ≠ 0))
  obtain ⟨t, ht⟩ := hdivNat
  have ht0 : t ≠ 0 := by
    intro h
    apply hDn0
    rw [ht, h, mul_zero]
  have hval : padicValNat 2 (zsPhi n a b).toNat + padicValNat 2 (a ^ N - b ^ N)
      ≤ padicValNat 2 (a ^ n - b ^ n) := by
    have e1 : padicValNat 2 (a ^ n - b ^ n)
        = padicValNat 2 ((zsPhi n a b).toNat * (a ^ N - b ^ N))
          + padicValNat 2 t := by
      conv_lhs => rw [ht]
      exact padicValNat.mul (mul_ne_zero hZ0 hDN0) ht0
    have e2 : padicValNat 2 ((zsPhi n a b).toNat * (a ^ N - b ^ N))
        = padicValNat 2 (zsPhi n a b).toNat + padicValNat 2 (a ^ N - b ^ N) :=
      padicValNat.mul hZ0 hDN0
    omega
  have hab2 : 2 ∣ a - b := by omega
  have heven_n : Even n := by
    rw [hn_eq2]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : k' + 1 ≠ 0))
  have heven_N : Even N := by
    rw [hN_eq]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : k' ≠ 0))
  have e1 : padicValNat 2 (a ^ n - b ^ n) + 1
      = padicValNat 2 (a + b) + padicValNat 2 (a - b) + padicValNat 2 n :=
    padicValNat.pow_two_sub_pow hba hab2 hpa (by omega : n ≠ 0) heven_n
  have e2 : padicValNat 2 (a ^ N - b ^ N) + 1
      = padicValNat 2 (a + b) + padicValNat 2 (a - b) + padicValNat 2 N :=
    padicValNat.pow_two_sub_pow hba hab2 hpa (by omega : N ≠ 0) heven_N
  have evn : padicValNat 2 n = k' + 1 := by
    rw [hn_eq2]
    exact padicValNat.prime_pow _
  have evN : padicValNat 2 N = k' := by
    rw [hN_eq]
    exact padicValNat.prime_pow _
  have hvZ : padicValNat 2 (zsPhi n a b).toNat ≤ 1 := by omega
  intro hsq
  have hsqNat : 2 ^ 2 ∣ (zsPhi n a b).toNat := by
    have h2 : ((((2 ^ 2 : ℕ))) : ℤ) ∣ (((zsPhi n a b).toNat : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg (le_of_lt hZpos)]
      exact hsq
    exact Int.natCast_dvd_natCast.mp h2
  have h2le : 2 ≤ padicValNat 2 (zsPhi n a b).toNat :=
    (padicValNat_dvd_iff_le hZ0).mp hsqNat
  omega

/-- If no prime is primitive at index `n ≥ 3`, `p ^ 2 ∤ zsPhi n a b`. -/
private theorem zsVal_le_one {a b n p : ℕ} [Fact p.Prime]
    (hp : Nat.Prime p) (hn : 3 ≤ n)
    (hcop : Nat.Coprime a b) (hb : 1 ≤ b) (hba : b < a)
    (hno : ∀ q, Nat.Prime q →
      ¬ IntegerSequence.IsPrimitivePrimeDivisor
        (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q)
    (hdvd : (p : ℤ) ∣ zsPhi n a b) :
    ¬ (p : ℤ) ^ 2 ∣ zsPhi n a b := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact zsVal_two hn hcop hb hba hno hdvd
  · exact zsVal_odd hp hodd hn hcop hb hba hno hdvd

/-- If no prime is primitive at index `n ≥ 3`, `zsPhi n a b = 1` or `= P`
for a prime `P ∣ n`. -/
private theorem zsSmall {a b n : ℕ}
    (hn : 3 ≤ n) (hcop : Nat.Coprime a b) (hb : 1 ≤ b) (hba : b < a)
    (hno : ∀ q, Nat.Prime q →
      ¬ IntegerSequence.IsPrimitivePrimeDivisor
        (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q) :
    zsPhi n a b = 1 ∨ ∃ P, Nat.Prime P ∧ P ∣ n ∧ zsPhi n a b = P := by
  have hZpos : 0 < zsPhi n a b := zsPhi_pos (by omega) (by omega) hb
  set Z : ℕ := (zsPhi n a b).toNat with hZdef
  have hZcast : ((Z : ℕ) : ℤ) = zsPhi n a b :=
    Int.toNat_of_nonneg (le_of_lt hZpos)
  have hZ0 : Z ≠ 0 := fun h => not_le_of_gt hZpos (Int.toNat_eq_zero.mp h)
  by_cases hZ1 : Z = 1
  · left
    rw [hZ1, Nat.cast_one] at hZcast
    exact hZcast.symm
  · obtain ⟨P, hP, hPdvd⟩ := Nat.exists_prime_and_dvd hZ1
    have : Fact (Nat.Prime P) := Fact.mk hP
    have hPZ : (P : ℤ) ∣ zsPhi n a b := by
      have h1 : ((P : ℕ) : ℤ) ∣ ((Z : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr hPdvd
      rwa [hZcast] at h1
    have huniqNat : ∀ {d : ℕ}, Nat.Prime d → d ∣ Z → d = P := by
      intro d hd hdd
      have hddZ : (d : ℤ) ∣ zsPhi n a b := by
        have h1 : ((d : ℕ) : ℤ) ∣ ((Z : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr hdd
        rwa [hZcast] at h1
      have : Fact (Nat.Prime d) := Fact.mk hd
      exact zsUnique_prime hd hP (by omega) hcop hb hba hno hddZ hPZ
    have hpow : Z = P ^ Z.primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hZ0 huniqNat
    have he1 : Z.primeFactorsList.length = 1 := by
      by_contra he'
      have he0 : Z.primeFactorsList.length ≠ 0 := by
        intro h0
        apply hZ1
        rw [hpow, h0, pow_zero]
      have he2 : 2 ≤ Z.primeFactorsList.length := by omega
      have hdvd2 : P ^ 2 ∣ Z := by
        rw [hpow]
        exact pow_dvd_pow P he2
      have hdvd2Z : (P : ℤ) ^ 2 ∣ zsPhi n a b := by
        have h2 : ((((P ^ 2 : ℕ))) : ℤ) ∣ ((Z : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr hdvd2
        push_cast at h2
        rwa [hZcast] at h2
      exact zsVal_le_one hP hn hcop hb hba hno hPZ hdvd2Z
    have hZP : Z = P := by rw [hpow, he1, pow_one]
    right
    obtain ⟨kP, nP', hndvdP, heqP⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) P hP.ne_one
    obtain ⟨-, -, hPn, -, -⟩ :=
      zsNoPrim_structure hP (by omega) hcop hb hba hno hPZ heqP hndvdP
    refine ⟨P, hP, hPn, ?_⟩
    have hcast : ((Z : ℕ) : ℤ) = ((P : ℕ) : ℤ) := by rw [hZP]
    rwa [hZcast] at hcast

/-- Single-factor norm identity: for `‖ζ‖ = 1`,
`‖x - ζ * y‖ ^ 2 = (x - y) ^ 2 + x * y * ‖1 - ζ‖ ^ 2`. -/
private theorem zsNormFactor (x y : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖(x : ℂ) - ζ * (y : ℂ)‖ ^ 2
      = (x - y) ^ 2 + x * y * (‖(1 : ℂ) - ζ‖ ^ 2) := by
  have hnorm : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
    have h2 : ‖ζ‖ ^ 2 = 1 := by rw [hζ, one_pow]
    rwa [Complex.sq_norm, Complex.normSq_apply] at h2
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  linear_combination (y ^ 2 - x * y) * hnorm

/-- `(zsPhi n a b : ℝ) ^ 2` as a product over primitive `n`-th roots. -/
private theorem zsNorm_sq {n a b : ℕ} (hn : 1 ≤ n) (hb : 1 ≤ b) :
    (((zsPhi n a b : ℤ)) : ℝ) ^ 2
      = ∏ ζ ∈ primitiveRoots n ℂ,
        (((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - ζ‖ ^ 2)) := by
  have hn0 : n ≠ 0 := by omega
  have hbC : ((b : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : b ≠ 0)
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) n :=
    Complex.isPrimitiveRoot_exp n hn0
  have hfac := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ
  have hcast := zsPhi_cast (n := n) (a := a) (b := b) (K := ℂ) hbC
  rw [hfac, Polynomial.eval_prod] at hcast
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hcast
  have hcard : (primitiveRoots n ℂ).card = Nat.totient n :=
    Complex.card_primitiveRoots n
  have hprod : ((b : ℂ)) ^ Nat.totient n
        * ∏ μ ∈ primitiveRoots n ℂ, ((a : ℂ) / (b : ℂ) - μ)
      = ∏ μ ∈ primitiveRoots n ℂ, ((a : ℂ) - μ * (b : ℂ)) := by
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro μ _
    rw [mul_sub, mul_div_cancel₀ _ hbC, mul_comm μ (b : ℂ)]
  rw [hprod] at hcast
  have hμ1 : ∀ μ ∈ primitiveRoots n ℂ, ‖μ‖ = 1 := by
    intro μ hμ
    rw [mem_primitiveRoots (by omega)] at hμ
    exact hμ.norm'_eq_one hn0
  have hnorm : ‖(((zsPhi n a b : ℤ)) : ℂ)‖ ^ 2
      = ∏ μ ∈ primitiveRoots n ℂ, ‖(a : ℂ) - μ * (b : ℂ)‖ ^ 2 := by
    rw [hcast, norm_prod, ← Finset.prod_pow]
  have hLHS : ‖(((zsPhi n a b : ℤ)) : ℂ)‖ ^ 2
      = (((zsPhi n a b : ℤ)) : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_intCast]
    ring
  rw [hLHS] at hnorm
  have ea : ((a : ℕ) : ℂ) = ((((a : ℕ) : ℝ)) : ℂ) := by exact_mod_cast rfl
  have eb : ((b : ℕ) : ℂ) = ((((b : ℕ) : ℝ)) : ℂ) := by exact_mod_cast rfl
  have hfac2 : ∀ μ ∈ primitiveRoots n ℂ,
      ‖(a : ℂ) - μ * (b : ℂ)‖ ^ 2
        = (((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2)) := by
    intro μ hμ
    rw [ea, eb]
    exact zsNormFactor _ _ (hμ1 μ hμ)
  exact hnorm.trans (Finset.prod_congr rfl hfac2)

/-- At one: `(eval 1 (cyclotomic n ℝ)) ^ 2` as a product of `‖1 - ζ‖ ^ 2`. -/
private theorem zsNorm_one {n : ℕ} (hn : 1 ≤ n) :
    (Polynomial.eval 1 (Polynomial.cyclotomic n ℝ)) ^ 2
      = ∏ ζ ∈ primitiveRoots n ℂ, (‖(1 : ℂ) - ζ‖ ^ 2) := by
  have h := zsNorm_sq (n := n) (a := 1) (b := 1) hn le_rfl
  have hZ : zsPhi n 1 1 = Polynomial.eval 1 (Polynomial.cyclotomic n ℤ) := by
    have hb1 : ((1 : ℕ) : ℚ) ≠ 0 := by norm_num
    have hcast := zsPhi_cast (n := n) (a := 1) (b := 1) (K := ℚ) hb1
    simp only [Nat.cast_one] at hcast
    have h1 : ((1 : ℚ) / (1 : ℚ)) = 1 := by norm_num
    rw [h1] at hcast
    have hphi : ((1 : ℚ)) ^ Nat.totient n = 1 := one_pow _
    rw [hphi, one_mul] at hcast
    have hmap : Polynomial.eval 1 (Polynomial.cyclotomic n ℚ)
        = (((Polynomial.eval 1 (Polynomial.cyclotomic n ℤ)) : ℤ) : ℚ) := by
      have h := Polynomial.eval_intCast_map (Int.castRingHom ℚ)
        (Polynomial.cyclotomic n ℤ) 1
      simpa [Polynomial.map_cyclotomic] using h
    rw [hmap] at hcast
    exact_mod_cast hcast
  rw [hZ] at h
  have hcast2 : Polynomial.eval 1 (Polynomial.cyclotomic n ℝ)
      = ((((Polynomial.eval 1 (Polynomial.cyclotomic n ℤ)) : ℤ)) : ℝ) := by
    have h := Polynomial.eval_intCast_map (Int.castRingHom ℝ)
      (Polynomial.cyclotomic n ℤ) 1
    simpa [Polynomial.map_cyclotomic] using h
  rw [← hcast2] at h
  simpa using h

/-- If `n = q ^ j` with `q` prime and `j ≥ 1`, and `1 ≤ b < a`,
then `(q : ℤ) < zsPhi n a b`. -/
private theorem zsLower_primePow {n a b q j : ℕ} (hq : Nat.Prime q) (hj : 1 ≤ j)
    (heq : n = q ^ j) (hb : 1 ≤ b) (hba : b < a) :
    (q : ℤ) < zsPhi n a b := by
  have : Fact (Nat.Prime q) := Fact.mk hq
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, (Nat.sub_add_cancel hj).symm⟩
  have hn1 : 1 ≤ n := by
    rw [heq]
    exact one_le_pow₀ hq.one_le
  have hsq := zsNorm_sq (n := n) (a := a) (b := b) hn1 hb
  have heval : Polynomial.eval 1 (Polynomial.cyclotomic n ℝ) = (q : ℝ) := by
    rw [heq]
    exact Polynomial.eval_one_cyclotomic_prime_pow k
  have hqq := zsNorm_one hn1
  rw [heval] at hqq
  have hD : (1 : ℝ) ≤ ((a : ℝ) - (b : ℝ)) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (a : ℝ) - (b : ℝ) := by
      have hba' : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hba
      linarith
    exact one_le_pow₀ h1
  have hab1 : (1 : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
    have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 1 ≤ a)
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (a : ℝ) * (b : ℝ) :=
        mul_le_mul ha1 hb1 (by norm_num) (by linarith)
  have hne : (primitiveRoots n ℂ).Nonempty := by
    have h0 : (0 : ℕ) < n := by omega
    exact ⟨_, (mem_primitiveRoots h0).mpr
      (Complex.isPrimitiveRoot_exp n (by omega))⟩
  obtain ⟨ζ0, hζ0⟩ := hne
  have hSle : ∀ μ ∈ primitiveRoots n ℂ,
      (‖(1 : ℂ) - μ‖ ^ 2)
        ≤ ((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2) := by
    intro μ _
    have hs : (0 : ℝ) ≤ ‖(1 : ℂ) - μ‖ ^ 2 := sq_nonneg _
    nlinarith [hD, hab1, hs]
  have hSlt : (‖(1 : ℂ) - ζ0‖ ^ 2)
      < ((a : ℝ) - (b : ℝ)) ^ 2
        + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - ζ0‖ ^ 2) := by
    have hs : (0 : ℝ) ≤ ‖(1 : ℂ) - ζ0‖ ^ 2 := sq_nonneg _
    nlinarith [hD, hab1, hs]
  have hFpos : ∀ μ ∈ primitiveRoots n ℂ,
      (0 : ℝ) < ((a : ℝ) - (b : ℝ)) ^ 2
        + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2) := by
    intro μ hμ
    have hmul : (0 : ℝ) ≤ (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (sq_nonneg _)
    linarith [hD]
  have hRge : ∏ μ ∈ (primitiveRoots n ℂ).erase ζ0, (‖(1 : ℂ) - μ‖ ^ 2)
      ≤ ∏ μ ∈ (primitiveRoots n ℂ).erase ζ0,
        (((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2)) :=
    Finset.prod_le_prod₀ (fun μ _ => sq_nonneg _)
      (fun μ hμ => hSle μ (Finset.mem_of_mem_erase hμ))
  have hRpos : (0 : ℝ) < ∏ μ ∈ (primitiveRoots n ℂ).erase ζ0,
      (((a : ℝ) - (b : ℝ)) ^ 2
        + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2)) :=
    Finset.prod_pos (fun μ hμ => hFpos μ (Finset.mem_of_mem_erase hμ))
  have hSnn : (0 : ℝ) ≤ ‖(1 : ℂ) - ζ0‖ ^ 2 := sq_nonneg _
  have hsplit : ∏ ζ ∈ primitiveRoots n ℂ,
        (((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - ζ‖ ^ 2))
      = ((((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - ζ0‖ ^ 2))
        * ∏ μ ∈ (primitiveRoots n ℂ).erase ζ0,
          (((a : ℝ) - (b : ℝ)) ^ 2
            + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2))) :=
    (Finset.mul_prod_erase _ _ hζ0).symm
  have hsplitS : ∏ ζ ∈ primitiveRoots n ℂ, (‖(1 : ℂ) - ζ‖ ^ 2)
      = ((‖(1 : ℂ) - ζ0‖ ^ 2)
        * ∏ μ ∈ (primitiveRoots n ℂ).erase ζ0, (‖(1 : ℂ) - μ‖ ^ 2)) :=
    (Finset.mul_prod_erase _ _ hζ0).symm
  have hlt : ∏ ζ ∈ primitiveRoots n ℂ, (‖(1 : ℂ) - ζ‖ ^ 2)
      < ∏ ζ ∈ primitiveRoots n ℂ,
        (((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - ζ‖ ^ 2)) := by
    rw [hsplit, hsplitS]
    have g1 : (‖(1 : ℂ) - ζ0‖ ^ 2)
          * ∏ μ ∈ (primitiveRoots n ℂ).erase ζ0, (‖(1 : ℂ) - μ‖ ^ 2)
        ≤ (‖(1 : ℂ) - ζ0‖ ^ 2)
          * ∏ μ ∈ (primitiveRoots n ℂ).erase ζ0,
            (((a : ℝ) - (b : ℝ)) ^ 2
              + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hRge hSnn
    have g2 : (‖(1 : ℂ) - ζ0‖ ^ 2)
          * ∏ μ ∈ (primitiveRoots n ℂ).erase ζ0,
            (((a : ℝ) - (b : ℝ)) ^ 2
              + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2))
        < ((((a : ℝ) - (b : ℝ)) ^ 2
            + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - ζ0‖ ^ 2))
          * ∏ μ ∈ (primitiveRoots n ℂ).erase ζ0,
            (((a : ℝ) - (b : ℝ)) ^ 2
              + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2))) :=
      mul_lt_mul_of_pos_right hSlt hRpos
    exact lt_of_le_of_lt g1 g2
  have hn2 : 2 ≤ n := by
    have hqdvd : q ∣ n := by
      rw [heq]
      exact dvd_pow_self q (by omega : k + 1 ≠ 0)
    have hle : q ≤ n := Nat.le_of_dvd (by omega) hqdvd
    have hq2 := hq.two_le
    omega
  have hZnn : (0 : ℝ) ≤ ((((zsPhi n a b : ℤ))) : ℝ) := by
    exact_mod_cast le_of_lt (zsPhi_pos hn2 (by omega) hb)
  have h2 : (q : ℝ) ^ 2 < ((((zsPhi n a b : ℤ))) : ℝ) ^ 2 := by
    rw [hsq, hqq]
    exact hlt
  have h1 : (q : ℝ) < ((((zsPhi n a b : ℤ))) : ℝ) :=
    lt_of_pow_lt_pow_left₀ 2 hZnn h2
  exact_mod_cast h1

/-- If `n ≥ 2` is not a prime power and `1 ≤ b < a`,
then `(3 : ℝ) ^ φ(n) ≤ (zsPhi n a b : ℝ) ^ 2`. -/
private theorem zsLower_general {n a b : ℕ} (hn : 2 ≤ n)
    (hnotpp : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ n)
    (hb : 1 ≤ b) (hba : b < a) :
    (3 : ℝ) ^ Nat.totient n ≤ ((((zsPhi n a b : ℤ))) : ℝ) ^ 2 := by
  have hsq := zsNorm_sq (n := n) (a := a) (b := b) (by omega : 1 ≤ n) hb
  have hone := zsNorm_one (n := n) (by omega : 1 ≤ n)
  have heval1 : Polynomial.eval 1 (Polynomial.cyclotomic n ℝ) = 1 :=
    Polynomial.eval_one_cyclotomic_not_prime_pow hnotpp
  rw [heval1] at hone
  have hcard : (primitiveRoots n ℂ).card = Nat.totient n :=
    Complex.card_primitiveRoots n
  have hD : (1 : ℝ) ≤ ((a : ℝ) - (b : ℝ)) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (a : ℝ) - (b : ℝ) := by
      have hba' : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hba
      linarith
    exact one_le_pow₀ h1
  have hab2 : (2 : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
    have ha2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : 2 ≤ a)
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ (a : ℝ) * (b : ℝ) :=
        mul_le_mul ha2 hb1 (by norm_num) (by positivity)
  have hFge : ∀ μ ∈ primitiveRoots n ℂ,
      (1 : ℝ) + 2 * (‖(1 : ℂ) - μ‖ ^ 2)
        ≤ ((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2) := by
    intro μ _
    have hs : (0 : ℝ) ≤ ‖(1 : ℂ) - μ‖ ^ 2 := sq_nonneg _
    nlinarith [hD, hab2, hs]
  have hcube : ∀ μ ∈ primitiveRoots n ℂ,
      (27 : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2) ^ 2
        ≤ (((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2)) ^ 3 := by
    intro μ hμ
    have hs : (0 : ℝ) ≤ ‖(1 : ℂ) - μ‖ ^ 2 := sq_nonneg _
    have hge := hFge μ hμ
    have h1 : (27 : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2) ^ 2
        ≤ ((1 : ℝ) + 2 * (‖(1 : ℂ) - μ‖ ^ 2)) ^ 3 := by
      have hfact : ((1 : ℝ) + 2 * (‖(1 : ℂ) - μ‖ ^ 2)) ^ 3
            - 27 * (‖(1 : ℂ) - μ‖ ^ 2) ^ 2
          = (‖(1 : ℂ) - μ‖ ^ 2 - 1) ^ 2 * (8 * (‖(1 : ℂ) - μ‖ ^ 2) + 1) := by
        ring
      have hnn : (0 : ℝ) ≤ (‖(1 : ℂ) - μ‖ ^ 2 - 1) ^ 2
          * (8 * (‖(1 : ℂ) - μ‖ ^ 2) + 1) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      linarith
    have h2 : ((1 : ℝ) + 2 * (‖(1 : ℂ) - μ‖ ^ 2)) ^ 3
        ≤ (((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hge 3
    linarith
  have hprod : ∏ μ ∈ primitiveRoots n ℂ, ((27 : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2) ^ 2)
      ≤ ∏ μ ∈ primitiveRoots n ℂ,
        ((((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2)) ^ 3) :=
    Finset.prod_le_prod₀
      (fun μ _ => mul_nonneg (by norm_num) (sq_nonneg _))
      (fun μ hμ => hcube μ hμ)
  have hS1 : ∏ μ ∈ primitiveRoots n ℂ, (‖(1 : ℂ) - μ‖ ^ 2) = 1 := by
    rw [← hone]
    norm_num
  have hS2 : ∏ μ ∈ primitiveRoots n ℂ, (‖(1 : ℂ) - μ‖ ^ 2) ^ 2 = 1 := by
    rw [Finset.prod_pow, hS1, one_pow]
  have hA : ∏ μ ∈ primitiveRoots n ℂ, ((27 : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2) ^ 2)
      = (27 : ℝ) ^ Nat.totient n := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, hS2, mul_one]
  have hB : ∏ μ ∈ primitiveRoots n ℂ,
        ((((a : ℝ) - (b : ℝ)) ^ 2
          + (a : ℝ) * (b : ℝ) * (‖(1 : ℂ) - μ‖ ^ 2)) ^ 3)
      = (((((zsPhi n a b : ℤ))) : ℝ) ^ 2) ^ 3 := by
    rw [Finset.prod_pow, ← hsq]
  rw [hA, hB] at hprod
  have h27 : (27 : ℝ) ^ Nat.totient n = ((3 : ℝ) ^ Nat.totient n) ^ 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  rw [h27] at hprod
  exact le_of_pow_le_pow_left₀ (by norm_num) (sq_nonneg _) hprod

/-- `zsPhi 6 a b = a ^ 2 - a * b + b ^ 2` for `1 ≤ b < a`. -/
private theorem zsSix {a b : ℕ} (hb : 1 ≤ b) (hba : b < a) :
    zsPhi 6 a b = (a : ℤ) ^ 2 - (a : ℤ) * (b : ℤ) + (b : ℤ) ^ 2 := by
  have hab : (a : ℤ) - (b : ℤ) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hba.ne')
  have hZ1 : zsPhi 1 a b = (a : ℤ) - (b : ℤ) := by
    have h := zsProd (n := 1) (a := a) (b := b) le_rfl hb
    rw [show Nat.divisors 1 = {1} by decide, Finset.prod_singleton] at h
    simpa [pow_one] using h.symm
  have hZ2 : zsPhi 2 a b = (a : ℤ) + (b : ℤ) := by
    have h := zsProd (n := 2) (a := a) (b := b) (by norm_num) hb
    rw [show Nat.divisors 2 = {1, 2} by decide,
      Finset.prod_pair (by norm_num)] at h
    rw [hZ1] at h
    have e : ((a : ℤ) - (b : ℤ)) * zsPhi 2 a b
        = ((a : ℤ) - (b : ℤ)) * ((a : ℤ) + (b : ℤ)) := by
      rw [← h]
      ring
    exact mul_left_cancel₀ hab e
  have hZ3 : zsPhi 3 a b
      = (a : ℤ) ^ 2 + (a : ℤ) * (b : ℤ) + (b : ℤ) ^ 2 := by
    have h := zsProd (n := 3) (a := a) (b := b) (by norm_num) hb
    rw [show Nat.divisors 3 = {1, 3} by decide,
      Finset.prod_pair (by norm_num)] at h
    rw [hZ1] at h
    have e : ((a : ℤ) - (b : ℤ)) * zsPhi 3 a b
        = ((a : ℤ) - (b : ℤ))
          * ((a : ℤ) ^ 2 + (a : ℤ) * (b : ℤ) + (b : ℤ) ^ 2) := by
      rw [← h]
      ring
    exact mul_left_cancel₀ hab e
  have h6 := zsProd (n := 6) (a := a) (b := b) (by norm_num) hb
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton] at h6
  rw [hZ1, hZ2, hZ3] at h6
  have hab2 : (a : ℤ) + (b : ℤ) ≠ 0 := by
    have h1 : (0 : ℤ) < (a : ℤ) := by exact_mod_cast (by omega : 0 < a)
    have h2 : (0 : ℤ) ≤ (b : ℤ) := by exact_mod_cast Nat.zero_le b
    omega
  have hab3 : (0 : ℤ) < (a : ℤ) ^ 2 + (a : ℤ) * (b : ℤ) + (b : ℤ) ^ 2 := by
    have h1 : (0 : ℤ) < (a : ℤ) := by exact_mod_cast (by omega : 0 < a)
    have h2 : (0 : ℤ) ≤ (a : ℤ) * (b : ℤ) :=
      mul_nonneg (le_of_lt h1) (by exact_mod_cast Nat.zero_le b)
    have h3 : (0 : ℤ) ≤ (b : ℤ) ^ 2 := sq_nonneg _
    have h4 : (0 : ℤ) < (a : ℤ) ^ 2 := pow_pos h1 2
    linarith
  have e : ((a : ℤ) - (b : ℤ))
        * (((a : ℤ) + (b : ℤ))
          * (((a : ℤ) ^ 2 + (a : ℤ) * (b : ℤ) + (b : ℤ) ^ 2) * zsPhi 6 a b))
      = ((a : ℤ) - (b : ℤ))
        * (((a : ℤ) + (b : ℤ))
          * (((a : ℤ) ^ 2 + (a : ℤ) * (b : ℤ) + (b : ℤ) ^ 2)
            * ((a : ℤ) ^ 2 - (a : ℤ) * (b : ℤ) + (b : ℤ) ^ 2))) := by
    rw [← h6]
    ring
  have e1 := mul_left_cancel₀ hab e
  have e2 := mul_left_cancel₀ hab2 e1
  exact mul_left_cancel₀ (ne_of_gt hab3) e2

/-- Auxiliary: `m ^ 2 < 3 ^ (m - 1)` for `5 ≤ m`. -/
private theorem zsPow3 {m : ℕ} (hm : 5 ≤ m) : m ^ 2 < 3 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have e1 : n + 1 - 1 = n := by omega
    rw [e1]
    have h4 : (n + 1) ^ 2 < 3 * n ^ 2 := by
      have e1 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      have e2 : 3 * n ^ 2 = n ^ 2 + n ^ 2 + n ^ 2 := by ring
      have en : n ^ 2 = n * n := by ring
      have gnn : 5 * n ≤ n * n := by gcongr
      omega
    calc (n + 1) ^ 2 < 3 * n ^ 2 := h4
      _ ≤ 3 * 3 ^ (n - 1) :=
        mul_le_mul_of_nonneg_left (le_of_lt ih) (by norm_num)
      _ = 3 ^ n := by
        conv_rhs => rw [show n = (n - 1) + 1 from by omega, pow_succ']

/-- If `n = n' * P ^ k` with `P` prime, `k ≥ 1`, `n' ≥ 2`, `n' ∣ P - 1`,
and `n ≠ 6`, then `3 ^ φ(n) > P ^ 2`. -/
private theorem zsTotient_big {n n' P k : ℕ} (hP : Nat.Prime P) (hk : 1 ≤ k)
    (hn' : 2 ≤ n') (hdvd : n' ∣ P - 1) (heq : n = n' * P ^ k) (hn6 : n ≠ 6) :
    P ^ 2 < 3 ^ Nat.totient n := by
  have hP2 := hP.two_le
  have hPndvd : ¬ P ∣ n' := by
    intro h
    have hle : P ≤ n' := Nat.le_of_dvd (by omega) h
    have hle2 : n' ≤ P - 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  have hcopP : Nat.Coprime P n' := hP.coprime_iff_not_dvd.mpr hPndvd
  have hcop : Nat.Coprime n' (P ^ k) := by
    rw [Nat.coprime_comm, Nat.coprime_pow_left_iff (by omega) P n']
    exact hcopP
  have hphi : Nat.totient n
      = Nat.totient n' * (P ^ (k - 1) * (P - 1)) := by
    rw [heq, Nat.totient_mul hcop, Nat.totient_prime_pow hP (by omega : 0 < k)]
  have hP3 : 3 ≤ P := by
    have hle : n' ≤ P - 1 := Nat.le_of_dvd (by omega) hdvd
    omega
  by_cases hP5 : 5 ≤ P
  · have hphi_ge : P - 1 ≤ Nat.totient n := by
      rw [hphi]
      have hA : 1 ≤ Nat.totient n' * P ^ (k - 1) :=
        Nat.mul_le_mul (Nat.totient_pos.mpr (by omega))
          (one_le_pow₀ (by omega : 1 ≤ P))
      calc P - 1 = 1 * (P - 1) := (one_mul _).symm
        _ ≤ (Nat.totient n' * P ^ (k - 1)) * (P - 1) :=
          Nat.mul_le_mul hA le_rfl
        _ = Nat.totient n' * (P ^ (k - 1) * (P - 1)) := by ring
    have h3 : P ^ 2 < 3 ^ (P - 1) := zsPow3 hP5
    have h4 : (3 : ℕ) ^ (P - 1) ≤ 3 ^ Nat.totient n :=
      pow_le_pow_right₀ (by norm_num) hphi_ge
    omega
  · have hPlt : P < 5 := by omega
    have hPeq : P = 3 := by
      interval_cases P
      · rfl
      · exact absurd hP (by norm_num)
    subst hPeq
    have hn'2 : n' = 2 := by
      have h : n' ∣ 3 - 1 := hdvd
      have h2 : n' ∣ 2 := by simpa using h
      have hle : n' ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      omega
    have hk1 : k ≠ 1 := by
      intro hkk
      apply hn6
      rw [heq, hn'2, hkk]
      norm_num
    have hk2 : 2 ≤ k := by omega
    have hphi2 : Nat.totient n = 3 ^ (k - 1) * 2 := by
      rw [hphi, hn'2, show Nat.totient 2 = 1 by decide,
        show (3 : ℕ) - 1 = 2 by norm_num, one_mul]
    have hphi6 : 6 ≤ Nat.totient n := by
      rw [hphi2]
      have h3 : 3 ≤ 3 ^ (k - 1) := by
        calc (3 : ℕ) = 3 ^ 1 := (pow_one _).symm
          _ ≤ 3 ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    have hfin : (3 : ℕ) ^ 6 ≤ 3 ^ Nat.totient n :=
      pow_le_pow_right₀ (by norm_num) hphi6
    have e36 : (3 : ℕ) ^ 6 = 729 := by norm_num
    have e32 : (3 : ℕ) ^ 2 = 9 := by norm_num
    rw [e36] at hfin
    rw [e32]
    omega

/-- Assembly, case `n = 2`: an odd prime factor of `a + b` is primitive. -/
private theorem zsCaseTwo {a b : ℕ}
    (hcop : Nat.Coprime a b) (h2pow : ¬ ∃ k : ℕ, a + b = 2 ^ k) :
    ∃ p, IntegerSequence.IsPrimitivePrimeDivisor
      (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) 2 p := by
  obtain ⟨p, hp, hpdvd, hodd⟩ : ∃ p, Nat.Prime p ∧ p ∣ a + b ∧ Odd p := by
    by_contra hcon
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (a + b) with h | h
    · exact h2pow h
    · obtain ⟨q, hq, hqdvd, hoddq⟩ := h
      exact hcon ⟨q, hq, hqdvd, hoddq⟩
  have : Fact (Nat.Prime p) := Fact.mk hp
  have h1 : (p : ℤ) ∣ (a : ℤ) + (b : ℤ) := by
    have h0 : (p : ℤ) ∣ ((((a + b : ℕ))) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hpdvd
    have e : ((((a + b : ℕ))) : ℤ) = (a : ℤ) + (b : ℤ) := by simp
    rwa [e] at h0
  refine ⟨p, hp, (by omega : 1 ≤ 2), hp.two_le, ?_, ?_⟩
  · change (p : ℤ) ∣ (a : ℤ) ^ 2 - (b : ℤ) ^ 2
    have h3 : (a : ℤ) ^ 2 - (b : ℤ) ^ 2
        = ((a : ℤ) - (b : ℤ)) * ((a : ℤ) + (b : ℤ)) := by ring
    rw [h3]
    exact dvd_mul_of_dvd_right h1 _
  · intro s hs1 hsn hdvd
    have hs1' : s = 1 := by omega
    subst hs1'
    change (p : ℤ) ∣ (a : ℤ) ^ 1 - (b : ℤ) ^ 1 at hdvd
    simp only [pow_one] at hdvd
    have h2a : (p : ℤ) ∣ 2 * (a : ℤ) := by
      have h := dvd_add h1 hdvd
      have e : ((a : ℤ) + (b : ℤ)) + ((a : ℤ) - (b : ℤ)) = 2 * (a : ℤ) := by
        ring
      rwa [e] at h
    have h2b : (p : ℤ) ∣ 2 * (b : ℤ) := by
      have h := dvd_sub h1 hdvd
      have e : ((a : ℤ) + (b : ℤ)) - ((a : ℤ) - (b : ℤ)) = 2 * (b : ℤ) := by
        ring
      rwa [e] at h
    have hpa : p ∣ a := by
      have e : ((((2 * a : ℕ))) : ℤ) = 2 * (a : ℤ) := by simp
      have h0 : (p : ℤ) ∣ ((((2 * a : ℕ))) : ℤ) := by
        rw [e]
        exact h2a
      have h1n : p ∣ 2 * a := Int.natCast_dvd_natCast.mp h0
      rcases (Nat.Prime.dvd_mul hp).mp h1n with h | h
      · have h2eq : p = 2 := by
          have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
          have h2l := hp.two_le
          omega
        subst h2eq
        exact absurd hodd (by norm_num)
      · exact h
    have hpb : p ∣ b := by
      have e : ((((2 * b : ℕ))) : ℤ) = 2 * (b : ℤ) := by simp
      have h0 : (p : ℤ) ∣ ((((2 * b : ℕ))) : ℤ) := by
        rw [e]
        exact h2b
      have h1n : p ∣ 2 * b := Int.natCast_dvd_natCast.mp h0
      rcases (Nat.Prime.dvd_mul hp).mp h1n with h | h
      · have h2eq : p = 2 := by
          have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
          have h2l := hp.two_le
          omega
        subst h2eq
        exact absurd hodd (by norm_num)
      · exact h
    have hgcd : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
    have h1c : Nat.gcd a b = 1 := hcop
    rw [h1c] at hgcd
    have hpeq1 : p = 1 := Nat.dvd_one.mp hgcd
    have hpt := hp.two_le
    omega

/-- Assembly, `n = 6` subcase: `zsPhi 6 a b = P` with prime `P ∣ 6`
contradicts `(a, b) ≠ (2, 1)`. -/
private theorem zsSixContra {a b P : ℕ} (hP : Nat.Prime P)
    (hb : 1 ≤ b) (hba : b < a)
    (hab21 : ¬ (a = 2 ∧ b = 1))
    (hPn : P ∣ 6) (hPv : zsPhi 6 a b = (P : ℤ)) :
    False := by
  have h6v := zsSix hb hba
  have hPval : (P : ℤ) = ((a : ℤ) - (b : ℤ)) ^ 2 + (a : ℤ) * (b : ℤ) := by
    rw [← hPv, h6v]
    ring
  have hab_ge : (2 : ℤ) ≤ (a : ℤ) * (b : ℤ) := by
    have ha2 : (2 : ℤ) ≤ (a : ℤ) := by exact_mod_cast (by omega : 2 ≤ a)
    have hb1 : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    calc (2 : ℤ) = 2 * 1 := by ring
      _ ≤ _ := mul_le_mul ha2 hb1 (by norm_num) (by linarith)
  have hd_ge : (1 : ℤ) ≤ ((a : ℤ) - (b : ℤ)) ^ 2 := by
    have h1 : (1 : ℤ) ≤ (a : ℤ) - (b : ℤ) := by
      have hba' : (b : ℤ) + 1 ≤ (a : ℤ) := by exact_mod_cast hba
      linarith
    exact one_le_pow₀ h1
  have hP23 : P = 2 ∨ P = 3 := by
    have h26 : (6 : ℕ) = 2 * 3 := by norm_num
    rw [h26] at hPn
    rcases (Nat.Prime.dvd_mul hP).mp hPn with h | h
    · left
      exact (Nat.prime_dvd_prime_iff_eq hP Nat.prime_two).mp h
    · right
      exact (Nat.prime_dvd_prime_iff_eq hP Nat.prime_three).mp h
  have hP3 : P = 3 := by
    rcases hP23 with h | h
    · subst h
      norm_num at hPval
      linarith
    · exact h
  subst hP3
  norm_num at hPval
  have hab2eq : (a : ℤ) * (b : ℤ) = 2 := by linarith
  have hab_nat : a * b = 2 := by exact_mod_cast hab2eq
  have hb1eq : b = 1 := by
    have hbdvd : b ∣ 2 := ⟨a, by rw [mul_comm b a, hab_nat]⟩
    have hle : b ≤ 2 := Nat.le_of_dvd (by norm_num) hbdvd
    interval_cases b
    · rfl
    · have ha1 : a = 1 := by omega
      omega
  have ha2eq : a = 2 := by
    rw [hb1eq, mul_one] at hab_nat
    exact hab_nat
  exact hab21 ⟨ha2eq, hb1eq⟩

/-- **Zsigmondy's theorem.** Let $a$, $b$ and $n$ be natural numbers with $0 < b < a$, $a$ and $b$
coprime, and $n \ge 2$, and suppose that $(a, b, n)$ is not a Bang–Zsigmondy exceptional case:
neither $(a, b, n) = (2, 1, 6)$, nor $n = 2$ with $a + b$ a power of two. Then $a^n - b^n$ has a
primitive prime divisor, that is, a prime $p$ that divides $a^n - b^n$ and divides no $a^m - b^m$
with $1 \le m < n$.

Proves `Wanted` entry `bangZsigmondy_exists_primitivePrimeDivisor`.

Source: Bayarmagnai lines 133–137 invoke the general theorem, with the explicit
exception families per Jones Theorem `Bang` lines 211–215. -/
public theorem bangZsigmondy_exists_primitivePrimeDivisor {a b n : ℕ}
    (hbpos : 0 < b) (hba : b < a) (hcop : Nat.Coprime a b)
    (hn : 2 ≤ n) (hnexc : ¬ IsBangZsigmondyExceptional a b n) :
    ∃ p, IntegerSequence.IsPrimitivePrimeDivisor
      (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n p := by
  have hb : 1 ≤ b := hbpos
  have hne6 : ¬ (a = 2 ∧ b = 1 ∧ n = 6) := fun h => hnexc (Or.inl h)
  have hne2 : ¬ (n = 2 ∧ ∃ k : ℕ, a + b = 2 ^ k) := fun h => hnexc (Or.inr h)
  by_cases hn2 : n = 2
  · subst hn2
    have h2pow : ¬ ∃ k : ℕ, a + b = 2 ^ k := fun h => hne2 ⟨rfl, h⟩
    exact zsCaseTwo hcop h2pow
  · have hn3 : 3 ≤ n := by omega
    by_contra hcon
    have hno : ∀ q, Nat.Prime q →
        ¬ IntegerSequence.IsPrimitivePrimeDivisor
          (fun m => (a : ℤ) ^ m - (b : ℤ) ^ m) n q := fun q _ h => hcon ⟨q, h⟩
    by_cases hpp : ∃ q j, Nat.Prime q ∧ 1 ≤ j ∧ n = q ^ j
    · obtain ⟨q, j, hq, hj, heqq⟩ := hpp
      have hlt := zsLower_primePow hq hj heqq hb hba
      rcases zsSmall hn3 hcop hb hba hno with h1 | ⟨P, hP, hPn, hPv⟩
      · rw [h1] at hlt
        have hq2 : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.two_le
        omega
      · rw [hPv] at hlt
        rw [heqq] at hPn
        have hPq' : P ∣ q := hP.dvd_of_dvd_pow hPn
        have heqPQ : P = q := (Nat.prime_dvd_prime_iff_eq hP hq).mp hPq'
        rw [heqPQ] at hlt
        exact lt_irrefl _ hlt
    · have hnotpp : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ n := by
        intro p hp k hconk
        have hk1 : 1 ≤ k := by
          by_contra hk0
          have hk00 : k = 0 := by omega
          subst hk00
          rw [pow_zero] at hconk
          omega
        apply hpp
        exact ⟨p, k, hp, hk1, hconk.symm⟩
      rcases zsSmall hn3 hcop hb hba hno with h1 | ⟨P, hP, hPn, hPv⟩
      · have h13 := zsLower_general hn hnotpp hb hba
        rw [h1] at h13
        simp only [Int.cast_one, one_pow] at h13
        have hphi1 : 1 ≤ Nat.totient n := Nat.totient_pos.mpr (by omega)
        have h3 : (3 : ℝ) ≤ 3 ^ Nat.totient n := by
          calc (3 : ℝ) = 3 ^ 1 := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) hphi1
        linarith
      · have : Fact (Nat.Prime P) := Fact.mk hP
        have hPZdvd : (P : ℤ) ∣ zsPhi n a b := by
          rw [hPv]
        obtain ⟨kP, nP', hndvdP, heqP⟩ :=
          Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) P hP.ne_one
        obtain ⟨-, -, -, hkP, hnP'dvd⟩ :=
          zsNoPrim_structure hP (by omega) hcop hb hba hno hPZdvd heqP hndvdP
        have heqP' : n = nP' * P ^ kP := by
          rw [heqP]
          ring
        have hnP'2 : 2 ≤ nP' := by
          by_contra hcon2
          have hnP'0 : nP' ≠ 0 := by
            intro h
            apply (by omega : n ≠ 0)
            rw [heqP, h, mul_zero]
          have hnP'1 : nP' = 1 := by omega
          apply hpp
          refine ⟨P, kP, hP, hkP, ?_⟩
          rw [heqP, hnP'1, mul_one]
        by_cases hn6 : n = 6
        · subst hn6
          have hab21 : ¬ (a = 2 ∧ b = 1) := fun h => hne6 ⟨h.1, h.2, rfl⟩
          exact zsSixContra hP hb hba hab21 hPn hPv
        · have h13 := zsLower_general hn hnotpp hb hba
          have h15 := zsTotient_big hP hkP hnP'2 hnP'dvd heqP' hn6
          have hPvR : ((((zsPhi n a b : ℤ))) : ℝ) = (P : ℝ) := by
            rw [hPv]
            norm_cast
          rw [hPvR] at h13
          have h15R : (P : ℝ) ^ 2 < 3 ^ Nat.totient n := by
            exact_mod_cast h15
          linarith

end MetaMathlibExt
