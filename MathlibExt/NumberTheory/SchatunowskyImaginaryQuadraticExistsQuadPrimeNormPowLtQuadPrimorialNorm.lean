/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SchatunowskyImaginaryQuadratic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Finset.Card

/-!
# Prime norm powers eventually fall below the quadratic primorial

The `n`-th prime norm is at most `4 ^ (n + 1)`, the primorial norm is at least
`(n + 1)!`, and every fixed power of the prime norm eventually falls below the
primorial norm.

Statement-only targets from Hirofumi Nakai, Ken Sasaki and Konoka Yoshida,
*Schatunowsky-type Theorems for Imaginary Quadratic Integer Rings of Class Number One*,
INTEGERS 26 (2026), Article A110.
-/

open NumberField

namespace MetaMathlibExt

namespace exists_quadPrimeNorm_pow_lt_quadPrimorialNorm

/-- The `n`-th element of an infinite set of naturals is at most `B` if the set has
at least `n + 1` elements at most `B`. -/
private theorem nth_le_of_mem_card {p : ℕ → Prop}
    (hinf : (Set.ofPred p).Infinite) (t : Finset ℕ) (B n : ℕ)
    (hmem : ∀ x ∈ t, p x) (hle : ∀ x ∈ t, x ≤ B) (hcard : t.card = n + 1) :
    Nat.nth p n ≤ B := by
  by_contra hlt
  have hB : B < Nat.nth p n := lt_of_not_ge hlt
  have hsub : t ⊆ (Finset.range n).image (Nat.nth p) := by
    intro x hxt
    obtain ⟨k, hk⟩ := Nat.subset_range_nth (hmem x hxt)
    have hkn : k < n :=
      (Nat.nth_lt_nth hinf).mp (by rw [hk]; exact lt_of_le_of_lt (hle x hxt) hB)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hkn, hk⟩
  have h1 := Finset.card_le_card hsub
  have h2 : ((Finset.range n).image (Nat.nth p)).card ≤ n :=
    Finset.card_image_le.trans (by rw [Finset.card_range])
  omega

/-- The `n`-th rational prime is at most `2 ^ (n + 1)`, by Bertrand's postulate. -/
private theorem nth_prime_le_two_pow (n : ℕ) : Nat.nth Nat.Prime n ≤ 2 ^ (n + 1) := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  induction n with
  | zero =>
    rw [Nat.nth_prime_zero_eq_two]
    exact Nat.le_refl _
  | succ n ih =>
    have hnpos : Nat.nth Nat.Prime n ≠ 0 := by
      have h2 := (Nat.nth_mem_of_infinite hinf n).two_le
      omega
    obtain ⟨q, hq, hlt, hle⟩ := Nat.bertrand (Nat.nth Nat.Prime n) hnpos
    have hcount : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
    have hnk : n + 1 ≤ Nat.count Nat.Prime q := by
      have h : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (Nat.count Nat.Prime q) := by
        rw [hcount]
        exact hlt
      have h3 := (Nat.nth_lt_nth hinf).mp h
      omega
    have hle2 : Nat.nth Nat.Prime (n + 1) ≤ q := by
      have h : Nat.nth Nat.Prime (n + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
        (Nat.nth_le_nth hinf).mpr hnk
      rw [hcount] at h
      exact h
    have hexp : (2 : ℕ) * 2 ^ (n + 1) = 2 ^ (n + 1 + 1) := by rw [← pow_succ']
    calc Nat.nth Nat.Prime (n + 1) ≤ q := hle2
      _ ≤ 2 * Nat.nth Nat.Prime n := hle
      _ ≤ 2 * 2 ^ (n + 1) := by omega
      _ = 2 ^ (n + 1 + 1) := hexp

/-- A fixed-base exponential eventually falls below the factorial. -/
private theorem pow_lt_factorial (C : ℕ) (hC : 2 ≤ C) (m : ℕ)
    (hm : C ^ (2 * C - 1) + 2 * C ≤ m) :
    C ^ m < Nat.factorial m := by
  have h2C1 : 2 * C - 1 ≤ m := by omega
  have h1 : (2 * C) ^ (m - (2 * C - 1)) ≤ Nat.factorial m := by
    have hsub : Finset.Ico (2 * C - 1) m ⊆ Finset.range m := by
      intro x hx
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
    calc (2 * C) ^ (m - (2 * C - 1))
        = ∏ _i ∈ Finset.Ico (2 * C - 1) m, (2 * C) := by
          rw [Finset.prod_const, Nat.card_Ico]
      _ ≤ ∏ i ∈ Finset.Ico (2 * C - 1) m, (i + 1) :=
          Finset.prod_le_prod (fun i hi => by
            have h' := (Finset.mem_Ico.mp hi).1
            omega)
      _ ≤ ∏ i ∈ Finset.range m, (i + 1) :=
          Finset.prod_le_prod_of_subset_of_one_le hsub (fun i _ _ => by omega)
      _ = Nat.factorial m := Finset.prod_range_add_one_eq_factorial m
  have hCpow : C ^ m = C ^ (2 * C - 1) * C ^ (m - (2 * C - 1)) := by
    rw [← pow_add, Nat.add_sub_cancel' h2C1]
  have hk : C ^ (2 * C - 1) ≤ m - (2 * C - 1) := by omega
  have h2 : C ^ (2 * C - 1) < 2 ^ (m - (2 * C - 1)) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (pow_le_pow_right₀ (by omega) hk)
  calc C ^ m = C ^ (2 * C - 1) * C ^ (m - (2 * C - 1)) := hCpow
    _ < 2 ^ (m - (2 * C - 1)) * C ^ (m - (2 * C - 1)) :=
        mul_lt_mul_of_pos_right h2 (pow_pos (by omega) _)
    _ = (2 * C) ^ (m - (2 * C - 1)) := (mul_pow 2 C _).symm
    _ ≤ Nat.factorial m := h1

/-- A prime divides every integer above one that divides its square. -/
private theorem prime_dvd_of_dvd_sq {q m : ℕ} (hq : q.Prime) (hdvd : m ∣ q ^ 2)
    (hm : 1 < m) : q ∣ m := by
  obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hrq : r ∣ q := hr.dvd_of_dvd_pow (hrm.trans hdvd)
  have heq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
  rw [← heq]
  exact hrm

/-- Above every rational prime lies a nonzero prime ideal whose norm divides the
square of that prime and exceeds one. -/
private theorem exists_prime_ideal_over {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (p : ℕ) (hp : p.Prime) :
    ∃ Q : Ideal (𝓞 K), Q.IsPrime ∧ Q ≠ ⊥ ∧ Ideal.absNorm Q ∣ p ^ 2 ∧
      1 < Ideal.absNorm Q := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQmax, hQlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := ℤ) (S := 𝓞 K)
      (Ideal.span {(p : ℤ)})
  have hQprime : Q.IsPrime := hQmax.isPrime
  have hmem : ((p : ℕ) : 𝓞 K) ∈ Q := by
    have hQunder : Ideal.span {(p : ℤ)} = Ideal.under ℤ Q :=
      (Ideal.liesOver_iff Q _).mp hQlies
    have h1 : (p : ℤ) ∈ Ideal.under ℤ Q :=
      hQunder ▸ Ideal.mem_span_singleton_self (p : ℤ)
    have h2 : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ Q := Ideal.mem_comap.mp h1
    rw [map_natCast] at h2
    exact h2
  have hle : Ideal.span {((p : ℕ) : 𝓞 K)} ≤ Q :=
    (Ideal.span_singleton_le_iff_mem (I := Q)).mpr hmem
  have hdvd : Ideal.absNorm Q ∣ p ^ 2 := by
    have h1 : Ideal.absNorm Q ∣ Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) :=
      Ideal.absNorm_dvd_absNorm_of_le hle
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hK] at h1
    exact h1
  have hne0 : Ideal.absNorm Q ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
    exact hp2 (zero_dvd_iff.mp hdvd)
  have hQbot : Q ≠ ⊥ := by
    intro hcon
    exact hne0 (Ideal.absNorm_eq_zero_iff.mpr hcon)
  have hgt1 : 1 < Ideal.absNorm Q := by
    have hpos : 0 < Ideal.absNorm Q := Nat.pos_of_ne_zero hne0
    have hne1 : Ideal.absNorm Q ≠ 1 := by
      intro h1
      exact hQprime.ne_top (Ideal.absNorm_eq_one_iff.mp h1)
    omega
  exact ⟨Q, hQprime, hQbot, hdvd, hgt1⟩

/-- The set of absolute norms of nonzero prime ideals of a quadratic number field
is infinite: above every rational prime there is a prime ideal whose norm is a
multiple of that prime. -/
private theorem primeNormSet_infinite {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    (Set.ofPred (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
      Ideal.absNorm P = x)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (B + 1)
  obtain ⟨Q, hQprime, hQbot, hdvd, hgt1⟩ := exists_prime_ideal_over hK p hp
  have hpdvd : p ∣ Ideal.absNorm Q := prime_dvd_of_dvd_sq hp hdvd hgt1
  have hpos : 0 < Ideal.absNorm Q := by omega
  have hle : p ≤ Ideal.absNorm Q := Nat.le_of_dvd hpos hpdvd
  have hmem : Ideal.absNorm Q ∈ Set.ofPred
      (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) :=
    ⟨Q, hQprime, hQbot, rfl⟩
  have hle' := hB hmem
  omega

/-- For `n ≥ 1`, the prime norm `quadPrimeNorm K n` is the `(n - 1)`-st element of the
set of prime ideal norms. -/
private theorem primeNorm_eq_nth {K : Type*} [Field K] [NumberField K] (n : ℕ) :
    quadPrimeNorm K (n + 1) =
      Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) n := by
  simp only [quadPrimeNorm, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]

/-- The `n`-th prime norm is at most `4 ^ (n + 1)`: the first `n + 1` rational
primes give distinct prime ideal norms below the square of the `n`-th prime. -/
private theorem primeNorm_le_four_pow {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (n : ℕ) :
    quadPrimeNorm K (n + 1) ≤ 4 ^ (n + 1) := by
  have hinfS : (Set.ofPred (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
      Ideal.absNorm P = x)).Infinite := primeNormSet_infinite hK
  have hinfP : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hchoice : ∀ q : ℕ, q.Prime → ∃ m : ℕ,
      (∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = m) ∧ m ∣ q ^ 2 ∧
        1 < m := by
    intro q hq
    obtain ⟨Q, hQp, hQb, hdvd, hgt⟩ := exists_prime_ideal_over hK q hq
    exact ⟨Ideal.absNorm Q, ⟨Q, hQp, hQb, rfl⟩, hdvd, hgt⟩
  choose φ hφmem hφdvd hφgt using hchoice
  have hψinj : Function.Injective
      (fun i => φ (Nat.nth Nat.Prime i) (Nat.nth_mem_of_infinite hinfP i)) := by
    intro i₁ i₂ heq
    simp only [] at heq
    have hd1 : Nat.nth Nat.Prime i₁ ∣ φ (Nat.nth Nat.Prime i₁)
        (Nat.nth_mem_of_infinite hinfP i₁) :=
      prime_dvd_of_dvd_sq (Nat.nth_mem_of_infinite hinfP i₁)
        (hφdvd _ _) (hφgt _ _)
    rw [heq] at hd1
    have h1 : Nat.nth Nat.Prime i₁ ∣ Nat.nth Nat.Prime i₂ ^ 2 :=
      hd1.trans (hφdvd _ _)
    have h2 : Nat.nth Nat.Prime i₁ ∣ Nat.nth Nat.Prime i₂ :=
      (Nat.nth_mem_of_infinite hinfP i₁).dvd_of_dvd_pow h1
    have h3 : Nat.nth Nat.Prime i₁ = Nat.nth Nat.Prime i₂ :=
      (Nat.prime_dvd_prime_iff_eq (Nat.nth_mem_of_infinite hinfP i₁)
        (Nat.nth_mem_of_infinite hinfP i₂)).mp h2
    exact Nat.nth_injective hinfP h3
  have hcard : ((Finset.range (n + 1)).image
      (fun i => φ (Nat.nth Nat.Prime i) (Nat.nth_mem_of_infinite hinfP i))).card
      = n + 1 := by
    rw [Finset.card_image_of_injective _ hψinj, Finset.card_range]
  have hmem : ∀ x ∈ (Finset.range (n + 1)).image
      (fun i => φ (Nat.nth Nat.Prime i) (Nat.nth_mem_of_infinite hinfP i)),
      (∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hφmem _ _
  have hle : ∀ x ∈ (Finset.range (n + 1)).image
      (fun i => φ (Nat.nth Nat.Prime i) (Nat.nth_mem_of_infinite hinfP i)),
      x ≤ (Nat.nth Nat.Prime n) ^ 2 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' : i ≤ n := by
      have h := Finset.mem_range.mp hi
      omega
    calc φ (Nat.nth Nat.Prime i) (Nat.nth_mem_of_infinite hinfP i)
          ≤ (Nat.nth Nat.Prime i) ^ 2 :=
            Nat.le_of_dvd (pow_pos (by
              have h2 := (Nat.nth_mem_of_infinite hinfP i).two_le
              omega) _) (hφdvd _ _)
        _ ≤ (Nat.nth Nat.Prime n) ^ 2 :=
            Nat.pow_le_pow_left ((Nat.nth_le_nth hinfP).mpr hi') _
  have hnth := nth_le_of_mem_card hinfS _ _ _ hmem hle hcard
  rw [← primeNorm_eq_nth] at hnth
  have hprime : Nat.nth Nat.Prime n ≤ 2 ^ (n + 1) := nth_prime_le_two_pow n
  have h4 : ((2 ^ (n + 1)) ^ 2) = 4 ^ (n + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, ← pow_mul]
    congr 1
    omega
  calc quadPrimeNorm K (n + 1) ≤ (Nat.nth Nat.Prime n) ^ 2 := hnth
    _ ≤ (2 ^ (n + 1)) ^ 2 := Nat.pow_le_pow_left hprime _
    _ = 4 ^ (n + 1) := h4

/-- The `n`-th prime norm is at least `n + 2`. -/
private theorem primeNorm_ge_add_two {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (n : ℕ) :
    n + 2 ≤ Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
      Ideal.absNorm P = x) n := by
  have hinfS : (Set.ofPred (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
      Ideal.absNorm P = x)).Infinite := primeNormSet_infinite hK
  have h2 : ∀ k : ℕ, 2 ≤ Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
      Ideal.absNorm P = x) k := by
    intro k
    obtain ⟨P, hPprime, hPbot, hPeq⟩ := Nat.nth_mem_of_infinite hinfS k
    have hpos : 0 < Ideal.absNorm P := Nat.pos_of_ne_zero (by
      intro h0
      exact hPbot (Ideal.absNorm_eq_zero_iff.mp h0))
    have hne1 : Ideal.absNorm P ≠ 1 := by
      intro h1
      exact hPprime.ne_top (Ideal.absNorm_eq_one_iff.mp h1)
    omega
  induction n with
  | zero => exact h2 0
  | succ n ih =>
    have hlt : Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
        Ideal.absNorm P = x) n <
        Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
          Ideal.absNorm P = x) (n + 1) :=
      (Nat.nth_lt_nth hinfS).mpr (by omega)
    omega

/-- The primorial norm is at least `(n + 1)!`: it is a product over distinct prime
ideals, one for each of the first `n` prime norms, each at least the next integer. -/
private theorem factorial_le_primorialNorm {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (n : ℕ) :
    Nat.factorial (n + 1) ≤ quadPrimorialNorm K n := by
  classical
  have hinfS : (Set.ofPred (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
      Ideal.absNorm P = x)).Infinite := primeNormSet_infinite hK
  have hchoice : ∀ j : ℕ, ∃ P : Ideal (𝓞 K),
      P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P =
        Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
          Ideal.absNorm P = x) j := by
    intro j
    exact Nat.nth_mem_of_infinite hinfS j
  choose P hPprime hPbot hPnorm using hchoice
  set S : Set (Ideal (𝓞 K)) :=
    {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥ ∧
      Ideal.absNorm P ≤ quadPrimeNorm K n} with hS
  have hSfin : S.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (quadPrimeNorm K n)).subset
      (fun P hP => hP.2.2)
  have hprim : quadPrimorialNorm K n = ∏ P ∈ hSfin.toFinset, Ideal.absNorm P := by
    rw [quadPrimorialNorm, finprod_mem_eq_finite_toFinset_prod _ hSfin]
  have himg_sub : (Finset.range n).image P ⊆ hSfin.toFinset := by
    intro Q hQ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hQ
    rw [hSfin.mem_toFinset]
    refine ⟨hPprime j, hPbot j, ?_⟩
    rw [hPnorm j]
    have hj' : j < n := Finset.mem_range.mp hj
    by_cases hn : n = 0
    · omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [primeNorm_eq_nth]
      apply (Nat.nth_le_nth hinfS).mpr
      have h := Finset.mem_range.mp hj
      omega
  have hPInj : Set.InjOn P (Finset.range n) := by
    intro j₁ _ j₂ _ heq
    have h1 : Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
        Ideal.absNorm P = x) j₁ =
        Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
          Ideal.absNorm P = x) j₂ := by
      rw [← hPnorm j₁, ← hPnorm j₂, heq]
    exact Nat.nth_injective hinfS h1
  have hfacteq : ∀ k : ℕ, Nat.factorial (k + 1) = ∏ j ∈ Finset.range k, (j + 2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : (∏ j ∈ Finset.range (k + 1), (j + 2))
          = (∏ j ∈ Finset.range k, (j + 2)) * (k + 2) :=
        Finset.prod_range_succ (fun j => j + 2) k
      rw [h1, Nat.factorial_succ, ih]
      have e : k + 1 + 1 = k + 2 := by omega
      rw [e]
      exact mul_comm _ _
  calc Nat.factorial (n + 1) = ∏ j ∈ Finset.range n, (j + 2) := hfacteq n
    _ ≤ ∏ j ∈ Finset.range n, Nat.nth (fun x => ∃ P : Ideal (𝓞 K),
          P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) j :=
        Finset.prod_le_prod (fun j _ => primeNorm_ge_add_two hK j)
    _ = ∏ Q ∈ (Finset.range n).image P, Ideal.absNorm Q := by
        rw [Finset.prod_image hPInj]
        apply Finset.prod_congr rfl
        intro j hj
        exact (hPnorm j).symm
    _ ≤ ∏ Q ∈ hSfin.toFinset, Ideal.absNorm Q :=
        Finset.prod_le_prod_of_subset_of_one_le himg_sub (fun Q hQ _ => by
          have hQ' : Q ∈ S := hSfin.mem_toFinset.mp hQ
          have hpos : 0 < Ideal.absNorm Q :=
            Nat.pos_of_ne_zero (fun h0 => hQ'.2.1 (Ideal.absNorm_eq_zero_iff.mp h0))
          omega)
    _ = quadPrimorialNorm K n := hprim.symm

end exists_quadPrimeNorm_pow_lt_quadPrimorialNorm

@[expose] public section

/-- **Prime norm powers eventually fall below the quadratic primorial.** Let $K$ be an imaginary
quadratic field. Put $N(\pi_0) = 1$ and, for $n \ge 1$, let $N(\pi_n)$ be the $n$-th smallest
number that is the norm of a nonzero prime ideal of $\mathcal{O}_K$; let $N(\pi_n\#)$ be the
product of the norms of the nonzero prime ideals of $\mathcal{O}_K$ of norm at most $N(\pi_n)$.
For every natural number $\ell$ there is $n_0$ such that $N(\pi_{n+1})^{\ell+1} < N(\pi_n\#)$
for all $n \ge n_0$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Proposition 4
(`integers-2026-A110-prop-4`). -/
public theorem exists_quadPrimeNorm_pow_lt_quadPrimorialNorm {K : Type*} [Field K]
    [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (ℓ : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n := by
  set C : ℕ := 4 ^ (ℓ + 1) with hC
  have hC4 : 4 ≤ C := by
    rw [hC]
    calc (4 : ℕ) = 4 ^ 1 := (pow_one 4).symm
      _ ≤ 4 ^ (ℓ + 1) := pow_le_pow_right₀ (by omega) (by omega)
  refine ⟨C ^ (2 * C - 1) + 2 * C, fun n hn => ?_⟩
  have hm : C ^ (2 * C - 1) + 2 * C ≤ n + 1 := by omega
  have hfactorial :=
    exists_quadPrimeNorm_pow_lt_quadPrimorialNorm.pow_lt_factorial C (by omega)
      (n + 1) hm
  have hupper := exists_quadPrimeNorm_pow_lt_quadPrimorialNorm.primeNorm_le_four_pow hK n
  have hlower :=
    exists_quadPrimeNorm_pow_lt_quadPrimorialNorm.factorial_le_primorialNorm hK n
  have hexp : (4 ^ (n + 1)) ^ (ℓ + 1) = C ^ (n + 1) := by
    rw [hC, ← pow_mul, ← pow_mul]
    congr 1
    exact mul_comm _ _
  calc quadPrimeNorm K (n + 1) ^ (ℓ + 1)
        ≤ (4 ^ (n + 1)) ^ (ℓ + 1) := Nat.pow_le_pow_left hupper _
      _ = C ^ (n + 1) := hexp
      _ < Nat.factorial (n + 1) := hfactorial
      _ ≤ quadPrimorialNorm K n := hlower

end

end MetaMathlibExt
