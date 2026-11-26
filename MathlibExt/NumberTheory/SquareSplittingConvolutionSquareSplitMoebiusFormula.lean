/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareSplittingConvolution
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import MathlibExt.NumberTheory.SquareSplittingConvolution.DivisorProperties
import MathlibExt.NumberTheory.SquareSplittingConvolution.MoebiusInversion
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Möbius function of the square-splitting convolution

The inverse of the constant-one function under the square-splitting convolution is the
product of the classical Möbius function evaluated at the squarefree and square-root parts,
with its values at prime powers and its Euler product `1 / (ζ(s) * ζ(2 * s))`.
-/

namespace MetaMathlibExt
namespace squareSplitMoebius_proof

/-- Coordinates of `u * v ^ 2` with `u` squarefree split back into `u` and `v`. -/
private theorem split_coords {u v : ℕ} (hu : Squarefree u) (hv : v ≠ 0) :
    squareSplitU (u * v ^ 2) = u ∧ squareSplitV (u * v ^ 2) = v := by
  have hn := mul_ne_zero hu.ne_zero (pow_ne_zero 2 hv)
  have hroot : Nat.floorRoot 2 (u * v ^ 2) = v := by
    apply Nat.eq_of_factorization_eq (Nat.floorRoot_ne_zero.mpr ⟨by decide, hn⟩) hv
    intro p
    rw [Nat.factorization_floorRoot, Finsupp.floorDiv_apply, Nat.factorization_mul hu.ne_zero
      (pow_ne_zero 2 hv), Nat.factorization_pow]
    change (u.factorization p + 2 * v.factorization p) / 2 = v.factorization p
    have := hu.natFactorization_le_one p
    omega
  have hV : squareSplitV (u * v ^ 2) = v := by
    simpa [Nat.floorRoot, hn, squareSplitV] using hroot
  have h := squareSplitU_mul_squareSplitV_sq hn
  rw [hV] at h
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (pow_ne_zero 2 hv)) h, hV⟩

/-- The squarefree part of a positive integer is squarefree. -/
private theorem squarefree_U {n : ℕ} (hn : n ≠ 0) : Squarefree (squareSplitU n) := by
  obtain ⟨a, b, _, hb, h, ha⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  rw [mul_comm] at h
  rw [← h, (split_coords ha hb.ne').1]
  exact ha

/-- The square-splitting coordinates of a prime power. -/
private theorem UV_prime_pow {p k : ℕ} (hp : p.Prime) :
    squareSplitU (p ^ k) = p ^ (k % 2) ∧ squareSplitV (p ^ k) = p ^ (k / 2) := by
  simp only [squareSplitU, squareSplitV, hp.factorization_pow]
  exact ⟨Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)⟩

/-- The square-splitting coordinates multiply across coprime inputs. -/
private theorem UV_mul {m n : ℕ} (h : m.Coprime n) :
    squareSplitU (m * n) = squareSplitU m * squareSplitU n ∧
      squareSplitV (m * n) = squareSplitV m * squareSplitV n := by
  have prod_mul (F : ℕ → ℕ → ℕ) :
      (m * n).factorization.prod F = m.factorization.prod F * n.factorization.prod F := by
    rw [Nat.factorization_mul_of_coprime h]
    exact Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors F
  simp only [squareSplitU, squareSplitV]
  exact ⟨prod_mul _, prod_mul _⟩

/-- The square-splitting coordinates divide the input. -/
private theorem UV_dvd (n : ℕ) : squareSplitU n ∣ n ∧ squareSplitV n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [squareSplitU, squareSplitV, Nat.factorization_zero, Finsupp.prod_zero_index]
    exact ⟨dvd_zero _, dvd_zero _⟩
  · have h := squareSplitU_mul_squareSplitV_sq hn
    exact ⟨⟨squareSplitV n ^ 2, h.symm⟩,
      ⟨squareSplitU n * squareSplitV n, h.symm.trans (by ring)⟩⟩

/-- The divisor sum of the Möbius function is the arithmetic identity. -/
private theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℂ) =
      (1 : ArithmeticFunction ℂ) n := by
  have h := DFunLike.congr_fun (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ)) n
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b =>
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) a *
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) b)] at h
  rw [← h]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hd0, Nat.cast_one,
    ArithmeticFunction.intCoe_apply, one_mul]

/-- The candidate Möbius function: the product of the classical Möbius values on the two
square-splitting coordinates. -/
private noncomputable def moebiusStar : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
    ArithmeticFunction.moebius (squareSplitV n), by simp⟩

/-- Values of the candidate Möbius function. -/
private theorem moebiusStar_apply (n : ℕ) : moebiusStar n = if n = 0 then 0 else
    (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n) := rfl

/-- The square-splitting convolution vanishes at zero. -/
private theorem squareSplitConv_zero (f g : ArithmeticFunction ℂ) :
    squareSplitConv f g 0 = 0 := rfl

/-- The constant-one function square-splitting-convolved with the candidate Möbius function is
the identity. -/
private theorem zeta_conv_moebiusStar :
    squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) moebiusStar = 1 := by
  apply ArithmeticFunction.ext
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [squareSplitConv_zero, ArithmeticFunction.one_apply_ne (by norm_num)]
  · have hUV := squareSplitU_mul_squareSplitV_sq hn
    have hV0 : squareSplitV n ≠ 0 := fun h => hn (by rw [← hUV, h]; simp)
    have hUsq : Squarefree (squareSplitU n) := squarefree_U hn
    have hprops := squareSplitDivisors_properties.1 n hn
    rw [squareSplitConv_apply _ _ hn]
    have hsimp : ∀ d ∈ squareSplitDivisors n,
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) d * moebiusStar (n / d) =
          (ArithmeticFunction.moebius (squareSplitU (n / d)) : ℂ) *
            ArithmeticFunction.moebius (squareSplitV (n / d)) := by
      intro d hd
      have hdvd := hprops.2.2 d hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn)
      have hnd0 : n / d ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hdpos).ne'
      rw [moebiusStar_apply, ite_eq_right hnd0, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne hdpos.ne', Nat.cast_one, one_mul]
    refine (Finset.sum_congr rfl hsimp).trans ?_
    have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2 ^ 2)
        ↑((squareSplitU n).divisors ×ˢ (squareSplitV n).divisors) := by
      rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ h
      obtain ⟨ha₁, hb₁⟩ := Finset.mem_product.mp h₁
      obtain ⟨ha₂, hb₂⟩ := Finset.mem_product.mp h₂
      have H₁ := split_coords
        (Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha₁) hUsq)
        (Nat.pos_of_mem_divisors hb₁).ne'
      have H₂ := split_coords
        (Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha₂) hUsq)
        (Nat.pos_of_mem_divisors hb₂).ne'
      change a₁ * b₁ ^ 2 = a₂ * b₂ ^ 2 at h
      rw [h] at H₁
      exact Prod.ext (H₁.1.symm.trans H₂.1) (H₁.2.symm.trans H₂.2)
    rw [squareSplitDivisors, Finset.sum_image hinj, Finset.sum_product]
    trans ∑ a ∈ (squareSplitU n).divisors, ∑ b ∈ (squareSplitV n).divisors,
      (ArithmeticFunction.moebius (squareSplitU n / a) : ℂ) *
        ArithmeticFunction.moebius (squareSplitV n / b)
    · refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
      change (ArithmeticFunction.moebius (squareSplitU (n / (a * b ^ 2))) : ℂ) *
        ArithmeticFunction.moebius (squareSplitV (n / (a * b ^ 2))) =
        (ArithmeticFunction.moebius (squareSplitU n / a) : ℂ) *
          ArithmeticFunction.moebius (squareSplitV n / b)
      have hau : a ∣ squareSplitU n := Nat.dvd_of_mem_divisors ha
      have hbv : b ∣ squareSplitV n := Nat.dvd_of_mem_divisors hb
      have hdiv : n / (a * b ^ 2) = (squareSplitU n / a) * (squareSplitV n / b) ^ 2 := by
        conv_lhs => rw [← hUV]
        rw [← Nat.div_mul_div_comm hau (pow_dvd_pow_of_dvd hbv 2)]
        simp only [sq, Nat.div_mul_div_comm hbv hbv]
      have hUa : Squarefree (squareSplitU n / a) :=
        Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hau) hUsq
      have hVb : squareSplitV n / b ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hV0) hbv)
          (Nat.pos_of_mem_divisors hb)).ne'
      rw [hdiv, (split_coords hUa hVb).1, (split_coords hUa hVb).2]
    · rw [← Finset.sum_mul_sum, sum_moebius_divisors, sum_moebius_divisors]
      simp only [ArithmeticFunction.one_apply]
      by_cases hU : squareSplitU n = 1
      · by_cases hV : squareSplitV n = 1
        · have hn1 : n = 1 := by rw [← hUV, hU, hV, one_pow, mul_one]
          simp [hn1, squareSplitU_one, squareSplitV_one]
        · have hn1 : n ≠ 1 := fun h => hV (by rw [h]; exact squareSplitV_one)
          simp [hU, hV, hn1]
      · have hn1 : n ≠ 1 := fun h => hU (by rw [h]; exact squareSplitU_one)
        simp [hU, hn1]

/-- Every arithmetic function is fixed on the right by the identity. -/
private theorem conv_m_one (m : ArithmeticFunction ℂ) : squareSplitConv m 1 = m := by
  apply ArithmeticFunction.ext
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [squareSplitConv_zero]
    exact (m.map_zero').symm
  · rw [squareSplitConv_apply _ _ hn]
    have hprops := squareSplitDivisors_properties.1 n hn
    have h₀ : ∀ d ∈ squareSplitDivisors n, d ≠ n →
        m d * (1 : ArithmeticFunction ℂ) (n / d) = 0 := by
      intro d hd hdn
      have hdvd := hprops.2.2 d hd
      have hne : n / d ≠ 1 := fun h => hdn (by rw [← Nat.div_mul_cancel hdvd, h, one_mul])
      simp [hne]
    have hsum := Finset.sum_eq_single_of_mem n hprops.2.1 h₀
    rw [hsum, Nat.div_self (Nat.pos_of_ne_zero hn), ArithmeticFunction.one_apply]
    simp

/-- The inverse of the constant-one function is the product of the classical Möbius values on
the two square-splitting coordinates. -/
private theorem part1 (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) (n : ℕ)
    (hn : n ≠ 0) :
    m n = (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n) := by
  have hmem : moebiusStar = m := by
    have h := (squareSplit_moebius_inversion m hm moebiusStar 1).mp zeta_conv_moebiusStar.symm
    rwa [conv_m_one] at h
  rw [← hmem, moebiusStar_apply, ite_eq_right hn]

/-- Values of the inverse at prime powers. -/
private theorem part2 (m : ArithmeticFunction ℂ)
    (h1 : ∀ n ≠ 0, m n = (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n)) (p : ℕ) (hp : p.Prime) :
    m p = -1 ∧ m (p ^ 2) = -1 ∧ m (p ^ 3) = 1 ∧ ∀ k, 4 ≤ k → m (p ^ k) = 0 := by
  have hp0 : ∀ k, p ^ k ≠ 0 := fun k => pow_ne_zero k hp.ne_zero
  have hU : ∀ k, squareSplitU (p ^ k) = p ^ (k % 2) := fun k => (UV_prime_pow hp).1
  have hV : ∀ k, squareSplitV (p ^ k) = p ^ (k / 2) := fun k => (UV_prime_pow hp).2
  have e1 : m p = -1 := by
    have h := h1 p hp.ne_zero
    rw [show p = p ^ 1 from (pow_one p).symm, hU 1, hV 1, show (1 % 2) = 1 from rfl,
      show (1 / 2) = 0 from rfl, pow_one, pow_zero,
      ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one] at h
    simpa using h
  have e2 : m (p ^ 2) = -1 := by
    have h := h1 _ (hp0 2)
    rw [hU 2, hV 2, show (2 % 2) = 0 from rfl, show (2 / 2) = 1 from rfl, pow_zero, pow_one,
      ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hp] at h
    simpa using h
  have e3 : m (p ^ 3) = 1 := by
    have h := h1 _ (hp0 3)
    rw [hU 3, hV 3, show (3 % 2) = 1 from rfl, show (3 / 2) = 1 from rfl, pow_one,
      ArithmeticFunction.moebius_apply_prime hp] at h
    simpa using h
  have e4 : ∀ k, 4 ≤ k → m (p ^ k) = 0 := by
    intro k hk
    have hk2 : k / 2 ≠ 1 := by omega
    have hk0 : k / 2 ≠ 0 := by omega
    rw [h1 _ (hp0 k), hV k, ArithmeticFunction.moebius_apply_prime_pow hp hk0,
      ite_eq_right hk2]
    simp
  exact ⟨e1, e2, e3, e4⟩

/-- The inverse is multiplicative. -/
private theorem m_mul (m : ArithmeticFunction ℂ)
    (h1 : ∀ n ≠ 0, m n = (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n)) {a b : ℕ} (hab : a.Coprime b) :
    m (a * b) = m a * m b := by
  rcases eq_or_ne a 0 with rfl | ha
  · have h0 : m 0 = 0 := m.map_zero'
    rw [zero_mul, h0, zero_mul]
  rcases eq_or_ne b 0 with rfl | hb
  · have h0 : m 0 = 0 := m.map_zero'
    rw [mul_zero, h0, mul_zero]
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  rw [h1 _ hab0, h1 a ha, h1 b hb, (UV_mul hab).1, (UV_mul hab).2]
  have hUcop : (squareSplitU a).Coprime (squareSplitU b) :=
    Nat.Coprime.of_dvd (UV_dvd a).1 (UV_dvd b).1 hab
  have hVcop : (squareSplitV a).Coprime (squareSplitV b) :=
    Nat.Coprime.of_dvd (UV_dvd a).2 (UV_dvd b).2 hab
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hUcop,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hVcop]
  push_cast
  ring

/-- The inverse takes value one at one. -/
private theorem m_one (m : ArithmeticFunction ℂ)
    (h1 : ∀ n ≠ 0, m n = (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n)) : m 1 = 1 := by
  rw [h1 1 one_ne_zero, squareSplitU_one, squareSplitV_one,
    ArithmeticFunction.moebius_apply_one]
  norm_num

/-- The inverse is bounded by one in absolute value. -/
private theorem norm_m_le_one (m : ArithmeticFunction ℂ)
    (h1 : ∀ n ≠ 0, m n = (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n)) (n : ℕ) : ‖m n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : m 0 = 0 := m.map_zero'
    simp [h0]
  · rw [h1 n hn, norm_mul]
    have hnorm : ∀ x : ℕ, ‖((ArithmeticFunction.moebius x : ℤ) : ℂ)‖ ≤ 1 := by
      intro x
      rcases ArithmeticFunction.moebius_eq_or x with h | h | h <;> simp [h]
    have e1 := hnorm (squareSplitU n)
    have e2 := hnorm (squareSplitV n)
    calc ‖((ArithmeticFunction.moebius (squareSplitU n) : ℤ) : ℂ)‖ *
        ‖((ArithmeticFunction.moebius (squareSplitV n) : ℤ) : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul e1 e2 (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1

/-- The `LSeries` term of the inverse factors through the zeta summand homomorphism. -/
private theorem term_eq (m : ArithmeticFunction ℂ) {s : ℂ} (hs0 : s ≠ 0) (n : ℕ) :
    LSeries.term (fun n => m n) s n = m n * riemannZetaSummandHom hs0 n :=
  LSeries.term_def₀ (m.map_zero') s n

/-- The `LSeries` term of the inverse is multiplicative. -/
private theorem term_mul (m : ArithmeticFunction ℂ)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → m (a * b) = m a * m b) {s : ℂ} (hs0 : s ≠ 0)
    {a b : ℕ} (hab : a.Coprime b) :
    LSeries.term (fun n => m n) s (a * b) =
      LSeries.term (fun n => m n) s a * LSeries.term (fun n => m n) s b := by
  rw [term_eq m hs0, term_eq m hs0, term_eq m hs0, hmul hab, map_mul]
  ring

/-- The `LSeries` term of the inverse at one. -/
private theorem term_one (m : ArithmeticFunction ℂ) (hm1 : m 1 = 1) {s : ℂ} (hs0 : s ≠ 0) :
    LSeries.term (fun n => m n) s 1 = 1 := by
  rw [term_eq m hs0, hm1, map_one, mul_one]

/-- The local factor of the Euler product at a prime. -/
private theorem local_tsum (m : ArithmeticFunction ℂ) (hm1 : m 1 = 1)
    (h2 : ∀ p : ℕ, p.Prime → m p = -1 ∧ m (p ^ 2) = -1 ∧ m (p ^ 3) = 1 ∧
      ∀ k, 4 ≤ k → m (p ^ k) = 0) {s : ℂ} (hs0 : s ≠ 0) (q : Nat.Primes) :
    ∑' k, LSeries.term (fun n => m n) s ((q : ℕ) ^ k) =
      1 - (((q : ℕ) : ℂ) ^ (-s)) - (((q : ℕ) : ℂ) ^ (-(2 * s))) +
        (((q : ℕ) : ℂ) ^ (-(3 * s))) := by
  have hp : (q : ℕ).Prime := q.2
  have hp0 : (((q : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hexp2 : (-s) + (-s) = -(2 * s) := by ring
  have hsq : ((((q : ℕ) : ℂ) ^ (-s)) ^ 2) = (((q : ℕ) : ℂ) ^ (-(2 * s))) := by
    rw [pow_two, ← Complex.cpow_add _ _ hp0, hexp2]
  have hcb : ((((q : ℕ) : ℂ) ^ (-s)) ^ 3) = (((q : ℕ) : ℂ) ^ (-(3 * s))) := by
    have hexp2' : (-s) + (-(2 * s)) = -(3 * s) := by ring
    rw [pow_three, ← Complex.cpow_add _ _ hp0, hexp2, ← Complex.cpow_add _ _ hp0, hexp2']
  have hterm : ∀ k : ℕ, LSeries.term (fun n => m n) s ((q : ℕ) ^ k) =
      m ((q : ℕ) ^ k) * ((((q : ℕ) : ℂ) ^ (-s)) ^ k) := by
    intro k
    rw [term_eq m hs0, map_pow (riemannZetaSummandHom hs0) _ _]
    rfl
  have hvan : ∀ k : ℕ, k ∉ ({0, 1, 2, 3} : Finset ℕ) →
      m ((q : ℕ) ^ k) * ((((q : ℕ) : ℂ) ^ (-s)) ^ k) = 0 := by
    intro k hk
    have hk4 : 4 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega
    rw [(h2 _ hp).2.2.2 k hk4, zero_mul]
  rw [tsum_congr hterm, tsum_eq_sum (s := ({0, 1, 2, 3} : Finset ℕ)) hvan,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [pow_zero, pow_one]
  rw [hm1, (h2 _ hp).1, (h2 _ hp).2.1, (h2 _ hp).2.2.1, hsq, hcb]
  ring

/-- The Euler product of the inverse's Dirichlet series. -/
private theorem euler_hasProd (m : ArithmeticFunction ℂ)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → m (a * b) = m a * m b) (hm1 : m 1 = 1)
    (h2 : ∀ p : ℕ, p.Prime → m p = -1 ∧ m (p ^ 2) = -1 ∧ m (p ^ 3) = 1 ∧
      ∀ k, 4 ≤ k → m (p ^ k) = 0)
    (hnorm : ∀ n : ℕ, ‖m n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun q : Nat.Primes => 1 - (((q : ℕ) : ℂ) ^ (-s)) -
        (((q : ℕ) : ℂ) ^ (-(2 * s))) + (((q : ℕ) : ℂ) ^ (-(3 * s))))
      (LSeries (fun n => m n) s) := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hterm_mul : ∀ {a b : ℕ}, a.Coprime b →
      LSeries.term (fun n => m n) s (a * b) =
        LSeries.term (fun n => m n) s a * LSeries.term (fun n => m n) s b :=
    fun hab => term_mul m hmul hs0 hab
  have hterm_one : LSeries.term (fun n => m n) s 1 = 1 := term_one m hm1 hs0
  have hsum : LSeriesSummable (fun n => m n) s := by
    have hbase := summable_riemannZetaSummand hs
    refine hbase.of_norm_bounded (fun n => ?_)
    change ‖LSeries.term (fun n => m n) s n‖ ≤ ‖riemannZetaSummandHom hs0 n‖
    rw [term_eq m hs0, norm_mul]
    calc ‖m n‖ * ‖riemannZetaSummandHom hs0 n‖ ≤ 1 * ‖riemannZetaSummandHom hs0 n‖ :=
        mul_le_mul_of_nonneg_right (hnorm n) (norm_nonneg _)
      _ = ‖riemannZetaSummandHom hs0 n‖ := one_mul _
  have heuler := EulerProduct.eulerProduct_hasProd (f := LSeries.term (fun n => m n) s)
    hterm_one hterm_mul hsum.norm (LSeries.term_zero _ _)
  refine heuler.congr_fun (fun q => ?_)
  exact (local_tsum m hm1 h2 hs0 q).symm

/-- The Dirichlet series of the inverse is the stated Euler product and equals
`1 / (ζ(s) * ζ(2 * s))`. -/
private theorem part3 (m : ArithmeticFunction ℂ)
    (hmul : ∀ {a b : ℕ}, a.Coprime b → m (a * b) = m a * m b) (hm1 : m 1 = 1)
    (h2 : ∀ p : ℕ, p.Prime → m p = -1 ∧ m (p ^ 2) = -1 ∧ m (p ^ 3) = 1 ∧
      ∀ k, 4 ≤ k → m (p ^ k) = 0)
    (hnorm : ∀ n : ℕ, ‖m n‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => m n) s = ∏' q : Nat.Primes,
        (1 - (((q : ℕ) : ℂ) ^ (-s)) - (((q : ℕ) : ℂ) ^ (-(2 * s))) +
          (((q : ℕ) : ℂ) ^ (-(3 * s)))) ∧
      LSeries (fun n => m n) s = 1 / (riemannZeta s * riemannZeta (2 * s)) := by
  have heuler := euler_hasProd m hmul hm1 h2 hnorm hs
  refine ⟨heuler.tprod_eq.symm, ?_⟩
  have hre : (2 * s).re = 2 * s.re := by rw [two_mul, Complex.add_re, ← two_mul]
  have h2s : 1 < (2 * s).re := by rw [hre]; linarith
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs0' : 2 * s ≠ 0 := by
    intro hcon
    have hrez : (2 * s).re = 0 := by rw [hcon]; simp
    rw [hre] at hrez
    linarith
  have hZ1 : HasProd (fun q : Nat.Primes => (1 - ((((q : ℕ)) : ℂ) ^ (-s)))⁻¹)
      (riemannZeta s) :=
    riemannZeta_eulerProduct_hasProd hs
  have hZ2 : HasProd (fun q : Nat.Primes => (1 - ((((q : ℕ)) : ℂ) ^ (-(2 * s))))⁻¹)
      (riemannZeta (2 * s)) :=
    riemannZeta_eulerProduct_hasProd h2s
  have hmul := heuler.mul (hZ1.mul hZ2)
  have hone : HasProd (fun _ : Nat.Primes => (1 : ℂ))
      (LSeries (fun n => m n) s * (riemannZeta s * riemannZeta (2 * s))) := by
    refine hmul.congr_fun (fun q => ?_)
    have hp : (q : ℕ).Prime := q.2
    have hp0 : (((q : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hexp : (-s) + (-(2 * s)) = -(3 * s) := by ring
    have hzw : ((((q : ℕ)) : ℂ) ^ (-s)) * ((((q : ℕ)) : ℂ) ^ (-(2 * s))) =
        ((((q : ℕ)) : ℂ) ^ (-(3 * s))) := by
      rw [← Complex.cpow_add _ _ hp0, hexp]
    have hF : 1 - ((((q : ℕ)) : ℂ) ^ (-s)) - ((((q : ℕ)) : ℂ) ^ (-(2 * s))) +
        ((((q : ℕ)) : ℂ) ^ (-(3 * s))) =
        (1 - ((((q : ℕ)) : ℂ) ^ (-s))) * (1 - ((((q : ℕ)) : ℂ) ^ (-(2 * s)))) := by
      rw [← hzw]
      ring
    have hAnorm : ‖((((q : ℕ)) : ℂ) ^ (-s))‖ < 1 :=
      (summable_riemannZetaSummand hs).of_norm.norm_lt_one
        (f := (riemannZetaSummandHom hs0).toMonoidHom) hp.one_lt
    have hBnorm : ‖((((q : ℕ)) : ℂ) ^ (-(2 * s)))‖ < 1 :=
      (summable_riemannZetaSummand h2s).of_norm.norm_lt_one
        (f := (riemannZetaSummandHom hs0').toMonoidHom) hp.one_lt
    have hA : (1 : ℂ) - ((((q : ℕ)) : ℂ) ^ (-s)) ≠ 0 := by
      intro hcon
      have heq : ((((q : ℕ)) : ℂ) ^ (-s)) = 1 := (sub_eq_zero.mp hcon).symm
      rw [heq] at hAnorm
      simp at hAnorm
    have hB : (1 : ℂ) - ((((q : ℕ)) : ℂ) ^ (-(2 * s))) ≠ 0 := by
      intro hcon
      have heq : ((((q : ℕ)) : ℂ) ^ (-(2 * s))) = 1 := (sub_eq_zero.mp hcon).symm
      rw [heq] at hBnorm
      simp at hBnorm
    change (1 : ℂ) = (1 - ((((q : ℕ)) : ℂ) ^ (-s)) - ((((q : ℕ)) : ℂ) ^ (-(2 * s))) +
      ((((q : ℕ)) : ℂ) ^ (-(3 * s)))) *
      (((1 - ((((q : ℕ)) : ℂ) ^ (-s)))⁻¹) * ((1 - ((((q : ℕ)) : ℂ) ^ (-(2 * s))))⁻¹))
    rw [hF, mul_mul_mul_comm, mul_inv_cancel₀ hA, mul_inv_cancel₀ hB, mul_one]
  have hL := hone.unique hasProd_one
  rw [eq_inv_of_mul_eq_one_left hL, one_div]

end squareSplitMoebius_proof

open squareSplitMoebius_proof

/-- **Möbius function of the square-splitting convolution.** Let $\star$ be the square-splitting
convolution, $\mathbf{1}$ the constant function $1$ on the positive integers, $\varepsilon$ the
identity element ($\varepsilon(1) = 1$ and $\varepsilon(n) = 0$ for $n \ne 1$), and let $\mu_\star$
be any complex-valued arithmetic function with $\mathbf{1} \star \mu_\star = \varepsilon$. Then
$\mu_\star(n) = \mu(u(n))\,\mu(v(n))$ for every $n \ge 1$, where $\mu$ is the Möbius function,
$u(n)$ is the product of the primes dividing $n$ to an odd power and $v(n)$ is the positive
integer with $n = u(n)\,v(n)^2$. For every prime $p$, $\mu_\star(p) = \mu_\star(p^2) = -1$,
$\mu_\star(p^3) = 1$ and $\mu_\star(p^k) = 0$ for every $k \ge 4$. For every complex $s$ with
$\operatorname{Re} s > 1$,
$$\sum_{n \ge 1} \frac{\mu_\star(n)}{n^s} = \prod_p \left(1 - p^{-s} - p^{-2s} + p^{-3s}\right)
= \frac{1}{\zeta(s)\,\zeta(2s)}.$$

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 3
(`integers-2026-A56-thm-3`). -/
public theorem squareSplitMoebius_formula (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    (∀ n ≠ 0, m n = (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n)) ∧
    (∀ p : ℕ, p.Prime → m p = -1 ∧ m (p ^ 2) = -1 ∧ m (p ^ 3) = 1 ∧
      ∀ k, 4 ≤ k → m (p ^ k) = 0) ∧
    ∀ s : ℂ, 1 < s.re →
      LSeries (fun n => m n) s = ∏' p : Nat.Primes,
        (1 - ((p : ℕ) : ℂ) ^ (-s) - ((p : ℕ) : ℂ) ^ (-(2 * s)) + ((p : ℕ) : ℂ) ^ (-(3 * s))) ∧
      LSeries (fun n => m n) s = 1 / (riemannZeta s * riemannZeta (2 * s)) := by
  have h1 : ∀ n ≠ 0, m n = (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n) := fun n hn => part1 m hm n hn
  have h2 : ∀ p : ℕ, p.Prime → m p = -1 ∧ m (p ^ 2) = -1 ∧ m (p ^ 3) = 1 ∧
      ∀ k, 4 ≤ k → m (p ^ k) = 0 := fun p hp => part2 m h1 p hp
  have hmul : ∀ {a b : ℕ}, a.Coprime b → m (a * b) = m a * m b :=
    fun hab => m_mul m h1 hab
  have hm1 : m 1 = 1 := m_one m h1
  have hnorm : ∀ n : ℕ, ‖m n‖ ≤ 1 := fun n => norm_m_le_one m h1 n
  exact ⟨h1, h2, fun s hs => part3 m hmul hm1 h2 hnorm s hs⟩

end MetaMathlibExt
