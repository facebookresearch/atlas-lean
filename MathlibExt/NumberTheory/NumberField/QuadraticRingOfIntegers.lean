/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import MathlibExt.NumberTheory.DirichletCharacter.Quadratic

@[expose] public section

set_option autoImplicit false

/-!
# The ring of integers and the discriminant of a quadratic field

Let `K` be a number field with `[K : ℚ] = 2` and ring of integers `𝒪_K = integralClosure ℤ K`.

* `NumberField.exists_sq_eq_squarefree`: `K = ℚ(θ)` with `θ² = m` for a squarefree integer
  `m ≠ 1`;
* `NumberField.mem_integralClosure_iff_of_sq_eq`: `𝒪_K = ℤ + ℤω` with `ω = (1 + θ)/2` if
  `m ≡ 1 (mod 4)` and `ω = θ` otherwise;
* `NumberField.discr_eq_of_sq_eq`: `disc K = m` if `m ≡ 1 (mod 4)` and `disc K = 4m` otherwise;
* `NumberField.isFundamentalDiscriminant_discr`: `disc K` is a fundamental discriminant;
* `NumberField.exists_sq_eq_discr` and `NumberField.mem_integralClosure_iff_of_sq_eq_discr`:
  `disc K = D` is a square `δ²` in `K` and `𝒪_K = ℤ + ℤ(D + δ)/2`;
* `NumberField.discr_eq_of_sq_eq_fundamental`: if `θ² = D` for a fundamental discriminant
  `D ≠ 1`, then `disc K = D`.

The source is F. Keune, *Number Fields*, Radboud University Press, 2023: Theorem 1.9
("Integers of a quadratic number field", p. 7) and Example 1.44 (p. 21).
-/

namespace NumberField

open Polynomial Module

/-- If `m q²` is an integer for a squarefree integer `m`, then the rational `q` is an integer. -/
private lemma exists_intCast_eq_of_mul_sq {m : ℤ} (hm : Squarefree m) {q : ℚ} {n : ℤ}
    (h : (m : ℚ) * q ^ 2 = n) : ∃ z : ℤ, q = z := by
  have h1 : ((m * q.num ^ 2 : ℤ) : ℚ) = ((n * (q.den : ℤ) ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [← Rat.mul_den_eq_num, mul_pow, ← mul_assoc, h]
  have h2 : m * q.num ^ 2 = n * (q.den : ℤ) ^ 2 := by exact_mod_cast h1
  have hcop : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    refine IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.mpr ?_)
    simpa [Int.gcd, Nat.coprime_comm] using q.reduced
  have hdvd : (q.den : ℤ) ^ 2 ∣ m := hcop.dvd_of_dvd_mul_right ⟨n, by rw [h2]; ring⟩
  have hunit : IsUnit (q.den : ℤ) := hm _ (by simpa [sq] using hdvd)
  have hden : q.den = 1 := by
    rcases Int.isUnit_iff.mp hunit with h | h <;> omega
  exact ⟨q.num, (Rat.intCast_num_of_den_eq_one hden).symm⟩

/-- A squarefree integer `m ≠ 1` is not the square of a rational number. -/
private lemma sq_ne_of_squarefree {m : ℤ} (hm : Squarefree m) (hm1 : m ≠ 1) (q : ℚ) :
    q ^ 2 ≠ m := by
  intro h
  obtain ⟨z, rfl⟩ := exists_intCast_eq_of_mul_sq (m := 1) squarefree_one (n := m)
    (by simpa using h)
  have hz : z ^ 2 = m := by exact_mod_cast h
  have hu : IsUnit z := hm z ⟨1, by rw [← hz]; ring⟩
  apply hm1
  rw [← hz]
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> norm_num

variable {K : Type*} [Field K] [NumberField K]

/-- `r + sθ` is not rational when `θ² = m` with `m` squarefree, `m ≠ 1`, and `s ≠ 0`. -/
private lemma add_mul_notMem_range {θ : K} {m : ℤ} (hθ : θ ^ 2 = m) (hm : Squarefree m)
    (hm1 : m ≠ 1) (r s : ℚ) (hs : s ≠ 0) :
    (r : K) + s * θ ∉ Set.range (algebraMap ℚ K) := by
  rintro ⟨q, hq⟩
  rw [eq_ratCast] at hq
  apply sq_ne_of_squarefree hm hm1 ((q - r) / s)
  have hs' : (s : K) ≠ 0 := by exact_mod_cast hs
  have hθ' : θ = (((q - r) / s : ℚ) : K) := by
    push_cast
    rw [eq_div_iff hs', hq]
    ring
  apply Rat.cast_injective (α := K)
  rw [Rat.cast_pow, ← hθ', hθ, Rat.cast_intCast]

private lemma notMem_range_of_sq_eq {θ : K} {m : ℤ} (hθ : θ ^ 2 = m) (hm : Squarefree m)
    (hm1 : m ≠ 1) : θ ∉ Set.range (algebraMap ℚ K) := by
  simpa using add_mul_notMem_range hθ hm hm1 0 1 one_ne_zero

/-- The `ℚ`-basis `(1, y)` of a quadratic field, for `y ∉ ℚ`. -/
private noncomputable def basisPair (hK : finrank ℚ K = 2) (y : K)
    (hy : y ∉ Set.range (algebraMap ℚ K)) : Basis (Fin 2) ℚ K :=
  basisOfLinearIndependentOfCardEqFinrank (b := ![1, y])
    (LinearIndependent.pair_iff.mpr fun s t hst => by
      by_cases ht : t = 0
      · subst ht
        simpa using hst
      · refine absurd ⟨-s / t, ?_⟩ hy
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_div₀, map_neg, div_eq_iff (by simpa using ht)]
        linear_combination -hst)
    (by simp [hK])

private lemma basisPair_apply (hK : finrank ℚ K = 2) (y : K)
    (hy : y ∉ Set.range (algebraMap ℚ K)) : ⇑(basisPair hK y hy) = ![1, y] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

private lemma exists_eq_add_mul (hK : finrank ℚ K = 2) (y : K)
    (hy : y ∉ Set.range (algebraMap ℚ K)) (x : K) : ∃ r s : ℚ, x = r + s * y := by
  refine ⟨(basisPair hK y hy).repr x 0, (basisPair hK y hy).repr x 1, ?_⟩
  conv_lhs => rw [← (basisPair hK y hy).sum_repr x]
  simp [Fin.sum_univ_two, basisPair_apply, Rat.smul_def]

/-- Integrality of `r + sθ` forces `2r ∈ ℤ` and `r² - ms² ∈ ℤ`. -/
private lemma integral_coeffs (hK : finrank ℚ K = 2) {θ : K} {m : ℤ} (hθ : θ ^ 2 = m)
    (hm : Squarefree m) (hm1 : m ≠ 1) {r s : ℚ} (h : IsIntegral ℤ ((r : K) + s * θ)) :
    (∃ A : ℤ, 2 * r = A) ∧ ∃ n : ℤ, r ^ 2 - m * s ^ 2 = n := by
  by_cases hs : s = 0
  · subst hs
    have hr : IsIntegral ℤ r := by
      rw [← isIntegral_algebraMap_iff (B := K)]
      simpa using h
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hr
    rw [eq_intCast] at hz
    exact ⟨⟨2 * z, by rw [← hz]; push_cast; ring⟩, ⟨z ^ 2, by rw [← hz]; push_cast; ring⟩⟩
  · set x : K := (r : K) + s * θ with hx
    set p : ℚ[X] := X ^ 2 - C (2 * r) * X + C (r ^ 2 - m * s ^ 2) with hp
    have hpm : p.Monic := by rw [hp]; monicity!
    have hpd : p.natDegree = 2 := by rw [hp]; compute_degree!
    have hpx : aeval x p = 0 := by
      rw [hp, hx]
      simp
      linear_combination (s : K) ^ 2 * hθ
    have hxi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hdeg : (minpoly ℚ x).natDegree = 2 := by
      have h1 : (minpoly ℚ x).natDegree ≤ 2 := hK ▸ minpoly.natDegree_le x
      have h2 : (minpoly ℚ x).natDegree ≠ 1 := by
        rw [Ne, minpoly.natDegree_eq_one_iff]
        exact add_mul_notMem_range hθ hm hm1 r s hs
      have h3 := minpoly.natDegree_pos hxi
      omega
    have heq : p = minpoly ℚ x :=
      eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hpm (minpoly.dvd ℚ x hpx)
        (by omega)
    have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ h
    rw [← heq] at hmap
    have c1 := congrArg (fun f : ℚ[X] => f.coeff 1) hmap
    have c0 := congrArg (fun f : ℚ[X] => f.coeff 0) hmap
    simp only [hp, coeff_map, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul_X, coeff_C] at c1 c0
    norm_num at c1 c0
    exact ⟨⟨-(minpoly ℤ x).coeff 1, by push_cast; linarith⟩, ⟨(minpoly ℤ x).coeff 0, c0⟩⟩

private lemma zmod_four_aux : ∀ a b c : ZMod 4, a ^ 2 - c * b ^ 2 = 0 → c ≠ 0 →
    (c = 1 → 2 * (a - b) = 0) ∧ (c ≠ 1 → 2 * a = 0 ∧ 2 * b = 0) := by
  decide

private lemma emod_four_ne_zero {m : ℤ} (hm : Squarefree m) : m % 4 ≠ 0 := by
  intro h
  have : IsUnit (2 : ℤ) := hm 2 ⟨m / 4, by omega⟩
  rw [Int.isUnit_iff] at this
  omega

/-- The arithmetic step of Keune, Theorem 1.9. -/
private lemma exists_of_coeffs (θ : K) {m : ℤ} (hm : Squarefree m)
    {r s : ℚ} {A n : ℤ} (hA : 2 * r = A) (hn : r ^ 2 - m * s ^ 2 = n) :
    ∃ a b : ℤ, (r : K) + s * θ = a + b * (if m % 4 = 1 then (1 + θ) / 2 else θ) := by
  obtain ⟨B, hB⟩ := exists_intCast_eq_of_mul_sq hm (q := 2 * s) (n := A ^ 2 - 4 * n)
    (by push_cast; linear_combination (-4) * hn + (2 * r + A) * hA)
  have hB' : 2 * s = B := hB
  have h4 : (4 : ℤ) ∣ A ^ 2 - m * B ^ 2 := ⟨n, by
    have : (A : ℚ) ^ 2 - m * B ^ 2 = 4 * n := by
      linear_combination 4 * hn - (2 * r + A) * hA + m * (2 * s + B) * hB'
    exact_mod_cast this⟩
  have hz : ((A : ZMod 4)) ^ 2 - (m : ZMod 4) * (B : ZMod 4) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (A ^ 2 - m * B ^ 2) 4).mpr (by exact_mod_cast h4)
    push_cast at this
    exact this
  have hm0 : (m : ZMod 4) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := emod_four_ne_zero hm
    omega
  have hrK : (r : K) = A / 2 := by
    have := congrArg (Rat.cast : ℚ → K) hA
    push_cast at this
    linear_combination this / 2
  have hsK : (s : K) = B / 2 := by
    have := congrArg (Rat.cast : ℚ → K) hB'
    push_cast at this
    linear_combination this / 2
  obtain ⟨h1, h2⟩ := zmod_four_aux _ _ _ hz hm0
  rw [hrK, hsK]
  by_cases hm4 : m % 4 = 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm4)]
    have hc : (m : ZMod 4) = 1 := by
      have := (ZMod.intCast_eq_intCast_iff' m 1 4).mpr (by omega)
      simpa using this
    have h3 := h1 hc
    have h5 : (4 : ℤ) ∣ 2 * (A - B) := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (A - B)) 4).mp (by push_cast; exact h3)
      exact_mod_cast this
    obtain ⟨k, hk⟩ : ∃ k, A - B = 2 * k := ⟨(A - B) / 2, by omega⟩
    refine ⟨k, B, ?_⟩
    have hk' : (A : K) - B = 2 * k := by exact_mod_cast hk
    linear_combination hk' / 2
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm4)]
    have hc : (m : ZMod 4) ≠ 1 := by
      intro hc
      have := (ZMod.intCast_eq_intCast_iff' m 1 4).mp (by simpa using hc)
      omega
    obtain ⟨h3, h5⟩ := h2 hc
    have h6 : (4 : ℤ) ∣ 2 * A := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * A) 4).mp (by push_cast; exact h3)
      exact_mod_cast this
    have h7 : (4 : ℤ) ∣ 2 * B := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * B) 4).mp (by push_cast; exact h5)
      exact_mod_cast this
    obtain ⟨a, ha⟩ : ∃ a, A = 2 * a := ⟨A / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, B = 2 * b := ⟨B / 2, by omega⟩
    refine ⟨a, b, ?_⟩
    rw [ha, hb]
    push_cast
    ring

/-- **A quadratic field is generated by the square root of a squarefree integer.** If $K$ is a
number field with $[K : \mathbb{Q}] = 2$, then there are $\theta \in K$ and $m \in \mathbb{Z}$
with $\theta^2 = m$, $m$ squarefree and $m \ne 1$.

This is the setting of F. Keune, *Number Fields* (2023), Theorem 1.9, p. 7: "Let m ∈ Z be
squarefree and ≠ 1. The integers in Q(√m) are the numbers [...]". Then $\theta \notin \mathbb{Q}$
(as $m$ is not a rational square), so $K = \mathbb{Q}(\theta)$. -/
theorem exists_sq_eq_squarefree (hK : finrank ℚ K = 2) :
    ∃ (θ : K) (m : ℤ), θ ^ 2 = m ∧ Squarefree m ∧ m ≠ 1 := by
  obtain ⟨α, hα⟩ : ∃ α : K, α ∉ Set.range (algebraMap ℚ K) := by
    by_contra! h
    have htop : (⊥ : Subalgebra ℚ K) = ⊤ :=
      eq_top_iff.mpr fun x _ => Algebra.mem_bot.mpr (h x)
    rw [Subalgebra.bot_eq_top_iff_finrank_eq_one, hK] at htop
    norm_num at htop
  obtain ⟨c0, c1, hc⟩ := exists_eq_add_mul hK α hα (α ^ 2)
  set ρ : ℚ := c0 + c1 ^ 2 / 4 with hρ
  set β : K := α - ((c1 / 2 : ℚ) : K) with hβ
  have hβ2 : β ^ 2 = ρ := by
    rw [hβ, hρ]
    push_cast
    linear_combination hc
  have hβn : β ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨q, hq⟩
    apply hα
    refine ⟨q + c1 / 2, ?_⟩
    rw [eq_ratCast] at hq ⊢
    rw [Rat.cast_add, hq, hβ]
    ring
  have hρ0 : ρ ≠ 0 := by
    intro h0
    apply hβn
    refine ⟨0, ?_⟩
    have : β ^ 2 = 0 := by rw [hβ2, h0, Rat.cast_zero]
    rw [map_zero, (pow_eq_zero_iff two_ne_zero).mp this]
  obtain ⟨t, m, ht, hm⟩ := exists_sq_mul_squarefree (ρ.num * ρ.den : ℤ)
  have hN : (ρ.num * ρ.den : ℤ) ≠ 0 :=
    mul_ne_zero (Rat.num_ne_zero.mpr hρ0) (by exact_mod_cast ρ.den_ne_zero)
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hN
    rw [← ht]
    ring
  have ht0K : (t : K) ≠ 0 := by exact_mod_cast ht0
  have hden : (ρ.den : K) ≠ 0 := by exact_mod_cast ρ.den_ne_zero
  set θ : K := (ρ.den : K) * β / t with hθdef
  have hθ : θ ^ 2 = m := by
    have hρK : (ρ : K) * ρ.den = ρ.num := by exact_mod_cast Rat.mul_den_eq_num ρ
    have htK : (t : K) ^ 2 * m = ρ.num * ρ.den := by exact_mod_cast ht
    rw [hθdef, div_pow, mul_pow, hβ2, div_eq_iff (pow_ne_zero 2 ht0K)]
    linear_combination (ρ.den : K) * hρK - htK
  refine ⟨θ, m, hθ, hm, ?_⟩
  rintro rfl
  have hθ1 : (θ - 1) * (θ + 1) = 0 := by
    push_cast at hθ
    linear_combination hθ
  have hβθ : β = θ * t / ρ.den := by
    rw [hθdef]
    field_simp
  apply hβn
  rcases mul_eq_zero.mp hθ1 with h | h
  · refine ⟨t / ρ.den, ?_⟩
    rw [eq_ratCast, hβθ, sub_eq_zero.mp h]
    push_cast
    ring
  · refine ⟨-t / ρ.den, ?_⟩
    rw [eq_ratCast, hβθ, eq_neg_of_add_eq_zero_left h]
    push_cast
    ring

private lemma isIntegral_omega {θ : K} {m : ℤ} (hθ : θ ^ 2 = m) :
    IsIntegral ℤ (if m % 4 = 1 then (1 + θ) / 2 else θ) := by
  by_cases hm4 : m % 4 = 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm4)]
    obtain ⟨k, hk⟩ : ∃ k : ℤ, m = 4 * k + 1 := ⟨m / 4, by omega⟩
    refine ⟨X ^ 2 - X - C k, by monicity!, ?_⟩
    have hθ' : θ ^ 2 = 4 * k + 1 := by
      rw [hθ, hk]
      push_cast
      ring
    rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, eq_intCast]
    linear_combination hθ' / 4
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm4)]
    refine IsIntegral.of_pow two_pos ?_
    rw [hθ]
    simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := m)

/-- **The ring of integers of a quadratic field.** Let $K$ be a number field with
$[K : \mathbb{Q}] = 2$ and let $\theta \in K$ satisfy $\theta^2 = m$ for a squarefree integer
$m \ne 1$. Put $\omega = (1 + \theta)/2$ if $m \equiv 1 \pmod 4$ and $\omega = \theta$ otherwise.
Then $x \in K$ lies in $\mathcal{O}_K$ (`integralClosure ℤ K`) if and only if $x = a + b\omega$
for some $a, b \in \mathbb{Z}$.

F. Keune, *Number Fields* (2023), Theorem 1.9 ("Integers of a quadratic number field"), p. 7:
"Let m ∈ Z be squarefree and ≠ 1. The integers in Q(√m) are the numbers a + b√m with a, b ∈ Z
if m ≡ 2, 3 (mod 4) and in case m ≡ 1 (mod 4) the integers are the numbers (a + b√m)/2 with
a, b ∈ Z and a ≡ b (mod 2)", in the form of Corollary 1.11, p. 8: "the integers in Q(√m) form
the subring Z[ωm]". -/
theorem mem_integralClosure_iff_of_sq_eq (hK : finrank ℚ K = 2) {θ : K} {m : ℤ}
    (hθ : θ ^ 2 = m) (hm : Squarefree m) (hm1 : m ≠ 1) (x : K) :
    x ∈ integralClosure ℤ K ↔
      ∃ a b : ℤ, x = a + b * (if m % 4 = 1 then (1 + θ) / 2 else θ) := by
  constructor
  · intro hx
    obtain ⟨r, s, rfl⟩ := exists_eq_add_mul hK θ (notMem_range_of_sq_eq hθ hm hm1) x
    obtain ⟨⟨A, hA⟩, ⟨n, hn⟩⟩ := integral_coeffs hK hθ hm hm1 hx
    exact exists_of_coeffs θ hm hA hn
  · rintro ⟨a, b, rfl⟩
    have ha : IsIntegral ℤ (a : K) := by
      simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := a)
    have hb : IsIntegral ℤ (b : K) := by
      simpa using isIntegral_algebraMap (R := ℤ) (A := K) (x := b)
    exact ha.add (hb.mul (isIntegral_omega hθ))

private lemma trace_eq_zero_of_sq_eq (hK : finrank ℚ K = 2) {θ : K} {m : ℤ}
    (hθ : θ ^ 2 = m) (hm : Squarefree m) (hm1 : m ≠ 1) : Algebra.trace ℚ K θ = 0 := by
  set b := basisPair hK θ (notMem_range_of_sq_eq hθ hm hm1) with hb
  have h0 : θ * b 0 = b 1 := by simp [hb, basisPair_apply]
  have h1 : θ * b 1 = (m : ℚ) • b 0 := by
    simp [hb, basisPair_apply, Rat.smul_def, ← sq, hθ]
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, h0, h1, b.repr_self, map_smul, b.repr_self]
  simp

private lemma trace_add_mul (hK : finrank ℚ K = 2) {θ : K} {m : ℤ}
    (hθ : θ ^ 2 = m) (hm : Squarefree m) (hm1 : m ≠ 1) (r s : ℚ) :
    Algebra.trace ℚ K ((r : K) + s * θ) = 2 * r := by
  rw [map_add, ← Rat.smul_def, map_smul, trace_eq_zero_of_sq_eq hK hθ hm hm1,
    ← eq_ratCast (algebraMap ℚ K), Algebra.trace_algebraMap, hK]
  simp

private lemma discr_pair (hK : finrank ℚ K = 2) {θ : K} {m : ℤ}
    (hθ : θ ^ 2 = m) (hm : Squarefree m) (hm1 : m ≠ 1) (c d : ℚ) :
    Algebra.discr ℚ ![(1 : K), c + d * θ] = 4 * d ^ 2 * m := by
  have e1 : (1 : K) * 1 = ((1 : ℚ) : K) + ((0 : ℚ) : K) * θ := by simp
  have e2 : (1 : K) * (c + d * θ) = c + d * θ := one_mul _
  have e3 : ((c : K) + d * θ) * 1 = c + d * θ := mul_one _
  have e4 : ((c : K) + d * θ) * (c + d * θ) =
      ((c ^ 2 + d ^ 2 * m : ℚ) : K) + ((2 * c * d : ℚ) : K) * θ := by
    push_cast
    linear_combination (d : K) ^ 2 * hθ
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [e1, e2, e3, e4, trace_add_mul hK hθ hm hm1, trace_add_mul hK hθ hm hm1,
    trace_add_mul hK hθ hm hm1]
  ring

private lemma isIntegral_intCast_rat (z : ℤ) : IsIntegral ℤ (z : ℚ) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := z)

private lemma coe_discr_eq_discr_pair (hK : finrank ℚ K = 2) (ω : K)
    (hω : ω ∉ Set.range (algebraMap ℚ K))
    (hmem : ∀ x : K, x ∈ integralClosure ℤ K ↔ ∃ a b : ℤ, x = a + b * ω) :
    (discr K : ℚ) = Algebra.discr ℚ ![(1 : K), ω] := by
  rw [coe_discr, ← basisPair_apply hK ω hω]
  refine Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral K (fun i j => ?_) (fun i j => ?_)
  · have hj : basisPair hK ω hω j ∈ integralClosure ℤ K := by
      rw [hmem]
      fin_cases j
      · exact ⟨1, 0, by simp [basisPair_apply]⟩
      · exact ⟨0, 1, by simp [basisPair_apply]⟩
    have h := integralBasis_repr_apply K ⟨_, hj⟩ i
    rw [Module.Basis.toMatrix_apply]
    rw [show algebraMap (RingOfIntegers K) K ⟨_, hj⟩ = basisPair hK ω hω j from rfl] at h
    rw [h]
    exact isIntegral_algebraMap
  · have hj : integralBasis K j ∈ integralClosure ℤ K := by
      rw [integralBasis_apply]
      exact (RingOfIntegers.basis K j).2
    obtain ⟨a, b, hab⟩ := (hmem _).mp hj
    have hrepr : integralBasis K j =
        (a : ℚ) • basisPair hK ω hω 0 + (b : ℚ) • basisPair hK ω hω 1 := by
      rw [hab]
      simp [basisPair_apply, Rat.smul_def]
    rw [Module.Basis.toMatrix_apply, hrepr]
    fin_cases i
    · simpa using isIntegral_intCast_rat a
    · simpa using isIntegral_intCast_rat b

/-- **The discriminant of a quadratic field.** Let $K$ be a number field with
$[K : \mathbb{Q}] = 2$ and let $\theta \in K$ satisfy $\theta^2 = m$ for a squarefree integer
$m \ne 1$. Then $\operatorname{disc} K = m$ if $m \equiv 1 \pmod 4$ and
$\operatorname{disc} K = 4m$ otherwise.

F. Keune, *Number Fields* (2023), Example 1.44, p. 21: "Let m be a squarefree integer ≠ 1. For
m ≡ 2, 3 (mod 4) we have disc(Q(√m)) = 4m, whereas disc(Q(√m)) = m for m ≡ 1 (mod 4)." -/
theorem discr_eq_of_sq_eq (hK : finrank ℚ K = 2) {θ : K} {m : ℤ}
    (hθ : θ ^ 2 = m) (hm : Squarefree m) (hm1 : m ≠ 1) :
    discr K = if m % 4 = 1 then m else 4 * m := by
  have hmem := mem_integralClosure_iff_of_sq_eq hK hθ hm hm1
  by_cases hm4 : m % 4 = 1
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true hm4)] at hmem ⊢
    have hω : (1 + θ) / 2 = ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * θ := by
      push_cast
      ring
    have hnot := add_mul_notMem_range hθ hm hm1 (1 / 2) (1 / 2) (by norm_num)
    rw [← hω] at hnot
    have h := coe_discr_eq_discr_pair hK _ hnot hmem
    have h2 := discr_pair hK hθ hm hm1 (1 / 2) (1 / 2)
    rw [← hω] at h2
    rw [h2] at h
    have h3 : ((discr K : ℤ) : ℚ) = ((m : ℤ) : ℚ) := by rw [h]; ring
    exact_mod_cast h3
  · simp only [ite_eq_right_of_eq_false _ _ (eq_false hm4)] at hmem ⊢
    have h := coe_discr_eq_discr_pair hK _ (notMem_range_of_sq_eq hθ hm hm1) hmem
    have h2 := discr_pair hK hθ hm hm1 0 1
    simp only [Rat.cast_zero, Rat.cast_one, zero_add, one_mul] at h2
    rw [h2] at h
    have h3 : ((discr K : ℤ) : ℚ) = ((4 * m : ℤ) : ℚ) := by rw [h]; push_cast; ring
    exact_mod_cast h3

/-- **The discriminant of a quadratic field is fundamental.** If $K$ is a number field with
$[K : \mathbb{Q}] = 2$, then $\operatorname{disc} K$ is a fundamental discriminant
(`MetaMathlibExt.IsFundamentalDiscriminant`): either it is squarefree and $\equiv 1 \pmod 4$,
or it is $4m$ with $m$ squarefree and $m \equiv 2, 3 \pmod 4$.

This combines `NumberField.exists_sq_eq_squarefree` with F. Keune, *Number Fields* (2023),
Example 1.44, p. 21: "For m ≡ 2, 3 (mod 4) we have disc(Q(√m)) = 4m, whereas disc(Q(√m)) = m
for m ≡ 1 (mod 4)." -/
theorem isFundamentalDiscriminant_discr (hK : finrank ℚ K = 2) :
    MetaMathlibExt.IsFundamentalDiscriminant (discr K) := by
  obtain ⟨θ, m, hθ, hm, hm1⟩ := exists_sq_eq_squarefree hK
  rw [discr_eq_of_sq_eq hK hθ hm hm1]
  by_cases hm4 : m % 4 = 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm4)]
    exact Or.inl ⟨hm, hm4⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm4)]
    have := emod_four_ne_zero hm
    exact Or.inr ⟨m, rfl, hm, by omega⟩

private lemma exists_iff_of_eq_add {ω ω' : K} {c ε : ℤ} (hε : ε ^ 2 = 1)
    (h : ω' = c + ε * ω) (x : K) :
    (∃ a b : ℤ, x = a + b * ω) ↔ ∃ a b : ℤ, x = a + b * ω' := by
  have hεK : (ε : K) ^ 2 = 1 := by exact_mod_cast hε
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a - b * ε * c, b * ε, ?_⟩
    rw [h]
    push_cast
    linear_combination (-(b : K) * ω) * hεK
  · rintro ⟨a, b, rfl⟩
    refine ⟨a + b * c, b * ε, ?_⟩
    rw [h]
    push_cast
    ring

/-- **The ring of integers in terms of the discriminant.** Let $K$ be a number field with
$[K : \mathbb{Q}] = 2$, let $D = \operatorname{disc} K$ and let $\delta \in K$ satisfy
$\delta^2 = D$. Then $x \in K$ lies in $\mathcal{O}_K$ (`integralClosure ℤ K`) if and only if
$x = a + b(D + \delta)/2$ for some $a, b \in \mathbb{Z}$.

This combines F. Keune, *Number Fields* (2023), Theorem 1.9, p. 7 ("The integers in Q(√m) are
the numbers a + b√m with a, b ∈ Z if m ≡ 2, 3 (mod 4) and in case m ≡ 1 (mod 4) the integers are
the numbers (a + b√m)/2 with a, b ∈ Z and a ≡ b (mod 2)") with Example 1.44, p. 21: if $D = m$
then $\delta = \pm\theta$ and $(D + \delta)/2 = (m - 1)/2 + (1 \pm \theta)/2$; if $D = 4m$ then
$\delta = \pm 2\theta$ and $(D + \delta)/2 = 2m \pm \theta$. -/
theorem mem_integralClosure_iff_of_sq_eq_discr (hK : finrank ℚ K = 2) {δ : K}
    (hδ : δ ^ 2 = discr K) (x : K) :
    x ∈ integralClosure ℤ K ↔ ∃ a b : ℤ, x = a + b * ((discr K + δ) / 2) := by
  obtain ⟨θ, m, hθ, hm, hm1⟩ := exists_sq_eq_squarefree hK
  rw [mem_integralClosure_iff_of_sq_eq hK hθ hm hm1]
  have hD := discr_eq_of_sq_eq hK hθ hm hm1
  by_cases hm4 : m % 4 = 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm4)] at hD ⊢
    rw [hD] at hδ ⊢
    obtain ⟨k, hk⟩ : ∃ k : ℤ, m = 2 * k + 1 := ⟨m / 2, by omega⟩
    have hprod : (δ - θ) * (δ + θ) = 0 := by linear_combination hδ - hθ
    rcases mul_eq_zero.mp hprod with h | h
    · refine exists_iff_of_eq_add (c := k) (ε := 1) (by norm_num) ?_ x
      rw [hk]
      push_cast
      linear_combination h / 2
    · refine exists_iff_of_eq_add (c := k + 1) (ε := -1) (by norm_num) ?_ x
      rw [hk]
      push_cast
      linear_combination h / 2
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm4)] at hD ⊢
    rw [hD] at hδ ⊢
    push_cast at hδ
    have hprod : (δ - 2 * θ) * (δ + 2 * θ) = 0 := by linear_combination hδ - 4 * hθ
    rcases mul_eq_zero.mp hprod with h | h
    · refine exists_iff_of_eq_add (c := 2 * m) (ε := 1) (by norm_num) ?_ x
      push_cast
      linear_combination h / 2
    · refine exists_iff_of_eq_add (c := 2 * m) (ε := -1) (by norm_num) ?_ x
      push_cast
      linear_combination h / 2

/-- **The discriminant of a quadratic field is a square in the field.** If $K$ is a number field
with $[K : \mathbb{Q}] = 2$, then $\operatorname{disc} K = \delta^2$ for some $\delta \in K$.

With $\theta^2 = m$ as in `NumberField.exists_sq_eq_squarefree`, take $\delta = \theta$ or
$\delta = 2\theta$, by F. Keune, *Number Fields* (2023), Example 1.44, p. 21: "For m ≡ 2, 3
(mod 4) we have disc(Q(√m)) = 4m, whereas disc(Q(√m)) = m for m ≡ 1 (mod 4)." -/
theorem exists_sq_eq_discr (hK : finrank ℚ K = 2) :
    ∃ δ : K, δ ^ 2 = discr K := by
  obtain ⟨θ, m, hθ, hm, hm1⟩ := exists_sq_eq_squarefree hK
  rw [discr_eq_of_sq_eq hK hθ hm hm1]
  by_cases hm4 : m % 4 = 1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm4)]
    exact ⟨θ, hθ⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hm4)]
    exact ⟨2 * θ, by push_cast; linear_combination 4 * hθ⟩

/-- **A fundamental discriminant that is a square in a quadratic field is its discriminant.** Let
$K$ be a number field with $[K : \mathbb{Q}] = 2$ and let $\theta \in K$ satisfy $\theta^2 = D$
for a fundamental discriminant $D \ne 1$ (`MetaMathlibExt.IsFundamentalDiscriminant`). Then
$\operatorname{disc} K = D$.

If $D$ is squarefree with $D \equiv 1 \pmod 4$ this is `NumberField.discr_eq_of_sq_eq` with
$m = D$; if $D = 4m$ with $m$ squarefree and $m \equiv 2, 3 \pmod 4$, apply it to $\theta/2$.
Source: F. Keune, *Number Fields* (2023), Example 1.44, p. 21: "For m ≡ 2, 3 (mod 4) we have
disc(Q(√m)) = 4m, whereas disc(Q(√m)) = m for m ≡ 1 (mod 4)." -/
theorem discr_eq_of_sq_eq_fundamental (hK : finrank ℚ K = 2) {θ : K} {D : ℤ}
    (hθ : θ ^ 2 = D) (hD : MetaMathlibExt.IsFundamentalDiscriminant D) (hD1 : D ≠ 1) :
    discr K = D := by
  rcases hD with ⟨hsq, h4⟩ | ⟨m, rfl, hm, h4⟩
  · rw [discr_eq_of_sq_eq hK hθ hsq hD1, ite_eq_left_of_eq_true _ _ (eq_true h4)]
  · have hθ' : (θ / 2) ^ 2 = m := by
      rw [div_pow, hθ]
      push_cast
      ring
    have hm1 : m ≠ 1 := by omega
    have hm4 : ¬ m % 4 = 1 := by omega
    rw [discr_eq_of_sq_eq hK hθ' hm hm1, ite_eq_right_of_eq_false _ _ (eq_false hm4)]

end NumberField
