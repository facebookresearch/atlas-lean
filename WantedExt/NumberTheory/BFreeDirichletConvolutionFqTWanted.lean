/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius

/-!
# Dirichlet convolutions over `𝔽_q[T]`

Self-contained identities from Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and
Divisor Problems over B-Free Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80:
Perron's formula (Lemma 1), the convolution identities of Lemmas 2-5 and Theorem 6, the Möbius
sums of Lemmas 6 and 7, the bounds of Lemma 8, the Euler-product asymptotics of Propositions 1-3,
the character-sum bound of Proposition 5, the `m = 1` exact sums of Proposition 4, and the
`B_κ`-free divisor-sum asymptotics of Theorems 1-5 (Theorems 2 and 4 for `h ≤ 2`).

Throughout, `F` is a finite field with `q = Fintype.card F` elements, `M` is the set of monic
polynomials, `|f| = q ^ deg f`, `μ` is `UniqueFactorizationMonoid.moebius`, and the primes `P`
of `F[T]` are the monic irreducible polynomials.
-/

open Polynomial UniqueFactorizationMonoid Filter Asymptotics

namespace MetaMathlibExt

@[expose] public section

/-- The Dirichlet convolution over monic divisors in `F[T]`:
`(α * β)(f) = ∑_{g ∈ M, g ∣ f} α(g) β(f / g)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of the
Dirichlet convolution. -/
public noncomputable def monicDirichletConv {F : Type*} [Field F] (α β : F[X] → ℂ)
    (f : F[X]) : ℂ :=
  ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, α g * β (f /ₘ g)

/-- The only monic divisor of `1` is `1`, so `(α * β)(1) = α(1) β(1)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of the
Dirichlet convolution. -/
public theorem monicDirichletConv_one {F : Type*} [Field F] (α β : F[X] → ℂ) :
    monicDirichletConv α β 1 = α 1 * β 1 := by
  have hset : {g : F[X] | g.Monic ∧ g ∣ 1} = {1} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hm, hg⟩
      exact hm.isUnit_iff.mp (isUnit_of_dvd_one hg)
    · rintro rfl
      exact ⟨monic_one, dvd_rfl⟩
  rw [monicDirichletConv, hset, finsum_mem_singleton, divByMonic_one]

/-- Perron's formula over `𝔽_q[T]`: if `A(u) = ∑_{f ∈ M} a(f) u^{deg f}` converges absolutely on
`|u| ≤ ρ` with `0 < ρ < 1`, then
`∑_{f ∈ M, deg f ≤ n} a(f) = (2πi)⁻¹ ∮_{|u| = ρ} A(u) / (u^n (1 - u)) du / u`.
Absolute convergence is stated as summability of `‖a f‖ ρ^{deg f}` over monic `f`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 1 (Perron's Formula)
(`integers-2026-A80-lem-1`). -/
public theorem_wanted monic_perron_formula {F : Type*} [Field F] [Finite F]
    (a : F[X] → ℂ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (habs : Summable fun f : {f : F[X] // f.Monic} => ‖a f‖ * ρ ^ (f : F[X]).natDegree)
    (n : ℕ) :
    ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ n}, a f =
      (2 * Real.pi * Complex.I)⁻¹ •
        ∮ u in C(0, ρ),
          (∑' f : {f : F[X] // f.Monic}, a f * u ^ (f : F[X]).natDegree) /
            (u ^ n * (1 - u)) * u⁻¹

/-- For completely multiplicative `α, β` and monic `f, g`,
`(α * β)(f g) = ∑_{ℓ ∈ M, ℓ ∣ f, ℓ ∣ g} μ(ℓ) α(ℓ) β(ℓ) (α * β)(f / ℓ) (α * β)(g / ℓ)`.
Complete multiplicativity is encoded by taking `α, β` to be monoid homomorphisms
`F[T] →* ℂ`; every completely multiplicative function on monic polynomials extends to one
(send nonzero constants to `1` and `0` to `0`), and only values on monic polynomials enter.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 2
(`integers-2026-A80-lem-2`). -/
public theorem_wanted monicDirichletConv_mul_of_completelyMultiplicative {F : Type*} [Field F]
    (α β : F[X] →* ℂ) {f g : F[X]} (hf : f.Monic) (hg : g.Monic) :
    monicDirichletConv α β (f * g) =
      ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ f ∧ ℓ ∣ g},
        (moebius ℓ : ℂ) * α ℓ * β ℓ * monicDirichletConv α β (f /ₘ ℓ) *
          monicDirichletConv α β (g /ₘ ℓ)

/-- For monic `f`, `∑_{g ∈ M, g ∣ f} μ(g) / |g| = Φ(f) / |f| = ∏_{P ∣ f} (1 - 1 / |P|)`, where
`Φ(f) = |f| ∏_{P ∣ f} (1 - 1/|P|)` is the paper's Euler totient; the right side is written as
the product, so `Φ` is not introduced.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 6
(`integers-2026-A80-lem-6`); `Φ` as defined after Theorem 3. -/
public theorem_wanted monic_sum_moebius_div_norm {F : Type*} [Field F] [Fintype F] {f : F[X]}
    (hf : f.Monic) :
    ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f},
        (moebius g : ℝ) / (Fintype.card F : ℝ) ^ g.natDegree =
      ∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ f},
        (1 - 1 / (Fintype.card F : ℝ) ^ P.natDegree)

/-- For monic `f`, `∑_{g ∈ M, g ∣ f} μ(g) deg(g) / |g| = (Φ(f) / |f|) ∑_{P ∣ f} deg P / (1 - |P|)`,
with `Φ(f) / |f| = ∏_{P ∣ f} (1 - 1/|P|)` written as the product.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 7
(`integers-2026-A80-lem-7`); `Φ` as defined after Theorem 3. -/
public theorem_wanted monic_sum_moebius_mul_natDegree_div_norm {F : Type*} [Field F] [Fintype F]
    {f : F[X]} (hf : f.Monic) :
    ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f},
        (moebius g : ℝ) * g.natDegree / (Fintype.card F : ℝ) ^ g.natDegree =
      (∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ f},
          (1 - 1 / (Fintype.card F : ℝ) ^ P.natDegree)) *
        ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ f},
          (P.natDegree : ℝ) / (1 - (Fintype.card F : ℝ) ^ P.natDegree)

/-- The number of monic polynomials of degree at most `N` is `(q^{N+1} - 1) / (q - 1)`
(Proposition 4, case `h = 1`, `m = 1`).

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 4
(`integers-2026-A80-prop-4`), case `h = 1`, `m = 1`. -/
public theorem_wanted monic_count_natDegree_le {F : Type*} [Field F] [Fintype F] (N : ℕ) :
    (Nat.card {f : F[X] // f.Monic ∧ f.natDegree ≤ N} : ℚ) =
      ((Fintype.card F : ℚ) ^ (N + 1) - 1) / (Fintype.card F - 1)

/-- `∑_{f ∈ M, deg f ≤ N} (1 * 1)(f) = ((N + 1) q^{N+2} - (N + 2) q^{N+1} + 1) / (q - 1)^2`, where
`(1 * 1)(f)` is the number of monic divisors of `f` (Proposition 4, case `h = 2`, `m = 1`).

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 4
(`integers-2026-A80-prop-4`), case `h = 2`, `m = 1`. -/
public theorem_wanted monic_sum_divisorCount_natDegree_le {F : Type*} [Field F] [Fintype F]
    (N : ℕ) :
    ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ N},
        monicDirichletConv (fun _ => (1 : ℂ)) (fun _ => 1) f =
      (((N + 1 : ℂ) * (Fintype.card F : ℂ) ^ (N + 2) - (N + 2) * (Fintype.card F : ℂ) ^ (N + 1)
          + 1) / ((Fintype.card F : ℂ) - 1) ^ 2)

/-- The norm `|f| = q ^ deg f` of a nonzero `f ∈ 𝔽_q[T]`, with `|0| = 0`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of the
norm. -/
public noncomputable def fqNorm {F : Type*} [Field F] [Fintype F] (f : F[X]) : ℝ :=
  open scoped Classical in
  if f = 0 then 0 else (Fintype.card F : ℝ) ^ f.natDegree

/-- For `f ≠ 0`, `|f| = q ^ deg f`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of the
norm. -/
public theorem fqNorm_of_ne_zero {F : Type*} [Field F] [Fintype F] {f : F[X]} (hf : f ≠ 0) :
    fqNorm f = (Fintype.card F : ℝ) ^ f.natDegree := by
  classical
  simp [fqNorm, hf]

/-- The norm is multiplicative on nonzero polynomials: `|f g| = |f| |g|`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of the
norm. -/
public theorem fqNorm_mul {F : Type*} [Field F] [Fintype F] {f g : F[X]} (hf : f ≠ 0)
    (hg : g ≠ 0) : fqNorm (f * g) = fqNorm f * fqNorm g := by
  rw [fqNorm_of_ne_zero (mul_ne_zero hf hg), fqNorm_of_ne_zero hf, fqNorm_of_ne_zero hg,
    natDegree_mul hf hg, pow_add]

/-- The only monic polynomial of degree at most `0` is `1`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 2, the set
`M_{≤ 0}`. -/
public theorem monic_natDegree_le_zero_iff {F : Type*} [Field F] {f : F[X]} :
    f.Monic ∧ f.natDegree ≤ 0 ↔ f = 1 := by
  constructor
  · rintro ⟨hm, hd⟩
    exact eq_one_of_monic_natDegree_zero hm (Nat.le_zero.mp hd)
  · rintro rfl
    exact ⟨monic_one, by simp⟩

/-- `f ∈ 𝔽_q[T]` is `B_κ`-free when no `P ^ κ(P)`, `P` monic irreducible, divides it.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`B_κ`-free polynomials. -/
public def IsBFree {F : Type*} [Field F] (κ : F[X] → ℕ) (f : F[X]) : Prop :=
  ∀ P : F[X], P.Monic → Irreducible P → ¬ P ^ κ P ∣ f

/-- `1` is `B_κ`-free when every `κ(P)` is nonzero.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`B_κ`-free polynomials. -/
public theorem isBFree_one {F : Type*} [Field F] (κ : F[X] → ℕ)
    (hκ : ∀ P : F[X], P.Monic → Irreducible P → κ P ≠ 0) : IsBFree κ (1 : F[X]) := by
  intro P hm hP hdvd
  exact hP.not_isUnit ((isUnit_pow_iff (hκ P hm hP)).mp (isUnit_of_dvd_one hdvd))

/-- `κ_min = min_P κ(P)` over the monic irreducible `P`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`κ_min`. -/
public noncomputable def kappaMin {F : Type*} [Field F] (κ : F[X] → ℕ) : ℕ :=
  ⨅ P : {P : F[X] // P.Monic ∧ Irreducible P}, κ P

/-- `κ_min ≤ κ(P)` for every monic irreducible `P`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`κ_min`. -/
public theorem kappaMin_le {F : Type*} [Field F] (κ : F[X] → ℕ) {P : F[X]} (hm : P.Monic)
    (hP : Irreducible P) : kappaMin κ ≤ κ P :=
  ciInf_le (OrderBot.bddBelow _) (⟨P, hm, hP⟩ : {P : F[X] // P.Monic ∧ Irreducible P})

/-- `f ^ κ = ∏_P P ^ (ν_P(f) κ(P))` for `f = ∏_P P ^ ν_P(f)` monic.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`f ^ κ`. -/
public noncomputable def kappaPow {F : Type*} [Field F] (κ : F[X] → ℕ) (f : F[X]) : F[X] :=
  open scoped Classical in
  ((normalizedFactors f).map fun P => P ^ κ P).prod

/-- `1 ^ κ = 1`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`f ^ κ`. -/
public theorem kappaPow_one {F : Type*} [Field F] (κ : F[X] → ℕ) :
    kappaPow κ (1 : F[X]) = 1 := by
  classical
  simp [kappaPow]

/-- `P ^ κ = P ^ κ(P)` for monic irreducible `P`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`f ^ κ`. -/
public theorem kappaPow_of_irreducible {F : Type*} [Field F] (κ : F[X] → ℕ) {P : F[X]}
    (hm : P.Monic) (hP : Irreducible P) : kappaPow κ P = P ^ κ P := by
  classical
  simp [kappaPow, normalizedFactors_irreducible hP, hm.normalize_eq_self]

/-- The `h`-divisor function `d_h(f) = #{(g_1, …, g_h) ∈ M^h : g_1 ⋯ g_h = f}`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`d_h`. -/
public noncomputable def monicDivisorCount {F : Type*} [Field F] (h : ℕ) (f : F[X]) : ℕ :=
  Nat.card {v : Fin h → F[X] // (∀ i, (v i).Monic) ∧ ∏ i, v i = f}

/-- `d_h(1) = 1`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`d_h`. -/
public theorem monicDivisorCount_one {F : Type*} [Field F] (h : ℕ) :
    monicDivisorCount h (1 : F[X]) = 1 := by
  rw [monicDivisorCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨fun _ => 1, fun _ => monic_one, by simp⟩, ?_⟩
  rintro ⟨v, hv, hprod⟩
  apply Subtype.ext
  funext i
  have hdvd : v i ∣ 1 := hprod ▸ Finset.dvd_prod_of_mem v (Finset.mem_univ i)
  exact (hv i).isUnit_iff.mp (isUnit_of_dvd_one hdvd)

/-- `d_0(f) = 0` for `f ≠ 1` (the empty product is `1`).

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`d_h`. -/
public theorem monicDivisorCount_zero_of_ne_one {F : Type*} [Field F] {f : F[X]} (hf : f ≠ 1) :
    monicDivisorCount 0 f = 0 := by
  rw [monicDivisorCount, Nat.card_eq_zero]
  left
  exact ⟨fun ⟨v, _, hv⟩ => hf (by simpa using hv.symm)⟩

/-- `d_1(f) = 1` for monic `f`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`d_h`. -/
public theorem monicDivisorCount_one_left {F : Type*} [Field F] {f : F[X]} (hf : f.Monic) :
    monicDivisorCount 1 f = 1 := by
  rw [monicDivisorCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨fun _ => f, fun _ => hf, by simp⟩, ?_⟩
  rintro ⟨v, hv, hprod⟩
  apply Subtype.ext
  funext i
  obtain rfl := Subsingleton.elim i 0
  simpa using hprod

/-- `S_f[α, β](n) = ∑_{g ∈ M, deg f + deg g ≤ n} (α * β)(f g)` (the paper's `g ∈ M_{≤ n - deg f}`).

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, eq. (3). -/
public noncomputable def monicConvShiftedSum {F : Type*} [Field F] (α β : F[X] → ℂ)
    (f : F[X]) (n : ℕ) : ℂ :=
  ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ f.natDegree + g.natDegree ≤ n}, monicDirichletConv α β (f * g)

/-- `S_f[α, β](n) = 0` when `n < deg f`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, eq. (3). -/
public theorem monicConvShiftedSum_of_lt {F : Type*} [Field F] (α β : F[X] → ℂ) {f : F[X]}
    {n : ℕ} (hn : n < f.natDegree) : monicConvShiftedSum α β f n = 0 := by
  have hset : {g : F[X] | g.Monic ∧ f.natDegree + g.natDegree ≤ n} = ∅ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro _
    omega
  rw [monicConvShiftedSum, hset, finsum_mem_empty]

/-- `D[α, β](n) = ∑_{g ∈ M_{≤ n}} (α * β)(g)`, taken as `0` for `n < 0` (empty range), which is
how the paper's Lemma 3 uses it at `n - deg(f ℓ)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[α, β](n)`. -/
public noncomputable def monicConvPartialSum {F : Type*} [Field F] (α β : F[X] → ℂ) (n : ℤ) : ℂ :=
  ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ (g.natDegree : ℤ) ≤ n}, monicDirichletConv α β g

/-- `D[α, β](n) = 0` for `n < 0`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[α, β](n)`. -/
public theorem monicConvPartialSum_of_neg {F : Type*} [Field F] (α β : F[X] → ℂ) {n : ℤ}
    (hn : n < 0) : monicConvPartialSum α β n = 0 := by
  have hset : {g : F[X] | g.Monic ∧ (g.natDegree : ℤ) ≤ n} = ∅ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro _
    omega
  rw [monicConvPartialSum, hset, finsum_mem_empty]

/-- `D[α, β](0) = α(1) β(1)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[α, β](n)`. -/
public theorem monicConvPartialSum_zero {F : Type*} [Field F] (α β : F[X] → ℂ) :
    monicConvPartialSum α β 0 = α 1 * β 1 := by
  have hset : {g : F[X] | g.Monic ∧ (g.natDegree : ℤ) ≤ 0} = {1} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [← monic_natDegree_le_zero_iff]
    exact and_congr_right fun _ => ⟨fun h => by omega, fun h => by omega⟩
  rw [monicConvPartialSum, hset, finsum_mem_singleton, monicDirichletConv_one]

/-- `D[γ, α, β](n) = ∑_{f ∈ M_{≤ n}} γ(f) (α * β)(f)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[γ, α, β](n)`. -/
public noncomputable def weightedMonicConvSum {F : Type*} [Field F] (γ α β : F[X] → ℂ)
    (n : ℕ) : ℂ :=
  ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ n}, γ f * monicDirichletConv α β f

/-- `D[γ, α, β](0) = γ(1) α(1) β(1)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[γ, α, β](n)`. -/
public theorem weightedMonicConvSum_zero {F : Type*} [Field F] (γ α β : F[X] → ℂ) :
    weightedMonicConvSum γ α β 0 = γ 1 * (α 1 * β 1) := by
  have hset : {f : F[X] | f.Monic ∧ f.natDegree ≤ 0} = {1} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact monic_natDegree_le_zero_iff
  rw [weightedMonicConvSum, hset, finsum_mem_singleton, monicDirichletConv_one]

/-- Lemma 3: for completely multiplicative `α, β` (monoid homomorphisms, as in Lemma 2) and monic
`f`, `S_f[α, β](n) = ∑_{d ∣ f} α(d) β(f/d) ∑_{ℓ ∣ d} μ(ℓ) β(ℓ) D[α, β](n - deg(f ℓ))`, sums over
monic divisors; `D` vanishes at negative arguments. The paper leaves `f ∈ 𝔽_q[T]` unrestricted; its
proof applies Lemma 2, which needs `f` monic.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 3
(`integers-2026-A80-lem-3`). -/
public theorem_wanted monicConvShiftedSum_eq_of_completelyMultiplicative {F : Type*} [Field F]
    [Finite F] (α β : F[X] →* ℂ) {f : F[X]} (hf : f.Monic) (n : ℕ) :
    monicConvShiftedSum α β f n =
      ∑ᶠ d ∈ {d : F[X] | d.Monic ∧ d ∣ f}, α d * β (f /ₘ d) *
        ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ d},
          (moebius ℓ : ℂ) * β ℓ * monicConvPartialSum α β ((n : ℤ) - (f * ℓ).natDegree)

/-- Lemma 4: for arbitrary `α, β, γ`,
`D[γ, α, β](n) = ∑_{f ∈ M_{≤ n}} λ(f) S_f[α, β](n)` with `λ = γ * μ`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 4
(`integers-2026-A80-lem-4`). -/
public theorem_wanted weightedMonicConvSum_eq_sum_shifted {F : Type*} [Field F] [Finite F]
    (γ α β : F[X] → ℂ) (n : ℕ) :
    weightedMonicConvSum γ α β n =
      ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ n},
        monicDirichletConv γ (fun g => (moebius g : ℂ)) f * monicConvShiftedSum α β f n

/-- Theorem 6 (function-field Camargo identity): for completely multiplicative `α, β` and any `γ`,
`D[γ, α, β](n) = ∑_{deg f ≤ n} (γ * μ)(f) ∑_{d ∣ f} α(d) β(f/d) ∑_{ℓ ∣ d} μ(ℓ) β(ℓ)
D[α, β](n - deg(f ℓ))`, all sums over monic polynomials.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 6
(`integers-2026-A80-thm-6`). -/
public theorem_wanted weightedMonicConvSum_eq_of_completelyMultiplicative {F : Type*} [Field F]
    [Finite F] (γ : F[X] → ℂ) (α β : F[X] →* ℂ) (n : ℕ) :
    weightedMonicConvSum γ α β n =
      ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ n},
        monicDirichletConv γ (fun g => (moebius g : ℂ)) f *
          ∑ᶠ d ∈ {d : F[X] | d.Monic ∧ d ∣ f}, α d * β (f /ₘ d) *
            ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ d},
              (moebius ℓ : ℂ) * β ℓ * monicConvPartialSum α β ((n : ℤ) - (f * ℓ).natDegree)

/-- Lemma 5: for monic `f` and positive `κ(P)`, `(1_{B_κ} * μ)(f) = μ(f^{1/κ})` if `f^{1/κ} ∈ M`
and `0` otherwise. `f^{1/κ} ∈ M` means `f = r ^ κ` for a (unique) monic `r`, so the right side is
the sum of `μ(r)` over monic `r` with `r ^ κ = f`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 5
(`integers-2026-A80-lem-5`). -/
public theorem_wanted monicDirichletConv_bFreeIndicator_moebius {F : Type*} [Field F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → κ P ≠ 0) {f : F[X]}
    (hf : f.Monic) :
    monicDirichletConv ({g : F[X] | IsBFree κ g}.indicator 1) (fun g => (moebius g : ℂ)) f =
      ∑ᶠ r ∈ {r : F[X] | r.Monic ∧ kappaPow κ r = f}, (moebius r : ℂ)

/-- Lemma 8, bound (6): for `κ ≥ 2` and `N ≥ 1`,
`|∑_{r ∈ M, deg r^κ ≤ N} μ(r) ∑_{f ∣ r^κ} ∑_{ℓ ∣ f} μ(ℓ)| ≤ q ^ (N / κ_min)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 8, eq. (6)
(`integers-2026-A80-lem-8`). -/
public theorem_wanted abs_sum_moebius_kappaPow_le {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {N : ℕ} (hN : 1 ≤ N) :
    |∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N},
        (moebius r : ℝ) * ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r},
          ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ f}, (moebius ℓ : ℝ)| ≤
      (Fintype.card F : ℝ) ^ ((N : ℝ) / kappaMin κ)

/-- Lemma 8, bound (7): for `κ ≥ 2` and every `ε > 0`,
`∑_{r ∈ M, deg r^κ ≤ N} ∑_{f ∣ r^κ} ∑_{ℓ ∣ f} 1 = O(q ^ ((1/κ_min + ε) N))` as `N → ∞`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Lemma 8, eq. (7)
(`integers-2026-A80-lem-8`). -/
public theorem_wanted sum_divisors_kappaPow_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => ((∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N},
        ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r},
          Nat.card {ℓ : F[X] // ℓ.Monic ∧ ℓ ∣ f} : ℕ) : ℝ)) =O[atTop]
      fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε) * N)

/-- Proposition 1: for `κ ≥ 2`, fixed monic `m`, `h ≥ 1` and `ε > 0`,
`∑_{r ∈ M, deg r^κ ≤ N, (r, m) = 1} μ(r)/|r^κ| ∑_{f ∣ r^κ} d_{h-1}(f) ∑_{g ∣ f} μ(g)/|g|
= ∏_{P ∤ m} [1 - |P|^{-κ(P)} (C_P + |P|^{-1} (1 - C_P))] + O(q ^ ((1/κ_min + ε - 1)(N + 1)))`
with `C_P = binom(h + κ(P) - 1, κ(P))`; `(r, m) = 1` is `IsCoprime r m` and `|P^{κ(P)}|` is written
`|P|^{κ(P)}`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 1
(`integers-2026-A80-prop-1`). -/
public theorem_wanted sum_moebius_kappaPow_divisorCount_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {m : F[X]}
    (hm : m.Monic) {h : ℕ} (hh : 1 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ =>
      (∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N ∧ IsCoprime r m},
          (moebius r : ℝ) / fqNorm (kappaPow κ r) *
            ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r}, (monicDivisorCount (h - 1) f : ℝ) *
              ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, (moebius g : ℝ) / fqNorm g) -
        ∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
          (1 - 1 / fqNorm (P : F[X]) ^ κ P *
            ((Nat.choose (h + κ P - 1) (κ P) : ℝ) +
              1 / fqNorm (P : F[X]) * (1 - (Nat.choose (h + κ P - 1) (κ P) : ℝ))))) =O[atTop]
      fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε - 1) * (N + 1))

/-- Proposition 2: for `κ ≥ 2`, fixed monic `m` and `ε > 0`,
`∑_{deg r^κ ≤ N, (r, m) = 1} μ(r)/|r^κ| ∑_{f ∣ r^κ} ∑_{g ∣ f} μ(g) deg(g)/|g|
= ∏_{P ∤ m} (1 - (κ+1)/|P|^κ + κ/|P|^{κ+1}) ∑_{P ∤ m} κ deg P / (|P|^{κ+1} - |P|(κ+1) + κ)
+ O(q ^ ((1/κ_min + ε - 1)(N + 1)))`, with `κ = κ(P)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 2
(`integers-2026-A80-prop-2`). -/
public theorem_wanted sum_moebius_kappaPow_moebius_natDegree_isBigO {F : Type*} [Field F]
    [Fintype F] (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {m : F[X]}
    (hm : m.Monic) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ =>
      (∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N ∧ IsCoprime r m},
          (moebius r : ℝ) / fqNorm (kappaPow κ r) *
            ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r},
              ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, (moebius g : ℝ) * g.natDegree / fqNorm g) -
        (∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - (κ P + 1 : ℝ) / fqNorm (P : F[X]) ^ κ P +
              (κ P : ℝ) / fqNorm (P : F[X]) ^ (κ P + 1))) *
          ∑' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (κ P : ℝ) * (P : F[X]).natDegree /
              (fqNorm (P : F[X]) ^ (κ P + 1) - fqNorm (P : F[X]) * (κ P + 1) + κ P)) =O[atTop]
      fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε - 1) * (N + 1))

/-- Proposition 3: for `κ ≥ 2`, fixed monic `m` and `ε > 0`,
`∑_{deg r^κ ≤ N, (r, m) = 1} μ(r) deg(r^κ)/|r^κ| ∑_{f ∣ r^κ} ∑_{g ∣ f} μ(g)/|g|
= -∏_{P ∤ m} (1 - (κ+1)/|P|^κ + κ/|P|^{κ+1})
× ∑_{P ∤ m} κ deg P (|P|(κ+1) - κ) / (|P|^{κ+1} - |P|(κ+1) + κ)
+ O(q ^ ((1/κ_min + ε - 1)(N + 1)))`, with `κ = κ(P)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 3
(`integers-2026-A80-prop-3`). -/
public theorem_wanted sum_moebius_natDegree_kappaPow_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {m : F[X]}
    (hm : m.Monic) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ =>
      (∑ᶠ r ∈ {r : F[X] | r.Monic ∧ (kappaPow κ r).natDegree ≤ N ∧ IsCoprime r m},
          (moebius r : ℝ) * (kappaPow κ r).natDegree / fqNorm (kappaPow κ r) *
            ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f ∣ kappaPow κ r},
              ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, (moebius g : ℝ) / fqNorm g) +
        (∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - (κ P + 1 : ℝ) / fqNorm (P : F[X]) ^ κ P +
              (κ P : ℝ) / fqNorm (P : F[X]) ^ (κ P + 1))) *
          ∑' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (κ P : ℝ) * (P : F[X]).natDegree * (fqNorm (P : F[X]) * (κ P + 1) - κ P) /
              (fqNorm (P : F[X]) ^ (κ P + 1) - fqNorm (P : F[X]) * (κ P + 1) + κ P)) =O[atTop]
      fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε - 1) * (N + 1))

/-- Proposition 5: for a non-principal Dirichlet character `χ` modulo monic `m` (a multiplicative
character of `𝔽_q[T]/(m)`, zero off the units) and `h ≥ 1`,
`|∑_{f ∈ M_{≤ N}} χ^{(h)}(f)| ≤ (√q + 1) ^ (h (deg m - 1))`, where `χ^{(h)}(f) = χ(f) d_h(f)` by
eq. (8). The paper's trailing `= O(q^{h deg(m)/2})` is a coarser restatement and is omitted.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Proposition 5
(`integers-2026-A80-prop-5`); `χ^{(h)}` as in eq. (8). -/
public theorem_wanted norm_sum_mulChar_divisorCount_le {F : Type*} [Field F] [Fintype F]
    {m : F[X]} (hm : m.Monic) (χ : MulChar (F[X] ⧸ Ideal.span {m}) ℂ) (hχ : χ ≠ 1) {h : ℕ}
    (hh : 1 ≤ h) (N : ℕ) :
    ‖∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ N},
        χ (Ideal.Quotient.mk (Ideal.span {m}) f) * (monicDivisorCount h f : ℂ)‖ ≤
      (Real.sqrt (Fintype.card F) + 1) ^ (h * (m.natDegree - 1))

/-- `D̃_{B_κ,h}(N) = ∑_{f ∈ M_{≤ N}} 1_{B_κ}(f) d_h(f)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`D̃_{B_κ,h}(N)`. -/
public noncomputable def bFreeDivisorSum {F : Type*} [Field F] (κ : F[X] → ℕ) (h N : ℕ) : ℕ :=
  ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ N ∧ IsBFree κ f}, monicDivisorCount h f

/-- `D̃_{B_κ,h}(0) = 1` when every `κ(P)` is nonzero.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`D̃_{B_κ,h}(N)`. -/
public theorem bFreeDivisorSum_zero {F : Type*} [Field F] (κ : F[X] → ℕ)
    (hκ : ∀ P : F[X], P.Monic → Irreducible P → κ P ≠ 0) (h : ℕ) :
    bFreeDivisorSum κ h 0 = 1 := by
  have hset : {f : F[X] | f.Monic ∧ f.natDegree ≤ 0 ∧ IsBFree κ f} = {1} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hm, hd, -⟩
      exact monic_natDegree_le_zero_iff.mp ⟨hm, hd⟩
    · rintro rfl
      exact ⟨monic_one, by simp, isBFree_one κ hκ⟩
  rw [bFreeDivisorSum, hset, finsum_mem_singleton, monicDivisorCount_one]

/-- `D̃_{B_κ,h}(N, a, m) = ∑_{f ∈ M_{≤ N}, f ≡ a (mod m)} 1_{B_κ}(f) d_h(f)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`D̃_{B_κ,h}(N, a, m)`. -/
public noncomputable def bFreeDivisorSumMod {F : Type*} [Field F] (κ : F[X] → ℕ) (h N : ℕ)
    (a m : F[X]) : ℕ :=
  ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ N ∧ IsBFree κ f ∧ m ∣ f - a}, monicDivisorCount h f

/-- Modulo `m = 1` the progression sum is the full sum: `D̃_{B_κ,h}(N, a, 1) = D̃_{B_κ,h}(N)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 1, definition of
`D̃_{B_κ,h}(N, a, m)`. -/
public theorem bFreeDivisorSumMod_one {F : Type*} [Field F] (κ : F[X] → ℕ) (h N : ℕ)
    (a : F[X]) : bFreeDivisorSumMod κ h N a 1 = bFreeDivisorSum κ h N := by
  simp [bFreeDivisorSumMod, bFreeDivisorSum]

/-- Theorem 1, case `h = 1`: for `κ ≥ 2` and every `ε > 0`,
`D̃_{B_κ,1}(N) = q^N / (1 - 1/q) ∏_P (1 - 1/|P|^{κ(P)}) + O(q ^ ((1/κ_min + ε) N))`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 1, first formula
(`integers-2026-A80-thm-1`). -/
public theorem_wanted bFreeDivisorSum_one_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => (bFreeDivisorSum κ 1 N : ℝ) -
        (Fintype.card F : ℝ) ^ N / (1 - 1 / (Fintype.card F : ℝ)) *
          ∏' P : {P : F[X] // P.Monic ∧ Irreducible P}, (1 - 1 / fqNorm (P : F[X]) ^ κ P))
      =O[atTop] fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε) * N)

/-- Theorem 1, case `h = 2`: for `κ ≥ 2` and every `ε > 0`,
`D̃_{B_κ,2}(N) = q^N / (1 - 1/q) ∏_P (1 - (κ+1)/|P|^κ + κ/|P|^{κ+1})
× [N + 1 - 1/(q - 1) + ∑_P κ(κ+1) deg(P) (|P| - 1) / (|P|^{κ+1} - |P|(κ+1) + κ)]
+ O(q ^ ((1/κ_min + ε) N))`, with `κ = κ(P)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 1, second formula
(`integers-2026-A80-thm-1`). -/
public theorem_wanted bFreeDivisorSum_two_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => (bFreeDivisorSum κ 2 N : ℝ) -
        (Fintype.card F : ℝ) ^ N / (1 - 1 / (Fintype.card F : ℝ)) *
          (∏' P : {P : F[X] // P.Monic ∧ Irreducible P},
            (1 - (κ P + 1 : ℝ) / fqNorm (P : F[X]) ^ κ P +
              (κ P : ℝ) / fqNorm (P : F[X]) ^ (κ P + 1))) *
          ((N : ℝ) + 1 - 1 / ((Fintype.card F : ℝ) - 1) +
            ∑' P : {P : F[X] // P.Monic ∧ Irreducible P},
              (κ P : ℝ) * (κ P + 1) * (P : F[X]).natDegree * (fqNorm (P : F[X]) - 1) /
                (fqNorm (P : F[X]) ^ (κ P + 1) - fqNorm (P : F[X]) * (κ P + 1) + κ P)))
      =O[atTop] fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε) * N)

/-- Theorem 2 for `h ∈ {1, 2}`: for `κ ≥ 2`,
`D̃_{B_κ,h}(N) = q^N N^{h-1} / (1 - 1/q) ∏_P [1 - |P|^{-κ(P)} (C_P + |P|^{-1} (1 - C_P))]
(1 + O(1/N))` with `C_P = binom(h + κ(P) - 1, κ(P))`, stated as
`D̃ - main = O(main / N)`. For `h ≥ 3` the printed main term is wrong (see the audit row).

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 2, cases `h = 1, 2`
(`integers-2026-A80-thm-2`). -/
public theorem_wanted bFreeDivisorSum_isBigO_of_le_two {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {h : ℕ} (hh1 : 1 ≤ h)
    (hh2 : h ≤ 2) :
    (fun N : ℕ => (bFreeDivisorSum κ h N : ℝ) -
        (Fintype.card F : ℝ) ^ N * (N : ℝ) ^ (h - 1) / (1 - 1 / (Fintype.card F : ℝ)) *
          ∏' P : {P : F[X] // P.Monic ∧ Irreducible P},
            (1 - 1 / fqNorm (P : F[X]) ^ κ P *
              ((Nat.choose (h + κ P - 1) (κ P) : ℝ) +
                1 / fqNorm (P : F[X]) * (1 - (Nat.choose (h + κ P - 1) (κ P) : ℝ)))))
      =O[atTop] fun N : ℕ =>
        (Fintype.card F : ℝ) ^ N * (N : ℝ) ^ (h - 1) / (1 - 1 / (Fintype.card F : ℝ)) *
          (∏' P : {P : F[X] // P.Monic ∧ Irreducible P},
            (1 - 1 / fqNorm (P : F[X]) ^ κ P *
              ((Nat.choose (h + κ P - 1) (κ P) : ℝ) +
                1 / fqNorm (P : F[X]) * (1 - (Nat.choose (h + κ P - 1) (κ P) : ℝ))))) / N

/-- Theorem 3, case `h = 1`: for `κ ≥ 2`, `m ≠ 0`, `(a, m) = 1` and every `ε > 0`,
`D̃_{B_κ,1}(N, a, m) = q^N / ((1 - 1/q) |m|) ∏_{P ∤ m} (1 - 1/|P|^{κ(P)})
+ O(q ^ ((1/κ_min + ε) N))`.
`m ≠ 0` is added (the modulus of a progression).

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 3, first formula
(`integers-2026-A80-thm-3`). -/
public theorem_wanted bFreeDivisorSumMod_one_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {a m : F[X]}
    (hm : m ≠ 0) (ham : IsCoprime a m) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => (bFreeDivisorSumMod κ 1 N a m : ℝ) -
        (Fintype.card F : ℝ) ^ N / ((1 - 1 / (Fintype.card F : ℝ)) * fqNorm m) *
          ∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - 1 / fqNorm (P : F[X]) ^ κ P))
      =O[atTop] fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε) * N)

/-- Theorem 3, case `h = 2`: for `κ ≥ 2`, `m ≠ 0`, `(a, m) = 1` and every `ε > 0`,
`D̃_{B_κ,2}(N, a, m) = q^N Φ(m) / ((1 - 1/q) |m|^2) ∏_{P ∤ m} (1 - (κ+1)/|P|^κ + κ/|P|^{κ+1})
× [N + 1 - 1/(q - 1) + 2 ∑_{P ∣ m} deg P / (|P| - 1)
+ ∑_{P ∤ m} κ(κ+1) deg(P) (|P| - 1) / (|P|^{κ+1} - |P|(κ+1) + κ)] + O(q ^ ((1/κ_min + ε) N))`,
with `Φ(m) / |m| = ∏_{P ∣ m} (1 - 1/|P|)` written as the product.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 3, second formula
(`integers-2026-A80-thm-3`); `Φ` as defined after Theorem 3. -/
public theorem_wanted bFreeDivisorSumMod_two_isBigO {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {a m : F[X]}
    (hm : m ≠ 0) (ham : IsCoprime a m) {ε : ℝ} (hε : 0 < ε) :
    (fun N : ℕ => (bFreeDivisorSumMod κ 2 N a m : ℝ) -
        (Fintype.card F : ℝ) ^ N *
            (∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ m}, (1 - 1 / fqNorm P)) /
            ((1 - 1 / (Fintype.card F : ℝ)) * fqNorm m) *
          (∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - (κ P + 1 : ℝ) / fqNorm (P : F[X]) ^ κ P +
              (κ P : ℝ) / fqNorm (P : F[X]) ^ (κ P + 1))) *
          ((N : ℝ) + 1 - 1 / ((Fintype.card F : ℝ) - 1) +
            2 * (∑ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ m},
              (P.natDegree : ℝ) / (fqNorm P - 1)) +
            ∑' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
              (κ P : ℝ) * (κ P + 1) * (P : F[X]).natDegree * (fqNorm (P : F[X]) - 1) /
                (fqNorm (P : F[X]) ^ (κ P + 1) - fqNorm (P : F[X]) * (κ P + 1) + κ P)))
      =O[atTop] fun N : ℕ => (Fintype.card F : ℝ) ^ ((1 / (kappaMin κ : ℝ) + ε) * N)

/-- Theorem 4 for `h ∈ {1, 2}`: for `κ ≥ 2`, `m ≠ 0` and `(a, m) = 1`,
`D̃_{B_κ,h}(N, a, m) = q^N N^{h-1} / (h-1)! · Φ(m)^{h-1} / |m|^h · (1 - 1/q)^{-1}
∏_{P ∤ m} [1 - |P|^{-κ(P)} (C_P + |P|^{-1} (1 - C_P))] (1 + O(1/N))`, stated as
`D̃ - main = O(main / N)`, with `Φ(m)^{h-1} / |m|^h = (Φ(m)/|m|)^{h-1} / |m|`. For `h ≥ 3` the
printed main term is wrong (see the audit row).

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 4, cases `h = 1, 2`
(`integers-2026-A80-thm-4`); `Φ` as defined after Theorem 3. -/
public theorem_wanted bFreeDivisorSumMod_isBigO_of_le_two {F : Type*} [Field F] [Fintype F]
    (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P) {a m : F[X]}
    (hm : m ≠ 0) (ham : IsCoprime a m) {h : ℕ} (hh1 : 1 ≤ h) (hh2 : h ≤ 2) :
    (fun N : ℕ => (bFreeDivisorSumMod κ h N a m : ℝ) -
        (Fintype.card F : ℝ) ^ N * (N : ℝ) ^ (h - 1) / (h - 1).factorial *
          (∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ m}, (1 - 1 / fqNorm P)) ^ (h - 1) /
          fqNorm m / (1 - 1 / (Fintype.card F : ℝ)) *
          ∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - 1 / fqNorm (P : F[X]) ^ κ P *
              ((Nat.choose (h + κ P - 1) (κ P) : ℝ) +
                1 / fqNorm (P : F[X]) * (1 - (Nat.choose (h + κ P - 1) (κ P) : ℝ)))))
      =O[atTop] fun N : ℕ =>
        (Fintype.card F : ℝ) ^ N * (N : ℝ) ^ (h - 1) / (h - 1).factorial *
          (∏ᶠ P ∈ {P : F[X] | P.Monic ∧ Irreducible P ∧ P ∣ m}, (1 - 1 / fqNorm P)) ^ (h - 1) /
          fqNorm m / (1 - 1 / (Fintype.card F : ℝ)) *
          (∏' P : {P : F[X] // P.Monic ∧ Irreducible P ∧ ¬ P ∣ m},
            (1 - 1 / fqNorm (P : F[X]) ^ κ P *
              ((Nat.choose (h + κ P - 1) (κ P) : ℝ) +
                1 / fqNorm (P : F[X]) * (1 - (Nat.choose (h + κ P - 1) (κ P) : ℝ))))) / N

/-- Theorem 5 (short intervals): let `κ ≥ 2` be symmetric (`κ(P) = κ(P^*)` with
`P^*(T) = T^{deg P} P(1/T)` made monic, for `P ≠ T`), `h ≥ 1`, `c > (h + 2/κ_min)/(h + 2)` and
`ε > 0`. Then, uniformly in monic `A` of degree `N` and `cN ≤ Δ ≤ N - 2`,
`Ñ_{B_κ,h}(A, Δ) = q^{-(N-Δ-1)} (D̃_{B_κ,h}(N) - D̃_{B_κ,h}(N-1))
+ O(q ^ (h(N-Δ)/2 + (1/κ_min + ε) N))`,
where `Ñ_{B_κ,h}(A, Δ) = ∑_{|f - A| ≤ q^Δ} 1_{B_κ}(f) d_h(f)` (`|f - A| ≤ q^Δ` is
`deg(f - A) ≤ Δ`). The paper's `κ(P^*)` leaves `P^*` unnormalized and undefined for `P = T`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 5, general formula
(`integers-2026-A80-thm-5`). -/
public theorem_wanted bFreeDivisorSum_shortInterval {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P)
    (hsymm : ∀ P : F[X], P.Monic → Irreducible P → P.coeff 0 ≠ 0 →
      κ (normalize P.reverse) = κ P)
    {h : ℕ} (hh : 1 ≤ h) {c : ℝ} (hc : (h + 2 / (kappaMin κ : ℝ)) / (h + 2) < c) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ N in atTop, ∀ A : F[X], A.Monic → A.natDegree = N → ∀ Δ : ℕ,
      c * N ≤ Δ → Δ + 2 ≤ N →
        |(∑ᶠ f ∈ {f : F[X] | (f - A).degree ≤ Δ ∧ IsBFree κ f}, (monicDivisorCount h f : ℝ)) -
            ((bFreeDivisorSum κ h N : ℝ) - bFreeDivisorSum κ h (N - 1)) /
              (Fintype.card F : ℝ) ^ (N - Δ - 1)| ≤
          C * (Fintype.card F : ℝ) ^ (h * ((N : ℝ) - Δ) / 2 + (1 / (kappaMin κ : ℝ) + ε) * N)

/-- Theorem 5, case `h = 1`: under the hypotheses of `bFreeDivisorSum_shortInterval` with `h = 1`,
`Ñ_{B_κ,1}(A, Δ) = q^{Δ+1} ∏_P (1 - 1/|P|^{κ(P)}) + O(q ^ ((N-Δ)/2 + (1/κ_min + ε) N))`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 5, case `h = 1`
(`integers-2026-A80-thm-5`). -/
public theorem_wanted bFreeDivisorSum_shortInterval_one {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P)
    (hsymm : ∀ P : F[X], P.Monic → Irreducible P → P.coeff 0 ≠ 0 →
      κ (normalize P.reverse) = κ P)
    {c : ℝ} (hc : (1 + 2 / (kappaMin κ : ℝ)) / 3 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ N in atTop, ∀ A : F[X], A.Monic → A.natDegree = N → ∀ Δ : ℕ,
      c * N ≤ Δ → Δ + 2 ≤ N →
        |(∑ᶠ f ∈ {f : F[X] | (f - A).degree ≤ Δ ∧ IsBFree κ f}, (monicDivisorCount 1 f : ℝ)) -
            (Fintype.card F : ℝ) ^ (Δ + 1) *
              ∏' P : {P : F[X] // P.Monic ∧ Irreducible P}, (1 - 1 / fqNorm (P : F[X]) ^ κ P)| ≤
          C * (Fintype.card F : ℝ) ^ (((N : ℝ) - Δ) / 2 + (1 / (kappaMin κ : ℝ) + ε) * N)

/-- Theorem 5, case `h = 2`: under the hypotheses of `bFreeDivisorSum_shortInterval` with `h = 2`,
`Ñ_{B_κ,2}(A, Δ) = q^{Δ+1} ∏_P (1 - (κ+1)/|P|^κ + κ/|P|^{κ+1})
× [N + 1 + ∑_P κ deg(P) (κ+1) (|P| - 1) / (|P|^{κ+1} - |P|(κ+1) + κ)]
+ O(q ^ (N - Δ + (1/κ_min + ε) N))`, with `κ = κ(P)`.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 5, case `h = 2`
(`integers-2026-A80-thm-5`). -/
public theorem_wanted bFreeDivisorSum_shortInterval_two {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (κ : F[X] → ℕ) (hκ : ∀ P : F[X], P.Monic → Irreducible P → 2 ≤ κ P)
    (hsymm : ∀ P : F[X], P.Monic → Irreducible P → P.coeff 0 ≠ 0 →
      κ (normalize P.reverse) = κ P)
    {c : ℝ} (hc : (2 + 2 / (kappaMin κ : ℝ)) / 4 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ N in atTop, ∀ A : F[X], A.Monic → A.natDegree = N → ∀ Δ : ℕ,
      c * N ≤ Δ → Δ + 2 ≤ N →
        |(∑ᶠ f ∈ {f : F[X] | (f - A).degree ≤ Δ ∧ IsBFree κ f}, (monicDivisorCount 2 f : ℝ)) -
            (Fintype.card F : ℝ) ^ (Δ + 1) *
              (∏' P : {P : F[X] // P.Monic ∧ Irreducible P},
                (1 - (κ P + 1 : ℝ) / fqNorm (P : F[X]) ^ κ P +
                  (κ P : ℝ) / fqNorm (P : F[X]) ^ (κ P + 1))) *
              ((N : ℝ) + 1 + ∑' P : {P : F[X] // P.Monic ∧ Irreducible P},
                (κ P : ℝ) * (P : F[X]).natDegree * (κ P + 1) * (fqNorm (P : F[X]) - 1) /
                  (fqNorm (P : F[X]) ^ (κ P + 1) - fqNorm (P : F[X]) * (κ P + 1) + κ P))| ≤
          C * (Fintype.card F : ℝ) ^ ((N : ℝ) - Δ + (1 / (kappaMin κ : ℝ) + ε) * N)

end

end MetaMathlibExt
