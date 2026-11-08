/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.Data.Nat.Nth

/-!
# Bertrand postulates and Schatunowsky-type theorems in ℕ and Gaussian and Eisenstein integers

Statement-only targets from Hirofumi Nakai, Ken Sasaki and Konoka Yoshida,
*Schatunowsky-type Theorems for Imaginary Quadratic Integer Rings of Class Number One*,
INTEGERS 26 (2026), Article A110. The Eisenstein integers are the ring of integers of
`CyclotomicField 3 ℚ`, with the field norm `Algebra.norm ℚ`.

For the paper's Sections 3-5 an imaginary quadratic field is a number field `K` with
`Module.finrank ℚ K = 2` and `IsTotallyComplex K`; "`m` is one of the integers of Proposition 1"
is `NumberField.classNumber K = 1`, and the Gaussian (`m = -1`) and Eisenstein (`m = -3`) cases
are the fields with `NumberField.discr K = -4` and `-3`. The norm `N(α)` is
`Ideal.absNorm (Ideal.span {α})`, `Ω(β)` is the number of prime ideal factors of `(β)` with
multiplicity, and `gcd(α, β) = 1` is `IsCoprime α β`. The paper's norm-ordered primes `π_n`
(Definition 1: one prime from each conjugate pair) and primorials `π_n#` (Definition 2) enter
only through `N(π_n)` and `N(π_n#)` and through divisibility by `π_n#`; since the prime ideals
of norm at most `N(π_n)` are exactly those lying over the first `n` rational primes in this
order, `(π_n#)` is their product, `N(π_n#)` is the product of their norms, and `π_n# ∣ α`
says that `α` lies in each of them.
-/

open NumberField

namespace MetaMathlibExt

@[expose] public section

/-- Bertrand's postulate for Gaussian integers: for every Gaussian prime `π` other than the
associates of `1 + i` (equivalently `N(π) ≠ 2`; the paper's `π_n` with `n ≥ 2`), there is a
Gaussian prime `ρ` with `N(π) < N(ρ) ≤ 2 N(π)`.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Lemma 2
(`integers-2026-A110-lem-2`). -/
public theorem_wanted gaussianInt_exists_prime_norm_between {π : GaussianInt} (hπ : Prime π)
    (hπ₂ : π.norm ≠ 2) :
    ∃ ρ : GaussianInt, Prime ρ ∧ π.norm < ρ.norm ∧ ρ.norm ≤ 2 * π.norm

/-- Bertrand's postulate for Eisenstein integers: for every Eisenstein prime `π` (the paper's
`π_n`, `n ≥ 1`), there is an Eisenstein prime `ρ` with `N(π) < N(ρ) ≤ 2 N(π)`. The Eisenstein
integers are `𝓞 (CyclotomicField 3 ℚ)` and `N` is the field norm to `ℚ`.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Lemma 3
(`integers-2026-A110-lem-3`). -/
public theorem_wanted eisenstein_exists_prime_norm_between
    {π : 𝓞 (CyclotomicField 3 ℚ)} (hπ : Prime π) :
    ∃ ρ : 𝓞 (CyclotomicField 3 ℚ), Prime ρ ∧
      Algebra.norm ℚ (π : CyclotomicField 3 ℚ) < Algebra.norm ℚ (ρ : CyclotomicField 3 ℚ) ∧
      Algebra.norm ℚ (ρ : CyclotomicField 3 ℚ) ≤ 2 * Algebra.norm ℚ (π : CyclotomicField 3 ℚ)

/-- Schatunowsky's theorem: the integers `a ≥ 2` such that every `b` with `1 < b < a` and
`gcd(a, b) = 1` is prime are exactly `2, 3, 4, 6, 8, 12, 18, 24, 30`. Here
`T(a) = {b | 1 < b < a, gcd(a, b) = 1}`, the rational counterpart of the paper's
`T_G(α) = {β | 1 < N(β) < N(α), gcd(α, β) = 1}`; `a = 0, 1` (empty `T(a)`) are excluded, as
in the printed set.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 1,
quoting Schatunowsky (`integers-2026-A110-thm-1`). -/
public theorem_wanted nat_schatunowsky :
    {a : ℕ | 2 ≤ a ∧ ∀ b : ℕ, 1 < b → b < a → Nat.Coprime a b → b.Prime} =
      {2, 3, 4, 6, 8, 12, 18, 24, 30}

/-- Iwata's generalization of Schatunowsky's theorem: for each `ℓ`, only finitely many `a`
have `Ω(b) ≤ ℓ` for every `b` with `1 < b < a` and `gcd(a, b) = 1`; `Ω` is
`ArithmeticFunction.cardFactors`, the number of prime factors with multiplicity.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 2,
quoting Iwata (`integers-2026-A110-thm-2`). `ℓ = 0` is included (trivially finite). -/
public theorem_wanted nat_iwata_finite (ℓ : ℕ) :
    {a : ℕ | ∀ b : ℕ, 1 < b → b < a → Nat.Coprime a b →
      ArithmeticFunction.cardFactors b ≤ ℓ}.Finite

/-- Dalezman's Gaussian Schatunowsky theorem: let `S_G` be the set of Gaussian integers `α` such
that every `β` with `1 < N(β) < N(α)` and `gcd(α, β) = 1` is a Gaussian prime. Then `5 + 5i`
lies in `S_G`, every element of `S_G` has norm at most `N(5 + 5i) = 50`, and every element of
`S_G` of norm `50` is a unit multiple of `5 + 5i`.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 3,
quoting Dalezman (`integers-2026-A110-thm-3`). -/
public theorem_wanted gaussianInt_schatunowsky_max_norm_five_add_five_i :
    let S : Set GaussianInt :=
      {α | ∀ β : GaussianInt, 1 < β.norm → β.norm < α.norm → IsCoprime α β → Prime β}
    (⟨5, 5⟩ : GaussianInt) ∈ S ∧ (∀ α ∈ S, α.norm ≤ 50) ∧
      ∀ α ∈ S, α.norm = 50 → Associated α ⟨5, 5⟩


/-- `N(π_n)`, the norm of the `n`-th prime of the paper's ordered set `P_m^+` (Definition 1), with
`N(π_0) = 1` for the paper's convention `π_0 = 1`: the `n`-th smallest norm of a nonzero prime
ideal of `𝓞 K` (distinct primes of `P_m^+` have distinct norms `p` or `p^2`).

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Definition 1 and Section 4 (`N(π_n)`). -/
public noncomputable def quadPrimeNorm (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  if n = 0 then 1
  else Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) (n - 1)

/-- `N(π_0) = 1`.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Definition 1 (convention `π_0 = 1`). -/
public theorem quadPrimeNorm_zero (K : Type*) [Field K] [NumberField K] :
    quadPrimeNorm K 0 = 1 := by
  simp [quadPrimeNorm]

/-- `N(π_n#)`, the norm of the paper's quadratic primorial (Definition 2): the product of the norms
of the nonzero prime ideals of norm at most `N(π_n)`.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Definition 2 (`π_n#`). -/
public noncomputable def quadPrimorialNorm (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  ∏ᶠ P ∈ {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ quadPrimeNorm K n},
    Ideal.absNorm P

/-- `N(π_0#) = 1`: no nonzero prime ideal has norm at most `1`.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Definition 2 (`π_0# = 1`). -/
public theorem quadPrimorialNorm_zero (K : Type*) [Field K] [NumberField K] :
    quadPrimorialNorm K 0 = 1 := by
  have hempty : {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ 1} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun P ⟨hP, hbot, hle⟩ => ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · exact hbot (Ideal.absNorm_eq_zero_iff.mp h)
    · exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  rw [quadPrimorialNorm, quadPrimeNorm_zero, hempty, finprod_mem_empty]

/-- The paper's set `Q_{m,ℓ}` (Equation (4)), as a set of elements of `𝓞 K` (it is closed under
multiplication by units): `α` with `N(α) > 1` such that every `β` with `1 < N(β) < N(α)` and
`gcd(α, β) = 1` has `Ω(β) ≤ ℓ`.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Section 5, Equation (4). -/
public def quadSchatunowskySet (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) : Set (𝓞 K) :=
  {α | 1 < Ideal.absNorm (Ideal.span {α}) ∧ ∀ β : 𝓞 K,
      1 < Ideal.absNorm (Ideal.span {β}) →
      Ideal.absNorm (Ideal.span {β}) < Ideal.absNorm (Ideal.span {α}) →
    IsCoprime α β → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {β})).card ≤ ℓ}

/-- `1 ∉ Q_{m,ℓ}` (its norm is `1`).

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Section 5, Equation (4). -/
public theorem one_not_mem_quadSchatunowskySet (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) :
    (1 : 𝓞 K) ∉ quadSchatunowskySet K ℓ := by
  simp [quadSchatunowskySet]

/-- Proposition 2 (units): the unit group of the ring of integers of an imaginary quadratic field
is cyclic of order `4` for `ℚ(√-1)` (discriminant `-4`), `6` for `ℚ(√-3)` (discriminant `-3`),
and `2` otherwise. The representative convention `-θ_m < arg α ≤ θ_m` in the record is setup text
and is not stated.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Proposition 2 (`integers-2026-A110-prop-2`). -/
public theorem_wanted imagQuadratic_units_isCyclic_card {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    IsCyclic (𝓞 K)ˣ ∧
      Nat.card (𝓞 K)ˣ = if discr K = -4 then 4 else if discr K = -3 then 6 else 2

/-- Lemma 1: `N(ρ_{n+1}) / N(ρ_n) → 1` and `N(π_{n+1}) / N(π_n) → 1`, where `N(ρ_n)` is the
`n`-th smallest norm of a nonzero prime ideal counted with multiplicity (the paper's `ρ_n` runs
over all primes up to units, Definition 1). Indices are shifted by one (`n ≥ 1`). Stated for every
imaginary quadratic field: the norms do not need the paper's class-number-one assumption.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Lemma 1 (`integers-2026-A110-lem-1`). -/
public theorem_wanted tendsto_quadPrimeNorm_succ_div {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    Filter.Tendsto (fun n : ℕ =>
        ((sInf {x : ℕ | n + 2 ≤
            Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ x}} : ℕ) : ℝ) /
          ((sInf {x : ℕ | n + 1 ≤
            Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ x}} : ℕ) : ℝ))
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto (fun n : ℕ => (quadPrimeNorm K (n + 2) : ℝ) / quadPrimeNorm K (n + 1))
        Filter.atTop (nhds 1)

/-- Proposition 4: for every `ℓ ≥ 0` there is `n(ℓ)` with `N(π_{n+1})^{ℓ+1} < N(π_n#)` for all
`n ≥ n(ℓ)`. Stated for every imaginary quadratic field (no class-number-one assumption is needed
at the level of norms).

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Proposition 4 (`integers-2026-A110-prop-4`). -/
public theorem_wanted exists_quadPrimeNorm_pow_lt_quadPrimorialNorm {K : Type*} [Field K]
    [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (ℓ : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n

/-- Lemma 4: for `α ∈ Q_{m,ℓ}` with `N(π_n)^{ℓ+1} < N(α)`, `π_n# ∣ α`, i.e. `α` lies in every
nonzero prime ideal of norm at most `N(π_n)`.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Lemma 4 (`integers-2026-A110-lem-4`). -/
public theorem_wanted mem_prime_of_mem_quadSchatunowskySet {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n : ℕ)
    (α : 𝓞 K) (hα : α ∈ quadSchatunowskySet K ℓ)
    (hn : quadPrimeNorm K n ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α})) :
    ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → Ideal.absNorm P ≤ quadPrimeNorm K n → α ∈ P

/-- Theorem 4: if `n₀` has the property of Proposition 4 (`N(π_{n+1})^{ℓ+1} < N(π_n#)` for all
`n ≥ n₀`), then no `α` with `N(π_{n₀})^{ℓ+1} < N(α)` lies in `Q_{m,ℓ}`; and `Q_{m,ℓ}` is finite.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 4 (`integers-2026-A110-thm-4`). -/
public theorem_wanted quadSchatunowskySet_norm_bound_and_finite {K : Type*} [Field K]
    [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n₀ : ℕ)
    (hn₀ : ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n) :
    (∀ α : 𝓞 K, quadPrimeNorm K n₀ ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}) →
        α ∉ quadSchatunowskySet K ℓ) ∧
      (quadSchatunowskySet K ℓ).Finite

/-- Theorem 5 (main identity): if `n₀` has the property of Proposition 4, then
`Q_{m,ℓ} = ⋃_{n=1}^{n₀} Q_{m,ℓ,n}` with
`Q_{m,ℓ,n} = {α | N(π_{n-1})^{ℓ+1} < N(α) ≤ N(π_n)^{ℓ+1}, π_{n-1}# ∣ α}`. The record's
"in particular" clause (the element of largest norm is divisible by `π_{n₀-1}#`) holds only for
the least admissible `n₀`: for the Gaussian integers with `ℓ = 1`, `n₀ = 4` is admissible (as is
`3`), but the element of largest norm, `5(1+i) = π_2#`, is not divisible by `π_3# = 15(1+i)`; it is
omitted.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 5 (`integers-2026-A110-thm-5`). -/
public theorem_wanted quadSchatunowskySet_eq_iUnion {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n₀ : ℕ)
    (hn₀ : ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n) :
    quadSchatunowskySet K ℓ = ⋃ n ∈ Finset.Icc 1 n₀,
      {α : 𝓞 K | quadPrimeNorm K (n - 1) ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}) ∧
        Ideal.absNorm (Ideal.span {α}) ≤ quadPrimeNorm K n ^ (ℓ + 1) ∧
        ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → Ideal.absNorm P ≤ quadPrimeNorm K (n - 1) → α ∈ P}

/-- Proposition 5: for the Gaussian integers (`discr K = -4`, i.e. `K ≅ ℚ(i)`) and
`(ℓ, n(ℓ)) = (1, 3), (2, 4), (3, 5), (4, 5), (5, 6), (6, 7), (7, 7)`,
`N(π_{n+1})^{ℓ+1} < N(π_n#)` for all `n ≥ n(ℓ)`. The record's trailing "…" (larger `ℓ`) is
not stated.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Proposition 5 (`integers-2026-A110-prop-5`). -/
public theorem_wanted gaussian_quadPrimeNorm_pow_lt_quadPrimorialNorm {K : Type*} [Field K]
    [NumberField K]
    (hK : discr K = -4) :
    ∀ p ∈ [(1, 3), (2, 4), (3, 5), (4, 5), (5, 6), (6, 7), (7, 7)], ∀ n ≥ p.2,
      quadPrimeNorm K (n + 1) ^ (p.1 + 1) < quadPrimorialNorm K n

/-- Proposition 6: for the Eisenstein integers (`discr K = -3`, i.e. `K ≅ ℚ(√-3)`) and
`(ℓ, n(ℓ)) = (1, 3), (2, 4), (3, 5), (4, 5), (5, 6), (6, 7), (7, 8)`,
`N(π_{n+1})^{ℓ+1} < N(π_n#)` for all `n ≥ n(ℓ)`. The record's trailing "…" is not stated.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Proposition 6 (`integers-2026-A110-prop-6`). -/
public theorem_wanted eisenstein_quadPrimeNorm_pow_lt_quadPrimorialNorm {K : Type*} [Field K]
    [NumberField K]
    (hK : discr K = -3) :
    ∀ p ∈ [(1, 3), (2, 4), (3, 5), (4, 5), (5, 6), (6, 7), (7, 8)], ∀ n ≥ p.2,
      quadPrimeNorm K (n + 1) ^ (p.1 + 1) < quadPrimorialNorm K n

/-- Corollary 1: for the Gaussian integers (`discr K = -4`), with `π_1 = 1 + i` the prime of norm
`2` (any element `π` of norm `2`; all are associates), `π_2# = 5π`, `π_3# = 15π`, `π_4# = 195π`:
`Q_{-1,1} = {α | 1 < N(α) ≤ 4} ∪ {γπ_1 | 3 ≤ N(γ) ≤ 12} ∪ {π_2#}`,
`Q_{-1,2} = {α | 1 < N(α) ≤ 8} ∪ {γπ_1 | 5 ≤ N(γ) ≤ 62} ∪ {γ(π_2#) | 3 ≤ N(γ) ≤ 14} ∪
{γ(π_3#) | 2 ≤ N(γ) ≤ 4}`,
`Q_{-1,3} = {α | 1 < N(α) ≤ 16} ∪ {γπ_1 | 9 ≤ N(γ) ≤ 312} ∪ {γ(π_2#) | 13 ≤ N(γ) ≤ 131} ∪
{γ(π_3#) | 15 ≤ N(γ) ≤ 63} ∪ {π_4#}` (as sets of elements, so `{π_k#}` is its associates), and
the elements of largest norm are `π_2# = 5(1+i)`, `2(π_3#) = 30(1+i)` and `π_4# = 195(1+i)`,
unique up to units. The record's closing remark on Dalezman is omitted.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Corollary 1 (`integers-2026-A110-cor-1`). -/
public theorem_wanted gaussian_quadSchatunowskySet_eq {K : Type*} [Field K] [NumberField K]
    (hK : discr K = -4) :
    quadSchatunowskySet K 1 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 4) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 3 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 12 ∧ α = γ * π) ∨
          (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ Associated α (5 * π))} ∧
      quadSchatunowskySet K 2 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 8) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 5 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 62 ∧ α = γ * π) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 3 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 14 ∧ α = γ * (5 * π)) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 2 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 4 ∧ α = γ * (15 * π))} ∧
      quadSchatunowskySet K 3 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 16) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 9 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 312 ∧ α = γ * π) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 13 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 131 ∧ α = γ * (5 * π)) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ 15 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 63 ∧ α = γ * (15 * π)) ∨
          (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ Associated α (195 * π))} ∧
      (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ (5 * π) ∈ quadSchatunowskySet K 1 ∧
          ∀ α ∈ quadSchatunowskySet K 1,
              Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(5 * π)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(5 * π)}) →
                Associated α (5 * π))) ∧
      (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ (30 * π) ∈ quadSchatunowskySet K 2 ∧
          ∀ α ∈ quadSchatunowskySet K 2,
              Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(30 * π)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(30 * π)}) →
                Associated α (30 * π))) ∧
      (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 2 ∧ (195 * π) ∈ quadSchatunowskySet K 3 ∧
          ∀ α ∈ quadSchatunowskySet K 3,
              Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(195 * π)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(195 * π)}) →
                Associated α (195 * π)))

/-- Corollary 2: for the Eisenstein integers (`discr K = -3`), with `π_1 = 1 + ζ` the prime of
norm `3` (any element `π` of norm `3`), `π_2# = 2π`, `π_3# = 14π`, `π_4# = 182π`:
`Q_{-3,1} = {α | 1 < N(α) ≤ 9} ∪ {γπ_1 | 4 ≤ N(γ) ≤ 5} ∪ {γ(π_2#) | 2 ≤ N(γ) ≤ 4}`,
`Q_{-3,2} = {α | 1 < N(α) ≤ 27} ∪ {γπ_1 | 10 ≤ N(γ) ≤ 21} ∪ {γ(π_2#) | 6 ≤ N(γ) ≤ 28} ∪
{γ(π_3#) | 1 ≤ N(γ) ≤ 3}`,
`Q_{-3,3} = {α | 1 < N(α) ≤ 81} ∪ {γπ_1 | 28 ≤ N(γ) ≤ 85} ∪ {γ(π_2#) | 22 ≤ N(γ) ≤ 200} ∪
{γ(π_3#) | 5 ≤ N(γ) ≤ 48} ∪ {π_4#}`, and the elements of largest norm are `2(π_2#) = 4(1+ζ)`,
`(2-ζ)(π_3#) = 42` and `π_4# = 182(1+ζ)`, unique up to units. The record prints the second as
`(2-ζ)(π_4#) = 42`; `(2-ζ)(π_4#)` has norm `298116`, while `(2-ζ)(π_3#) = 42` (norm `1764`), the
element of largest norm in the `γ(π_3#)` part.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Corollary 2 (`integers-2026-A110-cor-2`). -/
public theorem_wanted eisenstein_quadSchatunowskySet_eq {K : Type*} [Field K] [NumberField K]
    (hK : discr K = -3) :
    quadSchatunowskySet K 1 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 9) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 4 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 5 ∧ α = γ * π) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 2 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 4 ∧ α = γ * (2 * π))} ∧
      quadSchatunowskySet K 2 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 27) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 10 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 21 ∧ α = γ * π) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 6 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 28 ∧ α = γ * (2 * π)) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 1 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 3 ∧ α = γ * (14 * π))} ∧
      quadSchatunowskySet K 3 =
        {α | (1 < Ideal.absNorm (Ideal.span {α}) ∧ Ideal.absNorm (Ideal.span {α}) ≤ 81) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 28 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 85 ∧ α = γ * π) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 22 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 200 ∧ α = γ * (2 * π)) ∨
          (∃ γ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ 5 ≤ Ideal.absNorm (Ideal.span {γ}) ∧
              Ideal.absNorm (Ideal.span {γ}) ≤ 48 ∧ α = γ * (14 * π)) ∨
          (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ Associated α (182 * π))} ∧
      (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ (4 * π) ∈ quadSchatunowskySet K 1 ∧
          ∀ α ∈ quadSchatunowskySet K 1,
              Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(4 * π)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(4 * π)}) →
                Associated α (4 * π))) ∧
      ((42 : 𝓞 K) ∈ quadSchatunowskySet K 2 ∧ ∀ α ∈ quadSchatunowskySet K 2,
          Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(42 : 𝓞 K)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(42 : 𝓞 K)}) →
                Associated α 42)) ∧
      (∃ π : 𝓞 K, Ideal.absNorm (Ideal.span {π}) = 3 ∧ (182 * π) ∈ quadSchatunowskySet K 3 ∧
          ∀ α ∈ quadSchatunowskySet K 3,
              Ideal.absNorm (Ideal.span {α}) ≤ Ideal.absNorm (Ideal.span {(182 * π)}) ∧
            (Ideal.absNorm (Ideal.span {α}) = Ideal.absNorm (Ideal.span {(182 * π)}) →
                Associated α (182 * π)))

end

end MetaMathlibExt
