/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.Data.Set.Density

namespace MetaMathlibExt

@[expose] public section

/-! A Laurent polynomial in `r` variables with coefficients in `R` is an element of
`AddMonoidAlgebra R (Fin r → ℤ)`; its coefficient of `x^j` is `f.coeff j` and its
constant term `ct[f]` is `f.coeff 0`. Kohen's array `a^n_k = coef_{-k}[P^n]` is
`(P ^ n).coeff (-k)`. The paper's index box `T = [-m, m]^r` is
`Fintype.piFinset fun _ => Finset.Icc (-m) m`. Definitions follow Kohen's arXiv
version (arXiv:2503.21988v1, Sections 1, 2 and 5), which matches the journal records. -/

/-- Kohen's operator `Λ_k`: keep the terms whose exponents are all multiples of `k` and
substitute `x_j^k ↦ x_j`, so `coef_j[Λ_k f] = coef_{k j}[f]`. For `k = 0` it is set to `0`
(the paper uses only positive `k`).

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 2 (definition of `Λ_k`). -/
public noncomputable def laurentCartier {R : Type*} [Semiring R] {r : ℕ} (k : ℕ)
    (f : AddMonoidAlgebra R (Fin r → ℤ)) : AddMonoidAlgebra R (Fin r → ℤ) :=
  if hk : k = 0 then 0 else
    .ofCoeff (Finsupp.comapDomain (fun j => k • j) f.coeff
      (fun _ _ _ _ h => smul_right_injective (Fin r → ℤ) hk h))

/-- The coefficient of `x^j` in `Λ_k f` is the coefficient of `x^{k j}` in `f`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 2 (definition of `Λ_k`). -/
public theorem coeff_laurentCartier {R : Type*} [Semiring R] {r k : ℕ} (hk : k ≠ 0)
    (f : AddMonoidAlgebra R (Fin r → ℤ)) (j : Fin r → ℤ) :
    (laurentCartier k f).coeff j = f.coeff (k • j) := by
  simp [laurentCartier, hk]

/-- Kohen's degree of a Laurent polynomial: the largest absolute value of any exponent of any
single variable occurring in it (`0` for the zero polynomial), e.g.
`deg(5x^{-3}y^{-2} + 2xy^{-1}) = 3`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 1.1. -/
public def laurentDeg {R : Type*} [Semiring R] {r : ℕ}
    (f : AddMonoidAlgebra R (Fin r → ℤ)) : ℕ :=
  f.coeff.support.sup fun j => Finset.univ.sup fun i => (j i).natAbs

/-- `deg f ≤ m` exactly when every exponent occurring in `f` lies in `[-m, m]^r`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Section 1.1. -/
public theorem laurentDeg_le_iff {R : Type*} [Semiring R] {r : ℕ}
    (f : AddMonoidAlgebra R (Fin r → ℤ)) (m : ℕ) :
    laurentDeg f ≤ m ↔ ∀ j ∈ f.coeff.support, ∀ i, (j i).natAbs ≤ m := by
  simp [laurentDeg, Finset.sup_le_iff]

/-- The factor of `s` of length `ℓ` starting at position `i` also occurs at position `i'`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public def SeqFactorOccursAt {α : Type*} (s : ℕ → α) (i ℓ i' : ℕ) : Prop :=
  ∀ t < ℓ, s (i' + t) = s (i + t)

/-- A sequence is recurrent if every occurrence of a factor is followed by a later occurrence.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
definition before Proposition 19. -/
public def IsRecurrentSeq {α : Type*} (s : ℕ → α) : Prop :=
  ∀ i ℓ : ℕ, ∃ j, 0 < j ∧ SeqFactorOccursAt s i ℓ (i + j)

/-- A sequence is uniformly recurrent if for every factor `w` there is a constant `C_w` such
that every occurrence of `w` is followed by another occurrence at distance at most `C_w`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public def IsUniformlyRecurrentSeq {α : Type*} (s : ℕ → α) : Prop :=
  ∀ i ℓ : ℕ, ∃ C, ∀ i', SeqFactorOccursAt s i ℓ i' →
    ∃ j, 0 < j ∧ j ≤ C ∧ SeqFactorOccursAt s i ℓ (i' + j)

/-- A sequence is linearly recurrent if the return constant `C_w` of every nonempty factor `w`
can be taken to be a fixed multiple of the length of `w`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public def IsLinearlyRecurrentSeq {α : Type*} (s : ℕ → α) : Prop :=
  ∃ K : ℕ, ∀ i ℓ : ℕ, 0 < ℓ → ∀ i', SeqFactorOccursAt s i ℓ i' →
    ∃ j, 0 < j ∧ j ≤ K * ℓ ∧ SeqFactorOccursAt s i ℓ (i' + j)

/-- Linear recurrence implies uniform recurrence.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public theorem IsLinearlyRecurrentSeq.isUniformlyRecurrentSeq {α : Type*} {s : ℕ → α}
    (h : IsLinearlyRecurrentSeq s) : IsUniformlyRecurrentSeq s := by
  obtain ⟨K, hK⟩ := h
  intro i ℓ
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · exact ⟨1, fun _ _ => ⟨1, one_pos, le_rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩⟩
  · exact ⟨K * ℓ, fun i' hi' => hK i ℓ hℓ i' hi'⟩

/-- Uniform recurrence implies recurrence.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public theorem IsUniformlyRecurrentSeq.isRecurrentSeq {α : Type*} {s : ℕ → α}
    (h : IsUniformlyRecurrentSeq s) : IsRecurrentSeq s := by
  intro i ℓ
  obtain ⟨C, hC⟩ := h i ℓ
  obtain ⟨j, hj, -, hocc⟩ := hC i fun _ _ => rfl
  exact ⟨j, hj, hocc⟩

/-- A constant sequence is linearly recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Definition 1. -/
public theorem isLinearlyRecurrentSeq_const {α : Type*} (c : α) :
    IsLinearlyRecurrentSeq fun _ : ℕ => c :=
  ⟨1, fun _ ℓ hℓ _ _ => ⟨1, one_pos, by omega, fun _ _ => rfl⟩⟩

/-! ### Section 2: the Rowland–Zeilberger congruence and the degree bound -/

/-- Rowland–Zeilberger congruence: `ct[P^{pn+k} Q] ≡ ct[P^n Λ_p(P^k Q)] (mod p)`.
Stated for natural `n` and `k` (the paper writes "integers"; negative powers of a general
Laurent polynomial are undefined).

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 3 (`jis-2026-26.4.2-lem-3`). -/
public theorem_wanted constantTerm_pow_mul_modEq_laurentCartier {r p : ℕ} (hp : p.Prime)
    (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (n k : ℕ) :
    (P ^ (p * n + k) * Q).coeff 0 ≡ (P ^ n * laurentCartier p (P ^ k * Q)).coeff 0 [ZMOD p]

/-- Degree bound for the Rowland–Zeilberger states: iterating `Q ↦ Λ_p(P^k Q)` with digits
`k < p` never raises the degree above `m = max(deg P - 1, deg Q)`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 4 (`jis-2026-26.4.2-lem-4`). -/
public theorem_wanted laurentDeg_foldl_laurentCartier_le {r p : ℕ} (hp : p.Prime)
    (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (ks : List ℕ) (hks : ∀ k ∈ ks, k < p) :
    laurentDeg (ks.foldl (fun R k => laurentCartier p (P ^ k * R)) Q) ≤
      max (laurentDeg P - 1) (laurentDeg Q)

/-! ### Section 3: the linear representation mod `p` -/

/-- Bookkeeping identity: for a digit `k < p` and `i ∈ T = [-m, m]^r` with
`m ≥ deg P - 1`, `Λ_p(P^k x^i) = ∑_{j ∈ T} a^k_{i - p j} x^j`, where
`a^k_{i-pj} = coef_{pj-i}[P^k]`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 6 (`jis-2026-26.4.2-prop-6`). -/
public theorem_wanted laurentCartier_pow_mul_single_eq_sum {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (m : ℕ) (hm : laurentDeg P ≤ m + 1) (k : ℕ)
    (hk : k < p) (i : Fin r → ℤ)
    (hi : i ∈ Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) :
    laurentCartier p (P ^ k * AddMonoidAlgebra.single i 1) =
      ∑ j ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        AddMonoidAlgebra.single j ((P ^ k).coeff (p • j - i))

/-- The linear representation step `γ(k) · V(n) = V(pn + k)` over `𝔽_p`, entrywise: with
`γ(k) = (a^k_{i-pj})_{i,j ∈ T}` and `V(n) = (a^n_i)_{i ∈ T}`, for `m ≥ deg P - 1`, a digit
`k < p` and `i ∈ T`, `a^{pn+k}_i ≡ ∑_{j ∈ T} a^k_{i-pj} a^n_j (mod p)`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 9 (`jis-2026-26.4.2-lem-9`). -/
public theorem_wanted coeff_pow_modEq_sum_gamma_mul_V {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (m : ℕ) (hm : laurentDeg P ≤ m + 1) (k : ℕ)
    (hk : k < p) (n : ℕ) (i : Fin r → ℤ)
    (hi : i ∈ Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) :
    (P ^ (p * n + k)).coeff (-i) ≡
      ∑ j ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        (P ^ k).coeff (p • j - i) * (P ^ n).coeff (-j) [ZMOD p]

/-- Eventually `γ(0)^{s'} = e_{C,C}` over `𝔽_p`, where `γ(0)_{i,j} = a^0_{i-pj} = [i = p j]`
on `T = [-m, m]^r` and `C` is the index of the constant monomial.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 11 (`jis-2026-26.4.2-lem-11`). -/
public theorem_wanted exists_gammaZero_pow_eq_single {p : ℕ} (hp : p.Prime) (r m : ℕ) :
    ∃ s : ℕ, ∀ s' ≥ s,
      (Matrix.of fun i j : ↥(Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) =>
        if (i : Fin r → ℤ) = p • (j : Fin r → ℤ) then (1 : ZMod p) else 0) ^ s' =
        Matrix.single ⟨0, by simp⟩ ⟨0, by simp⟩ 1

/-! ### Section 4: classification mod `p` -/

/-- Whether `p` divides some `ct[P^n]` can be decided on a prefix whose length depends only on
`p`, the number of variables and a bound on `deg P`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 12 (`jis-2026-26.4.2-prop-12`). -/
public theorem_wanted exists_bound_constantTerm_pow_dvd {p : ℕ} (hp : p.Prime) (r d : ℕ) :
    ∃ B : ℕ, ∀ P : AddMonoidAlgebra ℤ (Fin r → ℤ), laurentDeg P ≤ d →
      (∃ n, (p : ℤ) ∣ (P ^ n).coeff 0) → ∃ n₀ < B, (p : ℤ) ∣ (P ^ n₀).coeff 0

/-- If `p ∣ ct[P^n]` for some `n`, then for every `Q` the zeros of `ct[P^n Q] mod p` have
density `1`, there are arbitrarily long runs of zeros, and the sequence is either identically
`0` or not uniformly recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Theorem 14 (`jis-2026-26.4.2-thm-14`). -/
public theorem_wanted constantTerm_zero_density_mod_prime {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (hP : ∃ n, (p : ℤ) ∣ (P ^ n).coeff 0)
    (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) :
    ({n : ℕ | (p : ℤ) ∣ (P ^ n * Q).coeff 0} : Set ℕ).HasDensity 1 ∧
      (∀ L : ℕ, ∃ i, ∀ t < L, (p : ℤ) ∣ (P ^ (i + t) * Q).coeff 0) ∧
      ((∀ n, (p : ℤ) ∣ (P ^ n * Q).coeff 0) ∨
        ¬ IsUniformlyRecurrentSeq fun n => ((P ^ n * Q).coeff 0 : ZMod p))

/-- There is `t₀` such that for every `n` with `p ∤ ct[P^n]`, the block
`σ^{t₀}(V(n)) = V(p^{t₀} n) ⋯ V(p^{t₀} n + p^{t₀} - 1)` contains `V(0)`; stated with
`V(n) = (a^n_i mod p)_{i ∈ T}` on `T = [-m, m]^r` for any `m ≥ deg P - 1`, and
`V(0)` the indicator of the constant monomial.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 15 (`jis-2026-26.4.2-prop-15`). -/
public theorem_wanted exists_sigma_pow_V_contains_V_zero {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (m : ℕ) (hm : laurentDeg P ≤ m + 1) :
    ∃ t₀ : ℕ, ∀ n : ℕ, ¬ (p : ℤ) ∣ (P ^ n).coeff 0 → ∃ j < p ^ t₀,
      ∀ i ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        (P ^ (p ^ t₀ * n + j)).coeff (-i) ≡ if i = 0 then 1 else 0 [ZMOD p]

/-- Main theorem mod `p`: if `ct[P^n Q] mod p` is not identically `0`, it is linearly
recurrent if and only if `p ∤ ct[P^n]` for all `n`; otherwise its zeros have density `1`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Theorem 16 (`jis-2026-26.4.2-thm-16`). -/
public theorem_wanted isLinearlyRecurrentSeq_constantTerm_mod_prime_iff {r p : ℕ}
    (hp : p.Prime) (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hQ : ∃ n, ¬ (p : ℤ) ∣ (P ^ n * Q).coeff 0) :
    (IsLinearlyRecurrentSeq (fun n => ((P ^ n * Q).coeff 0 : ZMod p)) ↔
        ∀ n, ¬ (p : ℤ) ∣ (P ^ n).coeff 0) ∧
      (¬ IsLinearlyRecurrentSeq (fun n => ((P ^ n * Q).coeff 0 : ZMod p)) →
        ({n : ℕ | (p : ℤ) ∣ (P ^ n * Q).coeff 0} : Set ℕ).HasDensity 1)

/-- Combinations mod `p`: for `b_n = F(ct[P^{n+k_1} Q_1] mod p, …, ct[P^{n+k_ℓ} Q_ℓ] mod p)`
not constantly `F(0, …, 0)`, `b` is linearly recurrent if and only if `p ∤ ct[P^n]` for all `n`,
and if `p ∣ ct[P^n]` for some `n` then `F(0, …, 0)` has frequency `1` in `b`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Corollary 17 (`jis-2026-26.4.2-cor-17`). -/
public theorem_wanted isLinearlyRecurrentSeq_combination_mod_prime_iff {r p ℓ : ℕ}
    {X : Type*} (hp : p.Prime) (P : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (F : (Fin ℓ → ZMod p) → X) (k : Fin ℓ → ℕ) (Q : Fin ℓ → AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hb : ∃ n, F (fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod p)) ≠ F 0) :
    (IsLinearlyRecurrentSeq (fun n => F fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod p)) ↔
        ∀ n, ¬ (p : ℤ) ∣ (P ^ n).coeff 0) ∧
      ((∃ n, (p : ℤ) ∣ (P ^ n).coeff 0) →
        ({n : ℕ | F (fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod p)) = F 0} :
          Set ℕ).HasDensity 1)

/-- If `p ∤ ct[P^{n₀}]` for some `n₀ > 0`, then `ct[P^n Q] mod p` is recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 19 (`jis-2026-26.4.2-prop-19`). -/
public theorem_wanted isRecurrentSeq_constantTerm_mod_prime {r p : ℕ} (hp : p.Prime)
    (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hP : ∃ n₀, 0 < n₀ ∧ ¬ (p : ℤ) ∣ (P ^ n₀).coeff 0) :
    IsRecurrentSeq fun n => ((P ^ n * Q).coeff 0 : ZMod p)

/-! ### Section 5: prime powers

`P̃` is any integer Laurent polynomial with `P^{p^{a-1}}(x) ≡ P̃(x^{p^ℓ}) (mod p^a)`
coefficientwise; the substitution `x ↦ x^q` is `AddMonoidAlgebra.mapDomain (q • ·)`. The paper
takes `ℓ` as large as possible; the statements below hold for every such pair `(ℓ, P̃)`. -/

/-- `p` divides some `ct[P^n]` if and only if it divides some `ct[P̃^n]`, and the same index
works in the forward direction.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 22 (`jis-2026-26.4.2-lem-22`). -/
public theorem_wanted exists_constantTerm_pow_dvd_iff_tilde {r p a ℓ : ℕ} (hp : p.Prime)
    (ha : 0 < a) (P Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (P ^ (p ^ (a - 1))).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p ^ ℓ • j) Pt).coeff j [ZMOD (p : ℤ) ^ a]) :
    ((∃ n₀, (p : ℤ) ∣ (P ^ n₀).coeff 0) ↔ ∃ n₁, (p : ℤ) ∣ (Pt ^ n₁).coeff 0) ∧
      ∀ n₀, (p : ℤ) ∣ (P ^ n₀).coeff 0 → (p : ℤ) ∣ (Pt ^ n₀).coeff 0

/-- Conversion to `P̃`: `ct[P^{p^{a-1} n + k} Q] ≡ ct[P̃^n Λ_{p^ℓ}(P^k Q)] (mod p^a)`, for all
natural `k` (the paper restricts to `k < p^{a-1}`).

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 23 (`jis-2026-26.4.2-prop-23`). -/
public theorem_wanted constantTerm_pow_mul_modEq_tilde {r p a ℓ : ℕ} (hp : p.Prime)
    (ha : 0 < a) (P Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (P ^ (p ^ (a - 1))).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p ^ ℓ • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (n k : ℕ) :
    (P ^ (p ^ (a - 1) * n + k) * Q).coeff 0 ≡
      (Pt ^ n * laurentCartier (p ^ ℓ) (P ^ k * Q)).coeff 0 [ZMOD (p : ℤ) ^ a]

/-- Rowland–Zeilberger congruence mod `p^a` for `P̃` with `P̃(x)^p ≡ P̃(x^p) (mod p^a)`:
`ct[P̃^{pn+k} Q] ≡ ct[P̃^n Λ_p(P̃^k Q)] (mod p^a)`, for all natural `k` (the paper states
`k ∈ 𝔽_p`).

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 24 (`jis-2026-26.4.2-lem-24`). -/
public theorem_wanted constantTerm_tilde_pow_mul_modEq_laurentCartier {r p a : ℕ}
    (hp : p.Prime) (Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (Pt ^ p).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (n k : ℕ) :
    (Pt ^ (p * n + k) * Q).coeff 0 ≡ (Pt ^ n * laurentCartier p (Pt ^ k * Q)).coeff 0
      [ZMOD (p : ℤ) ^ a]

/-- Degree bound mod `p^a`: for Laurent polynomials `P̃` and `Q₀` over `ℤ/p^aℤ`, iterating
`Q ↦ Λ_p(P̃^k Q)` with digits `k < p` never raises the degree above
`max(deg P̃ - 1, deg Q₀)`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 25 (`jis-2026-26.4.2-lem-25`). -/
public theorem_wanted laurentDeg_foldl_laurentCartier_le_zmod {r p a : ℕ} (hp : p.Prime)
    (Pt Q₀ : AddMonoidAlgebra (ZMod (p ^ a)) (Fin r → ℤ)) (ks : List ℕ)
    (hks : ∀ k ∈ ks, k < p) :
    laurentDeg (ks.foldl (fun R k => laurentCartier p (Pt ^ k * R)) Q₀) ≤
      max (laurentDeg Pt - 1) (laurentDeg Q₀)

/-- The step `γ̃(k) · Ṽ(n) = Ṽ(pn + k)` over `ℤ/p^aℤ`, entrywise, for `P̃` with
`P̃(x)^p ≡ P̃(x^p) (mod p^a)`, `m ≥ deg P̃ - 1`, a digit `k < p` and `i ∈ [-m, m]^r`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 28 (`jis-2026-26.4.2-lem-28`). -/
public theorem_wanted coeff_tilde_pow_modEq_sum_gamma_mul_V {r p a : ℕ} (hp : p.Prime)
    (Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (Pt ^ p).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (m : ℕ) (hm : laurentDeg Pt ≤ m + 1) (k : ℕ) (hk : k < p) (n : ℕ) (i : Fin r → ℤ)
    (hi : i ∈ Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) :
    (Pt ^ (p * n + k)).coeff (-i) ≡
      ∑ j ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        (Pt ^ k).coeff (p • j - i) * (Pt ^ n).coeff (-j) [ZMOD (p : ℤ) ^ a]

/-- Eventually `γ̃(0)^{s'} = e_{C,C}` over `ℤ/p^aℤ` (the printed `γ̃(0)^s` is read as
`γ̃(0)^{s'}`, as in Lemma 11).

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 30 (`jis-2026-26.4.2-lem-30`). -/
public theorem_wanted exists_gammaZero_pow_eq_single_zmod {p : ℕ} (hp : p.Prime)
    (a : ℕ) (ha : 0 < a) (r m : ℕ) :
    ∃ s : ℕ, ∀ s' ≥ s,
      (Matrix.of fun i j : ↥(Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) =>
        if (i : Fin r → ℤ) = p • (j : Fin r → ℤ) then (1 : ZMod (p ^ a)) else 0) ^ s' =
        Matrix.single ⟨0, by simp⟩ ⟨0, by simp⟩ 1

/-- If `P̃(x)^p ≡ P̃(x^p) (mod p^a)` and `p ∣ ct[P̃^{n₀}]` for some `n₀`, then for every `Q`
the zeros of `ct[P̃^n Q] mod p^a` have density `1`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 31 (`jis-2026-26.4.2-lem-31`). -/
public theorem_wanted constantTerm_tilde_zero_density {r p a : ℕ} (hp : p.Prime)
    (Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (Pt ^ p).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (h : ∃ n₀, (p : ℤ) ∣ (Pt ^ n₀).coeff 0) (Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) :
    ({n : ℕ | (p : ℤ) ^ a ∣ (Pt ^ n * Q).coeff 0} : Set ℕ).HasDensity 1

/-- Analogue of Proposition 15 mod `p^a`: for `P̃` with `P̃(x)^p ≡ P̃(x^p) (mod p^a)` and any
`m ≥ deg P̃ - 1` there is `t₀` such that for every `n` with `p ∤ ct[P̃^n]` some
`Ṽ(p^{t₀} n + j)`, `j < p^{t₀}`, equals `Ṽ(0)` mod `p^a`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 32 (`jis-2026-26.4.2-prop-32`). -/
public theorem_wanted exists_sigma_pow_V_contains_V_zero_tilde {r p a : ℕ} (hp : p.Prime)
    (Pt : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hPt : ∀ j, (Pt ^ p).coeff j ≡
      (AddMonoidAlgebra.mapDomain (fun j => p • j) Pt).coeff j [ZMOD (p : ℤ) ^ a])
    (m : ℕ) (hm : laurentDeg Pt ≤ m + 1) :
    ∃ t₀ : ℕ, ∀ n : ℕ, ¬ (p : ℤ) ∣ (Pt ^ n).coeff 0 → ∃ j < p ^ t₀,
      ∀ i ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        (Pt ^ (p ^ t₀ * n + j)).coeff (-i) ≡ if i = 0 then 1 else 0 [ZMOD (p : ℤ) ^ a]

/-- Main theorem mod `p^a`: if `ct[P^n Q] mod p^a` is not identically `0`, it is linearly
recurrent if and only if `p ∤ ct[P^n]` for all `n` (independently of `Q` and `a`); otherwise
its zeros have density `1`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Theorem 33 (`jis-2026-26.4.2-thm-33`). -/
public theorem_wanted isLinearlyRecurrentSeq_constantTerm_mod_primePow_iff {r p a : ℕ}
    (hp : p.Prime) (ha : 0 < a) (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hQ : ∃ n, ¬ (p : ℤ) ^ a ∣ (P ^ n * Q).coeff 0) :
    (IsLinearlyRecurrentSeq (fun n => ((P ^ n * Q).coeff 0 : ZMod (p ^ a))) ↔
        ∀ n, ¬ (p : ℤ) ∣ (P ^ n).coeff 0) ∧
      (¬ IsLinearlyRecurrentSeq (fun n => ((P ^ n * Q).coeff 0 : ZMod (p ^ a))) →
        ({n : ℕ | (p : ℤ) ^ a ∣ (P ^ n * Q).coeff 0} : Set ℕ).HasDensity 1)

/-- Combinations mod `p^a`: for
`b_n = F(ct[P^{n+k_1} Q_1] mod p^a, …, ct[P^{n+k_ℓ} Q_ℓ] mod p^a)` not constantly
`F(0, …, 0)`, `b` is linearly recurrent if and only if `p ∤ ct[P^n]` for all `n`, and if
`p ∣ ct[P^n]` for some `n` then `F(0, …, 0)` has frequency `1` in `b`.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Corollary 34 (`jis-2026-26.4.2-cor-34`). -/
public theorem_wanted isLinearlyRecurrentSeq_combination_mod_primePow_iff {r p a ℓ : ℕ}
    {X : Type*} (hp : p.Prime) (ha : 0 < a) (P : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (F : (Fin ℓ → ZMod (p ^ a)) → X) (k : Fin ℓ → ℕ)
    (Q : Fin ℓ → AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hb : ∃ n, F (fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod (p ^ a))) ≠ F 0) :
    (IsLinearlyRecurrentSeq
        (fun n => F fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod (p ^ a))) ↔
        ∀ n, ¬ (p : ℤ) ∣ (P ^ n).coeff 0) ∧
      ((∃ n, (p : ℤ) ∣ (P ^ n).coeff 0) →
        ({n : ℕ | F (fun i => ((P ^ (n + k i) * Q i).coeff 0 : ZMod (p ^ a))) = F 0} :
          Set ℕ).HasDensity 1)

/-- If `ct[P^{n₀}] mod p ≠ 0` for some `n₀ > 0`, then `ct[P^n Q] mod p^a` is recurrent.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Proposition 35 (`jis-2026-26.4.2-prop-35`). -/
public theorem_wanted isRecurrentSeq_constantTerm_mod_primePow {r p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ))
    (hP : ∃ n₀, 0 < n₀ ∧ ¬ (p : ℤ) ∣ (P ^ n₀).coeff 0) :
    IsRecurrentSeq fun n => ((P ^ n * Q).coeff 0 : ZMod (p ^ a))

end

end MetaMathlibExt
