/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Fintype.Pi
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.NumberTheory.MultipleZeta.CyclicSumFormula

/-!
# q-analogues of multiple zeta values: Schlesinger–Zudilin and OOZ models

Statements from Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24
(2024), Article A6 (arXiv:2111.00051), about Schlesinger–Zudilin (SZ) qMZVs,
their generating series and duality, the partition function, and the
Ohno–Okuda–Zudilin (OOZ) model, the general qMZVs of Bachmann–Kühn with the
spaces `𝒵_q` and `𝒵_{q,1}` they span, the Bradley–Zhao (BZ) model, and the
description of `𝒵_q` by polynomial functions on partitions in Stanley coordinates,
and the quasi-shuffle and shuffle products the evaluation maps respect.

All q-series are formal power series in `q = PowerSeries.X` over `ℚ`; the factor
`1/(1 - q^m)` is the inverse `(1 - X ^ m)⁻¹` in `ℚ⟦X⟧`. Indices are lists of
natural numbers.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- Partial sums of SZ-qMZVs: for an index `(k₁, …, kᵣ)` and a bound `M`,
`∑_{M > m₁ > ⋯ > mᵣ > 0} ∏ⱼ q^{mⱼ kⱼ} / (1 - q^{mⱼ})^{kⱼ}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs (defining sum truncated at
`m₁ < M`). -/
public noncomputable def szQMZVPartial : List ℕ → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | k :: ks, M => ∑ m ∈ Finset.Ioo 0 M, (X ^ m * (1 - X ^ m)⁻¹) ^ k * szQMZVPartial ks m

/-- The Schlesinger–Zudilin qMZV
`ζ_q^SZ(k₁, …, kᵣ) = ∑_{m₁ > ⋯ > mᵣ > 0} ∏ⱼ q^{mⱼ kⱼ} / (1 - q^{mⱼ})^{kⱼ}`,
with `ζ_q^SZ(∅) = 1`. For an SZ-admissible index (empty, or `k₁ ≥ 1`) the
summands with `m₁ > N` have `q`-adic order `> N`, so the coefficient of `q^N` is
that of the partial sum with `m₁ ≤ N`; this is the definition used here. The
value for indices with `k₁ = 0` (not defined in the paper) is a junk value.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs (extended version of
Ebrahimi-Fard, Manchon and Singer, allowing `kⱼ = 0` for `j ≥ 2`). -/
public noncomputable def szQMZV (k : List ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun N => coeff N (szQMZVPartial k (N + 1))

/-- `ζ_q^SZ(∅) = 1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem szQMZV_nil : szQMZV [] = 1 := by
  ext N
  simp [szQMZV, szQMZVPartial]

/-- The defining sum peels off its outermost summation variable.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem szQMZVPartial_cons (k : ℕ) (ks : List ℕ) (M : ℕ) :
    szQMZVPartial (k :: ks) M =
      ∑ m ∈ Finset.Ioo 0 M, (X ^ m * (1 - X ^ m)⁻¹) ^ k * szQMZVPartial ks m :=
  rfl

/-- A nonempty SZ-qMZV has no constant term.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem coeff_zero_szQMZV_cons (k : ℕ) (ks : List ℕ) :
    coeff 0 (szQMZV (k :: ks)) = 0 := by
  have h : Finset.Ioo 0 1 = ∅ := by decide
  simp [szQMZV, szQMZVPartial, h]

/-- The coefficient of `q` in `ζ_q^SZ(1) = ∑_{m > 0} q^m / (1 - q^m)` is `1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem coeff_one_szQMZV_singleton_one : coeff 1 (szQMZV [1]) = 1 := by
  have h : Finset.Ioo 0 2 = {1} := by decide
  simp [szQMZV, szQMZVPartial, h, coeff_succ_X_mul, constantCoeff_inv]

/-- The SZ index `(k₁, {0}^{d₁-1}, …, kᵣ, {0}^{dᵣ-1})` built from the list of
pairs `[(k₁, d₁), …, (kᵣ, dᵣ)]`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 4 and Theorem 5 (SZ duality), index notation. -/
public def szBlockIndex (kd : List (ℕ × ℕ)) : List ℕ :=
  (kd.map fun p => p.1 :: List.replicate (p.2 - 1) 0).flatten

/-- `szBlockIndex [] = []`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 5, index notation. -/
public theorem szBlockIndex_nil : szBlockIndex [] = [] := rfl

/-- `szBlockIndex ((k, d) :: kd) = k :: {0}^{d-1} ++ szBlockIndex kd`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 5, index notation. -/
public theorem szBlockIndex_cons (k d : ℕ) (kd : List (ℕ × ℕ)) :
    szBlockIndex ((k, d) :: kd) = k :: (List.replicate (d - 1) 0 ++ szBlockIndex kd) :=
  rfl

/-- Partial OOZ sums without the leading `q^{m₁}`:
`∑_{M > m₁ > ⋯ > mᵣ > 0} ∏ⱼ 1 / (1 - q^{mⱼ})^{kⱼ}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs (inner sums of the defining series). -/
public noncomputable def oozQMZVPartial : List ℕ → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | k :: ks, M => ∑ m ∈ Finset.Ioo 0 M, ((1 - X ^ m)⁻¹) ^ k * oozQMZVPartial ks m

/-- The (extended) Ohno–Okuda–Zudilin qMZV
`ζ_q^OOZ(k₁, …, kᵣ) = ∑_{m₁ > ⋯ > mᵣ > 0} q^{m₁} / ((1 - q^{m₁})^{k₁} ⋯ (1 - q^{mᵣ})^{kᵣ})`,
with `ζ_q^OOZ(∅) = 1`. Summands with `m₁ > N` have `q`-adic order `> N`, so the
coefficient of `q^N` is computed from the summands with `m₁ ≤ N`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs (extended version, `k₁ ≥ 1`, `kᵢ ≥ 0`). -/
public noncomputable def oozQMZV : List ℕ → ℚ⟦X⟧
  | [] => 1
  | k :: ks => PowerSeries.mk fun N =>
      coeff N (∑ m ∈ Finset.Ioo 0 (N + 1), X ^ m * ((1 - X ^ m)⁻¹) ^ k * oozQMZVPartial ks m)

/-- `ζ_q^OOZ(∅) = 1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs. -/
public theorem oozQMZV_nil : oozQMZV [] = 1 := rfl

/-- A nonempty OOZ-qMZV has no constant term.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs. -/
public theorem coeff_zero_oozQMZV_cons (k : ℕ) (ks : List ℕ) :
    coeff 0 (oozQMZV (k :: ks)) = 0 := by
  have h : Finset.Ioo 0 1 = ∅ := by decide
  simp [oozQMZV, h]

/-- Generating series of SZ-qMZVs, coefficientwise: for `kⱼ, dⱼ ≥ 1` the coefficient
of `q^N` in `ζ_q^SZ(k₁, {0}^{d₁-1}, …, kᵣ, {0}^{dᵣ-1})` is
`∑ ∏ⱼ C(nⱼ - 1, kⱼ - 1) C(mⱼ - mⱼ₊₁ - 1, dⱼ - 1)` over `m₁ > ⋯ > mᵣ > 0`,
`n₁, …, nᵣ ≥ 1` with `∑ mⱼ nⱼ = N` and `m_{r+1} := 0`. This is the coefficient of
`X₁^{k₁-1}⋯Xᵣ^{kᵣ-1} Y₁^{d₁-1}⋯Yᵣ^{dᵣ-1} q^N` on both sides of the paper's identity
`s(X; Y) = ∑ ∏ⱼ (1 + Xⱼ)^{nⱼ-1} (1 + Yⱼ)^{mⱼ-mⱼ₊₁-1} q^{mⱼ nⱼ}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 4 (`integers-2024-A6-thm-4`). -/
public theorem_wanted coeff_szQMZV_szBlockIndex_eq_sum_choose (r : ℕ) (k d : Fin r → ℕ)
    (hk : ∀ j, 1 ≤ k j) (hd : ∀ j, 1 ≤ d j) (N : ℕ) :
    coeff N (szQMZV (szBlockIndex (List.ofFn fun j => (k j, d j)))) =
      ∑ mn ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (N + 1)) ×ˢ
          (Fintype.piFinset fun _ : Fin r => Finset.range (N + 1)) with
          StrictAnti mn.1 ∧ (∀ j, 0 < mn.1 j) ∧ (∀ j, 0 < mn.2 j) ∧
            ∑ j, mn.1 j * mn.2 j = N,
        ∏ j : Fin r, ((((mn.2 j - 1).choose (k j - 1)) *
          ((mn.1 j - (if h : j.val + 1 < r then mn.1 ⟨j.val + 1, h⟩ else 0) - 1).choose
            (d j - 1)) : ℕ) : ℚ)

/-- SZ duality in index form: for `kⱼ, dⱼ ≥ 1`,
`ζ_q^SZ(k₁, {0}^{d₁-1}, …, kᵣ, {0}^{dᵣ-1}) = ζ_q^SZ(dᵣ, {0}^{kᵣ-1}, …, d₁, {0}^{k₁-1})`.
The paper's equivalent word form `ζ_q^SZ ∘ τ̃ = ζ_q^SZ` on `𝔎¹` is not stated
separately.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 5 (SZ duality, Zhao) (`integers-2024-A6-thm-5`). -/
public theorem_wanted szQMZV_szBlockIndex_dual (kd : List (ℕ × ℕ))
    (hkd : ∀ p ∈ kd, 1 ≤ p.1 ∧ 1 ≤ p.2) :
    szQMZV (szBlockIndex kd) = szQMZV (szBlockIndex (kd.reverse.map Prod.swap))

/-- `∑_{r ≥ 1} ζ_q^SZ({1}^r) = ∑_{N ≥ 1} p(N) q^N`, coefficientwise: the coefficient
of `q^N` (`N ≥ 1`) in `∑_{r=1}^{R} ζ_q^SZ({1}^r)` is the number of partitions of
`N` for every `R ≥ N` (the summands with `r > N` have no `q^N` term).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 3 (`integers-2024-A6-lem-3`). -/
public theorem_wanted sum_coeff_szQMZV_replicate_one_eq_card_partition (N R : ℕ)
    (hN : 1 ≤ N) (hR : N ≤ R) :
    ∑ r ∈ Finset.Icc 1 R, coeff N (szQMZV (List.replicate r 1)) =
      Fintype.card N.Partition

/-- Conjugacy classes of `S_n` correspond bijectively to partitions of `n`, via the
cycle type: there is an equivalence sending the class of `σ` to `σ.partition`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 4 (`integers-2024-A6-lem-4`). -/
public theorem_wanted exists_conjClasses_perm_equiv_partition (n : ℕ) :
    ∃ e : ConjClasses (Equiv.Perm (Fin n)) ≃ (Fintype.card (Fin n)).Partition,
      ∀ σ : Equiv.Perm (Fin n), e (ConjClasses.mk σ) = σ.partition

/-- The number of conjugacy classes of `S_n` is the partition number `p(n)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 4 (`integers-2024-A6-lem-4`). -/
public theorem_wanted card_conjClasses_perm_eq_card_partition (n : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Fin n))) = Fintype.card n.Partition

/-- For a finite field `K` with `c` elements,
`∑_{n ≥ 0} a_{n,K} q^n = ∑_{r ≥ 0} (c - 1)^r ζ_q^OOZ({1}^r)`, where `a_{n,K}` is the
number of conjugacy classes of `GL(n, K)` (`a_{0,K} = 1`, the class number of the
trivial group `GL(0, K)`). Stated coefficientwise: for every `R ≥ N` the
coefficient of `q^N` in `∑_{r=0}^{R} (c - 1)^r ζ_q^OOZ({1}^r)` is `a_{N,K}` (the
summands with `r > N` have no `q^N` term).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 20 (`integers-2024-A6-thm-20`). -/
public theorem_wanted card_conjClasses_GL_eq_coeff_sum_oozQMZV (K : Type*) [Field K]
    [Fintype K] (N R : ℕ) (hR : N ≤ R) :
    (Nat.card (ConjClasses (GL (Fin N) K)) : ℚ) =
      ∑ r ∈ Finset.range (R + 1),
        ((Fintype.card K : ℚ) - 1) ^ r * coeff N (oozQMZV (List.replicate r 1))

/-- Partial sums of general qMZVs: for data `[(k₁, Q₁), …, (kᵣ, Qᵣ)]` and a bound
`M`, `∑_{M > m₁ > ⋯ > mᵣ > 0} ∏ⱼ Qⱼ(q^{mⱼ}) / (1 - q^{mⱼ})^{kⱼ}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs (after Bachmann–Kühn), defining sum truncated at
`m₁ < M`. -/
public noncomputable def qMZVPartial : List (ℕ × Polynomial ℚ) → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | (k, Q) :: kQ, M => ∑ m ∈ Finset.Ioo 0 M,
      Polynomial.aeval (X ^ m : ℚ⟦X⟧) Q * ((1 - X ^ m)⁻¹) ^ k * qMZVPartial kQ m

/-- The general qMZV
`ζ_q(k₁, …, kᵣ; Q₁, …, Qᵣ) = ∑_{m₁ > ⋯ > mᵣ > 0} ∏ⱼ Qⱼ(q^{mⱼ}) / (1 - q^{mⱼ})^{kⱼ}`
with `ζ_q(∅; ∅) = 1`. When `Q₁(0) = 0` (the paper's condition `Q₁ ∈ X ℚ[X]`) the
summands with `m₁ > N` have `q`-adic order `> N`, so the coefficient of `q^N` is
computed from the summands with `m₁ ≤ N`; for other data the value is junk.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs (after Bachmann–Kühn). -/
public noncomputable def qMZV : List (ℕ × Polynomial ℚ) → ℚ⟦X⟧
  | [] => 1
  | (k, Q) :: kQ => PowerSeries.mk fun N => coeff N (∑ m ∈ Finset.Ioo 0 (N + 1),
      Polynomial.aeval (X ^ m : ℚ⟦X⟧) Q * ((1 - X ^ m)⁻¹) ^ k * qMZVPartial kQ m)

/-- `ζ_q(∅; ∅) = 1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs. -/
public theorem qMZV_nil : qMZV [] = 1 := rfl

/-- A nonempty general qMZV has no constant term.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs. -/
public theorem coeff_zero_qMZV_cons (k : ℕ) (Q : Polynomial ℚ) (kQ : List (ℕ × Polynomial ℚ)) :
    coeff 0 (qMZV ((k, Q) :: kQ)) = 0 := by
  have h : Finset.Ioo 0 1 = ∅ := by decide
  simp [qMZV, h]

/-- The `ℚ`-span `𝒵_{q,d}` of the general qMZVs `ζ_q(k₁, …, kᵣ; Q₁, …, Qᵣ)` with
`Q₁(0) = 0` and `deg Qⱼ ≤ kⱼ - d` (encoded as `natDegree Qⱼ + d ≤ kⱼ`, which for
`d = 1` also forces `kⱼ ≥ 1`). `qMZVSpace 0` is the algebra `𝒵_q` of qMZVs
(`kⱼ ≥ 0`) and `qMZVSpace 1` is `𝒵_{q,1}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs (ii) and Definition of `𝒵_{q,d}` (after
Bachmann–Kühn). -/
public noncomputable def qMZVSpace (d : ℕ) : Submodule ℚ ℚ⟦X⟧ :=
  Submodule.span ℚ {f | ∃ kQ : List (ℕ × Polynomial ℚ),
    (∀ p ∈ kQ, p.2.natDegree + d ≤ p.1) ∧ (∀ p ∈ kQ.head?, p.2.coeff 0 = 0) ∧ f = qMZV kQ}

/-- `1 ∈ 𝒵_{q,d}` (the empty qMZV).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs (ii). -/
public theorem one_mem_qMZVSpace (d : ℕ) : (1 : ℚ⟦X⟧) ∈ qMZVSpace d :=
  Submodule.subset_span ⟨[], by simp, by simp, rfl⟩

/-- The Bradley–Zhao qMZV `ζ_q^BZ(k) = ζ_q(k₁, …, kᵣ; X^{k₁-1}, …, X^{kᵣ-1})
= ∑_{m₁ > ⋯ > mᵣ > 0} ∏ⱼ q^{mⱼ(kⱼ-1)} / (1 - q^{mⱼ})^{kⱼ}` of an admissible
index (`k₁ ≥ 2`, `kᵢ ≥ 1`); junk for other indices.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Bradley–Zhao qMZVs. -/
public noncomputable def bzQMZV (k : List ℕ) : ℚ⟦X⟧ :=
  qMZV (k.map fun k => (k, Polynomial.X ^ (k - 1)))

/-- `ζ_q^BZ(∅) = 1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Bradley–Zhao qMZVs. -/
public theorem bzQMZV_nil : bzQMZV [] = 1 := rfl

/-- A nonempty BZ-qMZV has no constant term.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Bradley–Zhao qMZVs. -/
public theorem coeff_zero_bzQMZV_cons (k : ℕ) (ks : List ℕ) :
    coeff 0 (bzQMZV (k :: ks)) = 0 :=
  coeff_zero_qMZV_cons _ _ _

/-- The admissible index `(a₁ + 1, {1}^{b₁-1}, …, aᵣ + 1, {1}^{bᵣ-1})` built from
`[(a₁, b₁), …, (aᵣ, bᵣ)]`; for `aⱼ, bⱼ ≥ 1` it corresponds to the word
`x^{a₁} y^{b₁} ⋯ x^{aᵣ} y^{bᵣ}` of `𝔥⁰`, and the duality `τ` maps it to the index
of `[(bᵣ, aᵣ), …, (b₁, a₁)]`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 6 and Theorem 7 (BZ duality), index notation. -/
public def bzBlockIndex (ab : List (ℕ × ℕ)) : List ℕ :=
  (ab.map fun p => (p.1 + 1) :: List.replicate (p.2 - 1) 1).flatten

/-- `bzBlockIndex ((a, b) :: ab) = (a + 1) :: {1}^{b-1} ++ bzBlockIndex ab`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 7, index notation. -/
public theorem bzBlockIndex_cons (a b : ℕ) (ab : List (ℕ × ℕ)) :
    bzBlockIndex ((a, b) :: ab) = (a + 1) :: (List.replicate (b - 1) 1 ++ bzBlockIndex ab) :=
  rfl

/-- SZ-qMZVs span `𝒵_q`, and `𝒵_q` (hence the SZ model) is closed under `q d/dq`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 3 (`integers-2024-A6-prop-3`). -/
public theorem_wanted qMZVSpace_zero_eq_span_szQMZV :
    qMZVSpace 0 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ k₁ ∈ k.head?, 1 ≤ k₁) ∧ f = szQMZV k} ∧
      ∀ f ∈ qMZVSpace 0, X * derivative f ∈ qMZVSpace 0

/-- BZ-qMZVs of admissible indices span `𝒵_{q,1}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 4 (`integers-2024-A6-prop-4`). -/
public theorem_wanted qMZVSpace_one_eq_span_bzQMZV :
    qMZVSpace 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 1 ≤ kᵢ) ∧ (∀ k₁ ∈ k.head?, 2 ≤ k₁) ∧ f = bzQMZV k}

/-- The spans of the OOZ model: (i) `𝒵_{q,1}` is spanned by the `ζ_q^OOZ(k)` with
`k₁ ≥ 2`, `kᵢ ≥ 1`; (ii) `𝒵_q` is spanned by the `ζ_q^OOZ(k)` with `k₁ ≥ 1`,
`kᵢ ≥ 0`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 10 (`integers-2024-A6-prop-10`). -/
public theorem_wanted qMZVSpace_eq_span_oozQMZV :
    qMZVSpace 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 1 ≤ kᵢ) ∧ (∀ k₁ ∈ k.head?, 2 ≤ k₁) ∧ f = oozQMZV k} ∧
      qMZVSpace 0 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ k₁ ∈ k.head?, 1 ≤ k₁) ∧ f = oozQMZV k}

/-- BZ duality `ζ_q^BZ ∘ τ = ζ_q^BZ` on `𝔥⁰`, in index form: for `aⱼ, bⱼ ≥ 1`,
`ζ_q^BZ(a₁ + 1, {1}^{b₁-1}, …, aᵣ + 1, {1}^{bᵣ-1}) =
ζ_q^BZ(bᵣ + 1, {1}^{aᵣ-1}, …, b₁ + 1, {1}^{a₁-1})`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 7 (BZ duality, Bradley; Seki–Yamamoto)
(`integers-2024-A6-thm-7`). -/
public theorem_wanted bzQMZV_bzBlockIndex_dual (ab : List (ℕ × ℕ))
    (hab : ∀ p ∈ ab, 1 ≤ p.1 ∧ 1 ≤ p.2) :
    bzQMZV (bzBlockIndex ab) = bzQMZV (bzBlockIndex (ab.reverse.map Prod.swap))

/-- q-Ohno relations: for an admissible index `k = (a₁ + 1, {1}^{b₁-1}, …)` with dual
`k^∨` and every `c ≥ 0`, `∑_{|𝐜| = c} ζ_q^BZ(k + 𝐜) = ∑_{|𝐜'| = c} ζ_q^BZ(k^∨ + 𝐜')`,
the sums over `𝐜 ∈ ℕ^{depth k}` and `𝐜' ∈ ℕ^{depth k^∨}` with entry sum `c`, added
componentwise.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 8 (q-Ohno relations, Okuda–Takeyama)
(`integers-2024-A6-thm-8`). -/
public theorem_wanted sum_bzQMZV_add_eq_sum_bzQMZV_dual_add (ab : List (ℕ × ℕ))
    (hab : ∀ p ∈ ab, 1 ≤ p.1 ∧ 1 ≤ p.2) (c : ℕ) :
    ∑ cs ∈ Finset.Nat.antidiagonalTuple (bzBlockIndex ab).length c,
        bzQMZV (List.zipWith (· + ·) (bzBlockIndex ab) (List.ofFn cs)) =
      ∑ cs ∈ Finset.Nat.antidiagonalTuple
          (bzBlockIndex (ab.reverse.map Prod.swap)).length c,
        bzQMZV (List.zipWith (· + ·) (bzBlockIndex (ab.reverse.map Prod.swap)) (List.ofFn cs))

/-- The set `𝒫_r(N)` of partitions of `N` of length `r` in Stanley coordinates:
pairs `((m₁, …, mᵣ), (n₁, …, nᵣ))` of positive integers with `m₁ > ⋯ > mᵣ` and
`m₁ n₁ + ⋯ + mᵣ nᵣ = N` (all coordinates are then at most `N`).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Stanley coordinates and of `𝒫_r(N)` (Section 4). -/
public def stanleyPartitions (r N : ℕ) : Finset ((Fin r → ℕ) × (Fin r → ℕ)) :=
  ((Fintype.piFinset fun _ : Fin r => Finset.Icc 1 N) ×ˢ
      (Fintype.piFinset fun _ : Fin r => Finset.Icc 1 N)).filter
    fun p => (∀ i j : Fin r, i < j → p.1 j < p.1 i) ∧ ∑ j, p.1 j * p.2 j = N

/-- Membership in `𝒫_r(N)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of `𝒫_r(N)` (Section 4). -/
public theorem mem_stanleyPartitions {r N : ℕ} {p : (Fin r → ℕ) × (Fin r → ℕ)} :
    p ∈ stanleyPartitions r N ↔
      (∀ i j : Fin r, i < j → p.1 j < p.1 i) ∧ (∀ j, 0 < p.1 j) ∧ (∀ j, 0 < p.2 j) ∧
        ∑ j, p.1 j * p.2 j = N := by
  constructor
  · intro h
    simp only [stanleyPartitions, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
      Finset.mem_Icc] at h
    exact ⟨h.2.1, fun j => (h.1.1 j).1, fun j => (h.1.2 j).1, h.2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hle : ∀ j, p.1 j * p.2 j ≤ N := fun j =>
      h4 ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (p.1 i * p.2 i)) (Finset.mem_univ j)
    simp only [stanleyPartitions, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
      Finset.mem_Icc]
    exact ⟨⟨fun j => ⟨h2 j, (Nat.le_mul_of_pos_right _ (h3 j)).trans (hle j)⟩,
      fun j => ⟨h3 j, (Nat.le_mul_of_pos_left _ (h2 j)).trans (hle j)⟩⟩, h1, h4⟩

/-- The transposed partition `ρ(𝐦, 𝐧) = ((n₁ + ⋯ + nᵣ, …, n₁ + n₂, n₁),
(mᵣ, mᵣ₋₁ - mᵣ, …, m₁ - m₂))` in Stanley coordinates (Young diagram reflected in
the main diagonal); with `0`-based indices, `ρ.1 j = ∑_{i + j < r} nᵢ` and
`ρ.2 j = m_{r-1-j} - m_{r-j}` with `m_r := 0`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Section 4, transposed partition in Stanley coordinates. -/
public def stanleyTranspose {r : ℕ} (p : (Fin r → ℕ) × (Fin r → ℕ)) :
    (Fin r → ℕ) × (Fin r → ℕ) :=
  (fun j => ∑ i : Fin r with i.val + j.val < r, p.2 i,
    fun j => p.1 (Fin.rev j) -
      (if h : (Fin.rev j).val + 1 < r then p.1 ⟨(Fin.rev j).val + 1, h⟩ else 0))

/-- For partitions of length one, `ρ((m), (n)) = ((n), (m))`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Section 4, transposed partition in Stanley coordinates. -/
public theorem stanleyTranspose_fin_one (m n : Fin 1 → ℕ) :
    stanleyTranspose (m, n) = (n, m) := by
  ext j <;> fin_cases j <;> simp [stanleyTranspose]

/-- Summing any function over `𝒫_r(N)` is invariant under composing it with the
transposition `ρ`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 1 (`integers-2024-A6-lem-1`). -/
public theorem_wanted sum_stanleyPartitions_comp_stanleyTranspose (r N : ℕ)
    (a : (Fin r → ℕ) × (Fin r → ℕ) → ℚ) :
    ∑ p ∈ stanleyPartitions r N, a p = ∑ p ∈ stanleyPartitions r N, a (stanleyTranspose p)

/-- Every general qMZV `ζ_q(k₁, …, kᵣ; Q₁, …, Qᵣ) ∈ 𝒵_q` with `r ≥ 1` is
`∑_{(𝐦, 𝐧) ∈ 𝒫_{≤ r}} a_{𝐦,𝐧} q^{m₁n₁ + ⋯}` with coefficients given on each
`𝒫_s` (`1 ≤ s ≤ r`) by a polynomial `f_s ∈ ℚ[X₁, …, X_s, Y₁, …, Y_s]` in
`m₁, …, m_s, n₁, …, n_s`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 18 (`integers-2024-A6-thm-18`). -/
public theorem_wanted exists_mvPolynomial_coeff_qMZV_eq_sum_stanleyPartitions
    (kQ : List (ℕ × Polynomial ℚ)) (hr : kQ ≠ [])
    (hdeg : ∀ p ∈ kQ, p.2.natDegree ≤ p.1) (h0 : ∀ p ∈ kQ.head?, p.2.coeff 0 = 0) :
    ∃ f : (s : ℕ) → MvPolynomial (Fin s ⊕ Fin s) ℚ, ∀ N,
      coeff N (qMZV kQ) = ∑ s ∈ Finset.Icc 1 kQ.length, ∑ p ∈ stanleyPartitions s N,
        MvPolynomial.eval (Sum.elim (fun j => (p.1 j : ℚ)) fun j => (p.2 j : ℚ)) (f s)

/-- A `q`-series `S` lies in `𝒵_q` iff there are `f₀ ∈ ℚ` and polynomials
`f_r ∈ ℚ[X₁, …, X_r, Y₁, …, Y_r]`, all but finitely many zero, with
`S = f₀ + ∑_{N ≥ 1} (∑_{r ≥ 1} ∑_{(𝐦, 𝐧) ∈ 𝒫_r(N)} f_r(𝐦, 𝐧)) q^N`. The inner sum is
written over `1 ≤ r ≤ N`, which is exact because `𝒫_r(N)` is empty for `r > N`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 19 (`integers-2024-A6-thm-19`). -/
public theorem_wanted mem_qMZVSpace_zero_iff_exists_mvPolynomial (S : ℚ⟦X⟧) :
    S ∈ qMZVSpace 0 ↔ ∃ (f₀ : ℚ) (f : (r : ℕ) → MvPolynomial (Fin r ⊕ Fin r) ℚ) (R : ℕ),
      (∀ r, R < r → f r = 0) ∧
      ∀ N, coeff N S = if N = 0 then f₀ else
        ∑ r ∈ Finset.Icc 1 N, ∑ p ∈ stanleyPartitions r N,
          MvPolynomial.eval (Sum.elim (fun j => (p.1 j : ℚ)) fun j => (p.2 j : ℚ)) (f r)

/-- The quasi-shuffle product of two words over an alphabet `α` with a product of
letters `d : α → α → List α` (the formal sum of the listed letters), returned as the
formal sum (list) of words: `𝟏 ∗ w = w ∗ 𝟏 = w` and
`a u ∗ b v = a (u ∗ b v) + b (a u ∗ v) + (a ⋄ b)(u ∗ v)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, quasi-shuffle products of Section 2 (the induced quasi-shuffle
products on `M`, `𝔎`, `𝔥¹`). -/
public def quasiShuffle {α : Type*} (d : α → α → List α) : List α → List α → List (List α)
  | [], v => [v]
  | a :: u, [] => [a :: u]
  | a :: u, b :: v =>
      (quasiShuffle d u (b :: v)).map (a :: ·) ++ (quasiShuffle d (a :: u) v).map (b :: ·) ++
        (d a b).flatMap fun c => (quasiShuffle d u v).map (c :: ·)
termination_by u v => u.length + v.length

/-- `𝟏 ∗ w = w`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, quasi-shuffle products of Section 2. -/
public theorem quasiShuffle_nil_left {α : Type*} (d : α → α → List α) (v : List α) :
    quasiShuffle d [] v = [v] := by
  simp [quasiShuffle]

/-- The stuffle of two letters: `a ∗ b = ab + ba + (a + b)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the SZ-stuffle product. -/
public theorem quasiShuffle_singleton_singleton (a b : ℕ) :
    quasiShuffle (fun a b => [a + b]) [a] [b] = [[a, b], [b, a], [a + b]] := by
  simp [quasiShuffle]

/-- The SZ-qshuffle product on words in the letters `p` (`true`) and `y` (`false`):
`𝟏 ш w = w ш 𝟏 = w`, `y u ш v = y (u ш v)`, `p u ш y v = y (p u ш v)`,
`p u ш p v = p (u ш p v) + p (p u ш v) + p (u ш v)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the SZ-qshuffle product. -/
public def szShuffle : List Bool → List Bool → List (List Bool)
  | [], v => [v]
  | false :: u, v => (szShuffle u v).map (false :: ·)
  | true :: u, [] => [true :: u]
  | true :: u, false :: v => (szShuffle (true :: u) v).map (false :: ·)
  | true :: u, true :: v =>
      (szShuffle u (true :: v)).map (true :: ·) ++ (szShuffle (true :: u) v).map (true :: ·) ++
        (szShuffle u v).map (true :: ·)
termination_by u v => u.length + v.length

/-- `y ш y = y y`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the SZ-qshuffle product. -/
public theorem szShuffle_y_y : szShuffle [false] [false] = [[false, false]] := by
  simp [szShuffle]

/-- The word `p^{k₁} y ⋯ p^{kᵣ} y` of an index `(k₁, …, kᵣ)` (`p = true`, `y = false`).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public def szWord (k : List ℕ) : List Bool :=
  (k.map fun n => List.replicate n true ++ [false]).flatten

/-- `szWord [] = []`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public theorem szWord_nil : szWord [] = [] := rfl

/-- Reads the index off a word of `𝔎¹`: the lengths of the maximal `p`-blocks before
each `y`, with `c` the number of `p`s already read (trailing `p`s are dropped).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public def szIndexOfWordAux : ℕ → List Bool → List ℕ
  | _, [] => []
  | c, true :: w => szIndexOfWordAux (c + 1) w
  | c, false :: w => c :: szIndexOfWordAux 0 w

/-- `p^n y w` is read as `(c + n) :: (index of w)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public theorem szIndexOfWordAux_replicate_append (c n : ℕ) (w : List Bool) :
    szIndexOfWordAux c (List.replicate n true ++ false :: w) = (c + n) :: szIndexOfWordAux 0 w := by
  induction n generalizing c with
  | zero => simp [szIndexOfWordAux]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, szIndexOfWordAux, ih]
    congr 1
    omega

/-- `ζ_q^SZ` extended to words of `𝔎¹`: `p^{k₁} y ⋯ p^{kᵣ} y ↦ ζ_q^SZ(k₁, …, kᵣ)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the SZ-qshuffle product (ii). -/
public noncomputable def szQMZVWord (w : List Bool) : ℚ⟦X⟧ :=
  szQMZV (szIndexOfWordAux 0 w)

/-- `szQMZVWord (szWord [k]) = ζ_q^SZ(k)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the SZ-qshuffle product (ii). -/
public theorem szQMZVWord_szWord_singleton (k : ℕ) :
    szQMZVWord (szWord [k]) = szQMZV [k] := by
  simp only [szQMZVWord, szWord, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  rw [szIndexOfWordAux_replicate_append]
  simp [szIndexOfWordAux]

/-- The general evaluation map is an algebra homomorphism for the quasi-shuffle
product on `M` induced by `(k₁, Q₁) ⋄ (k₂, Q₂) = (k₁ + k₂, Q₁ Q₂)`: for words
`u, v` of `M` (letters with `deg Q ≤ k`, first letter with `Q(0) = 0`),
`ζ_q(u ∗ v) = ζ_q(u) ζ_q(v)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 2 (`integers-2024-A6-prop-2`). -/
public theorem_wanted qMZV_mul_eq_sum_quasiShuffle (u v : List (ℕ × Polynomial ℚ))
    (hu : ∀ p ∈ u, p.2.natDegree ≤ p.1) (hu0 : ∀ p ∈ u.head?, p.2.coeff 0 = 0)
    (hv : ∀ p ∈ v, p.2.natDegree ≤ p.1) (hv0 : ∀ p ∈ v.head?, p.2.coeff 0 = 0) :
    qMZV u * qMZV v =
      ((quasiShuffle (fun a b => [(a.1 + b.1, a.2 * b.2)]) u v).map qMZV).sum

/-- `ζ_q^SZ` is an algebra homomorphism on `(𝔎¹, ∗_SZ)`: for SZ-admissible `v, w`,
`ζ_q^SZ(v) ζ_q^SZ(w) = ζ_q^SZ(v ∗_SZ w)`, with the stuffle `∗_SZ` on indices.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 2 (`integers-2024-A6-thm-2`). -/
public theorem_wanted szQMZV_mul_eq_sum_stuffle (v w : List ℕ)
    (hv : ∀ k₁ ∈ v.head?, 1 ≤ k₁) (hw : ∀ k₁ ∈ w.head?, 1 ≤ k₁) :
    szQMZV v * szQMZV w = ((quasiShuffle (fun a b => [a + b]) v w).map szQMZV).sum

/-- `ζ_q^SZ` is an algebra homomorphism on `(𝔎¹, ш_SZ)`: for SZ-admissible indices
`u, v`, `ζ_q^SZ(u) ζ_q^SZ(v) = ζ_q^SZ(u ш_SZ v)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 3 (Singer) (`integers-2024-A6-thm-3`). -/
public theorem_wanted szQMZV_mul_eq_sum_szShuffle (u v : List ℕ)
    (hu : ∀ k₁ ∈ u.head?, 1 ≤ k₁) (hv : ∀ k₁ ∈ v.head?, 1 ≤ k₁) :
    szQMZV u * szQMZV v = ((szShuffle (szWord u) (szWord v)).map szQMZVWord).sum

/-- `ζ_q^BZ` is an algebra homomorphism on `(𝔥⁰, ∗_BZ)`, where `∗_BZ` is the
quasi-shuffle product induced by `z_{k₁} ⋄_BZ z_{k₂} = z_{k₁+k₂} + z_{k₁+k₂-1}`:
for admissible `u, v`, `ζ_q^BZ(u ∗_BZ v) = ζ_q^BZ(u) ζ_q^BZ(v)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 5 (`integers-2024-A6-prop-5`). -/
public theorem_wanted bzQMZV_mul_eq_sum_quasiShuffle (u v : List ℕ)
    (hu : ∀ k ∈ u, 1 ≤ k) (hu₁ : ∀ k₁ ∈ u.head?, 2 ≤ k₁)
    (hv : ∀ k ∈ v, 1 ≤ k) (hv₁ : ∀ k₁ ∈ v.head?, 2 ≤ k₁) :
    bzQMZV u * bzQMZV v =
      ((quasiShuffle (fun a b => [a + b, a + b - 1]) u v).map bzQMZV).sum


/-- Analytic behaviour of general qMZVs: let `k₁, …, kᵣ ≥ 1`, `Q₁(0) = 0` and
`deg Qⱼ ≤ kⱼ` (the paper's admissible data). (i) The series `∑ₙ cₙ qⁿ` of
`ζ_q(k₁, …, kᵣ; Q₁, …, Qᵣ)` converges for complex `|q| < 1`, and `τ ↦ ∑ₙ cₙ e^{2πiτn}` is
holomorphic on the upper half plane. (ii) If moreover `k₁ ≥ 2`, then
`lim_{q → 1⁻} (1 - q)^{k₁+⋯+kᵣ} ζ_q(k₁, …, kᵣ; Q₁, …, Qᵣ) = ζ(k₁, …, kᵣ) ∏ⱼ Qⱼ(1)`, with
`ζ(k₁, …, kᵣ)` the existing `multipleZetaValue` (largest summation index paired with `k₁`).
The record's remark on how the limit is obtained (interchanging limit and sum) is omitted.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 1 (`integers-2024-A6-prop-1`). -/
public theorem_wanted qMZV_summable_differentiableOn_tendsto (kQ : List (ℕ × Polynomial ℚ))
    (hk : ∀ p ∈ kQ, 1 ≤ p.1) (hQ : ∀ p ∈ kQ, p.2.natDegree ≤ p.1)
    (hQ₁ : ∀ p ∈ kQ.head?, p.2.eval 0 = 0) :
    (∀ q : ℂ, ‖q‖ < 1 → Summable fun n : ℕ => ((coeff n (qMZV kQ) : ℚ) : ℂ) * q ^ n) ∧
    DifferentiableOn ℂ
      (fun τ : ℂ => ∑' n : ℕ, ((coeff n (qMZV kQ) : ℚ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * τ) ^ n) {τ : ℂ | 0 < τ.im} ∧
    (∀ p ∈ kQ.head?, 2 ≤ p.1 →
      Filter.Tendsto (fun q : ℝ => (1 - q) ^ (kQ.map Prod.fst).sum *
          ∑' n : ℕ, ((coeff n (qMZV kQ) : ℚ) : ℝ) * q ^ n)
        (nhdsWithin 1 (Set.Iio 1))
        (nhds (multipleZetaValue (kQ.map Prod.fst) *
          ((kQ.map fun p => ((p.2.eval 1 : ℚ) : ℝ)).prod))))


/-- A letter of the Takeyama–Bradley–Zhao model as general-qMZV data: `none` is the symbol
`1̄` (summand `q^m / (1 - q^m)`, data `(1, X)`) and `some k` is `k ∈ ℕ`, `k ≥ 1` (summand
`q^{(k-1)m} / (1 - q^m)^k`, data `(k, X^{k-1})`); `some 0` is junk (data `(0, 1)`).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the Takeyama–Bradley–Zhao model (`f(1̄, m)`, `f(k, m)`). -/
public noncomputable def tbzLetter : Option ℕ → ℕ × Polynomial ℚ
  | none => (1, Polynomial.X)
  | some k => (k, Polynomial.X ^ (k - 1))

/-- The TBZ-qMZV `ζ_q^TBZ(k₁, …, kᵣ) = ∑_{m₁ > ⋯ > mᵣ > 0} f(k₁, m₁) ⋯ f(kᵣ, mᵣ)` for
`kᵢ ∈ ℕ̄ = {1̄} ∪ ℕ` (encoded as `Option ℕ`, `none = 1̄`, `some k` with `k ≥ 1`) with
`k₁ ≠ 1`; junk for `k₁ = 1` and whenever some entry is `some 0` (then `tbzLetter` gives
`(0, 1)`, not a TBZ summand).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the Takeyama–Bradley–Zhao model. -/
public noncomputable def tbzQMZV (k : List (Option ℕ)) : ℚ⟦X⟧ :=
  qMZV (k.map tbzLetter)

/-- `ζ_q^TBZ(∅) = 1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the Takeyama–Bradley–Zhao model. -/
public theorem tbzQMZV_nil : tbzQMZV [] = 1 := rfl

/-- The TBZ model extends the BZ model: on indices without `1̄` it is `ζ_q^BZ`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the Takeyama–Bradley–Zhao model. -/
public theorem tbzQMZV_map_some (k : List ℕ) : tbzQMZV (k.map some) = bzQMZV k := by
  simp only [tbzQMZV, bzQMZV, List.map_map]
  rfl

/-- The TBZ model spans `𝒵_q`: `𝒵_q` is the `ℚ`-span of the `ζ_q^TBZ(k₁, …, kᵣ)` with
`kᵢ ∈ ℕ̄` (entries `some kᵢ` have `kᵢ ≥ 1`) and `k₁ ≠ 1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 6 (`integers-2024-A6-prop-6`). -/
public theorem_wanted qMZVSpace_zero_eq_span_tbzQMZV :
    qMZVSpace 0 = Submodule.span ℚ {f | ∃ k : List (Option ℕ),
        (∀ j ∈ k, ∀ kⱼ ∈ j, 1 ≤ kⱼ) ∧ k.head? ≠ some (some 1) ∧ f = tbzQMZV k}

/-- The space `𝒵°_{q,d}`: the `ℚ`-span of the general qMZVs `ζ_q(k₁, …, kᵣ; Q₁, …, Qᵣ)` with
`kⱼ ≥ 1`, `deg Qⱼ ≤ kⱼ - d` (encoded as `natDegree Qⱼ + d ≤ kⱼ`) and every `Qⱼ ∈ X ℚ[X]`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of `𝒵_{q,d}` and `𝒵°_{q,d}` (after Bachmann–Kühn). -/
public noncomputable def qMZVSpaceCirc (d : ℕ) : Submodule ℚ ℚ⟦X⟧ :=
  Submodule.span ℚ {f | ∃ kQ : List (ℕ × Polynomial ℚ),
    (∀ p ∈ kQ, 1 ≤ p.1 ∧ p.2.natDegree + d ≤ p.1 ∧ p.2.coeff 0 = 0) ∧ f = qMZV kQ}

/-- `1 ∈ 𝒵°_{q,d}` (the empty qMZV).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of `𝒵°_{q,d}`. -/
public theorem one_mem_qMZVSpaceCirc (d : ℕ) : (1 : ℚ⟦X⟧) ∈ qMZVSpaceCirc d :=
  Submodule.subset_span ⟨[], by simp, rfl⟩

/-- `𝒵°_{q,d} ⊆ 𝒵_{q,d}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of `𝒵°_{q,d}` (a subspace of `𝒵_{q,d}`). -/
public theorem qMZVSpaceCirc_le_qMZVSpace (d : ℕ) : qMZVSpaceCirc d ≤ qMZVSpace d := by
  refine Submodule.span_mono ?_
  rintro f ⟨kQ, h, rfl⟩
  exact ⟨kQ, fun p hp => (h p hp).2.1,
    fun p hp => (h p (List.mem_of_mem_head? hp)).2.2, rfl⟩

/-- Okounkov's polynomials: `p_k(X) = X^{k/2}` for even `k` and `X^{(k-1)/2}(1 + X)` for
odd `k`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Okounkov qMZVs. -/
public noncomputable def okounkovPoly (k : ℕ) : Polynomial ℚ :=
  if k % 2 = 0 then Polynomial.X ^ (k / 2) else Polynomial.X ^ ((k - 1) / 2) * (1 + Polynomial.X)

/-- `p₂ = X` and `p₃ = X (1 + X)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Okounkov qMZVs. -/
public theorem okounkovPoly_two_three :
    okounkovPoly 2 = Polynomial.X ∧ okounkovPoly 3 = Polynomial.X * (1 + Polynomial.X) := by
  simp [okounkovPoly]

/-- The Okounkov qMZV `ζ_q^Oko(k₁, …, kᵣ) = ζ_q(k₁, …, kᵣ; p_{k₁}, …, p_{kᵣ})` for indices with
every entry `≥ 2`; junk otherwise.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Okounkov qMZVs. -/
public noncomputable def okounkovQMZV (k : List ℕ) : ℚ⟦X⟧ :=
  qMZV (k.map fun k => (k, okounkovPoly k))

/-- `ζ_q^Oko(∅) = 1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Okounkov qMZVs. -/
public theorem okounkovQMZV_nil : okounkovQMZV [] = 1 := rfl

/-- Okounkov qMZVs span `𝒵°_{q,1}`: `𝒵°_{q,1}` is the `ℚ`-span of the `ζ_q^Oko(k)` with every
`kᵢ ≥ 2`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 13 (after Bachmann–Kühn) (`integers-2024-A6-prop-13`). -/
public theorem_wanted qMZVSpaceCirc_one_eq_span_okounkovQMZV :
    qMZVSpaceCirc 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 2 ≤ kᵢ) ∧ f = okounkovQMZV k}

/-- The `q`-series `∑_{n ≥ 1} n^{k-1}/(k-1)! q^{m n} = P_k(q^m)/(1 - q^m)^k` (`P_k` the `k`-th
Eulerian polynomial), the inner sum of a bi-bracket.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition-Proposition of bi-brackets (Eulerian polynomials). -/
public noncomputable def eulerianQSeries (k m : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun e =>
    if 0 < e ∧ m ∣ e then ((e / m : ℕ) : ℚ) ^ (k - 1) / (k - 1).factorial else 0

/-- The coefficient of `q^{m n}` in `∑_{n ≥ 1} n^{k-1}/(k-1)! q^{m n}` is `n^{k-1}/(k-1)!`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition-Proposition of bi-brackets. -/
public theorem coeff_mul_eulerianQSeries (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    coeff (m * n) (eulerianQSeries k m) = (n : ℚ) ^ (k - 1) / (k - 1).factorial := by
  simp [eulerianQSeries, Nat.mul_pos hm hn, Nat.mul_div_cancel_left n hm]

/-- Partial sums of bi-brackets: for `[(k₁, d₁), …, (kᵣ, dᵣ)]` and a bound `M`,
`∑_{M > m₁ > ⋯ > mᵣ > 0} ∏ⱼ mⱼ^{dⱼ}/dⱼ! ∑_{nⱼ ≥ 1} nⱼ^{kⱼ-1}/(kⱼ-1)! q^{mⱼ nⱼ}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition-Proposition of bi-brackets (defining sum truncated at `m₁ < M`). -/
public noncomputable def biBracketPartial : List (ℕ × ℕ) → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | (k, d) :: kd, M => ∑ m ∈ Finset.Ioo 0 M,
      ((m : ℚ) ^ d / d.factorial) • (eulerianQSeries k m * biBracketPartial kd m)

/-- The bi-bracket
`g(k₁, …, kᵣ; d₁, …, dᵣ) = ∑_{m₁ > ⋯ > mᵣ > 0, n₁, …, nᵣ > 0} ∏ⱼ mⱼ^{dⱼ}/dⱼ! nⱼ^{kⱼ-1}/(kⱼ-1)!
q^{m₁ n₁ + ⋯ + mᵣ nᵣ}` (`kⱼ ≥ 1`, `dⱼ ≥ 0`), with `g(∅; ∅) = 1`, indexed by the list of pairs
`(kⱼ, dⱼ)`. Summands with `m₁ > N` have `q`-adic order `> N`, so the coefficient of `q^N` is
that of the partial sum with `m₁ ≤ N`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition-Proposition of bi-brackets (after Bachmann). -/
public noncomputable def biBracket (kd : List (ℕ × ℕ)) : ℚ⟦X⟧ :=
  PowerSeries.mk fun N => coeff N (biBracketPartial kd (N + 1))

/-- `g(∅; ∅) = 1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition-Proposition of bi-brackets. -/
public theorem biBracket_nil : biBracket [] = 1 := by
  ext N
  simp [biBracket, biBracketPartial]

/-- The generating series of bi-brackets of depth `r`,
`g(X₁, …, Xᵣ; Y₁, …, Yᵣ) = ∑_{kⱼ, dⱼ > 0} g(k₁, …, kᵣ; d₁ - 1, …, dᵣ - 1) ∏ⱼ Xⱼ^{kⱼ-1} Yⱼ^{dⱼ-1}`,
in the variables `Xⱼ = Sum.inl j`, `Yⱼ = Sum.inr j` over `ℚ⟦q⟧`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 11 (definition of the generating series). -/
public noncomputable def biBracketGen (r : ℕ) : MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧ :=
  fun e => biBracket (List.ofFn fun j => (e (Sum.inl j) + 1, e (Sum.inr j)))

/-- The coefficient of `∏ⱼ Xⱼ^{aⱼ} Yⱼ^{bⱼ}` in `g(X; Y)` is `g(a₁ + 1, …; b₁, …)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 11. -/
public theorem coeff_biBracketGen (r : ℕ) (e : Fin r ⊕ Fin r →₀ ℕ) :
    MvPowerSeries.coeff e (biBracketGen r) =
      biBracket (List.ofFn fun j => (e (Sum.inl j) + 1, e (Sum.inr j))) :=
  rfl

/-- The generating series of SZ-qMZVs of depth `r`,
`s(X₁, …, Xᵣ; Y₁, …, Yᵣ) = ∑_{kⱼ ≥ 1, dⱼ ≥ 0} ζ_q^SZ(k₁, {0}^{d₁}, …, kᵣ, {0}^{dᵣ})
∏ⱼ Xⱼ^{kⱼ-1} Yⱼ^{dⱼ}`, in the variables `Xⱼ = Sum.inl j`, `Yⱼ = Sum.inr j` over `ℚ⟦q⟧`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 4 (definition of the generating series). -/
public noncomputable def szGen (r : ℕ) : MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧ :=
  fun e => szQMZV (szBlockIndex (List.ofFn fun j => (e (Sum.inl j) + 1, e (Sum.inr j) + 1)))

/-- The coefficient of `∏ⱼ Xⱼ^{aⱼ} Yⱼ^{bⱼ}` in `s(X; Y)` is
`ζ_q^SZ(a₁ + 1, {0}^{b₁}, …, aᵣ + 1, {0}^{bᵣ})`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 4. -/
public theorem coeff_szGen (r : ℕ) (e : Fin r ⊕ Fin r →₀ ℕ) :
    MvPowerSeries.coeff e (szGen r) =
      szQMZV (szBlockIndex (List.ofFn fun j => (e (Sum.inl j) + 1, e (Sum.inr j) + 1))) :=
  rfl

/-- The series `ln(1 + T) = ∑_{n ≥ 1} (-1)^{n+1} T^n / n`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 13 (ii) (the substitution `Xⱼ ↦ ln(Xⱼ + 1)`). -/
public noncomputable def logOneAddSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ (n + 1) / n

/-- `ln(1 + T)` has no constant term and linear coefficient `1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 13 (ii). -/
public theorem coeff_logOneAddSeries_zero_one :
    coeff 0 logOneAddSeries = 0 ∧ coeff 1 logOneAddSeries = 1 := by
  simp [logOneAddSeries]

/-- Generating series of bi-brackets as a product of exponentials, coefficientwise in `q`: for
every `N`, the coefficient of `q^N` in `g(X₁, …, Xᵣ; Y₁, …, Yᵣ)` is
`∑ ∏ⱼ e^{mⱼ Yⱼ} e^{nⱼ Xⱼ}` over `m₁ > ⋯ > mᵣ > 0`, `n₁, …, nᵣ ≥ 1` with `∑ mⱼ nⱼ = N`
(a finite sum of power series over `ℚ` in the `2r` variables). This is the `q^N`-part of the
paper's identity `g(X; Y) = ∑ ∏ⱼ e^{mⱼ Yⱼ} e^{nⱼ Xⱼ} q^{mⱼ nⱼ}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 11 (after Bachmann) (`integers-2024-A6-thm-11`). -/
public theorem_wanted coeff_biBracketGen_eq_sum_exp (r N : ℕ) :
    (fun e => coeff N (MvPowerSeries.coeff e (biBracketGen r)) :
        MvPowerSeries (Fin r ⊕ Fin r) ℚ) =
      ∑ mn ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (N + 1)) ×ˢ
          (Fintype.piFinset fun _ : Fin r => Finset.range (N + 1)) with
          StrictAnti mn.1 ∧ (∀ j, 0 < mn.1 j) ∧ (∀ j, 0 < mn.2 j) ∧
            ∑ j, mn.1 j * mn.2 j = N,
        ∏ j : Fin r,
          PowerSeries.subst ((mn.1 j : ℚ) • MvPowerSeries.X (Sum.inr j)) (exp ℚ) *
            PowerSeries.subst ((mn.2 j : ℚ) • MvPowerSeries.X (Sum.inl j)) (exp ℚ)

/-- Partition relation for bi-brackets: for `r ≥ 1`,
`g(X₁, …, Xᵣ; Y₁, …, Yᵣ) = g(Y₁ + ⋯ + Yᵣ, …, Y₁ + Y₂, Y₁; Xᵣ, Xᵣ₋₁ - Xᵣ, …, X₁ - X₂)`,
as a substitution of linear forms into the generating series. With `0`-based indices, the `i`-th
upper variable becomes `∑_{j < r - i} Yⱼ` and the `i`-th lower variable becomes
`X_{r-1-i} - X_{r-i}` (with `X_r := 0`). The identity also holds trivially for `r = 0`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 12 (partition relation, after Bachmann) (`integers-2024-A6-thm-12`). -/
public theorem_wanted biBracketGen_partition_relation (r : ℕ) :
    biBracketGen r = MvPowerSeries.subst
      (Sum.elim
        (fun i : Fin r => ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val < r - i.val),
          MvPowerSeries.X (Sum.inr j))
        (fun i : Fin r => MvPowerSeries.X (Sum.inl i.rev) -
          ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val = r - i.val),
            MvPowerSeries.X (Sum.inl j)))
      (biBracketGen r)

/-- Translation between bi-brackets and the SZ model (`r ≥ 1`): (i)
`∏ⱼ e^{Xⱼ} e^{Y₁ + ⋯ + Yⱼ} · s(e^{X₁} - 1, …, e^{Xᵣ} - 1; e^{Y₁} - 1, …, e^{Y₁ + ⋯ + Yᵣ} - 1)
= g(X₁, …, Xᵣ; Y₁, …, Yᵣ)`; (ii)
`∏ⱼ (1 + Xⱼ)(1 + Yⱼ) · s(X₁, …, Xᵣ; Y₁, …, Yᵣ)
= g(ln(X₁ + 1), …, ln(Xᵣ + 1); ln(Y₁ + 1), ln(Y₂ + 1) - ln(Y₁ + 1), …, ln(Yᵣ + 1) - ln(Yᵣ₋₁ + 1))`.
Part (ii) is stated with the unit `∏ⱼ (1 + Xⱼ)(1 + Yⱼ)` multiplied out instead of inverted.
`e^Z` and `ln(1 + Z)` are substitutions of `Z` into `exp ℚ` and `logOneAddSeries`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 13 (translation bi-brackets/SZ model) (`integers-2024-A6-thm-13`). -/
public theorem_wanted biBracketGen_eq_szGen_subst (r : ℕ) :
    (∏ j : Fin r,
        PowerSeries.subst (MvPowerSeries.X (Sum.inl j) :
            MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧) (exp ℚ) *
          PowerSeries.subst (∑ i ∈ Finset.Iic j,
            (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧)) (exp ℚ)) *
        MvPowerSeries.subst
          (Sum.elim
            (fun j : Fin r => PowerSeries.subst (MvPowerSeries.X (Sum.inl j) :
              MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧) (exp ℚ) - 1)
            (fun j : Fin r => PowerSeries.subst (∑ i ∈ Finset.Iic j,
              (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧)) (exp ℚ) - 1))
          (szGen r) = biBracketGen r ∧
    (∏ j : Fin r, (1 + MvPowerSeries.X (Sum.inl j)) * (1 + MvPowerSeries.X (Sum.inr j))) *
        szGen r =
      MvPowerSeries.subst
        (Sum.elim
          (fun j : Fin r => PowerSeries.subst (MvPowerSeries.X (Sum.inl j) :
            MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧) logOneAddSeries)
          (fun j : Fin r => PowerSeries.subst (MvPowerSeries.X (Sum.inr j) :
              MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧) logOneAddSeries -
            ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val + 1 = j.val),
              PowerSeries.subst (MvPowerSeries.X (Sum.inr i) :
                MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧) logOneAddSeries))
        (biBracketGen r)

/-- Generating series of OOZ-qMZVs, coefficientwise: for `kⱼ ≥ 1` and `dⱼ ≥ 0`, the coefficient
of `q^N` in `ζ_q^OOZ(k₁, {0}^{d₁}, …, kᵣ, {0}^{dᵣ})` equals that of
`∑ q^{m₁} ∏ⱼ C(mⱼ - mⱼ₊₁ - 1, dⱼ) / (1 - q^{mⱼ})^{kⱼ}` over `N ≥ m₁ > ⋯ > mᵣ > 0`
(`m_{r+1} := 0`; summands with `m₁ > N` have `q`-order `> N`). This is the coefficient of
`∏ⱼ Xⱼ^{kⱼ}/kⱼ! Yⱼ^{dⱼ}` on both sides of the paper's identity
`𝔬𝔷(X; Y) = ∑ q^{m₁} ∏ⱼ (1 + Yⱼ)^{mⱼ-mⱼ₊₁-1} (e^{Xⱼ/(1 - q^{mⱼ})} - 1)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 11 (`integers-2024-A6-prop-11`). -/
public theorem_wanted coeff_oozQMZV_szBlockIndex_eq_sum_choose (r : ℕ) (k d : Fin r → ℕ)
    (hk : ∀ j, 1 ≤ k j) (N : ℕ) :
    coeff N (oozQMZV (szBlockIndex (List.ofFn fun j => (k j, d j + 1)))) =
      coeff N (∑ m ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (N + 1)) with
          StrictAnti m ∧ ∀ j, 0 < m j,
        X ^ (if h : 0 < r then m ⟨0, h⟩ else 0) *
          ∏ j : Fin r, ((((m j - (if h : j.val + 1 < r then m ⟨j.val + 1, h⟩ else 0) - 1).choose
            (d j) : ℕ) : ℚ⟦X⟧) * ((1 - X ^ m j)⁻¹) ^ k j))

/-- `𝒵°_{q,1}` is spanned by brackets, by Okounkov qMZVs, and by Bradley–Zhao qMZVs, each with all
entries `kᵢ ≥ 2`: `𝒵°_{q,1} = ⟨g(k) | kᵢ ≥ 2⟩ = ⟨ζ_q^Oko(k) | kᵢ ≥ 2⟩ = ⟨ζ_q^BZ(k) | kᵢ ≥ 2⟩`.
The bracket `g(k₁, …, kᵣ)` is the bi-bracket with all `dⱼ = 0`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 16 (`integers-2024-A6-prop-16`). -/
public theorem_wanted qMZVSpaceCirc_one_eq_span_bracket_okounkov_bz :
    qMZVSpaceCirc 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 2 ≤ kᵢ) ∧ f = biBracket (k.map fun kᵢ => (kᵢ, 0))} ∧
      qMZVSpaceCirc 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 2 ≤ kᵢ) ∧ f = okounkovQMZV k} ∧
      qMZVSpaceCirc 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 2 ≤ kᵢ) ∧ f = bzQMZV k}

/-- The quasi-shuffle product with weighted letter product `d : α → α → (α →₀ ℚ)` on formal
`ℚ`-linear combinations of words: `𝟏 ∗ w = w ∗ 𝟏 = w` and
`a u ∗ b v = a (u ∗ b v) + b (a u ∗ v) + ∑_c d(a, b)_c · c (u ∗ v)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
quasi-shuffle products of Section 2 (with `ℚ`-valued letter product, as for bi-brackets). -/
public noncomputable def weightedQuasiShuffle {α : Type*} (d : α → α → (α →₀ ℚ)) :
    List α → List α → (List α →₀ ℚ)
  | [], v => Finsupp.single v 1
  | a :: u, [] => Finsupp.single (a :: u) 1
  | a :: u, b :: v =>
      (weightedQuasiShuffle d u (b :: v)).mapDomain (a :: ·) +
        (weightedQuasiShuffle d (a :: u) v).mapDomain (b :: ·) +
        (d a b).sum fun c x => x • (weightedQuasiShuffle d u v).mapDomain (c :: ·)
termination_by u v => u.length + v.length

/-- `𝟏 ∗ w = w` for the weighted quasi-shuffle.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
quasi-shuffle products of Section 2. -/
public theorem weightedQuasiShuffle_nil_left {α : Type*} (d : α → α → (α →₀ ℚ)) (v : List α) :
    weightedQuasiShuffle d [] v = Finsupp.single v 1 := by
  simp [weightedQuasiShuffle]

/-- Bachmann's coefficients
`λ_{a,b}^j = (-1)^{b-1} C(a + b - j - 1, a - j) B_{a+b-j} / (a + b - j)!`, with Mathlib's
Bernoulli numbers `bernoulli` (`B₁ = -1/2`).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the bi-bracket product `⊠` (after Bachmann). -/
public noncomputable def biBracketLambda (a b j : ℕ) : ℚ :=
  (-1) ^ (b - 1) * ((a + b - j - 1).choose (a - j) : ℚ) * bernoulli (a + b - j) /
    (a + b - j).factorial

/-- `λ_{1,1}^1 = B₁ = -1/2`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the bi-bracket product `⊠`. -/
public theorem biBracketLambda_one_one_one : biBracketLambda 1 1 1 = -1 / 2 := by
  simp [biBracketLambda, bernoulli_one]

/-- Bachmann's product on letters `z_{k,d}` (pairs `(k, d)`):
`z_{k₁,d₁} ⊠ z_{k₂,d₂} = C(d₁ + d₂, d₁) (∑_{j ≤ k₁} λ_{k₁,k₂}^j z_{j,d₁+d₂}
+ ∑_{j ≤ k₂} λ_{k₂,k₁}^j z_{j,d₁+d₂} + z_{k₁+k₂,d₁+d₂})`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the bi-bracket product `⊠` (after Bachmann). -/
public noncomputable def biBracketDiamond (x y : ℕ × ℕ) : (ℕ × ℕ) →₀ ℚ :=
  ((x.2 + y.2).choose x.2 : ℚ) •
    ((∑ j ∈ Finset.Icc 1 x.1, biBracketLambda x.1 y.1 j • Finsupp.single (j, x.2 + y.2) 1) +
      (∑ j ∈ Finset.Icc 1 y.1, biBracketLambda y.1 x.1 j • Finsupp.single (j, x.2 + y.2) 1) +
      Finsupp.single (x.1 + y.1, x.2 + y.2) 1)

/-- Bi-brackets form a quasi-shuffle algebra: for words `u, v` in the letters `z_{k,d}`
(`k ≥ 1`, `d ≥ 0`), `g(u) g(v) = g(u ⊠∗ v)`, where `⊠∗` is the quasi-shuffle product induced by
`biBracketDiamond` and `g` is extended `ℚ`-linearly. Part (ii) (the product "implies" the
stuffle product of MZVs) is informal and omitted.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 10 (i) (`integers-2024-A6-thm-10`). -/
public theorem_wanted biBracket_mul_eq_sum_weightedQuasiShuffle (u v : List (ℕ × ℕ))
    (hu : ∀ p ∈ u, 1 ≤ p.1) (hv : ∀ p ∈ v, 1 ≤ p.1) :
    biBracket u * biBracket v =
      (weightedQuasiShuffle biBracketDiamond u v).sum fun w c => c • biBracket w

/-- The map `T : 𝔥⁰ → 𝔥¹` on a word: `𝟏 ↦ 𝟏` and `z_n v ↦ z_n v - z_{n-1} v`, as a formal
`ℚ`-linear combination of words (letters `z_k` are naturals `k`).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the OOZ quasi-shuffle product. -/
public noncomputable def oozT : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | n :: v => Finsupp.single (n :: v) 1 - Finsupp.single ((n - 1) :: v) 1

/-- `T(𝟏) = 𝟏`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the OOZ quasi-shuffle product. -/
public theorem oozT_nil : oozT [] = Finsupp.single [] 1 := rfl

/-- `T(z_2) = z_2 - z_1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the OOZ quasi-shuffle product. -/
public theorem oozT_singleton_two : oozT [2] = Finsupp.single [2] 1 - Finsupp.single [1] 1 := rfl

/-- The stuffle product `∗` (`z_m ⋄ z_n = z_{m+n}`) extended bilinearly to formal
`ℚ`-linear combinations of words.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the stuffle product `∗` on `𝔥¹`. -/
public noncomputable def stuffleComb (A B : List ℕ →₀ ℚ) : List ℕ →₀ ℚ :=
  A.sum fun a x => B.sum fun b y =>
    (x * y) • ((quasiShuffle (fun m n => [m + n]) a b).map fun w => Finsupp.single w (1 : ℚ)).sum

/-- `𝟏 ∗ B = B`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the stuffle product `∗` on `𝔥¹`. -/
public theorem stuffleComb_single_nil (b : List ℕ) :
    stuffleComb (Finsupp.single [] 1) (Finsupp.single b 1) = Finsupp.single b 1 := by
  simp [stuffleComb, quasiShuffle_nil_left]

/-- The OOZ quasi-shuffle product `ш_OOZ` (defined by `T(u ш_OOZ v) = T(u) ∗ T(v)`) is well defined
and `ζ_q^OOZ` respects it: for admissible words `u, v` (letters `≥ 1`, first letter `≥ 2`), there is
exactly one `ℚ`-combination `w` of admissible words with `T(w) = T(u) ∗ T(v)`, and every such `w`
has `ζ_q^OOZ(w) = ζ_q^OOZ(u) ζ_q^OOZ(v)` (`T` and `ζ_q^OOZ` extended `ℚ`-linearly). The record's
trailing remarks (references for the quasi-shuffle structure, the generating series) are
omitted.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 16 (after Castillo Medina, Ebrahimi-Fard and Manchon) (`integers-2024-A6-thm-16`). -/
public theorem_wanted oozQMZV_mul_eq_of_oozT_eq_stuffleComb (u v : List ℕ)
    (hu : ∀ k ∈ u, 1 ≤ k) (hu₁ : ∀ k₁ ∈ u.head?, 2 ≤ k₁)
    (hv : ∀ k ∈ v, 1 ≤ k) (hv₁ : ∀ k₁ ∈ v.head?, 2 ≤ k₁) :
    (∃! w : List ℕ →₀ ℚ, (∀ x ∈ w.support, (∀ k ∈ x, 1 ≤ k) ∧ ∀ k₁ ∈ x.head?, 2 ≤ k₁) ∧
        (w.sum fun x c => c • oozT x) = stuffleComb (oozT u) (oozT v)) ∧
      ∀ w : List ℕ →₀ ℚ, (∀ x ∈ w.support, (∀ k ∈ x, 1 ≤ k) ∧ ∀ k₁ ∈ x.head?, 2 ≤ k₁) →
        (w.sum fun x c => c • oozT x) = stuffleComb (oozT u) (oozT v) →
        (w.sum fun x c => c • oozQMZV x) = oozQMZV u * oozQMZV v

/-- Weighted chain sums: for a word of markers (`some k` a position weighted by `C(j, k)` in its
multiplicity `j`, `none` an unweighted position), a bound `M` and a target `R`,
`∑ ∏ C(jₜ, kₜ)` over strictly decreasing chains `M > a₁ > a₂ > ⋯ > 0` (one value per marker) and
multiplicities `jₜ ≥ 0` with `∑ aₜ jₜ = R`, the product over the `some` positions.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 1 (the sums over `m₁ > n₁ > ⋯ > m_r > ⋯ > 0` with multiplicities `j, i ≥ 0`). -/
public def bzChainSum : List (Option ℕ) → ℕ → ℕ → ℕ
  | [], _, R => if R = 0 then 1 else 0
  | o :: os, M, R => ∑ m ∈ Finset.Ioo 0 M, ∑ j ∈ Finset.range (R / m + 1),
      (match o with
        | some k => j.choose k
        | none => 1) * bzChainSum os m (R - m * j)

/-- The marker word of a list of blocks `(s, k)`: each block is a weighted position `some k`
followed by `s - 1` unweighted positions.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 1 (block `t` of the chain is `m_t > n > ⋯ > n` with `d_t - 1` entries `n`). -/
public def bzChainWord (b : List (ℕ × ℕ)) : List (Option ℕ) :=
  b.flatMap fun sk => some sk.2 :: List.replicate (sk.1 - 1) none

/-- For one block `(1, 1)`, the chain sum at `R = 2` is `∑_{m j = 2} j = 3`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 1 (case `r = 1`, `k₁ = d₁ = 1`, `N = 2`). -/
public theorem bzChainSum_bzChainWord_one_one :
    bzChainSum (bzChainWord [(1, 1)]) 3 2 = 3 := by
  decide

/-- Combinatorial form of Bradley–Zhao duality: for `r ≥ 1`, `k₁, …, kᵣ, d₁, …, dᵣ ≥ 1` and
`N ≥ 1`,
`∑ C(j₁, k₁) ⋯ C(jᵣ, kᵣ)` over chains `m₁ > n₁ > ⋯ > n_{d₁-1} > m₂ > ⋯ > mᵣ > ⋯ > n_{d₁+⋯+dᵣ-r} > 0`
(block `t` of length `dₜ` headed by `mₜ`) and multiplicities `j, i ≥ 0` with
`∑ mₜ jₜ + ∑ nₛ iₛ = N` equals the same sum with blocks of lengths `kᵣ, …, k₁` and weights
`C(j₁, dᵣ) ⋯ C(jᵣ, d₁)`. Blocks are pairs `(length, binomial index)`; values are taken below
`N + 1`, which loses nothing since `C(j₁, ·)` with a positive index forces `j₁ ≥ 1`, hence
`m₁ ≤ N`. The record's formula is garbled; it is read from arXiv:2111.00051, Theorem 4.18. The
paper's closing remark (equivalence with BZ duality) is not part of this statement.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 1 (`integers-2024-A6-thm-1`). -/
public theorem_wanted bzChainSum_dual (k d : List ℕ) (hlen : k.length = d.length)
    (hr : k ≠ []) (hk : ∀ x ∈ k, 1 ≤ x) (hd : ∀ x ∈ d, 1 ≤ x) (N : ℕ) (hN : 1 ≤ N) :
    bzChainSum (bzChainWord (d.zip k)) (N + 1) N =
      bzChainSum (bzChainWord (k.zip d).reverse) (N + 1) N

/-- The SZ dual index `k†`: the index read off `τ̃(p^{k₁} y ⋯ p^{kᵣ} y)`, where `τ̃` is the
anti-automorphism of words with `τ̃(p) = y`, `τ̃(y) = p` (reverse the word, swap the letters). For
`k = (k₁, {0}^{d₁-1}, …, kᵣ, {0}^{dᵣ-1})` it is `(dᵣ, {0}^{kᵣ-1}, …, d₁, {0}^{k₁-1})`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 5 (SZ duality, the map `τ̃` and the SZ dual index). -/
public def szDualIndex (k : List ℕ) : List ℕ :=
  szIndexOfWordAux 0 ((szWord k).reverse.map not)

/-- `(2)† = (1, 0)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 5 (SZ dual index). -/
public theorem szDualIndex_two : szDualIndex [2] = [1, 0] := by decide

/-- The BZ dual of an admissible index: `z_{k₁} ⋯ z_{kᵣ} = x^{k₁-1} y ⋯ x^{kᵣ-1} y` is mapped by the
anti-automorphism `τ` (`τ(x) = y`, `τ(y) = x`) of `𝔥⁰`, and the index is read off again. In terms of
SZ words (`p = x`) this is `szDualIndex` of `(k₁ - 1, …, kᵣ - 1)`, shifted back by one.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 7 (BZ duality, the map `τ`). -/
public def bzDualIndex (k : List ℕ) : List ℕ :=
  (szDualIndex (k.map (· - 1))).map (· + 1)

/-- `τ(z₃) = z₂ z₁`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 7 (BZ duality). -/
public theorem bzDualIndex_three : bzDualIndex [3] = [2, 1] := by decide

/-- The non-leading letters of the map `U`: `z_{k₂} ⋯ z_{kᵣ} ↦
∑_{1 ≤ nⱼ ≤ kⱼ} ∏ⱼ C(kⱼ - 1, nⱼ - 1) z_{n₂} ⋯ z_{nᵣ}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i) (after Ebrahimi-Fard, Manchon and Singer, the map `U`). -/
public noncomputable def oozToBZTail : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | b :: k => ∑ n ∈ Finset.Icc 1 b,
      (((b - 1).choose (n - 1) : ℕ) : ℚ) • (oozToBZTail k).mapDomain (List.cons n)

/-- The map `U : 𝔥⁰ → 𝔥⁰` on a word: `𝟏 ↦ 𝟏` and
`z_{k₁} ⋯ z_{kᵣ} ↦ ∑ C(k₁ - 2, n₁ - 2) C(k₂ - 1, n₂ - 1) ⋯ C(kᵣ - 1, nᵣ - 1) z_{n₁} ⋯ z_{nᵣ}` over
`2 ≤ n₁ ≤ k₁` and `1 ≤ nⱼ ≤ kⱼ` (`j ≥ 2`), as a formal `ℚ`-combination of words.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i) (after Ebrahimi-Fard, Manchon and Singer, the map `U`). -/
public noncomputable def oozToBZ : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | a :: k => ∑ n ∈ Finset.Icc 2 a,
      (((a - 2).choose (n - 2) : ℕ) : ℚ) • (oozToBZTail k).mapDomain (List.cons n)

/-- `U(𝟏) = 𝟏`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i). -/
public theorem oozToBZ_nil : oozToBZ [] = Finsupp.single [] 1 := rfl

/-- `U(z₂) = z₂`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i). -/
public theorem oozToBZ_two : oozToBZ [2] = Finsupp.single [2] 1 := by
  simp [oozToBZ, oozToBZTail]

/-- The non-leading letters of the map `V`: `p^{k₂} y ⋯ p^{kᵣ} y ↦
∑_{0 ≤ nⱼ ≤ kⱼ} ∏ⱼ C(kⱼ, nⱼ) p^{n₂} y ⋯ p^{nᵣ} y` (words as their indices).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii) (after Ebrahimi-Fard, Manchon and Singer, the map `V`). -/
public noncomputable def oozToSZTail : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | b :: k => ∑ n ∈ Finset.range (b + 1),
      ((b.choose n : ℕ) : ℚ) • (oozToSZTail k).mapDomain (List.cons n)

/-- The map `V : 𝔎¹ → 𝔎¹` on a word (words `p^{k₁} y ⋯ p^{kᵣ} y` as their indices): `𝟏 ↦ 𝟏` and
`p^{k₁} y ⋯ p^{kᵣ} y ↦ ∑ C(k₁ - 1, n₁ - 1) C(k₂, n₂) ⋯ C(kᵣ, nᵣ) p^{n₁} y ⋯ p^{nᵣ} y` over
`1 ≤ n₁ ≤ k₁` and `0 ≤ nⱼ ≤ kⱼ` (`j ≥ 2`).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii) (after Ebrahimi-Fard, Manchon and Singer, the map `V`). -/
public noncomputable def oozToSZ : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | a :: k => ∑ n ∈ Finset.Icc 1 a,
      (((a - 1).choose (n - 1) : ℕ) : ℚ) • (oozToSZTail k).mapDomain (List.cons n)

/-- `V(p y) = p y`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii). -/
public theorem oozToSZ_one : oozToSZ [1] = Finsupp.single [1] 1 := by
  simp [oozToSZ, oozToSZTail]

/-- Restricted OOZ-qMZVs in the BZ model: for an admissible index `k` (`kᵢ ≥ 1`, `k₁ ≥ 2`),
`ζ_q^OBZ(k) = ζ_q^BZ(U(k))`, with `ζ_q^BZ` extended `ℚ`-linearly.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i) (`integers-2024-A6-prop-12`). -/
public theorem_wanted oozQMZV_eq_sum_bzQMZV_oozToBZ (k : List ℕ) (hk : ∀ a ∈ k, 1 ≤ a)
    (hk₁ : ∀ a ∈ k.head?, 2 ≤ a) :
    oozQMZV k = (oozToBZ k).sum fun w c => c • bzQMZV w

/-- `U` is a linear isomorphism of `𝔥⁰`: its `ℚ`-linear extension maps the combinations of
admissible words bijectively onto themselves.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i) (`integers-2024-A6-prop-12`). -/
public theorem_wanted bijOn_linearCombination_oozToBZ :
    Set.BijOn (Finsupp.linearCombination ℚ oozToBZ)
      (Finsupp.supported ℚ ℚ {w : List ℕ | (∀ a ∈ w, 1 ≤ a) ∧ ∀ a ∈ w.head?, 2 ≤ a})
      (Finsupp.supported ℚ ℚ {w : List ℕ | (∀ a ∈ w, 1 ≤ a) ∧ ∀ a ∈ w.head?, 2 ≤ a})

/-- OOZ-qMZVs in the SZ model: for an SZ-admissible index `k` (empty or `k₁ ≥ 1`),
`ζ_q^OSZ(k) = ζ_q^SZ(V(k))`, with `ζ_q^SZ` extended `ℚ`-linearly.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii) (`integers-2024-A6-prop-12`). -/
public theorem_wanted oozQMZV_eq_sum_szQMZV_oozToSZ (k : List ℕ) (hk₁ : ∀ a ∈ k.head?, 1 ≤ a) :
    oozQMZV k = (oozToSZ k).sum fun w c => c • szQMZV w

/-- `V` is a linear isomorphism of `𝔎¹`: its `ℚ`-linear extension maps the combinations of
SZ-admissible words bijectively onto themselves.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii) (`integers-2024-A6-prop-12`). -/
public theorem_wanted bijOn_linearCombination_oozToSZ :
    Set.BijOn (Finsupp.linearCombination ℚ oozToSZ)
      (Finsupp.supported ℚ ℚ {w : List ℕ | ∀ a ∈ w.head?, 1 ≤ a})
      (Finsupp.supported ℚ ℚ {w : List ℕ | ∀ a ∈ w.head?, 1 ≤ a})

/-- Duality for restricted OOZ-qMZVs, `ζ_q^OBZ = ζ_q^OBZ ∘ U⁻¹ ∘ τ ∘ U` on `𝔥⁰`: for an admissible
index `w` and every combination `x` of admissible words with `U(x) = τ(U(w))`,
`ζ_q^OBZ(x) = ζ_q^OBZ(w)` (`U⁻¹` exists by `bijOn_linearCombination_oozToBZ`).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (i) (after Ebrahimi-Fard, Manchon and Singer) (`integers-2024-A6-thm-17`). -/
public theorem_wanted sum_oozQMZV_eq_of_oozToBZ_eq_bzDual (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    (hw₁ : ∀ a ∈ w.head?, 2 ≤ a) (x : List ℕ →₀ ℚ)
    (hx : x ∈ Finsupp.supported ℚ ℚ {v : List ℕ | (∀ a ∈ v, 1 ≤ a) ∧ ∀ a ∈ v.head?, 2 ≤ a})
    (hUx : Finsupp.linearCombination ℚ oozToBZ x = (oozToBZ w).mapDomain bzDualIndex) :
    (x.sum fun v c => c • oozQMZV v) = oozQMZV w

/-- Duality for OOZ-qMZVs, `ζ_q^OSZ = ζ_q^OSZ ∘ V⁻¹ ∘ τ̃ ∘ V` on `𝔎¹`: for an SZ-admissible index
`w` and every combination `x` of SZ-admissible words with `V(x) = τ̃(V(w))`,
`ζ_q^OSZ(x) = ζ_q^OSZ(w)` (`V⁻¹` exists by `bijOn_linearCombination_oozToSZ`).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (ii) (after Ebrahimi-Fard, Manchon and Singer) (`integers-2024-A6-thm-17`). -/
public theorem_wanted sum_oozQMZV_eq_of_oozToSZ_eq_szDual (w : List ℕ)
    (hw₁ : ∀ a ∈ w.head?, 1 ≤ a) (x : List ℕ →₀ ℚ)
    (hx : x ∈ Finsupp.supported ℚ ℚ {v : List ℕ | ∀ a ∈ v.head?, 1 ≤ a})
    (hVx : Finsupp.linearCombination ℚ oozToSZ x = (oozToSZ w).mapDomain szDualIndex) :
    (x.sum fun v c => c • oozQMZV v) = oozQMZV w

/-- Partial sums of SZ-star qMZVs: for an index `(k₁, …, kᵣ)` and a bound `M`,
`∑_{M ≥ m₁ ≥ ⋯ ≥ mᵣ > 0} ∏ⱼ q^{mⱼ kⱼ} / (1 - q^{mⱼ})^{kⱼ}`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (iii) (SZ-star qMZVs, defining sum truncated at `m₁ ≤ M`). -/
public noncomputable def szStarQMZVPartial : List ℕ → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | k :: ks, M => ∑ m ∈ Finset.Icc 1 M, (X ^ m * (1 - X ^ m)⁻¹) ^ k * szStarQMZVPartial ks m

/-- The SZ-star qMZV
`ζ_q^{SZ,⋆}(k₁, …, kᵣ) = ∑_{m₁ ≥ ⋯ ≥ mᵣ > 0} ∏ⱼ q^{mⱼ kⱼ} / (1 - q^{mⱼ})^{kⱼ}`, `ζ_q^{SZ,⋆}(∅) = 1`.
For `k₁ ≥ 1` the summands with `m₁ > N` have `q`-adic order `> N`, so the coefficient of `q^N` is
that of the partial sum with `m₁ ≤ N`; junk for `k₁ = 0`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (iii) (the map `ζ_q^{SZ,⋆}` of SZ-star qMZVs). -/
public noncomputable def szStarQMZV (k : List ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun N => coeff N (szStarQMZVPartial k N)

/-- `ζ_q^{SZ,⋆}(∅) = 1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (iii). -/
public theorem szStarQMZV_nil : szStarQMZV [] = 1 := by
  ext N
  simp [szStarQMZV, szStarQMZVPartial]

/-- The coefficient of `q` in `ζ_q^{SZ,⋆}(1) = ∑_{m > 0} q^m / (1 - q^m)` is `1`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (iii). -/
public theorem coeff_one_szStarQMZV_singleton_one : coeff 1 (szStarQMZV [1]) = 1 := by
  simp [szStarQMZV, szStarQMZVPartial, coeff_succ_X_mul, constantCoeff_inv]

/-- OOZ-qMZVs as SZ-star qMZVs, `ζ_q^OSZ = ζ_q^{SZ,⋆} ∘ τ̃` on `𝔎¹`: for an SZ-admissible index `k`
(empty or `k₁ ≥ 1`), `ζ_q^OOZ(k) = ζ_q^{SZ,⋆}(k†)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (iii) (after Ebrahimi-Fard, Manchon and Singer) (`integers-2024-A6-thm-17`). -/
public theorem_wanted oozQMZV_eq_szStarQMZV_szDualIndex (k : List ℕ)
    (hk₁ : ∀ a ∈ k.head?, 1 ≤ a) :
    oozQMZV k = szStarQMZV (szDualIndex k)

/-- The map `U_TBZ : 𝔥^TBZ → 𝔎¹` on a word (letters `none = 1̄`, `some k`): each `1̄` becomes the SZ
letter `1`, each `k` becomes `k` or `k - 1` (sum over both choices), as a formal `ℚ`-combination of
SZ indices.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (i) (the map `U_TBZ`). -/
public noncomputable def tbzToSZ : List (Option ℕ) → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | none :: w => (tbzToSZ w).mapDomain (List.cons 1)
  | some k :: w => (tbzToSZ w).mapDomain (List.cons k) + (tbzToSZ w).mapDomain (List.cons (k - 1))

/-- `U_TBZ(z_1̄) = p y`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (i). -/
public theorem tbzToSZ_bar : tbzToSZ [none] = Finsupp.single [1] 1 := by
  simp [tbzToSZ]

/-- The map `V_TBZ : 𝔎¹ → 𝔥^TBZ` on an SZ index: each letter `0` becomes `z_1 - z_1̄`, each letter
`k ≥ 1` becomes `∑_{1 ≤ j ≤ k} (-1)^{k-j} z_{j'}` with `j' = 1̄` for `j = 1` and `j' = j` otherwise,
multiplied out as a formal `ℚ`-combination of TBZ words.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (ii) (the map `V_TBZ`). -/
public noncomputable def szToTBZ : List ℕ → (List (Option ℕ) →₀ ℚ)
  | [] => Finsupp.single [] 1
  | 0 :: k => (szToTBZ k).mapDomain (List.cons (some 1)) - (szToTBZ k).mapDomain (List.cons none)
  | (a + 1) :: k => ∑ j ∈ Finset.Icc 1 (a + 1),
      ((-1 : ℚ) ^ (a + 1 - j)) •
        (szToTBZ k).mapDomain (List.cons (if j = 1 then none else some j))

/-- `V_TBZ(p y) = z_1̄`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (ii). -/
public theorem szToTBZ_one : szToTBZ [1] = Finsupp.single [none] 1 := by
  simp [szToTBZ]

/-- TBZ-qMZVs in the SZ model: for `d₁, …, dᵣ ≥ 0` and `k₁, …, k_{r-1} ≥ 1` with `k₁ ≥ 2` if
`d₁ = 0`, `ζ_q^TBZ({1̄}^{d₁}, k₁, …, k_{r-1}, {1̄}^{dᵣ}) =
∑_{δⱼ ∈ {0,1}} ζ_q^SZ({1}^{d₁}, k₁ - δ₁, …, {1}^{d_{r-1}}, k_{r-1} - δ_{r-1}, {1}^{dᵣ})`. Every TBZ
word with letters `kᵢ ≥ 1` and first letter `≠ 1` has this shape, so it is stated for such words.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (i) (`integers-2024-A6-prop-9`). -/
public theorem_wanted tbzQMZV_eq_sum_szQMZV_tbzToSZ (w : List (Option ℕ))
    (hw : ∀ j ∈ w, ∀ k ∈ j, 1 ≤ k) (hw₁ : w.head? ≠ some (some 1)) :
    tbzQMZV w = (tbzToSZ w).sum fun v c => c • szQMZV v

/-- SZ-qMZVs in the TBZ model: for an SZ-admissible index `k` (empty or `k₁ ≥ 1`),
`ζ_q^SZ(k) = ζ_q^TBZ(V_TBZ(k))`, i.e. the paper's signed sum
`∑ (-1)^{∑ kᵢ - jᵢ + |εᵢ|} ζ_q^TBZ(j₁', ε₁, …, jᵣ', εᵣ)`, with `ζ_q^TBZ` extended `ℚ`-linearly.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (ii) (`integers-2024-A6-prop-9`). -/
public theorem_wanted szQMZV_eq_sum_tbzQMZV_szToTBZ (k : List ℕ) (hk₁ : ∀ a ∈ k.head?, 1 ≤ a) :
    szQMZV k = (szToTBZ k).sum fun w c => c • tbzQMZV w

/-- TBZ duality, `ζ_q^TBZ = ζ_q^TBZ ∘ V_TBZ ∘ τ̃ ∘ U_TBZ` on `𝔥^TBZ`: for a TBZ word `w` (letters
`kᵢ ≥ 1`, first letter `≠ 1`), translating into the SZ model, applying `τ̃` (the SZ dual index) and
translating back gives a combination of TBZ-qMZVs equal to `ζ_q^TBZ(w)`.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 8 (after Takeyama) (`integers-2024-A6-prop-8`). -/
public theorem_wanted tbzQMZV_eq_sum_tbzQMZV_szToTBZ_szDual (w : List (Option ℕ))
    (hw : ∀ j ∈ w, ∀ k ∈ j, 1 ≤ k) (hw₁ : w.head? ≠ some (some 1)) :
    tbzQMZV w = ((tbzToSZ w).mapDomain szDualIndex).sum fun v c =>
      c • (szToTBZ v).sum fun u d => d • tbzQMZV u

end

end MetaMathlibExt
