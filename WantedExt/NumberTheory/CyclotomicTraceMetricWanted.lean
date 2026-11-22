/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.Analysis.Real.Sqrt

/-!
# A trace metric on the `p`-th cyclotomic field

Statements from Katerina Saettone, Alexandru Zaharescu and Zhuo Zhang, *On a Special
Metric in Cyclotomic Fields*, INTEGERS 25 (2025), Article A10 (arXiv:2410.22687).

For `K = ℚ(ω)` with `ω` a primitive `p`-th root of unity, `α ∈ K` is sent to the vector
`(Tr_{K/ℚ}(α ω^j))_{1 ≤ j ≤ p-1} ∈ ℚ^{p-1}`; `‖α‖` is its Euclidean length and
`d(α, β) = ‖α - β‖`. The field is any `K` with `IsCyclotomicExtension {p} ℚ K` (for
example `CyclotomicField p ℚ`), and `ω = IsCyclotomicExtension.zeta p ℚ K`.
The box `B(p, N)` consists of the points `a₁ ω + ⋯ + a_{p-1} ω^{p-1}` with integer
`aᵢ ∈ [-N, N]`; it is indexed by its coefficient vectors, which is faithful since
`ω, …, ω^{p-1}` is a `ℚ`-basis of `K`.

The paper fixes `p` an odd prime throughout; statements that also hold for `p = 2`
assume only that `p` is prime.
-/

namespace MetaMathlibExt

@[expose] public section

open IsCyclotomicExtension

variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

/-- The squared trace norm `‖α‖² = ∑_{j=1}^{p-1} Tr_{K/ℚ}(α ω^j)²` on `K = ℚ(ω)`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 1 (Definition 2.1 of arXiv:2410.22687). -/
noncomputable def cyclotomicTraceNormSq (p : ℕ) [NeZero p] [IsCyclotomicExtension {p} ℚ K]
    (α : K) : ℚ :=
  ∑ j ∈ Finset.Icc 1 (p - 1),
    Algebra.trace ℚ K (α * zeta p ℚ K ^ j) ^ 2

/-- The trace norm `‖α‖`, the Euclidean length of `(Tr_{K/ℚ}(α ω^j))_{1 ≤ j ≤ p-1}`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 1 (Definition 2.1 of arXiv:2410.22687). -/
noncomputable def cyclotomicTraceNorm (p : ℕ) [NeZero p] [IsCyclotomicExtension {p} ℚ K]
    (α : K) : ℝ :=
  √(cyclotomicTraceNormSq p α : ℝ)

/-- The trace metric `d(α, β) = ‖α - β‖` on `K = ℚ(ω)`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 2 (Definition 2.2 of arXiv:2410.22687). -/
noncomputable def cyclotomicTraceDist (p : ℕ) [NeZero p] [IsCyclotomicExtension {p} ℚ K]
    (α β : K) : ℝ :=
  cyclotomicTraceNorm p (α - β)

/-- The lattice point `a₁ ω + ⋯ + a_{p-1} ω^{p-1}` of `K` with integer coefficients
(indexed from `0`, so `a i` multiplies `ω^(i+1)`).

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 1 (the box `B(p, N)`). -/
noncomputable def cyclotomicLatticePoint (K : Type*) [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K]
    (a : Fin (p - 1) → ℤ) : K :=
  ∑ i, (a i : K) * zeta p ℚ K ^ (i.val + 1)

/-- The coefficient vectors of the box `B(p, N)`: all `a ∈ ℤ^{p-1}` with
`-N ≤ aᵢ ≤ N`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 1 (the box `B(p, N)`). -/
def cyclotomicBox (p N : ℕ) : Finset (Fin (p - 1) → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-- The `k`-th moment `M_k(p, N) = #B(p, N)⁻² ∑_{α, β ∈ B(p, N)} d(α, β)^k`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 6 (Definition 6.1 of arXiv:2410.22687). -/
noncomputable def cyclotomicDistMoment (p : ℕ) [NeZero p] (K : Type*) [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (N k : ℕ) : ℝ :=
  (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
      cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ^ k) /
    ((cyclotomicBox p N).card : ℝ) ^ 2

/-- `‖0‖² = 0`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 1. -/
@[simp] theorem cyclotomicTraceNormSq_zero : cyclotomicTraceNormSq p (0 : K) = 0 := by
  simp [cyclotomicTraceNormSq]

/-- `‖-α‖² = ‖α‖²`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 1. -/
@[simp] theorem cyclotomicTraceNormSq_neg (α : K) :
    cyclotomicTraceNormSq p (-α) = cyclotomicTraceNormSq p α := by
  simp [cyclotomicTraceNormSq, neg_mul, map_neg]

/-- `d(α, α) = 0`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 2. -/
@[simp] theorem cyclotomicTraceDist_self (α : K) :
    cyclotomicTraceDist p α α = 0 := by
  simp [cyclotomicTraceDist, cyclotomicTraceNorm]

/-- `d` is symmetric.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Definition 2. -/
theorem cyclotomicTraceDist_comm (α β : K) :
    cyclotomicTraceDist p α β = cyclotomicTraceDist p β α := by
  rw [cyclotomicTraceDist, cyclotomicTraceDist, ← neg_sub, cyclotomicTraceNorm,
    cyclotomicTraceNorm, cyclotomicTraceNormSq_neg]

/-- The zero coefficient vector gives the point `0`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 1 (the box `B(p, N)`). -/
@[simp] theorem cyclotomicLatticePoint_zero :
    cyclotomicLatticePoint K (0 : Fin (p - 1) → ℤ) = 0 := by
  simp [cyclotomicLatticePoint]

/-- The box `B(0)` of radius `0` is the single coefficient vector `0`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 1 (the box `B(p, N)`). -/
theorem cyclotomicBox_zero (p : ℕ) : cyclotomicBox p 0 = {0} := by
  ext a
  simp [cyclotomicBox, funext_iff]

/-- The coefficient vector `0` lies in every box.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 1 (the box `B(p, N)`). -/
theorem zero_mem_cyclotomicBox (p N : ℕ) : (0 : Fin (p - 1) → ℤ) ∈ cyclotomicBox p N := by
  simp [cyclotomicBox]

/-- The zeroth moment is `1`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Section 6 (Definition 6.1 of arXiv:2410.22687). -/
theorem cyclotomicDistMoment_zero (N : ℕ) : cyclotomicDistMoment p K N 0 = 1 := by
  have h : ((cyclotomicBox p N).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨0, zero_mem_cyclotomicBox p N⟩).ne'
  simp [cyclotomicDistMoment, sq, h]

/-- **Proposition 1.** The metric `d` is invariant under `Gal(K/ℚ)`:
`d(σ α, σ β) = d(α, β)`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Proposition 1 (`integers-2025-A10-prop-1`). -/
public theorem_wanted cyclotomicTraceDist_algEquiv (hp : p.Prime)
    (σ : K ≃ₐ[ℚ] K) (α β : K) :
    cyclotomicTraceDist p (σ α) (σ β) = cyclotomicTraceDist p α β

/-- **Theorem 2.** `‖·‖` is a norm on the `ℚ`-vector space `K`: it vanishes only at
`0`, satisfies the triangle inequality, and is absolutely homogeneous.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 2 (`integers-2025-A10-thm-2`). -/
public theorem_wanted cyclotomicTraceNorm_isNorm (hp : p.Prime) :
    (∀ α : K, cyclotomicTraceNorm p α = 0 ↔ α = 0) ∧
    (∀ α β : K,
      cyclotomicTraceNorm p (α + β) ≤ cyclotomicTraceNorm p α + cyclotomicTraceNorm p β) ∧
    ∀ (q : ℚ) (α : K), cyclotomicTraceNorm p (q • α) = |(q : ℝ)| * cyclotomicTraceNorm p α

/-- **Theorem 4** (a Krasner-type lemma). If `β ∈ K` satisfies
`d(α, β) < d(α, σ α) / 2` for every conjugate `σ α ≠ α` (`σ ∈ Gal(K/ℚ)`), then
`ℚ(α) ⊆ ℚ(β)`.

The record's "conjugates of `α` over `K`" is read as conjugates over `ℚ` (the Galois
conjugates `σ α`), as in the paper's proof.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 4 (`integers-2025-A10-thm-4`). -/
public theorem_wanted adjoin_le_adjoin_of_cyclotomicTraceDist_lt (hp : p.Prime)
    {α β : K}
    (h : ∀ σ : K ≃ₐ[ℚ] K, σ α ≠ α →
      cyclotomicTraceDist p α β < cyclotomicTraceDist p α (σ α) / 2) :
    IntermediateField.adjoin ℚ {α} ≤ IntermediateField.adjoin ℚ {β}

/-- **Corollary 1.** For `α, β ∈ K`, `ℚ(α + n β) = ℚ(α, β)` for all sufficiently
large `n`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Corollary 1 (`integers-2025-A10-cor-1`). -/
public theorem_wanted eventually_adjoin_add_nsmul_eq (hp : p.Prime) (α β : K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      IntermediateField.adjoin ℚ {α + (n : K) * β} =
        IntermediateField.adjoin ℚ {α, β}

/-- **Lemma 1.** For `α = a₁ ω + ⋯ + a_{p-1} ω^{p-1}` with rational `aᵢ`,
`‖α‖² = p² ‖α‖_E² - (p + 1) Tr_{K/ℚ}(α)²` where `‖α‖_E² = ∑ aᵢ²`; consequently
`‖α‖_E² ≤ ‖α‖²`.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 1 (`integers-2025-A10-lem-1`). -/
public theorem_wanted cyclotomicTraceNormSq_eq_and_ge (hp : p.Prime) (a : Fin (p - 1) → ℚ) :
    let α : K :=
      ∑ i, (a i : K) * zeta p ℚ K ^ (i.val + 1)
    cyclotomicTraceNormSq p α =
        (p : ℚ) ^ 2 * ∑ i, a i ^ 2 - (p + 1) * Algebra.trace ℚ K α ^ 2 ∧
      ∑ i, a i ^ 2 ≤ cyclotomicTraceNormSq p α

/-- **Lemma 2.** For an odd prime `p`, the diameter of `B(p, N)` is `2 N p √(p - 1)`:
every distance in the box is at most this, and it is attained by
`α = N ω - N ω² + ⋯ + N ω^{p-2} - N ω^{p-1}` and `β = -α`.

The record's `∑ N (-ω)^{i-1}` is read as the displayed expansion (coefficient of
`ω^i` equal to `(-1)^{i-1} N`).

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 2 (`integers-2025-A10-lem-2`). -/
public theorem_wanted cyclotomicBox_diam (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) :
    (∀ a ∈ cyclotomicBox p N, ∀ b ∈ cyclotomicBox p N,
      cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ≤
        2 * N * p * √(p - 1 : ℝ)) ∧
    cyclotomicTraceDist p (cyclotomicLatticePoint K fun i : Fin (p - 1) => (N : ℤ) * (-1) ^ i.val)
        (cyclotomicLatticePoint K fun i : Fin (p - 1) => -((N : ℤ) * (-1) ^ i.val)) =
      2 * N * p * √(p - 1 : ℝ)

/-- **Lemma 3.** The power sums `S_r(N) = ∑_{-N ≤ a ≤ N} a^r` satisfy `S_r(N) = 0`
for odd `r`, `S_2(N) = N(N+1)(2N+1)/3` and `S_4(N) = N(N+1)(2N+1)(3N²+3N-1)/15`.

The paper takes `N ≥ 1`; `N = 0` is included.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 3 (`integers-2025-A10-lem-3`). -/
public theorem_wanted symmetric_power_sums (N : ℕ) :
    (∀ r : ℕ, Odd r → ∑ a ∈ Finset.Icc (-(N : ℤ)) N, a ^ r = 0) ∧
    ∑ a ∈ Finset.Icc (-(N : ℤ)) N, (a : ℚ) ^ 2 = N * (N + 1) * (2 * N + 1) / 3 ∧
    ∑ a ∈ Finset.Icc (-(N : ℤ)) N, (a : ℚ) ^ 4 =
      N * (N + 1) * (2 * N + 1) * (3 * N ^ 2 + 3 * N - 1) / 15

/-- **Lemma 4.** The second moment is
`M_2(p, N) = (2/3)(p³ - 2p² + 1) N (N + 1)`.

Only the exact formula is stated; the paper's `= (2/3) p³ N² + O(p² N² + p³ N)` follows
from it.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 4 (`integers-2025-A10-lem-4`). -/
public theorem_wanted cyclotomicDistMoment_two (hp : p.Prime) (N : ℕ) :
    cyclotomicDistMoment p K N 2 = 2 / 3 * ((p : ℝ) ^ 3 - 2 * p ^ 2 + 1) * N * (N + 1)

/-- **Lemma 5.** Over the box `a, b ∈ [-N, N]^(p-1)`,
`∑_{i,j} ∑_{a,b} (aᵢ - bᵢ)² (aⱼ - bⱼ)² =
(2N+1)^(2(p-1)) · (2/45) N (N+1) (p-1) (10N²p + 4N² + 10Np + 4N - 3)`.

Corrected reading: the printed right side omits the factor `(2N+1)^(2(p-1))` (for `p = 3`,
`N = 1` the sum is `936` while the printed right side is `104/9`). The paper's own proof
carries the factors `(2N+1)^(2p-4)` and `(2N+1)^(2p-6)` in its pieces (10) and (11), and
combining them gives the stated value; the printed formula is the sum divided by
`#B(p, N)² = (2N+1)^(2(p-1))`. The paper takes `p` an odd prime; only `p` prime is assumed.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 5 (`integers-2025-A10-lem-5`). -/
public theorem_wanted sum_sq_sub_mul_sq_sub_box (p : ℕ) (hp : p.Prime) (N : ℕ) :
    ∑ i : Fin (p - 1), ∑ j : Fin (p - 1),
      ∑ a ∈ Fintype.piFinset (fun _ : Fin (p - 1) => Finset.Icc (-(N : ℤ)) N),
        ∑ b ∈ Fintype.piFinset (fun _ : Fin (p - 1) => Finset.Icc (-(N : ℤ)) N),
          (((a i - b i) ^ 2 * (a j - b j) ^ 2 : ℤ) : ℚ) =
      (2 * N + 1) ^ (2 * (p - 1)) * (2 / 45 * N * (N + 1) * ((p : ℚ) - 1) *
        (10 * N ^ 2 * p + 4 * N ^ 2 + 10 * N * p + 4 * N - 3))

/-- **Lemma 6.** The fourth moment is
`M_4(p, N) = (2/45) N (N+1) (p-1) ((2N² + 2N)(5p⁵ - 8p⁴ + p³ + 8p² - 21p - 18) - 3(p² - p - 1)²)`.

Only the exact formula is stated; the paper's `= (4/9) p⁶ N⁴ + O(p⁵ N⁴ + p⁶ N³)` follows
from it.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 6 (`integers-2025-A10-lem-6`). -/
public theorem_wanted cyclotomicDistMoment_four (hp : p.Prime) (N : ℕ) :
    cyclotomicDistMoment p K N 4 = 2 / 45 * N * (N + 1) * (p - 1) *
      ((2 * (N : ℝ) ^ 2 + 2 * N) * (5 * p ^ 5 - 8 * p ^ 4 + p ^ 3 + 8 * p ^ 2 - 21 * p - 18) -
        3 * ((p : ℝ) ^ 2 - p - 1) ^ 2)

/-- **Lemma 7.** The variance-type sum
`R(p, N) = #B(p, N)⁻² ∑_{α, β} (d(α, β)² - (2/3) p³ N²)²` satisfies
`R(p, N) ≪ p⁵ N⁴ + p⁶ N³`, with an absolute implied constant.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Lemma 7 (`integers-2025-A10-lem-7`). -/
public theorem_wanted exists_cyclotomicDist_variance_le :
    ∃ C : ℝ, ∀ p N : ℕ, ∀ (_ : NeZero p) (K : Type) [Field K] [CharZero K]
      [IsCyclotomicExtension {p} ℚ K], p.Prime → 1 ≤ N →
      (∑ a ∈ cyclotomicBox p N, ∑ b ∈ cyclotomicBox p N,
          (cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) ^ 2 -
            2 / 3 * (p : ℝ) ^ 3 * N ^ 2) ^ 2) / ((cyclotomicBox p N).card : ℝ) ^ 2 ≤
        C * ((p : ℝ) ^ 5 * N ^ 4 + (p : ℝ) ^ 6 * N ^ 3)

/-- **Theorem 1** (main theorem). For every `ε > 0` there is `A(ε)` such that for
`N, p > A(ε)` (`p` prime), fewer than `ε · #B(p, N)²` pairs `(α, β) ∈ B(p, N)²` have
`|d_{p,N}(α, β) - 1/√6| > ε`, where `d_{p,N} = d / (2 N p √(p - 1))` is the distance
normalized by the diameter.

The paper's "absolute and effectively computable" is not formalized.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 1 (`integers-2025-A10-thm-1`). -/
public theorem_wanted cyclotomicBox_almost_equidistant :
    ∀ ε > (0 : ℝ), ∃ A : ℕ, ∀ p N : ℕ, ∀ (_ : NeZero p) (K : Type) [Field K] [CharZero K]
      [IsCyclotomicExtension {p} ℚ K], p.Prime → A < p → A < N →
      ((((cyclotomicBox p N ×ˢ cyclotomicBox p N).filter fun ab =>
          ε < |cyclotomicTraceDist p (cyclotomicLatticePoint K ab.1)
              (cyclotomicLatticePoint K ab.2) /
            (2 * N * p * √(p - 1 : ℝ)) - 1 / √6|).card : ℝ)) <
        ε * ((cyclotomicBox p N).card : ℝ) ^ 2

/-- **Theorem 5** (quantitative form). There is an absolute `C` such that for every
`ε > 0`, prime `p` and `N ≥ 1`, the proportion of pairs `(α, β) ∈ B(p, N)²` with
`|d(α, β) / (2 N p^{3/2}) - 1/√6| > ε` is at most `C ε⁻² (1/p + 1/N)`.

The paper fixes `p` odd; `p = 2` is included. Effective computability of `C` is not
formalized.

Source: Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*,
INTEGERS 25 (2025), Article A10, Theorem 5 (`integers-2025-A10-thm-5`). -/
public theorem_wanted exists_cyclotomicBox_deviation_le :
    ∃ C : ℝ, ∀ ε > (0 : ℝ), ∀ p N : ℕ, ∀ (_ : NeZero p) (K : Type) [Field K] [CharZero K]
      [IsCyclotomicExtension {p} ℚ K], p.Prime → 1 ≤ N →
      ((((cyclotomicBox p N ×ˢ cyclotomicBox p N).filter fun ab =>
          ε < |cyclotomicTraceDist p (cyclotomicLatticePoint K ab.1)
              (cyclotomicLatticePoint K ab.2) /
            (2 * N * (p * √(p : ℝ))) - 1 / √6|).card : ℝ)) /
        ((cyclotomicBox p N).card : ℝ) ^ 2 ≤ C / ε ^ 2 * (1 / p + 1 / N)

end

end MetaMathlibExt
