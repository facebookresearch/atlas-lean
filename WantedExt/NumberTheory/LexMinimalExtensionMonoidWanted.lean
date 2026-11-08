/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.GroupTheory.Finiteness
public import WantedExt.NumberTheory.BinomidIndexWanted

namespace MetaMathlibExt

@[expose] public section

/-! Statements from Caalim and Tanaka, *Generalized Binomial Coefficients and
the Monoid of Lexicographically Minimal Extensions*, INTEGERS 26 (2026),
Article A113 (preprint arXiv:2505.20018, whose text supplies the definitions).

Conventions follow `WantedExt.NumberTheory.BinomidIndexWanted`: an infinite
index is `η : ℕ → ℕ` read from `0`, so the paper's entry `e_i` (`i ≥ 1`) is
`η (i - 1)` and the paper's partial sum `S_i = e_1 + ⋯ + e_i` is
`∑ l ∈ Finset.range i, η l`. The lex-minimal extension `η̃` of a finite binomid
index of length `m` is an `η` with `IsLexMinimalExtensionOf η m`; the paper's
set `L_k(I_k)` of lex-minimal extensions of length-`k` binomid indices is
`{η | IsLexMinimalExtensionOf η k}`. -/

/-- `A_1 = e_1`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 2. -/
public theorem binomidAverage_one (η : ℕ → ℕ) : binomidAverage η 1 = η 0 := by
  simp [binomidAverage]

/-- The indices `1 ≤ i ≤ m` with `A_i = A_max`, where
`A_max = max {A_i | 1 ≤ i ≤ m}`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 3 (the set `{i ≤ m | A_max = A_i}`). -/
public noncomputable def maxAverageIndices (η : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  open scoped Classical in
  (Finset.Icc 1 m).filter fun i =>
    ∀ j ∈ Finset.Icc 1 m, binomidAverage η j ≤ binomidAverage η i

/-- For `m = 1` the only index is `1`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 3. -/
public theorem maxAverageIndices_one (η : ℕ → ℕ) : maxAverageIndices η 1 = {1} := by
  simp [maxAverageIndices]

/-- `B` is a basis of `M`: `M` is the span `⟨B⟩` of `B`, and no element of `B`
is a nonnegative integer combination `∑ m_i β_i` of distinct elements `β_i` of
`B` in which its own coefficient is `0`. The family `β` is injective: the
paper's wording allows repeated entries, under which `β = (b, b)` and
`b = 0 • b + 1 • b` would rule out every nonempty `B`; its uniqueness proof
uses distinct entries.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 4 (definition of a basis). -/
public def IsAddMonoidBasis {α : Type*} [AddCommMonoid α] (M B : Set α) : Prop :=
  (AddSubmonoid.closure B : Set α) = M ∧
    ∀ (n : ℕ) (β : Fin n → α), Function.Injective β → (∀ i, β i ∈ B) →
      ∀ (c : Fin n → ℕ) (j : Fin n), β j = ∑ i, c i • β i → 1 ≤ c j

/-- A basis never contains `0`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 4. -/
public theorem IsAddMonoidBasis.zero_notMem {α : Type*} [AddCommMonoid α] {M B : Set α}
    (h : IsAddMonoidBasis M B) : (0 : α) ∉ B := by
  intro h0
  have := h.2 1 (fun _ => 0) (fun a b _ => Subsingleton.elim a b) (fun _ => h0)
    (fun _ => 0) 0 (by simp)
  simp at this

/-- The empty set is a basis of the trivial monoid `{0}`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 4. -/
public theorem isAddMonoidBasis_empty {α : Type*} [AddCommMonoid α] :
    IsAddMonoidBasis ({0} : Set α) ∅ :=
  ⟨by simp, fun _ _ _ hβ _ j _ => absurd (hβ j) (Set.notMem_empty _)⟩

/-- `η` is a nonzero atomic binomid index (an element of the paper's set
`Atom`): a nonzero binomid index that is not the sum of two nonzero binomid
indices.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 4 (definition of atomic). -/
public def IsAtomicBinomidIndex (η : ℕ → ℕ) : Prop :=
  IsBinomidIndex η ∧ η ≠ 0 ∧
    ∀ η₁ η₂ : ℕ → ℕ, IsBinomidIndex η₁ → IsBinomidIndex η₂ → η = η₁ + η₂ →
      η₁ = 0 ∨ η₂ = 0

/-- The constant sequence `1^∞ = (E_1)^∞` is atomic.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Section 4 (example of `(E_m)^∞` with `m = 1`). -/
public theorem isAtomicBinomidIndex_one : IsAtomicBinomidIndex fun _ => 1 := by
  have key : ∀ γ : ℕ → ℕ, IsBinomidIndex γ → ∀ i, γ 0 ≤ γ i := fun γ hγ i => by
    simpa using hγ 1 (i + 1) (by omega)
  refine ⟨isBinomidIndex_const 1, fun h => by simpa using congrFun h 0, ?_⟩
  intro η₁ η₂ h₁ h₂ h
  have hs : ∀ i, η₁ i + η₂ i = 1 := fun i => by simpa [eq_comm] using congrFun h i
  rcases Nat.eq_zero_or_pos (η₁ 0) with h0 | h0
  · left
    funext i
    have := key η₂ h₂ i
    have := hs 0
    have := hs i
    show η₁ i = 0
    omega
  · right
    funext i
    have := key η₁ h₁ i
    have := hs 0
    have := hs i
    show η₂ i = 0
    omega

/-- Proposition 1, part 2: if the first `k` entries (`k ≥ 1`) form a finite
binomid index (`S_i + S_j ≤ S_{i+j}` for `i, j ≥ 1`, `i + j ≤ k`), then `η` is
the lex-minimal extension of its first `k` entries if and only if
`Δ_η(r) = min {S_r - S_i - S_j | i + j = r, i, j ≥ 1} = 0` for every `r > k`,
written as `S_i + S_j ≤ S_r` for all such splits with equality for one of
them. Part 1 (`η` is binomid iff `S_i + S_j ≤ S_{i+j}`) is the first conjunct
of `isBinomidIndex_iff_partialSum`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Proposition 1 (`integers-2026-A113-prop-1`). -/
public theorem_wanted isLexMinimalExtensionOf_iff_forall_lt {η : ℕ → ℕ} {k : ℕ}
    (hk : 1 ≤ k)
    (hpre : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i + j ≤ k →
      ∑ l ∈ Finset.range i, η l + ∑ l ∈ Finset.range j, η l
        ≤ ∑ l ∈ Finset.range (i + j), η l) :
    IsLexMinimalExtensionOf η k ↔ ∀ r : ℕ, k < r →
      (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i + j = r →
        ∑ l ∈ Finset.range i, η l + ∑ l ∈ Finset.range j, η l
          ≤ ∑ l ∈ Finset.range r, η l) ∧
      ∃ i j : ℕ, 1 ≤ i ∧ 1 ≤ j ∧ i + j = r ∧
        ∑ l ∈ Finset.range i, η l + ∑ l ∈ Finset.range j, η l
          = ∑ l ∈ Finset.range r, η l

/-- Proposition 2: if `η` is the lex-minimal extension of a finite binomid
index of length `m ≥ 1`, then for every `c ≥ 1` there is a solution
`(n_i)_{i ≤ m}` of the unbounded knapsack problem `UKP[(S_i); (i); c]`
(maximize `∑ n_i S_i` subject to `∑ n_i i ≤ c`) with `S_c = ∑ n_i S_i` and
`c = ∑ n_i i`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Proposition 2 (`integers-2026-A113-prop-2`). -/
public theorem_wanted IsLexMinimalExtensionOf.exists_knapsack {η : ℕ → ℕ} {m : ℕ}
    (hη : IsLexMinimalExtensionOf η m) (hm : 1 ≤ m) {c : ℕ} (hc : 1 ≤ c) :
    ∃ n : ℕ → ℕ, ∑ i ∈ Finset.Icc 1 m, n i * i = c ∧
      ∑ l ∈ Finset.range c, η l
        = ∑ i ∈ Finset.Icc 1 m, n i * ∑ l ∈ Finset.range i, η l ∧
      ∀ n' : ℕ → ℕ, ∑ i ∈ Finset.Icc 1 m, n' i * i ≤ c →
        ∑ i ∈ Finset.Icc 1 m, n' i * ∑ l ∈ Finset.range i, η l
          ≤ ∑ i ∈ Finset.Icc 1 m, n i * ∑ l ∈ Finset.range i, η l

/-- Lemma 1: for the lex-minimal extension of a finite binomid index of length
`m`, `A_max = max {A_i | 1 ≤ i ≤ m}` is the maximum of all averages: `A_i ≤ A_j`
for every `i ≥ 1` and every maximizing index `j ≤ m`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Lemma 1 (`integers-2026-A113-lem-1`). -/
public theorem_wanted IsLexMinimalExtensionOf.binomidAverage_le {η : ℕ → ℕ} {m : ℕ}
    (hη : IsLexMinimalExtensionOf η m) {i : ℕ} (hi : 1 ≤ i) {j : ℕ}
    (hj : j ∈ maxAverageIndices η m) :
    binomidAverage η i ≤ binomidAverage η j

/-- Lemma 2: `GCD {i ≤ m | A_i = A_max} = GCD {i ∈ ℕ | A_i = A_max}`, stated as:
the left gcd divides every `i ≥ 1` with `A_i = A_max` (the other divisibility
is immediate).

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Lemma 2 (`integers-2026-A113-lem-2`). -/
public theorem_wanted IsLexMinimalExtensionOf.gcd_maxAverageIndices_dvd {η : ℕ → ℕ}
    {m : ℕ} (hη : IsLexMinimalExtensionOf η m) {i : ℕ} (hi : 1 ≤ i)
    (hmax : ∃ j ∈ maxAverageIndices η m, binomidAverage η i = binomidAverage η j) :
    (maxAverageIndices η m).gcd id ∣ i

/-- Lemma 3: the minimal period of the lex-minimal extension `η̃` of a finite
binomid index of length `m ≥ 1` (the least `p ≥ 1` with `η (i + p) = η i` for
all large `i`) is divisible by `GCD {i ≤ m | A_i = A_max}`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Lemma 3 (`integers-2026-A113-lem-3`). -/
public theorem_wanted IsLexMinimalExtensionOf.gcd_maxAverageIndices_dvd_minimalPeriod
    {η : ℕ → ℕ} {m : ℕ} (hη : IsLexMinimalExtensionOf η m) (hm : 1 ≤ m) {p : ℕ}
    (hp : IsLeast {q : ℕ | 0 < q ∧ ∃ N, ∀ i, N ≤ i → η (i + q) = η i} p) :
    (maxAverageIndices η m).gcd id ∣ p

/-- Theorem 1: the minimal period of the lex-minimal extension `η̃` of a finite
binomid index of length `m ≥ 1` is `GCD {i ≤ m | A_i = A_max}`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Theorem 1 (`integers-2026-A113-thm-1`). -/
public theorem_wanted IsLexMinimalExtensionOf.isLeast_period_gcd_maxAverageIndices
    {η : ℕ → ℕ} {m : ℕ} (hη : IsLexMinimalExtensionOf η m) (hm : 1 ≤ m) :
    IsLeast {q : ℕ | 0 < q ∧ ∃ N, ∀ i, N ≤ i → η (i + q) = η i}
      ((maxAverageIndices η m).gcd id)

/-- Theorem 2: if `k ≤ m` attains `A_k = A_max`, then `k m (m + 1) / 2` is a
preperiod of `η̃`: the tail `(e_i)_{i > k m (m + 1) / 2}`, i.e. `η j` for
`j ≥ k m (m + 1) / 2`, is periodic.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Theorem 2 (`integers-2026-A113-thm-2`). -/
public theorem_wanted IsLexMinimalExtensionOf.exists_period_from_preperiod_bound
    {η : ℕ → ℕ} {m : ℕ} (hη : IsLexMinimalExtensionOf η m) {k : ℕ}
    (hk : k ∈ maxAverageIndices η m) :
    ∃ p, 0 < p ∧ ∀ j, k * (m * (m + 1) / 2) ≤ j → η (j + p) = η j

/-- Proposition 3: if the lex-minimal extension of the first `k` entries of
`η₁ + η₂` decomposes with `η₁`, `η₂` binomid indices, then each `ηᵢ` is the
lex-minimal extension of its own first `k` entries. Since every lex-minimal
extension is one of its first `k` entries for some `k`, this includes the first
claim (`η₁`, `η₂` are lex-minimal extensions).

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Proposition 3 (`integers-2026-A113-prop-3`). -/
public theorem_wanted IsLexMinimalExtensionOf.of_add {η₁ η₂ : ℕ → ℕ} {k : ℕ}
    (h : IsLexMinimalExtensionOf (η₁ + η₂) k) (h₁ : IsBinomidIndex η₁)
    (h₂ : IsBinomidIndex η₂) :
    IsLexMinimalExtensionOf η₁ k ∧ IsLexMinimalExtensionOf η₂ k

/-- Proposition 4: let `M` be a submonoid of `ℕ^ι` and `A` its set of nonzero
atomic elements (nonzero, and not a sum of two nonzero elements of `M`). If
every element of `M` is a finite sum of elements of `A`, then `A` is the unique
basis of `M`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Proposition 4 (`integers-2026-A113-prop-4`). -/
public theorem_wanted isAddMonoidBasis_iff_eq_atoms {ι : Type*} (M : AddSubmonoid (ι → ℕ))
    (hM : ∀ x ∈ M, x ∈ AddSubmonoid.closure
      {a | a ∈ M ∧ a ≠ 0 ∧ ∀ y ∈ M, ∀ z ∈ M, a = y + z → y = 0 ∨ z = 0})
    (B : Set (ι → ℕ)) :
    IsAddMonoidBasis (M : Set (ι → ℕ)) B ↔
      B = {a | a ∈ M ∧ a ≠ 0 ∧ ∀ y ∈ M, ∀ z ∈ M, a = y + z → y = 0 ∨ z = 0}

/-- Proposition 5, first part: `Atom ∩ L` is the unique basis of the monoid `L`
of lex-minimal extensions.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Proposition 5 (`integers-2026-A113-prop-5`). -/
public theorem_wanted isAddMonoidBasis_lexMinimalExtensions_iff (B : Set (ℕ → ℕ)) :
    IsAddMonoidBasis {η | IsLexMinimalExtension η} B ↔
      B = {η | IsAtomicBinomidIndex η ∧ IsLexMinimalExtension η}

/-- Proposition 5, second part: `Atom ∩ L_k(I_k)` is the unique basis of the
span `⟨L_k(I_k)⟩`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Proposition 5 (`integers-2026-A113-prop-5`). -/
public theorem_wanted isAddMonoidBasis_closure_lexMinimalExtensionsOf_iff (k : ℕ)
    (B : Set (ℕ → ℕ)) :
    IsAddMonoidBasis
        (AddSubmonoid.closure {η : ℕ → ℕ | IsLexMinimalExtensionOf η k} : Set (ℕ → ℕ)) B ↔
      B = {η | IsAtomicBinomidIndex η ∧ IsLexMinimalExtensionOf η k}

/-- Lemma 4: if `η` is the lex-minimal extension of its first `k ≥ 1` entries,
then for every bound `l` there is a map `π` with `1 ≤ π i < i` and
`S_i - S_{π(i)} - S_{i - π(i)} = 0` for all `k < i ≤ l`. The paper takes the
specific bound `l = l(k)` from its proof of the preceding lemma; the statement
here holds for every `l`.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Lemma 4 (`integers-2026-A113-lem-4`). -/
public theorem_wanted IsLexMinimalExtensionOf.exists_path {η : ℕ → ℕ} {k : ℕ}
    (hη : IsLexMinimalExtensionOf η k) (hk : 1 ≤ k) (l : ℕ) :
    ∃ π : ℕ → ℕ, ∀ i, k < i → i ≤ l → 1 ≤ π i ∧ π i < i ∧
      ∑ t ∈ Finset.range i, η t
        = ∑ t ∈ Finset.range (π i), η t + ∑ t ∈ Finset.range (i - π i), η t

/-- Lemma 5: the span `⟨L_k(I_k)⟩` is a finitely generated monoid, and its
basis `Atom ∩ L_k(I_k)` is finite.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Lemma 5 (`integers-2026-A113-lem-5`). -/
public theorem_wanted fg_closure_lexMinimalExtensionsOf (k : ℕ) :
    (AddSubmonoid.closure {η : ℕ → ℕ | IsLexMinimalExtensionOf η k}).FG ∧
      {η | IsAtomicBinomidIndex η ∧ IsLexMinimalExtensionOf η k}.Finite

/-- Lemma 6: the span `⟨L_k(I_k)⟩` is a finitely presented commutative monoid:
it is the image of a surjective homomorphism from the free commutative monoid
`ℕ^n` whose kernel congruence is generated by finitely many relations.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Lemma 6 (`integers-2026-A113-lem-6`). -/
public theorem_wanted exists_finitePresentation_closure_lexMinimalExtensionsOf (k : ℕ) :
    ∃ (n : ℕ) (f : (Fin n → ℕ) →+
        AddSubmonoid.closure {η : ℕ → ℕ | IsLexMinimalExtensionOf η k}),
      Function.Surjective f ∧ ∃ R : Set ((Fin n → ℕ) × (Fin n → ℕ)), R.Finite ∧
        addConGen (fun x y => (x, y) ∈ R) = AddCon.ker f

/-- Theorem 3: `L` is the inductive limit (directed union) of the increasing
system of submonoids `⟨L_k(I_k)⟩` (finitely presented by
`exists_finitePresentation_closure_lexMinimalExtensionsOf`), and
`(Atom ∩ L_k(I_k))_k` is an increasing system of generators of that system.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Theorem 3 (`integers-2026-A113-thm-3`). -/
public theorem_wanted iUnion_closure_lexMinimalExtensionsOf :
    Monotone (fun k => AddSubmonoid.closure {η : ℕ → ℕ | IsLexMinimalExtensionOf η k}) ∧
    (⋃ k, (AddSubmonoid.closure {η : ℕ → ℕ | IsLexMinimalExtensionOf η k} :
        Set (ℕ → ℕ))) = {η | IsLexMinimalExtension η} ∧
    Monotone (fun k => {η : ℕ → ℕ | IsAtomicBinomidIndex η ∧ IsLexMinimalExtensionOf η k}) ∧
    ∀ k, AddSubmonoid.closure {η : ℕ → ℕ | IsAtomicBinomidIndex η ∧ IsLexMinimalExtensionOf η k}
      = AddSubmonoid.closure {η : ℕ → ℕ | IsLexMinimalExtensionOf η k}

end

end MetaMathlibExt
