/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# Unit-weighted zero-sum constants of `ℤ_n`: wishlist

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38 (arXiv:2203.02665).

Definitions follow the paper. For an `R`-module `M` and `A ⊆ R`, a subsequence of
`(x_1, …, x_k)` indexed by a nonempty `I` is `A`-weighted zero-sum if `∑_{i ∈ I} a_i x_i = 0`
for some `a_i ∈ A`. `D_A(M)` (resp. `C_A(M)`) is the least positive `k` such that every length-`k`
sequence has such a subsequence (resp. one of consecutive terms); both are stated with
`IsLeast` on the sets below (local notation), so no new definition is introduced. `D(M)`,
`C(M)` are the case `A = {1}`. `U(n)` is the unit group of `ℤ_n`, `Ω` is
`ArithmeticFunction.cardFactors`, `v_2` is `padicValNat 2`, and `f_{n,m}` is the natural map.
Vectors of `ℤ_2^m` are functions `Fin m → ZMod 2`. Several statements of the Drive extraction
print `2a` where the paper (arXiv:2203.02665v2) has `2^a`; the exponent is restored (see the
audit table).
-/

open scoped ArithmeticFunction.Omega

namespace MetaMathlibExt

@[expose] public section

set_option quotPrecheck false in
/-- The set of positive `k` such that every length-`k` sequence in `M` has an `A`-weighted
zero-sum subsequence; `D_A(M)` is its least element. -/
local notation "davenportSet" R:max M:max A:max => {k : ℕ | 0 < k ∧ ∀ x : Fin k → M,
  ∃ I : Finset (Fin k), I.Nonempty ∧
    ∃ a : Fin k → R, (∀ i ∈ I, a i ∈ A) ∧ ∑ i ∈ I, a i • x i = 0}

set_option quotPrecheck false in
/-- The set of positive `k` such that every length-`k` sequence in `M` has an `A`-weighted
zero-sum subsequence of consecutive terms; `C_A(M)` is its least element. -/
local notation "consecutiveSet" R:max M:max A:max => {k : ℕ | 0 < k ∧ ∀ x : Fin k → M,
  ∃ s t : Fin k, s ≤ t ∧
    ∃ a : Fin k → R, (∀ i ∈ Finset.Icc s t, a i ∈ A) ∧ ∑ i ∈ Finset.Icc s t, a i • x i = 0}

set_option quotPrecheck false in
/-- `x : Fin k → ZMod n` is a `U(n)`-weighted zero-sum sequence (all terms used). -/
local notation "IsUnitWeightedZeroSum" n:max x:max =>
  ∃ a : _ → ZMod n, (∀ i, IsUnit (a i)) ∧ ∑ i, a i * x i = 0

set_option quotPrecheck false in
/-- `x : Fin k → ZMod n` has a `U(n)`-weighted zero-sum subsequence of length `L`. -/
local notation "HasUnitWeightedZeroSumOfCard" n:max L:max x:max =>
  ∃ I : Finset _, I.card = L ∧
    ∃ a : _ → ZMod n, (∀ i ∈ I, IsUnit (a i)) ∧ ∑ i ∈ I, a i * x i = 0

set_option quotPrecheck false in
/-- The `ℕ`-indexed sequence `x` of length `L` in `ℤ_n` has no `U(n)`-weighted zero-sum
subsequence of consecutive terms. -/
local notation "NoConsecutiveUnitWeightedZeroSum" n:max L:max x:max =>
  ¬ ∃ s t : ℕ, s ≤ t ∧ t < L ∧ ∃ a : ℕ → ZMod n,
    (∀ i ∈ Finset.Icc s t, IsUnit (a i)) ∧ ∑ i ∈ Finset.Icc s t, a i * x i = 0

/-- Theorem 2.1: for an `R`-module `M`, an `R'`-module `N`, `A ⊆ R` and `B ⊆ R'`, with `M × N`
a module over `R × R'` (componentwise action),
`D_{A × B}(M × N) ≥ D_A(M) + D_B(N) - 1`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.1 (`integers-2024-A38-thm-2-1`). -/
public theorem_wanted davenport_prod_ring_ge {R R' M N : Type*} [Ring R] [Ring R']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N] (A : Set R) (B : Set R')
    {dA dB d : ℕ} (hA : IsLeast (davenportSet R M A) dA)
    (hB : IsLeast (davenportSet R' N B) dB)
    (h : IsLeast {k : ℕ | 0 < k ∧ ∀ x : Fin k → M × N, ∃ I : Finset (Fin k), I.Nonempty ∧
      ∃ a : Fin k → R × R', (∀ i ∈ I, a i ∈ A ×ˢ B) ∧
        ∑ i ∈ I, ((a i).1 • (x i).1, (a i).2 • (x i).2) = 0} d) :
    dA + dB - 1 ≤ d

/-- Theorem 2.2: for `R`-modules `M`, `N` and `A ⊆ R`,
`D_A(M × N) ≥ D_A(M) + D_A(N) - 1`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.2 (`integers-2024-A38-thm-2-2`). -/
public theorem_wanted davenport_prod_ge {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (A : Set R) {dM dN d : ℕ}
    (hM : IsLeast (davenportSet R M A) dM) (hN : IsLeast (davenportSet R N A) dN)
    (h : IsLeast (davenportSet R (M × N) A) d) :
    dM + dN - 1 ≤ d

/-- Theorem 2.3: for an `R`-module `M`, an `R'`-module `N`, `A ⊆ R` and `B ⊆ R'`, with `M × N`
a module over `R × R'` (componentwise action), `C_{A × B}(M × N) ≥ C_A(M) C_B(N)`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.3 (`integers-2024-A38-thm-2-3`). -/
public theorem_wanted consecutive_prod_ring_ge {R R' M N : Type*} [Ring R] [Ring R']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N] (A : Set R) (B : Set R')
    {cA cB c : ℕ} (hA : IsLeast (consecutiveSet R M A) cA)
    (hB : IsLeast (consecutiveSet R' N B) cB)
    (h : IsLeast {k : ℕ | 0 < k ∧ ∀ x : Fin k → M × N, ∃ s t : Fin k, s ≤ t ∧
      ∃ a : Fin k → R × R', (∀ i ∈ Finset.Icc s t, a i ∈ A ×ˢ B) ∧
        ∑ i ∈ Finset.Icc s t, ((a i).1 • (x i).1, (a i).2 • (x i).2) = 0} c) :
    cA * cB ≤ c

/-- Theorem 2.4: for `R`-modules `M`, `N` and `A ⊆ R`, `C_A(M × N) ≥ C_A(M) C_A(N)`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.4 (`integers-2024-A38-thm-2-4`). -/
public theorem_wanted consecutive_prod_ge {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (A : Set R) {cM cN c : ℕ}
    (hM : IsLeast (consecutiveSet R M A) cM) (hN : IsLeast (consecutiveSet R N A) cN)
    (h : IsLeast (consecutiveSet R (M × N) A) c) :
    cM * cN ≤ c

/-- Theorem 3.1: for a finite abelian group `G`, `C(G) = |G|`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 3.1 (`integers-2024-A38-thm-3-1`). -/
public theorem_wanted consecutive_constant_eq_card (G : Type*) [AddCommGroup G] [Fintype G] :
    IsLeast (consecutiveSet ℤ G ({1} : Set ℤ)) (Fintype.card G)

/-- Lemma 3.2: if `2^a ≤ m` and `v_1, …, v_a ∈ ℤ_2^m`, some nonzero `w ∈ ℤ_2^m` whose ones
occupy consecutive positions `s, …, t` satisfies `w · v_i = 0` for all `i`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 3.2 (`integers-2024-A38-lem-3-2`). -/
public theorem_wanted exists_consecutive_orthogonal {a m : ℕ} (hm : 2 ^ a ≤ m)
    (v : Fin a → Fin m → ZMod 2) :
    ∃ s t : Fin m, s ≤ t ∧ ∀ i, ∑ j ∈ Finset.Icc s t, v i j = 0

/-- Lemma 3.3: if `2^a ≤ m` and `X_1, …, X_a` are sets, some nonempty block of consecutive
integers `Y = [s, t] ⊆ [1, m]` meets every `X_i` in an even number of elements.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 3.3 (`integers-2024-A38-lem-3-3`). -/
public theorem_wanted exists_consecutive_even_inter {a m : ℕ} (hm : 2 ^ a ≤ m)
    (X : Fin a → Finset ℕ) :
    ∃ s t : ℕ, 1 ≤ s ∧ s ≤ t ∧ t ≤ m ∧ ∀ i, Even (Finset.Icc s t ∩ X i).card

/-- Lemma 3.5 (Griffiths): for `n = p^r` with `p` prime, if for each `i ∈ [1, r]` the set
`X_i = {j : x_j ≢ 0 (mod p^i)}` has even size, then `(x_1, …, x_k)` is a `U(n)`-weighted
zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 3.5 (`integers-2024-A38-lem-3-5`). -/
public theorem_wanted unitWeightedZeroSum_of_even_nonDivisible {p r k : ℕ} (hp : p.Prime)
    (x : Fin k → ZMod (p ^ r))
    (h : ∀ i ∈ Finset.Icc 1 r, Even (Finset.univ.filter fun j => ¬ p ^ i ∣ (x j).val).card) :
    IsUnitWeightedZeroSum (p ^ r) x

/-- Theorem 4.1: `D(ℤ_2^a) = a + 1`. Stated for every `a` (the paper: `a` positive).

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 4.1 (`integers-2024-A38-thm-4-1`). -/
public theorem_wanted davenport_zmod_two_pow (a : ℕ) :
    IsLeast (davenportSet (ZMod 2) (Fin a → ZMod 2) ({1} : Set (ZMod 2))) (a + 1)

/-- Lemma 4.2: if `a + 1 ≤ m` and `v_1, …, v_a ∈ ℤ_2^m`, some nonzero `w ∈ ℤ_2^m` satisfies
`w · v_i = 0` for all `i`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 4.2 (`integers-2024-A38-lem-4-2`). -/
public theorem_wanted exists_ne_zero_orthogonal {a m : ℕ} (hm : a + 1 ≤ m)
    (v : Fin a → Fin m → ZMod 2) :
    ∃ w : Fin m → ZMod 2, w ≠ 0 ∧ ∀ i, ∑ j, w j * v i j = 0

/-- Lemma 4.3: if `a + 1 ≤ m` and `X_1, …, X_a` are sets, some nonempty `Y ⊆ [1, m]` meets every
`X_i` in an even number of elements.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 4.3 (`integers-2024-A38-lem-4-3`). -/
public theorem_wanted exists_nonempty_even_inter {a m : ℕ} (hm : a + 1 ≤ m)
    (X : Fin a → Finset ℕ) :
    ∃ Y : Finset ℕ, Y.Nonempty ∧ Y ⊆ Finset.Icc 1 m ∧ ∀ i, Even (Y ∩ X i).card

/-- Theorem 5.2: if `m` is even with `2^a ≤ m`, every sequence of length `m + a` in `ℤ_2^a` has a
zero-sum subsequence of length `m`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 5.2 (`integers-2024-A38-thm-5-2`). -/
public theorem_wanted exists_zeroSum_card_zmod_two_pow {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m)
    (x : Fin (m + a) → Fin a → ZMod 2) :
    ∃ I : Finset (Fin (m + a)), I.card = m ∧ ∑ i ∈ I, x i = 0

/-- Lemma 5.3: if `m` is even with `2^a ≤ m` and `v_1, …, v_a ∈ ℤ_2^{m+a}`, some `w ∈ ℤ_2^{m+a}`
with exactly `m` coordinates equal to one satisfies `w · v_i = 0` for all `i`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 5.3 (`integers-2024-A38-lem-5-3`). -/
public theorem_wanted exists_weight_orthogonal {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m)
    (v : Fin a → Fin (m + a) → ZMod 2) :
    ∃ w : Fin (m + a) → ZMod 2, (Finset.univ.filter fun j => w j = 1).card = m ∧
      ∀ i, ∑ j, w j * v i j = 0

/-- Lemma 5.4: if `m` is even with `2^a ≤ m` and `X_1, …, X_a` are sets, some `Y ⊆ [1, m + a]`
with `|Y| = m` meets every `X_i` in an even number of elements.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 5.4 (`integers-2024-A38-lem-5-4`). -/
public theorem_wanted exists_card_even_inter {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m)
    (X : Fin a → Finset ℕ) :
    ∃ Y : Finset ℕ, Y ⊆ Finset.Icc 1 (m + a) ∧ Y.card = m ∧ ∀ i, Even (Y ∩ X i).card

/-- Theorem 5.5: for `n ≥ 1` and even `m ≥ 2^{Ω(n)}`, every sequence of length `m + Ω(n)` in
`ℤ_n` has a `U(n)`-weighted zero-sum subsequence of length `m`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 5.5 (`integers-2024-A38-thm-5-5`). -/
public theorem_wanted exists_unitWeightedZeroSum_card {n m : ℕ} (hn : 0 < n) (hme : Even m)
    (hm : 2 ^ Ω n ≤ m) (x : Fin (m + Ω n) → ZMod n) :
    HasUnitWeightedZeroSumOfCard n m x

/-- Corollary 5.7: if `m` is even with `2^a ≤ m`, every `m`-dimensional subspace of `ℤ_2^{m+a}`
contains a vector with exactly `m` coordinates equal to one.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Corollary 5.7 (`integers-2024-A38-cor-5-7`). -/
public theorem_wanted exists_weight_mem_subspace {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m)
    (W : Submodule (ZMod 2) (Fin (m + a) → ZMod 2)) (hW : Module.finrank (ZMod 2) W = m) :
    ∃ v ∈ W, (Finset.univ.filter fun j => v j = 1).card = m

/-- Corollary 5.9: if `m` is even with `2^a ≤ m` and `n = m + a`, the largest dimension
`l(n, m)` of a subspace of `ℤ_2^n` with no vector of weight `m` is `m - 1`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Corollary 5.9 (`integers-2024-A38-cor-5-9`). -/
public theorem_wanted max_finrank_avoiding_weight {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m) :
    IsGreatest {d : ℕ | ∃ W : Submodule (ZMod 2) (Fin (m + a) → ZMod 2),
      Module.finrank (ZMod 2) W = d ∧
        ∀ v ∈ W, (Finset.univ.filter fun j => v j = 1).card ≠ m} (m - 1)

/-- Theorem 6.3: for even `n`, `E_{U(n)}(n) = n + Ω(n)`, where `E_A(n)` is the least positive `k`
such that every length-`k` sequence in `ℤ_n` has an `A`-weighted zero-sum subsequence of
length `n`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 6.3 (`integers-2024-A38-thm-6-3`). -/
public theorem_wanted gao_unit_constant_of_even {n : ℕ} (hn : 0 < n) (he : Even n) :
    IsLeast {k : ℕ | 0 < k ∧ ∀ x : Fin k → ZMod n, HasUnitWeightedZeroSumOfCard n n x}
      (n + Ω n)

/-- Theorem 6.4: for `r ≥ 1` and `n = 2^r`, a sequence of length `n + r - 1` in `ℤ_n` that is
`U(n)`-equivalent (`c y_{σ(i)} = a_i x_i` with units `c`, `a_i` and a permutation `σ`) to a
sequence `y` in which `2^i` occurs exactly once for each `i ∈ [0, r - 2]`, `2^{r-1}` occurs an
odd number of times and all other terms are zero is `E`-extremal for `U(n)`: it has no
`U(n)`-weighted zero-sum subsequence of length `n` (its length is `E_{U(n)}(n) - 1` by
Theorem 6.3).

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 6.4 (`integers-2024-A38-thm-6-4`). -/
public theorem_wanted eExtremal_of_unitEquiv_profile {r : ℕ} (hr : 1 ≤ r)
    (x y : Fin (2 ^ r + r - 1) → ZMod (2 ^ r))
    (hy : (∀ i < r - 1, (Finset.univ.filter fun j => y j = 2 ^ i).card = 1) ∧
      Odd (Finset.univ.filter fun j => y j = 2 ^ (r - 1)).card ∧
      ∀ j, y j = 0 ∨ ∃ i < r, y j = 2 ^ i)
    (hxy : ∃ c : ZMod (2 ^ r), IsUnit c ∧ ∃ σ : Equiv.Perm (Fin (2 ^ r + r - 1)),
      ∃ b : Fin (2 ^ r + r - 1) → ZMod (2 ^ r), (∀ i, IsUnit (b i)) ∧
        ∀ i, c * y (σ i) = b i * x i) :
    ¬ HasUnitWeightedZeroSumOfCard (2 ^ r) (2 ^ r) x

/-- Theorem 6.6: for `r ≥ 1` and `n = 2^r`, an `E`-extremal sequence for `U(n)` (length
`n + r - 1 = E_{U(n)}(n) - 1` and no `U(n)`-weighted zero-sum subsequence of length `n`) is
`U(n)`-equivalent to a sequence in which `2^i` occurs exactly once for each `i ∈ [0, r - 2]`,
`2^{r-1}` occurs an odd number of times and all other terms are zero.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 6.6 (`integers-2024-A38-thm-6-6`). -/
public theorem_wanted unitEquiv_profile_of_eExtremal {r : ℕ} (hr : 1 ≤ r)
    (x : Fin (2 ^ r + r - 1) → ZMod (2 ^ r))
    (hx : ¬ HasUnitWeightedZeroSumOfCard (2 ^ r) (2 ^ r) x) :
    ∃ y : Fin (2 ^ r + r - 1) → ZMod (2 ^ r),
      ((∀ i < r - 1, (Finset.univ.filter fun j => y j = 2 ^ i).card = 1) ∧
        Odd (Finset.univ.filter fun j => y j = 2 ^ (r - 1)).card ∧
        ∀ j, y j = 0 ∨ ∃ i < r, y j = 2 ^ i) ∧
      ∃ c : ZMod (2 ^ r), IsUnit c ∧ ∃ σ : Equiv.Perm (Fin (2 ^ r + r - 1)),
        ∃ b : Fin (2 ^ r + r - 1) → ZMod (2 ^ r), (∀ i, IsUnit (b i)) ∧
          ∀ i, c * y (σ i) = b i * x i

/-- Lemma 6.5 (Luca): a sequence in `ℤ_{2^r}` with a nonzero even number of unit terms is a
`U(2^r)`-weighted zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 6.5 (`integers-2024-A38-lem-6-5`). -/
public theorem_wanted unitWeightedZeroSum_of_even_units {r k : ℕ} (x : Fin k → ZMod (2 ^ r))
    (h0 : (Finset.univ.filter fun j => IsUnit (x j)).card ≠ 0)
    (he : Even (Finset.univ.filter fun j => IsUnit (x j)).card) :
    IsUnitWeightedZeroSum (2 ^ r) x

/-- Lemma 6.7: let `n = p n'` with `p` prime and `S = (p z_1, …, p z_k)` a sequence in `ℤ_n`
whose terms are divisible by `p`. If the image `S'` of `S / p = (z_1, …, z_k)` under
`f_{n,n'}` is a `U(n')`-weighted zero-sum sequence, then `S` is a `U(n)`-weighted zero-sum
sequence. (`S / p` is defined modulo `n'`, so any choice of the `z_i` gives the same `S'`.)

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 6.7 (`integers-2024-A38-lem-6-7`). -/
public theorem_wanted unitWeightedZeroSum_of_div_prime {p n' k : ℕ} (hp : p.Prime)
    (z : Fin k → ZMod (p * n'))
    (h : IsUnitWeightedZeroSum n' (fun i => ZMod.castHom (dvd_mul_left n' p) (ZMod n') (z i))) :
    IsUnitWeightedZeroSum (p * n') (fun i => (p : ZMod (p * n')) * z i)

/-- Theorem 6.8: let `n = 2^{s+1}`, `n' = n / 2`, and `S = (x_1, …, x_{n-1})` in `ℤ_n` (here
`ℕ`-indexed from `0`, so the middle term `x_{n'}` is `x (n' - 1)`). Then `S` is `C`-extremal for
`U(n)` (length `n - 1 = C_{U(n)}(n) - 1` and no `U(n)`-weighted zero-sum subsequence of
consecutive terms) if and only if every term except the middle one is even, the middle term is
odd, and the images in `ℤ_{n'}` of `S_1 / 2 = (x_1, …, x_{n'-1}) / 2` and
`S_2 / 2 = (x_{n'+1}, …, x_{n-1}) / 2` are `C`-extremal for `U(n')`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 6.8 (`integers-2024-A38-thm-6-8`). -/
public theorem_wanted cExtremal_iff_halves (s : ℕ) (x : ℕ → ZMod (2 ^ (s + 1))) :
    (NoConsecutiveUnitWeightedZeroSum (2 ^ (s + 1)) (2 ^ (s + 1) - 1) x) ↔
      (∀ j < 2 ^ (s + 1) - 1, j ≠ 2 ^ s - 1 → Even (x j).val) ∧ Odd (x (2 ^ s - 1)).val ∧
        (NoConsecutiveUnitWeightedZeroSum (2 ^ s) (2 ^ s - 1)
          (fun j => (((x j).val / 2 : ℕ) : ZMod (2 ^ s)))) ∧
        (NoConsecutiveUnitWeightedZeroSum (2 ^ s) (2 ^ s - 1)
          (fun j => (((x (2 ^ s + j)).val / 2 : ℕ) : ZMod (2 ^ s))))

/-- Theorem 7.1: for `n ≥ 2`, `r ∈ [1, n - 1]` and `A = [1, r] ⊆ ℤ_n`, `C_A(n) = ⌈n / r⌉`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 7.1 (`integers-2024-A38-thm-7-1`). -/
public theorem_wanted consecutive_interval_weights {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n - 1) :
    IsLeast (consecutiveSet (ZMod n) (ZMod n) ((fun j : ℕ => (j : ZMod n)) '' Set.Icc 1 r))
      ⌈(n : ℚ) / r⌉₊

/-- Theorem 7.2: for even `n` with `v_2(n) = r`, `m = n / 2^r`, `B` the odd elements of `ℤ_n`
and `{m} ⊆ A ⊆ B`, `C_A(n) = 2^r`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 7.2 (`integers-2024-A38-thm-7-2`). -/
public theorem_wanted consecutive_odd_weights {n : ℕ} (hn : 0 < n) (he : Even n)
    (A : Set (ZMod n)) (hmA : ((n / 2 ^ padicValNat 2 n : ℕ) : ZMod n) ∈ A)
    (hAB : A ⊆ {x : ZMod n | Odd x.val}) :
    IsLeast (consecutiveSet (ZMod n) (ZMod n) A) (2 ^ padicValNat 2 n)

/-- Theorem 7.5: for an odd prime `k` and a prime `p` with `p ≡ 1 (mod k)` and
`p ≢ 1 (mod k²)`, `D_{U(p)^k}(p) ≤ k`: every sequence of length `k` in `ℤ_p` has a
`U(p)^k`-weighted zero-sum subsequence (`U(p)^k = {u^k : u ∈ U(p)}`).

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 7.5 (`integers-2024-A38-thm-7-5`). -/
public theorem_wanted davenport_unit_pow_le {k p : ℕ} (hk : k.Prime) (hk2 : k ≠ 2)
    (hp : p.Prime) (hpk : p % k = 1) (hpk2 : p % k ^ 2 ≠ 1) :
    k ∈ davenportSet (ZMod p) (ZMod p) {x : ZMod p | ∃ u : ZMod p, IsUnit u ∧ x = u ^ k}

/-- Lemma 7.6: for a field `F`, a subgroup `A` of `F^*` and nonzero `x, y ∈ F`, the sequence
`(x, y)` has no `A`-weighted zero-sum subsequence if and only if `x` and `-y` lie in different
cosets of `A` in `F^*`. (A zero term is itself a zero-sum subsequence, so the cosets are taken
for nonzero `x, y`.)

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 7.6 (`integers-2024-A38-lem-7-6`). -/
public theorem_wanted pair_no_weightedZeroSum_iff {F : Type*} [Field F] (A : Subgroup Fˣ)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    (¬ ∃ I : Finset (Fin 2), I.Nonempty ∧ ∃ a : Fin 2 → F,
      (∀ i ∈ I, a i ∈ ((↑) : Fˣ → F) '' A) ∧ ∑ i ∈ I, a i * ![x, y] i = 0) ↔
      (QuotientGroup.mk (Units.mk0 x hx) : Fˣ ⧸ A) ≠
        QuotientGroup.mk (Units.mk0 (-y) (neg_ne_zero.mpr hy))

/-- Corollary 7.7: for a field `F` and a proper subgroup `A` of `F^*`, `D_A(F) ≥ 3`: some
sequence of length `2` in `F` has no `A`-weighted zero-sum subsequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Corollary 7.7 (`integers-2024-A38-cor-7-7`). -/
public theorem_wanted davenport_proper_subgroup_ge_three {F : Type*} [Field F]
    (A : Subgroup Fˣ) (hA : A ≠ ⊤) :
    2 ∉ davenportSet F F (((↑) : Fˣ → F) '' A)

/-- Corollary 7.8: for `k ≥ 2` and a prime `p ≡ 1 (mod k)`, `D_{U(p)^k}(p) ≥ 3`: some sequence of
length `2` in `ℤ_p` has no `U(p)^k`-weighted zero-sum subsequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Corollary 7.8 (`integers-2024-A38-cor-7-8`). -/
public theorem_wanted davenport_unit_pow_ge_three {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hpk : p % k = 1) :
    2 ∉ davenportSet (ZMod p) (ZMod p) {x : ZMod p | ∃ u : ZMod p, IsUnit u ∧ x = u ^ k}

end

end MetaMathlibExt
