/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Hindman
public import Mathlib.Data.PNat.Basic

/-!
# From Schur's theorem to the pairwise sum theorem

Statements from Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum
Theorem*, INTEGERS 25 (2025), Article A105.

A finite coloring is a map `c : S → Fin r`; a set `F` is monochromatic when `c` is constant on
`F` with some value `k : Fin r`. `FS(A)` is the set of sums of nonempty finite subsets of `A`.
Ultrafilters on `ℕ+` carry Mathlib's sum `Ultrafilter.add` (`A ∈ U + V` iff
`{n | {m | n + m ∈ A} ∈ V} ∈ U`) and the Stone–Čech topology. The tensor product of ultrafilters
on `ℕ` is `X ∈ U ⊗ V ↔ {n | {m | (n, m) ∈ X} ∈ V} ∈ U`.
-/

open Filter

namespace MetaMathlibExt

@[expose] public section

/-- (Hindman's finite sums theorem) For every finite coloring of `ℕ` there is an infinite set
`A` whose set of finite sums `FS(A)` (sums of nonempty finite subsets of `A`) is monochromatic.
(Mathlib's `Hindman.exists_FS_of_finite_cover` gives the form with a sequence that may repeat
terms.)

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Theorem 1.1 (`integers-2025-A105-thm-1-1`). -/
public theorem_wanted exists_infinite_finiteSums_monochromatic {r : ℕ} (c : ℕ → Fin r) :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ k : Fin r, ∀ F : Finset ℕ, F.Nonempty → (F : Set ℕ) ⊆ A →
      c (∑ a ∈ F, a) = k

/-- (Pairwise sum theorem) For every finite coloring of `ℕ` there is an infinite set `A` such
that `A ∪ {a + a' | a, a' ∈ A, a ≠ a'}` is monochromatic.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Theorem 1.2 (`integers-2025-A105-thm-1-2`). -/
public theorem_wanted exists_infinite_pairwiseSums_monochromatic {r : ℕ} (c : ℕ → Fin r) :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ k : Fin r, (∀ a ∈ A, c a = k) ∧
      ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → c (a + a') = k

/-- For every finite coloring of `ℕ` there are infinite disjoint sets `A`, `B` such that
`A ∪ B ∪ (A + B)` is monochromatic.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Theorem 2.2 (`integers-2025-A105-thm-2-2`). -/
public theorem_wanted exists_disjoint_infinite_union_add_monochromatic {r : ℕ} (c : ℕ → Fin r) :
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ Disjoint A B ∧ ∃ k : Fin r,
      (∀ a ∈ A, c a = k) ∧ (∀ b ∈ B, c b = k) ∧ ∀ a ∈ A, ∀ b ∈ B, c (a + b) = k

/-- For `X ⊆ ℕ × ℕ` the following are equivalent: (1) there are disjoint strictly increasing
sequences `(a_n)`, `(b_n)` with `(a_i, b_j) ∈ X` for `i ≤ j` and `(b_j, a_i) ∈ X` for `j < i`;
(2) there are non-principal ultrafilters `V₁`, `V₂` on `ℕ` with `X ∈ (V₁ ⊗ V₂) ∩ (V₂ ⊗ V₁)`.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Lemma 2.1 (`integers-2025-A105-lem-2-1`). -/
public theorem_wanted exists_interleaved_sequences_iff_mem_tensor (X : Set (ℕ × ℕ)) :
    (∃ a b : ℕ → ℕ, StrictMono a ∧ StrictMono b ∧ Disjoint (Set.range a) (Set.range b) ∧
        (∀ i j, i ≤ j → (a i, b j) ∈ X) ∧ (∀ i j, j < i → (b j, a i) ∈ X)) ↔
      ∃ V₁ V₂ : Ultrafilter ℕ, (V₁ : Filter ℕ) ≤ cofinite ∧ (V₂ : Filter ℕ) ≤ cofinite ∧
        {n | {m | (n, m) ∈ X} ∈ V₂} ∈ V₁ ∧ {n | {m | (n, m) ∈ X} ∈ V₁} ∈ V₂

/-- A family `𝓕` of subsets of `S` is weakly partition regular (every finite coloring of `S`
has a monochromatic member of `𝓕`) if and only if some ultrafilter `U` on `S` is a PR-witness of
`𝓕`: every `A ∈ U` contains some member of `𝓕`.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.1 (`integers-2025-A105-prop-3-1`), quoting
Hindman and Strauss, Theorem 5.7. -/
public theorem_wanted weaklyPartitionRegular_iff_exists_ultrafilter {S : Type*}
    (𝓕 : Set (Set S)) :
    (∀ (r : ℕ) (c : S → Fin r), ∃ F ∈ 𝓕, ∃ k : Fin r, ∀ x ∈ F, c x = k) ↔
      ∃ U : Ultrafilter S, ∀ A ∈ U, ∃ F ∈ 𝓕, F ⊆ A

/-- An ultrafilter `U` on `ℕ+` is a PR-witness of the Hindman family
`{FS(X) | X ⊆ ℕ+ infinite}` (every `A ∈ U` contains `FS(X)` for some infinite `X`) if and only if
`U` lies in the closure of the set of idempotents `{V ∈ βℕ+ | V + V = V}`.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.3 (`integers-2025-A105-prop-3-3`), quoting
Hindman and Strauss, Lemma 5.19. -/
public theorem_wanted finiteSums_witness_iff_mem_closure_idempotents (U : Ultrafilter ℕ+) :
    letI : Add (Ultrafilter ℕ+) := Ultrafilter.add
    (∀ A ∈ U, ∃ X : Set ℕ+, X.Infinite ∧
        ∀ F : Finset ℕ+, F.Nonempty → (F : Set ℕ+) ⊆ X →
          ∃ y ∈ A, (y : ℕ) = ∑ x ∈ F, (x : ℕ)) ↔
      U ∈ closure {V : Ultrafilter ℕ+ | V + V = V}

/-- (Ramsey's witnesses are the closure of tensor squares) An ultrafilter `W` on `ℕ × ℕ` is a
Ramsey's witness (Definition 3.4: every `X ∈ W` contains `[H]^2 = {(h, h') ∈ H × H | h < h'}` for
some infinite `H ⊆ ℕ`) if and only if `W` lies in the closure, in `β(ℕ × ℕ)`, of the tensor
squares `U ⊗ U` of non-principal ultrafilters `U` on `ℕ`. The tensor square is
`U.bind fun n => U.map (Prod.mk n)`, whose members are the `X` with
`{n | {m | (n, m) ∈ X} ∈ U} ∈ U`.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.5 (`integers-2025-A105-prop-3-5`). -/
public theorem_wanted ramseyWitness_iff_mem_closure_tensor_squares (W : Ultrafilter (ℕ × ℕ)) :
    (∀ X ∈ W, ∃ H : Set ℕ, H.Infinite ∧ ∀ h ∈ H, ∀ h' ∈ H, h < h' → (h, h') ∈ X) ↔
      W ∈ closure {V : Ultrafilter (ℕ × ℕ) | ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ cofinite ∧
        V = U.bind fun n => U.map (Prod.mk n)}

/-- (PR-witnesses of the pairwise sum family) An ultrafilter `U` on `ℕ` is a PR-witness of
`S₂ = {B ∪ (B ⊕ B) | B ⊆ ℕ infinite}` (every `A ∈ U` contains `B` and all sums `b + b'` of
distinct `b, b' ∈ B` for some infinite `B`) if and only if there is a Ramsey's witness `W` on
`ℕ × ℕ` (Definition 3.4) whose images under the two projections and under the sum map
`(a, b) ↦ a + b` all equal `U`.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.6 (`integers-2025-A105-prop-3-6`). -/
public theorem_wanted pairwiseSums_witness_iff_exists_ramseyWitness (U : Ultrafilter ℕ) :
    (∀ A ∈ U, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∀ b ∈ B, ∀ b' ∈ B, b < b' → b + b' ∈ A) ↔
      ∃ W : Ultrafilter (ℕ × ℕ),
        (∀ X ∈ W, ∃ H : Set ℕ, H.Infinite ∧ ∀ h ∈ H, ∀ h' ∈ H, h < h' → (h, h') ∈ X) ∧
        W.map Prod.fst = U ∧ W.map Prod.snd = U ∧ W.map (fun p => p.1 + p.2) = U

end

end MetaMathlibExt
