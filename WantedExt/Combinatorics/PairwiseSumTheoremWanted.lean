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

/-- **Hindman's finite sums theorem.** For every finite coloring of
$\mathbb{N} = \{0, 1, 2, \dots\}$ there is an infinite set $A \subseteq \mathbb{N}$ whose set of
finite sums $\mathrm{FS}(A) = \{\sum_{a \in F} a : F \subseteq A \text{ finite and nonempty}\}$ is
monochromatic.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Theorem 1.1 (`integers-2025-A105-thm-1-1`). -/
public theorem_wanted exists_infinite_finiteSums_monochromatic {r : ℕ} (c : ℕ → Fin r) :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ k : Fin r, ∀ F : Finset ℕ, F.Nonempty → (F : Set ℕ) ⊆ A →
      c (∑ a ∈ F, a) = k

/-- **Pairwise sum theorem.** For every finite coloring of $\mathbb{N} = \{0, 1, 2, \dots\}$ there
is an infinite set $A \subseteq \mathbb{N}$ such that $A \cup \{a + a' : a, a' \in A, a \ne a'\}$
is monochromatic.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Theorem 1.2 (`integers-2025-A105-thm-1-2`). -/
public theorem_wanted exists_infinite_pairwiseSums_monochromatic {r : ℕ} (c : ℕ → Fin r) :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ k : Fin r, (∀ a ∈ A, c a = k) ∧
      ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → c (a + a') = k

/-- **Disjoint infinite sets with monochromatic union and sumset.** For every finite coloring of
$\mathbb{N} = \{0, 1, 2, \dots\}$ there are disjoint infinite sets $A, B \subseteq \mathbb{N}$ such
that $A \cup B \cup (A + B)$ is monochromatic, where $A + B = \{a + b : a \in A, b \in B\}$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Theorem 2.2 (`integers-2025-A105-thm-2-2`). -/
public theorem_wanted exists_disjoint_infinite_union_add_monochromatic {r : ℕ} (c : ℕ → Fin r) :
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ Disjoint A B ∧ ∃ k : Fin r,
      (∀ a ∈ A, c a = k) ∧ (∀ b ∈ B, c b = k) ∧ ∀ a ∈ A, ∀ b ∈ B, c (a + b) = k

/-- **Interleaved sequences and tensor products of ultrafilters.** For ultrafilters $U$, $V$ on
$\mathbb{N} = \{0, 1, 2, \dots\}$ and $X \subseteq \mathbb{N} \times \mathbb{N}$, write
$X \in U \otimes V$ when $\{n : \{m : (n, m) \in X\} \in V\} \in U$. For every
$X \subseteq \mathbb{N} \times \mathbb{N}$ the following are equivalent: (1) there are strictly
increasing sequences $(a_i)_{i \in \mathbb{N}}$, $(b_j)_{j \in \mathbb{N}}$ in $\mathbb{N}$ with
disjoint ranges such that $(a_i, b_j) \in X$ whenever $i \le j$ and $(b_j, a_i) \in X$ whenever
$j < i$; (2) there are non-principal ultrafilters $V_1$, $V_2$ on $\mathbb{N}$ with
$X \in V_1 \otimes V_2$ and $X \in V_2 \otimes V_1$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Lemma 2.1 (`integers-2025-A105-lem-2-1`). -/
public theorem_wanted exists_interleaved_sequences_iff_mem_tensor (X : Set (ℕ × ℕ)) :
    (∃ a b : ℕ → ℕ, StrictMono a ∧ StrictMono b ∧ Disjoint (Set.range a) (Set.range b) ∧
        (∀ i j, i ≤ j → (a i, b j) ∈ X) ∧ (∀ i j, j < i → (b j, a i) ∈ X)) ↔
      ∃ V₁ V₂ : Ultrafilter ℕ, (V₁ : Filter ℕ) ≤ cofinite ∧ (V₂ : Filter ℕ) ≤ cofinite ∧
        {n | {m | (n, m) ∈ X} ∈ V₂} ∈ V₁ ∧ {n | {m | (n, m) ∈ X} ∈ V₁} ∈ V₂

/-- **Partition regular families and ultrafilters.** Let $\mathcal{F}$ be a family of subsets of a
set $S$. Every finite coloring of $S$ has a monochromatic member of $\mathcal{F}$ (that is,
$\mathcal{F}$ is weakly partition regular) if and only if there is an ultrafilter $U$ on $S$ such
that every $A \in U$ contains some member of $\mathcal{F}$ ($U$ is a PR-witness of $\mathcal{F}$).

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.1 (`integers-2025-A105-prop-3-1`), quoting
Hindman and Strauss, Theorem 5.7. -/
public theorem_wanted weaklyPartitionRegular_iff_exists_ultrafilter {S : Type*}
    (𝓕 : Set (Set S)) :
    (∀ (r : ℕ) (c : S → Fin r), ∃ F ∈ 𝓕, ∃ k : Fin r, ∀ x ∈ F, c x = k) ↔
      ∃ U : Ultrafilter S, ∀ A ∈ U, ∃ F ∈ 𝓕, F ⊆ A

/-- **PR-witnesses of the finite sums family.** Let $\beta\mathbb{N}^+$ be the space of
ultrafilters on the positive integers $\mathbb{N}^+$, with the Stone–Čech topology and the sum
for which $A \in U + V$ if and only if $\{n : \{m : n + m \in A\} \in V\} \in U$. For
$X \subseteq \mathbb{N}^+$ let $\mathrm{FS}(X)$ be the set of sums of nonempty finite subsets of
$X$. An ultrafilter $U \in \beta\mathbb{N}^+$ is a PR-witness of the Hindman family, that is,
every $A \in U$ contains $\mathrm{FS}(X)$ for some infinite $X \subseteq \mathbb{N}^+$, if and
only if $U$ lies in the closure of the set of idempotents $\{V \in \beta\mathbb{N}^+ : V + V = V\}$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.3 (`integers-2025-A105-prop-3-3`), quoting
Hindman and Strauss, Lemma 5.19. -/
public theorem_wanted finiteSums_witness_iff_mem_closure_idempotents (U : Ultrafilter ℕ+) :
    letI : Add (Ultrafilter ℕ+) := Ultrafilter.add
    (∀ A ∈ U, ∃ X : Set ℕ+, X.Infinite ∧
        ∀ F : Finset ℕ+, F.Nonempty → (F : Set ℕ+) ⊆ X →
          ∃ y ∈ A, (y : ℕ) = ∑ x ∈ F, (x : ℕ)) ↔
      U ∈ closure {V : Ultrafilter ℕ+ | V + V = V}

/-- **Ramsey's witnesses are the closure of tensor squares.** For an ultrafilter $U$ on
$\mathbb{N} = \{0, 1, 2, \dots\}$, the tensor square $U \otimes U$ is the ultrafilter on
$\mathbb{N} \times \mathbb{N}$ whose members are the sets $X$ with
$\{n : \{m : (n, m) \in X\} \in U\} \in U$. An ultrafilter $W$ on $\mathbb{N} \times \mathbb{N}$ is
a Ramsey's witness when every $X \in W$ contains $[H]^2 = \{(h, h') \in H \times H : h < h'\}$ for
some infinite $H \subseteq \mathbb{N}$. An ultrafilter $W$ on $\mathbb{N} \times \mathbb{N}$ is a
Ramsey's witness if and only if $W$ lies in the closure, in the Stone–Čech space
$\beta(\mathbb{N} \times \mathbb{N})$, of the set of tensor squares $U \otimes U$ of non-principal
ultrafilters $U$ on $\mathbb{N}$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.5 (`integers-2025-A105-prop-3-5`). -/
public theorem_wanted ramseyWitness_iff_mem_closure_tensor_squares (W : Ultrafilter (ℕ × ℕ)) :
    (∀ X ∈ W, ∃ H : Set ℕ, H.Infinite ∧ ∀ h ∈ H, ∀ h' ∈ H, h < h' → (h, h') ∈ X) ↔
      W ∈ closure {V : Ultrafilter (ℕ × ℕ) | ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ cofinite ∧
        V = U.bind fun n => U.map (Prod.mk n)}

/-- **PR-witnesses of the pairwise sum family.** An ultrafilter $W$ on
$\mathbb{N} \times \mathbb{N}$, where $\mathbb{N} = \{0, 1, 2, \dots\}$, is a Ramsey's witness
when every $X \in W$ contains $\{(h, h') \in H \times H : h < h'\}$ for some infinite
$H \subseteq \mathbb{N}$. For an ultrafilter $U$ on $\mathbb{N}$ the following are equivalent:
(1) every $A \in U$ contains an infinite set $B$ together with all sums $b + b'$ of distinct
$b, b' \in B$ ($U$ is a PR-witness of the pairwise sum family); (2) there is a Ramsey's witness
$W$ on $\mathbb{N} \times \mathbb{N}$ whose images under the projections $(a, b) \mapsto a$ and
$(a, b) \mapsto b$ and under the sum map $(a, b) \mapsto a + b$ all equal $U$.

Source: Mauro Di Nasso and Renling Jin, *From Schur's Theorem to the Pairwise Sum Theorem*,
INTEGERS 25 (2025), Article A105, Proposition 3.6 (`integers-2025-A105-prop-3-6`). -/
public theorem_wanted pairwiseSums_witness_iff_exists_ramseyWitness (U : Ultrafilter ℕ) :
    (∀ A ∈ U, ∃ B : Set ℕ, B.Infinite ∧ B ⊆ A ∧ ∀ b ∈ B, ∀ b' ∈ B, b < b' → b + b' ∈ A) ↔
      ∃ W : Ultrafilter (ℕ × ℕ),
        (∀ X ∈ W, ∃ H : Set ℕ, H.Infinite ∧ ∀ h ∈ H, ∀ h' ∈ H, h < h' → (h, h') ∈ X) ∧
        W.map Prod.fst = U ∧ W.map Prod.snd = U ∧ W.map (fun p => p.1 + p.2) = U

end

end MetaMathlibExt
