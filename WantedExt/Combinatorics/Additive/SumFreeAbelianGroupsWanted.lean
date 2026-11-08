/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.Rank
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sum-free sets in abelian groups

Statements from Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian
Groups*, INTEGERS 26 (2026), Article A97 (arXiv:2506.17401; definitions taken from the arXiv
TeX source): counts of maximal (distinct) sum-free sets, the container and structure lemmas
the paper quotes, subgroup-counting lemmas, and the quoted bounds on the number of maximal
independent sets in graphs.

A *Schur triple* is `x + y = z`; it is *distinct* when `x, y, z` are pairwise distinct. The
paper's decompositions `G = ℤ_{2^{α₁}} ⊕ … ⊕ K` are written as explicit products.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- `S` is sum-free: it contains no Schur triple `x + y = z`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public def IsSumFreeSet {G : Type*} [Add G] (S : Set G) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S

/-- `S` is distinct sum-free: it contains no Schur triple `x + y = z` with `x, y, z`
pairwise distinct.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public def IsDistinctSumFreeSet {G : Type*} [Add G] (S : Set G) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ≠ x → x + y ≠ y → x + y ∉ S

/-- A sum-free set is distinct sum-free.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public theorem IsSumFreeSet.isDistinctSumFreeSet {G : Type*} [Add G] {S : Set G}
    (h : IsSumFreeSet S) : IsDistinctSumFreeSet S :=
  fun x hx y hy _ _ _ => h x hx y hy

/-- The empty set is sum-free.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public theorem isSumFreeSet_empty {G : Type*} [Add G] : IsSumFreeSet (∅ : Set G) :=
  fun _ hx => hx.elim

/-- The size of a largest sum-free subset of `S` (for `S = univ` this is `μ(G)`).

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction (`μ(G)`) and Theorem 2. -/
public noncomputable def largestSumFreeCard {G : Type*} [Add G] (S : Set G) : ℕ :=
  sSup {k | ∃ T : Finset G, (T : Set G) ⊆ S ∧ IsSumFreeSet (T : Set G) ∧ T.card = k}

/-- A largest sum-free subset of `S` has at most `|S|` elements.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public theorem largestSumFreeCard_le {G : Type*} [Add G] (S : Finset G) :
    largestSumFreeCard (S : Set G) ≤ S.card := by
  refine csSup_le' ?_
  rintro k ⟨T, hT, -, rfl⟩
  exact Finset.card_le_card (Finset.coe_subset.1 hT)

/-- `f_max(G)`: the number of maximal sum-free subsets of `G`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction. -/
public noncomputable def maxSumFreeCount (G : Type*) [Add G] : ℕ :=
  {S : Set G | Maximal IsSumFreeSet S}.ncard

/-- `f*_max(G)`: the number of maximal distinct sum-free subsets of `G`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, section "Maximal distinct sum-free subsets". -/
public noncomputable def maxDistinctSumFreeCount (G : Type*) [Add G] : ℕ :=
  {S : Set G | Maximal IsDistinctSumFreeSet S}.ncard

/-- The number of ordered distinct Schur triples `(x, y, x + y)` inside `F`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, introduction and Lemma 1. -/
public noncomputable def distinctSchurTripleCount {G : Type*} [Add G] (F : Set G) : ℕ :=
  {xy : G × G | xy.1 ∈ F ∧ xy.2 ∈ F ∧ xy.1 ≠ xy.2 ∧ xy.1 + xy.2 ≠ xy.1 ∧
    xy.1 + xy.2 ≠ xy.2 ∧ xy.1 + xy.2 ∈ F}.ncard

/-- `G` is of type `I(p)`: `p` is the smallest prime `p ≡ 2 (mod 3)` dividing `|G|`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 1. -/
public def IsTypeOneGroup (G : Type*) [Fintype G] (p : ℕ) : Prop :=
  p.Prime ∧ p % 3 = 2 ∧ p ∣ Fintype.card G ∧
    ∀ q : ℕ, q.Prime → q % 3 = 2 → q ∣ Fintype.card G → p ≤ q

/-- Unfolding of `IsTypeOneGroup`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 1. -/
public theorem isTypeOneGroup_iff (G : Type*) [Fintype G] (p : ℕ) :
    IsTypeOneGroup G p ↔ p.Prime ∧ p % 3 = 2 ∧ p ∣ Fintype.card G ∧
      ∀ q : ℕ, q.Prime → q % 3 = 2 → q ∣ Fintype.card G → p ≤ q :=
  Iff.rfl

/-- **Diananda-Yap and Green-Ruzsa.** The largest sum-free subset of a finite abelian group
`G` of order `n` has size `μ(G) = n (1/3 + 1/(3p))` if `G` is of type `I(p)`, `n/3` if `G` is of
type `II` (no prime `≡ 2 (mod 3)` divides `n`, but `3 ∣ n`), and `n (1/3 - 1/(3m))` with `m` the
exponent of `G` if `G` is of type `III` (otherwise). Values compared in `ℚ`. Quoted in the
paper from Diananda-Yap and Green-Ruzsa.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 1 (`integers-2026-A97-thm-1`), with Definition 1. -/
public theorem_wanted largestSumFreeCard_univ_eq {G : Type*} [AddCommGroup G] [Fintype G] :
    (∀ p, IsTypeOneGroup G p →
      (largestSumFreeCard (Set.univ : Set G) : ℚ) = Fintype.card G * (1 / 3 + 1 / (3 * p))) ∧
    ((∀ q : ℕ, q.Prime → q % 3 = 2 → ¬ q ∣ Fintype.card G) → 3 ∣ Fintype.card G →
      (largestSumFreeCard (Set.univ : Set G) : ℚ) = Fintype.card G / 3) ∧
    ((∀ q : ℕ, q.Prime → q % 3 = 2 → ¬ q ∣ Fintype.card G) → ¬ 3 ∣ Fintype.card G →
      (largestSumFreeCard (Set.univ : Set G) : ℚ) =
        Fintype.card G * (1 / 3 - 1 / (3 * AddMonoid.exponent G)))

/-- `mis(Γ)`: the number of maximal independent sets of the graph `Γ`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, subsection "Maximal independent sets in graphs". -/
public noncomputable def maxIndepSetCount {V : Type*} (Γ : SimpleGraph V) : ℕ :=
  {I : Set V | Maximal Γ.IsIndepSet I}.ncard

/-- Edge relation of the distinct link graph `L*_S[B]` between two vertices: `x ≠ y` and
`{x, y, s}` is a distinct Schur triple for some `s ∈ S`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 2 (i). -/
public def DistinctLinkAdj {G : Type*} [Add G] (S : Set G) (x y : G) : Prop :=
  x ≠ y ∧ ∃ s ∈ S, x ≠ s ∧ y ≠ s ∧ (x + y = s ∨ x + s = y ∨ y + s = x)

/-- Loop of the distinct link graph `L*_S[B]` at `x`: `{x, s, s'}` is a distinct Schur triple
for some distinct `s, s' ∈ S`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 2 (ii). -/
public def DistinctLinkLoop {G : Type*} [Add G] (S : Set G) (x : G) : Prop :=
  ∃ s ∈ S, ∃ s' ∈ S, s ≠ s' ∧ x ≠ s ∧ x ≠ s' ∧ (s + s' = x ∨ x + s = s' ∨ x + s' = s)

/-- `I` is an independent set of the distinct link graph `L*_S[B]`: `I ⊆ B`, no vertex of
`I` carries a loop, and no two vertices of `I` are adjacent.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 2. -/
public def IsDistinctLinkIndep {G : Type*} [Add G] (S B I : Set G) : Prop :=
  I ⊆ B ∧ (∀ x ∈ I, ¬DistinctLinkLoop S x) ∧ ∀ x ∈ I, ∀ y ∈ I, ¬DistinctLinkAdj S x y

/-- The empty set is independent in every distinct link graph.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Definition 2. -/
public theorem isDistinctLinkIndep_empty {G : Type*} [Add G] (S B : Set G) :
    IsDistinctLinkIndep S B ∅ :=
  ⟨Set.empty_subset B, fun _ hx => hx.elim, fun _ hx => hx.elim⟩

/-- **Container lemma.** For every `δ > 0` there is `n₀` such that every finite abelian group
`G` of order `n ≥ n₀` has a family `𝓕` of subsets with: (i) each `F ∈ 𝓕` has at most `δn²`
distinct Schur triples, (ii) every distinct sum-free set lies in some `F ∈ 𝓕`,
(iii) `|𝓕| ≤ 2^(δn)`, (iv) every `F ∈ 𝓕` is `A ∪ B` with `A` sum-free and `|B| ≤ δn`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 1 (`integers-2026-A97-lem-1`). -/
public theorem_wanted exists_distinct_sumFree_containers (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ (G : Type) [AddCommGroup G] [Fintype G], n₀ ≤ Fintype.card G →
      ∃ 𝓕 : Set (Set G),
        (∀ F ∈ 𝓕, (distinctSchurTripleCount F : ℝ) ≤ δ * (Fintype.card G : ℝ) ^ 2) ∧
        (∀ S : Set G, IsDistinctSumFreeSet S → ∃ F ∈ 𝓕, S ⊆ F) ∧
        (𝓕.ncard : ℝ) ≤ (2 : ℝ) ^ (δ * Fintype.card G) ∧
        ∀ F ∈ 𝓕, ∃ A B : Set G, F = A ∪ B ∧ IsSumFreeSet A ∧
          (B.ncard : ℝ) ≤ δ * Fintype.card G

/-- **Green–Ruzsa structure lemma.** If `G` is of type `I(p)`, `p = 3k + 2`, and `A ⊆ G` is
sum-free with `|A| > (1/3 + 1/(3(p+1)))|G|`, then some homomorphism `ψ : G → ℤ_p` maps `A`
into `{k + 1, …, 2k + 1}`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 2 (`integers-2026-A97-lem-2`). -/
public theorem_wanted exists_addMonoidHom_zmod_of_large_sumFree {G : Type*} [AddCommGroup G]
    [Fintype G] {p k : ℕ} (hG : IsTypeOneGroup G p) (hpk : p = 3 * k + 2) {A : Set G}
    (hA : IsSumFreeSet A)
    (hcard : ((1 : ℝ) / 3 + 1 / (3 * (p + 1))) * Fintype.card G < A.ncard) :
    ∃ ψ : G →+ ZMod p, ∀ a ∈ A, (ψ a).val ∈ Finset.Icc (k + 1) (2 * k + 1)

/-- In a finite abelian group the number of subgroups of order `k` equals the number of
subgroups of index `k`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 3 (`integers-2026-A97-lem-3`). -/
public theorem_wanted ncard_addSubgroup_card_eq_ncard_index_eq (G : Type*) [AddCommGroup G]
    [Finite G] (k : ℕ) :
    {H : AddSubgroup G | Nat.card H = k}.ncard = {H : AddSubgroup G | H.index = k}.ncard

/-- For `G = ℤ_{2^{α₁}} ⊕ … ⊕ ℤ_{2^{α_{r₁}}} ⊕ ℤ₂^{r₂}` with every `αᵢ ≥ 2` and
`r = r₁ + r₂ ≥ 1`, exactly `2^{r₁} - 1` index-2 subgroups have rank `r` and exactly
`2^r - 2^{r₁}` have rank `r - 1` (rank = minimal number of generators, `AddGroup.rank`).

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 4 (`integers-2026-A97-lem-4`). -/
public theorem_wanted ncard_index_two_addSubgroup_rank (r₁ r₂ : ℕ) (hr : 1 ≤ r₁ + r₂)
    (α : Fin r₁ → ℕ) (hα : ∀ i, 2 ≤ α i) :
    {H : AddSubgroup (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2)) |
        H.index = 2 ∧ AddGroup.rank H = r₁ + r₂}.ncard = 2 ^ r₁ - 1 ∧
      {H : AddSubgroup (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2)) |
        H.index = 2 ∧ AddGroup.rank H = r₁ + r₂ - 1}.ncard = 2 ^ (r₁ + r₂) - 2 ^ r₁

/-- **Balogh–Liu–Sharifzadeh–Treglown bound.** If `k ≥ 1`, `Γ` has `n` vertices,
`Δ(Γ) ≤ k δ(Γ)` and `b = √δ(Γ)`, then
`mis(Γ) ≤ ∑_{0 ≤ i ≤ n/b} C(n, i) · 3^{(k/(k+1)) n/3 + 2n/(3b)}`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 5 (`integers-2026-A97-lem-5`). -/
public theorem_wanted maxIndepSetCount_le_of_maxDegree_le {V : Type*} [Fintype V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {k : ℝ} (hk : 1 ≤ k)
    (hΔ : (Γ.maxDegree : ℝ) ≤ k * Γ.minDegree) :
    (maxIndepSetCount Γ : ℝ) ≤
      (∑ i ∈ Finset.range (⌊(Fintype.card V : ℝ) / Real.sqrt Γ.minDegree⌋₊ + 1),
          ((Fintype.card V).choose i : ℝ)) *
        (3 : ℝ) ^ (k / (k + 1) * (Fintype.card V / 3) +
          2 * Fintype.card V / (3 * Real.sqrt Γ.minDegree))

/-- **Almost triangle-free bound.** Let `n, D ≥ 1` and `k ∈ ℝ`. If deleting the vertex set
`T` from `Γ` leaves a triangle-free graph `Γ'` with `n` vertices and at least `n/2 + k`
edges, and `Δ(Γ) ≤ D`, then `mis(Γ) ≤ 2^{n/2 - k/(100D²) + 2|T|}`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 6 (`integers-2026-A97-lem-6`). -/
public theorem_wanted maxIndepSetCount_le_of_almost_triangleFree {V : Type*} [Fintype V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (T : Finset V) {n D : ℕ} (hn : 1 ≤ n)
    (hD : 1 ≤ D) (k : ℝ)
    (htri : ∀ a b c : V, a ∉ T → b ∉ T → c ∉ T → ¬(Γ.Adj a b ∧ Γ.Adj b c ∧ Γ.Adj a c))
    (hΔ : Γ.maxDegree ≤ D) (hv : Fintype.card V - T.card = n)
    (he : (n : ℝ) / 2 + k ≤ {e ∈ Γ.edgeSet | ∀ v ∈ e, v ∉ T}.ncard) :
    (maxIndepSetCount Γ : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 - k / (100 * (D : ℝ) ^ 2) + 2 * T.card)

/-- **Liu–Sharifzadeh stability bound.** If `Γ` has `n` vertices, `n + k` edges (`k ∈ ℤ`) and
maximum degree `Δ ≥ 1`, then `mis(Γ) ≤ 3^{Δ/13} · 3^{n/3 - k/(13Δ)}`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 7 (`integers-2026-A97-lem-7`). -/
public theorem_wanted maxIndepSetCount_le_of_edge_count {V : Type*} [Fintype V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (k : ℤ) {Δ : ℕ} (hΔpos : 1 ≤ Δ)
    (hΔ : Γ.maxDegree = Δ) (he : (Γ.edgeFinset.card : ℤ) = Fintype.card V + k) :
    (maxIndepSetCount Γ : ℝ) ≤
      (3 : ℝ) ^ ((Δ : ℝ) / 13) * (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3 - k / (13 * Δ))

/-- **Link-graph extension lemma.** Let `B, S ⊆ G` be distinct sum-free and disjoint. If
`I ⊆ B` and `S ∪ I` is a maximal distinct sum-free subset of `G`, then `I` is a maximal
independent set of the distinct link graph `L*_S[B]`. Disjointness of `B` and `S` is
added; without it the statement fails (`G = ℤ₂`, `S = G`, `B = {0}`, `I = ∅`).

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 8 (`integers-2026-A97-lem-8`). -/
public theorem_wanted maximal_isDistinctLinkIndep_of_maximal {G : Type*} [AddCommGroup G]
    {B S I : Set G} (hB : IsDistinctSumFreeSet B) (hS : IsDistinctSumFreeSet S)
    (hBS : Disjoint B S) (hI : I ⊆ B) (hmax : Maximal IsDistinctSumFreeSet (S ∪ I)) :
    Maximal (IsDistinctLinkIndep S B) I

/-- If `p ≥ 5` and `G` is of type `I(p)`, then `f*_max(G) ≥ 2^{μ(G)/2}`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Proposition 1 (`integers-2026-A97-prop-1`). -/
public theorem_wanted two_rpow_le_maxDistinctSumFreeCount_of_typeOne {G : Type*}
    [AddCommGroup G] [Fintype G] {p : ℕ} (hp : 5 ≤ p) (hG : IsTypeOneGroup G p) :
    (2 : ℝ) ^ ((largestSumFreeCard (Set.univ : Set G) : ℝ) / 2) ≤ maxDistinctSumFreeCount G

/-- **Random sum-free sets.** Let `(G_n)` be finite abelian groups with `|G_i| < |G_j|` and
`μ(G_i)/|G_i| = μ(G_j)/|G_j|` for `i < j`. For every `ε > 0` there is `C > 0` such that if
`C |G_n|^{-1/2} ≤ p_n ≤ 1`, then the probability that the largest sum-free subset of the
binomial random subset `G_{n,p_n}` has size within `(1 ± ε) μ(G_n) p_n` tends to `1`. The
probability is the explicit sum `∑_S p^{|S|} (1-p)^{|G|-|S|}` over qualifying `S`; the
bound `p_n ≤ 1` (a probability) is made explicit.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 2 (`integers-2026-A97-thm-2`). -/
public theorem_wanted tendsto_prob_largestSumFreeCard_random (G : ℕ → Type)
    [∀ n, AddCommGroup (G n)] [∀ n, Fintype (G n)] [∀ n, DecidableEq (G n)]
    (hcard : ∀ i j, i < j → Fintype.card (G i) < Fintype.card (G j))
    (hdens : ∀ i j, i < j →
      (largestSumFreeCard (Set.univ : Set (G i)) : ℝ) / Fintype.card (G i) =
        (largestSumFreeCard (Set.univ : Set (G j)) : ℝ) / Fintype.card (G j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ → ℝ,
      (∀ n, C * (Fintype.card (G n) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ p n) → (∀ n, p n ≤ 1) →
      Tendsto (fun n => ∑ S : Finset (G n),
          (p n) ^ S.card * (1 - p n) ^ (Fintype.card (G n) - S.card) *
            (if |(largestSumFreeCard (S : Set (G n)) : ℝ) -
                largestSumFreeCard (Set.univ : Set (G n)) * p n| ≤
                ε * largestSumFreeCard (Set.univ : Set (G n)) * p n then 1 else 0))
        atTop (nhds 1)

/-- **Hassler–Treglown.** With `n = 2^k`, `f_max(ℤ₂^k) = (C(n-1, 2) + o(1)) 2^{n/4}`; with
`n = 3^k`, `f_max(ℤ₃^k) = ((n-3)(n-1)/3 + o(1)) 3^{n/9}`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 3 (`integers-2026-A97-thm-3`). -/
public theorem_wanted maxSumFreeCount_elementary_two_three :
    Tendsto (fun k : ℕ => (maxSumFreeCount (Fin k → ZMod 2) : ℝ) /
        (2 : ℝ) ^ ((2 : ℝ) ^ k / 4) - ((2 ^ k - 1).choose 2 : ℝ)) atTop (nhds 0) ∧
      Tendsto (fun k : ℕ => (maxSumFreeCount (Fin k → ZMod 3) : ℝ) /
        (3 : ℝ) ^ ((3 : ℝ) ^ k / 9) - ((3 : ℝ) ^ k - 3) * ((3 : ℝ) ^ k - 1) / 3)
        atTop (nhds 0)

/-- **Theorem 4.** There is an absolute `C` such that for every `ε > 0` and all sufficiently
large even-order `G = ℤ_{2^{α₁}} ⊕ … ⊕ ℤ_{2^{α_r}} ⊕ K` (`r, αᵢ ≥ 1`, `|K|` odd) with
`n/2^r ≥ C`, `2^{(1/4-ε)n} ≤ f*_max(G) ≤ 2^{(1/4+ε)n}`, i.e. `f*_max(G) = 2^{n/4+o(n)}`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 4 (`integers-2026-A97-thm-4`). -/
public theorem_wanted maxDistinctSumFreeCount_even_order :
    ∃ C : ℕ, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (r : ℕ) (α : Fin r → ℕ) (K : Type)
      [AddCommGroup K] [Fintype K], 1 ≤ r → (∀ i, 1 ≤ α i) → Odd (Fintype.card K) →
      n₀ ≤ Fintype.card (((i : Fin r) → ZMod (2 ^ α i)) × K) →
      (C : ℝ) ≤ (Fintype.card (((i : Fin r) → ZMod (2 ^ α i)) × K) : ℝ) / 2 ^ r →
      (2 : ℝ) ^ ((1 / 4 - ε) * Fintype.card (((i : Fin r) → ZMod (2 ^ α i)) × K)) ≤
          maxDistinctSumFreeCount (((i : Fin r) → ZMod (2 ^ α i)) × K) ∧
        (maxDistinctSumFreeCount (((i : Fin r) → ZMod (2 ^ α i)) × K) : ℝ) ≤
          (2 : ℝ) ^ ((1 / 4 + ε) * Fintype.card (((i : Fin r) → ZMod (2 ^ α i)) × K))

/-- **Theorem 5 (sharp upper bound).** There is an absolute `C` such that for every `η > 0`
and all even `n ≥ n₀`, if `G = ℤ_{2^{α₁}} ⊕ … ⊕ ℤ_{2^{α_{r₁}}} ⊕ ℤ₂^{r₂} ⊕ K` has order `n`,
`αᵢ ≥ 2`, `|K|` odd, `r = r₁ + r₂ ≥ 1` and `n/2^r ≥ C`, then
`f*_max(G) ≤ (2^{2r-1} + 2^{r+r₁-1} - 2^{r+1} + 2^{r₁}) 2^{n/4}
  + (2^r - 2^{r₁} + η) 2^{n/4 - 2^{r-2}}`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 5 (`integers-2026-A97-thm-5`). -/
public theorem_wanted maxDistinctSumFreeCount_le_sharp :
    ∃ C : ℕ, ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ (r₁ r₂ : ℕ) (α : Fin r₁ → ℕ) (K : Type)
      [AddCommGroup K] [Fintype K], 1 ≤ r₁ + r₂ → (∀ i, 2 ≤ α i) → Odd (Fintype.card K) →
      n₀ ≤ Fintype.card (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) →
      (C : ℝ) ≤ (Fintype.card (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) /
        2 ^ (r₁ + r₂) →
      (maxDistinctSumFreeCount
          (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) ≤
        ((2 : ℝ) ^ (2 * (r₁ + r₂) - 1) + 2 ^ (r₁ + r₂ + r₁ - 1) - 2 ^ (r₁ + r₂ + 1) + 2 ^ r₁) *
            (2 : ℝ) ^ ((Fintype.card
              (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) / 4) +
          ((2 : ℝ) ^ (r₁ + r₂) - 2 ^ r₁ + η) *
            (2 : ℝ) ^ ((Fintype.card
              (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) / 4 -
                (2 : ℝ) ^ ((r₁ + r₂ : ℝ) - 2))

/-- **Theorem 6 (sharp lower bound).** Under the hypotheses of Theorem 5,
`(2^{2r-1} + 2^{r+r₁-1} - 2^{r+1} + 2^{r₁}) 2^{n/4} + (2^r - 2^{r₁} - η) 2^{n/4 - 2^{r-2}}
  ≤ f*_max(G)`.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Theorem 6 (`integers-2026-A97-thm-6`). -/
public theorem_wanted le_maxDistinctSumFreeCount_sharp :
    ∃ C : ℕ, ∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ (r₁ r₂ : ℕ) (α : Fin r₁ → ℕ) (K : Type)
      [AddCommGroup K] [Fintype K], 1 ≤ r₁ + r₂ → (∀ i, 2 ≤ α i) → Odd (Fintype.card K) →
      n₀ ≤ Fintype.card (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) →
      (C : ℝ) ≤ (Fintype.card (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) /
        2 ^ (r₁ + r₂) →
      ((2 : ℝ) ^ (2 * (r₁ + r₂) - 1) + 2 ^ (r₁ + r₂ + r₁ - 1) - 2 ^ (r₁ + r₂ + 1) + 2 ^ r₁) *
            (2 : ℝ) ^ ((Fintype.card
              (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) / 4) +
          ((2 : ℝ) ^ (r₁ + r₂) - 2 ^ r₁ - η) *
            (2 : ℝ) ^ ((Fintype.card
              (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ) / 4 -
                (2 : ℝ) ^ ((r₁ + r₂ : ℝ) - 2)) ≤
        (maxDistinctSumFreeCount
          (((i : Fin r₁) → ZMod (2 ^ α i)) × (Fin r₂ → ZMod 2) × K) : ℝ)

end

end MetaMathlibExt
