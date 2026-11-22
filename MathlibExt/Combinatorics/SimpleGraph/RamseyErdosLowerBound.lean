/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
public import MathlibExt.Combinatorics.Ramsey
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Probability.Combinatorics.RandomSubset
public import Mathlib.Combinatorics.SimpleGraph.Copy

import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# Erdős's lower bound for diagonal Ramsey numbers

Erdős (1947): if `C(n, k) 2^{1 - C(k, 2)} < 1`, then some graph on `n` vertices has neither a
clique nor an independent set of size `k`, so `R(k, k) > n`. The proof is the first moment
method: in a uniformly random graph each `k`-set is a clique or an independent set with
probability `2^{1 - C(k, 2)}`, and a union bound over the `C(n, k)` sets leaves positive
probability for a graph with neither.

Graphs on `Fin n` are encoded by indicators `ω` of sets of pairs `{i, j}`, and the uniformly
random graph is the random subset of pairs with every pair kept with probability `1/2`
(`MathlibExt.Probability.Combinatorics.RandomSubset.randomSubsetLaw`).

## Main results

* `exists_not_isContained_of_choose_mul_lt`: a graph on `n` vertices with no `K_k` in it or in
  its complement.
* `not_classicalRamsey_of_choose_mul_lt`: the Ramsey property `classicalRamsey k k n` fails.
* `lt_of_classicalRamsey_of_choose_mul_lt`, `lt_graphRamsey_of_choose_mul_lt`: `R(k, k) > n`.
* `exists_classicalRamsey`: some `N` has the Ramsey property, from the repository's finite
  Ramsey theorem for pairs `MathlibExt.Combinatorics.Ramsey.ramsey_two_uniform`; so
  `graphRamsey s t` is a genuine minimum.

Reference: Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes,
Spring 2019, Theorem 1.4 (https://yufeizhao.com/pm/sp19/pmnotes.pdf); P. Erdős, "Some remarks on
the theory of graphs", *Bull. Amer. Math. Soc.* 53 (1947).
-/

@[expose] public section

open MeasureTheory SimpleGraph Finset unitInterval MathlibExt.Probability.Combinatorics.RandomSubset

namespace MathlibExt.Combinatorics.RamseyErdosLowerBound

variable {n : ℕ}

/-- **Pairs of vertices.** The two-element subsets `{i, j}` of `Fin n`, the possible edges of a
graph on `Fin n`. -/
abbrev Pair (n : ℕ) := {s : Finset (Fin n) // s.card = 2}

/-- **Graph with a given set of pairs as edges.** For an indicator `ω` of a set of pairs of
vertices of `Fin n`, the simple graph in which distinct `i` and `j` are adjacent exactly when
`ω {i, j} = true` (Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes,
2019, proof of Theorem 1.4: a red-blue colouring of the edges of `K_n`, read as the graph of its
red edges). -/
def pairGraph (ω : Pair n → Bool) : SimpleGraph (Fin n) where
  Adj i j := ∃ h : i ≠ j, ω ⟨{i, j}, Finset.card_pair h⟩ = true
  symm := ⟨fun i j ⟨h, hω⟩ => by
    refine ⟨h.symm, ?_⟩
    have e : (⟨{j, i}, Finset.card_pair h.symm⟩ : Pair n) = ⟨{i, j}, Finset.card_pair h⟩ :=
      Subtype.ext (Finset.pair_comm j i)
    rw [e]
    exact hω⟩
  loopless := ⟨fun i ⟨h, _⟩ => h rfl⟩

/-- **Pairs inside a vertex set.** The two-element subsets of a set `R` of vertices; there are
`C(|R|, 2)` of them (`card_pairsIn`). -/
def pairsIn (R : Finset (Fin n)) : Finset (Pair n) :=
  Finset.univ.filter fun s => s.1 ⊆ R

lemma card_pairsIn (R : Finset (Fin n)) : (pairsIn R).card = R.card.choose 2 := by
  have hmap : (pairsIn R).map ⟨Subtype.val, Subtype.val_injective⟩ = R.powersetCard 2 := by
    ext s
    simp only [pairsIn, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Finset.mem_powersetCard]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht, t.2⟩
    · rintro ⟨hs, hc⟩
      exact ⟨⟨s, hc⟩, hs, rfl⟩
  rw [← Finset.card_map, hmap, Finset.card_powersetCard]

/-- **A copy of `K_k` gives a monochromatic `k`-set.** A copy of `K_k` in `pairGraph ω`
(`b = true`) or in its complement (`b = false`) occupies a `k`-set `R` of vertices all of whose
pairs `s` have `ω s = b`. -/
lemma exists_of_isContained {k : ℕ} (ω : Pair n → Bool) (b : Bool)
    (hG : (completeGraph (Fin k)).IsContained
      (if b then pairGraph ω else (pairGraph ω)ᶜ)) :
    ∃ R ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∀ s ∈ pairsIn R, ω s = b := by
  classical
  obtain ⟨f⟩ := hG
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.mem_powersetCard, Finset.card_image_of_injective (f := (f : Fin k → Fin n)) _
      (by exact f.injective)]
    exact ⟨Finset.subset_univ _, by simp⟩
  · intro s hs
    simp only [pairsIn, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨a, c, hac, hsac⟩ := Finset.card_eq_two.1 s.2
    have ha : a ∈ Finset.univ.image f := hs (by rw [hsac]; simp)
    have hc : c ∈ Finset.univ.image f := hs (by rw [hsac]; simp)
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hc
    have hxy : x ≠ y := fun h => hac (by rw [h])
    have hadj := f.toHom.map_adj (show (completeGraph (Fin k)).Adj x y from hxy)
    have hs' : s = ⟨{f x, f y}, Finset.card_pair hac⟩ := Subtype.ext hsac
    subst hs'
    cases b with
    | true =>
      simp only [ite_true] at hadj
      obtain ⟨_, h⟩ := hadj
      exact h
    | false =>
      simp only [Bool.false_eq_true, ite_false, compl_adj] at hadj
      obtain ⟨_, hnot⟩ := hadj
      by_contra hω
      exact hnot ⟨hac, by simpa using hω⟩

/-- **Erdős's lower bound for diagonal Ramsey numbers (existence form).** If
`C(n, k) · 2^{1 - C(k, 2)} < 1`, then there is a graph on `n` vertices such that neither it nor
its complement contains `K_k`; equivalently, the edges of `K_n` can be coloured red and blue with
no monochromatic `K_k` (Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes,
2019, Theorem 1.4; P. Erdős, 1947). -/
theorem exists_not_isContained_of_choose_mul_lt (k : ℕ)
    (h : (n.choose k : ℝ) * 2 ^ (1 - (k.choose 2 : ℤ)) < 1) :
    ∃ G : SimpleGraph (Fin n),
      ¬ (completeGraph (Fin k)).IsContained G ∧ ¬ (completeGraph (Fin k)).IsContained Gᶜ := by
  classical
  set half : I := ⟨1 / 2, by norm_num, by norm_num⟩
  set μ := randomSubsetLaw (fun _ : Pair n => half)
  set ks := (Finset.univ : Finset (Fin n)).powersetCard k
  set bad : Set (Pair n → Bool) :=
    (⋃ R ∈ ks, containsEvent (pairsIn R)) ∪ (⋃ R ∈ ks, avoidEvent (pairsIn R))
  have hhalf : ((half : ℝ)) = 1 / 2 := rfl
  have hone : ∀ R ∈ ks, μ.real (containsEvent (pairsIn R)) = (1 / 2) ^ (k.choose 2) := by
    intro R hR
    rw [randomSubsetLaw_real_containsEvent, Finset.prod_const, card_pairsIn,
      (Finset.mem_powersetCard.1 hR).2, hhalf]
  have htwo : ∀ R ∈ ks, μ.real (avoidEvent (pairsIn R)) = (1 / 2) ^ (k.choose 2) := by
    intro R hR
    rw [randomSubsetLaw_real_avoidEvent, Finset.prod_const, card_pairsIn,
      (Finset.mem_powersetCard.1 hR).2, hhalf]
    norm_num
  have hks : (ks.card : ℝ) = n.choose k := by
    simp [ks, Finset.card_powersetCard]
  have hbad : μ.real bad < 1 := by
    calc μ.real bad ≤ μ.real (⋃ R ∈ ks, containsEvent (pairsIn R)) +
          μ.real (⋃ R ∈ ks, avoidEvent (pairsIn R)) := measureReal_union_le _ _
      _ ≤ (∑ R ∈ ks, μ.real (containsEvent (pairsIn R))) +
          ∑ R ∈ ks, μ.real (avoidEvent (pairsIn R)) :=
        add_le_add (measureReal_biUnion_finset_le _ _) (measureReal_biUnion_finset_le _ _)
      _ = (n.choose k : ℝ) * 2 ^ (1 - (k.choose 2 : ℤ)) := by
        rw [Finset.sum_congr rfl hone, Finset.sum_congr rfl htwo, Finset.sum_const,
          nsmul_eq_mul, hks, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_natCast,
          one_div, inv_pow]
        field_simp
        ring
      _ < 1 := h
  have hex : ∃ ω, ω ∉ bad := by
    by_contra hall
    push Not at hall
    have huniv : bad = Set.univ := Set.eq_univ_of_forall hall
    rw [huniv, probReal_univ] at hbad
    exact lt_irrefl _ hbad
  obtain ⟨ω, hω⟩ := hex
  refine ⟨pairGraph ω, fun hG => ?_, fun hG => ?_⟩
  · obtain ⟨R, hR, hall⟩ := exists_of_isContained ω true (by simpa using hG)
    exact hω (Or.inl (Set.mem_biUnion hR (fun s hs => hall s hs)))
  · obtain ⟨R, hR, hall⟩ := exists_of_isContained ω false (by simpa using hG)
    exact hω (Or.inr (Set.mem_biUnion hR (fun s hs => hall s hs)))

/-- **Erdős's bound: the Ramsey property fails.** If `C(n, k) · 2^{1 - C(k, 2)} < 1`, then
`classicalRamsey k k n` fails: some graph on `n` vertices contains no `K_k`, and neither does its
complement (Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019,
Theorem 1.4). -/
theorem not_classicalRamsey_of_choose_mul_lt (k : ℕ)
    (h : (n.choose k : ℝ) * 2 ^ (1 - (k.choose 2 : ℤ)) < 1) :
    ¬ classicalRamsey k k n := by
  intro hR
  obtain ⟨G, h1, h2⟩ := exists_not_isContained_of_choose_mul_lt k h
  rcases hR G with h3 | h3
  · exact h1 h3
  · exact h2 h3

/-- **Monotonicity of the Ramsey property.** If every graph on `N` vertices contains `K_s` or
has `K_t` in its complement, the same holds on every `M ≥ N` vertices (restrict to the first
`N` vertices). -/
theorem classicalRamsey_mono {s t N M : ℕ} (hNM : N ≤ M) (h : classicalRamsey s t N) :
    classicalRamsey s t M := by
  intro G
  let e : Fin N ↪ Fin M := Fin.castLEEmb hNM
  let G' : SimpleGraph (Fin N) := G.comap e
  have hcopy : ∀ {H : SimpleGraph (Fin N)} {K : SimpleGraph (Fin M)},
      (∀ x y, H.Adj x y → K.Adj (e x) (e y)) → ∀ {W : Type} {F : SimpleGraph W},
        F.IsContained H → F.IsContained K := by
    intro H K hHK W F ⟨f⟩
    exact ⟨⟨⟨fun w => e (f w), fun hw => hHK _ _ (f.toHom.map_adj hw)⟩,
      e.injective.comp f.injective⟩⟩
  rcases h G' with h1 | h1
  · exact Or.inl (hcopy (fun x y hxy => hxy) h1)
  · refine Or.inr (hcopy (fun x y hxy => ?_) h1)
    rw [compl_adj] at hxy ⊢
    exact ⟨e.injective.ne hxy.1, hxy.2⟩

/-- **Erdős's lower bound for diagonal Ramsey numbers.** If `C(n, k) · 2^{1 - C(k, 2)} < 1`, then
every `N` with the Ramsey property `classicalRamsey k k N` satisfies `N > n`; that is,
`R(k, k) > n` (Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019,
Theorem 1.4). -/
theorem lt_of_classicalRamsey_of_choose_mul_lt (k : ℕ)
    (h : (n.choose k : ℝ) * 2 ^ (1 - (k.choose 2 : ℤ)) < 1) {N : ℕ}
    (hN : classicalRamsey k k N) : n < N := by
  by_contra hle
  exact not_classicalRamsey_of_choose_mul_lt k h (classicalRamsey_mono (not_lt.1 hle) hN)

/-- **Existence of Ramsey numbers for cliques.** For all `s` and `t` there is an `N` such that every
graph on `N` vertices contains `K_s` or has `K_t` in its complement. It follows from the finite
Ramsey theorem for pairs (`MathlibExt.Combinatorics.Ramsey.ramsey_two_uniform`, F. P. Ramsey,
1930) applied to the 2-colouring of pairs by adjacency, with a monochromatic set of size
`max s t`. Hence the defining set of `graphRamsey s t` is nonempty. -/
theorem exists_classicalRamsey (s t : ℕ) : ∃ N, classicalRamsey s t N := by
  classical
  obtain ⟨N, hN⟩ := MathlibExt.Combinatorics.Ramsey.ramsey_two_uniform
    (r := 2) (k := max s t) (by norm_num)
  refine ⟨N, fun G => ?_⟩
  let φ : Finset (Fin N) → Fin 2 := fun T =>
    if ∃ i j, G.Adj i j ∧ T = {i, j} then 0 else 1
  obtain ⟨S, hS, c, hc⟩ := hN φ
  have hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → φ {i, j} = c := by
    intro i hi j hj hij
    refine hc _ (Finset.mem_powersetCard.2 ⟨?_, Finset.card_pair hij⟩)
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hi
    · rw [Finset.mem_singleton.1 hx]; exact hj
  have hadj0 : ∀ i j, G.Adj i j → φ {i, j} = 0 := fun i j h => by
    simp only [φ]; exact ite_eq_left_iff.2 (fun hn => absurd ⟨i, j, h, rfl⟩ hn)
  have hnadj : ∀ i j, i ≠ j → φ {i, j} = 0 → G.Adj i j := fun i j hij h => by
    simp only [φ] at h
    split_ifs at h with hex
    · obtain ⟨a, b, hab, he⟩ := hex
      have hi : i ∈ ({a, b} : Finset (Fin N)) := he ▸ by simp
      have hj : j ∈ ({a, b} : Finset (Fin N)) := he ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact absurd rfl hij
      · exact hab
      · exact hab.symm
      · exact absurd rfl hij
    · exact absurd h (by decide)
  fin_cases c
  · left
    obtain ⟨S', hS'S, hS'⟩ := Finset.exists_subset_card_eq (show s ≤ S.card by omega)
    refine (not_cliqueFree_iff_top_isContained s).1 (fun hf => hf S' ⟨?_, hS'⟩)
    intro i hi j hj hij
    exact hnadj i j hij (hpair i (hS'S hi) j (hS'S hj) hij)
  · right
    obtain ⟨S', hS'S, hS'⟩ := Finset.exists_subset_card_eq (show t ≤ S.card by omega)
    refine (not_cliqueFree_iff_top_isContained t).1 (fun hf => hf S' ⟨?_, hS'⟩)
    intro i hi j hj hij
    refine (compl_adj G i j).2 ⟨hij, fun h => ?_⟩
    have h1 := hpair i (hS'S hi) j (hS'S hj) hij
    rw [hadj0 i j h] at h1
    exact absurd h1 (by decide)

/-- **Erdős's lower bound, `graphRamsey` form.** If `C(n, k) · 2^{1 - C(k, 2)} < 1`, then
`n < R(k, k)` for the repository's `graphRamsey` (Y. Zhao, *The Probabilistic Method in
Combinatorics*, MIT 18.218 notes, 2019, Theorem 1.4); the least `N` with the Ramsey property
exists by `exists_classicalRamsey`. -/
theorem lt_graphRamsey_of_choose_mul_lt (k : ℕ)
    (h : (n.choose k : ℝ) * 2 ^ (1 - (k.choose 2 : ℤ)) < 1) : n < graphRamsey k k := by
  rw [graphRamsey_eq_sInf]
  exact lt_of_classicalRamsey_of_choose_mul_lt k h (Nat.sInf_mem (exists_classicalRamsey k k))

end MathlibExt.Combinatorics.RamseyErdosLowerBound
