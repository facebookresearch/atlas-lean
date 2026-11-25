/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Counting maximal independent sets

The Balogh–Liu–Sharifzadeh–Treglown bound controls the number of maximal independent sets
of a finite graph in terms of its order and its minimum and maximum degrees.
The Liu–Sharifzadeh bound accounts for the number of edges in excess of the order.
-/

namespace MetaMathlibExt

/-- **Number of maximal independent sets.** For a graph $\Gamma$, $\mathrm{mis}(\Gamma)$ is the
number of maximal independent sets of $\Gamma$, that is, of sets of pairwise non-adjacent
vertices that are not properly contained in another such set; it is $0$ if there are
infinitely many.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, subsection "Maximal independent sets in graphs". -/
@[expose] public noncomputable def maxIndepSetCount {V : Type*} (Γ : SimpleGraph V) : ℕ :=
  {I : Set V | Maximal Γ.IsIndepSet I}.ncard

namespace MaximalIndependentSets

open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

-- Membership in a closed neighborhood.
private def covers (u v : V) : Prop := u = v ∨ G.Adj u v

-- An independent subset of X is maximal precisely when it dominates X.
private noncomputable def family (X : Finset V) : Finset (Finset V) := by
  classical
  exact X.powerset.filter fun I ↦ G.IsIndepSet (I : Set V) ∧
    ∀ v ∈ X, ∃ u ∈ I, covers G u v

private lemma mem_family {X I : Finset V} :
    I ∈ family G X ↔ I ⊆ X ∧ G.IsIndepSet (I : Set V) ∧ ∀ v ∈ X, ∃ u ∈ I, covers G u v := by
  classical
  simp [family]

private lemma count_le_family : maxIndepSetCount G ≤ (family G univ).card := by
  classical
  rw [maxIndepSetCount, ← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard_of_injOn (fun I : Set V ↦ I.toFinset) _ (by
    intro I _ J _ he
    simpa using congrArg (fun t : Finset V ↦ (t : Set V)) he)
  intro I hI
  obtain ⟨hi, hmax⟩ := G.isMaximalIndepSet_iff.mp hI
  refine (mem_family G).2 ⟨subset_univ _, by simpa using hi, fun v _ ↦ ?_⟩
  by_contra! h
  simp only [Set.mem_toFinset, covers, not_or] at h
  have hind : G.IsIndepSet (insert v I) := by
    rw [G.isIndepSet_iff, Set.pairwise_insert]
    exact ⟨hi, fun u hu _ ↦ ⟨fun e ↦ (h u hu).2 e.symm, (h u hu).2⟩⟩
  have hv := hmax _ hind (Set.subset_insert v I) (Set.mem_insert v I)
  exact (h v hv).1 rfl

-- Removing a chosen subset of the independent set leaves a maximal independent set on
-- any remaining vertex set that contains the rest and avoids its closed neighborhoods.
private lemma restrict_family [DecidableEq V] {I X S C : Finset V} (hI : I ∈ family G X)
    (hC : C ⊆ X) (hrest : I \ S ⊆ C) (hsep : ∀ u ∈ S, ∀ v ∈ C, ¬ covers G u v) :
    I \ S ∈ family G C := by
  classical
  obtain ⟨_, hi, hd⟩ := (mem_family G).1 hI
  refine (mem_family G).2 ⟨hrest, hi.mono (by exact_mod_cast sdiff_subset (s := I) (t := S)), ?_⟩
  intro v hv
  obtain ⟨u, hu, huv⟩ := hd v (hC hv)
  exact ⟨u, mem_sdiff.mpr ⟨hu, fun hs ↦ hsep u hs v hv huv⟩, huv⟩

private lemma nat_le_three_rpow (m : ℕ) : (m : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) / 3) := by
  have cube : (m : ℝ) ^ 3 ≤ (3 : ℝ) ^ m := by
    rcases lt_or_ge m 3 with hm | hm
    · interval_cases m <;> norm_num
    · induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ m hm ih =>
        have h : (m : ℝ) + 1 ≤ (4 / 3) * m := by
          have : (3 : ℝ) ≤ m := by exact_mod_cast hm
          linarith
        calc
          ((m + 1 : ℕ) : ℝ) ^ 3 ≤ ((4 / 3) * (m : ℝ)) ^ 3 := by push_cast; gcongr
          _ ≤ 3 * (m : ℝ) ^ 3 := by rw [mul_pow]; gcongr; norm_num
          _ ≤ (3 : ℝ) ^ (m + 1) := by rw [pow_succ (3 : ℝ), mul_comm]; gcongr
  apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 3)).1
  rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ (by norm_num)]
  simpa using cube

-- Branch on a vertex of minimum closed-neighborhood size. Every maximal independent set
-- contains a member of that neighborhood; choosing it removes at least that many vertices.
private lemma moon_moser (X : Finset V) :
    ((family G X).card : ℝ) ≤ (3 : ℝ) ^ ((X.card : ℝ) / 3) := by
  classical
  rcases X.eq_empty_or_nonempty with rfl | hX
  · simpa [family] using card_filter_le (powerset (∅ : Finset V)) _
  let N (v : V) := X.filter (covers G v)
  obtain ⟨v, hv, hmin⟩ := X.exists_min_image (fun v ↦ (N v).card) hX
  have hmem (w : V) (hw : w ∈ X) : w ∈ N w := mem_filter.mpr ⟨hw, Or.inl rfl⟩
  let branch (w : V) := (family G (X \ N w)).image (insert w)
  have hsub : family G X ⊆ (N v).biUnion branch := by
    intro I hI
    obtain ⟨his, hi, hd⟩ := (mem_family G).1 hI
    obtain ⟨w, hw, hwv⟩ := hd v hv
    have hrest : I \ {w} ⊆ X \ N w := by
      intro u hu
      obtain ⟨hui, hne⟩ := mem_sdiff.mp hu
      simp only [mem_singleton] at hne
      exact mem_sdiff.mpr ⟨his hui, fun hn ↦ ((mem_filter.mp hn).2).elim
        (Ne.symm hne) (hi hw hui (Ne.symm hne))⟩
    have hr := restrict_family G hI sdiff_subset hrest (by
      simpa only [mem_singleton, forall_eq] using
        (show ∀ u ∈ X \ N w, ¬ covers G w u from fun u hu h ↦
          (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1, h⟩)))
    refine mem_biUnion.mpr ⟨w, mem_filter.mpr ⟨his hw, hwv.elim
      (fun h ↦ Or.inl h.symm) (fun h ↦ Or.inr h.symm)⟩, ?_⟩
    exact mem_image.mpr ⟨_, hr, by ext; simp; grind⟩
  have hcard (w : V) : (X \ N w).card + (N w).card = X.card :=
    card_sdiff_add_card_eq_card (filter_subset _ _)
  calc
    ((family G X).card : ℝ) ≤ ∑ w ∈ N v, ((branch w).card : ℝ) := by
      exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _w ∈ N v, (3 : ℝ) ^ (((X.card : ℝ) - (N v).card) / 3) := by
      apply sum_le_sum
      intro w hw
      have hwX := (mem_filter.mp hw).1
      have hlt : (X \ N w).card < X.card := by
        have := card_pos.mpr ⟨w, hmem w hwX⟩
        have := hcard w
        omega
      calc
        ((branch w).card : ℝ) ≤ (family G (X \ N w)).card := by exact_mod_cast card_image_le
        _ ≤ _ := moon_moser (X \ N w)
        _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have he : ((X \ N w).card : ℝ) + (N w).card = X.card := by exact_mod_cast hcard w
          have hm : ((N v).card : ℝ) ≤ (N w).card := by exact_mod_cast hmin w hwX
          linarith
    _ = ((N v).card : ℝ) * (3 : ℝ) ^ (((X.card : ℝ) - (N v).card) / 3) := by simp
    _ ≤ (3 : ℝ) ^ ((X.card : ℝ) / 3) := by
      rw [show (X.card : ℝ) / 3 = (N v).card / 3 + ((X.card : ℝ) - (N v).card) / 3 by ring,
        Real.rpow_add (by norm_num)]
      gcongr
      exact nat_le_three_rpow _
termination_by X.card
decreasing_by exact hlt

-- The fingerprint S determines its undominated vertices, and hence the low-degree
-- vertices among them. Only the latter will be needed to complete the independent set.
private noncomputable def available (S : Finset V) : Finset V := by
  classical
  exact univ.filter fun v ↦ ∀ u ∈ S, ¬ covers G u v

private lemma mem_available {v : V} {S : Finset V} :
    v ∈ available G S ↔ ∀ u ∈ S, ¬ covers G u v := by simp [available]

private noncomputable def container [DecidableRel G.Adj] (S : Finset V) (b : ℝ) : Finset V := by
  classical
  exact (available G S).filter fun v ↦ (((available G S).filter (G.Adj v)).card : ℝ) ≤ b

private lemma fingerprint [DecidableEq V] [DecidableRel G.Adj] {I : Finset V}
    (hI : I ∈ family G univ) {b : ℝ} (hb : 0 < b) :
    ∃ S ⊆ I, S.card ≤ ⌊(Fintype.card V : ℝ) / b⌋₊ ∧ I \ S ∈ family G (container G S b) := by
  classical
  -- A fingerprint is affordable if the vertices already removed pay for its size.
  let candidates := I.powerset.filter fun S ↦
    (S.card : ℝ) * b + (available G S).card ≤ Fintype.card V
  have hzero : ∅ ∈ candidates := by
    apply mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), ?_⟩
    simpa using (available G ∅).card_le_univ
  obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image Finset.card ⟨_, hzero⟩
  obtain ⟨hsub, hbudget⟩ := mem_filter.mp hS
  have hSI := mem_powerset.mp hsub
  refine ⟨S, hSI, Nat.le_floor ((le_div_iff₀ hb).2 (by linarith)), ?_⟩
  apply restrict_family G hI (subset_univ _)
  · intro v hv
    obtain ⟨hvI, hvS⟩ := mem_sdiff.mp hv
    have hva : v ∈ available G S := by
      simp only [available, mem_filter, mem_univ, true_and]
      intro u hu
      have hne : u ≠ v := fun e ↦ hvS (e ▸ hu)
      exact fun h ↦ h.elim hne (((mem_family G).1 hI).2.1 (hSI hu) hvI hne)
    apply mem_filter.mpr ⟨hva, ?_⟩
    by_contra! hlarge
    let A := available G S
    have hnext : available G (insert v S) ⊆ A.filter (fun w ↦ ¬ G.Adj v w) := by
      intro w hw
      simp only [available, mem_filter, mem_univ, true_and, forall_mem_insert] at hw
      exact mem_filter.mpr ⟨(mem_available G).mpr hw.2, fun e ↦ hw.1 (Or.inr e)⟩
    have hsplit : ((A.filter (G.Adj v)).card : ℝ) + (A.filter (fun w ↦ ¬ G.Adj v w)).card =
        A.card := by exact_mod_cast A.card_filter_add_card_filter_not (G.Adj v)
    have hle : ((available G (insert v S)).card : ℝ) ≤
        (A.filter (fun w ↦ ¬ G.Adj v w)).card := by exact_mod_cast card_le_card hnext
    have hins : insert v S ∈ candidates := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hvI hSI), ?_⟩
      rw [card_insert_of_notMem hvS]
      push_cast
      change b < ((A.filter (G.Adj v)).card : ℝ) at hlarge
      change (S.card : ℝ) * b + A.card ≤ _ at hbudget
      linarith
    simpa [card_insert_of_notMem hvS] using hmax _ hins
  · intro u hu v hv
    exact (mem_available G).mp (mem_filter.mp hv).1 u hu

-- Count the edges from C to its complement in both directions.
private lemma container_exponent [DecidableRel G.Adj] {k b : ℝ} (hk : 1 ≤ k)
    (hΔ : (G.maxDegree : ℝ) ≤ k * G.minDegree) (hb : 0 < b)
    (hsq : b ^ 2 = G.minDegree) (S : Finset V) :
    ((container G S b).card : ℝ) / 3 ≤ k / (k + 1) * (Fintype.card V / 3) +
      2 * Fintype.card V / (3 * b) := by
  classical
  let C := container G S b
  have hdeg (v : V) : (univ.filter (G.Adj v)).card = G.degree v := by
    rw [← G.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
  have lower (v : V) (hv : v ∈ C) :
      (G.minDegree : ℝ) - b ≤ (Cᶜ.bipartiteAbove G.Adj v).card := by
    have hsmall := (mem_filter.mp hv).2
    have hle : (C.filter (G.Adj v)).card ≤ ((available G S).filter (G.Adj v)).card :=
      card_le_card (filter_subset_filter _ (filter_subset _ _))
    have he : (C.filter (G.Adj v)).card + (Cᶜ.filter (G.Adj v)).card = G.degree v := by
      have hd : Disjoint (C.filter (G.Adj v)) (Cᶜ.filter (G.Adj v)) :=
        (show Disjoint C Cᶜ from disjoint_compl_right).mono (filter_subset _ _) (filter_subset _ _)
      rw [← hdeg, ← card_union_of_disjoint hd, ← filter_union, sup_compl_eq_top]
      rfl
    change _ ≤ ((Cᶜ.filter (G.Adj v)).card : ℝ)
    have hmin := G.minDegree_le_degree v
    have hed := Nat.cast_le (α := ℝ).mpr (hmin.trans_eq he.symm)
    push_cast at hed
    linarith [Nat.cast_le (α := ℝ).mpr hle]
  have upper (v : V) (_ : v ∈ Cᶜ) :
      ((C.bipartiteBelow G.Adj v).card : ℝ) ≤ k * G.minDegree := by
    refine le_trans ?_ hΔ
    exact_mod_cast (show (C.bipartiteBelow G.Adj v).card ≤ G.maxDegree from
      (card_le_card (t := univ.filter (G.Adj v)) (fun w hw ↦
        mem_filter.mpr ⟨mem_univ _, ((mem_bipartiteBelow G.Adj).mp hw).2.symm⟩)).trans
        ((hdeg v).le.trans (G.degree_le_maxDegree v)))
  have hcut := card_nsmul_le_card_nsmul G.Adj lower upper
  simp only [nsmul_eq_mul] at hcut
  have hcompl : (Cᶜ.card : ℝ) + C.card = Fintype.card V := by
    exact_mod_cast C.card_compl_add_card
  have hsize : (C.card : ℝ) ≤ Fintype.card V := by exact_mod_cast C.card_le_univ
  have key : (C.card : ℝ) * ((k + 1) * b ^ 2) ≤
      k * Fintype.card V * b ^ 2 + Fintype.card V * b := by
    rw [hsq]
    rw [show (Cᶜ.card : ℝ) = Fintype.card V - C.card by linarith] at hcut
    nlinarith [mul_le_mul_of_nonneg_right hsize hb.le]
  change (C.card : ℝ) / 3 ≤ _
  have hk' : 0 < k + 1 := by linarith
  apply (mul_le_mul_iff_of_pos_right (show 0 < 3 * ((k + 1) * b ^ 2) by positivity)).mp
  field_simp
  ring_nf at key ⊢
  nlinarith [show 0 ≤ k * (Fintype.card V : ℝ) * b by positivity,
    show 0 ≤ (Fintype.card V : ℝ) * b by positivity]

private lemma count_pos_degree [DecidableRel G.Adj] {k b : ℝ} (hk : 1 ≤ k)
    (hΔ : (G.maxDegree : ℝ) ≤ k * G.minDegree) (hb : 0 < b) (hsq : b ^ 2 = G.minDegree) :
    (maxIndepSetCount G : ℝ) ≤
      (∑ i ∈ range (⌊(Fintype.card V : ℝ) / b⌋₊ + 1), ((Fintype.card V).choose i : ℝ)) *
        (3 : ℝ) ^ (k / (k + 1) * (Fintype.card V / 3) + 2 * Fintype.card V / (3 * b)) := by
  classical
  let sizes := range (⌊(Fintype.card V : ℝ) / b⌋₊ + 1)
  let seeds := sizes.biUnion fun i ↦ (univ : Finset V).powersetCard i
  let completions (S : Finset V) := (family G (container G S b)).image (S ∪ ·)
  let B := (3 : ℝ) ^ (k / (k + 1) * (Fintype.card V / 3) + 2 * Fintype.card V / (3 * b))
  have hcover : family G univ ⊆ seeds.biUnion completions := by
    intro I hI
    obtain ⟨S, hSI, hcard, hrest⟩ := fingerprint G hI hb
    have hS : S ∈ seeds := mem_biUnion.mpr ⟨S.card, mem_range.mpr (by omega),
      mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩
    exact mem_biUnion.mpr ⟨S, hS, mem_image.mpr ⟨_, hrest, by
      rw [union_comm, sdiff_union_of_subset hSI]⟩⟩
  have hseeds : (seeds.card : ℝ) ≤ ∑ i ∈ sizes, ((Fintype.card V).choose i : ℝ) := by
    exact_mod_cast (card_biUnion_le (s := sizes) (t := fun i ↦ (univ : Finset V).powersetCard i)
      |>.trans_eq (by simp))
  calc
    (maxIndepSetCount G : ℝ) ≤ (family G univ).card := by exact_mod_cast count_le_family G
    _ ≤ ∑ S ∈ seeds, ((completions S).card : ℝ) := by
      exact_mod_cast (card_le_card hcover).trans card_biUnion_le
    _ ≤ ∑ _S ∈ seeds, B := by
      refine sum_le_sum fun S _ ↦ ?_
      calc
        ((completions S).card : ℝ) ≤ (family G (container G S b)).card := by
          exact_mod_cast card_image_le
        _ ≤ _ := moon_moser G _
        _ ≤ B := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (container_exponent G hk hΔ hb hsq S)
    _ = seeds.card * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hseeds (Real.rpow_nonneg (by norm_num) _)

end MaximalIndependentSets

open MaximalIndependentSets

/-- **Balogh–Liu–Sharifzadeh–Treglown bound.** Let $k \ge 1$ be a real number and let $\Gamma$
be a finite graph with $n$ vertices, minimum degree $\delta(\Gamma)$ and maximum degree
$\Delta(\Gamma) \le k\,\delta(\Gamma)$, and put $b = \sqrt{\delta(\Gamma)}$. Then the number
$\mathrm{mis}(\Gamma)$ of maximal independent sets of $\Gamma$ satisfies
$\mathrm{mis}(\Gamma) \le \bigl(\sum_{0 \le i \le n/b} \binom{n}{i}\bigr) \cdot
3^{\frac{k}{k+1} \cdot \frac{n}{3} + \frac{2n}{3b}}$, where $n/b$ and $2n/(3b)$ are read as $0$
when $\delta(\Gamma) = 0$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 5 (`integers-2026-A97-lem-5`). -/
public theorem maxIndepSetCount_le_of_maxDegree_le {V : Type*} [Fintype V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {k : ℝ} (hk : 1 ≤ k)
    (hΔ : (Γ.maxDegree : ℝ) ≤ k * Γ.minDegree) :
    (maxIndepSetCount Γ : ℝ) ≤
      (∑ i ∈ Finset.range (⌊(Fintype.card V : ℝ) / Real.sqrt Γ.minDegree⌋₊ + 1),
          ((Fintype.card V).choose i : ℝ)) *
        (3 : ℝ) ^ (k / (k + 1) * (Fintype.card V / 3) +
          2 * Fintype.card V / (3 * Real.sqrt Γ.minDegree)) := by
  by_cases h : Γ.minDegree = 0
  · have hz : Γ.maxDegree = 0 := by simpa [h] using hΔ
    have he := Γ.maxDegree_eq_zero_iff.mp hz
    have hi : Γ.IsIndepSet Set.univ := by simp [he, SimpleGraph.isIndepSet_iff, Set.Pairwise]
    have hcount : maxIndepSetCount Γ ≤ 1 := by
      apply (Set.ncard_le_ncard (t := {Set.univ}) _).trans_eq (Set.ncard_singleton _)
      intro I hI
      exact Set.mem_singleton_iff.mpr (Set.eq_univ_of_univ_subset
        ((Γ.isMaximalIndepSet_iff.mp hI).2 _ hi (Set.subset_univ I)))
    simp only [h, Nat.cast_zero, Real.sqrt_zero, div_zero, Nat.floor_zero, zero_add,
      Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_zero, add_zero]
    exact (Nat.cast_le_one.mpr hcount).trans (Real.one_le_rpow (by norm_num) (by positivity))
  · exact count_pos_degree Γ hk hΔ (Real.sqrt_pos.2 (by positivity)) (Real.sq_sqrt (by positivity))

namespace MaximalIndependentSets.EdgeCount

open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]

private def neighbors (X : Finset V) (v : V) := G.neighborFinset v ∩ X

private def edges (X : Finset V) := G.edgeFinset ∩ X.sym2

private lemma mem_neighbors {X : Finset V} {v w : V} :
    w ∈ neighbors G X v ↔ G.Adj v w ∧ w ∈ X := by simp [neighbors]

private lemma mem_edges {X : Finset V} {a b : V} :
    s(a, b) ∈ edges G X ↔ G.Adj a b ∧ a ∈ X ∧ b ∈ X := by simp [edges]

-- Handshaking on the induced subgraph supplies the base case of the induction.
private lemma edges_le_card_of_degree_le_two (X : Finset V)
    (h : ∀ v ∈ X, (neighbors G X v).card ≤ 2) : (edges G X).card ≤ X.card := by
  let : Fintype (X : Set V) := Subtype.fintype (· ∈ (X : Set V))
  let H := G.induce (X : Set V)
  have hd (v : X) : H.degree v ≤ 2 := by
    have he := congrArg Finset.card (G.map_neighborFinset_induce (s := (X : Set V)) v)
    simp only [card_map, SimpleGraph.card_neighborFinset_eq_degree, toFinset_coe] at he
    exact he.le.trans (h v v.property)
  have he := congrArg Finset.card (G.map_edgeFinset_induce (s := (X : Set V)))
  have hs := H.sum_degrees_eq_twice_card_edges
  have hb : ∑ v, H.degree v ≤ ∑ _v : X, 2 := sum_le_sum fun v _ ↦ hd v
  simp only [sum_const, card_univ, Fintype.card_coe, smul_eq_mul] at hb
  simp only [card_map, toFinset_coe] at he
  change H.edgeFinset.card = (edges G X).card at he
  omega

-- All edges lost by deleting the closed neighborhood touch an open neighbor:
-- even an edge through the central vertex has its other endpoint there.
private lemma deletion_edges (X : Finset V) (v : V)
    (hm : ∀ w ∈ X, (neighbors G X w).card ≤ (neighbors G X v).card) :
    (edges G X).card ≤ (edges G (X.erase v)).card + (neighbors G X v).card ∧
    (edges G X).card ≤ (edges G (X \ insert v (neighbors G X v))).card +
      (neighbors G X v).card ^ 2 := by
  let N := neighbors G X v
  let star (w : V) := (neighbors G X w).image (fun u ↦ s(w, u))
  have mem_star {w u : V} (hw : G.Adj w u) (hu : u ∈ X) : s(w, u) ∈ star w :=
    mem_image.mpr ⟨u, (mem_neighbors G).2 ⟨hw, hu⟩, rfl⟩
  have single : edges G X ⊆ edges G (X.erase v) ∪ star v := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      obtain ⟨hab, ha, hb⟩ := (mem_edges G).1 he
      by_cases hav : a = v
      · subst a
        exact mem_union_right _ (mem_star hab hb)
      by_cases hbv : b = v
      · subst b
        rw [Sym2.eq_swap]
        exact mem_union_right _ (mem_star hab.symm ha)
      exact mem_union_left _ ((mem_edges G).2 ⟨hab, mem_erase.mpr ⟨hav, ha⟩,
        mem_erase.mpr ⟨hbv, hb⟩⟩)
  have closed : edges G X ⊆ edges G (X \ insert v N) ∪ N.biUnion star := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      obtain ⟨hab, ha, hb⟩ := (mem_edges G).1 he
      by_cases han : a ∈ N
      · exact mem_union_right _ (mem_biUnion.mpr ⟨a, han, mem_star hab hb⟩)
      by_cases hbn : b ∈ N
      · rw [Sym2.eq_swap]
        exact mem_union_right _ (mem_biUnion.mpr ⟨b, hbn, mem_star hab.symm ha⟩)
      have hav : a ≠ v := fun e ↦ hbn ((mem_neighbors G).2 ⟨e ▸ hab, hb⟩)
      have hbv : b ≠ v := fun e ↦ han ((mem_neighbors G).2 ⟨e ▸ hab.symm, ha⟩)
      exact mem_union_left _ ((mem_edges G).2 ⟨hab, by simp [ha, hav, han],
        by simp [hb, hbv, hbn]⟩)
  constructor
  · exact (card_le_card single).trans ((card_union_le _ _).trans (by
      gcongr
      exact card_image_le))
  · have hstars : (N.biUnion star).card ≤ N.card ^ 2 := calc
        _ ≤ ∑ w ∈ N, (star w).card := card_biUnion_le
        _ ≤ ∑ _w ∈ N, N.card := sum_le_sum fun w hw ↦
          card_image_le.trans (hm w ((mem_neighbors G).1 hw).2)
        _ = _ := by simp [sq]
    exact (card_le_card closed).trans ((card_union_le _ _).trans (Nat.add_le_add_left hstars _))

-- Partition according to whether the independent set contains v. In each part,
-- restricting to the undeleted vertices determines the original set.
private lemma deletion_family (X : Finset V) (v : V) :
    (family G X).card ≤ (family G (X.erase v)).card +
      (family G (X \ insert v (neighbors G X v))).card := by
  classical
  let R := X \ insert v (neighbors G X v)
  have hs : family G X ⊆ family G (X.erase v) ∪ (family G R).image (insert v) := by
    intro I hI
    obtain ⟨his, hi, hd⟩ := (mem_family G).1 hI
    by_cases hv : v ∈ I
    · apply mem_union_right
      have hr : I \ {v} ⊆ R := by
        intro w hw
        obtain ⟨hwI, hne⟩ := mem_sdiff.mp hw
        simp only [mem_singleton] at hne
        have hna := hi hv hwI (Ne.symm hne)
        simp [R, his hwI, hne, mem_neighbors, hna]
      have hsep : ∀ u ∈ ({v} : Finset V), ∀ w ∈ R, ¬ covers G u w := by
        simp only [mem_singleton, forall_eq]
        intro w hw h
        obtain ⟨hwX, hnot⟩ := mem_sdiff.mp hw
        apply hnot
        exact h.elim (fun e ↦ e ▸ mem_insert_self _ _) fun e ↦
          mem_insert_of_mem ((mem_neighbors G).2 ⟨e, hwX⟩)
      exact mem_image.mpr ⟨_, restrict_family G hI sdiff_subset hr hsep, by ext; simp; grind⟩
    · apply mem_union_left
      exact (mem_family G).2 ⟨fun w hw ↦ mem_erase.mpr ⟨fun e ↦ hv (e ▸ hw), his hw⟩,
        hi, fun w hw ↦ hd w (mem_erase.mp hw).2⟩
  exact (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_left card_image_le _))

-- Raising to the 39th power reduces the branching inequalities to rational arithmetic.
private lemma rpow_neg_div_le (a : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (h : 1 ≤ (3 : ℝ) ^ a * b ^ 39) : (3 : ℝ) ^ (-(a : ℝ) / 39) ≤ b := by
  apply le_of_pow_le_pow_left₀ (n := 39) (by decide) hb
  rw [← Real.rpow_mul_natCast (by norm_num),
    show -(a : ℝ) / 39 * (39 : ℕ) = -(a : ℝ) by push_cast; ring,
    Real.rpow_neg (by norm_num), Real.rpow_natCast]
  exact (inv_le_iff_one_le_mul₀' (by positivity)).2 h

-- At degree three the two branches lose at least 11/39 and 47/39 in the exponent.
-- From degree four onward, the coarser losses 10/39 and 50/39 suffice.
private lemma branch_factors (d : ℕ) (hd : 3 ≤ d) (c : ℝ) (hc : 0 ≤ c)
    (hdc : d * c ≤ 1 / 13) :
    (3 : ℝ) ^ (-(1 / 3) + (d - 1) * c) +
      (3 : ℝ) ^ (-(d + 1) / 3 + ((d : ℝ) ^ 2 - (d + 1)) * c) ≤ 1 := by
  by_cases he : d = 3
  · subst d
    have h₁ := rpow_neg_div_le 11 (b := 7336 / 10000) (by norm_num) (by norm_num)
    have h₂ := rpow_neg_div_le 47 (b := 2661 / 10000) (by norm_num) (by norm_num)
    refine (add_le_add ((Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_).trans h₁)
      ((Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_).trans h₂)).trans (by norm_num)
    all_goals norm_num at hdc ⊢; linarith
  · have hd' : (4 : ℝ) ≤ d := by exact_mod_cast (show 4 ≤ d by omega)
    have hsq := mul_le_mul_of_nonneg_left hdc (Nat.cast_nonneg (α := ℝ) d)
    have h₁ := rpow_neg_div_le 10 (b := 7546 / 10000) (by norm_num) (by norm_num)
    have h₂ := rpow_neg_div_le 50 (b := 2446 / 10000) (by norm_num) (by norm_num)
    refine (add_le_add ((Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_).trans h₁)
      ((Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_).trans h₂)).trans (by norm_num)
    · push_cast
      linarith
    · push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hc]

-- For c = 1/(13Δ), charge c for each edge in excess of the vertex count.
private noncomputable def exponent (X : Finset V) (c : ℝ) : ℝ :=
  X.card / 3 - ((edges G X).card - (X.card : ℝ)) * c

private lemma count_le (X : Finset V) (c : ℝ) (hc : 0 ≤ c)
    (hΔ : G.maxDegree * c ≤ 1 / 13) :
    ((family G X).card : ℝ) ≤ (3 : ℝ) ^ exponent G X c := by
  classical
  by_cases hs : (edges G X).card ≤ X.card
  · refine (moon_moser G X).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    unfold exponent
    have h : ((edges G X).card : ℝ) ≤ X.card := by exact_mod_cast hs
    linarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hc]
  have hX : X.Nonempty := by
    by_contra! h
    simp [h, edges] at hs
  obtain ⟨v, hv, hm⟩ := X.exists_max_image (fun w ↦ (neighbors G X w).card) hX
  let N := neighbors G X v
  let d := N.card
  have hd : 3 ≤ d := by
    by_contra! h
    exact hs (edges_le_card_of_degree_le_two G X fun w hw ↦
      (hm w hw).trans (show d ≤ 2 by omega))
  have hdΔ : d ≤ G.maxDegree :=
    (card_le_card (inter_subset_left : N ⊆ G.neighborFinset v)).trans (G.degree_le_maxDegree v)
  have hdc : (d : ℝ) * c ≤ 1 / 13 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hdΔ) hc).trans hΔ
  let A := X.erase v
  let B := X \ insert v N
  have hA : A.card + 1 = X.card := card_erase_add_one hv
  have hB : B.card + (d + 1) = X.card := by
    have hsub : insert v N ⊆ X := insert_subset hv inter_subset_right
    have he := card_sdiff_add_card_eq_card hsub
    have hnot : v ∉ N := by simp [N, mem_neighbors]
    simpa [B, d, card_insert_of_notMem hnot] using he
  have hltA : A.card < X.card := by omega
  have hltB : B.card < X.card := by omega
  obtain ⟨hea, heb⟩ := deletion_edges G X v hm
  have hEa : ((edges G X).card : ℝ) ≤ (edges G A).card + d := by exact_mod_cast hea
  have hEb : ((edges G X).card : ℝ) ≤ (edges G B).card + (d : ℝ) ^ 2 := by exact_mod_cast heb
  have hVa : (A.card : ℝ) + 1 = X.card := by exact_mod_cast hA
  have hVb : (B.card : ℝ) + ((d : ℝ) + 1) = X.card := by exact_mod_cast hB
  have boundA : exponent G A c ≤ exponent G X c + (-(1 / 3) + (d - 1) * c) := by
    unfold exponent
    nlinarith [mul_le_mul_of_nonneg_right hEa hc, congrArg (· * c) hVa]
  have boundB : exponent G B c ≤ exponent G X c +
      (-(d + 1) / 3 + ((d : ℝ) ^ 2 - (d + 1)) * c) := by
    unfold exponent
    nlinarith [mul_le_mul_of_nonneg_right hEb hc, congrArg (· * c) hVb]
  calc
    ((family G X).card : ℝ) ≤ (family G A).card + ((family G B).card : ℝ) := by
      exact_mod_cast deletion_family G X v
    _ ≤ _ := add_le_add (count_le A c hc hΔ) (count_le B c hc hΔ)
    _ ≤ _ := add_le_add (Real.rpow_le_rpow_of_exponent_le (by norm_num) boundA)
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) boundB)
    _ ≤ _ := by
      simp only [Real.rpow_add (by norm_num : (0 : ℝ) < 3) (exponent G X c), ← mul_add]
      exact mul_le_of_le_one_right (by positivity) (branch_factors d hd c hc hdc)
termination_by X.card
decreasing_by all_goals assumption

end MaximalIndependentSets.EdgeCount

/-- **Liu–Sharifzadeh stability bound.** Let $\Gamma$ be a graph with $n$ vertices, $n + k$
edges for an integer $k$, and maximum degree $\Delta \ge 1$. Then the number
$\mathrm{mis}(\Gamma)$ of maximal independent sets of $\Gamma$ satisfies
$\mathrm{mis}(\Gamma) \le 3^{\Delta/13} \cdot 3^{n/3 - k/(13\Delta)}$.

Source: Nathanaël Hassler and Andrew Treglown, *Notes on Sum-Free Sets in Abelian Groups*,
INTEGERS 26 (2026), Article A97, Lemma 7 (`integers-2026-A97-lem-7`). -/
public theorem maxIndepSetCount_le_of_edge_count {V : Type*} [Fintype V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (k : ℤ) {Δ : ℕ} (hΔpos : 1 ≤ Δ)
    (hΔ : Γ.maxDegree = Δ) (he : (Γ.edgeFinset.card : ℤ) = Fintype.card V + k) :
    (maxIndepSetCount Γ : ℝ) ≤
      (3 : ℝ) ^ ((Δ : ℝ) / 13) * (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3 - k / (13 * Δ)) := by
  classical
  let c : ℝ := 1 / (13 * Δ)
  have hpos : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hΔc : (Γ.maxDegree : ℝ) * c ≤ 1 / 13 := by
    rw [hΔ]
    exact le_of_eq (by dsimp [c]; field_simp)
  have hcount := MaximalIndependentSets.EdgeCount.count_le Γ Finset.univ c (by positivity) hΔc
  have he' : (Γ.edgeFinset.card : ℝ) = Fintype.card V + (k : ℝ) := by exact_mod_cast he
  simp only [MaximalIndependentSets.EdgeCount.exponent, MaximalIndependentSets.EdgeCount.edges,
    Finset.sym2_univ, Finset.inter_univ, Finset.card_univ, he', add_sub_cancel_left] at hcount
  calc
    (maxIndepSetCount Γ : ℝ) ≤ (family Γ Finset.univ).card := by exact_mod_cast count_le_family Γ
    _ ≤ _ := hcount
    _ ≤ _ := by
      rw [← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp [c]
      rw [mul_one_div]
      linarith

end MetaMathlibExt
