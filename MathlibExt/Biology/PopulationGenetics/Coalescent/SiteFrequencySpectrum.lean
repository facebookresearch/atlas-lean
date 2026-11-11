/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Kingman
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Probability.Independence.Integration

/-!
# The expected site frequency spectrum under the coalescent

The genealogy of a sample of `n` gene copies under Kingman's coalescent consists of the
holding times `T k` (`k = n, …, 2` lineages; `KingmanTimes`, time in units of `2N`
generations) and an independent random tree topology obtained by **random joining**: starting
from `n` singleton blocks, repeatedly merge a pair of blocks chosen uniformly among the
`k.choose 2` pairs. Only the block sizes matter here; `randomJoining` is the law of the
sequence of block-size lists, the `j`-th entry listing the sizes of the `n - j` blocks
present while there are `n - j` lineages. A block of size `i` is a branch subtending `i`
sample copies, so the total length of branches subtending exactly `i` copies is
`L_i = ∑_{k=2}^{n} (number of blocks of size i among k blocks) · T k` (`sfsLength`).

Under neutral infinite-sites mutation at rate `θ / 2` per lineage per unit time (`θ = 4Nu`),
the number `ξ i` of segregating sites whose derived allele is carried by exactly `i` of the
`n` sample copies (the unfolded site frequency spectrum) is, given the genealogy, Poisson with
mean `(θ / 2) L_i`; only the conditional mean is used here. Then `E ξ_i = θ / i` for
`1 ≤ i ≤ n - 1` (Fu 1995). Summing over `i` recovers Watterson's `E S = θ H_{n-1}`
(`MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanTimes.integral_segSites`).

The proof computes the expected number of blocks of size `i` when `k` blocks remain,
`k · C(n-i-1, k-2) / C(n-1, k-1)`, by showing that, up to the order of the blocks, one step of
random joining maps the uniform law on compositions of `n` into `k` positive parts to the
uniform law on compositions into `k - 1` parts. Order-free statistics are handled through
multisets of block sizes; compositions are functions `Fin k → ℕ`. The holding times enter
only through `E T_k = (k.choose 2)⁻¹` and their independence from the topology.

## Main results

* `exists_finset_randomJoining`: the random-joining law has finite support, and the expected
  value of a statistic of the `j`-th block-size list is the `j`-th iterate of `joinStep`.
* `joinStep_iterate_count`: the expected number of blocks of size `i` among `k` blocks.
* `sum_blockCount_mul_inv_choose_two`: the resulting expected length `E L_i = 2 / i`.
* `integral_sfs`: **Fu's expected site frequency spectrum** `E ξ_i = θ / i` for an integrable
  count `ξ i` (integrability matters: Mathlib's conditional expectation and integral of a
  non-integrable function are `0`).

## References

* Y.-X. Fu, *Statistical properties of segregating sites*, Theor. Popul. Biol. 48 (1995),
  172–197.
* R. C. Griffiths and S. Tavaré, *The age of a mutation in a general coalescent tree*,
  Stoch. Models 14 (1998), 273–295.
* J. Wakeley, *Coalescent Theory: An Introduction* (2009).
* R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed. (2008).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum

/-! ### Random joining on block sizes -/

/-- Merge the blocks at positions `i < j` of the block-size list `b`: remove both and append a
block of size `b[i] + b[j]`. -/
def mergeBlocks (b : List ℕ) (i j : ℕ) : List ℕ :=
  ((b.eraseIdx j).eraseIdx i) ++ [b.getD i 0 + b.getD j 0]

/-- The unordered pairs of positions `i < j` among `k` blocks. -/
def blockPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  (range k ×ˢ range k).filter fun p => p.1 < p.2

/-- The **random-joining** law: `randomJoining m b ps` is the probability that `m` steps of
random joining started from the block-size list `b` visit the list of block-size lists `ps`
(starting with `b` itself). Each step merges a pair of blocks chosen uniformly among all
pairs; the process stops once fewer than two blocks remain. -/
noncomputable def randomJoining : ℕ → List ℕ → List (List ℕ) → ℝ
  | 0, b, ps => if ps = [b] then 1 else 0
  | m + 1, b, ps =>
    if (blockPairs b.length).card = 0 then (if ps = [b] then 1 else 0)
    else match ps with
      | [] => 0
      | b' :: rest =>
        if b' = b then
          (∑ p ∈ blockPairs b.length, randomJoining m (mergeBlocks b p.1 p.2) rest) /
            (blockPairs b.length).card
        else 0

/-- The transition operator of random joining acting on a statistic `g` of block-size lists:
the average of `g` over the lists obtained from `b` by merging a uniformly chosen pair of
blocks (`g []` once fewer than two blocks remain). By `exists_finset_randomJoining`, its `j`-th
iterate at `b` is the expectation of `g` at step `j` of random joining started from `b`. -/
noncomputable def joinStep (g : List ℕ → ℝ) (b : List ℕ) : ℝ :=
  if (blockPairs b.length).card = 0 then g []
  else (∑ p ∈ blockPairs b.length, g (mergeBlocks b p.1 p.2)) / (blockPairs b.length).card

/-- The total length of the branches subtending exactly `i` of the `n` sample copies, for the
block-size history `ps` (entry `n - k` lists the block sizes while there are `k` lineages)
and holding times `T`: `∑_{k=2}^{n} #{blocks of size i among k} · T k`. -/
def sfsLength (n i : ℕ) (ps : List (List ℕ)) (T : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Icc 2 n, ((ps.getD (n - k) []).count i : ℝ) * T k

/-! ### Finite support and marginals of the random-joining law -/

private lemma blockPairs_zero : blockPairs 0 = ∅ := by simp [blockPairs]

private lemma joinStep_iterate_nil (j : ℕ) (g : List ℕ → ℝ) : (joinStep^[j] g) [] = g [] := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', joinStep]; simp [blockPairs_zero, ih]

private lemma randomJoining_cons {m : ℕ} {b : List ℕ} (hb : (blockPairs b.length).card ≠ 0)
    (b' : List ℕ) (rest : List (List ℕ)) :
    randomJoining (m + 1) b (b' :: rest) = if b' = b then
      (∑ p ∈ blockPairs b.length, randomJoining m (mergeBlocks b p.1 p.2) rest) /
        (blockPairs b.length).card else 0 := by
  rw [randomJoining]
  simp only [hb, ↓reduceIte]

/-- The random-joining law has finite support, and the expectation of a statistic of the
`j`-th visited list (`j ≤ m`) is the `j`-th iterate of `joinStep`. -/
theorem exists_finset_randomJoining (m : ℕ) (b : List ℕ) :
    ∃ F : Finset (List (List ℕ)), (∀ ps ∉ F, randomJoining m b ps = 0) ∧
      ∀ j ≤ m, ∀ g : List ℕ → ℝ,
        ∑ ps ∈ F, randomJoining m b ps * g (ps.getD j []) = (joinStep^[j] g) b := by
  induction m generalizing b with
  | zero =>
    refine ⟨{[b]}, fun ps hps => ?_, fun j hj g => ?_⟩
    · rw [mem_singleton] at hps
      simp [randomJoining, hps]
    · obtain rfl : j = 0 := by omega
      simp [randomJoining]
  | succ m ih =>
    by_cases hb : (blockPairs b.length).card = 0
    · refine ⟨{[b]}, fun ps hps => ?_, fun j hj g => ?_⟩
      · rw [mem_singleton] at hps
        simp [randomJoining, hb, hps]
      · rw [sum_singleton]
        simp only [randomJoining, hb, ↓reduceIte, one_mul]
        rcases j with _ | j
        · simp
        · rw [Function.iterate_succ_apply', joinStep, joinStep_iterate_nil]
          simp [hb]
    · choose F hF0 hF using fun p : ℕ × ℕ => ih (mergeBlocks b p.1 p.2)
      have hsupp : ∀ rest p, p ∈ blockPairs b.length → rest ∉ F p →
          randomJoining m (mergeBlocks b p.1 p.2) rest = 0 := fun rest p _ h => hF0 p rest h
      refine ⟨((blockPairs b.length).biUnion F).image (List.cons b), fun ps hps => ?_, ?_⟩
      · rcases ps with _ | ⟨b', rest⟩
        · simp [randomJoining, hb]
        · rw [randomJoining_cons hb]
          split_ifs with hb'
          · subst hb'
            rw [div_eq_zero_iff]
            left
            refine sum_eq_zero fun p hp => hF0 p rest fun hr => hps ?_
            exact mem_image.2 ⟨rest, mem_biUnion.2 ⟨p, hp, hr⟩, rfl⟩
          · rfl
      have key : ∀ G : List (List ℕ) → ℝ,
          ∑ ps ∈ ((blockPairs b.length).biUnion F).image (List.cons b),
              randomJoining (m + 1) b ps * G ps =
            (∑ p ∈ blockPairs b.length, ∑ rest ∈ F p,
              randomJoining m (mergeBlocks b p.1 p.2) rest * G (b :: rest)) /
              (blockPairs b.length).card := by
        intro G
        rw [sum_image fun x _ y _ h => List.cons_injective h]
        simp only [randomJoining_cons hb, ↓reduceIte, sum_div, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun p hp => ?_
        rw [← sum_subset (subset_biUnion_of_mem F hp) fun rest _ hr => by
          rw [hsupp rest p hp hr, zero_div, zero_mul]]
        exact sum_congr rfl fun _ _ => div_mul_eq_mul_div _ _ _
      intro j hj g
      rw [key]
      rcases j with _ | j
      · have h1 : ∀ p, ∑ rest ∈ F p, randomJoining m (mergeBlocks b p.1 p.2) rest = 1 := by
          intro p
          simpa using hF p 0 (Nat.zero_le _) fun _ => 1
        simp only [List.getD_cons_zero, ← sum_mul, h1, sum_const, nsmul_eq_mul, mul_one]
        simp only [Function.iterate_zero, id]
        have hc : ((blockPairs b.length).card : ℝ) ≠ 0 := by exact_mod_cast hb
        field_simp
      · simp only [List.getD_cons_succ]
        rw [sum_congr rfl fun p _ => hF p j (by omega) g, Function.iterate_succ_apply',
          joinStep]
        simp [hb]

/-! ### Order-free statistics and uniform compositions -/

private lemma sum_blockPairs_succ {M : Type*} [AddCommMonoid M] (k : ℕ) (F : ℕ × ℕ → M) :
    ∑ p ∈ blockPairs (k + 1), F p =
      ∑ j ∈ range k, F (0, j + 1) + ∑ p ∈ blockPairs k, F (p.1 + 1, p.2 + 1) := by
  simp only [blockPairs, sum_filter, sum_product]
  rw [sum_range_succ']
  simp only [sum_range_succ' _ k, Nat.succ_pos, ↓reduceIte, Nat.lt_irrefl,
    add_zero, Nat.add_lt_add_iff_right, Nat.not_lt_zero]
  rw [add_comm]

private lemma sum_range_getD {M : Type*} [AddCommMonoid M] (l : List ℕ) (f : ℕ → M) :
    ∑ j ∈ range l.length, f (l.getD j 0) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp [add_comm]

private lemma mergeBlocks_cons_zero (a : ℕ) (l : List ℕ) (j : ℕ) :
    mergeBlocks (a :: l) 0 (j + 1) = l.eraseIdx j ++ [a + l.getD j 0] := by
  simp [mergeBlocks]

private lemma mergeBlocks_cons_succ (a : ℕ) (l : List ℕ) (i j : ℕ) :
    mergeBlocks (a :: l) (i + 1) (j + 1) = a :: mergeBlocks l i j := by
  simp [mergeBlocks]

private lemma coe_eraseIdx_append {l : List ℕ} {j : ℕ} (hj : j < l.length) (x : ℕ) :
    ((l.eraseIdx j ++ [x] : List ℕ) : Multiset ℕ) = x ::ₘ (l : Multiset ℕ).erase (l.getD j 0) := by
  rw [Multiset.coe_eq_coe.2 (List.perm_append_singleton x _), ← Multiset.cons_coe,
    Multiset.coe_erase, List.getD_eq_getElem _ _ hj,
    Multiset.coe_eq_coe.2 (List.erase_getElem hj)]

/-- The sum over pairs of positions of a statistic of the merged multiset depends only on the
multiset of block sizes. -/
private lemma sum_blockPairs_eq_powersetCard (l : List ℕ) (G : Multiset ℕ → ℝ) :
    ∑ p ∈ blockPairs l.length, G (mergeBlocks l p.1 p.2) =
      ((Multiset.powersetCard 2 (l : Multiset ℕ)).map
        fun t => G (t.sum ::ₘ ((l : Multiset ℕ) - t))).sum := by
  induction l generalizing G with
  | nil =>
    simp only [blockPairs, List.length_nil, range_zero, empty_product, filter_empty,
      sum_empty, Multiset.coe_nil]
    rw [Multiset.powersetCard_zero_right, Multiset.map_zero, Multiset.sum_zero]
  | cons a l ih =>
    rw [List.length_cons, sum_blockPairs_succ]
    simp only [mergeBlocks_cons_zero, mergeBlocks_cons_succ, ← Multiset.cons_coe]
    rw [ih (fun s => G (a ::ₘ s)), Multiset.powersetCard_cons,
      Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.powersetCard_one,
      Multiset.map_map]
    rw [add_comm]
    congr 1
    · refine congrArg Multiset.sum (Multiset.map_congr rfl fun t ht => ?_)
      rw [Multiset.cons_sub_of_le _ (Multiset.mem_powersetCard.1 ht).1, Multiset.cons_swap]
    · rw [sum_congr rfl fun j hj => by rw [coe_eraseIdx_append (mem_range.1 hj)]]
      rw [sum_range_getD l (fun y => G ((a + y) ::ₘ (l : Multiset ℕ).erase y))]
      rw [Multiset.map_coe, Multiset.sum_coe]
      refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
      simp [Multiset.sub_cons]

/-- A statistic of block-size lists that does not depend on the order of the blocks. -/
private def IsSymm (g : List ℕ → ℝ) : Prop := ∀ l l' : List ℕ, l.Perm l' → g l = g l'

private lemma IsSymm.eq_toList {g : List ℕ → ℝ} (hg : IsSymm g) (l : List ℕ) :
    g l = g (l : Multiset ℕ).toList :=
  hg _ _ (Multiset.coe_eq_coe.1 (Multiset.coe_toList _).symm)

private lemma isSymm_joinStep {g : List ℕ → ℝ} (hg : IsSymm g) : IsSymm (joinStep g) := by
  intro l l' h
  have key : ∀ l : List ℕ, ∑ p ∈ blockPairs l.length, g (mergeBlocks l p.1 p.2) =
      ((Multiset.powersetCard 2 (l : Multiset ℕ)).map
        fun t => g (t.sum ::ₘ ((l : Multiset ℕ) - t)).toList).sum := fun l => by
    rw [← sum_blockPairs_eq_powersetCard l (fun s => g s.toList)]
    exact sum_congr rfl fun p _ => hg.eq_toList _
  unfold joinStep
  rw [key l, key l', h.length_eq, Multiset.coe_eq_coe.2 h]

/-- The multiset of block sizes after merging positions `i < j`. -/
private lemma coe_mergeBlocks {l : List ℕ} {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    (mergeBlocks l i j : Multiset ℕ) = (l.getD i 0 + l.getD j 0) ::ₘ
      (((l : Multiset ℕ).erase (l.getD j 0)).erase (l.getD i 0)) := by
  have hi' : i < (l.eraseIdx j).length := by rw [List.length_eraseIdx_of_lt hj]; omega
  rw [mergeBlocks, coe_eraseIdx_append hi', List.getD_eq_getElem _ _ hi',
    List.getElem_eraseIdx_of_lt _ hij, ← List.getD_eq_getElem _ 0 (by omega : i < l.length),
    ← Multiset.coe_eq_coe.2 (List.erase_getElem hj), ← List.getD_eq_getElem _ 0 hj]
  simp only [Multiset.coe_erase]

/-- Compositions of `N` into `k` positive parts, as functions on `Fin k`. -/
private def comps (N k : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ => Icc 1 N).filter fun c => ∑ t, c t = N

private lemma mem_comps {N k : ℕ} {c : Fin k → ℕ} :
    c ∈ comps N k ↔ (∀ t, 1 ≤ c t) ∧ ∑ t, c t = N := by
  simp only [comps, mem_filter, Fintype.mem_piFinset, mem_Icc]
  constructor
  · rintro ⟨h, hs⟩; exact ⟨fun t => (h t).1, hs⟩
  · rintro ⟨h, hs⟩
    refine ⟨fun t => ⟨h t, ?_⟩, hs⟩
    rw [← hs]
    exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ t)

private lemma sum_comps_comp_perm {M : Type*} [AddCommMonoid M] {N k : ℕ}
    (σ : Equiv.Perm (Fin k)) (F : (Fin k → ℕ) → M) :
    ∑ c ∈ comps N k, F (c ∘ σ) = ∑ c ∈ comps N k, F c := by
  refine sum_nbij' (· ∘ σ) (· ∘ σ.symm) (fun c hc => ?_) (fun c hc => ?_)
    (fun c _ => by ext; simp) (fun c _ => by ext; simp) (fun c _ => rfl)
  · rw [mem_comps] at hc ⊢
    exact ⟨fun t => hc.1 _, by rw [← hc.2]; exact Equiv.sum_comp σ c⟩
  · rw [mem_comps] at hc ⊢
    exact ⟨fun t => hc.1 _, by rw [← hc.2]; exact Equiv.sum_comp σ.symm c⟩

private lemma sum_comps_succ {M : Type*} [AddCommMonoid M] (N m : ℕ)
    (F : ℕ → (Fin m → ℕ) → M) :
    ∑ c ∈ comps N (m + 1), F (c 0) (fun t => c t.succ) =
      ∑ a ∈ Icc 1 N, ∑ r ∈ comps (N - a) m, F a r := by
  rw [sum_sigma']
  refine (sum_nbij' (fun x => Fin.cons x.1 x.2) (fun c => ⟨c 0, fun t => c t.succ⟩)
    (fun x hx => ?_) (fun c hc => ?_) (fun x _ => ?_) (fun c _ => ?_) (fun x _ => ?_)).symm
  · rw [mem_sigma, mem_Icc, mem_comps] at hx
    rw [mem_comps, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    refine ⟨fun t => Fin.cases hx.1.1 (fun t => hx.2.1 t) t, by omega⟩
  · rw [mem_comps, Fin.sum_univ_succ] at hc
    rw [mem_sigma, mem_Icc, mem_comps]
    dsimp only
    exact ⟨⟨hc.1 0, by omega⟩, fun t => hc.1 _, by omega⟩
  · simp
  · exact Fin.cons_self_tail c
  · simp

private lemma IsSymm.ofFn_comp {g : List ℕ → ℝ} (hg : IsSymm g) {k : ℕ} (c : Fin k → ℕ)
    (σ : Equiv.Perm (Fin k)) : g (List.ofFn (c ∘ σ)) = g (List.ofFn c) :=
  hg _ _ (σ.ofFn_comp_perm c)

/-- Merging positions `i < j` of a composition gives (up to order) the same list as merging the
first two positions of the composition relabeled by `swap 0 i * swap 1 j`. -/
private lemma IsSymm.mergeBlocks_eq {g : List ℕ → ℝ} (hg : IsSymm g) {m : ℕ}
    (c : Fin (m + 2) → ℕ) {i j : Fin (m + 2)} (hij : i < j) :
    g (mergeBlocks (List.ofFn c) i j) =
      g (mergeBlocks (List.ofFn (c ∘ (Equiv.swap 0 i * Equiv.swap 1 j))) 0 1) := by
  have hj0 : (0 : Fin (m + 2)) ≠ j := by
    intro h; rw [← h] at hij; exact Fin.not_lt_zero _ hij
  have hji : j ≠ i := hij.ne'
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp
  apply hg
  rw [← Multiset.coe_eq_coe, coe_mergeBlocks hij (by rw [List.length_ofFn]; exact j.isLt),
    coe_mergeBlocks Nat.zero_lt_one (by simp),
    Multiset.coe_eq_coe.2 (Equiv.Perm.ofFn_comp_perm _ c)]
  have e0 : (List.ofFn (c ∘ (Equiv.swap 0 i * Equiv.swap 1 j))).getD 0 0 = c i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp only [Function.comp_apply, Equiv.Perm.coe_mul]
    rw [show (⟨0, by omega⟩ : Fin (m + 2)) = 0 from rfl, Equiv.swap_apply_of_ne_of_ne h01 hj0,
      Equiv.swap_apply_left]
  have e1 : (List.ofFn (c ∘ (Equiv.swap 0 i * Equiv.swap 1 j))).getD 1 0 = c j := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp only [Function.comp_apply, Equiv.Perm.coe_mul]
    rw [show (⟨1, by omega⟩ : Fin (m + 2)) = 1 from rfl, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hj0.symm hji]
  have ei : (List.ofFn c).getD i 0 = c i := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  have ej : (List.ofFn c).getD j 0 = c j := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]
  rw [e0, e1, ei, ej]

private lemma sum_comps_joinStep {g : List ℕ → ℝ} (hg : IsSymm g) (N m : ℕ) :
    ∑ c ∈ comps N (m + 2), joinStep g (List.ofFn c) =
      ∑ c ∈ comps N (m + 2), g ((c 0 + c 1) :: List.ofFn fun t : Fin m => c t.succ.succ) := by
  have hmem : ((0 : ℕ), (1 : ℕ)) ∈ blockPairs (m + 2) := by simp [blockPairs]
  have hcard : (blockPairs (m + 2)).card ≠ 0 := card_ne_zero_of_mem hmem
  have hpair : ∀ p ∈ blockPairs (m + 2),
      ∑ c ∈ comps N (m + 2), g (mergeBlocks (List.ofFn c) p.1 p.2) =
        ∑ c ∈ comps N (m + 2), g (mergeBlocks (List.ofFn c) 0 1) := by
    intro p hp
    simp only [blockPairs, mem_filter, mem_product, mem_range] at hp
    have hlt : (⟨p.1, hp.1.1⟩ : Fin (m + 2)) < ⟨p.2, hp.1.2⟩ := hp.2
    rw [sum_congr rfl fun c _ => hg.mergeBlocks_eq c hlt]
    exact sum_comps_comp_perm _ (fun c => g (mergeBlocks (List.ofFn c) 0 1))
  have hc : ((blockPairs (m + 2)).card : ℝ) ≠ 0 := by exact_mod_cast hcard
  simp only [joinStep, List.length_ofFn, hcard, ↓reduceIte]
  rw [← sum_div, sum_comm, sum_congr rfl hpair, sum_const, nsmul_eq_mul,
    mul_div_cancel_left₀ _ hc]
  refine sum_congr rfl fun c _ => hg _ _ ?_
  simp only [mergeBlocks, List.ofFn_succ]
  simp

private lemma sum_Icc_sum_Icc_add (N : ℕ) (Φ : ℕ → ℝ) :
    ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 (N - a), Φ (a + b) = ∑ s ∈ Icc 1 N, ((s : ℝ) - 1) * Φ s := by
  have inner : ∀ a, ∑ b ∈ Icc 1 (N - a), Φ (a + b) = ∑ s ∈ Icc (a + 1) N, Φ s := by
    intro a
    refine sum_nbij' (a + ·) (· - a) ?_ ?_ ?_ ?_ ?_ <;> intro x hx <;>
      simp only [mem_Icc] at hx ⊢ <;> omega
  rw [sum_congr rfl fun a _ => inner a,
    sum_comm' (t' := Icc 1 N) (s' := fun s => Ico 1 s) (fun a s => by
      simp only [mem_Icc, mem_Ico]; omega)]
  refine sum_congr rfl fun s hs => ?_
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (mem_Icc.1 hs).1]
  simp

private lemma sum_comps_merge01 (N m : ℕ) (h : ℕ → (Fin m → ℕ) → ℝ) :
    ∑ c ∈ comps N (m + 2), h (c 0 + c 1) (fun t => c t.succ.succ) =
      ∑ d ∈ comps N (m + 1), ((d 0 : ℝ) - 1) * h (d 0) (fun t => d t.succ) := by
  have e1 := sum_comps_succ N (m + 1) (fun a r => h (a + r 0) (fun t => r t.succ))
  have e2 := sum_comps_succ N m (fun s r => ((s : ℝ) - 1) * h s r)
  simp only [Fin.succ_zero_eq_one] at e1 e2
  refine e1.trans ?_
  rw [e2]
  simp only [← mul_sum]
  rw [← sum_Icc_sum_Icc_add N (fun s => ∑ r ∈ comps (N - s) m, h s r)]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comps_succ (N - a) m (fun b r => h (a + b) r)]
  refine sum_congr rfl fun b _ => ?_
  rw [Nat.sub_sub]

private lemma sum_comps_mul_sub_one {g : List ℕ → ℝ} (hg : IsSymm g) (N m : ℕ) :
    ((m : ℝ) + 1) * ∑ d ∈ comps N (m + 1), ((d 0 : ℝ) - 1) * g (List.ofFn d) =
      ((N : ℝ) - (m + 1)) * ∑ d ∈ comps N (m + 1), g (List.ofFn d) := by
  have ht : ∀ t : Fin (m + 1), ∑ d ∈ comps N (m + 1), ((d t : ℝ) - 1) * g (List.ofFn d) =
      ∑ d ∈ comps N (m + 1), ((d 0 : ℝ) - 1) * g (List.ofFn d) := by
    intro t
    rw [← sum_comps_comp_perm (Equiv.swap 0 t) (fun d => ((d t : ℝ) - 1) * g (List.ofFn d))]
    refine sum_congr rfl fun d _ => ?_
    simp only [Function.comp_apply, Equiv.swap_apply_right, hg.ofFn_comp]
  calc ((m : ℝ) + 1) * ∑ d ∈ comps N (m + 1), ((d 0 : ℝ) - 1) * g (List.ofFn d)
      = ∑ t : Fin (m + 1), ∑ d ∈ comps N (m + 1), ((d t : ℝ) - 1) * g (List.ofFn d) := by
        rw [sum_congr rfl fun t _ => ht t, sum_const, card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast; ring
    _ = ∑ d ∈ comps N (m + 1), (∑ t : Fin (m + 1), ((d t : ℝ) - 1)) * g (List.ofFn d) := by
        rw [sum_comm]; simp only [sum_mul]
    _ = ∑ d ∈ comps N (m + 1), ((N : ℝ) - (m + 1)) * g (List.ofFn d) := by
        refine sum_congr rfl fun d hd => ?_
        rw [sum_sub_distrib, ← Nat.cast_sum, (mem_comps.1 hd).2]
        simp
    _ = _ := by rw [mul_sum]

/-- One step of random joining maps the uniform law on compositions with `m + 2` parts to the
uniform law on compositions with `m + 1` parts (for order-free statistics). -/
private lemma sum_comps_joinStep_eq {g : List ℕ → ℝ} (hg : IsSymm g) (N m : ℕ) :
    ((m : ℝ) + 1) * ∑ c ∈ comps N (m + 2), joinStep g (List.ofFn c) =
      ((N : ℝ) - (m + 1)) * ∑ d ∈ comps N (m + 1), g (List.ofFn d) := by
  rw [sum_comps_joinStep hg, sum_comps_merge01 N m (fun a r => g (a :: List.ofFn r)),
    ← sum_comps_mul_sub_one hg]
  simp only [← List.ofFn_succ]

private lemma comps_self (N : ℕ) : comps N N = {fun _ => 1} := by
  ext c
  rw [mem_comps, mem_singleton]
  constructor
  · rintro ⟨h1, hs⟩
    have hle : ∀ t ∈ (univ : Finset (Fin N)), (fun _ => 1) t ≤ c t := fun t _ => h1 t
    have := (sum_eq_sum_iff_of_le hle).1 (by simp [hs])
    funext t
    exact (this t (mem_univ t)).symm
  · rintro rfl
    simp

private lemma joinStep_iterate_replicate {N : ℕ} :
    ∀ j, j + 1 ≤ N → ∀ g : List ℕ → ℝ, IsSymm g →
      (joinStep^[j] g) (List.replicate N 1) * ((N - 1).choose j : ℝ) =
        ∑ c ∈ comps N (N - j), g (List.ofFn c)
  | 0, _, g, _ => by
    rw [Nat.sub_zero, comps_self, sum_singleton, List.ofFn_const]
    simp
  | j + 1, hj, g, hg => by
    have ih := joinStep_iterate_replicate (N := N) j (by omega) (joinStep g) (isSymm_joinStep hg)
    obtain ⟨m, hm⟩ : ∃ m, N - j = m + 2 := by exact ⟨N - j - 2, by omega⟩
    have hm' : N - (j + 1) = m + 1 := by omega
    rw [hm] at ih
    rw [hm', Function.iterate_succ_apply]
    have htr := sum_comps_joinStep_eq hg N m
    have hch := Nat.choose_succ_right_eq (N - 1) j
    rw [show N - 1 - j = m + 1 by omega] at hch
    have hch' : ((N - 1).choose (j + 1) : ℝ) * (j + 1) = ((N - 1).choose j : ℝ) * (m + 1) := by
      exact_mod_cast hch
    have hNm : (N : ℝ) - (m + 1) = j + 1 := by
      have : (N : ℝ) = m + 2 + j := by exact_mod_cast (by omega : N = m + 2 + j)
      rw [this]; ring
    rw [hNm] at htr
    set X := (joinStep^[j] (joinStep g)) (List.replicate N 1)
    have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    apply mul_right_cancel₀ hj1
    rw [mul_assoc, hch', ← mul_assoc, ih, mul_comm, htr, mul_comm]

private lemma count_ofFn {k : ℕ} (c : Fin k → ℕ) (i : ℕ) :
    ((List.ofFn c).count i : ℝ) = ∑ t, if c t = i then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ← ih]
    push_cast
    by_cases h : c 0 = i <;> simp [h, add_comm]

private lemma card_comps {N k : ℕ} (hk : 1 ≤ k) (hN : 1 ≤ N) :
    ((comps N k).card : ℝ) = ((N - 1).choose (k - 1) : ℝ) := by
  by_cases hkN : k ≤ N
  · have hone : IsSymm fun _ => (1 : ℝ) := fun _ _ _ => rfl
    have hfix : joinStep (fun _ => (1 : ℝ)) = fun _ => 1 := by
      funext l
      unfold joinStep
      split_ifs with h
      · rfl
      · rw [sum_const, nsmul_eq_mul, mul_one, div_self (by exact_mod_cast h)]
    have := joinStep_iterate_replicate (N := N) (N - k) (by omega) _ hone
    rw [Function.iterate_fixed hfix, show N - (N - k) = k by omega, one_mul] at this
    rw [Nat.choose_symm_of_eq_add (show N - 1 = (k - 1) + (N - k) by omega), this]
    simp
  · have hempty : comps N k = ∅ := by
      refine eq_empty_of_forall_notMem fun c hc => ?_
      rw [mem_comps] at hc
      have : ∑ t : Fin k, 1 ≤ ∑ t, c t := sum_le_sum fun t _ => hc.1 t
      simp [hc.2] at this
      omega
    rw [hempty, Nat.choose_eq_zero_of_lt (by omega)]
    simp

private lemma sum_comps_count {n k i : ℕ} (hk : 2 ≤ k) (hi : 1 ≤ i) (hin : i < n) :
    ∑ c ∈ comps n k, ((List.ofFn c).count i : ℝ) = k * ((n - i - 1).choose (k - 2) : ℝ) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [count_ofFn]
  rw [sum_comm]
  have ht : ∀ t : Fin (k' + 1), ∑ c ∈ comps n (k' + 1), (if c t = i then (1 : ℝ) else 0) =
      ∑ c ∈ comps n (k' + 1), (if c 0 = i then (1 : ℝ) else 0) := by
    intro t
    rw [← sum_comps_comp_perm (Equiv.swap 0 t) (fun c => if c t = i then (1 : ℝ) else 0)]
    simp only [Function.comp_apply, Equiv.swap_apply_right]
  rw [sum_congr rfl fun t _ => ht t, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [sum_comps_succ n k' (fun a _ => if a = i then (1 : ℝ) else 0)]
  simp only [sum_const, nsmul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq' (Icc 1 n) i]
  simp only [mem_Icc, hi, hin.le, and_self, ↓reduceIte]
  rw [card_comps (by omega) (by omega)]
  congr 2

/-- **Expected number of blocks of size `i`** when `k` blocks remain, for random joining
started from `n` singletons: `k · C(n-i-1, k-2) / C(n-1, k-1)` (Fu 1995; Griffiths–Tavaré
1998). Equivalently, a given one of the `k` blocks has size `i` with probability
`C(n-i-1, k-2) / C(n-1, k-1)`. -/
theorem joinStep_iterate_count {n k i : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hi : 1 ≤ i)
    (hin : i < n) :
    (joinStep^[n - k] (fun b => (b.count i : ℝ))) (List.replicate n 1) =
      k * ((n - i - 1).choose (k - 2) : ℝ) / ((n - 1).choose (k - 1) : ℝ) := by
  have hsym : IsSymm fun b => (b.count i : ℝ) := fun l l' h => by simp only [h.count_eq]
  have h := joinStep_iterate_replicate (N := n) (n - k) (by omega) _ hsym
  rw [show n - (n - k) = k by omega, sum_comps_count hk hi hin,
    Nat.choose_symm_of_eq_add (show n - 1 = (n - k) + (k - 1) by omega)] at h
  have hpos : (0 : ℝ) < ((n - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [eq_div_iff hpos.ne', h]

/-! ### The expected branch length `E L_i = 2 / i` -/

private lemma choose_mul_choose_sub (m a r : ℕ) :
    m.choose r * (m - r).choose a = m.choose a * (m - a).choose r := by
  have h1 := Nat.choose_mul (n := m) (k := r + a) (s := r) (by omega)
  have h2 := Nat.choose_mul (n := m) (k := r + a) (s := a) (by omega)
  rw [Nat.add_sub_cancel_left] at h1
  rw [Nat.add_sub_cancel] at h2
  rw [← h1, ← h2, Nat.choose_symm_add]

private lemma sum_range_choose_left (m a : ℕ) :
    ∑ s ∈ range (m + 1), s.choose a = (m + 1).choose (a + 1) := by
  induction m with
  | zero =>
    rcases a with _ | a
    · simp
    · simp [Nat.choose_eq_zero_of_lt (show 1 < a + 1 + 1 by omega)]
  | succ m ih => rw [sum_range_succ, ih, Nat.choose_succ_succ' (m + 1), add_comm]

private lemma sum_choose_div_choose {m a : ℕ} (ha : a ≤ m) :
    ∑ r ∈ range (m + 1), ((m - a).choose r : ℝ) / (m.choose r : ℝ) =
      ((m : ℝ) + 1) / ((a : ℝ) + 1) := by
  have hma : (0 : ℝ) < (m.choose a : ℝ) := by exact_mod_cast Nat.choose_pos ha
  have hterm : ∀ r ∈ range (m + 1), ((m - a).choose r : ℝ) / (m.choose r : ℝ) =
      ((m - r).choose a : ℝ) / (m.choose a : ℝ) := by
    intro r hr
    have hmr : (0 : ℝ) < (m.choose r : ℝ) := by
      exact_mod_cast Nat.choose_pos (by simpa [Nat.lt_succ_iff] using hr)
    rw [div_eq_div_iff hmr.ne' hma.ne']
    have := choose_mul_choose_sub m a r
    exact_mod_cast (by linarith [this] : (m - a).choose r * m.choose a =
      (m - r).choose a * m.choose r)
  rw [sum_congr rfl hterm, ← sum_div]
  have hsum : ∑ r ∈ range (m + 1), ((m - r).choose a : ℝ) = ((m + 1).choose (a + 1) : ℝ) := by
    rw [← sum_range_choose_left]
    push_cast
    rw [← sum_range_reflect (fun s => (s.choose a : ℝ)) (m + 1)]
    refine sum_congr rfl fun r hr => ?_
    congr 2
  rw [hsum, div_eq_div_iff hma.ne' (by positivity)]
  have := Nat.add_one_mul_choose_eq m a
  exact_mod_cast this.symm

/-- Summing the expected block counts against `E T_k = (k.choose 2)⁻¹` gives `2 / i`:
`∑_{k=2}^{n} k C(n-i-1, k-2) / C(n-1, k-1) · (k.choose 2)⁻¹ = 2 / i` for `1 ≤ i < n`. -/
theorem sum_blockCount_mul_inv_choose_two {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    ∑ k ∈ Icc 2 n, k * ((n - i - 1).choose (k - 2) : ℝ) / ((n - 1).choose (k - 1) : ℝ) *
      ((k.choose 2 : ℕ) : ℝ)⁻¹ = 2 / i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
  have ha : a ≤ m := by omega
  have hIcc : Icc 2 (m + 2) = (range (m + 1)).map (addRightEmbedding 2) := by
    ext k; simp only [mem_Icc, mem_map, mem_range, addRightEmbedding_apply]
    constructor
    · intro h; exact ⟨k - 2, by omega, by omega⟩
    · rintro ⟨r, hr, rfl⟩; omega
  rw [hIcc, sum_map]
  simp only [addRightEmbedding_apply]
  have hterm : ∀ r ∈ range (m + 1),
      ((r + 2 : ℕ) : ℝ) * ((m + 2 - (a + 1) - 1).choose (r + 2 - 2) : ℝ) /
        ((m + 2 - 1).choose (r + 2 - 1) : ℝ) * (((r + 2).choose 2 : ℕ) : ℝ)⁻¹ =
      2 / ((m : ℝ) + 1) * (((m - a).choose r : ℝ) / (m.choose r : ℝ)) := by
    intro r hr
    have hr' : r ≤ m := by simpa [Nat.lt_succ_iff] using hr
    simp only [show m + 2 - (a + 1) - 1 = m - a by omega, show r + 2 - 2 = r by omega,
      show m + 2 - 1 = m + 1 by omega, show r + 2 - 1 = r + 1 by omega]
    have hs := Nat.add_one_mul_choose_eq m r
    have hc : (0 : ℝ) < (m.choose r : ℝ) := by exact_mod_cast Nat.choose_pos hr'
    have hs' : ((m + 1).choose (r + 1) : ℝ) = (m + 1) * m.choose r / (r + 1) := by
      rw [eq_div_iff (by positivity)]; exact_mod_cast hs.symm
    have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
    rw [hs', Nat.cast_choose_two]
    push_cast
    rw [show ((r : ℝ) + 2 - 1) = r + 1 by ring]
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum, sum_choose_div_choose ha]
  push_cast
  field_simp

/-! ### The expected site frequency spectrum -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A random block-size history `τ` with the random-joining law takes values a.s. in a finite
set, so every statistic of it is integrable with the expectation given by the law. -/
private lemma integral_comp_randomJoining {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ}
    {b : List ℕ} {τ : Ω → List (List ℕ)} (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining m b ps) {F : Finset (List (List ℕ))}
    (hF : ∀ ps ∉ F, randomJoining m b ps = 0) (g : List (List ℕ) → ℝ) :
    Integrable (fun ω => g (τ ω)) μ ∧
      μ[fun ω => g (τ ω)] = ∑ ps ∈ F, randomJoining m b ps * g ps := by
  have hmeas : ∀ ps, MeasurableSet (τ ⁻¹' {ps}) := fun ps =>
    hτ _ (MeasurableSpace.measurableSet_comap.2 ⟨{ps}, trivial, rfl⟩)
  have hae : ∀ᵐ ω ∂μ, τ ω ∈ F := by
    rw [ae_iff]
    have : {ω | ¬ τ ω ∈ F} = ⋃ ps : {ps // ps ∉ F}, τ ⁻¹' {ps.1} := by
      ext ω; simp
    rw [this]
    refine measure_iUnion_null fun ps => ?_
    rw [← measureReal_eq_zero_iff, hτ_law, hF _ ps.2]
  have heq : (fun ω => g (τ ω)) =ᵐ[μ]
      fun ω => ∑ ps ∈ F, (τ ⁻¹' {ps}).indicator (fun _ => g ps) ω := by
    filter_upwards [hae] with ω hω
    rw [Finset.sum_eq_single_of_mem (τ ω) hω]
    · simp
    · intro ps _ hne
      simp [Set.indicator, Ne.symm hne]
  have hint : ∀ ps ∈ F, Integrable ((τ ⁻¹' {ps}).indicator (fun _ => g ps)) μ :=
    fun ps _ => (integrable_const _).indicator (hmeas ps)
  refine ⟨(integrable_finsetSum _ hint).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun ps _ => ?_
  rw [integral_indicator_const _ (hmeas ps), hτ_law, smul_eq_mul]

/-- **Expected site frequency spectrum** (Fu 1995). Let the genealogy of a sample of `n` gene
copies consist of Kingman holding times `K.T` and an independent block-size history `τ` with
the random-joining law. If, given the genealogy (the σ-algebra generated by `τ` and the
holding times), the number `ξ i` of sites whose derived allele is carried by exactly `i`
copies is integrable and has conditional mean `(θ / 2) L_i` (neutral infinite-sites mutation,
`θ = 4Nu`), then `E ξ_i = θ / i` for `1 ≤ i ≤ n - 1`. (Integrability matters: Mathlib's
conditional expectation of a non-integrable function is `0`.)

Source: Fu (1995); Griffiths & Tavaré (1998). Proves the deferred entry `integral_sfs`. -/
theorem integral_sfs {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (K : KingmanTimes μ n) (hT : ∀ k, Measurable (K.T k))
    {τ : Ω → List (List ℕ)} (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) =
      randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    {θ : ℝ} {ξ : ℕ → Ω → ℝ} (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => K.T k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    μ[ξ i] = θ / i := by
  have hmT : MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi ≤ mΩ :=
    (measurable_pi_iff.2 hT).comap_le
  have hm := sup_le hτ hmT
  obtain ⟨F, hF0, hF⟩ := exists_finset_randomJoining (n - 1) (List.replicate n 1)
  -- the expected length of branches subtending `i` copies
  have hL : μ[fun ω => sfsLength n i (τ ω) (fun k => K.T k ω)] = (2 : ℝ) / i := by
    have hterm : ∀ k ∈ Icc 2 n,
        Integrable (fun ω => (((τ ω).getD (n - k) []).count i : ℝ) * K.T k ω) μ ∧
        μ[fun ω => (((τ ω).getD (n - k) []).count i : ℝ) * K.T k ω] =
          k * ((n - i - 1).choose (k - 2) : ℝ) / ((n - 1).choose (k - 1) : ℝ) *
            ((k.choose 2 : ℕ) : ℝ)⁻¹ := by
      intro k hk
      have hk2 := (mem_Icc.1 hk)
      set X : Ω → ℝ := fun ω => (((τ ω).getD (n - k) []).count i : ℝ)
      obtain ⟨hXi, hXe⟩ := integral_comp_randomJoining hτ hτ_law hF0
        (fun ps => ((ps.getD (n - k) []).count i : ℝ))
      have hind : IndepFun X (K.T k) μ := by
        rw [IndepFun_iff_Indep]
        refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h_indep ?_) ?_
        · rw [show X = (fun ps : List (List ℕ) => ((ps.getD (n - k) []).count i : ℝ)) ∘ τ
            from rfl, ← MeasurableSpace.comap_comp]
          exact MeasurableSpace.comap_mono le_top
        · rw [show K.T k = (fun f : ℕ → ℝ => f k) ∘ (fun ω k => K.T k ω) from rfl,
            ← MeasurableSpace.comap_comp]
          exact MeasurableSpace.comap_mono (measurable_pi_apply k).comap_le
      refine ⟨hind.integrable_mul hXi (K.integrable_T hk), ?_⟩
      change μ[X * K.T k] = _
      rw [hind.integral_mul_eq_mul_integral hXi.aestronglyMeasurable
        (K.integrable_T hk).aestronglyMeasurable, hXe, K.integral_T hk,
        hF (n - k) (by omega) (fun b => (b.count i : ℝ)), joinStep_iterate_count hk2.1 hk2.2 hi hin]
    unfold sfsLength
    rw [integral_finsetSum _ fun k hk => (hterm k hk).1,
      Finset.sum_congr rfl fun k hk => (hterm k hk).2, sum_blockCount_mul_inv_choose_two hi hin]
  have h := setIntegral_condExp hm (hξ_int i)
    (@MeasurableSet.univ Ω (MeasurableSpace.comap τ ⊤ ⊔
      MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi))
  simp only [Measure.restrict_univ] at h
  rw [← h, integral_congr_ae (hξ i), integral_const_mul, hL]
  have : (i : ℝ) ≠ 0 := by positivity
  field_simp

end MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum
