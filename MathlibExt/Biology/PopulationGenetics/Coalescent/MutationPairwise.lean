/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Mutation
public import MathlibExt.Biology.PopulationGenetics.Coalescent.Topology
import MathlibExt.Probability.Distributions.ExponentialMoments
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Pairwise differences under Poisson mutation marking

`Mutation.lean` derives the segregating-site moments from infinite-sites Poisson mutation on a
Kingman genealogy, but leaves the pairwise hypotheses of `integral_meanPairDiff` open: the number
of differences between two sampled genes depends on which branches separate them, i.e. on the
tree topology, which `KingmanTimes` does not record. This file adds the topology as a ranked
labeled history (`RankedHistory`, `Topology.lean`) and discharges those hypotheses from
`kingmanMutationKernel`.

* **Which branches a pair shares.** Branch `⟨k, j⟩` (lineage `j` while there are `k` lineages)
  lies above the block `branchBlock h ⟨k, j⟩` of sampled genes. For a pair `s = {a, b}`, the
  branches above exactly one of the two genes form the path between them through their MRCA
  (`pairPath`); the branches above both are shared, from the MRCA to the root (`pairShared`). In
  every epoch during which `a` and `b` are in different lineages (`PairApart`) exactly two
  branches separate them and none is shared; after they coalesce none separates them and exactly
  one is shared (`card_pairPath_epoch`, `card_pairShared_epoch`). Hence the path has length
  `2 τ_s`, with `τ_s` the pair's coalescence time (`pairCoalTime`, `sum_pairPath_branchLength`).
  These rest on the partition invariant of `blocksAfter` (`blocksAfter_spec`) and the one-step
  recursion: two genes in lineages `p ≠ q` coalesce at a step iff that step merges exactly
  lineages `p` and `q` (`pairApart_succ_iff`).
* **Pairwise differences.** Under infinite sites the two sequences of `s` differ exactly at the
  mutations on `pairPath` (`pairDiff`). If the branch counts have conditional law
  `kingmanMutationKernel` given the epoch lengths and the history
  (`kingmanTreeMutationKernel`), then `D_s` is integrable and `E[D_s | genealogy] = θ τ_s` a.s.
  (`KingmanTimes.integrable_pairDiff_of_mutation`, `KingmanTimes.condExp_pairDiff_of_mutation`).
  These are the hypotheses `hDint`, `hD` of `integral_meanPairDiff`, so `E π = θ` follows once
  the coalescence times are `Exp(1)` (`KingmanTimes.integral_meanPairDiff_of_mutation`); and
  `E[D_s] = θ E[τ_s]` in general (`KingmanTimes.integral_pairDiff_of_mutation`).
* **Random joining.** Under `randomJoining n`, genes `a ≠ b` are still apart after `t ≤ n - 2`
  events with probability `(n - t - 1)(n + 1) / ((n - t + 1)(n - 1))`: by double counting,
  exactly one of the `C(n - t, 2)` choices at step `t` merges them (`card_pairApart_succ`,
  `card_pairApart_div`). During the epoch with `k = n - t` lineages this is
  `pairSeparateProb n k` of `Topology.lean` (`integral_pairApart_randomJoining`).
* **A concrete model.** With independent exponential epochs and random-joining topology
  (`kingmanGenealogyMeasure`, `kingmanTreeMutationMeasure`), `E τ_s = 1`
  (`integral_pairCoalTime_kingmanGenealogyMeasure`, by `sum_pairSeparateProb_div_choose`), hence
  `E[D_s] = θ` for every pair and Tajima's `E π = θ` with no remaining hypotheses
  (`integral_pairDiff_kingmanTreeMutationMeasure`,
  `integral_meanPairDiff_kingmanTreeMutationMeasure`).
* **The law `τ_s ~ Exp(1)`.** In the same model the coalescence time of every pair is `Exp(1)`
  (`hasLaw_pairCoalTime_kingmanGenealogyMeasure`,
  `hasLaw_pairCoalTime_kingmanTreeMutationMeasure`): the hypothesis `hτ` of
  `integral_meanPairDiff`, so every hypothesis of `KingmanTimes.integral_meanPairDiff_of_mutation`
  holds in this model. The pair is apart during an upward-closed set of epochs `k ≥ M`;
  conditionally on the topology the characteristic function of `τ_s` is
  `∏_{k ≥ M} C(k, 2) / (C(k, 2) - i u)`, which telescopes into a sum linear in the indicators of
  `PairApart` (`prod_ite_eq_sum_of_threshold`). Averaging with `pairSeparateProb` and summing
  (`sum_pairRatio_prod`) gives `1 / (1 - i u)`, the transform of `Exp(1)`
  (`ProbabilityTheory.charFun_expMeasure`, `hasLaw_sum_ite_of_threshold`).
* **Second moments.** Given the genealogy, the branch counts are independent Poisson with means
  `λ_b = (θ/2) ℓ_b`, so `E[D_s D_{s'} | g] = θ² τ_s τ_{s'} + (θ/2) ℓ(path s ∩ path s')`, the
  second term being the Poisson variance on the branches separating both pairs
  (`integral_pairDiff_mul_kernel`, `pairPathOverlap`). Hence
  `E[D_s D_{s'}] = θ² E[τ_s τ_{s'}] + (θ/2) E[ℓ(path s ∩ path s')]` and
  `Cov(D_s, D_{s'}) = θ² Cov(τ_s, τ_{s'}) + (θ/2) E[ℓ(path s ∩ path s')]`
  (`integral_pairDiff_mul_kingmanTreeMutationMeasure`,
  `covariance_pairDiff_kingmanTreeMutationMeasure`), the pair covariances entering Tajima's
  `Var π`. For a single pair the path overlaps itself in length `2 τ_s`, and `E τ_s² = 2` gives
  `Var D_s = θ + θ²` (`variance_pairDiff_kingmanTreeMutationMeasure`).
* **Distinct pairs.** For two pairs sharing a gene, `E[τ_{ab} τ_{ac}] = 4/3`, so
  `Cov(τ_{ab}, τ_{ac}) = 1/3`, and `E[ℓ(P_{ab} ∩ P_{ac})] = 1`; hence
  `Cov(D_{ab}, D_{ac}) = θ/2 + θ²/3` (`covariance_pairCoalTime_shared`,
  `integral_pairPathOverlap_shared`, `covariance_pairDiff_shared`). For disjoint pairs,
  `E[τ_{ab} τ_{cd}] = 11/9`, `Cov = 2/9`, `E[ℓ(P_{ab} ∩ P_{cd})] = 2/3`, and
  `Cov(D_{ab}, D_{cd}) = θ/3 + 2θ²/9` (`covariance_pairCoalTime_disjoint`,
  `integral_pairPathOverlap_disjoint`, `covariance_pairDiff_disjoint`). The proofs are backward
  recursions over the steps of the history, by the double counting of `card_pairApart_succ`:
  resampling step `t` (`sum_mul_card_eq_sum_update`) turns the states of three or four genes
  after `t` events into transition counts (`sum_mul_ite_mul_rateAfter`, e.g. `C(k, 2) - 3` of
  the choices keep three lineages apart and one merges `b` with `c`). Given the first `t` steps,
  the remaining coalescence time of a pair has mean `1` and second moment `2`
  (`sum_mul_futureMean`, `sum_mul_futureProd_self`); from three distinct lineages the remaining
  product moment is `4/3` (`sum_mul_apart3_futureProd`), and from four it is `11/9`
  (`sum_mul_apart4_futureProd`). The shared-gene overlap is linear in the pair indicators
  (`overlapCount_shared`); the disjoint one has its own recursion
  (`sum_mul_apart4_futureOverlap`).

The segregating-site moments are not repeated here (see `Mutation.lean`). Assembling the pair
covariances into the closed form of Tajima's `Var π` is not done here.

## References

* F. Tajima, *Evolutionary relationship of DNA sequences in finite populations*, Genetics 105
  (1983), 437–460.
* A. W. F. Edwards, *Estimation of the branch points of a branching diffusion process*,
  J. R. Stat. Soc. B 32 (1970), 155–174.
* J. Wakeley, *Coalescent Theory: An Introduction* (2009), ch. 3–4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-! ### Ancestral partitions as lists of blocks -/

section Blocks

variable {n : ℕ}

/-- `bs` is a list of blocks partitioning `Fin n`, with `pos a` the index of the block holding
`a`. -/
def IsBlockPartition (bs : List (Finset (Fin n))) (pos : Fin n → ℕ) : Prop :=
  ∀ a, pos a < bs.length ∧ ∀ j (hj : j < bs.length), a ∈ bs[j] ↔ j = pos a

/-- The index of a block after merging positions `x < y`: `y` goes to `x`, indices above `y`
shift down by one. -/
def mergeIdx (x y p : ℕ) : ℕ := if p = y then x else if y < p then p - 1 else p

/-- Merging two blocks removes one entry. -/
theorem length_mergeBlocks (bs : List (Finset (Fin n))) {x y : ℕ} (hy : y < bs.length) :
    (mergeBlocks bs x y).length = bs.length - 1 := by
  simp [mergeBlocks, List.length_eraseIdx, hy]

/-- The blocks after merging positions `x < y`: the union at `x`, the others shifted past
`y`. -/
theorem getElem_mergeBlocks (bs : List (Finset (Fin n))) {x y : ℕ} (hxy : x < y)
    (hy : y < bs.length) (j : ℕ) (hj : j < (mergeBlocks bs x y).length) :
    (mergeBlocks bs x y)[j] =
      if hjy : j < y then (if j = x then bs[x] ∪ bs[y] else bs[j]'(by omega))
      else bs[j + 1]'(by rw [length_mergeBlocks bs hy] at hj; omega) := by
  have hlen := length_mergeBlocks bs (x := x) hy
  simp only [mergeBlocks, List.getElem_eraseIdx]
  have hx : bs.getD x ∅ = bs[x] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hy' : bs.getD y ∅ = bs[y] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy, Option.getD_some]
  split_ifs with h1 h2 <;> simp only [List.getElem_set, hx, hy']
  · simp [h2]
  · simp [Ne.symm h2]
  · simp [show x ≠ j + 1 by omega]

/-- Merging two blocks of a partition gives a partition, with positions moved by
`mergeIdx`. -/
theorem isBlockPartition_mergeBlocks {bs : List (Finset (Fin n))} {pos : Fin n → ℕ}
    (hP : IsBlockPartition bs pos) {x y : ℕ} (hxy : x < y) (hy : y < bs.length) :
    IsBlockPartition (mergeBlocks bs x y) fun a => mergeIdx x y (pos a) := by
  intro a
  obtain ⟨hpa, hmem⟩ := hP a
  have hlen := length_mergeBlocks bs (x := x) hy
  refine ⟨by simp only [hlen]; unfold mergeIdx; split_ifs <;> omega, fun j hj => ?_⟩
  rw [getElem_mergeBlocks bs hxy hy]
  unfold mergeIdx
  split_ifs <;> simp only [Finset.mem_union, hmem] <;> split_ifs <;> omega

/-- The lower label of a merging pair of lineages. -/
def pairLo {k : ℕ} (p : LineagePair k) : ℕ := (p.1.map Fin.valEmbedding).min.getD 0

/-- The upper label of a merging pair of lineages. -/
def pairHi {k : ℕ} (p : LineagePair k) : ℕ := (p.1.map Fin.valEmbedding).max.getD 0

private theorem min_getD_pair (u v : ℕ) : ({u, v} : Finset ℕ).min.getD 0 = min u v := by
  rw [Finset.min_insert, Finset.min_singleton]
  rcases le_total u v with h | h
  · rw [min_eq_left (WithTop.coe_le_coe.2 h), min_eq_left h]
    rfl
  · rw [min_eq_right (WithTop.coe_le_coe.2 h), min_eq_right h]
    rfl

private theorem max_getD_pair (u v : ℕ) : ({u, v} : Finset ℕ).max.getD 0 = max u v := by
  rw [Finset.max_insert, Finset.max_singleton]
  rcases le_total u v with h | h
  · rw [max_eq_right (WithBot.coe_le_coe.2 h), max_eq_right h]
    rfl
  · rw [max_eq_left (WithBot.coe_le_coe.2 h), max_eq_left h]
    rfl

/-- The labels of a merging pair `{u, v}` are `min u v` and `max u v`. -/
theorem pairLo_pairHi_of_map {k : ℕ} (p : LineagePair k) {u v : ℕ}
    (hp : p.1.map Fin.valEmbedding = {u, v}) : pairLo p = min u v ∧ pairHi p = max u v := by
  rw [pairLo, pairHi, hp]
  exact ⟨min_getD_pair u v, max_getD_pair u v⟩

/-- A merging pair of `k` lineages has two distinct labels below `k`, and `pairLo < pairHi`
are their minimum and maximum. -/
theorem pairLo_pairHi_spec {k : ℕ} (p : LineagePair k) :
    ∃ a b : ℕ, a ≠ b ∧ a < k ∧ b < k ∧ p.1.map Fin.valEmbedding = {a, b} ∧
      pairLo p = min a b ∧ pairHi p = max a b := by
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.1 p.2
  have hab' : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
  have hmap : p.1.map Fin.valEmbedding = {(a : ℕ), (b : ℕ)} := by
    rw [hp]
    simp [Finset.map_insert, Finset.map_singleton]
  exact ⟨a, b, hab', a.2, b.2, hmap, pairLo_pairHi_of_map p hmap⟩

/-- One coalescence event: the blocks after `t + 1` events are those after `t` events with the
pair recorded at step `t` merged. -/
theorem blocksAfter_succ (h : RankedHistory n) {t : ℕ} (ht : t < n - 1) :
    blocksAfter h (t + 1) =
      mergeBlocks (blocksAfter h t) (pairLo (h ⟨t, ht⟩)) (pairHi (h ⟨t, ht⟩)) := by
  unfold blocksAfter
  rw [List.take_add_one, List.foldl_append]
  simp [List.getElem?_eq_getElem (l := List.finRange (n - 1)) (by simpa using ht), pairLo,
    pairHi]

/-- The blocks after `t` events depend only on the first `t` steps of the history. -/
theorem blocksAfter_congr {h h' : RankedHistory n} {t : ℕ}
    (H : ∀ i : Fin (n - 1), (i : ℕ) < t → h i = h' i) : blocksAfter h t = blocksAfter h' t := by
  unfold blocksAfter
  refine List.foldl_ext _ _ _ fun bs i hi => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 hi
  rw [H _ (by simp only [List.getElem_finRange, Fin.val_cast]; omega)]

/-- **The blocks after `t ≤ n - 1` events partition the sample into `n - t` lineages.** -/
theorem blocksAfter_spec (h : RankedHistory n) {t : ℕ} (ht : t ≤ n - 1) :
    (blocksAfter h t).length = n - t ∧ ∃ pos, IsBlockPartition (blocksAfter h t) pos := by
  induction t with
  | zero =>
    refine ⟨by simp [blocksAfter], fun a => (a : ℕ), fun a => ?_⟩
    simp only [blocksAfter, List.take_zero, List.foldl_nil, List.length_map,
      List.length_finRange, List.getElem_map, List.getElem_finRange, Finset.mem_singleton]
    exact ⟨a.2, fun j hj => by rw [Fin.ext_iff]; simp [eq_comm]⟩
  | succ t ih =>
    obtain ⟨hlen, pos, hP⟩ := ih (by omega)
    have hlt : t < n - 1 := by omega
    obtain ⟨a, b, hab, ha, hb, -, hlo, hhi⟩ := pairLo_pairHi_spec (h ⟨t, hlt⟩)
    have hxy : pairLo (h ⟨t, hlt⟩) < pairHi (h ⟨t, hlt⟩) := by
      rw [hlo, hhi]; omega
    have hy : pairHi (h ⟨t, hlt⟩) < (blocksAfter h t).length := by
      rw [hhi, hlen]; simp only at ha hb; omega
    rw [blocksAfter_succ h hlt]
    exact ⟨by rw [length_mergeBlocks _ hy, hlen]; omega, _,
      isBlockPartition_mergeBlocks hP hxy hy⟩

/-! ### When two sampled genes coalesce -/

/-- The genes of `s` are still in different lineages after `t` coalescence events of the
history `h`: no block contains `s`. -/
def PairApart (h : RankedHistory n) (s : Finset (Fin n)) (t : ℕ) : Prop :=
  ∀ B ∈ blocksAfter h t, ¬s ⊆ B

/-- Being apart is decidable (so small cases can be evaluated). -/
instance (h : RankedHistory n) (s : Finset (Fin n)) (t : ℕ) : Decidable (PairApart h s t) := by
  unfold PairApart
  infer_instance

private theorem forall_not_pair_subset_iff {bs : List (Finset (Fin n))} {pos : Fin n → ℕ}
    (hP : IsBlockPartition bs pos) {a b : Fin n} :
    (∀ B ∈ bs, ¬({a, b} : Finset (Fin n)) ⊆ B) ↔ pos a ≠ pos b := by
  constructor
  · intro H heq
    obtain ⟨ha, hma⟩ := hP a
    refine H bs[pos a] (List.getElem_mem _) ?_
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff, hma, (hP b).2 _ ha, heq]
    simp
  · intro hne B hB hsub
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hB
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff, (hP a).2, (hP b).2] at hsub
    exact hne (hsub.1.symm.trans hsub.2)

private theorem mergeIdx_eq_iff {x y p q : ℕ} (hxy : x < y) :
    mergeIdx x y p = mergeIdx x y q ↔ p = q ∨ (p = x ∧ q = y) ∨ (p = y ∧ q = x) := by
  unfold mergeIdx
  split_ifs <;> omega

/-- In a partition with positions `pos`, two genes are apart iff their positions differ. -/
theorem pairApart_iff {h : RankedHistory n} {t : ℕ} {pos : Fin n → ℕ}
    (hP : IsBlockPartition (blocksAfter h t) pos) {a b : Fin n} :
    PairApart h {a, b} t ↔ pos a ≠ pos b :=
  forall_not_pair_subset_iff hP

/-- **One step of the history**: genes in lineages `pos a`, `pos b` after `t` events are
together after `t + 1` events iff they were together already or step `t` merges exactly their
two lineages. -/
theorem pairApart_succ_iff {h : RankedHistory n} {t : ℕ} (ht : t < n - 1) {pos : Fin n → ℕ}
    (hP : IsBlockPartition (blocksAfter h t) pos) {a b : Fin n} :
    PairApart h {a, b} (t + 1) ↔
      ¬(pos a = pos b ∨ (pos a = pairLo (h ⟨t, ht⟩) ∧ pos b = pairHi (h ⟨t, ht⟩)) ∨
        (pos a = pairHi (h ⟨t, ht⟩) ∧ pos b = pairLo (h ⟨t, ht⟩))) := by
  have hlen := (blocksAfter_spec h ht.le).1
  obtain ⟨u, v, huv, hu, hv, -, hlo, hhi⟩ := pairLo_pairHi_spec (h ⟨t, ht⟩)
  have hxy : pairLo (h ⟨t, ht⟩) < pairHi (h ⟨t, ht⟩) := by rw [hlo, hhi]; omega
  have hy : pairHi (h ⟨t, ht⟩) < (blocksAfter h t).length := by
    rw [hhi, hlen]; simp only at hu hv; omega
  unfold PairApart
  rw [blocksAfter_succ h ht, forall_not_pair_subset_iff (isBlockPartition_mergeBlocks hP hxy hy),
    Ne, mergeIdx_eq_iff hxy]

/-- Once together, two genes stay together. -/
theorem PairApart.of_succ {h : RankedHistory n} {t : ℕ} {a b : Fin n}
    (H : PairApart h {a, b} (t + 1)) : PairApart h {a, b} t := by
  by_cases ht : t < n - 1
  · obtain ⟨-, pos, hP⟩ := blocksAfter_spec h ht.le
    rw [pairApart_succ_iff ht hP] at H
    rw [pairApart_iff hP]
    exact fun he => H (Or.inl he)
  · have : blocksAfter h (t + 1) = blocksAfter h t := by
      unfold blocksAfter
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
    unfold PairApart at H ⊢
    rwa [this] at H

end Blocks

/-! ### Counting histories -/

section Counting

/-- Double counting: if `A` does not depend on coordinate `i`, `E ⊆ A`, and for every `f ∈ A`
exactly one value of coordinate `i` takes `f` out of `E`, then `#E * #β i + #A = #A * #β i`. -/
theorem card_filter_mul_add_of_existsUnique {ι : Type*} [DecidableEq ι] [Fintype ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (i : ι)
    (A E : (∀ j, β j) → Prop) [DecidablePred A] [DecidablePred E]
    (hA : ∀ f x, A (Function.update f i x) ↔ A f) (hEA : ∀ f, E f → A f)
    (hE : ∀ f, A f → ∃! x, ¬E (Function.update f i x)) :
    #{f | E f} * Fintype.card (β i) + #{f | A f} = #{f | A f} * Fintype.card (β i) := by
  classical
  -- the involution `(f, x) ↦ (update f i x, f i)`
  let e : (∀ j, β j) × β i ≃ (∀ j, β j) × β i :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have h1 : (∑ p : (∀ j, β j) × β i,
      if A p.1 ∧ ¬E (Function.update p.1 i p.2) then 1 else 0) = #{f | A f} := by
    rw [Fintype.sum_prod_type, Finset.card_filter]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hf : A f
    · obtain ⟨x, hx, hu⟩ := hE f hf
      simp only [hf, true_and, ite_true]
      rw [Finset.sum_boole, Nat.cast_id, Finset.card_eq_one]
      exact ⟨x, by ext y; simpa using ⟨hu y, fun h => h ▸ hx⟩⟩
    · simp [hf]
  have h2 : (∑ p : (∀ j, β j) × β i,
      if A p.1 ∧ ¬E (Function.update p.1 i p.2) then 1 else 0) =
      #{f | A f ∧ ¬E f} * Fintype.card (β i) := by
    rw [← Equiv.sum_comp e]
    simp only [e, Equiv.coe_fn_mk, Function.update_idem, Function.update_eq_self, hA]
    rw [Fintype.sum_prod_type, Finset.card_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs <;> simp
  have h3 : #{f | A f} = #{f | E f} + #{f | A f ∧ ¬E f} := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun f _ hE' h => h.2 hE')]
    congr 1
    ext f
    by_cases hf : E f <;> simp [hf, hEA f]
  rw [h1] at h2
  generalize #{f | A f} = a at *
  generalize #{f | E f} = e at *
  generalize #{f | A f ∧ ¬E f} = m at *
  subst h3
  rw [add_mul, ← h2]

private theorem pair_eq_of_minmax {u v p q : ℕ}
    (h : (p = min u v ∧ q = max u v) ∨ (p = max u v ∧ q = min u v)) :
    ({u, v} : Finset ℕ) = {p, q} := by
  rcases le_total u v with huv | huv <;>
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [huv, Finset.pair_comm]

variable {n : ℕ}

/-- **Counting step**: among the ranked labeled histories in which the genes `a ≠ b` are apart
after `t < n - 1` events, exactly a fraction `1 / C(n - t, 2)` merge them at step `t` (one of the
`C(n - t, 2)` pairs of current lineages). -/
theorem card_pairApart_succ {a b : Fin n} {t : ℕ} (ht : t < n - 1) :
    #{h : RankedHistory n | PairApart h {a, b} (t + 1)} * (n - t).choose 2 +
      #{h : RankedHistory n | PairApart h {a, b} t} =
      #{h : RankedHistory n | PairApart h {a, b} t} * (n - t).choose 2 := by
  have hcong : ∀ (f : RankedHistory n) (x : LineagePair (n - t)),
      blocksAfter (Function.update f ⟨t, ht⟩ x) t = blocksAfter f t := fun f x =>
    blocksAfter_congr fun j hj => Function.update_of_ne (fun h => by simp [h] at hj) _ _
  have := card_filter_mul_add_of_existsUnique (β := fun i : Fin (n - 1) => LineagePair (n - i))
    ⟨t, ht⟩ (fun h => PairApart h {a, b} t) (fun h => PairApart h {a, b} (t + 1))
    (fun f x => by unfold PairApart; rw [hcong f x]) (fun f => PairApart.of_succ) ?_
  · simpa only [card_lineagePair] using this
  intro f hf
  obtain ⟨hlen, pos, hP⟩ := blocksAfter_spec f ht.le
  rw [pairApart_iff hP] at hf
  have hpa : pos a < n - t := hlen ▸ (hP a).1
  have hpb : pos b < n - t := hlen ▸ (hP b).1
  have key : ∀ x : LineagePair (n - t), ¬PairApart (Function.update f ⟨t, ht⟩ x) {a, b} (t + 1) ↔
      (pos a = pairLo x ∧ pos b = pairHi x) ∨ (pos a = pairHi x ∧ pos b = pairLo x) := by
    intro x
    have hP' : IsBlockPartition (blocksAfter (Function.update f ⟨t, ht⟩ x) t) pos :=
      (hcong f x).symm ▸ hP
    rw [pairApart_succ_iff ht hP', Function.update_self]
    tauto
  let x0 : LineagePair (n - t) :=
    ⟨{⟨pos a, hpa⟩, ⟨pos b, hpb⟩}, Finset.card_pair (by simpa [Fin.ext_iff] using hf)⟩
  have hx0 : x0.1.map Fin.valEmbedding = {pos a, pos b} := by simp [x0]
  refine ⟨x0, ?_, fun x hx => ?_⟩
  · simp only
    rw [key]
    obtain ⟨hl, hh⟩ := pairLo_pairHi_of_map x0 hx0
    rw [hl, hh]
    omega
  · have hx' := (key x).1 hx
    obtain ⟨u, v, -, -, -, hmap, hl, hh⟩ := pairLo_pairHi_spec x
    refine Subtype.ext (Finset.map_injective Fin.valEmbedding ?_)
    rw [hmap, hx0]
    rw [hl, hh] at hx'
    exact pair_eq_of_minmax hx'

/-- At the start of the history all sampled genes are in different lineages. -/
theorem pairApart_zero (h : RankedHistory n) {a b : Fin n} (hab : a ≠ b) :
    PairApart h {a, b} 0 := by
  obtain ⟨-, pos, hP⟩ := blocksAfter_spec h (Nat.zero_le _)
  rw [pairApart_iff hP]
  intro he
  -- in the initial partition, `pos` is the label
  have h0 : ∀ c : Fin n, pos c = c := by
    intro c
    obtain ⟨hc, hmem⟩ := hP c
    have hc' : (c : ℕ) < (blocksAfter h 0).length := by simp [blocksAfter]
    refine ((hmem c hc').1 ?_).symm
    simp [blocksAfter]
  exact hab (Fin.ext (by rw [← h0 a, ← h0 b, he]))

/-- **Probability that two genes are still apart after `t` coalescence events** (Tajima 1983):
under random joining, for `n ≥ 2` and `t ≤ n - 2`, it is
`∏_{i < t} (1 - 1 / C(n - i, 2)) = (n - t - 1)(n + 1) / ((n - t + 1)(n - 1))`, which is
`pairSeparateProb n (n - t)`; `integral_pairApart_randomJoining` states it in that form. -/
theorem card_pairApart_div {a b : Fin n} (hab : a ≠ b) {t : ℕ} (ht : t + 2 ≤ n) :
    (#{h : RankedHistory n | PairApart h {a, b} t} : ℝ) / Fintype.card (RankedHistory n) =
      ((n : ℝ) - t - 1) * (n + 1) / (((n : ℝ) - t + 1) * (n - 1)) := by
  have hpos : (0 : ℝ) < Fintype.card (RankedHistory n) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨fun i => Classical.arbitrary _⟩
  induction t with
  | zero =>
    have hall : #{h : RankedHistory n | PairApart h {a, b} 0} = Fintype.card (RankedHistory n) := by
      rw [Finset.filter_true_of_mem fun h _ => pairApart_zero h hab, Finset.card_univ]
    have h1 : (n : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast ht
      linarith
    have h2 : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [hall, div_self hpos.ne']
    push_cast
    field_simp
    ring
  | succ t ih =>
    have hrec := card_pairApart_succ (a := a) (b := b) (t := t) (by omega)
    have hC : (((n - t).choose 2 : ℕ) : ℝ) = ((n : ℝ) - t) * ((n : ℝ) - t - 1) / 2 := by
      rw [Nat.cast_choose_two, Nat.cast_sub (by omega)]
    have hrec' : (#{h : RankedHistory n | PairApart h {a, b} (t + 1)} : ℝ) =
        #{h : RankedHistory n | PairApart h {a, b} t} *
          (1 - 1 / (((n - t).choose 2 : ℕ) : ℝ)) := by
      have hC0 : (((n - t).choose 2 : ℕ) : ℝ) ≠ 0 := by
        rw [hC]
        have : (t : ℝ) + 2 + 1 ≤ n := by exact_mod_cast (show t + 1 + 2 ≤ n by omega)
        have h1 : (0 : ℝ) < (n : ℝ) - t := by linarith
        have h2 : (0 : ℝ) < (n : ℝ) - t - 1 := by linarith
        positivity
      have := congrArg (fun x : ℕ => (x : ℝ)) hrec
      push_cast at this
      field_simp
      linarith
    rw [hrec', mul_div_right_comm, ih (by omega), hC]
    have : (t : ℝ) + 1 + 2 ≤ n := by exact_mod_cast ht
    have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (n : ℝ) - t - 1 ≠ 0 := by linarith
    have h3 : (n : ℝ) - t ≠ 0 := by linarith
    have h4 : (n : ℝ) - t + 1 ≠ 0 := by linarith
    have e : (1 : ℝ) - 1 / (((n : ℝ) - t) * ((n : ℝ) - t - 1) / 2) =
        ((n : ℝ) - t - 2) * ((n : ℝ) - t + 1) / (((n : ℝ) - t) * ((n : ℝ) - t - 1)) := by
      field_simp
      ring
    have h6 : ((n : ℝ) - (t + 1 : ℕ) + 1) * ((n : ℝ) - 1) ≠ 0 := by
      push_cast
      exact mul_ne_zero (by linarith) h1
    rw [e, div_mul_div_comm, div_eq_div_iff (by positivity) h6]
    push_cast
    ring

end Counting

/-! ### The branches between two sampled genes -/

section Branches

variable {n : ℕ}

/-- The sampled genes below branch `b = ⟨k, j⟩` of a genealogy with history `h`: the block of
lineage `j` while there are `k` lineages, i.e. after `n - k` coalescence events. -/
def branchBlock (h : RankedHistory n) (b : KingmanBranch n) : Finset (Fin n) :=
  (blocksAfter h (n - b.1)).getD b.2 ∅

/-- The branches **separating** the two genes of `s`: those ancestral to exactly one of them.
These form the path between the two genes through their most recent common ancestor (MRCA). -/
def pairPath (h : RankedHistory n) (s : Finset (Fin n)) : Finset (KingmanBranch n) :=
  {b | (s ∩ branchBlock h b).card = 1}

/-- The branches **shared** by the two genes of `s`: those ancestral to both, i.e. above their
MRCA. Mutations there are carried by both genes and do not separate them. -/
def pairShared (h : RankedHistory n) (s : Finset (Fin n)) : Finset (KingmanBranch n) :=
  {b | s ⊆ branchBlock h b}

/-- The **coalescence time** of the two genes of `s` in a genealogy with epoch lengths `t` and
history `h`: the total length of the epochs during which they are in different lineages. -/
def pairCoalTime (h : RankedHistory n) (s : Finset (Fin n)) (t : Icc 2 n → ℝ) : ℝ :=
  ∑ k : Icc 2 n, if PairApart h s (n - k) then t k else 0

private theorem card_pair_inter_eq_one {a b : Fin n} (hab : a ≠ b) (B : Finset (Fin n)) :
    (({a, b} : Finset (Fin n)) ∩ B).card = 1 ↔ (a ∈ B ↔ b ∉ B) := by
  by_cases ha : a ∈ B <;> by_cases hb : b ∈ B <;>
    simp [Finset.insert_inter_of_mem, Finset.insert_inter_of_notMem, ha, hb, hab]

/-- **In each epoch exactly two branches separate a pair that is still apart, and none separate
a pair that has coalesced.** -/
theorem card_pairPath_epoch (h : RankedHistory n) {a b : Fin n} (hab : a ≠ b) (k : Icc 2 n) :
    #{j : Fin k | (({a, b} : Finset (Fin n)) ∩ branchBlock h ⟨k, j⟩).card = 1} =
      if PairApart h {a, b} (n - k) then 2 else 0 := by
  obtain ⟨k, hk⟩ := k
  simp only [branchBlock]
  rw [Finset.mem_Icc] at hk
  obtain ⟨hlen, pos, hP⟩ := blocksAfter_spec h (t := n - k) (by omega)
  rw [show n - (n - k) = k by omega] at hlen
  have hmem : ∀ (c : Fin n) (j : Fin k),
      c ∈ (blocksAfter h (n - k)).getD j ∅ ↔ (j : ℕ) = pos c := by
    intro c j
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact (hP c).2 j (by omega)
  have hpa : pos a < k := hlen ▸ (hP a).1
  have hpb : pos b < k := hlen ▸ (hP b).1
  simp_rw [card_pair_inter_eq_one hab, hmem]
  by_cases hne' : PairApart h {a, b} (n - k)
  · have hne := (pairApart_iff hP).1 hne'
    simp only [hne', ↓reduceIte]
    rw [Finset.card_eq_two]
    refine ⟨⟨pos a, hpa⟩, ⟨pos b, hpb⟩, by simpa [Fin.ext_iff] using hne, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    omega
  · have hne : pos a = pos b := by
      by_contra hne
      exact hne' ((pairApart_iff hP).2 hne)
    simp only [hne', ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _
    omega

/-- **In each epoch the pair shares one branch once it has coalesced, and none before**: the
shared branches are the lineage ancestral to both genes, from their MRCA up to the root. -/
theorem card_pairShared_epoch (h : RankedHistory n) {a b : Fin n} (k : Icc 2 n) :
    #{j : Fin k | ({a, b} : Finset (Fin n)) ⊆ branchBlock h ⟨k, j⟩} =
      if PairApart h {a, b} (n - k) then 0 else 1 := by
  obtain ⟨k, hk⟩ := k
  simp only [branchBlock]
  rw [Finset.mem_Icc] at hk
  obtain ⟨hlen, pos, hP⟩ := blocksAfter_spec h (t := n - k) (by omega)
  rw [show n - (n - k) = k by omega] at hlen
  have hmem : ∀ (c : Fin n) (j : Fin k),
      c ∈ (blocksAfter h (n - k)).getD j ∅ ↔ (j : ℕ) = pos c := by
    intro c j
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact (hP c).2 j (by omega)
  have hpa : pos a < k := hlen ▸ (hP a).1
  simp_rw [Finset.insert_subset_iff, Finset.singleton_subset_iff, hmem]
  by_cases hne' : PairApart h {a, b} (n - k)
  · have hne := (pairApart_iff hP).1 hne'
    simp only [hne', ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _
    omega
  · have hne : pos a = pos b := by
      by_contra hne
      exact hne' ((pairApart_iff hP).2 hne)
    simp only [hne', ↓reduceIte]
    rw [Finset.card_eq_one]
    refine ⟨⟨pos a, hpa⟩, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
    omega

/-- **The path between two genes has length twice their coalescence time**:
`∑_{b separating s} ℓ_b = 2 ∑_{epochs k with s apart} t_k`. -/
theorem sum_pairPath_branchLength (h : RankedHistory n) {s : Finset (Fin n)}
    (hs : s ∈ samplePairs n) (t : Icc 2 n → ℝ) :
    ∑ b ∈ pairPath h s, kingmanBranchLength n t b =
      2 * ∑ k : Icc 2 n, if PairApart h s (n - k) then (t k).toNNReal else 0 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (Finset.mem_powersetCard.1 hs).2
  rw [pairPath, Finset.sum_filter, Fintype.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_filter]
  simp only [kingmanBranchLength]
  rw [Finset.sum_const, card_pairPath_epoch h hab k, nsmul_eq_mul]
  split_ifs <;> simp

end Branches

/-! ### Pairwise differences under Poisson mutation marking -/

/-- Infinite-sites mutation on a Kingman genealogy with topology: given the epoch lengths `t` and
the ranked labeled history `h`, branch `b` carries an independent `Po((θ/2) ℓ_b(t))` number of
mutation events (`kingmanMutationKernel`, which does not depend on `h`). -/
def kingmanTreeMutationKernel (n : ℕ) (θ : ℝ≥0) :
    Kernel ((Icc 2 n → ℝ) × RankedHistory n) (KingmanBranch n → ℕ) :=
  (kingmanMutationKernel n θ).comap Prod.fst measurable_fst

/-- The mutation kernel with topology is a Markov kernel. -/
instance (n : ℕ) (θ : ℝ≥0) : IsMarkovKernel (kingmanTreeMutationKernel n θ) := by
  unfold kingmanTreeMutationKernel
  infer_instance

/-- The number of pairwise differences between the two genes of `s`: under infinite sites, the
two sequences differ exactly at the mutations on the branches separating them (`pairPath`). -/
def pairDiff {Ω : Type*} {n : ℕ} (H : Ω → RankedHistory n) (N : Ω → KingmanBranch n → ℕ)
    (s : Finset (Fin n)) (ω : Ω) : ℝ :=
  ((∑ b ∈ pairPath (H ω) s, N ω b : ℕ) : ℝ)

/-- The conditional Poisson mean of branch `b` depends measurably on the genealogy. -/
theorem measurable_branchMean (n : ℕ) (θ : ℝ≥0) (b : KingmanBranch n) :
    Measurable fun x : (Icc 2 n → ℝ) × RankedHistory n =>
      θ / 2 * kingmanBranchLength n x.1 b :=
  measurable_const.mul ((measurable_kingmanBranchLength n).eval.comp measurable_fst)

section Mutation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ} {θ : ℝ≥0}
  {H : Ω → RankedHistory n} {N : Ω → KingmanBranch n → ℕ}

/-- The count on a single branch is conditionally `Po((θ/2) ℓ_b)` given the genealogy. -/
theorem hasCondDistrib_branch_of_treeMutation [SFinite μ] {X : Ω → (Icc 2 n → ℝ) × RankedHistory n}
    (hN : HasCondDistrib N X (kingmanTreeMutationKernel n θ) μ) (b : KingmanBranch n) :
    HasCondDistrib (fun ω => N ω b) X
      (poissonMeasureKernel.comap _ (measurable_branchMean n θ b)) μ := by
  have h := hN.comp_left (measurable_pi_apply b)
  have hk : (kingmanTreeMutationKernel n θ).map (fun N : KingmanBranch n → ℕ => N b) =
      poissonMeasureKernel.comap _ (measurable_branchMean n θ b) := by
    ext1 x
    rw [Kernel.map_apply _ (measurable_pi_apply b), kingmanTreeMutationKernel, Kernel.comap_apply,
      kingmanMutationKernel, branchMutationKernel, Kernel.comap_apply, piPoissonKernel_apply,
      (measurePreserving_eval _ b).map_eq, Kernel.comap_apply, poissonMeasureKernel_apply]
  rw [hk] at h
  exact h

namespace KingmanTimes

variable (K : KingmanTimes μ n)

private theorem ae_nonneg_epochs : ∀ᵐ ω ∂μ, ∀ k : Icc 2 n, 0 ≤ K.epochs ω k :=
  ae_all_iff.2 fun k => ae_nonneg_of_hasLaw_expMeasure (choose_two_pos k.2) (K.hasLaw k k.2)

private theorem integrable_branchLength (b : KingmanBranch n) :
    Integrable (fun ω => ((kingmanBranchLength n (K.epochs ω) b : ℝ≥0) : ℝ)) μ := by
  simp only [kingmanBranchLength, Real.coe_toNNReal']
  exact (K.integrable_T b.1.2).pos_part

variable [IsProbabilityMeasure μ]

/-- Each branch count is integrable. -/
private theorem integrable_branch (hN : HasCondDistrib N (fun ω => (K.epochs ω, H ω))
    (kingmanTreeMutationKernel n θ) μ) (b : KingmanBranch n) :
    Integrable (fun ω => (N ω b : ℝ)) μ :=
  integrable_natCast_of_hasCondDistrib_poisson (hasCondDistrib_branch_of_treeMutation hN b)
    (by simpa using (K.integrable_branchLength b).const_mul ((θ : ℝ) / 2))

/-- The pairwise difference as a sum over all branches, weighted by the indicator of the
path. -/
private theorem pairDiff_eq (s : Finset (Fin n)) :
    pairDiff H N s = ∑ b, (fun ω => (if b ∈ pairPath (H ω) s then (1 : ℝ) else 0) *
      (N ω b : ℝ)) := by
  funext ω
  simp only [pairDiff, Finset.sum_apply, Nat.cast_sum, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

private theorem integrable_term (hN : HasCondDistrib N (fun ω => (K.epochs ω, H ω))
    (kingmanTreeMutationKernel n θ) μ) (hX : Measurable fun ω => (K.epochs ω, H ω))
    (s : Finset (Fin n)) (b : KingmanBranch n) :
    Integrable (fun ω => (if b ∈ pairPath (H ω) s then (1 : ℝ) else 0) * (N ω b : ℝ)) μ := by
  refine (K.integrable_branch hN b).bdd_mul (c := 1) ?_ (ae_of_all _ fun ω => ?_)
  · exact ((Measurable.of_discrete (f := fun h : RankedHistory n =>
      if b ∈ pairPath h s then (1 : ℝ) else 0)).comp (measurable_snd.comp hX)).aestronglyMeasurable
  · split_ifs <;> simp

/-- **The pairwise difference count is integrable** under Poisson mutation marking. This
discharges the hypothesis `hDint` of `integral_meanPairDiff`. -/
theorem integrable_pairDiff_of_mutation (hX : Measurable fun ω => (K.epochs ω, H ω))
    (hN : HasCondDistrib N (fun ω => (K.epochs ω, H ω)) (kingmanTreeMutationKernel n θ) μ)
    (s : Finset (Fin n)) : Integrable (pairDiff H N s) μ := by
  rw [pairDiff_eq]
  exact integrable_finsetSum' _ fun b _ => K.integrable_term hN hX s b

/-- **Conditional mean of the pairwise differences** (Tajima 1983): under infinite-sites
mutation at rate `θ / 2` per lineage, the number of differences between the two genes of a pair
`s` has conditional mean `θ τ_s` given the genealogy (epoch lengths and topology), where `τ_s` is
their coalescence time: the separating path has length `2 τ_s`. This discharges the hypothesis
`hD` of `integral_meanPairDiff`. -/
theorem condExp_pairDiff_of_mutation (hX : Measurable fun ω => (K.epochs ω, H ω))
    (hN : HasCondDistrib N (fun ω => (K.epochs ω, H ω)) (kingmanTreeMutationKernel n θ) μ)
    {s : Finset (Fin n)} (hs : s ∈ samplePairs n) :
    μ[pairDiff H N s | MeasurableSpace.comap (fun ω => (K.epochs ω, H ω)) inferInstance] =ᵐ[μ]
      fun ω => (θ : ℝ) * pairCoalTime (H ω) s (K.epochs ω) := by
  have hXm : Measurable[MeasurableSpace.comap (fun ω => (K.epochs ω, H ω)) inferInstance]
      (fun ω => (K.epochs ω, H ω)) := comap_measurable _
  have hterm : ∀ b : KingmanBranch n,
      μ[fun ω => (if b ∈ pairPath (H ω) s then (1 : ℝ) else 0) * (N ω b : ℝ) |
        MeasurableSpace.comap (fun ω => (K.epochs ω, H ω)) inferInstance] =ᵐ[μ]
        fun ω => (if b ∈ pairPath (H ω) s then (1 : ℝ) else 0) *
          ((θ : ℝ) / 2 * (kingmanBranchLength n (K.epochs ω) b : ℝ)) := by
    intro b
    have hg : StronglyMeasurable[MeasurableSpace.comap (fun ω => (K.epochs ω, H ω)) inferInstance]
        fun ω => if b ∈ pairPath (H ω) s then (1 : ℝ) else 0 :=
      ((Measurable.of_discrete (f := fun h : RankedHistory n =>
        if b ∈ pairPath h s then (1 : ℝ) else 0)).comp
          (measurable_snd.comp hXm)).stronglyMeasurable
    have hmean := condExp_natCast_of_hasCondDistrib_poisson hX
      (hasCondDistrib_branch_of_treeMutation hN b)
      (by simpa using (K.integrable_branchLength b).const_mul ((θ : ℝ) / 2))
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hg (K.integrable_term hN hX s b)
      (K.integrable_branch hN b), hmean] with ω h1 h2
    refine h1.trans ?_
    rw [Pi.mul_apply, h2]
    simp
  have hsum := condExp_finsetSum (fun b _ => K.integrable_term hN hX s b)
    (MeasurableSpace.comap (fun ω => (K.epochs ω, H ω)) inferInstance) (s := univ)
  rw [pairDiff_eq]
  filter_upwards [hsum, ae_all_iff.2 hterm, K.ae_nonneg_epochs] with ω h1 h2 h3
  rw [h1, Finset.sum_apply]
  simp_rw [h2]
  have hpath := congrArg (fun x : ℝ≥0 => (x : ℝ)) (sum_pairPath_branchLength (H ω) hs (K.epochs ω))
  simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_ofNat] at hpath
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum, hpath, pairCoalTime]
  have : ∀ k : Icc 2 n,
      ((if PairApart (H ω) s (n - k) then (K.epochs ω k).toNNReal else 0 : ℝ≥0) : ℝ) =
      if PairApart (H ω) s (n - k) then K.epochs ω k else 0 := fun k => by
    split_ifs <;> simp [Real.coe_toNNReal _ (h3 k)]
  simp_rw [this]
  ring

/-- **Expected pairwise differences of one pair**: `E[D_s] = θ E[τ_s]`. -/
theorem integral_pairDiff_of_mutation (hX : Measurable fun ω => (K.epochs ω, H ω))
    (hN : HasCondDistrib N (fun ω => (K.epochs ω, H ω)) (kingmanTreeMutationKernel n θ) μ)
    {s : Finset (Fin n)} (hs : s ∈ samplePairs n) :
    μ[pairDiff H N s] = (θ : ℝ) * μ[fun ω => pairCoalTime (H ω) s (K.epochs ω)] := by
  rw [← integral_condExp hX.comap_le, integral_congr_ae (K.condExp_pairDiff_of_mutation hX hN hs),
    integral_const_mul]

/-- **Tajima's `E π = θ` with the pairwise hypotheses discharged by the mutation model**: under
infinite-sites mutation at rate `θ / 2` per lineage on a Kingman genealogy with topology `H`,
if each pair's coalescence time is `Exp(1)` then `E π = θ`. The mutation hypotheses `hDint`,
`hD` of `integral_meanPairDiff` are proved (`integrable_pairDiff_of_mutation`,
`condExp_pairDiff_of_mutation`); only the law of the coalescence times remains. -/
theorem integral_meanPairDiff_of_mutation (hX : Measurable fun ω => (K.epochs ω, H ω))
    (hN : HasCondDistrib N (fun ω => (K.epochs ω, H ω)) (kingmanTreeMutationKernel n θ) μ)
    (hn : 2 ≤ n)
    (hτ : ∀ s ∈ samplePairs n,
      HasLaw (fun ω => pairCoalTime (H ω) s (K.epochs ω)) (expMeasure 1) μ) :
    μ[meanPairDiff n (pairDiff H N)] = (θ : ℝ) :=
  integral_meanPairDiff hX.comap_le hn hτ
    (fun s _ => K.integrable_pairDiff_of_mutation hX hN s)
    (fun _ hs => K.condExp_pairDiff_of_mutation hX hN hs)

end KingmanTimes

end Mutation

/-! ### A concrete model: exponential epochs and random joining -/

section Model

variable {n : ℕ}

/-- Under random joining, the probability that the genes of a pair `s` are apart during the epoch
with `k` lineages is `pairSeparateProb n k = (k - 1)(n + 1) / ((n - 1)(k + 1))`. -/
theorem integral_pairApart_randomJoining {s : Finset (Fin n)} (hs : s ∈ samplePairs n) {k : ℕ}
    (hk : k ∈ Icc 2 n) :
    ∫ h, (if PairApart h s (n - k) then (1 : ℝ) else 0) ∂randomJoining n =
      pairSeparateProb n k := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (Finset.mem_powersetCard.1 hs).2
  rw [Finset.mem_Icc] at hk
  have hsing : ∀ h : RankedHistory n,
      (randomJoining n).real {h} = (Fintype.card (RankedHistory n) : ℝ)⁻¹ := fun h => by
    rw [measureReal_def, randomJoining_singleton_eq_inv, ← card_rankedHistory, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
  rw [integral_fintype (Integrable.of_finite), Finset.sum_congr rfl fun h _ => by rw [hsing h],
    ← Finset.smul_sum, Finset.sum_boole, smul_eq_mul, inv_mul_eq_div,
    card_pairApart_div hab (t := n - k) (by omega), Nat.cast_sub hk.2, pairSeparateProb]
  ring_nf

/-- The Kingman genealogy with topology for a sample of size `n`: independent exponential epoch
lengths (`piMeasure n`) and an independent random-joining ranked labeled history. -/
def kingmanGenealogyMeasure (n : ℕ) : Measure ((Icc 2 n → ℝ) × RankedHistory n) :=
  (piMeasure n).prod (randomJoining n)

/-- The genealogy law is a probability measure. -/
instance (n : ℕ) : IsProbabilityMeasure (kingmanGenealogyMeasure n) := by
  unfold kingmanGenealogyMeasure
  infer_instance

/-- The coalescence time of a pair is a measurable function of the genealogy. -/
theorem measurable_pairCoalTime (s : Finset (Fin n)) :
    Measurable fun g : (Icc 2 n → ℝ) × RankedHistory n => pairCoalTime g.2 s g.1 := by
  unfold pairCoalTime
  refine Finset.measurable_sum _ fun k _ => Measurable.ite ?_ ?_ measurable_const
  · exact measurable_snd
      (MeasurableSet.of_discrete : MeasurableSet {h : RankedHistory n | PairApart h s (n - k)})
  · exact (measurable_pi_apply k).comp measurable_fst

/-- **The mean coalescence time of a pair is one** (in units of `2N` generations): averaging the
epoch lengths over the random-joining topology,
`E τ_s = ∑_{k=2}^n pairSeparateProb n k / C(k, 2) = 1` (`sum_pairSeparateProb_div_choose`). -/
theorem integral_pairCoalTime_kingmanGenealogyMeasure (hn : 2 ≤ n) {s : Finset (Fin n)}
    (hs : s ∈ samplePairs n) :
    ∫ g, pairCoalTime g.2 s g.1 ∂kingmanGenealogyMeasure n = 1 := by
  have hT : ∀ k : Icc 2 n, ∫ t, t k ∂piMeasure n = (((k : ℕ).choose 2 : ℕ) : ℝ)⁻¹ := fun k => by
    have := (KingmanTimes.ofPi n).integral_T k.2
    simpa [KingmanTimes.ofPi, Finset.mem_Icc.1 k.2] using this
  have hTi : ∀ k : Icc 2 n, Integrable (fun t : Icc 2 n → ℝ => t k) (piMeasure n) := fun k => by
    have := (KingmanTimes.ofPi n).integrable_T k.2
    simpa [KingmanTimes.ofPi, Finset.mem_Icc.1 k.2] using this
  have hterm : ∀ k : Icc 2 n, (fun g : (Icc 2 n → ℝ) × RankedHistory n =>
      if PairApart g.2 s (n - k) then g.1 k else 0) =
      fun g => g.1 k * (if PairApart g.2 s (n - k) then (1 : ℝ) else 0) := fun k => by
    funext g
    split_ifs <;> simp
  unfold pairCoalTime kingmanGenealogyMeasure
  rw [integral_finsetSum _ fun k _ => by
    rw [hterm k]
    exact (hTi k).mul_prod
      (g := fun h : RankedHistory n => if PairApart h s (n - k) then (1 : ℝ) else 0)
      Integrable.of_finite]
  rw [Finset.sum_congr rfl fun k _ => by
    rw [hterm k, integral_prod_mul (fun t : Icc 2 n → ℝ => t k)
      (fun h : RankedHistory n => if PairApart h s (n - k) then (1 : ℝ) else 0), hT k,
      integral_pairApart_randomJoining hs k.2, mul_comm]]
  rw [Finset.sum_coe_sort (Icc 2 n) fun k : ℕ => pairSeparateProb n k *
    ((k.choose 2 : ℕ) : ℝ)⁻¹]
  exact sum_pairSeparateProb_div_choose hn

/-- The marked Kingman model with topology: genealogy from `kingmanGenealogyMeasure n`, then
independent `Po((θ/2) ℓ_b)` mutation counts on the branches. -/
def kingmanTreeMutationMeasure (n : ℕ) (θ : ℝ≥0) :
    Measure (((Icc 2 n → ℝ) × RankedHistory n) × (KingmanBranch n → ℕ)) :=
  kingmanGenealogyMeasure n ⊗ₘ kingmanTreeMutationKernel n θ

/-- The marked model is a probability measure. -/
instance (n : ℕ) (θ : ℝ≥0) : IsProbabilityMeasure (kingmanTreeMutationMeasure n θ) := by
  unfold kingmanTreeMutationMeasure
  infer_instance

/-- The genealogy coordinate of the marked model has law `kingmanGenealogyMeasure n`. -/
theorem measurePreserving_genealogy (n : ℕ) (θ : ℝ≥0) :
    MeasurePreserving Prod.fst (kingmanTreeMutationMeasure n θ) (kingmanGenealogyMeasure n) :=
  measurePreserving_fst_compProd _ _

/-- The epoch lengths of the marked model with topology form a Kingman coalescent. -/
def KingmanTimes.ofTreeMutationModel (n : ℕ) (θ : ℝ≥0) :
    KingmanTimes (kingmanTreeMutationMeasure n θ) n where
  T k p := (KingmanTimes.ofPi n).T k p.1.1
  hasLaw k hk := ((KingmanTimes.ofPi n).hasLaw k hk).comp
    (measurePreserving_fst.comp (measurePreserving_genealogy n θ)).hasLaw
  indep := iIndepFun_comp_of_measurePreserving
    (measurePreserving_fst.comp (measurePreserving_genealogy n θ))
    (fun k => by
      simp only [KingmanTimes.ofPi, k.2, ↓reduceDIte]
      exact measurable_pi_apply _)
    (KingmanTimes.ofPi n).indep

/-- In the marked model the epoch lengths are the first genealogy coordinate. -/
theorem KingmanTimes.epochs_ofTreeMutationModel (n : ℕ) (θ : ℝ≥0) :
    (KingmanTimes.ofTreeMutationModel n θ).epochs = fun p => p.1.1 := by
  funext p k
  simp only [KingmanTimes.epochs, KingmanTimes.ofTreeMutationModel, KingmanTimes.ofPi, k.2,
    ↓reduceDIte]

private theorem genealogy_eq (n : ℕ) (θ : ℝ≥0) :
    (fun p : ((Icc 2 n → ℝ) × RankedHistory n) × (KingmanBranch n → ℕ) =>
      ((KingmanTimes.ofTreeMutationModel n θ).epochs p, p.1.2)) = Prod.fst := by
  rw [KingmanTimes.epochs_ofTreeMutationModel]

private theorem measurable_genealogy (n : ℕ) (θ : ℝ≥0) :
    Measurable fun p : ((Icc 2 n → ℝ) × RankedHistory n) × (KingmanBranch n → ℕ) =>
      ((KingmanTimes.ofTreeMutationModel n θ).epochs p, p.1.2) := by
  rw [genealogy_eq]
  exact measurable_fst

/-- In the marked model the branch counts have conditional law `kingmanTreeMutationKernel n θ`
given the genealogy. -/
theorem hasCondDistrib_kingmanTreeMutationMeasure (n : ℕ) (θ : ℝ≥0) :
    HasCondDistrib Prod.snd
      (fun p => ((KingmanTimes.ofTreeMutationModel n θ).epochs p, p.1.2))
      (kingmanTreeMutationKernel n θ) (kingmanTreeMutationMeasure n θ) := by
  rw [genealogy_eq]
  refine ⟨by fun_prop, ?_⟩
  rw [kingmanTreeMutationMeasure, (measurePreserving_fst_compProd _ _).map_eq]
  simp only [Prod.mk.eta]
  exact Measure.map_id

/-- **Expected pairwise differences of one pair in the marked Kingman model**: `E[D_s] = θ`
for every pair `s` of a sample of size `n ≥ 2`, with no remaining hypotheses. -/
theorem integral_pairDiff_kingmanTreeMutationMeasure {θ : ℝ≥0} (hn : 2 ≤ n)
    {s : Finset (Fin n)} (hs : s ∈ samplePairs n) :
    ∫ p, pairDiff (fun p => p.1.2) Prod.snd s p ∂kingmanTreeMutationMeasure n θ = θ := by
  rw [(KingmanTimes.ofTreeMutationModel n θ).integral_pairDiff_of_mutation
    (measurable_genealogy n θ)
    (hasCondDistrib_kingmanTreeMutationMeasure n θ) hs,
    KingmanTimes.epochs_ofTreeMutationModel]
  have h := integral_map (μ := kingmanTreeMutationMeasure n θ) measurable_fst.aemeasurable
    (f := fun g : (Icc 2 n → ℝ) × RankedHistory n => pairCoalTime g.2 s g.1)
    ((measurable_pairCoalTime s).aestronglyMeasurable)
  rw [(measurePreserving_genealogy n θ).map_eq,
    integral_pairCoalTime_kingmanGenealogyMeasure hn hs] at h
  rw [← h, mul_one]

/-- **Tajima's `E π = θ` in the marked Kingman model with random-joining topology** (Tajima
1983): the mean number of pairwise differences of a sample of size `n ≥ 2` has mean `θ`, with
no remaining hypotheses. -/
theorem integral_meanPairDiff_kingmanTreeMutationMeasure {θ : ℝ≥0} (hn : 2 ≤ n) :
    ∫ p, meanPairDiff n (pairDiff (fun p => p.1.2) Prod.snd) p ∂kingmanTreeMutationMeasure n θ =
      θ := by
  have hint : ∀ s ∈ samplePairs n,
      Integrable (pairDiff (fun p => p.1.2) Prod.snd s) (kingmanTreeMutationMeasure n θ) :=
    fun s _ => (KingmanTimes.ofTreeMutationModel n θ).integrable_pairDiff_of_mutation
      (measurable_genealogy n θ) (hasCondDistrib_kingmanTreeMutationMeasure n θ) s
  have hc : ((n.choose 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hn).ne'
  unfold meanPairDiff
  rw [integral_const_mul, integral_finsetSum _ hint,
    Finset.sum_congr rfl fun s hs => integral_pairDiff_kingmanTreeMutationMeasure hn hs,
    Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end Model

/-! ### The law of the coalescence time of a pair -/

section Law

open Complex

variable {n : ℕ}

/-- The ratio `(m - 1) / (m + 1)`; the probability that a pair is still apart with `m` lineages
is `pairSeparateProb n m = ((n + 1) / (n - 1)) * pairRatio m`. -/
noncomputable def pairRatio (m : ℕ) : ℂ := ((m : ℂ) - 1) / ((m : ℂ) + 1)

/-- `C(m, 2) (r_m - r_{m-1}) = r_m`: given apart with `m` lineages, the pair coalesces at the next
event with probability `1 / C(m, 2)`. -/
private theorem choose_mul_pairRatio_sub {m : ℕ} (hm : 2 ≤ m) :
    ((m.choose 2 : ℕ) : ℂ) * (pairRatio m - pairRatio (m - 1)) = pairRatio m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [Nat.cast_choose_two, pairRatio, pairRatio, Nat.add_sub_cancel]
  push_cast
  have h1 : (j : ℂ) + 1 + 1 ≠ 0 := by norm_cast
  have h2 : (j : ℂ) + 1 ≠ 0 := by norm_cast
  field_simp
  ring

/-- **The mixture identity behind `τ ~ Exp(1)`**: mixing the hypoexponential sums
`T_m + ⋯ + T_N` (`T_k ~ Exp(C(k, 2))`) over the epoch `m` in which the pair coalesces, with
weights `r_m - r_{m-1}`, gives `r_N` times the `Exp(1)` transform `1 / (1 - z)`. -/
theorem sum_pairRatio_prod {z : ℂ} (hz : ∀ k, 2 ≤ k → z ≠ ((k.choose 2 : ℕ) : ℂ)) {N : ℕ}
    (hN : 2 ≤ N) :
    ∑ m ∈ Icc 2 N, (pairRatio m - pairRatio (m - 1)) *
        ∏ k ∈ Icc m N, ((k.choose 2 : ℕ) : ℂ) / (((k.choose 2 : ℕ) : ℂ) - z) =
      pairRatio N / (1 - z) := by
  have h1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (by simpa using (hz 2 le_rfl).symm)
  induction N, hN using Nat.le_induction with
  | base =>
    simp [pairRatio]
    norm_num
    ring
  | succ N hN ih =>
    have hc : ((N + 1).choose 2 : ℕ) - z ≠ (0 : ℂ) := sub_ne_zero.2 (hz _ (by omega)).symm
    rw [sum_Icc_succ_top (by omega)]
    have : ∀ m ∈ Icc 2 N, (pairRatio m - pairRatio (m - 1)) *
        ∏ k ∈ Icc m (N + 1), ((k.choose 2 : ℕ) : ℂ) / (((k.choose 2 : ℕ) : ℂ) - z) =
        (pairRatio m - pairRatio (m - 1)) *
          (∏ k ∈ Icc m N, ((k.choose 2 : ℕ) : ℂ) / (((k.choose 2 : ℕ) : ℂ) - z)) *
          (((N + 1).choose 2 : ℕ) / ((((N + 1).choose 2 : ℕ) : ℂ) - z)) := fun m hm => by
      rw [prod_Icc_succ_top (by simp at hm; omega), mul_assoc]
    rw [sum_congr rfl this, ← sum_mul, ih, Nat.add_sub_cancel, Icc_self, prod_singleton]
    have key := choose_mul_pairRatio_sub (m := N + 1) (by omega)
    rw [Nat.add_sub_cancel] at key
    field_simp
    linear_combination (-z) * key

/-- A predicate on `1, …, n` that is false at `1`, true at `n` and upward closed is a threshold
`M ≤ k` with `2 ≤ M ≤ n`. -/
private theorem exists_threshold (a : ℕ → Prop) (hn2 : 2 ≤ n) (h1 : ¬a 1)
    (hn : a n) (hmono : ∀ k, 1 ≤ k → k < n → a k → a (k + 1)) :
    ∃ M, 2 ≤ M ∧ M ≤ n ∧ ∀ k, 1 ≤ k → k ≤ n → (a k ↔ M ≤ k) := by
  have hex : ∃ k, 1 ≤ k ∧ a k := ⟨n, by omega, hn⟩
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_min' hex ⟨by omega, hn⟩, fun k hk1 hkn => ⟨fun hk =>
    Nat.find_min' hex ⟨hk1, hk⟩, fun hk => ?_⟩⟩
  · obtain ⟨hM1, hMa⟩ := Nat.find_spec hex
    by_contra hlt
    have : Nat.find hex = 1 := by omega
    exact h1 (this ▸ hMa)
  · obtain ⟨-, hMa⟩ := Nat.find_spec hex
    induction k, hk using Nat.le_induction with
    | base => exact hMa
    | succ k hk ih =>
      have := (Nat.find_spec hex).1
      exact hmono k (by omega) (by omega) (ih (by omega) (by omega))

/-- **Telescoping over a threshold**: if `a k ↔ M ≤ k` on `1, …, n`, the product of `φ k` over
the `k ∈ [2, n]` with `a k` is `∑_m (1[a m] - 1[a (m - 1)]) ∏_{k=m}^n φ k`, whose only nonzero
term is `m = M`. The right side is linear in the indicators. -/
private theorem prod_ite_eq_sum_of_threshold {M : ℕ} (hM : 2 ≤ M) (hMn : M ≤ n) (a : ℕ → Prop)
    [DecidablePred a] (ha : ∀ k, 1 ≤ k → k ≤ n → (a k ↔ M ≤ k)) (φ : ℕ → ℂ) :
    ∏ k ∈ Icc 2 n, (if a k then φ k else 1) =
      ∑ m ∈ Icc 2 n, ((if a m then (1 : ℂ) else 0) - (if a (m - 1) then 1 else 0)) *
        ∏ k ∈ Icc m n, φ k := by
  rw [Finset.sum_eq_single M]
  · rw [ite_eq_left ((ha M (by omega) hMn).2 le_rfl), ite_eq_right (fun h => by
      have := (ha (M - 1) (by omega) (by omega)).1 h; omega), sub_zero, one_mul,
      prod_ite, prod_const_one, mul_one]
    congr 1
    ext k
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h2, hkn⟩, hk⟩
      exact ⟨(ha k (by omega) hkn).1 hk, hkn⟩
    · rintro ⟨hMk, hkn⟩
      exact ⟨⟨by omega, hkn⟩, (ha k (by omega) hkn).2 hMk⟩
  · intro m hm hmM
    simp only [mem_Icc] at hm
    have e1 := ha m (by omega) hm.2
    have e2 := ha (m - 1) (by omega) (by omega)
    rcases lt_or_gt_of_ne hmM with h | h
    · rw [ite_eq_right (fun x => by have := e1.1 x; omega),
        ite_eq_right (fun x => by have := e2.1 x; omega)]
      simp
    · rw [ite_eq_left (e1.2 (by omega)), ite_eq_left (e2.2 (by omega))]
      simp
  · intro h
    exact absurd (mem_Icc.2 ⟨hM, hMn⟩) h

/-- **A sum of exponential epochs stopped at a threshold epoch is `Exp(1)`.** Let the epochs be
independent `T_k ~ Exp(C(k, 2))` (`piMeasure n`) and, independently, let `h ~ ν` select the epochs
`k` with `A h k`, an upward-closed set containing `n` but not `1`. If
`P(A · k) = (k - 1)(n + 1) / ((n - 1)(k + 1))` for `1 ≤ k ≤ n`, then `∑_{k : A h k} T_k` has law
`Exp(1)`. The proof compares characteristic functions: conditionally on `h` the transform is
`∏_{k : A h k} C(k, 2) / (C(k, 2) - i u)`, which `prod_ite_eq_sum_of_threshold` makes linear in
the indicators, and `sum_pairRatio_prod` sums to `1 / (1 - i u)`. -/
theorem hasLaw_sum_ite_of_threshold {H : Type*} [Finite H] [MeasurableSpace H]
    [DiscreteMeasurableSpace H] (ν : Measure H) [IsProbabilityMeasure ν] (A : H → ℕ → Prop)
    [∀ h k, Decidable (A h k)] (hn : 2 ≤ n) (h1 : ∀ h, ¬A h 1) (hN : ∀ h, A h n)
    (hmono : ∀ h k, 1 ≤ k → k < n → A h k → A h (k + 1))
    (hp : ∀ k, 1 ≤ k → k ≤ n → ∫ h, (if A h k then (1 : ℝ) else 0) ∂ν =
      ((k : ℝ) - 1) * ((n : ℝ) + 1) / (((n : ℝ) - 1) * ((k : ℝ) + 1))) :
    HasLaw (fun g : (Icc 2 n → ℝ) × H => ∑ k : Icc 2 n, if A g.2 k then g.1 k else 0)
      (expMeasure 1) ((piMeasure n).prod ν) := by
  have hmeas : Measurable fun g : (Icc 2 n → ℝ) × H =>
      ∑ k : Icc 2 n, if A g.2 k then g.1 k else 0 :=
    Finset.measurable_sum _ fun k _ => Measurable.ite
      (measurable_snd (MeasurableSet.of_discrete : MeasurableSet {h : H | A h k}))
      ((measurable_pi_apply k).comp measurable_fst) measurable_const
  have := isProbabilityMeasure_expMeasure (zero_lt_one' ℝ)
  refine ⟨hmeas.aemeasurable, Measure.ext_of_charFun (funext fun u => ?_)⟩
  rw [charFun_apply, integral_map hmeas.aemeasurable (by fun_prop), charFun_expMeasure one_pos]
  set z : ℂ := u * I with hz_def
  have hint : Integrable (fun g : (Icc 2 n → ℝ) × H =>
      cexp (↑(inner ℝ (∑ k : Icc 2 n, if A g.2 k then g.1 k else 0) u) * I))
      ((piMeasure n).prod ν) :=
    Integrable.of_bound (((by fun_prop : Continuous fun x : ℝ =>
      cexp (↑(inner ℝ x u) * I)).measurable.comp hmeas).aestronglyMeasurable) 1
      (ae_of_all _ fun g => by
        rw [Complex.norm_exp_ofReal_mul_I])
  rw [integral_prod_symm _ hint]
  set φ : ℕ → ℂ := fun k => ((k.choose 2 : ℕ) : ℂ) / (((k.choose 2 : ℕ) : ℂ) - z) with hφ
  have hinner : ∀ h, ∫ t, cexp (↑(inner ℝ (∑ k : Icc 2 n, if A h k then t k else 0) u) * I)
      ∂piMeasure n = ∏ k ∈ Icc 2 n, (if A h k then φ k else 1) := by
    intro h
    have hprod : ∀ t : Icc 2 n → ℝ,
        cexp (↑(inner ℝ (∑ k : Icc 2 n, if A h k then t k else 0) u) * I) =
        ∏ k : Icc 2 n, (fun (k : Icc 2 n) (x : ℝ) =>
          if A h k then cexp (↑(inner ℝ x u) * I) else 1) k (t k) := by
      intro t
      simp only [RCLike.inner_apply, conj_trivial]
      rw [Finset.mul_sum, ofReal_sum, Finset.sum_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun k _ => ?_
      split_ifs <;> simp
    refine (integral_congr_ae (ae_of_all _ hprod)).trans ?_
    rw [piMeasure, integral_fintype_prod_eq_prod (fun (k : Icc 2 n) (x : ℝ) =>
      if A h k then cexp (↑(inner ℝ x u) * I) else 1), ← Finset.prod_coe_sort (Icc 2 n)]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs
    · rw [← charFun_apply, charFun_expMeasure (KingmanTimes.choose_two_pos k.2)]
      simp [φ, z]
    · simp
  simp_rw [hinner]
  have htel : ∀ h, ∏ k ∈ Icc 2 n, (if A h k then φ k else 1) =
      ∑ m ∈ Icc 2 n, ((if A h m then (1 : ℂ) else 0) - (if A h (m - 1) then 1 else 0)) *
        ∏ k ∈ Icc m n, φ k := fun h => by
    obtain ⟨M, hM2, hMn, hM⟩ := exists_threshold (A h) hn (h1 h) (hN h) (hmono h)
    exact prod_ite_eq_sum_of_threshold hM2 hMn (A h) hM φ
  simp_rw [htel]
  rw [integral_finsetSum _ fun m _ => Integrable.of_finite]
  simp_rw [integral_mul_const]
  set κ : ℂ := ((n : ℂ) + 1) / ((n : ℂ) - 1) with hκ
  have hind : ∀ k, 1 ≤ k → k ≤ n →
      ∫ h, (if A h k then (1 : ℂ) else 0) ∂ν = κ * pairRatio k := by
    intro k hk1 hkn
    have e : (fun h => if A h k then (1 : ℂ) else 0) =
        fun h => ((if A h k then (1 : ℝ) else 0 : ℝ) : ℂ) := by
      funext h
      split_ifs <;> simp
    rw [e, integral_complex_ofReal, hp k hk1 hkn, pairRatio, hκ]
    push_cast
    rw [mul_comm ((k : ℂ) - 1), mul_div_mul_comm]
  rw [Finset.sum_congr rfl fun m hm => by
    rw [integral_sub Integrable.of_finite Integrable.of_finite,
      hind m (by simp at hm; omega) (by simp at hm; omega),
      hind (m - 1) (by simp at hm; omega) (by simp at hm; omega), ← mul_sub, mul_assoc]]
  rw [← Finset.mul_sum, sum_pairRatio_prod (fun k hk heq => ?_) hn]
  · have hn1 : (n : ℂ) - 1 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hn2 : (n : ℂ) + 1 ≠ 0 := by norm_cast
    rw [hκ, pairRatio, hz_def]
    field_simp
    simp
  · have := congrArg Complex.re heq
    simp [hz_def] at this
    exact (Nat.choose_pos hk).ne' (by exact_mod_cast this.symm)

/-- After `n - 1` events all genes are in one lineage, so no pair is apart. -/
theorem not_pairApart_sub_one (h : RankedHistory n) (hn : 1 ≤ n) (a b : Fin n) :
    ¬PairApart h {a, b} (n - 1) := by
  obtain ⟨hlen, pos, hP⟩ := blocksAfter_spec h (t := n - 1) le_rfl
  rw [pairApart_iff hP, not_not]
  have ha := (hP a).1
  have hb := (hP b).1
  rw [hlen] at ha hb
  omega

/-- **The coalescence time of a pair is `Exp(1)`** (in units of `2N` generations) in the Kingman
genealogy with random-joining topology: the hypothesis `hτ` of `integral_meanPairDiff`. While
the pair is apart with `k` lineages, the next event merges it with probability `1 / C(k, 2)` and
comes at rate `C(k, 2)`, so the pair coalesces at rate one. -/
theorem hasLaw_pairCoalTime_kingmanGenealogyMeasure (hn : 2 ≤ n) {s : Finset (Fin n)}
    (hs : s ∈ samplePairs n) :
    HasLaw (fun g : (Icc 2 n → ℝ) × RankedHistory n => pairCoalTime g.2 s g.1) (expMeasure 1)
      (kingmanGenealogyMeasure n) := by
  have hs' := hs
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (Finset.mem_powersetCard.1 hs).2
  refine hasLaw_sum_ite_of_threshold (randomJoining n) (fun h k => PairApart h {a, b} (n - k)) hn
    (fun h => not_pairApart_sub_one h (by omega) a b)
    (fun h => by simpa using pairApart_zero h hab)
    (fun h k hk1 hkn H => ?_) (fun k hk1 hkn => ?_)
  · have e : n - k = n - (k + 1) + 1 := by omega
    rw [e] at H
    exact H.of_succ
  · rcases Nat.eq_or_lt_of_le hk1 with rfl | hk
    · have : ∀ h : RankedHistory n, (if PairApart h {a, b} (n - 1) then (1 : ℝ) else 0) = 0 :=
        fun h => ite_eq_right (not_pairApart_sub_one h (by omega) a b)
      simp only [Nat.cast_one, sub_self, zero_mul, zero_div]
      simp_rw [this, integral_zero]
    · rw [integral_pairApart_randomJoining hs' (Finset.mem_Icc.2 ⟨hk, hkn⟩), pairSeparateProb]

/-- In the marked Kingman model the coalescence time of every pair is `Exp(1)`. -/
theorem hasLaw_pairCoalTime_kingmanTreeMutationMeasure {θ : ℝ≥0} (hn : 2 ≤ n)
    {s : Finset (Fin n)} (hs : s ∈ samplePairs n) :
    HasLaw (fun p : ((Icc 2 n → ℝ) × RankedHistory n) × (KingmanBranch n → ℕ) =>
      pairCoalTime p.1.2 s p.1.1) (expMeasure 1) (kingmanTreeMutationMeasure n θ) :=
  (hasLaw_pairCoalTime_kingmanGenealogyMeasure hn hs).comp
    (measurePreserving_genealogy n θ).hasLaw

end Law

/-! ### Second moments of pairwise differences -/

section SecondMoment

variable {n : ℕ}

/-- The total length of the branches separating **both** pairs `s` and `s'`: mutations there are
counted in both `D_s` and `D_{s'}`. -/
def pairPathOverlap (h : RankedHistory n) (s s' : Finset (Fin n)) (t : Icc 2 n → ℝ) : ℝ :=
  ∑ b ∈ pairPath h s ∩ pairPath h s', (kingmanBranchLength n t b : ℝ)

/-- Product moments of the coordinates of a product of laws on `ℕ` with finite second moments:
`E[N_b N_b'] = E[N_b²]` if `b = b'` and `E[N_b] E[N_b']` otherwise. -/
private theorem integrable_and_integral_natCast_mul_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : ι → Measure ℕ) [∀ i, IsProbabilityMeasure (ν i)]
    (h1 : ∀ i, Integrable (fun n : ℕ => (n : ℝ)) (ν i))
    (h2 : ∀ i, Integrable (fun n : ℕ => (n : ℝ) ^ 2) (ν i)) (b b' : ι) :
    Integrable (fun N : ι → ℕ => (N b : ℝ) * N b') (Measure.pi ν) ∧
      ∫ N, (N b : ℝ) * N b' ∂Measure.pi ν = if b = b' then ∫ n, (n : ℝ) ^ 2 ∂ν b
        else (∫ n, (n : ℝ) ∂ν b) * ∫ n, (n : ℝ) ∂ν b' := by
  have hev : ∀ i, MeasurePreserving (fun N : ι → ℕ => N i) (Measure.pi ν) (ν i) :=
    fun i => measurePreserving_eval ν i
  have heval : ∀ i (f : ℕ → ℝ), ∫ N, f (N i) ∂Measure.pi ν = ∫ n, f n ∂ν i := fun i f => by
    rw [← (hev i).map_eq, integral_map (hev i).measurable.aemeasurable
      (measurable_of_countable f).aestronglyMeasurable]
  by_cases hbb : b = b'
  · subst hbb
    simp only [↓reduceIte, ← sq]
    exact ⟨(hev b).integrable_comp_of_integrable (h2 b), heval b fun n => (n : ℝ) ^ 2⟩
  · simp only [hbb, ↓reduceIte]
    have hind : IndepFun (fun N : ι → ℕ => (N b : ℝ)) (fun N => (N b' : ℝ)) (Measure.pi ν) :=
      (iIndepFun_pi (μ := ν) (X := fun _ (n : ℕ) => (n : ℝ)) (fun _ => by fun_prop)).indepFun hbb
    have hi : ∀ i, Integrable (fun N : ι → ℕ => (N i : ℝ)) (Measure.pi ν) :=
      fun i => (hev i).integrable_comp_of_integrable (h1 i)
    refine ⟨IndepFun.integrable_mul hind (hi b) (hi b'), ?_⟩
    have := IndepFun.integral_mul_eq_mul_integral hind (hi b).aestronglyMeasurable
      (hi b').aestronglyMeasurable
    rw [Pi.mul_def] at this
    rw [this, heval b fun n => (n : ℝ), heval b' fun n => (n : ℝ)]

/-- The mutation kernel at a genealogy `g`: independent `Po((θ/2) ℓ_b)` counts. -/
theorem kingmanTreeMutationKernel_apply (θ : ℝ≥0) (g : (Icc 2 n → ℝ) × RankedHistory n) :
    kingmanTreeMutationKernel n θ g =
      Measure.pi fun b => poissonMeasure (θ / 2 * kingmanBranchLength n g.1 b) := by
  rw [kingmanTreeMutationKernel, Kernel.comap_apply, kingmanMutationKernel, branchMutationKernel,
    Kernel.comap_apply, piPoissonKernel_apply]

/-- **Conditional product moment of two pairwise differences**: given the genealogy, the counts on
the branches are independent Poisson with means `λ_b = (θ/2) ℓ_b`, so
`E[D_s D_{s'} | g] = (∑_{b ∈ path s} λ_b)(∑_{b ∈ path s'} λ_b) + ∑_{b ∈ path s ∩ path s'} λ_b`:
the Poisson variance of a shared branch adds to the product of the means. -/
theorem integral_pairDiff_mul_kernel (θ : ℝ≥0) (g : (Icc 2 n → ℝ) × RankedHistory n)
    (s s' : Finset (Fin n)) :
    ∫ N, ((∑ b ∈ pairPath g.2 s, N b : ℕ) : ℝ) * ((∑ b ∈ pairPath g.2 s', N b : ℕ) : ℝ)
        ∂kingmanTreeMutationKernel n θ g =
      (∑ b ∈ pairPath g.2 s, ((θ / 2 * kingmanBranchLength n g.1 b : ℝ≥0) : ℝ)) *
          (∑ b ∈ pairPath g.2 s', ((θ / 2 * kingmanBranchLength n g.1 b : ℝ≥0) : ℝ)) +
        ∑ b ∈ pairPath g.2 s ∩ pairPath g.2 s',
          ((θ / 2 * kingmanBranchLength n g.1 b : ℝ≥0) : ℝ) := by
  classical
  set lam : KingmanBranch n → ℝ := fun b => ((θ / 2 * kingmanBranchLength n g.1 b : ℝ≥0) : ℝ)
    with hlam
  have hm := integrable_and_integral_natCast_mul_pi
    (fun b => poissonMeasure (θ / 2 * kingmanBranchLength n g.1 b))
    (fun b => integrable_natCast_poissonMeasure _) (fun b => integrable_natCast_sq_poissonMeasure _)
  rw [kingmanTreeMutationKernel_apply]
  simp_rw [Nat.cast_sum, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun b' _ => (hm b b').1,
    Finset.sum_congr rfl fun b _ => integral_finsetSum _ fun b' _ => (hm b b').1]
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => (hm b b').2]
  simp only [integral_natCast_sq_poissonMeasure, integral_natCast_poissonMeasure]
  have hsplit : ∀ b b', (if b = b' then lam b + lam b ^ 2 else lam b * lam b') =
      lam b * lam b' + if b = b' then lam b else 0 := by
    intro b b'
    split_ifs with h
    · subst h
      ring
    · ring
  simp_rw [hlam] at hsplit
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul_sum, Finset.sum_ite_eq,
    Finset.sum_ite_mem]
  rfl

/-- Each branch count is square integrable in the marked model. -/
private theorem memLp_branch_kingmanTreeMutationMeasure (θ : ℝ≥0) (b : KingmanBranch n) :
    MemLp (fun p : ((Icc 2 n → ℝ) × RankedHistory n) × (KingmanBranch n → ℕ) => (p.2 b : ℝ)) 2
      (kingmanTreeMutationMeasure n θ) := by
  refine memLp_two_natCast_of_hasCondDistrib_poisson
    (hasCondDistrib_branch_of_treeMutation (hasCondDistrib_kingmanTreeMutationMeasure n θ) b) ?_
  have := ((KingmanTimes.ofTreeMutationModel n θ).memLp_T b.1.2).pos_part.const_mul ((θ : ℝ) / 2)
  simpa [kingmanBranchLength, KingmanTimes.epochs, Real.coe_toNNReal'] using this

/-- The pairwise difference as a sum over all branches, pointwise. -/
private theorem pairDiff_apply_eq {Ω : Type*} (H : Ω → RankedHistory n)
    (N : Ω → KingmanBranch n → ℕ) (s : Finset (Fin n)) (ω : Ω) :
    pairDiff H N s ω = ∑ b, (if b ∈ pairPath (H ω) s then (1 : ℝ) else 0) * (N ω b : ℝ) := by
  simp only [pairDiff, Nat.cast_sum, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **The product of two pairwise differences is integrable** in the marked model. -/
theorem integrable_pairDiff_mul_kingmanTreeMutationMeasure (θ : ℝ≥0) (s s' : Finset (Fin n)) :
    Integrable (fun p => pairDiff (fun p => p.1.2) Prod.snd s p *
      pairDiff (fun p => p.1.2) Prod.snd s' p) (kingmanTreeMutationMeasure n θ) := by
  have hterm : ∀ b b' : KingmanBranch n, Integrable
      (fun p : ((Icc 2 n → ℝ) × RankedHistory n) × (KingmanBranch n → ℕ) =>
        ((if b ∈ pairPath p.1.2 s then (1 : ℝ) else 0) *
          (if b' ∈ pairPath p.1.2 s' then (1 : ℝ) else 0)) * ((p.2 b : ℝ) * (p.2 b' : ℝ)))
      (kingmanTreeMutationMeasure n θ) := fun b b' => by
    refine ((memLp_branch_kingmanTreeMutationMeasure θ b).integrable_mul
      (memLp_branch_kingmanTreeMutationMeasure θ b')).bdd_mul (c := 1) ?_
      (ae_of_all _ fun p => ?_)
    · exact ((Measurable.of_discrete (f := fun h : RankedHistory n =>
        (if b ∈ pairPath h s then (1 : ℝ) else 0) *
          (if b' ∈ pairPath h s' then (1 : ℝ) else 0))).comp
            (measurable_snd.comp measurable_fst)).aestronglyMeasurable
    · split_ifs <;> simp
  have heq : (fun p => pairDiff (fun p => p.1.2) Prod.snd s p *
      pairDiff (fun p => p.1.2) Prod.snd s' p) =
      fun p : ((Icc 2 n → ℝ) × RankedHistory n) × (KingmanBranch n → ℕ) => ∑ b, ∑ b',
        ((if b ∈ pairPath p.1.2 s then (1 : ℝ) else 0) *
          (if b' ∈ pairPath p.1.2 s' then (1 : ℝ) else 0)) * ((p.2 b : ℝ) * (p.2 b' : ℝ)) := by
    funext p
    rw [pairDiff_apply_eq, pairDiff_apply_eq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    ring
  rw [heq]
  exact integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun b' _ => hterm b b'

/-- The epoch lengths of the genealogy are a.s. nonnegative. -/
private theorem ae_nonneg_kingmanGenealogyMeasure :
    ∀ᵐ g ∂kingmanGenealogyMeasure n, ∀ k : Icc 2 n, 0 ≤ g.1 k := by
  have hpi : ∀ᵐ t ∂piMeasure n, ∀ k : Icc 2 n, 0 ≤ t k := by
    filter_upwards [(KingmanTimes.ofPi n).ae_nonneg_epochs] with t ht k
    have := ht k
    simpa [KingmanTimes.epochs, KingmanTimes.ofPi, (Finset.mem_Icc.1 k.2).1,
      (Finset.mem_Icc.1 k.2).2] using this
  exact (measurePreserving_fst (μ := piMeasure n) (ν := randomJoining n)).quasiMeasurePreserving.ae
    hpi

/-- For nonnegative epoch lengths the path between the two genes of `s` has length `2 τ_s`. -/
private theorem sum_pairPath_eq_two_mul (h : RankedHistory n) {t : Icc 2 n → ℝ}
    (ht : ∀ k, 0 ≤ t k) {s : Finset (Fin n)} (hs : s ∈ samplePairs n) :
    ∑ b ∈ pairPath h s, (kingmanBranchLength n t b : ℝ) = 2 * pairCoalTime h s t := by
  have hpath := congrArg (fun x : ℝ≥0 => (x : ℝ)) (sum_pairPath_branchLength h hs t)
  simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_ofNat] at hpath
  rw [hpath, pairCoalTime]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [Real.coe_toNNReal _ (ht k)]

/-- The coalescence time of a pair is square integrable. -/
private theorem memLp_pairCoalTime (hn : 2 ≤ n) {s : Finset (Fin n)} (hs : s ∈ samplePairs n) :
    MemLp (fun g : (Icc 2 n → ℝ) × RankedHistory n => pairCoalTime g.2 s g.1) 2
      (kingmanGenealogyMeasure n) := by
  have := isProbabilityMeasure_expMeasure (zero_lt_one' ℝ)
  refine (hasLaw_pairCoalTime_kingmanGenealogyMeasure hn hs).memLp ?_
  exact (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
    (by simpa using integrable_pow_expMeasure one_pos 2)

/-- The overlap length is integrable. -/
private theorem integrable_pairPathOverlap (s s' : Finset (Fin n)) :
    Integrable (fun g : (Icc 2 n → ℝ) × RankedHistory n => pairPathOverlap g.2 s s' g.1)
      (kingmanGenealogyMeasure n) := by
  have heq : (fun g : (Icc 2 n → ℝ) × RankedHistory n => pairPathOverlap g.2 s s' g.1) =
      fun g => ∑ b, (if b ∈ pairPath g.2 s ∩ pairPath g.2 s' then (1 : ℝ) else 0) *
        max (g.1 b.1) 0 := by
    funext g
    simp only [pairPathOverlap, kingmanBranchLength, Real.coe_toNNReal', ite_mul, one_mul,
      zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [heq]
  refine integrable_finsetSum _ fun b _ => ?_
  have hT : Integrable (fun g : (Icc 2 n → ℝ) × RankedHistory n => max (g.1 b.1) 0)
      (kingmanGenealogyMeasure n) := by
    have hTi : Integrable (fun t : Icc 2 n → ℝ => t b.1) (piMeasure n) := by
      have := (KingmanTimes.ofPi n).integrable_T b.1.2
      simpa [KingmanTimes.ofPi, Finset.mem_Icc.1 b.1.2] using this
    exact (measurePreserving_fst (μ := piMeasure n)
      (ν := randomJoining n)).integrable_comp_of_integrable hTi.pos_part
  refine hT.bdd_mul (c := 1) ?_ (ae_of_all _ fun g => ?_)
  · exact ((Measurable.of_discrete (f := fun h : RankedHistory n =>
      if b ∈ pairPath h s ∩ pairPath h s' then (1 : ℝ) else 0)).comp
        measurable_snd).aestronglyMeasurable
  · split_ifs <;> simp

/-- **Product moment of two pairwise differences** in the marked Kingman model:
`E[D_s D_{s'}] = θ² E[τ_s τ_{s'}] + (θ/2) E[ℓ(path s ∩ path s')]`. The first term is the
product of the conditional means `θ τ_s`, `θ τ_{s'}`; the second is the Poisson variance of the
mutations on the branches separating both pairs. This reduces Tajima's `Var π` to moments of the
genealogy. -/
theorem integral_pairDiff_mul_kingmanTreeMutationMeasure {θ : ℝ≥0} (hn : 2 ≤ n)
    {s s' : Finset (Fin n)} (hs : s ∈ samplePairs n) (hs' : s' ∈ samplePairs n) :
    ∫ p, pairDiff (fun p => p.1.2) Prod.snd s p * pairDiff (fun p => p.1.2) Prod.snd s' p
        ∂kingmanTreeMutationMeasure n θ =
      (θ : ℝ) ^ 2 * ∫ g, pairCoalTime g.2 s g.1 * pairCoalTime g.2 s' g.1
          ∂kingmanGenealogyMeasure n +
        (θ : ℝ) / 2 * ∫ g, pairPathOverlap g.2 s s' g.1 ∂kingmanGenealogyMeasure n := by
  have hint := integrable_pairDiff_mul_kingmanTreeMutationMeasure θ s s'
  rw [kingmanTreeMutationMeasure] at hint ⊢
  rw [Measure.integral_compProd hint]
  have hi1 := ((memLp_pairCoalTime hn hs).integrable_mul (memLp_pairCoalTime hn hs')).const_mul
    ((θ : ℝ) ^ 2)
  have hi2 := (integrable_pairPathOverlap (n := n) s s').const_mul ((θ : ℝ) / 2)
  simp only [Pi.mul_apply] at hi1
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add hi1 hi2]
  refine integral_congr_ae ?_
  filter_upwards [ae_nonneg_kingmanGenealogyMeasure] with g hg
  simp only [pairDiff]
  rw [integral_pairDiff_mul_kernel]
  have hsum : ∀ {s : Finset (Fin n)}, s ∈ samplePairs n →
      ∑ b ∈ pairPath g.2 s, ((θ / 2 * kingmanBranchLength n g.1 b : ℝ≥0) : ℝ) =
        (θ : ℝ) * pairCoalTime g.2 s g.1 := fun hs => by
    simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
    rw [← Finset.mul_sum, sum_pairPath_eq_two_mul g.2 hg hs]
    ring
  rw [hsum hs, hsum hs', pairPathOverlap]
  simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
  rw [← Finset.mul_sum]
  ring

/-- **Covariance of two pairwise differences** in the marked Kingman model:
`Cov(D_s, D_{s'}) = θ² Cov(τ_s, τ_{s'}) + (θ/2) E[ℓ(path s ∩ path s')]`. -/
theorem covariance_pairDiff_kingmanTreeMutationMeasure {θ : ℝ≥0} (hn : 2 ≤ n)
    {s s' : Finset (Fin n)} (hs : s ∈ samplePairs n) (hs' : s' ∈ samplePairs n) :
    cov[pairDiff (fun p => p.1.2) Prod.snd s, pairDiff (fun p => p.1.2) Prod.snd s';
        kingmanTreeMutationMeasure n θ] =
      (θ : ℝ) ^ 2 * cov[fun g => pairCoalTime g.2 s g.1, fun g => pairCoalTime g.2 s' g.1;
          kingmanGenealogyMeasure n] +
        (θ : ℝ) / 2 * ∫ g, pairPathOverlap g.2 s s' g.1 ∂kingmanGenealogyMeasure n := by
  have hL2 : ∀ {s : Finset (Fin n)}, MemLp (pairDiff (fun p => p.1.2) Prod.snd s) 2
      (kingmanTreeMutationMeasure n θ) := fun {s} => by
    refine (memLp_two_iff_integrable_sq ((KingmanTimes.ofTreeMutationModel n θ)
      |>.integrable_pairDiff_of_mutation (measurable_genealogy n θ)
        (hasCondDistrib_kingmanTreeMutationMeasure n θ) s).aestronglyMeasurable).2 ?_
    simpa [sq] using integrable_pairDiff_mul_kingmanTreeMutationMeasure θ s s
  have hτ1 : ∀ {s : Finset (Fin n)}, s ∈ samplePairs n →
      ∫ g, pairCoalTime g.2 s g.1 ∂kingmanGenealogyMeasure n = 1 :=
    fun hs => integral_pairCoalTime_kingmanGenealogyMeasure hn hs
  rw [covariance_eq_sub hL2 hL2, covariance_eq_sub (memLp_pairCoalTime hn hs)
    (memLp_pairCoalTime hn hs'), integral_pairDiff_kingmanTreeMutationMeasure hn hs,
    integral_pairDiff_kingmanTreeMutationMeasure hn hs', hτ1 hs, hτ1 hs']
  have := integral_pairDiff_mul_kingmanTreeMutationMeasure (θ := θ) hn hs hs'
  simp only [Pi.mul_apply] at this ⊢
  rw [this]
  ring

/-- **Variance of the pairwise differences of one pair** (Tajima 1983): in the marked Kingman
model `D_s` is geometric with mean `θ`, so `Var D_s = θ + θ²`. Here `E[τ_s²] = 2` from
`τ_s ~ Exp(1)` and the path of `s` overlaps itself in its whole length `2 τ_s`. -/
theorem variance_pairDiff_kingmanTreeMutationMeasure {θ : ℝ≥0} (hn : 2 ≤ n)
    {s : Finset (Fin n)} (hs : s ∈ samplePairs n) :
    Var[pairDiff (fun p => p.1.2) Prod.snd s; kingmanTreeMutationMeasure n θ] =
      (θ : ℝ) + (θ : ℝ) ^ 2 := by
  have := isProbabilityMeasure_expMeasure (zero_lt_one' ℝ)
  have hcov := covariance_pairDiff_kingmanTreeMutationMeasure (θ := θ) hn hs hs
  rw [covariance_self (((KingmanTimes.ofTreeMutationModel n θ)
      |>.integrable_pairDiff_of_mutation (measurable_genealogy n θ)
        (hasCondDistrib_kingmanTreeMutationMeasure n θ) s).aemeasurable),
    covariance_self (measurable_pairCoalTime s).aemeasurable,
    (hasLaw_pairCoalTime_kingmanGenealogyMeasure hn hs).variance_eq_of_expMeasure one_pos] at hcov
  rw [hcov]
  have hover : ∫ g, pairPathOverlap g.2 s s g.1 ∂kingmanGenealogyMeasure n = 2 := by
    rw [integral_congr_ae (g := fun g => 2 * pairCoalTime g.2 s g.1) ?_, integral_const_mul,
      integral_pairCoalTime_kingmanGenealogyMeasure hn hs, mul_one]
    filter_upwards [ae_nonneg_kingmanGenealogyMeasure] with g hg
    rw [pairPathOverlap, Finset.inter_self, sum_pairPath_eq_two_mul g.2 hg hs]
  rw [hover]
  ring

end SecondMoment

/-! ### Distinct pairs: backward recursions over histories -/

section DistinctPairs

variable {n : ℕ}

/-- The coalescence rate `C(n - u, 2)` after `u` events of a sample of size `n`. -/
noncomputable def rateAfter (n u : ℕ) : ℝ := (((n - u).choose 2 : ℕ) : ℝ)

theorem rateAfter_pos {u : ℕ} (hu : u < n - 1) : 0 < rateAfter n u := by
  unfold rateAfter
  exact_mod_cast Nat.choose_pos (by omega)

/-- `1` if the genes of `s` are apart after `u` events of `h`, else `0`. -/
noncomputable def apartInd (h : RankedHistory n) (s : Finset (Fin n)) (u : ℕ) : ℝ :=
  if PairApart h s u then 1 else 0

/-- `X` depends only on the first `t` steps of the history. -/
def DependsBefore (X : RankedHistory n → ℝ) (t : ℕ) : Prop :=
  ∀ (f : RankedHistory n) (j : Fin (n - 1)) (x : LineagePair (n - j)), t ≤ (j : ℕ) →
    X (Function.update f j x) = X f

/-- Changing step `j ≥ u` does not change the partition after `u` events. -/
theorem pairApart_update_of_le {f : RankedHistory n} {j : Fin (n - 1)} (x : LineagePair (n - j))
    {u : ℕ} (hu : u ≤ j) (s : Finset (Fin n)) :
    PairApart (Function.update f j x) s u ↔ PairApart f s u := by
  have hb : blocksAfter (Function.update f j x) u = blocksAfter f u :=
    blocksAfter_congr fun i hi => Function.update_of_ne (fun h => by rw [h] at hi; omega) _ _
  unfold PairApart
  rw [hb]

theorem DependsBefore.mono {X : RankedHistory n → ℝ} {t t' : ℕ} (hX : DependsBefore X t)
    (htt' : t ≤ t') : DependsBefore X t' :=
  fun f j x hj => hX f j x (htt'.trans hj)

theorem DependsBefore.mul {X Y : RankedHistory n → ℝ} {t : ℕ} (hX : DependsBefore X t)
    (hY : DependsBefore Y t) : DependsBefore (fun h => X h * Y h) t :=
  fun f j x hj => by simp only [hX f j x hj, hY f j x hj]

theorem dependsBefore_const (c : ℝ) (t : ℕ) : DependsBefore (n := n) (fun _ => c) t :=
  fun _ _ _ _ => rfl

theorem dependsBefore_ite {t : ℕ} (P : RankedHistory n → Prop) [DecidablePred P]
    (hP : ∀ f (j : Fin (n - 1)) (x : LineagePair (n - j)), t ≤ (j : ℕ) →
      (P (Function.update f j x) ↔ P f)) :
    DependsBefore (fun h => if P h then (1 : ℝ) else 0) t :=
  fun f j x hj => by simp only [hP f j x hj]

/-- **Resampling one step**: summing `F` over histories `C(n - i, 2)` times is summing it over
all histories with step `i` replaced by every possible pair. -/
theorem sum_mul_card_eq_sum_update (F : RankedHistory n → ℝ) (i : Fin (n - 1)) :
    (∑ h, F h) * (((n - (i : ℕ)).choose 2 : ℕ) : ℝ) =
      ∑ h, ∑ x : LineagePair (n - i), F (Function.update h i x) := by
  classical
  let e : RankedHistory n × LineagePair (n - i) ≃ RankedHistory n × LineagePair (n - i) :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have h1 : ∑ h, ∑ x : LineagePair (n - i), F (Function.update h i x) =
      ∑ p : RankedHistory n × LineagePair (n - i), F (e p).1 := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [h1, Equiv.sum_comp e (fun p => F p.1), Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, card_lineagePair, nsmul_eq_mul]
  ring

/-- **Transition counts**: if from every history in state `P` (determined before step `t`)
exactly `m` choices of step `t` lead into `E ⊆ P`, then summing a weight `Y` determined before
step `t` over `E` gives `m / C(n - t, 2)` times its sum over `P`. -/
theorem sum_mul_ite_mul_rateAfter {t : ℕ} (ht : t < n - 1) (Y : RankedHistory n → ℝ)
    (hY : DependsBefore Y t) (P E : RankedHistory n → Prop) [DecidablePred P] [DecidablePred E]
    (hP : ∀ f (x : LineagePair (n - t)), P (Function.update f ⟨t, ht⟩ x) ↔ P f)
    (hEP : ∀ f, E f → P f) (m : ℝ)
    (hm : ∀ f, P f → (#{x : LineagePair (n - t) | E (Function.update f ⟨t, ht⟩ x)} : ℝ) = m) :
    (∑ h, Y h * (if E h then 1 else 0)) * rateAfter n t =
      m * ∑ h, Y h * (if P h then 1 else 0) := by
  classical
  have key := sum_mul_card_eq_sum_update (fun h => Y h * (if E h then (1 : ℝ) else 0)) ⟨t, ht⟩
  rw [rateAfter]
  refine key.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp_rw [hY f ⟨t, ht⟩ _ le_rfl]
  rw [← Finset.mul_sum, Finset.sum_boole]
  by_cases hf : P f
  · rw [hm f hf]
    simp only [hf, ↓reduceIte]
    ring
  · rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ hx =>
      hf ((hP f x).1 (hEP _ hx)))]
    simp [hf]

theorem pairLo_lt_pairHi {k : ℕ} (x : LineagePair k) : pairLo x < pairHi x ∧ pairHi x < k := by
  obtain ⟨a, b, hab, ha, hb, -, hlo, hhi⟩ := pairLo_pairHi_spec x
  rw [hlo, hhi]
  omega

/-- The genes `u, v` are apart after step `t` with pair `x` iff they were apart and `x` is not
the pair of their lineages. -/
theorem pairApart_update_succ_iff {f : RankedHistory n} {t : ℕ} (ht : t < n - 1)
    {pos : Fin n → ℕ} (hP : IsBlockPartition (blocksAfter f t) pos) (x : LineagePair (n - t))
    (u v : Fin n) :
    PairApart (Function.update f ⟨t, ht⟩ x) {u, v} (t + 1) ↔
      ¬(pos u = pos v ∨ (pos u = pairLo x ∧ pos v = pairHi x) ∨
        (pos u = pairHi x ∧ pos v = pairLo x)) := by
  have hcong : blocksAfter (Function.update f ⟨t, ht⟩ x) t = blocksAfter f t :=
    blocksAfter_congr fun j hj => Function.update_of_ne (fun h => by simp [h] at hj) _ _
  have hP' : IsBlockPartition (blocksAfter (Function.update f ⟨t, ht⟩ x) t) pos :=
    hcong.symm ▸ hP
  rw [pairApart_succ_iff ht hP', Function.update_self]

/-- The pairs of lineages whose sorted labels lie in a set `S` of valid label pairs: `#S` of
them. -/
theorem card_lineagePair_mem {k : ℕ} (S : Finset (ℕ × ℕ)) (hS : ∀ p ∈ S, p.1 < p.2 ∧ p.2 < k) :
    #{x : LineagePair k | (pairLo x, pairHi x) ∈ S} = #S := by
  refine Finset.card_bij (fun x _ => (pairLo x, pairHi x))
    (fun x hx => (Finset.mem_filter.1 hx).2) (fun x _ y _ hxy => ?_) (fun p hp => ?_)
  · obtain ⟨u, v, -, -, -, hx, hlx, hhx⟩ := pairLo_pairHi_spec x
    obtain ⟨u', v', -, -, -, hy, hly, hhy⟩ := pairLo_pairHi_spec y
    simp only [Prod.mk.injEq] at hxy
    rw [hlx, hhx, hly, hhy] at hxy
    refine Subtype.ext (Finset.map_injective Fin.valEmbedding ?_)
    rw [hx, hy]
    exact pair_eq_of_minmax (by omega)
  · obtain ⟨h1, h2⟩ := hS p hp
    let x : LineagePair k := ⟨{⟨p.1, lt_trans h1 h2⟩, ⟨p.2, h2⟩},
      Finset.card_pair (fun he => absurd (congrArg Fin.val he) (Nat.ne_of_lt h1))⟩
    have hmap : x.1.map Fin.valEmbedding = {p.1, p.2} := by simp [x]
    obtain ⟨hl, hh⟩ := pairLo_pairHi_of_map x hmap
    have hxp : (pairLo x, pairHi x) = p := by
      rw [hl, hh, min_eq_left h1.le, max_eq_right h1.le]
    exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hxp ▸ hp⟩, hxp⟩

/-- The pairs of lineages whose sorted labels avoid `S`: `C(k, 2) - #S` of them. -/
theorem card_lineagePair_not_mem {k : ℕ} (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 < p.2 ∧ p.2 < k) :
    (#{x : LineagePair k | (pairLo x, pairHi x) ∉ S} : ℝ) = ((k.choose 2 : ℕ) : ℝ) - #S := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (LineagePair k))) (fun x => (pairLo x, pairHi x) ∈ S)
  rw [card_lineagePair_mem S hS, Finset.card_univ, card_lineagePair] at h
  rw [← h]
  push_cast
  ring

/-- From a history in which the pair is apart after `t` events, all but one of the
`C(n - t, 2)` choices of step `t` keep it apart. -/
theorem card_update_pairApart_succ {t : ℕ} (ht : t < n - 1) {a b : Fin n} (f : RankedHistory n)
    (hf : PairApart f {a, b} t) :
    (#{x : LineagePair (n - t) | PairApart (Function.update f ⟨t, ht⟩ x) {a, b} (t + 1)} : ℝ) =
      rateAfter n t - 1 := by
  obtain ⟨hlen, pos, hP⟩ := blocksAfter_spec f ht.le
  rw [pairApart_iff hP] at hf
  have hpa : pos a < n - t := hlen ▸ (hP a).1
  have hpb : pos b < n - t := hlen ▸ (hP b).1
  have hS : ∀ p ∈ ({(min (pos a) (pos b), max (pos a) (pos b))} : Finset (ℕ × ℕ)),
      p.1 < p.2 ∧ p.2 < n - t := by
    simp only [Finset.mem_singleton]
    rintro p rfl
    omega
  rw [Finset.filter_congr (q := fun x : LineagePair (n - t) => (pairLo x, pairHi x) ∉
      ({(min (pos a) (pos b), max (pos a) (pos b))} : Finset (ℕ × ℕ))) (fun x _ => by
    rw [pairApart_update_succ_iff ht hP]
    have := pairLo_lt_pairHi x
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    constructor <;> intro h' <;> omega),
    card_lineagePair_not_mem _ hS, Finset.card_singleton, rateAfter]
  push_cast
  ring

/-- **One step for one pair**: given anything determined before step `t`, a pair apart after `t`
events stays apart with probability `1 - 1 / C(n - t, 2)`. -/
theorem sum_mul_apartInd_succ {t : ℕ} (ht : t < n - 1) {a b : Fin n} (Y : RankedHistory n → ℝ)
    (hY : DependsBefore Y t) :
    ∑ h, Y h * apartInd h {a, b} (t + 1) =
      (1 - (rateAfter n t)⁻¹) * ∑ h, Y h * apartInd h {a, b} t := by
  have hc := (rateAfter_pos ht).ne'
  have key := sum_mul_ite_mul_rateAfter ht Y hY (fun h => PairApart h {a, b} t)
    (fun h => PairApart h {a, b} (t + 1))
    (fun f x => pairApart_update_of_le (j := ⟨t, ht⟩) x le_rfl _)
    (fun f => PairApart.of_succ) (rateAfter n t - 1)
    (fun f hf => card_update_pairApart_succ ht f hf)
  unfold apartInd
  generalize (∑ h, Y h * (if PairApart h {a, b} (t + 1) then (1 : ℝ) else 0)) = X at key ⊢
  generalize (∑ h, Y h * (if PairApart h {a, b} t then (1 : ℝ) else 0)) = Z at key ⊢
  generalize rateAfter n t = c at key hc ⊢
  field_simp
  linear_combination key

/-- Apart after `u` events implies apart after any `t ≤ u` events. -/
theorem pairApart_of_le {h : RankedHistory n} {a b : Fin n} {t u : ℕ} (H : PairApart h {a, b} u)
    (htu : t ≤ u) : PairApart h {a, b} t := by
  induction u, htu using Nat.le_induction with
  | base => exact H
  | succ u _ ih => exact ih H.of_succ

theorem apartInd_mul_of_le (h : RankedHistory n) (a b : Fin n) {t u : ℕ} (htu : t ≤ u) :
    apartInd h {a, b} t * apartInd h {a, b} u = apartInd h {a, b} u := by
  unfold apartInd
  by_cases hu : PairApart h {a, b} u
  · simp [hu, pairApart_of_le hu htu]
  · simp [hu]

theorem apartInd_mul_self (h : RankedHistory n) (s : Finset (Fin n)) (u : ℕ) :
    apartInd h s u * apartInd h s u = apartInd h s u := by
  unfold apartInd
  split_ifs <;> simp

theorem apartInd_sub_one (h : RankedHistory n) (a b : Fin n) :
    apartInd h {a, b} (n - 1) = 0 := by
  simp [apartInd, not_pairApart_sub_one h a.pos a b]

/-- The expected remaining coalescence time of `s` after `t` events, given the history:
`∑_{u ≥ t} 1[s apart after u] / C(n - u, 2)`. -/
noncomputable def futureMean (h : RankedHistory n) (s : Finset (Fin n)) (t : ℕ) : ℝ :=
  ∑ u ∈ Ico t (n - 1), apartInd h s u / rateAfter n u

/-- The diagonal part of `E[τ_s τ_{s'} | h]` after `t` events (the variance of the shared
epochs): `∑_{u ≥ t} 1[s apart] 1[s' apart] / C(n - u, 2)²`. -/
noncomputable def futureDiag (h : RankedHistory n) (s s' : Finset (Fin n)) (t : ℕ) : ℝ :=
  ∑ u ∈ Ico t (n - 1), apartInd h s u * apartInd h s' u / rateAfter n u ^ 2

/-- `E[τ_s^{(t)} τ_{s'}^{(t)} | h]` for the parts of the coalescence times after `t` events. -/
noncomputable def futureProd (h : RankedHistory n) (s s' : Finset (Fin n)) (t : ℕ) : ℝ :=
  futureMean h s t * futureMean h s' t + futureDiag h s s' t

theorem futureMean_succ (h : RankedHistory n) (s : Finset (Fin n)) {t : ℕ} (ht : t < n - 1) :
    futureMean h s t = apartInd h s t / rateAfter n t + futureMean h s (t + 1) := by
  rw [futureMean, futureMean, Finset.sum_eq_sum_Ico_succ_bot ht]

theorem futureDiag_succ (h : RankedHistory n) (s s' : Finset (Fin n)) {t : ℕ}
    (ht : t < n - 1) :
    futureDiag h s s' t =
      apartInd h s t * apartInd h s' t / rateAfter n t ^ 2 + futureDiag h s s' (t + 1) := by
  rw [futureDiag, futureDiag, Finset.sum_eq_sum_Ico_succ_bot ht]

theorem futureProd_succ (h : RankedHistory n) (s s' : Finset (Fin n)) {t : ℕ} (ht : t < n - 1) :
    futureProd h s s' t =
      apartInd h s t * apartInd h s' t * (2 / rateAfter n t ^ 2) +
        apartInd h s t / rateAfter n t * futureMean h s' (t + 1) +
        apartInd h s' t / rateAfter n t * futureMean h s (t + 1) +
        futureProd h s s' (t + 1) := by
  rw [futureProd, futureProd, futureMean_succ h s ht, futureMean_succ h s' ht,
    futureDiag_succ h s s' ht]
  ring

theorem futureProd_end (h : RankedHistory n) (s s' : Finset (Fin n)) :
    futureProd h s s' (n - 1) = 0 := by
  simp [futureProd, futureMean, futureDiag]

/-- The remaining time of a pair vanishes once it has coalesced. -/
theorem apartInd_mul_futureMean (h : RankedHistory n) (a b : Fin n) (t : ℕ) :
    apartInd h {a, b} t * futureMean h {a, b} t = futureMean h {a, b} t := by
  rw [futureMean, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [← mul_div_assoc, apartInd_mul_of_le h a b (Finset.mem_Ico.1 hu).1]

theorem apartInd_mul_futureProd (h : RankedHistory n) (a b c d : Fin n) (t : ℕ) :
    apartInd h {a, b} t * apartInd h {c, d} t * futureProd h {a, b} {c, d} t =
      futureProd h {a, b} {c, d} t := by
  have hD : apartInd h {a, b} t * apartInd h {c, d} t * futureDiag h {a, b} {c, d} t =
      futureDiag h {a, b} {c, d} t := by
    rw [futureDiag, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have h1 := apartInd_mul_of_le h a b (Finset.mem_Ico.1 hu).1
    have h2 := apartInd_mul_of_le h c d (Finset.mem_Ico.1 hu).1
    calc _ = (apartInd h {a, b} t * apartInd h {a, b} u) *
          (apartInd h {c, d} t * apartInd h {c, d} u) / rateAfter n u ^ 2 := by ring
      _ = _ := by rw [h1, h2]
  have e : apartInd h {a, b} t * apartInd h {c, d} t *
      (futureMean h {a, b} t * futureMean h {c, d} t) =
      (apartInd h {a, b} t * futureMean h {a, b} t) *
        (apartInd h {c, d} t * futureMean h {c, d} t) := by ring
  rw [futureProd, mul_add, hD, e, apartInd_mul_futureMean, apartInd_mul_futureMean]

/-- **The remaining coalescence time of a pair has mean one**, whatever happened before: given
anything determined by the first `t` steps, `E[τ^{(t)}] = P(apart after t)`. -/
theorem sum_mul_futureMean {a b : Fin n} (d : ℕ) : ∀ t, t + d = n - 1 →
    ∀ Y : RankedHistory n → ℝ, DependsBefore Y t →
      ∑ h, Y h * futureMean h {a, b} t = ∑ h, Y h * apartInd h {a, b} t := by
  induction d with
  | zero =>
    intro t hd Y _
    obtain rfl : t = n - 1 := by omega
    simp [futureMean, apartInd_sub_one]
  | succ d ih =>
    intro t hd Y hY
    have ht : t < n - 1 := by omega
    have hc := (rateAfter_pos ht).ne'
    simp_rw [futureMean_succ _ _ ht, mul_add, Finset.sum_add_distrib]
    rw [ih (t + 1) (by omega) Y (hY.mono (Nat.le_succ t)), sum_mul_apartInd_succ ht Y hY]
    have : ∑ h, Y h * (apartInd h {a, b} t / rateAfter n t) =
        (∑ h, Y h * apartInd h {a, b} t) / rateAfter n t := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun h _ => by ring
    rw [this]
    field_simp
    ring

/-- **Second moment of the remaining coalescence time of a pair**: `E[(τ^{(t)})²] = 2 P(apart)`,
the `Exp(1)` second moment, given anything determined by the first `t` steps. -/
theorem sum_mul_futureProd_self {a b : Fin n} (d : ℕ) : ∀ t, t + d = n - 1 →
    ∀ Y : RankedHistory n → ℝ, DependsBefore Y t →
      ∑ h, Y h * futureProd h {a, b} {a, b} t = 2 * ∑ h, Y h * apartInd h {a, b} t := by
  induction d with
  | zero =>
    intro t hd Y _
    obtain rfl : t = n - 1 := by omega
    simp [futureProd_end, apartInd_sub_one]
  | succ d ih =>
    intro t hd Y hY
    have ht : t < n - 1 := by omega
    have hc := (rateAfter_pos ht).ne'
    have hYA : DependsBefore (fun h => Y h * apartInd h {a, b} t) (t + 1) :=
      (hY.mul (fun f j x hj => by simp only [apartInd, pairApart_update_of_le x hj])).mono
        (Nat.le_succ t)
    have hM := sum_mul_futureMean (a := a) (b := b) d (t + 1) (by omega) _ hYA
    have hM' : ∑ h, Y h * apartInd h {a, b} t * apartInd h {a, b} (t + 1) =
        ∑ h, Y h * apartInd h {a, b} (t + 1) :=
      Finset.sum_congr rfl fun h _ => by rw [mul_assoc, apartInd_mul_of_le h a b (Nat.le_succ t)]
    rw [hM'] at hM
    have hstep := sum_mul_apartInd_succ ht Y hY (a := a) (b := b)
    have hIH := ih (t + 1) (by omega) Y (hY.mono (Nat.le_succ t))
    simp_rw [futureProd_succ _ _ _ ht, apartInd_mul_self]
    simp only [mul_add, Finset.sum_add_distrib]
    have e1 : ∑ h, Y h * (apartInd h {a, b} t * (2 / rateAfter n t ^ 2)) =
        2 / rateAfter n t ^ 2 * ∑ h, Y h * apartInd h {a, b} t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by ring
    have e2 : ∑ h, Y h * (apartInd h {a, b} t / rateAfter n t * futureMean h {a, b} (t + 1)) =
        (rateAfter n t)⁻¹ * ∑ h, Y h * apartInd h {a, b} t * futureMean h {a, b} (t + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h _ => by ring
    rw [e1, e2, hM, hIH, hstep]
    field_simp
    ring

/-- Together after `t` events implies together afterwards. -/
theorem not_pairApart_of_le {h : RankedHistory n} {a b : Fin n} {t u : ℕ}
    (H : ¬PairApart h {a, b} t) (htu : t ≤ u) : ¬PairApart h {a, b} u :=
  fun H' => H (pairApart_of_le H' htu)

/-- Once `b` and `c` share a lineage, `{a, c}` is apart exactly when `{a, b}` is. -/
theorem pairApart_congr_of_not {h : RankedHistory n} {a b c : Fin n} {t u : ℕ}
    (H : ¬PairApart h {b, c} t) (htu : t ≤ u) (hu : u ≤ n - 1) :
    PairApart h {a, c} u ↔ PairApart h {a, b} u := by
  obtain ⟨-, pos, hP⟩ := blocksAfter_spec h hu
  have H' := not_pairApart_of_le H htu
  rw [pairApart_iff hP, not_not] at H'
  rw [pairApart_iff hP, pairApart_iff hP, H']

theorem futureMean_congr {h : RankedHistory n} {s r : Finset (Fin n)} {t : ℕ}
    (H : ∀ u, t ≤ u → u < n - 1 → (PairApart h s u ↔ PairApart h r u)) :
    futureMean h s t = futureMean h r t := by
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hu
  simp only [apartInd, H u h1 h2]

theorem futureProd_congr {h : RankedHistory n} {s s' r r' : Finset (Fin n)} {t : ℕ}
    (H : ∀ u, t ≤ u → u < n - 1 → (PairApart h s u ↔ PairApart h r u))
    (H' : ∀ u, t ≤ u → u < n - 1 → (PairApart h s' u ↔ PairApart h r' u)) :
    futureProd h s s' t = futureProd h r r' t := by
  have hD : futureDiag h s s' t = futureDiag h r r' t := by
    refine Finset.sum_congr rfl fun u hu => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hu
    simp only [apartInd, H u h1 h2, H' u h1 h2]
  rw [futureProd, futureProd, futureMean_congr H, futureMean_congr H', hD]

/-- The genes `a, b, c` are in three distinct lineages after `t` events. -/
def Apart3 (h : RankedHistory n) (a b c : Fin n) (t : ℕ) : Prop :=
  PairApart h {a, b} t ∧ PairApart h {a, c} t ∧ PairApart h {b, c} t

instance (h : RankedHistory n) (a b c : Fin n) (t : ℕ) : Decidable (Apart3 h a b c t) := by
  unfold Apart3
  infer_instance

/-- After `t` events gene `a` is alone among `a, b, c`, and `b, c` share a lineage. -/
def SplitA (h : RankedHistory n) (a b c : Fin n) (t : ℕ) : Prop :=
  PairApart h {a, b} t ∧ PairApart h {a, c} t ∧ ¬PairApart h {b, c} t

instance (h : RankedHistory n) (a b c : Fin n) (t : ℕ) : Decidable (SplitA h a b c t) := by
  unfold SplitA
  infer_instance

theorem apart3_update_of_le {f : RankedHistory n} {j : Fin (n - 1)} (x : LineagePair (n - j))
    {u : ℕ} (hu : u ≤ j) (a b c : Fin n) :
    Apart3 (Function.update f j x) a b c u ↔ Apart3 f a b c u := by
  simp only [Apart3, pairApart_update_of_le x hu]

theorem Apart3.of_succ {h : RankedHistory n} {a b c : Fin n} {t : ℕ}
    (H : Apart3 h a b c (t + 1)) : Apart3 h a b c t :=
  ⟨H.1.of_succ, H.2.1.of_succ, H.2.2.of_succ⟩

/-- `#{(p, q), (p, r), (q, r)} = 3` for sorted pairs of three distinct labels. -/
private theorem card_sortedPairs_three {p q r : ℕ} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    #({(min p q, max p q), (min p r, max p r), (min q r, max q r)} : Finset (ℕ × ℕ)) = 3 := by
  rw [Finset.card_insert_of_notMem, Finset.card_pair]
  · simp only [ne_eq, Prod.mk.injEq]
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega

/-- From three distinct lineages, `C(k, 2) - 3` choices of the next step keep them distinct. -/
theorem card_update_apart3_succ {t : ℕ} (ht : t < n - 1) {a b c : Fin n} (f : RankedHistory n)
    (hf : Apart3 f a b c t) :
    (#{x : LineagePair (n - t) | Apart3 (Function.update f ⟨t, ht⟩ x) a b c (t + 1)} : ℝ) =
      rateAfter n t - 3 := by
  obtain ⟨hlen, pos, hP⟩ := blocksAfter_spec f ht.le
  obtain ⟨h1, h2, h3⟩ := hf
  rw [pairApart_iff hP] at h1 h2 h3
  have hpa : pos a < n - t := hlen ▸ (hP a).1
  have hpb : pos b < n - t := hlen ▸ (hP b).1
  have hpc : pos c < n - t := hlen ▸ (hP c).1
  set S : Finset (ℕ × ℕ) := {(min (pos a) (pos b), max (pos a) (pos b)),
    (min (pos a) (pos c), max (pos a) (pos c)), (min (pos b) (pos c), max (pos b) (pos c))}
    with hSdef
  have hS : ∀ p ∈ S, p.1 < p.2 ∧ p.2 < n - t := by
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton]
    rintro p (rfl | rfl | rfl) <;> omega
  rw [Finset.filter_congr (q := fun x : LineagePair (n - t) => (pairLo x, pairHi x) ∉ S)
      (fun x _ => by
    simp only [Apart3, pairApart_update_succ_iff ht hP, hSdef, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    have := pairLo_lt_pairHi x
    omega),
    card_lineagePair_not_mem _ hS, hSdef, card_sortedPairs_three h1 h2 h3, rateAfter]
  push_cast
  ring

/-- From three distinct lineages, exactly one choice of the next step merges `b` with `c`. -/
theorem card_update_splitA_succ {t : ℕ} (ht : t < n - 1) {a b c : Fin n} (f : RankedHistory n)
    (hf : Apart3 f a b c t) :
    (#{x : LineagePair (n - t) | Apart3 (Function.update f ⟨t, ht⟩ x) a b c t ∧
      SplitA (Function.update f ⟨t, ht⟩ x) a b c (t + 1)} : ℝ) = 1 := by
  obtain ⟨hlen, pos, hP⟩ := blocksAfter_spec f ht.le
  have hf' := hf
  obtain ⟨h1, h2, h3⟩ := hf
  rw [pairApart_iff hP] at h1 h2 h3
  have hpb : pos b < n - t := hlen ▸ (hP b).1
  have hpc : pos c < n - t := hlen ▸ (hP c).1
  have hS : ∀ p ∈ ({(min (pos b) (pos c), max (pos b) (pos c))} : Finset (ℕ × ℕ)),
      p.1 < p.2 ∧ p.2 < n - t := by
    simp only [Finset.mem_singleton]
    rintro p rfl
    omega
  rw [Finset.filter_congr (q := fun x : LineagePair (n - t) => (pairLo x, pairHi x) ∈
      ({(min (pos b) (pos c), max (pos b) (pos c))} : Finset (ℕ × ℕ))) (fun x _ => by
    rw [apart3_update_of_le (j := ⟨t, ht⟩) x le_rfl]
    simp only [hf', true_and, SplitA, pairApart_update_succ_iff ht hP, Finset.mem_singleton,
      Prod.mk.injEq]
    have := pairLo_lt_pairHi x
    omega),
    card_lineagePair_mem _ hS, Finset.card_singleton]
  simp

private theorem ite_mul_ite_eq {p q : Prop} [Decidable p] [Decidable q] :
    (if p then (1 : ℝ) else 0) * (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- **Two pairs sharing a gene, from three distinct lineages**: given anything determined by the
first `t` steps, the remaining coalescence times of `{a, b}` and `{a, c}` have product moment
`E[τ_{ab}^{(t)} τ_{ac}^{(t)}; a, b, c apart] = (4/3) P(a, b, c apart)`. While the three are
apart, the next event merges `b` with `c` (leaving one pair with `E[τ²] = 2`) with probability
`1 / C(k, 2)`, ends one of the pairs with probability `2 / C(k, 2)`, and otherwise keeps all
three apart. -/
theorem sum_mul_apart3_futureProd {a b c : Fin n} (d : ℕ) : ∀ t, t + d = n - 1 →
    ∀ Y : RankedHistory n → ℝ, DependsBefore Y t →
      ∑ h, Y h * (if Apart3 h a b c t then 1 else 0) * futureProd h {a, b} {a, c} t =
        4 / 3 * ∑ h, Y h * (if Apart3 h a b c t then 1 else 0) := by
  induction d with
  | zero =>
    intro t hd Y _
    obtain rfl : t = n - 1 := by omega
    have h0 : ∀ h : RankedHistory n, ¬Apart3 h a b c (n - 1) :=
      fun h H => not_pairApart_sub_one h a.pos a b H.1
    simp [h0]
  | succ d ih =>
    intro t hd Y hY
    have ht : t < n - 1 := by omega
    have hc := (rateAfter_pos ht).ne'
    set r := rateAfter n t with hr
    -- indicators and weights
    have hI : DependsBefore (fun h => if Apart3 h a b c t then (1 : ℝ) else 0) t :=
      dependsBefore_ite _ fun f j x hj => apart3_update_of_le x hj a b c
    have hY3 := hY.mul hI
    -- one step of `futureProd` on `Apart3`
    have hstep : ∀ h : RankedHistory n, Y h * (if Apart3 h a b c t then 1 else 0) *
        futureProd h {a, b} {a, c} t =
        Y h * (if Apart3 h a b c t then 1 else 0) * (2 / r ^ 2) +
          r⁻¹ * (Y h * (if Apart3 h a b c t then 1 else 0) * futureMean h {a, c} (t + 1)) +
          r⁻¹ * (Y h * (if Apart3 h a b c t then 1 else 0) * futureMean h {a, b} (t + 1)) +
          Y h * (if Apart3 h a b c t then 1 else 0) * futureProd h {a, b} {a, c} (t + 1) := by
      intro h
      rw [futureProd_succ h _ _ ht]
      by_cases H : Apart3 h a b c t
      · simp only [H, ↓reduceIte, apartInd, H.1, H.2.1]
        ring
      · simp [H]
    simp_rw [hstep]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    -- the remaining time of each pair
    have hmean : ∀ {u v : Fin n}, (∀ h, Apart3 h a b c t → PairApart h {u, v} t) →
        ∑ h, Y h * (if Apart3 h a b c t then 1 else 0) * futureMean h {u, v} (t + 1) =
          (1 - r⁻¹) * ∑ h, Y h * (if Apart3 h a b c t then 1 else 0) := by
      intro u v huv
      rw [sum_mul_futureMean d (t + 1) (by omega) _ (hY3.mono (Nat.le_succ t)),
        sum_mul_apartInd_succ ht _ hY3]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases H : Apart3 h a b c t
      · simp [H, apartInd, huv h H]
      · simp [H]
    rw [hmean fun h H => H.2.1, hmean fun h H => H.1]
    -- decompose the future by the next state
    have hdec : ∀ h : RankedHistory n, Y h * (if Apart3 h a b c t then 1 else 0) *
        futureProd h {a, b} {a, c} (t + 1) =
        Y h * (if Apart3 h a b c (t + 1) then 1 else 0) * futureProd h {a, b} {a, c} (t + 1) +
          Y h * (if Apart3 h a b c t ∧ SplitA h a b c (t + 1) then 1 else 0) *
            futureProd h {a, b} {a, b} (t + 1) := by
      intro h
      rw [← apartInd_mul_futureProd h a b a c (t + 1)]
      by_cases H1 : Apart3 h a b c (t + 1)
      · have H0 := H1.of_succ
        have hn : ¬SplitA h a b c (t + 1) := fun H => H.2.2 H1.2.2
        simp [H1, H0, hn, apartInd, H1.1, H1.2.1]
      · by_cases H2 : Apart3 h a b c t ∧ SplitA h a b c (t + 1)
        · have hbc := H2.2.2.2
          rw [futureProd_congr (h := h) (s := {a, b}) (s' := {a, c}) (r := {a, b})
            (r' := {a, b}) (t := t + 1) (fun u _ _ => Iff.rfl)
            (fun u hu hu' => pairApart_congr_of_not hbc hu hu'.le)]
          simp [H1, H2, apartInd, H2.2.1, pairApart_congr_of_not hbc le_rfl ht]
        · have : ¬(PairApart h {a, b} (t + 1) ∧ PairApart h {a, c} (t + 1)) ∨
              ¬Apart3 h a b c t := by
            by_cases H0 : Apart3 h a b c t
            · left
              rintro ⟨h1, h2⟩
              by_cases h3 : PairApart h {b, c} (t + 1)
              · exact H1 ⟨h1, h2, h3⟩
              · exact H2 ⟨H0, h1, h2, h3⟩
            · right
              exact H0
          rcases this with h' | h'
          · by_cases h1 : PairApart h {a, b} (t + 1)
            · have h2 : ¬PairApart h {a, c} (t + 1) := fun h2 => h' ⟨h1, h2⟩
              simp [H1, H2, apartInd, h1, h2]
            · simp [H1, H2, apartInd, h1]
          · simp [H1, h']
    simp_rw [hdec]
    rw [Finset.sum_add_distrib, ih (t + 1) (by omega) Y (hY.mono (Nat.le_succ t))]
    have hS : DependsBefore
        (fun h => Y h * (if Apart3 h a b c t ∧ SplitA h a b c (t + 1) then (1 : ℝ) else 0))
        (t + 1) :=
      (hY.mono (Nat.le_succ t)).mul (dependsBefore_ite _ fun f j x hj => by
        simp only [SplitA, apart3_update_of_le x ((Nat.le_succ t).trans hj),
          pairApart_update_of_le x hj])
    rw [sum_mul_futureProd_self (a := a) (b := b) d (t + 1) (by omega) _ hS]
    have hSA : ∀ h : RankedHistory n,
        Y h * (if Apart3 h a b c t ∧ SplitA h a b c (t + 1) then (1 : ℝ) else 0) *
          apartInd h {a, b} (t + 1) =
        Y h * (if Apart3 h a b c t ∧ SplitA h a b c (t + 1) then 1 else 0) := by
      intro h
      by_cases H : Apart3 h a b c t ∧ SplitA h a b c (t + 1)
      · simp [H, apartInd, H.2.1]
      · simp [H]
    simp_rw [hSA]
    -- transition counts
    have k1 := sum_mul_ite_mul_rateAfter ht Y hY (fun h => Apart3 h a b c t)
      (fun h => Apart3 h a b c (t + 1))
      (fun f x => apart3_update_of_le (j := ⟨t, ht⟩) x le_rfl a b c)
      (fun f => Apart3.of_succ) (r - 3) (fun f hf => card_update_apart3_succ ht f hf)
    have k2 := sum_mul_ite_mul_rateAfter ht Y hY (fun h => Apart3 h a b c t)
      (fun h => Apart3 h a b c t ∧ SplitA h a b c (t + 1))
      (fun f x => apart3_update_of_le (j := ⟨t, ht⟩) x le_rfl a b c)
      (fun f H => H.1) 1 (fun f hf => card_update_splitA_succ ht f hf)
    generalize (∑ h, Y h * (if Apart3 h a b c t then (1 : ℝ) else 0)) = X at k1 k2 ⊢
    generalize (∑ h, Y h * (if Apart3 h a b c (t + 1) then (1 : ℝ) else 0)) = X1 at k1 k2 ⊢
    generalize (∑ h, Y h * (if Apart3 h a b c t ∧ SplitA h a b c (t + 1) then (1 : ℝ) else 0))
      = X2 at k1 k2 ⊢
    rw [← hr] at k1 k2
    have e1 : X1 = (r - 3) / r * X := by
      field_simp
      linear_combination k1
    have e2 : X2 = X / r := by
      field_simp
      linear_combination k2
    rw [e1, e2]
    field_simp
    ring

/-- Genes in one lineage are interchangeable: if `g, g'` share a lineage after `t` events, then
afterwards `{g, x}` is apart exactly when `{g', x}` is. -/
theorem pairApart_congr_of_together {h : RankedHistory n} {g g' : Fin n} {t u : ℕ}
    (H : ¬PairApart h {g, g'} t) (htu : t ≤ u) (hu : u ≤ n - 1) (x : Fin n) :
    PairApart h {g, x} u ↔ PairApart h {g', x} u := by
  obtain ⟨-, pos, hP⟩ := blocksAfter_spec h hu
  have H' := not_pairApart_of_le H htu
  rw [pairApart_iff hP, not_not] at H'
  rw [pairApart_iff hP, pairApart_iff hP, H']

/-- The genes `a, b, c, d` are in four distinct lineages after `t` events. -/
def Apart4 (h : RankedHistory n) (a b c d : Fin n) (t : ℕ) : Prop :=
  PairApart h {a, b} t ∧ PairApart h {a, c} t ∧ PairApart h {a, d} t ∧
    PairApart h {b, c} t ∧ PairApart h {b, d} t ∧ PairApart h {c, d} t

instance (h : RankedHistory n) (a b c d : Fin n) (t : ℕ) : Decidable (Apart4 h a b c d t) := by
  unfold Apart4
  infer_instance

theorem apart4_update_of_le {f : RankedHistory n} {j : Fin (n - 1)} (x : LineagePair (n - j))
    {u : ℕ} (hu : u ≤ j) (a b c d : Fin n) :
    Apart4 (Function.update f j x) a b c d u ↔ Apart4 f a b c d u := by
  simp only [Apart4, pairApart_update_of_le x hu]

theorem Apart4.of_succ {h : RankedHistory n} {a b c d : Fin n} {t : ℕ}
    (H : Apart4 h a b c d (t + 1)) : Apart4 h a b c d t :=
  ⟨H.1.of_succ, H.2.1.of_succ, H.2.2.1.of_succ, H.2.2.2.1.of_succ, H.2.2.2.2.1.of_succ,
    H.2.2.2.2.2.of_succ⟩

/-- `pairApart_succ_iff` for a pair in distinct lineages, with the sorted labels. -/
theorem pairApart_succ_iff_sorted {h : RankedHistory n} {t : ℕ} (ht : t < n - 1)
    {pos : Fin n → ℕ} (hP : IsBlockPartition (blocksAfter h t) pos) {u v : Fin n}
    (huv : pos u ≠ pos v) :
    PairApart h {u, v} (t + 1) ↔
      (pairLo (h ⟨t, ht⟩), pairHi (h ⟨t, ht⟩)) ≠ (min (pos u) (pos v), max (pos u) (pos v)) := by
  rw [pairApart_succ_iff ht hP]
  have := pairLo_lt_pairHi (h ⟨t, ht⟩)
  simp only [ne_eq, Prod.mk.injEq]
  omega

private theorem sortedPair_ne {p q r w : ℕ} (h : ¬((p = r ∧ q = w) ∨ (p = w ∧ q = r))) :
    (min p q, max p q) ≠ (min r w, max r w) := by
  simp only [ne_eq, Prod.mk.injEq]
  omega

/-- **The next step from four distinct lineages, in coordinates**: the step is a point `z`, the
six pairs of the four lineages are distinct points `s₁, …, s₆` (in the order `ab, ac, ad, bc,
bd, cd`), and a pair stays apart unless `z` is its point. -/
theorem apart4_succ_iff {h : RankedHistory n} {a b c d : Fin n} {t : ℕ} (ht : t < n - 1)
    (H : Apart4 h a b c d t) :
    ∃ z s₁ s₂ s₃ s₄ s₅ s₆ : ℕ × ℕ,
      s₁ ≠ s₂ ∧ s₁ ≠ s₃ ∧ s₁ ≠ s₄ ∧ s₁ ≠ s₅ ∧ s₁ ≠ s₆ ∧ s₂ ≠ s₃ ∧ s₂ ≠ s₄ ∧ s₂ ≠ s₅ ∧
      s₂ ≠ s₆ ∧ s₃ ≠ s₄ ∧ s₃ ≠ s₅ ∧ s₃ ≠ s₆ ∧ s₄ ≠ s₅ ∧ s₄ ≠ s₆ ∧ s₅ ≠ s₆ ∧
      (PairApart h {a, b} (t + 1) ↔ z ≠ s₁) ∧ (PairApart h {a, c} (t + 1) ↔ z ≠ s₂) ∧
      (PairApart h {a, d} (t + 1) ↔ z ≠ s₃) ∧ (PairApart h {b, c} (t + 1) ↔ z ≠ s₄) ∧
      (PairApart h {b, d} (t + 1) ↔ z ≠ s₅) ∧ (PairApart h {c, d} (t + 1) ↔ z ≠ s₆) := by
  obtain ⟨-, pos, hP⟩ := blocksAfter_spec h ht.le
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
  rw [pairApart_iff hP] at h1 h2 h3 h4 h5 h6
  exact ⟨_, _, _, _, _, _, _,
    sortedPair_ne (by omega), sortedPair_ne (by omega),
    sortedPair_ne (by omega), sortedPair_ne (by omega),
    sortedPair_ne (by omega), sortedPair_ne (by omega),
    sortedPair_ne (by omega), sortedPair_ne (by omega),
    sortedPair_ne (by omega), sortedPair_ne (by omega),
    sortedPair_ne (by omega), sortedPair_ne (by omega),
    sortedPair_ne (by omega), sortedPair_ne (by omega),
    sortedPair_ne (by omega),
    pairApart_succ_iff_sorted ht hP h1, pairApart_succ_iff_sorted ht hP h2,
    pairApart_succ_iff_sorted ht hP h3, pairApart_succ_iff_sorted ht hP h4,
    pairApart_succ_iff_sorted ht hP h5, pairApart_succ_iff_sorted ht hP h6⟩

/-- A point equals at most one of six distinct points: the indicator identity behind the
next-state decomposition from four lineages. -/
private theorem ite_split_six {z s₁ s₂ s₃ s₄ s₅ s₆ : ℕ × ℕ} (d12 : s₁ ≠ s₂) (d13 : s₁ ≠ s₃)
    (d14 : s₁ ≠ s₄) (d15 : s₁ ≠ s₅) (d16 : s₁ ≠ s₆) (d23 : s₂ ≠ s₃) (d24 : s₂ ≠ s₄)
    (d25 : s₂ ≠ s₅) (d26 : s₂ ≠ s₆) (d34 : s₃ ≠ s₄) (d35 : s₃ ≠ s₅) (d36 : s₃ ≠ s₆)
    (d45 : s₄ ≠ s₅) (d46 : s₄ ≠ s₆) (d56 : s₅ ≠ s₆) :
    (if z ≠ s₁ then (1 : ℝ) else 0) * (if z ≠ s₆ then 1 else 0) =
      (if z ≠ s₁ ∧ z ≠ s₂ ∧ z ≠ s₃ ∧ z ≠ s₄ ∧ z ≠ s₅ ∧ z ≠ s₆ then 1 else 0) +
        (if ¬z ≠ s₂ then 1 else 0) + (if ¬z ≠ s₃ then 1 else 0) +
        (if ¬z ≠ s₄ then 1 else 0) + (if ¬z ≠ s₅ then 1 else 0) := by
  by_cases e1 : z = s₁
  · subst e1
    simp [d12, d13, d14, d15, d16]
  by_cases e2 : z = s₂
  · subst e2
    simp [e1, d23, d24, d25, d26]
  by_cases e3 : z = s₃
  · subst e3
    simp [e1, e2, d34, d35, d36]
  by_cases e4 : z = s₄
  · subst e4
    simp [e1, e2, e3, d45, d46]
  by_cases e5 : z = s₅
  · subst e5
    simp [e1, e2, e3, e4, d56]
  by_cases e6 : z = s₆
  · subst e6
    simp [e1, e2, e3, e4, e5]
  simp [e1, e2, e3, e4, e5, e6]

/-- `#` of the six sorted pairs of four distinct labels. -/
private theorem card_sortedPairs_six {p q r w : ℕ} (hpq : p ≠ q) (hpr : p ≠ r) (hpw : p ≠ w)
    (hqr : q ≠ r) (hqw : q ≠ w) (hrw : r ≠ w) :
    #({(min p q, max p q), (min p r, max p r), (min p w, max p w), (min q r, max q r),
      (min q w, max q w), (min r w, max r w)} : Finset (ℕ × ℕ)) = 6 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_pair]
  · simp only [ne_eq, Prod.mk.injEq]
    omega
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega

/-- `pairApart_update_succ_iff` for a pair in distinct lineages, with the sorted labels. -/
theorem pairApart_update_succ_iff_sorted {f : RankedHistory n} {t : ℕ} (ht : t < n - 1)
    {pos : Fin n → ℕ} (hP : IsBlockPartition (blocksAfter f t) pos) (x : LineagePair (n - t))
    {u v : Fin n} (huv : pos u ≠ pos v) :
    PairApart (Function.update f ⟨t, ht⟩ x) {u, v} (t + 1) ↔
      (pairLo x, pairHi x) ≠ (min (pos u) (pos v), max (pos u) (pos v)) := by
  rw [pairApart_update_succ_iff ht hP]
  have := pairLo_lt_pairHi x
  simp only [ne_eq, Prod.mk.injEq]
  omega

/-- From four distinct lineages, `C(k, 2) - 6` choices of the next step keep them distinct. -/
theorem card_update_apart4_succ {t : ℕ} (ht : t < n - 1) {a b c d : Fin n} (f : RankedHistory n)
    (hf : Apart4 f a b c d t) :
    (#{x : LineagePair (n - t) | Apart4 (Function.update f ⟨t, ht⟩ x) a b c d (t + 1)} : ℝ) =
      rateAfter n t - 6 := by
  obtain ⟨hlen, pos, hP⟩ := blocksAfter_spec f ht.le
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hf
  rw [pairApart_iff hP] at h1 h2 h3 h4 h5 h6
  have hpa : pos a < n - t := hlen ▸ (hP a).1
  have hpb : pos b < n - t := hlen ▸ (hP b).1
  have hpc : pos c < n - t := hlen ▸ (hP c).1
  have hpd : pos d < n - t := hlen ▸ (hP d).1
  set S : Finset (ℕ × ℕ) := {(min (pos a) (pos b), max (pos a) (pos b)),
    (min (pos a) (pos c), max (pos a) (pos c)), (min (pos a) (pos d), max (pos a) (pos d)),
    (min (pos b) (pos c), max (pos b) (pos c)), (min (pos b) (pos d), max (pos b) (pos d)),
    (min (pos c) (pos d), max (pos c) (pos d))} with hSdef
  have hS : ∀ p ∈ S, p.1 < p.2 ∧ p.2 < n - t := by
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  rw [Finset.filter_congr (q := fun x : LineagePair (n - t) => (pairLo x, pairHi x) ∉ S)
      (fun x _ => by
    simp only [Apart4, pairApart_update_succ_iff_sorted ht hP x h1,
      pairApart_update_succ_iff_sorted ht hP x h2, pairApart_update_succ_iff_sorted ht hP x h3,
      pairApart_update_succ_iff_sorted ht hP x h4, pairApart_update_succ_iff_sorted ht hP x h5,
      pairApart_update_succ_iff_sorted ht hP x h6, hSdef, Finset.mem_insert,
      Finset.mem_singleton, not_or]),
    card_lineagePair_not_mem _ hS, hSdef, card_sortedPairs_six h1 h2 h3 h4 h5 h6, rateAfter]
  push_cast
  ring

/-- From a history in state `Q` (fixed by the first `t` steps) with `{u, v}` apart, exactly one
choice of step `t` merges `u` with `v`. -/
theorem card_update_and_not_pairApart_succ {t : ℕ} (ht : t < n - 1) {u v : Fin n}
    (Q : RankedHistory n → Prop) [DecidablePred Q] (f : RankedHistory n)
    (hQ : ∀ x : LineagePair (n - t), Q (Function.update f ⟨t, ht⟩ x) ↔ Q f) (hf : Q f)
    (huv : PairApart f {u, v} t) :
    (#{x : LineagePair (n - t) | Q (Function.update f ⟨t, ht⟩ x) ∧
      ¬PairApart (Function.update f ⟨t, ht⟩ x) {u, v} (t + 1)} : ℝ) = 1 := by
  rw [Finset.filter_congr (q := fun x : LineagePair (n - t) =>
    ¬PairApart (Function.update f ⟨t, ht⟩ x) {u, v} (t + 1)) (fun x _ => by simp [hQ x, hf])]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (LineagePair (n - t))))
    (fun x => PairApart (Function.update f ⟨t, ht⟩ x) {u, v} (t + 1))
  rw [Finset.card_univ, card_lineagePair] at h
  have h1 := card_update_pairApart_succ ht f huv
  have h2 : (#{x : LineagePair (n - t) | ¬PairApart (Function.update f ⟨t, ht⟩ x) {u, v} (t + 1)}
      : ℝ) = (((n - t).choose 2 : ℕ) : ℝ) -
        #{x : LineagePair (n - t) | PairApart (Function.update f ⟨t, ht⟩ x) {u, v} (t + 1)} := by
    rw [← h]
    push_cast
    ring
  rw [h2, h1, rateAfter]
  ring

/-- **The next state from four distinct lineages**: either all four stay distinct, or exactly
one of the four cross pairs `{a, c}, {a, d}, {b, c}, {b, d}` merges, or `{a, b}` or `{c, d}`
merges. -/
theorem ite_apart4_mul_apartInd_succ (h : RankedHistory n) {a b c d : Fin n} {t : ℕ}
    (ht : t < n - 1) :
    (if Apart4 h a b c d t then (1 : ℝ) else 0) * apartInd h {a, b} (t + 1) *
        apartInd h {c, d} (t + 1) =
      (if Apart4 h a b c d (t + 1) then 1 else 0) +
        (if Apart4 h a b c d t ∧ ¬PairApart h {a, c} (t + 1) then 1 else 0) +
        (if Apart4 h a b c d t ∧ ¬PairApart h {a, d} (t + 1) then 1 else 0) +
        (if Apart4 h a b c d t ∧ ¬PairApart h {b, c} (t + 1) then 1 else 0) +
        (if Apart4 h a b c d t ∧ ¬PairApart h {b, d} (t + 1) then 1 else 0) := by
  by_cases H : Apart4 h a b c d t
  · obtain ⟨z, s₁, s₂, s₃, s₄, s₅, s₆, d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35,
      d36, d45, d46, d56, i1, i2, i3, i4, i5, i6⟩ := apart4_succ_iff ht H
    simp only [H, true_and, ↓reduceIte, one_mul]
    simp only [apartInd, Apart4, i1, i2, i3, i4, i5, i6]
    exact ite_split_six d12 d13 d14 d15 d16 d23 d24 d25 d26 d34 d35 d36 d45 d46 d56
  · have : ¬Apart4 h a b c d (t + 1) := fun H' => H H'.of_succ
    simp [H, this]

/-- The triple left by merging the cross pair `{a, c}` from four distinct lineages. -/
theorem apart3_of_apart4_not_ac {h : RankedHistory n} {a b c d : Fin n} {t : ℕ}
    (ht : t < n - 1) (H : Apart4 h a b c d t) (Hac : ¬PairApart h {a, c} (t + 1)) :
    Apart3 h a b d (t + 1) ∧ PairApart h {c, d} (t + 1) ∧ PairApart h {b, c} (t + 1) := by
  obtain ⟨z, s₁, s₂, s₃, s₄, s₅, s₆, d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35,
    d36, d45, d46, d56, i1, i2, i3, i4, i5, i6⟩ := apart4_succ_iff ht H
  rw [i2, not_not] at Hac
  simp only [Apart3, i1, i3, i5, i6, i4, Hac]
  exact ⟨⟨d12.symm, d23, d25⟩, d26, d24⟩

theorem apart3_of_apart4_not_ad {h : RankedHistory n} {a b c d : Fin n} {t : ℕ}
    (ht : t < n - 1) (H : Apart4 h a b c d t) (Had : ¬PairApart h {a, d} (t + 1)) :
    Apart3 h a b c (t + 1) ∧ PairApart h {c, d} (t + 1) ∧ PairApart h {b, d} (t + 1) := by
  obtain ⟨z, s₁, s₂, s₃, s₄, s₅, s₆, d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35,
    d36, d45, d46, d56, i1, i2, i3, i4, i5, i6⟩ := apart4_succ_iff ht H
  rw [i3, not_not] at Had
  simp only [Apart3, i1, i2, i4, i6, i5, Had]
  exact ⟨⟨d13.symm, d23.symm, d34⟩, d36, d35⟩

theorem apart3_of_apart4_not_bc {h : RankedHistory n} {a b c d : Fin n} {t : ℕ}
    (ht : t < n - 1) (H : Apart4 h a b c d t) (Hbc : ¬PairApart h {b, c} (t + 1)) :
    Apart3 h c a d (t + 1) ∧ PairApart h {a, b} (t + 1) ∧ PairApart h {b, d} (t + 1) := by
  obtain ⟨z, s₁, s₂, s₃, s₄, s₅, s₆, d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35,
    d36, d45, d46, d56, i1, i2, i3, i4, i5, i6⟩ := apart4_succ_iff ht H
  rw [i4, not_not] at Hbc
  simp only [Apart3, Finset.pair_comm c a, i1, i2, i3, i5, i6, Hbc]
  exact ⟨⟨d24.symm, d46, d34.symm⟩, d14.symm, d45⟩

theorem apart3_of_apart4_not_bd {h : RankedHistory n} {a b c d : Fin n} {t : ℕ}
    (ht : t < n - 1) (H : Apart4 h a b c d t) (Hbd : ¬PairApart h {b, d} (t + 1)) :
    Apart3 h b a c (t + 1) ∧ PairApart h {a, b} (t + 1) ∧ PairApart h {c, d} (t + 1) := by
  obtain ⟨z, s₁, s₂, s₃, s₄, s₅, s₆, d12, d13, d14, d15, d16, d23, d24, d25, d26, d34, d35,
    d36, d45, d46, d56, i1, i2, i3, i4, i5, i6⟩ := apart4_succ_iff ht H
  rw [i5, not_not] at Hbd
  simp only [Apart3, Finset.pair_comm b a, i1, i2, i4, i6, Hbd]
  exact ⟨⟨d15.symm, d45.symm, d25.symm⟩, d15.symm, d56⟩

/-- **Two disjoint pairs, from four distinct lineages**: given anything determined by the first
`t` steps, `E[τ_{ab}^{(t)} τ_{cd}^{(t)}; a, b, c, d apart] = (11/9) P(a, b, c, d apart)`. From
four lineages, the next event merges one of the four cross pairs with probability
`4 / C(k, 2)` (leaving two pairs that share a lineage, `E = 4/3`), ends one of the pairs with
probability `2 / C(k, 2)`, and otherwise keeps all four apart. -/
theorem sum_mul_apart4_futureProd {a b c d : Fin n} (k : ℕ) : ∀ t, t + k = n - 1 →
    ∀ Y : RankedHistory n → ℝ, DependsBefore Y t →
      ∑ h, Y h * (if Apart4 h a b c d t then 1 else 0) * futureProd h {a, b} {c, d} t =
        11 / 9 * ∑ h, Y h * (if Apart4 h a b c d t then 1 else 0) := by
  induction k with
  | zero =>
    intro t hd Y _
    obtain rfl : t = n - 1 := by omega
    have h0 : ∀ h : RankedHistory n, ¬Apart4 h a b c d (n - 1) :=
      fun h H => not_pairApart_sub_one h a.pos a b H.1
    simp [h0]
  | succ k ih =>
    intro t hd Y hY
    have ht : t < n - 1 := by omega
    have hc := (rateAfter_pos ht).ne'
    set r := rateAfter n t with hr
    have hI : DependsBefore (fun h => if Apart4 h a b c d t then (1 : ℝ) else 0) t :=
      dependsBefore_ite _ fun f j x hj => apart4_update_of_le x hj a b c d
    have hY4 := hY.mul hI
    have hstep : ∀ h : RankedHistory n, Y h * (if Apart4 h a b c d t then 1 else 0) *
        futureProd h {a, b} {c, d} t =
        Y h * (if Apart4 h a b c d t then 1 else 0) * (2 / r ^ 2) +
          r⁻¹ * (Y h * (if Apart4 h a b c d t then 1 else 0) * futureMean h {c, d} (t + 1)) +
          r⁻¹ * (Y h * (if Apart4 h a b c d t then 1 else 0) * futureMean h {a, b} (t + 1)) +
          Y h * (if Apart4 h a b c d t then 1 else 0) * futureProd h {a, b} {c, d} (t + 1) := by
      intro h
      rw [futureProd_succ h _ _ ht]
      by_cases H : Apart4 h a b c d t
      · simp only [H, ↓reduceIte, apartInd, H.1, H.2.2.2.2.2]
        ring
      · simp [H]
    simp_rw [hstep]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    have hmean : ∀ {u v : Fin n}, (∀ h, Apart4 h a b c d t → PairApart h {u, v} t) →
        ∑ h, Y h * (if Apart4 h a b c d t then 1 else 0) * futureMean h {u, v} (t + 1) =
          (1 - r⁻¹) * ∑ h, Y h * (if Apart4 h a b c d t then 1 else 0) := by
      intro u v huv
      rw [sum_mul_futureMean k (t + 1) (by omega) _ (hY4.mono (Nat.le_succ t)),
        sum_mul_apartInd_succ ht _ hY4]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases H : Apart4 h a b c d t
      · simp [H, apartInd, huv h H]
      · simp [H]
    rw [hmean fun h H => H.2.2.2.2.2, hmean fun h H => H.1]
    -- decompose the future by the next state
    have hdec : ∀ h : RankedHistory n, Y h * (if Apart4 h a b c d t then 1 else 0) *
        futureProd h {a, b} {c, d} (t + 1) =
        Y h * (if Apart4 h a b c d (t + 1) then 1 else 0) * futureProd h {a, b} {c, d} (t + 1) +
          Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {a, c} (t + 1) then 1 else 0) *
            (if Apart3 h a b d (t + 1) then 1 else 0) * futureProd h {a, b} {a, d} (t + 1) +
          Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {a, d} (t + 1) then 1 else 0) *
            (if Apart3 h a b c (t + 1) then 1 else 0) * futureProd h {a, b} {a, c} (t + 1) +
          Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {b, c} (t + 1) then 1 else 0) *
            (if Apart3 h c a d (t + 1) then 1 else 0) * futureProd h {c, a} {c, d} (t + 1) +
          Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {b, d} (t + 1) then 1 else 0) *
            (if Apart3 h b a c (t + 1) then 1 else 0) * futureProd h {b, a} {b, c} (t + 1) := by
      intro h
      have e0 := ite_apart4_mul_apartInd_succ h (a := a) (b := b) (c := c) (d := d) ht
      have hF := apartInd_mul_futureProd h a b c d (t + 1)
      have hac : (if Apart4 h a b c d t ∧ ¬PairApart h {a, c} (t + 1) then (1 : ℝ) else 0) *
          futureProd h {a, b} {c, d} (t + 1) =
          (if Apart4 h a b c d t ∧ ¬PairApart h {a, c} (t + 1) then 1 else 0) *
            (if Apart3 h a b d (t + 1) then 1 else 0) * futureProd h {a, b} {a, d} (t + 1) := by
        by_cases E : Apart4 h a b c d t ∧ ¬PairApart h {a, c} (t + 1)
        · rw [futureProd_congr (r := {a, b}) (r' := {a, d}) (fun u _ _ => Iff.rfl)
            (fun u h1 h2 => (pairApart_congr_of_together E.2 h1 h2.le d).symm)]
          simp [E, (apart3_of_apart4_not_ac ht E.1 E.2).1]
        · simp [E]
      have had : (if Apart4 h a b c d t ∧ ¬PairApart h {a, d} (t + 1) then (1 : ℝ) else 0) *
          futureProd h {a, b} {c, d} (t + 1) =
          (if Apart4 h a b c d t ∧ ¬PairApart h {a, d} (t + 1) then 1 else 0) *
            (if Apart3 h a b c (t + 1) then 1 else 0) * futureProd h {a, b} {a, c} (t + 1) := by
        by_cases E : Apart4 h a b c d t ∧ ¬PairApart h {a, d} (t + 1)
        · rw [futureProd_congr (r := {a, b}) (r' := {a, c}) (fun u _ _ => Iff.rfl)
            (fun u h1 h2 => by
              rw [Finset.pair_comm c d]
              exact (pairApart_congr_of_together E.2 h1 h2.le c).symm)]
          simp [E, (apart3_of_apart4_not_ad ht E.1 E.2).1]
        · simp [E]
      have hbc : (if Apart4 h a b c d t ∧ ¬PairApart h {b, c} (t + 1) then (1 : ℝ) else 0) *
          futureProd h {a, b} {c, d} (t + 1) =
          (if Apart4 h a b c d t ∧ ¬PairApart h {b, c} (t + 1) then 1 else 0) *
            (if Apart3 h c a d (t + 1) then 1 else 0) * futureProd h {c, a} {c, d} (t + 1) := by
        by_cases E : Apart4 h a b c d t ∧ ¬PairApart h {b, c} (t + 1)
        · rw [futureProd_congr (r := {c, a}) (r' := {c, d})
            (fun u h1 h2 => by
              rw [Finset.pair_comm a b]
              exact pairApart_congr_of_together E.2 h1 h2.le a) (fun u _ _ => Iff.rfl)]
          simp [E, (apart3_of_apart4_not_bc ht E.1 E.2).1]
        · simp [E]
      have hbd : (if Apart4 h a b c d t ∧ ¬PairApart h {b, d} (t + 1) then (1 : ℝ) else 0) *
          futureProd h {a, b} {c, d} (t + 1) =
          (if Apart4 h a b c d t ∧ ¬PairApart h {b, d} (t + 1) then 1 else 0) *
            (if Apart3 h b a c (t + 1) then 1 else 0) * futureProd h {b, a} {b, c} (t + 1) := by
        by_cases E : Apart4 h a b c d t ∧ ¬PairApart h {b, d} (t + 1)
        · rw [futureProd_congr (r := {b, a}) (r' := {b, c})
            (fun u _ _ => by rw [Finset.pair_comm a b])
            (fun u h1 h2 => by
              rw [Finset.pair_comm c d]
              exact (pairApart_congr_of_together E.2 h1 h2.le c).symm)]
          simp [E, (apart3_of_apart4_not_bd ht E.1 E.2).1]
        · simp [E]
      linear_combination (-(Y h * (if Apart4 h a b c d t then (1 : ℝ) else 0))) * hF +
        (Y h * futureProd h {a, b} {c, d} (t + 1)) * e0 + Y h * hac + Y h * had + Y h * hbc +
        Y h * hbd
    simp_rw [hdec]
    simp only [Finset.sum_add_distrib]
    rw [ih (t + 1) (by omega) Y (hY.mono (Nat.le_succ t))]
    -- the four cross pieces
    have hdepE : ∀ u v : Fin n, DependsBefore (fun h =>
        Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1) then (1 : ℝ) else 0))
        (t + 1) := fun u v =>
      (hY.mono (Nat.le_succ t)).mul (dependsBefore_ite _ fun f j x hj => by
        simp only [apart4_update_of_le x ((Nat.le_succ t).trans hj),
          pairApart_update_of_le x hj])
    have hcnt : ∀ {u v : Fin n}, (∀ h, Apart4 h a b c d t → PairApart h {u, v} t) →
        ∑ h, Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1) then (1 : ℝ) else 0) =
          r⁻¹ * ∑ h, Y h * (if Apart4 h a b c d t then 1 else 0) := by
      intro u v huv
      have cnt := sum_mul_ite_mul_rateAfter ht Y hY (fun h => Apart4 h a b c d t)
        (fun h => Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1))
        (fun f x => apart4_update_of_le (j := ⟨t, ht⟩) x le_rfl a b c d) (fun f H => H.1) 1
        (fun f hf => card_update_and_not_pairApart_succ ht (fun h => Apart4 h a b c d t) f
          (fun x => apart4_update_of_le (j := ⟨t, ht⟩) x le_rfl a b c d) hf (huv f hf))
      rw [← hr] at cnt
      field_simp
      linear_combination cnt
    have pac := sum_mul_apart3_futureProd (a := a) (b := b) (c := d) k (t + 1) (by omega) _
      (hdepE a c)
    have pad := sum_mul_apart3_futureProd (a := a) (b := b) (c := c) k (t + 1) (by omega) _
      (hdepE a d)
    have pbc := sum_mul_apart3_futureProd (a := c) (b := a) (c := d) k (t + 1) (by omega) _
      (hdepE b c)
    have pbd := sum_mul_apart3_futureProd (a := b) (b := a) (c := c) k (t + 1) (by omega) _
      (hdepE b d)
    beta_reduce at pac pad pbc pbd
    rw [pac, pad, pbc, pbd]
    have drop : ∀ {u v : Fin n} {A : RankedHistory n → Prop} [DecidablePred A],
        (∀ h, Apart4 h a b c d t → ¬PairApart h {u, v} (t + 1) → A h) →
        ∑ h, Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1) then (1 : ℝ) else 0) *
          (if A h then 1 else 0) =
        ∑ h, Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1) then 1 else 0) := by
      intro u v A _ hA
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases E : Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1)
      · simp [E, hA h E.1 E.2]
      · simp [E]
    rw [drop fun h H E => (apart3_of_apart4_not_ac ht H E).1,
      drop fun h H E => (apart3_of_apart4_not_ad ht H E).1,
      drop fun h H E => (apart3_of_apart4_not_bc ht H E).1,
      drop fun h H E => (apart3_of_apart4_not_bd ht H E).1,
      hcnt fun h H => H.2.1, hcnt fun h H => H.2.2.1, hcnt fun h H => H.2.2.2.1,
      hcnt fun h H => H.2.2.2.2.1]
    have k1 := sum_mul_ite_mul_rateAfter ht Y hY (fun h => Apart4 h a b c d t)
      (fun h => Apart4 h a b c d (t + 1))
      (fun f x => apart4_update_of_le (j := ⟨t, ht⟩) x le_rfl a b c d)
      (fun f => Apart4.of_succ) (r - 6) (fun f hf => card_update_apart4_succ ht f hf)
    generalize (∑ h, Y h * (if Apart4 h a b c d t then (1 : ℝ) else 0)) = X at k1 ⊢
    generalize (∑ h, Y h * (if Apart4 h a b c d (t + 1) then (1 : ℝ) else 0)) = X1 at k1 ⊢
    rw [← hr] at k1
    have e1 : X1 = (r - 6) / r * X := by
      field_simp
      linear_combination k1
    rw [e1]
    field_simp
    ring

/-! #### Overlap of two paths -/

/-- The number of branches of the epoch after `u` events that separate both pairs `s` and `s'`
(labels `j < n - u` of the lineages holding exactly one gene of each pair). -/
noncomputable def overlapCount (h : RankedHistory n) (s s' : Finset (Fin n)) (u : ℕ) : ℝ :=
  ∑ j ∈ range (n - u), if (s ∩ (blocksAfter h u).getD j ∅).card = 1 ∧
    (s' ∩ (blocksAfter h u).getD j ∅).card = 1 then 1 else 0

/-- `E[ℓ(path s ∩ path s')^{(t)} | h]`, the part of the overlap length after `t` events. -/
noncomputable def futureOverlap (h : RankedHistory n) (s s' : Finset (Fin n)) (t : ℕ) : ℝ :=
  ∑ u ∈ Ico t (n - 1), overlapCount h s s' u / rateAfter n u

/-- The overlap count in lineage coordinates: lineage `j` separates `{a, b}` iff it holds
exactly one of `a, b`. -/
theorem overlapCount_eq {h : RankedHistory n} {u : ℕ} (hu : u ≤ n - 1) {pos : Fin n → ℕ}
    (hP : IsBlockPartition (blocksAfter h u) pos) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    overlapCount h {a, b} {c, d} u = ∑ j ∈ range (n - u),
      if (j = pos a ↔ ¬j = pos b) ∧ (j = pos c ↔ ¬j = pos d) then 1 else 0 := by
  have hlen := (blocksAfter_spec h hu).1
  have hmem : ∀ (g : Fin n) (j : ℕ), j < n - u →
      (g ∈ (blocksAfter h u).getD j ∅ ↔ j = pos g) := by
    intro g j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact (hP g).2 j (by omega)
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  simp only [card_pair_inter_eq_one hab, card_pair_inter_eq_one hcd, hmem _ _ hj']

/-- **Overlap of two paths through a shared gene**: the lineages separating both `{a, b}` and
`{a, c}` number `1[a, b apart] + 1[a, c apart] - 1[b, c apart]` (the tree identity
`ℓ(P_{ab} ∩ P_{ac}) = (ℓ(P_{ab}) + ℓ(P_{ac}) - ℓ(P_{bc}))/2`, epoch by epoch). -/
theorem overlapCount_shared {h : RankedHistory n} {u : ℕ} (hu : u ≤ n - 1) {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) :
    overlapCount h {a, b} {a, c} u =
      apartInd h {a, b} u + apartInd h {a, c} u - apartInd h {b, c} u := by
  obtain ⟨hlen, pos, hP⟩ := blocksAfter_spec h hu
  have hpa : pos a < n - u := hlen ▸ (hP a).1
  have hpb : pos b < n - u := hlen ▸ (hP b).1
  rw [overlapCount_eq hu hP hab hac]
  simp only [apartInd, pairApart_iff hP]
  have e : ∀ j ∈ range (n - u),
      (if (j = pos a ↔ ¬j = pos b) ∧ (j = pos a ↔ ¬j = pos c) then (1 : ℝ) else 0) =
        (if j = pos a then (if pos a ≠ pos b ∧ pos a ≠ pos c then 1 else 0) else 0) +
          (if j = pos b then (if pos b = pos c ∧ pos a ≠ pos b then 1 else 0) else 0) := by
    intro j _
    split_ifs <;> first | (exfalso; omega) | norm_num
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_range, hpa, hpb, ↓reduceIte]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem futureOverlap_shared (h : RankedHistory n) (t : ℕ) {a b c : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) :
    futureOverlap h {a, b} {a, c} t =
      futureMean h {a, b} t + futureMean h {a, c} t - futureMean h {b, c} t := by
  rw [futureOverlap, futureMean, futureMean, futureMean, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [overlapCount_shared (Finset.mem_Ico.1 hu).2.le hab hac]
  ring

theorem futureOverlap_succ (h : RankedHistory n) (s s' : Finset (Fin n)) {t : ℕ}
    (ht : t < n - 1) :
    futureOverlap h s s' t =
      overlapCount h s s' t / rateAfter n t + futureOverlap h s s' (t + 1) := by
  rw [futureOverlap, futureOverlap, Finset.sum_eq_sum_Ico_succ_bot ht]

/-- No lineage separates both of two disjoint pairs while all four genes are apart. -/
theorem overlapCount_of_apart4 {h : RankedHistory n} {u : ℕ} (hu : u ≤ n - 1) {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d) (H : Apart4 h a b c d u) : overlapCount h {a, b} {c, d} u = 0 := by
  obtain ⟨-, pos, hP⟩ := blocksAfter_spec h hu
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
  rw [pairApart_iff hP] at h1 h2 h3 h4 h5 h6
  rw [overlapCount_eq hu hP hab hcd]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [ite_eq_right_iff]
  intro hj
  omega

/-- A pair that has coalesced is separated by no lineage. -/
theorem overlapCount_of_not_left {h : RankedHistory n} {u : ℕ} (hu : u ≤ n - 1)
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (H : ¬PairApart h {a, b} u) :
    overlapCount h {a, b} {c, d} u = 0 := by
  obtain ⟨-, pos, hP⟩ := blocksAfter_spec h hu
  rw [pairApart_iff hP, not_not] at H
  rw [overlapCount_eq hu hP hab hcd]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [ite_eq_right_iff]
  intro hj
  omega

theorem overlapCount_of_not_right {h : RankedHistory n} {u : ℕ} (hu : u ≤ n - 1)
    {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (H : ¬PairApart h {c, d} u) :
    overlapCount h {a, b} {c, d} u = 0 := by
  obtain ⟨-, pos, hP⟩ := blocksAfter_spec h hu
  rw [pairApart_iff hP, not_not] at H
  rw [overlapCount_eq hu hP hab hcd]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [ite_eq_right_iff]
  intro hj
  omega

/-- The overlap count only sees the lineages of the four genes. -/
theorem overlapCount_congr {h : RankedHistory n} {u : ℕ} (hu : u ≤ n - 1)
    {a b c d a' b' c' d' : Fin n} (hab : a ≠ b) (hcd : c ≠ d) (hab' : a' ≠ b') (hcd' : c' ≠ d')
    (H : ∀ pos : Fin n → ℕ, IsBlockPartition (blocksAfter h u) pos →
      pos a = pos a' ∧ pos b = pos b' ∧ pos c = pos c' ∧ pos d = pos d') :
    overlapCount h {a, b} {c, d} u = overlapCount h {a', b'} {c', d'} u := by
  obtain ⟨-, pos, hP⟩ := blocksAfter_spec h hu
  obtain ⟨e1, e2, e3, e4⟩ := H pos hP
  rw [overlapCount_eq hu hP hab hcd, overlapCount_eq hu hP hab' hcd', e1, e2, e3, e4]

/-- Genes that have coalesced share their lineage label from then on. -/
theorem pos_eq_of_not_pairApart {h : RankedHistory n} {g g' : Fin n} {t u : ℕ}
    (H : ¬PairApart h {g, g'} t) (htu : t ≤ u) {pos : Fin n → ℕ}
    (hP : IsBlockPartition (blocksAfter h u) pos) : pos g = pos g' := by
  have H' := not_pairApart_of_le H htu
  rwa [pairApart_iff hP, not_not] at H'

theorem apartInd_mul_futureOverlap (h : RankedHistory n) {a b c d : Fin n} (hab : a ≠ b)
    (hcd : c ≠ d) (t : ℕ) :
    apartInd h {a, b} t * apartInd h {c, d} t * futureOverlap h {a, b} {c, d} t =
      futureOverlap h {a, b} {c, d} t := by
  rw [futureOverlap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hu
  unfold apartInd
  by_cases A : PairApart h {a, b} t
  · by_cases C : PairApart h {c, d} t
    · simp [A, C]
    · simp [A, C, overlapCount_of_not_right h2.le hab hcd (not_pairApart_of_le C h1)]
  · simp [A, overlapCount_of_not_left h2.le hab hcd (not_pairApart_of_le A h1)]

/-- **Overlap of the paths of two disjoint pairs, from four distinct lineages**: given anything
determined by the first `t` steps, `E[ℓ(P_{ab} ∩ P_{cd})^{(t)}; apart] = (2/3) P(apart)`. Nothing
overlaps until a cross pair merges (probability `4 / C(k, 2)` per step), after which the overlap
is that of two pairs through a shared lineage, of mean one. -/
theorem sum_mul_apart4_futureOverlap {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hcd : c ≠ d) (k : ℕ) : ∀ t, t + k = n - 1 →
    ∀ Y : RankedHistory n → ℝ, DependsBefore Y t →
      ∑ h, Y h * (if Apart4 h a b c d t then 1 else 0) * futureOverlap h {a, b} {c, d} t =
        2 / 3 * ∑ h, Y h * (if Apart4 h a b c d t then 1 else 0) := by
  induction k with
  | zero =>
    intro t hd Y _
    obtain rfl : t = n - 1 := by omega
    have h0 : ∀ h : RankedHistory n, ¬Apart4 h a b c d (n - 1) :=
      fun h H => not_pairApart_sub_one h a.pos a b H.1
    simp [h0]
  | succ k ih =>
    intro t hd Y hY
    have ht : t < n - 1 := by omega
    have hc := (rateAfter_pos ht).ne'
    set r := rateAfter n t with hr
    have hstep : ∀ h : RankedHistory n, Y h * (if Apart4 h a b c d t then 1 else 0) *
        futureOverlap h {a, b} {c, d} t =
        Y h * (if Apart4 h a b c d t then 1 else 0) * futureOverlap h {a, b} {c, d} (t + 1) := by
      intro h
      rw [futureOverlap_succ h _ _ ht]
      by_cases H : Apart4 h a b c d t
      · simp [H, overlapCount_of_apart4 ht.le hab hcd H]
      · simp [H]
    simp_rw [hstep]
    -- the overlap after a cross pair merges
    have hshared : ∀ h : RankedHistory n, ∀ {g g' x y z w : Fin n},
        ¬PairApart h {g, g'} (t + 1) → x ≠ y → z ≠ w →
        (∀ pos : Fin n → ℕ, pos g = pos g' →
          pos a = pos x ∧ pos b = pos y ∧ pos c = pos z ∧ pos d = pos w) →
        futureOverlap h {a, b} {c, d} (t + 1) = futureOverlap h {x, y} {z, w} (t + 1) := by
      intro h g g' x y z w H hxy hzw hpos
      refine Finset.sum_congr rfl fun u hu => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hu
      rw [overlapCount_congr h2.le hab hcd hxy hzw fun pos hP =>
        hpos pos (pos_eq_of_not_pairApart H h1 hP)]
    have hdec : ∀ h : RankedHistory n, Y h * (if Apart4 h a b c d t then 1 else 0) *
        futureOverlap h {a, b} {c, d} (t + 1) =
        Y h * (if Apart4 h a b c d (t + 1) then 1 else 0) *
            futureOverlap h {a, b} {c, d} (t + 1) +
          Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {a, c} (t + 1) then 1 else 0) *
            (futureMean h {a, b} (t + 1) + futureMean h {a, d} (t + 1) -
              futureMean h {b, d} (t + 1)) +
          Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {a, d} (t + 1) then 1 else 0) *
            (futureMean h {a, b} (t + 1) + futureMean h {a, c} (t + 1) -
              futureMean h {b, c} (t + 1)) +
          Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {b, c} (t + 1) then 1 else 0) *
            (futureMean h {c, a} (t + 1) + futureMean h {c, d} (t + 1) -
              futureMean h {a, d} (t + 1)) +
          Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {b, d} (t + 1) then 1 else 0) *
            (futureMean h {b, a} (t + 1) + futureMean h {b, c} (t + 1) -
              futureMean h {a, c} (t + 1)) := by
      intro h
      have e0 := ite_apart4_mul_apartInd_succ h (a := a) (b := b) (c := c) (d := d) ht
      have hF := apartInd_mul_futureOverlap h hab hcd (t + 1)
      have hac' : (if Apart4 h a b c d t ∧ ¬PairApart h {a, c} (t + 1) then (1 : ℝ) else 0) *
          futureOverlap h {a, b} {c, d} (t + 1) =
          (if Apart4 h a b c d t ∧ ¬PairApart h {a, c} (t + 1) then 1 else 0) *
            (futureMean h {a, b} (t + 1) + futureMean h {a, d} (t + 1) -
              futureMean h {b, d} (t + 1)) := by
        by_cases E : Apart4 h a b c d t ∧ ¬PairApart h {a, c} (t + 1)
        · rw [hshared h E.2 hab had fun pos e => ⟨rfl, rfl, e.symm, rfl⟩,
            futureOverlap_shared h _ hab had]
        · simp [E]
      have had' : (if Apart4 h a b c d t ∧ ¬PairApart h {a, d} (t + 1) then (1 : ℝ) else 0) *
          futureOverlap h {a, b} {c, d} (t + 1) =
          (if Apart4 h a b c d t ∧ ¬PairApart h {a, d} (t + 1) then 1 else 0) *
            (futureMean h {a, b} (t + 1) + futureMean h {a, c} (t + 1) -
              futureMean h {b, c} (t + 1)) := by
        by_cases E : Apart4 h a b c d t ∧ ¬PairApart h {a, d} (t + 1)
        · rw [hshared h E.2 hab (Ne.symm hac) fun pos e => ⟨rfl, rfl, rfl, e.symm⟩,
            Finset.pair_comm c a, futureOverlap_shared h _ hab hac]
        · simp [E]
      have hbc' : (if Apart4 h a b c d t ∧ ¬PairApart h {b, c} (t + 1) then (1 : ℝ) else 0) *
          futureOverlap h {a, b} {c, d} (t + 1) =
          (if Apart4 h a b c d t ∧ ¬PairApart h {b, c} (t + 1) then 1 else 0) *
            (futureMean h {c, a} (t + 1) + futureMean h {c, d} (t + 1) -
              futureMean h {a, d} (t + 1)) := by
        by_cases E : Apart4 h a b c d t ∧ ¬PairApart h {b, c} (t + 1)
        · rw [hshared h E.2 hac hcd fun pos e => ⟨rfl, e, rfl, rfl⟩,
            Finset.pair_comm a c, futureOverlap_shared h _ (Ne.symm hac) hcd]
        · simp [E]
      have hbd' : (if Apart4 h a b c d t ∧ ¬PairApart h {b, d} (t + 1) then (1 : ℝ) else 0) *
          futureOverlap h {a, b} {c, d} (t + 1) =
          (if Apart4 h a b c d t ∧ ¬PairApart h {b, d} (t + 1) then 1 else 0) *
            (futureMean h {b, a} (t + 1) + futureMean h {b, c} (t + 1) -
              futureMean h {a, c} (t + 1)) := by
        by_cases E : Apart4 h a b c d t ∧ ¬PairApart h {b, d} (t + 1)
        · rw [hshared h E.2 hab (Ne.symm hbc) fun pos e => ⟨rfl, rfl, rfl, e.symm⟩,
            Finset.pair_comm a b, Finset.pair_comm c b,
            futureOverlap_shared h _ (Ne.symm hab) hbc]
        · simp [E]
      linear_combination (-(Y h * (if Apart4 h a b c d t then (1 : ℝ) else 0))) * hF +
        (Y h * futureOverlap h {a, b} {c, d} (t + 1)) * e0 + Y h * hac' + Y h * had' +
        Y h * hbc' + Y h * hbd'
    simp_rw [hdec]
    simp only [Finset.sum_add_distrib]
    rw [ih (t + 1) (by omega) Y (hY.mono (Nat.le_succ t))]
    have hdepE : ∀ u v : Fin n, DependsBefore (fun h =>
        Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1) then (1 : ℝ) else 0))
        (t + 1) := fun u v =>
      (hY.mono (Nat.le_succ t)).mul (dependsBefore_ite _ fun f j x hj => by
        simp only [apart4_update_of_le x ((Nat.le_succ t).trans hj),
          pairApart_update_of_le x hj])
    -- the mean remaining time of a pair apart after the merge is one
    have hM : ∀ {u v g g' : Fin n},
        (∀ h, Apart4 h a b c d t → ¬PairApart h {u, v} (t + 1) → PairApart h {g, g'} (t + 1)) →
        ∑ h, Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1) then (1 : ℝ) else 0) *
            futureMean h {g, g'} (t + 1) =
          ∑ h, Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1) then 1 else 0) := by
      intro u v g g' hA
      rw [sum_mul_futureMean k (t + 1) (by omega) _ (hdepE u v)]
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases E : Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1)
      · simp [E, apartInd, hA h E.1 E.2]
      · simp [E]
    have hpiece : ∀ {u v g₁ g₂ g₃ g₄ g₅ g₆ : Fin n},
        (∀ h, Apart4 h a b c d t → ¬PairApart h {u, v} (t + 1) →
          PairApart h {g₁, g₂} (t + 1) ∧ PairApart h {g₃, g₄} (t + 1) ∧
            PairApart h {g₅, g₆} (t + 1)) →
        ∑ h, Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1) then (1 : ℝ) else 0) *
            (futureMean h {g₁, g₂} (t + 1) + futureMean h {g₃, g₄} (t + 1) -
              futureMean h {g₅, g₆} (t + 1)) =
          ∑ h, Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1) then 1 else 0) := by
      intro u v g₁ g₂ g₃ g₄ g₅ g₆ hA
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [hM fun h H E => (hA h H E).1, hM fun h H E => (hA h H E).2.1,
        hM fun h H E => (hA h H E).2.2]
      ring
    rw [hpiece fun h H E => by
        have := apart3_of_apart4_not_ac ht H E
        exact ⟨this.1.1, this.1.2.1, this.1.2.2⟩,
      hpiece fun h H E => by
        have := apart3_of_apart4_not_ad ht H E
        exact ⟨this.1.1, this.1.2.1, this.1.2.2⟩,
      hpiece fun h H E => by
        have := apart3_of_apart4_not_bc ht H E
        exact ⟨this.1.1, this.1.2.1, this.1.2.2⟩,
      hpiece fun h H E => by
        have := apart3_of_apart4_not_bd ht H E
        exact ⟨this.1.1, this.1.2.1, this.1.2.2⟩]
    have hcnt : ∀ {u v : Fin n}, (∀ h, Apart4 h a b c d t → PairApart h {u, v} t) →
        ∑ h, Y h * (if Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1) then (1 : ℝ) else 0) =
          r⁻¹ * ∑ h, Y h * (if Apart4 h a b c d t then 1 else 0) := by
      intro u v huv
      have cnt := sum_mul_ite_mul_rateAfter ht Y hY (fun h => Apart4 h a b c d t)
        (fun h => Apart4 h a b c d t ∧ ¬PairApart h {u, v} (t + 1))
        (fun f x => apart4_update_of_le (j := ⟨t, ht⟩) x le_rfl a b c d) (fun f H => H.1) 1
        (fun f hf => card_update_and_not_pairApart_succ ht (fun h => Apart4 h a b c d t) f
          (fun x => apart4_update_of_le (j := ⟨t, ht⟩) x le_rfl a b c d) hf (huv f hf))
      rw [← hr] at cnt
      field_simp
      linear_combination cnt
    rw [hcnt fun h H => H.2.1, hcnt fun h H => H.2.2.1, hcnt fun h H => H.2.2.2.1,
      hcnt fun h H => H.2.2.2.2.1]
    have k1 := sum_mul_ite_mul_rateAfter ht Y hY (fun h => Apart4 h a b c d t)
      (fun h => Apart4 h a b c d (t + 1))
      (fun f x => apart4_update_of_le (j := ⟨t, ht⟩) x le_rfl a b c d)
      (fun f => Apart4.of_succ) (r - 6) (fun f hf => card_update_apart4_succ ht f hf)
    generalize (∑ h, Y h * (if Apart4 h a b c d t then (1 : ℝ) else 0)) = X at k1 ⊢
    generalize (∑ h, Y h * (if Apart4 h a b c d (t + 1) then (1 : ℝ) else 0)) = X1 at k1 ⊢
    rw [← hr] at k1
    have e1 : X1 = (r - 6) / r * X := by
      field_simp
      linear_combination k1
    rw [e1]
    field_simp
    ring

/-! #### From histories to the Kingman model -/

/-- Integrals against random joining are averages over the ranked labeled histories
(`MultispeciesCoalescent.integral_randomJoining` is the public version, with the number of
histories written as `∏_{k=2}^n C(k, 2)`). -/
private theorem integral_randomJoining (F : RankedHistory n → ℝ) :
    ∫ h, F h ∂randomJoining n = (∑ h, F h) / Fintype.card (RankedHistory n) := by
  have hsing : ∀ h : RankedHistory n,
      (randomJoining n).real {h} = (Fintype.card (RankedHistory n) : ℝ)⁻¹ := fun h => by
    rw [measureReal_def, randomJoining_singleton_eq_inv, ← card_rankedHistory, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
  rw [integral_fintype Integrable.of_finite]
  simp_rw [hsing, smul_eq_mul, ← Finset.mul_sum]
  rw [inv_mul_eq_div]

/-- Epoch `k ∈ [2, n]` is the epoch after `n - k` events. -/
private theorem sum_Icc_sub_eq_sum_Ico (g : ℕ → ℝ) :
    ∑ k : Icc 2 n, g (n - k) = ∑ u ∈ Ico 0 (n - 1), g u := by
  rw [Finset.sum_coe_sort (Icc 2 n) (fun k => g (n - k))]
  refine Finset.sum_nbij' (fun k => n - k) (fun u => n - u) ?_ ?_ ?_ ?_ fun _ _ => rfl
  all_goals
    intro k hk
    simp only [Finset.mem_Icc, Finset.mem_Ico] at hk ⊢
    omega

theorem rateAfter_sub {k : ℕ} (hk : k ≤ n) : rateAfter n (n - k) = ((k.choose 2 : ℕ) : ℝ) := by
  rw [rateAfter, Nat.sub_sub_self hk]

/-- **Integrating out the epoch lengths**: `E[τ_s τ_{s'} | h] = futureProd h s s' 0`. -/
theorem integral_pairCoalTime_mul_piMeasure (h : RankedHistory n) (s s' : Finset (Fin n)) :
    ∫ t, pairCoalTime h s t * pairCoalTime h s' t ∂piMeasure n = futureProd h s s' 0 := by
  have hL2 : ∀ k : Icc 2 n, MemLp (fun t : Icc 2 n → ℝ => t k) 2 (piMeasure n) := fun k => by
    have := (KingmanTimes.ofPi n).memLp_T k.2
    simpa [KingmanTimes.ofPi, Finset.mem_Icc.1 k.2] using this
  have hmom : ∀ k k' : Icc 2 n, ∫ t, t k * t k' ∂piMeasure n =
      (((k : ℕ).choose 2 : ℕ) : ℝ)⁻¹ * (((k' : ℕ).choose 2 : ℕ) : ℝ)⁻¹ +
        if (k : ℕ) = k' then ((((k : ℕ).choose 2 : ℕ) : ℝ)⁻¹) ^ 2 else 0 := fun k k' => by
    have := (KingmanTimes.ofPi n).integral_T_mul_T k.2 k'.2
    have e : ∀ j : Icc 2 n, (KingmanTimes.ofPi n).T j = fun t => t j := fun j => by
      funext t
      simp [KingmanTimes.ofPi, Finset.mem_Icc.1 j.2]
    simp only [e] at this
    exact this
  have hτ : ∀ (r : Finset (Fin n)) (t : Icc 2 n → ℝ),
      pairCoalTime h r t = ∑ k : Icc 2 n, apartInd h r (n - k) * t k := by
    intro r t
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [apartInd]
    split_ifs <;> simp
  simp_rw [hτ, Finset.sum_mul_sum]
  have hint : ∀ k k' : Icc 2 n, Integrable (fun t : Icc 2 n → ℝ =>
      apartInd h s (n - k) * t k * (apartInd h s' (n - k') * t k')) (piMeasure n) :=
    fun k k' => (((hL2 k).integrable_mul (hL2 k')).const_mul
      (apartInd h s (n - k) * apartInd h s' (n - k'))).congr
      (ae_of_all _ fun t => by simp only [Pi.mul_apply]; ring)
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun k' _ => hint k k']
  have hterm : ∀ k k' : Icc 2 n, ∫ t, apartInd h s (n - k) * t k *
      (apartInd h s' (n - k') * t k') ∂piMeasure n =
      apartInd h s (n - k) * apartInd h s' (n - k') * ∫ t, t k * t k' ∂piMeasure n := by
    intro k k'
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun t => by ring)
  simp_rw [integral_finsetSum _ fun k' _ => hint _ k', hterm, hmom]
  have hmean : ∀ r : Finset (Fin n), futureMean h r 0 =
      ∑ k : Icc 2 n, apartInd h r (n - k) * (((k : ℕ).choose 2 : ℕ) : ℝ)⁻¹ := by
    intro r
    rw [futureMean, ← sum_Icc_sub_eq_sum_Ico (fun u => apartInd h r u / rateAfter n u)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rateAfter_sub (Finset.mem_Icc.1 k.2).2, div_eq_mul_inv]
  have hdiag : futureDiag h s s' 0 = ∑ k : Icc 2 n, apartInd h s (n - k) *
      apartInd h s' (n - k) * ((((k : ℕ).choose 2 : ℕ) : ℝ)⁻¹) ^ 2 := by
    rw [futureDiag, ← sum_Icc_sub_eq_sum_Ico
      (fun u => apartInd h s u * apartInd h s' u / rateAfter n u ^ 2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rateAfter_sub (Finset.mem_Icc.1 k.2).2, div_eq_mul_inv, inv_pow]
  rw [futureProd, hmean, hmean, hdiag, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Subtype.coe_inj,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  congr 1
  refine Finset.sum_congr rfl fun k' _ => ?_
  ring

/-- **Integrating out the epoch lengths, overlap**: `E[ℓ(path s ∩ path s') | h] =
futureOverlap h s s' 0`. -/
theorem integral_pairPathOverlap_piMeasure (h : RankedHistory n) (s s' : Finset (Fin n)) :
    ∫ t, pairPathOverlap h s s' t ∂piMeasure n = futureOverlap h s s' 0 := by
  have hTi : ∀ k : Icc 2 n, Integrable (fun t : Icc 2 n → ℝ => t k) (piMeasure n) := fun k => by
    have := (KingmanTimes.ofPi n).integrable_T k.2
    simpa [KingmanTimes.ofPi, Finset.mem_Icc.1 k.2] using this
  have hpi : ∀ᵐ t ∂piMeasure n, ∀ k : Icc 2 n, 0 ≤ t k := by
    filter_upwards [(KingmanTimes.ofPi n).ae_nonneg_epochs] with t ht k
    have := ht k
    simpa [KingmanTimes.epochs, KingmanTimes.ofPi, (Finset.mem_Icc.1 k.2).1,
      (Finset.mem_Icc.1 k.2).2] using this
  have hmax : ∀ k : Icc 2 n,
      ∫ t, max (t k) 0 ∂piMeasure n = (((k : ℕ).choose 2 : ℕ) : ℝ)⁻¹ := fun k => by
    rw [integral_congr_ae (g := fun t : Icc 2 n → ℝ => t k)
      (by filter_upwards [hpi] with t ht; exact max_eq_left (ht k))]
    have := (KingmanTimes.ofPi n).integral_T k.2
    simpa [KingmanTimes.ofPi, Finset.mem_Icc.1 k.2] using this
  have e : ∀ t : Icc 2 n → ℝ, pairPathOverlap h s s' t = ∑ b : KingmanBranch n,
      (if b ∈ pairPath h s ∩ pairPath h s' then (1 : ℝ) else 0) * max (t b.1) 0 := by
    intro t
    simp only [pairPathOverlap, kingmanBranchLength, Real.coe_toNNReal', ite_mul, one_mul,
      zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [e]
  rw [integral_finsetSum _ fun b _ => (hTi b.1).pos_part.const_mul _]
  simp_rw [integral_const_mul, hmax]
  rw [Fintype.sum_sigma, futureOverlap,
    ← sum_Icc_sub_eq_sum_Ico (fun u => overlapCount h s s' u / rateAfter n u)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := (Finset.mem_Icc.1 k.2).2
  dsimp only
  rw [← Finset.sum_mul, rateAfter_sub hk, div_eq_mul_inv]
  congr 1
  rw [overlapCount, Nat.sub_sub_self hk, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [pairPath, branchBlock]

private theorem two_le_of_ne {a b : Fin n} (hab : a ≠ b) : 2 ≤ n := by
  have := a.2
  have := b.2
  have : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
  omega

private theorem pair_mem_samplePairs {a b : Fin n} (hab : a ≠ b) :
    ({a, b} : Finset (Fin n)) ∈ samplePairs n :=
  Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, Finset.card_pair hab⟩

private theorem card_rankedHistory_pos : (0 : ℝ) < Fintype.card (RankedHistory n) := by
  exact_mod_cast Fintype.card_pos_iff.2 ⟨fun i => Classical.arbitrary _⟩

/-- `E[τ_s τ_{s'}]` as an average over histories. -/
theorem integral_pairCoalTime_mul_eq_sum (hn : 2 ≤ n) {s s' : Finset (Fin n)}
    (hs : s ∈ samplePairs n) (hs' : s' ∈ samplePairs n) :
    ∫ g, pairCoalTime g.2 s g.1 * pairCoalTime g.2 s' g.1 ∂kingmanGenealogyMeasure n =
      (∑ h, futureProd h s s' 0) / Fintype.card (RankedHistory n) := by
  have hi : Integrable (fun g : (Icc 2 n → ℝ) × RankedHistory n =>
      pairCoalTime g.2 s g.1 * pairCoalTime g.2 s' g.1) ((piMeasure n).prod (randomJoining n)) :=
    (memLp_pairCoalTime hn hs).integrable_mul (memLp_pairCoalTime hn hs')
  rw [kingmanGenealogyMeasure, integral_prod_symm _ hi]
  simp_rw [integral_pairCoalTime_mul_piMeasure]
  exact integral_randomJoining _

/-- `E[ℓ(path s ∩ path s')]` as an average over histories. -/
theorem integral_pairPathOverlap_eq_sum (s s' : Finset (Fin n)) :
    ∫ g, pairPathOverlap g.2 s s' g.1 ∂kingmanGenealogyMeasure n =
      (∑ h, futureOverlap h s s' 0) / Fintype.card (RankedHistory n) := by
  have hi : Integrable (fun g : (Icc 2 n → ℝ) × RankedHistory n => pairPathOverlap g.2 s s' g.1)
      ((piMeasure n).prod (randomJoining n)) := integrable_pairPathOverlap s s'
  rw [kingmanGenealogyMeasure, integral_prod_symm _ hi]
  simp_rw [integral_pairPathOverlap_piMeasure]
  exact integral_randomJoining _

/-! #### Two pairs sharing a gene -/

/-- **Product moment of the coalescence times of two pairs sharing a gene**:
`E[τ_{ab} τ_{ac}] = 4/3`. -/
theorem integral_pairCoalTime_mul_shared {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    ∫ g, pairCoalTime g.2 {a, b} g.1 * pairCoalTime g.2 {a, c} g.1 ∂kingmanGenealogyMeasure n =
      4 / 3 := by
  rw [integral_pairCoalTime_mul_eq_sum (two_le_of_ne hab) (pair_mem_samplePairs hab)
    (pair_mem_samplePairs hac)]
  have key := sum_mul_apart3_futureProd (a := a) (b := b) (c := c) (n - 1) 0 (by omega)
    (fun _ => 1) (dependsBefore_const 1 0)
  have h0 : ∀ h : RankedHistory n, Apart3 h a b c 0 :=
    fun h => ⟨pairApart_zero h hab, pairApart_zero h hac, pairApart_zero h hbc⟩
  simp only [h0, ↓reduceIte, one_mul, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at key
  rw [key]
  have := (card_rankedHistory_pos (n := n)).ne'
  field_simp

/-- **Covariance of the coalescence times of two pairs sharing a gene**: `Cov(τ_{ab}, τ_{ac}) =
1/3`. -/
theorem covariance_pairCoalTime_shared {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    cov[fun g => pairCoalTime g.2 {a, b} g.1, fun g => pairCoalTime g.2 {a, c} g.1;
      kingmanGenealogyMeasure n] = 1 / 3 := by
  have hn := two_le_of_ne hab
  rw [covariance_eq_sub (memLp_pairCoalTime hn (pair_mem_samplePairs hab))
    (memLp_pairCoalTime hn (pair_mem_samplePairs hac))]
  simp only [Pi.mul_apply]
  rw [integral_pairCoalTime_mul_shared hab hac hbc,
    integral_pairCoalTime_kingmanGenealogyMeasure hn (pair_mem_samplePairs hab),
    integral_pairCoalTime_kingmanGenealogyMeasure hn (pair_mem_samplePairs hac)]
  norm_num

/-- **Mean overlap of the paths of two pairs sharing a gene**: `E[ℓ(P_{ab} ∩ P_{ac})] = 1`
(the branch from `a` to the meeting point, `τ_{ab} + τ_{ac} - τ_{bc}`). -/
theorem integral_pairPathOverlap_shared {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    ∫ g, pairPathOverlap g.2 {a, b} {a, c} g.1 ∂kingmanGenealogyMeasure n = 1 := by
  rw [integral_pairPathOverlap_eq_sum]
  simp_rw [futureOverlap_shared _ 0 hab hac]
  have hM : ∀ {u v : Fin n}, u ≠ v → ∑ h : RankedHistory n, futureMean h {u, v} 0 =
      Fintype.card (RankedHistory n) := by
    intro u v huv
    have := sum_mul_futureMean (a := u) (b := v) (n - 1) 0 (by omega) (fun _ => 1)
      (dependsBefore_const 1 0)
    simp only [one_mul, apartInd, pairApart_zero _ huv, ↓reduceIte, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one] at this
    exact this
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hM hab, hM hac, hM hbc]
  have := (card_rankedHistory_pos (n := n)).ne'
  field_simp
  ring

/-- **Covariance of the pairwise differences of two pairs sharing a gene** (Tajima 1983):
`Cov(D_{ab}, D_{ac}) = θ/2 + θ²/3`. -/
theorem covariance_pairDiff_shared {θ : ℝ≥0} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    cov[pairDiff (fun p => p.1.2) Prod.snd {a, b}, pairDiff (fun p => p.1.2) Prod.snd {a, c};
        kingmanTreeMutationMeasure n θ] = (θ : ℝ) / 2 + (θ : ℝ) ^ 2 / 3 := by
  rw [covariance_pairDiff_kingmanTreeMutationMeasure (two_le_of_ne hab)
    (pair_mem_samplePairs hab) (pair_mem_samplePairs hac),
    covariance_pairCoalTime_shared hab hac hbc, integral_pairPathOverlap_shared hab hac hbc]
  ring

/-! #### Two disjoint pairs -/

/-- **Product moment of the coalescence times of two disjoint pairs**:
`E[τ_{ab} τ_{cd}] = 11/9`. -/
theorem integral_pairCoalTime_mul_disjoint {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∫ g, pairCoalTime g.2 {a, b} g.1 * pairCoalTime g.2 {c, d} g.1 ∂kingmanGenealogyMeasure n =
      11 / 9 := by
  rw [integral_pairCoalTime_mul_eq_sum (two_le_of_ne hab) (pair_mem_samplePairs hab)
    (pair_mem_samplePairs hcd)]
  have key := sum_mul_apart4_futureProd (a := a) (b := b) (c := c) (d := d) (n - 1) 0 (by omega)
    (fun _ => 1) (dependsBefore_const 1 0)
  have h0 : ∀ h : RankedHistory n, Apart4 h a b c d 0 :=
    fun h => ⟨pairApart_zero h hab, pairApart_zero h hac, pairApart_zero h had,
      pairApart_zero h hbc, pairApart_zero h hbd, pairApart_zero h hcd⟩
  simp only [h0, ↓reduceIte, one_mul, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at key
  rw [key]
  have := (card_rankedHistory_pos (n := n)).ne'
  field_simp

/-- **Covariance of the coalescence times of two disjoint pairs**: `Cov(τ_{ab}, τ_{cd}) = 2/9`. -/
theorem covariance_pairCoalTime_disjoint {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    cov[fun g => pairCoalTime g.2 {a, b} g.1, fun g => pairCoalTime g.2 {c, d} g.1;
      kingmanGenealogyMeasure n] = 2 / 9 := by
  have hn := two_le_of_ne hab
  rw [covariance_eq_sub (memLp_pairCoalTime hn (pair_mem_samplePairs hab))
    (memLp_pairCoalTime hn (pair_mem_samplePairs hcd))]
  simp only [Pi.mul_apply]
  rw [integral_pairCoalTime_mul_disjoint hab hac had hbc hbd hcd,
    integral_pairCoalTime_kingmanGenealogyMeasure hn (pair_mem_samplePairs hab),
    integral_pairCoalTime_kingmanGenealogyMeasure hn (pair_mem_samplePairs hcd)]
  norm_num

/-- **Mean overlap of the paths of two disjoint pairs**: `E[ℓ(P_{ab} ∩ P_{cd})] = 2/3`. -/
theorem integral_pairPathOverlap_disjoint {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∫ g, pairPathOverlap g.2 {a, b} {c, d} g.1 ∂kingmanGenealogyMeasure n = 2 / 3 := by
  rw [integral_pairPathOverlap_eq_sum]
  have key := sum_mul_apart4_futureOverlap hab hac had hbc hcd (n - 1) 0 (by omega)
    (fun _ => 1) (dependsBefore_const 1 0)
  have h0 : ∀ h : RankedHistory n, Apart4 h a b c d 0 :=
    fun h => ⟨pairApart_zero h hab, pairApart_zero h hac, pairApart_zero h had,
      pairApart_zero h hbc, pairApart_zero h hbd, pairApart_zero h hcd⟩
  simp only [h0, ↓reduceIte, one_mul, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at key
  rw [key]
  have := (card_rankedHistory_pos (n := n)).ne'
  field_simp

/-- **Covariance of the pairwise differences of two disjoint pairs** (Tajima 1983):
`Cov(D_{ab}, D_{cd}) = θ/3 + 2θ²/9`. -/
theorem covariance_pairDiff_disjoint {θ : ℝ≥0} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    cov[pairDiff (fun p => p.1.2) Prod.snd {a, b}, pairDiff (fun p => p.1.2) Prod.snd {c, d};
        kingmanTreeMutationMeasure n θ] = (θ : ℝ) / 3 + 2 * (θ : ℝ) ^ 2 / 9 := by
  rw [covariance_pairDiff_kingmanTreeMutationMeasure (two_le_of_ne hab)
    (pair_mem_samplePairs hab) (pair_mem_samplePairs hcd),
    covariance_pairCoalTime_disjoint hab hac had hbc hbd hcd,
    integral_pairPathOverlap_disjoint hab hac had hbc hbd hcd]
  ring

end DistinctPairs

end MathlibExt.Biology.PopulationGenetics.Coalescent
