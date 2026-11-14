/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Mutation
public import MathlibExt.Biology.PopulationGenetics.Coalescent.Topology

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

The segregating-site moments are not repeated here (see `Mutation.lean`). The law
`τ_s ~ Exp(1)` itself (hypothesis `hτ` of `integral_meanPairDiff`) is not derived; only its mean
is, which is what `E π = θ` needs. The covariances between the pairwise differences of two pairs
(the input to Tajima's `Var π`) are not treated.

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

end MathlibExt.Biology.PopulationGenetics.Coalescent
