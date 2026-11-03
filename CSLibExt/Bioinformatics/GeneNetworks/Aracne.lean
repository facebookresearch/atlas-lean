/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Sym.Sym2

/-!
# ARACNE: pruning gene networks with the data-processing inequality

ARACNE (Margolin et al. 2006) reconstructs a gene network from pairwise mutual informations
`I i k`. It starts from all pairs with `I i k > I₀` and examines every triplet whose three mutual
informations all exceed `I₀`, removing the edge with the smallest value. The output does not
depend on the order in which triplets are examined. `aracne I hI I₀` is this output with DPI
tolerance zero: the pair `{i, k}` is kept iff `I₀ < I i k` and no third gene `j` with
`I₀ < I i j` and `I₀ < I j k` has `I i k < min (I i j) (I j k)`. When two values of a triplet tie
for the smallest, neither tied edge is removed by that triplet.

The mutual informations are abstract real weights here. The hypotheses of the theorems are the
data-processing inequality for separated triples: if every path from `a` to `b` in the true network
`T` passes through `c`, then `I a b ≤ min (I a c) (I c b)` (strictly, for exact recovery). For a
joint law that is Markov with respect to `T`, the finite data-processing inequality
`InformationTheory.finiteMutualInformation_le_left_of_markov` (and `..._right_...`) gives the
non-strict form for each such triple. Deriving the conditional independence of `X_a` and `X_b`
given `X_c` from graph separation (the global Markov property) is not part of this file.

## Main results

* `le_aracne_of_isAcyclic`: if `T` is a forest whose edges all have `I > I₀`, the non-strict
  data-processing inequality on separated triples implies that ARACNE keeps every edge of `T`
  (no false negatives).
* `aracne_le_of_isTree`: if `T` is a tree, the strict data-processing inequality on separated
  triples implies that ARACNE keeps no pair outside `T` (no false positives).
* `aracne_eq_of_isTree` (Margolin et al. 2006, Theorem 1, with the paper's exclusion of exact
  cancellations made explicit as strictness): under both, ARACNE returns `T` exactly.
* `le_aracne_of_isMaxWeightSpanningTree` (Margolin et al. 2006, Theorem 2): every maximum
  mutual-information spanning tree (a Chow–Liu tree) whose edges all have `I > I₀` is a subnetwork
  of the ARACNE network.

## References

* A. A. Margolin, I. Nemenman, K. Basso, C. Wiggins, G. Stolovitzky, R. Dalla Favera and
  A. Califano, "ARACNE: an algorithm for the reconstruction of gene regulatory networks in a
  mammalian cellular context", *BMC Bioinformatics* 7 (Suppl. 1) (2006), S7.
* C. K. Chow and C. N. Liu, "Approximating discrete probability distributions with dependence
  trees", *IEEE Trans. Inform. Theory* 14 (1968), 462–467.
-/

@[expose] public section

namespace Cslib.Bioinformatics.GeneNetworks.Aracne

variable {V : Type*}

/-- The network ARACNE reconstructs from symmetric pairwise mutual informations `I` with
independence threshold `I₀` and DPI tolerance zero (Margolin et al. 2006): `{i, k}` is an edge
iff `i ≠ k`, `I₀ < I i k`, and no third gene `j` with `I₀ < I i j` and `I₀ < I j k` has
`I i k < min (I i j) (I j k)`. -/
def aracne (I : V → V → ℝ) (hI : ∀ i k, I i k = I k i) (I₀ : ℝ) : SimpleGraph V where
  Adj i k := i ≠ k ∧ I₀ < I i k ∧
    ∀ j, j ≠ i → j ≠ k → I₀ < I i j → I₀ < I j k → min (I i j) (I j k) ≤ I i k
  symm := ⟨by
    rintro i k ⟨hik, h0, h⟩
    refine ⟨hik.symm, hI i k ▸ h0, fun j hjk hji hkj hji' ↦ ?_⟩
    rw [hI k j, hI j i] at *
    rw [hI k i, min_comm]
    exact h j hji hjk hji' hkj⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- In a forest, for an edge `i - k` and any vertex `j`, either `k` separates `j` from `i` or `i`
separates `j` from `k`: otherwise two walks avoiding them would join `i` to `k` without the bridge
`s(i, k)`. -/
private theorem separates_of_adj {T : SimpleGraph V} (hT : T.IsAcyclic) {i k : V}
    (hik : T.Adj i k) (j : V) :
    (∀ p : T.Walk j i, k ∈ p.support) ∨ (∀ p : T.Walk j k, i ∈ p.support) := by
  by_contra h
  push Not at h
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := h
  have := SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT hik) (p.reverse.append q)
  rw [SimpleGraph.Walk.edges_append, List.mem_append, SimpleGraph.Walk.edges_reverse,
    List.mem_reverse] at this
  rcases this with h | h
  · exact hp (p.snd_mem_support_of_mem_edges h)
  · exact hq (q.fst_mem_support_of_mem_edges h)

/-- **No false negatives**: if the true network `T` is a forest whose edges all carry mutual
information above `I₀`, and `I a b ≤ min (I a c) (I c b)` whenever `c` separates `a` from `b` in
`T` (every walk from `a` to `b` visits `c`), then ARACNE keeps every edge of `T`. -/
theorem le_aracne_of_isAcyclic (T : SimpleGraph V) (hT : T.IsAcyclic) (I : V → V → ℝ)
    (hI : ∀ i k, I i k = I k i) (I₀ : ℝ) (hedge : ∀ i k, T.Adj i k → I₀ < I i k)
    (hdpi : ∀ a b c, c ≠ a → c ≠ b → (∀ p : T.Walk a b, c ∈ p.support) →
      I a b ≤ min (I a c) (I c b)) :
    T ≤ aracne I hI I₀ := by
  intro i k hik
  refine ⟨T.ne_of_adj hik, hedge i k hik, fun j hji hjk _ _ ↦ ?_⟩
  rcases separates_of_adj hT hik j with h | h
  · have := hdpi j i k hjk.symm (T.ne_of_adj hik).symm h
    rw [hI j i, hI k i] at this
    exact (min_le_left _ _).trans (this.trans (min_le_right _ _))
  · have := hdpi j k i hji.symm (T.ne_of_adj hik) h
    exact (min_le_right _ _).trans (this.trans (min_le_right _ _))

/-- **No false positives**: if the true network `T` is a tree and `I a b < min (I a c) (I c b)`
whenever `c` separates `a` from `b` in `T`, then every edge ARACNE keeps is an edge of `T`. -/
theorem aracne_le_of_isTree (T : SimpleGraph V) (hT : T.IsTree) (I : V → V → ℝ)
    (hI : ∀ i k, I i k = I k i) (I₀ : ℝ)
    (hdpi : ∀ a b c, c ≠ a → c ≠ b → (∀ p : T.Walk a b, c ∈ p.support) →
      I a b < min (I a c) (I c b)) :
    aracne I hI I₀ ≤ T := by
  classical
  rintro i k ⟨hik, h0, hkeep⟩
  by_contra hadj
  obtain ⟨w⟩ := hT.connected.preconnected i k
  set P : T.Path i k := ⟨w.bypass, w.bypass_isPath⟩
  have hc : ∃ c, c ≠ i ∧ c ≠ k ∧ c ∈ P.1.support := by
    obtain ⟨P, -⟩ := P
    cases P with
    | nil => exact absurd rfl hik
    | cons h q => exact ⟨_, (T.ne_of_adj h).symm, fun hk ↦ hadj (hk ▸ h), by simp⟩
  obtain ⟨c, hci, hck, hcP⟩ := hc
  have hsep : ∀ q : T.Walk i k, c ∈ q.support := by
    intro q
    have : (⟨q.bypass, q.bypass_isPath⟩ : T.Path i k) = P :=
      (hT.isAcyclic.subsingleton_path i k).elim _ _
    have hq : q.bypass = P.1 := congrArg Subtype.val this
    exact q.support_bypass_subset_support (hq ▸ hcP)
  have hlt := hdpi i k c hci hck hsep
  have := hkeep c hci hck (h0.trans (hlt.trans_le (min_le_left _ _)))
    (h0.trans (hlt.trans_le (min_le_right _ _)))
  exact absurd this (not_le.mpr hlt)

/-- **ARACNE recovers tree networks exactly** (Margolin et al. 2006, Theorem 1): if the true
network `T` is a tree whose edges all carry mutual information above `I₀`, and the strict
data-processing inequality holds on every separated triple, then ARACNE returns `T`. Strictness
is the explicit form of the paper's exclusion of exact cancellations; with equality ARACNE can
keep an indirect edge (see the tests). -/
theorem aracne_eq_of_isTree (T : SimpleGraph V) (hT : T.IsTree) (I : V → V → ℝ)
    (hI : ∀ i k, I i k = I k i) (I₀ : ℝ) (hedge : ∀ i k, T.Adj i k → I₀ < I i k)
    (hdpi : ∀ a b c, c ≠ a → c ≠ b → (∀ p : T.Walk a b, c ∈ p.support) →
      I a b < min (I a c) (I c b)) :
    aracne I hI I₀ = T :=
  le_antisymm (aracne_le_of_isTree T hT I hI I₀ hdpi)
    (le_aracne_of_isAcyclic T hT.isAcyclic I hI I₀ hedge fun a b c hca hcb hsep ↦
      (hdpi a b c hca hcb hsep).le)

/-- Deleting an edge `s(i, k)` of a tree leaves every vertex reachable from `i` or from `k`. -/
private theorem reachable_or_reachable_delete_edge (T : SimpleGraph V)
    (hT : T.IsTree) (i k v : V) (hik : T.Adj i k) :
    (T.deleteEdges {s(i, k)}).Reachable i v ∨
      (T.deleteEdges {s(i, k)}).Reachable k v := by
  classical
  by_cases h : (T.deleteEdges {s(i, k)}).Reachable i v
  · exact Or.inl h
  · right
    have hb := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic hik
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath k v
    apply SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
    refine ⟨p, ?_⟩
    have hki : ¬(T.deleteEdges {s(k, i)}).Reachable k i := by
      simpa only [Sym2.eq_swap] using (fun r ↦ hb r.symm)
    have hvi : ¬(T.deleteEdges {s(k, i)}).Reachable v i := by
      simpa only [Sym2.eq_swap] using (fun r ↦ h r.symm)
    simpa only [Sym2.eq_swap] using hp.isTrail.notMem_edges_of_not_reachable hki hvi

/-- Exchange argument: in a maximum-weight spanning tree, if `j` stays on the side of `i` after
deleting `s(i, k)`, then `I j k ≤ I i k` (else swap `s(i, k)` for `s(j, k)`). -/
private theorem max_weight_edge_bound [Fintype V] (I : V → V → ℝ)
    (hI : ∀ i k, I i k = I k i) (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree)
    (hmax : ∀ (T' : SimpleGraph V) [DecidableRel T'.Adj], T'.IsTree →
      ∑ e ∈ T'.edgeFinset, Sym2.lift ⟨I, hI⟩ e ≤
        ∑ e ∈ T.edgeFinset, Sym2.lift ⟨I, hI⟩ e)
    (i k j : V) (hik : T.Adj i k) (hjk : j ≠ k)
    (hij : (T.deleteEdges {s(i, k)}).Reachable i j) : I j k ≤ I i k := by
  classical
  let H := T.deleteEdges {s(i, k)}
  let F := H ⊔ SimpleGraph.edge j k
  have hb : ¬H.Reachable i k :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic hik
  have hnr : ¬H.Reachable j k := fun r ↦ hb (hij.trans r)
  have hnadj : ¬H.Adj j k := fun h ↦ hnr h.reachable
  have hedge' : F.Adj j k := Or.inr (by simp [SimpleGraph.adj_edge, hjk])
  have hreach : ∀ v, F.Reachable k v := by
    intro v
    obtain h | h := reachable_or_reachable_delete_edge T hT i k v hik
    · exact hedge'.reachable.symm.trans ((hij.symm.trans h).mono le_sup_left)
    · exact h.mono le_sup_left
  let : Nonempty V := ⟨i⟩
  have hF : F.IsTree :=
    ⟨⟨fun u v ↦ (hreach u).symm.trans (hreach v)⟩,
      (hT.isAcyclic.anti (T.deleteEdges_le _)).sup_edge_of_not_reachable hnr⟩
  have hHedges : H.edgeFinset = T.edgeFinset.erase s(i, k) := by
    ext e
    simp [H, SimpleGraph.edgeSet_deleteEdges, and_comm]
  have hnew : s(j, k) ∉ H.edgeFinset := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hnadj
  have hold : s(i, k) ∈ T.edgeFinset := by simpa using hik
  have hsum : ∑ e ∈ F.edgeFinset, Sym2.lift ⟨I, hI⟩ e ≤
      ∑ e ∈ T.edgeFinset, Sym2.lift ⟨I, hI⟩ e := by
    convert hmax F hF using 1
    congr 1
    ext e
    simp
  have hFedges : F.edgeFinset = H.edgeFinset.cons s(j, k) hnew := by
    ext e
    simp [F, SimpleGraph.edgeSet_edge_of_ne hjk, or_comm]
  rw [hFedges, Finset.sum_cons] at hsum
  have hsplit := Finset.sum_erase_add T.edgeFinset (Sym2.lift ⟨I, hI⟩) hold
  rw [← hHedges] at hsplit
  simp only [Sym2.lift_mk] at hsum hsplit
  rw [← hsplit, add_comm (I j k)] at hsum
  exact (add_le_add_iff_left _).mp hsum

/-- **Chow–Liu trees survive ARACNE** (Margolin et al. 2006, Theorem 2): a spanning tree `T` of
maximum total weight `∑_{{i, k} ∈ T} I i k` among all spanning trees, whose edges all carry
mutual information above `I₀`, is a subnetwork of the ARACNE network. -/
theorem le_aracne_of_isMaxWeightSpanningTree [Fintype V] (I : V → V → ℝ)
    (hI : ∀ i k, I i k = I k i) (I₀ : ℝ) (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree)
    (hmax : ∀ (T' : SimpleGraph V) [DecidableRel T'.Adj], T'.IsTree →
      ∑ e ∈ T'.edgeFinset, Sym2.lift ⟨I, hI⟩ e ≤ ∑ e ∈ T.edgeFinset, Sym2.lift ⟨I, hI⟩ e)
    (hedge : ∀ i k, T.Adj i k → I₀ < I i k) :
    T ≤ aracne I hI I₀ := by
  classical
  intro i k hik
  refine ⟨hik.ne, hedge i k hik, ?_⟩
  intro j hji hjk _ _
  by_cases h : (T.deleteEdges {s(i, k)}).Reachable i j
  · exact (min_le_right _ _).trans (max_weight_edge_bound I hI T hT hmax i k j hik hjk h)
  · have hkj := (reachable_or_reachable_delete_edge T hT i k j hik).resolve_left h
    have hkj' : (T.deleteEdges {s(k, i)}).Reachable k j := by
      simpa only [Sym2.eq_swap] using hkj
    have hb := max_weight_edge_bound I hI T hT hmax k i j hik.symm hji hkj'
    rw [hI j i, hI k i] at hb
    exact (min_le_left _ _).trans hb

end Cslib.Bioinformatics.GeneNetworks.Aracne
