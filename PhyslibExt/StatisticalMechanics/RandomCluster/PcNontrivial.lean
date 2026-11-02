/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.MonotoneLimit
public import MathlibExt.Probability.Percolation.PcNontrivial
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.Limits
/-!
# Positivity of the random-cluster critical point

For `q ≥ 1` and `d ≥ 1`, the critical point `p_c(q, d)` of the random-cluster model on `ℤ^d`
is strictly positive.

## i. Overview

For `q ≥ 1` the wired random-cluster measure on a finite graph is stochastically dominated by
Bernoulli bond percolation with the same `p`: its weight `p^{o(ω)} (1 - p)^{c(ω)} q^{k¹(ω)}`
satisfies the Holley lattice condition against the product measure, because the wired cluster
count `k¹` is antitone in `ω`. An infinite open path from the origin contains, for every `m`, a
self-avoiding open path with `m` edges. There are at most `(2d)^m` such paths and each is open
with Bernoulli probability `p^m`, so the wired infinite-volume percolation probability satisfies
`θ¹(p, q) ≤ (2dp)^m` for all `m`. Hence `θ¹(p, q) = 0` for `p < 1 / (2d)`, and
`p_c(q, d) ≥ 1 / (4d) > 0`.

## ii. Key results

- `wiredFkProb_le_fkProbOne_increasing` : the wired random-cluster measure on a finite graph is
  dominated by Bernoulli percolation (`q = 1`) on increasing events, for `q ≥ 1`.
- `fkProbOne_cylinder` : the Bernoulli probability that a set `F` of edges is open is `p^|F|`.
- `fkTheta_le_pow` : `θ¹(p, q) ≤ (2dp)^m` for every `m`.
- `fkTheta_eq_zero_of_lt` : `θ¹(p, q) = 0` when `2dp < 1`.
- `fkPc_pos` : `0 < p_c(q, d)` for `d ≥ 1` and `q ≥ 1`.

## iii. Table of contents

- A. Domination of the wired measure by Bernoulli percolation
- B. Bernoulli cylinder probabilities
- C. Open self-avoiding walks
- D. Bounds on the wired measure of a walk event
- E. Positivity of the critical point

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 3.21 and Section 5.1.
-/

@[expose] public section

open MeasureTheory Filter Topology Set SimpleGraph
open scoped NNReal ENNReal BigOperators

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]

/-! ## A. Domination of the wired measure by Bernoulli percolation -/

/-- The open subgraph is monotone in the configuration. -/
lemma openGraph_mono {a b : ConfigSpace (Sym2 V)} (h : a ≤ b) :
    openGraph G a ≤ openGraph G b := by
  intro x y hxy
  rw [openGraph_adj] at hxy ⊢
  refine ⟨hxy.1, ?_⟩
  have := h s(x, y)
  rw [hxy.2] at this
  exact le_antisymm le_top this

omit [DecidablePred bdry] in
/-- The wired graph (open edges plus the boundary clique) is monotone in the configuration. -/
lemma wiredGraph_mono {a b : ConfigSpace (Sym2 V)} (h : a ≤ b) :
    wiredGraph G bdry a ≤ wiredGraph G bdry b := by
  unfold wiredGraph
  exact sup_le_sup_right (openGraph_mono G h) _

omit [DecidablePred bdry] in
/-- The wired cluster count `k¹(ω)` is antitone in `ω`. -/
lemma numClustersWired_antitone {a b : ConfigSpace (Sym2 V)} (h : a ≤ b) :
    numClustersWired G bdry b ≤ numClustersWired G bdry a := by
  unfold numClustersWired
  exact SimpleGraph.ConnectedComponent.card_le_card_of_le (wiredGraph_mono G bdry h)

omit [DecidablePred bdry] in
/-- Holley cross inequality between the wired random-cluster weight and the Bernoulli product
weight, for `q ≥ 1`. -/
lemma wiredFkWeight_edgeProduct_cross {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q a * edgeProduct G p b
      ≤ wiredFkWeight G bdry p q (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
  unfold wiredFkWeight
  have hmod : edgeProduct G p a * edgeProduct G p b
      = edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) := by
    rw [edgeProduct_logModular G p a b]; ring
  have hk : numClustersWired G bdry a ≤ numClustersWired G bdry (a ⊓ b) :=
    numClustersWired_antitone G bdry inf_le_left
  have hclust : q ^ numClustersWired G bdry a ≤ q ^ numClustersWired G bdry (a ⊓ b) :=
    pow_le_pow_right₀ hq hk
  have hepa : (0 : ℝ) ≤ edgeProduct G p a := (edgeProduct_pos G hp hp1 a).le
  have hepb : (0 : ℝ) ≤ edgeProduct G p b := (edgeProduct_pos G hp hp1 b).le
  have hepab : (0 : ℝ) ≤ edgeProduct G p (a ⊓ b) := (edgeProduct_pos G hp hp1 (a ⊓ b)).le
  have hepsup : (0 : ℝ) ≤ edgeProduct G p (a ⊔ b) := (edgeProduct_pos G hp hp1 (a ⊔ b)).le
  have hqa : (0 : ℝ) ≤ q ^ numClustersWired G bdry a := pow_nonneg (by linarith) _
  calc edgeProduct G p a * q ^ numClustersWired G bdry a * edgeProduct G p b
      = (edgeProduct G p a * edgeProduct G p b) * q ^ numClustersWired G bdry a := by ring
    _ = (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b)) * q ^ numClustersWired G bdry a := by
          rw [hmod]
    _ ≤ (edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b)) *
          q ^ numClustersWired G bdry (a ⊓ b) := by
          apply mul_le_mul_of_nonneg_left hclust
          exact mul_nonneg hepab hepsup
    _ = edgeProduct G p (a ⊓ b) * q ^ numClustersWired G bdry (a ⊓ b) *
          edgeProduct G p (a ⊔ b) := by
          ring

omit [DecidablePred bdry] in
/-- Holley cross inequality between the wired random-cluster probability and Bernoulli percolation,
for `q ≥ 1`. -/
lemma wiredFkProb_fkProbOne_cross {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q a * fkProb G p 1 b
      ≤ wiredFkProb G bdry p q (a ⊓ b) * fkProb G p 1 (a ⊔ b) := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ1 : 0 < wiredFkZ G bdry p q := wiredFkZ_pos G bdry hp hp1 hq0
  have hZ2 : 0 < fkZ G p 1 := fkZ_pos G hp hp1 one_pos
  unfold wiredFkProb fkProb
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)]
  rw [fkWeight_one, fkWeight_one]
  exact wiredFkWeight_edgeProduct_cross G bdry hp hp1 hq a b

omit [DecidablePred bdry] in
/-- For `q ≥ 1`, the wired random-cluster measure gives every increasing event at most its Bernoulli
percolation probability. -/
lemma wiredFkProb_le_fkProbOne_increasing {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p 1 ω := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun ω => wiredFkProb_nonneg G bdry hp hp1 hq0 ω
  · exact fun ω => fkProb_nonneg G hp hp1 one_pos ω
  · rw [wiredFkProb_sum_eq_one G bdry hp hp1 hq0, fkProb_sum_eq_one G hp hp1 one_pos]
  · exact fun a b => wiredFkProb_fkProbOne_cross G bdry hp hp1 hq a b

/-! ## B. Bernoulli cylinder probabilities -/

/-- Summing a product of single-coordinate factors over all Boolean configurations: coordinates
outside `s` contribute a factor `2` each. -/
lemma sum_prod_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι)
    (h : ι → Bool → ℝ) :
    ∑ ω : ι → Bool, ∏ e ∈ s, h e (ω e)
      = 2 ^ (Fintype.card ι - s.card) * ∏ e ∈ s, (∑ b : Bool, h e b) := by
  classical
  set hbar : ι → Bool → ℝ := fun e b => if e ∈ s then h e b else 1 with hhbar
  have key : ∀ ω : ι → Bool, ∏ e ∈ s, h e (ω e) = ∏ e : ι, hbar e (ω e) := by
    intro ω; rw [Finset.prod_ite_mem Finset.univ s]; congr 1; ext x; simp
  simp_rw [key]; rw [← Fintype.prod_sum]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ s) (fun e => ∑ b : Bool, hbar e b)]
  have h1 : (Finset.univ.filter (· ∈ s)) = s := by ext x; simp
  have h2 : ∀ e ∈ (Finset.univ.filter (fun e => ¬ e ∈ s)), (∑ b : Bool, hbar e b) = 2 := by
    intro e he; simp only [Finset.mem_filter] at he; simp only [hhbar, ite_eq_right he.2]; simp
  rw [Finset.prod_congr rfl h2, Finset.prod_const]
  have hcard : (Finset.univ.filter (fun e => ¬ e ∈ s)).card = Fintype.card ι - s.card := by
    rw [Finset.filter_not, Finset.card_univ_sdiff]; simp
  rw [hcard, h1]
  have h3 : ∀ e ∈ s, (∑ b : Bool, hbar e b) = ∑ b : Bool, h e b := by
    intro e he; simp only [hhbar, ite_eq_left he]
  rw [Finset.prod_congr rfl h3]; ring

/-- Under Bernoulli percolation on a finite graph, a set `F` of edges is open with probability
`p^|F|`. -/
lemma fkProbOne_cylinder {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (F : Finset (Sym2 V))
    (hF : F ⊆ G.edgeFinset) :
    ∑ ω : ConfigSpace (Sym2 V),
        (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * fkProb G p 1 ω = p ^ F.card := by
  classical
  have hZpos : 0 < fkZ G p 1 := fkZ_pos G hp hp1 one_pos
  have hnum : ∑ ω : ConfigSpace (Sym2 V),
      (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * fkProb G p 1 ω
      = (∑ ω : ConfigSpace (Sym2 V),
          (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * edgeProduct G p ω) / fkZ G p 1 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    unfold fkProb; rw [fkWeight_one]; ring
  rw [hnum]
  set h : Sym2 V → Bool → ℝ :=
    fun e b => if e ∈ F then (if b then p else 0) else (if b then p else 1 - p) with hh
  have hforced : (∑ ω : ConfigSpace (Sym2 V),
      (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * edgeProduct G p ω)
      = ∑ ω : ConfigSpace (Sym2 V), ∏ e ∈ G.edgeFinset, h e (ω e) := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    unfold edgeProduct
    by_cases hall : ∀ e ∈ F, ω e = true
    · rw [ite_eq_left hall, one_mul]
      refine Finset.prod_congr rfl (fun e he => ?_)
      simp only [hh]
      by_cases heF : e ∈ F
      · rw [ite_eq_left heF, hall e heF]; simp
      · rw [ite_eq_right heF]
    · rw [ite_eq_right hall, zero_mul]
      symm
      push Not at hall
      obtain ⟨e0, he0F, he0⟩ := hall
      apply Finset.prod_eq_zero (i := e0) (hF he0F)
      have he0' : ω e0 = false := by simpa using he0
      simp only [hh, ite_eq_left he0F, he0']; simp
  rw [hforced, sum_prod_factor]
  have hZ : fkZ G p 1
      = 2 ^ (Fintype.card (Sym2 V) - G.edgeFinset.card)
        * ∏ e ∈ G.edgeFinset, (∑ b : Bool, (if b then p else 1 - p)) := by
    rw [fkZ_one]
    have heq : (∑ ω : ConfigSpace (Sym2 V), edgeProduct G p ω)
        = ∑ ω : ConfigSpace (Sym2 V),
            ∏ e ∈ G.edgeFinset, (fun (e : Sym2 V) (b : Bool) => if b then p else 1 - p) e (ω e) :=
      rfl
    rw [heq, sum_prod_factor G.edgeFinset (fun (e : Sym2 V) (b : Bool) => if b then p else 1 - p)]
  rw [hZ]
  have hprodF : (∏ e ∈ G.edgeFinset, (∑ b : Bool, h e b))
      = ∏ e ∈ G.edgeFinset, (if e ∈ F then p else 1) := by
    refine Finset.prod_congr rfl (fun e _ => ?_)
    simp only [hh]
    by_cases heF : e ∈ F
    · simp [heF]
    · simp only [heF, ite_false]; norm_num
  have hprodZ : (∏ e ∈ G.edgeFinset, (∑ b : Bool, (if b then p else 1 - p)))
      = ∏ e ∈ G.edgeFinset, (1 : ℝ) := by
    refine Finset.prod_congr rfl (fun e _ => ?_); norm_num
  rw [hprodF, hprodZ, Finset.prod_const_one]
  have hpF : (∏ e ∈ G.edgeFinset, (if e ∈ F then p else 1)) = p ^ F.card := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hF, Finset.prod_const]
  rw [hpF]; field_simp

variable {d : ℕ}

/-! ## C. Open self-avoiding walks -/

/-- Extend a word of `m` lattice steps to an infinite word by a fixed padding step. -/
def fkExtWord (m : ℕ) (hd : 0 < d) (w : Fin m → Fin d × Bool) : ℕ → Fin d × Bool :=
  fun k => if hk : k < m then w ⟨k, hk⟩ else (⟨0, hd⟩, false)

/-- The event that some self-avoiding walk of `m` steps from the origin is open. -/
def fkExistsOpenWalk (d m : ℕ) (hd : 0 < d) : Set (ConfigSpace (Sym2 (Site d))) :=
  ⋃ (w : Fin m → Fin d × Bool) (_ : goodWord (fkExtWord m hd w) m), wordEvent (fkExtWord m hd w) m

/-- The event that a given edge is open is clopen. -/
lemma isClopen_singleOpen (e : Sym2 (Site d)) :
    IsClopen {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} = (fun ω => ω e) ⁻¹' {true} := rfl
  rw [h]
  exact IsClopen.preimage (isClopen_discrete _) (continuous_apply e)

/-- The event that a given walk is open is clopen. -/
lemma isClopen_wordEvent (g : ℕ → Fin d × Bool) (m : ℕ) : IsClopen (wordEvent g m) := by
  have heq : wordEvent g m
      = ⋂ k ∈ (Finset.range m : Set ℕ),
          {ω : ConfigSpace (Sym2 (Site d)) | ω (edgeOf g k) = true} := by
    ext ω
    simp only [wordEvent, Set.mem_ofPred_eq, Set.mem_iInter, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h k hk; exact h k (Finset.mem_range.mpr hk)
    · intro h k hk; exact h k (Finset.mem_range.mp hk)
  rw [heq]
  exact Set.Finite.isClopen_biInter (Finset.finite_toSet _) (fun k _ => isClopen_singleOpen _)

/-- The event that a given walk is open is increasing. -/
lemma isIncreasing_wordEvent (g : ℕ → Fin d × Bool) (m : ℕ) : IsIncreasing (wordEvent g m) := by
  intro x y hxy hx k hk
  have := hxy (edgeOf g k)
  rw [hx k hk] at this
  exact le_antisymm le_top this

/-- The open-walk event is clopen. -/
lemma isClopen_fkExistsOpenWalk (m : ℕ) (hd : 0 < d) : IsClopen (fkExistsOpenWalk d m hd) := by
  classical
  rw [fkExistsOpenWalk]
  apply isClopen_iUnion_of_finite
  intro w
  by_cases hgw : goodWord (fkExtWord m hd w) m
  · rw [Set.iUnion_eq_if, ite_eq_left hgw]; exact isClopen_wordEvent _ _
  · rw [Set.iUnion_eq_if, ite_eq_right hgw]; exact isClopen_empty

/-- The open-walk event is increasing. -/
lemma isIncreasing_fkExistsOpenWalk (m : ℕ) (hd : 0 < d) :
    IsIncreasing (fkExistsOpenWalk d m hd) := by
  apply isUpperSet_iUnion₂
  intro w _
  exact isIncreasing_wordEvent _ _

/-- Percolation from the origin implies an open self-avoiding walk of every length `m`. -/
lemma percolationEvent_subset_fkExistsOpenWalk (hd : 0 < d) (m : ℕ) :
    percolationEvent d ⊆ fkExistsOpenWalk d m hd := by
  refine (percolationEvent_subset_iUnion_wordEvent hd m).trans ?_
  refine Set.iUnion_subset (fun g => Set.iUnion_subset (fun hg => ?_))
  set w : Fin m → Fin d × Bool := fun i => g i.1 with hw
  have hvert : ∀ j ≤ m, vertOf g j = vertOf (fkExtWord m hd w) j := by
    intro j hj
    induction j with
    | zero => rfl
    | succ k ih =>
      have hk : k < m := by omega
      rw [vertOf_succ, vertOf_succ, ih (by omega)]
      congr 1 <;> simp only [fkExtWord, dite_eq_left hk, hw]
  have hgood' : goodWord (fkExtWord m hd w) m := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rw [← hvert a (by omega), ← hvert b (by omega)] at hab
    exact hg (by simp only [Finset.coe_range, Set.mem_Iio]; omega)
      (by simp only [Finset.coe_range, Set.mem_Iio]; omega) hab
  have hwe : wordEvent g m = wordEvent (fkExtWord m hd w) m := by
    apply Set.ext; intro ω
    simp only [wordEvent, Set.mem_ofPred_eq, Finset.mem_range]
    have hedge : ∀ k < m, edgeOf g k = edgeOf (fkExtWord m hd w) k := by
      intro k hk; unfold edgeOf; rw [hvert k (by omega), hvert (k + 1) (by omega)]
    constructor
    · intro h k hk; rw [← hedge k hk]; exact h k hk
    · intro h k hk; rw [hedge k hk]; exact h k hk
  rw [hwe]
  exact Set.subset_iUnion_of_subset w (Set.subset_iUnion_of_subset hgood' (le_refl _))

/-! ## D. Bounds on the wired measure of a walk event -/

/-- Extending a box configuration to `ℤ^d` keeps the state of box edges. -/
lemma extendEdge_eq_of_range (n : ℕ) (be : Sym2 (boxVerts d n))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    extendEdge d n ω (edgeIncl d n be) = ω be := by
  unfold extendEdge
  have hmem : edgeIncl d n be ∈ Set.range (edgeIncl d n) := ⟨be, rfl⟩
  rw [dite_eq_left hmem, edgeIncl_injective d n hmem.choose_spec]

/-- An edge that is open in an extended box configuration is a box edge. -/
lemma range_of_extendEdge_true (n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (e : Sym2 (Site d)) (h : extendEdge d n ω e = true) : e ∈ Set.range (edgeIncl d n) := by
  by_contra hc; unfold extendEdge at h; rw [dite_eq_right hc] at h; exact absurd h (by simp)

/-- A box edge whose image is a lattice edge is an edge of the box graph. -/
lemma boxEdge_mem (n : ℕ) (be : Sym2 (boxVerts d n)) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) (heq : edgeIncl d n be = s(x, y)) :
    be ∈ (boxGraph d n).edgeFinset := by
  induction be using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj]
    unfold edgeIncl at heq
    rw [Sym2.map_mk, Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · show (hypercubicLattice d).Adj (u : Site d) (v : Site d); rw [h1, h2]; exact hadj
    · show (hypercubicLattice d).Adj (u : Site d) (v : Site d); rw [h1, h2]; exact hadj.symm

/-- An open self-avoiding walk of `m` steps that lies in the box gives `m` distinct box edges that
are all open. -/
lemma exists_boxF (n m : ℕ) (g : ℕ → Fin d × Bool) (hg : goodWord g m)
    (hrange : ∀ k ∈ Finset.range m, edgeOf g k ∈ Set.range (edgeIncl d n)) :
    ∃ F : Finset (Sym2 (boxVerts d n)), F ⊆ (boxGraph d n).edgeFinset ∧ F.card = m ∧
      (extendEdge d n ⁻¹' wordEvent g m ⊆ {ω | ∀ be ∈ F, ω be = true}) := by
  classical
  set bef : {k // k ∈ Finset.range m} → Sym2 (boxVerts d n) :=
    fun k => (hrange k.1 k.2).choose with hbef
  have hbef_spec : ∀ k : {k // k ∈ Finset.range m}, edgeIncl d n (bef k) = edgeOf g k.1 :=
    fun k => (hrange k.1 k.2).choose_spec
  refine ⟨(Finset.range m).attach.image bef, ?_, ?_, ?_⟩
  · intro f hf
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at hf
    obtain ⟨k, rfl⟩ := hf
    have hadj : (hypercubicLattice d).Adj (vertOf g k.1) (vertOf g (k.1 + 1)) := by
      rw [vertOf_succ]; exact adj_coordShift _ _ _
    exact boxEdge_mem n (bef k) _ _ hadj (by rw [hbef_spec k]; rfl)
  · rw [Finset.card_image_of_injOn, Finset.card_attach, Finset.card_range]
    intro a _ b _ hab
    have heq : edgeIncl d n (bef a) = edgeIncl d n (bef b) := by rw [hab]
    rw [hbef_spec a, hbef_spec b] at heq
    have ha := Finset.mem_range.mp a.2
    have hb := Finset.mem_range.mp b.2
    exact Subtype.ext ((edgeOf_injOn g m hg) (by simp [ha]) (by simp [hb]) heq)
  · intro ω hω be hbe
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at hbe
    obtain ⟨k, rfl⟩ := hbe
    simp only [Set.mem_preimage, wordEvent, Set.mem_ofPred_eq] at hω
    have htrue := hω k.1 k.2
    rw [← hbef_spec k] at htrue
    rw [extendEdge_eq_of_range] at htrue
    exact htrue

/-- Under Bernoulli percolation on the box, a fixed self-avoiding walk of `m` steps is open with
probability at most `p^m`. -/
lemma perWord_box_bound (n m : ℕ) (g : ℕ → Fin d × Bool) (hg : goodWord g m)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
        (extendEdge d n ⁻¹' wordEvent g m).indicator (fun _ => (1 : ℝ)) ω
          * fkProb (boxGraph d n) p 1 ω ≤ p ^ m := by
  classical
  by_cases hempty : (extendEdge d n ⁻¹' wordEvent g m) = ∅
  · rw [hempty]
    simp only [Set.indicator_empty, zero_mul, Finset.sum_const_zero]
    positivity
  · rw [← Set.not_nonempty_iff_eq_empty, not_not] at hempty
    obtain ⟨ω0, hω0⟩ := hempty
    simp only [Set.mem_preimage, wordEvent, Set.mem_ofPred_eq] at hω0
    have hrange : ∀ k ∈ Finset.range m, edgeOf g k ∈ Set.range (edgeIncl d n) :=
      fun k hk => range_of_extendEdge_true n ω0 _ (hω0 k hk)
    obtain ⟨F, hFsub, hFcard, hFcont⟩ := exists_boxF n m g hg hrange
    calc ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
            (extendEdge d n ⁻¹' wordEvent g m).indicator (fun _ => (1 : ℝ)) ω
              * fkProb (boxGraph d n) p 1 ω
        ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
            (if (∀ e ∈ F, ω e = true) then (1 : ℝ) else 0) * fkProb (boxGraph d n) p 1 ω := by
          apply Finset.sum_le_sum
          intro ω _
          apply mul_le_mul_of_nonneg_right _ (fkProb_nonneg (boxGraph d n) hp hp1 one_pos ω)
          by_cases hω : ω ∈ extendEdge d n ⁻¹' wordEvent g m
          · rw [Set.indicator_of_mem hω]
            have hmem : ∀ be ∈ F, ω be = true := hFcont hω
            rw [ite_eq_left hmem]
          · rw [Set.indicator_of_notMem hω]; split <;> positivity
      _ = p ^ F.card := fkProbOne_cylinder (boxGraph d n) hp hp1 F hFsub
      _ = p ^ m := by rw [hFcard]

/-- The wired box measure of an event, as a finite sum over box configurations. -/
lemma wiredFiniteMeasure_real_eq (n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : MeasurableSet A) :
    (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real A
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' A).indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hw : (wiredFiniteMeasure d n hp hp1 hq : Measure _).real A
      = ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure
          (extendEdge d n ⁻¹' A)).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hw, wiredFkPMF_toMeasure_toReal]

/-- For `q ≥ 1`, the wired box measure of the open-walk event is at most `(2dp)^m`. -/
lemma wiredFiniteMeasure_fkExistsOpenWalk_le (n m : ℕ) (hd : 0 < d) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fkExistsOpenWalk d m hd)
      ≤ ((2 * d : ℝ) * p) ^ m := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hAmeas : MeasurableSet (fkExistsOpenWalk d m hd) :=
    (isClopen_fkExistsOpenWalk m hd).isOpen.measurableSet
  set μ1 := fkProb (boxGraph d n) p 1 with hμ1
  rw [wiredFiniteMeasure_real_eq n hp hp1 hq0 _ hAmeas]
  have hHolley :
      (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω)
        ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
            (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω
              * fkProb (boxGraph d n) p 1 ω :=
    wiredFkProb_le_fkProbOne_increasing (boxGraph d n) (boxBoundary d n) hp hp1 hq
      (isIncreasing_preimage_extendEdge d n (isIncreasing_fkExistsOpenWalk m hd))
  refine hHolley.trans ?_
  set S : Finset (Fin m → Fin d × Bool) :=
    Finset.univ.filter (fun w => goodWord (fkExtWord m hd w) m) with hS
  have hsplit : ∀ ω : ConfigSpace (Sym2 (boxVerts d n)),
      (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω
        ≤ ∑ w ∈ S, (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ =>
            (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ extendEdge d n ⁻¹' fkExistsOpenWalk d m hd
    · rw [Set.indicator_of_mem hω]
      rw [Set.mem_preimage, fkExistsOpenWalk, Set.mem_iUnion₂] at hω
      obtain ⟨w, hgw, hwe⟩ := hω
      have hmem : w ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgw⟩
      have hωmem : ω ∈ extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m := hwe
      have hstep := Finset.single_le_sum
        (f := fun w => (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ =>
            (1 : ℝ)) ω)
        (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω) hmem
      rwa [Set.indicator_of_mem hωmem] at hstep
    · rw [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg (fun w _ => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  calc ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' fkExistsOpenWalk d m hd).indicator (fun _ => (1 : ℝ)) ω * μ1 ω
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (∑ w ∈ S, (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ =>
              (1 : ℝ)) ω)
            * μ1 ω := by
        apply Finset.sum_le_sum
        intro ω _
        exact mul_le_mul_of_nonneg_right (hsplit ω) (fkProb_nonneg (boxGraph d n) hp hp1 one_pos ω)
    _ = ∑ w ∈ S, ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (extendEdge d n ⁻¹' wordEvent (fkExtWord m hd w) m).indicator (fun _ =>
              (1 : ℝ)) ω * μ1 ω := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun ω _ => ?_)
        rw [Finset.sum_mul]
    _ ≤ ∑ w ∈ S, p ^ m := by
        apply Finset.sum_le_sum
        intro w hw
        exact perWord_box_bound n m (fkExtWord m hd w) (Finset.mem_filter.mp hw).2 hp hp1
    _ = (S.card : ℝ) * p ^ m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Finset.univ : Finset (Fin m → Fin d × Bool)).card : ℝ) * p ^ m := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp.le m)
        exact_mod_cast Finset.card_le_card (Finset.subset_univ S)
    _ = ((2 * d : ℝ) * p) ^ m := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, Fintype.card_fin]
        push_cast
        rw [mul_pow]
        ring_nf

/-! ## E. Positivity of the critical point -/

/-- For `q ≥ 1`, the wired percolation probability satisfies `θ¹(p, q) ≤ (2dp)^m` for every `m`. -/
lemma fkTheta_le_pow (hd : 0 < d) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (m : ℕ) :
    fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) ≤ ((2 * d : ℝ) * p) ^ m := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨φ, hφ, htends⟩ := wiredInfiniteVolume_isLimit d hp hp1 hq0
  have hmono : fkTheta d hp hp1 hq0 (q := q)
      ≤ (wiredInfiniteVolume d hp hp1 hq0 : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fkExistsOpenWalk d m hd) := by
    unfold fkTheta
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (percolationEvent_subset_fkExistsOpenWalk hd m))
  have hlim : (wiredInfiniteVolume d hp hp1 hq0 : Measure (ConfigSpace (Sym2 (Site d)))).real
        (fkExistsOpenWalk d m hd) ≤ ((2 * d : ℝ) * p) ^ m :=
    le_of_tendsto (htends.tendsto_real_of_isClopen (isClopen_fkExistsOpenWalk m hd))
      (Filter.Eventually.of_forall
        (fun n => wiredFiniteMeasure_fkExistsOpenWalk_le (φ n) m hd hp hp1 hq))
  exact hmono.trans hlim

/-- For `q ≥ 1` and `2dp < 1`, there is no percolation in the wired measure: `θ¹(p, q) = 0`. -/
lemma fkTheta_eq_zero_of_lt (hd : 0 < d) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hsmall : (2 * d : ℝ) * p < 1) :
    fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) = 0 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hbase_nonneg : (0 : ℝ) ≤ (2 * d : ℝ) * p := by positivity
  have htend : Filter.Tendsto (fun m => ((2 * d : ℝ) * p) ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hsmall
  have hle : fkTheta d hp hp1 hq0 (q := q) ≤ 0 :=
    ge_of_tendsto htend (Filter.Eventually.of_forall (fun m => fkTheta_le_pow hd hp hp1 hq m))
  exact le_antisymm hle (fkTheta_nonneg d hp hp1 hq0 (q := q))

/-- The set of `p` with `θ¹(p, q) = 0` is bounded above by `1`. -/
lemma fkSubcriticalSet_bddAbove (d : ℕ) (q : ℝ) : BddAbove (fkSubcriticalSet d q) := by
  refine ⟨1, fun x hx => ?_⟩
  obtain ⟨hp, hp1, hq, _⟩ := hx
  exact hp1.le

/-- Every subcritical `p` is at most `p_c(q, d)`. -/
lemma le_fkPc_of_mem {d : ℕ} {q p : ℝ} (hp : p ∈ fkSubcriticalSet d q) : p ≤ fkPc d q :=
  le_csSup (fkSubcriticalSet_bddAbove d q) hp

/-- **Positivity of the random-cluster critical point.** For `d ≥ 1` and `q ≥ 1`,
`0 < p_c(q, d)`; in fact `p_c(q, d) ≥ 1 / (4d)`.

Reference: G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 5.1. -/
theorem fkPc_pos (hd : 0 < d) {q : ℝ} (hq : 1 ≤ q) : 0 < fkPc d q := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set p : ℝ := 1 / (4 * d) with hp_def
  have hp_pos : 0 < p := by rw [hp_def]; positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : p < 1 := by
    rw [hp_def, div_lt_one (by positivity)]; nlinarith
  have hsmall : (2 * d : ℝ) * p < 1 := by
    rw [hp_def, mul_one_div, div_lt_one (by positivity)]; nlinarith
  have hmem : p ∈ fkSubcriticalSet d q :=
    ⟨hp_pos, hp1, zero_lt_one.trans_le hq, fkTheta_eq_zero_of_lt hd hp_pos hp1 hq hsmall⟩
  exact lt_of_lt_of_le hp_pos (le_fkPc_of_mem hmem)

/-- `fkPc_pos` for `d ≥ 2`. -/
lemma fkPc_pos_of_two_le (hd : 2 ≤ d) {q : ℝ} (hq : 1 ≤ q) : 0 < fkPc d q :=
  fkPc_pos (by omega) hq

end FK

end StatMech
