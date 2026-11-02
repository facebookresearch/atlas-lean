/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent

/-!
# Tests for the multispecies coalescent

Concrete species trees and their clusters, the one-species boundary case, the star-tree limits
(zero internal branches give the random-joining probabilities `1/3`, `1/18`, `1/9`), a point
inside and a point outside the four-species anomaly zone, unrooted quartets at the boundary,
clade probabilities for small samples (including the excluded case `k = m`), and junk values
outside the parameter domains.
-/

@[expose] public section

open MeasureTheory Finset Filter Topology

namespace MathlibExtTest.Biology.PopulationGenetics.MultispeciesCoalescent

open MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting
open MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent

/-! ### Species trees -/

/-- The caterpillar species tree has the four leaves and the clusters `{0, 1}`, `{0, 1, 2}`. -/
example : (caterpillar 1 2).taxa = univ ∧
    {0, 1} ∈ (caterpillar 1 2).clusters ∧ {0, 1, 2} ∈ (caterpillar 1 2).clusters ∧
    {0, 2} ∉ (caterpillar 1 2).clusters := by
  simp only [caterpillar, SpeciesTree.taxa, SpeciesTree.clusters]
  decide

/-- The balanced species tree has the clusters `{0, 1}` and `{2, 3}`. -/
example : (balanced 1 2).clusters = balancedTree 0 1 2 3 := by
  simp only [balanced, SpeciesTree.clusters, SpeciesTree.taxa, balancedTree]
  decide

/-- The shape forgets branch lengths. -/
example : (triple 1).shape = (triple 5).shape := rfl

/-- Merging along a history from the singletons: after one coalescence of three genes there
are two lineages, one of which is a pair. -/
example : ∀ h : RankedHistory 3, (mergeAlong ((List.finRange 3).map fun j => {j}) h 1).length = 2
    := by
  decide +kernel

/-- One species, one lineage: the gene tree is the single leaf with probability one. -/
example : geneTreeProb (.leaf 0 : SpeciesTree 1) (· = {{0}}) = 1 := by
  simp [geneTreeProb]

/-- The weights of all gene trees sum to one for any species tree, e.g. a five-species tree. -/
example : geneTreeProb (.node (.node (.leaf 0) (.leaf 1) 1)
    (.node (.leaf 2) (.node (.leaf 3) (.leaf 4) 2) 3) 0 : SpeciesTree 5) (fun _ => True) = 1 :=
  geneTreeProb_true _

/-- With nonnegative branch lengths every gene-tree probability lies in `[0, 1]`. -/
example {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (G : Finset (Finset (Fin 4))) :
    0 ≤ geneTreeProb (caterpillar x y) (· = G) ∧ geneTreeProb (caterpillar x y) (· = G) ≤ 1 := by
  have hT : (caterpillar x y).NonnegLengths :=
    ⟨⟨⟨trivial, trivial, hy⟩, trivial, hx⟩, trivial, le_rfl⟩
  exact ⟨geneTreeProb_nonneg hT _, geneTreeProb_le_one hT _⟩

/-- Disjoint events add: the matching gene tree or `((A, B), (C, D))`. -/
example (x y : ℝ) : geneTreeProb (caterpillar x y)
    (fun G => G = caterpillarTree 0 1 2 3 ∨ G = balancedTree 0 1 2 3) = drF x y + drH x y := by
  rw [geneTreeProb_or _ _ _ (fun G h h' => by subst h; revert h'; decide +kernel),
    geneTreeProb_caterpillar_matching, geneTreeProb_caterpillar_AB_CD]

/-- The three unrooted quartets on the caterpillar have total probability one. -/
example (x y : ℝ) : geneTreeProb (caterpillar x y) (DisplaysSplit 0 1) +
    geneTreeProb (caterpillar x y) (DisplaysSplit 0 2) +
    geneTreeProb (caterpillar x y) (DisplaysSplit 0 3) = 1 := by
  rw [geneTreeProb_caterpillar_split_01, geneTreeProb_caterpillar_split_02,
    geneTreeProb_caterpillar_split_03]
  ring

/-! ### Three species -/

/-- Zero internal branch (star tree): the three gene trees are equally likely, `1/3` each. -/
example : geneTreeProb (triple 0) (· = tripleTree {0, 1}) = 1 / 3 ∧
    geneTreeProb (triple 0) (· = tripleTree {0, 2}) = 1 / 3 := by
  rw [geneTreeProb_triple_matching, geneTreeProb_triple_cherry_02]
  norm_num

/-- The three gene-tree probabilities sum to one. -/
example (t : ℝ) : geneTreeProb (triple t) (· = tripleTree {0, 1}) +
    geneTreeProb (triple t) (· = tripleTree {0, 2}) +
    geneTreeProb (triple t) (· = tripleTree {1, 2}) = 1 := by
  rw [geneTreeProb_triple_matching, geneTreeProb_triple_cherry_02, geneTreeProb_triple_cherry_12]
  ring

/-- With a positive internal branch the matching gene tree is the most probable. -/
example : geneTreeProb (triple 1) (· = tripleTree {1, 2}) <
    geneTreeProb (triple 1) (· = (triple 1).clusters) :=
  (triple_no_anomaly one_pos).2

/-! ### Four species -/

/-- Zero internal branches: the matching asymmetric gene tree has the random-joining
probability `1/18` and the symmetric gene tree `((A, B), (C, D))` has `1/9`, so it is
anomalous. -/
example : geneTreeProb (caterpillar 0 0) (· = caterpillarTree 0 1 2 3) = 1 / 18 ∧
    geneTreeProb (caterpillar 0 0) (· = balancedTree 0 1 2 3) = 1 / 9 := by
  rw [geneTreeProb_caterpillar_matching, geneTreeProb_caterpillar_AB_CD]
  simp only [drF, drH]
  norm_num

/-- Sanity check against the paper: `f + 2g + h` plus the eleven other gene trees is one, so
`f + 2g + h ≤ 1`; at the star tree `f + 2g + h = 1/18 + 2/9 + 1/9 = 7/18`. -/
example : drF 0 0 + 2 * drG 0 0 + drH 0 0 = 7 / 18 := by
  simp only [drF, drG, drH]
  norm_num

/-- Short deep branches make the symmetric gene tree anomalous even when the shallower branch
is long (here `y = 1`), because `a(x) → ∞` as `x → 0⁺`. -/
example : ∃ x > 0, geneTreeProb (caterpillar x 1) (· = (caterpillar x 1).clusters) <
    geneTreeProb (caterpillar x 1) (· = balancedTree 0 1 2 3) := by
  obtain ⟨x, hx1, hx0⟩ :=
    ((tendsto_anomalyA.eventually (eventually_gt_atTop 1)).and self_mem_nhdsWithin).exists
  exact ⟨x, hx0, (caterpillar_anomalous_iff hx0 1).2 hx1⟩

/-- A point outside the anomaly zone: long branches make the matching gene tree more probable
than `((A, B), (C, D))`. -/
example : geneTreeProb (caterpillar 1 1) (· = balancedTree 0 1 2 3) <
    geneTreeProb (caterpillar 1 1) (· = (caterpillar 1 1).clusters) := by
  rw [clusters_caterpillar, geneTreeProb_caterpillar_matching, geneTreeProb_caterpillar_AB_CD]
  simp only [drF, drH]
  have h1 : Real.exp (-1) < 1 / 2 := by
    rw [Real.exp_neg]
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have h2 : 0 < Real.exp (-1) := Real.exp_pos _
  have h3 : 0 < Real.exp (-(1 + 1)) := Real.exp_pos _
  have h4 : 0 < Real.exp (-(3 * 1 + 1)) := Real.exp_pos _
  generalize Real.exp (-1) = a at *
  generalize Real.exp (-(1 + 1)) = b at *
  generalize Real.exp (-(3 * 1 + 1)) = c at *
  linarith

/-- The anomaly zone as a statement about all gene trees: with a short deep branch the
caterpillar has some anomalous gene tree exactly when `y < a(x)`. -/
example {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (h : anomalyA x ≤ y) (G : Finset (Finset (Fin 4))) :
    geneTreeProb (caterpillar x y) (· = G) ≤
      geneTreeProb (caterpillar x y) (· = (caterpillar x y).clusters) := by
  by_contra hG
  exact absurd ((caterpillar_exists_anomalous_iff hx hy).1 ⟨G, not_le.1 hG⟩) (not_lt.2 h)

/-- The balanced species tree has no anomalous gene tree; at zero branch lengths the other
balanced gene trees tie with the matching one (`1/9` each). -/
example : geneTreeProb (balanced 0 0) (· = balancedTree 0 2 1 3) ≤
    geneTreeProb (balanced 0 0) (· = balancedTree 0 1 2 3) :=
  balanced_no_anomaly le_rfl le_rfl _

/-- At zero internal branches the three unrooted quartets are equally likely. -/
example : geneTreeProb (caterpillar 0 0) (DisplaysSplit 0 1) = 1 / 3 ∧
    geneTreeProb (balanced 0 0) (DisplaysSplit 0 2) = 1 / 3 := by
  rw [geneTreeProb_caterpillar_split_01, geneTreeProb_balanced_split_02]
  norm_num

/-- Unrooted quartet probabilities do not depend on the deeper branch of the caterpillar. -/
example (x x' y : ℝ) : geneTreeProb (caterpillar x y) (DisplaysSplit 0 1) =
    geneTreeProb (caterpillar x' y) (DisplaysSplit 0 1) := by
  rw [geneTreeProb_caterpillar_split_01, geneTreeProb_caterpillar_split_01]

/-! ### Clade probabilities -/

/-- A pair among four genes is a clade with probability `2/9`. -/
example : (randomJoining 4).real {h | IsClade h {0, 1}} = 2 / 9 := by
  rw [randomJoining_isClade_of_le_five (by norm_num) _ (by decide) (by decide)]
  norm_num [Nat.choose]

/-- Three of four genes form a clade with probability `2 / (4 · 3) = 1/6`. -/
example : (randomJoining 4).real {h | IsClade h {0, 1, 2}} = 1 / 6 := by
  rw [randomJoining_isClade_of_le_five (by norm_num) _ (by decide) (by decide)]
  norm_num [Nat.choose]

/-- The excluded case `k = m`: the whole sample is always a clade (probability `1`), while the
formula would give `2m / (m (m + 1)) = 1/2` for `m = 3`. -/
example : (randomJoining 3).real {h | IsClade h univ} = 1 := by
  rw [randomJoining_real]
  simp only [Set.mem_ofPred_eq]
  rw [show #{h : RankedHistory 3 | IsClade h univ} = 3 by decide +kernel,
    show Icc 2 3 = {2, 3} by decide]
  norm_num [Nat.choose]

/-! ### Junk values outside the domains -/

/-- Tavaré's formula is an identity for all real `t`, but only `t ≥ 0` is a probability: at
`t = -1` the "probability" of no coalescence is `e > 1`. -/
example : 1 < tavareProb 2 2 (-1) := by
  rw [tavareProb_two_two, neg_neg]
  simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (one_pos (α := ℝ))

/-- Outside `NonnegLengths`, `geneTreeProb` is only a signed weight: with internal branch `-1`
the matching three-species gene tree gets `1 - (2/3) e < 0`. -/
example : geneTreeProb (triple (-1)) (· = tripleTree {0, 1}) < 0 := by
  rw [geneTreeProb_triple_matching, neg_neg]
  have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
  linarith

/-- At `x = 0` the denominator of `a(x)` vanishes and Lean's `a / 0 = 0` gives the junk value
`a(0) = log (2/3)`; the anomaly-zone theorem assumes `x > 0`. -/
example : anomalyA 0 = Real.log (2 / 3) := by
  simp [anomalyA]

end MathlibExtTest.Biology.PopulationGenetics.MultispeciesCoalescent
