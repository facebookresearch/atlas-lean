/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.FelsensteinZone
public import Domains.Biology.Phylogenetics.JukesCantor

/-!
# Consistency of neighbor joining under Jukes–Cantor

**Consistency of neighbor joining under Jukes–Cantor** (Jukes & Cantor 1969; Saitou & Nei 1987;
Atteson 1999). Along a path with branch lengths `t₁, …, t_k` the JC transition matrices multiply
to the matrix of length `t₁ + ⋯ + t_k` (`jcPath_eq`), so the JC-corrected difference
probability of two leaves is `μ` times their path length (`jcDistance_jcPath`). With independent
sites, the empirical p-distances converge almost surely (strong law), hence so do the corrected
distances; if neighbor joining recovers the tree from every dissimilarity within a radius
`r > 0` of the scaled tree metric, then almost surely every complete run of neighbor joining on
the corrected empirical distances returns the true splits for all long enough alignments
(`ae_eventually_njRun_splits_jcHat`). For `μ > 0` and internal edge lengths at least `m > 0`,
Atteson's theorem (`njRun_splits_of_abs_sub_lt` in `NeighborJoiningRobustness.lean`) gives the
radius `r = μ m / 2` (`njRecoversWithin_of_le`), so the consistency holds unconditionally
(`ae_eventually_njRun_splits_jcHat_of_le`).

## References

* T. H. Jukes and C. R. Cantor, *Evolution of protein molecules*, in Mammalian Protein
  Metabolism, Academic Press, 1969, 21–132.
* N. Saitou and M. Nei, *The neighbor-joining method: a new method for reconstructing
  phylogenetic trees*, Mol. Biol. Evol. 4 (1987), 406–425.
* K. Atteson, *The performance of neighbor-joining methods of phylogenetic reconstruction*,
  Algorithmica 25 (1999), 251–278.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Phylogenetics.FelsensteinZone

open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
open MathlibExt.Biology.Phylogenetics.JukesCantor NeighborJoining

/-- **Chapman–Kolmogorov along a path**: the JC transition matrix along a path is the
transition matrix of the total length. -/
theorem jcPath_eq (μ : ℝ) (ts : List ℝ) : jcPath μ ts = Matrix.of (jcProb μ ts.sum) := by
  induction ts with
  | nil =>
    ext i j
    change (1 : Matrix (Fin 4) (Fin 4) ℝ) i j = jcProb μ 0 i j
    simp [jcProb_zero, Matrix.one_apply]
  | cons t ts ih =>
    ext i j
    change (Matrix.of (jcProb μ t) * jcPath μ ts) i j = _
    rw [ih, Matrix.mul_apply, List.sum_cons]
    exact sum_jcProb_mul_jcProb μ t ts.sum i j

/-- **JC-corrected distances are path lengths** (Jukes & Cantor 1969): the JC distance of the
probability that the two ends of a path differ is `μ` times the total branch length. -/
theorem jcDistance_jcPath (μ : ℝ) (ts : List ℝ) (i : Fin 4) :
    jcDistance (∑ j ∈ univ.erase i, jcPath μ ts i j) = μ * ts.sum := by
  rw [jcPath_eq]
  exact jcDistance_pDiff μ ts.sum i

/-- **Statistical consistency of neighbor joining under Jukes–Cantor** (Saitou & Nei 1987;
Atteson 1999). Let `(G, ι)` be a binary phylogenetic `X`-tree with path-length metric `d` for
edge lengths `w`, and let the sites be pairwise independent and identically distributed, with
the two-leaf marginals of the JC model with rate `μ` and uniform root: for every path `p` from
`x` to `y`, `ℙ(site x = i, site y = j) = jcPath μ (lengths of p) i j / 4`. If neighbor joining
recovers the tree within some radius `r > 0` of the scaled metric `μ d` (for `μ > 0`, Atteson's
theorem gives `r = μ m / 2`, `m` the shortest internal edge length), then almost surely, for all
long enough alignments, every complete run of neighbor joining on the JC-corrected empirical
distances returns exactly the splits of the internal edges of the tree. -/
theorem ae_eventually_njRun_splits_jcHat {X : Type*} [DecidableEq X] [Fintype X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {w : Sym2 V → ℝ} {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    {μ r : ℝ} (hr : 0 < r) (hNJ : NJRecoversWithin G ι (fun x y => μ * d x y) r)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (site : ℕ → Ω → X → Fin 4) (hmeas : ∀ i, Measurable (site i))
    (hident : ∀ i, IdentDistrib (site i) (site 0) P P)
    (hindep : Pairwise fun i j => IndepFun (site i) (site j) P)
    (hpair : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → ∀ i j,
      P.real {ω | site 0 ω x = i ∧ site 0 ω y = j} = jcPath μ (p.edges.map w) i j / 4) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ S Dc C, NJRun (jcHat (fun i => site i ω) n) S Dc C →
      S.card ≤ 3 → ∀ A : Finset X,
        ((A ∈ C ∨ univ \ A ∈ C) ↔
          ∃ a b, G.Adj a b ∧ a ∉ Set.range ι ∧ b ∉ Set.range ι ∧
            ∀ x, x ∈ A ↔ (G.deleteEdges {s(a, b)}).Reachable (ι x) a) := by
  classical
  have hdiff : ∀ x y, P.real {ω | site 0 ω x ≠ site 0 ω y} = pDiff μ (d x y) 0 := by
    intro x y
    obtain ⟨p, hp⟩ := (hT.1.connected.preconnected (ι x) (ι y)).exists_isPath
    have hg : Measurable fun ω => (site 0 ω x, site 0 ω y) :=
      ((measurable_pi_apply x).comp (hmeas 0)).prodMk ((measurable_pi_apply y).comp (hmeas 0))
    have hsum := sum_measureReal_preimage_singleton (μ := P)
      (univ.filter fun q : Fin 4 × Fin 4 => q.1 ≠ q.2)
      (fun q _ => hg (measurableSet_singleton q))
    have hset : (fun ω => (site 0 ω x, site 0 ω y)) ⁻¹'
        ↑(univ.filter fun q : Fin 4 × Fin 4 => q.1 ≠ q.2) = {ω | site 0 ω x ≠ site 0 ω y} := by
      ext ω
      simp
    have hfib : ∀ q : Fin 4 × Fin 4, (fun ω => (site 0 ω x, site 0 ω y)) ⁻¹' {q} =
        {ω | site 0 ω x = q.1 ∧ site 0 ω y = q.2} := by
      intro q
      ext ω
      simp [Prod.ext_iff]
    rw [hset] at hsum
    rw [← hsum]
    simp only [hfib, hpair x y p hp, jcPath_eq, ← hd x y p hp, Matrix.of_apply]
    rw [Finset.sum_filter, Fintype.sum_prod_type, pDiff_eq]
    simp [Fin.sum_univ_four, jcProb]
    ring
  filter_upwards [ae_tendsto_pHat site hmeas hident hindep] with ω hω
  have hjc : ∀ x y, Tendsto (fun n => jcHat (fun i => site i ω) n x y) atTop
      (𝓝 (μ * d x y)) := by
    intro x y
    have h1 := hω x y
    rw [hdiff] at h1
    have hpos : 1 - 4 / 3 * pDiff μ (d x y) 0 ≠ 0 := by
      have := pDiff_lt_three_quarters μ (d x y) 0
      linarith
    rw [← jcDistance_pDiff μ (d x y) 0]
    exact ((tendsto_const_nhds.sub (h1.const_mul (4 / 3))).log hpos).const_mul (-(3 / 4))
  have hev : ∀ᶠ n in atTop, ∀ x y, |jcHat (fun i => site i ω) n x y - μ * d x y| < r := by
    rw [eventually_all]
    intro x
    rw [eventually_all]
    intro y
    filter_upwards [(hjc x y).eventually (Metric.ball_mem_nhds _ hr)] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [hev] with n hn
  intro S Dc C hrun hS A
  refine hNJ _ (fun x y => ?_) (fun x => ?_) (fun x y _ => hn x y) S Dc C hrun hS A
  · unfold jcHat pHat
    rw [Finset.sum_congr rfl fun i _ => if_congr eq_comm rfl rfl]
  · change jcDistance (pHat _ _ x x) = 0
    simp [pHat, jcDistance]

/-- **Statistical consistency of neighbor joining under Jukes–Cantor** (Saitou & Nei 1987;
Atteson 1999), without a robustness hypothesis. Let `(G, ι)` be a binary phylogenetic `X`-tree
with path-length metric `d` for positive edge lengths `w`, whose internal edges have length at
least `m > 0`, and let the sites be pairwise independent and identically distributed, with the
two-leaf marginals of the JC model with rate `μ > 0` and uniform root. Then almost surely, for
all long enough alignments, every complete run of neighbor joining on the JC-corrected
empirical distances returns exactly the splits of the internal edges of the tree. -/
theorem ae_eventually_njRun_splits_jcHat_of_le {X : Type*} [DecidableEq X] [Fintype X]
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {w : Sym2 V → ℝ} (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    {μ m : ℝ} (hμ : 0 < μ) (hm0 : 0 < m)
    (hm : ∀ a b, G.Adj a b → a ∉ Set.range ι → b ∉ Set.range ι → m ≤ w s(a, b))
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (site : ℕ → Ω → X → Fin 4) (hmeas : ∀ i, Measurable (site i))
    (hident : ∀ i, IdentDistrib (site i) (site 0) P P)
    (hindep : Pairwise fun i j => IndepFun (site i) (site j) P)
    (hpair : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → ∀ i j,
      P.real {ω | site 0 ω x = i ∧ site 0 ω y = j} = jcPath μ (p.edges.map w) i j / 4) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ S Dc C, NJRun (jcHat (fun i => site i ω) n) S Dc C →
      S.card ≤ 3 → ∀ A : Finset X,
        ((A ∈ C ∨ univ \ A ∈ C) ↔
          ∃ a b, G.Adj a b ∧ a ∉ Set.range ι ∧ b ∉ Set.range ι ∧
            ∀ x, x ∈ A ↔ (G.deleteEdges {s(a, b)}).Reachable (ι x) a) :=
  ae_eventually_njRun_splits_jcHat hT hd (by positivity) (njRecoversWithin_of_le hT hw hd hμ hm)
    site hmeas hident hindep hpair

end Cslib.Bioinformatics.Phylogenetics.FelsensteinZone
