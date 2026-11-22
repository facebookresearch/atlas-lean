/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.EdwardsSokal
public import PhyslibExt.StatisticalMechanics.RandomCluster.Tilt

/-!
# Compatible colorings in the Edwards–Sokal coupling

The joint Edwards–Sokal probability of a coloring and a bond configuration vanishes unless the
coloring is constant on open clusters, and otherwise equals `p^o (1-p)^c / Z_FK`.

## i. Overview

A `q`-coloring `σ` is compatible with a bond configuration `ω` if every open edge joins vertices
of the same color, equivalently if `σ` is constant on the open clusters. Compatible colorings are
exactly the colorings of the clusters, so there are `q^{k(ω)}` of them, where `k(ω)` is the number
of clusters; every edge with differently colored endpoints is closed. The Edwards–Sokal weight of
a compatible pair is `p^{o(ω)} (1-p)^{c(ω)}`, with `o` and `c` the numbers of open and closed
edges, and dividing by `Z_ES = Z_FK` gives the joint probability.

## ii. Key results

- `Compatible` : `σ` is constant along open edges of `ω`.
- `card_compatible` : there are `q^{k(ω)}` compatible colorings.
- `esJointProb` : the joint Edwards–Sokal probability of `(σ, ω)`.
- `esJointProb_eq` : it is `p^o (1-p)^c / Z_FK` for compatible pairs and `0` otherwise.

## iii. Table of contents

- A. Compatible colorings
- B. Colorings of the open clusters
- C. The joint Edwards–Sokal probability

## iv. References

- C. M. Fortuin and P. W. Kasteleyn, *On the random-cluster model I. Introduction and relation to
  other models*, Physica 57 (1972) 536–564.
- R. G. Edwards and A. D. Sokal, *Generalization of the Fortuin–Kasteleyn–Swendsen–Wang
  representation and Monte Carlo algorithm*, Phys. Rev. D 38 (1988) 2009–2012.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 1.4.
-/

@[expose] public section

open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Compatible colorings -/

/-- A coloring `σ` is compatible with the bond configuration `ω` if every open edge of `G` joins
vertices of the same color. See also `FK.ConstOnOpen` (`compatible_iff_constOnOpen`). -/
def Compatible {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : Prop :=
  ∀ x y, G.Adj x y → ω s(x, y) = true → σ x = σ y

/-- Compatibility of a coloring with a bond configuration is decidable. -/
instance instDecidableCompatible {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    Decidable (Compatible G σ ω) := by
  unfold Compatible; infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma compatible_iff_constOnOpen {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    Compatible G σ ω ↔ ConstOnOpen G ω σ :=
  ⟨fun h x y hadj => h x y hadj.1 hadj.2, fun h x y h1 h2 => h x y ⟨h1, h2⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma compatible_constant_on_cluster {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : Compatible G σ ω) {x y : V} (r : (openSub G ω).Reachable x y) : σ x = σ y :=
  constOnOpen_reachable G ω σ ((compatible_iff_constOnOpen G σ ω).1 h) r

/-- Whether an edge is monochromatic under the coloring `σ`. -/
def monoBool {q : ℕ} (σ : V → Fin q) : Sym2 V → Bool :=
  Sym2.lift ⟨fun x y => decide (σ x = σ y), by
    intro a b
    simp only [decide_eq_decide]
    exact ⟨Eq.symm, Eq.symm⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
lemma monoBool_mk {q : ℕ} (σ : V → Fin q) (x y : V) :
    monoBool σ s(x, y) = decide (σ x = σ y) := by
  unfold monoBool; rw [Sym2.lift_mk]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma monoBool_iff {q : ℕ} (σ : V → Fin q) (x y : V) :
    monoBool σ s(x, y) = true ↔ σ x = σ y := by
  rw [monoBool_mk, decide_eq_true_eq]

/-- The edges of `G` whose endpoints have different colors. -/
def disagreeEdges {q : ℕ} (σ : V → Fin q) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ¬ monoBool σ e)

omit [DecidableEq V] in
lemma mem_disagreeEdges {q : ℕ} (σ : V → Fin q) (x y : V) :
    s(x, y) ∈ disagreeEdges G σ ↔ G.Adj x y ∧ σ x ≠ σ y := by
  unfold disagreeEdges
  rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Bool.not_eq_true, ← Bool.not_eq_true, monoBool_iff]

omit [DecidableEq V] in
lemma compatible_closed_on_disagree {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : Compatible G σ ω) {e : Sym2 V} (he : e ∈ disagreeEdges G σ) : ω e = false := by
  induction e with
  | _ x y =>
    rw [mem_disagreeEdges] at he
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    exact he.2 (h x y he.1 hopen)

/-! ## B. Colorings of the open clusters -/

/-- The coloring of the vertices obtained from a coloring `τ` of the open clusters of `ω`. -/
def coloring {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) : V → Fin q :=
  fun v => τ ((openSub G ω).connectedComponentMk v)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
lemma coloring_apply {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) (x : V) :
    coloring G ω τ x = τ ((openSub G ω).connectedComponentMk x) := rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma coloring_compatible {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) :
    Compatible G (coloring G ω τ) ω := by
  rw [compatible_iff_constOnOpen]
  intro x y hxy
  simp only [coloring_apply]
  congr 1
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma coloring_eq_constOnOpenEquiv {q : ℕ} (ω : ConfigSpace (Sym2 V))
    (τ : (openSub G ω).ConnectedComponent → Fin q) :
    coloring G ω τ = (constOnOpenEquiv G ω τ).1 := rfl

lemma card_compatible {q : ℕ} (ω : ConfigSpace (Sym2 V)) :
    Nat.card {σ : V → Fin q // Compatible G σ ω} = q ^ numClusters G ω := by
  have hcongr : Nat.card {σ : V → Fin q // Compatible G σ ω}
      = Nat.card {σ : V → Fin q // ConstOnOpen G ω σ} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun σ => compatible_iff_constOnOpen G σ ω)
  rw [hcongr, card_constOnOpen]

/-! ## C. The joint Edwards–Sokal probability -/

omit [DecidableEq V] in
lemma edgeProduct_eq_pow (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p ω = p ^ openCount G ω * (1 - p) ^ closedCount G ω := by
  unfold edgeProduct openCount closedCount
  rw [← Finset.prod_filter_mul_prod_filter_not G.edgeFinset (fun e => ω e = true)]
  congr 1
  · rw [Finset.prod_congr rfl (fun e he => ite_eq_left (Finset.mem_filter.1 he).2),
      Finset.prod_const]
  · have hfilt : G.edgeFinset.filter (fun e => ¬ ω e = true)
        = G.edgeFinset.filter (fun e => ω e = false) := by
      apply Finset.filter_congr; intro e _; simp [Bool.not_eq_true]
    rw [Finset.prod_congr rfl (fun e he => ite_eq_right (Finset.mem_filter.1 he).2),
      Finset.prod_const, hfilt]

omit [DecidableEq V] in
lemma esWeight_eq_of_compatible {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esWeight G p σ ω = if Compatible G σ ω then edgeProduct G p ω else 0 := by
  rw [esWeight_factor, monoProd_eq_indicator]
  simp only [compatible_iff_constOnOpen]
  split <;> ring

/-- The joint Edwards–Sokal probability of the coloring `σ` and the bond configuration `ω`. -/
noncomputable def esJointProb (q : ℕ) (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  esWeight G p σ ω / esZ G q p

lemma esJointProb_incompatible {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : ¬ Compatible G σ ω) : esJointProb G q p σ ω = 0 := by
  unfold esJointProb
  rw [esWeight_eq_of_compatible, ite_eq_right h, zero_div]

lemma esJointProb_compatible {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V))
    (h : Compatible G σ ω) :
    esJointProb G q p σ ω
      = (p ^ openCount G ω * (1 - p) ^ closedCount G ω) / fkZ G p (q : ℝ) := by
  unfold esJointProb
  rw [esWeight_eq_of_compatible, ite_eq_left h, esZ_eq_fkZ, edgeProduct_eq_pow]

lemma esJointProb_eq {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esJointProb G q p σ ω
      = if Compatible G σ ω then
          (p ^ openCount G ω * (1 - p) ^ closedCount G ω) / fkZ G p (q : ℝ)
        else 0 := by
  by_cases h : Compatible G σ ω
  · rw [ite_eq_left h, esJointProb_compatible G p σ ω h]
  · rw [ite_eq_right h, esJointProb_incompatible G p σ ω h]

end IsingFK

end StatMech
