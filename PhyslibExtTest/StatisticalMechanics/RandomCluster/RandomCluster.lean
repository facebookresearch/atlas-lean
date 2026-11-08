/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.RandomCluster

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.RandomCluster`

On the one-edge graph `⊤ : SimpleGraph (Fin 2)` and the edgeless graph `⊥`:
* `openSub` keeps exactly the open edges: with every coordinate open it is `⊤`, with every
  coordinate closed it is `⊥`;
* `numClusters` counts `1` cluster when the edge is open and `2` when it is closed, and
  `card V` clusters on an edgeless graph;
* `edgeProduct` is `p` (open edge), `1 - p` (closed edge) and `1` on an edgeless graph;
* `fkWeight` and `fkZ` are evaluated: `fkWeight ⊤ p q 1 = p q`, `fkWeight ⊤ p q 0 = (1 - p) q²`,
  and `fkZ ⊥ p q = 8 q²` on `Fin 2` (three free coordinates of `Sym2 (Fin 2)`);
* `fkProb`, `fkPMF` are positive and normalized at `p = 1/2`, `q = 2`, and `fkWeight_one`
  reduces `q = 1` to the Bernoulli product.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.RandomCluster

open _root_.StatMech _root_.StatMech.FK

-- The test namespace repeats the module name `RandomCluster`, as the test-file convention requires.
set_option linter.dupNamespace false

/-- Equal graphs have equally many connected components (the `Fintype` instances may differ). -/
theorem card_connectedComponent_congr {V : Type*} {H H' : SimpleGraph V}
    [Fintype H.ConnectedComponent] [Fintype H'.ConnectedComponent] (h : H = H') :
    Fintype.card H.ConnectedComponent = Fintype.card H'.ConnectedComponent := by
  subst h
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]

/-- The product over the (empty) edge set of `⊥` is `1`. -/
theorem prod_edgeFinset_bot {V : Type*} {_ : Fintype (⊥ : SimpleGraph V).edgeSet} (f : Sym2 V → ℝ) :
    ∏ e ∈ (⊥ : SimpleGraph V).edgeFinset, f e = 1 :=
  Finset.prod_eq_one fun e he => by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_bot] at he
    exact absurd he (Set.notMem_empty e)

/-- The configuration with every coordinate open. -/
def allOpen {V : Type*} : ConfigSpace (Sym2 V) := fun _ => true

/-- The configuration with every coordinate closed. -/
def allClosed {V : Type*} : ConfigSpace (Sym2 V) := fun _ => false

/-- On an edgeless graph every vertex is its own cluster. -/
theorem numClusters_bot {V : Type*} [Fintype V] [DecidableEq V] (ω : ConfigSpace (Sym2 V)) :
    numClusters (⊥ : SimpleGraph V) ω = Fintype.card V := by
  have hsub : openSub (⊥ : SimpleGraph V) ω = ⊥ := le_bot_iff.mp (openSub_le _ ω)
  unfold numClusters
  refine Fintype.card_congr ?_
  rw [hsub]
  refine (Equiv.ofBijective (SimpleGraph.connectedComponentMk (⊥ : SimpleGraph V))
    ⟨fun u v h => ?_, fun c => ?_⟩).symm
  · exact SimpleGraph.reachable_bot.mp (SimpleGraph.ConnectedComponent.eq.mp h)
  · induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact ⟨v, rfl⟩

-- With all coordinates open, the open subgraph of `⊤` is `⊤`.
example : openSub (⊤ : SimpleGraph (Fin 2)) allOpen = ⊤ := by
  ext x y
  simp [allOpen]

-- With all coordinates closed, the open subgraph is empty.
example : openSub (⊤ : SimpleGraph (Fin 2)) allClosed = ⊥ := by
  ext x y
  simp [allClosed]

/-- One open edge joins the two vertices of `Fin 2` into a single cluster. -/
theorem numClusters_top_allOpen : numClusters (⊤ : SimpleGraph (Fin 2)) allOpen = 1 := by
  have hsub : openSub (⊤ : SimpleGraph (Fin 2)) allOpen = ⊤ := by
    ext x y; simp [allOpen]
  unfold numClusters
  rw [Fintype.card_eq_one_iff]
  refine ⟨SimpleGraph.connectedComponentMk _ 0, fun c => ?_⟩
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    refine SimpleGraph.ConnectedComponent.eq.mpr ?_
    rw [hsub]
    exact SimpleGraph.connected_top.preconnected v 0

-- With the edge closed there are two clusters.
example : numClusters (⊤ : SimpleGraph (Fin 2)) allClosed = 2 := by
  have hsub : openSub (⊤ : SimpleGraph (Fin 2)) allClosed = openSub ⊥ allClosed := by
    ext x y; simp [allClosed]
  rw [numClusters, card_connectedComponent_congr hsub, ← numClusters, numClusters_bot,
    Fintype.card_fin]

/-- The edge product of the open edge of `⊤` on `Fin 2` is `p`. -/
theorem edgeProduct_top_allOpen (p : ℝ) : edgeProduct (⊤ : SimpleGraph (Fin 2)) p allOpen = p := by
  simp only [edgeProduct, allOpen, ↓reduceIte, Finset.prod_const,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  norm_num

/-- The edge product of the closed edge is `1 - p`. -/
theorem edgeProduct_top_allClosed (p : ℝ) :
    edgeProduct (⊤ : SimpleGraph (Fin 2)) p allClosed = 1 - p := by
  simp only [edgeProduct, allClosed, Bool.false_eq_true, ↓reduceIte, Finset.prod_const,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  norm_num

-- On an edgeless graph the edge product is the empty product.
example {V : Type*} [Fintype V] (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    edgeProduct (⊥ : SimpleGraph V) p ω = 1 :=
  prod_edgeFinset_bot _

-- The FK weight of the open configuration on `Fin 2` is `p q`.
example (p q : ℝ) : fkWeight (⊤ : SimpleGraph (Fin 2)) p q allOpen = p * q := by
  rw [fkWeight, edgeProduct_top_allOpen, numClusters_top_allOpen, pow_one]

-- The FK weight of the closed configuration on `Fin 2` is `(1 - p) q²`.
example (p q : ℝ) : fkWeight (⊤ : SimpleGraph (Fin 2)) p q allClosed = (1 - p) * q ^ 2 := by
  have hk : numClusters (⊤ : SimpleGraph (Fin 2)) allClosed = 2 := by
    have hsub : openSub (⊤ : SimpleGraph (Fin 2)) allClosed = openSub ⊥ allClosed := by
      ext x y; simp [allClosed]
    rw [numClusters, card_connectedComponent_congr hsub, ← numClusters, numClusters_bot,
      Fintype.card_fin]
  rw [fkWeight, edgeProduct_top_allClosed, hk]

-- The partition function of the edgeless graph on `Fin 2`: `2³` configurations of
-- `Sym2 (Fin 2)`, each of weight `q²`.
example (p q : ℝ) : fkZ (⊥ : SimpleGraph (Fin 2)) p q = 8 * q ^ 2 := by
  have hw : ∀ ω, fkWeight (⊥ : SimpleGraph (Fin 2)) p q ω = q ^ 2 := fun ω => by
    rw [fkWeight, edgeProduct, prod_edgeFinset_bot, numClusters_bot, Fintype.card_fin, one_mul]
  simp only [fkZ, hw, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    nsmul_eq_mul, Sym2.card, Fintype.card_fin]
  norm_num

-- `fkProb` at `p = 1/2`, `q = 2` is a positive probability vector.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    0 < fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 ω :=
  fkProb_pos _ (by norm_num) (by norm_num) (by norm_num) ω

-- `fkProb` sums to one.
example : ∑ ω, fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 ω = 1 :=
  fkProb_sum_eq_one _ (by norm_num) (by norm_num) (by norm_num)

-- `fkPMF` puts mass `fkProb` on each configuration.
example :
    fkPMF (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
        (by norm_num) allOpen
      = ENNReal.ofReal (fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 allOpen) := by
  simp

-- At `q = 1` the FK weight is the Bernoulli product weight.
example (p : ℝ) : fkWeight (⊤ : SimpleGraph (Fin 2)) p 1 allClosed = 1 - p := by
  rw [fkWeight_one, edgeProduct_top_allClosed]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.RandomCluster
