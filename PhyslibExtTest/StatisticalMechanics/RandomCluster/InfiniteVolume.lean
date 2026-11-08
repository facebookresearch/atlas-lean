/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolume

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolume`

* The wired measure on `⊤ : SimpleGraph (Fin 2)` with both vertices on the boundary: the wired
  graph is connected, so `numClustersWired = 1` and `wiredFkWeight = edgeProduct · q`; the wired
  probabilities are nonnegative and sum to one at `p = 1/2`, `q = 2`.
* Boxes: the origin lies in every box `Λ_n`; `Λ_0` is the single site `0`, so `boxGraph d 0` has
  no edges. Hence the hypothesis `∀ n, 0 < (boxGraph d n).edgeFinset.card` used by several
  RandomCluster lemmas is false (it is refuted here for every `d`).
* `extendEdge` declares every edge outside the box closed.
* `freeInfiniteVolume`, `wiredInfiniteVolume` at `d = 2`, `p = 1/2`, `q = 2`: both are
  probability measures and subsequential weak limits of the box measures
  (`freeInfiniteVolume_isLimit`, `wiredInfiniteVolume_isLimit`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.InfiniteVolume

open MeasureTheory _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

/-- With both vertices of `Fin 2` on the boundary, the wired graph has one cluster, whatever the
configuration. -/
theorem numClustersWired_top_all (ω : ConfigSpace (Sym2 (Fin 2))) :
    numClustersWired (⊤ : SimpleGraph (Fin 2)) (fun _ => True) ω = 1 := by
  rw [numClustersWired, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun c c' => ?_⟩, ⟨SimpleGraph.connectedComponentMk _ 0⟩⟩
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h u =>
    induction c' using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      refine SimpleGraph.ConnectedComponent.eq.mpr ?_
      by_cases huv : u = v
      · rw [huv]
      · exact (wiredGraph_adj_of_bdry _ _ huv trivial trivial).reachable

-- The wired weight on `Fin 2` with both vertices wired is `edgeProduct · q`.
example (p q : ℝ) (ω : ConfigSpace (Sym2 (Fin 2))) :
    wiredFkWeight (⊤ : SimpleGraph (Fin 2)) (fun _ => True) p q ω
      = edgeProduct (⊤ : SimpleGraph (Fin 2)) p ω * q := by
  rw [wiredFkWeight, numClustersWired_top_all, pow_one]

-- The wired probabilities at `p = 1/2`, `q = 2` are nonnegative and sum to one.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    0 ≤ wiredFkProb (⊤ : SimpleGraph (Fin 2)) (fun _ => True) (1 / 2) 2 ω :=
  wiredFkProb_nonneg _ _ (by norm_num) (by norm_num) (by norm_num) ω

-- The wired probabilities are normalized.
example : ∑ ω, wiredFkProb (⊤ : SimpleGraph (Fin 2)) (fun _ => True) (1 / 2) 2 ω = 1 :=
  wiredFkProb_sum_eq_one _ _ (by norm_num) (by norm_num) (by norm_num)

-- The origin lies in every box.
example (d n : ℕ) : (0 : Site d) ∈ box d n := by simp

/-- The box `Λ_0` is the single site `0`. -/
theorem boxVerts_zero_subsingleton (d : ℕ) : Subsingleton (boxVerts d 0) := by
  refine ⟨fun x y => Subtype.ext (funext fun i => ?_)⟩
  have hx := x.2 i
  have hy := y.2 i
  simp only [nonpos_iff_eq_zero, Int.natAbs_eq_zero] at hx hy
  rw [hx, hy]

/-- `boxGraph d 0` has no edges. -/
theorem boxGraph_zero_edgeFinset_card (d : ℕ) : (boxGraph d 0).edgeFinset.card = 0 := by
  have := boxVerts_zero_subsingleton d
  rw [Finset.card_eq_zero, SimpleGraph.edgeFinset_eq_empty]
  ext x y
  simp only [SimpleGraph.bot_adj, iff_false]
  rw [Subsingleton.elim x y]
  exact (boxGraph d 0).loopless.irrefl y

-- The hypothesis `∀ n, 0 < (boxGraph d n).edgeFinset.card` is false for every `d`, so lemmas
-- assuming it are vacuous.
example (d : ℕ) : ¬ ∀ n, 0 < (boxGraph d n).edgeFinset.card := fun h => by
  have := h 0
  rw [boxGraph_zero_edgeFinset_card] at this
  exact lt_irrefl 0 this

-- `extendEdge` declares edges outside the box closed.
example (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) (e : Sym2 (Site d))
    (he : e ∉ Set.range (edgeIncl d n)) : extendEdge d n ω e = false := by
  simp [extendEdge, he]

-- `extendEdge` copies the box configuration on box edges.
example (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) (e : Sym2 (boxVerts d n)) :
    extendEdge d n ω (edgeIncl d n e) = ω e := by
  have hr : edgeIncl d n e ∈ Set.range (edgeIncl d n) := ⟨e, rfl⟩
  rw [extendEdge, dite_eq_left_of_eq_true (eq_true hr)]
  exact congrArg ω (edgeIncl_injective d n hr.choose_spec)

-- The free infinite-volume measure at `d = 2`, `p = 1/2`, `q = 2` is a probability measure.
example : (freeInfiniteVolume 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)
    : Measure (ConfigSpace (Sym2 (Site 2)))) Set.univ = 1 := measure_univ

-- It is the weak limit of the free box measures along a subsequence.
example : ∃ φ : ℕ → ℕ, StrictMono φ ∧
    WeakConvergesTo
      (fun n => freeFiniteMeasure 2 (φ n) (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
        (by norm_num))
      (freeInfiniteVolume 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)) :=
  freeInfiniteVolume_isLimit 2 _ _ _

-- The wired infinite-volume measure is the weak limit of the wired box measures along a
-- subsequence.
example : ∃ φ : ℕ → ℕ, StrictMono φ ∧
    WeakConvergesTo
      (fun n => wiredFiniteMeasure 2 (φ n) (p := 1 / 2) (q := 2) (by norm_num) (by norm_num)
        (by norm_num))
      (wiredInfiniteVolume 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)) :=
  wiredInfiniteVolume_isLimit 2 _ _ _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.InfiniteVolume
