/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Exploration
public import MathlibExt.Probability.Percolation.SubcriticalDecay
public import MathlibExt.Probability.Percolation.Theta

/-!
# Last-exit decomposition of a crossing

A walk that starts in `S` and ends outside `S` has a last vertex in `S`; after it the walk stays
outside `S`. Applied to an open path from the origin to distance `n` with `S` the explored cluster,
this decomposes the crossing event: the cluster `C` of the origin inside `S`, an open boundary edge
`(x, y)` with `x ∈ C`, `y ∉ C`, and an open crossing from `y` to distance `n` avoiding `C`.

## Main definitions

* `StatMech.Percolation.offClusterCrossing`: `y` is joined to distance `n` by an open path avoiding
  `C`.
* `StatMech.Percolation.boundaryOpen`: `(x, y)` is an open edge with `x ∈ C`, `y ∉ C`.

## Main results

* `StatMech.Percolation.exists_lastExit`: the last exit of a walk from a set.
* `StatMech.Percolation.crossingEvent_lastExit_subset`: the decomposition of the crossing event.

## References

* H. Duminil-Copin, V. Tassion, *A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model*, Comm. Math. Phys. 343 (2016), 725–745.
-/

@[expose] public section

open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal

namespace StatMech

namespace Percolation

open StatMech.Lattice

section AbstractWalk

variable {V : Type*} {G : SimpleGraph V}

theorem lastIndexMem {a b : V} (p : G.Walk a b) (S : Set V)
    (ha : a ∈ S) (hb : b ∉ S) :
    ∃ m, m < p.length ∧ p.getVert m ∈ S ∧
      ∀ n, m < n → n ≤ p.length → p.getVert n ∉ S := by
  classical
  set T : Finset ℕ := (Finset.range (p.length + 1)).filter (fun n => p.getVert n ∈ S) with hT
  have h0 : 0 ∈ T := by
    rw [hT]; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [Walk.getVert_zero]; exact ha⟩
  have hTne : T.Nonempty := ⟨0, h0⟩
  set m := T.max' hTne with hm
  have hmT : m ∈ T := T.max'_mem hTne
  rw [hT] at hmT
  simp only [Finset.mem_filter, Finset.mem_range] at hmT
  obtain ⟨hmle, hmS⟩ := hmT
  have hmlt : m < p.length := by
    rcases Nat.lt_or_ge m p.length with h | h
    · exact h
    · exact absurd (p.getVert_of_length_le (by omega) ▸ hmS) hb
  refine ⟨m, hmlt, hmS, ?_⟩
  intro n hmn hnle hnS
  have hnT : n ∈ T := by
    rw [hT]; simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hnS⟩
  have := T.le_max' n hnT
  rw [← hm] at this
  omega

theorem drop_avoids_of_after {a b : V} (p : G.Walk a b) (S : Set V) {m : ℕ}
    (hm : m < p.length)
    (hafter : ∀ n, m < n → n ≤ p.length → p.getVert n ∉ S) :
    ∀ z ∈ (p.drop (m + 1)).support, z ∉ S := by
  intro z hz hzS
  rw [Walk.mem_support_iff_exists_getVert] at hz
  obtain ⟨k, hk, hkle⟩ := hz
  rw [Walk.drop_getVert] at hk
  rw [Walk.drop_length] at hkle
  exact hafter (m + 1 + k) (by omega) (by omega) (hk ▸ hzS)

theorem exists_lastExit {a b : V} (p : G.Walk a b) (S : Set V)
    (ha : a ∈ S) (hb : b ∉ S) :
    ∃ (x y : V) (_hx : x ∈ S) (hy : y ∉ S) (_hadj : G.Adj x y),
      Nonempty ((G.induce {v | v ∉ S}).Walk ⟨y, hy⟩ ⟨b, hb⟩) := by
  classical
  obtain ⟨m, hmlt, hmS, hafter⟩ := lastIndexMem p S ha hb
  have hyS : p.getVert (m + 1) ∉ S := hafter (m + 1) (by omega) (by omega)
  have hadj : G.Adj (p.getVert m) (p.getVert (m + 1)) := p.adj_getVert_succ hmlt
  have hqsupp : ∀ z ∈ (p.drop (m + 1)).support, z ∈ {v | v ∉ S} :=
    fun z hz => drop_avoids_of_after p S hmlt hafter z hz
  refine ⟨p.getVert m, p.getVert (m + 1), hmS, hyS, hadj,
    ⟨((p.drop (m + 1)).induce {v | v ∉ S} hqsupp).copy (by simp) rfl⟩⟩

end AbstractWalk

variable {d : ℕ}

theorem lattice_lastExit (ω : ConfigSpace (Sym2 (Site d))) (K : Set (Site d)) (o v : Site d)
    (ho : o ∈ K) (hv : v ∉ K) (hconn : Connected d ω o v) :
    ∃ (x y : Site d) (_hx : x ∈ K) (hy : y ∉ K), IsOpenEdge d ω x y ∧
      ConnectedWithin d ω {z | z ∉ K} ⟨y, hy⟩ ⟨v, hv⟩ := by
  classical
  obtain ⟨p⟩ := hconn
  obtain ⟨x, y, hx, hy, hadj, ⟨w⟩⟩ := exists_lastExit p K ho hv
  exact ⟨x, y, hx, hy, hadj, ⟨w⟩⟩

/-- `y ∉ C` is joined by an open path avoiding `C` to a site outside `Λ_{n-1}`. -/
def offClusterCrossing (d : ℕ) (C : Set (Site d)) (y : Site d) (n : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ v, v ∉ box d (n - 1) ∧ ∃ (hy : y ∉ C) (hv : v ∉ C),
    ConnectedWithin d ω {z | z ∉ C} ⟨y, hy⟩ ⟨v, hv⟩

/-- The edge `{x, y}` is open, with `x ∈ C` and `y ∉ C`. -/
def boundaryOpen (d : ℕ) (C : Set (Site d)) (x y : Site d)
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  x ∈ C ∧ y ∉ C ∧ IsOpenEdge d ω x y

theorem boundaryOpen_dependsOn (C : Set (Site d)) (x y : Site d) :
    DependsOn ({ω | boundaryOpen d C x y ω}.indicator (fun _ => (1 : ℝ)))
      ({s(x, y)} : Set (Sym2 (Site d))) := by
  intro ω ω' h
  have hedge : ω s(x, y) = ω' s(x, y) := h s(x, y) rfl
  have hiff : (ω ∈ {ω | boundaryOpen d C x y ω}) ↔ (ω' ∈ {ω | boundaryOpen d C x y ω}) := by
    simp only [Set.mem_ofPred_eq, boundaryOpen, IsOpenEdge, hedge]
  by_cases hmem : ω ∈ {ω | boundaryOpen d C x y ω}
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hiff.mpr hc))]

theorem crossingEvent_lastExit_subset (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (n : ℕ)
    (hSbox : (S : Set (Site d)) ⊆ box d (n - 1)) :
    crossingEvent d n ⊆
      ⋃ (C : Set (Site d)), ⋃ (x : Site d), ⋃ (y : Site d),
        (clusterEvent d (S : Set (Site d)) (origin d) C
          ∩ {ω | boundaryOpen d C x y ω}
          ∩ {ω | offClusterCrossing d C y n ω}) := by
  intro ω hω
  obtain ⟨v, hconn, hv⟩ := hω
  set C := clusterWithin d ω (S : Set (Site d)) (origin d) with hC
  have hoC : origin d ∈ C := ⟨hoS, hoS, connectedWithin_refl ω _ ⟨origin d, hoS⟩⟩
  have hCsub : C ⊆ (S : Set (Site d)) := fun z hz => hz.1
  have hvC : v ∉ C := fun hvc => hv (hSbox (hCsub hvc))
  obtain ⟨x, y, hx, hy, hopen, hwithin⟩ := lattice_lastExit ω C (origin d) v hoC hvC hconn
  simp only [Set.mem_iUnion]
  exact ⟨C, x, y, ⟨⟨rfl, ⟨hx, hy, hopen⟩⟩, ⟨v, hv, hy, hvC, hwithin⟩⟩⟩

end Percolation

end StatMech
