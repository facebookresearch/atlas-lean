/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusFacePotential
import Code.FrontierA.TriangularIsingTorusPhaseAssembly





open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Onsager

theorem triangularTorusEvenHomology_eq_zero_of_surfaceHomology
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hhom : surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) F = 0) :
    triangularTorusEvenHomology L F = 0 := by
  have heq := triangularTorus_surfaceSubgraphHomology_eq L F
  rw [hhom] at heq
  apply Prod.ext
  · simpa using congrFun (congrArg Prod.fst heq.symm) 0
  · simpa using congrFun (congrArg Prod.snd heq.symm) 0



theorem triangularTorus_dartEdge_mem_cycle_iff
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall (k : Fin p.darts.length) (a : Fin 6),
      (triangularTorusDartEquiv L
          ((triangularTorusCycleNativeDart L p k).1, a)).edge ∈
          p.edges.toFinset ↔
        ((triangularTorusCycleNativeDart L p k).1, a) =
            triangularTorusCycleNativeDart L p k ∨
          ((triangularTorusCycleNativeDart L p k).1, a) =
            triangularTorusDartReverse L
              (triangularTorusCycleNativeDart L p (k - 1)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k a
  let q : triangularTorusDart L :=
    ((triangularTorusCycleNativeDart L p k).1, a)
  let d : Fin p.darts.length → triangularTorusDart L :=
    triangularTorusCycleNativeDart L p
  rw [triangularTorusCycle_edges_toFinset_eq_image L p]
  constructor
  · rw [Finset.mem_image]
    rintro ⟨j, -, hedge⟩
    rcases (SimpleGraph.dart_edge_eq_iff
      (triangularTorusDartEquiv L q)
      (kwGraphCycleDartLoop p j)).mp hedge.symm with hsame | hreverse
    · left
      change q = d k
      have hnative : q = d j := by
        apply (triangularTorusDartEquiv L).injective
        calc
          triangularTorusDartEquiv L q = kwGraphCycleDartLoop p j := hsame
          _ = triangularTorusDartEquiv L (d j) := by
            symm
            exact triangularTorusCycleNativeDart_equiv L p j
      have hjk : j = k := by
        apply triangularTorusCycleNativeSite_injective L p hp
        change (d j).1 = (d k).1
        rw [← hnative]
      simpa [q, d, hjk] using hnative
    · right
      change q = triangularTorusDartReverse L (d (k - 1))
      have hnative : q = triangularTorusDartReverse L (d j) := by
        apply (triangularTorusDartEquiv L).injective
        rw [triangularTorusDartEquiv_reverse,
          triangularTorusCycleNativeDart_equiv]
        exact hreverse
      have hjk : j + 1 = k := by
        apply triangularTorusCycleNativeSite_injective L p hp
        change (d (j + 1)).1 = (d k).1
        rw [triangularTorusCycleNativeDart_fst L p (j + 1),
          triangularTorusCycleNativeDart_fst L p k]
        calc
          (kwGraphCycleDartLoop p (j + 1)).fst =
              (kwGraphCycleDartLoop p j).snd :=
            (kwGraphCycleDartLoop_valid p hp j).symm
          _ = (triangularTorusDartEquiv L q).fst := by
            exact congrArg
              (fun z : (triangularTorusGraph L).Dart ↦ z.fst) hreverse.symm
          _ = (kwGraphCycleDartLoop p k).fst := by
            change q.1 = (kwGraphCycleDartLoop p k).fst
            exact triangularTorusCycleNativeDart_fst L p k
      have hj : j = k - 1 := by
        calc
          j = (j + 1) - 1 := by abel
          _ = k - 1 := by rw [hjk]
      simpa [q, d, hj] using hnative
  · rintro (hsame | hreverse)
    · refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
      rw [← triangularTorusCycleNativeDart_equiv L p k]
      exact (congrArg
        (fun z : triangularTorusDart L ↦ (triangularTorusDartEquiv L z).edge)
        hsame).symm
    · refine Finset.mem_image.mpr ⟨k - 1, Finset.mem_univ _, ?_⟩
      rw [← triangularTorusCycleNativeDart_equiv L p (k - 1)]
      calc
        (triangularTorusDartEquiv L
            (triangularTorusCycleNativeDart L p (k - 1))).edge =
            (triangularTorusDartEquiv L
              (triangularTorusDartReverse L
                (triangularTorusCycleNativeDart L p (k - 1)))).edge := by
          rw [triangularTorusDartEquiv_reverse,
            SimpleGraph.Dart.edge_symm]
        _ = (triangularTorusDartEquiv L q).edge := by
          exact congrArg
            (fun z : triangularTorusDart L ↦
              (triangularTorusDartEquiv L z).edge) hreverse.symm

theorem triangularZeroHomology_boundaryCoeff_cast
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (d : triangularTorusDart L) :
    (triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) d : ZMod 2) =
      (ons_edgeBit F (triangularTorusDartEquiv L d).edge : ZMod 2) := by
  rcases d with ⟨⟨x, y⟩, a⟩
  fin_cases a <;>
    simp [triangularFaceBoundaryCoeff, Int.cast_neg, CharTwo.neg_eq,
      triangularZeroHomology_eastCoeff_cast L F hF hhom,
      triangularZeroHomology_northCoeff_cast L F hF hhom,
      triangularZeroHomology_diagonalCoeff_cast,
      triangularTorusEastEdge, triangularTorusNorthEdge,
      triangularTorusNortheastEdge, triangularTorusDartEquiv_apply,
      triangularTorusDartToGraphDart, triangularTorusDirectionStep,
      SimpleGraph.Dart.edge, Sym2.eq_swap]

theorem triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (d : triangularTorusDart L)
    (hnot : (triangularTorusDartEquiv L d).edge ∉ F) :
    triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) d = 0 := by
  have hcast :
      (triangularFaceBoundaryCoeff
          (triangularZeroHomologyLowerPotential L F)
          (triangularZeroHomologyUpperPotential L F) d : ZMod 2) = 0 := by
    rw [triangularZeroHomology_boundaryCoeff_cast L F hF hhom]
    rw [ons_edgeBit, if_neg hnot]
    rfl
  rcases d with ⟨⟨x, y⟩, a⟩
  fin_cases a
  · change -triangularFaceEastCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) (x - 1, y) = 0
    rw [neg_eq_zero]
    apply triangularFaceEastCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff, Int.cast_neg] using hcast
  · apply triangularFaceEastCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff] using hcast
  · change -triangularFaceNorthCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) (x, y - 1) = 0
    rw [neg_eq_zero]
    apply triangularFaceNorthCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff, Int.cast_neg] using hcast
  · apply triangularFaceNorthCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff] using hcast
  · change -triangularFaceDiagonalCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) (x - 1, y - 1) = 0
    rw [neg_eq_zero]
    apply triangularFaceDiagonalCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff, Int.cast_neg] using hcast
  · apply triangularFaceDiagonalCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff] using hcast

theorem triangularZeroHomology_boundaryCoeff_ne_zero_of_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (d : triangularTorusDart L)
    (hmem : (triangularTorusDartEquiv L d).edge ∈ F) :
    triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) d ≠ 0 := by
  intro hz
  have hcast := triangularZeroHomology_boundaryCoeff_cast L F hF hhom d
  rw [hz] at hcast
  rw [ons_edgeBit, if_pos hmem] at hcast
  exact zero_ne_one hcast

private theorem finSix_sum_eq_two
    (f : Fin 6 → Int) (a b : Fin 6) (hab : a ≠ b)
    (hzero : ∀ c, c ≠ a → c ≠ b → f c = 0) :
    (∑ c, f c) = f a + f b := by
  have hb : b ∈ (Finset.univ : Finset (Fin 6)).erase a := by
    simp [hab.symm]
  calc
    (∑ c, f c) = f a + ∑ c ∈ (Finset.univ : Finset (Fin 6)).erase a, f c := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
      abel
    _ = f a + (f b + ∑ c ∈
        ((Finset.univ : Finset (Fin 6)).erase a).erase b, f c) := by
      rw [← Finset.sum_erase_add _ _ hb]
      abel
    _ = f a + f b := by
      have hrest :
          (∑ c ∈ ((Finset.univ : Finset (Fin 6)).erase a).erase b,
            f c) = 0 := by
        apply Finset.sum_eq_zero
        intro c hc
        rw [Finset.mem_erase] at hc
        exact hzero c (Finset.mem_erase.mp hc.2).1 hc.1
      rw [hrest, add_zero]

theorem triangularZeroHomology_cycleBoundaryCoeff_eq_prev
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k : Fin p.darts.length,
      triangularFaceBoundaryCoeff
          (triangularZeroHomologyLowerPotential L p.edges.toFinset)
          (triangularZeroHomologyUpperPotential L p.edges.toFinset)
          (triangularTorusCycleNativeDart L p k) =
        triangularFaceBoundaryCoeff
          (triangularZeroHomologyLowerPotential L p.edges.toFinset)
          (triangularZeroHomologyUpperPotential L p.edges.toFinset)
          (triangularTorusCycleNativeDart L p (k - 1)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k
  let F := p.edges.toFinset
  let lower := triangularZeroHomologyLowerPotential L F
  let upper := triangularZeroHomologyUpperPotential L F
  let d : Fin p.darts.length → triangularTorusDart L :=
    triangularTorusCycleNativeDart L p
  let a : Fin 6 := (d k).2
  let b : Fin 6 := triangularTorusDirectionReverse (d (k - 1)).2
  have hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L) := by
    exact ons_cycle_edges_evenSubgraph (triangularTorusGraph L) p hp
  have hab : a ≠ b := by
    have hnb := triangularTorus_cycleDirection_nonbacktracking L p hp (k - 1)
    simpa [a, b, d, triangularTorusCycleNativeDart_snd] using hnb
  have hincoming : ((d k).1, b) =
      triangularTorusDartReverse L (d (k - 1)) := by
    apply Prod.ext
    · change (d k).1 =
        (d (k - 1)).1 - triangularTorusDirectionStep L (d (k - 1)).2
      have hs := triangularTorusCycleNativeSite_succ L p hp (k - 1)
      rw [show k - 1 + 1 = k by abel,
        triangularIntReduce_step] at hs
      simpa [d, sub_eq_add_neg] using hs
    · rfl
  let f : Fin 6 → Int := fun c =>
    triangularFaceBoundaryCoeff lower upper ((d k).1, c)
  have hzero : ∀ c, c ≠ a → c ≠ b → f c = 0 := by
    intro c hca hcb
    have hnot : (triangularTorusDartEquiv L ((d k).1, c)).edge ∉ F := by
      intro hmem
      have hor := (triangularTorus_dartEdge_mem_cycle_iff L p hp k c).mp hmem
      rcases hor with hout | hin
      · apply hca
        exact congrArg Prod.snd hout
      · apply hcb
        exact congrArg Prod.snd (hin.trans hincoming.symm)
    exact triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem
      L F hF hhom ((d k).1, c) hnot
  have hsum : (∑ c, f c) = f a + f b :=
    finSix_sum_eq_two f a b hab hzero
  have hdiv := triangularFaceBoundaryCoeff_divergence lower upper (d k).1
  change (∑ c, f c) = 0 at hdiv
  rw [hsum] at hdiv
  have hfa : f a = triangularFaceBoundaryCoeff lower upper (d k) := by
    rfl
  have hfb : f b =
      -triangularFaceBoundaryCoeff lower upper (d (k - 1)) := by
    change triangularFaceBoundaryCoeff lower upper ((d k).1, b) = _
    rw [show ((d k).1, b) = triangularTorusDartReverse L (d (k - 1))
      from hincoming]
    exact triangularFaceBoundaryCoeff_reverse lower upper (d (k - 1))
  rw [hfa, hfb] at hdiv
  change triangularFaceBoundaryCoeff lower upper (d k) =
    triangularFaceBoundaryCoeff lower upper (d (k - 1))
  omega

theorem triangularZeroHomology_cycleBoundaryCoeff_eq_root
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k : Fin p.darts.length,
      triangularFaceBoundaryCoeff
          (triangularZeroHomologyLowerPotential L p.edges.toFinset)
          (triangularZeroHomologyUpperPotential L p.edges.toFinset)
          (triangularTorusCycleNativeDart L p k) =
        triangularFaceBoundaryCoeff
          (triangularZeroHomologyLowerPotential L p.edges.toFinset)
          (triangularZeroHomologyUpperPotential L p.edges.toFinset)
          (triangularTorusCycleNativeDart L p 0) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  exact ons_fin_pred_invariant
    (fun k => triangularFaceBoundaryCoeff
      (triangularZeroHomologyLowerPotential L p.edges.toFinset)
      (triangularZeroHomologyUpperPotential L p.edges.toFinset)
      (triangularTorusCycleNativeDart L p k))
    (triangularZeroHomology_cycleBoundaryCoeff_eq_prev L p hp hhom)

theorem triangularZeroHomology_cycleBoundaryCoeff_root_ne_zero
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L p.edges.toFinset)
        (triangularZeroHomologyUpperPotential L p.edges.toFinset)
        (triangularTorusCycleNativeDart L p 0) ≠ 0 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hF : p.edges.toFinset ∈
      StatMech.Ising.evenSubgraphs (triangularTorusGraph L) :=
    ons_cycle_edges_evenSubgraph (triangularTorusGraph L) p hp
  have hedge :
      (triangularTorusDartEquiv L
        (triangularTorusCycleNativeDart L p 0)).edge ∈ p.edges.toFinset := by
    rw [triangularTorusCycle_edges_toFinset_eq_image L p,
      Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, by
      rw [triangularTorusCycleNativeDart_equiv]⟩
  exact triangularZeroHomology_boundaryCoeff_ne_zero_of_mem
    L p.edges.toFinset hF hhom _ hedge

def triangularTorusPositiveIndex : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

def triangularTorusPositiveSource {L : Nat}
    (d : triangularTorusDart L) : ZMod L × ZMod L :=
  match d.2.val with
  | 0 => (d.1.1 - 1, d.1.2)
  | 1 => d.1
  | 2 => (d.1.1, d.1.2 - 1)
  | 3 => d.1
  | 4 => (d.1.1 - 1, d.1.2 - 1)
  | _ => d.1

def triangularFacePositiveCoeff {L : Nat}
    (lower upper : (ZMod L × ZMod L) → ZMod 2)
    (a : Fin 3) (p : ZMod L × ZMod L) : Int :=
  match a.val with
  | 0 => triangularFaceEastCoeff lower upper p
  | 1 => triangularFaceNorthCoeff lower upper p
  | _ => triangularFaceDiagonalCoeff lower upper p

def triangularTorusPositiveRepresentation {L : Nat}
    (d : triangularTorusDart L) : Fin 3 × (ZMod L × ZMod L) :=
  (triangularTorusPositiveIndex d.2, triangularTorusPositiveSource d)

theorem triangularPositiveEdge_index_source
    (L : Nat) [Fact (2 < L)] (d : triangularTorusDart L) :
    triangularPositiveEdge L (triangularTorusPositiveIndex d.2)
        (triangularTorusPositiveSource d) =
      (triangularTorusDartEquiv L d).edge := by
  rcases d with ⟨⟨x, y⟩, a⟩
  fin_cases a <;>
    simp [triangularTorusPositiveIndex, triangularTorusPositiveSource,
      triangularPositiveEdge, triangularTorusPositiveDirection,
      triangularTorusDartEquiv_apply, triangularTorusDartToGraphDart,
      triangularTorusDirectionStep, SimpleGraph.Dart.edge, Sym2.eq_swap]

theorem triangularTorusCycle_positiveRepresentation_injective
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    Function.Injective (fun k : Fin p.darts.length =>
      triangularTorusPositiveRepresentation
        (triangularTorusCycleNativeDart L p k)) := by
  intro i j hij
  apply triangularTorusCycle_edge_injective L p hp
  change (kwGraphCycleDartLoop p i).edge =
    (kwGraphCycleDartLoop p j).edge
  rw [← triangularTorusCycleNativeDart_equiv L p i,
    ← triangularTorusCycleNativeDart_equiv L p j,
    ← triangularPositiveEdge_index_source L
      (triangularTorusCycleNativeDart L p i),
    ← triangularPositiveEdge_index_source L
      (triangularTorusCycleNativeDart L p j)]
  simpa [triangularTorusPositiveRepresentation] using congrArg
    (fun q : Fin 3 × (ZMod L × ZMod L) =>
      triangularPositiveEdge L q.1 q.2) hij

theorem triangularBoundaryCoeff_mul_step_fst
    {L : Nat} (lower upper : (ZMod L × ZMod L) → ZMod 2)
    (d : triangularTorusDart L) :
    triangularFaceBoundaryCoeff lower upper d * (triangularIntStep d.2).1 =
      triangularFacePositiveCoeff lower upper
          (triangularTorusPositiveIndex d.2)
          (triangularTorusPositiveSource d) *
        (triangularIntStep
          (triangularTorusPositiveDirection
            (triangularTorusPositiveIndex d.2))).1 := by
  rcases d with ⟨⟨x, y⟩, a⟩
  fin_cases a <;>
    simp [triangularFaceBoundaryCoeff, triangularFacePositiveCoeff,
      triangularTorusPositiveIndex, triangularTorusPositiveSource,
      triangularTorusPositiveDirection, triangularIntStep] <;> ring

theorem triangularBoundaryCoeff_mul_step_snd
    {L : Nat} (lower upper : (ZMod L × ZMod L) → ZMod 2)
    (d : triangularTorusDart L) :
    triangularFaceBoundaryCoeff lower upper d * (triangularIntStep d.2).2 =
      triangularFacePositiveCoeff lower upper
          (triangularTorusPositiveIndex d.2)
          (triangularTorusPositiveSource d) *
        (triangularIntStep
          (triangularTorusPositiveDirection
            (triangularTorusPositiveIndex d.2))).2 := by
  rcases d with ⟨⟨x, y⟩, a⟩
  fin_cases a <;>
    simp [triangularFaceBoundaryCoeff, triangularFacePositiveCoeff,
      triangularTorusPositiveIndex, triangularTorusPositiveSource,
      triangularTorusPositiveDirection, triangularIntStep] <;> ring

theorem triangularFacePositiveCoeff_full_fst_sum_eq_zero
    {L : Nat} [NeZero L]
    (lower upper : (ZMod L × ZMod L) → ZMod 2) :
    (∑ q : Fin 3 × (ZMod L × ZMod L),
      triangularFacePositiveCoeff lower upper q.1 q.2 *
        (triangularIntStep
          (triangularTorusPositiveDirection q.1)).1) = 0 := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  simp [triangularFacePositiveCoeff,
    triangularTorusPositiveDirection, triangularIntStep]
  rw [← Finset.sum_add_distrib, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro x _
  exact triangularFaceBoundary_horizontal_seam_sum lower upper x

theorem triangularFacePositiveCoeff_full_snd_sum_eq_zero
    {L : Nat} [NeZero L]
    (lower upper : (ZMod L × ZMod L) → ZMod 2) :
    (∑ q : Fin 3 × (ZMod L × ZMod L),
      triangularFacePositiveCoeff lower upper q.1 q.2 *
        (triangularIntStep
          (triangularTorusPositiveDirection q.1)).2) = 0 := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  simp [triangularFacePositiveCoeff,
    triangularTorusPositiveDirection, triangularIntStep]
  rw [← Finset.sum_add_distrib, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y _
  exact triangularFaceBoundary_vertical_seam_sum lower upper y

theorem triangularZeroHomology_cycleBoundaryCoeff_mul_step_fst_sum_eq_zero
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L p.edges.toFinset)
        (triangularZeroHomologyUpperPotential L p.edges.toFinset)
        (triangularTorusCycleNativeDart L p k) *
      (triangularIntStep
        (triangularTorusCycleNativeDart L p k).2).1) = 0 := by
  classical
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let F := p.edges.toFinset
  let lower := triangularZeroHomologyLowerPotential L F
  let upper := triangularZeroHomologyUpperPotential L F
  let d : Fin p.darts.length → triangularTorusDart L :=
    triangularTorusCycleNativeDart L p
  let rep : Fin p.darts.length → Fin 3 × (ZMod L × ZMod L) :=
    fun k => triangularTorusPositiveRepresentation (d k)
  let T := (Finset.univ : Finset (Fin 3 × (ZMod L × ZMod L))).filter
    (fun q => triangularPositiveEdge L q.1 q.2 ∈ F)
  let g : Fin 3 × (ZMod L × ZMod L) → Int := fun q =>
    triangularFacePositiveCoeff lower upper q.1 q.2 *
      (triangularIntStep (triangularTorusPositiveDirection q.1)).1
  have hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L) :=
    ons_cycle_edges_evenSubgraph (triangularTorusGraph L) p hp
  have hedge (k : Fin p.darts.length) :
      triangularPositiveEdge L (rep k).1 (rep k).2 =
        (kwGraphCycleDartLoop p k).edge := by
    rw [show rep k = triangularTorusPositiveRepresentation (d k) by rfl]
    rw [triangularTorusPositiveRepresentation,
      triangularPositiveEdge_index_source,
      triangularTorusCycleNativeDart_equiv]
  have hedgeMem (k : Fin p.darts.length) :
      (kwGraphCycleDartLoop p k).edge ∈ F := by
    rw [show F = p.edges.toFinset by rfl,
      triangularTorusCycle_edges_toFinset_eq_image L p,
      Finset.mem_image]
    exact ⟨k, Finset.mem_univ _, rfl⟩
  calc
    (∑ k, triangularFaceBoundaryCoeff lower upper (d k) *
        (triangularIntStep (d k).2).1) = ∑ q ∈ T, g q := by
      apply Finset.sum_bij (fun k _ => rep k)
      · intro k _
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [hedge k]; exact hedgeMem k⟩
      · intro i _ j _ hij
        exact triangularTorusCycle_positiveRepresentation_injective
          L p hp hij
      · intro q hq
        have hqF := (Finset.mem_filter.mp hq).2
        rw [show F = p.edges.toFinset by rfl,
          triangularTorusCycle_edges_toFinset_eq_image L p,
          Finset.mem_image] at hqF
        obtain ⟨k, hk, hedgeq⟩ := hqF
        have hpositive : triangularPositiveEdge L (rep k).1 (rep k).2 =
            triangularPositiveEdge L q.1 q.2 :=
          (hedge k).trans hedgeq
        have hpair := (triangularTorusPositiveEdge_eq_iff
          L (rep k).2 q.2 (rep k).1 q.1).mp hpositive
        exact ⟨k, hk, Prod.ext hpair.2 hpair.1⟩
      · intro k _
        exact triangularBoundaryCoeff_mul_step_fst lower upper (d k)
    _ = ∑ q : Fin 3 × (ZMod L × ZMod L), g q := by
      apply Finset.sum_subset
      · simp [T]
      · intro q _ hqT
        have hnotF : triangularPositiveEdge L q.1 q.2 ∉ F := by
          intro hmem
          apply hqT
          simp [T, hmem]
        have hz := triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem
          L F hF hhom
          (q.2, triangularTorusPositiveDirection q.1) (by
            simpa [triangularPositiveEdge] using hnotF)
        have hpc : triangularFacePositiveCoeff lower upper q.1 q.2 = 0 := by
          rcases q with ⟨a, q⟩
          fin_cases a <;>
            simpa [triangularFacePositiveCoeff,
              triangularFaceBoundaryCoeff,
              triangularTorusPositiveDirection] using hz
        change g q = 0
        simp [g, hpc]
    _ = 0 := triangularFacePositiveCoeff_full_fst_sum_eq_zero lower upper

theorem triangularZeroHomology_cycleBoundaryCoeff_mul_step_snd_sum_eq_zero
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L p.edges.toFinset)
        (triangularZeroHomologyUpperPotential L p.edges.toFinset)
        (triangularTorusCycleNativeDart L p k) *
      (triangularIntStep
        (triangularTorusCycleNativeDart L p k).2).2) = 0 := by
  classical
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let F := p.edges.toFinset
  let lower := triangularZeroHomologyLowerPotential L F
  let upper := triangularZeroHomologyUpperPotential L F
  let d : Fin p.darts.length → triangularTorusDart L :=
    triangularTorusCycleNativeDart L p
  let rep : Fin p.darts.length → Fin 3 × (ZMod L × ZMod L) :=
    fun k => triangularTorusPositiveRepresentation (d k)
  let T := (Finset.univ : Finset (Fin 3 × (ZMod L × ZMod L))).filter
    (fun q => triangularPositiveEdge L q.1 q.2 ∈ F)
  let g : Fin 3 × (ZMod L × ZMod L) → Int := fun q =>
    triangularFacePositiveCoeff lower upper q.1 q.2 *
      (triangularIntStep (triangularTorusPositiveDirection q.1)).2
  have hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L) :=
    ons_cycle_edges_evenSubgraph (triangularTorusGraph L) p hp
  have hedge (k : Fin p.darts.length) :
      triangularPositiveEdge L (rep k).1 (rep k).2 =
        (kwGraphCycleDartLoop p k).edge := by
    rw [show rep k = triangularTorusPositiveRepresentation (d k) by rfl]
    rw [triangularTorusPositiveRepresentation,
      triangularPositiveEdge_index_source,
      triangularTorusCycleNativeDart_equiv]
  have hedgeMem (k : Fin p.darts.length) :
      (kwGraphCycleDartLoop p k).edge ∈ F := by
    rw [show F = p.edges.toFinset by rfl,
      triangularTorusCycle_edges_toFinset_eq_image L p,
      Finset.mem_image]
    exact ⟨k, Finset.mem_univ _, rfl⟩
  calc
    (∑ k, triangularFaceBoundaryCoeff lower upper (d k) *
        (triangularIntStep (d k).2).2) = ∑ q ∈ T, g q := by
      apply Finset.sum_bij (fun k _ => rep k)
      · intro k _
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [hedge k]; exact hedgeMem k⟩
      · intro i _ j _ hij
        exact triangularTorusCycle_positiveRepresentation_injective
          L p hp hij
      · intro q hq
        have hqF := (Finset.mem_filter.mp hq).2
        rw [show F = p.edges.toFinset by rfl,
          triangularTorusCycle_edges_toFinset_eq_image L p,
          Finset.mem_image] at hqF
        obtain ⟨k, hk, hedgeq⟩ := hqF
        have hpositive : triangularPositiveEdge L (rep k).1 (rep k).2 =
            triangularPositiveEdge L q.1 q.2 :=
          (hedge k).trans hedgeq
        have hpair := (triangularTorusPositiveEdge_eq_iff
          L (rep k).2 q.2 (rep k).1 q.1).mp hpositive
        exact ⟨k, hk, Prod.ext hpair.2 hpair.1⟩
      · intro k _
        exact triangularBoundaryCoeff_mul_step_snd lower upper (d k)
    _ = ∑ q : Fin 3 × (ZMod L × ZMod L), g q := by
      apply Finset.sum_subset
      · simp [T]
      · intro q _ hqT
        have hnotF : triangularPositiveEdge L q.1 q.2 ∉ F := by
          intro hmem
          apply hqT
          simp [T, hmem]
        have hz := triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem
          L F hF hhom
          (q.2, triangularTorusPositiveDirection q.1) (by
            simpa [triangularPositiveEdge] using hnotF)
        have hpc : triangularFacePositiveCoeff lower upper q.1 q.2 = 0 := by
          rcases q with ⟨a, q⟩
          fin_cases a <;>
            simpa [triangularFacePositiveCoeff,
              triangularFaceBoundaryCoeff,
              triangularTorusPositiveDirection] using hz
        change g q = 0
        simp [g, hpc]
    _ = 0 := triangularFacePositiveCoeff_full_snd_sum_eq_zero lower upper

theorem triangularTorus_simpleCycle_zeroEvenHomology_displacement_eq_zero
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    (∑ k, triangularIntStep
      (triangularTorusCycleNativeDart L p k).2) = 0 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let lower := triangularZeroHomologyLowerPotential L p.edges.toFinset
  let upper := triangularZeroHomologyUpperPotential L p.edges.toFinset
  let d : Fin p.darts.length → triangularTorusDart L :=
    triangularTorusCycleNativeDart L p
  let C := triangularFaceBoundaryCoeff lower upper (d 0)
  have hconst : ∀ k, triangularFaceBoundaryCoeff lower upper (d k) = C := by
    exact triangularZeroHomology_cycleBoundaryCoeff_eq_root L p hp hhom
  have hC : C ≠ 0 := by
    exact triangularZeroHomology_cycleBoundaryCoeff_root_ne_zero
      L p hp hhom
  have hxWeighted :=
    triangularZeroHomology_cycleBoundaryCoeff_mul_step_fst_sum_eq_zero
      L p hp hhom
  have hyWeighted :=
    triangularZeroHomology_cycleBoundaryCoeff_mul_step_snd_sum_eq_zero
      L p hp hhom
  have hx : (∑ k, (triangularIntStep (d k).2).1) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hC
    calc
      C * ∑ k, (triangularIntStep (d k).2).1 =
          ∑ k, C * (triangularIntStep (d k).2).1 := by
        rw [Finset.mul_sum]
      _ = ∑ k, triangularFaceBoundaryCoeff lower upper (d k) *
          (triangularIntStep (d k).2).1 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hconst k]
      _ = 0 := hxWeighted
  have hy : (∑ k, (triangularIntStep (d k).2).2) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hC
    calc
      C * ∑ k, (triangularIntStep (d k).2).2 =
          ∑ k, C * (triangularIntStep (d k).2).2 := by
        rw [Finset.mul_sum]
      _ = ∑ k, triangularFaceBoundaryCoeff lower upper (d k) *
          (triangularIntStep (d k).2).2 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hconst k]
      _ = 0 := hyWeighted
  apply Prod.ext
  · simpa only [Prod.fst_sum, Prod.fst_zero] using hx
  · simpa only [Prod.snd_sum, Prod.snd_zero] using hy

theorem triangularTorus_zeroHomologyWinding
    (L : Nat) [Fact (2 < L)] : TriangularTorusZeroHomologyWinding L := by
  intro root p hp hsurface
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hhom := triangularTorusEvenHomology_eq_zero_of_surfaceHomology
    L p.edges.toFinset hsurface
  simpa only [triangularTorusCycleNativeDart_snd] using
    (triangularTorus_simpleCycle_zeroEvenHomology_displacement_eq_zero
      L p hp hhom)

theorem triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign_closed
    (L : Nat) [Fact (2 < L)]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
        (kwGraphCycleDartLoop p) =
      -(surfaceParitySign
        (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0)
          (surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
            p.edges.toFinset)) : Complex) := by
  exact triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign
    L rho hrho (triangularTorus_zeroHomologyWinding L) p hp

end StatMech.FrontierA
