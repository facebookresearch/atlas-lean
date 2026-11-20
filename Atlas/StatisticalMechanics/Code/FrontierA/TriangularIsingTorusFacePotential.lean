/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusFaceBoundary
import Code.Onsager.TorusPrimitiveWinding









open scoped BigOperators
open scoped symmDiff

namespace StatMech.FrontierA

open StatMech.Onsager

noncomputable def triangularTorusEastEdge (L : Nat) [Fact (2 < L)]
    (p : ZMod L × ZMod L) : Sym2 (ZMod L × ZMod L) :=
  (triangularTorusDartEquiv L (p, 1)).edge

noncomputable def triangularTorusNorthEdge (L : Nat) [Fact (2 < L)]
    (p : ZMod L × ZMod L) : Sym2 (ZMod L × ZMod L) :=
  (triangularTorusDartEquiv L (p, 3)).edge

noncomputable def triangularTorusNortheastEdge (L : Nat) [Fact (2 < L)]
    (p : ZMod L × ZMod L) : Sym2 (ZMod L × ZMod L) :=
  (triangularTorusDartEquiv L (p, 5)).edge

def triangularTorusPositiveDirection : Fin 3 → Fin 6 := ![1, 3, 5]

theorem triangularTorusPositiveDirection_injective :
    Function.Injective triangularTorusPositiveDirection := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusPositiveDirection] at h ⊢

theorem triangularTorusPositiveEdge_eq_iff
    (L : Nat) [Fact (2 < L)]
    (p q : ZMod L × ZMod L) (a b : Fin 3) :
    (triangularTorusDartEquiv L
        (p, triangularTorusPositiveDirection a)).edge =
      (triangularTorusDartEquiv L
        (q, triangularTorusPositiveDirection b)).edge ↔
      p = q ∧ a = b := by
  constructor
  · intro hedge
    rcases (SimpleGraph.dart_edge_eq_iff
      (triangularTorusDartEquiv L
        (p, triangularTorusPositiveDirection a))
      (triangularTorusDartEquiv L
        (q, triangularTorusPositiveDirection b))).mp hedge with hsame | hrev
    · have hnative := (triangularTorusDartEquiv L).injective hsame
      exact ⟨congrArg Prod.fst hnative,
        triangularTorusPositiveDirection_injective
          (congrArg Prod.snd hnative)⟩
    · have hnative :
          (p, triangularTorusPositiveDirection a) =
            triangularTorusDartReverse L
              (q, triangularTorusPositiveDirection b) := by
        apply (triangularTorusDartEquiv L).injective
        rw [triangularTorusDartEquiv_reverse]
        exact hrev
      have hdir := congrArg Prod.snd hnative
      fin_cases a <;> fin_cases b <;>
        simp [triangularTorusPositiveDirection,
          triangularTorusDartReverse,
          triangularTorusDirectionReverse] at hdir
  · rintro ⟨rfl, rfl⟩
    rfl

theorem triangularTorusEastEdge_eq_ons
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    triangularTorusEastEdge L p = ons_portEdge L (p, 0) := by
  rcases p with ⟨x, y⟩
  simp [triangularTorusEastEdge, triangularTorusDartEquiv_apply,
    triangularTorusDartToGraphDart, triangularTorusDirectionStep,
    ons_portEdge, ons_dirStep, SimpleGraph.Dart.edge]

theorem triangularTorusNorthEdge_eq_ons
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    triangularTorusNorthEdge L p = ons_portEdge L (p, 1) := by
  rcases p with ⟨x, y⟩
  simp [triangularTorusNorthEdge, triangularTorusDartEquiv_apply,
    triangularTorusDartToGraphDart, triangularTorusDirectionStep,
    ons_portEdge, ons_dirStep, SimpleGraph.Dart.edge]

theorem ons_eastPortEdge_injective
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (fun p : ZMod L × ZMod L => ons_portEdge L (p, 0)) := by
  intro p q hpq
  rcases (ons_portEdge_eq_iff L (p, 0) (q, 0)).mp hpq.symm with h | h
  · exact (congrArg Prod.fst h).symm
  · have hdir := congrArg Prod.snd h
    simp [ons_dartRev] at hdir

theorem ons_northPortEdge_injective
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (fun p : ZMod L × ZMod L => ons_portEdge L (p, 1)) := by
  intro p q hpq
  rcases (ons_portEdge_eq_iff L (p, 1) (q, 1)).mp hpq.symm with h | h
  · exact (congrArg Prod.fst h).symm
  · have hdir := congrArg Prod.snd h
    simp [ons_dartRev] at hdir

theorem ons_eastPortEdge_ne_northPortEdge
    (L : Nat) [Fact (2 < L)] (p q : ZMod L × ZMod L) :
    ons_portEdge L (p, 0) ≠ ons_portEdge L (q, 1) := by
  intro hpq
  rcases (ons_portEdge_eq_iff L (p, 0) (q, 1)).mp hpq.symm with h | h
  · have hdir := congrArg Prod.snd h
    simp at hdir
  · have hdir := congrArg Prod.snd h
    simp [ons_dartRev] at hdir

theorem triangularTorusDirectionStep_injective_public
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (triangularTorusDirectionStep L) := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
    exact one_ne_zero
  have h2 : (2 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : 2 < L)
    omega
  have hm1 : (-1 : ZMod L) ≠ 0 := neg_ne_zero.mpr h1
  have hpm : (1 : ZMod L) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have h01 : (0 : ZMod L) ≠ 1 := Ne.symm h1
  have hmp : (-1 : ZMod L) ≠ 1 := Ne.symm hpm
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionStep, h1, hm1, hpm, h01, hmp] at hab ⊢

theorem triangularTorus_neighborFinset_steps
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    (triangularTorusGraph L).neighborFinset p =
      Finset.univ.image (fun a : Fin 6 =>
        p - triangularTorusDirectionStep L a) := by
  ext q
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro hadj
    change triangularTorusAdj L p q at hadj
    rcases hadj with
      (⟨hcoord, hstep | hstep⟩ | ⟨hcoord, hstep | hstep⟩) |
        (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · refine ⟨2, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hcoord]
      · simp [triangularTorusDirectionStep]
        rw [hstep]
        ring
    · refine ⟨3, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hcoord]
      · simp [triangularTorusDirectionStep]
        rw [hstep]
        ring
    · refine ⟨0, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hstep]
        ring
      · simp [triangularTorusDirectionStep]
        rw [hcoord]
    · refine ⟨1, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hstep]
        ring
      · simp [triangularTorusDirectionStep]
        rw [hcoord]
    · refine ⟨4, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hx]
        ring
      · simp [triangularTorusDirectionStep]
        rw [hy]
        ring
    · refine ⟨5, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hx]
        ring
      · simp [triangularTorusDirectionStep]
        rw [hy]
        ring
  · rintro ⟨a, rfl⟩
    fin_cases a <;>
      simp [triangularTorusGraph, triangularTorusAdj, onsTorusAdj,
        triangularTorusDirectionStep] <;> ring

private theorem sum_fin_six {A : Type*} [AddCommMonoid A]
    (f : Fin 6 → A) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  exact Fin.sum_univ_six f

set_option maxHeartbeats 800000 in


theorem triangularTorus_edgeBits_divergence_zero
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (p : ZMod L × ZMod L) :
    (ons_edgeBit F (triangularTorusEastEdge L p) : ZMod 2) +
      ons_edgeBit F (triangularTorusEastEdge L (p.1 - 1, p.2)) +
      ons_edgeBit F (triangularTorusNorthEdge L p) +
      ons_edgeBit F (triangularTorusNorthEdge L (p.1, p.2 - 1)) +
      ons_edgeBit F (triangularTorusNortheastEdge L p) +
      ons_edgeBit F
        (triangularTorusNortheastEdge L (p.1 - 1, p.2 - 1)) = 0 := by
  have hsum := ons_evenSubgraph_neighbor_sum_zero
    (triangularTorusGraph L) F hF p
  rw [triangularTorus_neighborFinset_steps L p] at hsum
  have hinj : Function.Injective (fun a : Fin 6 =>
      p - triangularTorusDirectionStep L a) := by
    intro a b hab
    apply triangularTorusDirectionStep_injective_public L
    apply Prod.ext
    · have h := congrArg Prod.fst hab
      dsimp at h ⊢
      linear_combination -h
    · have h := congrArg Prod.snd hab
      dsimp at h ⊢
      linear_combination -h
  have hreindex :
      (∑ w ∈ Finset.univ.image (fun a : Fin 6 =>
          p - triangularTorusDirectionStep L a),
          if s(p, w) ∈ F then (1 : ZMod 2) else 0) =
        ∑ a : Fin 6,
          if s(p, p - triangularTorusDirectionStep L a) ∈ F then
            (1 : ZMod 2) else 0 := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hinj hab
  rw [hreindex] at hsum
  rw [sum_fin_six] at hsum
  have hpadd (x y : ZMod L) :
      p + (x, y) = (p.1 + x, p.2 + y) := by
    rcases p
    rfl
  simpa [ons_edgeBit, triangularTorusEastEdge,
    triangularTorusNorthEdge, triangularTorusNortheastEdge,
    triangularTorusDartEquiv_apply, triangularTorusDartToGraphDart,
    triangularTorusDirectionStep, SimpleGraph.Dart.edge,
    sub_eq_add_neg, hpadd, Sym2.eq_swap,
    add_assoc, add_left_comm, add_comm] using hsum

noncomputable def triangularSquareHorizontalEdges
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  ((Finset.univ.filter (fun p => triangularTorusEastEdge L p ∈ F)).image
      (fun p => ons_portEdge L (p, 0))) ∆
    ((Finset.univ.filter
      (fun p => triangularTorusNortheastEdge L p ∈ F)).image
        (fun p => ons_portEdge L (p, 0)))

noncomputable def triangularSquareVerticalEdges
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  ((Finset.univ.filter (fun p => triangularTorusNorthEdge L p ∈ F)).image
      (fun p => ons_portEdge L (p, 1))) ∆
    ((Finset.univ.filter
      (fun p => triangularTorusNortheastEdge L p ∈ F)).image
        (fun p => ons_portEdge L ((p.1 + 1, p.2), 1)))



noncomputable def triangularSquareExpansion
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  triangularSquareHorizontalEdges L F ∪ triangularSquareVerticalEdges L F

private theorem mem_image_east_iff
    (L : Nat) [Fact (2 < L)]
    (S : Finset (ZMod L × ZMod L)) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 0) ∈ S.image (fun q => ons_portEdge L (q, 0)) ↔
      p ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, heq⟩
    exact (ons_eastPortEdge_injective L heq).symm ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

private theorem mem_image_north_iff
    (L : Nat) [Fact (2 < L)]
    (S : Finset (ZMod L × ZMod L)) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 1) ∈ S.image (fun q => ons_portEdge L (q, 1)) ↔
      p ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, heq⟩
    exact (ons_northPortEdge_injective L heq).symm ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

private theorem mem_shifted_image_north_iff
    (L : Nat) [Fact (2 < L)]
    (S : Finset (ZMod L × ZMod L)) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 1) ∈
        S.image (fun q => ons_portEdge L ((q.1 + 1, q.2), 1)) ↔
      (p.1 - 1, p.2) ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, heq⟩
    have hsite := ons_northPortEdge_injective L heq
    have hqsite : q = (p.1 - 1, p.2) := by
      apply Prod.ext
      · have hx := congrArg Prod.fst hsite
        dsimp at hx
        linear_combination hx
      · simpa using congrArg Prod.snd hsite
    rwa [hqsite] at hq
  · intro hp
    refine ⟨(p.1 - 1, p.2), hp, ?_⟩
    apply congrArg (fun q => ons_portEdge L (q, 1))
    apply Prod.ext <;> simp <;> ring

private theorem east_not_mem_verticalEdges
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 0) ∉ triangularSquareVerticalEdges L F := by
  intro hmem
  rw [triangularSquareVerticalEdges, Finset.mem_symmDiff] at hmem
  rcases hmem with ⟨hmem, -⟩ | ⟨hmem, -⟩
  · rw [Finset.mem_image] at hmem
    obtain ⟨q, -, heq⟩ := hmem
    exact ons_eastPortEdge_ne_northPortEdge L p q heq.symm
  · rw [Finset.mem_image] at hmem
    obtain ⟨q, -, heq⟩ := hmem
    exact ons_eastPortEdge_ne_northPortEdge L p (q.1 + 1, q.2) heq.symm

private theorem north_not_mem_horizontalEdges
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (p : ZMod L × ZMod L) :
    ons_portEdge L (p, 1) ∉ triangularSquareHorizontalEdges L F := by
  intro hmem
  rw [triangularSquareHorizontalEdges, Finset.mem_symmDiff] at hmem
  rcases hmem with ⟨hmem, -⟩ | ⟨hmem, -⟩
  · rw [Finset.mem_image] at hmem
    obtain ⟨q, -, heq⟩ := hmem
    exact ons_eastPortEdge_ne_northPortEdge L q p heq
  · rw [Finset.mem_image] at hmem
    obtain ⟨q, -, heq⟩ := hmem
    exact ons_eastPortEdge_ne_northPortEdge L q p heq

theorem triangularSquareExpansion_horizontalBit
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (p : ZMod L × ZMod L) :
    ons_horizontalZBit (triangularSquareExpansion L F) p =
      (ons_edgeBit F (triangularTorusEastEdge L p) : ZMod 2) +
        (ons_edgeBit F (triangularTorusNortheastEdge L p) : ZMod 2) := by
  have hH : ons_portEdge L (p, 0) ∈
      triangularSquareHorizontalEdges L F ↔
      (triangularTorusEastEdge L p ∈ F ∧
          triangularTorusNortheastEdge L p ∉ F) ∨
        (triangularTorusNortheastEdge L p ∈ F ∧
          triangularTorusEastEdge L p ∉ F) := by
    unfold triangularSquareHorizontalEdges
    rw [Finset.mem_symmDiff, mem_image_east_iff, mem_image_east_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hV := east_not_mem_verticalEdges L F p
  unfold ons_horizontalZBit ons_horizontalBit triangularSquareExpansion
  rw [ons_edgeBit]
  simp only [Finset.mem_union, hV, or_false, hH]
  by_cases he : triangularTorusEastEdge L p ∈ F <;>
    by_cases hd : triangularTorusNortheastEdge L p ∈ F <;>
      simp [ons_edgeBit, he, hd]

theorem triangularSquareExpansion_verticalBit
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (p : ZMod L × ZMod L) :
    ons_verticalZBit (triangularSquareExpansion L F) p =
      (ons_edgeBit F (triangularTorusNorthEdge L p) : ZMod 2) +
        (ons_edgeBit F
          (triangularTorusNortheastEdge L (p.1 - 1, p.2)) : ZMod 2) := by
  have hV : ons_portEdge L (p, 1) ∈ triangularSquareVerticalEdges L F ↔
      (triangularTorusNorthEdge L p ∈ F ∧
          triangularTorusNortheastEdge L (p.1 - 1, p.2) ∉ F) ∨
        (triangularTorusNortheastEdge L (p.1 - 1, p.2) ∈ F ∧
          triangularTorusNorthEdge L p ∉ F) := by
    unfold triangularSquareVerticalEdges
    rw [Finset.mem_symmDiff, mem_image_north_iff,
      mem_shifted_image_north_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hH := north_not_mem_horizontalEdges L F p
  unfold ons_verticalZBit ons_verticalBit triangularSquareExpansion
  rw [ons_edgeBit]
  simp only [Finset.mem_union, hH, false_or, hV]
  by_cases hn : triangularTorusNorthEdge L p ∈ F <;>
    by_cases hd : triangularTorusNortheastEdge L (p.1 - 1, p.2) ∈ F <;>
      simp [ons_edgeBit, hn, hd]

theorem triangularSquareExpansion_subset_edgeFinset
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    triangularSquareExpansion L F ⊆ (onsTorusGraph L).edgeFinset := by
  intro edge hedge
  rw [triangularSquareExpansion, Finset.mem_union] at hedge
  rcases hedge with hedge | hedge
  · rw [triangularSquareHorizontalEdges, Finset.mem_symmDiff] at hedge
    rcases hedge with ⟨hedge, -⟩ | ⟨hedge, -⟩ <;>
      rw [Finset.mem_image] at hedge <;>
      obtain ⟨p, -, rfl⟩ := hedge <;>
      exact ons_portEdge_mem_edgeFinset L (p, 0)
  · rw [triangularSquareVerticalEdges, Finset.mem_symmDiff] at hedge
    rcases hedge with ⟨hedge, -⟩ | ⟨hedge, -⟩ <;>
      rw [Finset.mem_image] at hedge
    · obtain ⟨p, -, rfl⟩ := hedge
      exact ons_portEdge_mem_edgeFinset L (p, 1)
    · obtain ⟨p, -, rfl⟩ := hedge
      exact ons_portEdge_mem_edgeFinset L ((p.1 + 1, p.2), 1)

set_option maxHeartbeats 800000 in


theorem triangularSquareExpansion_evenSubgraph
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L)) :
    triangularSquareExpansion L F ∈
      StatMech.Ising.evenSubgraphs (onsTorusGraph L) := by
  let E := triangularSquareExpansion L F
  have hsubset : E ⊆ (onsTorusGraph L).edgeFinset :=
    triangularSquareExpansion_subset_edgeFinset L F
  rw [StatMech.Ising.evenSubgraphs, Finset.mem_filter,
    Finset.mem_powerset]
  refine ⟨hsubset, ?_⟩
  intro p
  have hEeq : E = (onsTorusGraph L).edgeFinset.filter (fun e => e ∈ E) := by
    ext edge
    simp only [Finset.mem_filter]
    constructor
    · intro hedge
      exact ⟨hsubset hedge, hedge⟩
    · exact And.right
  have hcast := ons_cast_incCount_filter_eq_neighbor_sum
    (onsTorusGraph L) (fun e => e ∈ E) p
  rw [← hEeq, ons_torus_neighbor_sum_eq_direction_sum] at hcast
  rw [Fin.sum_univ_four] at hcast
  have hzero :
      ons_horizontalZBit E p +
        ons_horizontalZBit E (p.1 - 1, p.2) +
        ons_verticalZBit E p +
        ons_verticalZBit E (p.1, p.2 - 1) = 0 := by
    dsimp [E]
    rw [triangularSquareExpansion_horizontalBit,
      triangularSquareExpansion_horizontalBit,
      triangularSquareExpansion_verticalBit,
      triangularSquareExpansion_verticalBit]
    have hdiv := triangularTorus_edgeBits_divergence_zero L F hF p
    let d : Fin 2 := ons_edgeBit F
      (triangularTorusNortheastEdge L (p.1 - 1, p.2))
    have hdd : d + d = 0 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_zero]
      omega
    calc
      _ = (ons_edgeBit F (triangularTorusEastEdge L p) +
              ons_edgeBit F
                (triangularTorusEastEdge L (p.1 - 1, p.2)) +
              ons_edgeBit F (triangularTorusNorthEdge L p) +
              ons_edgeBit F
                (triangularTorusNorthEdge L (p.1, p.2 - 1)) +
              ons_edgeBit F (triangularTorusNortheastEdge L p) +
              ons_edgeBit F (triangularTorusNortheastEdge L
                (p.1 - 1, p.2 - 1))) + (d + d) := by
        dsimp [d]
        abel
      _ = ons_edgeBit F (triangularTorusEastEdge L p) +
              ons_edgeBit F
                (triangularTorusEastEdge L (p.1 - 1, p.2)) +
              ons_edgeBit F (triangularTorusNorthEdge L p) +
              ons_edgeBit F
                (triangularTorusNorthEdge L (p.1, p.2 - 1)) +
              ons_edgeBit F (triangularTorusNortheastEdge L p) +
              ons_edgeBit F (triangularTorusNortheastEdge L
                (p.1 - 1, p.2 - 1)) := by
        rw [hdd, add_zero]
      _ = 0 := hdiv
  have hcastzero : ((StatMech.Ising.incCount E p : Nat) : ZMod 2) = 0 := by
    change ((StatMech.Ising.incCount E p : Nat) : ZMod 2) =
      ((if ons_portEdge L (p, 0) ∈ E then 1 else 0) +
        (if ons_portEdge L (p, 1) ∈ E then 1 else 0) +
        (if ons_portEdge L (p, 2) ∈ E then 1 else 0) +
        if ons_portEdge L (p, 3) ∈ E then 1 else 0) at hcast
    rw [ons_portEdge_west_eq_horizontal,
      ons_portEdge_south_eq_vertical] at hcast
    rw [hcast]
    simpa only [ons_horizontalZBit, ons_horizontalBit,
      ons_verticalZBit, ons_verticalBit, ons_edgeBit,
      add_assoc, add_left_comm, add_comm] using hzero
  rw [Nat.even_iff]
  exact Nat.mod_eq_zero_of_dvd
    ((CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp hcastzero)

noncomputable def triangularPositiveEdge
    (L : Nat) [Fact (2 < L)] (a : Fin 3)
    (p : ZMod L × ZMod L) : Sym2 (ZMod L × ZMod L) :=
  (triangularTorusDartEquiv L
    (p, triangularTorusPositiveDirection a)).edge

noncomputable def triangularPositiveEdgeSources
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (a : Fin 3) :
    Finset (ZMod L × ZMod L) :=
  Finset.univ.filter (fun p => triangularPositiveEdge L a p ∈ F)

noncomputable def triangularPositiveEdgeReconstruction
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  Finset.univ.biUnion (fun a : Fin 3 =>
    (triangularPositiveEdgeSources L F a).image
      (triangularPositiveEdge L a))

theorem triangularPositiveEdgeReconstruction_eq
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ⊆ (triangularTorusGraph L).edgeFinset) :
    triangularPositiveEdgeReconstruction L F = F := by
  apply Finset.ext
  intro edge
  constructor
  · intro hedge
    rw [triangularPositiveEdgeReconstruction, Finset.mem_biUnion] at hedge
    obtain ⟨a, -, hedge⟩ := hedge
    rw [Finset.mem_image] at hedge
    obtain ⟨p, hp, rfl⟩ := hedge
    exact (Finset.mem_filter.mp hp).2
  · intro hedge
    have hedgeGraph := hF hedge
    rw [SimpleGraph.mem_edgeFinset] at hedgeGraph
    induction edge using Sym2.ind with
    | _ u v =>
      let dart : (triangularTorusGraph L).Dart := ⟨(u, v), hedgeGraph⟩
      let d : triangularTorusDart L := (triangularTorusDartEquiv L).symm dart
      have hdart : triangularTorusDartEquiv L d = dart := by simp [d]
      have hdedge : (triangularTorusDartEquiv L d).edge = s(u, v) := by
        rw [hdart]
        rfl
      rcases d with ⟨p, a⟩
      fin_cases a
      · let r := triangularTorusDartReverse L (p, 0)
        have hrdir : r.2 = 1 := by
          simp [r, triangularTorusDartReverse,
            triangularTorusDirectionReverse]
        have hredge : (triangularTorusDartEquiv L r).edge = s(u, v) := by
          rw [triangularTorusDartEquiv_reverse, SimpleGraph.Dart.edge_symm]
          exact hdedge
        refine Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨r.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using
            (hredge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using hredge
      · refine Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using
            (hdedge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using hdedge
      · let r := triangularTorusDartReverse L (p, 2)
        have hrdir : r.2 = 3 := by
          simp [r, triangularTorusDartReverse,
            triangularTorusDirectionReverse]
        have hredge : (triangularTorusDartEquiv L r).edge = s(u, v) := by
          rw [triangularTorusDartEquiv_reverse, SimpleGraph.Dart.edge_symm]
          exact hdedge
        refine Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨r.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using
            (hredge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using hredge
      · refine Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using
            (hdedge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using hdedge
      · let r := triangularTorusDartReverse L (p, 4)
        have hrdir : r.2 = 5 := by
          simp [r, triangularTorusDartReverse,
            triangularTorusDirectionReverse]
        have hredge : (triangularTorusDartEquiv L r).edge = s(u, v) := by
          rw [triangularTorusDartEquiv_reverse, SimpleGraph.Dart.edge_symm]
          exact hdedge
        refine Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨r.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using
            (hredge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using hredge
      · refine Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using
            (hdedge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using hdedge

theorem triangularPositiveEdgeReconstruction_pairwiseDisjoint
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      (fun a => (triangularPositiveEdgeSources L F a).image
        (triangularPositiveEdge L a)) := by
  intro a _ b _ hab
  change Disjoint
    ((triangularPositiveEdgeSources L F a).image
      (triangularPositiveEdge L a))
    ((triangularPositiveEdgeSources L F b).image
      (triangularPositiveEdge L b))
  rw [Finset.disjoint_left]
  intro edge hea heb
  rw [Finset.mem_image] at hea heb
  obtain ⟨p, -, rfl⟩ := hea
  obtain ⟨q, -, heq⟩ := heb
  have hnative := (triangularTorusPositiveEdge_eq_iff L p q a b).mp heq.symm
  exact hab hnative.2

theorem sum_triangularPositiveEdgeSources
    {A : Type*} [AddCommMonoid A]
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ⊆ (triangularTorusGraph L).edgeFinset)
    (f : Sym2 (ZMod L × ZMod L) → A) :
    (∑ edge ∈ F, f edge) =
      ∑ a : Fin 3, ∑ p ∈ triangularPositiveEdgeSources L F a,
        f (triangularPositiveEdge L a p) := by
  conv_lhs =>
    rw [← triangularPositiveEdgeReconstruction_eq L F hF]
  unfold triangularPositiveEdgeReconstruction
  rw [Finset.sum_biUnion
    (triangularPositiveEdgeReconstruction_pairwiseDisjoint L F)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_image]
  intro p _ q _ hpq
  exact (triangularTorusPositiveEdge_eq_iff L p q a a).mp hpq |>.1

theorem triangularTorusXSeamEdge_positiveEdge_iff
    (L : Nat) [Fact (2 < L)] (a : Fin 3)
    (p : ZMod L × ZMod L) :
    triangularTorusXSeamEdge L (triangularPositiveEdge L a p) ↔
      (a = 0 ∨ a = 2) ∧ p.1 = -1 := by
  unfold triangularPositiveEdge
  rw [triangularTorusXSeamEdge_dart_iff]
  fin_cases a <;>
    simp [triangularTorusPositiveDirection,
      triangularTorusXMovementDart, triangularTorusXMovementDirection,
      ons_xWrap]

theorem triangularTorusYSeamEdge_positiveEdge_iff
    (L : Nat) [Fact (2 < L)] (a : Fin 3)
    (p : ZMod L × ZMod L) :
    triangularTorusYSeamEdge L (triangularPositiveEdge L a p) ↔
      (a = 1 ∨ a = 2) ∧ p.2 = -1 := by
  unfold triangularPositiveEdge
  rw [triangularTorusYSeamEdge_dart_iff]
  fin_cases a <;>
    simp [triangularTorusPositiveDirection,
      triangularTorusYMovementDart, triangularTorusYMovementDirection,
      ons_yWrap]

private theorem sum_positiveSources_first_seam
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (a : Fin 3) :
    (∑ p ∈ triangularPositiveEdgeSources L F a,
        if p.1 = -1 then (1 : ZMod 2) else 0) =
      ∑ y : ZMod L,
        (ons_edgeBit F (triangularPositiveEdge L a (-1, y)) : ZMod 2) := by
  classical
  unfold triangularPositiveEdgeSources
  calc
    (∑ p ∈ Finset.univ.filter
        (fun p => triangularPositiveEdge L a p ∈ F),
        if p.1 = -1 then (1 : ZMod 2) else 0) =
      ∑ p : ZMod L × ZMod L,
        if triangularPositiveEdge L a p ∈ F then
          (if p.1 = -1 then (1 : ZMod 2) else 0) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ x : ZMod L, ∑ y : ZMod L,
        if triangularPositiveEdge L a (x, y) ∈ F then
          (if x = -1 then (1 : ZMod 2) else 0) else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ y : ZMod L,
        if triangularPositiveEdge L a (-1, y) ∈ F then 1 else 0 := by
      rw [Finset.sum_eq_single (-1)]
      · apply Finset.sum_congr rfl
        intro y _
        simp
      · intro x _ hx
        apply Finset.sum_eq_zero
        intro y _
        simp [hx]
      · simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [ons_edgeBit]
      split <;> rfl

private theorem sum_positiveSources_second_seam
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (a : Fin 3) :
    (∑ p ∈ triangularPositiveEdgeSources L F a,
        if p.2 = -1 then (1 : ZMod 2) else 0) =
      ∑ x : ZMod L,
        (ons_edgeBit F (triangularPositiveEdge L a (x, -1)) : ZMod 2) := by
  classical
  unfold triangularPositiveEdgeSources
  calc
    (∑ p ∈ Finset.univ.filter
        (fun p => triangularPositiveEdge L a p ∈ F),
        if p.2 = -1 then (1 : ZMod 2) else 0) =
      ∑ p : ZMod L × ZMod L,
        if triangularPositiveEdge L a p ∈ F then
          (if p.2 = -1 then (1 : ZMod 2) else 0) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ x : ZMod L, ∑ y : ZMod L,
        if triangularPositiveEdge L a (x, y) ∈ F then
          (if y = -1 then (1 : ZMod 2) else 0) else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ x : ZMod L,
        if triangularPositiveEdge L a (x, -1) ∈ F then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (-1)]
      · simp
      · intro y _ hy
        simp [hy]
      · simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [ons_edgeBit]
      split <;> rfl

private theorem triangularTorusEvenHomology_fst_cast_eq_sum
    (L : Nat) (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ((triangularTorusEvenHomology L F).1 : ZMod 2) =
      ∑ edge ∈ F,
        if triangularTorusXSeamEdge L edge then (1 : ZMod 2) else 0 := by
  classical
  rw [Finset.sum_boole]
  apply ZMod.val_injective 2
  simp only [triangularTorusEvenHomology, ZMod.val_natCast]
  rfl

private theorem triangularTorusEvenHomology_snd_cast_eq_sum
    (L : Nat) (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ((triangularTorusEvenHomology L F).2 : ZMod 2) =
      ∑ edge ∈ F,
        if triangularTorusYSeamEdge L edge then (1 : ZMod 2) else 0 := by
  classical
  rw [Finset.sum_boole]
  apply ZMod.val_injective 2
  simp only [triangularTorusEvenHomology, ZMod.val_natCast]
  rfl

@[simp] theorem triangularPositiveEdge_zero
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    triangularPositiveEdge L 0 p = triangularTorusEastEdge L p := by
  simp [triangularPositiveEdge, triangularTorusPositiveDirection,
    triangularTorusEastEdge]

@[simp] theorem triangularPositiveEdge_one
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    triangularPositiveEdge L 1 p = triangularTorusNorthEdge L p := by
  simp [triangularPositiveEdge, triangularTorusPositiveDirection,
    triangularTorusNorthEdge]

@[simp] theorem triangularPositiveEdge_two
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    triangularPositiveEdge L 2 p = triangularTorusNortheastEdge L p := by
  simp [triangularPositiveEdge, triangularTorusPositiveDirection,
    triangularTorusNortheastEdge]



theorem triangularSquareExpansion_evenHomology
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ⊆ (triangularTorusGraph L).edgeFinset) :
    ons_evenHomology L (triangularSquareExpansion L F) =
      triangularTorusEvenHomology L F := by
  apply Prod.ext
  · apply Fin.ext
    have hcast :
        ((ons_evenHomology L (triangularSquareExpansion L F)).1 : ZMod 2) =
          ((triangularTorusEvenHomology L F).1 : ZMod 2) := by
      rw [ons_evenHomology_fst_cast_eq_xFlux,
        triangularTorusEvenHomology_fst_cast_eq_sum,
        sum_triangularPositiveEdgeSources L F hF]
      unfold ons_xFlux
      simp_rw [triangularSquareExpansion_horizontalBit]
      change (∑ y ∈ Finset.univ,
        ((ons_edgeBit F (triangularTorusEastEdge L (-1, y)) : ZMod 2) +
          ons_edgeBit F (triangularTorusNortheastEdge L (-1, y)))) = _
      rw [Finset.sum_add_distrib, Fin.sum_univ_three]
      simp_rw [triangularTorusXSeamEdge_positiveEdge_iff]
      simp only [Fin.isValue, Fin.reduceEq, one_ne_zero, or_false,
        false_or, or_self, true_or, or_true, true_and, false_and,
        ite_true, ite_false, zero_add, add_zero]
      rw [sum_positiveSources_first_seam L F 0,
        sum_positiveSources_first_seam L F 2]
      simp only [triangularPositiveEdge_zero,
        triangularPositiveEdge_two, Finset.sum_const_zero, add_zero]
      rfl
    exact congrArg (fun z : ZMod 2 => z.val) hcast
  · apply Fin.ext
    have hcast :
        ((ons_evenHomology L (triangularSquareExpansion L F)).2 : ZMod 2) =
          ((triangularTorusEvenHomology L F).2 : ZMod 2) := by
      rw [ons_evenHomology_snd_cast_eq_yFlux,
        triangularTorusEvenHomology_snd_cast_eq_sum,
        sum_triangularPositiveEdgeSources L F hF]
      unfold ons_yFlux
      simp_rw [triangularSquareExpansion_verticalBit]
      change (∑ x ∈ Finset.univ,
        ((ons_edgeBit F (triangularTorusNorthEdge L (x, -1)) : ZMod 2) +
          ons_edgeBit F
            (triangularTorusNortheastEdge L (x - 1, -1)))) = _
      rw [Finset.sum_add_distrib, Fin.sum_univ_three]
      simp_rw [triangularTorusYSeamEdge_positiveEdge_iff]
      simp only [Fin.isValue, Fin.reduceEq, one_ne_zero, or_false,
        false_or, or_self, true_or, or_true, true_and, false_and,
        ite_true, ite_false, zero_add, add_zero]
      rw [sum_positiveSources_second_seam L F 1,
        sum_positiveSources_second_seam L F 2]
      simp only [triangularPositiveEdge_one, triangularPositiveEdge_two,
        Finset.sum_const_zero, zero_add, add_zero]
      congr 1
      simpa [sub_eq_add_neg] using
        (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
          (fun x : ZMod L =>
            (ons_edgeBit F
              (triangularTorusNortheastEdge L (x, -1)) : ZMod 2)))
    exact congrArg (fun z : ZMod 2 => z.val) hcast


noncomputable def triangularZeroHomologyUpperPotential
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  ons_zeroFluxPotential (triangularSquareExpansion L F) p

@[simp] theorem zmodFinEquiv_two_apply (a : Fin 2) :
    (ZMod.finEquiv 2) a = (a : ZMod 2) := rfl

private theorem finTwo_add_self_eq_zero (a : Fin 2) : a + a = 0 := by
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_zero]
  omega



noncomputable def triangularZeroHomologyLowerPotential
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  triangularZeroHomologyUpperPotential L F p +
    (ZMod.finEquiv 2)
      (ons_edgeBit F (triangularTorusNortheastEdge L p))

private theorem triangularEvenSubgraph_subset
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L)) :
    F ⊆ (triangularTorusGraph L).edgeFinset := by
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1

theorem triangularZeroHomology_eastCoeff_cast
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L) :
    (triangularFaceEastCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p : ZMod 2) =
      ons_edgeBit F (triangularTorusEastEdge L p) := by
  let E := triangularSquareExpansion L F
  have hE := triangularSquareExpansion_evenSubgraph L F hF
  have hEhom : ons_evenHomology L E = 0 := by
    dsimp [E]
    rw [triangularSquareExpansion_evenHomology L F
      (triangularEvenSubgraph_subset L F hF), hhom]
  rw [triangularFaceEastCoeff_cast_mod_two]
  change (ons_zeroFluxPotential E p +
      (ZMod.finEquiv 2)
        (ons_edgeBit F (triangularTorusNortheastEdge L p))) +
    ons_zeroFluxPotential E (p.1, p.2 - 1) = _
  calc
    _ = (ons_zeroFluxPotential E p +
          ons_zeroFluxPotential E (p.1, p.2 - 1)) +
        (ZMod.finEquiv 2)
          (ons_edgeBit F (triangularTorusNortheastEdge L p)) := by abel
    _ = ons_horizontalZBit E p +
        (ZMod.finEquiv 2)
          (ons_edgeBit F (triangularTorusNortheastEdge L p)) := by
      rw [ons_zeroFluxPotential_horizontal_boundary_of_zeroHomology
        L E hE hEhom]
    _ = _ := by
      rw [triangularSquareExpansion_horizontalBit,
        zmodFinEquiv_two_apply]
      let a : ZMod 2 := ons_edgeBit F (triangularTorusEastEdge L p)
      let d : ZMod 2 := ons_edgeBit F (triangularTorusNortheastEdge L p)
      change a + d + d = a
      calc
        _ = a + (d + d) := by abel
        _ = a := by rw [CharTwo.add_self_eq_zero, add_zero]

theorem triangularZeroHomology_northCoeff_cast
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L) :
    (triangularFaceNorthCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p : ZMod 2) =
      ons_edgeBit F (triangularTorusNorthEdge L p) := by
  let E := triangularSquareExpansion L F
  have hE := triangularSquareExpansion_evenSubgraph L F hF
  have hEhom : ons_evenHomology L E = 0 := by
    dsimp [E]
    rw [triangularSquareExpansion_evenHomology L F
      (triangularEvenSubgraph_subset L F hF), hhom]
  rw [triangularFaceNorthCoeff_cast_mod_two]
  change (ons_zeroFluxPotential E (p.1 - 1, p.2) +
      (ZMod.finEquiv 2) (ons_edgeBit F
        (triangularTorusNortheastEdge L (p.1 - 1, p.2)))) +
    ons_zeroFluxPotential E p = _
  calc
    _ = (ons_zeroFluxPotential E p +
          ons_zeroFluxPotential E (p.1 - 1, p.2)) +
        (ZMod.finEquiv 2) (ons_edgeBit F
          (triangularTorusNortheastEdge L (p.1 - 1, p.2))) := by abel
    _ = ons_verticalZBit E p +
        (ZMod.finEquiv 2) (ons_edgeBit F
          (triangularTorusNortheastEdge L (p.1 - 1, p.2))) := by
      rw [ons_zeroFluxPotential_vertical_boundary_of_zeroHomology
        L E hE hEhom]
    _ = _ := by
      rw [triangularSquareExpansion_verticalBit,
        zmodFinEquiv_two_apply]
      let a : ZMod 2 := ons_edgeBit F (triangularTorusNorthEdge L p)
      let d : ZMod 2 := ons_edgeBit F
        (triangularTorusNortheastEdge L (p.1 - 1, p.2))
      change a + d + d = a
      calc
        _ = a + (d + d) := by abel
        _ = a := by rw [CharTwo.add_self_eq_zero, add_zero]

theorem triangularZeroHomology_diagonalCoeff_cast
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) :
    (triangularFaceDiagonalCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p : ZMod 2) =
      ons_edgeBit F (triangularTorusNortheastEdge L p) := by
  rw [triangularFaceDiagonalCoeff_cast_mod_two]
  unfold triangularZeroHomologyLowerPotential
  calc
    _ = (triangularZeroHomologyUpperPotential L F p +
        triangularZeroHomologyUpperPotential L F p) +
      (ZMod.finEquiv 2)
        (ons_edgeBit F (triangularTorusNortheastEdge L p)) := by abel
    _ = _ := by
      rw [CharTwo.add_self_eq_zero, zero_add,
        zmodFinEquiv_two_apply]

theorem triangularZeroHomology_eastCoeff_eq_zero_of_not_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L)
    (hnot : triangularTorusEastEdge L p ∉ F) :
    triangularFaceEastCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p = 0 := by
  apply triangularFaceEastCoeff_eq_zero_of_cast_eq_zero
  rw [triangularZeroHomology_eastCoeff_cast L F hF hhom]
  simp [ons_edgeBit, hnot]
  rfl

theorem triangularZeroHomology_northCoeff_eq_zero_of_not_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L)
    (hnot : triangularTorusNorthEdge L p ∉ F) :
    triangularFaceNorthCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p = 0 := by
  apply triangularFaceNorthCoeff_eq_zero_of_cast_eq_zero
  rw [triangularZeroHomology_northCoeff_cast L F hF hhom]
  simp [ons_edgeBit, hnot]
  rfl

theorem triangularZeroHomology_diagonalCoeff_eq_zero_of_not_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L)
    (hnot : triangularTorusNortheastEdge L p ∉ F) :
    triangularFaceDiagonalCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p = 0 := by
  apply triangularFaceDiagonalCoeff_eq_zero_of_cast_eq_zero
  rw [triangularZeroHomology_diagonalCoeff_cast]
  simp [ons_edgeBit, hnot]
  rfl

theorem triangularZeroHomology_eastCoeff_ne_zero_of_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L)
    (hmem : triangularTorusEastEdge L p ∈ F) :
    triangularFaceEastCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p ≠ 0 := by
  intro hz
  have hcast : (triangularFaceEastCoeff
      (triangularZeroHomologyLowerPotential L F)
      (triangularZeroHomologyUpperPotential L F) p : ZMod 2) = 0 := by
    rw [hz]
    rfl
  rw [triangularZeroHomology_eastCoeff_cast L F hF hhom] at hcast
  rw [ons_edgeBit, if_pos hmem] at hcast
  exact one_ne_zero hcast

theorem triangularZeroHomology_northCoeff_ne_zero_of_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (p : ZMod L × ZMod L)
    (hmem : triangularTorusNorthEdge L p ∈ F) :
    triangularFaceNorthCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p ≠ 0 := by
  intro hz
  have hcast : (triangularFaceNorthCoeff
      (triangularZeroHomologyLowerPotential L F)
      (triangularZeroHomologyUpperPotential L F) p : ZMod 2) = 0 := by
    rw [hz]
    rfl
  rw [triangularZeroHomology_northCoeff_cast L F hF hhom] at hcast
  rw [ons_edgeBit, if_pos hmem] at hcast
  exact one_ne_zero hcast

theorem triangularZeroHomology_diagonalCoeff_ne_zero_of_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L)
    (hmem : triangularTorusNortheastEdge L p ∈ F) :
    triangularFaceDiagonalCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) p ≠ 0 := by
  intro hz
  have hcast : (triangularFaceDiagonalCoeff
      (triangularZeroHomologyLowerPotential L F)
      (triangularZeroHomologyUpperPotential L F) p : ZMod 2) = 0 := by
    rw [hz]
    rfl
  rw [triangularZeroHomology_diagonalCoeff_cast] at hcast
  rw [ons_edgeBit, if_pos hmem] at hcast
  exact one_ne_zero hcast

end StatMech.FrontierA
