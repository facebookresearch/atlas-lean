/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.TurningTelescope
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.Torus
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.TrivalentCycles

/-!

# The trivalent decoration of the torus

Each torus site replaced by a path of four darts, and the bijection between even subgraphs of the
torus and of the decorated graph.

## i. Overview

The decorated graph `ons_decGraph L` has the `4L²` darts of the torus as vertices. Each dart is
joined to its reverse (an external edge, one for each torus edge), and the four darts at a site are
joined in a path `(s, 0) - (s, 1) - (s, 2) - (s, 3)` (internal edges). Every vertex has degree at
most `3`. An even subgraph of the torus is determined by its port pattern, the set of darts whose
underlying edge it uses, which has an even number of darts at each site. Conversely, at each site
there is exactly one way to choose internal edges so that a port pattern becomes an even subgraph of
the decorated graph. This gives bijections between even subgraphs of the torus, port patterns, and
even subgraphs of the decorated graph, so the Kac-Ward argument for trivalent graphs applies to the
square lattice.

## ii. Key results

- `ons_decGraph` : the decorated graph on darts
- `ons_decGraph_degree_le_three` : it has maximal degree `3`
- `ons_PortPattern` : port patterns: reversal-invariant dart bits, even at each site
- `ons_decChain_existsUnique` : the unique even completion of a port pattern at one site
- `ons_decorationEquiv` : even subgraphs of the torus correspond to even subgraphs of the decorated
  graph
- `ons_decorated_evenSubgraph_cycle_decomposition` : the decorated even subgraphs are disjoint
  unions of cycles

## iii. Table of contents

- A. The decorated graph
- B. Completing a site
- C. Port patterns
- D. Parity sums at a vertex
- E. From torus subgraphs to port patterns
- F. From decorated subgraphs to port patterns
- G. The bijections

## iv. References

- M. E. Fisher, *On the dimer solution of planar Ising models*, J. Math. Phys. 7 (1966) 1776-1781
- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337

-/

@[expose] public section

namespace StatMech.Onsager

open Finset SimpleGraph
open StatMech.Ising

/-! ## A. The decorated graph -/

/-- Internal adjacency of the decoration: two darts at the same site whose directions are
consecutive in `0, 1, 2, 3`. -/
def ons_decInternalAdj {L : ℕ} (d e : ons_Dart L) : Prop :=
  d.1 = e.1 ∧ (d.2.val + 1 = e.2.val ∨ e.2.val + 1 = d.2.val)

/-- Adjacency of the decorated graph: a dart is joined to its reverse and to its internal neighbors.
-/
def ons_decAdj (L : ℕ) (d e : ons_Dart L) : Prop :=
  e = ons_dartRev L d ∨ ons_decInternalAdj d e

/-- Decidability of decorated adjacency. -/
instance (L : ℕ) : DecidableRel (ons_decAdj L) := by
  intro d e
  unfold ons_decAdj ons_decInternalAdj
  infer_instance

lemma ons_decAdj_symm (L : ℕ) : Symmetric (ons_decAdj L) := by
  intro d e h
  rcases h with hrev | hint
  · left
    rw [hrev, ons_dartRev_involutive]
  · right
    exact ⟨hint.1.symm, hint.2.symm⟩

lemma ons_dartRev_ne_self (L : ℕ) (d : ons_Dart L) :
    ons_dartRev L d ≠ d := by
  intro h
  have hdir := congrArg Prod.snd h
  rcases d with ⟨s, mu⟩
  simp only [ons_dartRev] at hdir
  fin_cases mu <;> simp at hdir

/-- The decorated graph of the torus: vertices are darts, external edges join each dart to its
reverse, and internal edges form the path `(s, 0) - (s, 1) - (s, 2) - (s, 3)` at each site `s`. -/
def ons_decGraph (L : ℕ) : SimpleGraph (ons_Dart L) where
  Adj := ons_decAdj L
  symm := ⟨fun _ _ h => ons_decAdj_symm L h⟩
  loopless := by
    refine ⟨?_⟩
    intro d hd
    rcases hd with hrev | hint
    · exact ons_dartRev_ne_self L d hrev.symm
    · rcases hint.2 with h | h <;> omega

/-- Decidable adjacency of the decorated graph. -/
instance (L : ℕ) : DecidableRel (ons_decGraph L).Adj :=
  inferInstanceAs (DecidableRel (ons_decAdj L))

/-- The internal neighbors of a dart in the path at its site. -/
def ons_decInternalNeighbors {L : ℕ} (d : ons_Dart L) : Finset (ons_Dart L) :=
  match d.2 with
  | 0 => {(d.1, 1)}
  | 1 => {(d.1, 0), (d.1, 2)}
  | 2 => {(d.1, 1), (d.1, 3)}
  | 3 => {(d.1, 2)}

lemma ons_decGraph_neighborFinset (L : ℕ) [NeZero L] (d : ons_Dart L) :
    (ons_decGraph L).neighborFinset d =
      insert (ons_dartRev L d) (ons_decInternalNeighbors d) := by
  ext e
  rw [SimpleGraph.mem_neighborFinset]
  rcases d with ⟨s, mu⟩
  rcases e with ⟨t, nu⟩
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_decGraph, ons_decAdj, ons_decInternalAdj,
      ons_decInternalNeighbors, eq_comm]

lemma ons_decGraph_degree_le_three (L : ℕ) [NeZero L] (d : ons_Dart L) :
    (ons_decGraph L).degree d ≤ 3 := by
  change ((ons_decGraph L).neighborFinset d).card ≤ 3
  rw [ons_decGraph_neighborFinset]
  refine (Finset.card_insert_le _ _).trans ?_
  rcases d with ⟨s, mu⟩
  fin_cases mu <;> simp [ons_decInternalNeighbors]

/-! ## B. Completing a site -/

/-- The internal-edge bits `(b₀, b₀ + b₁, b₀ + b₁ + b₂)` that complete port bits `b₀, …, b₃` at one
site to an even subgraph. -/
def ons_decChainCompletion (b0 b1 b2 : Fin 2) : Fin 3 → Fin 2 :=
  ![b0, b0 + b1, b0 + b1 + b2]

/-- Parity of the decorated subgraph at the four darts of one site, for port bits `b₀, …, b₃` and
internal-edge bits `y`. -/
def ons_decChainEven (b0 b1 b2 b3 : Fin 2) (y : Fin 3 → Fin 2) : Prop :=
  b0 + y 0 = 0 ∧
  b1 + y 0 + y 1 = 0 ∧
  b2 + y 1 + y 2 = 0 ∧
  b3 + y 2 = 0

/-- Decidability of the local parity condition at a site. -/
instance (b0 b1 b2 b3 : Fin 2) (y : Fin 3 → Fin 2) :
    Decidable (ons_decChainEven b0 b1 b2 b3 y) := by
  unfold ons_decChainEven
  infer_instance

lemma ons_decChainCompletion_even_iff (b0 b1 b2 b3 : Fin 2) :
    ons_decChainEven b0 b1 b2 b3 (ons_decChainCompletion b0 b1 b2) ↔
      b0 + b1 + b2 + b3 = 0 := by
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> decide

@[simp] lemma ons_fin2_one_add_eq_zero_iff (x : Fin 2) :
    (1 : Fin 2) + x = 0 ↔ x = 1 := by
  fin_cases x <;> decide

lemma ons_decChain_eq_completion {b0 b1 b2 b3 : Fin 2} {y : Fin 3 → Fin 2}
    (heven : b0 + b1 + b2 + b3 = 0)
    (hy : ons_decChainEven b0 b1 b2 b3 y) :
    y = ons_decChainCompletion b0 b1 b2 := by
  funext k
  fin_cases k <;>
    fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    simp [ons_decChainEven, ons_decChainCompletion] at heven hy ⊢ <;> aesop

lemma ons_decChain_existsUnique (b0 b1 b2 b3 : Fin 2)
    (heven : b0 + b1 + b2 + b3 = 0) :
    ∃! y : Fin 3 → Fin 2, ons_decChainEven b0 b1 b2 b3 y := by
  refine ⟨ons_decChainCompletion b0 b1 b2,
    (ons_decChainCompletion_even_iff b0 b1 b2 b3).mpr heven, ?_⟩
  intro y hy
  exact ons_decChain_eq_completion heven hy

lemma ons_decChainEven_port_even {b0 b1 b2 b3 : Fin 2}
    {y : Fin 3 → Fin 2} (hy : ons_decChainEven b0 b1 b2 b3 y) :
    b0 + b1 + b2 + b3 = 0 := by
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    simp [ons_decChainEven] at hy ⊢ <;> aesop

/-! ## C. Port patterns -/

/-- A port pattern: one bit per dart, equal on a dart and its reverse, with an even number of ones
at each site. Port patterns encode even subgraphs of the torus. -/
structure ons_PortPattern (L : ℕ) where
  bit : ons_Dart L → Fin 2
  rev_bit : ∀ d, bit (ons_dartRev L d) = bit d
  site_even : ∀ s : ZMod L × ZMod L,
    bit (s, 0) + bit (s, 1) + bit (s, 2) + bit (s, 3) = 0

@[ext] lemma ons_PortPattern.ext {L : ℕ} {P Q : ons_PortPattern L}
    (h : P.bit = Q.bit) : P = Q := by
  cases P
  cases Q
  simp only [ons_PortPattern.mk.injEq]
  exact h

/-- The internal-edge bits at a site determined by a port pattern. -/
def ons_portChainBit {L : ℕ} (P : ons_PortPattern L)
    (s : ZMod L × ZMod L) : Fin 3 → Fin 2 :=
  ons_decChainCompletion (P.bit (s, 0)) (P.bit (s, 1)) (P.bit (s, 2))

/-- The bit of the decorated edge between `d` and `e` determined by a port pattern. -/
def ons_decNeighborBit {L : ℕ} (P : ons_PortPattern L)
    (d e : ons_Dart L) : Fin 2 :=
  if e = ons_dartRev L d then P.bit d else
    if d.1 = e.1 then
      match d.2, e.2 with
      | 0, 1 | 1, 0 => ons_portChainBit P d.1 0
      | 1, 2 | 2, 1 => ons_portChainBit P d.1 1
      | 2, 3 | 3, 2 => ons_portChainBit P d.1 2
      | _, _ => 0
    else 0

lemma ons_decNeighborBit_symm {L : ℕ} (P : ons_PortPattern L)
    (d e : ons_Dart L) :
    ons_decNeighborBit P d e = ons_decNeighborBit P e d := by
  by_cases hrev : e = ons_dartRev L d
  · subst e
    have hinv : ons_dartRev L (ons_dartRev L d) = d :=
      ons_dartRev_involutive L d
    rw [ons_decNeighborBit, ite_eq_left rfl, ons_decNeighborBit,
      ite_eq_left hinv.symm, P.rev_bit]
  · have hrev' : d ≠ ons_dartRev L e := by
      intro h
      apply hrev
      rw [h, ons_dartRev_involutive]
    rw [ons_decNeighborBit, ite_eq_right hrev, ons_decNeighborBit, ite_eq_right hrev']
    by_cases hs : d.1 = e.1
    · rw [ite_eq_left hs, ite_eq_left hs.symm]
      rcases d with ⟨s, mu⟩
      rcases e with ⟨t, nu⟩
      simp only at hs
      subst t
      fin_cases mu <;> fin_cases nu <;> rfl
    · rw [ite_eq_right hs, ite_eq_right (Ne.symm hs)]

/-- The bit of a decorated edge determined by a port pattern. -/
def ons_decEdgeBit {L : ℕ} (P : ons_PortPattern L) :
    Sym2 (ons_Dart L) → Fin 2 :=
  Sym2.lift ⟨ons_decNeighborBit P, ons_decNeighborBit_symm P⟩

@[simp] lemma ons_decEdgeBit_mk {L : ℕ} (P : ons_PortPattern L)
    (d e : ons_Dart L) :
    ons_decEdgeBit P s(d, e) = ons_decNeighborBit P d e := rfl

/-- The even subgraph of the decorated graph determined by a port pattern. -/
noncomputable def ons_decoratedEdges {L : ℕ} [NeZero L]
    (P : ons_PortPattern L) : Finset (Sym2 (ons_Dart L)) :=
  (ons_decGraph L).edgeFinset.filter (fun e => ons_decEdgeBit P e = 1)

/-! ## D. Parity sums at a vertex -/

lemma ons_incidenceFinset_eq_image_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    H.incidenceFinset v = (H.neighborFinset v).image (fun w => s(v, w)) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      simp only [SimpleGraph.mem_incidenceFinset,
        SimpleGraph.mk'_mem_incidenceSet_iff, Finset.mem_image,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hab, rfl | rfl⟩
        · exact ⟨b, hab, rfl⟩
        · exact ⟨a, hab.symm, Sym2.eq_swap⟩
      · rintro ⟨w, hvw, heq⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨hva, hwb⟩ | ⟨hvb, hwa⟩
        · subst a
          subst b
          exact ⟨hvw, Or.inl rfl⟩
        · subst a
          subst b
          exact ⟨hvw.symm, Or.inr rfl⟩

lemma ons_neighborEdge_injective
    {V : Type*} [DecidableEq V] (H : SimpleGraph V) (v : V) :
    Set.InjOn (fun w => s(v, w)) (H.neighborSet v) := by
  intro a ha b hb heq
  rw [Sym2.eq_iff] at heq
  rcases heq with h | h
  · exact h.2
  · exfalso
    have hva : H.Adj v a := ha
    rw [h.2] at hva
    exact H.loopless.irrefl v hva

lemma ons_incCount_filter_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (Q : Sym2 V → Prop) [DecidablePred Q] (v : V) :
    incCount (H.edgeFinset.filter Q) v =
      ((H.incidenceFinset v).filter Q).card := by
  unfold incCount
  rw [SimpleGraph.incidenceFinset_eq_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  tauto

lemma ons_cast_incCount_filter_eq_neighbor_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (Q : Sym2 V → Prop) [DecidablePred Q] (v : V) :
    ((incCount (H.edgeFinset.filter Q) v : ℕ) : ZMod 2) =
      ∑ w ∈ H.neighborFinset v,
        if Q s(v, w) then (1 : ZMod 2) else 0 := by
  rw [ons_incCount_filter_edgeFinset, Finset.natCast_card_filter,
    ons_incidenceFinset_eq_image_neighborFinset, Finset.sum_image]
  intro a ha b hb hab
  apply ons_neighborEdge_injective H v
  · exact (SimpleGraph.mem_neighborFinset H v a).mp ha
  · exact (SimpleGraph.mem_neighborFinset H v b).mp hb
  · exact hab

lemma ons_evenSubgraph_neighbor_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (F : Finset (Sym2 V)) (hF : F ∈ evenSubgraphs H) (v : V) :
    ∑ w ∈ H.neighborFinset v,
      (if s(v, w) ∈ F then (1 : ZMod 2) else 0) = 0 := by
  have hdata := hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  have hFeq : F = H.edgeFinset.filter (fun e => e ∈ F) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · intro he
      exact ⟨hdata.1 he, he⟩
    · exact And.right
  have hcast : ((incCount F v : ℕ) : ZMod 2) = 0 := by
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr
    exact even_iff_two_dvd.mp (hdata.2 v)
  have hsum := ons_cast_incCount_filter_eq_neighbor_sum H (fun e => e ∈ F) v
  rw [← hFeq, hcast] at hsum
  exact hsum.symm

@[simp] lemma ons_fin2_indicator_eq (a : Fin 2) :
    (if a = 1 then (1 : Fin 2) else 0) = a := by
  fin_cases a <;> decide

lemma ons_dirStep_ne_self (L : ℕ) [Fact (2 < L)]
    (mu : Fin 4) (s : ZMod L × ZMod L) :
    ons_dirStep L mu s ≠ s := by
  have : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
  fin_cases mu <;> simp [ons_dirStep, Prod.ext_iff, h1]

lemma ons_decInternalNeighbors_site {L : ℕ} {d e : ons_Dart L}
    (he : e ∈ ons_decInternalNeighbors d) : e.1 = d.1 := by
  rcases d with ⟨s, mu⟩
  fin_cases mu <;> simp [ons_decInternalNeighbors] at he <;>
    rcases he with rfl | rfl <;> rfl

lemma ons_dartRev_not_mem_internalNeighbors (L : ℕ) [Fact (2 < L)]
    (d : ons_Dart L) :
    ons_dartRev L d ∉ ons_decInternalNeighbors d := by
  intro h
  have hsite : (ons_dartRev L d).1 = d.1 := ons_decInternalNeighbors_site h
  exact ons_dirStep_ne_self L d.2 d.1 hsite

lemma ons_decNeighborBit_sum_zero (L : ℕ) [Fact (2 < L)]
    (P : ons_PortPattern L) (d : ons_Dart L) :
    ∑ e ∈ (ons_decGraph L).neighborFinset d, ons_decNeighborBit P d e = 0 := by
  rw [ons_decGraph_neighborFinset,
    Finset.sum_insert (ons_dartRev_not_mem_internalNeighbors L d)]
  have hchain := (ons_decChainCompletion_even_iff
    (P.bit (d.1, 0)) (P.bit (d.1, 1))
    (P.bit (d.1, 2)) (P.bit (d.1, 3))).mpr (P.site_even d.1)
  unfold ons_decChainEven at hchain
  rcases d with ⟨s, mu⟩
  fin_cases mu
  · simpa [ons_decNeighborBit, ons_decInternalNeighbors, ons_portChainBit,
      ons_dartRev] using hchain.1
  · simpa [ons_decNeighborBit, ons_decInternalNeighbors, ons_portChainBit,
      ons_dartRev, add_assoc] using hchain.2.1
  · simpa [ons_decNeighborBit, ons_decInternalNeighbors, ons_portChainBit,
      ons_dartRev, add_assoc] using hchain.2.2.1
  · simpa [ons_decNeighborBit, ons_decInternalNeighbors, ons_portChainBit,
      ons_dartRev] using hchain.2.2.2

/-! ## E. From torus subgraphs to port patterns -/

/-- The torus edge underlying a dart. -/
def ons_portEdge (L : ℕ) (d : ons_Dart L) : Sym2 (ZMod L × ZMod L) :=
  s(d.1, ons_dirStep L d.2 d.1)

lemma ons_portEdge_rev (L : ℕ) (d : ons_Dart L) :
    ons_portEdge L (ons_dartRev L d) = ons_portEdge L d := by
  rcases d with ⟨s, mu⟩
  simp only [ons_portEdge, ons_dartRev]
  rw [ons_dirStep_opposite]
  exact Sym2.eq_swap

lemma ons_torus_neighborFinset_steps (L : ℕ) [Fact (2 < L)]
    (v : ZMod L × ZMod L) :
    (onsTorusGraph L).neighborFinset v =
      {ons_dirStep L 0 v, ons_dirStep L 1 v,
        ons_dirStep L 2 v, ons_dirStep L 3 v} := by
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases v with ⟨vx, vy⟩
  rcases w with ⟨wx, wy⟩
  simp only [onsTorusGraph, onsTorusAdj]
  constructor
  · rintro (⟨hx, hy | hy⟩ | ⟨hy, hx | hx⟩)
    · right; right; right
      apply Prod.ext <;> simp [ons_dirStep, hx] <;> linear_combination -hy
    · right; left
      apply Prod.ext <;> simp [ons_dirStep, hx] <;> linear_combination -hy
    · right; right; left
      apply Prod.ext <;> simp [ons_dirStep, hy] <;> linear_combination -hx
    · left
      apply Prod.ext <;> simp [ons_dirStep, hy] <;> linear_combination -hx
  · rintro (h | h | h | h)
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [ons_dirStep] at hx hy
      exact Or.inr ⟨hy.symm, Or.inr (by linear_combination -hx)⟩
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [ons_dirStep] at hx hy
      exact Or.inl ⟨hx.symm, Or.inr (by linear_combination -hy)⟩
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [ons_dirStep] at hx hy
      exact Or.inr ⟨hy.symm, Or.inl (by linear_combination -hx)⟩
    · have hx := congrArg Prod.fst h
      have hy := congrArg Prod.snd h
      simp only [ons_dirStep] at hx hy
      exact Or.inl ⟨hx.symm, Or.inl (by linear_combination -hy)⟩

lemma ons_dirStep_injective (L : ℕ) [Fact (2 < L)]
    (v : ZMod L × ZMod L) :
    Function.Injective (fun mu : Fin 4 => ons_dirStep L mu v) := by
  have : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have h1 : (1 : ZMod L) ≠ 0 := one_ne_zero
  have h2 : (2 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    have := (Fact.out : 2 < L)
    omega
  intro mu nu h
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_dirStep, Prod.ext_iff, h1] at h ⊢ <;>
    try {exfalso; apply h2; linear_combination h} <;>
    try {exfalso; apply h2; linear_combination -h}

lemma ons_torus_neighbor_sum_eq_direction_sum (L : ℕ) [Fact (2 < L)]
    (v : ZMod L × ZMod L) (f : (ZMod L × ZMod L) → ZMod 2) :
    ∑ w ∈ (onsTorusGraph L).neighborFinset v, f w =
      ∑ mu : Fin 4, f (ons_dirStep L mu v) := by
  rw [ons_torus_neighborFinset_steps]
  have hset : ({ons_dirStep L 0 v, ons_dirStep L 1 v,
      ons_dirStep L 2 v, ons_dirStep L 3 v} : Finset (ZMod L × ZMod L)) =
      Finset.univ.image (fun mu : Fin 4 => ons_dirStep L mu v) := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · rintro ⟨mu, rfl⟩
      fin_cases mu <;> simp
  rw [hset, Finset.sum_image (fun _ _ _ _ h => ons_dirStep_injective L v h)]

/-- The bit of a dart in the port pattern of an edge set `F`: `1` if its underlying torus edge lies
in `F`. -/
def ons_portBit {L : ℕ} (F : Finset (Sym2 (ZMod L × ZMod L)))
    (d : ons_Dart L) : Fin 2 :=
  if ons_portEdge L d ∈ F then 1 else 0

/-- The port pattern of an even subgraph of the torus. -/
noncomputable def ons_evenSubgraphPortPattern (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L)) : ons_PortPattern L where
  bit := ons_portBit F
  rev_bit := by
    intro d
    simp only [ons_portBit, ons_portEdge_rev]
  site_even := by
    intro v
    have hdata := hF
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
    have hFeq : F = (onsTorusGraph L).edgeFinset.filter (fun e => e ∈ F) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · intro he
        exact ⟨hdata.1 he, he⟩
      · exact And.right
    have hcast : ((incCount F v : ℕ) : ZMod 2) = 0 := by
      apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr
      exact even_iff_two_dvd.mp (hdata.2 v)
    have hsum := ons_cast_incCount_filter_eq_neighbor_sum
      (onsTorusGraph L) (fun e => e ∈ F) v
    rw [← hFeq, hcast] at hsum
    rw [ons_torus_neighbor_sum_eq_direction_sum] at hsum
    simp only [ons_portBit]
    replace hsum := hsum.symm
    simp only [ons_portEdge, Fin.sum_univ_four, add_assoc] at hsum ⊢
    exact hsum

/-! ## F. From decorated subgraphs to port patterns -/

/-- The port bit of a dart in a decorated edge set: whether the external edge at the dart is
present. -/
def ons_decoratedPortBit {L : ℕ}
    (D : Finset (Sym2 (ons_Dart L))) (d : ons_Dart L) : Fin 2 :=
  if s(d, ons_dartRev L d) ∈ D then 1 else 0

/-- The three internal-edge bits of a decorated edge set at one site. -/
def ons_decoratedChainBits {L : ℕ}
    (D : Finset (Sym2 (ons_Dart L))) (s : ZMod L × ZMod L) :
    Fin 3 → Fin 2 :=
  ![if s((s, 0), (s, 1)) ∈ D then 1 else 0,
    if s((s, 1), (s, 2)) ∈ D then 1 else 0,
    if s((s, 2), (s, 3)) ∈ D then 1 else 0]

lemma ons_decorated_local_even (L : ℕ) [Fact (2 < L)]
    (D : Finset (Sym2 (ons_Dart L)))
    (hD : D ∈ evenSubgraphs (ons_decGraph L))
    (s : ZMod L × ZMod L) :
    ons_decChainEven
      (ons_decoratedPortBit D (s, 0)) (ons_decoratedPortBit D (s, 1))
      (ons_decoratedPortBit D (s, 2)) (ons_decoratedPortBit D (s, 3))
      (ons_decoratedChainBits D s) := by
  have h0 := ons_evenSubgraph_neighbor_sum_zero
    (ons_decGraph L) D hD (s, (0 : Fin 4))
  have h1 := ons_evenSubgraph_neighbor_sum_zero
    (ons_decGraph L) D hD (s, (1 : Fin 4))
  have h2 := ons_evenSubgraph_neighbor_sum_zero
    (ons_decGraph L) D hD (s, (2 : Fin 4))
  have h3 := ons_evenSubgraph_neighbor_sum_zero
    (ons_decGraph L) D hD (s, (3 : Fin 4))
  rw [ons_decGraph_neighborFinset,
    Finset.sum_insert (ons_dartRev_not_mem_internalNeighbors L (s, (0 : Fin 4)))] at h0
  rw [ons_decGraph_neighborFinset,
    Finset.sum_insert (ons_dartRev_not_mem_internalNeighbors L (s, (1 : Fin 4)))] at h1
  rw [ons_decGraph_neighborFinset,
    Finset.sum_insert (ons_dartRev_not_mem_internalNeighbors L (s, (2 : Fin 4)))] at h2
  rw [ons_decGraph_neighborFinset,
    Finset.sum_insert (ons_dartRev_not_mem_internalNeighbors L (s, (3 : Fin 4)))] at h3
  rw [show ons_decInternalNeighbors (s, (0 : Fin 4)) = {(s, (1 : Fin 4))} from rfl,
    Finset.sum_singleton] at h0
  rw [show ons_decInternalNeighbors (s, (1 : Fin 4)) =
      {(s, (0 : Fin 4)), (s, (2 : Fin 4))} from rfl,
    Finset.sum_insert (by simp), Finset.sum_singleton] at h1
  rw [show ons_decInternalNeighbors (s, (2 : Fin 4)) =
      {(s, (1 : Fin 4)), (s, (3 : Fin 4))} from rfl,
    Finset.sum_insert (by simp), Finset.sum_singleton] at h2
  rw [show ons_decInternalNeighbors (s, (3 : Fin 4)) = {(s, (2 : Fin 4))} from rfl,
    Finset.sum_singleton] at h3
  rw [show s((s, (1 : Fin 4)), (s, (0 : Fin 4))) =
      s((s, (0 : Fin 4)), (s, (1 : Fin 4))) from Sym2.eq_swap] at h1
  rw [show s((s, (2 : Fin 4)), (s, (1 : Fin 4))) =
      s((s, (1 : Fin 4)), (s, (2 : Fin 4))) from Sym2.eq_swap] at h2
  rw [show s((s, (3 : Fin 4)), (s, (2 : Fin 4))) =
      s((s, (2 : Fin 4)), (s, (3 : Fin 4))) from Sym2.eq_swap] at h3
  unfold ons_decChainEven
  constructor
  · simp [ons_decoratedPortBit, ons_decoratedChainBits] at h0 ⊢
    exact h0
  constructor
  · simp [ons_decoratedPortBit, ons_decoratedChainBits,
      add_assoc] at h1 ⊢
    exact h1
  constructor
  · simp [ons_decoratedPortBit, ons_decoratedChainBits,
      add_assoc] at h2 ⊢
    exact h2
  · simp [ons_decoratedPortBit, ons_decoratedChainBits] at h3 ⊢
    exact h3

/-- The port pattern of an even subgraph of the decorated graph. -/
noncomputable def ons_portPatternOfDecorated (L : ℕ) [Fact (2 < L)]
    (D : Finset (Sym2 (ons_Dart L)))
    (hD : D ∈ evenSubgraphs (ons_decGraph L)) : ons_PortPattern L where
  bit := ons_decoratedPortBit D
  rev_bit := by
    intro d
    have hinv : ons_dartRev L (ons_dartRev L d) = d :=
      ons_dartRev_involutive L d
    have hedge : s(ons_dartRev L d, ons_dartRev L (ons_dartRev L d)) =
        s(d, ons_dartRev L d) := by
      rw [hinv]
      exact Sym2.eq_swap
    simp only [ons_decoratedPortBit, hedge]
  site_even := by
    intro s
    exact ons_decChainEven_port_even (ons_decorated_local_even L D hD s)

lemma ons_decoratedChainBits_eq_completion (L : ℕ) [Fact (2 < L)]
    (D : Finset (Sym2 (ons_Dart L)))
    (hD : D ∈ evenSubgraphs (ons_decGraph L))
    (s : ZMod L × ZMod L) :
    ons_decoratedChainBits D s =
      ons_portChainBit (ons_portPatternOfDecorated L D hD) s := by
  apply ons_decChain_eq_completion
  · exact (ons_portPatternOfDecorated L D hD).site_even s
  · exact ons_decorated_local_even L D hD s

lemma ons_decoratedEdges_portPatternOfDecorated (L : ℕ) [Fact (2 < L)]
    (D : Finset (Sym2 (ons_Dart L)))
    (hD : D ∈ evenSubgraphs (ons_decGraph L)) :
    ons_decoratedEdges (ons_portPatternOfDecorated L D hD) = D := by
  have hdata := hD
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  ext edge
  induction edge using Sym2.inductionOn with
  | _ d e =>
      by_cases hedge : s(d, e) ∈ (ons_decGraph L).edgeFinset
      · have hadj : ons_decAdj L d e := by
          exact SimpleGraph.mem_edgeFinset.mp hedge
        rcases hadj with hrev | hint
        · subst e
          rw [ons_decoratedEdges, Finset.mem_filter, and_iff_right hedge,
            ons_decEdgeBit_mk, ons_decNeighborBit, ite_eq_left rfl]
          change ons_decoratedPortBit D d = 1 ↔
            s(d, ons_dartRev L d) ∈ D
          simp [ons_decoratedPortBit]
        · rcases d with ⟨s, mu⟩
          rcases e with ⟨t, nu⟩
          rcases hint with ⟨hsite, hdir⟩
          change s = t at hsite
          subst t
          have hne : (s, nu) ≠ ons_dartRev L (s, mu) := by
            intro h
            have hs := congrArg Prod.fst h
            exact ons_dirStep_ne_self L mu s hs.symm
          rw [ons_decoratedEdges, Finset.mem_filter, and_iff_right hedge,
            ons_decEdgeBit_mk, ons_decNeighborBit, ite_eq_right hne, ite_eq_left rfl]
          have hchain := ons_decoratedChainBits_eq_completion L D hD s
          have hc0 := congrFun hchain 0
          have hc1 := congrFun hchain 1
          have hc2 := congrFun hchain 2
          have hc0f :
              (if s((s, 0), (s, 1)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 0 := by
            simpa [ons_decoratedChainBits] using hc0
          have hc1f :
              (if s((s, 1), (s, 2)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 1 := by
            simpa [ons_decoratedChainBits] using hc1
          have hc2f :
              (if s((s, 2), (s, 3)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 2 := by
            simpa [ons_decoratedChainBits] using hc2
          have hc0r :
              (if s((s, 1), (s, 0)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 0 := by
            rw [show s((s, (1 : Fin 4)), (s, (0 : Fin 4))) =
              s((s, (0 : Fin 4)), (s, (1 : Fin 4))) from Sym2.eq_swap]
            exact hc0
          have hc1r :
              (if s((s, 2), (s, 1)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 1 := by
            rw [show s((s, (2 : Fin 4)), (s, (1 : Fin 4))) =
              s((s, (1 : Fin 4)), (s, (2 : Fin 4))) from Sym2.eq_swap]
            exact hc1
          have hc2r :
              (if s((s, 3), (s, 2)) ∈ D then (1 : Fin 2) else 0) =
                ons_portChainBit (ons_portPatternOfDecorated L D hD) s 2 := by
            rw [show s((s, (3 : Fin 4)), (s, (2 : Fin 4))) =
              s((s, (2 : Fin 4)), (s, (3 : Fin 4))) from Sym2.eq_swap]
            exact hc2
          have hind {p : Prop} [Decidable p] {a : Fin 2}
              (h : (if p then (1 : Fin 2) else 0) = a) : a = 1 ↔ p := by
            rw [← h]
            simp
          fin_cases mu <;> fin_cases nu <;>
            simp at hdir <;>
            first
            | exact hind hc0f
            | exact hind hc0r
            | exact hind hc1f
            | exact hind hc1r
            | exact hind hc2f
            | exact hind hc2r
      · have hnotD : s(d, e) ∉ D := fun he => hedge (hdata.1 he)
        simp [ons_decoratedEdges, hedge, hnotD]

/-! ## G. The bijections -/

@[simp] lemma ons_decEdgeBit_external {L : ℕ} (P : ons_PortPattern L)
    (d : ons_Dart L) :
    ons_decEdgeBit P s(d, ons_dartRev L d) = P.bit d := by
  rw [ons_decEdgeBit_mk, ons_decNeighborBit, ite_eq_left rfl]

lemma ons_decorated_external_mem_iff (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L)) (d : ons_Dart L) :
    s(d, ons_dartRev L d) ∈
        ons_decoratedEdges (ons_evenSubgraphPortPattern L F hF) ↔
      ons_portEdge L d ∈ F := by
  rw [ons_decoratedEdges, Finset.mem_filter]
  have hedge : s(d, ons_dartRev L d) ∈ (ons_decGraph L).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact Or.inl rfl
  rw [and_iff_right hedge, ons_decEdgeBit_external]
  change ons_portBit F d = 1 ↔ ons_portEdge L d ∈ F
  simp [ons_portBit]

lemma ons_decoratedEdges_even (L : ℕ) [Fact (2 < L)]
    (P : ons_PortPattern L) :
    ons_decoratedEdges P ∈ evenSubgraphs (ons_decGraph L) := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact Finset.filter_subset _ _
  · intro d
    apply even_iff_two_dvd.mpr
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp
    rw [ons_decoratedEdges]
    rw [ons_incCount_filter_edgeFinset]
    rw [Finset.natCast_card_filter]
    have hind : ∀ e : Sym2 (ons_Dart L),
        (if ons_decEdgeBit P e = 1 then (1 : ZMod 2) else 0) =
          @id (ZMod 2) (ons_decEdgeBit P e) := by
      intro e
      generalize heq : ons_decEdgeBit P e = a
      fin_cases a <;> simp_all <;> rfl
    simp_rw [hind]
    rw [ons_incidenceFinset_eq_image_neighborFinset]
    rw [Finset.sum_image]
    · simp only [ons_decEdgeBit_mk]
      exact ons_decNeighborBit_sum_zero L P d
    · intro a ha b hb hab
      apply ons_neighborEdge_injective (ons_decGraph L) d
      · exact (SimpleGraph.mem_neighborFinset (ons_decGraph L) d a).mp ha
      · exact (SimpleGraph.mem_neighborFinset (ons_decGraph L) d b).mp hb
      · exact hab

lemma ons_portEdge_mem_edgeFinset (L : ℕ) [Fact (2 < L)]
    (d : ons_Dart L) :
    ons_portEdge L d ∈ (onsTorusGraph L).edgeFinset := by
  rcases d with ⟨v, mu⟩
  rw [SimpleGraph.mem_edgeFinset]
  simp only [ons_portEdge]
  rw [SimpleGraph.mem_edgeSet]
  rw [← SimpleGraph.mem_neighborFinset, ons_torus_neighborFinset_steps]
  fin_cases mu <;> simp

lemma ons_portEdge_eq_iff (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L) :
    ons_portEdge L e = ons_portEdge L d ↔
      e = d ∨ e = ons_dartRev L d := by
  rcases d with ⟨u, mu⟩
  rcases e with ⟨v, nu⟩
  constructor
  · intro h
    simp only [ons_portEdge, Sym2.eq_iff] at h
    rcases h with ⟨hvu, hstep⟩ | ⟨hvstep, hstepu⟩
    · subst v
      have hmu : nu = mu := ons_dirStep_injective L u hstep
      subst nu
      exact Or.inl rfl
    · have hnu : nu = mu + 2 := by
        apply ons_dirStep_injective L v
        calc
          ons_dirStep L nu v = u := hstepu
          _ = ons_dirStep L (mu + 2) v := by
            rw [hvstep, ons_dirStep_opposite]
      right
      simp only [ons_dartRev, Prod.mk.injEq]
      exact ⟨hvstep, hnu⟩
  · intro h
    rcases h with h | h
    · cases h
      rfl
    · cases h
      exact ons_portEdge_rev L (u, mu)

/-- The torus edge set of a port pattern. -/
noncomputable def ons_portPatternEdges (L : ℕ) [NeZero L]
    (P : ons_PortPattern L) :
    Finset (Sym2 (ZMod L × ZMod L)) :=
  (Finset.univ.filter (fun d : ons_Dart L => P.bit d = 1)).image
    (ons_portEdge L)

lemma ons_portEdge_mem_portPatternEdges_iff (L : ℕ) [Fact (2 < L)]
    (P : ons_PortPattern L) (d : ons_Dart L) :
    ons_portEdge L d ∈ ons_portPatternEdges L P ↔ P.bit d = 1 := by
  rw [ons_portPatternEdges, Finset.mem_image]
  constructor
  · rintro ⟨e, he, hedge⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases (ons_portEdge_eq_iff L d e).mp hedge with rfl | rfl
    · exact he
    · simpa only [P.rev_bit] using he
  · intro hd
    exact ⟨d, by simp [hd], rfl⟩

lemma ons_torusEdge_eq_portEdge (L : ℕ) [Fact (2 < L)]
    {edge : Sym2 (ZMod L × ZMod L)}
    (hedge : edge ∈ (onsTorusGraph L).edgeFinset) :
    ∃ d : ons_Dart L, ons_portEdge L d = edge := by
  induction edge using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        ← SimpleGraph.mem_neighborFinset, ons_torus_neighborFinset_steps] at hedge
      simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
      rcases hedge with rfl | rfl | rfl | rfl
      · exact ⟨(u, 0), rfl⟩
      · exact ⟨(u, 1), rfl⟩
      · exact ⟨(u, 2), rfl⟩
      · exact ⟨(u, 3), rfl⟩

lemma ons_portPatternEdges_subset (L : ℕ) [Fact (2 < L)]
    (P : ons_PortPattern L) :
    ons_portPatternEdges L P ⊆ (onsTorusGraph L).edgeFinset := by
  intro edge hedge
  rw [ons_portPatternEdges, Finset.mem_image] at hedge
  rcases hedge with ⟨d, _, rfl⟩
  exact ons_portEdge_mem_edgeFinset L d

lemma ons_portPatternEdges_even (L : ℕ) [Fact (2 < L)]
    (P : ons_PortPattern L) :
    ons_portPatternEdges L P ∈ evenSubgraphs (onsTorusGraph L) := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact ons_portPatternEdges_subset L P
  · intro v
    apply even_iff_two_dvd.mpr
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp
    have hFeq : ons_portPatternEdges L P =
        (onsTorusGraph L).edgeFinset.filter
          (fun e => e ∈ ons_portPatternEdges L P) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · intro he
        exact ⟨ons_portPatternEdges_subset L P he, he⟩
      · exact And.right
    have hsum := ons_cast_incCount_filter_eq_neighbor_sum
      (onsTorusGraph L) (fun e => e ∈ ons_portPatternEdges L P) v
    rw [← hFeq, ons_torus_neighbor_sum_eq_direction_sum] at hsum
    have hind : ∀ mu : Fin 4,
        (if s(v, ons_dirStep L mu v) ∈ ons_portPatternEdges L P
          then (1 : ZMod 2) else 0) = @id (ZMod 2) (P.bit (v, mu)) := by
      intro mu
      change (if ons_portEdge L (v, mu) ∈ ons_portPatternEdges L P
        then (1 : Fin 2) else 0) = P.bit (v, mu)
      simp only [ons_portEdge_mem_portPatternEdges_iff]
      exact ons_fin2_indicator_eq _
    simp_rw [hind] at hsum
    rw [Fin.sum_univ_four] at hsum
    have hp : (P.bit (v, 0) : ZMod 2) + P.bit (v, 1) +
        P.bit (v, 2) + P.bit (v, 3) = 0 := by
      exact_mod_cast P.site_even v
    exact hsum.trans hp

lemma ons_portPatternEdges_evenSubgraphPortPattern
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
    ons_portPatternEdges L (ons_evenSubgraphPortPattern L F hF) = F := by
  ext edge
  constructor
  · intro hedge
    rw [ons_portPatternEdges, Finset.mem_image] at hedge
    rcases hedge with ⟨d, hd, rfl⟩
    rw [Finset.mem_filter] at hd
    simp only [Finset.mem_univ, true_and,
      ons_evenSubgraphPortPattern, ons_portBit] at hd
    split at hd
    · assumption
    · simp at hd
  · intro hedge
    have hdata := hF
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
    obtain ⟨d, hd⟩ := ons_torusEdge_eq_portEdge L (hdata.1 hedge)
    rw [← hd]
    rw [ons_portEdge_mem_portPatternEdges_iff]
    simp [ons_evenSubgraphPortPattern, ons_portBit, hd, hedge]

lemma ons_evenSubgraphPortPattern_portPatternEdges
    (L : ℕ) [Fact (2 < L)] (P : ons_PortPattern L) :
    ons_evenSubgraphPortPattern L (ons_portPatternEdges L P)
      (ons_portPatternEdges_even L P) = P := by
  apply ons_PortPattern.ext
  funext d
  simp [ons_evenSubgraphPortPattern, ons_portBit,
    ons_portEdge_mem_portPatternEdges_iff, ons_fin2_indicator_eq]

/-- Even subgraphs of the torus are equivalent to port patterns. -/
noncomputable def ons_evenSubgraphPortEquiv (L : ℕ) [Fact (2 < L)] :
    {F : Finset (Sym2 (ZMod L × ZMod L)) //
      F ∈ evenSubgraphs (onsTorusGraph L)} ≃ ons_PortPattern L where
  toFun F := ons_evenSubgraphPortPattern L F.1 F.2
  invFun P := ⟨ons_portPatternEdges L P, ons_portPatternEdges_even L P⟩
  left_inv F := Subtype.ext (ons_portPatternEdges_evenSubgraphPortPattern L F.1 F.2)
  right_inv P := ons_evenSubgraphPortPattern_portPatternEdges L P

lemma ons_portPatternOfDecorated_decoratedEdges
    (L : ℕ) [Fact (2 < L)] (P : ons_PortPattern L) :
    ons_portPatternOfDecorated L (ons_decoratedEdges P)
      (ons_decoratedEdges_even L P) = P := by
  apply ons_PortPattern.ext
  funext d
  have hedge : s(d, ons_dartRev L d) ∈ (ons_decGraph L).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact Or.inl rfl
  simp only [ons_portPatternOfDecorated, ons_decoratedPortBit,
    ons_decoratedEdges, Finset.mem_filter, hedge, true_and,
    ons_decEdgeBit_external, ons_fin2_indicator_eq]

/-- Even subgraphs of the decorated graph are equivalent to port patterns. -/
noncomputable def ons_decoratedPortEquiv (L : ℕ) [Fact (2 < L)] :
    {D : Finset (Sym2 (ons_Dart L)) //
      D ∈ evenSubgraphs (ons_decGraph L)} ≃ ons_PortPattern L where
  toFun D := ons_portPatternOfDecorated L D.1 D.2
  invFun P := ⟨ons_decoratedEdges P, ons_decoratedEdges_even L P⟩
  left_inv D := Subtype.ext (ons_decoratedEdges_portPatternOfDecorated L D.1 D.2)
  right_inv P := ons_portPatternOfDecorated_decoratedEdges L P

/-- Even subgraphs of the torus are equivalent to even subgraphs of the decorated graph. -/
noncomputable def ons_decorationEquiv (L : ℕ) [Fact (2 < L)] :
    {F : Finset (Sym2 (ZMod L × ZMod L)) //
      F ∈ evenSubgraphs (onsTorusGraph L)} ≃
    {D : Finset (Sym2 (ons_Dart L)) //
      D ∈ evenSubgraphs (ons_decGraph L)} :=
  (ons_evenSubgraphPortEquiv L).trans (ons_decoratedPortEquiv L).symm

lemma ons_decorated_evenSubgraph_cycle_decomposition
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ evenSubgraphs (onsTorusGraph L)) :
    let D := ons_decoratedEdges (ons_evenSubgraphPortPattern L F hF)
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (base : ι → ons_Dart L)
      (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)),
      (∀ i, (p i).IsCycle) ∧
      D = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).edges.toFinset) := by
  dsimp only
  obtain ⟨ι, hi, hdeci, base, p, hcycle, hcover, hedge, _⟩ :=
    ons_trivalent_even_cycle_decomposition (ons_decGraph L)
      (ons_decGraph_degree_le_three L)
      (ons_decoratedEdges (ons_evenSubgraphPortPattern L F hF))
      (ons_decoratedEdges_even L (ons_evenSubgraphPortPattern L F hF))
  exact ⟨ι, hi, hdeci, base, p, hcycle, hcover, hedge⟩

end StatMech.Onsager
