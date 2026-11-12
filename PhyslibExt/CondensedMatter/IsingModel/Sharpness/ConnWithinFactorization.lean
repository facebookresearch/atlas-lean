/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Exploration
public import MathlibExt.Probability.Percolation.ConnectionsInsideSet

/-!
# Factorization of connections within a set

Connections inside a finite set `S` of `ℤ^d` are independent of events depending only on edges with
an endpoint outside `S`.

## i. Overview

The event that `o` and `x` are connected inside `S` depends only on the edges with both endpoints in
`S` (`withinConnEvent`, `edgesWithinFinset` from `DctDifferentialFull`). Under the Bernoulli product
measure it is therefore independent of any event determined by edges with an endpoint outside `S`.

## ii. Key results

- `internalEdges` : edges with both endpoints in a set
- `shp_internalEdgesFinset_disjoint` : such edges are disjoint from edges leaving `S`
- `shp_pivotal_factor` : the factorization

## iii. Table of contents

- A. Internal edges
- B. Factorization

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745

-/

@[expose] public section

open MeasureTheory Function Set
open scoped NNReal ENNReal

namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}

/-! ## A. Internal edges -/

/-- The edges of `ℤ^d` with both endpoints in `S`. -/
def internalEdges (S : Set (Site d)) : Set (Sym2 (Site d)) :=
  {e | ∃ x ∈ S, ∃ y ∈ S, e = s(x, y)}

lemma mem_internalEdges {S : Set (Site d)} {x y : Site d} (hx : x ∈ S) (hy : y ∈ S) :
    s(x, y) ∈ internalEdges S := ⟨x, hx, y, hy, rfl⟩

lemma internalEdgesFinset_coe (S : Finset (Site d)) :
    (edgesWithinFinset S : Set (Sym2 (Site d))) = internalEdges (S : Set _) := by
  ext e
  rw [Finset.mem_coe, mem_edgesWithinFinset]
  simp only [internalEdges, Set.mem_ofPred_eq, Finset.mem_coe]

lemma shp_internalEdges_disjoint {S : Set (Site d)} {U : Set (Sym2 (Site d))}
    (hU : ∀ e ∈ U, ∃ a b : Site d, e = s(a, b) ∧ (a ∉ S ∨ b ∉ S)) :
    Disjoint (internalEdges S) U := by
  rw [Set.disjoint_left]
  rintro e ⟨x, hx, y, hy, rfl⟩ heU
  obtain ⟨a, b, hab, hout⟩ := hU _ heU
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst ha <;> subst hb <;>
    rcases hout with h | h <;> exact h (by assumption)

lemma shp_internalEdgesFinset_disjoint {S : Finset (Site d)} {U : Finset (Sym2 (Site d))}
    (hU : ∀ e ∈ U, ∃ a b : Site d, e = s(a, b) ∧ (a ∉ S ∨ b ∉ S)) :
    Disjoint (edgesWithinFinset S) U := by
  rw [Finset.disjoint_left]
  intro e he heU
  rw [mem_edgesWithinFinset] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := he
  obtain ⟨a, b, hab, hout⟩ := hU _ heU
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst ha <;> subst hb <;>
    rcases hout with h | h <;> exact h (by assumption)

/-! ## B. Factorization -/

lemma shp_connWithin_transfer {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)}
    (hagree : ∀ e ∈ internalEdges S, ω e = ω' e)
    {a b : ↥S} (h : ConnectedWithin d ω S a b) : ConnectedWithin d ω' S a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v t hadj p ih =>
    have hopen : IsOpenEdge d ω (u : Site d) (v : Site d) := hadj
    obtain ⟨hadj0, hop⟩ := hopen
    have hopen' : IsOpenEdge d ω' (u : Site d) (v : Site d) := by
      refine ⟨hadj0, ?_⟩
      rw [← hagree _ ⟨(u : Site d), u.2, (v : Site d), v.2, rfl⟩]; exact hop
    exact (SimpleGraph.Adj.reachable
      (show (openSubgraphInduce d ω' S).Adj u v from hopen')).trans ih

lemma shp_connWithinEvent_congr {S : Set (Site d)} {o x : Site d}
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ internalEdges S, ω e = ω' e) :
    ω ∈ withinConnEvent d S o x ↔ ω' ∈ withinConnEvent d S o x := by
  constructor
  · rintro ⟨ho, hx, hc⟩; exact ⟨ho, hx, shp_connWithin_transfer hagree hc⟩
  · rintro ⟨ho, hx, hc⟩
    exact ⟨ho, hx, shp_connWithin_transfer (fun e he => (hagree e he).symm) hc⟩

lemma shp_pivotal_factor (p : ℝ≥0) (hp : p ≤ 1)
    (S : Finset (Site d)) (o x : Site d)
    (B : Set (ConfigSpace (Sym2 (Site d)))) (U : Finset (Sym2 (Site d)))
    (hUext : ∀ e ∈ U, ∃ a b : Site d, e = s(a,
        b) ∧ (a ∉ (S : Set (Site d)) ∨ b ∉ (S : Set (Site d))))
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (withinConnEvent d (S : Set (Site d)) o x ∩ B)
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) o x)
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B :=
  withinConn_indep p hp S o x B U (shp_internalEdgesFinset_disjoint hUext) hB

end Sharpness

end StatMech
