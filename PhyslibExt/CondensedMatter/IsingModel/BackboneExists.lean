/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import PhyslibExt.CondensedMatter.IsingModel.TwoReplica
public import PhyslibExt.CondensedMatter.IsingModel.TwoReplicaWeighted

/-!
# Backbones of random currents

Existence of a backbone between two sites connected to a common site through odd edges, and its
effect on sources and weights when sub-currents are reflected along it.

## i. Overview

For a current `m` on an edge set `E`, if `o` is joined to `x` and to `y` through the edges of odd
multiplicity, the symmetric difference of the two connecting edge sets is a set `P` of odd edges
with boundary `{x, y}`. Reflecting a sub-current `n ≤ m` along such a `P` changes its sources by
`{x, y}` and preserves the product of the weights of `n` and `m - n`; this is the step used in the
switching lemma.

All results here are proved unconditionally (no `Prop` hypotheses beyond connectivity of the odd
edges and distinctness of the sites). The backbone chain rule (P2) does not appear.

## ii. Key results

- `StatMech.Ising.bbe_backbone_exists` : a set of odd edges with boundary `{x, y}`
- `StatMech.Ising.bbe_backbone_exists_toggle` : the same, together with the source and weight
  identities for reflection along it

## iii. Table of contents

- A. Existence of a backbone
- B. Reflection along a backbone

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48
- H. Duminil-Copin, "Random currents expansion of the Ising model", lecture notes (2016),
  arXiv:1607.06933
-/

@[expose] public section

open Finset
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (Sym2 V))

/-! ## A. Existence of a backbone -/

/-- A set of odd edges with boundary `{o, x}` when `o ≠ x` are joined through odd edges. -/
lemma bbe_backbone_path (m : Current V) {o x : V} (hox : o ≠ x)
    (hconn : connP (oddEdges E m) o x) :
    ∃ P₁ ⊆ oddEdges E m, srcP P₁ = ({o, x} : Finset V) :=
  exists_conn_set (oddEdges E m) hconn hox

/-- **Backbone existence.** If `o` is joined to distinct sites `x` and `y` through the odd edges of
`m`, there is a set `P` of odd edges of `m` whose boundary (odd-degree sites) is `{x, y}`. -/
theorem bbe_backbone_exists (m : Current V) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hconnx : connP (oddEdges E m) o x) (hconny : connP (oddEdges E m) o y) :
    ∃ P ⊆ oddEdges E m, srcP P = ({x, y} : Finset V)
      ∧ (∀ e ∈ P, Odd (m e)) := by
  obtain ⟨P₁, hP₁sub, hP₁src⟩ := bbe_backbone_path E m hox hconnx
  obtain ⟨P₂, hP₂sub, hP₂src⟩ := bbe_backbone_path E m hoy hconny
  refine ⟨P₁ ∆ P₂, ?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_symmDiff] at he
    rcases he with ⟨h, _⟩ | ⟨h, _⟩
    · exact hP₁sub h
    · exact hP₂sub h
  · rw [srcP_symmDiff, hP₁src, hP₂src]
    ext z
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h, hn⟩ | ⟨h, hn⟩)
      · rcases h with rfl | rfl
        · exact absurd (Or.inl rfl) hn
        · exact Or.inl rfl
      · rcases h with rfl | rfl
        · exact absurd (Or.inl rfl) hn
        · exact Or.inr rfl
    · rintro (rfl | rfl)
      · left; exact ⟨Or.inr rfl, by rintro (h | h); exacts [hox h.symm, hxy h]⟩
      · right; exact ⟨Or.inr rfl, by rintro (h | h); exacts [hoy h.symm, hxy h.symm]⟩
  · intro e he
    have heod : e ∈ oddEdges E m := by
      rw [Finset.mem_symmDiff] at he
      rcases he with ⟨h, _⟩ | ⟨h, _⟩
      · exact hP₁sub h
      · exact hP₂sub h
    rw [oddEdges, Finset.mem_filter] at heod
    exact heod.2

/-! ## B. Reflection along a backbone -/

/-- Reflecting a sub-current along a set of odd edges with boundary `{x, y}` changes its sources by
`{x, y}`. -/
lemma bbe_backbone_toggle_disconnects (m : Current V) (P : Finset (Sym2 V))
    (hPE : P ⊆ E) (hPodd : ∀ e ∈ P, Odd (m e)) {x y : V}
    (hPsrc : srcP P = ({x, y} : Finset V))
    (n : Current V) (hn : ∀ e, n e ≤ m e) :
    sources E (reflect m P n) = sources E n ∆ ({x, y} : Finset V) := by
  rw [sources_reflect E m P n hn hPE hPodd, hPsrc]

/-- Backbone existence together with its reflection identities: a set `P` of odd edges with boundary
`{x, y}`, such that reflecting any sub-current `n ≤ m` along `P` changes its sources by `{x, y}` and
preserves `w(n) w(m - n)`. -/
theorem bbe_backbone_exists_toggle (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hconnx : connP (oddEdges G.edgeFinset m) o x)
    (hconny : connP (oddEdges G.edgeFinset m) o y) :
    ∃ P ⊆ oddEdges G.edgeFinset m,
        srcP P = ({x, y} : Finset V) ∧ (∀ e ∈ P, Odd (m e))
        ∧ (∀ n : Current V, (∀ e, n e ≤ m e) →
            Sharpness.sources G (reflect m P n)
              = Sharpness.sources G n ∆ ({x, y} : Finset V))
        ∧ (∀ n : Current V, (∀ e, n e ≤ m e) →
            Sharpness.weight G β J (reflect m P n)
                * Sharpness.weight G β J (fun e => m e - reflect m P n e)
              = Sharpness.weight G β J n * Sharpness.weight G β J (fun e => m e - n e)) := by
  obtain ⟨P, hPsub, hPsrc, hPodd⟩ :=
    bbe_backbone_exists G.edgeFinset m hox hoy hxy hconnx hconny
  have hPE : P ⊆ G.edgeFinset := hPsub.trans (oddEdges_subset G.edgeFinset m)
  refine ⟨P, hPsub, hPsrc, hPodd, ?_, ?_⟩
  · intro n hn
    have hsrc : Sharpness.sources G (reflect m P n)
        = Sharpness.sources G n ∆ srcP P :=
      sources_reflect (V := V) G.edgeFinset m P n hn hPE hPodd
    rw [hsrc, hPsrc]
  · intro n hn
    exact weight_reflect_split_eq G β J m P hn

end Ising

end StatMech

