/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCoordinateBoundary
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex

/-!
# Original endpoint coordinates of relative root-boundary scalar cells

A whole original root simplex outside its actual coordinate boundary
changes every positive original coordinate. Monotonicity of its complete
subset word therefore excludes every positive coordinate at its original
first vertex and retains every coordinate at its original last vertex.
The same native relative nondegenerate index consequently supplies both
original maximum endpoints and genuine positive scalar dimension.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- Every positive original coordinate is absent from the actual first vertex of a whole original simplex outside
the coordinate boundary. -/
theorem coneRootCoordinateRelative_first_not_mem {n d : ℕ}
    (x : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (hx : x ∉ (coneCoordinateBoundary (⊥ : Vertex.{u} n)).obj (op ⦋d⦌))
    (k : Vertex.{u} n) (hk : ⊥ < k) : k ∉ (x.obj 0).vertices := by
  intro hmem
  apply hx
  apply (mem_coneCoordinateBoundary_iff (⊥ : Vertex.{u} n) x).mpr
  refine ⟨⟨k, hk⟩, true, fun t => ?_⟩
  constructor
  · intro _
    rfl
  · intro _
    have ht : x.obj 0 ≤ x.obj t :=
      leOfHom (x.map (homOfLE (show (⊥ : Vertex.{u} d) ≤ ULift.up t from bot_le)))
    exact ht hmem

/-- Every positive original coordinate belongs to the actual last vertex of the whole original scalar word outside
the coordinate boundary. -/
theorem coneRootCoordinateRelative_last_mem {n d : ℕ}
    (x : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (hx : x ∉ (coneCoordinateBoundary (⊥ : Vertex.{u} n)).obj (op ⦋d⦌))
    (k : Vertex.{u} n) (hk : ⊥ < k) : k ∈ (x.obj (Fin.last d)).vertices := by
  classical
  by_contra hmem
  apply hx
  apply (mem_coneCoordinateBoundary_iff (⊥ : Vertex.{u} n) x).mpr
  refine ⟨⟨k, hk⟩, false, fun t => ?_⟩
  constructor
  · intro htmem
    have ht : x.obj t ≤ x.obj (Fin.last d) :=
      leOfHom (x.map (homOfLE (show (ULift.up t : Vertex.{u} d) ≤ ⊤ from le_top)))
    exact (hmem (ht htmem)).elim
  · intro h
    cases h

/-- The actual first whole subset maximum of an original scalar cell outside its coordinate boundary is the
unchanged original root. -/
theorem coneRootCoordinateRelative_first_maximum {n d : ℕ}
    (x : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (hx : x ∉ (coneCoordinateBoundary (⊥ : Vertex.{u} n)).obj (op ⦋d⦌)) :
    (x.obj 0).maximum = (⊥ : Vertex.{u} n) := by
  classical
  by_contra h
  have hk : (⊥ : Vertex.{u} n) < (x.obj 0).maximum :=
    lt_of_le_of_ne bot_le (Ne.symm h)
  exact coneRootCoordinateRelative_first_not_mem x hx _ hk (x.obj 0).maximum_mem

/-- The actual final whole subset maximum is the unchanged original top ordinal vertex, using every original
coordinate of that same scalar word. -/
theorem coneRootCoordinateRelative_last_maximum {n d : ℕ}
    (x : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (hx : x ∉ (coneCoordinateBoundary (⊥ : Vertex.{u} n)).obj (op ⦋d⦌)) :
    (x.obj (Fin.last d)).maximum = (⊤ : Vertex.{u} n) := by
  classical
  have hmem : (⊤ : Vertex.{u} n) ∈ (x.obj (Fin.last d)).vertices := by
    by_cases ht : (⊤ : Vertex.{u} n) = ⊥
    · exact ht.symm ▸ (x.obj (Fin.last d)).mem
    · exact coneRootCoordinateRelative_last_mem x hx _ (lt_of_le_of_ne bot_le (Ne.symm ht))
  exact le_antisymm le_top ((x.obj (Fin.last d)).le_maximum _ hmem)

/-- A whole original relative coordinate scalar has genuinely positive dimension whenever the original root cube has
a positive coordinate. -/
theorem coneRootCoordinateRelative_positive_dimension {n d : ℕ} (hn : 0 < n)
    (x : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (hx : x ∉ (coneCoordinateBoundary (⊥ : Vertex.{u} n)).obj (op ⦋d⦌)) : 0 < d := by
  by_contra hd
  obtain rfl : d = 0 := Nat.eq_zero_of_not_pos hd
  have h : (⊥ : Vertex.{u} n) = (⊤ : Vertex.{u} n) :=
    (coneRootCoordinateRelative_first_maximum x hx).symm.trans
      (coneRootCoordinateRelative_last_maximum x hx)
  have hval := congrArg (fun v : Vertex.{u} n => v.down.val) h
  change 0 = n at hval
  omega

/-- Every original native relative nondegenerate root scalar retains both actual original maximum endpoints without
any supplied endpoint certificate. -/
theorem coneRootCoordinateRelative_native_maxima {n : ℕ}
    (s : (coneCoordinateBoundary (⊥ : Vertex.{u} n)).N) :
    (s.simplex.obj 0).maximum = (⊥ : Vertex.{u} n) ∧
      (s.simplex.obj (Fin.last s.dim)).maximum = (⊤ : Vertex.{u} n) :=
  ⟨coneRootCoordinateRelative_first_maximum s.simplex s.notMem,
    coneRootCoordinateRelative_last_maximum s.simplex s.notMem⟩

/-- The same unchanged original native relative nondegenerate scalar index has positive actual dimension for every
original positive-dimensional root cube. -/
theorem coneRootCoordinateRelative_native_positive_dim {n : ℕ} (hn : 0 < n)
    (s : (coneCoordinateBoundary (⊥ : Vertex.{u} n)).N) : 0 < s.dim :=
  coneRootCoordinateRelative_positive_dimension hn s.simplex s.notMem

end SSet.Marked.CoherentWeight
