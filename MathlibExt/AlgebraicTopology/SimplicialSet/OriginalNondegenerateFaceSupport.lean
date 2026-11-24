/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Original nondegenerate face supports

The finite support of the literal original face deletes exactly its omitted
vertex. The support and simplex maps are Mathlib's standard-simplex APIs.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.stdSimplex.OriginalFaceSupport

/-- The original face of a nondegenerate standard simplex is nondegenerate. -/
theorem nonDegenerate_face {n d : ℕ}
    (x : (Δ[n] : SSet.{u}).nonDegenerate (d + 1)) (i : Fin (d + 2)) :
    (Δ[n] : SSet.{u}).δ i x.val ∈ (Δ[n] : SSet.{u}).nonDegenerate d := by
  apply (stdSimplex.mem_nonDegenerate_iff_strictMono _).2
  exact ((stdSimplex.mem_nonDegenerate_iff_strictMono _).1 x.property).comp
    (Fin.succAboveOrderEmb i).strictMono

/-- The full original nondegenerate face, with its literal simplex map. -/
noncomputable def face {n d : ℕ}
    (x : (Δ[n] : SSet.{u}).nonDegenerate (d + 1)) (i : Fin (d + 2)) :
    (Δ[n] : SSet.{u}).nonDegenerate d :=
  ⟨(Δ[n] : SSet.{u}).δ i x.val, nonDegenerate_face x i⟩

/-- Deleting the original ordinal vertex deletes precisely its support value. -/
theorem support_face {n d : ℕ}
    (x : (Δ[n] : SSet.{u}).nonDegenerate (d + 1)) (i : Fin (d + 2)) :
    (stdSimplex.nonDegenerateEquiv' (face x i)).val =
      (stdSimplex.nonDegenerateEquiv' x).val.erase (x.val i) := by
  classical
  have hx : Function.Injective x.val :=
    ((stdSimplex.mem_nonDegenerate_iff_strictMono _).1 x.property).injective
  ext j
  rw [stdSimplex.nonDegenerateEquiv'_iff, Finset.mem_erase,
    stdSimplex.nonDegenerateEquiv'_iff]
  constructor
  · rintro ⟨r, hr⟩
    change x.val (i.succAbove r) = j at hr
    refine ⟨?_, ⟨i.succAbove r, hr⟩⟩
    intro hj
    exact Fin.succAbove_ne i r (hx (hr.trans hj))
  · rintro ⟨hj, r, hr⟩
    have hri : r ≠ i := by
      intro h
      subst r
      exact hj hr.symm
    obtain ⟨s, hs⟩ := Fin.exists_succAbove_eq hri
    refine ⟨s, ?_⟩
    change x.val (i.succAbove s) = j
    rw [hs]
    exact hr

end SSet.stdSimplex.OriginalFaceSupport
