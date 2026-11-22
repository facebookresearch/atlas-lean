/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeEdge
import Mathlib.Tactic.FinCases

/-!
# Every original edge of the coherent one-simplex cone

The cone at zero has its two original subset vertices and the one
nonidentity coefficient edge. The cone at one has its original single
vertex. Thus every cone edge is either already maximum-marked or is
the exact original coefficient edge. These finite statements retain
all coefficient universes and the actual whole edge functors.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

attribute [local instance] vertexDecidableEq

/-- A whole cone subset at original vertex zero is precisely the singleton or the full original pair. -/
theorem ConeSubset.zero_cases (a : ConeSubset (zeroOne.{u})) :
    a = coefficientSource ∨ a = coefficientTarget := by
  classical
  have h0 : ULift.up (0 : Fin 2) ∈ a.vertices := a.mem
  by_cases h1 : ULift.up (1 : Fin 2) ∈ a.vertices
  · right
    apply ConeSubset.ext
    ext j
    cases j with
    | up j => fin_cases j <;> simp [coefficientTarget, zeroOne, h0, h1]
  · left
    apply ConeSubset.ext
    ext j
    cases j with
    | up j => fin_cases j <;> simp [coefficientSource, zeroOne, h0, h1]

/-- The whole cone subset at original vertex one retains exactly that single vertex. -/
theorem ConeSubset.one_vertices (a : ConeSubset (ULift.up.{u} (1 : Fin 2))) :
    a.vertices = {ULift.up (1 : Fin 2)} := by
  classical
  have h1 : ULift.up (1 : Fin 2) ∈ a.vertices := a.mem
  have h0 : ULift.up (0 : Fin 2) ∉ a.vertices := by
    intro h
    have hl : (1 : Fin 2) ≤ 0 := a.lower _ h
    exact (by decide : ¬ (1 : Fin 2) ≤ 0) hl
  ext j
  cases j with
  | up j => fin_cases j <;> simp [h0, h1]

/-- The original full pair cannot include into the original singleton source. -/
theorem coefficientTarget_not_le_source : ¬ coefficientTarget.{u} ≤ coefficientSource := by
  intro h
  have h1 : ULift.up (1 : Fin 2) ∈ coefficientTarget.{u}.vertices := by
    simp [coefficientTarget]
  have hs := h h1
  simp [coefficientSource, zeroOne] at hs

/-- Every whole edge at zero is already maximum-marked or is precisely the original nonidentity coefficient edge. -/
theorem coneWeight_zeroOne_edge (e : (nerve (ConeSubset (zeroOne.{u}))) _⦋1⦌) :
    e ∈ (coneWeight zeroOne).marking ∨ e = coefficientEdge := by
  rcases (e.obj 0).zero_cases with hs | hs <;> rcases (e.obj 1).zero_cases with ht | ht
  · left
    exact congrArg ConeSubset.maximum (hs.trans ht.symm)
  · right
    refine CategoryTheory.Functor.ext (fun k => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    fin_cases k
    · exact hs
    · exact ht
  · let f : coefficientTarget ⟶ coefficientSource :=
      eqToHom hs.symm ≫ e.map (homOfLE (show (0 : Fin 2) ≤ 1 by decide)) ≫ eqToHom ht
    exact False.elim (coefficientTarget_not_le_source (leOfHom f))
  · left
    exact congrArg ConeSubset.maximum (hs.trans ht.symm)

/-- Every original cone edge at vertex one is already marked by its constant maximum. -/
theorem coneWeight_one_marked (e : (nerve (ConeSubset (ULift.up.{u} (1 : Fin 2)))) _⦋1⦌) :
    e ∈ (coneWeight (ULift.up (1 : Fin 2))).marking :=
  congrArg ConeSubset.maximum (ConeSubset.ext ((e.obj 0).one_vertices.trans (e.obj 1).one_vertices.symm))

end SSet.Marked.CoherentWeight
