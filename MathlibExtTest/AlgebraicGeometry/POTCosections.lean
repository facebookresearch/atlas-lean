/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.POTCosections

@[expose] public noncomputable section

open MathlibExt.AlgebraicGeometry.AffineConeAtlas
open MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
open MathlibExt.AlgebraicGeometry.POTCosections

namespace POTCosectionsTest

variable {B : Type} [CommRing B] [Algebra ℂ B] {P : Algebra.Extension.{0} ℂ B}
  (F : ConePresentation P)

/-- The cosection is evaluation of an obstruction class at the cycle vector. -/
example (s : Cosection F) (a : (Fin F.negativeRank → B) →ₗ[B] B) :
    obstructionCosection F s
      ((LinearMap.range (dualDifferential (presentationModel F) B)).mkQ a) = a s.vector :=
  obstructionCosection_mk F s a

/-- The zero cosection. -/
def zeroCosection : Cosection F := ⟨0, map_zero _⟩

/-- The zero cosection degenerates everywhere: its degeneracy ideal is zero. -/
example : degeneracyIdeal F (zeroCosection F) = ⊥ := by
  simp [degeneracyIdeal, zeroCosection]

/-- The zero cosection kills every obstruction class. -/
example (a : ObstructionModule (presentationModel F) B) :
    obstructionCosection F (zeroCosection F) a = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ a
  rw [obstructionCosection_mk]
  exact map_zero a

/-- A cosection with a unit coordinate is nowhere degenerate. -/
example (s : Cosection F) (i : Fin F.negativeRank) (h : IsUnit (s.vector i)) :
    degeneracyIdeal F s = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) h

/-- Cosections are additive: the degeneracy ideal of a sum lies in the sum of
the degeneracy ideals. -/
example (s t : Cosection F) :
    degeneracyIdeal F ⟨s.vector + t.vector, by rw [map_add, s.cycle, t.cycle, add_zero]⟩ ≤
      degeneracyIdeal F s ⊔ degeneracyIdeal F t := by
  rw [degeneracyIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
    (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))

end POTCosectionsTest
