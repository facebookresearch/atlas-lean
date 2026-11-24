/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.PrimeToEllAlterations

set_option autoImplicit false

/-! Tests for generic field maps, generic degrees and prime-to-`ell` alterations. -/

open AlgebraicGeometry CategoryTheory MathlibExt.AlgebraicGeometry.NormalCrossingsModels
  MathlibExt.AlgebraicGeometry.PrimeToEllAlterations

universe u

/-! ### Smooth proper models -/

-- The structure fields of a smooth proper model are found by instance inference.
example {k : Type u} [Field k] (M : SmoothProperModel k) : IsIntegral M.variety.left :=
  inferInstance

example {k : Type u} [Field k] (M : SmoothProperModel k) : Smooth M.variety.hom := inferInstance

example {k : Type u} [Field k] (M : SmoothProperModel k) : IsProper M.variety.hom := inferInstance

/-! ### Generic field maps and degrees -/

-- The generic field map of the identity is the identity, so the identity has generic degree one.
example {X : Scheme.{u}} [IsIntegral X] (h : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X) :
    genericFieldMap (𝟙 X) h = 𝟙 X.functionField := by
  simp

example {X : Scheme.{u}} [IsIntegral X] (h : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X) :
    genericDegree (𝟙 X) h = 1 := by
  simp

/-! ### Prime-to-`ell` degree -/

-- The degree condition is coprimality: for composite `ell` it is stronger than non-divisibility.
example : ¬ Nat.Coprime 6 4 ∧ ¬ 6 ∣ 4 := by decide

-- For prime `ell` it says that `ell` does not divide the generic degree.
example {k : Type u} [Field k] {X : Over (Spec (.of k))} [IsIntegral X.left]
    {D : X.left.IdealSheafData} {ell : ℕ} (hell : ell.Prime) (a : PrimeToEllAlteration X D ell) :
    ¬ ell ∣ genericDegree a.morphism.left a.genericPointMap :=
  (Nat.Prime.coprime_iff_not_dvd hell).mp a.coprimeDegree

/-! ### Alterations -/

-- An alteration is surjective.
example {k : Type u} [Field k] {X : Over (Spec (.of k))} [IsIntegral X.left]
    {D : X.left.IdealSheafData} {ell : ℕ} (a : PrimeToEllAlteration X D ell) :
    Function.Surjective a.morphism.left :=
  a.surjective

-- The identity of a smooth proper integral model, with empty boundary, is a prime-to-`ell`
-- alteration for every `ell`.
example {k : Type u} [Field k] (M : SmoothProperModel k) (ell : ℕ) :
    Nonempty (PrimeToEllAlteration M.variety (⊤ : M.variety.left.IdealSheafData) ell) := by
  have := LocallyOfFiniteType.isLocallyNoetherian M.variety.hom
  have hgp : (𝟙 M.variety.left : M.variety.left ⟶ M.variety.left)
      (genericPoint M.variety.left) = genericPoint M.variety.left := by simp
  refine ⟨{ source := M
            morphism := 𝟙 M.variety
            properMorphism := inferInstanceAs (IsProper (𝟙 M.variety.left))
            genericPointMap := hgp
            finiteField := ?_
            coprimeDegree := ?_
            crossings := isStrictNormalCrossings_of_support_eq_bot ?_ }⟩
  · change (genericFieldMap (𝟙 M.variety.left) hgp).hom.Finite
    rw [genericFieldMap_id, CommRingCat.hom_id]
    exact RingHom.Finite.id _
  · change Nat.Coprime ell (genericDegree (𝟙 M.variety.left) hgp)
    rw [genericDegree_id]
    exact Nat.coprime_one_right ell
  · ext y
    rw [reducedPullbackBoundary_support]
    simp
