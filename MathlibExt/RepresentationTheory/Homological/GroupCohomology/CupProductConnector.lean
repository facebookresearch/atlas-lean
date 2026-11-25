/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import MathlibExt.Algebra.Homology.CochainGradedPairingConnector
public import MathlibExt.CategoryTheory.Monoidal.PreservesColimits
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductNaturality

/-!
# Arbitrary-degree cup/connector compatibility in group cohomology

The arbitrary-degree Alexander--Whitney cup product satisfies both
one-sided compatibility laws with connecting morphisms.  A connector in the
right input contributes the Koszul sign `(-1)^p`; a connector in the left
input contributes no sign.  Exactness after tensoring is retained as an
explicit hypothesis.

## Main declarations

* `groupCohomology.cup_delta_right`
* `groupCohomology.cup_delta_left`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- Cupping with a connecting class in the right coefficient variable
commutes with the target connector with Koszul sign `(-1)^p`. -/
theorem cup_delta_right
    (A : Rep k G) (S : ShortComplex (Rep k G))
    (hS : S.ShortExact)
    (hAS : (S.map (tensorLeft A)).ShortExact)
    (p q : ℕ) :
    ((𝟙 (groupCohomology A p) ⊗ₘ δ hS q (q + 1) rfl) ≫
        cup G k A S.X₁ p (q + 1) ≫
        ((inhomogeneousCochains (A ⊗ S.X₁)).homologyIsoOfEq
          (show p + (q + 1) = p + q + 1 by omega)).hom) =
      ((-1 : ℤ) ^ p) •
        (cup G k A S.X₃ p q ≫
          δ hAS (p + q) (p + q + 1) rfl) := by
  set_option backward.isDefEq.respectTransparency false in
  apply HomologicalComplex.CochainGradedPairing.pairHomology_delta_right k
    (map_cochainsFunctor_shortExact hS)
    (map_cochainsFunctor_shortExact hAS)
    (inhomogeneousCupPairing G k A S.X₁)
    (inhomogeneousCupPairing G k A S.X₂)
    (inhomogeneousCupPairing G k A S.X₃)
  · intro i j
    simpa using inhomogeneousCupPairing_naturality
      (f := 𝟙 A) (g := S.f) i j
  · intro i j
    simpa using inhomogeneousCupPairing_naturality
      (f := 𝟙 A) (g := S.g) i j

/-- Cupping with a connecting class in the left coefficient variable
commutes with the target connector without an additional sign. -/
theorem cup_delta_left
    (B : Rep k G) (S : ShortComplex (Rep k G))
    (hS : S.ShortExact)
    (hSB : (S.map (tensorRight B)).ShortExact)
    (p q : ℕ) :
    ((δ hS p (p + 1) rfl ⊗ₘ 𝟙 (groupCohomology B q)) ≫
        cup G k S.X₁ B (p + 1) q ≫
        ((inhomogeneousCochains (S.X₁ ⊗ B)).homologyIsoOfEq
          (show (p + 1) + q = p + q + 1 by omega)).hom) =
      cup G k S.X₃ B p q ≫
        δ hSB (p + q) (p + q + 1) rfl := by
  set_option backward.isDefEq.respectTransparency false in
  apply HomologicalComplex.CochainGradedPairing.pairHomology_delta_left k
    (map_cochainsFunctor_shortExact hS)
    (map_cochainsFunctor_shortExact hSB)
    (inhomogeneousCupPairing G k S.X₁ B)
    (inhomogeneousCupPairing G k S.X₂ B)
    (inhomogeneousCupPairing G k S.X₃ B)
  · intro i j
    simpa using inhomogeneousCupPairing_naturality
      (f := S.f) (g := 𝟙 B) i j
  · intro i j
    simpa using inhomogeneousCupPairing_naturality
      (f := S.g) (g := 𝟙 B) i j

end groupCohomology
