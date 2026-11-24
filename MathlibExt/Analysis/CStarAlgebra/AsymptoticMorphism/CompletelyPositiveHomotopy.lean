/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositive
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Homotopy
public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.CodRestrict

/-!
# CPC witnesses for the existing matching-endpoint pair family

Compatible literal CPC homotopies determine a CPC family in the already
existing matching-path pullback.  The underlying asymptotic family is exactly
the ordinary `Homotopy.pairFamily`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace AsymptoticMorphism
namespace CompletelyPositiveContraction
namespace Homotopy

open ContinuousMap.IntervalGluing

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {phi psi chi : CompletelyPositiveContraction A B}

/-- The existing ordinary matching-endpoint pair family has a genuine CPC
witness at every finite time. -/
theorem pairFamily_isCompletelyPositiveContraction
    (H : Homotopy phi psi) (K : Homotopy psi chi) :
    IsCompletelyPositiveContraction
      (AsymptoticMorphism.Homotopy.pairFamily
        H.toAsymptoticHomotopy K.toAsymptoticHomotopy) := by
  let S : NonUnitalStarSubalgebra ℂ
      (C(unitInterval, B) × C(unitInterval, B)) :=
    NonUnitalCStarPullback.Pullback (evalAt B 1) (evalAt B 0)
  let _ : IsClosed (S : Set (C(unitInterval, B) × C(unitInterval, B))) :=
    NonUnitalCStarPullback.isClosed_pullback (evalAt B 1) (evalAt B 0)
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let _ : PartialOrder C(unitInterval, B) :=
    CStarAlgebra.spectralOrder C(unitInterval, B)
  let _ : StarOrderedRing C(unitInterval, B) :=
    CStarAlgebra.spectralOrderedRing C(unitInterval, B)
  let _ : PartialOrder (C(unitInterval, B) × C(unitInterval, B)) :=
    CStarAlgebra.spectralOrder (C(unitInterval, B) × C(unitInterval, B))
  let _ : StarOrderedRing (C(unitInterval, B) × C(unitInterval, B)) :=
    CStarAlgebra.spectralOrderedRing
      (C(unitInterval, B) × C(unitInterval, B))
  let _ : PartialOrder S := CStarAlgebra.spectralOrder S
  let _ : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  have hH := H.family.completelyPositiveContraction
  have hK := K.family.completelyPositiveContraction
  dsimp only [IsCompletelyPositiveContraction] at hH hK ⊢
  intro t
  obtain ⟨f, hfNorm, hfValue⟩ := hH t
  obtain ⟨g, hgNorm, hgValue⟩ := hK t
  let fg : CompletelyPositiveMap.Canonical A
      (C(unitInterval, B) × C(unitInterval, B)) :=
    CompletelyPositiveMap.prod f g
  have hfgNorm : ∀ a : A, ‖fg a‖ ≤ ‖a‖ := fun a =>
    CompletelyPositiveMap.norm_prod_apply_le f g hfNorm hgNorm a
  have hmem : ∀ a : A, fg a ∈ S := by
    intro a
    change f a 1 = g a 0
    rw [hfValue a, hgValue a, H.finish t a, K.start t a]
  let restricted : CompletelyPositiveMap.Canonical A S :=
    CompletelyPositiveMap.Canonical.codRestrictClosed fg S hmem
  refine ⟨restricted, ?_, ?_⟩
  · intro a
    exact CompletelyPositiveMap.Canonical.norm_codRestrictClosed_apply_le
      fg S hmem hfgNorm a
  · intro a
    apply Subtype.ext
    change ((restricted a : S) :
      C(unitInterval, B) × C(unitInterval, B)) =
      ((AsymptoticMorphism.Homotopy.pairFamily
        H.toAsymptoticHomotopy K.toAsymptoticHomotopy t a : MatchingPaths B) :
          C(unitInterval, B) × C(unitInterval, B))
    rw [CompletelyPositiveMap.Canonical.codRestrictClosed_apply,
      CompletelyPositiveMap.prod_apply, hfValue a, hgValue a,
      AsymptoticMorphism.Homotopy.pairFamily_val]
    rfl

/-- Package the CPC witness without changing the existing ordinary pair
family. -/
noncomputable def matchingPairFamily
    (H : Homotopy phi psi) (K : Homotopy psi chi) :
    CompletelyPositiveContraction A (MatchingPaths B) where
  toAsymptoticMorphism :=
    AsymptoticMorphism.Homotopy.pairFamily
      H.toAsymptoticHomotopy K.toAsymptoticHomotopy
  completelyPositiveContraction :=
    pairFamily_isCompletelyPositiveContraction H K

/-- Forgetting the CPC witness returns exactly the established ordinary
matching-endpoint pair family. -/
@[simp]
theorem matchingPairFamily_toAsymptoticMorphism
    (H : Homotopy phi psi) (K : Homotopy psi chi) :
    (matchingPairFamily H K).toAsymptoticMorphism =
      AsymptoticMorphism.Homotopy.pairFamily
        H.toAsymptoticHomotopy K.toAsymptoticHomotopy :=
  rfl

/-- The CPC pair family has the literal two path coordinates of `H` and `K`. -/
theorem matchingPairFamily_val
    (H : Homotopy phi psi) (K : Homotopy psi chi)
    (t : AsymptoticTime) (a : A) :
    (((matchingPairFamily H K).toAsymptoticMorphism t a : MatchingPaths B) :
      C(unitInterval, B) × C(unitInterval, B)) =
      (H.family.toAsymptoticMorphism t a,
        K.family.toAsymptoticMorphism t a) :=
  AsymptoticMorphism.Homotopy.pairFamily_val
    H.toAsymptoticHomotopy K.toAsymptoticHomotopy t a

end Homotopy
end CompletelyPositiveContraction
end AsymptoticMorphism
