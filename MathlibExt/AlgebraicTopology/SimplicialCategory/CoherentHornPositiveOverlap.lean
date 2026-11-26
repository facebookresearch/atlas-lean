/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornShortComposition
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentDoubleFaceProjections

/-!
# Actual agreement of the two positive Hom-box pieces

The genuine triple-Hom chart gives the two original interval projections.
The supplied horn's short-leg composition laws and actual enriched
associativity prove agreement on the entire original intersection.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornPositiveOverlap
open SimplicialEnrichment HornBoxFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (b c : Interior.{u} n) (hbc : b.val ≤ c.val)

include hbc in
/-- The two constructed positive maps agree on the actual original double positive face. -/
theorem agreement :
    DoubleFaceProjections.first (ULift.up.{u} (0 : Fin (n + 3))) b.val c.val (ULift.up.{u} (Fin.last (n + 2))) ≫
        positiveMap f hi₀ hiₙ b =
      DoubleFaceProjections.second (ULift.up.{u} (0 : Fin (n + 3))) b.val c.val (ULift.up.{u} (Fin.last (n + 2))) ≫
        positiveMap f hi₀ hiₙ c := by
  let X := nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3))) b.val)
  let Y := nerve (SimplicialThickening.Path b.val c.val)
  let Z := nerve (SimplicialThickening.Path c.val (ULift.up.{u} (Fin.last (n + 2))))
  let A := HornFaces.object f 0
  let B := HornFaces.object f (HornBoxFaces.vertex b)
  let C' := HornFaces.object f (HornBoxFaces.vertex c)
  let D := HornFaces.object f (Fin.last (n + 2))
  let L := leftMap f hi₀ hiₙ b
  let M := HornMiddleMap.firstMap f hi₀ b c
  let R := rightMap f hi₀ hiₙ c
  let E := DoubleCompositionFace.faceIso (ULift.up.{u} (0 : Fin (n + 3))) b.val c.val
    (ULift.up.{u} (Fin.last (n + 2))) hbc
  apply (cancel_epi E.hom).mp
  have h₁ : E.hom ≫
      (DoubleFaceProjections.first (ULift.up.{u} (0 : Fin (n + 3))) b.val c.val (ULift.up.{u} (Fin.last (n + 2))) ≫
        positiveMap f hi₀ hiₙ b) =
      (X ◁ CompositionFace.composition b.val c.val (ULift.up.{u} (Fin.last (n + 2)))) ≫
        (L ⊗ₘ rightMap f hi₀ hiₙ b) ≫ eComp SSet.{u} A B D := by
    rw [← Category.assoc, DoubleFaceProjections.first_chart, Category.assoc, positiveMap_readback]
  have h₂ : E.hom ≫
      (DoubleFaceProjections.second (ULift.up.{u} (0 : Fin (n + 3))) b.val c.val (ULift.up.{u} (Fin.last (n + 2))) ≫
        positiveMap f hi₀ hiₙ c) =
      (α_ X Y Z).inv ≫ CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 3))) b.val c.val ▷ Z ≫
        (leftMap f hi₀ hiₙ c ⊗ₘ R) ≫ eComp SSet.{u} A C' D := by
    rw [← Category.assoc, DoubleFaceProjections.second_chart, Category.assoc, Category.assoc, positiveMap_readback]
  have hL : (X ◁ CompositionFace.composition b.val c.val (ULift.up.{u} (Fin.last (n + 2)))) ≫
        (L ⊗ₘ rightMap f hi₀ hiₙ b) ≫ eComp SSet.{u} A B D =
      (L ⊗ₘ (M ⊗ₘ R)) ≫ ((A ⟶[SSet.{u}] B) ◁ eComp SSet.{u} B C' D) ≫ eComp SSet.{u} A B D := by
    rw [← Category.assoc, whiskerLeft_comp_tensorHom, HornShortComposition.right_comp f hi₀ hiₙ b c]
    rw [← tensorHom_comp_whiskerLeft, Category.assoc]
  have hR : (α_ X Y Z).inv ≫ CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 3))) b.val c.val ▷ Z ≫
        (leftMap f hi₀ hiₙ c ⊗ₘ R) ≫ eComp SSet.{u} A C' D =
      (L ⊗ₘ (M ⊗ₘ R)) ≫ ((A ⟶[SSet.{u}] B) ◁ eComp SSet.{u} B C' D) ≫ eComp SSet.{u} A B D := by
    rw [← Category.assoc _ (leftMap f hi₀ hiₙ c ⊗ₘ R), whiskerRight_comp_tensorHom,
      HornShortComposition.left_comp f hi₀ hiₙ b c]
    rw [← tensorHom_comp_whiskerRight]
    have hA : (α_ X Y Z).inv ≫ ((L ⊗ₘ M) ⊗ₘ R) =
        (L ⊗ₘ (M ⊗ₘ R)) ≫ (α_ (A ⟶[SSet.{u}] B) (B ⟶[SSet.{u}] C') (C' ⟶[SSet.{u}] D)).inv :=
      (associator_inv_naturality L M R).symm
    have hN := congrArg (fun g => (g ≫ eComp SSet.{u} A B C' ▷ (C' ⟶[SSet.{u}] D)) ≫ eComp SSet.{u} A C' D) hA
    have hP := congrArg (fun g => (L ⊗ₘ (M ⊗ₘ R)) ≫ g) (e_assoc SSet.{u} A B C' D)
    have hQ : (((L ⊗ₘ (M ⊗ₘ R)) ≫
        (α_ (A ⟶[SSet.{u}] B) (B ⟶[SSet.{u}] C') (C' ⟶[SSet.{u}] D)).inv) ≫
          eComp SSet.{u} A B C' ▷ (C' ⟶[SSet.{u}] D)) ≫ eComp SSet.{u} A C' D =
        (L ⊗ₘ (M ⊗ₘ R)) ≫ ((A ⟶[SSet.{u}] B) ◁ eComp SSet.{u} B C' D) ≫ eComp SSet.{u} A B D := by
      simpa only [Category.assoc] using hP
    simpa only [Category.assoc] using hN.trans hQ
  exact h₁.trans (hL.trans (hR.symm.trans h₂.symm))

end CategoryTheory.CoherentRealization.HornPositiveOverlap
