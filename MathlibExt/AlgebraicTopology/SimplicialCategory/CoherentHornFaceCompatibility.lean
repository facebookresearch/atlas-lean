/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornMixedOverlap
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornPositiveOverlap
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornNegativeIntersection
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornInteriorPreimages

/-!
# Actual compatibility of the whole coherent Hom-box face family

Every pair of the constructed original face maps agrees on its actual
intersection. The negative, positive and mixed cases use their original
whole charts. A coincident positive and negative label has an empty
intersection, including the literal smallest face cases.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornFaceCompatibility
open SimplicialEnrichment HornBoxFaces

/-- The original first projection from the actual overlap of two subcomplexes. -/
def first {X : SSet.{u}} (A B : X.Subcomplex) : ((A ⊓ B : X.Subcomplex) : SSet.{u}) ⟶ A :=
  SSet.Subcomplex.homOfLE inf_le_left

/-- The original other projection from the same actual subcomplex overlap. -/
def second {X : SSet.{u}} (A B : X.Subcomplex) : ((A ⊓ B : X.Subcomplex) : SSet.{u}) ⟶ B :=
  SSet.Subcomplex.homOfLE inf_le_right

private theorem swap {X Y : SSet.{u}} (A B : X.Subcomplex) (fA : (A : SSet.{u}) ⟶ Y) (fB : (B : SSet.{u}) ⟶ Y)
    (h : first A B ≫ fA = second A B ≫ fB) : first B A ≫ fB = second B A ≫ fA := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro p
  let p' : ((A ⊓ B : X.Subcomplex) : SSet.{u}).obj q := ⟨p.val, p.property.2, p.property.1⟩
  have h' := congrArg (fun g : ((A ⊓ B : X.Subcomplex) : SSet.{u}) ⟶ Y => (g.app q) p') h
  exact h'.symm

variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))

private theorem mixed_of_middle (k : Interior.{u} n) (t : HornInteriorFace.SourceInterior n)
    (b : Interior.{u} n) (hb : HornInteriorFace.middle k t = b) (hk : HornBoxFaces.vertex k ≠ i) :
    first (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))))
        (CompositionFace.positive (ULift.up 0) b.val (ULift.up (Fin.last (n + 2)))) ≫ negativeMap f k hk =
      second (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))))
        (CompositionFace.positive (ULift.up 0) b.val (ULift.up (Fin.last (n + 2)))) ≫ positiveMap f hi₀ hiₙ b := by
  subst b
  exact HornMixedOverlap.agreement f hi₀ hiₙ k t hk

private theorem mixed (k b : Interior.{u} n) (hk : HornBoxFaces.vertex k ≠ i) :
    first (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))))
        (CompositionFace.positive (ULift.up 0) b.val (ULift.up (Fin.last (n + 2)))) ≫ negativeMap f k hk =
      second (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))))
        (CompositionFace.positive (ULift.up 0) b.val (ULift.up (Fin.last (n + 2)))) ≫ positiveMap f hi₀ hiₙ b := by
  classical
  by_cases h : HornBoxFaces.vertex b = HornBoxFaces.vertex k
  · have hb : b = k := HornInteriorPreimages.label_injective h
    subst b
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    exact False.elim (p.property.1 0 (p.property.2 0))
  · exact mixed_of_middle f hi₀ hiₙ k (HornInteriorPreimages.preimage k b h) b
      (HornInteriorPreimages.middle_preimage k b h) hk

/-- The constructed actual face maps of the supplied horn agree on every whole original pairwise intersection. -/
theorem compatible (x y : Index.{u} i) :
    first (face i x) (face i y) ≫ maps f hi₀ hiₙ x = second (face i x) (face i y) ≫ maps f hi₀ hiₙ y := by
  classical
  rcases x with b | k <;> rcases y with c | l
  · by_cases h : b.val ≤ c.val
    · exact HornPositiveOverlap.agreement f hi₀ hiₙ b c h
    · exact swap _ _ _ _ (HornPositiveOverlap.agreement f hi₀ hiₙ c b (le_of_not_ge h))
  · exact swap _ _ _ _ (mixed f hi₀ hiₙ l.val b l.property)
  · exact mixed f hi₀ hiₙ k.val c k.property
  · rcases lt_trichotomy (HornBoxFaces.vertex k.val) (HornBoxFaces.vertex l.val) with h | h | h
    · exact HornNegativeIntersection.agreement k.val l.val h f k.property l.property
    · have hk : k = l := Subtype.ext (HornInteriorPreimages.label_injective h)
      subst l
      rfl
    · exact swap _ _ _ _ (HornNegativeIntersection.agreement l.val k.val h f l.property k.property)

end CategoryTheory.CoherentRealization.HornFaceCompatibility
