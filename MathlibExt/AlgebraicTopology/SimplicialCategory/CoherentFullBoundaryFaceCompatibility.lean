/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryNegativeCommon
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornFaceCompatibility

/-!
# Full original boundary Hom face compatibility

Every positive composition face and every negative omitted-vertex
face retains its same original full map. Pairwise agreement follows
from genuine original retaining-horn readbacks and the full boundary
common-face equation. The smallest same-label mixed overlap is empty.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryHomFaceCompatibility
open SimplicialEnrichment HornBoxFaces HornFaceCompatibility
variable {C : Carrier.{u}} {n : ℕ}
  (f : (∂Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- All same original positive and all same original negative boundary face labels. -/
abbrev Index (n : ℕ) := Interior.{u} n ⊕ Interior.{u} n

/-- The actual whole original boundary Hom face, preserving its positive or negative occurrence. -/
def face : Index.{u} n → (outerHom.{u} n).Subcomplex
  | .inl b => CompositionFace.positive (ULift.up 0) b.val (ULift.up (Fin.last (n+2)))
  | .inr k => HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n+2)))

/-- Every original full boundary face carries its same complete original Hom map. -/
def maps : (x : Index.{u} n) → (face x : SSet.{u}) ⟶
    (BoundaryFaces.object f 0 ⟶[SSet.{u}] BoundaryFaces.object f (Fin.last (n+2)))
  | .inl b => BoundaryHomFaces.positiveMap f b
  | .inr k => BoundaryHomFaces.negativeMap f k

private theorem positive (b c : Interior.{u} n) :
    first (face (.inl b)) (face (.inl c)) ≫ maps f (.inl b) =
      second (face (.inl b)) (face (.inl c)) ≫ maps f (.inl c) := by
  have h := compatible (BoundaryFaces.horn f BoundaryHomFaces.canonicalIndex)
    BoundaryHomFaces.canonicalIndex_ne_zero BoundaryHomFaces.canonicalIndex_ne_last
      (.inl b) (.inl c)
  change first (face (.inl b)) (face (.inl c)) ≫
    HornBoxFaces.positiveMap (BoundaryFaces.horn f BoundaryHomFaces.canonicalIndex)
      BoundaryHomFaces.canonicalIndex_ne_zero BoundaryHomFaces.canonicalIndex_ne_last b =
    second (face (.inl b)) (face (.inl c)) ≫
    HornBoxFaces.positiveMap (BoundaryFaces.horn f BoundaryHomFaces.canonicalIndex)
      BoundaryHomFaces.canonicalIndex_ne_zero BoundaryHomFaces.canonicalIndex_ne_last c at h
  simp only [BoundaryHomFaces.positiveMap_horn] at h
  change first (face (.inl b)) (face (.inl c)) ≫ BoundaryHomFaces.positiveMap f b =
    second (face (.inl b)) (face (.inl c)) ≫ BoundaryHomFaces.positiveMap f c at h
  exact h

private theorem negative (j k : Interior.{u} n)
    (hjk : HornBoxFaces.vertex j < HornBoxFaces.vertex k) :
    first (face (.inr j)) (face (.inr k)) ≫ maps f (.inr j) =
      second (face (.inr j)) (face (.inr k)) ≫ maps f (.inr k) := by
  apply (cancel_epi (HornNegativeIntersection.commonChart j k hjk).hom).mp
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ BoundaryHomFaces.negativeMap f j)
      (HornNegativeIntersection.first_chart j k hjk)).trans
      ((BoundaryNegativeCommon.agreement f j k hjk).trans
        ((congrArg (fun q => q ≫ BoundaryHomFaces.negativeMap f k)
          (HornNegativeIntersection.second_chart j k hjk).symm).trans (Category.assoc _ _ _))))

private theorem swap {X Y : SSet.{u}} (A B : X.Subcomplex) (a : (A : SSet.{u}) ⟶ Y)
    (b : (B : SSet.{u}) ⟶ Y) (h : first A B ≫ a = second A B ≫ b) :
    first B A ≫ b = second B A ≫ a := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro p
  let p' : ((A ⊓ B : X.Subcomplex) : SSet.{u}).obj q := ⟨p.val, p.property.2, p.property.1⟩
  exact (congrArg (fun g => (g.app q) p') h).symm

private theorem mixed (k b : Interior.{u} n) :
    first (face (.inr k)) (face (.inl b)) ≫ maps f (.inr k) =
      second (face (.inr k)) (face (.inl b)) ≫ maps f (.inl b) := by
  classical
  by_cases he : n = 0
  · subst n
    have hb : b = k := by
      apply Subtype.ext
      apply ULift.ext
      apply Fin.ext
      have hp := b.property
      have hq := k.property
      change 0 < b.val.down.val ∧ b.val.down.val < 2 at hp
      change 0 < k.val.down.val ∧ k.val.down.val < 2 at hq
      omega
    subst b
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    exact False.elim (p.property.1 0 (p.property.2 0))
  · let one : Fin (n+3) := ⟨1, by omega⟩
    let two : Fin (n+3) := ⟨2, by omega⟩
    let i : Fin (n+3) := if HornBoxFaces.vertex k = one then two else one
    have hi₀ : i ≠ 0 := by
      dsimp [i]
      split_ifs <;> intro h <;> have hv := congrArg Fin.val h
      · change 2 = 0 at hv
        omega
      · change 1 = 0 at hv
        omega
    have hiₙ : i ≠ Fin.last (n+2) := by
      dsimp [i]
      split_ifs <;> intro h <;> have hv := congrArg Fin.val h
      · change 2 = n+2 at hv
        omega
      · change 1 = n+2 at hv
        omega
    have hk : HornBoxFaces.vertex k ≠ i := by
      dsimp [i]
      split_ifs with h
      · rw [h]
        intro h12
        have hv := congrArg Fin.val h12
        change 1 = 2 at hv
        omega
      · exact h
    have h := compatible (BoundaryFaces.horn f i) hi₀ hiₙ (.inr ⟨k,hk⟩) (.inl b)
    change first (face (.inr k)) (face (.inl b)) ≫
      HornBoxFaces.negativeMap (BoundaryFaces.horn f i) k hk =
      second (face (.inr k)) (face (.inl b)) ≫
        HornBoxFaces.positiveMap (BoundaryFaces.horn f i) hi₀ hiₙ b at h
    simp only [BoundaryHomFaces.negativeMap_horn, BoundaryHomFaces.positiveMap_horn] at h
    change first (face (.inr k)) (face (.inl b)) ≫ BoundaryHomFaces.negativeMap f k =
      second (face (.inr k)) (face (.inl b)) ≫ BoundaryHomFaces.positiveMap f b at h
    exact h

/-- All complete original boundary Hom face maps agree on every same actual original intersection. -/
theorem compatible (x y : Index.{u} n) :
    first (face x) (face y) ≫ maps f x = second (face x) (face y) ≫ maps f y := by
  rcases x with b | k <;> rcases y with c | l
  · exact positive f b c
  · exact swap _ _ _ _ (mixed f l b)
  · exact mixed f k c
  · rcases lt_trichotomy (HornBoxFaces.vertex k) (HornBoxFaces.vertex l) with h | h | h
    · exact negative f k l h
    · have he : k = l := HornInteriorPreimages.label_injective h
      subst l
      rfl
    · exact swap _ _ _ _ (negative f l k h)

end CategoryTheory.CoherentRealization.BoundaryHomFaceCompatibility
