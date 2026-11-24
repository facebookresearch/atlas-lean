/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNegativeFaceRelations

/-!
# Actual agreement on the intersection of two supplied negative faces

The actual negative-subcomplex inclusions restrict the two supplied face
maps to the same whole map on their intersection. Both original endpoint
transports are explicit. The proof uses the genuine common-face Hom
isomorphism and the actual original horn relation; no compatibility
conclusion is passed as data.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.NegativeFaceOverlap
open SimplicialEnrichment HornHomFaces

private theorem negative_transport_ι {J : Type u} [LinearOrder J] (t : J) {a b a' b' : J}
    (ha : a = a') (hb : b = b') :
    eqToHom (congrArg₂ (fun a b : J => (HomBoxDecomposition.negative a t b : SSet.{u})) ha hb) ≫
      (HomBoxDecomposition.negative a' t b').ι =
    (HomBoxDecomposition.negative a t b).ι ≫
      eqToHom (congrArg₂ (fun a b : J => nerve (SimplicialThickening.Path a b)) ha hb) := by
  subst a'
  subst b'
  change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
  exact (Category.id_comp _).trans (Category.comp_id _).symm

variable {n : ℕ} (j k : Fin (n + 3)) (hjk : j < k) (a b : ULift.{u} (Fin (n + 1)))

/-- The actual inclusion of the common negative-face intersection in its first original negative face. -/
def firstInclusion : (DoubleOrdinalFace.face j k hjk a b : SSet.{u}) ⟶
    HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a) (ULift.up j) (TwoOutsideFaces.point j k hjk b) :=
  SSet.Subcomplex.homOfLE (show DoubleOrdinalFace.face j k hjk a b ≤ _ from inf_le_left)

/-- The actual inclusion in the other original negative face, before its precise endpoint transport. -/
def secondInclusion : (DoubleOrdinalFace.face j k hjk a b : SSet.{u}) ⟶
    HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a) (ULift.up k) (TwoOutsideFaces.point j k hjk b) :=
  SSet.Subcomplex.homOfLE (show DoubleOrdinalFace.face j k hjk a b ≤ _ from inf_le_right)

/-- The exact original endpoint transport to the other common ordinal face's negative subcomplex. -/
def secondTransport :
    (HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a) (ULift.up k)
      (TwoOutsideFaces.point j k hjk b) : SSet.{u}) ⟶
    HomBoxDecomposition.negative
      ((OrdinalFace.embedding k) ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a)) (ULift.up k)
      ((OrdinalFace.embedding k) ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b)) :=
  eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) =>
    (HomBoxDecomposition.negative a (ULift.up k) b : SSet.{u}))
      (TwoOutsideFaces.point_right j k hjk a) (TwoOutsideFaces.point_right j k hjk b))

/-- The first actual intersection chart followed by its subcomplex inclusion is the original coherent face Hom chart. -/
theorem first_chart :
    (DoubleOrdinalFace.homIso j k hjk a b).hom ≫ firstInclusion j k hjk a b =
      (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).map (.mk a) (.mk b) ≫
        (OrdinalFace.negativeIso j ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
          ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b)).hom := by
  apply (cancel_mono (HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a)
    (ULift.up j) (TwoOutsideFaces.point j k hjk b)).ι).mp
  have h₁ : ((DoubleOrdinalFace.homIso j k hjk a b).hom ≫ firstInclusion j k hjk a b) ≫
      (HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a) (ULift.up j)
        (TwoOutsideFaces.point j k hjk b)).ι =
      (DoubleOrdinalFace.homIso j k hjk a b).hom ≫ (DoubleOrdinalFace.face j k hjk a b).ι :=
    (Category.assoc _ _ _).trans
      (congrArg (fun h => (DoubleOrdinalFace.homIso j k hjk a b).hom ≫ h)
        (SSet.Subcomplex.homOfLE_ι (show DoubleOrdinalFace.face j k hjk a b ≤ _ from inf_le_left)))
  have h₂ := OrdinalFace.negativeIso_operator j
    ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
    ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b)
  have h₃ := (Category.assoc
    ((coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).map (.mk a) (.mk b))
    (OrdinalFace.negativeIso j ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
      ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b)).hom
    (HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a) (ULift.up j)
      (TwoOutsideFaces.point j k hjk b)).ι).trans
        (congrArg (fun h =>
          (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk)))).map (.mk a) (.mk b) ≫ h) h₂)
  exact h₁.trans ((DoubleOrdinalFace.homIso_operator j k hjk a b).trans h₃.symm)

private theorem operator_forward :
    (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫
      coherentSimplexMap (SimplexCategory.δ j)).map (.mk a) (.mk b) ≫
        eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
          (TwoOutsideFaces.point_right j k hjk a) (TwoOutsideFaces.point_right j k hjk b)) =
    (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫
      coherentSimplexMap (SimplexCategory.δ k)).map (.mk a) (.mk b) := by
  let e := eqToIso (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
    (TwoOutsideFaces.point_right j k hjk a) (TwoOutsideFaces.point_right j k hjk b))
  have h := CommonIntervalMaps.operator_eq j k hjk a b
  change (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫
    coherentSimplexMap (SimplexCategory.δ k)).map (.mk a) (.mk b) ≫ e.inv =
      (coherentSimplexMap (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))) ≫
        coherentSimplexMap (SimplexCategory.δ j)).map (.mk a) (.mk b) at h
  exact (congrArg (fun h => h ≫ e.hom) h.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun h =>
        (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))) ≫
          coherentSimplexMap (SimplexCategory.δ k)).map (.mk a) (.mk b) ≫ h) e.inv_hom_id).trans
            (Category.comp_id _)))

/-- The other actual intersection chart retains its own original negative-face Hom map with the precise
  endpoint transport. -/
theorem second_chart :
    ((DoubleOrdinalFace.homIso j k hjk a b).hom ≫ secondInclusion j k hjk a b) ≫ secondTransport j k hjk a b =
      (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).map (.mk a) (.mk b) ≫
        (OrdinalFace.negativeIso k ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a)
          ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b)).hom := by
  let L := HomBoxDecomposition.negative (TwoOutsideFaces.point j k hjk a) (ULift.up k) (TwoOutsideFaces.point j k hjk b)
  let R := HomBoxDecomposition.negative
    ((OrdinalFace.embedding k) ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a)) (ULift.up k)
    ((OrdinalFace.embedding k) ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b))
  let T := eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
    (TwoOutsideFaces.point_right j k hjk a) (TwoOutsideFaces.point_right j k hjk b))
  let E := DoubleOrdinalFace.homIso j k hjk a b
  let P := secondInclusion j k hjk a b
  let S := secondTransport j k hjk a b
  apply (cancel_mono R.ι).mp
  have hS : S ≫ R.ι = L.ι ≫ T := negative_transport_ι (ULift.up k)
    (TwoOutsideFaces.point_right j k hjk a) (TwoOutsideFaces.point_right j k hjk b)
  have hP : P ≫ L.ι = (DoubleOrdinalFace.face j k hjk a b).ι :=
    SSet.Subcomplex.homOfLE_ι (show DoubleOrdinalFace.face j k hjk a b ≤ _ from inf_le_right)
  have h₁ : ((E.hom ≫ P) ≫ S) ≫ R.ι =
      (E.hom ≫ (DoubleOrdinalFace.face j k hjk a b).ι) ≫ T :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun h => (E.hom ≫ P) ≫ h) hS).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun h => h ≫ T) ((Category.assoc _ _ _).trans
            (congrArg (fun h => E.hom ≫ h) hP))))))
  have h₂ := (congrArg (fun h => h ≫ T) (DoubleOrdinalFace.homIso_operator j k hjk a b)).trans
    (operator_forward j k hjk a b)
  have h₃ := (Category.assoc
    ((coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).map (.mk a) (.mk b))
    (OrdinalFace.negativeIso k ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a)
      ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b)).hom R.ι).trans
        (congrArg (fun h =>
          (coherentSimplexMap (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk)))).map (.mk a) (.mk b) ≫ h)
            (OrdinalFace.negativeIso_operator k ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a)
              ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b)))
  exact h₁.trans (h₂.trans h₃.symm)

/-- The two actual supplied negative-face maps agree after their actual intersection inclusions and precise
  endpoint transports. -/
theorem restriction_agreement {C : Carrier.{u}} {i : Fin (n + 3)}
    (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C) (hj : j ≠ i) (hk : k ≠ i) :
    firstInclusion j k hjk a b ≫
      negativeMap f j hj ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
        ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b) =
    secondInclusion j k hjk a b ≫ secondTransport j k hjk a b ≫
      negativeMap f k hk ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a)
        ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b) ≫
          eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
            (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm)
            (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm)) := by
  let E := DoubleOrdinalFace.homIso j k hjk a b
  let P := firstInclusion j k hjk a b
  let Q := secondInclusion j k hjk a b
  let S := secondTransport j k hjk a b
  let L := negativeMap f j hj ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) a)
    ((OrdinalFace.embedding (k.pred (Fin.ne_zero_of_lt hjk))) b)
  let R := negativeMap f k hk ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) a)
    ((OrdinalFace.embedding (j.castPred (Fin.ne_last_of_lt hjk))) b)
  let T := eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
    (congrArg (HornFaces.object f) (common_vertex j k hjk a.down).symm)
    (congrArg (HornFaces.object f) (common_vertex j k hjk b.down).symm))
  apply (cancel_epi E.hom).mp
  have hL : E.hom ≫ (P ≫ L) = NegativeFaceRelations.leftRestriction f j k hj hjk a b :=
    (Category.assoc E.hom P L).symm.trans
      ((congrArg (fun h => h ≫ L) (first_chart j k hjk a b)).trans (Category.assoc _ _ _))
  have hR : E.hom ≫ (Q ≫ (S ≫ (R ≫ T))) = NegativeFaceRelations.rightRestriction f j k hk hjk a b :=
    (Category.assoc E.hom Q (S ≫ (R ≫ T))).symm.trans
      ((Category.assoc (E.hom ≫ Q) S (R ≫ T)).symm.trans
        ((congrArg (fun h => h ≫ (R ≫ T)) (second_chart j k hjk a b)).trans (Category.assoc _ _ _)))
  exact hL.trans ((NegativeFaceRelations.restriction_agreement f j k hj hk hjk a b).trans hR.symm)

end CategoryTheory.CoherentRealization.NegativeFaceOverlap
