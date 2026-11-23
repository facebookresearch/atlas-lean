/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import Mathlib.Topology.CompactOpen

/-!
# Products and reversal of the actual compact-open path object

The two projections of an actual product path and the pointwise pair of two
paths are inverse. The maps below use the original TopCat product and its
existing ordinary-product Iso. Reversal is precomposition by the existing
interval symmetry. This owner makes no fibration or homology claim.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousMap

universe u

namespace TopCat

private def pathProductHom (A B : TopCat.{u}) :
    pathObject (A ⨯ B) ⟶ pathObject A ⨯ pathObject B :=
  prod.lift (pathObjectMap (prod.fst : A ⨯ B ⟶ A))
    (pathObjectMap (prod.snd : A ⨯ B ⟶ B))

private def pathProductPair (A B : TopCat.{u}) :
    pathObject A ⨯ pathObject B ⟶ pathObject (A ⨯ B) :=
  TopCat.ofHom
    { toFun q := (TopCat.prodIsoProd A B).inv.hom.comp
        (((prod.fst : pathObject A ⨯ pathObject B ⟶ pathObject A) q).prodMk
          ((prod.snd : pathObject A ⨯ pathObject B ⟶ pathObject B) q))
      continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _ (by
        exact (TopCat.prodIsoProd A B).inv.hom.continuous.comp
          ((continuous_eval.comp
            (((prod.fst : pathObject A ⨯ pathObject B ⟶ pathObject A).hom.continuous.comp
              continuous_fst).prodMk continuous_snd)).prodMk
            (continuous_eval.comp
              (((prod.snd : pathObject A ⨯ pathObject B ⟶ pathObject B).hom.continuous.comp
                continuous_fst).prodMk continuous_snd)))) }

private theorem pathProductHom_fst (A B : TopCat.{u}) :
    pathProductHom A B ≫ prod.fst = pathObjectMap (prod.fst : A ⨯ B ⟶ A) :=
  prod.lift_fst _ _

private theorem pathProductHom_snd (A B : TopCat.{u}) :
    pathProductHom A B ≫ prod.snd = pathObjectMap (prod.snd : A ⨯ B ⟶ B) :=
  prod.lift_snd _ _

private theorem pathProductPair_fst (A B : TopCat.{u}) :
    pathProductPair A B ≫ pathObjectMap (prod.fst : A ⨯ B ⟶ A) = prod.fst := by
  ext q t
  change (prod.fst : A ⨯ B ⟶ A)
      ((TopCat.prodIsoProd A B).inv
        (((prod.fst : pathObject A ⨯ pathObject B ⟶ pathObject A) q) t,
          ((prod.snd : pathObject A ⨯ pathObject B ⟶ pathObject B) q) t)) = _
  simpa only [TopCat.prodFst] using
    (TopCat.prodIsoProd_inv_fst_apply A B
      (((prod.fst : pathObject A ⨯ pathObject B ⟶ pathObject A) q) t,
        ((prod.snd : pathObject A ⨯ pathObject B ⟶ pathObject B) q) t))

private theorem pathProductPair_snd (A B : TopCat.{u}) :
    pathProductPair A B ≫ pathObjectMap (prod.snd : A ⨯ B ⟶ B) = prod.snd := by
  ext q t
  change (prod.snd : A ⨯ B ⟶ B)
      ((TopCat.prodIsoProd A B).inv
        (((prod.fst : pathObject A ⨯ pathObject B ⟶ pathObject A) q) t,
          ((prod.snd : pathObject A ⨯ pathObject B ⟶ pathObject B) q) t)) = _
  simpa only [TopCat.prodSnd] using
    (TopCat.prodIsoProd_inv_snd_apply A B
      (((prod.fst : pathObject A ⨯ pathObject B ⟶ pathObject A) q) t,
        ((prod.snd : pathObject A ⨯ pathObject B ⟶ pathObject B) q) t))

private theorem pathProductPair_hom (A B : TopCat.{u}) :
    pathProductPair A B ≫ pathProductHom A B = 𝟙 (pathObject A ⨯ pathObject B) := by
  apply prod.hom_ext
  · simp only [pathProductHom, Category.assoc, prod.lift_fst, pathProductPair_fst,
      Category.id_comp]
  · simp only [pathProductHom, Category.assoc, prod.lift_snd, pathProductPair_snd,
      Category.id_comp]

private theorem pathProductHom_pair (A B : TopCat.{u}) :
    pathProductHom A B ≫ pathProductPair A B = 𝟙 (pathObject (A ⨯ B)) := by
  ext γ t
  let e := TopCat.homeoOfIso (TopCat.prodIsoProd A B)
  apply e.injective
  change e (e.symm
    (((prod.fst : pathObject A ⨯ pathObject B ⟶ pathObject A) (pathProductHom A B γ)) t,
      ((prod.snd : pathObject A ⨯ pathObject B ⟶ pathObject B) (pathProductHom A B γ)) t)) =
    e (γ t)
  rw [e.apply_symm_apply]
  apply Prod.ext
  · have h := ConcreteCategory.congr_hom
      (prod.lift_fst (pathObjectMap (prod.fst : A ⨯ B ⟶ A))
        (pathObjectMap (prod.snd : A ⨯ B ⟶ B))) γ
    exact congrArg (fun c : C(TopCat.I.{u}, A) => c t) h
  · have h := ConcreteCategory.congr_hom
      (prod.lift_snd (pathObjectMap (prod.fst : A ⨯ B ⟶ A))
        (pathObjectMap (prod.snd : A ⨯ B ⟶ B))) γ
    exact congrArg (fun c : C(TopCat.I.{u}, B) => c t) h

/-- The actual full path object of a product is the product of the full path objects. -/
public def pathObjectProductIso (A B : TopCat.{u}) :
    pathObject (A ⨯ B) ≅ pathObject A ⨯ pathObject B where
  hom := pathProductHom A B
  inv := pathProductPair A B
  hom_inv_id := pathProductHom_pair A B
  inv_hom_id := pathProductPair_hom A B

/-- Its original first path projection is postcomposition by the first product projection. -/
@[reassoc]
public theorem pathObjectProductIso_hom_fst (A B : TopCat.{u}) :
    (pathObjectProductIso A B).hom ≫ prod.fst =
      pathObjectMap (prod.fst : A ⨯ B ⟶ A) := by
  unfold pathObjectProductIso
  exact pathProductHom_fst A B

/-- Its original second path projection is postcomposition by the second product projection. -/
@[reassoc]
public theorem pathObjectProductIso_hom_snd (A B : TopCat.{u}) :
    (pathObjectProductIso A B).hom ≫ prod.snd =
      pathObjectMap (prod.snd : A ⨯ B ⟶ B) := by
  unfold pathObjectProductIso
  exact pathProductHom_snd A B

/-- The returned inverse retains the actual first projected path. -/
@[reassoc]
public theorem pathObjectProductIso_inv_fst (A B : TopCat.{u}) :
    (pathObjectProductIso A B).inv ≫ pathObjectMap (prod.fst : A ⨯ B ⟶ A) = prod.fst := by
  unfold pathObjectProductIso
  exact pathProductPair_fst A B

/-- The returned inverse retains the actual second projected path. -/
@[reassoc]
public theorem pathObjectProductIso_inv_snd (A B : TopCat.{u}) :
    (pathObjectProductIso A B).inv ≫ pathObjectMap (prod.snd : A ⨯ B ⟶ B) = prod.snd := by
  unfold pathObjectProductIso
  exact pathProductPair_snd A B

/-- The first initial endpoint of the actual paired path. -/
@[reassoc]
public theorem pathObjectProductIso_inv_evalZero_fst (A B : TopCat.{u}) :
    (pathObjectProductIso A B).inv ≫ pathEvalZero (A ⨯ B) ≫ prod.fst =
      (prod.fst : pathObject A ⨯ pathObject B ⟶ pathObject A) ≫ pathEvalZero A := by
  rw [← pathObjectMap_evalZero]
  exact pathObjectProductIso_inv_fst_assoc A B (pathEvalZero A)

/-- The second initial endpoint of the actual paired path. -/
@[reassoc]
public theorem pathObjectProductIso_inv_evalZero_snd (A B : TopCat.{u}) :
    (pathObjectProductIso A B).inv ≫ pathEvalZero (A ⨯ B) ≫ prod.snd =
      (prod.snd : pathObject A ⨯ pathObject B ⟶ pathObject B) ≫ pathEvalZero B := by
  rw [← pathObjectMap_evalZero]
  exact pathObjectProductIso_inv_snd_assoc A B (pathEvalZero B)

/-- The first terminal endpoint of the actual paired path. -/
@[reassoc]
public theorem pathObjectProductIso_inv_evalOne_fst (A B : TopCat.{u}) :
    (pathObjectProductIso A B).inv ≫ pathEvalOne (A ⨯ B) ≫ prod.fst =
      (prod.fst : pathObject A ⨯ pathObject B ⟶ pathObject A) ≫ pathEvalOne A := by
  rw [← pathObjectMap_evalOne]
  exact pathObjectProductIso_inv_fst_assoc A B (pathEvalOne A)

/-- The second terminal endpoint of the actual paired path. -/
@[reassoc]
public theorem pathObjectProductIso_inv_evalOne_snd (A B : TopCat.{u}) :
    (pathObjectProductIso A B).inv ≫ pathEvalOne (A ⨯ B) ≫ prod.snd =
      (prod.snd : pathObject A ⨯ pathObject B ⟶ pathObject B) ≫ pathEvalOne B := by
  rw [← pathObjectMap_evalOne]
  exact pathObjectProductIso_inv_snd_assoc A B (pathEvalOne B)

private def pathReverse (Y : TopCat.{u}) : pathObject Y ⟶ pathObject Y :=
  TopCat.ofHom ⟨fun γ => γ.comp TopCat.I.symm.hom,
    ContinuousMap.continuous_precomp TopCat.I.symm.hom⟩

private theorem pathReverse_involutive (Y : TopCat.{u}) :
    pathReverse Y ≫ pathReverse Y = 𝟙 (pathObject Y) := by
  ext γ t
  change γ (TopCat.I.symm (TopCat.I.symm t)) = γ t
  apply congrArg γ
  apply TopCat.I.ext
  simp only [TopCat.I.homeomorph_symm, unitInterval.symm_symm]

private theorem pathReverse_zero (Y : TopCat.{u}) :
    pathReverse Y ≫ pathEvalZero Y = pathEvalOne Y := by
  ext γ
  change γ (TopCat.I.symm 0) = γ 1
  rw [TopCat.I.symm_zero]

private theorem pathReverse_one (Y : TopCat.{u}) :
    pathReverse Y ≫ pathEvalOne Y = pathEvalZero Y := by
  ext γ
  change γ (TopCat.I.symm 1) = γ 0
  rw [TopCat.I.symm_one]

/-- Reversal of the same full compact-open path. -/
public def pathObjectReverseIso (Y : TopCat.{u}) : pathObject Y ≅ pathObject Y where
  hom := pathReverse Y
  inv := pathReverse Y
  hom_inv_id := pathReverse_involutive Y
  inv_hom_id := pathReverse_involutive Y

/-- Reversal exchanges the actual initial and terminal evaluations. -/
@[reassoc]
public theorem pathObjectReverseIso_evalZero (Y : TopCat.{u}) :
    (pathObjectReverseIso Y).hom ≫ pathEvalZero Y = pathEvalOne Y := by
  unfold pathObjectReverseIso
  exact pathReverse_zero Y

/-- The other evaluation is exchanged by the same reversal. -/
@[reassoc]
public theorem pathObjectReverseIso_evalOne (Y : TopCat.{u}) :
    (pathObjectReverseIso Y).hom ≫ pathEvalOne Y = pathEvalZero Y := by
  unfold pathObjectReverseIso
  exact pathReverse_one Y

end TopCat

end
