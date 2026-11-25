/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterLeibniz
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms
import Mathlib.CategoryTheory.Adhesive.PushoutProduct

/-!
# Monicity of every original marked parameter square

The same original parameter and marked source maps may have any actual
pushout point, including the point supplied by a marked slice. Forgetting
marks preserves that original square. Its whole comparison is canonically
isomorphic to the native simplicial pushout-product of the original maps,
so original monomorphisms give a genuine marked monomorphism.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory

namespace SSet.Marked

/-- Every original marked parameter square retains the same full underlying simplicial pushout square. -/
def underlyingParameterSquare {A D : SSet.{u}} {X Y : Marked.{u}}
    {a : A ⟶ D} {f : X ⟶ Y} (sq : maxTensorBifunctor.PushoutObjObj f a) :
    (curriedTensor SSet.{u}).flip.PushoutObjObj f.hom a := by
  let _ : PreservesColimitsOfSize.{u, u} forget.{u} := forgetPreservesColimits
  exact
    { pt := sq.pt.toSSet
      inl := sq.inl.hom
      inr := sq.inr.hom
      isPushout := forget.map_isPushout sq.isPushout
      ι := sq.ι.hom
      inl_ι := congrArg Hom.hom sq.inl_ι
      inr_ι := congrArg Hom.hom sq.inr_ι }

/-- The original whole underlying parameter map is the native simplicial pushout-product through its actual
  pushout-point comparison. -/
def underlyingParameterSquareIso {A D : SSet.{u}} {X Y : Marked.{u}}
    {a : A ⟶ D} {f : X ⟶ Y} (sq : maxTensorBifunctor.PushoutObjObj f a) :
    Arrow.mk sq.ι.hom ≅ (Arrow.mk a □ Arrow.mk f.hom) := by
  let s := (underlyingParameterSquare sq).flip
  let t := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) a f.hom
  let e := s.isPushout.isoIsPushout _ _ t.isPushout
  have h : e.hom ≫ t.ι = s.ι := by
    apply s.isPushout.hom_ext
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ t.ι) (s.isPushout.inl_isoIsPushout_hom _ _ t.isPushout)).trans
          (t.inl_ι.trans s.inl_ι.symm))
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ t.ι) (s.isPushout.inr_isoIsPushout_hom _ _ t.isPushout)).trans
          (t.inr_ι.trans s.inr_ι.symm))
  exact Arrow.isoMk e (Iso.refl _) (h.trans (Category.comp_id _).symm)

/-- Monic original parameter and marked source maps give a monic comparison for every actual original marked
  pushout point. -/
theorem parameterSquare_mono {A D : SSet.{u}} {X Y : Marked.{u}}
    {a : A ⟶ D} {f : X ⟶ Y} [Mono a] [Mono f]
    (sq : maxTensorBifunctor.PushoutObjObj f a) : Mono sq.ι := by
  let _ : Mono f.hom := f.mono_underlying
  let _ : Mono (Arrow.mk a).hom := (inferInstance : Mono a)
  let _ : Mono (Arrow.mk f.hom).hom := (inferInstance : Mono f.hom)
  let _ : Mono ((Arrow.mk a □ Arrow.mk f.hom).hom) :=
    MonoidalCategory.Arrow.PushoutProduct.instMonoHomObjArrowFunctorPushoutProduct
  let _ : Mono sq.ι.hom :=
    ((MorphismProperty.monomorphisms SSet.{u}).arrow_iso_iff (underlyingParameterSquareIso sq)).mpr inferInstance
  exact Hom.mono_of_underlying _

end SSet.Marked
