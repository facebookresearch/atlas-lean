/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SourceOperatorReconstruction

/-!
# Full orthogonal reverse actions on source morphisms

A genuine source I-space morphism that preserves the right sphere
transformation preserves each entire operator generator and its actual
weighted-coend descent. The field equations use all continuous Hom and
sphere objects. They supply the morphism compatibility for the reverse
carrier construction, whose source unit and associativity remain separate.

The primary source is MMSS, *Model categories of diagram spectra*,
December 30, 1999 preprint, Construction 2.1 and Theorem 2.2 on
printed/PDF page 9, with the reverse colimit construction on page 63.
The precise unbundled source-data scope is recorded in
`CanonicalSourceOperatorFunctor`. This file proves full source-morphism
naturality on the existing coend carrier and requires no level model.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceActionCompatibility

/-- The original orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original block-sum monoidal structure on orthogonal indices. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed CGWH enriched ordinary structure on orthogonal indices. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block symmetry on orthogonal indices. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}

attribute [local instance] Enriched.prodCategory

variable {X Y : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex}

/-- Every full enriched source morphism is natural on every original continuous index arrow. -/
theorem source_map_naturality (q : X ⟶ Y) {n k : OrthogonalIndex} (f : n ⟶ k) :
    X.toEnrichedFunctor.toOrdinaryFunctor.map f ≫ EnrichedFunctorCat.component q k =
      EnrichedFunctorCat.component q n ≫ Y.toEnrichedFunctor.toOrdinaryFunctor.map f := by
  have h := (Functor.whiskerLeft
    (ForgetEnrichment.equiv (D := OrthogonalIndex) PointedCGWH.{u, v}).inverse
    (Functor.whiskerRight q.toEnrichedNatTrans.out
      (ForgetEnrichment.equivFunctor PointedCGWH.{u, v} PointedCGWH.{u, v}))).naturality f
  change X.toEnrichedFunctor.toOrdinaryFunctor.map f ≫ EnrichedFunctorCat.component q k =
      EnrichedFunctorCat.component q n ≫ Y.toEnrichedFunctor.toOrdinaryFunctor.map f at h
  exact h

variable
  (t : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
    (X.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
    (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
      PointedCGWH.{u, v} X.toEnrichedFunctor))
  (s : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
    (Y.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
    (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
      PointedCGWH.{u, v} Y.toEnrichedFunctor))
  (q : X ⟶ Y)
  (hq : ∀ n a : OrthogonalIndex,
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ≫
          EnrichedFunctorCat.component q (n + a) =
      (EnrichedFunctorCat.component q n ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫
        Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n a)

include hq

/-- The source block inverse and genuine source morphism preserve the entire coefficient. -/
theorem coefficient_morphism (n a : OrthogonalIndex) :
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ≫
          EnrichedFunctorCat.component q (a + n) =
      (EnrichedFunctorCat.component q n ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫
        Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n a := by
  let C := PointedCGWH.orthogonalSphere.{u, v} a
  let sx : X.toEnrichedFunctor.obj n ⊗ C ⟶ X.toEnrichedFunctor.obj (n + a) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let sy : Y.toEnrichedFunctor.obj n ⊗ C ⟶ Y.toEnrichedFunctor.obj (n + a) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n a
  let bx : X.toEnrichedFunctor.obj (n + a) ⟶ X.toEnrichedFunctor.obj (a + n) :=
    X.toEnrichedFunctor.toOrdinaryFunctor.map (β_ a n).inv
  let by' : Y.toEnrichedFunctor.obj (n + a) ⟶ Y.toEnrichedFunctor.obj (a + n) :=
    Y.toEnrichedFunctor.toOrdinaryFunctor.map (β_ a n).inv
  let cx : X.toEnrichedFunctor.obj n ⊗ C ⟶ X.toEnrichedFunctor.obj (a + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let cy : Y.toEnrichedFunctor.obj n ⊗ C ⟶ Y.toEnrichedFunctor.obj (a + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n a
  let r := EnrichedFunctorCat.component q n ⊗ₘ 𝟙 C
  have hx : cx = sx ≫ bx := rfl
  have hy : cy = sy ≫ by' := rfl
  have hb : bx ≫ EnrichedFunctorCat.component q (a + n) =
      EnrichedFunctorCat.component q (n + a) ≫ by' := source_map_naturality q (β_ a n).inv
  have hs : sx ≫ EnrichedFunctorCat.component q (n + a) = r ≫ sy := hq n a
  change cx ≫ EnrichedFunctorCat.component q (a + n) = r ≫ cy
  calc
    _ = (sx ≫ bx) ≫ EnrichedFunctorCat.component q (a + n) :=
      congrArg (fun z => z ≫ EnrichedFunctorCat.component q (a + n)) hx
    _ = sx ≫ (bx ≫ EnrichedFunctorCat.component q (a + n)) := Category.assoc _ _ _
    _ = sx ≫ (EnrichedFunctorCat.component q (n + a) ≫ by') := congrArg (fun z => sx ≫ z) hb
    _ = (sx ≫ EnrichedFunctorCat.component q (n + a)) ≫ by' := (Category.assoc _ _ _).symm
    _ = (r ≫ sy) ≫ by' := congrArg (fun z => z ≫ by') hs
    _ = r ≫ (sy ≫ by') := Category.assoc _ _ _
    _ = r ≫ cy := congrArg (fun z => r ≫ z) hy.symm

/-- Every entire continuous-Hom/sphere generator is preserved on the same source components. -/
theorem generator_morphism (n k a : OrthogonalIndex) :
    Reconstruction.generator OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n k a ≫
          EnrichedFunctorCat.component q k =
      (EnrichedFunctorCat.component q n ⊗ₘ
        𝟙 (OrthogonalIndex.hom.{u, v} (a + n) k ⊗ PointedCGWH.orthogonalSphere.{u, v} a)) ≫
          Reconstruction.generator OrthogonalIndex.enrichedMonoidalData.{u, v}
            orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n k a := by
  let H := OrthogonalIndex.hom.{u, v} (a + n) k
  let C := PointedCGWH.orthogonalSphere.{u, v} a
  let cx : X.toEnrichedFunctor.obj n ⊗ C ⟶ X.toEnrichedFunctor.obj (a + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a
  let cy : Y.toEnrichedFunctor.obj n ⊗ C ⟶ Y.toEnrichedFunctor.obj (a + n) :=
    Reconstruction.coefficient OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n a
  let ex : X.toEnrichedFunctor.obj (a + n) ⊗ H ⟶ X.toEnrichedFunctor.obj k :=
    MonoidalClosed.uncurry (X.toEnrichedFunctor.map (a + n) k)
  let ey : Y.toEnrichedFunctor.obj (a + n) ⊗ H ⟶ Y.toEnrichedFunctor.obj k :=
    MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (a + n) k)
  let px : X.toEnrichedFunctor.obj n ⊗ (H ⊗ C) ⟶
      (X.toEnrichedFunctor.obj n ⊗ C) ⊗ H :=
    (X.toEnrichedFunctor.obj n ◁ (β_ H C).hom) ≫ (α_ (X.toEnrichedFunctor.obj n) C H).inv
  let py : Y.toEnrichedFunctor.obj n ⊗ (H ⊗ C) ⟶
      (Y.toEnrichedFunctor.obj n ⊗ C) ⊗ H :=
    (Y.toEnrichedFunctor.obj n ◁ (β_ H C).hom) ≫ (α_ (Y.toEnrichedFunctor.obj n) C H).inv
  let gx : X.toEnrichedFunctor.obj n ⊗ (H ⊗ C) ⟶ X.toEnrichedFunctor.obj k :=
    Reconstruction.generator OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n k a
  let gy : Y.toEnrichedFunctor.obj n ⊗ (H ⊗ C) ⟶ Y.toEnrichedFunctor.obj k :=
    Reconstruction.generator OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n k a
  have hx : gx = px ≫ (cx ▷ H) ≫ ex := rfl
  have hy : gy = py ≫ (cy ▷ H) ≫ ey := rfl
  have hc : cx ≫ EnrichedFunctorCat.component q (a + n) =
      (EnrichedFunctorCat.component q n ⊗ₘ 𝟙 C) ≫ cy := coefficient_morphism t s q hq n a
  have he : ex ≫ EnrichedFunctorCat.component q k =
      (EnrichedFunctorCat.component q (a + n) ⊗ₘ 𝟙 H) ≫ ey :=
    q.uncurriedNaturality (a + n) k
  change gx ≫ EnrichedFunctorCat.component q k =
    (EnrichedFunctorCat.component q n ⊗ₘ 𝟙 (H ⊗ C)) ≫ gy
  rw [hx, hy]
  simp only [Category.assoc]
  rw [he]
  simp only [tensorHom_id]
  rw [← comp_whiskerRight_assoc, hc, comp_whiskerRight]
  simp only [tensorHom_id, Category.assoc]
  dsimp only [px, py]
  simp only [Category.assoc]
  rw [← associator_inv_naturality_left_assoc, ← whisker_exchange_assoc]

/-- The complete original weighted coend action is preserved by every lawful source morphism. -/
theorem reverseOperatorAction_morphism (n k : OrthogonalIndex) :
    reverseOperatorAction.{u, v} X t n k ≫ EnrichedFunctorCat.component q k =
      (EnrichedFunctorCat.component q n ⊗ₘ 𝟙 (OrthogonalOperatorIndex.hom.{u, v} n k)) ≫
        reverseOperatorAction.{u, v} Y s n k := by
  apply Enriched.weightedCoend.Mapped.hom_ext
    (weight OrthogonalIndex.enrichedMonoidalData.{u, v} n k) orthogonalSphereFunctor.{u, v}
    (tensorLeft (X.toEnrichedFunctor.obj n))
  intro a
  let i := OrthogonalOperatorIndex.ι.{u, v} n k a
  have hi : (X.toEnrichedFunctor.obj n ◁ i) ≫
      (EnrichedFunctorCat.component q n ⊗ₘ 𝟙 (OrthogonalOperatorIndex.hom.{u, v} n k)) =
    (EnrichedFunctorCat.component q n ⊗ₘ
      𝟙 (OrthogonalIndex.hom.{u, v} (a + n) k ⊗ PointedCGWH.orthogonalSphere.{u, v} a)) ≫
        (Y.toEnrichedFunctor.obj n ◁ i) := by
    simpa only [tensorHom_id, id_tensorHom] using
      (tensorHom_def' (EnrichedFunctorCat.component q n) i).symm.trans
        (tensorHom_def (EnrichedFunctorCat.component q n) i)
  change (X.toEnrichedFunctor.obj n ◁ i) ≫
      (reverseOperatorAction.{u, v} X t n k ≫ EnrichedFunctorCat.component q k) =
    (X.toEnrichedFunctor.obj n ◁ i) ≫
      ((EnrichedFunctorCat.component q n ⊗ₘ 𝟙 (OrthogonalOperatorIndex.hom.{u, v} n k)) ≫
        reverseOperatorAction.{u, v} Y s n k)
  rw [← Category.assoc, reverseOperatorAction_generator]
  rw [← Category.assoc, hi, Category.assoc, reverseOperatorAction_generator]
  exact generator_morphism t s q hq n k a

/-- Every entire curried reverse field has the original full Hom naturality square. -/
theorem reverseOperatorMapField_morphism (n k : OrthogonalIndex) :
    MonoidalClosed.uncurry (reverseOperatorMapField.{u, v} X t n k) ≫
        EnrichedFunctorCat.component q k =
      (EnrichedFunctorCat.component q n ⊗ₘ 𝟙 (OrthogonalOperatorIndex.hom.{u, v} n k)) ≫
        MonoidalClosed.uncurry (reverseOperatorMapField.{u, v} Y s n k) := by
  simpa only [reverseOperatorMapField, Reconstruction.enrichedMapField,
    MonoidalClosed.uncurry_curry, reverseOperatorAction] using
      reverseOperatorAction_morphism t s q hq n k

omit hq

/-- Restriction of every original canonical morphism preserves the genuine sphere transformation. -/
theorem original_sphereTransformation_morphism
    {F G : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})} (f : F ⟶ G)
    (n a : OrthogonalIndex) :
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
        (sphereTransformation.{u, v} F) n a ≫
          EnrichedFunctorCat.component ((restrictionFunctor.{u, v}).map f) (n + a) =
      (EnrichedFunctorCat.component ((restrictionFunctor.{u, v}).map f) n ⊗ₘ
        𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫
          Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
            orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj G).toEnrichedFunctor
            (sphereTransformation.{u, v} G) n a := by
  let C := PointedCGWH.orthogonalSphere.{u, v} a
  let sx : F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⊗ C ⟶
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a)) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
      (sphereTransformation.{u, v} F) n a
  let sy : G.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⊗ C ⟶
      G.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a)) :=
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj G).toEnrichedFunctor
      (sphereTransformation.{u, v} G) n a
  let rn : F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⟶
      G.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) :=
    EnrichedFunctorCat.component ((restrictionFunctor.{u, v}).map f) n
  let rna : F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a)) ⟶
      G.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a)) :=
    EnrichedFunctorCat.component ((restrictionFunctor.{u, v}).map f) (n + a)
  have hx : sx = sphereAction.{u, v} F n a := sphereTransformation_component F (n, a)
  have hy : sy = sphereAction.{u, v} G n a := sphereTransformation_component G (n, a)
  have hn : rn = EnrichedFunctorCat.component f (OrthogonalOperatorIndex.ofIndex.{u, v} n) :=
    restrictionFunctor_map_component f n
  have hna : rna = EnrichedFunctorCat.component f
      (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a)) := restrictionFunctor_map_component f (n + a)
  change sx ≫ rna = (rn ⊗ₘ 𝟙 C) ≫ sy
  rw [hx, hy, hn, hna, tensorHom_id]
  exact sphereAction_natural.{u, v} f n a

/-- Every complete original canonical morphism is retained by the reverse coend action fields. -/
theorem original_reverseOperatorAction_morphism
    {F G : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})} (f : F ⟶ G)
    (n k : OrthogonalIndex) :
    reverseOperatorAction.{u, v} ((restrictionFunctor.{u, v}).obj F)
        (sphereTransformation.{u, v} F) n k ≫
          EnrichedFunctorCat.component f (OrthogonalOperatorIndex.ofIndex.{u, v} k) =
      (EnrichedFunctorCat.component f (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⊗ₘ
        𝟙 (OrthogonalOperatorIndex.hom.{u, v} n k)) ≫
          reverseOperatorAction.{u, v} ((restrictionFunctor.{u, v}).obj G)
            (sphereTransformation.{u, v} G) n k := by
  simpa only [restrictionFunctor_map_component] using
    reverseOperatorAction_morphism (sphereTransformation.{u, v} F) (sphereTransformation.{u, v} G)
      ((restrictionFunctor.{u, v}).map f) (original_sphereTransformation_morphism f) n k

/-- Every original morphism retains the whole reconstructed enriched-map-field square. -/
theorem original_reverseOperatorMapField_morphism
    {F G : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})} (f : F ⟶ G)
    (n k : OrthogonalIndex) :
    MonoidalClosed.uncurry (reverseOperatorMapField.{u, v} ((restrictionFunctor.{u, v}).obj F)
        (sphereTransformation.{u, v} F) n k) ≫
          EnrichedFunctorCat.component f (OrthogonalOperatorIndex.ofIndex.{u, v} k) =
      (EnrichedFunctorCat.component f (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⊗ₘ
        𝟙 (OrthogonalOperatorIndex.hom.{u, v} n k)) ≫
          MonoidalClosed.uncurry
            (reverseOperatorMapField.{u, v} ((restrictionFunctor.{u, v}).obj G)
              (sphereTransformation.{u, v} G) n k) := by
  simpa only [restrictionFunctor_map_component] using
    reverseOperatorMapField_morphism (sphereTransformation.{u, v} F) (sphereTransformation.{u, v} G)
      ((restrictionFunctor.{u, v}).map f) (original_sphereTransformation_morphism f) n k

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceActionCompatibility
