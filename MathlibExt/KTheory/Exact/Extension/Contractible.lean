/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.Basic
public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedNullhomotopy

/-!
# An actual contraction zigzag for the original extension category

The admissible-mono subdivision has the explicit intermediate functor
`(A ↪ B) ↦ (0 ↪ B)`. Its two natural transformations are the factorization
from the original mono and the factorization from `0 ↪ 0`. The constructed
normalization and denormalization transport these actual maps to Weibel's
original quotient-diagram extension category. Realizing the resulting
simplicial homotopies supplies a contraction zigzag on its original space.

This is the unlocalized total-space step of Weibel Exercise IV.7.3 and the
proof of IV.7.1. The localized Cartesian direct-sum action and its effect on
this contraction are separate mathematical comparisons.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory Limits Opposite ZeroObject
open scoped Simplicial

universe u v

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The original admissible map from the given zero object. -/
def admissibleMonoFromZero (B : AdmissibleMonoCategory (C := C)) :
    (⟨(0 : C)⟩ : AdmissibleMonoCategory (C := C)) ⟶ B :=
  ⟨0, IsAdmissibleMono.fromZero 0⟩

/-- The actual constant-endpoint subdivision object at zero. -/
def admissibleMonoSubdivisionZero : AdmissibleMonoSubdivision (C := C) :=
  SegalSubdivision.mk _ (admissibleMonoFromZero (C := C) ⟨(0 : C)⟩)

/-- Replace only the source of an original mono by zero. -/
def admissibleMonoSubdivisionZeroSource :
    AdmissibleMonoSubdivision (C := C) ⥤ AdmissibleMonoSubdivision (C := C) where
  obj x := SegalSubdivision.mk _ (admissibleMonoFromZero x.obj.2)
  map {x y} f := SegalSubdivision.homMk _ (𝟙 _) f.hom.2 (by
    apply WideSubcategory.hom_ext
    simp [admissibleMonoFromZero])
  map_id x := by
    apply Functor.Elements.hom_ext
    rfl
  map_comp f g := by
    apply Functor.Elements.hom_ext
    apply Prod.ext
    · simp
    · rfl

/-- Each original mono maps to the zero-source mono with its original target. -/
def admissibleMonoSubdivisionToZeroSource :
    𝟭 (AdmissibleMonoSubdivision (C := C)) ⟶
      admissibleMonoSubdivisionZeroSource (C := C) where
  app x := SegalSubdivision.homMk _
    (admissibleMonoFromZero x.obj.1.unop) (𝟙 _) (by
      apply WideSubcategory.hom_ext
      simp [admissibleMonoFromZero])
  naturality {x y} f := by
    apply Functor.Elements.hom_ext
    apply Prod.ext
    · apply Quiver.Hom.unop_inj
      apply WideSubcategory.hom_ext
      change (0 : (0 : C) ⟶ y.obj.1.unop.obj) ≫ f.hom.1.unop.hom =
        (𝟙 (0 : C)) ≫ (0 : (0 : C) ⟶ x.obj.1.unop.obj)
      simp
    · apply WideSubcategory.hom_ext
      change f.hom.2.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.2.hom
      simp

/-- The zero mono maps naturally to every zero-source mono. -/
def admissibleMonoSubdivisionZeroToZeroSource :
    (Functor.const (AdmissibleMonoSubdivision (C := C))).obj
        (admissibleMonoSubdivisionZero (C := C)) ⟶
      admissibleMonoSubdivisionZeroSource (C := C) where
  app x := SegalSubdivision.homMk _ (𝟙 _)
    (admissibleMonoFromZero x.obj.2) (by
      apply WideSubcategory.hom_ext
      simp [admissibleMonoFromZero])
  naturality {x y} f := by
    apply Functor.Elements.hom_ext
    apply Prod.ext
    · rfl
    · apply WideSubcategory.hom_ext
      change (𝟙 (0 : C)) ≫ (0 : (0 : C) ⟶ y.obj.2.obj) =
        (0 : (0 : C) ⟶ x.obj.2.obj) ≫ f.hom.2.hom
      simp

namespace ExtensionCategory

/-- The actual selected completion of the original zero mono. -/
def contractionZero : ExtensionCategory C :=
  (denormalization (C := C)).obj (admissibleMonoSubdivisionZero (C := C))

/-- The explicit intermediate endofunctor on original quotient-diagram rows. -/
def contractionMiddle : ExtensionCategory C ⥤ ExtensionCategory C :=
  normalization ⋙ admissibleMonoSubdivisionZeroSource ⋙ denormalization

/-- Normalize, apply the original factorization, and use the proved unit. -/
def toContractionMiddle : 𝟭 (ExtensionCategory C) ⟶ contractionMiddle :=
  (normalizationUnitIso (C := C)).hom ≫
    Functor.whiskerLeft normalization
      (Functor.whiskerRight admissibleMonoSubdivisionToZeroSource denormalization)

/-- The original zero-row completion maps to the intermediate original rows. -/
def zeroToContractionMiddle :
    (Functor.const (ExtensionCategory C)).obj (contractionZero (C := C)) ⟶
      contractionMiddle (C := C) :=
  (Functor.constComp (J := ExtensionCategory C)
      (admissibleMonoSubdivisionZero (C := C)) (denormalization (C := C))).inv ≫
    Functor.whiskerLeft normalization
      (Functor.whiskerRight admissibleMonoSubdivisionZeroToZeroSource denormalization)

/-- The first actual simplicial homotopy retains the original extension nerve. -/
def contractionIdentityHomotopy :
    SSet.Homotopy (𝟙 (nerve (ExtensionCategory C) : SSet.{max u v}))
      (nerveMap (contractionMiddle (C := C))) := by
  simpa only [nerveMap_id] using
    NatTrans.nerveHomotopy (toContractionMiddle (C := C))

/-- The second actual homotopy starts at the original chosen zero-row functor. -/
def contractionZeroHomotopy :
    SSet.Homotopy
      (nerveMap ((Functor.const (ExtensionCategory C)).obj
        (contractionZero (C := C))))
      (nerveMap (contractionMiddle (C := C))) :=
  NatTrans.nerveHomotopy (zeroToContractionMiddle (C := C))

/-- Realized identity-to-middle path on the original extension realization. -/
def realizedContractionIdentityHomotopy :
    ContinuousMap.Homotopy
      ((SSet.toTop.map (𝟙 (nerve (ExtensionCategory C)))).hom)
      ((SSet.toTop.map (nerveMap (contractionMiddle (C := C)))).hom) :=
  SSet.realizeHomotopy _ _ _ _ (contractionIdentityHomotopy (C := C))

/-- Realized zero-to-middle path, ready to reverse and concatenate. -/
def realizedContractionZeroHomotopy :
    ContinuousMap.Homotopy
      ((SSet.toTop.map (nerveMap ((Functor.const (ExtensionCategory C)).obj
        (contractionZero (C := C))))).hom)
      ((SSet.toTop.map (nerveMap (contractionMiddle (C := C)))).hom) :=
  SSet.realizeHomotopy _ _ _ _ (contractionZeroHomotopy (C := C))


/-- The original constant row functor is the literal simplicial constant map. -/
theorem contractionZeroNerveMap_eq_const :
    nerveMap ((Functor.const (ExtensionCategory C)).obj (contractionZero (C := C))) =
      SSet.const (ComposableArrows.mk₀ (contractionZero (C := C))) := by
  ext Δ A
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    rfl

/-- Concatenate the two actual realized paths to the original realized zero vertex. -/
def realizedContractionHomotopy :
    ContinuousMap.Homotopy
      (ContinuousMap.id (SSet.toTop.obj (nerve (ExtensionCategory C))))
      (ContinuousMap.const _
        (SSet.realizedVertex (ComposableArrows.mk₀ (contractionZero (C := C))))) := by
  have hid : (SSet.toTop.map (𝟙 (nerve (ExtensionCategory C)))).hom =
      ContinuousMap.id (SSet.toTop.obj (nerve (ExtensionCategory C))) := by
    rw [SSet.toTop.map_id]
    rfl
  have hzero :
      (SSet.toTop.map (nerveMap ((Functor.const (ExtensionCategory C)).obj
        (contractionZero (C := C))))).hom =
      ContinuousMap.const _
        (SSet.realizedVertex (ComposableArrows.mk₀ (contractionZero (C := C)))) := by
    rw [contractionZeroNerveMap_eq_const]
    exact SSet.toTop_map_const_hom _
  exact (ContinuousMap.Homotopy.cast
      (realizedContractionIdentityHomotopy (C := C)) hid rfl).trans
    (ContinuousMap.Homotopy.cast
      (realizedContractionZeroHomotopy (C := C)).symm rfl hzero)

/-- The realization of the original unlocalized quotient-diagram extension category
is contractible, using the original zero completion and constructed contraction. -/
theorem realization_contractibleSpace :
    ContractibleSpace (SSet.toTop.obj (nerve (ExtensionCategory C))) :=
  (contractible_iff_id_nullhomotopic _).2
    ⟨SSet.realizedVertex (ComposableArrows.mk₀ (contractionZero (C := C))),
      ⟨realizedContractionHomotopy (C := C)⟩⟩

end ExtensionCategory
end AlgebraicKTheory
end
