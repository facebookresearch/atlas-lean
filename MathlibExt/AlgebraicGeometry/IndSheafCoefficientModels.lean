/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.Topology.Sheaves.Functors

/-!
# Ordinary sheaf coefficients in the actual compact-support Ind category

The ordinary-to-Ind realization is the restricted Yoneda presheaf on the
original compact-support category. Its ind-object property is a separate
source construction. The lift uses the native Ind equivalence, keeping
every ordinary sheaf morphism. Tensor is the sheafification of the actual
pointwise module tensor, rather than an unspecified sheaf operation.

Source: Kashiwara--Schapira, Ind-sheaves; D'Agnolo--Kashiwara
arXiv:1311.2374v2, Sections2.2 and3.3. Native sheafification, tensor and
Ind equivalences are from Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679
(Apache2.0; Markus Himmel, Joël Riou and the Mathlib contributors).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open TopologicalSpace
open CompactSupportIndSheaves

variable (k : Type) [Field k] (X : TopCat.{0})

/-- Restricted Yoneda uses actual maps from every original compact sheaf. -/
def ordinaryRealization : OrdinarySheaf k X ⥤ (CompactSheaf k X)ᵒᵖ ⥤ Type :=
  yoneda ⋙
    (Functor.whiskeringLeft (CompactSheaf k X)ᵒᵖ (OrdinarySheaf k X)ᵒᵖ Type).obj
      (IsCompactSupported k X).ι.op

/-- The sole construction input is the Ind property of that prescribed presheaf. -/
structure OrdinaryIndSource : Prop where
  isInd : ∀ F : OrdinarySheaf k X, IsIndObject ((ordinaryRealization k X).obj F)

/-- The actual ordinary-sheaf embedding in the native compact-support Ind category. -/
def ordinaryToInd (S : OrdinaryIndSource k X) : OrdinarySheaf k X ⥤ IndSheaf k X :=
  ObjectProperty.lift (IsIndObject (C := CompactSheaf k X))
    (ordinaryRealization k X) S.isInd ⋙ (Ind.equivalence (CompactSheaf k X)).inverse

/-- All original compact-generator maps, viewed as ordinary sheaf maps. -/
def compactAsOrdinary : CompactSheaf k X ⥤ OrdinarySheaf k X :=
  (IsCompactSupported k X).ι

variable [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]

/-- Ordinary tensor is fixed by the actual pointwise module tensor and sheafification. -/
def ordinaryTensor : OrdinarySheaf k X × OrdinarySheaf k X ⥤ OrdinarySheaf k X :=
  ((TopCat.Sheaf.forget (ModuleCat.{0} k) X).prod
    (TopCat.Sheaf.forget (ModuleCat.{0} k) X)) ⋙
    tensor ((TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat.{0} k) ⋙
    presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k)

/-- Compactness refers to that same ordinary tensor, on every pair of compact generators. -/
structure CompactTensorSource : Prop where
  compact : ∀ F G : CompactSheaf k X,
    IsCompactSupported k X ((ordinaryTensor k X).obj (F.obj, G.obj))

/-- Tensor of compact generators retains the native tensor on objects and maps. -/
def compactTensor (S : CompactTensorSource k X) :
    CompactSheaf k X × CompactSheaf k X ⥤ CompactSheaf k X where
  obj FG := ⟨(ordinaryTensor k X).obj (FG.1.obj, FG.2.obj), S.compact FG.1 FG.2⟩
  map fg := ObjectProperty.homMk ((ordinaryTensor k X).map (fg.1.hom, fg.2.hom))
  map_id FG := by
    apply ObjectProperty.hom_ext
    exact (ordinaryTensor k X).map_id (FG.1.obj, FG.2.obj)
  map_comp {F G H} fg gh := by
    apply ObjectProperty.hom_ext
    exact (ordinaryTensor k X).map_comp
      (X := (F.1.obj, F.2.obj)) (Y := (G.1.obj, G.2.obj)) (Z := (H.1.obj, H.2.obj))
      (fg.1.hom, fg.2.hom) (gh.1.hom, gh.2.hom)

/-- The exact generator bifunctor whose native Kan extension defines Ind tensor. -/
def tensorGenerators (S : CompactTensorSource k X) :
    CompactSheaf k X × CompactSheaf k X ⥤ IndSheaf k X :=
  compactTensor k X S ⋙ Ind.yoneda

/-- The two native compact-Yoneda embeddings. -/
def compactYonedaPair :
    CompactSheaf k X × CompactSheaf k X ⥤ IndSheaf k X × IndSheaf k X :=
  (Ind.yoneda : CompactSheaf k X ⥤ IndSheaf k X).prod
    (Ind.yoneda : CompactSheaf k X ⥤ IndSheaf k X)

/-- Existence concerns only the prescribed compact-Yoneda tensor extension. -/
structure IndTensorSource (S : CompactTensorSource k X) : Prop where
  hasKan : (compactYonedaPair k X).HasLeftKanExtension
    (tensorGenerators k X S)

/-- Ind tensor is the actual compact-Yoneda left Kan extension. -/
def indTensor (S : CompactTensorSource k X) (D : IndTensorSource k X S) :
    IndSheaf k X × IndSheaf k X ⥤ IndSheaf k X :=
  letI := D.hasKan
  (compactYonedaPair k X).leftKanExtension
    (tensorGenerators k X S)

/-- Its native unit fixes the compact-generator normalization on every tensor map. -/
def tensorGeneratorUnit (S : CompactTensorSource k X) (D : IndTensorSource k X S) :
    tensorGenerators k X S ⟶
      compactYonedaPair k X ⋙ indTensor k X S D :=
  letI := D.hasKan
  (compactYonedaPair k X).leftKanExtensionUnit
    (tensorGenerators k X S)

end MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels
