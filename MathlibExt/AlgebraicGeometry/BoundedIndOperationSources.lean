/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundedIndImageModels
public import MathlibExt.AlgebraicGeometry.IndSheafBoundedTensorModels

/-!
# Normalized source data for the actual bounded Ind operations

These records collect only structural source proofs for already fixed
native operators. They contain no new object, carrier or functor.
The exposed operations are the same native tensor/localization and
compact-generator images, preserving their original objects and maps.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2,3.3--3.4 and4.1;
the exact native/source credits remain in the imported primitives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundedIndOperationSources

open _root_.CategoryTheory
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafInverseImageModels
open IndSheafPushforwardModels BoundedIndImageModels IndSheafBoundedTensorModels

variable (k : Type) [Field k]

local instance operationAbelianPreadditive (X : TopCat.{0}) [CompactSheafSource k X] :
    Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

section Tensor

variable (X : TopCat.{0}) [CompactSheafSource k X]
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]

/-- The condition, for ind-sheaves of $k$-vector spaces on $X$ ($k$ a field), that the sheafified
tensor product of two compactly supported sheaves is compactly supported (`compact`); that this
tensor product of compact generators, followed by the Yoneda embedding, has a left Kan extension
along the product of the Yoneda embeddings into ind-sheaves, the tensor product of ind-sheaves
(`ind`); that the latter is additive in each variable and every pair of cochain complexes of
ind-sheaves has a total tensor complex (`cochain`); that every termwise bounded complex has bounded
cohomology (`cohomology`) and the localization functor from termwise bounded complexes to the
bounded derived category is a localization at the quasi-isomorphisms (`localization`); that the
total tensor complex of two termwise bounded complexes is termwise bounded (`bounded`); and that
the total tensor complex followed by the localization functor inverts quasi-isomorphisms in each
variable (`derived`). -/
structure TensorSource : Prop where
  compact : CompactTensorSource k X
  ind : IndTensorSource k X compact
  [cochain : TensorCochainSource k X compact ind]
  cohomology : BoundedCohomologySource k X
  localization : BoundedLocalizationSource k X cohomology
  bounded : BoundedTensorSource k X compact ind
  derived : DerivedTensorSource k X compact ind cohomology bounded

/-- The derived tensor product on the bounded derived category of ind-sheaves of $k$-vector spaces
on $X$, under the conditions $S$: the bifunctor induced, through the localization of termwise
bounded complexes at quasi-isomorphisms in each variable, by the total tensor complex of two
termwise bounded complexes followed by the localization functor. -/
def tensorFunctor (S : TensorSource k X) :
    BoundedIndDerived k X ⥤ BoundedIndDerived k X ⥤ BoundedIndDerived k X :=
  letI := S.cochain
  derivedTensor k X S.compact S.ind S.cohomology S.localization S.bounded S.derived

end Tensor

section Inverse

variable {X Y : TopCat.{0}} [CompactSheafSource k X] [CompactSheafSource k Y] (f : X ⟶ Y)

/-- The condition, for a continuous map $f : X \to Y$ and ind-sheaves of $k$-vector spaces ($k$ a
field), that for every sheaf $F$ on $X$ the functor $G \mapsto \mathrm{Hom}(G, F)$ on compactly
supported sheaves $G$ is an ind-object, which defines the ind-sheaf of $F$ (`ordinary`); that the
functor sending a compactly supported sheaf $G$ on $Y$ to the ind-sheaf of $f^{-1} G$ has a left
Kan extension along the Yoneda embedding into ind-sheaves on $Y$, the inverse image of ind-sheaves
(`ind`); that this inverse image is additive (`additive`); that, applied termwise to cochain
complexes and followed by the localization functor, it inverts quasi-isomorphisms (`exact`), so
that it induces a functor of derived categories; and that this functor sends bounded objects to
bounded objects (`bounded`). -/
structure InverseSource : Prop where
  ordinary : OrdinaryIndSource k X
  ind : IndInverseImageSource k f ordinary
  [additive : (indInverseImage k f ordinary ind).Additive]
  exact : ExactIndInverseImageSource k f ordinary ind
  bounded : BoundedInverseImageSource k f ordinary ind exact

/-- The actual bounded inverse image constructed from those exact original generator proofs. -/
def inverseFunctor (S : InverseSource k f) : BoundedIndDerived k Y ⥤ BoundedIndDerived k X :=
  letI := S.additive
  boundedInverseImage k f S.ordinary S.ind S.exact S.bounded

end Inverse

section Proper

variable {X Y : TopCat.{0}} [CompactSheafSource k X] [CompactSheafSource k Y] (f : X ⟶ Y)

/-- The condition, for a continuous map $f : X \to Y$ and ind-sheaves of $k$-vector spaces ($k$ a
field), that the direct image $f_* G$ of every compactly supported sheaf $G$ on $X$ is compactly
supported (`compact`); that the functor sending a compactly supported sheaf $G$ on $X$ to $f_* G$,
as an ind-sheaf on $Y$, has a left Kan extension along the Yoneda embedding into ind-sheaves on
$X$, the proper direct image of ind-sheaves (`ind`); that this direct image is additive
(`additive`); that, applied termwise to cochain complexes and followed by the localization
functor, it has a total right derived functor with respect to quasi-isomorphisms (`derived`); and
that this derived functor sends bounded objects to bounded objects (`bounded`). -/
structure ProperSource : Prop where
  compact : CompactPushforwardSource k f
  ind : IndPushforwardSource k f compact
  [additive : (indProperImage k f compact ind).Additive]
  derived : DerivedIndPushforwardSource k f compact ind
  bounded : BoundedProperImageSource k f compact ind derived

/-- The actual bounded proper image of that same prescribed compact-generator extension. -/
def properFunctor (S : ProperSource k f) : BoundedIndDerived k X ⥤ BoundedIndDerived k Y :=
  letI := S.additive
  boundedProperImage k f S.compact S.ind S.derived S.bounded

end Proper

end MathlibExt.AlgebraicGeometry.BoundedIndOperationSources
