/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafAlphaBetaModels
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Source-normalized monoidal ordinary and native Ind sheaves

Both tensor functors are identified with the already prescribed native
pointwise/sheafified ordinary tensor and compact-Yoneda Ind tensor.
The ordinary unit is the actual constant coefficient sheaf. Beta is the
native LEFT adjoint of alpha and carries its own strong monoidal source
structure. It supplies beta-A ring objects for DK's local-End module
category, with the full original ordinary coefficient data retained.

Source: DK arXiv:1311.2374v2, Sections 2.2 and 4.10; native tensor,
monoidal functor and Mon constructors: Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IndSheafMonoidalModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open TopologicalSpace CompactSupportIndSheaves IndSheafCoefficientModels IndSheafAlphaBetaModels

variable (k : Type) [Field k] (X : TopCat.{0})
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]

def coefficientUnitSheaf : OrdinarySheaf k X :=
  (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k)).obj (ModuleCat.of k k)

/-- The ordinary source tensor and unit refer to the actual coefficient sheaves. -/
class OrdinaryMonoidalSource where
  [monoidal : MonoidalCategory (OrdinarySheaf k X)]
  [symmetric : SymmetricCategory (OrdinarySheaf k X)]
  tensorComparison : tensor (OrdinarySheaf k X) ≅ ordinaryTensor k X
  unitComparison : 𝟙_ (OrdinarySheaf k X) ≅ coefficientUnitSheaf k X

attribute [instance_reducible, instance] OrdinaryMonoidalSource.monoidal
  OrdinaryMonoidalSource.symmetric

section TopCatOf

/-! Lean 4.36 does not find the generic instances above at `X := TopCat.of M`: their keys keep the
carrier of `X`, which the query reduces to `M`. These restate them at `TopCat.of M`. -/

variable (M : Type) [TopologicalSpace M]
  [HasSheafify (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} k)]
  [OrdinaryMonoidalSource k (TopCat.of M)]

instance ordinaryMonoidalOf : MonoidalCategory (OrdinarySheaf k (TopCat.of M)) :=
  OrdinaryMonoidalSource.monoidal
instance ordinarySymmetricOf : SymmetricCategory (OrdinarySheaf k (TopCat.of M)) :=
  OrdinaryMonoidalSource.symmetric

end TopCatOf

def ordinaryUnitSection (U : Opens X) (c : k) :
    (coefficientUnitSheaf k X).presheaf.obj (Opposite.op U) :=
  ((toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of k k))).app (Opposite.op U)).hom c

def ordinaryTensorSection (F G : OrdinarySheaf k X) (U : Opens X)
    (f : F.presheaf.obj (Opposite.op U)) (g : G.presheaf.obj (Opposite.op U)) :
    ((ordinaryTensor k X).obj (F, G)).presheaf.obj (Opposite.op U) :=
  ((toSheafify (Opens.grothendieckTopology X) (F.presheaf ⊗ G.presheaf)).app
    (Opposite.op U)).hom (f ⊗ₜ[k] g)

def sourceUnitSection [S : OrdinaryMonoidalSource k X] (U : Opens X) (c : k) :
    (𝟙_ (OrdinarySheaf k X)).presheaf.obj (Opposite.op U) :=
  (S.unitComparison.inv.hom.app (Opposite.op U)).hom (ordinaryUnitSection k X U c)

def sourceTensorSection [S : OrdinaryMonoidalSource k X] (F G : OrdinarySheaf k X)
    (U : Opens X) (f : F.presheaf.obj (Opposite.op U))
    (g : G.presheaf.obj (Opposite.op U)) : (F ⊗ G).presheaf.obj (Opposite.op U) :=
  ((S.tensorComparison.inv.app (F, G)).hom.app (Opposite.op U)).hom
    (ordinaryTensorSection k X F G U f g)

variable (T : CompactTensorSource k X) (I : IndTensorSource k X T)

/-- The Ind tensor is the original complete compact-Yoneda extension. -/
class IndMonoidalSource where
  [monoidal : MonoidalCategory (IndSheaf k X)]
  [symmetric : SymmetricCategory (IndSheaf k X)]
  tensorComparison : tensor (IndSheaf k X) ≅ indTensor k X T I

attribute [instance_reducible, instance] IndMonoidalSource.monoidal IndMonoidalSource.symmetric

variable (A : AlphaSource k X) (B : BetaSource k X A)
  [OrdinaryMonoidalSource k X] [IndMonoidalSource k X T I]

/-- Strong monoidal construction for the prescribed beta, without identifying it with iota. -/
class BetaMonoidalSource where
  [braided : (beta k X A B).Braided]

attribute [instance_reducible, instance] BetaMonoidalSource.braided

/-- The strong monoidal data is the same data carried by the braided functor. -/
abbrev BetaMonoidalSource.monoidal (S : BetaMonoidalSource k X T I A B) :
    (beta k X A B).Monoidal := S.braided.toMonoidal

/-- Native mapping of the actual ordinary ring monoid through beta. -/
def betaMonoid (S : BetaMonoidalSource k X T I A B) :
    Mon (OrdinarySheaf k X) ⥤ Mon (IndSheaf k X) :=
  letI := S.monoidal
  (beta k X A B).mapMon

end MathlibExt.AlgebraicGeometry.IndSheafMonoidalModels
