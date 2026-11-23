/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGMoritaClosedModels
public import MathlibExt.CategoryTheory.PerfectDGModuleModels

/-!
# Actual enveloping modules and the derived diagonal

A curried bimodule C→RightModule(D) has the actual variance
C×Dᵒᵖ→Ch(k). It is a right module over Cᵒᵖ tensor D. The
uncurrying output fixes every value and every homogeneous pure-tensor
action by native DG composition. It does not freely choose a diagonal.

The diagonal is the identity graph, uncurried by that same model.
Its perfection is a genuine localized finite-cell retraction over the
native enveloping DG category. A cofibrant diagonal replacement is the
actual augmented module replacement. The cochain corepresentable
functor below is a completed adapter of native postcomposition.

References: Keller, Deriving DG categories, §6; Toën,
arXiv:math/0408337v7, §3; Brav--Dyckerhoff, arXiv:1606.00619v1, §2.1.
The corepresentable adapter uses dgPostcomp/ofDGMap from the completed
Tau Ceti contributors' Apache 2.0 source at62bbc0596dc3539d488232e4e924a338548ea0a9,
CategoryTheory/DG/Representables.lean and DG/Functor/Basic.lean;
their original notices and exact file URLs remain in DGSource.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGMoritaClosedModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels

universe u v

variable {k : Type u} [CommRing k]

/-- Native postcomposition is the actual covariant cochain Hom functor. -/
def cochainCorepresentable {C : Type v} [DGCategory k C] (x : C) :
    EnrichedFunctor (Cochains k) C (Cochains k) :=
  EnrichedFunctor.ofDGMap (fun y => dgHomComplex k x y)
    (fun {a b} n => dgPostcomp k (op x) (X := a) (X' := b) n)
    (fun _n f => dgPostcomp_dgDifferential k (op x) f)
    (fun y => dgPostcomp_dgId k (op x) y)
    (fun a b h => dgPostcomp_dgComp k (op x) a b h)

/-- The actual opposite coefficient DG category. -/
def oppositeCategory (C : DGCat k) : DGCat k := DGCat.of k Cᵒᵖ

/-- The native enveloping category with the source-correct module variance. -/
def enveloping (C D : DGCat k) : DGCat k := tensor (oppositeCategory C) D

/-- The right-enveloping-module point associated with x∈C and y∈Dᵒᵖ. -/
def moduleIndex (C D : DGCat k) (x : C) (y : Dᵒᵖ) : (enveloping C D)ᵒᵖ :=
  op (op x, y.unop)

/-- An actual pure homogeneous tensor in the right-module indexing category. -/
def tensorArrow {C D : DGCat k} {x x' : C} {y y' : Dᵒᵖ}
    {p q r : ℤ} (a : DGHom k p x x') (b : DGHom k q y y') (h : p + q = r) :
    DGHom k r (moduleIndex C D x y) (moduleIndex C D x' y') :=
  ((HomologicalComplex.ιTensorObj (dgHomComplex k x x') (dgHomComplex k y y')
    p q r h).hom) (TensorProduct.tmul k a b)

/-- Source-normalized uncurrying fixes every actual module value and tensor action. -/
structure EnvelopingModuleModel {C D : DGCat k} (M : Bimodule k C D) where
  module : RightModule k (enveloping C D)
  value_eq : ∀ (x : C) (y : Dᵒᵖ),
    module.toEnrichedFunctor.obj (moduleIndex C D x y) =
      (M.toEnrichedFunctor.obj x).toEnrichedFunctor.obj y
  action_eq : ∀ (x x' : C) (y y' : Dᵒᵖ) (p q r : ℤ)
    (a : DGHom k p x x') (b : DGHom k q y y') (h : p + q = r),
    HEq (module.toEnrichedFunctor.dgMap r (tensorArrow a b h))
      (dgComp k (DGFunctor.dgApp k p y (M.toEnrichedFunctor.dgMap p a))
        ((M.toEnrichedFunctor.obj x').toEnrichedFunctor.dgMap q b) h)

/-- The actual curried diagonal, without an arbitrary bimodule carrier. -/
def diagonal (C : DGCat k) : Bimodule k C C := graph (𝟙 C)

/-- Homological smoothness over a field: the fixed diagonal is perfect over the enveloping
category `Cᵒᵖ ⊗ C`. Over a field every cochain complex is K-flat, so this underived tensor computes
the derived envelope `Cᵒᵖ ⊗ᴸ C` of Toën--Vaquié, Definition 2.4(4). Over a general base the two
differ (for `𝔽_p` over `ℤ` the derived envelope has an exterior generator in degree `-1`), so the
predicate is only stated over fields. -/
def IsHomologicallySmooth {k : Type u} [Field k] (C : DGCat k)
    (D : EnvelopingModuleModel (diagonal C)) : Prop :=
  IsPerfectModule (enveloping C C) D.module

/-- A native cofibrant diagonal augmentation, with no CY comparison in its input. -/
abbrev CofibrantDiagonal {C : DGCat k} (D : EnvelopingModuleModel (diagonal C)) :=
  ModuleReplacement D.module

/-- The actual cochain value used for the inverse dualizing bimodule.
The representable point swaps x,y, retaining the left-CY bimodule variance. -/
def inverseDualizingValue {C : DGCat k} {D : EnvelopingModuleModel (diagonal C)}
    (P : CofibrantDiagonal D) (x : C) (y : Cᵒᵖ) : Cochains k :=
  dgHomComplex k P.module
    ((dgYoneda k (C := enveloping C C)).obj (op y.unop, x))

end MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
