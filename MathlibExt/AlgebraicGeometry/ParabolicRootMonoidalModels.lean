/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ParabolicRootComparisonMaps
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Native monoidal realization of the balanced parabolic tensor

The target is the existing actual Parabolic category. Its tensor is
identified, on objects and arrows, with the independently specified
balanced bilinear universal tensor. Its unit is the actual DF-weight
colimit. The native monoidal functor has precisely the preceding
direct-image/root-section tensor map and adjunction/unit-colimit map.
Equivalence and abelian-category proofs are output conditions.

Source: Borne–Vistoli arXiv:1001.0466v2, Section5.3 and Theorem6.1.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ParabolicRootMonoidalModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.CartesianStackModules _root_.AlgebraicGeometry.CartesianStackTensorProducts
open DeligneFaltingsCategories DeligneFaltingsSheaves DenominatorRootStacks EtaleMonoidInverseImage
open ParabolicSheafCategories RootWeightEvaluations GlobalParabolicRootModels
open ParabolicBilinearTensorModels ParabolicRootComparisonMaps

variable {X : Scheme.{0}}
  [∀ (Y Z : Scheme.{0}) (f : Y ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (j : A ⟶ B) (G : GroupifiedDF D)
  (R : DenominatorRootStacks.Model I D j (𝟙 X)) (TG : TensorLanding R.stack)
  (C : EtaleRootData I D j G R) (P : PhiAssembly I D j G R C)
  (S : StructuralRestriction I D j G R TG C)
  (T : TensorModel G j)
  (K : ∀ U : X.Etale, LineFunctorLaws (G.chart U)) (UO : UnitModel G j K)

/-- Monoidal structure is source integration on the actual category;
its tensor and unit are fixed independently by their native universal properties. The
unitors and associator are not fixed here: a strong monoidal comparison determines them. -/
structure MonoidalRealization where
  monoidal : MonoidalCategory (Parabolic G j)
  unit_eq : letI := monoidal; (𝟙_ (Parabolic G j)) = UO.object
  tensor_eq : letI := monoidal
    ∀ E F : Parabolic G j, E ⊗ F = (T.functor.obj E).obj F
  tensor_maps : letI := monoidal
    ∀ {E E' F F' : Parabolic G j} (a : E ⟶ E') (b : F ⟶ F'),
      (a ⊗ₘ b) ≫ eqToHom (tensor_eq E' F') =
        eqToHom (tensor_eq E F) ≫ (T.functor.map a).app F ≫ (T.functor.obj E').map b

variable (Bilin : TensorBilinearity I D j G R TG C P S)
  (N : UnitCocones I D j G R TG C S K)
  (V : UnitComparison I D j G R TG C P S K UO N)
  (M : MonoidalRealization D j G T K UO)

/-- Native strong monoidal data on the fixed Phi, with both structure
maps equal to the actual native comparison recipes. -/
structure PhiMonoidal where
  monoidal : letI := CartesianStackTensorComparisons.monoidal R.stack TG
    letI := M.monoidal
    P.functor.Monoidal
  unit_normalization : letI := CartesianStackTensorComparisons.monoidal R.stack TG
    letI := M.monoidal
    letI := monoidal
    Functor.LaxMonoidal.ε P.functor = eqToHom M.unit_eq ≫ V.map
  tensor_normalization : letI := CartesianStackTensorComparisons.monoidal R.stack TG
    letI := M.monoidal
    letI := monoidal
    ∀ F H : QCoh R.stack,
      Functor.LaxMonoidal.μ P.functor F H =
        eqToHom (M.tensor_eq (P.functor.obj F) (P.functor.obj H)) ≫
          tensorComparison I D j G R TG C P S T Bilin F H

/-- Full source theorem conclusion; no equivalence or abelian structure
is an input to the actual parabolic category or its tensor. -/
structure BorneVistoliComparison where
  monoidal : PhiMonoidal I D j G R TG C P S T K UO Bilin N V M
  isEquivalence : P.functor.IsEquivalence
  sourceAbelian : Abelian (QCoh R.stack)
  targetAbelian : Abelian (Parabolic G j)

end MathlibExt.AlgebraicGeometry.ParabolicRootMonoidalModels
