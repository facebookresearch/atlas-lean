/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.NativeDerivedSpectrumModels
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.Monoidal.Mod.Closed

/-!
# All-level evaluation of the actual native function spectrum

The function-space carrier is level zero of the native internal function
spectrum. Evaluation at any level first inserts the level-zero/level-q
Day-convolution summand into the balanced spectrum tensor. It then uses
the finite-set unit comparison, native braiding and the actual closed
adjunction counit. Every parameter simplex uses this same formula.

Sources: Hovey--Shipley--Smith, *Symmetric spectra*, Section 2.2;
completed Tau Ceti Day-convolution/module source at revision
62bbc0596dc3539d488232e4e924a338548ea0a9, with Apache 2.0 notices
and authors preserved in the imported source ports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeSpectrumFunctionEvaluation

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open StableSpectraInfinitySource NativeDerivedSpectrumModels
open MathlibExt.SpectraSource
open scoped Simplicial DayFunctor

/-- This is the actual complete native spectrum Hom space, including all higher simplices. -/
abbrev nativeFunctionSpace (E F : SymmetricSpectrum) : SSet.{0} :=
  (level ((Mod.internalHom E).obj F) 0).right

/-- Insert the original Day-convolution summand into the native balanced spectrum tensor. -/
def levelTensorInsertion (E F : SymmetricSpectrum) (p q : ℕ) :
    level E p ⊗ level F q ⟶ level (E ⊗ F) (p + q) :=
  (DayFunctor.η E.X F.X).app (FiniteBijection.mk p, FiniteBijection.mk q) ≫
    (Mod.tensorπ E F).natTrans.app (FiniteBijection.mk (p + q))

/-- The finite-unit comparison is applied to the original underlying spectrum sequence. -/
def leftLevelUnit (E : SymmetricSpectrum) (q : ℕ) : level E (0 + q) ⟶ level E q :=
  E.X.functor.map (λ_ (FiniteBijection.mk q)).hom

/-- All-level function evaluation is the original native closed counit on this tensor summand. -/
def functionEvaluation (E F : SymmetricSpectrum) (q : ℕ) :
    level ((Mod.internalHom E).obj F) 0 ⊗ level E q ⟶ level F q :=
  levelTensorInsertion ((Mod.internalHom E).obj F) E 0 q ≫
    leftLevelUnit (((Mod.internalHom E).obj F) ⊗ E) q ≫
    (SymmetricSpectrum.evaluation q).map
      ((β_ ((Mod.internalHom E).obj F) E).hom ≫ (ihom.ev E).app F)

/-- The action on every original higher parameter simplex is this exact counit evaluation. -/
def evaluatedSimplex (E F : SymmetricSpectrum) (q : ℕ) (n : SimplexCategoryᵒᵖ)
    (f : (nativeFunctionSpace E F).obj n) (x : (level E q).right.obj n) :
    (level F q).right.obj n :=
  (functionEvaluation E F q).right.app n (PointedSSet.smashMk f x)

end MathlibExt.AlgebraicTopology.NativeSpectrumFunctionEvaluation
