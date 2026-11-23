/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowGroupCompletion

noncomputable section

open CategoryTheory

universe u

/-- The actual model action is the original public row-matrix isomorphism. -/
example (R : Type u) [Ring R] (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (eqToIso (AlgebraicKTheory.StableGL.finiteFreeRowCoreModelFunctor_obj R n
      (SingleObj.star _))).symm ≪≫
      ((AlgebraicKTheory.StableGL.finiteFreeRowCoreModelFunctor R n).map
        (X := SingleObj.star _) (Y := SingleObj.star _) g).iso ≪≫
      eqToIso (AlgebraicKTheory.StableGL.finiteFreeRowCoreModelFunctor_obj R n
        (SingleObj.star _)) = FGProjectiveCat.IdempotentModel.freeAut R n g :=
  AlgebraicKTheory.StableGL.finiteFreeRowCoreModelFunctor_map_iso R n g

/-- Both zero-component coordinates are the same actual free object over any Ring. -/
example (R : Type u) [Ring R] (n : ℕ) :
    ((AlgebraicKTheory.StableGL.finiteFreeRowZeroComponentFunctor R n).obj
      (SingleObj.star _)).obj =
      (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n,
        (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
        SInverseS.Pair (FGProjectiveCat.IdempotentModel R)) :=
  AlgebraicKTheory.StableGL.finiteFreeRowZeroComponentFunctor_obj R n _

/-- The selected rank-zero point has the actual arrow to the canonical zero pair. -/
example (R : Type u) [Ring R] :
    (AlgebraicKTheory.StableGL.finiteFreeRowZeroComponentFunctor R 0).obj
      (SingleObj.star _) ⟶
        SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R) :=
  AlgebraicKTheory.StableGL.finiteFreeRowStageZeroToBase R

/-- All original finite matrix loops satisfy the actual successor square. -/
example (R : Type u) [Ring R] (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (AlgebraicKTheory.StableGL.finiteFreeRowZeroComponentFunctor R n).map g ≫
        AlgebraicKTheory.StableGL.finiteFreeRowSuccessorArrow R n =
      AlgebraicKTheory.StableGL.finiteFreeRowSuccessorArrow R n ≫
        (AlgebraicKTheory.StableGL.finiteFreeRowZeroComponentFunctor R (n + 1)).map
          (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop g))) :=
  AlgebraicKTheory.StableGL.finiteFreeRowSuccessorArrow_naturality R n g

/-- The successor transformation has the literal original stage/source functors. -/
example (R : Type u) [Ring R] (n : ℕ) :
    AlgebraicKTheory.StableGL.finiteFreeRowZeroComponentFunctor R n ⟶
      AlgebraicKTheory.StableGL.finiteOppositeGLRowStabilizationFunctor R n ⋙
        AlgebraicKTheory.StableGL.finiteFreeRowZeroComponentFunctor R (n + 1) :=
  AlgebraicKTheory.StableGL.finiteFreeRowSuccessorNatTrans R n

/-- The original categorical telescope of every Ring has a derived diagonal row comparison. -/
example (R : Type u) [Ring R] :
    AlgebraicKTheory.StableGL.FiniteBGLTelescopeCategory R ⥤
      SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) :=
  AlgebraicKTheory.StableGL.finiteBGLTelescopeToRowZeroComponent R

/-- The original chosen stage-zero vertex retains its literal comparison image. -/
example (R : Type u) [Ring R] :
    (AlgebraicKTheory.StableGL.finiteBGLTelescopeToRowZeroComponent R).obj
        (AlgebraicKTheory.StableGL.finiteBGLTelescopeBaseObject R) =
      (AlgebraicKTheory.StableGL.finiteFreeRowZeroComponentFunctor R 0).obj
        (SingleObj.star _) :=
  AlgebraicKTheory.StableGL.finiteBGLTelescopeToRowZeroComponent_base R

/-- Every original simplex retains the actual row telescope functor value. -/
example (R : Type u) [Ring R] (D : SimplexCategoryᵒᵖ)
    (X : (nerve (AlgebraicKTheory.StableGL.FiniteBGLTelescopeCategory R)).obj D) :
    (AlgebraicKTheory.StableGL.finiteBGLTelescopeToRowZeroComponentNerve R).app D X =
      (Functor.mapComposableArrows
        (AlgebraicKTheory.StableGL.finiteBGLTelescopeToRowZeroComponent R) D.unop.len).obj X :=
  AlgebraicKTheory.StableGL.finiteBGLTelescopeToRowZeroComponentNerve_app R D X

/-- The actual ordinary comparison exists over every Ring at its original carrier level. -/
example (R : Type u) [Ring R] :
    SSet.toTop.obj (nerve (AlgebraicKTheory.StableGL.FiniteBGLTelescopeCategory R)) ⟶
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) :=
  AlgebraicKTheory.StableGL.finiteBGLTelescopeToRowZeroComponentTop R
