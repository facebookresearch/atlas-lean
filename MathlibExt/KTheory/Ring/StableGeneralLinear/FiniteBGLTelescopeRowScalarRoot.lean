/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeRowScalarNatIso

/-!
# Original rank-zero root coherence of telescope scalar naturality

The two root isomorphisms use the original free-zero comparison in both
coordinates and the actual additive zero-object comparisons. The verified
scalar component at the original telescope vertex commutes with these
same root isomorphisms. No root trace or comparison witness is an input.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe uR uS uC vC

namespace AlgebraicKTheory.StableGL

private def diagonalIso
    {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
    [HasZeroObject C] [HasBinaryBiproducts C] {X Y : C} (e : X ≅ Y) :
    (⟨X, X⟩ : SInverseS.Pair C) ≅ ⟨Y, Y⟩ :=
  (SInverseS.corePairInclusion (C := C)).mapIso
    ((Core.isoMk (x := ⟨X⟩) (y := ⟨Y⟩) e).prod
      (Core.isoMk (x := ⟨X⟩) (y := ⟨Y⟩) e))

private theorem diagonalIso_trans
    {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
    [HasZeroObject C] [HasBinaryBiproducts C] {X Y Z : C}
    (e : X ≅ Y) (g : Y ≅ Z) :
    diagonalIso (e ≪≫ g) = diagonalIso e ≪≫ diagonalIso g := by
  let a := (Core.isoMk (x := ⟨X⟩) (y := ⟨Y⟩) e).prod
    (Core.isoMk (x := ⟨X⟩) (y := ⟨Y⟩) e)
  let b := (Core.isoMk (x := ⟨Y⟩) (y := ⟨Z⟩) g).prod
    (Core.isoMk (x := ⟨Y⟩) (y := ⟨Z⟩) g)
  let c := (Core.isoMk (x := ⟨X⟩) (y := ⟨Z⟩) (e ≪≫ g)).prod
    (Core.isoMk (x := ⟨X⟩) (y := ⟨Z⟩) (e ≪≫ g))
  have h : a.hom ≫ b.hom = c.hom := by
    apply Prod.ext <;> apply Core.hom_ext <;> rfl
  let J := SInverseS.corePairInclusion (C := C)
  apply Iso.ext
  exact (congrArg J.map h).symm.trans (J.map_comp a.hom b.hom)

private theorem rootedIsoSquare
    {C : Type uC} [Category.{vC} C] {A B X Y Z : C}
    (p : A ≅ X) (q : B ≅ Y) (e : A ≅ B) (r : X ≅ Z) (s : Y ≅ Z)
    (h : (p.symm ≪≫ e ≪≫ q) ≪≫ s = r) : e ≪≫ q ≪≫ s = p ≪≫ r := by
  apply Iso.ext
  apply (cancel_epi p.inv).1
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    using congrArg Iso.hom h

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private abbrev sourceFunctor (f : R →+* S) :=
  (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
    FGProjectiveCat.scalarExtension.{uR, uS, uR} f

private abbrev targetFunctor.{uTargetRoot, uCarrierRoot}
    (S : Type uTargetRoot) [Ring S] :
    FGProjectiveCat.IdempotentModel S ⥤ FGProjectiveCat.{max uTargetRoot uCarrierRoot} S :=
  (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
    (FGProjectiveCat.universeEquivalence.{uTargetRoot, uCarrierRoot} S).inverse

private def sourceZeroIso (f : R →+* S) :
    (sourceFunctor f).obj
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ)) ≅
      (0 : FGProjectiveCat.{max uS uR} S) :=
  (sourceFunctor f).mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso R) ≪≫
    (sourceFunctor f).mapZeroObject

private def targetZeroIso.{uTargetZero, uCarrierZero}
    {S : Type uTargetZero} [Ring S] :
    (targetFunctor.{uTargetZero, uCarrierZero} S).obj
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj (0 : ℕ)) ≅
      (0 : FGProjectiveCat.{max uTargetZero uCarrierZero} S) :=
  (targetFunctor.{uTargetZero, uCarrierZero} S).mapIso
      (FGProjectiveCat.IdempotentModel.freeZeroIso S) ≪≫
    (targetFunctor.{uTargetZero, uCarrierZero} S).mapZeroObject

/-- The source root is the two original free-zero isomorphisms after actual scalar extension. -/
public def finiteBGLTelescopeScalarSourceRootIso (f : R →+* S) :
    (finiteBGLTelescopeToRowZeroComponent R ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι ⋙
        SInverseS.pairFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{uR, uS, uR} f)).obj (finiteBGLTelescopeBaseObject R) ≅
      (⟨0, 0⟩ : SInverseS.Pair (FGProjectiveCat.{max uS uR} S)) :=
  eqToIso (finiteBGLTelescopeRowScalar_source_obj f (finiteBGLTelescopeBaseObject R)) ≪≫
    diagonalIso (sourceZeroIso f)

/-- The target root uses the same original stage-zero vertex and target free-zero comparisons. -/
public def finiteBGLTelescopeScalarTargetRootIso (f : R →+* S) :
    (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel S)).ι ⋙
        SInverseS.pairFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse)).obj
        (finiteBGLTelescopeBaseObject R) ≅
      (⟨0, 0⟩ : SInverseS.Pair (FGProjectiveCat.{max uS uR} S)) :=
  eqToIso (finiteBGLTelescopeRowScalar_target_obj f (finiteBGLTelescopeBaseObject R)) ≪≫
    diagonalIso (targetZeroIso.{uS, uR} (S := S))

/-- The actual scalar component commutes with the two original rank-zero root routes. -/
public theorem finiteBGLTelescopeRowScalarPairIso_original_root (f : R →+* S) :
    (finiteBGLTelescopeRowScalarPairIso f).app (finiteBGLTelescopeBaseObject R) ≪≫
        finiteBGLTelescopeScalarTargetRootIso f = finiteBGLTelescopeScalarSourceRootIso f := by
  let X := finiteBGLTelescopeBaseObject R
  let p := eqToIso (finiteBGLTelescopeRowScalar_source_obj f X)
  let q := eqToIso (finiteBGLTelescopeRowScalar_target_obj f X)
  let e := (finiteBGLTelescopeRowScalarPairIso f).app X
  let r := diagonalIso (sourceZeroIso f)
  let s := diagonalIso (targetZeroIso.{uS, uR} (S := S))
  have hScalar : finiteFreeRowScalarIso f 0 ≪≫ targetZeroIso.{uS, uR} (S := S) = sourceZeroIso f :=
    (finiteFreeRowScalarIso_zero f).symm
  have hRoot : diagonalIso (finiteFreeRowScalarIso f 0) ≪≫ s = r :=
    (diagonalIso_trans (finiteFreeRowScalarIso f 0) (targetZeroIso.{uS, uR} (S := S))).symm.trans
      (congrArg diagonalIso hScalar)
  have hComponent : p.symm ≪≫ e ≪≫ q = diagonalIso (finiteFreeRowScalarIso f 0) :=
    finiteBGLTelescopeRowScalarPairIso_app_after_obj f X
  have h : (p.symm ≪≫ e ≪≫ q) ≪≫ s = r :=
    (congrArg (fun k => k ≪≫ s) hComponent).trans hRoot
  exact rootedIsoSquare p q e r s h

end AlgebraicKTheory.StableGL

noncomputable section

open CategoryTheory

universe uScalarRootValueR uScalarRootValueS

namespace AlgebraicKTheory.StableGL

variable {R : Type uScalarRootValueR} {S : Type uScalarRootValueS} [Ring R] [Ring S]

private theorem finiteBGLTelescopeScalarSourceRootIsoValueComputed (f : R →+* S) :
    finiteBGLTelescopeScalarSourceRootIso f =
      eqToIso (finiteBGLTelescopeRowScalar_source_obj f (finiteBGLTelescopeBaseObject R)) ≪≫
(SInverseS.corePairInclusion (C := FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR}
    S)).mapIso
  ((Core.isoMk (x := ⟨((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR} f).obj
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ))⟩) (y := ⟨(0 :
      FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR} S)⟩)
      (((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR}
      f).mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso R) ≪≫
  ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR}
      f).mapZeroObject)).prod (Core.isoMk (x := ⟨((FGProjectiveCat.IdempotentModel.equivalence
      R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR} f).obj
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ))⟩) (y := ⟨(0 :
      FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR} S)⟩)
      (((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR}
      f).mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso R) ≪≫
  ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR}
      f).mapZeroObject))) := by
  rfl

/-- The SAME original source root Iso has its actual two-coordinate
freeZeroIso/mapZeroObject value, retaining the original object transport. -/
public theorem finiteBGLTelescopeScalarSourceRootIso_value (f : R →+* S) :
    finiteBGLTelescopeScalarSourceRootIso f =
      eqToIso (finiteBGLTelescopeRowScalar_source_obj f (finiteBGLTelescopeBaseObject R)) ≪≫
(SInverseS.corePairInclusion (C := FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR}
    S)).mapIso
  ((Core.isoMk (x := ⟨((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR} f).obj
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ))⟩) (y := ⟨(0 :
      FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR} S)⟩)
      (((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR}
      f).mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso R) ≪≫
  ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR}
      f).mapZeroObject)).prod (Core.isoMk (x := ⟨((FGProjectiveCat.IdempotentModel.equivalence
      R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR} f).obj
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ))⟩) (y := ⟨(0 :
      FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR} S)⟩)
      (((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR}
      f).mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso R) ≪≫
  ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
  FGProjectiveCat.scalarExtension.{uScalarRootValueR, uScalarRootValueS, uScalarRootValueR}
      f).mapZeroObject))) :=
  finiteBGLTelescopeScalarSourceRootIsoValueComputed f

private theorem finiteBGLTelescopeScalarTargetRootIsoValueComputed (f : R →+* S) :
    finiteBGLTelescopeScalarTargetRootIso f =
      eqToIso (finiteBGLTelescopeRowScalar_target_obj f (finiteBGLTelescopeBaseObject R)) ≪≫
(SInverseS.corePairInclusion (C := FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR}
    S)).mapIso
  ((Core.isoMk (x := ⟨((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR} S).inverse).obj
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj (0 : ℕ))⟩) (y := ⟨(0 :
      FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR} S)⟩)
      (((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR} S).inverse).mapIso
      (FGProjectiveCat.IdempotentModel.freeZeroIso S) ≪≫
  ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR}
      S).inverse).mapZeroObject)).prod (Core.isoMk (x :=
      ⟨((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR} S).inverse).obj
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj (0 : ℕ))⟩) (y := ⟨(0 :
      FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR} S)⟩)
      (((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR} S).inverse).mapIso
      (FGProjectiveCat.IdempotentModel.freeZeroIso S) ≪≫
  ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR}
      S).inverse).mapZeroObject))) := by
  rfl

/-- The SAME original target root Iso has its actual two-coordinate
freeZeroIso/mapZeroObject value, retaining the original object transport. -/
public theorem finiteBGLTelescopeScalarTargetRootIso_value (f : R →+* S) :
    finiteBGLTelescopeScalarTargetRootIso f =
      eqToIso (finiteBGLTelescopeRowScalar_target_obj f (finiteBGLTelescopeBaseObject R)) ≪≫
(SInverseS.corePairInclusion (C := FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR}
    S)).mapIso
  ((Core.isoMk (x := ⟨((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR} S).inverse).obj
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj (0 : ℕ))⟩) (y := ⟨(0 :
      FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR} S)⟩)
      (((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR} S).inverse).mapIso
      (FGProjectiveCat.IdempotentModel.freeZeroIso S) ≪≫
  ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR}
      S).inverse).mapZeroObject)).prod (Core.isoMk (x :=
      ⟨((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR} S).inverse).obj
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj (0 : ℕ))⟩) (y := ⟨(0 :
      FGProjectiveCat.{max uScalarRootValueS uScalarRootValueR} S)⟩)
      (((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR} S).inverse).mapIso
      (FGProjectiveCat.IdempotentModel.freeZeroIso S) ≪≫
  ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
  (FGProjectiveCat.universeEquivalence.{uScalarRootValueS, uScalarRootValueR}
      S).inverse).mapZeroObject))) :=
  finiteBGLTelescopeScalarTargetRootIsoValueComputed f

end AlgebraicKTheory.StableGL

end
