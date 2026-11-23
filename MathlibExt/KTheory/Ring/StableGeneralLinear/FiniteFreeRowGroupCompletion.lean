/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel
public import MathlibExt.CategoryTheory.Monoidal.GroupCompletion
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTotalTranslationAction
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Functor.OfSequence
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpaceTelescope
public import MathlibExt.CategoryTheory.Grothendieck.FunctorFrom
public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import MathlibExt.CategoryTheory.NerveCommonHom
public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.AlgebraicTopology.SingularHomology.Integral
public import MathlibExt.CategoryTheory.Monoidal.SInverseSLocalizedCoreHomology
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowLocalization
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingColimit
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingCofibration
public import MathlibExt.CategoryTheory.NerveSingleObj
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyComp
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Original opposite-row finite GL maps to the small projective zero component

The established row action and actual free-object comparison give a finite
GL map at the literal diagonal pair in the existing idempotent projective
model. Rank zero maps to the selected zero pair. Invertibility of the
telescope or homology comparisons is not asserted in this owner.
-/

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private abbrev rowFree (n : ℕ) : FGProjectiveCat.IdempotentModel R :=
  (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n

private def rowFreeAutMulEquiv (n : ℕ) :
    (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ≃* Aut (rowFree R n) :=
  (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv R n).trans
    (((FGProjectiveCat.IdempotentModel.equivalence R).fullyFaithfulFunctor.autMulEquivOfFullyFaithful
        (rowFree R n)).trans
      (FGProjectiveCat.IdempotentModel.freeIso R n).conjAut).symm

private theorem rowFreeAutMulEquiv_asIso (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (rowFreeAutMulEquiv R n g).asIso =
      FGProjectiveCat.IdempotentModel.freeAut R n g := by
  let E := FGProjectiveCat.IdempotentModel.equivalence R
  let e : Aut (rowFree R n) ≃* Aut (FGProjectiveCat.standardFree R n) :=
    (E.fullyFaithfulFunctor.autMulEquivOfFullyFaithful (rowFree R n)).trans
      (FGProjectiveCat.IdempotentModel.freeIso R n).conjAut
  have hfree : e (Aut.of (FGProjectiveCat.IdempotentModel.freeAut R n g)) =
      FGProjectiveCat.finiteOppositeGLAutRowMulEquiv R n g := by
    change (FGProjectiveCat.IdempotentModel.freeIso R n).conjAut
        (Aut.of (E.functor.mapIso
          (FGProjectiveCat.IdempotentModel.freeAut R n g))) = _
    exact ((FGProjectiveCat.IdempotentModel.free_block_characteristic R).2.2.2.1 n g).2.2
  have he : rowFreeAutMulEquiv R n g =
      Aut.of (FGProjectiveCat.IdempotentModel.freeAut R n g) := by
    apply e.injective
    have hrow : rowFreeAutMulEquiv R n g =
        e.symm (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv R n g) := rfl
    rw [hrow]
    exact (e.apply_symm_apply _).trans hfree.symm
  apply Iso.ext
  exact congrArg (fun a : Aut (rowFree R n) => a.asIso.hom) he

/-- The actual finite row-matrix action in the existing small projective core. -/
public def finiteFreeRowCoreModelFunctor (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
      Core (FGProjectiveCat.IdempotentModel R) :=
  Core.functorToCore
    (SingleObj.functor (Aut.toEnd.comp (rowFreeAutMulEquiv R n).toMonoidHom))

/-- Its object is the literal rank-n free Karoubi object. -/
private theorem finiteFreeRowCoreModelFunctor_obj_computation07 (n : ℕ)
    (X : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    ((finiteFreeRowCoreModelFunctor R n).obj X).of =
      (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n := by
  unfold finiteFreeRowCoreModelFunctor
  rfl

public theorem finiteFreeRowCoreModelFunctor_obj (n : ℕ)
    (X : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    ((finiteFreeRowCoreModelFunctor R n).obj X).of =
      (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n :=
  finiteFreeRowCoreModelFunctor_obj_computation07 R n X

/-- Every functor map is the existing actual row-matrix model isomorphism. -/
public theorem finiteFreeRowCoreModelFunctor_map_iso (n : ℕ)
    {X Y : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ}
    (g : X ⟶ Y) :
    (eqToIso (finiteFreeRowCoreModelFunctor_obj R n X)).symm ≪≫
      ((finiteFreeRowCoreModelFunctor R n).map g).iso ≪≫
      eqToIso (finiteFreeRowCoreModelFunctor_obj R n Y) =
        FGProjectiveCat.IdempotentModel.freeAut R n g := by
  have hMap : ((finiteFreeRowCoreModelFunctor R n).map g).iso =
      (rowFreeAutMulEquiv R n g).asIso := by
    apply Iso.ext
    rfl
  have hHom :
      ((finiteFreeRowCoreModelFunctor R n).map g).iso.hom =
        (FGProjectiveCat.IdempotentModel.freeAut R n g).hom :=
    congrArg Iso.hom (hMap.trans (rowFreeAutMulEquiv_asIso R n g))
  have hTransport :
      HEq
        ((eqToIso (finiteFreeRowCoreModelFunctor_obj R n X)).symm.hom ≫
          ((finiteFreeRowCoreModelFunctor R n).map g).iso.hom ≫
          (eqToIso (finiteFreeRowCoreModelFunctor_obj R n Y)).hom)
        ((finiteFreeRowCoreModelFunctor R n).map g).iso.hom :=
    (eqToHom_comp_heq
      (((finiteFreeRowCoreModelFunctor R n).map g).iso.hom ≫
        eqToHom (finiteFreeRowCoreModelFunctor_obj R n Y))
      (finiteFreeRowCoreModelFunctor_obj R n X).symm).trans
      (comp_eqToHom_heq ((finiteFreeRowCoreModelFunctor R n).map g).iso.hom
        (finiteFreeRowCoreModelFunctor_obj R n Y))
  apply Iso.ext
  exact eq_of_heq (hTransport.trans (heq_of_eq hHom))

private abbrev rowCorePairFunctor (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
      Core (FGProjectiveCat.IdempotentModel R) ×
        Core (FGProjectiveCat.IdempotentModel R) :=
  (finiteFreeRowCoreModelFunctor R n).prod'
    ((Functor.const _).obj (⟨rowFree R n⟩ : Core (FGProjectiveCat.IdempotentModel R)))

private abbrev rowPairFunctor (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
      SInverseS.Pair (FGProjectiveCat.IdempotentModel R) :=
  rowCorePairFunctor R n ⋙ SInverseS.corePairInclusion

private theorem rowPairFunctor_zero (n : ℕ)
    (X : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    SInverseS.zeroComponentProperty ((rowPairFunctor R n).obj X) := by
  unfold SInverseS.zeroComponentProperty SInverseS.Pair.difference
  change Algebra.GrothendieckAddGroup.of (toSkeleton (rowFree R n)) -
      Algebra.GrothendieckAddGroup.of (toSkeleton (rowFree R n)) = 0
  exact sub_self _

/-- The original opposite finite GL row action at the literal diagonal pair
in the actual categorical zero component. -/
public def finiteFreeRowZeroComponentFunctor (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
      SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) :=
  (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).lift
    (rowPairFunctor R n) (rowPairFunctor_zero R n)

/-- Both coordinates remain the literal original rank-n object. -/
private theorem finiteFreeRowZeroComponentFunctor_obj_computation07 (n : ℕ)
    (X : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    ((finiteFreeRowZeroComponentFunctor R n).obj X).obj =
      (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n,
        (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
        SInverseS.Pair (FGProjectiveCat.IdempotentModel R)) := by
  unfold finiteFreeRowZeroComponentFunctor rowPairFunctor rowCorePairFunctor
    finiteFreeRowCoreModelFunctor
  rfl

public theorem finiteFreeRowZeroComponentFunctor_obj (n : ℕ)
    (X : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    ((finiteFreeRowZeroComponentFunctor R n).obj X).obj =
      (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n,
        (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
        SInverseS.Pair (FGProjectiveCat.IdempotentModel R)) :=
  finiteFreeRowZeroComponentFunctor_obj_computation07 R n X

/-- The actual finite matrix acts only in the first coordinate. -/
public theorem finiteFreeRowZeroComponentFunctor_map (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    eqToHom (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)).symm ≫
      ((finiteFreeRowZeroComponentFunctor R n).map
        (X := SingleObj.star _) (Y := SingleObj.star _) g).hom ≫
      eqToHom (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)) =
      (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).map
        (X :=
          ((⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
              Core (FGProjectiveCat.IdempotentModel R)),
            (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
              Core (FGProjectiveCat.IdempotentModel R))))
        (Y :=
          ((⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
              Core (FGProjectiveCat.IdempotentModel R)),
            (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
              Core (FGProjectiveCat.IdempotentModel R))))
        ((⟨FGProjectiveCat.IdempotentModel.freeAut R n g⟩ :
            (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
              Core (FGProjectiveCat.IdempotentModel R)) ⟶
                (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
                  Core (FGProjectiveCat.IdempotentModel R))),
          𝟙 (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
            Core (FGProjectiveCat.IdempotentModel R))) := by
  let P : Core (FGProjectiveCat.IdempotentModel R) := ⟨rowFree R n⟩
  let J : Core (FGProjectiveCat.IdempotentModel R) ×
      Core (FGProjectiveCat.IdempotentModel R) ⥤
        SInverseS.Pair (FGProjectiveCat.IdempotentModel R) :=
    SInverseS.corePairInclusion
  have hMap :
      ((finiteFreeRowZeroComponentFunctor R n).map
        (X := SingleObj.star _) (Y := SingleObj.star _) g).hom =
      J.map (X := (P, P)) (Y := (P, P))
        ((finiteFreeRowCoreModelFunctor R n).map
          (X := SingleObj.star _) (Y := SingleObj.star _) g, 𝟙 P) := by
    unfold finiteFreeRowZeroComponentFunctor rowPairFunctor rowCorePairFunctor
    rfl
  have hCoreRaw :
      ((finiteFreeRowCoreModelFunctor R n).map
        (X := SingleObj.star _) (Y := SingleObj.star _) g).iso =
      (rowFreeAutMulEquiv R n g).asIso := by
    apply Iso.ext
    rfl
  have hCoreIso :
      ((finiteFreeRowCoreModelFunctor R n).map
        (X := SingleObj.star _) (Y := SingleObj.star _) g).iso =
      FGProjectiveCat.IdempotentModel.freeAut R n g :=
    hCoreRaw.trans (rowFreeAutMulEquiv_asIso R n g)
  have hCore :
      (finiteFreeRowCoreModelFunctor R n).map
        (X := SingleObj.star _) (Y := SingleObj.star _) g =
      (⟨FGProjectiveCat.IdempotentModel.freeAut R n g⟩ : P ⟶ P) := by
    apply Core.hom_ext
    exact congrArg Iso.hom hCoreIso
  have hPair :
      J.map (X := (P, P)) (Y := (P, P))
          ((finiteFreeRowCoreModelFunctor R n).map
            (X := SingleObj.star _) (Y := SingleObj.star _) g, 𝟙 P) =
        J.map (X := (P, P)) (Y := (P, P))
          ((⟨FGProjectiveCat.IdempotentModel.freeAut R n g⟩ : P ⟶ P), 𝟙 P) :=
    congrArg (fun f : P ⟶ P => J.map (X := (P, P)) (Y := (P, P)) (f, 𝟙 P)) hCore
  have hTransport :
      HEq
        (eqToHom (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)).symm ≫
          ((finiteFreeRowZeroComponentFunctor R n).map
            (X := SingleObj.star _) (Y := SingleObj.star _) g).hom ≫
          eqToHom (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)))
        ((finiteFreeRowZeroComponentFunctor R n).map
          (X := SingleObj.star _) (Y := SingleObj.star _) g).hom :=
    (eqToHom_comp_heq
      (((finiteFreeRowZeroComponentFunctor R n).map
        (X := SingleObj.star _) (Y := SingleObj.star _) g).hom ≫
        eqToHom (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)))
      (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)).symm).trans
      (comp_eqToHom_heq
        ((finiteFreeRowZeroComponentFunctor R n).map
          (X := SingleObj.star _) (Y := SingleObj.star _) g).hom
        (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)))
  exact eq_of_heq (hTransport.trans (heq_of_eq (hMap.trans hPair)))

/-- Rank zero maps to the selected original zero pair via the established
free-zero comparison in both coordinates. -/
public def finiteFreeRowStageZeroToBase :
    (finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _) ⟶
      SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R) :=
  ObjectProperty.homMk
    ((SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).map
      (X := ((⟨rowFree R 0⟩ : Core (FGProjectiveCat.IdempotentModel R)),
        (⟨rowFree R 0⟩ : Core (FGProjectiveCat.IdempotentModel R))))
      (Y := ((⟨0⟩ : Core (FGProjectiveCat.IdempotentModel R)),
        (⟨0⟩ : Core (FGProjectiveCat.IdempotentModel R))))
      ((⟨FGProjectiveCat.IdempotentModel.freeZeroIso R⟩ :
        (⟨rowFree R 0⟩ : Core (FGProjectiveCat.IdempotentModel R)) ⟶
          (⟨0⟩ : Core (FGProjectiveCat.IdempotentModel R))),
        (⟨FGProjectiveCat.IdempotentModel.freeZeroIso R⟩ :
        (⟨rowFree R 0⟩ : Core (FGProjectiveCat.IdempotentModel R)) ⟶
          (⟨0⟩ : Core (FGProjectiveCat.IdempotentModel R)))))

private def rowSuccessorIso (n : ℕ) :
    rowFree R 1 ⊞ rowFree R n ≅ rowFree R (n + 1) :=
  biprod.braiding (rowFree R 1) (rowFree R n) ≪≫
    (FGProjectiveCat.IdempotentModel.freeBiprodIso R n 1).symm

private theorem rowSuccessorIso_naturality (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    biprod.mapIso (Iso.refl (rowFree R 1))
        (FGProjectiveCat.IdempotentModel.freeAut R n g) ≪≫ rowSuccessorIso R n =
      rowSuccessorIso R n ≪≫
        FGProjectiveCat.IdempotentModel.freeAut R (n + 1)
          (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop g))) := by
  let B := FGProjectiveCat.IdempotentModel.freeBiprodIso R n 1
  let a := FGProjectiveCat.IdempotentModel.freeAut R n g
  let b := FGProjectiveCat.IdempotentModel.freeAut R (n + 1)
    (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop g)))
  have hb : b =
      (B.symm.conjAut (Aut.of (biprod.mapIso a (Iso.refl (rowFree R 1))))).asIso := by
    simpa only [MulOpposite.op_unop] using
      (FGProjectiveCat.IdempotentModel.free_block_characteristic R).2.2.2.2.2.2.1
        n (MulOpposite.unop g)
  have hB : biprod.mapIso a (Iso.refl (rowFree R 1)) ≪≫ B.symm = B.symm ≪≫ b := by
    have h := congrArg (fun e => B.symm ≪≫ e) hb
    rw [Iso.conjAut_apply] at h
    simpa only [Iso.symm_symm_eq, Iso.symm_self_id_assoc] using h.symm
  have hbraid :
      biprod.mapIso (Iso.refl (rowFree R 1)) a ≪≫
          biprod.braiding (rowFree R 1) (rowFree R n) =
        biprod.braiding (rowFree R 1) (rowFree R n) ≪≫
          biprod.mapIso a (Iso.refl (rowFree R 1)) := by
    apply Iso.ext
    apply biprod.hom_ext <;> simp
  change biprod.mapIso (Iso.refl (rowFree R 1)) a ≪≫
      (biprod.braiding (rowFree R 1) (rowFree R n) ≪≫ B.symm) =
    (biprod.braiding (rowFree R 1) (rowFree R n) ≪≫ B.symm) ≪≫ b
  rw [← Iso.trans_assoc, hbraid, Iso.trans_assoc, hB, ← Iso.trans_assoc]

private theorem row_zeroStabilized_naturality_hom
    {s X Y : FGProjectiveCat.IdempotentModel R}
    (a : X ≅ X) (b : Y ≅ Y) (e : s ⊞ X ≅ Y)
    (h : biprod.mapIso (Iso.refl s) a ≪≫ e = e ≪≫ b) :
    biprod.map (biprod.braiding s (0 : FGProjectiveCat.IdempotentModel R)).hom (𝟙 X) ≫
          (biprod.associator (0 : FGProjectiveCat.IdempotentModel R) s X).hom ≫
          biprod.map (𝟙 (0 : FGProjectiveCat.IdempotentModel R)) e.hom ≫
          (isoZeroBiprod (isZero_zero _)).symm.hom ≫ b.hom =
      (biprod.associator s (0 : FGProjectiveCat.IdempotentModel R) X).hom ≫
        biprod.map (𝟙 s) ((isoZeroBiprod (isZero_zero _)).symm.hom ≫ a.hom) ≫ e.hom := by
  have hn : biprod.map (𝟙 s) a.hom ≫ e.hom = e.hom ≫ b.hom := congrArg Iso.hom h
  have hu := SInverseS.RawHom.zeroStabilized_comp_hom (r := s) (X := X) e.hom
  have hm : biprod.map (𝟙 s) ((isoZeroBiprod (isZero_zero _)).symm.hom ≫ a.hom) =
      biprod.map (𝟙 s) (isoZeroBiprod (isZero_zero _)).symm.hom ≫
        biprod.map (𝟙 s) a.hom := by
    apply biprod.hom_ext <;> simp [Category.assoc]
  calc
    _ = (biprod.associator s (0 : FGProjectiveCat.IdempotentModel R) X).hom ≫
          biprod.map (𝟙 s) (isoZeroBiprod (isZero_zero _)).symm.hom ≫
          e.hom ≫ b.hom := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ b.hom) hu
    _ = (biprod.associator s (0 : FGProjectiveCat.IdempotentModel R) X).hom ≫
          biprod.map (𝟙 s) (isoZeroBiprod (isZero_zero _)).symm.hom ≫
          biprod.map (𝟙 s) a.hom ≫ e.hom := by rw [← hn]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun k => (biprod.associator s (0 : FGProjectiveCat.IdempotentModel R) X).hom ≫
          k ≫ e.hom) hm.symm

private def rowSuccessorRawHom (n : ℕ) :
    SInverseS.RawHom
      (⟨rowFree R n, rowFree R n⟩ : SInverseS.Pair (FGProjectiveCat.IdempotentModel R))
      (⟨rowFree R (n + 1), rowFree R (n + 1)⟩ :
        SInverseS.Pair (FGProjectiveCat.IdempotentModel R)) where
  stabilizer := rowFree R 1
  hom₁ := rowSuccessorIso R n
  hom₂ := rowSuccessorIso R n

/-- The literal regular-stabilization arrow between the actual diagonal stages. -/
public def finiteFreeRowSuccessorArrow (n : ℕ) :
    (finiteFreeRowZeroComponentFunctor R n).obj (SingleObj.star _) ⟶
      (finiteFreeRowZeroComponentFunctor R (n + 1)).obj (SingleObj.star _) :=
  ObjectProperty.homMk
    (eqToHom (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)) ≫
      SInverseS.Hom.mk (rowSuccessorRawHom R n) ≫
      eqToHom (finiteFreeRowZeroComponentFunctor_obj R (n + 1) (SingleObj.star _)).symm)

/-- Its naturality retains the original row-matrix successor stabilization. -/
public theorem finiteFreeRowSuccessorArrow_naturality (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (finiteFreeRowZeroComponentFunctor R n).map g ≫ finiteFreeRowSuccessorArrow R n =
      finiteFreeRowSuccessorArrow R n ≫
        (finiteFreeRowZeroComponentFunctor R (n + 1)).map
          (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop g))) := by
  let c (k : ℕ) : SingleObj (Matrix.GeneralLinearGroup (Fin k) R)ᵐᵒᵖ :=
    SingleObj.star (Matrix.GeneralLinearGroup (Fin k) R)ᵐᵒᵖ
  let d (k : ℕ) : SInverseS.Pair (FGProjectiveCat.IdempotentModel R) :=
    ⟨rowFree R k, rowFree R k⟩
  let e (k : ℕ) : ((finiteFreeRowZeroComponentFunctor R k).obj (c k)).obj = d k :=
    finiteFreeRowZeroComponentFunctor_obj R k (c k)
  let M (k : ℕ) (a : (Matrix.GeneralLinearGroup (Fin k) R)ᵐᵒᵖ) : d k ⟶ d k :=
    SInverseS.Hom.mk (SInverseS.RawHom.ofCorePair
      (X := ((⟨rowFree R k⟩ : Core (FGProjectiveCat.IdempotentModel R)),
        (⟨rowFree R k⟩ : Core (FGProjectiveCat.IdempotentModel R))))
      (Y := ((⟨rowFree R k⟩ : Core (FGProjectiveCat.IdempotentModel R)),
        (⟨rowFree R k⟩ : Core (FGProjectiveCat.IdempotentModel R))))
      ((⟨FGProjectiveCat.IdempotentModel.freeAut R k a⟩ :
        (⟨rowFree R k⟩ : Core (FGProjectiveCat.IdempotentModel R)) ⟶ ⟨rowFree R k⟩),
        𝟙 (⟨rowFree R k⟩ : Core (FGProjectiveCat.IdempotentModel R))))
  have hm (k : ℕ) (a : (Matrix.GeneralLinearGroup (Fin k) R)ᵐᵒᵖ) :
      eqToHom (e k).symm ≫
          ((finiteFreeRowZeroComponentFunctor R k).map (X := c k) (Y := c k) a).hom ≫
        eqToHom (e k) = M k a := by
    exact finiteFreeRowZeroComponentFunctor_map R k a
  let g' : (Matrix.GeneralLinearGroup (Fin (n + 1)) R)ᵐᵒᵖ :=
    MulOpposite.op (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop g))
  have hraw : M n g ≫ SInverseS.Hom.mk (rowSuccessorRawHom R n) =
      SInverseS.Hom.mk (rowSuccessorRawHom R n) ≫ M (n + 1) g' := by
    change SInverseS.Hom.comp (M n g) (SInverseS.Hom.mk (rowSuccessorRawHom R n)) =
      SInverseS.Hom.comp (SInverseS.Hom.mk (rowSuccessorRawHom R n)) (M (n + 1) g')
    dsimp only [M]
    rw [SInverseS.Hom.comp_mk, SInverseS.Hom.comp_mk]
    apply Quotient.sound
    refine ⟨biprod.braiding (rowFree R 1) (0 : FGProjectiveCat.IdempotentModel R), ?_, ?_⟩
    · apply Iso.ext
      dsimp only [SInverseS.RawHom.comp, SInverseS.RawHom.ofCorePair,
        rowSuccessorRawHom, SInverseS.stabilizerIso, Iso.trans_hom]
      exact row_zeroStabilized_naturality_hom R
        (FGProjectiveCat.IdempotentModel.freeAut R n g)
        (FGProjectiveCat.IdempotentModel.freeAut R (n + 1)
          (MulOpposite.op (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop g))))
        (rowSuccessorIso R n) (rowSuccessorIso_naturality R n g)
    · apply Iso.ext
      dsimp only [SInverseS.RawHom.comp, SInverseS.RawHom.ofCorePair,
        rowSuccessorRawHom, SInverseS.stabilizerIso, Iso.trans_hom]
      apply row_zeroStabilized_naturality_hom R
        (Iso.refl (rowFree R n)) (Iso.refl (rowFree R (n + 1))) (rowSuccessorIso R n)
      apply Iso.ext
      have hid : biprod.map (𝟙 (rowFree R 1)) (𝟙 (rowFree R n)) = 𝟙 _ := by
        apply biprod.hom_ext <;> simp
      simp only [Iso.trans_hom, Iso.refl_hom, biprod.mapIso_hom, hid,
        Category.id_comp, Category.comp_id]
  have htransport
      {X Y DX DY : SInverseS.Pair (FGProjectiveCat.IdempotentModel R)}
      (hx : X = DX) (hy : Y = DY) (a : X ⟶ X) (a' : Y ⟶ Y) (f : DX ⟶ DY)
      (hn : (eqToHom hx.symm ≫ a ≫ eqToHom hx) ≫ f =
        f ≫ (eqToHom hy.symm ≫ a' ≫ eqToHom hy)) :
      a ≫ (eqToHom hx ≫ f ≫ eqToHom hy.symm) =
        (eqToHom hx ≫ f ≫ eqToHom hy.symm) ≫ a' := by
    cases hx
    cases hy
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hn
  have hn :
      (eqToHom (e n).symm ≫
        ((finiteFreeRowZeroComponentFunctor R n).map (X := c n) (Y := c n) g).hom ≫
          eqToHom (e n)) ≫ SInverseS.Hom.mk (rowSuccessorRawHom R n) =
      SInverseS.Hom.mk (rowSuccessorRawHom R n) ≫
        (eqToHom (e (n + 1)).symm ≫
          ((finiteFreeRowZeroComponentFunctor R (n + 1)).map
            (X := c (n + 1)) (Y := c (n + 1)) g').hom ≫ eqToHom (e (n + 1))) := by
    rw [hm, hm]
    exact hraw
  apply ObjectProperty.hom_ext
  change
    ((finiteFreeRowZeroComponentFunctor R n).map (X := c n) (Y := c n) g).hom ≫
        (eqToHom (e n) ≫ SInverseS.Hom.mk (rowSuccessorRawHom R n) ≫
          eqToHom (e (n + 1)).symm) =
      (eqToHom (e n) ≫ SInverseS.Hom.mk (rowSuccessorRawHom R n) ≫
        eqToHom (e (n + 1)).symm) ≫
          ((finiteFreeRowZeroComponentFunctor R (n + 1)).map
            (X := c (n + 1)) (Y := c (n + 1)) g').hom
  exact htransport (e n) (e (n + 1)) _ _ _ hn

/-- The existing opposite-row successor group map, viewed as a one-object functor. -/
public def finiteOppositeGLRowStabilizationFunctor (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
      SingleObj (Matrix.GeneralLinearGroup (Fin (n + 1)) R)ᵐᵒᵖ :=
  SingleObj.mapHom _ _ (MonoidHom.op (Matrix.GeneralLinearGroup.stabilization R))

/-- The original finite diagonal-stage maps form the actual successor triangle. -/
public def finiteFreeRowSuccessorNatTrans (n : ℕ) :
    finiteFreeRowZeroComponentFunctor R n ⟶
      finiteOppositeGLRowStabilizationFunctor R n ⋙
        finiteFreeRowZeroComponentFunctor R (n + 1) :=
  SingleObj.natTrans (finiteFreeRowSuccessorArrow R n)
    (fun g => finiteFreeRowSuccessorArrow_naturality R n g)

private def rowStageObjectDiagram : ℕ ⥤
    SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) :=
  Functor.ofSequence (fun n => finiteFreeRowSuccessorArrow R n)

/-- The original iterated diagonal-stage arrow for every indexing morphism. -/
public def finiteFreeRowTransitionArrow {n m : ℕ} (f : n ⟶ m) :
    (finiteFreeRowZeroComponentFunctor R n).obj (SingleObj.star _) ⟶
      (finiteFreeRowZeroComponentFunctor R m).obj (SingleObj.star _) :=
  (rowStageObjectDiagram R).map f

private theorem rowTransitionArrow_succ (n : ℕ) :
    finiteFreeRowTransitionArrow R (homOfLE (Nat.le_add_right n 1)) =
      finiteFreeRowSuccessorArrow R n :=
  Functor.ofSequence_map_homOfLE_succ _ n

private def rowShift (n : ℕ) : ℕ ⥤ ℕ where
  obj k := n + k
  map {i j} f := homOfLE (Nat.add_le_add_left (leOfHom f) n)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private def rowTailDiagram (n : ℕ) : ℕ ⥤
    SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) :=
  rowShift n ⋙ rowStageObjectDiagram R

private def rowTailEnd (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    rowTailDiagram R n ⟶ rowTailDiagram R n :=
  NatTrans.ofSequence
    (fun k => (finiteFreeRowZeroComponentFunctor R (n + k)).map
      (X := SingleObj.star _) (Y := SingleObj.star _)
      ((finiteOppositeMonoidDiagram R).map (homOfLE (Nat.le_add_right n k)) g))
    (by
      intro k
      let p : n ⟶ n + k := homOfLE (Nat.le_add_right n k)
      let q : n + k ⟶ n + k + 1 := homOfLE (Nat.le_add_right (n + k) 1)
      let a : (Matrix.GeneralLinearGroup (Fin (n + k)) R)ᵐᵒᵖ :=
        (finiteOppositeMonoidDiagram R).map p g
      have hq : (finiteOppositeMonoidDiagram R).map q a =
          MulOpposite.op (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop a)) := by
        have hv := finiteOppositeMonoidDiagram_map_apply R q a
        have hs := finiteGLDiagram_obj_map_succ (SemiRingCat.of R) (n + k)
        have hstep :
            (finiteGLDiagram.obj (SemiRingCat.of R)).map q (MulOpposite.unop a) =
              Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop a) := by
          calc
            _ = (GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization R))
                (MulOpposite.unop a) := by
              exact congrArg
                (fun f : GrpCat.of (Matrix.GeneralLinearGroup (Fin (n + k)) R) ⟶
                    GrpCat.of (Matrix.GeneralLinearGroup (Fin (n + k + 1)) R) =>
                  f (MulOpposite.unop a)) hs
            _ = _ := GrpCat.ofHom_apply _ _
        exact hv.trans (congrArg MulOpposite.op hstep)
      have hcomp :
          (finiteOppositeMonoidDiagram R).map
              (homOfLE (Nat.le_add_right n (k + 1))) g =
            MulOpposite.op (Matrix.GeneralLinearGroup.stabilization R (MulOpposite.unop a)) := by
        have hf : (homOfLE (Nat.le_add_right n (k + 1)) : n ⟶ n + (k + 1)) =
            p ≫ q := Subsingleton.elim _ _
        rw [hf, (finiteOppositeMonoidDiagram R).map_comp]
        exact hq
      change finiteFreeRowTransitionArrow R q ≫
          (finiteFreeRowZeroComponentFunctor R (n + k + 1)).map
            ((finiteOppositeMonoidDiagram R).map
              (homOfLE (Nat.le_add_right n (k + 1))) g) =
        (finiteFreeRowZeroComponentFunctor R (n + k)).map a ≫
          finiteFreeRowTransitionArrow R q
      rw [hcomp, rowTransitionArrow_succ]
      exact (finiteFreeRowSuccessorArrow_naturality R (n + k) a).symm)

private theorem rowTransitionArrow_naturality_add (n k : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (finiteFreeRowZeroComponentFunctor R n).map
        (X := SingleObj.star _) (Y := SingleObj.star _) g ≫
      finiteFreeRowTransitionArrow R (homOfLE (Nat.le_add_right n k)) =
    finiteFreeRowTransitionArrow R (homOfLE (Nat.le_add_right n k)) ≫
      (finiteFreeRowZeroComponentFunctor R (n + k)).map
        ((finiteOppositeMonoidDiagram R).map (homOfLE (Nat.le_add_right n k)) g) := by
  have h := (rowTailEnd R n g).naturality (homOfLE (Nat.zero_le k))
  have hg : (finiteOppositeMonoidDiagram R).map
      (homOfLE (Nat.le_add_right n 0)) g = g := by
    have hf : (homOfLE (Nat.le_add_right n 0) : n ⟶ n + 0) = 𝟙 n :=
      Subsingleton.elim _ _
    rw [hf, (finiteOppositeMonoidDiagram R).map_id]
    rfl
  change finiteFreeRowTransitionArrow R (homOfLE (Nat.le_add_right n k)) ≫
      (finiteFreeRowZeroComponentFunctor R (n + k)).map
        ((finiteOppositeMonoidDiagram R).map (homOfLE (Nat.le_add_right n k)) g) =
    (finiteFreeRowZeroComponentFunctor R n).map
      ((finiteOppositeMonoidDiagram R).map (homOfLE (Nat.le_add_right n 0)) g) ≫
      finiteFreeRowTransitionArrow R (homOfLE (Nat.le_add_right n k)) at h
  rw [hg] at h
  exact h.symm

/-- Every original finite-classifying-category transition intertwines the same row action. -/
public theorem finiteFreeRowTransitionArrow_naturality {n m : ℕ} (f : n ⟶ m)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (finiteFreeRowZeroComponentFunctor R n).map
        (X := SingleObj.star _) (Y := SingleObj.star _) g ≫
      finiteFreeRowTransitionArrow R f =
    finiteFreeRowTransitionArrow R f ≫
      (finiteFreeRowZeroComponentFunctor R m).map
        (((finiteClassifyingCategoryDiagram R).map f).toFunctor.map
          (X := SingleObj.star _) (Y := SingleObj.star _) g) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (leOfHom f)
  subst m
  have hf : f = homOfLE (Nat.le_add_right n k) := Subsingleton.elim _ _
  subst f
  let p : n ⟶ n + k := homOfLE (Nat.le_add_right n k)
  have ho := finiteOppositeMonoidDiagram_map_apply R p g
  have hc := finiteClassifyingCategoryDiagram_map_map R p
    (X := SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
    (Y := SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) g
  have hv := congrArg
    (fun a : (Matrix.GeneralLinearGroup (Fin (n + k)) R)ᵐᵒᵖ =>
      finiteFreeRowTransitionArrow R p ≫
        (finiteFreeRowZeroComponentFunctor R (n + k)).map
          (X := SingleObj.star (Matrix.GeneralLinearGroup (Fin (n + k)) R)ᵐᵒᵖ)
          (Y := SingleObj.star (Matrix.GeneralLinearGroup (Fin (n + k)) R)ᵐᵒᵖ) a)
    (ho.trans hc.symm)
  exact (rowTransitionArrow_naturality_add R n k g).trans hv

private def rowDiagramFiber (n : ℕ) :
    (finiteClassifyingCategoryDiagram R).obj n ⥤
      SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) :=
  finiteFreeRowZeroComponentFunctor R n

/-- The actual row-stage transformations for every original telescope indexing arrow. -/
public def finiteFreeRowTransitionNatTrans {n m : ℕ} (f : n ⟶ m) :
    finiteFreeRowZeroComponentFunctor R n ⟶
      ((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
        finiteFreeRowZeroComponentFunctor R m :=
  SingleObj.natTrans (finiteFreeRowTransitionArrow R f)
    (fun g => finiteFreeRowTransitionArrow_naturality R f g)

private theorem rowTransitionNatTrans_id (n : ℕ) :
    finiteFreeRowTransitionNatTrans R (𝟙 n) =
      eqToHom (Grothendieck.fiberFunctor_id_eq
        (finiteClassifyingCategoryDiagram R) (rowDiagramFiber R) n) := by
  let F : (finiteClassifyingCategoryDiagram R).obj n ⥤
      SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) :=
    rowDiagramFiber R n
  let T : (finiteClassifyingCategoryDiagram R).obj n ⥤
      (finiteClassifyingCategoryDiagram R).obj n :=
    ((finiteClassifyingCategoryDiagram R).map (𝟙 n)).toFunctor
  let τ : F ⟶ T ⋙ F := finiteFreeRowTransitionNatTrans R (𝟙 n)
  let hF : F = T ⋙ F :=
    Grothendieck.fiberFunctor_id_eq (finiteClassifyingCategoryDiagram R)
      (rowDiagramFiber R) n
  change τ = (eqToHom hF : F ⟶ T ⋙ F)
  apply NatTrans.ext
  funext X
  let c : (finiteClassifyingCategoryDiagram R).obj n :=
    SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ
  have hsub : Subsingleton ((finiteClassifyingCategoryDiagram R).obj n) := by
    rw [finiteClassifyingCategoryDiagram_obj R n]
    simpa only [Cat.of_α] using
      (show Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) from
        ⟨fun _ _ => Quiver.SingleObj.ext⟩)
  have hX : X = c := @Subsingleton.elim _ hsub X c
  subst X
  have hτ : τ.app c = finiteFreeRowTransitionArrow R (𝟙 n) := by
    simpa only [τ, F, T, c, rowDiagramFiber, finiteFreeRowTransitionNatTrans] using
      (SingleObj.natTrans_app
        (F := finiteFreeRowZeroComponentFunctor R n)
        (G := ((finiteClassifyingCategoryDiagram R).map (𝟙 n)).toFunctor ⋙
          finiteFreeRowZeroComponentFunctor R n)
        (finiteFreeRowTransitionArrow R (𝟙 n))
        (fun a => finiteFreeRowTransitionArrow_naturality R (𝟙 n) a)
        (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))
  have hId : finiteFreeRowTransitionArrow R (𝟙 n) =
      𝟙 ((rowStageObjectDiagram R).obj n) := (rowStageObjectDiagram R).map_id n
  have hObj : (rowStageObjectDiagram R).obj n = F.obj c := by
    change F.obj c = F.obj c
    rfl
  have hIds : (𝟙 ((rowStageObjectDiagram R).obj n)) ≍ (𝟙 (F.obj c)) :=
    (eqToHom_heq_id_dom _ _ hObj).symm.trans (eqToHom_heq_id_cod _ _ hObj)
  have hEq := eqToHom_app hF c
  have hEqId : (eqToHom hF : F ⟶ T ⋙ F).app c ≍ (𝟙 (F.obj c)) :=
    (heq_of_eq hEq).trans
      (eqToHom_heq_id_dom _ _ (Functor.congr_obj hF c))
  apply eq_of_heq
  exact (heq_of_eq (hτ.trans hId)).trans (hIds.trans hEqId.symm)

section RowPointProofs

universe uPoint vPoint uValue vValue

private theorem rowNatTransAppPointHEq
    {C : Type uPoint} [Category.{vPoint} C]
    {D : Type uValue} [Category.{vValue} D] {F G : C ⥤ D}
    (a : F ⟶ G) {X Y : C} (h : X = Y) : a.app X ≍ a.app Y := by
  cases h
  rfl

private theorem rowNatTransCompositePointHEq
    {C : Type uPoint} [Category.{vPoint} C]
    {D : Type uValue} [Category.{vValue} D] {F G H I : C ⥤ D}
    (a : F ⟶ G) (b : G ⟶ H) (e : H = I) (X : C)
    {P Q S : D} (f : P ⟶ Q) (g : Q ⟶ S)
    (hP : F.obj X = P) (hQ : G.obj X = Q) (hS : H.obj X = S)
    (ha : a.app X ≍ f) (hb : b.app X ≍ g) :
    (a ≫ b ≫ eqToHom e).app X ≍ f ≫ g := by
  have hpre : a.app X ≫ b.app X ≍ f ≫ g := heq_comp hP hQ hS ha hb
  have hbe := NatTrans.comp_app b (eqToHom e) X
  have habe := NatTrans.comp_app a (b ≫ eqToHom e) X
  have hv := congrArg
    (fun k : G.obj X ⟶ I.obj X => a.app X ≫ k) hbe
  have hassoc : (a ≫ b ≫ eqToHom e).app X =
      (a.app X ≫ b.app X) ≫ (eqToHom e : H ⟶ I).app X :=
    (habe.trans hv).trans
      (Category.assoc (a.app X) (b.app X) ((eqToHom e : H ⟶ I).app X)).symm
  have he := congrArg
    (fun k : H.obj X ⟶ I.obj X => (a.app X ≫ b.app X) ≫ k) (eqToHom_app e X)
  exact (heq_of_eq (hassoc.trans he)).trans
    ((comp_eqToHom_heq (a.app X ≫ b.app X) (Functor.congr_obj e X)).trans hpre)

end RowPointProofs

section RowNatTransPointHelper

universe uC vC uD vD

/-- On an actual subsingleton source carrier, natural transformations are
 determined by their component at the specified actual source point. -/
private theorem rowNatTransEqAtPoint
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {F G : C ⥤ D} (c0 : C) (hc : Subsingleton C) {a b : F ⟶ G}
    (h : a.app c0 = b.app c0) : a = b := by
  apply NatTrans.ext
  funext X
  have hX : X = c0 := @Subsingleton.elim C hc X c0
  subst X
  exact h

end RowNatTransPointHelper

private theorem rowTransitionNatTransAppPoint {n m : ℕ} (f : n ⟶ m) :
    (finiteFreeRowTransitionNatTrans R f :
      rowDiagramFiber R n ⟶ ((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
        rowDiagramFiber R m).app
      (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) =
        finiteFreeRowTransitionArrow R f := by
  simpa only [rowDiagramFiber, finiteFreeRowTransitionNatTrans] using
    (SingleObj.natTrans_app
      (F := finiteFreeRowZeroComponentFunctor R n)
      (G := ((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
        finiteFreeRowZeroComponentFunctor R m)
      (finiteFreeRowTransitionArrow R f)
      (fun a => finiteFreeRowTransitionArrow_naturality R f a)
      (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))

section RowDiagramPointProof

universe uBase vBase uFiber vFiber uTarget vTarget

private theorem rowDiagramCompositionFromPoints
    {J : Type uBase} [Category.{vBase} J] (B : J ⥤ Cat.{vFiber, uFiber})
    {D : Type uTarget} [Category.{vTarget} D]
    (fib : ∀ j, B.obj j ⥤ D) (point : ∀ j, B.obj j)
    (uniquePoint : ∀ j, Subsingleton (B.obj j)) (V : J ⥤ D)
    (t : ∀ {i j : J} (f : i ⟶ j), fib i ⟶ (B.map f).toFunctor ⋙ fib j)
    (objectValue : ∀ j, (fib j).obj (point j) = V.obj j)
    (arrowValue : ∀ {i j : J} (f : i ⟶ j), (t f).app (point i) ≍ V.map f)
    {i j k : J} (f : i ⟶ j) (g : j ⟶ k) :
    t (f ≫ g) = t f ≫ Functor.whiskerLeft (B.map f).toFunctor (t g) ≫
      eqToHom (Grothendieck.fiberFunctor_comp_eq B fib f g) := by
  let T := (B.map f).toFunctor
  let S := (B.map g).toFunctor
  have hp : T.obj (point i) = point j :=
    @Subsingleton.elim _ (uniquePoint j) _ _
  have hq : S.obj (point j) = point k :=
    @Subsingleton.elim _ (uniquePoint k) _ _
  have hMid : (T ⋙ fib j).obj (point i) = V.obj j :=
    (congrArg (fib j).obj hp).trans (objectValue j)
  have hEnd : (T ⋙ (S ⋙ fib k)).obj (point i) = V.obj k :=
    (congrArg (fun X : B.obj j => (fib k).obj (S.obj X)) hp).trans
      ((congrArg (fib k).obj hq).trans (objectValue k))
  have hSecond : (Functor.whiskerLeft T (t g)).app (point i) ≍ V.map g :=
    (heq_of_eq (Functor.whiskerLeft_app T (t g) (point i))).trans
      ((rowNatTransAppPointHEq (t g) hp).trans (arrowValue g))
  have hComposite :
      (t f ≫ Functor.whiskerLeft T (t g) ≫
        eqToHom (Grothendieck.fiberFunctor_comp_eq B fib f g)).app (point i) ≍
          V.map f ≫ V.map g :=
    rowNatTransCompositePointHEq (t f) (Functor.whiskerLeft T (t g))
      (Grothendieck.fiberFunctor_comp_eq B fib f g) (point i)
      (V.map f) (V.map g) (objectValue i) hMid hEnd (arrowValue f) hSecond
  exact rowNatTransEqAtPoint (point i) (uniquePoint i)
    (eq_of_heq ((arrowValue (f ≫ g)).trans
      ((heq_of_eq (V.map_comp f g)).trans hComposite.symm)))

end RowDiagramPointProof

private theorem rowDiagramFiberPointObject (n : ℕ) :
    (rowDiagramFiber R n).obj
      (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) =
        (rowStageObjectDiagram R).obj n := by
  change (finiteFreeRowZeroComponentFunctor R n).obj
      (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) =
    (finiteFreeRowZeroComponentFunctor R n).obj
      (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
  rfl

private theorem rowTransitionNatTransStagePointHEq {n m : ℕ} (f : n ⟶ m) :
    (finiteFreeRowTransitionNatTrans R f :
      rowDiagramFiber R n ⟶ ((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
        rowDiagramFiber R m).app
      (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ≍
        (rowStageObjectDiagram R).map f := by
  let cn : (finiteClassifyingCategoryDiagram R).obj n :=
    SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ
  let cm : (finiteClassifyingCategoryDiagram R).obj m :=
    SingleObj.star (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ
  have hsub : Subsingleton ((finiteClassifyingCategoryDiagram R).obj m) := by
    rw [finiteClassifyingCategoryDiagram_obj R m]
    simpa only [Cat.of_α] using
      (show Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ) from
        ⟨fun _ _ => Quiver.SingleObj.ext⟩)
  have hPoint : ((finiteClassifyingCategoryDiagram R).map f).toFunctor.obj cn = cm :=
    @Subsingleton.elim _ hsub _ _
  have hSource : (rowDiagramFiber R n).obj cn = (rowStageObjectDiagram R).obj n :=
    rowDiagramFiberPointObject R n
  have hTarget :
      (((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
        rowDiagramFiber R m).obj cn = (rowStageObjectDiagram R).obj m :=
    (congrArg (rowDiagramFiber R m).obj hPoint).trans (rowDiagramFiberPointObject R m)
  have hArrowHEq :
      @HEq
        ((finiteFreeRowZeroComponentFunctor R n).obj
            (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ⟶
          (finiteFreeRowZeroComponentFunctor R m).obj
            (SingleObj.star (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ))
        (finiteFreeRowTransitionArrow R f)
        ((rowStageObjectDiagram R).obj n ⟶ (rowStageObjectDiagram R).obj m)
        ((rowStageObjectDiagram R).map f) := by
    change @HEq
      ((finiteFreeRowZeroComponentFunctor R n).obj
          (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ⟶
        (finiteFreeRowZeroComponentFunctor R m).obj
          (SingleObj.star (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ))
      ((rowStageObjectDiagram R).map f)
      ((finiteFreeRowZeroComponentFunctor R n).obj
          (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ⟶
        (finiteFreeRowZeroComponentFunctor R m).obj
          (SingleObj.star (Matrix.GeneralLinearGroup (Fin m) R)ᵐᵒᵖ))
      ((rowStageObjectDiagram R).map f)
    rfl
  have hArrowTransport :
      (finiteFreeRowTransitionArrow R f :
        (rowDiagramFiber R n).obj cn ⟶
          (((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
            rowDiagramFiber R m).obj cn) =
        eqToHom hSource ≫ (rowStageObjectDiagram R).map f ≫ eqToHom hTarget.symm :=
    (conj_eqToHom_iff_heq
      (finiteFreeRowTransitionArrow R f :
        (rowDiagramFiber R n).obj cn ⟶
          (((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
            rowDiagramFiber R m).obj cn)
      ((rowStageObjectDiagram R).map f) hSource hTarget).mpr hArrowHEq
  apply (conj_eqToHom_iff_heq
    ((finiteFreeRowTransitionNatTrans R f :
      rowDiagramFiber R n ⟶ ((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙
        rowDiagramFiber R m).app cn)
    ((rowStageObjectDiagram R).map f) hSource hTarget).mp
  exact (rowTransitionNatTransAppPoint R f).trans hArrowTransport

private theorem rowTransitionNatTrans_comp (n m k : ℕ) (f : n ⟶ m) (g : m ⟶ k) :
    finiteFreeRowTransitionNatTrans R (f ≫ g) =
      finiteFreeRowTransitionNatTrans R f ≫
        Functor.whiskerLeft ((finiteClassifyingCategoryDiagram R).map f).toFunctor
          (finiteFreeRowTransitionNatTrans R g) ≫
        eqToHom (Grothendieck.fiberFunctor_comp_eq
          (finiteClassifyingCategoryDiagram R) (rowDiagramFiber R) f g) := by
  let point (n : ℕ) : (finiteClassifyingCategoryDiagram R).obj n :=
    SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ
  have uniquePoint (n : ℕ) : Subsingleton ((finiteClassifyingCategoryDiagram R).obj n) := by
    rw [finiteClassifyingCategoryDiagram_obj R n]
    simpa only [Cat.of_α] using
      (show Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) from
        ⟨fun _ _ => Quiver.SingleObj.ext⟩)
  exact rowDiagramCompositionFromPoints (finiteClassifyingCategoryDiagram R)
    (rowDiagramFiber R) point uniquePoint (rowStageObjectDiagram R)
    (fun {a b} p => (finiteFreeRowTransitionNatTrans R p :
      rowDiagramFiber R a ⟶ ((finiteClassifyingCategoryDiagram R).map p).toFunctor ⋙
        rowDiagramFiber R b))
    (rowDiagramFiberPointObject R) (fun p => rowTransitionNatTransStagePointHEq R p) f g

/-- The original finite BGL Grothendieck telescope maps to the actual small-projective
zero component, using the original row loops and genuine regular-stabilization paths. -/
public def finiteBGLTelescopeToRowZeroComponent :
    FiniteBGLTelescopeCategory R ⥤
      SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) :=
  Grothendieck.functorFromWithCoherence (finiteClassifyingCategoryDiagram R)
    (rowDiagramFiber R) (finiteFreeRowTransitionNatTrans R)
    (rowTransitionNatTrans_id R) (rowTransitionNatTrans_comp R)

/-- The image of every original telescope object is its actual finite diagonal stage. -/
private theorem finiteBGLTelescopeToRowZeroComponent_obj_computation07
    (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeToRowZeroComponent R).obj X =
      (finiteFreeRowZeroComponentFunctor R X.base).obj X.fiber := by
  simpa only [finiteBGLTelescopeToRowZeroComponent, rowDiagramFiber] using
    (Grothendieck.functorFromWithCoherence_obj
      (finiteClassifyingCategoryDiagram R) (rowDiagramFiber R)
      (finiteFreeRowTransitionNatTrans R) (rowTransitionNatTrans_id R)
      (rowTransitionNatTrans_comp R) X)

public theorem finiteBGLTelescopeToRowZeroComponent_obj
    (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeToRowZeroComponent R).obj X =
      (finiteFreeRowZeroComponentFunctor R X.base).obj X.fiber :=
  finiteBGLTelescopeToRowZeroComponent_obj_computation07 R X

/-- The selected original stage-zero vertex keeps its actual image under the comparison. -/
private theorem finiteBGLTelescopeToRowZeroComponent_base_computation07 :
    (finiteBGLTelescopeToRowZeroComponent R).obj (finiteBGLTelescopeBaseObject R) =
      (finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _) := by
  exact finiteBGLTelescopeToRowZeroComponent_obj R (finiteBGLTelescopeBaseObject R)

public theorem finiteBGLTelescopeToRowZeroComponent_base :
    (finiteBGLTelescopeToRowZeroComponent R).obj (finiteBGLTelescopeBaseObject R) =
      (finiteFreeRowZeroComponentFunctor R 0).obj (SingleObj.star _) :=
  finiteBGLTelescopeToRowZeroComponent_base_computation07 R

/-- The actual nerve map of the original row telescope comparison uses the
existing common-Hom reader; the Ring and every simplex value are unchanged. -/
public def finiteBGLTelescopeToRowZeroComponentNerve :
    nerve (FiniteBGLTelescopeCategory R) ⟶
      nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)) :=
  nerveMapCommonHomUp.{0, u, 0} (finiteBGLTelescopeToRowZeroComponent R)

/-- The original actual functor is applied to every composable chain. -/
private theorem finiteBGLTelescopeToRowZeroComponentNerve_app_computation07
    (D : SimplexCategoryᵒᵖ) (X : (nerve (FiniteBGLTelescopeCategory R)).obj D) :
    (finiteBGLTelescopeToRowZeroComponentNerve R).app D X =
      ((finiteBGLTelescopeToRowZeroComponent R).mapComposableArrows D.unop.len).obj X := by
  unfold finiteBGLTelescopeToRowZeroComponentNerve
  exact nerveMapCommonHomUp_app.{0, u, 0}
    (finiteBGLTelescopeToRowZeroComponent R) D X

public theorem finiteBGLTelescopeToRowZeroComponentNerve_app
    (D : SimplexCategoryᵒᵖ) (X : (nerve (FiniteBGLTelescopeCategory R)).obj D) :
    (finiteBGLTelescopeToRowZeroComponentNerve R).app D X =
      ((finiteBGLTelescopeToRowZeroComponent R).mapComposableArrows D.unop.len).obj X :=
  finiteBGLTelescopeToRowZeroComponentNerve_app_computation07 R D X

/-- Ordinary realization of the same original row telescope map. -/
public def finiteBGLTelescopeToRowZeroComponentTop :
    SSet.toTop.obj (nerve (FiniteBGLTelescopeCategory R)) ⟶
      SSet.toTop.obj
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) :=
  SSet.toTop.map (finiteBGLTelescopeToRowZeroComponentNerve R)

/-- The exact ordinary integral homology map of the actual Ring-only
comparison, in each degree. Its invertibility is the separate remaining
localized-core and zero-K0-graded stabilization theorem. -/
public def finiteBGLTelescopeToRowZeroComponentIntegralHomologyMap (q : ℕ) :
    AlgebraicTopology.singularIntegralHomology q
        (SSet.toTop.obj (nerve (FiniteBGLTelescopeCategory R))) ⟶
      AlgebraicTopology.singularIntegralHomology q
        (SSet.toTop.obj
          (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))) :=
  (AlgebraicTopology.singularIntegralHomologyFunctor q).map
    (finiteBGLTelescopeToRowZeroComponentTop R)

/-- At the original finite row stage, adding the rank-n object to the second
coordinate of the positive core map gives the SAME diagonal-pair map, up to
the computed right-zero unitor. This retains the actual point transport. -/
public def finiteFreeRowTranslatedCoreIso (n : ℕ) :
    finiteFreeRowCoreModelFunctor R n ⋙
        (SInverseS.coreInclusion (C := FGProjectiveCat.IdempotentModel R)) ⋙
          SInverseS.translateSecondFunctor
            ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ≅
      finiteFreeRowZeroComponentFunctor R n ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι := by
  let C := FGProjectiveCat.IdempotentModel R
  let F := finiteFreeRowCoreModelFunctor R n
  let J : Core C × Core C ⥤ SInverseS.Pair C := SInverseS.corePairInclusion
  let z : Core C := ⟨0⟩
  let p : Core C := ⟨rowFree R n⟩
  let b : Core C := ⟨rowFree R n ⊞ (0 : C)⟩
  let e : b ≅ p := Core.isoMk (x := b) (y := p)
    ((isoBiprodZero (X := rowFree R n) (isZero_zero C)).symm)
  refine NatIso.ofComponents (fun X =>
    J.mapIso (X := (F.obj X, b)) (Y := (F.obj X, p))
      (Iso.prod (Iso.refl (F.obj X)) e)) ?_
  intro X Y g
  let f : F.obj X ⟶ F.obj Y := F.map g
  let f0 : ((F.obj X, z) : Core C × Core C) ⟶ (F.obj Y, z) := (f, 𝟙 z)
  let f2 : ((F.obj X, b) : Core C × Core C) ⟶ (F.obj Y, b) := (f, 𝟙 b)
  let f1 : ((F.obj X, p) : Core C × Core C) ⟶ (F.obj Y, p) := (f, 𝟙 p)
  let eX : ((F.obj X, b) : Core C × Core C) ⟶ (F.obj X, p) := (𝟙 (F.obj X), e.hom)
  let eY : ((F.obj Y, b) : Core C × Core C) ⟶ (F.obj Y, p) := (𝟙 (F.obj Y), e.hom)
  have hTranslate :
      (SInverseS.translateSecondFunctor (rowFree R n)).map (J.map f0) = J.map f2 := by
    rw [SInverseS.translateSecondFunctor_map_ofCorePair]
    apply congrArg J.map
    apply Prod.ext
    · rfl
    · apply Core.hom_ext
      change (biprod.mapIso (Iso.refl (rowFree R n)) (Iso.refl (0 : C))).hom =
        (𝟙 (rowFree R n ⊞ (0 : C)))
      apply biprod.hom_ext
      · rw [biprod.mapIso_hom, biprod.map_fst, Iso.refl_hom,
          Category.comp_id, Category.id_comp]
      · rw [biprod.mapIso_hom, biprod.map_snd, Iso.refl_hom,
          Category.comp_id, Category.id_comp]
  have hSquare : f2 ≫ eY = eX ≫ f1 := by
    apply Prod.ext
    · change f ≫ 𝟙 (F.obj Y) = 𝟙 (F.obj X) ≫ f
      simp only [Category.comp_id, Category.id_comp]
    · change (𝟙 b) ≫ e.hom = e.hom ≫ (𝟙 p)
      simp only [Category.id_comp, Category.comp_id]
  change
    (SInverseS.translateSecondFunctor (rowFree R n)).map (J.map f0) ≫ J.map eY =
      J.map eX ≫ J.map f1
  have hJ : J.map f2 ≫ J.map eY = J.map eX ≫ J.map f1 := by
    calc
      J.map f2 ≫ J.map eY = J.map (f2 ≫ eY) := (J.map_comp f2 eY).symm
      _ = J.map (eX ≫ f1) := congrArg J.map hSquare
      _ = J.map eX ≫ J.map f1 := J.map_comp eX f1
  exact (congrArg
    (fun k : J.obj (F.obj X, b) ⟶ J.obj (F.obj Y, b) => k ≫ J.map eY)
      hTranslate).trans hJ

/-- The stage comparison has the original core-pair arrow with identity first
coordinate and the actual right-zero unitor in the second coordinate. -/
private theorem finiteFreeRowTranslatedCoreIso_hom_app_computation07 (n : ℕ)
    (X : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (finiteFreeRowTranslatedCoreIso R n).hom.app X =
      (by
        let C := FGProjectiveCat.IdempotentModel R
        let F := finiteFreeRowCoreModelFunctor R n
        let J : Core C × Core C ⥤ SInverseS.Pair C := SInverseS.corePairInclusion
        let W : C := (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n
        let b : Core C := ⟨W ⊞ (0 : C)⟩
        let p : Core C := ⟨W⟩
        let L := F ⋙ (SInverseS.coreInclusion (C := C)) ⋙ SInverseS.translateSecondFunctor W
        let K := finiteFreeRowZeroComponentFunctor R n ⋙ (SInverseS.zeroComponentProperty (C := C)).ι
        have hL : L.obj X = J.obj (F.obj X, b) := rfl
        have hK : K.obj X = J.obj (F.obj X, p) := by
          change ((finiteFreeRowZeroComponentFunctor R n).obj X).obj = J.obj (F.obj X, p)
          rw [finiteFreeRowZeroComponentFunctor_obj]
          change (⟨W, W⟩ : SInverseS.Pair C) =
            (⟨((finiteFreeRowCoreModelFunctor R n).obj X).of, W⟩ : SInverseS.Pair C)
          rw [finiteFreeRowCoreModelFunctor_obj]
        let a : J.obj (F.obj X, b) ⟶ J.obj (F.obj X, p) :=
          (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).map
            (X := ((finiteFreeRowCoreModelFunctor R n).obj X,
              (⟨((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ⊞
                (0 : FGProjectiveCat.IdempotentModel R)⟩ : Core (FGProjectiveCat.IdempotentModel R))))
            (Y := ((finiteFreeRowCoreModelFunctor R n).obj X,
              (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
                Core (FGProjectiveCat.IdempotentModel R))))
            ((𝟙 ((finiteFreeRowCoreModelFunctor R n).obj X),
              (⟨(isoBiprodZero (X := ((Idempotents.toKaroubi
                (FGProjectiveCat.FiniteRowRanks R)).obj n))
                (isZero_zero (FGProjectiveCat.IdempotentModel R))).symm⟩ :
                (⟨((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ⊞
                  (0 : FGProjectiveCat.IdempotentModel R)⟩ :
                    Core (FGProjectiveCat.IdempotentModel R)) ⟶
                      (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
                        Core (FGProjectiveCat.IdempotentModel R)))))
        exact eqToHom hL ≫ a ≫ eqToHom hK.symm) := by
  let C := FGProjectiveCat.IdempotentModel R
  let F := finiteFreeRowCoreModelFunctor R n
  let J : Core C × Core C ⥤ SInverseS.Pair C := SInverseS.corePairInclusion
  let W : C := (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n
  let b : Core C := ⟨W ⊞ (0 : C)⟩
  let p : Core C := ⟨W⟩
  let L := F ⋙ (SInverseS.coreInclusion (C := C)) ⋙ SInverseS.translateSecondFunctor W
  let K := finiteFreeRowZeroComponentFunctor R n ⋙
    (SInverseS.zeroComponentProperty (C := C)).ι
  have hL : L.obj X = J.obj (F.obj X, b) := rfl
  have hK : K.obj X = J.obj (F.obj X, p) := by
    change ((finiteFreeRowZeroComponentFunctor R n).obj X).obj = J.obj (F.obj X, p)
    rw [finiteFreeRowZeroComponentFunctor_obj]
    change (⟨W, W⟩ : SInverseS.Pair C) =
      (⟨((finiteFreeRowCoreModelFunctor R n).obj X).of, W⟩ : SInverseS.Pair C)
    rw [finiteFreeRowCoreModelFunctor_obj]
  let e0 : W ⊞ (0 : C) ≅ W :=
    (isoBiprodZero (X := W) (isZero_zero C)).symm
  let a : J.obj (F.obj X, b) ⟶ J.obj (F.obj X, p) :=
    J.map (X := (F.obj X, b)) (Y := (F.obj X, p))
      (𝟙 (F.obj X), (⟨e0⟩ : b ⟶ p))
  have hCoreHom : (Core.isoMk (x := b) (y := p) e0).hom = (⟨e0⟩ : b ⟶ p) := by
    apply Core.hom_ext
    exact congrArg Iso.hom (Core.isoMk_hom_iso (x := b) (y := p) e0)
  have hApp : (finiteFreeRowTranslatedCoreIso R n).hom.app X = a := by
    let ePair : ((F.obj X, b) : Core C × Core C) ≅ (F.obj X, p) :=
      Iso.prod (Iso.refl (F.obj X)) (Core.isoMk (x := b) (y := p) e0)
    let iX : J.obj (F.obj X, b) ≅ J.obj (F.obj X, p) := J.mapIso ePair
    have hIsoApp : (finiteFreeRowTranslatedCoreIso R n).app X = iX := by
      dsimp only [finiteFreeRowTranslatedCoreIso]
      exact NatIso.ofComponents.app (F := L) (G := K) _ _ X
    have hPairHom : ePair.hom =
        ((𝟙 (F.obj X), (⟨e0⟩ : b ⟶ p)) :
          ((F.obj X, b) : Core C × Core C) ⟶ (F.obj X, p)) := by
      exact (Iso.prod_hom (Iso.refl (F.obj X))
        (Core.isoMk (x := b) (y := p) e0)).trans
          (congrArg₂ (fun (l : F.obj X ⟶ F.obj X) (r : b ⟶ p) => (l, r))
            (Iso.refl_hom (F.obj X)) hCoreHom)
    have hiXHom : iX.hom = a :=
      (Functor.mapIso_hom J ePair).trans (congrArg J.map hPairHom)
    have hHom : (finiteFreeRowTranslatedCoreIso R n).hom.app X = iX.hom :=
      (Iso.app_hom (finiteFreeRowTranslatedCoreIso R n) X).symm.trans
        (congrArg Iso.hom hIsoApp)
    exact hHom.trans hiXHom
  have hLid : (eqToHom hL : J.obj (F.obj X, b) ⟶ J.obj (F.obj X, b)) =
      𝟙 (J.obj (F.obj X, b)) := by
    rfl
  have hKid : (eqToHom hK.symm : J.obj (F.obj X, p) ⟶ J.obj (F.obj X, p)) =
      𝟙 (J.obj (F.obj X, p)) := by
    rfl
  have hTransport :
      (eqToHom hL : J.obj (F.obj X, b) ⟶ J.obj (F.obj X, b)) ≫ a ≫
        (eqToHom hK.symm : J.obj (F.obj X, p) ⟶ J.obj (F.obj X, p)) = a := by
    calc
      _ = 𝟙 (J.obj (F.obj X, b)) ≫ a ≫ 𝟙 (J.obj (F.obj X, p)) :=
        congrArg₂ (fun (l : J.obj (F.obj X, b) ⟶ J.obj (F.obj X, b))
          (r : J.obj (F.obj X, p) ⟶ J.obj (F.obj X, p)) => l ≫ a ≫ r) hLid hKid
      _ = a := by simp only [Category.id_comp, Category.comp_id]
  change (finiteFreeRowTranslatedCoreIso R n).hom.app X =
    eqToHom hL ≫ a ≫ eqToHom hK.symm
  exact hApp.trans hTransport.symm

public theorem finiteFreeRowTranslatedCoreIso_hom_app (n : ℕ)
    (X : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (finiteFreeRowTranslatedCoreIso R n).hom.app X =
      (by
        let C := FGProjectiveCat.IdempotentModel R
        let F := finiteFreeRowCoreModelFunctor R n
        let J : Core C × Core C ⥤ SInverseS.Pair C := SInverseS.corePairInclusion
        let W : C := (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n
        let b : Core C := ⟨W ⊞ (0 : C)⟩
        let p : Core C := ⟨W⟩
        let L := F ⋙ (SInverseS.coreInclusion (C := C)) ⋙ SInverseS.translateSecondFunctor W
        let K := finiteFreeRowZeroComponentFunctor R n ⋙ (SInverseS.zeroComponentProperty (C := C)).ι
        have hL : L.obj X = J.obj (F.obj X, b) := rfl
        have hK : K.obj X = J.obj (F.obj X, p) := by
          change ((finiteFreeRowZeroComponentFunctor R n).obj X).obj = J.obj (F.obj X, p)
          rw [finiteFreeRowZeroComponentFunctor_obj]
          change (⟨W, W⟩ : SInverseS.Pair C) =
            (⟨((finiteFreeRowCoreModelFunctor R n).obj X).of, W⟩ : SInverseS.Pair C)
          rw [finiteFreeRowCoreModelFunctor_obj]
        let a : J.obj (F.obj X, b) ⟶ J.obj (F.obj X, p) :=
          (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).map
            (X := ((finiteFreeRowCoreModelFunctor R n).obj X,
              (⟨((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ⊞
                (0 : FGProjectiveCat.IdempotentModel R)⟩ : Core (FGProjectiveCat.IdempotentModel R))))
            (Y := ((finiteFreeRowCoreModelFunctor R n).obj X,
              (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
                Core (FGProjectiveCat.IdempotentModel R))))
            ((𝟙 ((finiteFreeRowCoreModelFunctor R n).obj X),
              (⟨(isoBiprodZero (X := ((Idempotents.toKaroubi
                (FGProjectiveCat.FiniteRowRanks R)).obj n))
                (isZero_zero (FGProjectiveCat.IdempotentModel R))).symm⟩ :
                (⟨((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ⊞
                  (0 : FGProjectiveCat.IdempotentModel R)⟩ :
                    Core (FGProjectiveCat.IdempotentModel R)) ⟶
                      (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
                        Core (FGProjectiveCat.IdempotentModel R)))))
        exact eqToHom hL ≫ a ≫ eqToHom hK.symm) :=
  finiteFreeRowTranslatedCoreIso_hom_app_computation07 R n X

/-- The original finite row stage mapped to the core nerve using the existing
common-Hom reader on the original categories. -/
public def finiteFreeRowStageCoreNerveMap (n : ℕ) :
    nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ⟶
      nerve (Core (FGProjectiveCat.IdempotentModel R)) :=
  nerveMapCommonHomUp.{0, u, 0} (finiteFreeRowCoreModelFunctor R n)

/-- The existing universe adapter retains the actual original core functor
on every composable-arrow simplex. -/
private theorem finiteFreeRowStageCoreNerveMap_app_computation07 (n : ℕ)
    (Δ : SimplexCategoryᵒᵖ)
    (X : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).obj Δ) :
    (finiteFreeRowStageCoreNerveMap R n).app Δ X =
      ((finiteFreeRowCoreModelFunctor R n).mapComposableArrows Δ.unop.len).obj X := by
  unfold finiteFreeRowStageCoreNerveMap
  exact nerveMapCommonHomUp_app.{0, u, 0} (finiteFreeRowCoreModelFunctor R n) Δ X

public theorem finiteFreeRowStageCoreNerveMap_app (n : ℕ)
    (Δ : SimplexCategoryᵒᵖ)
    (X : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).obj Δ) :
    (finiteFreeRowStageCoreNerveMap R n).app Δ X =
      ((finiteFreeRowCoreModelFunctor R n).mapComposableArrows Δ.unop.len).obj X :=
  finiteFreeRowStageCoreNerveMap_app_computation07 R n Δ X

/-- The SAME actual finite row stage mapped to the categorical zero-component
nerve, retaining the original opposite-GL action in the first coordinate. -/
public def finiteFreeRowStageZeroNerveMap (n : ℕ) :
    nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ⟶
      nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)) :=
  nerveMapCommonHomUp.{0, u, 0} (finiteFreeRowZeroComponentFunctor R n)

open scoped Simplicial in
/-- The common-Hom reader retains the actual zero-component functor
on every original object vertex. -/
private theorem finiteFreeRowStageZeroNerveMap_app_mk₀_computation07 (n : ℕ)
    (X : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (finiteFreeRowStageZeroNerveMap R n).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀ ((finiteFreeRowZeroComponentFunctor R n).obj X) := by
  unfold finiteFreeRowStageZeroNerveMap
  exact nerveMapCommonHomUp_app_mk₀.{0, u, 0} (finiteFreeRowZeroComponentFunctor R n) X

open scoped Simplicial in
public theorem finiteFreeRowStageZeroNerveMap_app_mk₀ (n : ℕ)
    (X : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (finiteFreeRowStageZeroNerveMap R n).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀ ((finiteFreeRowZeroComponentFunctor R n).obj X) :=
  finiteFreeRowStageZeroNerveMap_app_mk₀_computation07 R n X

private def rowStageUpNerveMap (n : ℕ) :
    nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ⟶
      nerve (AsSmall.{u} (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) :=
  nerveMapCommonHomUp.{0, u, 0}
    (AsSmall.up : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
      AsSmall.{u} (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))

/-- On homology in EVERY degree, the actual finite-stage map into the full pair
nerve is the positive core map followed by the SAME second translation. The
universe transport uses the existing AsSmall source and retains the original
maps through both literal simplex-composition squares. -/
public theorem finiteFreeRowStageHomology_translation_square
    (A : AddCommGrpCat.{u}) (q n : ℕ) :
    SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q ≫
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap (SInverseS.coreInclusion (C := FGProjectiveCat.IdempotentModel R))) A q ≫
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap (SInverseS.translateSecondFunctor
            ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))) A q =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageZeroNerveMap R n) A q ≫
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap (SInverseS.zeroComponentProperty
            (C := FGProjectiveCat.IdempotentModel R)).ι) A q := by
  let D : AsSmall.{u} (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ⥤
      SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ := AsSmall.down
  let i := SInverseS.coreInclusion (C := FGProjectiveCat.IdempotentModel R)
  let t := SInverseS.translateSecondFunctor (rowFree R n)
  let j := (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι
  let U := rowStageUpNerveMap R n
  let L := D ⋙ finiteFreeRowCoreModelFunctor R n ⋙ i ⋙ t
  let K := D ⋙ finiteFreeRowZeroComponentFunctor R n ⋙ j
  let e := Functor.isoWhiskerLeft D (finiteFreeRowTranslatedCoreIso R n)
  have h :
      SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap L) A q =
        SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap K) A q :=
    SSet.Homotopy.congr_homologyMap (C := AddCommGrpCat.{u})
      (NatTrans.nerveHomotopy e.hom) A q
  have hLeft : U ≫ nerveMap L =
      finiteFreeRowStageCoreNerveMap R n ≫ nerveMap i ≫ nerveMap t := by
    ext Δ X
    rfl
  have hRight : U ≫ nerveMap K =
      finiteFreeRowStageZeroNerveMap R n ≫ nerveMap j := by
    ext Δ X
    rfl
  have hU :
      SSet.homologyMap (C := AddCommGrpCat.{u}) (U ≫ nerveMap L) A q =
        SSet.homologyMap (C := AddCommGrpCat.{u}) (U ≫ nerveMap K) A q := by
    rw [SSet.homologyMap_comp, SSet.homologyMap_comp]
    exact congrArg (fun k => SSet.homologyMap (C := AddCommGrpCat.{u}) U A q ≫ k) h
  calc
    SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q ≫
        SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap i) A q ≫
          SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap t) A q =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (U ≫ nerveMap L) A q := by
        rw [hLeft, SSet.homologyMap_comp, SSet.homologyMap_comp]
    _ = SSet.homologyMap (C := AddCommGrpCat.{u}) (U ≫ nerveMap K) A q := hU
    _ = SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageZeroNerveMap R n) A q ≫
        SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap j) A q := by
      rw [hRight, SSet.homologyMap_comp]

/-- The generalized canonical positive fraction comparison sends an original
finite-stage core homology class divided by the rank-n regular denominator to
the EXACT original finite row-stage map into the full zero-component inclusion.
No desired homology isomorphism or replacement comparison is assumed. -/
public theorem finiteFreeRowStageHomology_fraction_characteristic
    (A : AddCommGrpCat.{u}) (q n : ℕ)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    (SInverseS.secondTranslationBKLocalizedCoreHomologyIso
        (C := FGProjectiveCat.IdempotentModel R) A q ≪≫
      SInverseS.swapHomologyIso (C := FGProjectiveCat.IdempotentModel R) A q).hom
        (LocalizedModule.mk
          (R := CategoryTheory.SInverseS.coreTranslationRing
            (FGProjectiveCat.IdempotentModel R))
          (S := CategoryTheory.SInverseS.coreTranslationDenominators
            (FGProjectiveCat.IdempotentModel R))
          (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
            (FGProjectiveCat.IdempotentModel R) A q)
          (((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
            (FGProjectiveCat.IdempotentModel R) A q).inv
              (SSet.homologyMap (C := AddCommGrpCat.{u})
                (finiteFreeRowStageCoreNerveMap R n) A q x)) :
            CategoryTheory.SInverseS.coreTranslationHomologyModuleCat
              (FGProjectiveCat.IdempotentModel R) A q)
          ((finiteFreeRowRegularDenominator R) ^ n)) =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (finiteFreeRowStageZeroNerveMap R n ≫
          nerveMap (SInverseS.zeroComponentProperty
            (C := FGProjectiveCat.IdempotentModel R)).ι) A q x := by
  let C := FGProjectiveCat.IdempotentModel R
  let W := rowFree R n
  let s := toSkeleton W
  let ε := SInverseS.coreTranslationHomologyModuleAddCommGrpIso C A q
  let u := SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q x
  let y : SInverseS.coreTranslationHomologyModule C A q := ε.inv u
  have hJ : SInverseS.pairTranslationHomologyIso C A q s =
      SInverseS.pairTranslationHomologyIsoToSkeleton C A q W := by
    apply Iso.ext
    exact SInverseS.pairTranslationHomologyIso_hom C A q s
  have hInv : (SInverseS.pairTranslationHomologyIso C A q s).inv =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (nerveMap (SInverseS.translateSecondFunctor W)) A q :=
    congrArg Iso.inv hJ
  have hy := congrArg (fun f : (nerve (Core C)).homology (C := AddCommGrpCat.{u}) A q ⟶
      (nerve (Core C)).homology (C := AddCommGrpCat.{u}) A q => f u) ε.inv_hom_id
  change ε.hom y = u at hy
  have hFraction :=
    (SInverseS.secondTranslationBKLocalizedCoreHomologyIso_swap_characteristic
      (C := C) A q).2.2.2 s y
  have hPoint := ConcreteCategory.congr_hom
    (finiteFreeRowStageHomology_translation_square R A q n) x
  simp only [CategoryTheory.comp_apply] at hPoint
  have hFinish : (SInverseS.pairTranslationHomologyIso C A q s).inv
        (SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap (SInverseS.coreInclusion (C := C))) A q (ε.hom y)) =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (finiteFreeRowStageZeroNerveMap R n ≫
          nerveMap (SInverseS.zeroComponentProperty (C := C)).ι) A q x := by
    rw [hInv, hy, SSet.homologyMap_comp]
    exact hPoint
  rw [finiteFreeRowRegularDenominator_pow_eq_free]
  exact hFraction.trans hFinish

/-- The actual original opposite finite-GL row functor is fully faithful.
Its inverse on arrows is derived from the existing row-automorphism equivalence,
with the original computed object transports retained. -/
public def finiteFreeRowCoreFullyFaithful (n : ℕ) :
    (finiteFreeRowCoreModelFunctor R n).FullyFaithful where
  preimage {X Y} f :=
    (rowFreeAutMulEquiv R n).symm (Aut.of
      ((eqToIso (finiteFreeRowCoreModelFunctor_obj R n X)).symm ≪≫
        f.iso ≪≫ eqToIso (finiteFreeRowCoreModelFunctor_obj R n Y)))
  map_preimage {X Y} f := by
    let F : SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
        Core (FGProjectiveCat.IdempotentModel R) := finiteFreeRowCoreModelFunctor R n
    let E : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ≃* Aut (rowFree R n) :=
      rowFreeAutMulEquiv R n
    let eX : (F.obj X).of ≅ rowFree R n :=
      eqToIso (finiteFreeRowCoreModelFunctor_obj R n X)
    let eY : (F.obj Y).of ≅ rowFree R n :=
      eqToIso (finiteFreeRowCoreModelFunctor_obj R n Y)
    let a : Aut (rowFree R n) := Aut.of
      ((eqToIso (finiteFreeRowCoreModelFunctor_obj R n X)).symm ≪≫
        f.iso ≪≫ eqToIso (finiteFreeRowCoreModelFunctor_obj R n Y))
    let g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ := E.symm a
    have hInverse : E g = a := E.apply_symm_apply a
    have hAut : FGProjectiveCat.IdempotentModel.freeAut R n g = a.asIso :=
      (rowFreeAutMulEquiv_asIso R n g).symm.trans
        (congrArg (fun b : Aut (rowFree R n) => b.asIso) hInverse)
    have hMap := finiteFreeRowCoreModelFunctor_map_iso R n (X := X) (Y := Y) g
    have hIso : eX.symm ≪≫ (F.map g).iso ≪≫ eY = eX.symm ≪≫ f.iso ≪≫ eY :=
      hMap.trans hAut
    let mHom : (F.obj X).of ⟶ (F.obj Y).of := (F.map g).iso.hom
    let fHom : (F.obj X).of ⟶ (F.obj Y).of := f.iso.hom
    have hHom : eX.inv ≫ mHom ≫ eY.hom = eX.inv ≫ fHom ≫ eY.hom :=
      congrArg (fun e : rowFree R n ≅ rowFree R n => e.hom) hIso
    have hPost : (eX.inv ≫ mHom) ≫ eY.hom = (eX.inv ≫ fHom) ≫ eY.hom :=
      (Category.assoc eX.inv mHom eY.hom).trans
        (hHom.trans (Category.assoc eX.inv fHom eY.hom).symm)
    have hPre : eX.inv ≫ mHom = eX.inv ≫ fHom :=
      (cancel_mono eY.hom).mp hPost
    have hResult : mHom = fHom := (cancel_epi eX.inv).mp hPre
    have hCore : F.map (X := X) (Y := Y) g = f :=
      @Core.hom_ext (FGProjectiveCat.IdempotentModel R)
        (inferInstance : Category (FGProjectiveCat.IdempotentModel R))
        (F.obj X) (F.obj Y) (F.map (X := X) (Y := Y) g) f hResult
    dsimp only [F, E, g, a] at hCore
    exact hCore

  preimage_map {X Y} g := by
    let eX := eqToIso (finiteFreeRowCoreModelFunctor_obj R n X)
    let eY := eqToIso (finiteFreeRowCoreModelFunctor_obj R n Y)
    let a : Aut (rowFree R n) := Aut.of
      (eX.symm ≪≫ ((finiteFreeRowCoreModelFunctor R n).map g).iso ≪≫ eY)
    have hMap := finiteFreeRowCoreModelFunctor_map_iso R n (X := X) (Y := Y) g
    have hIso : a.asIso = (rowFreeAutMulEquiv R n g).asIso :=
      hMap.trans (rowFreeAutMulEquiv_asIso R n g).symm
    have ha : a = rowFreeAutMulEquiv R n g :=
      (Aut.isoEquiv (X := rowFree R n)).injective hIso
    change (rowFreeAutMulEquiv R n).symm a = g
    exact (congrArg (rowFreeAutMulEquiv R n).symm ha).trans
      ((rowFreeAutMulEquiv R n).symm_apply_apply g)

private instance rowCoreFunctorFull (n : ℕ) :
    (finiteFreeRowCoreModelFunctor R n).Full :=
  (finiteFreeRowCoreFullyFaithful R n).full

private instance rowCoreFunctorFaithful (n : ℕ) :
    (finiteFreeRowCoreModelFunctor R n).Faithful :=
  (finiteFreeRowCoreFullyFaithful R n).faithful

/-- The SAME finite row functor, restricted to the literal full isomorphism
class of the rank-n free object in the original projective core. This is not
the entire Grothendieck-grade component. -/
public def finiteFreeRowCoreClassFunctor (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ⥤
      ObjectProperty.FullSubcategory
        (fun Z : Core (FGProjectiveCat.IdempotentModel R) =>
          Nonempty (((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ≅ Z.of)) :=
  ObjectProperty.lift
    (fun Z : Core (FGProjectiveCat.IdempotentModel R) =>
      Nonempty (((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ≅ Z.of))
    (finiteFreeRowCoreModelFunctor R n)
    (fun X => ⟨(eqToIso (finiteFreeRowCoreModelFunctor_obj R n X)).symm⟩)

private instance rowCoreClassFunctorIsEquivalence (n : ℕ) :
    (finiteFreeRowCoreClassFunctor R n).IsEquivalence where
  faithful := by
    change (ObjectProperty.lift _ (finiteFreeRowCoreModelFunctor R n) _).Faithful
    infer_instance
  full := by
    change (ObjectProperty.lift _ (finiteFreeRowCoreModelFunctor R n) _).Full
    infer_instance
  essSurj :=
    { mem_essImage Z := by
        obtain ⟨e⟩ := Z.property
        refine ⟨SingleObj.star _, ⟨?_⟩⟩
        exact ObjectProperty.isoMk _ (Core.isoMk
          (eqToIso (finiteFreeRowCoreModelFunctor_obj R n (SingleObj.star _)) ≪≫ e)) }

/-- The original opposite finite general-linear category is equivalent to its
actual rank-n core isomorphism class. All arrows and the quasi-inverse are
derived; no classifying/model/comparison witness is supplied. -/
public def finiteFreeRowCoreClassEquivalence (n : ℕ) :
    SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ ≌
      ObjectProperty.FullSubcategory
        (fun Z : Core (FGProjectiveCat.IdempotentModel R) =>
          Nonempty (((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ≅ Z.of)) :=
  (finiteFreeRowCoreClassFunctor R n).asEquivalence

/-- The equivalence's forward functor is the SAME actual row functor restricted
to its computed isomorphism class. -/
private theorem finiteFreeRowCoreClassEquivalence_functor_computation07 (n : ℕ) :
    (finiteFreeRowCoreClassEquivalence R n).functor = finiteFreeRowCoreClassFunctor R n := by
  unfold finiteFreeRowCoreClassEquivalence
  rfl

public theorem finiteFreeRowCoreClassEquivalence_functor (n : ℕ) :
    (finiteFreeRowCoreClassEquivalence R n).functor = finiteFreeRowCoreClassFunctor R n :=
  finiteFreeRowCoreClassEquivalence_functor_computation07 R n

/-- The ORIGINAL finite-nerve successor map is the existing opposite block
stabilization map, without changing a group element or the source reader. -/
public theorem finiteFreeRowOriginalNerveSuccessor_eq (n : ℕ) :
    (finiteBGLNerveDiagram R).map (homOfLE (Nat.le_succ n)) =
      nerveMap (finiteOppositeGLRowStabilizationFunctor R n) := by
  change nerveMap ((finiteClassifyingCategoryDiagram R).map
    (homOfLE (Nat.le_succ n))).toFunctor = _
  rw [finiteClassifyingCategoryDiagram_map_toFunctor]
  simp only [finiteGLDiagram_obj_map_succ, finiteGLDiagram_obj_obj_of, GrpCat.hom_ofHom]
  rfl

/-- The SAME original finite nerve block-stabilization map is monic, derived
from the existing injective matrix stabilization and original nerve reader. -/
public theorem finiteFreeRowStabilizationNerve_mono (n : ℕ) :
    Mono (nerveMap (finiteOppositeGLRowStabilizationFunctor R n)) := by
  have hOriginal :
      Mono ((finiteBGLNerveDiagram R).map (homOfLE (Nat.le_succ n))) := by
    change Mono (finiteBGLSuccessorNerveMap R n)
    exact finiteBGLSuccessorNerveMap_mono R n
  exact (finiteFreeRowOriginalNerveSuccessor_eq R n) ▸ hOriginal

/-- The actual row successor natural transformation gives a WHOLE simplicial
homotopy on the ORIGINAL finite stage, through the existing AsSmall adapter. -/
public def finiteFreeRowSuccessorNerveHomotopy (n : ℕ) :
    SSet.Homotopy (finiteFreeRowStageZeroNerveMap R n)
      (nerveMap (finiteOppositeGLRowStabilizationFunctor R n) ≫
        finiteFreeRowStageZeroNerveMap R (n + 1)) := by
  let D : AsSmall.{u} (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) ⥤
      SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ := AsSmall.down
  let α := Functor.whiskerLeft D (finiteFreeRowSuccessorNatTrans R n)
  let H := (NatTrans.nerveHomotopy α).precomp (rowStageUpNerveMap R n)
  have h0 : rowStageUpNerveMap R n ≫ nerveMap (D ⋙ finiteFreeRowZeroComponentFunctor R n) =
      finiteFreeRowStageZeroNerveMap R n := by
    ext Δ X
    rfl
  have h1 : rowStageUpNerveMap R n ≫
        nerveMap (D ⋙ finiteOppositeGLRowStabilizationFunctor R n ⋙
          finiteFreeRowZeroComponentFunctor R (n + 1)) =
      nerveMap (finiteOppositeGLRowStabilizationFunctor R n) ≫
        finiteFreeRowStageZeroNerveMap R (n + 1) := by
    ext Δ X
    rfl
  simpa only [h0, h1] using H

/-- Ordinary realization of the SAME whole successor homotopy; both endpoints
are the literal original row maps and the original block stabilization. -/
public def finiteFreeRowSuccessorTopHomotopy (n : ℕ) :
    TopCat.Homotopy (SSet.toTop.map (finiteFreeRowStageZeroNerveMap R n))
      (SSet.toTop.map (nerveMap (finiteOppositeGLRowStabilizationFunctor R n)) ≫
        SSet.toTop.map (finiteFreeRowStageZeroNerveMap R (n + 1))) := by
  let f := finiteFreeRowStageZeroNerveMap R n
  let s := nerveMap (finiteOppositeGLRowStabilizationFunctor R n)
  let g := finiteFreeRowStageZeroNerveMap R (n + 1)
  let H := SSet.realizeHomotopy _ _ f (s ≫ g)
    (finiteFreeRowSuccessorNerveHomotopy R n)
  have htarget : (SSet.toTop.map (s ≫ g)).hom =
      (SSet.toTop.map s ≫ SSet.toTop.map g).hom :=
    congrArg (fun h => h.hom) (SSet.toTop.map_comp s g)
  exact H.cast rfl htarget

/-- The original realized block-stabilization map is a Hurewicz cofibration,
using the existing realization theorem on the derived simplicial Mono. -/
public theorem finiteFreeRowSuccessorTop_isHurewiczCofibration (n : ℕ) :
    TopCat.IsHurewiczCofibration
      (SSet.toTop.map (nerveMap (finiteOppositeGLRowStabilizationFunctor R n))) := by
  letI : Mono (nerveMap (finiteOppositeGLRowStabilizationFunctor R n)) :=
    finiteFreeRowStabilizationNerve_mono R n
  intro Z instZ f H h0
  exact @SSet.toTop_map_isHurewiczCofibration _ _
    (nerveMap (finiteOppositeGLRowStabilizationFunctor R n)) inferInstance Z instZ f H h0

/-- The original free-object successor Iso gives the actual core translation
versus block-stabilization natural Iso, retaining the original row action. -/
public def finiteFreeRowCoreSuccessorNatIso (n : ℕ) :
    finiteFreeRowCoreModelFunctor R n ⋙ SInverseS.coreLeftTranslationFunctor
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)) ≅
      finiteOppositeGLRowStabilizationFunctor R n ⋙
        finiteFreeRowCoreModelFunctor R (n + 1) :=
  NatIso.ofComponents (fun _ => Core.isoMk (rowSuccessorIso R n)) (by
    intro X Y g
    apply Core.hom_ext
    have h₁ : ((finiteFreeRowCoreModelFunctor R n).map g).iso =
        FGProjectiveCat.IdempotentModel.freeAut R n g := by
      have h := finiteFreeRowCoreModelFunctor_map_iso R n g
      change (Iso.refl _) ≪≫ ((finiteFreeRowCoreModelFunctor R n).map g).iso ≪≫
        Iso.refl _ = _ at h
      simpa only [Iso.refl_trans, Iso.trans_refl] using h
    let g' := (finiteOppositeGLRowStabilizationFunctor R n).map g
    have h₂ : ((finiteFreeRowCoreModelFunctor R (n + 1)).map g').iso =
        FGProjectiveCat.IdempotentModel.freeAut R (n + 1) g' := by
      have h := finiteFreeRowCoreModelFunctor_map_iso R (n + 1) g'
      change (Iso.refl _) ≪≫ ((finiteFreeRowCoreModelFunctor R (n + 1)).map g').iso ≪≫
        Iso.refl _ = _ at h
      simpa only [Iso.refl_trans, Iso.trans_refl] using h
    change ((SInverseS.coreLeftTranslationFunctor (rowFree R 1)).map
        ((finiteFreeRowCoreModelFunctor R n).map g)).iso.hom ≫
          (rowSuccessorIso R n).hom =
      (rowSuccessorIso R n).hom ≫
        ((finiteFreeRowCoreModelFunctor R (n + 1)).map g').iso.hom
    rw [SInverseS.coreLeftTranslationFunctor_map_iso_hom,
      congrArg Iso.hom h₁, congrArg Iso.hom h₂]
    exact congrArg Iso.hom (rowSuccessorIso_naturality R n g))

/-- Every original composable chain is sent by the SAME actual finite row
functor through the canonical common-Hom reader. -/
private theorem finiteFreeRowStageZeroNerveMap_app_computation07 (n : ℕ)
    (D : SimplexCategoryᵒᵖ)
    (X : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).obj D) :
    (finiteFreeRowStageZeroNerveMap R n).app D X =
      ((finiteFreeRowZeroComponentFunctor R n).mapComposableArrows D.unop.len).obj X := by
  unfold finiteFreeRowStageZeroNerveMap
  exact nerveMapCommonHomUp_app.{0, u, 0} (finiteFreeRowZeroComponentFunctor R n) D X

public theorem finiteFreeRowStageZeroNerveMap_app (n : ℕ)
    (D : SimplexCategoryᵒᵖ)
    (X : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).obj D) :
    (finiteFreeRowStageZeroNerveMap R n).app D X =
      ((finiteFreeRowZeroComponentFunctor R n).mapComposableArrows D.unop.len).obj X :=
  finiteFreeRowStageZeroNerveMap_app_computation07 R n D X

/-- Restricting the ORIGINAL categorical telescope map to an original
finite fiber gives its actual row functor. The Iso is the existing
Grothendieck fiber Iso for the SAME assembled maps. -/
public def finiteBGLTelescopeToRowZeroComponentFiberIso (n : ℕ) :
    finiteBGLTelescopeFiberInclusion R n ⋙ finiteBGLTelescopeToRowZeroComponent R ≅
      finiteFreeRowZeroComponentFunctor R n := by
  let I := finiteBGLTelescopeFiberInclusion R n
  let T := finiteBGLTelescopeToRowZeroComponent R
  let D := finiteClassifyingCategoryDiagram R
  let Fib : ∀ k : ℕ, D.obj k ⥤
      SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) := rowDiagramFiber R
  let hom : ∀ {k l : ℕ} (f : k ⟶ l), Fib k ⟶ (D.map f).toFunctor ⋙ Fib l :=
    fun {k l} f => finiteFreeRowTransitionNatTrans R f
  let hid : ∀ k : ℕ,
      hom (𝟙 k) = eqToHom (Grothendieck.fiberFunctor_id_eq D Fib k) :=
    fun k => rowTransitionNatTrans_id R k
  let hcomp : ∀ k l m : ℕ, ∀ (f : k ⟶ l) (g : l ⟶ m),
      hom (f ≫ g) = hom f ≫ Functor.whiskerLeft (D.map f).toFunctor (hom g) ≫
        eqToHom (Grothendieck.fiberFunctor_comp_eq D Fib f g) :=
    fun k l m f g => rowTransitionNatTrans_comp R k l m f g
  let T' := Grothendieck.functorFromWithCoherence D Fib hom hid hcomp
  have hT : T = T' := rfl
  let B := Fib n
  let hObj (X : (finiteClassifyingCategoryDiagram R).obj n) :
      (I ⋙ T').obj X = B.obj X :=
    Grothendieck.functorFromWithCoherence_obj D Fib hom hid hcomp (I.obj X)
  change I ⋙ T ≅ B
  let e : I ⋙ T' ≅ B := NatIso.ofComponents (fun X => eqToIso (hObj X)) (by
    intro X Y f
    have hIX : I.obj X = (⟨n, X⟩ : Grothendieck D) := Grothendieck.ι_obj D n X
    have hIY : I.obj Y = (⟨n, Y⟩ : Grothendieck D) := Grothendieck.ι_obj D n Y
    let p : (D.map (𝟙 n)).toFunctor.obj X = X := by
      rw [D.map_id]
      rfl
    let f₀ : I.obj X ⟶ I.obj Y :=
      { base := 𝟙 n
        fiber := eqToHom p ≫ f }
    have hIf : I.map f = f₀ := Grothendieck.ι_map D n f
    let q := Functor.congr_obj (Grothendieck.fiberFunctor_id_eq D Fib n) X
    have hIdApp : (hom (𝟙 n)).app X = eqToHom q := by
      have h := congrArg
        (fun a : Fib n ⟶ (D.map (𝟙 n)).toFunctor ⋙ Fib n => a.app X) (hid n)
      exact h.trans (eqToHom_app (Grothendieck.fiberFunctor_id_eq D Fib n) X)
    have hCancel : (hom (𝟙 n)).app X ≫ (Fib n).map (eqToHom p) =
        𝟙 ((Fib n).obj X) := by
      rw [hIdApp, eqToHom_map, eqToHom_trans]
      exact eqToHom_refl _ _
    have hAfter : (hom (𝟙 n)).app X ≫ (Fib n).map (eqToHom p ≫ f) =
        (Fib n).map f := by
      rw [(Fib n).map_comp, ← Category.assoc, hCancel, Category.id_comp]
    have hMap : (I ⋙ T').map f ≍ B.map f := by
      have hInput : T'.map (I.map f) = T'.map f₀ :=
        congrArg (fun a : I.obj X ⟶ I.obj Y => T'.map a) hIf
      have hRecipe := Grothendieck.functorFromWithCoherence_map D Fib hom hid hcomp f₀
      have hResult : T'.map f₀ ≍ (Fib n).map f := by
        apply (heq_of_eq hRecipe).trans
        cases hIX
        cases hIY
        change (hom (𝟙 n)).app X ≫ (Fib n).map (eqToHom p ≫ f) ≍ (Fib n).map f
        exact heq_of_eq hAfter
      exact (heq_of_eq hInput).trans hResult
    simp only [eqToIso.hom]
    apply (comp_eqToHom_iff (hObj Y) ((I ⋙ T').map f)
      (eqToHom (hObj X) ≫ B.map f)).2
    exact ((conj_eqToHom_iff_heq ((I ⋙ T').map f) (B.map f)
      (hObj X) (hObj Y)).2 hMap).trans (Category.assoc _ _ _).symm)
  exact Functor.isoWhiskerLeft I (eqToIso hT) ≪≫ e

/-- The original telescope map and original finite row map have a WHOLE
simplicial homotopy on the original finite-stage source. -/
public def finiteBGLTelescopeFiberZeroNerveHomotopy (n : ℕ) :
    SSet.Homotopy
      (nerveMap (finiteBGLTelescopeFiberInclusion R n) ≫
        finiteBGLTelescopeToRowZeroComponentNerve R)
      (finiteFreeRowStageZeroNerveMap R n) := by
  change SSet.Homotopy
    (nerveMap (finiteBGLTelescopeFiberInclusion R n) ≫
      nerveMapCommonHomUp.{0, u, 0} (finiteBGLTelescopeToRowZeroComponent R))
    (nerveMapCommonHomUp.{0, u, 0} (finiteFreeRowZeroComponentFunctor R n))
  rw [nerveMap_nerveMapCommonHomUp_comp.{0, u, 0}]
  exact NatTrans.nerveHomotopyCommonHomUp.{0, u, 0}
    (finiteBGLTelescopeToRowZeroComponentFiberIso R n).hom

/-- The ordinary telescope comparison is the realization of the SAME
original simplicial comparison. -/
public theorem finiteBGLTelescopeToRowZeroComponentTop_eq :
    finiteBGLTelescopeToRowZeroComponentTop R =
      SSet.toTop.map (finiteBGLTelescopeToRowZeroComponentNerve R) := by
  unfold finiteBGLTelescopeToRowZeroComponentTop
  rfl

/-- The public integral arrow is the homology image of the SAME original
ordinary telescope comparison. -/
public theorem finiteBGLTelescopeToRowZeroComponentIntegralHomologyMap_eq (q : ℕ) :
    finiteBGLTelescopeToRowZeroComponentIntegralHomologyMap R q =
      (AlgebraicTopology.singularIntegralHomologyFunctor q).map
        (finiteBGLTelescopeToRowZeroComponentTop R) := by
  unfold finiteBGLTelescopeToRowZeroComponentIntegralHomologyMap
  rfl

end AlgebraicKTheory.StableGL


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The original rank-diagonal transition on an identity indexing arrow
is the original identity at that same finite row object. -/
public theorem finiteFreeRowTransitionArrow_id (n : ℕ) :
    finiteFreeRowTransitionArrow R (𝟙 n) =
      𝟙 ((finiteFreeRowZeroComponentFunctor R n).obj (SingleObj.star _)) := by
  exact (rowStageObjectDiagram R).map_id n

/-- Every original pair of composable rank arrows has the same literal
composite under the original row transition sequence. -/
public theorem finiteFreeRowTransitionArrow_comp {n m k : ℕ}
    (f : n ⟶ m) (g : m ⟶ k) :
    finiteFreeRowTransitionArrow R (f ≫ g) =
      finiteFreeRowTransitionArrow R f ≫ finiteFreeRowTransitionArrow R g := by
  exact (rowStageObjectDiagram R).map_comp f g

/-- The original iterated transition at the actual successor rank is the
same original free-row successor arrow. -/
public theorem finiteFreeRowTransitionArrow_succ (n : ℕ) :
    finiteFreeRowTransitionArrow R (homOfLE (Nat.le_succ n)) =
      finiteFreeRowSuccessorArrow R n := by
  exact rowTransitionArrow_succ R n

/-- The original whole rank-transition natural transformation has its
actual original row arrow at the original finite source point. -/
public theorem finiteFreeRowTransitionNatTrans_app {n m : ℕ} (f : n ⟶ m) :
    (finiteFreeRowTransitionNatTrans R f).app
      (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) =
        finiteFreeRowTransitionArrow R f := by
  exact rowTransitionNatTransAppPoint R f

/-- The actual whole identity coherence used by the original assembled
row telescope functor, with every original fiber functor displayed. -/
public theorem finiteFreeRowTransitionNatTrans_id (n : ℕ) :
    finiteFreeRowTransitionNatTrans R (𝟙 n) =
      eqToHom (Grothendieck.fiberFunctor_id_eq
        (finiteClassifyingCategoryDiagram R)
        (fun k => finiteFreeRowZeroComponentFunctor R k) n) := by
  exact rowTransitionNatTrans_id R n

/-- The actual whole composition coherence of the original row telescope
transitions retains its original functor-composition transport. -/
public theorem finiteFreeRowTransitionNatTrans_comp {n m k : ℕ}
    (f : n ⟶ m) (g : m ⟶ k) :
    finiteFreeRowTransitionNatTrans R (f ≫ g) =
      finiteFreeRowTransitionNatTrans R f ≫
        Functor.whiskerLeft ((finiteClassifyingCategoryDiagram R).map f).toFunctor
          (finiteFreeRowTransitionNatTrans R g) ≫
        eqToHom (Grothendieck.fiberFunctor_comp_eq
          (finiteClassifyingCategoryDiagram R)
          (fun l => finiteFreeRowZeroComponentFunctor R l) f g) := by
  exact rowTransitionNatTrans_comp R n m k f g

/-- Every original telescope arrow is sent by the original rank-transition
component followed by its actual original finite-row fiber map. The only
endpoint transports are the previously established object-value equalities. -/
public theorem finiteBGLTelescopeToRowZeroComponent_map
    {X Y : FiniteBGLTelescopeCategory R} (f : X ⟶ Y) :
    eqToHom (finiteBGLTelescopeToRowZeroComponent_obj R X).symm ≫
      (finiteBGLTelescopeToRowZeroComponent R).map f ≫
      eqToHom (finiteBGLTelescopeToRowZeroComponent_obj R Y) =
        (finiteFreeRowTransitionNatTrans R f.base).app X.fiber ≫
          (finiteFreeRowZeroComponentFunctor R Y.base).map f.fiber := by
  have hMap :
      (finiteBGLTelescopeToRowZeroComponent R).map f =
        (finiteFreeRowTransitionNatTrans R f.base).app X.fiber ≫
          (finiteFreeRowZeroComponentFunctor R Y.base).map f.fiber := by
    exact Grothendieck.functorFromWithCoherence_map
      (finiteClassifyingCategoryDiagram R) (rowDiagramFiber R)
      (finiteFreeRowTransitionNatTrans R) (rowTransitionNatTrans_id R)
      (rowTransitionNatTrans_comp R) f
  have hTransport : HEq
      (eqToHom (finiteBGLTelescopeToRowZeroComponent_obj R X).symm ≫
        (finiteBGLTelescopeToRowZeroComponent R).map f ≫
        eqToHom (finiteBGLTelescopeToRowZeroComponent_obj R Y))
      ((finiteBGLTelescopeToRowZeroComponent R).map f) :=
    (eqToHom_comp_heq
      ((finiteBGLTelescopeToRowZeroComponent R).map f ≫
        eqToHom (finiteBGLTelescopeToRowZeroComponent_obj R Y))
      (finiteBGLTelescopeToRowZeroComponent_obj R X).symm).trans
      (comp_eqToHom_heq ((finiteBGLTelescopeToRowZeroComponent R).map f)
        (finiteBGLTelescopeToRowZeroComponent_obj R Y))
  exact eq_of_heq (hTransport.trans (heq_of_eq hMap))

/-- The original row fiber Iso has its actual equality-morphism component
at every original finite object; its forward orientation and endpoints remain. -/
public theorem finiteBGLTelescopeToRowZeroComponentFiberIso_hom_app
    (n : ℕ) (X : (finiteClassifyingCategoryDiagram R).obj n) :
    (finiteBGLTelescopeToRowZeroComponentFiberIso R n).hom.app X =
      eqToHom (finiteBGLTelescopeToRowZeroComponent_obj R
        ((finiteBGLTelescopeFiberInclusion R n).obj X)) := by
  let hObj :
      (finiteBGLTelescopeFiberInclusion R n ⋙ finiteBGLTelescopeToRowZeroComponent R).obj X =
        (rowDiagramFiber R n).obj X :=
    finiteBGLTelescopeToRowZeroComponent_obj R
      ((finiteBGLTelescopeFiberInclusion R n).obj X)
  change (𝟙 _ ≫ eqToHom hObj) = eqToHom hObj
  rw [Category.id_comp]

end AlgebraicKTheory.StableGL

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The original finite diagram's successor is the original opposite
row stabilization as a WHOLE functor, retaining its actual object and map. -/
public theorem finiteFreeRowOriginalSuccessorFunctor_eq (n : ℕ) :
    ((finiteClassifyingCategoryDiagram R).map
      (homOfLE (Nat.le_succ n))).toFunctor =
        finiteOppositeGLRowStabilizationFunctor R n := by
  rw [finiteClassifyingCategoryDiagram_map_toFunctor]
  simp only [finiteGLDiagram_obj_map_succ, finiteGLDiagram_obj_obj_of, GrpCat.hom_ofHom]
  rfl

/-- The original iterated row transformation at the successor rank is
the original row successor transformation with its actual target transport. -/
public theorem finiteFreeRowTransitionNatTrans_succ (n : ℕ) :
    let h := congrArg
      (fun D => D ⋙ finiteFreeRowZeroComponentFunctor R (n + 1))
      (finiteFreeRowOriginalSuccessorFunctor_eq R n)
    finiteFreeRowTransitionNatTrans R (homOfLE (Nat.le_succ n)) ≫ eqToHom h =
      finiteFreeRowSuccessorNatTrans R n := by
  let f : n ⟶ n + 1 := homOfLE (Nat.le_succ n)
  let Cₙ : Cat.{u, 0} := (finiteClassifyingCategoryDiagram R).obj n
  let Cₘ : Cat.{u, 0} := (finiteClassifyingCategoryDiagram R).obj (n + 1)
  let D := SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)
  let F : Cₙ ⥤ D := rowDiagramFiber R n
  let M : Cₘ ⥤ D := rowDiagramFiber R (n + 1)
  let T : Cₙ ⥤ Cₘ := finiteOppositeGLRowStabilizationFunctor R n
  let G : Cₙ ⥤ D := ((finiteClassifyingCategoryDiagram R).map f).toFunctor ⋙ M
  let H : Cₙ ⥤ D := T ⋙ M
  let τ : F ⟶ G := finiteFreeRowTransitionNatTrans R f
  let σ : F ⟶ H := finiteFreeRowSuccessorNatTrans R n
  have hT : ((finiteClassifyingCategoryDiagram R).map f).toFunctor = T :=
    finiteFreeRowOriginalSuccessorFunctor_eq R n
  let e : G = H := congrArg (fun V : Cₙ ⥤ Cₘ => V ⋙ M) hT
  change τ ≫ (eqToHom e : G ⟶ H) = σ
  let cₙ : Cₙ := SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ
  let cₘ : Cₘ := SingleObj.star (Matrix.GeneralLinearGroup (Fin (n + 1)) R)ᵐᵒᵖ
  have hCₙ : Subsingleton Cₙ := by
    change Subsingleton ((finiteClassifyingCategoryDiagram R).obj n)
    rw [finiteClassifyingCategoryDiagram_obj R n]
    simpa only [Cat.of_α] using
      (show Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) from
        ⟨fun _ _ => Quiver.SingleObj.ext⟩)
  have hCₘ : Subsingleton Cₘ := by
    change Subsingleton ((finiteClassifyingCategoryDiagram R).obj (n + 1))
    rw [finiteClassifyingCategoryDiagram_obj R (n + 1)]
    simpa only [Cat.of_α] using
      (show Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin (n + 1)) R)ᵐᵒᵖ) from
        ⟨fun _ _ => Quiver.SingleObj.ext⟩)
  have hSource : F.obj cₙ =
      (finiteFreeRowZeroComponentFunctor R n).obj
        (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) := by rfl
  have hPoint : T.obj cₙ = cₘ := @Subsingleton.elim _ hCₘ _ _
  have hTarget : H.obj cₙ =
      (finiteFreeRowZeroComponentFunctor R (n + 1)).obj
        (SingleObj.star (Matrix.GeneralLinearGroup (Fin (n + 1)) R)ᵐᵒᵖ) :=
    congrArg M.obj hPoint
  have hApp : (τ ≫ (eqToHom e : G ⟶ H)).app cₙ =
      τ.app cₙ ≫ (eqToHom e : G ⟶ H).app cₙ :=
    NatTrans.comp_app τ (eqToHom e : G ⟶ H) cₙ
  have hEqApp : (eqToHom e : G ⟶ H).app cₙ =
      eqToHom (Functor.congr_obj e cₙ) := eqToHom_app e cₙ
  have hTransport : (τ ≫ (eqToHom e : G ⟶ H)).app cₙ =
      τ.app cₙ ≫ eqToHom (Functor.congr_obj e cₙ) :=
    hApp.trans (congrArg (fun a : G.obj cₙ ⟶ H.obj cₙ => τ.app cₙ ≫ a) hEqApp)
  have hStrip : (τ ≫ (eqToHom e : G ⟶ H)).app cₙ ≍ τ.app cₙ :=
    (heq_of_eq hTransport).trans
      (comp_eqToHom_heq (τ.app cₙ) (Functor.congr_obj e cₙ))
  have hOriginalArrow : (rowStageObjectDiagram R).map f ≍
      finiteFreeRowSuccessorArrow R n := by
    change finiteFreeRowTransitionArrow R f ≍ finiteFreeRowSuccessorArrow R n
    exact heq_of_eq (finiteFreeRowTransitionArrow_succ R n)
  have hTransition : τ.app cₙ ≍ finiteFreeRowSuccessorArrow R n :=
    (rowTransitionNatTransStagePointHEq R f).trans hOriginalArrow
  have hSuccessor :
      (finiteFreeRowSuccessorNatTrans R n).app
        (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) =
          finiteFreeRowSuccessorArrow R n := by
    exact SingleObj.natTrans_app
      (F := finiteFreeRowZeroComponentFunctor R n)
      (G := finiteOppositeGLRowStabilizationFunctor R n ⋙
        finiteFreeRowZeroComponentFunctor R (n + 1))
      (finiteFreeRowSuccessorArrow R n)
      (fun g => finiteFreeRowSuccessorArrow_naturality R n g)
      (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
  have hLeft : (τ ≫ (eqToHom e : G ⟶ H)).app cₙ =
      eqToHom hSource ≫ finiteFreeRowSuccessorArrow R n ≫ eqToHom hTarget.symm :=
    (conj_eqToHom_iff_heq ((τ ≫ (eqToHom e : G ⟶ H)).app cₙ)
      (finiteFreeRowSuccessorArrow R n) hSource hTarget).mpr (hStrip.trans hTransition)
  have hRight : σ.app cₙ =
      eqToHom hSource ≫ finiteFreeRowSuccessorArrow R n ≫ eqToHom hTarget.symm :=
    (conj_eqToHom_iff_heq (σ.app cₙ) (finiteFreeRowSuccessorArrow R n)
      hSource hTarget).mpr (heq_of_eq hSuccessor)
  exact rowNatTransEqAtPoint cₙ hCₙ (hLeft.trans hRight.symm)

end AlgebraicKTheory.StableGL

end


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial MonoidalCategory

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The ENTIRE original successor cylinder, with its original AsSmall
precomposition and original endpoint proofs, is the SAME native upward
cylinder of the ORIGINAL finiteFreeRowSuccessorNatTrans. No family is replaced. -/
public theorem finiteFreeRowSuccessorNerveHomotopy_h (n : ℕ) :
    (finiteFreeRowSuccessorNerveHomotopy R n).h =
      NatTrans.nerveHomotopyMapCommonHomUp.{0, u, 0}
        (finiteFreeRowSuccessorNatTrans R n) := by
  let C := SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ
  let Z := SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)
  let down : AsSmall.{u} C ⥤ C := AsSmall.down
  let Fdown : AsSmall.{u} C ⥤ Z := down ⋙ finiteFreeRowZeroComponentFunctor R n
  let Gdown : AsSmall.{u} C ⥤ Z := down ⋙
    (finiteOppositeGLRowStabilizationFunctor R n ⋙
      finiteFreeRowZeroComponentFunctor R (n + 1))
  let αdown : Fdown ⟶ Gdown :=
    Functor.whiskerLeft down (finiteFreeRowSuccessorNatTrans R n)
  change (rowStageUpNerveMap R n ▷ (Δ[1] : SSet.{u})) ≫
      NatTrans.nerveHomotopyMap (C := AsSmall.{u} C) (D := Z)
        (F := Fdown) (G := Gdown) αdown =
    NatTrans.nerveHomotopyMapCommonHomUp.{0, u, 0}
      (finiteFreeRowSuccessorNatTrans R n)
  have h := NatTrans.nerveHomotopyMapCommonHomUp_eq_asSmall.{0, u, 0}
    (finiteFreeRowSuccessorNatTrans R n)
  rw [nerveMapAsSmallUp_eq_nativeCommonHomUp,
    NatTrans.nerveHomotopyMapAsSmallDown_eq_ordinary] at h
  exact h.symm

end AlgebraicKTheory.StableGL

end


noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial ContinuousMap

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The entire ORIGINAL topological successor family is the ordinary
realization of its SAME original AsSmall simplicial successor cylinder.
Only its original endpoint casts occur; every point and time is retained. -/
public theorem finiteFreeRowSuccessorTopHomotopy_toContinuousMap (n : ℕ) :
    (finiteFreeRowSuccessorTopHomotopy R n).toContinuousMap =
      (SSet.realizeHomotopy
        (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))
        (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))
        (finiteFreeRowStageZeroNerveMap R n)
        (nerveMap (finiteOppositeGLRowStabilizationFunctor R n) ≫
          finiteFreeRowStageZeroNerveMap R (n + 1))
        (finiteFreeRowSuccessorNerveHomotopy R n)).toContinuousMap := by
  rfl

end AlgebraicKTheory.StableGL

end


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private theorem originalRowSuccessorRawValueComputed (n : ℕ) :
    eqToHom (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)).symm ≫
        (finiteFreeRowSuccessorArrow R n).hom ≫
        eqToHom (finiteFreeRowZeroComponentFunctor_obj R (n + 1) (SingleObj.star _)) =
      SInverseS.Hom.mk (rowSuccessorRawHom R n) := by
  let hx := finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)
  let hy := finiteFreeRowZeroComponentFunctor_obj R (n + 1) (SingleObj.star _)
  have h : (finiteFreeRowSuccessorArrow R n).hom =
      eqToHom hx ≫ SInverseS.Hom.mk (rowSuccessorRawHom R n) ≫ eqToHom hy.symm := rfl
  have hArrow : HEq (finiteFreeRowSuccessorArrow R n).hom
      (SInverseS.Hom.mk (rowSuccessorRawHom R n)) :=
    (conj_eqToHom_iff_heq _ _ hx hy).1 h
  exact ((conj_eqToHom_iff_heq' _ _ hx.symm hy).2 hArrow.symm).symm

/-- Removing only the original object-image transports gives the SAME
regular raw successor, with its literal rank-one stabilizer and both coordinates. -/
public theorem finiteFreeRowSuccessorArrow_hom_eq_raw (n : ℕ) :
    let free : ℕ → FGProjectiveCat.IdempotentModel R :=
      fun k => (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj k
    let e : free 1 ⊞ free n ≅ free (n + 1) :=
      biprod.braiding (free 1) (free n) ≪≫
        (FGProjectiveCat.IdempotentModel.freeBiprodIso R n 1).symm
    eqToHom (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)).symm ≫
        (finiteFreeRowSuccessorArrow R n).hom ≫
        eqToHom (finiteFreeRowZeroComponentFunctor_obj R (n + 1) (SingleObj.star _)) =
      SInverseS.Hom.mk
        (X := (⟨free n, free n⟩ : SInverseS.Pair (FGProjectiveCat.IdempotentModel R)))
        (Y := (⟨free (n + 1), free (n + 1)⟩ :
          SInverseS.Pair (FGProjectiveCat.IdempotentModel R)))
        { stabilizer := free 1
          hom₁ := e
          hom₂ := e } := by
  change eqToHom (finiteFreeRowZeroComponentFunctor_obj R n (SingleObj.star _)).symm ≫
      (finiteFreeRowSuccessorArrow R n).hom ≫
      eqToHom (finiteFreeRowZeroComponentFunctor_obj R (n + 1) (SingleObj.star _)) =
    SInverseS.Hom.mk (rowSuccessorRawHom R n)
  exact originalRowSuccessorRawValueComputed R n

private theorem originalRowTransitionStarValueComputed {n m : ℕ} (f : n ⟶ m) :
    (finiteFreeRowTransitionNatTrans R f).app
      (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) =
        finiteFreeRowTransitionArrow R f :=
  finiteFreeRowTransitionNatTrans_app R f

/-- The SAME original transformation has its actual transition at the
original unique stage object, in the complete original Ring scope. -/
public theorem finiteFreeRowTransitionNatTrans_app_star {n m : ℕ} (f : n ⟶ m) :
    (finiteFreeRowTransitionNatTrans R f).app
      (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) =
        finiteFreeRowTransitionArrow R f :=
  originalRowTransitionStarValueComputed R f

private theorem originalRowTelescopeMapAfterObjectComputed
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    eqToHom (finiteBGLTelescopeToRowZeroComponent_obj R X).symm ≫
        (finiteBGLTelescopeToRowZeroComponent R).map a ≫
        eqToHom (finiteBGLTelescopeToRowZeroComponent_obj R Y) =
      (finiteFreeRowTransitionNatTrans R a.base).app X.fiber ≫
        (finiteFreeRowZeroComponentFunctor R Y.base).map a.fiber :=
  finiteBGLTelescopeToRowZeroComponent_map R a

/-- The SAME original telescope map retains its actual base transition
and fiber map, with only its original object-image equality transports. -/
public theorem finiteBGLTelescopeToRowZeroComponent_map_after_obj
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    eqToHom (finiteBGLTelescopeToRowZeroComponent_obj R X).symm ≫
        (finiteBGLTelescopeToRowZeroComponent R).map a ≫
        eqToHom (finiteBGLTelescopeToRowZeroComponent_obj R Y) =
      (finiteFreeRowTransitionNatTrans R a.base).app X.fiber ≫
        (finiteFreeRowZeroComponentFunctor R Y.base).map a.fiber :=
  originalRowTelescopeMapAfterObjectComputed R a

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory

universe uRowZeroArrowValueRing

namespace AlgebraicKTheory.StableGL

private theorem finiteFreeRowStageZeroToBaseInclusionValueComputed
    (R : Type uRowZeroArrowValueRing) [Ring R] :
    (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι.map
        (finiteFreeRowStageZeroToBase R) =
      eqToHom (finiteFreeRowZeroComponentFunctor_obj R 0 (SingleObj.star _)) ≫
        (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).map
          ((Core.isoMk
            (x := ⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ)⟩)
            (y := ⟨(0 : FGProjectiveCat.IdempotentModel R)⟩)
            (FGProjectiveCat.IdempotentModel.freeZeroIso R)).prod
            (Core.isoMk
              (x := ⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ)⟩)
              (y := ⟨(0 : FGProjectiveCat.IdempotentModel R)⟩)
              (FGProjectiveCat.IdempotentModel.freeZeroIso R))).hom := by
  change (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).map
    ((Core.isoMk
      (x := ⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ)⟩)
      (y := ⟨(0 : FGProjectiveCat.IdempotentModel R)⟩)
      (FGProjectiveCat.IdempotentModel.freeZeroIso R)).prod
      (Core.isoMk
        (x := ⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ)⟩)
        (y := ⟨(0 : FGProjectiveCat.IdempotentModel R)⟩)
        (FGProjectiveCat.IdempotentModel.freeZeroIso R))).hom = 𝟙 _ ≫ _
  exact (Category.id_comp _).symm

/-- The whole inclusion value of the SAME original rank-zero row arrow has
its proper source-object transport and original freeZeroIso in BOTH coordinates. -/
public theorem finiteFreeRowStageZeroToBase_inclusion_value
    (R : Type uRowZeroArrowValueRing) [Ring R] :
    (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι.map
        (finiteFreeRowStageZeroToBase R) =
      eqToHom (finiteFreeRowZeroComponentFunctor_obj R 0 (SingleObj.star _)) ≫
        (SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel R)).map
          ((Core.isoMk
            (x := ⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ)⟩)
            (y := ⟨(0 : FGProjectiveCat.IdempotentModel R)⟩)
            (FGProjectiveCat.IdempotentModel.freeZeroIso R)).prod
            (Core.isoMk
              (x := ⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (0 : ℕ)⟩)
              (y := ⟨(0 : FGProjectiveCat.IdempotentModel R)⟩)
              (FGProjectiveCat.IdempotentModel.freeZeroIso R))).hom :=
  finiteFreeRowStageZeroToBaseInclusionValueComputed R

end AlgebraicKTheory.StableGL

end

noncomputable section

open CategoryTheory

universe uRowWholeFunctorValue

namespace AlgebraicKTheory.StableGL

private theorem finiteFreeRowZeroComponentFunctorCompInclusionComputed
    (R : Type uRowWholeFunctorValue) [Ring R] (n : ℕ) :
    finiteFreeRowZeroComponentFunctor R n ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι =
      ((finiteFreeRowCoreModelFunctor R n).prod'
        ((Functor.const _).obj
          (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
            Core (FGProjectiveCat.IdempotentModel R)))) ⋙
        SInverseS.corePairInclusion := rfl

/-- The WHOLE original finite-free Pair map is its original core row action
and constant rank-n second coordinate, followed by the original inclusion. -/
public theorem finiteFreeRowZeroComponentFunctor_comp_inclusion
    (R : Type uRowWholeFunctorValue) [Ring R] (n : ℕ) :
    finiteFreeRowZeroComponentFunctor R n ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι =
      ((finiteFreeRowCoreModelFunctor R n).prod'
        ((Functor.const _).obj
          (⟨(Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n⟩ :
            Core (FGProjectiveCat.IdempotentModel R)))) ⋙
        SInverseS.corePairInclusion :=
  finiteFreeRowZeroComponentFunctorCompInclusionComputed R n

end AlgebraicKTheory.StableGL

end
