/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeScalarMap
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowScalarSuccessor
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowGroupCompletion
public import MathlibExt.CategoryTheory.Monoidal.SInverseSStabilizationTransport
public import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Intrinsic scalar naturality of the original telescope-to-row functor

The original row automorphisms and rank-one regular arrows are sent through
the actual additive scalar-extension functor. Tensor coordinates intertwine
the automorphisms; their actual biproduct and braiding square transports the
regular arrows in the original stabilizer quotient. Mathlib's sequence
constructor gives every rank transition, and the original Grothendieck map
formula then gives every telescope arrow.

All component isomorphisms use the same finite row scalar coordinates and
only the proved original object-equality transports. No chosen Q/plus
comparison or expected naturality witness defines this isomorphism.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe uR uS uA uD vD uC vC

namespace AlgebraicKTheory.StableGL

private theorem transportSquare
    {C : Type uC} [Category.{vC} C] {A B A' B' X Y X' Y' : C}
    (p : A ≅ X) (q : B ≅ Y) (p' : A' ≅ X') (q' : B' ≅ Y')
    (u : X ≅ X') (v : Y ≅ Y') (a : A ⟶ B) (b : A' ⟶ B')
    (h : (p.inv ≫ a ≫ q.hom) ≫ v.hom =
      u.hom ≫ (p'.inv ≫ b ≫ q'.hom)) :
    a ≫ (q ≪≫ v ≪≫ q'.symm).hom =
      (p ≪≫ u ≪≫ p'.symm).hom ≫ b := by
  apply (cancel_epi p.inv).1
  apply (cancel_mono q'.hom).1
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

private theorem nestedIsoHom
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : E ≅ F) (e : F ≅ G) :
    (a ≪≫ ((b ≪≫ c ≪≫ d) ≪≫ e)).hom =
      a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ e.hom := by
  simp only [Iso.trans_hom, Category.assoc]

private theorem eqToHomCycle
    {C : Type uC} [Category.{vC} C] {A B D : C}
    (a : A = B) (b : B = D) (c : D = A) :
    eqToHom a ≫ eqToHom b ≫ eqToHom c = 𝟙 A :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k : A ⟶ D => k ≫ eqToHom c) (eqToHom_trans a b)).trans
      ((eqToHom_trans (a.trans b) c).trans (eqToHom_refl A ((a.trans b).trans c))))

private theorem eqToHomCycleSandwich
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (a : A = B) (b : B = D) (c : D = A)
    (d : E = F) (e : F = G) (g : G = E) (f : A ⟶ E) :
    eqToHom a ≫ (eqToHom b ≫ eqToHom c ≫ f ≫ eqToHom d ≫ eqToHom e) ≫ eqToHom g = f := by
  have hSource := eqToHomCycle a b c
  have hTarget := eqToHomCycle d e g
  have hAssoc :
      eqToHom a ≫ (eqToHom b ≫ eqToHom c ≫ f ≫ eqToHom d ≫ eqToHom e) ≫ eqToHom g =
        ((eqToHom a ≫ eqToHom b ≫ eqToHom c) ≫ f) ≫
          (eqToHom d ≫ eqToHom e ≫ eqToHom g) := by
    simp only [Category.assoc]
  have hCancel :
      ((eqToHom a ≫ eqToHom b ≫ eqToHom c) ≫ f) ≫
          (eqToHom d ≫ eqToHom e ≫ eqToHom g) = f := by
    rw [hSource, hTarget]
    exact (congrArg (fun k : A ⟶ E => k ≫ 𝟙 E) (Category.id_comp f)).trans
      (Category.comp_id f)
  exact hAssoc.trans hCancel

private theorem normalizeMappedArrow
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    (a : X ⟶ Y) :
    eqToHom (congrArg F.obj hx).symm ≫ F.map a ≫ eqToHom (congrArg F.obj hy) =
      F.map (eqToHom hx.symm ≫ a ≫ eqToHom hy) := by
  simp only [Functor.map_comp, eqToHom_map]

private theorem pairMapRaw
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    [HasZeroObject D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {X Y : SInverseS.Pair C}
    (a : SInverseS.RawHom X Y) :
    (SInverseS.pairFunctor F).map (SInverseS.Hom.mk a) =
      SInverseS.Hom.mk (SInverseS.mapRawHom F a) :=
  ((SInverseS.pairFunctor_characteristic F F (Iso.refl F) (𝟭 D)).2.1 a)

private abbrev rowFree (A : Type uA) [Ring A] (n : ℕ) :
    FGProjectiveCat.IdempotentModel A :=
  (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks A)).obj n

private abbrev originalSuccessorRaw (A : Type uA) [Ring A] (n : ℕ) :
    SInverseS.RawHom (⟨rowFree A n, rowFree A n⟩ :
      SInverseS.Pair (FGProjectiveCat.IdempotentModel A))
      ⟨rowFree A (n + 1), rowFree A (n + 1)⟩ where
  stabilizer := (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks A)).obj (1 : ℕ)
  hom₁ := biprod.braiding (rowFree A 1) (rowFree A n) ≪≫
    (FGProjectiveCat.IdempotentModel.freeBiprodIso A n 1).symm
  hom₂ := biprod.braiding (rowFree A 1) (rowFree A n) ≪≫
    (FGProjectiveCat.IdempotentModel.freeBiprodIso A n 1).symm

section Index

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

private def rowIndex (A : Type uA) [Ring A]
    (F : FGProjectiveCat.IdempotentModel A ⥤ D) [F.Additive] :
    ℕ ⥤ SInverseS.Pair D where
  obj n := (SInverseS.pairFunctor F).obj
    ((finiteFreeRowZeroComponentFunctor A n).obj (SingleObj.star _)).obj
  map {n m} a := (SInverseS.pairFunctor F).map
    (finiteFreeRowTransitionArrow A a).hom
  map_id n := by
    rw [finiteFreeRowTransitionArrow_id]
    change (SInverseS.pairFunctor F).map (𝟙 _) = 𝟙 _
    exact (SInverseS.pairFunctor F).map_id _
  map_comp a b := by
    rw [finiteFreeRowTransitionArrow_comp]
    change (SInverseS.pairFunctor F).map
      ((finiteFreeRowTransitionArrow A a).hom ≫
        (finiteFreeRowTransitionArrow A b).hom) = _
    exact (SInverseS.pairFunctor F).map_comp _ _

private theorem rowIndexObjEq (A : Type uA) [Ring A]
    (F : FGProjectiveCat.IdempotentModel A ⥤ D) [F.Additive] (n : ℕ) :
    (rowIndex A F).obj n =
      (⟨F.obj (rowFree A n), F.obj (rowFree A n)⟩ : SInverseS.Pair D) :=
  congrArg (SInverseS.pairFunctor F).obj
    (finiteFreeRowZeroComponentFunctor_obj A n (SingleObj.star _))

private def rowIndexAction (A : Type uA) [Ring A]
    (F : FGProjectiveCat.IdempotentModel A ⥤ D) [F.Additive] (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ) :
    (rowIndex A F).obj n ⟶ (rowIndex A F).obj n :=
  (SInverseS.pairFunctor F).map
    ((finiteFreeRowZeroComponentFunctor A n).map
      (X := SingleObj.star _) (Y := SingleObj.star _) g).hom

private theorem rowIndexSuccessorNormalized (A : Type uA) [Ring A]
    (F : FGProjectiveCat.IdempotentModel A ⥤ D) [F.Additive] (n : ℕ) :
    eqToHom (rowIndexObjEq A F n).symm ≫
        (rowIndex A F).map (homOfLE (Nat.le_succ n)) ≫
        eqToHom (rowIndexObjEq A F (n + 1)) =
      SInverseS.Hom.mk (SInverseS.mapRawHom F (originalSuccessorRaw A n)) := by
  change eqToHom (rowIndexObjEq A F n).symm ≫
      (SInverseS.pairFunctor F).map
        (finiteFreeRowTransitionArrow A (homOfLE (Nat.le_succ n))).hom ≫
      eqToHom (rowIndexObjEq A F (n + 1)) = _
  rw [finiteFreeRowTransitionArrow_succ]
  let J := SInverseS.pairFunctor F
  let hX := finiteFreeRowZeroComponentFunctor_obj A n (SingleObj.star _)
  let hY := finiteFreeRowZeroComponentFunctor_obj A (n + 1) (SingleObj.star _)
  let q := eqToHom hX.symm ≫ (finiteFreeRowSuccessorArrow A n).hom ≫ eqToHom hY
  have h0 :
      eqToHom (rowIndexObjEq A F n).symm ≫ J.map (finiteFreeRowSuccessorArrow A n).hom ≫
          eqToHom (rowIndexObjEq A F (n + 1)) = J.map q :=
    normalizeMappedArrow J hX hY (finiteFreeRowSuccessorArrow A n).hom
  have h1 : J.map q = J.map (SInverseS.Hom.mk (originalSuccessorRaw A n)) :=
    congrArg
      (fun k : (⟨rowFree A n, rowFree A n⟩ : SInverseS.Pair (FGProjectiveCat.IdempotentModel A)) ⟶
          (⟨rowFree A (n + 1), rowFree A (n + 1)⟩ :
            SInverseS.Pair (FGProjectiveCat.IdempotentModel A)) => J.map k)
      (finiteFreeRowSuccessorArrow_hom_eq_raw A n)
  have h2 : J.map (SInverseS.Hom.mk (originalSuccessorRaw A n)) =
      SInverseS.Hom.mk (SInverseS.mapRawHom F (originalSuccessorRaw A n)) :=
    pairMapRaw F (originalSuccessorRaw A n)
  exact h0.trans (h1.trans h2)

private theorem rowIndexActionNormalized (A : Type uA) [Ring A]
    (F : FGProjectiveCat.IdempotentModel A ⥤ D) [F.Additive] (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ) :
    let p : Core (FGProjectiveCat.IdempotentModel A) := ⟨rowFree A n⟩
    let k : ((p, p) : Core (FGProjectiveCat.IdempotentModel A) ×
        Core (FGProjectiveCat.IdempotentModel A)) ⟶ (p, p) :=
      ((⟨FGProjectiveCat.IdempotentModel.freeAut A n g⟩ : p ⟶ p), 𝟙 p)
    eqToHom (rowIndexObjEq A F n).symm ≫
        (SInverseS.pairFunctor F).map
          ((finiteFreeRowZeroComponentFunctor A n).map
            (X := SingleObj.star _) (Y := SingleObj.star _) g).hom ≫
        eqToHom (rowIndexObjEq A F n) =
      (SInverseS.corePairInclusion (C := D)).map
        (X := (F.core.obj p, F.core.obj p)) (Y := (F.core.obj p, F.core.obj p))
        ((F.core.prod F.core).map (X := (p, p)) (Y := (p, p)) k) := by
  dsimp only
  let p : Core (FGProjectiveCat.IdempotentModel A) := ⟨rowFree A n⟩
  let k : ((p, p) : Core (FGProjectiveCat.IdempotentModel A) ×
      Core (FGProjectiveCat.IdempotentModel A)) ⟶ (p, p) :=
    ((⟨FGProjectiveCat.IdempotentModel.freeAut A n g⟩ : p ⟶ p), 𝟙 p)
  let J := SInverseS.pairFunctor F
  let I := SInverseS.corePairInclusion (C := FGProjectiveCat.IdempotentModel A)
  let K := SInverseS.corePairInclusion (C := D)
  let h := finiteFreeRowZeroComponentFunctor_obj A n (SingleObj.star _)
  let q := eqToHom h.symm ≫
    ((finiteFreeRowZeroComponentFunctor A n).map
      (X := SingleObj.star _) (Y := SingleObj.star _) g).hom ≫ eqToHom h
  have h0 :
      eqToHom (rowIndexObjEq A F n).symm ≫
          J.map ((finiteFreeRowZeroComponentFunctor A n).map
            (X := SingleObj.star _) (Y := SingleObj.star _) g).hom ≫
          eqToHom (rowIndexObjEq A F n) = J.map q :=
    normalizeMappedArrow J h h _
  have h1 : J.map q = J.map (I.map (X := (p, p)) (Y := (p, p)) k) :=
    congrArg
      (fun a : (⟨rowFree A n, rowFree A n⟩ :
          SInverseS.Pair (FGProjectiveCat.IdempotentModel A)) ⟶
          (⟨rowFree A n, rowFree A n⟩ :
            SInverseS.Pair (FGProjectiveCat.IdempotentModel A)) => J.map a)
      (finiteFreeRowZeroComponentFunctor_map A n g)
  have h2 : J.map (I.map (X := (p, p)) (Y := (p, p)) k) =
      K.map (X := (F.core.obj p, F.core.obj p)) (Y := (F.core.obj p, F.core.obj p))
        ((F.core.prod F.core).map (X := (p, p)) (Y := (p, p)) k) :=
    (SInverseS.coreTranslation_characteristic F).1 k
  exact h0.trans (h1.trans h2)

end Index

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private abbrev sourceRowFunctor (f : R →+* S) :=
  (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
    FGProjectiveCat.scalarExtension.{uR, uS, uR} f

private abbrev targetRowFunctor.{uTargetPrivate, uCarrierPrivate}
    (S : Type uTargetPrivate) [Ring S] :
    FGProjectiveCat.IdempotentModel S ⥤ FGProjectiveCat.{max uTargetPrivate uCarrierPrivate} S :=
  (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
    (FGProjectiveCat.universeEquivalence.{uTargetPrivate, uCarrierPrivate} S).inverse

private def diagonalScalarIso (f : R →+* S) (n : ℕ) :
    (⟨(sourceRowFunctor f).obj (rowFree R n),
        (sourceRowFunctor f).obj (rowFree R n)⟩ :
      SInverseS.Pair (FGProjectiveCat.{max uS uR} S)) ≅
      ⟨(targetRowFunctor.{uS, uR} S).obj (rowFree S n),
        (targetRowFunctor.{uS, uR} S).obj (rowFree S n)⟩ :=
  (SInverseS.corePairInclusion (C := FGProjectiveCat.{max uS uR} S)).mapIso
    ((Core.isoMk
      (x := ⟨(sourceRowFunctor f).obj (rowFree R n)⟩)
      (y := ⟨(targetRowFunctor.{uS, uR} S).obj (rowFree S n)⟩)
      (finiteFreeRowScalarIso f n)).prod
      (Core.isoMk
        (x := ⟨(sourceRowFunctor f).obj (rowFree R n)⟩)
        (y := ⟨(targetRowFunctor.{uS, uR} S).obj (rowFree S n)⟩)
        (finiteFreeRowScalarIso f n)))

private theorem diagonalScalarIso_recipe (f : R →+* S) (n : ℕ) :
    diagonalScalarIso f n =
      (SInverseS.corePairInclusion (C := FGProjectiveCat.{max uS uR} S)).mapIso
        ((Core.isoMk
          (x := ⟨(sourceRowFunctor f).obj (rowFree R n)⟩)
          (y := ⟨(targetRowFunctor.{uS, uR} S).obj (rowFree S n)⟩)
          (finiteFreeRowScalarIso f n)).prod
          (Core.isoMk
            (x := ⟨(sourceRowFunctor f).obj (rowFree R n)⟩)
            (y := ⟨(targetRowFunctor.{uS, uR} S).obj (rowFree S n)⟩)
            (finiteFreeRowScalarIso f n))) := rfl

private def indexScalarIso (f : R →+* S) (n : ℕ) :
    (rowIndex R (sourceRowFunctor f)).obj n ≅
      (rowIndex S (targetRowFunctor.{uS, uR} S)).obj n :=
  eqToIso (rowIndexObjEq R (sourceRowFunctor f) n) ≪≫
    diagonalScalarIso f n ≪≫
      (eqToIso (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) n)).symm

private theorem indexScalarIso_recipe (f : R →+* S) (n : ℕ) :
    indexScalarIso f n =
      eqToIso (rowIndexObjEq R (sourceRowFunctor f) n) ≪≫ diagonalScalarIso f n ≪≫
        (eqToIso (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) n)).symm := rfl

private theorem scalarSuccessorSquare (f : R →+* S) (n : ℕ) :
    (rowIndex R (sourceRowFunctor f)).map (homOfLE (Nat.le_succ n)) ≫
        (indexScalarIso f (n + 1)).hom =
      (indexScalarIso f n).hom ≫
        (rowIndex S (targetRowFunctor.{uS, uR} S)).map (homOfLE (Nat.le_succ n)) := by
  let FR := sourceRowFunctor f
  let FS := targetRowFunctor.{uS, uR} S
  let : PreservesBinaryBiproduct (rowFree R 1) (rowFree R n) FR :=
    preservesBinaryBiproduct_of_preservesBiproduct FR _ _
  let : PreservesBinaryBiproduct (rowFree S 1) (rowFree S n) FS :=
    preservesBinaryBiproduct_of_preservesBiproduct FS _ _
  let a := (FR.mapBiprod (rowFree R 1) (rowFree R n)).symm ≪≫
    FR.mapIso (biprod.braiding (rowFree R 1) (rowFree R n) ≪≫
      (FGProjectiveCat.IdempotentModel.freeBiprodIso R n 1).symm)
  let b := (FS.mapBiprod (rowFree S 1) (rowFree S n)).symm ≪≫
    FS.mapIso (biprod.braiding (rowFree S 1) (rowFree S n) ≪≫
      (FGProjectiveCat.IdempotentModel.freeBiprodIso S n 1).symm)
  have hCoordinates : a ≪≫ finiteFreeRowScalarIso f (n + 1) =
      biprod.mapIso (finiteFreeRowScalarIso f 1) (finiteFreeRowScalarIso f n) ≪≫ b := by
    simpa only [a, b, FR, FS, rowFree, sourceRowFunctor, targetRowFunctor,
      Iso.trans_assoc] using finiteFreeRowScalarIso_successor_coordinates f n
  have hRaw :
      SInverseS.Hom.mk (SInverseS.mapRawHom FR (originalSuccessorRaw R n)) ≫
          (diagonalScalarIso f (n + 1)).hom =
        (diagonalScalarIso f n).hom ≫
          SInverseS.Hom.mk (SInverseS.mapRawHom FS (originalSuccessorRaw S n)) := by
    change SInverseS.Hom.mk (⟨FR.obj (rowFree R 1), a, a⟩ :
          SInverseS.RawHom
            (⟨FR.obj (rowFree R n), FR.obj (rowFree R n)⟩ : SInverseS.Pair _)
            ⟨FR.obj (rowFree R (n + 1)), FR.obj (rowFree R (n + 1))⟩) ≫
        (diagonalScalarIso f (n + 1)).hom =
      (diagonalScalarIso f n).hom ≫
        SInverseS.Hom.mk (⟨FS.obj (rowFree S 1), b, b⟩ :
          SInverseS.RawHom
            (⟨FS.obj (rowFree S n), FS.obj (rowFree S n)⟩ : SInverseS.Pair _)
            ⟨FS.obj (rowFree S (n + 1)), FS.obj (rowFree S (n + 1))⟩)
    exact SInverseS.diagonalStabilization_transport a b
      (finiteFreeRowScalarIso f 1) (finiteFreeRowScalarIso f n)
      (finiteFreeRowScalarIso f (n + 1)) hCoordinates
  have hNormalized :
      (eqToHom (rowIndexObjEq R FR n).symm ≫
          (rowIndex R FR).map (homOfLE (Nat.le_succ n)) ≫
          eqToHom (rowIndexObjEq R FR (n + 1))) ≫
        (diagonalScalarIso f (n + 1)).hom =
      (diagonalScalarIso f n).hom ≫
        (eqToHom (rowIndexObjEq S FS n).symm ≫
          (rowIndex S FS).map (homOfLE (Nat.le_succ n)) ≫
          eqToHom (rowIndexObjEq S FS (n + 1))) := by
    rw [rowIndexSuccessorNormalized, rowIndexSuccessorNormalized]
    exact hRaw
  exact transportSquare
    (eqToIso (rowIndexObjEq R FR n)) (eqToIso (rowIndexObjEq R FR (n + 1)))
    (eqToIso (rowIndexObjEq S FS n)) (eqToIso (rowIndexObjEq S FS (n + 1)))
    (diagonalScalarIso f n) (diagonalScalarIso f (n + 1)) _ _ hNormalized

private def indexScalarNatIso (f : R →+* S) :
    rowIndex R (sourceRowFunctor f) ≅
      rowIndex S (targetRowFunctor.{uS, uR} S) :=
  NatIso.ofComponents (indexScalarIso f) (by
    intro n m a
    exact (NatTrans.ofSequence (fun n => (indexScalarIso f n).hom)
      (scalarSuccessorSquare f)).naturality a)

private theorem scalarActionSquare (f : R →+* S) (n : ℕ)
    (g : (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ) :
    (SInverseS.pairFunctor (sourceRowFunctor f)).map
        ((finiteFreeRowZeroComponentFunctor R n).map
          (X := SingleObj.star _) (Y := SingleObj.star _) g).hom ≫
      (indexScalarIso f n).hom =
    (indexScalarIso f n).hom ≫
      (SInverseS.pairFunctor (targetRowFunctor.{uS, uR} S)).map
        ((finiteFreeRowZeroComponentFunctor S n).map
          (X := SingleObj.star _) (Y := SingleObj.star _)
          (MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f (MulOpposite.unop g)))).hom := by
  let FR := sourceRowFunctor f
  let FS := targetRowFunctor.{uS, uR} S
  let gS := MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f (MulOpposite.unop g))
  let pR : Core (FGProjectiveCat.IdempotentModel R) := ⟨rowFree R n⟩
  let pS : Core (FGProjectiveCat.IdempotentModel S) := ⟨rowFree S n⟩
  let dR : ((FR.core.obj pR, FR.core.obj pR) :
      Core (FGProjectiveCat.{max uS uR} S) × Core (FGProjectiveCat.{max uS uR} S)) ⟶
      (FR.core.obj pR, FR.core.obj pR) :=
    (FR.core.prod FR.core).map (X := (pR, pR)) (Y := (pR, pR))
      ((⟨FGProjectiveCat.IdempotentModel.freeAut R n g⟩ : pR ⟶ pR), 𝟙 pR)
  let dS : ((FS.core.obj pS, FS.core.obj pS) :
      Core (FGProjectiveCat.{max uS uR} S) × Core (FGProjectiveCat.{max uS uR} S)) ⟶
      (FS.core.obj pS, FS.core.obj pS) :=
    (FS.core.prod FS.core).map (X := (pS, pS)) (Y := (pS, pS))
      ((⟨FGProjectiveCat.IdempotentModel.freeAut S n gS⟩ : pS ⟶ pS), 𝟙 pS)
  let e := (Core.isoMk
      (x := ⟨FR.obj (rowFree R n)⟩) (y := ⟨FS.obj (rowFree S n)⟩)
      (finiteFreeRowScalarIso f n)).prod
    (Core.isoMk
      (x := ⟨FR.obj (rowFree R n)⟩) (y := ⟨FS.obj (rowFree S n)⟩)
      (finiteFreeRowScalarIso f n))
  have hCore : dR ≫ e.hom = e.hom ≫ dS := by
    apply Prod.ext
    · apply Core.hom_ext
      change FR.map (FGProjectiveCat.IdempotentModel.freeAut R n g).hom ≫
          (finiteFreeRowScalarIso f n).hom =
        (finiteFreeRowScalarIso f n).hom ≫
          FS.map (FGProjectiveCat.IdempotentModel.freeAut S n gS).hom
      simpa only [MulOpposite.op_unop] using
        finiteFreeRowScalarIso_naturality f n (MulOpposite.unop g)
    · apply Core.hom_ext
      change FR.map (𝟙 (rowFree R n)) ≫ (finiteFreeRowScalarIso f n).hom =
        (finiteFreeRowScalarIso f n).hom ≫ FS.map (𝟙 (rowFree S n))
      have hR := congrArg
        (fun k : FR.obj (rowFree R n) ⟶ FR.obj (rowFree R n) =>
          k ≫ (finiteFreeRowScalarIso f n).hom) (FR.map_id (rowFree R n))
      have hS := congrArg
        (fun k : FS.obj (rowFree S n) ⟶ FS.obj (rowFree S n) =>
          (finiteFreeRowScalarIso f n).hom ≫ k) (FS.map_id (rowFree S n))
      exact hR.trans ((Category.id_comp _).trans
        ((Category.comp_id _).symm.trans hS.symm))
  let J := SInverseS.corePairInclusion (C := FGProjectiveCat.{max uS uR} S)
  have hPair : J.map dR ≫ (diagonalScalarIso f n).hom =
      (diagonalScalarIso f n).hom ≫ J.map dS := by
    have hIso : (diagonalScalarIso f n).hom = J.map e.hom :=
      (congrArg Iso.hom (diagonalScalarIso_recipe f n)).trans (Functor.mapIso_hom J e)
    have hMap := (J.map_comp dR e.hom).symm.trans
      ((congrArg
        (fun k : ((FR.core.obj pR, FR.core.obj pR) :
            Core (FGProjectiveCat.{max uS uR} S) × Core (FGProjectiveCat.{max uS uR} S)) ⟶
            (FS.core.obj pS, FS.core.obj pS) => J.map k) hCore).trans
        (J.map_comp e.hom dS))
    have hLeft := congrArg
      (fun k : (⟨FR.obj (rowFree R n), FR.obj (rowFree R n)⟩ : SInverseS.Pair _) ⟶
          (⟨FS.obj (rowFree S n), FS.obj (rowFree S n)⟩ : SInverseS.Pair _) => J.map dR ≫ k) hIso
    have hRight := congrArg
      (fun k : (⟨FR.obj (rowFree R n), FR.obj (rowFree R n)⟩ : SInverseS.Pair _) ⟶
          (⟨FS.obj (rowFree S n), FS.obj (rowFree S n)⟩ : SInverseS.Pair _) => k ≫ J.map dS) hIso
    exact hLeft.trans (hMap.trans hRight.symm)
  have hNormalized :
      (eqToHom (rowIndexObjEq R FR n).symm ≫
          (SInverseS.pairFunctor FR).map
            ((finiteFreeRowZeroComponentFunctor R n).map
              (X := SingleObj.star _) (Y := SingleObj.star _) g).hom ≫
          eqToHom (rowIndexObjEq R FR n)) ≫
        (diagonalScalarIso f n).hom =
      (diagonalScalarIso f n).hom ≫
        (eqToHom (rowIndexObjEq S FS n).symm ≫
          (SInverseS.pairFunctor FS).map
            ((finiteFreeRowZeroComponentFunctor S n).map
              (X := SingleObj.star _) (Y := SingleObj.star _) gS).hom ≫
          eqToHom (rowIndexObjEq S FS n)) := by
    rw [rowIndexActionNormalized, rowIndexActionNormalized]
    exact hPair
  exact transportSquare
    (eqToIso (rowIndexObjEq R FR n)) (eqToIso (rowIndexObjEq R FR n))
    (eqToIso (rowIndexObjEq S FS n)) (eqToIso (rowIndexObjEq S FS n))
    (diagonalScalarIso f n) (diagonalScalarIso f n) _ _ hNormalized

section Telescope

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]

private abbrev rowPairTarget (A : Type uA) [Ring A]
    (F : FGProjectiveCat.IdempotentModel A ⥤ D) [F.Additive] :=
  (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel A)).ι ⋙
    SInverseS.pairFunctor F

private abbrev telescopePairFunctor (A : Type uA) [Ring A]
    (F : FGProjectiveCat.IdempotentModel A ⥤ D) [F.Additive] :=
  finiteBGLTelescopeToRowZeroComponent A ⋙ rowPairTarget A F

private theorem finiteStageSubsingleton (A : Type uA) [Ring A] (n : ℕ) :
    Subsingleton ((finiteClassifyingCategoryDiagram A).obj n) := by
  rw [finiteClassifyingCategoryDiagram_obj]
  change Subsingleton (SingleObj (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ)
  change Subsingleton Unit
  infer_instance

private theorem telescopeZeroStageEq (A : Type uA) [Ring A]
    (X : FiniteBGLTelescopeCategory A) :
    (finiteBGLTelescopeToRowZeroComponent A).obj X =
      (finiteFreeRowZeroComponentFunctor A X.base).obj (SingleObj.star _) :=
  (finiteBGLTelescopeToRowZeroComponent_obj A X).trans
    (congrArg (finiteFreeRowZeroComponentFunctor A X.base).obj
      (@Subsingleton.elim ((finiteClassifyingCategoryDiagram A).obj X.base)
        (finiteStageSubsingleton A X.base) X.fiber (SingleObj.star _)))

private theorem telescopeStageEq (A : Type uA) [Ring A]
    (F : FGProjectiveCat.IdempotentModel A ⥤ D) [F.Additive]
    (X : FiniteBGLTelescopeCategory A) :
    (telescopePairFunctor A F).obj X = (rowIndex A F).obj X.base :=
  congrArg (rowPairTarget A F).obj (telescopeZeroStageEq A X)

private def telescopeMapNormalValue (A : Type uA) [Ring A]
    (F : FGProjectiveCat.IdempotentModel A ⥤ D) [F.Additive]
    {X Y : FiniteBGLTelescopeCategory A} (a : X ⟶ Y) :
    (rowIndex A F).obj X.base ⟶ (rowIndex A F).obj Y.base :=
  (rowIndex A F).map a.base ≫ rowIndexAction A F Y.base
    (show (Matrix.GeneralLinearGroup (Fin Y.base) A)ᵐᵒᵖ from a.fiber)

private theorem telescopeMapNormalized (A : Type uA) [Ring A]
    (F : FGProjectiveCat.IdempotentModel A ⥤ D) [F.Additive]
    {X Y : FiniteBGLTelescopeCategory A} (a : X ⟶ Y) :
    eqToHom (telescopeStageEq A F X).symm ≫
        (telescopePairFunctor A F).map a ≫ eqToHom (telescopeStageEq A F Y) =
      telescopeMapNormalValue A F a := by
  have hZero :
      eqToHom (telescopeZeroStageEq A X).symm ≫
          (finiteBGLTelescopeToRowZeroComponent A).map a ≫
          eqToHom (telescopeZeroStageEq A Y) =
        finiteFreeRowTransitionArrow A a.base ≫
          (finiteFreeRowZeroComponentFunctor A Y.base).map
            (X := SingleObj.star _) (Y := SingleObj.star _)
            (show (Matrix.GeneralLinearGroup (Fin Y.base) A)ᵐᵒᵖ from a.fiber) := by
    rcases X with ⟨n, x⟩
    rcases Y with ⟨m, y⟩
    cases x
    cases y
    let p := SingleObj.star (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ
    let u := (finiteFreeRowZeroComponentFunctor A m).map
      (X := SingleObj.star _) (Y := SingleObj.star _)
      (show (Matrix.GeneralLinearGroup (Fin m) A)ᵐᵒᵖ from a.fiber)
    have hPoint : (finiteFreeRowTransitionNatTrans A a.base).app p =
        finiteFreeRowTransitionArrow A a.base :=
      finiteFreeRowTransitionNatTrans_app_star A a.base
    have hPointComp : (finiteFreeRowTransitionNatTrans A a.base).app p ≫ u =
        finiteFreeRowTransitionArrow A a.base ≫ u :=
      congrArg
        (fun q : (finiteFreeRowZeroComponentFunctor A n).obj (SingleObj.star _) ⟶
            (finiteFreeRowZeroComponentFunctor A m).obj (SingleObj.star _) => q ≫ u) hPoint
    have hMap :
        eqToHom (telescopeZeroStageEq A ⟨n, p⟩).symm ≫
            (finiteBGLTelescopeToRowZeroComponent A).map a ≫
            eqToHom (telescopeZeroStageEq A
              ⟨m, SingleObj.star (Matrix.GeneralLinearGroup (Fin m) A)ᵐᵒᵖ⟩) =
          (finiteFreeRowTransitionNatTrans A a.base).app p ≫ u :=
      finiteBGLTelescopeToRowZeroComponent_map_after_obj A a
    exact hMap.trans hPointComp
  let J := rowPairTarget A F
  let b := finiteFreeRowTransitionArrow A a.base
  let u := (finiteFreeRowZeroComponentFunctor A Y.base).map
    (X := SingleObj.star _) (Y := SingleObj.star _)
    (show (Matrix.GeneralLinearGroup (Fin Y.base) A)ᵐᵒᵖ from a.fiber)
  let q := eqToHom (telescopeZeroStageEq A X).symm ≫
    (finiteBGLTelescopeToRowZeroComponent A).map a ≫ eqToHom (telescopeZeroStageEq A Y)
  have h0 :
      eqToHom (telescopeStageEq A F X).symm ≫
          (telescopePairFunctor A F).map a ≫ eqToHom (telescopeStageEq A F Y) = J.map q :=
    normalizeMappedArrow J (telescopeZeroStageEq A X) (telescopeZeroStageEq A Y)
      ((finiteBGLTelescopeToRowZeroComponent A).map a)
  have h1 : J.map q = J.map (b ≫ u) :=
    congrArg
      (fun k : (finiteFreeRowZeroComponentFunctor A X.base).obj (SingleObj.star _) ⟶
          (finiteFreeRowZeroComponentFunctor A Y.base).obj (SingleObj.star _) => J.map k) hZero
  have h2 : J.map (b ≫ u) = telescopeMapNormalValue A F a :=
    J.map_comp b u
  exact h0.trans (h1.trans h2)

end Telescope

private abbrev sourceTelescopePairFunctor (f : R →+* S) :=
  telescopePairFunctor R (sourceRowFunctor f)

private abbrev targetTelescopePairFunctor (f : R →+* S) :=
  finiteBGLTelescopeScalarFunctor f ⋙
    telescopePairFunctor S (targetRowFunctor.{uS, uR} S)

private theorem targetTelescopePairFunctor_map (f : R →+* S)
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    (targetTelescopePairFunctor f).map a =
      (telescopePairFunctor S (targetRowFunctor.{uS, uR} S)).map
        ((finiteBGLTelescopeScalarFunctor f).map a) := rfl

private theorem targetTelescopeMapNormalValue (f : R →+* S)
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    telescopeMapNormalValue S (targetRowFunctor.{uS, uR} S)
        ((finiteBGLTelescopeScalarFunctor f).map a) =
      (rowIndex S (targetRowFunctor.{uS, uR} S)).map a.base ≫
        rowIndexAction S (targetRowFunctor.{uS, uR} S) Y.base
          (MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f
            (MulOpposite.unop
              (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber)))) := by
  let FS := targetRowFunctor.{uS, uR} S
  let gS : (Matrix.GeneralLinearGroup (Fin Y.base) S)ᵐᵒᵖ :=
    ((finiteBGLTelescopeScalarFunctor f).map a).fiber
  have h0 : telescopeMapNormalValue S FS ((finiteBGLTelescopeScalarFunctor f).map a) =
      (rowIndex S FS).map a.base ≫ rowIndexAction S FS Y.base gS := rfl
  have h1 : gS = MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f
      (MulOpposite.unop (show (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ from a.fiber))) :=
    finiteBGLTelescopeScalarFunctor_map_fiber f a
  exact h0.trans (congrArg
    (fun q : (Matrix.GeneralLinearGroup (Fin Y.base) S)ᵐᵒᵖ =>
      (rowIndex S FS).map a.base ≫ rowIndexAction S FS Y.base q) h1)

private def telescopeScalarComponent (f : R →+* S) (X : FiniteBGLTelescopeCategory R) :
    (sourceTelescopePairFunctor f).obj X ≅ (targetTelescopePairFunctor f).obj X :=
  eqToIso (telescopeStageEq R (sourceRowFunctor f) X) ≪≫ indexScalarIso f X.base ≪≫
    (eqToIso (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
      ((finiteBGLTelescopeScalarFunctor f).obj X))).symm

private theorem telescopeScalarComponent_recipe (f : R →+* S)
    (X : FiniteBGLTelescopeCategory R) :
    telescopeScalarComponent f X =
      eqToIso (telescopeStageEq R (sourceRowFunctor f) X) ≪≫ indexScalarIso f X.base ≪≫
        (eqToIso (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
          ((finiteBGLTelescopeScalarFunctor f).obj X))).symm := rfl

private theorem telescopeScalarComponent_hom_formula (f : R →+* S)
    (X : FiniteBGLTelescopeCategory R) :
    (telescopeScalarComponent f X).hom =
      eqToHom (telescopeStageEq R (sourceRowFunctor f) X) ≫
        eqToHom (rowIndexObjEq R (sourceRowFunctor f) X.base) ≫
        (diagonalScalarIso f X.base).hom ≫
        eqToHom (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) X.base).symm ≫
        eqToHom (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
          ((finiteBGLTelescopeScalarFunctor f).obj X)).symm := by
  let a := eqToIso (telescopeStageEq R (sourceRowFunctor f) X)
  let b := eqToIso (rowIndexObjEq R (sourceRowFunctor f) X.base)
  let c := diagonalScalarIso f X.base
  let d := (eqToIso (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) X.base)).symm
  let e := (eqToIso (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
    ((finiteBGLTelescopeScalarFunctor f).obj X))).symm
  have hRecipe : telescopeScalarComponent f X = a ≪≫ ((b ≪≫ c ≪≫ d) ≪≫ e) :=
    (telescopeScalarComponent_recipe f X).trans
      (congrArg
        (fun q : (rowIndex R (sourceRowFunctor f)).obj X.base ≅
            (rowIndex S (targetRowFunctor.{uS, uR} S)).obj X.base => a ≪≫ q ≪≫ e)
        (indexScalarIso_recipe f X.base))
  have hHom : (telescopeScalarComponent f X).hom = a.hom ≫ b.hom ≫ c.hom ≫ d.hom ≫ e.hom :=
    (congrArg Iso.hom hRecipe).trans (nestedIsoHom a b c d e)
  have hA : a.hom = eqToHom (telescopeStageEq R (sourceRowFunctor f) X) :=
    eqToIso.hom (telescopeStageEq R (sourceRowFunctor f) X)
  have hB : b.hom = eqToHom (rowIndexObjEq R (sourceRowFunctor f) X.base) :=
    eqToIso.hom (rowIndexObjEq R (sourceRowFunctor f) X.base)
  have hD : d.hom =
      eqToHom (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) X.base).symm :=
    eqToIso.inv (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) X.base)
  have hE : e.hom = eqToHom (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
      ((finiteBGLTelescopeScalarFunctor f).obj X)).symm :=
    eqToIso.inv (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
      ((finiteBGLTelescopeScalarFunctor f).obj X))
  have hTail := congrArg₂ (fun q r => q ≫ r) hD hE
  have hMiddle := congrArg (fun q => c.hom ≫ q) hTail
  have hWhole := congrArg₂ (fun q r => q ≫ r) hA
    (congrArg₂ (fun q r => q ≫ r) hB hMiddle)
  exact hHom.trans hWhole

private theorem telescopeScalarNaturality (f : R →+* S)
    {X Y : FiniteBGLTelescopeCategory R} (a : X ⟶ Y) :
    (sourceTelescopePairFunctor f).map a ≫ (telescopeScalarComponent f Y).hom =
      (telescopeScalarComponent f X).hom ≫ (targetTelescopePairFunctor f).map a := by
  let FR := sourceRowFunctor f
  let FS := targetRowFunctor.{uS, uR} S
  let g : (Matrix.GeneralLinearGroup (Fin Y.base) R)ᵐᵒᵖ := a.fiber
  let gS := MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f (MulOpposite.unop g))
  let ar : (rowIndex R FR).obj Y.base ⟶ (rowIndex R FR).obj Y.base :=
    rowIndexAction R FR Y.base g
  let bs : (rowIndex S FS).obj Y.base ⟶ (rowIndex S FS).obj Y.base :=
    rowIndexAction S FS Y.base gS
  have hR :
      eqToHom (telescopeStageEq R FR X).symm ≫
          (sourceTelescopePairFunctor f).map a ≫ eqToHom (telescopeStageEq R FR Y) =
        (rowIndex R FR).map a.base ≫ ar :=
    telescopeMapNormalized R FR a
  have hS :
      eqToHom (telescopeStageEq S FS ((finiteBGLTelescopeScalarFunctor f).obj X)).symm ≫
          (targetTelescopePairFunctor f).map a ≫
          eqToHom (telescopeStageEq S FS ((finiteBGLTelescopeScalarFunctor f).obj Y)) =
        (rowIndex S FS).map a.base ≫ bs := by
    have h0 := congrArg
      (fun k : (targetTelescopePairFunctor f).obj X ⟶ (targetTelescopePairFunctor f).obj Y =>
        eqToHom (telescopeStageEq S FS ((finiteBGLTelescopeScalarFunctor f).obj X)).symm ≫
          k ≫ eqToHom (telescopeStageEq S FS ((finiteBGLTelescopeScalarFunctor f).obj Y)))
      (targetTelescopePairFunctor_map f a)
    have h1 := telescopeMapNormalized S FS ((finiteBGLTelescopeScalarFunctor f).map a)
    have h2 := targetTelescopeMapNormalValue f a
    exact h0.trans (h1.trans h2)
  have hIndex : (rowIndex R FR).map a.base ≫ (indexScalarIso f Y.base).hom =
      (indexScalarIso f X.base).hom ≫ (rowIndex S FS).map a.base :=
    (indexScalarNatIso f).hom.naturality a.base
  have hFiber : ar ≫ (indexScalarIso f Y.base).hom =
      (indexScalarIso f Y.base).hom ≫ bs := scalarActionSquare f Y.base g
  have hNormalized :
      (eqToHom (telescopeStageEq R FR X).symm ≫
          (sourceTelescopePairFunctor f).map a ≫ eqToHom (telescopeStageEq R FR Y)) ≫
        (indexScalarIso f Y.base).hom =
      (indexScalarIso f X.base).hom ≫
        (eqToHom (telescopeStageEq S FS ((finiteBGLTelescopeScalarFunctor f).obj X)).symm ≫
          (targetTelescopePairFunctor f).map a ≫
          eqToHom (telescopeStageEq S FS ((finiteBGLTelescopeScalarFunctor f).obj Y))) := by
    have hLeft := congrArg
      (fun k : (rowIndex R FR).obj X.base ⟶ (rowIndex R FR).obj Y.base =>
        k ≫ (indexScalarIso f Y.base).hom) hR
    have hRight := congrArg
      (fun k : (rowIndex S FS).obj X.base ⟶ (rowIndex S FS).obj Y.base =>
        (indexScalarIso f X.base).hom ≫ k) hS
    have hMiddle : ((rowIndex R FR).map a.base ≫ ar) ≫ (indexScalarIso f Y.base).hom =
        (indexScalarIso f X.base).hom ≫ ((rowIndex S FS).map a.base ≫ bs) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun k : (rowIndex R FR).obj Y.base ⟶ (rowIndex S FS).obj Y.base =>
          (rowIndex R FR).map a.base ≫ k) hFiber).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k : (rowIndex R FR).obj X.base ⟶ (rowIndex S FS).obj Y.base =>
              k ≫ bs) hIndex).trans (Category.assoc _ _ _))))
    exact hLeft.trans (hMiddle.trans hRight.symm)
  exact transportSquare
    (eqToIso (telescopeStageEq R FR X)) (eqToIso (telescopeStageEq R FR Y))
    (eqToIso (telescopeStageEq S FS ((finiteBGLTelescopeScalarFunctor f).obj X)))
    (eqToIso (telescopeStageEq S FS ((finiteBGLTelescopeScalarFunctor f).obj Y)))
    (indexScalarIso f X.base) (indexScalarIso f Y.base) _ _ hNormalized

/-- The actual original telescope-to-row Pair functors commute up to their intrinsic
tensor/row isomorphism for every unital associative coefficient homomorphism. -/
public def finiteBGLTelescopeRowScalarPairIso (f : R →+* S) :
    finiteBGLTelescopeToRowZeroComponent R ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι ⋙
        SInverseS.pairFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{uR, uS, uR} f) ≅
      finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel S)).ι ⋙
        SInverseS.pairFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse) :=
  NatIso.ofComponents (telescopeScalarComponent f) (by
    intro X Y a
    exact telescopeScalarNaturality f a)

private theorem finiteBGLTelescopeRowScalarPairIso_app_recipe (f : R →+* S)
    (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeRowScalarPairIso f).app X = telescopeScalarComponent f X := by
  let e := NatIso.ofComponents
    (F := sourceTelescopePairFunctor f) (G := targetTelescopePairFunctor f)
    (telescopeScalarComponent f) (fun {X Y} a => telescopeScalarNaturality f a)
  have h : finiteBGLTelescopeRowScalarPairIso f = e := rfl
  exact (congrArg
    (fun q : sourceTelescopePairFunctor f ≅ targetTelescopePairFunctor f => q.app X) h).trans
    (NatIso.ofComponents.app (F := sourceTelescopePairFunctor f) (G := targetTelescopePairFunctor f)
      (telescopeScalarComponent f) (fun {X Y} a => telescopeScalarNaturality f a) X)

/-- The actual source Pair object is its original diagonal row object after
scalar extension; only the original telescope and finite-row object equalities are used. -/
public theorem finiteBGLTelescopeRowScalar_source_obj (f : R →+* S)
    (X : FiniteBGLTelescopeCategory R) :
    let FR := (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      FGProjectiveCat.scalarExtension.{uR, uS, uR} f
    (finiteBGLTelescopeToRowZeroComponent R ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι ⋙
        SInverseS.pairFunctor FR).obj X =
      (⟨FR.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj X.base),
        FR.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj X.base)⟩ :
        SInverseS.Pair (FGProjectiveCat.{max uS uR} S)) :=
  (telescopeStageEq R (sourceRowFunctor f) X).trans
    (rowIndexObjEq R (sourceRowFunctor f) X.base)

/-- The actual coefficient-image telescope has the same retained rank and the
original target diagonal row object in the common projective carrier universe. -/
public theorem finiteBGLTelescopeRowScalar_target_obj (f : R →+* S)
    (X : FiniteBGLTelescopeCategory R) :
    let FS := (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse
    (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel S)).ι ⋙
        SInverseS.pairFunctor FS).obj X =
      (⟨FS.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj X.base),
        FS.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj X.base)⟩ :
        SInverseS.Pair (FGProjectiveCat.{max uS uR} S)) :=
  (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
      ((finiteBGLTelescopeScalarFunctor f).obj X)).trans
    (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) X.base)

/-- Every component is exactly the two original row scalar isomorphisms under
the public actual object transports, including the retained rank-zero component. -/
public theorem finiteBGLTelescopeRowScalarPairIso_app_after_obj (f : R →+* S)
    (X : FiniteBGLTelescopeCategory R) :
    let FR := (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      FGProjectiveCat.scalarExtension.{uR, uS, uR} f
    let FS := (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse
    eqToIso (finiteBGLTelescopeRowScalar_source_obj f X).symm ≪≫
        (finiteBGLTelescopeRowScalarPairIso f).app X ≪≫
        eqToIso (finiteBGLTelescopeRowScalar_target_obj f X) =
      (SInverseS.corePairInclusion (C := FGProjectiveCat.{max uS uR} S)).mapIso
        ((Core.isoMk
          (x := ⟨FR.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj X.base)⟩)
          (y := ⟨FS.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj X.base)⟩)
          (finiteFreeRowScalarIso f X.base)).prod
          (Core.isoMk
            (x := ⟨FR.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj X.base)⟩)
            (y := ⟨FS.obj ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj X.base)⟩)
            (finiteFreeRowScalarIso f X.base))) := by
  have hApp : ((finiteBGLTelescopeRowScalarPairIso f).app X).hom =
      eqToHom (telescopeStageEq R (sourceRowFunctor f) X) ≫
        eqToHom (rowIndexObjEq R (sourceRowFunctor f) X.base) ≫
        (diagonalScalarIso f X.base).hom ≫
        eqToHom (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) X.base).symm ≫
        eqToHom (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
          ((finiteBGLTelescopeScalarFunctor f).obj X)).symm :=
    (congrArg Iso.hom (finiteBGLTelescopeRowScalarPairIso_app_recipe f X)).trans
      (telescopeScalarComponent_hom_formula f X)
  have hLeft :
      (eqToIso (finiteBGLTelescopeRowScalar_source_obj f X).symm ≪≫
        (finiteBGLTelescopeRowScalarPairIso f).app X ≪≫
        eqToIso (finiteBGLTelescopeRowScalar_target_obj f X)).hom =
      eqToHom (finiteBGLTelescopeRowScalar_source_obj f X).symm ≫
        (eqToHom (telescopeStageEq R (sourceRowFunctor f) X) ≫
          eqToHom (rowIndexObjEq R (sourceRowFunctor f) X.base) ≫
          (diagonalScalarIso f X.base).hom ≫
          eqToHom (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) X.base).symm ≫
          eqToHom (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
            ((finiteBGLTelescopeScalarFunctor f).obj X)).symm) ≫
        eqToHom (finiteBGLTelescopeRowScalar_target_obj f X) := by
    simpa only [Iso.trans_hom, eqToIso.hom] using congrArg
      (fun q : (sourceTelescopePairFunctor f).obj X ⟶ (targetTelescopePairFunctor f).obj X =>
        eqToHom (finiteBGLTelescopeRowScalar_source_obj f X).symm ≫ q ≫
          eqToHom (finiteBGLTelescopeRowScalar_target_obj f X)) hApp
  have hMiddle :
      eqToHom (finiteBGLTelescopeRowScalar_source_obj f X).symm ≫
        (eqToHom (telescopeStageEq R (sourceRowFunctor f) X) ≫
          eqToHom (rowIndexObjEq R (sourceRowFunctor f) X.base) ≫
          (diagonalScalarIso f X.base).hom ≫
          eqToHom (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) X.base).symm ≫
          eqToHom (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
            ((finiteBGLTelescopeScalarFunctor f).obj X)).symm) ≫
        eqToHom (finiteBGLTelescopeRowScalar_target_obj f X) =
      (diagonalScalarIso f X.base).hom := by
    exact eqToHomCycleSandwich
      (finiteBGLTelescopeRowScalar_source_obj f X).symm
      (telescopeStageEq R (sourceRowFunctor f) X)
      (rowIndexObjEq R (sourceRowFunctor f) X.base)
      (rowIndexObjEq S (targetRowFunctor.{uS, uR} S) X.base).symm
      (telescopeStageEq S (targetRowFunctor.{uS, uR} S)
        ((finiteBGLTelescopeScalarFunctor f).obj X)).symm
      (finiteBGLTelescopeRowScalar_target_obj f X) (diagonalScalarIso f X.base).hom
  apply Iso.ext
  exact hLeft.trans (hMiddle.trans (congrArg Iso.hom (diagonalScalarIso_recipe f X.base)))

/-- The same whole natural isomorphism restricts to the original zero components.
Both target objects earn their zero property from the actual Grothendieck map. -/
public def finiteBGLTelescopeRowScalarZeroIso (f : R →+* S) :
    finiteBGLTelescopeToRowZeroComponent R ⋙
        SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{uR, uS, uR} f) ≅
      finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S ⋙
        SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse) := by
  let FR := sourceRowFunctor f
  let FS := targetRowFunctor.{uS, uR} S
  let A := finiteBGLTelescopeToRowZeroComponent R ⋙ SInverseS.zeroComponentFunctor FR
  let B := (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S) ⋙
    SInverseS.zeroComponentFunctor FS
  let j := (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι
  let eA : A ⋙ j ≅ sourceTelescopePairFunctor f :=
    Functor.associator (finiteBGLTelescopeToRowZeroComponent R)
        (SInverseS.zeroComponentFunctor FR) j ≪≫
      Functor.isoWhiskerLeft (finiteBGLTelescopeToRowZeroComponent R)
        (SInverseS.zeroComponentFunctorInclusionIso FR)
  let eB : B ⋙ j ≅ targetTelescopePairFunctor f :=
    Functor.associator
        (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S)
        (SInverseS.zeroComponentFunctor FS) j ≪≫
      Functor.isoWhiskerLeft
        (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S)
        (SInverseS.zeroComponentFunctorInclusionIso FS)
  exact SInverseS.liftZeroComponentNatIso A B
    (eA ≪≫ finiteBGLTelescopeRowScalarPairIso f ≪≫ eB.symm)

/-- The actual source zero restriction has its original whole Pair inclusion comparison. -/
public def finiteBGLTelescopeScalarSourceZeroInclusionIso (f : R →+* S) :
    (finiteBGLTelescopeToRowZeroComponent R ⋙
      SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{uR, uS, uR} f)) ⋙
      (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι ≅
    finiteBGLTelescopeToRowZeroComponent R ⋙
      (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι ⋙
      SInverseS.pairFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{uR, uS, uR} f) :=
  Functor.associator (finiteBGLTelescopeToRowZeroComponent R)
      (SInverseS.zeroComponentFunctor (sourceRowFunctor f))
      (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι ≪≫
    Functor.isoWhiskerLeft (finiteBGLTelescopeToRowZeroComponent R)
      (SInverseS.zeroComponentFunctorInclusionIso (sourceRowFunctor f))

/-- The actual target zero restriction has its original whole Pair inclusion comparison. -/
public def finiteBGLTelescopeScalarTargetZeroInclusionIso (f : R →+* S) :
    ((finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S) ⋙
      SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
        (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse)) ⋙
      (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι ≅
    finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S ⋙
      (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel S)).ι ⋙
      SInverseS.pairFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
        (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse) :=
  Functor.associator
      (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S)
      (SInverseS.zeroComponentFunctor (targetRowFunctor.{uS, uR} S))
      (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι ≪≫
    Functor.isoWhiskerLeft
      (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S)
      (SInverseS.zeroComponentFunctorInclusionIso (targetRowFunctor.{uS, uR} S))

/-- The proper zero inclusion computes each actual scalar component by its original Pair Iso. -/
public theorem finiteBGLTelescopeRowScalarZeroIso_inclusion_app (f : R →+* S)
    (X : FiniteBGLTelescopeCategory R) :
    (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι.mapIso
        ((finiteBGLTelescopeRowScalarZeroIso f).app X) =
      (finiteBGLTelescopeScalarSourceZeroInclusionIso f).app X ≪≫
        (finiteBGLTelescopeRowScalarPairIso f).app X ≪≫
        ((finiteBGLTelescopeScalarTargetZeroInclusionIso f).app X).symm := by
  let A := finiteBGLTelescopeToRowZeroComponent R ⋙
    SInverseS.zeroComponentFunctor (sourceRowFunctor f)
  let B := (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S) ⋙
    SInverseS.zeroComponentFunctor (targetRowFunctor.{uS, uR} S)
  let j := (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{max uS uR} S)).ι
  let eA := finiteBGLTelescopeScalarSourceZeroInclusionIso f
  let eB := finiteBGLTelescopeScalarTargetZeroInclusionIso f
  let e := eA ≪≫ finiteBGLTelescopeRowScalarPairIso f ≪≫ eB.symm
  have hCtor : finiteBGLTelescopeRowScalarZeroIso f = SInverseS.liftZeroComponentNatIso A B e := rfl
  have hMap := congrArg (fun q : A ≅ B => j.mapIso (q.app X)) hCtor
  have hLift := SInverseS.liftZeroComponentNatIso_inclusion_app A B e X
  have hApp : e.app X = eA.app X ≪≫ (finiteBGLTelescopeRowScalarPairIso f).app X ≪≫
      (eB.app X).symm := rfl
  exact hMap.trans (hLift.trans hApp)

end AlgebraicKTheory.StableGL


noncomputable section

open CategoryTheory

universe uScalarInclusionValueR uScalarInclusionValueS

namespace AlgebraicKTheory.StableGL

variable {R : Type uScalarInclusionValueR} {S : Type uScalarInclusionValueS} [Ring R] [Ring S]

private theorem finiteBGLTelescopeScalarSourceZeroInclusionIsoAppValueComputed
    (f : R →+* S) (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeScalarSourceZeroInclusionIso f).app X =
      eqToIso (SInverseS.zeroComponentFunctor_obj_obj
        ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{
            uScalarInclusionValueR, uScalarInclusionValueS, uScalarInclusionValueR} f)
        ((finiteBGLTelescopeToRowZeroComponent R).obj X)) := by
  apply Iso.ext
  change 𝟙 _ ≫
    (SInverseS.zeroComponentFunctorInclusionIso
      ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{
          uScalarInclusionValueR, uScalarInclusionValueS, uScalarInclusionValueR} f)).hom.app
      ((finiteBGLTelescopeToRowZeroComponent R).obj X) = _
  rw [Category.id_comp]
  exact congrArg Iso.hom (SInverseS.zeroComponentFunctorInclusionIso_app_value
    ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      FGProjectiveCat.scalarExtension.{
        uScalarInclusionValueR, uScalarInclusionValueS, uScalarInclusionValueR} f)
    ((finiteBGLTelescopeToRowZeroComponent R).obj X))

/-- EVERY actual source inclusion component keeps the SAME associator/whisker
wrapper of its proper original zero-functor object transport. -/
public theorem finiteBGLTelescopeScalarSourceZeroInclusionIso_app_value
    (f : R →+* S) (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeScalarSourceZeroInclusionIso f).app X =
      eqToIso (SInverseS.zeroComponentFunctor_obj_obj
        ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{
            uScalarInclusionValueR, uScalarInclusionValueS, uScalarInclusionValueR} f)
        ((finiteBGLTelescopeToRowZeroComponent R).obj X)) :=
  finiteBGLTelescopeScalarSourceZeroInclusionIsoAppValueComputed f X

private theorem finiteBGLTelescopeScalarTargetZeroInclusionIsoAppValueComputed
    (f : R →+* S) (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeScalarTargetZeroInclusionIso f).app X =
      eqToIso (SInverseS.zeroComponentFunctor_obj_obj
        ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{
            uScalarInclusionValueS, uScalarInclusionValueR} S).inverse)
        ((finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S).obj X)) := by
  apply Iso.ext
  change 𝟙 _ ≫
    (SInverseS.zeroComponentFunctorInclusionIso
      ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
        (FGProjectiveCat.universeEquivalence.{
          uScalarInclusionValueS, uScalarInclusionValueR} S).inverse)).hom.app
      ((finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S).obj X) = _
  rw [Category.id_comp]
  exact congrArg Iso.hom (SInverseS.zeroComponentFunctorInclusionIso_app_value
    ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{
        uScalarInclusionValueS, uScalarInclusionValueR} S).inverse)
    ((finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S).obj X))

/-- EVERY actual target inclusion component keeps the SAME associator/whisker
wrapper at the original scalar/telescope object, with no root choice change. -/
public theorem finiteBGLTelescopeScalarTargetZeroInclusionIso_app_value
    (f : R →+* S) (X : FiniteBGLTelescopeCategory R) :
    (finiteBGLTelescopeScalarTargetZeroInclusionIso f).app X =
      eqToIso (SInverseS.zeroComponentFunctor_obj_obj
        ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{
            uScalarInclusionValueS, uScalarInclusionValueR} S).inverse)
        ((finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S).obj X)) :=
  finiteBGLTelescopeScalarTargetZeroInclusionIsoAppValueComputed f X

end AlgebraicKTheory.StableGL

end
