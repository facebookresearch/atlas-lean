/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionRowCompatibility
public import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel
public import MathlibExt.Algebra.Category.FGProjectiveCat.UniverseEquivalence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Intrinsic scalar calibration of the original finite row model

The canonical balanced tensor coordinates are bundled into an actual
finite-projective Iso. They intertwine the original opposite-GL row
automorphisms, then the original row-range free comparisons transport
this square to the actual small idempotent-row model.

Every map is an existing scalar-extension, row-range, free-coordinate or
carrier-lift map. The ring universes are independent. No chosen Q/plus
equivalence or expected source-naturality witness occurs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Matrix

universe uR uS uA uC vC

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- Actual tensor coordinates followed by the original projective carrier lift. -/
public def finiteFreeScalarIso (f : R →+* S) (n : ℕ) :
    (FGProjectiveCat.scalarExtension.{uR, uS, uR} f).obj (FGProjectiveCat.standardFree R n) ≅
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse.obj
        (FGProjectiveCat.standardFree S n) :=
  (ModuleCat.isFGProjective.{max uS uR} S).isoMk
    (_root_.LinearEquiv.toModuleIso
      ((ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n).trans
        (FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
          (FGProjectiveCat.standardFree S n)).symm))

/-- Down-coordinates of the actual bundled map are the literal tensor coordinates. -/
public theorem finiteFreeScalarIso_down (f : R →+* S) (n : ℕ)
    (x : (FGProjectiveCat.scalarExtension.{uR, uS, uR} f).obj
      (FGProjectiveCat.standardFree R n)) :
    FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
        (FGProjectiveCat.standardFree S n) ((finiteFreeScalarIso f n).hom x) =
      ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n x := by
  change FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
      (FGProjectiveCat.standardFree S n)
      ((FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
        (FGProjectiveCat.standardFree S n)).symm
          (ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n x)) = _
  exact (FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
    (FGProjectiveCat.standardFree S n)).apply_symm_apply _

private theorem rowAut_linear
    (A : Type uA) [Ring A] (n : ℕ) (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ) :
    (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv A n g).asIso.hom.hom.hom =
      (FGProjectiveCat.rowGLLinearEquiv A n g).toLinearMap := by
  apply LinearMap.ext
  intro x
  change (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv A n g).asIso.hom x =
    FGProjectiveCat.rowGLLinearEquiv A n g x
  exact (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv_apply A n g x).trans
    (FGProjectiveCat.rowGLLinearEquiv_apply A n g x).symm

/-- The actual finite-projective Iso intertwines the original row actions. -/
public theorem finiteFreeScalarIso_naturality (f : R →+* S) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (FGProjectiveCat.scalarExtension.{uR, uS, uR} f).map
        (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv R n (MulOpposite.op g)).asIso.hom ≫
      (finiteFreeScalarIso f n).hom =
    (finiteFreeScalarIso f n).hom ≫
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse.map
        (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv S n
          (MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f g))).asIso.hom := by
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
    (FGProjectiveCat.standardFree S n)).injective
  change ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n
      (((ModuleCat.RingHomScalarExtension.functor.{uR, uS, uR} f).map
        (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv R n
          (MulOpposite.op g)).asIso.hom.hom).hom x) =
    (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv S n
        (MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f g))).asIso.hom.hom.hom
      (ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n x)
  rw [ModuleCat.RingHomScalarExtension.functor_map_hom, rowAut_linear, rowAut_linear]
  exact DFunLike.congr_fun (FGProjectiveCat.scalarExtension_rowGL f n g) x

private theorem modelFreeAut_square
    (A : Type uA) [Ring A] (n : ℕ) (g : (Matrix.GeneralLinearGroup (Fin n) A)ᵐᵒᵖ) :
    (FGProjectiveCat.IdempotentModel.equivalence A).functor.map
        (FGProjectiveCat.IdempotentModel.freeAut A n g).hom ≫
      (FGProjectiveCat.IdempotentModel.freeIso A n).hom =
    (FGProjectiveCat.IdempotentModel.freeIso A n).hom ≫
      (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv A n g).asIso.hom := by
  let H := FGProjectiveCat.IdempotentModel.freeIso A n
  let G := (FGProjectiveCat.IdempotentModel.equivalence A).functor.mapIso
    (FGProjectiveCat.IdempotentModel.freeAut A n g)
  have hc : H.conjAut (Aut.of G) = FGProjectiveCat.finiteOppositeGLAutRowMulEquiv A n g :=
    ((FGProjectiveCat.IdempotentModel.free_block_characteristic A).2.2.2.1 n g).2.2
  have he : H.symm ≪≫ G ≪≫ H =
      (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv A n g).asIso :=
    (Iso.conjAut_apply H (Aut.of G)).symm.trans (congrArg Aut.asIso hc)
  have hh := H.hom ≫= congrArg Iso.hom he
  simpa only [H, G, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc] using hh

private theorem isoIntertwinerCompose
    {C : Type uC} [Category.{vC} C] {A B D E : C}
    (p : A ≅ B) (q : B ≅ D) (r : E ≅ D)
    {a : A ⟶ A} {b : B ⟶ B} {d : D ⟶ D} {e : E ⟶ E}
    (hp : a ≫ p.hom = p.hom ≫ b)
    (hq : b ≫ q.hom = q.hom ≫ d)
    (hr : e ≫ r.hom = r.hom ≫ d) :
    a ≫ (p ≪≫ q ≪≫ r.symm).hom = (p ≪≫ q ≪≫ r.symm).hom ≫ e := by
  have hd : d ≫ r.inv = r.inv ≫ e := by
    apply (cancel_mono r.hom).1
    calc
      (d ≫ r.inv) ≫ r.hom = d := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = r.inv ≫ (r.hom ≫ d) := by simp only [Iso.inv_hom_id_assoc]
      _ = r.inv ≫ (e ≫ r.hom) := congrArg (fun h => r.inv ≫ h) hr.symm
      _ = (r.inv ≫ e) ≫ r.hom := (Category.assoc _ _ _).symm
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc
    a ≫ p.hom ≫ q.hom ≫ r.inv = (a ≫ p.hom) ≫ (q.hom ≫ r.inv) :=
      (Category.assoc _ _ _).symm
    _ = (p.hom ≫ b) ≫ (q.hom ≫ r.inv) :=
      congrArg (fun h => h ≫ (q.hom ≫ r.inv)) hp
    _ = p.hom ≫ (b ≫ q.hom) ≫ r.inv := by simp only [Category.assoc]
    _ = p.hom ≫ (q.hom ≫ d) ≫ r.inv :=
      congrArg (fun h => p.hom ≫ h ≫ r.inv) hq
    _ = p.hom ≫ q.hom ≫ (d ≫ r.inv) := by simp only [Category.assoc]
    _ = p.hom ≫ q.hom ≫ (r.inv ≫ e) :=
      congrArg (fun h => p.hom ≫ q.hom ≫ h) hd
    _ = (p.hom ≫ q.hom ≫ r.inv) ≫ e := by simp only [Category.assoc]

/-- The original row-range free objects are compared by actual scalar coordinates. -/
public def finiteFreeRowScalarIso (f : R →+* S) (n : ℕ) :
    ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{uR, uS, uR} f).obj
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ≅
    ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
        (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse).obj
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj n) :=
  (FGProjectiveCat.scalarExtension.{uR, uS, uR} f).mapIso
      (FGProjectiveCat.IdempotentModel.freeIso R n) ≪≫
    finiteFreeScalarIso f n ≪≫
      ((FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse.mapIso
        (FGProjectiveCat.IdempotentModel.freeIso S n)).symm

/-- The actual row-model matrix square is derived from its original block characteristic. -/
public theorem finiteFreeRowScalarIso_naturality (f : R →+* S) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{uR, uS, uR} f).map
        (FGProjectiveCat.IdempotentModel.freeAut R n (MulOpposite.op g)).hom ≫
      (finiteFreeRowScalarIso f n).hom =
    (finiteFreeRowScalarIso f n).hom ≫
      ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
        (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse).map
        (FGProjectiveCat.IdempotentModel.freeAut S n
          (MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f g))).hom := by
  let F := FGProjectiveCat.scalarExtension.{uR, uS, uR} f
  let L := (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse
  let p := F.mapIso (FGProjectiveCat.IdempotentModel.freeIso R n)
  let q := finiteFreeScalarIso f n
  let r := L.mapIso (FGProjectiveCat.IdempotentModel.freeIso S n)
  have hp :
      F.map ((FGProjectiveCat.IdempotentModel.equivalence R).functor.map
          (FGProjectiveCat.IdempotentModel.freeAut R n (MulOpposite.op g)).hom) ≫ p.hom =
        p.hom ≫ F.map
          (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv R n (MulOpposite.op g)).asIso.hom := by
    have h := congrArg F.map (modelFreeAut_square R n (MulOpposite.op g))
    simpa only [p, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.mapIso_hom] using h
  have hq :
      F.map (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv R n
        (MulOpposite.op g)).asIso.hom ≫ q.hom =
        q.hom ≫ L.map (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv S n
          (MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f g))).asIso.hom :=
    finiteFreeScalarIso_naturality f n g
  have hr :
      L.map ((FGProjectiveCat.IdempotentModel.equivalence S).functor.map
          (FGProjectiveCat.IdempotentModel.freeAut S n
            (MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f g))).hom) ≫ r.hom =
        r.hom ≫ L.map
          (FGProjectiveCat.finiteOppositeGLAutRowMulEquiv S n
            (MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f g))).asIso.hom := by
    have h := congrArg L.map
      (modelFreeAut_square S n (MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f g)))
    simpa only [r, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.mapIso_hom] using h
  change F.map ((FGProjectiveCat.IdempotentModel.equivalence R).functor.map
      (FGProjectiveCat.IdempotentModel.freeAut R n (MulOpposite.op g)).hom) ≫
      (p ≪≫ q ≪≫ r.symm).hom =
    (p ≪≫ q ≪≫ r.symm).hom ≫
      L.map ((FGProjectiveCat.IdempotentModel.equivalence S).functor.map
        (FGProjectiveCat.IdempotentModel.freeAut S n
          (MulOpposite.op (Matrix.GeneralLinearGroup.mapRingHom f g))).hom)
  exact isoIntertwinerCompose p q r hp hq hr

/-- Both original rank-zero routes use the canonical additive zero comparison.
Their equality is derived at the actual target zero object, not assumed as a trace. -/
public theorem finiteFreeRowScalarIso_zero (f : R →+* S) :
    let FR := (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      FGProjectiveCat.scalarExtension.{uR, uS, uR} f
    let FS := (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse
    FR.mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso R) ≪≫ FR.mapZeroObject =
      finiteFreeRowScalarIso f 0 ≪≫
        FS.mapIso (FGProjectiveCat.IdempotentModel.freeZeroIso S) ≪≫ FS.mapZeroObject := by
  dsimp only
  apply Iso.ext
  exact (CategoryTheory.Limits.isZero_zero (FGProjectiveCat.{max uS uR} S)).eq_of_tgt _ _

private theorem tensorMatrix_coordinates (f : R →+* S) (n m : ℕ)
    (a : Matrix (Fin n) (Fin m) R) :
    (ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f m).toLinearMap.comp
        (ModuleCat.RingHomScalarExtension.linearMap f a.toLinearMapRight') =
      (Matrix.map a f).toLinearMapRight'.comp
        (ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n).toLinearMap := by
  apply ModuleCat.RingHomScalarExtension.linearMap_ext f (Fin n → R)
  intro s x
  simp only [LinearMap.comp_apply, ModuleCat.RingHomScalarExtension.linearMap_pure]
  apply funext
  intro j
  have hL :
      (ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f m).toLinearMap
          (ModuleCat.RingHomScalarExtension.pure f (Fin m → R) s
            (a.toLinearMapRight' x)) j =
        s * f (a.toLinearMapRight' x j) :=
    ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv_pure
      f m s (a.toLinearMapRight' x) j
  have hCoordinates :
      (ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n).toLinearMap
          (ModuleCat.RingHomScalarExtension.pure f (Fin n → R) s x) =
        (fun i => s * f (x i)) :=
    funext (fun i => ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv_pure
      f n s x i)
  have hR :
      (Matrix.map a f).toLinearMapRight'
          ((ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n).toLinearMap
            (ModuleCat.RingHomScalarExtension.pure f (Fin n → R) s x)) j =
        (Matrix.map a f).toLinearMapRight' (fun i => s * f (x i)) j :=
    congrArg (fun v : Fin n → S => (Matrix.map a f).toLinearMapRight' v j) hCoordinates
  have hSum :
      s * f (a.toLinearMapRight' x j) =
        (Matrix.map a f).toLinearMapRight' (fun i => s * f (x i)) j := by
    simp only [Matrix.toLinearMapRight'_apply, Matrix.vecMul_apply, dotProduct,
      Matrix.col_apply, Matrix.map_apply]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, mul_assoc]
  exact Eq.trans hL (Eq.trans hSum hR.symm)

/-- Actual scalar coordinates intertwine every original rectangular row-matrix map. -/
public theorem finiteFreeScalarIso_matrix (f : R →+* S) (n m : ℕ)
    (a : Matrix (Fin n) (Fin m) R) :
    (FGProjectiveCat.scalarExtension.{uR, uS, uR} f).map
        (FGProjectiveCat.ofHom a.toLinearMapRight') ≫
        (finiteFreeScalarIso f m).hom =
      (finiteFreeScalarIso f n).hom ≫
        (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse.map
          (FGProjectiveCat.ofHom (a.map f).toLinearMapRight') := by
  have hMap :
      ((FGProjectiveCat.scalarExtension.{uR, uS, uR} f).map
        (FGProjectiveCat.ofHom a.toLinearMapRight')).hom.hom =
      ((ModuleCat.RingHomScalarExtension.functor.{uR, uS, uR} f).map
        (FGProjectiveCat.ofHom a.toLinearMapRight').hom).hom := by
    exact congrArg ModuleCat.Hom.hom
      (ObjectProperty.ι_obj_lift_map
        (ModuleCat.isFGProjective.{max uS uR} S)
        ((ModuleCat.isFGProjective.{uR} R).ι ⋙
          ModuleCat.RingHomScalarExtension.functor.{uR, uS, uR} f)
        (fun P => ModuleCat.RingHomScalarExtension.isFGProjective_obj f P)
        (FGProjectiveCat.ofHom a.toLinearMapRight'))
  apply FGProjectiveCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
    (FGProjectiveCat.standardFree S m)).injective
  have hMapAt :
      ((FGProjectiveCat.scalarExtension.{uR, uS, uR} f).map
        (FGProjectiveCat.ofHom a.toLinearMapRight')).hom.hom x =
      ModuleCat.RingHomScalarExtension.linearMap f a.toLinearMapRight' x :=
    (LinearMap.congr_fun hMap x).trans
      (LinearMap.congr_fun
        (ModuleCat.RingHomScalarExtension.functor_map_hom f
          (FGProjectiveCat.ofHom a.toLinearMapRight').hom) x)
  have hLeft :
      FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
        (FGProjectiveCat.standardFree S m)
        ((finiteFreeScalarIso f m).hom
          (((FGProjectiveCat.scalarExtension.{uR, uS, uR} f).map
            (FGProjectiveCat.ofHom a.toLinearMapRight')).hom.hom x)) =
      ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f m
        (ModuleCat.RingHomScalarExtension.linearMap f a.toLinearMapRight' x) :=
    (finiteFreeScalarIso_down f m
      (((FGProjectiveCat.scalarExtension.{uR, uS, uR} f).map
        (FGProjectiveCat.ofHom a.toLinearMapRight')).hom.hom x)).trans
      (congrArg (fun y : ModuleCat.RingHomScalarExtension.tensor f (Fin m → R) =>
        ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f m y) hMapAt)
  let z : FGProjectiveCat.UniverseEquivalence.liftObject.{uS, uR} S
      (FGProjectiveCat.standardFree S n) :=
    (finiteFreeScalarIso f n).hom x
  have hLiftAt :
      ((FGProjectiveCat.UniverseEquivalence.liftFunctor.{uS, uR} S).map
        (FGProjectiveCat.ofHom (a.map f).toLinearMapRight')).hom.hom z =
      (FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
        (FGProjectiveCat.standardFree S m)).symm
          ((Matrix.map a f).toLinearMapRight'
            (FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
              (FGProjectiveCat.standardFree S n) z)) :=
    FGProjectiveCat.UniverseEquivalence.liftFunctor_map_apply.{uS, uR} S
      (M := FGProjectiveCat.standardFree S n) (N := FGProjectiveCat.standardFree S m)
      (FGProjectiveCat.ofHom (a.map f).toLinearMapRight') z
  have hRight :
      FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
        (FGProjectiveCat.standardFree S m)
        (((FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse.map
          (FGProjectiveCat.ofHom (a.map f).toLinearMapRight')).hom.hom z) =
      (Matrix.map a f).toLinearMapRight'
        (ModuleCat.RingHomScalarExtension.finiteFreeTensorLinearEquiv f n x) :=
    (congrArg (fun y : FGProjectiveCat.UniverseEquivalence.liftObject.{uS, uR} S
        (FGProjectiveCat.standardFree S m) =>
      FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
        (FGProjectiveCat.standardFree S m) y) hLiftAt).trans
      (((FGProjectiveCat.UniverseEquivalence.liftLinearEquiv.{uS, uR} S
        (FGProjectiveCat.standardFree S m)).apply_symm_apply _).trans
          (congrArg (fun v : Fin n → S => (Matrix.map a f).toLinearMapRight' v)
            (finiteFreeScalarIso_down f n x)))
  have hTensor := DFunLike.congr_fun (tensorMatrix_coordinates f n m a)
    (show ModuleCat.RingHomScalarExtension.tensor f (Fin n → R) from x)
  exact hLeft.trans (hTensor.trans hRight.symm)

/-- The original row-matrix arrow, before any scalar or realization transport. -/
public def finiteFreeRowMatrixArrow
    (A : Type uA) [Ring A] (n m : ℕ) (a : Matrix (Fin n) (Fin m) A) :
    (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks A)).obj n ⟶
      (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks A)).obj m :=
  (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks A)).map
    ((FGProjectiveCat.IdempotentModel.rowHomEquiv A n m).symm a)

private theorem modelFreeMatrix_square
    (A : Type uA) [Ring A] (n m : ℕ) (a : Matrix (Fin n) (Fin m) A) :
    (FGProjectiveCat.IdempotentModel.equivalence A).functor.map
        (finiteFreeRowMatrixArrow A n m a) ≫
      (FGProjectiveCat.IdempotentModel.freeIso A m).hom =
    (FGProjectiveCat.IdempotentModel.freeIso A n).hom ≫
      FGProjectiveCat.ofHom a.toLinearMapRight' :=
  (FGProjectiveCat.IdempotentModel.free_characteristic A).2.2.2.1 n m a

private theorem isoChartSquare
    {C : Type uC} [Category.{vC} C] {A B D E A' B' D' E' : C}
    (p : A ≅ B) (p' : A' ≅ B') (q : B ≅ D) (q' : B' ≅ D')
    (r : E ≅ D) (r' : E' ≅ D')
    {a : A ⟶ A'} {b : B ⟶ B'} {d : D ⟶ D'} {e : E ⟶ E'}
    (hp : a ≫ p'.hom = p.hom ≫ b)
    (hq : b ≫ q'.hom = q.hom ≫ d)
    (hr : e ≫ r'.hom = r.hom ≫ d) :
    a ≫ (p' ≪≫ q' ≪≫ r'.symm).hom = (p ≪≫ q ≪≫ r.symm).hom ≫ e := by
  have hd : d ≫ r'.inv = r.inv ≫ e := by
    apply (cancel_mono r'.hom).1
    calc
      (d ≫ r'.inv) ≫ r'.hom = d := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = r.inv ≫ (r.hom ≫ d) := by simp only [Iso.inv_hom_id_assoc]
      _ = r.inv ≫ (e ≫ r'.hom) := congrArg (fun h => r.inv ≫ h) hr.symm
      _ = (r.inv ≫ e) ≫ r'.hom := (Category.assoc _ _ _).symm
  simp only [Iso.trans_hom, Iso.symm_hom]
  calc
    a ≫ p'.hom ≫ q'.hom ≫ r'.inv = (a ≫ p'.hom) ≫ (q'.hom ≫ r'.inv) :=
      (Category.assoc _ _ _).symm
    _ = (p.hom ≫ b) ≫ (q'.hom ≫ r'.inv) :=
      congrArg (fun h => h ≫ (q'.hom ≫ r'.inv)) hp
    _ = p.hom ≫ (b ≫ q'.hom) ≫ r'.inv := by simp only [Category.assoc]
    _ = p.hom ≫ (q.hom ≫ d) ≫ r'.inv :=
      congrArg (fun h => p.hom ≫ h ≫ r'.inv) hq
    _ = p.hom ≫ q.hom ≫ (d ≫ r'.inv) := by simp only [Category.assoc]
    _ = p.hom ≫ q.hom ≫ (r.inv ≫ e) :=
      congrArg (fun h => p.hom ≫ q.hom ≫ h) hd
    _ = (p.hom ≫ q.hom ≫ r.inv) ≫ e := by simp only [Category.assoc]

/-- The original row-model calibration commutes with every original mixed-rank matrix. -/
public theorem finiteFreeRowScalarIso_matrix (f : R →+* S) (n m : ℕ)
    (a : Matrix (Fin n) (Fin m) R) :
    ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
        FGProjectiveCat.scalarExtension.{uR, uS, uR} f).map
        (finiteFreeRowMatrixArrow R n m a) ≫ (finiteFreeRowScalarIso f m).hom =
      (finiteFreeRowScalarIso f n).hom ≫
        ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse).map
          (finiteFreeRowMatrixArrow S n m (a.map f)) := by
  let F := FGProjectiveCat.scalarExtension.{uR, uS, uR} f
  let L := (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse
  let p := F.mapIso (FGProjectiveCat.IdempotentModel.freeIso R n)
  let p' := F.mapIso (FGProjectiveCat.IdempotentModel.freeIso R m)
  let q := finiteFreeScalarIso f n
  let q' := finiteFreeScalarIso f m
  let r := L.mapIso (FGProjectiveCat.IdempotentModel.freeIso S n)
  let r' := L.mapIso (FGProjectiveCat.IdempotentModel.freeIso S m)
  have hp :
      F.map ((FGProjectiveCat.IdempotentModel.equivalence R).functor.map
        (finiteFreeRowMatrixArrow R n m a)) ≫ p'.hom =
      p.hom ≫ F.map (FGProjectiveCat.ofHom a.toLinearMapRight') := by
    have h := congrArg F.map (modelFreeMatrix_square R n m a)
    simpa only [p, p', CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.mapIso_hom] using h
  have hq :
      F.map (FGProjectiveCat.ofHom a.toLinearMapRight') ≫ q'.hom =
        q.hom ≫ L.map (FGProjectiveCat.ofHom (a.map f).toLinearMapRight') :=
    finiteFreeScalarIso_matrix f n m a
  have hr :
      L.map ((FGProjectiveCat.IdempotentModel.equivalence S).functor.map
        (finiteFreeRowMatrixArrow S n m (a.map f))) ≫ r'.hom =
      r.hom ≫ L.map (FGProjectiveCat.ofHom (a.map f).toLinearMapRight') := by
    have h := congrArg L.map (modelFreeMatrix_square S n m (a.map f))
    simpa only [r, r', CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.mapIso_hom] using h
  change F.map ((FGProjectiveCat.IdempotentModel.equivalence R).functor.map
      (finiteFreeRowMatrixArrow R n m a)) ≫ (p' ≪≫ q' ≪≫ r'.symm).hom =
    (p ≪≫ q ≪≫ r.symm).hom ≫
      L.map ((FGProjectiveCat.IdempotentModel.equivalence S).functor.map
        (finiteFreeRowMatrixArrow S n m (a.map f)))
  exact isoChartSquare p p' q q' r r' hp hq hr

private def rowLeftProjection (A : Type uA) [Ring A] (n m : ℕ) :
    Matrix (Fin (n + m)) (Fin n) A :=
  fun k i => if k = Fin.castAdd m i then 1 else 0

private def rowRightProjection (A : Type uA) [Ring A] (n m : ℕ) :
    Matrix (Fin (n + m)) (Fin m) A :=
  fun k j => if k = Fin.natAdd n j then 1 else 0

private theorem scalar_leftProjection (f : R →+* S) (n m : ℕ) :
    Matrix.map (rowLeftProjection R n m) f = rowLeftProjection S n m := by
  apply Matrix.ext
  intro k i
  by_cases h : k = Fin.castAdd m i
  · simp only [Matrix.map_apply, rowLeftProjection, ite_eq_left h, map_one]
  · simp only [Matrix.map_apply, rowLeftProjection, ite_eq_right h, map_zero]

private theorem scalar_rightProjection (f : R →+* S) (n m : ℕ) :
    Matrix.map (rowRightProjection R n m) f = rowRightProjection S n m := by
  apply Matrix.ext
  intro k j
  by_cases h : k = Fin.natAdd n j
  · simp only [Matrix.map_apply, rowRightProjection, ite_eq_left h, map_one]
  · simp only [Matrix.map_apply, rowRightProjection, ite_eq_right h, map_zero]

private theorem freeBiprod_fst_matrix (A : Type uA) [Ring A] (n m : ℕ) :
    (FGProjectiveCat.IdempotentModel.freeBiprodIso A n m).hom ≫ biprod.fst =
      finiteFreeRowMatrixArrow A (n + m) n (rowLeftProjection A n m) := by
  have hProjection :
      (fun (k : Fin (n + m)) (i : Fin n) =>
        if k = Fin.castAdd m i then (1 : A) else 0) = rowLeftProjection A n m := by
    rfl
  have h := congrArg (fun k => k ≫ biprod.fst)
    ((FGProjectiveCat.IdempotentModel.free_block_characteristic A).1 n m)
  have h0 :
      (FGProjectiveCat.IdempotentModel.freeBiprodIso A n m).hom ≫ biprod.fst =
        finiteFreeRowMatrixArrow A (n + m) n
          (fun k i => if k = Fin.castAdd m i then (1 : A) else 0) :=
    h.trans (biprod.lift_fst _ _)
  exact h0.trans
    (congrArg (finiteFreeRowMatrixArrow A (n + m) n) hProjection)

private theorem freeBiprod_snd_matrix (A : Type uA) [Ring A] (n m : ℕ) :
    (FGProjectiveCat.IdempotentModel.freeBiprodIso A n m).hom ≫ biprod.snd =
      finiteFreeRowMatrixArrow A (n + m) m (rowRightProjection A n m) := by
  have hProjection :
      (fun (k : Fin (n + m)) (j : Fin m) =>
        if k = Fin.natAdd n j then (1 : A) else 0) = rowRightProjection A n m := by
    rfl
  have h := congrArg (fun k => k ≫ biprod.snd)
    ((FGProjectiveCat.IdempotentModel.free_block_characteristic A).1 n m)
  have h0 :
      (FGProjectiveCat.IdempotentModel.freeBiprodIso A n m).hom ≫ biprod.snd =
        finiteFreeRowMatrixArrow A (n + m) m
          (fun k j => if k = Fin.natAdd n j then (1 : A) else 0) :=
    h.trans (biprod.lift_snd _ _)
  exact h0.trans
    (congrArg (finiteFreeRowMatrixArrow A (n + m) m) hProjection)

universe uC' vC' uE vE

private theorem binaryIsoComparison
    {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {C' : Type uC'} [Category.{vC'} C'] [HasZeroMorphisms C'] [HasBinaryBiproducts C']
    {E : Type uE} [Category.{vE} E] [HasZeroMorphisms E]
    (F : C ⥤ E) (G : C' ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    {X Y Z : C} {X' Y' Z' : C'}
    [PreservesBinaryBiproduct X Y F] [PreservesBinaryBiproduct X' Y' G]
    (B : Z ≅ X ⊞ Y) (B' : Z' ≅ X' ⊞ Y')
    (eX : F.obj X ≅ G.obj X') (eY : F.obj Y ≅ G.obj Y') (eZ : F.obj Z ≅ G.obj Z')
    (hX : F.map (B.hom ≫ biprod.fst) ≫ eX.hom =
      eZ.hom ≫ G.map (B'.hom ≫ biprod.fst))
    (hY : F.map (B.hom ≫ biprod.snd) ≫ eY.hom =
      eZ.hom ≫ G.map (B'.hom ≫ biprod.snd)) :
    F.mapIso B ≪≫ F.mapBiprod X Y ≪≫ biprod.mapIso eX eY =
      eZ ≪≫ G.mapIso B' ≪≫ G.mapBiprod X' Y' := by
  apply Iso.ext
  apply biprod.hom_ext
  · have hF : (F.mapBiprod X Y).hom ≫ biprod.fst =
        F.map (biprod.fst : X ⊞ Y ⟶ X) := by
      rw [CategoryTheory.Functor.mapBiprod_hom]
      exact biprod.lift_fst _ _
    have hG : (G.mapBiprod X' Y').hom ≫ biprod.fst =
        G.map (biprod.fst : X' ⊞ Y' ⟶ X') := by
      rw [CategoryTheory.Functor.mapBiprod_hom]
      exact biprod.lift_fst _ _
    have hM : (biprod.mapIso eX eY).hom ≫ biprod.fst =
        biprod.fst ≫ eX.hom :=
      biprod.map_fst eX.hom eY.hom
    have hLeft :
        (F.mapIso B ≪≫ F.mapBiprod X Y ≪≫ biprod.mapIso eX eY).hom ≫ biprod.fst =
          F.map (B.hom ≫ biprod.fst) ≫ eX.hom := by
      calc
        _ = F.map B.hom ≫ ((F.mapBiprod X Y).hom ≫
              ((biprod.mapIso eX eY).hom ≫ biprod.fst)) := by
          simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc]
        _ = F.map B.hom ≫ ((F.mapBiprod X Y).hom ≫
              (biprod.fst ≫ eX.hom)) :=
          congrArg (fun h => F.map B.hom ≫ ((F.mapBiprod X Y).hom ≫ h)) hM
        _ = (F.map B.hom ≫ ((F.mapBiprod X Y).hom ≫ biprod.fst)) ≫ eX.hom := by
          simp only [Category.assoc]
        _ = (F.map B.hom ≫ F.map biprod.fst) ≫ eX.hom :=
          congrArg (fun h => (F.map B.hom ≫ h) ≫ eX.hom) hF
        _ = F.map (B.hom ≫ biprod.fst) ≫ eX.hom :=
          congrArg (fun h => h ≫ eX.hom) (F.map_comp B.hom biprod.fst).symm
    have hRight :
        (eZ ≪≫ G.mapIso B' ≪≫ G.mapBiprod X' Y').hom ≫ biprod.fst =
          eZ.hom ≫ G.map (B'.hom ≫ biprod.fst) := by
      calc
        _ = eZ.hom ≫ (G.map B'.hom ≫ ((G.mapBiprod X' Y').hom ≫ biprod.fst)) := by
          simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc]
        _ = eZ.hom ≫ (G.map B'.hom ≫ G.map biprod.fst) :=
          congrArg (fun h => eZ.hom ≫ (G.map B'.hom ≫ h)) hG
        _ = eZ.hom ≫ G.map (B'.hom ≫ biprod.fst) :=
          congrArg (fun h => eZ.hom ≫ h) (G.map_comp B'.hom biprod.fst).symm
    exact Eq.trans hLeft (Eq.trans hX hRight.symm)
  · have hF : (F.mapBiprod X Y).hom ≫ biprod.snd =
        F.map (biprod.snd : X ⊞ Y ⟶ Y) := by
      rw [CategoryTheory.Functor.mapBiprod_hom]
      exact biprod.lift_snd _ _
    have hG : (G.mapBiprod X' Y').hom ≫ biprod.snd =
        G.map (biprod.snd : X' ⊞ Y' ⟶ Y') := by
      rw [CategoryTheory.Functor.mapBiprod_hom]
      exact biprod.lift_snd _ _
    have hM : (biprod.mapIso eX eY).hom ≫ biprod.snd =
        biprod.snd ≫ eY.hom :=
      biprod.map_snd eX.hom eY.hom
    have hLeft :
        (F.mapIso B ≪≫ F.mapBiprod X Y ≪≫ biprod.mapIso eX eY).hom ≫ biprod.snd =
          F.map (B.hom ≫ biprod.snd) ≫ eY.hom := by
      calc
        _ = F.map B.hom ≫ ((F.mapBiprod X Y).hom ≫
              ((biprod.mapIso eX eY).hom ≫ biprod.snd)) := by
          simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc]
        _ = F.map B.hom ≫ ((F.mapBiprod X Y).hom ≫
              (biprod.snd ≫ eY.hom)) :=
          congrArg (fun h => F.map B.hom ≫ ((F.mapBiprod X Y).hom ≫ h)) hM
        _ = (F.map B.hom ≫ ((F.mapBiprod X Y).hom ≫ biprod.snd)) ≫ eY.hom := by
          simp only [Category.assoc]
        _ = (F.map B.hom ≫ F.map biprod.snd) ≫ eY.hom :=
          congrArg (fun h => (F.map B.hom ≫ h) ≫ eY.hom) hF
        _ = F.map (B.hom ≫ biprod.snd) ≫ eY.hom :=
          congrArg (fun h => h ≫ eY.hom) (F.map_comp B.hom biprod.snd).symm
    have hRight :
        (eZ ≪≫ G.mapIso B' ≪≫ G.mapBiprod X' Y').hom ≫ biprod.snd =
          eZ.hom ≫ G.map (B'.hom ≫ biprod.snd) := by
      calc
        _ = eZ.hom ≫ (G.map B'.hom ≫ ((G.mapBiprod X' Y').hom ≫ biprod.snd)) := by
          simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc]
        _ = eZ.hom ≫ (G.map B'.hom ≫ G.map biprod.snd) :=
          congrArg (fun h => eZ.hom ≫ (G.map B'.hom ≫ h)) hG
        _ = eZ.hom ≫ G.map (B'.hom ≫ biprod.snd) :=
          congrArg (fun h => eZ.hom ≫ h) (G.map_comp B'.hom biprod.snd).symm
    exact Eq.trans hLeft (Eq.trans hY hRight.symm)

/-- The actual row-model biproduct comparison is scalar natural.
Both corners are derived from the original mixed-rank projection matrices. -/
public theorem finiteFreeRowScalarIso_biproduct (f : R →+* S) (n m : ℕ) :
    let FR := (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      FGProjectiveCat.scalarExtension.{uR, uS, uR} f
    let FS := (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse
    letI : PreservesBinaryBiproduct
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj m) FR :=
      preservesBinaryBiproduct_of_preservesBiproduct FR _ _
    letI : PreservesBinaryBiproduct
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj n)
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj m) FS :=
      preservesBinaryBiproduct_of_preservesBiproduct FS _ _
    FR.mapIso (FGProjectiveCat.IdempotentModel.freeBiprodIso R n m) ≪≫
        FR.mapBiprod ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)
          ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj m) ≪≫
        biprod.mapIso (finiteFreeRowScalarIso f n) (finiteFreeRowScalarIso f m) =
      finiteFreeRowScalarIso f (n + m) ≪≫
        FS.mapIso (FGProjectiveCat.IdempotentModel.freeBiprodIso S n m) ≪≫
        FS.mapBiprod ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj n)
          ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj m) := by
  dsimp only
  let FR := (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
    FGProjectiveCat.scalarExtension.{uR, uS, uR} f
  let FS := (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
    (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse
  let : PreservesBinaryBiproduct
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj m) FR :=
    preservesBinaryBiproduct_of_preservesBiproduct FR _ _
  let : PreservesBinaryBiproduct
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj n)
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj m) FS :=
    preservesBinaryBiproduct_of_preservesBiproduct FS _ _
  let BR := FGProjectiveCat.IdempotentModel.freeBiprodIso R n m
  let BS := FGProjectiveCat.IdempotentModel.freeBiprodIso S n m
  have hLeft :
      FR.map (BR.hom ≫ biprod.fst) ≫ (finiteFreeRowScalarIso f n).hom =
        (finiteFreeRowScalarIso f (n + m)).hom ≫ FS.map (BS.hom ≫ biprod.fst) := by
    have hNat :
        FR.map (finiteFreeRowMatrixArrow R (n + m) n (rowLeftProjection R n m)) ≫
            (finiteFreeRowScalarIso f n).hom =
          (finiteFreeRowScalarIso f (n + m)).hom ≫
            FS.map (finiteFreeRowMatrixArrow S (n + m) n
              (Matrix.map (rowLeftProjection R n m) f)) :=
      finiteFreeRowScalarIso_matrix f (n + m) n (rowLeftProjection R n m)
    have hCoeff :
        finiteFreeRowMatrixArrow S (n + m) n (Matrix.map (rowLeftProjection R n m) f) =
          finiteFreeRowMatrixArrow S (n + m) n (rowLeftProjection S n m) :=
      congrArg (finiteFreeRowMatrixArrow S (n + m) n) (scalar_leftProjection f n m)
    have hR := congrArg FR.map (freeBiprod_fst_matrix R n m)
    have hS := congrArg FS.map (freeBiprod_fst_matrix S n m)
    have hM := congrArg FS.map hCoeff
    exact (congrArg (fun h => h ≫ (finiteFreeRowScalarIso f n).hom) hR).trans
      (hNat.trans ((congrArg (fun h => (finiteFreeRowScalarIso f (n + m)).hom ≫ h) hM).trans
        (congrArg (fun h => (finiteFreeRowScalarIso f (n + m)).hom ≫ h) hS).symm))
  have hRight :
      FR.map (BR.hom ≫ biprod.snd) ≫ (finiteFreeRowScalarIso f m).hom =
        (finiteFreeRowScalarIso f (n + m)).hom ≫ FS.map (BS.hom ≫ biprod.snd) := by
    have hNat :
        FR.map (finiteFreeRowMatrixArrow R (n + m) m (rowRightProjection R n m)) ≫
            (finiteFreeRowScalarIso f m).hom =
          (finiteFreeRowScalarIso f (n + m)).hom ≫
            FS.map (finiteFreeRowMatrixArrow S (n + m) m
              (Matrix.map (rowRightProjection R n m) f)) :=
      finiteFreeRowScalarIso_matrix f (n + m) m (rowRightProjection R n m)
    have hCoeff :
        finiteFreeRowMatrixArrow S (n + m) m (Matrix.map (rowRightProjection R n m) f) =
          finiteFreeRowMatrixArrow S (n + m) m (rowRightProjection S n m) :=
      congrArg (finiteFreeRowMatrixArrow S (n + m) m) (scalar_rightProjection f n m)
    have hR := congrArg FR.map (freeBiprod_snd_matrix R n m)
    have hS := congrArg FS.map (freeBiprod_snd_matrix S n m)
    have hM := congrArg FS.map hCoeff
    exact (congrArg (fun h => h ≫ (finiteFreeRowScalarIso f m).hom) hR).trans
      (hNat.trans ((congrArg (fun h => (finiteFreeRowScalarIso f (n + m)).hom ≫ h) hM).trans
        (congrArg (fun h => (finiteFreeRowScalarIso f (n + m)).hom ≫ h) hS).symm))
  exact binaryIsoComparison FR FS BR BS
    (finiteFreeRowScalarIso f n) (finiteFreeRowScalarIso f m)
    (finiteFreeRowScalarIso f (n + m)) hLeft hRight

end AlgebraicKTheory.StableGL
