/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.PointComponentHom
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeLoopShift
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSphereOne
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom
import MathlibExt.CategoryTheory.Monoidal.TensorPowers
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.Evaluation

/-!
# Actual sphere representatives of native cube homotopy

Iterate the original one-sphere suspension-loop Quillen adjunction with
its actual units, counits, and maps. Combine its localized Hom functions
with the native loop/cube comparison and the actual point-component Hom
equivalence. The canonical sphere comparison retains the original
freely based point, finite tensor powers, associators, and unitors.
Both correspondence directions preserve every original target map.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.SphereHom
attribute [local instance] PointedCGWH.modelCategory.allObjectsFibrant

/-- Actual iterated one-sphere suspension with its unchanged maps. -/
def sphereTensorPower : ℕ → PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  Nat.rec (𝟭 _) (fun _ previous => PointedCGWH.suspension ⋙ previous)

/-- The entire structural zero suspension iterate is the original identity functor. -/
theorem sphereTensorPowerZero : sphereTensorPower.{u, v} 0 = 𝟭 _ := rfl

/-- The original whole successor retains suspension followed by the actual preceding power. -/
theorem sphereTensorPowerSucc (n : ℕ) :
    sphereTensorPower.{u, v} (n + 1) = PointedCGWH.suspension ⋙ sphereTensorPower n := rfl

/-- Actual ordered native loop iteration with every original map. -/
abbrev loopPower (n : ℕ) : PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n

/-- The actual composed adjunction preserves all original units and counits. -/
def powerAdjunction : ∀ n : ℕ, sphereTensorPower.{u, v} n ⊣ loopPower n :=
  Nat.rec (motive := fun n => sphereTensorPower.{u, v} n ⊣ loopPower n)
    Adjunction.id
    (fun _ previous => PointedCGWH.suspensionLoopAdjunction.comp previous)

/-- The entire structural zero adjunction is the original identity, with its units and counits. -/
theorem powerAdjunctionZero :
    powerAdjunction.{u, v} 0 = Adjunction.id (C := PointedCGWH.{u, v}) := rfl

/-- The entire structural successor adjunction retains the original two Hom functions. -/
theorem powerAdjunctionSucc (n : ℕ) :
    powerAdjunction.{u, v} (n + 1) =
      PointedCGWH.suspensionLoopAdjunction.comp (powerAdjunction n) := rfl

instance powerAdjunction_quillen (n : ℕ) : (powerAdjunction.{u, v} n).IsQuillenAdjunction := by
  induction n with
  | zero =>
    change (Adjunction.id (C := PointedCGWH.{u, v})).IsQuillenAdjunction
    infer_instance
  | succ n ih =>
    let _ : (powerAdjunction n).IsQuillenAdjunction := ih
    change (PointedCGWH.suspensionLoopAdjunction.comp (powerAdjunction n)).IsQuillenAdjunction
    infer_instance

/-- Every actual cube degree has the full original ordered native-loop comparison. -/
def loopPowerPiShift : ∀ n k : ℕ,
    loopPower.{u, v} n ⋙ PointedCGWH.piNFunctor k ≅ PointedCGWH.piNFunctor (k + n) :=
  Nat.rec
    (motive := fun n => ∀ k : ℕ,
      loopPower.{u, v} n ⋙ PointedCGWH.piNFunctor k ≅ PointedCGWH.piNFunctor (k + n))
    (fun k => (PointedCGWH.piNFunctor k).leftUnitor)
    (fun n previous k =>
      Functor.associator (loopPower n) PointedCGWH.loop (PointedCGWH.piNFunctor k) ≪≫
        Functor.isoWhiskerLeft (loopPower n)
          (PointedCGWH.NativeLoopShiftGeometry.nativeLoopPiShiftNatIso k) ≪≫
        previous (k + 1) ≪≫
        eqToIso (congrArg PointedCGWH.piNFunctor
          (show k + 1 + n = k + (n + 1) by omega)))

/-- The entire structural successor retains every original comparison map and arithmetic cast. -/
theorem loopPowerPiShiftSucc (n k : ℕ) :
    loopPowerPiShift.{u, v} (n + 1) k =
      Functor.associator (loopPower n) PointedCGWH.loop (PointedCGWH.piNFunctor k) ≪≫
        Functor.isoWhiskerLeft (loopPower n)
          (PointedCGWH.NativeLoopShiftGeometry.nativeLoopPiShiftNatIso k) ≪≫
        loopPowerPiShift n (k + 1) ≪≫
        eqToIso (congrArg PointedCGWH.piNFunctor
          (show k + 1 + n = k + (n + 1) by omega)) := rfl

/-- The original whole zero pi shift is the actual homotopy-functor left unitor. -/
theorem loopPowerPiShiftZero (k : ℕ) :
    loopPowerPiShift.{u, v} 0 k = (PointedCGWH.piNFunctor k).leftUnitor := rfl

/-- The original freely pointed unit is retained as the zero-dimensional source. -/
abbrev freePoint : PointedCGWH.{u, v} := (Under.costar CGWH.point).obj CGWH.point

/-- Actual sphere sources are the iterated scalar suspension of the original free point. -/
def sphere (n : ℕ) : PointedCGWH.{u, v} := (sphereTensorPower n).obj freePoint

/-- The actual original power adjunction supplies both full localized Hom functions. -/
def sphereHoHomEquiv (n : ℕ) (X : PointedCGWH.{u, v}) :
    ((toHomotopyCategory PointedCGWH).obj (sphere n) ⟶
      (toHomotopyCategory PointedCGWH).obj X) ≃
    ((toHomotopyCategory PointedCGWH).obj freePoint ⟶
      (toHomotopyCategory PointedCGWH).obj ((loopPower n).obj X)) := by
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  letI : IsCofibrant freePoint.{u, v} :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
  exact QuillenOrdinaryHoHom.homEquiv (powerAdjunction n) freePoint X

/-- The full power Hom correspondence retains each original target-map square. -/
theorem sphereHoHomEquiv_naturality (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y)
    (g : (toHomotopyCategory PointedCGWH).obj (sphere n) ⟶
      (toHomotopyCategory PointedCGWH).obj X) :
    sphereHoHomEquiv n Y (g ≫ (toHomotopyCategory PointedCGWH).map f) =
      sphereHoHomEquiv n X g ≫ (toHomotopyCategory PointedCGWH).map ((loopPower n).map f) := by
  let _ : (Under.costarAdjForget CGWH.point.{u, v}).IsQuillenAdjunction :=
    Under.costarAdjForget_isQuillenAdjunction CGWH.point
  let _ : IsCofibrant freePoint.{u, v} :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.costarAdjForget CGWH.point) CGWH.point_isCofibrant
  exact QuillenOrdinaryHoHom.homEquiv_naturality_right (powerAdjunction n) freePoint g f

/-- Both whole inverse power Hom functions retain the original target map. -/
theorem sphereHoHomEquiv_inverse_naturality (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y)
    (g : (toHomotopyCategory PointedCGWH).obj freePoint ⟶
      (toHomotopyCategory PointedCGWH).obj ((loopPower n).obj X)) :
    (sphereHoHomEquiv n Y).symm
        (g ≫ (toHomotopyCategory PointedCGWH).map ((loopPower n).map f)) =
      (sphereHoHomEquiv n X).symm g ≫ (toHomotopyCategory PointedCGWH).map f := by
  apply (sphereHoHomEquiv n Y).injective
  rw [Equiv.apply_symm_apply, sphereHoHomEquiv_naturality, Equiv.apply_symm_apply]

/-- The exact full ordered-loop shift in target degree zero. -/
def zeroLoopPowerPiShift (n : ℕ) (X : PointedCGWH.{u, v}) :
    PointedCGWH.piN 0 ((loopPower n).obj X) ≃ PointedCGWH.piN n X :=
  ((loopPowerPiShift n 0).app X).toEquiv.trans
    (Equiv.cast (congrArg (fun k => PointedCGWH.piN k X) (Nat.zero_add n)))

/-- Every original cube class corresponds to an actual localized sphere map. -/
def spherePiHomEquiv (n : ℕ) (X : PointedCGWH.{u, v}) :
    PointedCGWH.piN n X ≃
    ((toHomotopyCategory PointedCGWH).obj (sphere n) ⟶
      (toHomotopyCategory PointedCGWH).obj X) :=
  (zeroLoopPowerPiShift n X).symm.trans
    ((PointedCGWH.piNZeroEquivPiZero ((loopPower n).obj X)).trans
      ((PointedCGWH.PointComponentHom.pointedPointClassHomEquiv ((loopPower n).obj X)).trans
        (sphereHoHomEquiv n X).symm))

/-- Every original pointed arrow retains the complete zero-loop shift naturality. -/
theorem zeroLoopPowerPiShift_naturality (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) (x : PointedCGWH.piN 0 ((loopPower n).obj X)) :
    zeroLoopPowerPiShift n Y (PointedCGWH.piNMap 0 ((loopPower n).map f) x) =
      PointedCGWH.piNMap n f (zeroLoopPowerPiShift n X x) := by
  have h := ConcreteCategory.congr_hom ((loopPowerPiShift n 0).hom.naturality f) x
  change ((loopPowerPiShift n 0).app Y).toEquiv
      (PointedCGWH.piNMap 0 ((loopPower n).map f) x) =
    PointedCGWH.piNMap (0 + n) f (((loopPowerPiShift n 0).app X).toEquiv x) at h
  have hcast := congrArg
    (Equiv.cast (congrArg (fun k => PointedCGWH.piN k Y) (Nat.zero_add n))) h
  have castMap {a b : ℕ} (hab : a = b) (z : PointedCGWH.piN a X) :
      (Equiv.cast (congrArg (fun k => PointedCGWH.piN k Y) hab))
          (PointedCGWH.piNMap a f z) =
        PointedCGWH.piNMap b f
          ((Equiv.cast (congrArg (fun k => PointedCGWH.piN k X) hab)) z) := by
    cases hab
    rfl
  exact hcast.trans (castMap (Nat.zero_add n) (((loopPowerPiShift n 0).app X).toEquiv x))

/-- The complete sphere representation commutes with every original target map. -/
theorem spherePiHomEquiv_naturality (n : ℕ) {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) (x : PointedCGWH.piN n X) :
    spherePiHomEquiv n Y (PointedCGWH.piNMap n f x) =
      spherePiHomEquiv n X x ≫ (toHomotopyCategory PointedCGWH).map f := by
  obtain ⟨z, rfl⟩ := (zeroLoopPowerPiShift n X).surjective x
  have hz := zeroLoopPowerPiShift_naturality n f z
  rw [← hz]
  simp only [spherePiHomEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  change (sphereHoHomEquiv n Y).symm
      (PointedCGWH.PointComponentHom.pointedPointClassHomEquiv ((loopPower n).obj Y)
        (PointedCGWH.piNZeroEquivPiZero ((loopPower n).obj Y)
          (PointedCGWH.piNMap 0 ((loopPower n).map f) z))) = _
  rw [PointedCGWH.piNZeroEquivPiZero_naturality,
    PointedCGWH.PointComponentHom.pointedPointClassHomEquiv_naturality,
    sphereHoHomEquiv_inverse_naturality]


/-- The original free-point source is canonically the native smash unit. -/
def freePointUnitIso : freePoint.{u, v} ≅ 𝟙_ PointedCGWH.{u, v} := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let e : CGWH.point.{u, v} ≅ 𝟙_ CGWH :=
    CGWH.point_isTerminal.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
  exact (Under.costar CGWH.point).mapIso e ≪≫
    (CategoryTheory.Pointed.costarCoreMonoidal CGWH.point CGWH.point_isTerminal).εIso.symm


/-- The actual ordered suspension iterate is the left-associated finite sphere power. -/
def spherePowerValueIso : ∀ (n : ℕ) (X : PointedCGWH.{u, v}),
    (sphereTensorPower n).obj X ≅
      MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n ⊗ X :=
  Nat.rec
    (motive := fun n => ∀ X : PointedCGWH.{u, v},
      (sphereTensorPower n).obj X ≅
        MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n ⊗ X)
    (fun X => (λ_ X).symm)
    (fun n previous X => previous (PointedCGWH.suspension.obj X) ≪≫
      (α_ (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n)
        PointedCGWH.sphereOne X).symm)

/-- Both original zero value-comparison maps retain the inverse left unitor. -/
theorem spherePowerValueIsoZero (X : PointedCGWH.{u, v}) :
    spherePowerValueIso.{u, v} 0 X = (λ_ X).symm := rfl

/-- Both original successor value-comparison maps retain suspension and the actual associator. -/
theorem spherePowerValueIsoSucc (n : ℕ) (X : PointedCGWH.{u, v}) :
    spherePowerValueIso.{u, v} (n + 1) X =
      spherePowerValueIso n (PointedCGWH.suspension.obj X) ≪≫
        (α_ (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n)
          PointedCGWH.sphereOne X).symm := rfl

/-- Both source-sphere functions retain the original free-point and canonical unit comparisons. -/
def sphereCanonicalIso (n : ℕ) :
    sphere.{u, v} n ≅ MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n :=
  spherePowerValueIso n freePoint ≪≫
    tensorIso (Iso.refl _) freePointUnitIso ≪≫
    ρ_ (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n)

/-- The canonical sphere-Hom correspondence uses both actual source isomorphism maps. -/
def canonicalSpherePiHomEquiv (n : ℕ) (X : PointedCGWH.{u, v}) :
    PointedCGWH.piN n X ≃
    ((toHomotopyCategory PointedCGWH).obj
       (MonoidalCategory.TensorPower.tensorPowObj PointedCGWH.sphereOne n) ⟶
      (toHomotopyCategory PointedCGWH).obj X) :=
  (spherePiHomEquiv n X).trans
    (((toHomotopyCategory PointedCGWH).mapIso (sphereCanonicalIso n)).homCongr (Iso.refl _))

end PointedCGWH.SphereHom
