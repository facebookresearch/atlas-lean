/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricNormalizationHomotopy
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPositiveAlgebra
public import MathlibExt.AlgebraicTopology.DoldKan.HomotopyNaturality
public import MathlibExt.Algebra.Homology.Hochschild.Simplicial

/-!
# Algebra scalars and Hochschild normalization

Algebra scalars act as simplicial coefficient endomorphisms.
The Dold–Kan projector and homotopy are natural under
these endomorphisms, giving their A-linearity after
transport to the coefficient tensor coordinates.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The coefficient scalar on the original raw tensor level. -/
def scalarTensorMap (a : A) (n : ℕ) : Module.End k (M ⊗[k] TensorPower k n A) :=
  TensorProduct.map (Algebra.lsmul k k M a) LinearMap.id

/-- The original tensor scalar map is exactly the original algebra action on every raw chain. -/
theorem scalarTensorMap_apply (a : A) (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    scalarTensorMap k A M a n x = a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m x => rfl
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

omit [SMulCommClass k A M] in
private theorem scalarTensorMap_eq_linearMap (a : A) (n : ℕ) :
    scalarTensorMap k A M a n = ModuleCat.Algebra.Hochschild.linearMap
      (NonUnitalAlgHom.id k A) (Algebra.lsmul k k M a) n := by
  change TensorProduct.map (Algebra.lsmul k k M a) LinearMap.id =
    TensorProduct.map (Algebra.lsmul k k M a)
      (PiTensorProduct.map (fun _ : Fin n => (LinearMap.id : A →ₗ[k] A)))
  rw [PiTensorProduct.map_id]

/-- The original coefficient scalar in coefficient-bar coordinates. -/
def scalarBarMapComponent (a : A) (n : ℕ) :
    (coefficientBar k A M).obj (Opposite.op ⦋n⦌) ⟶
      (coefficientBar k A M).obj (Opposite.op ⦋n⦌) :=
  (coefficientBarObjIso k A M n).hom ≫ ModuleCat.ofHom (scalarTensorMap k A M a n) ≫
    (coefficientBarObjIso k A M n).inv

/-- The coefficient scalar commutes with each original bar face. -/
theorem scalarBarMapComponent_face (a : A) (n : ℕ) (i : Fin (n + 2)) :
    scalarBarMapComponent k A M a (n + 1) ≫ (coefficientBar k A M).δ i =
      (coefficientBar k A M).δ i ≫ scalarBarMapComponent k A M a n := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  have h : ModuleCat.ofHom (scalarTensorMap k A M a (n + 1)) ≫
      ModuleCat.Algebra.Hochschild.face k A M n i =
    ModuleCat.Algebra.Hochschild.face k A M n i ≫
      ModuleCat.ofHom (scalarTensorMap k A M a n) := by
    apply ModuleCat.hom_ext
    simp only [scalarTensorMap_eq_linearMap]
    exact ModuleCat.Algebra.Hochschild.linearMap_face_comm
      (NonUnitalAlgHom.id k A) (Algebra.lsmul k k M a)
      (by intro b m; exact smul_comm a b m)
      (by intro b m; change a • (b • m) = b • (a • m); exact smul_comm a b m) n i
  apply (cancel_epi (coefficientBarObjIso k A M (n + 1)).inv).mp
  apply (cancel_mono (coefficientBarObjIso k A M n).hom).mp
  simpa only [scalarBarMapComponent, coefficientBar, coefficientBarObjIso,
    ModuleCat.Algebra.Hochschild.face, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- The coefficient scalar commutes with each original bar degeneracy. -/
theorem scalarBarMapComponent_degeneracy (a : A) (n : ℕ) (i : Fin (n + 1)) :
    scalarBarMapComponent k A M a n ≫ (coefficientBar k A M).σ i =
      (coefficientBar k A M).σ i ≫ scalarBarMapComponent k A M a (n + 1) := by
  letI := opModule A M
  letI := actionsComm A M
  letI := kOpComm k A M
  letI := kOpTower k A M
  have h : ModuleCat.ofHom (scalarTensorMap k A M a n) ≫
      ModuleCat.Algebra.Hochschild.degeneracy k A M n i =
    ModuleCat.Algebra.Hochschild.degeneracy k A M n i ≫
      ModuleCat.ofHom (scalarTensorMap k A M a (n + 1)) := by
    apply ModuleCat.hom_ext
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m x
    let d : (M ⊗[k] TensorPower k n A) →ₗ[k] M ⊗[k] TensorPower k (n + 1) A :=
      (ModuleCat.Algebra.Hochschild.degeneracy k A M n i).hom
    change d (scalarTensorMap k A M a n (m ⊗ₜ[k] PiTensorProduct.tprod k x)) =
      scalarTensorMap k A M a (n + 1) (d (m ⊗ₜ[k] PiTensorProduct.tprod k x))
    rw [scalarTensorMap_apply]
    have h₁ := ModuleCat.Algebra.Hochschild.degeneracy_tprod k A M n i (a • m) x
    have h₀ := ModuleCat.Algebra.Hochschild.degeneracy_tprod k A M n i m x
    have h₁' : d ((a • m) ⊗ₜ[k] PiTensorProduct.tprod k x) =
        (a • m) ⊗ₜ[k] PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildInsertOne i x) := h₁
    have h₀' : d (m ⊗ₜ[k] PiTensorProduct.tprod k x) =
        m ⊗ₜ[k] PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildInsertOne i x) := h₀
    have hs : scalarTensorMap k A M a (n + 1)
        (m ⊗ₜ[k] PiTensorProduct.tprod k (ModuleCat.Algebra.Hochschild.hochschildInsertOne i x)) =
        (a • m) ⊗ₜ[k] PiTensorProduct.tprod k
          (ModuleCat.Algebra.Hochschild.hochschildInsertOne i x) := by
      rw [scalarTensorMap_apply]
      rfl
    exact h₁'.trans ((congrArg (scalarTensorMap k A M a (n + 1)) h₀').trans hs).symm
  apply (cancel_epi (coefficientBarObjIso k A M n).inv).mp
  apply (cancel_mono (coefficientBarObjIso k A M (n + 1)).hom).mp
  simpa only [scalarBarMapComponent, coefficientBar, coefficientBarObjIso,
    ModuleCat.Algebra.Hochschild.degeneracy, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- The original algebra scalar is a simplicial coefficient endomorphism. -/
def scalarBarMap (a : A) : coefficientBar k A M ⟶ coefficientBar k A M :=
  SimplicialObject.homOfComponents (scalarBarMapComponent k A M a)
    (fun {n} i => scalarBarMapComponent_face k A M a n i)
    (fun {n} i => scalarBarMapComponent_degeneracy k A M a n i)

/-- Its original bar component is the coefficient-first algebra action. -/
theorem scalarBarMap_app (a : A) (n : ℕ) :
    (scalarBarMap k A M a).app (Opposite.op ⦋n⦌) = scalarBarMapComponent k A M a n :=
  SimplicialObject.homOfComponents_app_mk (scalarBarMapComponent k A M a)
    (fun {n} i => scalarBarMapComponent_face k A M a n i)
    (fun {n} i => scalarBarMapComponent_degeneracy k A M a n i) n

/-- The native Dold--Kan projector in the original raw tensor coordinates. -/
def rawNativeNormalizationProjector (n : ℕ) : Module.End k (M ⊗[k] TensorPower k n A) :=
  (coefficientBarObjIso k A M n).hom.hom.comp
    (((AlgebraicTopology.DoldKan.PInfty (X := coefficientBar k A M)).f n).hom.comp
      (coefficientBarObjIso k A M n).inv.hom)

/-- The original normalization homotopy component in original raw tensor coordinates. -/
def rawNativeNormalizationHomotopyComponent (n m : ℕ) :
    M ⊗[k] TensorPower k n A →ₗ[k] M ⊗[k] TensorPower k m A :=
  (coefficientBarObjIso k A M m).hom.hom.comp
    (((AlgebraicTopology.DoldKan.homotopyPInftyToId (coefficientBar k A M)).hom n m).hom.comp
      (coefficientBarObjIso k A M n).inv.hom)

/-- Native projector naturality proves the original projector is actually A-linear. -/
theorem rawNativeNormalizationProjector_smul (n : ℕ) (a : A)
    (x : M ⊗[k] TensorPower k n A) :
    rawNativeNormalizationProjector k A M n (a • x) = a • rawNativeNormalizationProjector k A M n x := by
  have h := AlgebraicTopology.DoldKan.PInfty_f_naturality n (scalarBarMap k A M a)
  rw [scalarBarMap_app] at h
  have hc := congrArg (fun f => (coefficientBarObjIso k A M n).inv ≫ f ≫
    (coefficientBarObjIso k A M n).hom) h
  simp only [scalarBarMapComponent, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] at hc
  have hx := ConcreteCategory.congr_hom hc x
  change rawNativeNormalizationProjector k A M n (scalarTensorMap k A M a n x) =
    scalarTensorMap k A M a n (rawNativeNormalizationProjector k A M n x) at hx
  simpa only [scalarTensorMap_apply] using hx

/-- Native homotopy naturality proves every original homotopy component is actually A-linear. -/
theorem rawNativeNormalizationHomotopyComponent_smul (n m : ℕ) (a : A)
    (x : M ⊗[k] TensorPower k n A) :
    rawNativeNormalizationHomotopyComponent k A M n m (a • x) =
      a • rawNativeNormalizationHomotopyComponent k A M n m x := by
  have h := AlgebraicTopology.DoldKan.homotopyPInftyToId_hom_naturality n m (scalarBarMap k A M a)
  rw [scalarBarMap_app, scalarBarMap_app] at h
  have hc := congrArg (fun f => (coefficientBarObjIso k A M n).inv ≫ f ≫
    (coefficientBarObjIso k A M m).hom) h
  simp only [scalarBarMapComponent, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] at hc
  have hx := ConcreteCategory.congr_hom hc x
  change scalarTensorMap k A M a m (rawNativeNormalizationHomotopyComponent k A M n m x) =
    rawNativeNormalizationHomotopyComponent k A M n m (scalarTensorMap k A M a n x) at hx
  simpa only [scalarTensorMap_apply] using hx.symm

/-- The normalization projector transported as an original raw chain endomorphism. -/
def rawNativeNormalizationProjectorComplex : chainComplex k A M ⟶ chainComplex k A M :=
  (chainComplexIso k A M).hom ≫ AlgebraicTopology.DoldKan.PInfty
    (X := coefficientBar k A M) ≫ (chainComplexIso k A M).inv

omit [SMulCommClass k A M] in
/-- The native raw chain projector has the original tensor-level projector. -/
theorem rawNativeNormalizationProjectorComplex_f (n : ℕ) :
    ((rawNativeNormalizationProjectorComplex k A M).f n).hom =
      rawNativeNormalizationProjector k A M n := rfl

/-- The native Dold--Kan homotopy transported through the raw/bar coordinates. -/
def rawNativeNormalizationHomotopy :
    Homotopy (rawNativeNormalizationProjectorComplex k A M) (𝟙 (chainComplex k A M)) := by
  let c := chainComplexIso k A M
  let h := ((AlgebraicTopology.DoldKan.homotopyPInftyToId (coefficientBar k A M)).compRightId c.inv).compLeft c.hom
  exact h.trans (Homotopy.ofEq c.hom_inv_id)

omit [SMulCommClass k A M] in
/-- The transported native homotopy has the original tensor-level homotopy component. -/
theorem rawNativeNormalizationHomotopy_hom (n m : ℕ) :
    ((rawNativeNormalizationHomotopy k A M).hom n m).hom =
      rawNativeNormalizationHomotopyComponent k A M n m := by
  simp only [rawNativeNormalizationHomotopy, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Homotopy.compLeft_hom, Homotopy.compRightId_hom,
    Pi.zero_apply, add_zero]
  rfl

end ModuleCat.Algebra.Hochschild.Symmetric
