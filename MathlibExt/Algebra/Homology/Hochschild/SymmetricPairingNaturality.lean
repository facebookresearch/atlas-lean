/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricNaturality
public import MathlibExt.AlgebraicTopology.SimplicialObject.HomOfComponents
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality

/-!
# Naturality of symmetric shuffle pairings

Unit-preserving algebra maps and compatible coefficient
maps induce simplicial maps of coefficient bars.
Their shuffle pairings and normalization maps are natural.
Source and target algebra universes are independent;
coefficients use an explicit common lifted category.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory Opposite
open scoped TensorProduct Simplicial MonoidalCategory

universe u v v' z

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable {k : Type u} [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A]
  {B : Type v'} [CommRing B] [Algebra k B]
  {M N : Type (max u v v' z)} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module B N]
  [IsScalarTower k A M] [IsScalarTower k B N]

/-- The coefficient/algebra map in native coefficient-bar coordinates. -/
def coefficientBarMapComponent (g : A →ₐ[k] B) (f : M →ₗ[k] N) (n : ℕ) :
    (coefficientBar.{u, v, max u v v' z} k A M).obj (op ⦋n⦌) ⟶
      (coefficientBar.{u, v', max u v v' z} k B N).obj (op ⦋n⦌) :=
  (coefficientBarObjIso.{u, v, max u v v' z} k A M n).hom ≫
    ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) ≫
      (coefficientBarObjIso.{u, v', max u v v' z} k B N n).inv

/-- Every face square is from the original action square. -/
theorem coefficientBarMapComponent_face (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) (i : Fin (n + 2)) :
    coefficientBarMapComponent.{u, v, v', z} g f (n + 1) ≫ (coefficientBar.{u, v', max u v v' z} k B N).δ i =
      (coefficientBar.{u, v, max u v v' z} k A M).δ i ≫ coefficientBarMapComponent.{u, v, v', z} g f n := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  have h : ModuleCat.ofHom
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f (n + 1)) ≫
      rawFace k B N n i = rawFace k A M n i ≫ ModuleCat.ofHom
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) :=
    ModuleCat.hom_ext (ModuleCat.Algebra.Hochschild.linearMap_face_comm
      g.toNonUnitalAlgHom f hf (rightAction_compatibility g.toNonUnitalAlgHom f hf) n i)
  apply (cancel_epi (coefficientBarObjIso.{u, v, max u v v' z} k A M (n + 1)).inv).1
  apply (cancel_mono (coefficientBarObjIso.{u, v', max u v v' z} k B N n).hom).1
  simpa only [coefficientBarMapComponent, rawFace, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

private theorem linearMap_degeneracy_comm (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (n : ℕ) (i : Fin (n + 1)) :
    letI := opModule A M
    letI := actionsComm A M
    letI := kOpComm k A M
    letI := kOpTower k A M
    letI := opModule B N
    letI := actionsComm B N
    letI := kOpComm k B N
    letI := kOpTower k B N
    (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f (n + 1)).comp
        (ModuleCat.Algebra.Hochschild.degeneracy k A M n i).hom =
      (ModuleCat.Algebra.Hochschild.degeneracy k B N n i).hom.comp
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.comp_apply]
  rw [ModuleCat.Algebra.Hochschild.degeneracy_tprod,
    ModuleCat.Algebra.Hochschild.linearMap_tprod,
    ModuleCat.Algebra.Hochschild.linearMap_tprod,
    ModuleCat.Algebra.Hochschild.degeneracy_tprod]
  apply congrArg (fun t : TensorPower k (n + 1) B => f m ⊗ₜ[k] t)
  apply congrArg (PiTensorProduct.tprod k)
  funext j
  change g (Fin.insertNth (α := fun _ : Fin (n + 1) => A) i (1 : A) a j) =
    Fin.insertNth (α := fun _ : Fin (n + 1) => B) i (1 : B)
      (fun l : Fin n => g (a l)) j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simp only [Fin.insertNth_apply_same, map_one]
  · simp only [Fin.insertNth_apply_succAbove]

/-- Unit preservation gives every coefficient-bar degeneracy square. -/
theorem coefficientBarMapComponent_degeneracy (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (n : ℕ) (i : Fin (n + 1)) :
    coefficientBarMapComponent.{u, v, v', z} g f n ≫ (coefficientBar.{u, v', max u v v' z} k B N).σ i =
      (coefficientBar.{u, v, max u v v' z} k A M).σ i ≫ coefficientBarMapComponent.{u, v, v', z} g f (n + 1) := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  have h : ModuleCat.ofHom
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) ≫
      ModuleCat.Algebra.Hochschild.degeneracy k B N n i =
    ModuleCat.Algebra.Hochschild.degeneracy k A M n i ≫ ModuleCat.ofHom
      (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f (n + 1)) :=
    ModuleCat.hom_ext (linearMap_degeneracy_comm.{u, v, v', z} g f n i).symm
  apply (cancel_epi (coefficientBarObjIso.{u, v, max u v v' z} k A M n).inv).1
  apply (cancel_mono (coefficientBarObjIso.{u, v', max u v v' z} k B N (n + 1)).hom).1
  simpa only [coefficientBarMapComponent, ModuleCat.Algebra.Hochschild.degeneracy,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id, coefficientBar, coefficientBarObjIso] using h

/-- The simplicial map of coefficient bars, constructed from
the proved face and degeneracy squares. -/
def coefficientBarMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    coefficientBar.{u, v, max u v v' z} k A M ⟶ coefficientBar.{u, v', max u v v' z} k B N :=
  SimplicialObject.homOfComponents (coefficientBarMapComponent.{u, v, v', z} g f)
    (fun {n} i => coefficientBarMapComponent_face.{u, v, v', z} g f hf n i)
    (fun {n} i => coefficientBarMapComponent_degeneracy.{u, v, v', z} g f n i)

/-- The new simplicial map preserves its original coefficient-first degree formula. -/
@[simp]
theorem coefficientBarMap_app_mk (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    (coefficientBarMap.{u, v, v', z} g f hf).app (op ⦋n⦌) = coefficientBarMapComponent.{u, v, v', z} g f n :=
  SimplicialObject.homOfComponents_app_mk (coefficientBarMapComponent.{u, v, v', z} g f)
    (fun {n} i => coefficientBarMapComponent_face.{u, v, v', z} g f hf n i)
    (fun {n} i => coefficientBarMapComponent_degeneracy.{u, v, v', z} g f n i) n

/-- The general raw chain-map provider specialized to symmetric coefficients.
The right-action square is from the original left-action square. -/
def coefficientChainMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) : chainComplex k A M ⟶ chainComplex k B N := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  exact ModuleCat.Algebra.Hochschild.map.{u, v, v', z} g.toNonUnitalAlgHom f hf
    (rightAction_compatibility g.toNonUnitalAlgHom f hf)

/-- The chain map has the native tensor-map components. -/
@[simp]
theorem coefficientChainMap_f (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) (n : ℕ) :
    (coefficientChainMap.{u, v, v', z} g f hf).f n =
      ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) := by
  rfl

/-- The raw/bar dictionaries commute with the parameter map. -/
@[reassoc]
theorem coefficientChainMap_comp_chainComplexIso (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    coefficientChainMap.{u, v, v', z} g f hf ≫ (chainComplexIso.{u, v', max u v v' z} k B N).hom =
      (chainComplexIso.{u, v, max u v v' z} k A M).hom ≫
        (AlgebraicTopology.alternatingFaceMapComplex _).map (coefficientBarMap.{u, v, v', z} g f hf) := by
  apply HomologicalComplex.hom_ext
  intro n
  change (coefficientChainMap.{u, v, v', z} g f hf).f n ≫ (coefficientBarObjIso.{u, v', max u v v' z} k B N n).inv =
    (coefficientBarObjIso.{u, v, max u v v' z} k A M n).inv ≫ (coefficientBarMap.{u, v, v', z} g f hf).app (op ⦋n⦌)
  rw [coefficientChainMap_f.{u, v, v', z}, coefficientBarMap_app_mk.{u, v, v', z}]
  change ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) ≫
      (coefficientBarObjIso.{u, v', max u v v' z} k B N n).inv =
    (coefficientBarObjIso.{u, v, max u v v' z} k A M n).inv ≫
      (coefficientBarObjIso.{u, v, max u v v' z} k A M n).hom ≫
        ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) ≫
          (coefficientBarObjIso.{u, v', max u v v' z} k B N n).inv
  exact ((coefficientBarObjIso.{u, v, max u v v' z} k A M n).inv_hom_id_assoc
    (ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) ≫
      (coefficientBarObjIso.{u, v', max u v v' z} k B N n).inv)).symm

/-- The normalized parameter map, using the original native
normalization quotient and its coordinate isomorphisms. -/
def normalizedCoefficientMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    normalizedChainComplex k A M ⟶ normalizedChainComplex k B N := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  exact (ModuleCat.Algebra.Hochschild.normalizationIso k A M).inv ≫
    AlgebraicTopology.NormalizedQuotient.map (coefficientBarMap.{u, v, v', z} g f hf) ≫
      (ModuleCat.Algebra.Hochschild.normalizationIso k B N).hom

/-- Original normalization projections commute with the parameter maps. -/
@[reassoc]
theorem normalizationProjection_coefficientMap (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
    normalizationProjection.{u, v, max u v v' z} k A M ≫ normalizedCoefficientMap.{u, v, v', z} g f hf =
      coefficientChainMap.{u, v, v', z} g f hf ≫ normalizationProjection.{u, v', max u v v' z} k B N := by
  let := opModule A M
  let := actionsComm A M
  let := kOpComm k A M
  let := kOpTower k A M
  let := opModule B N
  let := actionsComm B N
  let := kOpComm k B N
  let := kOpTower k B N
  let F := AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v v' z} k)
  let X : SimplicialObject (ModuleCat.{max u v v' z} k) :=
    coefficientBar.{u, v, max u v v' z} k A M
  let Y : SimplicialObject (ModuleCat.{max u v v' z} k) :=
    coefficientBar.{u, v', max u v v' z} k B N
  let cA : chainComplex k A M ≅ F.obj X :=
    chainComplexIso.{u, v, max u v v' z} k A M
  let cB : chainComplex k B N ≅ F.obj Y :=
    chainComplexIso.{u, v', max u v v' z} k B N
  let eA : AlgebraicTopology.NormalizedQuotient.obj X ≅ normalizedChainComplex k A M :=
    ModuleCat.Algebra.Hochschild.normalizationIso.{u, v, max u v v' z} k A M
  let eB : AlgebraicTopology.NormalizedQuotient.obj Y ≅ normalizedChainComplex k B N :=
    ModuleCat.Algebra.Hochschild.normalizationIso.{u, v', max u v v' z} k B N
  let pA := AlgebraicTopology.NormalizedQuotient.projection X
  let pB := AlgebraicTopology.NormalizedQuotient.projection Y
  let b : X ⟶ Y := coefficientBarMap.{u, v, v', z} g f hf
  let q := AlgebraicTopology.NormalizedQuotient.map b
  have hνA : normalizationProjection.{u, v, max u v v' z} k A M = (cA.hom ≫ pA) ≫ eA.hom := by rfl
  have hνB : normalizationProjection.{u, v', max u v v' z} k B N = (cB.hom ≫ pB) ≫ eB.hom := by rfl
  have hq : normalizedCoefficientMap.{u, v, v', z} g f hf = eA.inv ≫ q ≫ eB.hom := by rfl
  have hp : pA ≫ q = F.map b ≫ pB :=
    AlgebraicTopology.NormalizedQuotient.projection_map b
  have hc : coefficientChainMap.{u, v, v', z} g f hf ≫ cB.hom = cA.hom ≫ F.map b :=
    coefficientChainMap_comp_chainComplexIso.{u, v, v', z} g f hf
  rw [hνA, hq, hνB]
  calc
    ((cA.hom ≫ pA) ≫ eA.hom) ≫ (eA.inv ≫ q ≫ eB.hom) =
        cA.hom ≫ (pA ≫ q) ≫ eB.hom := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = cA.hom ≫ (F.map b ≫ pB) ≫ eB.hom := by rw [hp]
    _ = (cA.hom ≫ F.map b) ≫ pB ≫ eB.hom := by simp only [Category.assoc]
    _ = (coefficientChainMap.{u, v, v', z} g f hf ≫ cB.hom) ≫ pB ≫ eB.hom := by rw [hc]
    _ = coefficientChainMap.{u, v, v', z} g f hf ≫ ((cB.hom ≫ pB) ≫ eB.hom) := by
      simp only [Category.assoc]

/-- The diagonal chain maps commute with the coefficient and
algebra simplicial maps. The square is proved from the original tensor
representatives, not supplied as a hypothesis. -/
@[reassoc]
theorem diagonalChainMap_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  (AlgebraicTopology.alternatingFaceMapComplex _).map
      (coefficientBarMap.{u, v, v', z} g
        (regularCoefficientMap g.toNonUnitalAlgHom :
          ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
        (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom) ⊗ₘ coefficientBarMap.{u, v, v', z} g f hf) ≫
    diagonalChainMap.{u, v', max u v v' z} k B N =
  diagonalChainMap.{u, v, max u v v' z} k A M ≫ coefficientChainMap.{u, v, v', z} g f hf := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, coefficientChainMap_f.{u, v, v', z}]
  change ((coefficientBarMap.{u, v, v', z} g
      (regularCoefficientMap g.toNonUnitalAlgHom :
        ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
      (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom)).app (op ⦋n⦌) ⊗ₘ
      (coefficientBarMap.{u, v, v', z} g f hf).app (op ⦋n⦌)) ≫ diagonalComponent.{u, v', max u v v' z} k B N n =
    diagonalComponent.{u, v, max u v v' z} k A M n ≫ ModuleCat.ofHom
      (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n)
  have h :
      (ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom
        (regularCoefficientMap g.toNonUnitalAlgHom :
          ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B) n) ⊗ₘ
      ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n)) ≫
        ModuleCat.ofHom (diagonalRaw.{u, v', max u v v' z} k B N n) =
      ModuleCat.ofHom (diagonalRaw.{u, v, max u v v' z} k A M n) ≫ ModuleCat.ofHom
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n) :=
    by
      apply ModuleCat.hom_ext
      change (diagonalRaw.{u, v', max u v v' z} k B N n).comp
          (TensorProduct.map
            (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom
              (regularCoefficientMap g.toNonUnitalAlgHom :
                ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B) n)
            (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n)) =
        (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n).comp
          (diagonalRaw.{u, v, max u v v' z} k A M n)
      exact (diagonalRaw_naturality g.toNonUnitalAlgHom f hf n).symm
  have paste
      {X₁ X₂ Y₁ Y₂ R₁ R₂ L₁ L₂ T T' : ModuleCat.{max u v v' z} k}
      (a : X₁ ≅ R₁) (b : X₂ ≅ R₂) (c : Y₁ ≅ L₁) (d : Y₂ ≅ L₂)
      (r : R₁ ⟶ L₁) (s : R₂ ⟶ L₂) (δ : R₁ ⊗ R₂ ⟶ T) (ε : L₁ ⊗ L₂ ⟶ T')
      (t : T ⟶ T') (hδ : (r ⊗ₘ s) ≫ ε = δ ≫ t) :
      ((a.hom ≫ r ≫ c.inv) ⊗ₘ (b.hom ≫ s ≫ d.inv)) ≫ ((c.hom ⊗ₘ d.hom) ≫ ε) =
        ((a.hom ⊗ₘ b.hom) ≫ δ) ≫ t := by
    calc
      _ = (((a.hom ≫ r ≫ c.inv) ≫ c.hom) ⊗ₘ
          ((b.hom ≫ s ≫ d.inv) ≫ d.hom)) ≫ ε := by
        rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
      _ = ((a.hom ≫ r) ⊗ₘ (b.hom ≫ s)) ≫ ε := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = (a.hom ⊗ₘ b.hom) ≫ ((r ⊗ₘ s) ≫ ε) := by
        rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
      _ = _ := by rw [hδ, Category.assoc]
  simp only [coefficientBarMap, SimplicialObject.homOfComponents_app_mk,
    coefficientBarMapComponent]
  exact paste
    (coefficientBarObjIso k A (ULift.{max u v v' z} A) n)
    (coefficientBarObjIso.{u, v, max u v v' z} k A M n)
    (coefficientBarObjIso k B (ULift.{max u v v' z} B) n)
    (coefficientBarObjIso.{u, v', max u v v' z} k B N n)
    (ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom
      (regularCoefficientMap g.toNonUnitalAlgHom :
        ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B) n))
    (ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n))
    (ModuleCat.ofHom (diagonalRaw.{u, v, max u v v' z} k A M n))
    (ModuleCat.ofHom (diagonalRaw.{u, v', max u v v' z} k B N n))
    (ModuleCat.ofHom (ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom f n)) h

/-- The raw symmetric shuffle is natural in the original coefficient
and algebra maps. Only the module-action compatibility premise is used. -/
@[reassoc]
theorem pairing_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  HomologicalComplex.tensorHom
      (coefficientChainMap.{u, v, v', z} g
        (regularCoefficientMap g.toNonUnitalAlgHom :
          ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
        (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom)) (coefficientChainMap.{u, v, v', z} g f hf) ≫
    pairing.{u, v', max u v v' z} k B N =
      pairing.{u, v, max u v v' z} k A M ≫ coefficientChainMap.{u, v, v', z} g f hf := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  let r : ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B :=
    regularCoefficientMap g.toNonUnitalAlgHom
  let hr := regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom
  let fR := coefficientChainMap.{u, v, v', z} g r hr
  let fM := coefficientChainMap.{u, v, v', z} g f hf
  let bR := coefficientBarMap.{u, v, v', z} g r hr
  let bM := coefficientBarMap.{u, v, v', z} g f hf
  let F := AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v v' z} k)
  let cR := chainComplexIso.{u, v, max u v v' z} k A (ULift.{max u v v' z} A)
  let cM := chainComplexIso.{u, v, max u v v' z} k A M
  let dR := chainComplexIso.{u, v', max u v v' z} k B (ULift.{max u v v' z} B)
  let dM := chainComplexIso.{u, v', max u v v' z} k B N
  have hR : fR ≫ dR.hom = cR.hom ≫ F.map bR :=
    coefficientChainMap_comp_chainComplexIso.{u, v, v', z} g r hr
  have hM : fM ≫ dM.hom = cM.hom ≫ F.map bM :=
    coefficientChainMap_comp_chainComplexIso.{u, v, v', z} g f hf
  have hShuffle : HomologicalComplex.tensorHom (F.map bR) (F.map bM) ≫
      AlgebraicTopology.EilenbergZilber.alternatingPairing
        (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
          (coefficientBar.{u, v', max u v v' z} k B N) =
    AlgebraicTopology.EilenbergZilber.alternatingPairing
      (coefficientBar.{u, v, max u v v' z} k A (ULift.{max u v v' z} A)) (coefficientBar.{u, v, max u v v' z} k A M) ≫
        F.map (bR ⊗ₘ bM) :=
    AlgebraicTopology.EilenbergZilber.alternatingPairing_naturality bR bM
  have hDiagonal : F.map (bR ⊗ₘ bM) ≫ diagonalChainMap.{u, v', max u v v' z} k B N =
      diagonalChainMap.{u, v, max u v v' z} k A M ≫ fM := diagonalChainMap_naturality.{u, v, v', z} g f hf
  change HomologicalComplex.tensorHom fR fM ≫
      (HomologicalComplex.tensorHom dR.hom dM.hom ≫
        AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
            (coefficientBar.{u, v', max u v v' z} k B N) ≫
            diagonalChainMap.{u, v', max u v v' z} k B N) =
    (HomologicalComplex.tensorHom cR.hom cM.hom ≫
      AlgebraicTopology.EilenbergZilber.alternatingPairing
        (coefficientBar.{u, v, max u v v' z} k A (ULift.{max u v v' z} A)) (coefficientBar.{u, v, max u v v' z} k A M) ≫
          diagonalChainMap.{u, v, max u v v' z} k A M) ≫ fM
  calc
    _ = (HomologicalComplex.tensorHom fR fM ≫
        HomologicalComplex.tensorHom dR.hom dM.hom) ≫
        AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
            (coefficientBar.{u, v', max u v v' z} k B N) ≫
            diagonalChainMap.{u, v', max u v v' z} k B N := by simp only [Category.assoc]
    _ = HomologicalComplex.tensorHom (fR ≫ dR.hom) (fM ≫ dM.hom) ≫
        AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
            (coefficientBar.{u, v', max u v v' z} k B N) ≫
            diagonalChainMap.{u, v', max u v v' z} k B N := by rw [HomologicalComplex.tensorHom_comp_tensorHom]
    _ = HomologicalComplex.tensorHom (cR.hom ≫ F.map bR) (cM.hom ≫ F.map bM) ≫
        AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
            (coefficientBar.{u, v', max u v v' z} k B N) ≫
            diagonalChainMap.{u, v', max u v v' z} k B N := by rw [hR, hM]
    _ = HomologicalComplex.tensorHom cR.hom cM.hom ≫
        (HomologicalComplex.tensorHom (F.map bR) (F.map bM) ≫
          AlgebraicTopology.EilenbergZilber.alternatingPairing
            (coefficientBar.{u, v', max u v v' z} k B (ULift.{max u v v' z} B))
              (coefficientBar.{u, v', max u v v' z} k B N)) ≫
          diagonalChainMap.{u, v', max u v v' z} k B N := by
            rw [← HomologicalComplex.tensorHom_comp_tensorHom]
            simp only [Category.assoc]
    _ = HomologicalComplex.tensorHom cR.hom cM.hom ≫
        (AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v, max u v v' z} k A (ULift.{max u v v' z} A))
            (coefficientBar.{u, v, max u v v' z} k A M) ≫
            F.map (bR ⊗ₘ bM)) ≫ diagonalChainMap.{u, v', max u v v' z} k B N := by rw [hShuffle]
    _ = HomologicalComplex.tensorHom cR.hom cM.hom ≫
        AlgebraicTopology.EilenbergZilber.alternatingPairing
          (coefficientBar.{u, v, max u v v' z} k A (ULift.{max u v v' z} A))
            (coefficientBar.{u, v, max u v v' z} k A M) ≫
            (F.map (bR ⊗ₘ bM) ≫ diagonalChainMap.{u, v', max u v v' z} k B N) := by simp only [Category.assoc]
    _ = _ := by rw [hDiagonal]; simp only [Category.assoc]

/-- The target-normalized shuffle retains the original coefficient/algebra
naturality square. No separately normalized tail multiplication occurs. -/
@[reassoc]
theorem pairing_normalizationProjection_naturality (g : A →ₐ[k] B) (f : M →ₗ[k] N)
    (hf : ∀ a m, f (a • m) = g a • f m) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  HomologicalComplex.tensorHom
      (coefficientChainMap.{u, v, v', z} g
        (regularCoefficientMap g.toNonUnitalAlgHom :
          ULift.{max u v v' z} A →ₗ[k] ULift.{max u v v' z} B)
        (regularCoefficientMap_smul.{u, v, v', max u v v' z, max u v v' z}
          g.toNonUnitalAlgHom)) (coefficientChainMap.{u, v, v', z} g f hf) ≫
    (pairing.{u, v', max u v v' z} k B N).postcomp
      (normalizationProjection.{u, v', max u v v' z} k B N) =
  (pairing.{u, v, max u v v' z} k A M).postcomp
      (normalizationProjection.{u, v, max u v v' z} k A M) ≫ normalizedCoefficientMap.{u, v, v', z} g f hf := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v v' z} (R := k)
  let : MonoidalCategory (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v v' z} (R := k)
  let : MonoidalPreadditive (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v v' z} (R := k)
  let : MonoidalLinear k (ModuleCat.{max u v v' z} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v v' z} (R := k)
  rw [HomologicalComplex.ChainGradedPairing.postcomp,
    HomologicalComplex.ChainGradedPairing.postcomp, ← Category.assoc, pairing_naturality.{u, v, v', z}]
  rw [Category.assoc, ← normalizationProjection_coefficientMap.{u, v, v', z}]
  simp only [Category.assoc]

end ModuleCat.Algebra.Hochschild.Symmetric
