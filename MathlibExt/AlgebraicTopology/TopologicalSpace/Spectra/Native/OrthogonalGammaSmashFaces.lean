/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalFreeSphereSmashFlatness
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.ActualFunctionIteration
import MathlibExt.CategoryTheory.Monoidal.Mod.FreePairAugmentation

/-!
# The original free-pair Gamma smash maps

The two source-unit generator formulas retain the actual right-module free
tensorator, the original relative quotient and the entire target action.
They are the source equations for the native free-sphere rotation faces.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open scoped MonoidalClosed CategoryTheory.MonObj

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Source

universe uC vC
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  (R : C) [MonObj R] [IsCommMonObj R] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

open CommutativeModuleConversion

/-- The right-module tensor used to evaluate the original free-source adjunction and
precomposition maps. -/
local instance : MonoidalCategory (RightModule R) := RightModuleFree.tensorMonoidal R

/-- The original left-unit source pair preserves both complete generator arrows. -/
theorem left_unit_generator (P Q : C) (N : RightModule R)
    (f : RightModuleFree.freeObject R P ⟶ 𝟙_ (RightModule R))
    (g : RightModuleFree.freeObject R Q ⟶ N) :
    RightModuleFree.freeGenerator R (P ⊗ Q) ≫
        ((RightModuleFree.freeTensorIso R P Q).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom).hom =
      ((RightModuleFree.freeGenerator R P ≫ f.hom) ⊗ₘ
        (RightModuleFree.freeGenerator R Q ≫ g.hom)) ≫ leftAction R N := by
  let f₀ : P ⊗ R ⟶ R := f.hom
  let g₀ : Q ⊗ R ⟶ N.X := g.hom
  let p : (P ⊗ R) ⊗ (Q ⊗ R) ⟶
      (RightModuleFree.freeObject R P ⊗ RightModuleFree.freeObject R Q).X :=
    RightModuleFree.relativeTensorπ R
    (RightModuleFree.freeObject R P) (RightModuleFree.freeObject R Q)
  let p' : R ⊗ N.X ⟶ (𝟙_ (RightModule R) ⊗ N).X :=
    RightModuleFree.relativeTensorπ R (𝟙_ (RightModule R)) N
  let t := (RightModuleFree.relativeTensorMap R f g).hom
  let l := (λ_ N).hom.hom
  have ht : p ≫ t = (f₀ ⊗ₘ g₀) ≫ p' :=
    RightModuleFree.relativeTensorMap_π R f g
  have hl : p' ≫ l = leftAction R N :=
    RightModuleFree.relativeTensorLeftUnitor_hom_π R N
  change RightModuleFree.freeGenerator R (P ⊗ Q) ≫
      ((RightModuleFree.freeTensorIso R P Q).inv.hom ≫ t ≫ l) =
    ((RightModuleFree.freeGenerator R P ≫ f₀) ⊗ₘ
      (RightModuleFree.freeGenerator R Q ≫ g₀)) ≫ leftAction R N
  calc
    _ = (RightModuleFree.freeGenerator R P ⊗ₘ RightModuleFree.freeGenerator R Q) ≫
        p ≫ t ≫ l := by
      erw [← Category.assoc, RightModuleFree.freeTensorIso_inv_generator]
      simp only [RightModuleFree.tensorFreeGenerator, p, Category.assoc]
    _ = (RightModuleFree.freeGenerator R P ⊗ₘ RightModuleFree.freeGenerator R Q) ≫
        (f₀ ⊗ₘ g₀) ≫ p' ≫ l := by
      erw [← Category.assoc p t l, ht]
      simp only [Category.assoc]
      rfl
    _ = _ := by
      erw [hl, ← Category.assoc, tensorHom_comp_tensorHom]

/-- The full left-unit map is the actual extension of its unchanged generator and target action. -/
theorem left_unit_eq_extension (P Q : C) (N : RightModule R)
    (f : RightModuleFree.freeObject R P ⟶ 𝟙_ (RightModule R))
    (g : RightModuleFree.freeObject R Q ⟶ N) :
    (RightModuleFree.freeTensorIso R P Q).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom =
      RightModuleFree.extendFree R (P ⊗ Q) N
        (((RightModuleFree.freeGenerator R P ≫ f.hom) ⊗ₘ
          (RightModuleFree.freeGenerator R Q ≫ g.hom)) ≫ leftAction R N) := by
  apply RightModuleFree.free_hom_ext R (P ⊗ Q) N
  rw [RightModuleFree.freeGenerator_extend]
  exact left_unit_generator R P Q N f g

/-- The original right-unit source pair retains the complete original right action. -/
theorem right_unit_generator (P Q : C) (N : RightModule R)
    (f : RightModuleFree.freeObject R P ⟶ N)
    (g : RightModuleFree.freeObject R Q ⟶ 𝟙_ (RightModule R)) :
    RightModuleFree.freeGenerator R (P ⊗ Q) ≫
        ((RightModuleFree.freeTensorIso R P Q).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom).hom =
      ((RightModuleFree.freeGenerator R P ≫ f.hom) ⊗ₘ
        (RightModuleFree.freeGenerator R Q ≫ g.hom)) ≫ N.action := by
  let f₀ : P ⊗ R ⟶ N.X := f.hom
  let g₀ : Q ⊗ R ⟶ R := g.hom
  let p : (P ⊗ R) ⊗ (Q ⊗ R) ⟶
      (RightModuleFree.freeObject R P ⊗ RightModuleFree.freeObject R Q).X :=
    RightModuleFree.relativeTensorπ R
    (RightModuleFree.freeObject R P) (RightModuleFree.freeObject R Q)
  let p' : N.X ⊗ R ⟶ (N ⊗ 𝟙_ (RightModule R)).X :=
    RightModuleFree.relativeTensorπ R N (𝟙_ (RightModule R))
  let t := (RightModuleFree.relativeTensorMap R f g).hom
  let r := (ρ_ N).hom.hom
  have ht : p ≫ t = (f₀ ⊗ₘ g₀) ≫ p' :=
    RightModuleFree.relativeTensorMap_π R f g
  have hr : p' ≫ r = N.action :=
    RightModuleFree.relativeTensorRightUnitor_hom_π R N
  change RightModuleFree.freeGenerator R (P ⊗ Q) ≫
      ((RightModuleFree.freeTensorIso R P Q).inv.hom ≫ t ≫ r) =
    ((RightModuleFree.freeGenerator R P ≫ f₀) ⊗ₘ
      (RightModuleFree.freeGenerator R Q ≫ g₀)) ≫ N.action
  calc
    _ = (RightModuleFree.freeGenerator R P ⊗ₘ RightModuleFree.freeGenerator R Q) ≫
        p ≫ t ≫ r := by
      erw [← Category.assoc, RightModuleFree.freeTensorIso_inv_generator]
      simp only [RightModuleFree.tensorFreeGenerator, p, Category.assoc]
    _ = (RightModuleFree.freeGenerator R P ⊗ₘ RightModuleFree.freeGenerator R Q) ≫
        (f₀ ⊗ₘ g₀) ≫ p' ≫ r := by
      erw [← Category.assoc p t r, ht]
      simp only [Category.assoc]
      rfl
    _ = _ := by
      erw [hr, ← Category.assoc, tensorHom_comp_tensorHom]

/-- The full right-unit map is the actual extension of the original two coefficients and action. -/
theorem right_unit_eq_extension (P Q : C) (N : RightModule R)
    (f : RightModuleFree.freeObject R P ⟶ N)
    (g : RightModuleFree.freeObject R Q ⟶ 𝟙_ (RightModule R)) :
    (RightModuleFree.freeTensorIso R P Q).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom =
      RightModuleFree.extendFree R (P ⊗ Q) N
        (((RightModuleFree.freeGenerator R P ≫ f.hom) ⊗ₘ
          (RightModuleFree.freeGenerator R Q ≫ g.hom)) ≫ N.action) := by
  apply RightModuleFree.free_hom_ext R (P ⊗ Q) N
  rw [RightModuleFree.freeGenerator_extend]
  exact right_unit_generator R P Q N f g

/-- The actual left-unit pair after the original complete base comparison is its full free extension. -/
theorem left_pair_eq_extension (P Q T : C) (e : P ⊗ Q ≅ T) (N : RightModule R)
    (f : RightModuleFree.freeObject R P ⟶ 𝟙_ (RightModule R))
    (g : RightModuleFree.freeObject R Q ⟶ N) :
    (PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Primitive.ofIso R P Q T e).inv ≫
        (f ⊗ₘ g) ≫ (λ_ N).hom =
      RightModuleFree.extendFree R T N
        (e.inv ≫ ((RightModuleFree.freeGenerator R P ≫ f.hom) ⊗ₘ
          (RightModuleFree.freeGenerator R Q ≫ g.hom)) ≫ leftAction R N) := by
  simp only [PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Primitive.ofIso,
    Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  erw [left_unit_eq_extension]
  exact (RightModuleFree.freeHomEquiv_naturality_left R e.inv N _).symm

/-- The original left-unit base comparison retains every coefficient in the complete generator. -/
theorem left_pair_generator (P Q T : C) (e : P ⊗ Q ≅ T) (N : RightModule R)
    (f : RightModuleFree.freeObject R P ⟶ 𝟙_ (RightModule R))
    (g : RightModuleFree.freeObject R Q ⟶ N) :
    RightModuleFree.freeGenerator R T ≫
        ((PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Primitive.ofIso R P Q T e).inv ≫
          (f ⊗ₘ g) ≫ (λ_ N).hom).hom =
      e.inv ≫ ((RightModuleFree.freeGenerator R P ≫ f.hom) ⊗ₘ
        (RightModuleFree.freeGenerator R Q ≫ g.hom)) ≫ leftAction R N := by
  rw [left_pair_eq_extension, RightModuleFree.freeGenerator_extend]

/-- The actual right-unit pair after the original complete base comparison is its full free extension. -/
theorem right_pair_eq_extension (P Q T : C) (e : P ⊗ Q ≅ T) (N : RightModule R)
    (f : RightModuleFree.freeObject R P ⟶ N)
    (g : RightModuleFree.freeObject R Q ⟶ 𝟙_ (RightModule R)) :
    (PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Primitive.ofIso R P Q T e).inv ≫
        (f ⊗ₘ g) ≫ (ρ_ N).hom =
      RightModuleFree.extendFree R T N
        (e.inv ≫ ((RightModuleFree.freeGenerator R P ≫ f.hom) ⊗ₘ
          (RightModuleFree.freeGenerator R Q ≫ g.hom)) ≫ N.action) := by
  simp only [PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Primitive.ofIso,
    Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  erw [right_unit_eq_extension]
  exact (RightModuleFree.freeHomEquiv_naturality_left R e.inv N _).symm

/-- The original right-unit base comparison retains both coefficients and the entire right action. -/
theorem right_pair_generator (P Q T : C) (e : P ⊗ Q ≅ T) (N : RightModule R)
    (f : RightModuleFree.freeObject R P ⟶ N)
    (g : RightModuleFree.freeObject R Q ⟶ 𝟙_ (RightModule R)) :
    RightModuleFree.freeGenerator R T ≫
        ((PointedCGWH.Spectra.Orthogonal.SphereSmashFree.Primitive.ofIso R P Q T e).inv ≫
          (f ⊗ₘ g) ≫ (ρ_ N).hom).hom =
      e.inv ≫ ((RightModuleFree.freeGenerator R P ≫ f.hom) ⊗ₘ
        (RightModuleFree.freeGenerator R Q ≫ g.hom)) ≫ N.action := by
  rw [right_pair_eq_extension, RightModuleFree.freeGenerator_extend]

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Source


open CategoryTheory.Spectra.OrthogonalComplementBundle
open CategoryTheory.Spectra.OrthogonalCoendThom
open CategoryTheory.Spectra.OrthogonalSmashGammaGeometry
open PointedCGWH
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalFreeSphereSmashFlatness

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Geometry

theorem pointPair_braiding {X Y : PointedCGWH.{u, v}}
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ X) (q : 𝟙_ PointedCGWH.{u, v} ⟶ Y) :
    pointPair p q ≫ (β_ X Y).hom = pointPair q p := by
  dsimp only [pointPair]
  rw [Category.assoc, braiding_naturality]
  simp only [braiding_tensorUnit_left, unitors_equal, Category.assoc, Iso.hom_inv_id_assoc]

theorem pointedSplit_point (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) :
    spherePoint.{u, v} k x ≫ pointedSplit.{u, v} n k a g =
      pointPair
        (pointPair (OrthogonalIndex.matrixPoint.{u, v} g)
            (spherePoint.{u, v} a (coefficientCoordinates n k a g x)) ≫
          generatorThomLeg.{u, v} n k a)
        (spherePoint.{u, v} n (retainedCoordinates n k a g x)) := by
  apply pointValue_injective
  rw [pointValue_comp, spherePoint_value, pointedSplit_coe]
  rw [pointPair_value, generatorThomLeg_matrixSpherePoint, spherePoint_value]
  rw [targetProductIso]
  dsimp only [liftedSplitVector, splitVector, ULift.down_up]
  erw [onePointProdSmashIso_coe]
  rfl

theorem coefficientMap_point (n k a : ℕ) (g : Frame n k a) (x : Euclidean k) :
    spherePoint.{u, v} k x ≫ coefficientMap.{u, v} n k a g =
      pointPair (spherePoint.{u, v} n (retainedCoordinates n k a g x))
        (pointPair (OrthogonalIndex.matrixPoint.{u, v} g)
            (spherePoint.{u, v} a (coefficientCoordinates n k a g x)) ≫
          OrthogonalOperatorIndex.ι.{u, v} n k a) := by
  apply (cancel_mono (valueIso.{u, v} n k).hom).1
  simp only [coefficientMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [pointedSplit_point]
  rw [valueIso, Iso.trans_hom, nativeFreeThomComponentIso_hom]
  rw [← id_tensorHom, ← Category.assoc, pointPairNatural, Category.comp_id, pointPair_braiding]
  rw [Category.assoc, nativeToThom_generator]

theorem coefficientCoordinates_id_apply (n : ℕ) (x : Euclidean (n + n)) (i : Fin n) :
    (coefficientCoordinates n (n + n) n (OrthogonalMatrixHom.id (n + n)) x).ofLp i =
      x.ofLp (Fin.castAdd n i) := by
  rw [coefficientCoordinates, matrixLinear_ofLp]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, coefficientPart_apply,
    OrthogonalMatrixHom.id, Matrix.one_apply]

theorem retainedCoordinates_id_apply (n : ℕ) (x : Euclidean (n + n)) (i : Fin n) :
    (retainedCoordinates n (n + n) n (OrthogonalMatrixHom.id (n + n)) x).ofLp i =
      x.ofLp (Fin.natAdd n i) := by
  rw [retainedCoordinates, matrixLinear_ofLp]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, finalPart_apply,
    OrthogonalMatrixHom.id, Matrix.one_apply]

theorem coefficientCoordinates_blockSwap_apply (n : ℕ) (x : Euclidean (n + n)) (i : Fin n) :
    (coefficientCoordinates n (n + n) n (OrthogonalIndex.blockSwap n n) x).ofLp i =
      x.ofLp (Fin.natAdd n i) := by
  rw [coefficientCoordinates, matrixLinear_ofLp]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, coefficientPart_apply,
    OrthogonalIndex.blockSwap_matrix, finAddFlip_apply_castAdd]

theorem retainedCoordinates_blockSwap_apply (n : ℕ) (x : Euclidean (n + n)) (i : Fin n) :
    (retainedCoordinates n (n + n) n (OrthogonalIndex.blockSwap n n) x).ofLp i =
      x.ofLp (Fin.castAdd n i) := by
  rw [retainedCoordinates, matrixLinear_ofLp]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, finalPart_apply,
    OrthogonalIndex.blockSwap_matrix]
  have h : i.addNat n = Fin.natAdd n i := by
    apply Fin.ext
    exact Nat.add_comm _ _
  rw [h, finAddFlip_apply_natAdd]


end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Geometry


section NativeGammaFamilies
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory.EnrichedFunctorCat

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Independent
universe uV vV uD vD
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {D : Type uD} [Category.{vD} D]
/-- Tensor comparisons `P n X ⊗ P m Y ≅ P (t n m) (X ⊗ Y)` for every pair of labels and
coefficients. -/
def PairFormula (M : MonoidalCategory D) (P : ℕ → V → D) (t : ℕ → ℕ → ℕ) : Type _ :=
  letI := M
  ∀ (n m : ℕ) (X Y : V), P n X ⊗ P m Y ≅ P (t n m) (X ⊗ Y)


/-- Left Gamma-face families from `P (n + r) (S n ⊗ K)` to `P r K`. -/
def LeftFaceType (P : ℕ → V → D) (S : ℕ → V) : Type _ :=
  ∀ (n r : ℕ) (K : V), P (n + r) (S n ⊗ K) ⟶ P r K

/-- Right Gamma-face families from `P (r + n) (K ⊗ S n)` to `P r K`. -/
def RightFaceType (P : ℕ → V → D) (S : ℕ → V) : Type _ :=
  ∀ (n r : ℕ) (K : V), P (r + n) (K ⊗ S n) ⟶ P r K

/-- Gamma families taking each free sphere `P n (S n)` to the tensor unit. -/
def GammaType (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V) : Type _ :=
  letI := M
  ∀ n : ℕ, P n (S n) ⟶ 𝟙_ D

/-- The left Gamma faces formed from the inverse pair comparison, `gamma n` in the left factor,
and the left unitor. -/
def leftFaceFamily (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (gamma : GammaType M P S) (pair : PairFormula M P (fun n r => n + r)) :
    LeftFaceType P S := by
  letI := M
  intro n r K
  exact (pair n r (S n) K).inv ≫ (gamma n ⊗ₘ 𝟙 (P r K)) ≫ (λ_ (P r K)).hom

/-- The right Gamma faces formed from the inverse pair comparison, `gamma n` in the right factor,
and the right unitor. -/
def rightFaceFamily (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (gamma : GammaType M P S) (pair : PairFormula M P (fun n r => n + r)) :
    RightFaceType P S := by
  letI := M
  intro n r K
  exact (pair r n K (S n)).inv ≫ (𝟙 (P r K) ⊗ₘ gamma n) ≫ (ρ_ (P r K)).hom


/-- Tensor comparisons from two free spheres at `n` to the free sphere at `n + n`. -/
def SpherePairType (M : MonoidalCategory D) (F : ℕ → V ⥤ D) (S : ℕ → V) : Type _ :=
  letI := M
  ∀ n : ℕ, (F n).obj (S n) ⊗ (F n).obj (S n) ≅ (F (n + n)).obj (S (n + n))

/-- Sphere-face families from the doubled free sphere at `n + n` to the free sphere at `n`. -/
def SphereFaceType (F : ℕ → V ⥤ D) (S : ℕ → V) : Type _ :=
  ∀ n : ℕ, (F (n + n)).obj (S (n + n)) ⟶ (F n).obj (S n)

/-- Compose the free-pair comparison with the free functor applied to the inverse sphere
coefficient comparison. -/
def spherePairFamily (M : MonoidalCategory D) (F : ℕ → V ⥤ D) (S : ℕ → V)
    (pair : PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n : ℕ, S (n + n) ≅ S n ⊗ S n) : SpherePairType M F S := by
  letI := M
  intro n
  exact pair n n (S n) (S n) ≪≫ (F (n + n)).mapIso (coefficient n).symm

/-- The left sphere faces obtained by applying `gamma n` in the left factor of the inverse
sphere-pair comparison. -/
def leftSphereFamily (M : MonoidalCategory D) (F : ℕ → V ⥤ D) (S : ℕ → V)
    (gamma : GammaType M (fun n K => (F n).obj K) S)
    (pair : PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n : ℕ, S (n + n) ≅ S n ⊗ S n) : SphereFaceType F S := by
  letI := M
  intro n
  exact (spherePairFamily M F S pair coefficient n).inv ≫
    (gamma n ⊗ₘ 𝟙 ((F n).obj (S n))) ≫ (λ_ ((F n).obj (S n))).hom

/-- The right sphere faces obtained by applying `gamma n` in the right factor of the inverse
sphere-pair comparison. -/
def rightSphereFamily (M : MonoidalCategory D) (F : ℕ → V ⥤ D) (S : ℕ → V)
    (gamma : GammaType M (fun n K => (F n).obj K) S)
    (pair : PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n : ℕ, S (n + n) ≅ S n ⊗ S n) : SphereFaceType F S := by
  letI := M
  intro n
  exact (spherePairFamily M F S pair coefficient n).inv ≫
    (𝟙 ((F n).obj (S n)) ⊗ₘ gamma n) ≫ (ρ_ ((F n).obj (S n))).hom


/-- The given left faces equal the inverse pair comparison followed by the left Gamma tensor and
left unitor. -/
def LeftFaceFormula (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (gamma : GammaType M P S) (pair : PairFormula M P (fun n r => n + r))
    (faces : LeftFaceType P S) : Prop :=
  letI := M
  ∀ (n r : ℕ) (K : V), faces n r K =
    (pair n r (S n) K).inv ≫ (gamma n ⊗ₘ 𝟙 (P r K)) ≫ (λ_ (P r K)).hom

/-- The given right faces equal the inverse pair comparison followed by the right Gamma tensor and
right unitor. -/
def RightFaceFormula (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (gamma : GammaType M P S) (pair : PairFormula M P (fun n r => n + r))
    (faces : RightFaceType P S) : Prop :=
  letI := M
  ∀ (n r : ℕ) (K : V), faces n r K =
    (pair r n K (S n)).inv ≫ (𝟙 (P r K) ⊗ₘ gamma n) ≫ (ρ_ (P r K)).hom

theorem leftFaceFamily_original (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (gamma : GammaType M P S) (pair : PairFormula M P (fun n r => n + r)) :
    LeftFaceFormula M P S gamma pair (leftFaceFamily M P S gamma pair) := by
  let := M
  intro n r K
  rfl

theorem rightFaceFamily_original (M : MonoidalCategory D) (P : ℕ → V → D) (S : ℕ → V)
    (gamma : GammaType M P S) (pair : PairFormula M P (fun n r => n + r)) :
    RightFaceFormula M P S gamma pair (rightFaceFamily M P S gamma pair) := by
  let := M
  intro n r K
  rfl

/-- The given sphere pairs are the free pairs followed by the inverse sphere coefficient
comparison. -/
def SpherePairFormula (M : MonoidalCategory D) (F : ℕ → V ⥤ D) (S : ℕ → V)
    (pair : PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n : ℕ, S (n + n) ≅ S n ⊗ S n) (pairs : SpherePairType M F S) : Prop :=
  letI := M
  ∀ n : ℕ, pairs n = pair n n (S n) (S n) ≪≫ (F (n + n)).mapIso (coefficient n).symm

theorem spherePairFamily_original (M : MonoidalCategory D) (F : ℕ → V ⥤ D) (S : ℕ → V)
    (pair : PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n : ℕ, S (n + n) ≅ S n ⊗ S n) :
    SpherePairFormula M F S pair coefficient (spherePairFamily M F S pair coefficient) := by
  let := M
  intro n
  rfl

/-- The given left sphere faces are the inverse sphere pairs followed by the left Gamma tensor and
left unitor. -/
def LeftSphereFormula (M : MonoidalCategory D) (F : ℕ → V ⥤ D) (S : ℕ → V)
    (gamma : GammaType M (fun n K => (F n).obj K) S)
    (pairs : SpherePairType M F S) (faces : SphereFaceType F S) : Prop :=
  letI := M
  ∀ n : ℕ, faces n = (pairs n).inv ≫
    (gamma n ⊗ₘ 𝟙 ((F n).obj (S n))) ≫ (λ_ ((F n).obj (S n))).hom

/-- The given right sphere faces are the inverse sphere pairs followed by the right Gamma tensor
and right unitor. -/
def RightSphereFormula (M : MonoidalCategory D) (F : ℕ → V ⥤ D) (S : ℕ → V)
    (gamma : GammaType M (fun n K => (F n).obj K) S)
    (pairs : SpherePairType M F S) (faces : SphereFaceType F S) : Prop :=
  letI := M
  ∀ n : ℕ, faces n = (pairs n).inv ≫
    (𝟙 ((F n).obj (S n)) ⊗ₘ gamma n) ≫ (ρ_ ((F n).obj (S n))).hom

theorem leftSphereFamily_original (M : MonoidalCategory D) (F : ℕ → V ⥤ D) (S : ℕ → V)
    (gamma : GammaType M (fun n K => (F n).obj K) S)
    (pair : PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n : ℕ, S (n + n) ≅ S n ⊗ S n) :
    LeftSphereFormula M F S gamma (spherePairFamily M F S pair coefficient)
      (leftSphereFamily M F S gamma pair coefficient) := by
  let := M
  intro n
  rfl

theorem rightSphereFamily_original (M : MonoidalCategory D) (F : ℕ → V ⥤ D) (S : ℕ → V)
    (gamma : GammaType M (fun n K => (F n).obj K) S)
    (pair : PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n : ℕ, S (n + n) ≅ S n ⊗ S n) :
    RightSphereFormula M F S gamma (spherePairFamily M F S pair coefficient)
      (rightSphereFamily M F S gamma pair coefficient) := by
  let := M
  intro n
  rfl

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Independent

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Selected
universe uV vV uJ
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local instance] EnrichedDayKernel.ColimitMonoidal.smallestColimits
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [Category ℕ] [MonoidalCategory ℕ] [SymmetricCategory ℕ]
  [EnrichedOrdinaryCategory V ℕ]
  [HasColimitsOfSize.{0, 0} V] [HasProducts.{0} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V ℕ)
  {J : Type uJ} [EnrichedCategory V J]
  (c : PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.SelectedPair.Context q J)

open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.FunctionIteration

/-- Free-pair tensor comparisons in the selected native presentation, with its original index and
tensor-index maps. -/
def PairFamilyType : Type _ :=
  letI := q.moduleMonoidal
  letI := Monoidal.transport c.sourceEquivalence
  ∀ (n m : ℕ) (X Y : V),
    Free.object (c.indexMap n) X ⊗ Free.object (c.indexMap m) Y ≅
      Free.object (c.indexMap (c.tensorIndex n m)) (X ⊗ Y)

/-- The canonical selected free-pair comparisons, transported from the primitive source-module
tensor. -/
def pairFamily : PairFamilyType q c := by
  unfold PairFamilyType
  rw [q.moduleMonoidal_eq_primitive]
  exact CanonicalSourceFreeSmash.SelectedPair.pairIso c

theorem pairFamily_type_original :
    PairFamilyType q c = Independent.PairFormula
      (TypedFullPowerData.sourceContext c).monoidalCategory
      (fun (n : ℕ) (X : V) => Free.object (c.indexMap n) X) c.tensorIndex := rfl


theorem pairFamily_heq_original : HEq (pairFamily q c) (CanonicalSourceFreeSmash.SelectedPair.pairIso c) := by
  rfl

/-- Casting the complete selected family preserves the whole original canonical pair value. -/
def CastOriginalPairFormula (T : Type _) (h : PairFamilyType q c = T) : Prop :=
  HEq (cast h (pairFamily q c)) (CanonicalSourceFreeSmash.SelectedPair.pairIso c)

/-- The exact type transport and original selected pair retain the same whole Iso family. -/
theorem castPairFamily_original (T : Type _) (h : PairFamilyType q c = T) :
    CastOriginalPairFormula q c T h :=
  (cast_heq h (pairFamily q c)).trans (pairFamily_heq_original q c)

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Selected

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open MMSSStabilization.FunctionIteration
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory

/-- The native sphere-module tensor used by the free-pair Gamma comparisons. -/
local instance : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmashStructure.monoidalCategory.{u, v}
/-- The canonical source smash tensor on native orthogonal spectra. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- Free-pair comparisons for native orthogonal spectra at the literal operator labels and their
sums. -/
def NativeFamilyType : Type _ :=
  Independent.PairFormula CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) =>
      Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    (fun n m => n + m)

theorem freeObjects_original :
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) =>
      Free.object (CanonicalSourceFreeSmash.pairData.{u, v}.indexMap n) K) =
      (fun (n : ℕ) (K : PointedCGWH.{u, v}) =>
        Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K) := rfl

theorem tensorIndex_original :
    CanonicalSourceFreeSmash.pairData.{u, v}.tensorIndex = (fun n m => n + m) := rfl

theorem sourceMonoidal_original :
    (TypedFullPowerData.sourceContext CanonicalSourceFreeSmash.pairData.{u, v}).monoidalCategory =
      CanonicalSourceSmash.monoidalCategory.{u, v} :=
  congrArg (fun source => source.monoidalCategory) NativeTypedFullPowerData.context_original.{u, v}

theorem pairFamily_type_native :
    Selected.PairFamilyType SphereSmash.sourceData.{u, v}
      CanonicalSourceFreeSmash.pairData.{u, v} = NativeFamilyType.{u, v} :=
  (Selected.pairFamily_type_original SphereSmash.sourceData.{u, v}
    CanonicalSourceFreeSmash.pairData.{u, v}).trans
      ((congrArg₂ (fun M P => Independent.PairFormula M P
          CanonicalSourceFreeSmash.pairData.{u, v}.tensorIndex)
        sourceMonoidal_original.{u, v} freeObjects_original.{u, v}).trans
          (congrArg (fun t => Independent.PairFormula CanonicalSourceSmash.monoidalCategory.{u, v}
            (fun (n : ℕ) (K : PointedCGWH.{u, v}) =>
              Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K) t)
            tensorIndex_original.{u, v}))

/-- The selected free-pair comparisons transported to the literal native orthogonal operator
labels. -/
def nativePairFamily : NativeFamilyType.{u, v} :=
  Eq.mp pairFamily_type_native.{u, v}
    (Selected.pairFamily SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v})

/-- The native left Gamma faces from the literal free-pair comparisons and the original
unit-source Gamma maps. -/
def nativeLeftFaces : Independent.LeftFaceType
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) => Free.object
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v} :=
  Independent.leftFaceFamily CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) => Free.object
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v}
    MMSSStabilization.LambdaUnitSource.gamma.{u, v} nativePairFamily.{u, v}

/-- The native right Gamma faces from the literal free-pair comparisons and the original
unit-source Gamma maps. -/
def nativeRightFaces : Independent.RightFaceType
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) => Free.object
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v} :=
  Independent.rightFaceFamily CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) => Free.object
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v}
    MMSSStabilization.LambdaUnitSource.gamma.{u, v} nativePairFamily.{u, v}


/-- The pointed free orthogonal-spectrum functor at the operator label `n`. -/
def nativeFreeFunctor (n : ℕ) : PointedCGWH.{u, v} ⥤ CanonicalSourceSmash.Carrier.{u, v} :=
  Free.functor (V := PointedCGWH.{u, v}) (OrthogonalOperatorIndex.ofIndex.{u, v} n)

/-- The native free-sphere pair comparisons using the original orthogonal sphere tensor
isomorphisms. -/
def nativeSpherePairFamily : Independent.SpherePairType CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v} :=
  Independent.spherePairFamily CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v} nativePairFamily.{u, v}
    (fun n => PointedCGWH.orthogonalSphereTensorIso.{u, v} n n)

/-- The native left sphere faces using the original Gamma maps and orthogonal sphere tensor
comparisons. -/
def nativeLeftSphereFaces : Independent.SphereFaceType nativeFreeFunctor.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} :=
  Independent.leftSphereFamily CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v}
    MMSSStabilization.LambdaUnitSource.gamma.{u, v} nativePairFamily.{u, v}
    (fun n => PointedCGWH.orthogonalSphereTensorIso.{u, v} n n)

/-- The native right sphere faces using the original Gamma maps and orthogonal sphere tensor
comparisons. -/
def nativeRightSphereFaces : Independent.SphereFaceType nativeFreeFunctor.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} :=
  Independent.rightSphereFamily CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v}
    MMSSStabilization.LambdaUnitSource.gamma.{u, v} nativePairFamily.{u, v}
    (fun n => PointedCGWH.orthogonalSphereTensorIso.{u, v} n n)


theorem nativeLeftFaces_original : Independent.LeftFaceFormula CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) => Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v} MMSSStabilization.LambdaUnitSource.gamma.{u, v}
    nativePairFamily.{u, v} nativeLeftFaces.{u, v} :=
  Independent.leftFaceFamily_original CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) => Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v} MMSSStabilization.LambdaUnitSource.gamma.{u, v}
    nativePairFamily.{u, v}

theorem nativeRightFaces_original : Independent.RightFaceFormula CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) => Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v} MMSSStabilization.LambdaUnitSource.gamma.{u, v}
    nativePairFamily.{u, v} nativeRightFaces.{u, v} :=
  Independent.rightFaceFamily_original CanonicalSourceSmash.monoidalCategory.{u, v}
    (fun (n : ℕ) (K : PointedCGWH.{u, v}) => Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} n) K)
    PointedCGWH.orthogonalSphere.{u, v} MMSSStabilization.LambdaUnitSource.gamma.{u, v}
    nativePairFamily.{u, v}

theorem nativeSpherePairFamily_original : Independent.SpherePairFormula CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v}
    nativePairFamily.{u, v} (fun n => PointedCGWH.orthogonalSphereTensorIso.{u, v} n n)
    nativeSpherePairFamily.{u, v} :=
  Independent.spherePairFamily_original CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v} nativePairFamily.{u, v}
    (fun n => PointedCGWH.orthogonalSphereTensorIso.{u, v} n n)

theorem nativeLeftSphereFaces_original : Independent.LeftSphereFormula CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v}
    MMSSStabilization.LambdaUnitSource.gamma.{u, v} nativeSpherePairFamily.{u, v} nativeLeftSphereFaces.{u, v} :=
  Independent.leftSphereFamily_original CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v}
    MMSSStabilization.LambdaUnitSource.gamma.{u, v} nativePairFamily.{u, v}
    (fun n => PointedCGWH.orthogonalSphereTensorIso.{u, v} n n)

theorem nativeRightSphereFaces_original : Independent.RightSphereFormula CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v}
    MMSSStabilization.LambdaUnitSource.gamma.{u, v} nativeSpherePairFamily.{u, v} nativeRightSphereFaces.{u, v} :=
  Independent.rightSphereFamily_original CanonicalSourceSmash.monoidalCategory.{u, v}
    nativeFreeFunctor.{u, v} PointedCGWH.orthogonalSphere.{u, v}
    MMSSStabilization.LambdaUnitSource.gamma.{u, v} nativePairFamily.{u, v}
    (fun n => PointedCGWH.orthogonalSphereTensorIso.{u, v} n n)


/-- The entire native pair/original-value relation at its complete original selected-source type. -/
def NativePairOriginalFormula : Prop :=
  Selected.CastOriginalPairFormula SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
    NativeFamilyType.{u, v} pairFamily_type_native.{u, v}

/-- The whole native pair is the same original canonical pair, with only its proved type transport. -/
theorem nativePairFamily_heq_original : NativePairOriginalFormula.{u, v} :=
  Selected.castPairFamily_original SphereSmash.sourceData.{u, v} CanonicalSourceFreeSmash.pairData.{u, v}
    NativeFamilyType.{u, v} pairFamily_type_native.{u, v}

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces

end NativeGammaFamilies
