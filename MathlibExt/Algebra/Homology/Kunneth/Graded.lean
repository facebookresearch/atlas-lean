/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.Kunneth.Collapse
public import MathlibExt.Algebra.Homology.Kunneth.Naturality
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import MathlibExt.CategoryTheory.GradedObject.Preadditive
public import MathlibExt.Algebra.Homology.GradedHomology.Monoidal
public import MathlibExt.CategoryTheory.GradedObject.TensorAntidiagonal

/-!
# The canonical Künneth map on native graded homology

The native graded tensor uses a coproduct over the addition fibres. The
existing Künneth API uses the finite antidiagonal biproduct. The two actual
objects are compared here by their injections; no tensor comparison is
supplied by a caller. The tensorator is the existing cycle pairing.

This file retains the actual existing boundary: `R : Type u` and
`ModuleCat.{u} R`. A larger coefficient world is not inferred from this API.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.Kunneth

variable {R : Type u} [CommRing R]


local instance moduleFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- The existing native graded homology functor. -/
abbrev homologyFunctor : (ChainComplex (ModuleCat.{u} R) ℕ) ⥤ (GradedObject ℕ (ModuleCat.{u} R)) :=
  gradedHomologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- The actual cycle-induced bidegree pairing, with descent data earned from
the identity chain map on the tensor complex. -/
abbrev pair (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q : ℕ) :
    K.homology p ⊗ L.homology q ⟶ (tensorObj K L).homology (p + q) :=
  ChainGradedPairing.pairHomology (𝟙 (tensorObj K L))
    (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K L))) p q

/-- The canonical map from the native graded tensor to the finite
antidiagonal biproduct in one total degree. -/
def toAntidiagonal (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    ((homologyFunctor.obj K) ⊗ (homologyFunctor.obj L)) n ⟶
      ⨁ fun ij : KunnethTensorIndex n => K.homology ij.val.1 ⊗ L.homology ij.val.2 :=
  GradedObject.TensorAntidiagonal.toBiproduct
    (homologyFunctor.obj K) (homologyFunctor.obj L) n

/-- The reverse comparison, using the native graded tensor injections. -/
def fromAntidiagonal (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    (⨁ fun ij : KunnethTensorIndex n => K.homology ij.val.1 ⊗ L.homology ij.val.2) ⟶
      ((homologyFunctor.obj K) ⊗ (homologyFunctor.obj L)) n :=
  GradedObject.TensorAntidiagonal.fromBiproduct
    (homologyFunctor.obj K) (homologyFunctor.obj L) n

@[reassoc (attr := simp)]
theorem ι_toAntidiagonal (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
      (homologyFunctor.obj L) p q n h ≫ toAntidiagonal K L n =
    biproduct.ι (fun ij : KunnethTensorIndex n =>
      K.homology ij.val.1 ⊗ L.homology ij.val.2)
      ⟨(p, q), Finset.mem_antidiagonal.mpr h⟩ := by
  exact GradedObject.TensorAntidiagonal.ι_toBiproduct
    (homologyFunctor.obj K) (homologyFunctor.obj L) p q n h

@[reassoc (attr := simp)]
theorem ι_fromAntidiagonal (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) (ij : KunnethTensorIndex n) :
    biproduct.ι (fun ij : KunnethTensorIndex n =>
      K.homology ij.val.1 ⊗ L.homology ij.val.2) ij ≫ fromAntidiagonal K L n =
    GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
      (homologyFunctor.obj L) ij.val.1 ij.val.2 n
      (Finset.mem_antidiagonal.mp ij.property) := by
  exact GradedObject.TensorAntidiagonal.ι_fromBiproduct
    (homologyFunctor.obj K) (homologyFunctor.obj L) n ij

/-- The earned comparison between the two actual tensor sources. -/
def antidiagonalIso (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    ((homologyFunctor.obj K) ⊗ (homologyFunctor.obj L)) n ≅
      ⨁ fun ij : KunnethTensorIndex n => K.homology ij.val.1 ⊗ L.homology ij.val.2 :=
  GradedObject.TensorAntidiagonal.iso
    (homologyFunctor.obj K) (homologyFunctor.obj L) n

/-- The canonical cycle Künneth tensorator on the native graded tensor. -/
def tensorator (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    homologyFunctor.obj K ⊗ homologyFunctor.obj L ⟶ homologyFunctor.obj (K ⊗ L) :=
  fun n => toAntidiagonal K L n ≫ kunnethHomologyTensorMap K L n

@[reassoc (attr := simp)]
theorem ι_tensorator (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
      (homologyFunctor.obj L) p q n h ≫ tensorator K L n =
      pair K L p q ≫ (homologyIsoOfEq (tensorObj K L) h).hom := by
  change GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
      (homologyFunctor.obj L) p q n h ≫
      (toAntidiagonal K L n ≫ kunnethHomologyTensorMap K L n) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ kunnethHomologyTensorMap K L n)
      (ι_toAntidiagonal K L p q n h)).trans
        (kunnethHomologyTensorMap_ι K L n
          ⟨(p, q), Finset.mem_antidiagonal.mpr h⟩))

/-- The canonical Künneth tensorator is the literal existing map under the
earned antidiagonal comparison. -/
theorem tensorator_eq (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    tensorator K L n = (antidiagonalIso K L n).hom ≫ kunnethHomologyTensorMap K L n := rfl

@[reassoc]
theorem toAntidiagonal_naturality {K L K' L' : (ChainComplex (ModuleCat.{u} R) ℕ)} (f : K ⟶ K') (g : L ⟶ L')
    (n : ℕ) :
    (homologyFunctor.map f ⊗ₘ homologyFunctor.map g) n ≫ toAntidiagonal K' L' n =
      toAntidiagonal K L n ≫ kunnethTensorSourceMap f g n := by
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  have ht := GradedObject.Monoidal.ι_tensorHom
    (homologyFunctor.map f) (homologyFunctor.map g) p q n h
  have hp := congrArg (fun z =>
    (homologyMap f p ⊗ₘ homologyMap g q) ≫ z)
      (ι_toAntidiagonal K' L' p q n h)
  have hl := (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ toAntidiagonal K' L' n) ht).trans
      ((Category.assoc _ _ _).trans hp))
  have hr := (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ kunnethTensorSourceMap f g n)
      (ι_toAntidiagonal K L p q n h))
  exact hl.trans ((kunnethTensorSourceMap_ι f g n
    ⟨(p, q), Finset.mem_antidiagonal.mpr h⟩).symm.trans hr.symm)

@[reassoc]
theorem tensorator_naturality {K L K' L' : (ChainComplex (ModuleCat.{u} R) ℕ)} (f : K ⟶ K') (g : L ⟶ L') :
    (homologyFunctor.map f ⊗ₘ homologyFunctor.map g) ≫ tensorator K' L' =
      tensorator K L ≫ homologyFunctor.map (f ⊗ₘ g) := by
  funext n
  change ((homologyFunctor.map f ⊗ₘ homologyFunctor.map g) n) ≫
      (toAntidiagonal K' L' n ≫ kunnethHomologyTensorMap K' L' n) =
    (toAntidiagonal K L n ≫ kunnethHomologyTensorMap K L n) ≫
      homologyMap (f ⊗ₘ g) n
  rw [← Category.assoc, toAntidiagonal_naturality, Category.assoc,
    kunnethHomologyTensorMap_naturality]
  exact (Category.assoc _ _ _).symm

/-- The unit of graded homology is identified by the native homology of a
single complex. In other degrees both actual objects are zero. -/
def unitIso : 𝟙_ (GradedObject ℕ (ModuleCat.{u} R)) ≅ homologyFunctor.obj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) :=
  HomologicalComplex.GradedHomology.unitIso (V := (ModuleCat.{u} R))

/-- The actual scalar-unit map on graded homology. -/
def unitMap : 𝟙_ (GradedObject ℕ (ModuleCat.{u} R)) ⟶ homologyFunctor.obj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) :=
  HomologicalComplex.GradedHomology.unitMap (V := (ModuleCat.{u} R))

@[simp]
theorem unitMap_zero : unitMap (R := R) 0 =
    (GradedObject.Monoidal.tensorUnit₀ (I := ℕ) (C := (ModuleCat.{u} R))).hom ≫
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv := by
  exact HomologicalComplex.GradedHomology.unitMap_zero (V := (ModuleCat.{u} R))

instance unitMap_isIso : IsIso (unitMap (R := R)) := by
  exact HomologicalComplex.GradedHomology.unitMap_isIso (V := (ModuleCat.{u} R))

/-- The actual unit comparison in each degree, obtained from the one
canonical graded unit isomorphism. -/
def unitComparison (n : ℕ) : (𝟙_ (GradedObject ℕ (ModuleCat.{u} R))) n ≅
  (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)).homology n :=
  (GradedObject.eval n).mapIso (unitIso (R := R))

@[simp]
theorem unitComparison_zero : unitComparison (R := R) 0 =
    (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).symm := by
  apply Iso.ext
  change unitMap (R := R) 0 = (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv
  rw [unitMap_zero]
  change 𝟙 (𝟙_ (ModuleCat.{u} R)) ≫ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv = _
  rw [Category.id_comp]

/-- Flat terms and flat homology in the first factor suffice for the
canonical tensorator in a chosen degree. -/
theorem isIso_tensorator_of_flat_homology (K L : (ChainComplex (ModuleCat.{u} R) ℕ))
    (hK : ∀ i : ℕ, Module.Flat R (K.X i))
    (hHK : ∀ i : ℕ, Module.Flat R (K.homology i)) (n : ℕ) :
    IsIso (tensorator K L n) := by
  letI := isIso_kunnethHomologyTensorMap_of_flat_homology K L hK hHK n
  let e := (antidiagonalIso K L n) ≪≫ asIso (kunnethHomologyTensorMap K L n)
  change IsIso e.hom
  infer_instance

/-- The existing field Künneth theorem applies to the actual canonical
tensorator; no replacement tensor map is chosen. -/
theorem isIso_tensorator_of_field {k : Type u} [Field k]
    (K L : ChainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    IsIso (tensorator K L n) := by
  letI := isIso_kunnethHomologyTensorMap_of_field K L n
  let e := (antidiagonalIso K L n) ≪≫ asIso (kunnethHomologyTensorMap K L n)
  change IsIso e.hom
  infer_instance

/-- Objectwise invertibility of the canonical Künneth maps packages their
actual inverses into a graded isomorphism. -/
def tensoratorIso (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) [∀ n : ℕ, IsIso (kunnethHomologyTensorMap K L n)] :
    homologyFunctor.obj K ⊗ homologyFunctor.obj L ≅ homologyFunctor.obj (K ⊗ L) :=
  GradedObject.isoMk _ _ fun n => by
    letI : IsIso (tensorator K L n) := by
      let e := (antidiagonalIso K L n) ≪≫ asIso (kunnethHomologyTensorMap K L n)
      change IsIso e.hom
      infer_instance
    exact asIso (tensorator K L n)

@[simp]
theorem tensoratorIso_hom (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) [∀ n : ℕ, IsIso (kunnethHomologyTensorMap K L n)] :
    (tensoratorIso K L).hom = tensorator K L := rfl

instance tensorator_isIso (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) [∀ n : ℕ, IsIso (kunnethHomologyTensorMap K L n)] :
    IsIso (tensorator K L) := by
  rw [← tensoratorIso_hom K L]
  infer_instance

end HomologicalComplex.Kunneth
