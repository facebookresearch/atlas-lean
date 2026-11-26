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
# The Künneth tensorator on graded homology

Let `R : Type u` be a commutative ring and work with nonnegative chain complexes in
`ModuleCat.{u} R`. The degree-`n` tensor of their graded homologies is the coproduct over
`i+j=n`, canonically isomorphic to the finite antidiagonal biproduct.

Composing this comparison with the cycle pairing gives a natural graded tensorator `H(K) ⊗
H(L) → H(K ⊗ L)`. The graded tensor unit is identified with homology of the chain tensor unit.
Flat terms and flat homology of the first complex make the tensorator invertible in each
degree; over a field these conditions hold automatically.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.Kunneth

variable {R : Type u} [CommRing R]


/-- Finite biproducts in the common-universe module category.

The abelian category `ModuleCat.{u} R` has the finite biproducts used by the tensor
antidiagonal. -/
local instance moduleFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- The graded homology functor for nonnegative module chains.

Send a chain complex to its natural-number-graded family of homology modules. -/
abbrev homologyFunctor : (ChainComplex (ModuleCat.{u} R) ℕ) ⥤ (GradedObject ℕ (ModuleCat.{u} R)) :=
  gradedHomologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- The bidegree cycle pairing on module homology.

Tensor cycle representatives to obtain `H_p(K) ⊗ H_q(L) → H_(p+q)(K ⊗ L)`. -/
abbrev pair (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q : ℕ) :
    K.homology p ⊗ L.homology q ⟶ (tensorObj K L).homology (p + q) :=
  ChainGradedPairing.pairHomology (𝟙 (tensorObj K L))
    (ChainGradedPairing.homologyDescentData (𝟙 (tensorObj K L))) p q

/-- The coproduct-to-biproduct comparison of a graded homology tensor.

In degree `n`, identify the graded tensor coproduct over `p+q=n` with the finite antidiagonal
biproduct. -/
def toAntidiagonal (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    ((homologyFunctor.obj K) ⊗ (homologyFunctor.obj L)) n ⟶
      ⨁ fun ij : KunnethTensorIndex n => K.homology ij.val.1 ⊗ L.homology ij.val.2 :=
  GradedObject.TensorAntidiagonal.toBiproduct
    (homologyFunctor.obj K) (homologyFunctor.obj L) n

/-- The biproduct-to-coproduct comparison of a graded homology tensor.

Send each finite antidiagonal tensor summand to its graded tensor inclusion. -/
def fromAntidiagonal (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    (⨁ fun ij : KunnethTensorIndex n => K.homology ij.val.1 ⊗ L.homology ij.val.2) ⟶
      ((homologyFunctor.obj K) ⊗ (homologyFunctor.obj L)) n :=
  GradedObject.TensorAntidiagonal.fromBiproduct
    (homologyFunctor.obj K) (homologyFunctor.obj L) n

/-- The graded tensor inclusion under antidiagonal comparison.

The bidegree `(p,q)` graded inclusion followed by the comparison is the corresponding finite
biproduct inclusion. -/
@[reassoc (attr := simp)]
theorem ι_toAntidiagonal (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
      (homologyFunctor.obj L) p q n h ≫ toAntidiagonal K L n =
    biproduct.ι (fun ij : KunnethTensorIndex n =>
      K.homology ij.val.1 ⊗ L.homology ij.val.2)
      ⟨(p, q), Finset.mem_antidiagonal.mpr h⟩ := by
  exact GradedObject.TensorAntidiagonal.ι_toBiproduct
    (homologyFunctor.obj K) (homologyFunctor.obj L) p q n h

/-- The antidiagonal inclusion under inverse tensor comparison.

A finite biproduct inclusion followed by the inverse comparison is the corresponding graded
tensor inclusion. -/
@[reassoc (attr := simp)]
theorem ι_fromAntidiagonal (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) (ij : KunnethTensorIndex n) :
    biproduct.ι (fun ij : KunnethTensorIndex n =>
      K.homology ij.val.1 ⊗ L.homology ij.val.2) ij ≫ fromAntidiagonal K L n =
    GradedObject.Monoidal.ιTensorObj (homologyFunctor.obj K)
      (homologyFunctor.obj L) ij.val.1 ij.val.2 n
      (Finset.mem_antidiagonal.mp ij.property) := by
  exact GradedObject.TensorAntidiagonal.ι_fromBiproduct
    (homologyFunctor.obj K) (homologyFunctor.obj L) n ij

/-- The graded-tensor antidiagonal isomorphism.

The degree-`n` graded homology tensor is canonically isomorphic to the finite biproduct
indexed by `p+q=n`. -/
def antidiagonalIso (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    ((homologyFunctor.obj K) ⊗ (homologyFunctor.obj L)) n ≅
      ⨁ fun ij : KunnethTensorIndex n => K.homology ij.val.1 ⊗ L.homology ij.val.2 :=
  GradedObject.TensorAntidiagonal.iso
    (homologyFunctor.obj K) (homologyFunctor.obj L) n

/-- The canonical graded Künneth tensorator.

In degree `n`, apply the antidiagonal comparison and then the finite-sum homology tensor
pairing. -/
def tensorator (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) :
    homologyFunctor.obj K ⊗ homologyFunctor.obj L ⟶ homologyFunctor.obj (K ⊗ L) :=
  fun n => toAntidiagonal K L n ≫ kunnethHomologyTensorMap K L n

/-- The bidegree component of the graded Künneth tensorator.

The graded tensor inclusion at `(p,q)` followed by the tensorator is the cycle pairing,
transported to its chosen total degree. -/
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

/-- The finite-antidiagonal formula for the Künneth tensorator.

The tensorator component equals the forward antidiagonal isomorphism followed by the canonical
finite-sum homology tensor map. -/
theorem tensorator_eq (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) (n : ℕ) :
    tensorator K L n = (antidiagonalIso K L n).hom ≫ kunnethHomologyTensorMap K L n := rfl

/-- Naturality of graded homology antidiagonal comparison.

Tensor products of homology maps commute with the comparison to the finite antidiagonal source
map. -/
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

/-- Naturality of the graded Künneth tensorator.

The tensorator commutes with homology maps in both complex variables and homology of their
tensor chain map. -/
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

/-- The unit isomorphism of graded module homology.

The graded tensor unit is isomorphic to homology of the chain tensor unit, using degree-zero
single-complex homology. -/
def unitIso : 𝟙_ (GradedObject ℕ (ModuleCat.{u} R)) ≅ homologyFunctor.obj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) :=
  HomologicalComplex.GradedHomology.unitIso (V := (ModuleCat.{u} R))

/-- The unit map of graded module homology.

The canonical unit isomorphism gives the map from the graded tensor unit to homology of the
chain tensor unit. -/
def unitMap : 𝟙_ (GradedObject ℕ (ModuleCat.{u} R)) ⟶ homologyFunctor.obj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) :=
  HomologicalComplex.GradedHomology.unitMap (V := (ModuleCat.{u} R))

/-- The degree-zero unit map of graded module homology.

The degree-zero component is the graded-unit coordinate followed by the inverse single-complex
homology comparison. -/
@[simp]
theorem unitMap_zero : unitMap (R := R) 0 =
    (GradedObject.Monoidal.tensorUnit₀ (I := ℕ) (C := (ModuleCat.{u} R))).hom ≫
      (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv := by
  exact HomologicalComplex.GradedHomology.unitMap_zero (V := (ModuleCat.{u} R))

/-- Invertibility of the graded homology unit map.

The unit map is the forward map of the graded homology unit isomorphism. -/
instance unitMap_isIso : IsIso (unitMap (R := R)) := by
  exact HomologicalComplex.GradedHomology.unitMap_isIso (V := (ModuleCat.{u} R))

/-- The degreewise unit comparison of graded homology.

Evaluate the graded unit isomorphism in degree `n` to compare the unit component with homology
of the chain unit. -/
def unitComparison (n : ℕ) : (𝟙_ (GradedObject ℕ (ModuleCat.{u} R))) n ≅
  (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)).homology n :=
  (GradedObject.eval n).mapIso (unitIso (R := R))

/-- The single-complex coordinate of the degree-zero unit comparison.

The degree-zero unit isomorphism is the inverse homology comparison for the tensor unit
concentrated in degree zero. -/
@[simp]
theorem unitComparison_zero : unitComparison (R := R) 0 =
    (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).symm := by
  apply Iso.ext
  change unitMap (R := R) 0 = (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv
  rw [unitMap_zero]
  change 𝟙 (𝟙_ (ModuleCat.{u} R)) ≫ (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat.{u} R))).inv = _
  rw [Category.id_comp]

/-- The Künneth tensorator isomorphism under flatness of the first complex.

If every term and every homology module of `K` is flat over `R`, the canonical tensorator with
any nonnegative `L` is an isomorphism in degree `n`. -/
theorem isIso_tensorator_of_flat_homology (K L : (ChainComplex (ModuleCat.{u} R) ℕ))
    (hK : ∀ i : ℕ, Module.Flat R (K.X i))
    (hHK : ∀ i : ℕ, Module.Flat R (K.homology i)) (n : ℕ) :
    IsIso (tensorator K L n) := by
  letI := isIso_kunnethHomologyTensorMap_of_flat_homology K L hK hHK n
  let e := (antidiagonalIso K L n) ≪≫ asIso (kunnethHomologyTensorMap K L n)
  change IsIso e.hom
  infer_instance

/-- The graded Künneth tensorator isomorphism over a field.

For two nonnegative module chain complexes over a field, every tensorator component is an
isomorphism. -/
theorem isIso_tensorator_of_field {k : Type u} [Field k]
    (K L : ChainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    IsIso (tensorator K L n) := by
  letI := isIso_kunnethHomologyTensorMap_of_field K L n
  let e := (antidiagonalIso K L n) ≪≫ asIso (kunnethHomologyTensorMap K L n)
  change IsIso e.hom
  infer_instance

/-- The graded isomorphism of invertible Künneth tensorator components.

If all canonical homology tensor maps for `K,L` are isomorphisms, their component inverses
give a graded isomorphism with forward map the tensorator. -/
def tensoratorIso (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) [∀ n : ℕ, IsIso (kunnethHomologyTensorMap K L n)] :
    homologyFunctor.obj K ⊗ homologyFunctor.obj L ≅ homologyFunctor.obj (K ⊗ L) :=
  GradedObject.isoMk _ _ fun n => by
    letI : IsIso (tensorator K L n) := by
      let e := (antidiagonalIso K L n) ≪≫ asIso (kunnethHomologyTensorMap K L n)
      change IsIso e.hom
      infer_instance
    exact asIso (tensorator K L n)

/-- The forward map of the graded Künneth isomorphism.

The assembled graded isomorphism has the canonical tensorator as its forward map. -/
@[simp]
theorem tensoratorIso_hom (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) [∀ n : ℕ, IsIso (kunnethHomologyTensorMap K L n)] :
    (tensoratorIso K L).hom = tensorator K L := rfl

/-- Invertibility of the full graded Künneth tensorator.

If every finite-sum homology tensor map is invertible, the full graded tensorator is
invertible. -/
instance tensorator_isIso (K L : (ChainComplex (ModuleCat.{u} R) ℕ)) [∀ n : ℕ, IsIso (kunnethHomologyTensorMap K L n)] :
    IsIso (tensorator K L) := by
  rw [← tensoratorIso_hom K L]
  infer_instance

end HomologicalComplex.Kunneth
