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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.MatrixCoinvariants
public import MathlibExt.Algebra.Homology.HomologyCoalgebra.NativeUnitComparison
public import MathlibExt.Algebra.Homology.HomologyCoalgebra.Basic

/-!
# Homology coalgebras of finite matrix Lie algebras

For a unital algebra over a field, finite matrix Chevalley–Eilenberg homology and its
scalar-adjoint coinvariants carry coaugmented graded cocommutative coalgebras. The field and
coefficient algebra use a common carrier universe in this module.

Matrix inclusions, coefficient maps, and coinvariant projections induce the corresponding
homology coalgebra maps.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ComonObj

universe u

namespace ChevalleyEilenberg

variable (k : Type u) [Field k]
variable (A : Type u) [Ring A] [Algebra k A]

attribute [local instance] ComonObj.instTensorUnit


local instance fieldTensorComparison_isIso (C D : (ChainComplex (ModuleCat.{u} k) ℕ)) (n : ℕ) :
    IsIso (HomologicalComplex.kunnethHomologyTensorMap C D n) :=
  HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field C D n

/-- The matrix CE comonoid in the fixed canonical lifted-unit source category. -/
def matrixLiftedUnitCoalgebra (m : ℕ) : Comon (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k) :=
  nativeCoalgebra k (Matrix (Fin m) (Fin m) A)

/-- The unit/tensor comparison gives the common-universe chain comonoid. -/
def matrixOrdinaryCoalgebra (m : ℕ) : Comon (ChainComplex (ModuleCat.{u} k) ℕ) :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeComonFunctor.obj
    (matrixLiftedUnitCoalgebra k A m)

@[simp]
theorem matrixOrdinaryCoalgebra_X (m : ℕ) : (matrixOrdinaryCoalgebra k A m).X = matrixComplex k A m := rfl

/-- The graded homology object, with its matrix CE carrier. -/
def matrixHomologyGraded (m : ℕ) : (GradedObject ℕ (ModuleCat.{u} k)) := fun n => matrixHomology k A m n

/-- The general canonical field Künneth provider establishes the matrix homology comonoid. -/
def matrixHomologyComonObj (m : ℕ) : ComonObj (matrixHomologyGraded k A m) := by
  letI : ComonObj (matrixOrdinaryCoalgebra k A m).X := (matrixOrdinaryCoalgebra k A m).comon
  exact HomologicalComplex.HomologyCoalgebra.comonObjOfField (matrixOrdinaryCoalgebra k A m).X

/-- The coaugmented graded coalgebra on finite matrix Chevalley–Eilenberg homology over a field. -/
def matrixHomologyCoalgebra (m : ℕ) : Comon (GradedObject ℕ (ModuleCat.{u} k)) :=
  { X := matrixHomologyGraded k A m, comon := matrixHomologyComonObj k A m }

/-- The source coaugmentation converts through the scalar unit isomorphism. -/
def matrixOrdinaryCoaug (m : ℕ) : 𝟙_ (ChainComplex (ModuleCat.{u} k) ℕ) ⟶ (matrixOrdinaryCoalgebra k A m).X :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeCoaug
    (matrixLiftedUnitCoalgebra k A m).X (matrixCoaug k A m)

/-- The converted finite-matrix coaugmentation preserves the comonoid. -/
def matrixOrdinaryCoaugIsComonHom (m : ℕ) :
    letI : ComonObj (matrixOrdinaryCoalgebra k A m).X := (matrixOrdinaryCoalgebra k A m).comon
    IsComonHom (matrixOrdinaryCoaug k A m) := by
  let C : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k := (matrixLiftedUnitCoalgebra k A m).X
  let η : 𝟙_ (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k) ⟶ C := matrixCoaug k A m
  letI : ComonObj C := (matrixLiftedUnitCoalgebra k A m).comon
  letI : IsComonHom η := nativeComplexCoaugIsComonHom k (Matrix (Fin m) (Fin m) A)
  exact HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeCoaugIsComonHom C η

/-- The matrix homology coaugmentation is the canonical homology/unit map. -/
def matrixHomologyCoaug (m : ℕ) : 𝟙_ (GradedObject ℕ (ModuleCat.{u} k)) ⟶ matrixHomologyGraded k A m := by
  letI : ComonObj (matrixOrdinaryCoalgebra k A m).X := (matrixOrdinaryCoalgebra k A m).comon
  exact HomologicalComplex.HomologyCoalgebra.coaug (matrixOrdinaryCoalgebra k A m).X
    (matrixOrdinaryCoaug k A m)

/-- Matrix homology coproduct, from the general field provider. -/
def matrixHomologyComul (m : ℕ) :
    matrixHomologyGraded k A m ⟶ matrixHomologyGraded k A m ⊗ matrixHomologyGraded k A m :=
  (matrixHomologyComonObj k A m).comul

/-- Matrix homology counit. -/
def matrixHomologyCounit (m : ℕ) : matrixHomologyGraded k A m ⟶ 𝟙_ (GradedObject ℕ (ModuleCat.{u} k)) :=
  (matrixHomologyComonObj k A m).counit

/-- The matrix homology coaugmentation is a comonoid morphism. -/
def matrixHomologyCoaugIsComonHom (m : ℕ) :
    letI : ComonObj (matrixHomologyGraded k A m) := matrixHomologyComonObj k A m
    IsComonHom (matrixHomologyCoaug k A m) := by
  letI : ComonObj (matrixOrdinaryCoalgebra k A m).X := (matrixOrdinaryCoalgebra k A m).comon
  letI : IsComonHom (matrixOrdinaryCoaug k A m) := matrixOrdinaryCoaugIsComonHom k A m
  exact HomologicalComplex.HomologyCoalgebra.coaugIsComonHom
    (matrixOrdinaryCoalgebra k A m).X (matrixOrdinaryCoaug k A m)

/-- The converted source comonoid map for every zero corner. -/
def matrixOrdinaryZeroCornerMap {m n : ℕ} (h : m ≤ n) :
    matrixOrdinaryCoalgebra k A m ⟶ matrixOrdinaryCoalgebra k A n := by
  let C := matrixLiftedUnitCoalgebra k A m
  let D := matrixLiftedUnitCoalgebra k A n
  let g : C.X ⟶ D.X := matrixZeroCornerMap k A h
  letI : ComonObj C.X := C.comon
  letI : ComonObj D.X := D.comon
  let gC : C ⟶ D := { hom := g, isComonHom_hom := matrixZeroCornerMapIsComonHom k A h }
  exact HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeComonFunctor.map gC

/-- The homology map of the converted zero-corner comonoid morphism. -/
def matrixHomologyZeroCornerMap {m n : ℕ} (h : m ≤ n) :
    matrixHomologyGraded k A m ⟶ matrixHomologyGraded k A n :=
  fun d => HomologicalComplex.homologyMap (matrixOrdinaryZeroCornerMap k A h).hom d

/-- The zero-corner homology map preserves the homology comonoids. -/
def matrixHomologyZeroCornerMapIsComonHom {m n : ℕ} (h : m ≤ n) :
    letI : ComonObj (matrixHomologyGraded k A m) := matrixHomologyComonObj k A m
    letI : ComonObj (matrixHomologyGraded k A n) := matrixHomologyComonObj k A n
    IsComonHom (matrixHomologyZeroCornerMap k A h) := by
  letI : ComonObj (matrixOrdinaryCoalgebra k A m).X := (matrixOrdinaryCoalgebra k A m).comon
  letI : ComonObj (matrixOrdinaryCoalgebra k A n).X := (matrixOrdinaryCoalgebra k A n).comon
  letI : IsComonHom (matrixOrdinaryZeroCornerMap k A h).hom := inferInstance
  exact HomologicalComplex.HomologyCoalgebra.mapIsComonHom
    (matrixOrdinaryCoalgebra k A m).X (matrixOrdinaryZeroCornerMap k A h).hom

/-- The action cokernel comonoid in the canonical lifted-unit source category. -/
def matrixCoinvariantLiftedUnitCoalgebra (m : ℕ) : Comon (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k) :=
  matrixCoinvariantCoalgebra k A m

/-- The common-universe unit conversion of the coinvariant chain coalgebra. -/
def matrixCoinvariantOrdinaryCoalgebra (m : ℕ) : Comon (ChainComplex (ModuleCat.{u} k) ℕ) :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeComonFunctor.obj
    (matrixCoinvariantLiftedUnitCoalgebra k A m)

/-- The graded homology of the matrix coinvariant complex. -/
def matrixCoinvariantHomologyGraded (m : ℕ) : (GradedObject ℕ (ModuleCat.{u} k)) := fun d => matrixCoinvariantHomology
  k A m d

/-- Field homology comonoid of the coinvariant cokernel. -/
def matrixCoinvariantHomologyComonObj (m : ℕ) : ComonObj (matrixCoinvariantHomologyGraded k A m) := by
  letI : ComonObj (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
    (matrixCoinvariantOrdinaryCoalgebra k A m).comon
  exact HomologicalComplex.HomologyCoalgebra.comonObjOfField
    (matrixCoinvariantOrdinaryCoalgebra k A m).X

/-- Coinvariant homology coalgebra, with its homology objects. -/
def matrixCoinvariantHomologyCoalgebra (m : ℕ) : Comon (GradedObject ℕ (ModuleCat.{u} k)) :=
  { X := matrixCoinvariantHomologyGraded k A m, comon := matrixCoinvariantHomologyComonObj k A m }

/-- The converted coaugmentation of the matrix coinvariant chain coalgebra. -/
def matrixCoinvariantOrdinaryCoaug (m : ℕ) :
    𝟙_ (ChainComplex (ModuleCat.{u} k) ℕ) ⟶ (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeCoaug
    (matrixCoinvariantLiftedUnitCoalgebra k A m).X (matrixCoinvariantCoaug k A m)

/-- The converted coinvariant coaugmentation preserves the comonoid. -/
def matrixCoinvariantOrdinaryCoaugIsComonHom (m : ℕ) :
    letI : ComonObj (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
      (matrixCoinvariantOrdinaryCoalgebra k A m).comon
    IsComonHom (matrixCoinvariantOrdinaryCoaug k A m) := by
  let C : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k := (matrixCoinvariantLiftedUnitCoalgebra k A m).X
  let η : 𝟙_ (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k) ⟶ C := matrixCoinvariantCoaug k A m
  letI : ComonObj C := (matrixCoinvariantLiftedUnitCoalgebra k A m).comon
  letI : IsComonHom η := adjointCoinvariantCoaugIsComonHom k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)
  exact HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeCoaugIsComonHom C η

/-- The canonical coaugmentation of matrix coinvariant homology. -/
def matrixCoinvariantHomologyCoaug (m : ℕ) : 𝟙_ (GradedObject ℕ (ModuleCat.{u} k)) ⟶ matrixCoinvariantHomologyGraded k
  A m := by
  letI : ComonObj (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
    (matrixCoinvariantOrdinaryCoalgebra k A m).comon
  exact HomologicalComplex.HomologyCoalgebra.coaug
    (matrixCoinvariantOrdinaryCoalgebra k A m).X (matrixCoinvariantOrdinaryCoaug k A m)

/-- The coinvariant homology coaugmentation is a comonoid morphism. -/
def matrixCoinvariantHomologyCoaugIsComonHom (m : ℕ) :
    letI : ComonObj (matrixCoinvariantHomologyGraded k A m) := matrixCoinvariantHomologyComonObj k A m
    IsComonHom (matrixCoinvariantHomologyCoaug k A m) := by
  letI : ComonObj (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
    (matrixCoinvariantOrdinaryCoalgebra k A m).comon
  letI : IsComonHom (matrixCoinvariantOrdinaryCoaug k A m) :=
    matrixCoinvariantOrdinaryCoaugIsComonHom k A m
  exact HomologicalComplex.HomologyCoalgebra.coaugIsComonHom
    (matrixCoinvariantOrdinaryCoalgebra k A m).X (matrixCoinvariantOrdinaryCoaug k A m)

/-- The converted zero-corner morphism of coinvariant chain coalgebras. -/
def matrixCoinvariantOrdinaryZeroCornerMap {m n : ℕ} (h : m ≤ n) :
    matrixCoinvariantOrdinaryCoalgebra k A m ⟶ matrixCoinvariantOrdinaryCoalgebra k A n := by
  let C := matrixCoinvariantLiftedUnitCoalgebra k A m
  let D := matrixCoinvariantLiftedUnitCoalgebra k A n
  let g : C.X ⟶ D.X := matrixCoinvariantZeroCornerMap k A h
  letI : ComonObj C.X := C.comon
  letI : ComonObj D.X := D.comon
  let gC : C ⟶ D := { hom := g, isComonHom_hom := matrixCoinvariantZeroCornerMapIsComonHom k A h }
  exact HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeComonFunctor.map gC

/-- The zero-corner map on the graded coinvariant homology. -/
def matrixCoinvariantHomologyZeroCornerMap {m n : ℕ} (h : m ≤ n) :
    matrixCoinvariantHomologyGraded k A m ⟶ matrixCoinvariantHomologyGraded k A n :=
  fun d => HomologicalComplex.homologyMap (matrixCoinvariantOrdinaryZeroCornerMap k A h).hom d

/-- The zero-corner homology map preserves the coinvariant homology comonoids. -/
def matrixCoinvariantHomologyZeroCornerMapIsComonHom {m n : ℕ} (h : m ≤ n) :
    letI : ComonObj (matrixCoinvariantHomologyGraded k A m) := matrixCoinvariantHomologyComonObj k A m
    letI : ComonObj (matrixCoinvariantHomologyGraded k A n) := matrixCoinvariantHomologyComonObj k A n
    IsComonHom (matrixCoinvariantHomologyZeroCornerMap k A h) := by
  letI : ComonObj (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
    (matrixCoinvariantOrdinaryCoalgebra k A m).comon
  letI : ComonObj (matrixCoinvariantOrdinaryCoalgebra k A n).X :=
    (matrixCoinvariantOrdinaryCoalgebra k A n).comon
  letI : IsComonHom (matrixCoinvariantOrdinaryZeroCornerMap k A h).hom := inferInstance
  exact HomologicalComplex.HomologyCoalgebra.mapIsComonHom
    (matrixCoinvariantOrdinaryCoalgebra k A m).X (matrixCoinvariantOrdinaryZeroCornerMap k A h).hom

end ChevalleyEilenberg
