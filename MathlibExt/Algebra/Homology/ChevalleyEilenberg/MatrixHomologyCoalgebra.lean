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
# Field homology coalgebras of matrices and their scalar coinvariants

Let `k` be a field and `A` a unital `k`-algebra, with carriers in a common universe. The
matrix CE chain coalgebra and its scalar-adjoint coinvariant coalgebra transport through the
scalar-unit comparison to the module chain tensor category.

The field Künneth isomorphism gives graded homology comultiplications, counits, and
coaugmentations for both complexes. Zero-extension maps preserve the chain comonoids and
induce comonoid maps on their graded homology.
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


/-- The field Künneth isomorphism for module chain complexes.

Over a field, the canonical map from tensor products of homology to homology of a tensor total
is an isomorphism in every degree. -/
local instance fieldTensorComparison_isIso (C D : (ChainComplex (ModuleCat.{u} k) ℕ)) (n : ℕ) :
    IsIso (HomologicalComplex.kunnethHomologyTensorMap C D n) :=
  HomologicalComplex.isIso_kunnethHomologyTensorMap_of_field C D n

/-- The finite matrix CE coalgebra with a lifted scalar unit.

Take the canonical matrix CE coalgebra in the lifted-unit source chain category. -/
def matrixLiftedUnitCoalgebra (m : ℕ) : Comon (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k) :=
  nativeCoalgebra k (Matrix (Fin m) (Fin m) A)

/-- The finite matrix CE coalgebra after scalar-unit comparison.

The lifted-unit comparison gives its comonoid structure in the common-universe module chain
category. -/
def matrixOrdinaryCoalgebra (m : ℕ) : Comon (ChainComplex (ModuleCat.{u} k) ℕ) :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeComonFunctor.obj
    (matrixLiftedUnitCoalgebra k A m)

/-- The carrier of the compared finite matrix chain coalgebra.

Its chain complex is the canonical finite matrix CE complex. -/
@[simp]
theorem matrixOrdinaryCoalgebra_X (m : ℕ) : (matrixOrdinaryCoalgebra k A m).X = matrixComplex k A m := rfl

/-- The graded homology object of a finite matrix CE complex.

In degree `n`, this graded object is matrix CE homology at the given size. -/
def matrixHomologyGraded (m : ℕ) : (GradedObject ℕ (ModuleCat.{u} k)) := fun n => matrixHomology k A m n

/-- The comonoid structure of finite matrix CE homology over a field.

Use the field Künneth isomorphism to transfer the compared matrix chain comultiplication and
counit to graded homology. -/
def matrixHomologyComonObj (m : ℕ) : ComonObj (matrixHomologyGraded k A m) := by
  letI : ComonObj (matrixOrdinaryCoalgebra k A m).X := (matrixOrdinaryCoalgebra k A m).comon
  exact HomologicalComplex.HomologyCoalgebra.comonObjOfField (matrixOrdinaryCoalgebra k A m).X

/-- The bundled graded finite matrix CE homology coalgebra.

Bundle the matrix homology graded object with its field Künneth comonoid structure. -/
def matrixHomologyCoalgebra (m : ℕ) : Comon (GradedObject ℕ (ModuleCat.{u} k)) :=
  { X := matrixHomologyGraded k A m, comon := matrixHomologyComonObj k A m }

/-- The coaugmentation of the compared matrix chain coalgebra.

Transport the canonical matrix CE coaugmentation through the scalar-unit isomorphism. -/
def matrixOrdinaryCoaug (m : ℕ) : 𝟙_ (ChainComplex (ModuleCat.{u} k) ℕ) ⟶ (matrixOrdinaryCoalgebra k A m).X :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeCoaug
    (matrixLiftedUnitCoalgebra k A m).X (matrixCoaug k A m)

/-- Comonoid compatibility of compared matrix chain coaugmentation.

The transported matrix coaugmentation preserves counit and comultiplication. -/
def matrixOrdinaryCoaugIsComonHom (m : ℕ) :
    letI : ComonObj (matrixOrdinaryCoalgebra k A m).X := (matrixOrdinaryCoalgebra k A m).comon
    IsComonHom (matrixOrdinaryCoaug k A m) := by
  let C : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k := (matrixLiftedUnitCoalgebra k A m).X
  let η : 𝟙_ (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k) ⟶ C := matrixCoaug k A m
  letI : ComonObj C := (matrixLiftedUnitCoalgebra k A m).comon
  letI : IsComonHom η := nativeComplexCoaugIsComonHom k (Matrix (Fin m) (Fin m) A)
  exact HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeCoaugIsComonHom C η

/-- The graded coaugmentation of finite matrix CE homology.

Apply the homology unit comparison and homology of the compared chain coaugmentation. -/
def matrixHomologyCoaug (m : ℕ) : 𝟙_ (GradedObject ℕ (ModuleCat.{u} k)) ⟶ matrixHomologyGraded k A m := by
  letI : ComonObj (matrixOrdinaryCoalgebra k A m).X := (matrixOrdinaryCoalgebra k A m).comon
  exact HomologicalComplex.HomologyCoalgebra.coaug (matrixOrdinaryCoalgebra k A m).X
    (matrixOrdinaryCoaug k A m)

/-- The graded coproduct of finite matrix CE homology.

The field homology comonoid comultiplication maps graded matrix homology to its graded tensor
square. -/
def matrixHomologyComul (m : ℕ) :
    matrixHomologyGraded k A m ⟶ matrixHomologyGraded k A m ⊗ matrixHomologyGraded k A m :=
  (matrixHomologyComonObj k A m).comul

/-- The graded counit of finite matrix CE homology.

The field homology comonoid counit maps matrix homology to the graded tensor unit. -/
def matrixHomologyCounit (m : ℕ) : matrixHomologyGraded k A m ⟶ 𝟙_ (GradedObject ℕ (ModuleCat.{u} k)) :=
  (matrixHomologyComonObj k A m).counit

/-- Comonoid compatibility of finite matrix homology coaugmentation.

The graded matrix coaugmentation preserves the homology counit and comultiplication. -/
def matrixHomologyCoaugIsComonHom (m : ℕ) :
    letI : ComonObj (matrixHomologyGraded k A m) := matrixHomologyComonObj k A m
    IsComonHom (matrixHomologyCoaug k A m) := by
  letI : ComonObj (matrixOrdinaryCoalgebra k A m).X := (matrixOrdinaryCoalgebra k A m).comon
  letI : IsComonHom (matrixOrdinaryCoaug k A m) := matrixOrdinaryCoaugIsComonHom k A m
  exact HomologicalComplex.HomologyCoalgebra.coaugIsComonHom
    (matrixOrdinaryCoalgebra k A m).X (matrixOrdinaryCoaug k A m)

/-- The compared matrix chain coalgebra map of zero extension.

The matrix zero-extension comonoid map transports through the scalar-unit comparison. -/
def matrixOrdinaryZeroCornerMap {m n : ℕ} (h : m ≤ n) :
    matrixOrdinaryCoalgebra k A m ⟶ matrixOrdinaryCoalgebra k A n := by
  let C := matrixLiftedUnitCoalgebra k A m
  let D := matrixLiftedUnitCoalgebra k A n
  let g : C.X ⟶ D.X := matrixZeroCornerMap k A h
  letI : ComonObj C.X := C.comon
  letI : ComonObj D.X := D.comon
  let gC : C ⟶ D := { hom := g, isComonHom_hom := matrixZeroCornerMapIsComonHom k A h }
  exact HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeComonFunctor.map gC

/-- The graded matrix homology map of zero extension.

Take homology of the compared zero-extension chain coalgebra morphism in each degree. -/
def matrixHomologyZeroCornerMap {m n : ℕ} (h : m ≤ n) :
    matrixHomologyGraded k A m ⟶ matrixHomologyGraded k A n :=
  fun d => HomologicalComplex.homologyMap (matrixOrdinaryZeroCornerMap k A h).hom d

/-- Comonoid compatibility of finite matrix homology size maps.

The zero-extension homology map preserves the field homology comultiplication and counit. -/
def matrixHomologyZeroCornerMapIsComonHom {m n : ℕ} (h : m ≤ n) :
    letI : ComonObj (matrixHomologyGraded k A m) := matrixHomologyComonObj k A m
    letI : ComonObj (matrixHomologyGraded k A n) := matrixHomologyComonObj k A n
    IsComonHom (matrixHomologyZeroCornerMap k A h) := by
  letI : ComonObj (matrixOrdinaryCoalgebra k A m).X := (matrixOrdinaryCoalgebra k A m).comon
  letI : ComonObj (matrixOrdinaryCoalgebra k A n).X := (matrixOrdinaryCoalgebra k A n).comon
  letI : IsComonHom (matrixOrdinaryZeroCornerMap k A h).hom := inferInstance
  exact HomologicalComplex.HomologyCoalgebra.mapIsComonHom
    (matrixOrdinaryCoalgebra k A m).X (matrixOrdinaryZeroCornerMap k A h).hom

/-- The lifted-unit chain coalgebra of scalar-adjoint matrix coinvariants.

Use the descended coinvariant CE coalgebra in the lifted-unit source category. -/
def matrixCoinvariantLiftedUnitCoalgebra (m : ℕ) : Comon (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k) :=
  matrixCoinvariantCoalgebra k A m

/-- The compared chain coalgebra of matrix scalar coinvariants.

Transport the coinvariant coalgebra through the scalar-unit comparison to the module chain
category. -/
def matrixCoinvariantOrdinaryCoalgebra (m : ℕ) : Comon (ChainComplex (ModuleCat.{u} k) ℕ) :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeComonFunctor.obj
    (matrixCoinvariantLiftedUnitCoalgebra k A m)

/-- The graded homology object of matrix scalar coinvariants.

In each degree, take homology of the scalar-adjoint matrix coinvariant complex. -/
def matrixCoinvariantHomologyGraded (m : ℕ) : (GradedObject ℕ (ModuleCat.{u} k)) := fun d => matrixCoinvariantHomology
  k A m d

/-- The field comonoid structure of matrix coinvariant homology.

The field Künneth isomorphism transfers the compared coinvariant chain coproduct and counit to
graded homology. -/
def matrixCoinvariantHomologyComonObj (m : ℕ) : ComonObj (matrixCoinvariantHomologyGraded k A m) := by
  letI : ComonObj (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
    (matrixCoinvariantOrdinaryCoalgebra k A m).comon
  exact HomologicalComplex.HomologyCoalgebra.comonObjOfField
    (matrixCoinvariantOrdinaryCoalgebra k A m).X

/-- The bundled graded homology coalgebra of matrix scalar coinvariants.

Bundle the coinvariant graded homology object with its field homology comonoid structure. -/
def matrixCoinvariantHomologyCoalgebra (m : ℕ) : Comon (GradedObject ℕ (ModuleCat.{u} k)) :=
  { X := matrixCoinvariantHomologyGraded k A m, comon := matrixCoinvariantHomologyComonObj k A m }

/-- The compared chain coaugmentation of matrix coinvariants.

Transport the descended matrix coinvariant coaugmentation through the scalar-unit comparison. -/
def matrixCoinvariantOrdinaryCoaug (m : ℕ) :
    𝟙_ (ChainComplex (ModuleCat.{u} k) ℕ) ⟶ (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
  HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeCoaug
    (matrixCoinvariantLiftedUnitCoalgebra k A m).X (matrixCoinvariantCoaug k A m)

/-- Comonoid compatibility of compared coinvariant coaugmentation.

The compared coinvariant chain coaugmentation preserves the comultiplication and counit. -/
def matrixCoinvariantOrdinaryCoaugIsComonHom (m : ℕ) :
    letI : ComonObj (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
      (matrixCoinvariantOrdinaryCoalgebra k A m).comon
    IsComonHom (matrixCoinvariantOrdinaryCoaug k A m) := by
  let C : HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k := (matrixCoinvariantLiftedUnitCoalgebra k A m).X
  let η : 𝟙_ (HomologicalComplex.HomologyCoalgebra.LiftedUnitChain k) ⟶ C := matrixCoinvariantCoaug k A m
  letI : ComonObj C := (matrixCoinvariantLiftedUnitCoalgebra k A m).comon
  letI : IsComonHom η := adjointCoinvariantCoaugIsComonHom k (Matrix (Fin m) (Fin m) A) (Matrix.scalarLieHom k A m)
  exact HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeCoaugIsComonHom C η

/-- The graded coaugmentation of matrix coinvariant homology.

The homology unit map and compared chain coaugmentation give the graded coinvariant
coaugmentation. -/
def matrixCoinvariantHomologyCoaug (m : ℕ) : 𝟙_ (GradedObject ℕ (ModuleCat.{u} k)) ⟶ matrixCoinvariantHomologyGraded k
  A m := by
  letI : ComonObj (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
    (matrixCoinvariantOrdinaryCoalgebra k A m).comon
  exact HomologicalComplex.HomologyCoalgebra.coaug
    (matrixCoinvariantOrdinaryCoalgebra k A m).X (matrixCoinvariantOrdinaryCoaug k A m)

/-- Comonoid compatibility of matrix coinvariant homology coaugmentation.

The graded coinvariant coaugmentation preserves the homology comultiplication and counit. -/
def matrixCoinvariantHomologyCoaugIsComonHom (m : ℕ) :
    letI : ComonObj (matrixCoinvariantHomologyGraded k A m) := matrixCoinvariantHomologyComonObj k A m
    IsComonHom (matrixCoinvariantHomologyCoaug k A m) := by
  letI : ComonObj (matrixCoinvariantOrdinaryCoalgebra k A m).X :=
    (matrixCoinvariantOrdinaryCoalgebra k A m).comon
  letI : IsComonHom (matrixCoinvariantOrdinaryCoaug k A m) :=
    matrixCoinvariantOrdinaryCoaugIsComonHom k A m
  exact HomologicalComplex.HomologyCoalgebra.coaugIsComonHom
    (matrixCoinvariantOrdinaryCoalgebra k A m).X (matrixCoinvariantOrdinaryCoaug k A m)

/-- The compared chain coalgebra size map of matrix coinvariants.

Transport the coinvariant zero-extension comonoid morphism through the scalar-unit comparison. -/
def matrixCoinvariantOrdinaryZeroCornerMap {m n : ℕ} (h : m ≤ n) :
    matrixCoinvariantOrdinaryCoalgebra k A m ⟶ matrixCoinvariantOrdinaryCoalgebra k A n := by
  let C := matrixCoinvariantLiftedUnitCoalgebra k A m
  let D := matrixCoinvariantLiftedUnitCoalgebra k A n
  let g : C.X ⟶ D.X := matrixCoinvariantZeroCornerMap k A h
  letI : ComonObj C.X := C.comon
  letI : ComonObj D.X := D.comon
  let gC : C ⟶ D := { hom := g, isComonHom_hom := matrixCoinvariantZeroCornerMapIsComonHom k A h }
  exact HomologicalComplex.HomologyCoalgebra.LiftedUnitChain.nativeComonFunctor.map gC

/-- The graded size map of matrix coinvariant homology.

Take homology of the compared coinvariant zero-extension chain map in every degree. -/
def matrixCoinvariantHomologyZeroCornerMap {m n : ℕ} (h : m ≤ n) :
    matrixCoinvariantHomologyGraded k A m ⟶ matrixCoinvariantHomologyGraded k A n :=
  fun d => HomologicalComplex.homologyMap (matrixCoinvariantOrdinaryZeroCornerMap k A h).hom d

/-- Comonoid compatibility of matrix coinvariant homology size maps.

The graded zero-extension map preserves the field coinvariant homology comultiplication and
counit. -/
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
