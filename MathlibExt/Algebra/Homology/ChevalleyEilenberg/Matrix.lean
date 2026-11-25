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

public import MathlibExt.Algebra.Lie.MatrixZeroExtension
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraWorkingHeight
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraUnshuffle
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Chevalley–Eilenberg complexes of finite matrix Lie algebras

For a unital algebra over a commutative ring, finite square matrices form Lie algebras under
the commutator bracket. Their Chevalley–Eilenberg complexes carry the exterior coproduct and
coaugmentation.

Top-left zero extension and entrywise algebra homomorphisms induce natural chain and homology
maps. Pure-wedge formulas identify the differential and these maps; universe lifts allow
independent coefficient carrier universes.
-/

@[expose] public section

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v w z

namespace ChevalleyEilenberg

variable (k : Type u) [CommRing k]
variable (A : Type v) [Ring A] [Algebra k A]

/-- The canonical CE complex of finite matrices. -/
abbrev matrixComplex (m : ℕ) := (canonicalChainData k (Matrix (Fin m) (Fin m) A)).complex

/-- The canonical CE coalgebra, specialized to the finite matrix Lie algebra. -/
abbrev matrixCoalgebra (m : ℕ) := nativeCoalgebra k (Matrix (Fin m) (Fin m) A)

/-- The canonical coaugmentation. -/
abbrev matrixCoaug (m : ℕ) := nativeComplexCoaug k (Matrix (Fin m) (Fin m) A)

/-- The canonical counit. -/
abbrev matrixCounit (m : ℕ) := nativeComplexCounit k (Matrix (Fin m) (Fin m) A)

/-- The canonical coproduct chain map. -/
abbrev matrixComul (m : ℕ) := nativeComplexComul k (Matrix (Fin m) (Fin m) A)

/-- The degreewise matrix CE boundary has the alternating bracket formula. -/
theorem matrixComplex_d_pure (m n : ℕ) (v : Fin (n + 1) → Matrix (Fin m) (Fin m) A) :
    ((matrixComplex k A m).d (n + 1) n).hom (exteriorPower.ιMulti k (n + 1) v) =
      bracketBoundary k (Matrix (Fin m) (Fin m) A) n v := by
  rw [ChainData.complex_d_succ]
  exact differential_apply_ιMulti k (Matrix (Fin m) (Fin m) A) n v

/-- The degree-one boundary vanishes, including the size-zero matrix stage. -/
theorem matrixComplex_d_one_zero (m : ℕ) : (matrixComplex k A m).d 1 0 = 0 := by
  rw [ChainData.complex_d_succ]
  apply ModuleCat.hom_ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  exact differential_apply_ιMulti k (Matrix (Fin m) (Fin m) A) 0 v

/-- The zero corner induces the canonical CE chain map. -/
def matrixZeroCornerMap {m n : ℕ} (h : m ≤ n) : matrixComplex k A m ⟶ matrixComplex k A n :=
  nativeComplexMap k (Matrix (Fin m) (Fin m) A) (Matrix.zeroExtendLieHom k A h)

/-- Every pure wedge is mapped by entrywise application of the zero corner. -/
theorem matrixZeroCornerMap_pure {m n : ℕ} (h : m ≤ n) (d : ℕ)
    (v : Fin d → Matrix (Fin m) (Fin m) A) :
    ((matrixZeroCornerMap k A h).f d).hom (exteriorPower.ιMulti k d v) =
      exteriorPower.ιMulti k d (fun i => Matrix.zeroExtend h (v i)) := by
  simpa only [matrixZeroCornerMap, Function.comp_def, Matrix.zeroExtendLieHom_apply] using
    nativeComplexMap_f_ιMulti k (Matrix (Fin m) (Fin m) A)
      (Matrix.zeroExtendLieHom k A h) d v

@[simp]
theorem matrixZeroCornerMap_id (m : ℕ) : matrixZeroCornerMap k A (le_rfl : m ≤ m) = 𝟙 _ := by
  rw [matrixZeroCornerMap, Matrix.zeroExtendLieHom_id, nativeComplexMap_id]

theorem matrixZeroCornerMap_comp {m n p : ℕ} (h : m ≤ n) (h' : n ≤ p) :
    matrixZeroCornerMap k A h ≫ matrixZeroCornerMap k A h' = matrixZeroCornerMap k A (h.trans h') := by
  rw [matrixZeroCornerMap, matrixZeroCornerMap, matrixZeroCornerMap,
    nativeComplexMap_comp, Matrix.zeroExtendLieHom_comp]

/-- The canonical finite-stage CE functor, including its zero-size stage. -/
def matrixComplexFunctor : ℕ ⥤ ChainComplex (ModuleCat.{max u v} k) ℕ where
  obj m := matrixComplex k A m
  map h := matrixZeroCornerMap k A (leOfHom h)
  map_id m := matrixZeroCornerMap_id k A m
  map_comp h h' := (matrixZeroCornerMap_comp k A (leOfHom h) (leOfHom h')).symm

/-- Zero corners preserve the CE coaugmentation. -/
theorem matrixZeroCornerMap_coaug {m n : ℕ} (h : m ≤ n) :
    matrixCoaug k A m ≫ matrixZeroCornerMap k A h = matrixCoaug k A n :=
  nativeComplexMap_coaug k (Matrix (Fin m) (Fin m) A) (Matrix.zeroExtendLieHom k A h)

/-- The zero-corner map is a comonoid map under the fixed canonical dictionaries. -/
abbrev matrixZeroCornerMapIsComonHom {m n : ℕ} (h : m ≤ n) :=
  nativeComplexMapIsComonHom k (Matrix (Fin m) (Fin m) A) (Matrix.zeroExtendLieHom k A h)

/-- The complete exterior unshuffle is the finite matrix coproduct component. -/
theorem matrixCoproductComponent_eq_unshuffle (m p q : ℕ) :
    coproductComponent k (Matrix (Fin m) (Fin m) A) (p + q) p q =
      exteriorPower.unshuffle k (Matrix (Fin m) (Fin m) A) p q :=
  coproductComponent_eq_unshuffle k (Matrix (Fin m) (Fin m) A) p q

/-- Homology of the matrix CE complex. -/
abbrev matrixHomology (m d : ℕ) := (matrixComplex k A m).homology d

/-- The homology map is a map of the zero-corner chain map. -/
def matrixZeroCornerHomologyMap {m n : ℕ} (h : m ≤ n) (d : ℕ) :
    matrixHomology k A m d ⟶ matrixHomology k A n d :=
  HomologicalComplex.homologyMap (matrixZeroCornerMap k A h) d

section SameCoefficientWorld

variable {B : Type v} [Ring B] [Algebra k B]

/-- A coefficient algebra map gives the canonical CE matrix map. -/
def matrixCoefficientMap (f : A →ₐ[k] B) (m : ℕ) : matrixComplex k A m ⟶ matrixComplex k B m :=
  nativeComplexMap k (Matrix (Fin m) (Fin m) A) (Matrix.coefficientLieHom k A f m)

theorem matrixCoefficientMap_pure (f : A →ₐ[k] B) (m d : ℕ)
    (v : Fin d → Matrix (Fin m) (Fin m) A) :
    ((matrixCoefficientMap k A f m).f d).hom (exteriorPower.ιMulti k d v) =
      exteriorPower.ιMulti k d (fun i => (v i).map f) := by
  exact nativeComplexMap_f_ιMulti k (Matrix (Fin m) (Fin m) A)
    (Matrix.coefficientLieHom k A f m) d v

/-- Coefficient functoriality commutes with every zero-corner CE map. -/
theorem matrixCoefficientMap_naturality (f : A →ₐ[k] B) {m n : ℕ} (h : m ≤ n) :
    matrixZeroCornerMap k A h ≫ matrixCoefficientMap k A f n =
      matrixCoefficientMap k A f m ≫ matrixZeroCornerMap k B h := by
  rw [matrixZeroCornerMap, matrixCoefficientMap, matrixZeroCornerMap, matrixCoefficientMap,
    nativeComplexMap_comp, nativeComplexMap_comp, Matrix.coefficientLieHom_zeroExtend_comp]

/-- Coefficient maps give a natural transformation of finite-stage CE functors. -/
def matrixCoefficientNatTrans (f : A →ₐ[k] B) : matrixComplexFunctor k A ⟶ matrixComplexFunctor k B where
  app m := matrixCoefficientMap k A f m
  naturality m n h := matrixCoefficientMap_naturality k A f (leOfHom h)

end SameCoefficientWorld

section WorkingHeight

/-- The matrix CE complex carried to the full working height by prolongation. -/
abbrev matrixComplexAtHeight (m : ℕ) :=
  canonicalComplexULift.{u,v,max u v z} k (Matrix (Fin m) (Fin m) A)

/-- The zero corner at a full working height. -/
def matrixZeroCornerMapAtHeight {m n : ℕ} (h : m ≤ n) :
    matrixComplexAtHeight.{u,v,z} k A m ⟶ matrixComplexAtHeight.{u,v,z} k A n :=
  nativeLiftedComplexMapAtHeight.{u,v,v,z} k (Matrix (Fin m) (Fin m) A)
    (Matrix.zeroExtendLieHom k A h)

theorem matrixZeroCornerMapAtHeight_pure {m n : ℕ} (h : m ≤ n) (d : ℕ)
    (v : Fin d → Matrix (Fin m) (Fin m) A) :
    ((matrixZeroCornerMapAtHeight.{u,v,z} k A h).f d).hom
        (ULift.up (exteriorPower.ιMulti k d v)) =
      ULift.up (exteriorPower.ιMulti k d (fun i => Matrix.zeroExtend h (v i))) := by
  rw [matrixZeroCornerMapAtHeight, nativeLiftedComplexMapAtHeight_f_up]
  congr 1
  exact exteriorPower.map_apply_ιMulti (Matrix.zeroExtendLieHom k A h).toLinearMap v

/-- The complete finite-stage functor at the common height. -/
def matrixComplexFunctorAtHeight : ℕ ⥤ ChainComplex (ModuleCat.{max u v z} k) ℕ where
  obj m := matrixComplexAtHeight.{u,v,z} k A m
  map h := matrixZeroCornerMapAtHeight.{u,v,z} k A (leOfHom h)
  map_id m := by
    rw [matrixZeroCornerMapAtHeight, Matrix.zeroExtendLieHom_id,
      nativeLiftedComplexMapAtHeight_id]
  map_comp {m n p} h h' := by
    dsimp only [matrixZeroCornerMapAtHeight]
    rw [← Matrix.zeroExtendLieHom_comp k A (leOfHom h) (leOfHom h')]
    exact (nativeLiftedComplexMapAtHeight_comp.{u,v,v,v,z} k (Matrix (Fin m) (Fin m) A)
      (Matrix.zeroExtendLieHom k A (leOfHom h))
      (Matrix.zeroExtendLieHom k A (leOfHom h'))).symm

variable {B : Type w} [Ring B] [Algebra k B]

/-- A coefficient map across independent universes, at their common height. -/
def matrixCoefficientMapAtHeight (f : A →ₐ[k] B) (m : ℕ) :
    matrixComplexAtHeight.{u,v,max u v w z} k A m ⟶
      matrixComplexAtHeight.{u,w,max u v w z} k B m :=
  nativeLiftedComplexMapAtHeight.{u,v,w,z} k (Matrix (Fin m) (Fin m) A)
    (Matrix.coefficientLieHom k A f m)

theorem matrixCoefficientMapAtHeight_pure (f : A →ₐ[k] B) (m d : ℕ)
    (v : Fin d → Matrix (Fin m) (Fin m) A) :
    ((matrixCoefficientMapAtHeight.{u,v,w,z} k A f m).f d).hom
        (ULift.up (exteriorPower.ιMulti k d v)) =
      ULift.up (exteriorPower.ιMulti k d (fun i => (v i).map f)) := by
  rw [matrixCoefficientMapAtHeight, nativeLiftedComplexMapAtHeight_f_up]
  congr 1
  exact exteriorPower.map_apply_ιMulti (Matrix.coefficientLieHom k A f m).toLinearMap v

/-- Simultaneous size and coefficient naturality at one height for all carrier universes. -/
theorem matrixCoefficientMapAtHeight_naturality (f : A →ₐ[k] B) {m n : ℕ} (h : m ≤ n) :
    matrixZeroCornerMapAtHeight.{u,v,max u v w z} k A h ≫
        matrixCoefficientMapAtHeight.{u,v,w,z} k A f n =
      matrixCoefficientMapAtHeight.{u,v,w,z} k A f m ≫
        matrixZeroCornerMapAtHeight.{u,w,max u v w z} k B h := by
  let fm := Matrix.coefficientLieHom k A f m
  let fn := Matrix.coefficientLieHom k A f n
  let za := Matrix.zeroExtendLieHom k A h
  let zb := Matrix.zeroExtendLieHom k B h
  have h₁ := nativeLiftedComplexMapAtHeight_comp.{u,v,v,w,max u v w z} k
    (Matrix (Fin m) (Fin m) A) za fn
  have h₂ := nativeLiftedComplexMapAtHeight_comp.{u,v,w,w,max u v w z} k
    (Matrix (Fin m) (Fin m) A) fm zb
  have hLie : fn.comp za = zb.comp fm := Matrix.coefficientLieHom_zeroExtend_comp k A f h
  have hMap := congrArg (nativeLiftedComplexMapAtHeight.{u,v,w,max u v w z} k
    (Matrix (Fin m) (Fin m) A)) hLie
  exact h₁.trans (hMap.trans h₂.symm)

/-- The full-height coefficient natural transformation retains independent universes. -/
def matrixCoefficientNatTransAtHeight (f : A →ₐ[k] B) :
    matrixComplexFunctorAtHeight.{u,v,max u v w z} k A ⟶
      matrixComplexFunctorAtHeight.{u,w,max u v w z} k B where
  app m := matrixCoefficientMapAtHeight.{u,v,w,z} k A f m
  naturality m n h := matrixCoefficientMapAtHeight_naturality k A f (leOfHom h)

/-- Homology maps of full-height coefficient maps. -/
def matrixCoefficientHomologyMapAtHeight (f : A →ₐ[k] B) (m d : ℕ) :
    (matrixComplexAtHeight.{u,v,max u v w z} k A m).homology d ⟶
      (matrixComplexAtHeight.{u,w,max u v w z} k B m).homology d :=
  HomologicalComplex.homologyMap (matrixCoefficientMapAtHeight.{u,v,w,z} k A f m) d

end WorkingHeight

end ChevalleyEilenberg
