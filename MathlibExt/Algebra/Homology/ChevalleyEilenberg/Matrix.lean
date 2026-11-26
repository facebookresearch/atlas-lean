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

Let `k` be a commutative ring and `A` a unital `k`-algebra. The square matrices `gl_m(A)` form
a Lie algebra under `[X,Y] = XY-YX`. Its CE term in degree `n` is `⋀ⁿ[k] gl_m(A)`, with the
canonical bracket boundary and exterior unshuffle coproduct.

Top-left zero extension for `m ≤ r` induces a coalgebra chain map, and these complexes form a
functor in matrix size, including size zero. Entrywise algebra homomorphisms commute with zero
extension and give coefficient natural transformations and homology maps. Lifted versions
place independently sized entry algebras in a common module universe.
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

/-- The canonical CE complex of a finite matrix Lie algebra.

For matrix size `m`, take the CE complex of `gl_m(A)` with commutator bracket. -/
abbrev matrixComplex (m : ℕ) := (canonicalChainData k (Matrix (Fin m) (Fin m) A)).complex

/-- The exterior coalgebra complex of finite matrix CE chains.

Specialize the canonical CE coalgebra to the finite matrix Lie algebra. -/
abbrev matrixCoalgebra (m : ℕ) := nativeCoalgebra k (Matrix (Fin m) (Fin m) A)

/-- The coaugmentation of a finite matrix CE complex.

The scalar unit maps to the exterior-degree-zero unit of the matrix CE complex. -/
abbrev matrixCoaug (m : ℕ) := nativeComplexCoaug k (Matrix (Fin m) (Fin m) A)

/-- The counit of a finite matrix CE complex.

The canonical CE counit projects the matrix exterior complex onto its scalar unit complex. -/
abbrev matrixCounit (m : ℕ) := nativeComplexCounit k (Matrix (Fin m) (Fin m) A)

/-- The comultiplication of finite matrix CE chains.

The canonical CE coproduct gives a chain map from matrix exterior chains to their tensor
total. -/
abbrev matrixComul (m : ℕ) := nativeComplexComul k (Matrix (Fin m) (Fin m) A)

/-- The bracket boundary of a pure matrix exterior wedge.

The successor differential on a wedge of `n+1` matrices is its canonical signed matrix-bracket
boundary. -/
theorem matrixComplex_d_pure (m n : ℕ) (v : Fin (n + 1) → Matrix (Fin m) (Fin m) A) :
    ((matrixComplex k A m).d (n + 1) n).hom (exteriorPower.ιMulti k (n + 1) v) =
      bracketBoundary k (Matrix (Fin m) (Fin m) A) n v := by
  rw [ChainData.complex_d_succ]
  exact differential_apply_ιMulti k (Matrix (Fin m) (Fin m) A) n v

/-- The zero degree-one differential of finite matrix CE chains.

The boundary from exterior degree one to zero is zero for every matrix size, including size
zero. -/
theorem matrixComplex_d_one_zero (m : ℕ) : (matrixComplex k A m).d 1 0 = 0 := by
  rw [ChainData.complex_d_succ]
  apply ModuleCat.hom_ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  exact differential_apply_ιMulti k (Matrix (Fin m) (Fin m) A) 0 v

/-- The CE chain map of top-left matrix zero extension.

For `m ≤ n`, the matrix Lie inclusion by zero extension induces a map of canonical CE
complexes. -/
def matrixZeroCornerMap {m n : ℕ} (h : m ≤ n) : matrixComplex k A m ⟶ matrixComplex k A n :=
  nativeComplexMap k (Matrix (Fin m) (Fin m) A) (Matrix.zeroExtendLieHom k A h)

/-- The exterior formula for a matrix zero-extension chain map.

A pure wedge maps to the wedge of the matrices extended by zeros in the top-left corner. -/
theorem matrixZeroCornerMap_pure {m n : ℕ} (h : m ≤ n) (d : ℕ)
    (v : Fin d → Matrix (Fin m) (Fin m) A) :
    ((matrixZeroCornerMap k A h).f d).hom (exteriorPower.ιMulti k d v) =
      exteriorPower.ιMulti k d (fun i => Matrix.zeroExtend h (v i)) := by
  simpa only [matrixZeroCornerMap, Function.comp_def, Matrix.zeroExtendLieHom_apply] using
    nativeComplexMap_f_ιMulti k (Matrix (Fin m) (Fin m) A)
      (Matrix.zeroExtendLieHom k A h) d v

/-- The identity matrix zero-extension CE map.

Zero extension at equal matrix sizes induces the identity chain map. -/
@[simp]
theorem matrixZeroCornerMap_id (m : ℕ) : matrixZeroCornerMap k A (le_rfl : m ≤ m) = 𝟙 _ := by
  rw [matrixZeroCornerMap, Matrix.zeroExtendLieHom_id, nativeComplexMap_id]

/-- Composition of matrix zero-extension CE maps.

For `m ≤ n ≤ p`, the two zero-extension chain maps compose to zero extension from `m` to `p`. -/
theorem matrixZeroCornerMap_comp {m n p : ℕ} (h : m ≤ n) (h' : n ≤ p) :
    matrixZeroCornerMap k A h ≫ matrixZeroCornerMap k A h' = matrixZeroCornerMap k A (h.trans h') := by
  rw [matrixZeroCornerMap, matrixZeroCornerMap, matrixZeroCornerMap,
    nativeComplexMap_comp, Matrix.zeroExtendLieHom_comp]

/-- The size-indexed functor of finite matrix CE complexes.

The natural-number size category maps to matrix CE complexes, with order morphisms acting by
top-left zero extension. -/
def matrixComplexFunctor : ℕ ⥤ ChainComplex (ModuleCat.{max u v} k) ℕ where
  obj m := matrixComplex k A m
  map h := matrixZeroCornerMap k A (leOfHom h)
  map_id m := matrixZeroCornerMap_id k A m
  map_comp h h' := (matrixZeroCornerMap_comp k A (leOfHom h) (leOfHom h')).symm

/-- Coaugmentation preservation by matrix zero extension.

The matrix CE coaugmentation followed by a zero-extension map is the target coaugmentation. -/
theorem matrixZeroCornerMap_coaug {m n : ℕ} (h : m ≤ n) :
    matrixCoaug k A m ≫ matrixZeroCornerMap k A h = matrixCoaug k A n :=
  nativeComplexMap_coaug k (Matrix (Fin m) (Fin m) A) (Matrix.zeroExtendLieHom k A h)

/-- Comonoid compatibility of a matrix zero-extension CE map.

The zero-extension chain map preserves the canonical CE comultiplication and counit. -/
abbrev matrixZeroCornerMapIsComonHom {m n : ℕ} (h : m ≤ n) :=
  nativeComplexMapIsComonHom k (Matrix (Fin m) (Fin m) A) (Matrix.zeroExtendLieHom k A h)

/-- The unshuffle component of a finite matrix CE coproduct.

The coproduct from exterior degree `p+q` to degrees `p,q` is the signed exterior unshuffle
map. -/
theorem matrixCoproductComponent_eq_unshuffle (m p q : ℕ) :
    coproductComponent k (Matrix (Fin m) (Fin m) A) (p + q) p q =
      exteriorPower.unshuffle k (Matrix (Fin m) (Fin m) A) p q :=
  coproductComponent_eq_unshuffle k (Matrix (Fin m) (Fin m) A) p q

/-- The homology module of a finite matrix CE complex.

For size `m` and degree `d`, take degree-`d` homology of the matrix Lie-algebra CE complex. -/
abbrev matrixHomology (m d : ℕ) := (matrixComplex k A m).homology d

/-- The matrix CE homology map of zero extension.

The size inclusion `m ≤ n` induces the homology map of its zero-extension chain map in degree
`d`. -/
def matrixZeroCornerHomologyMap {m n : ℕ} (h : m ≤ n) (d : ℕ) :
    matrixHomology k A m d ⟶ matrixHomology k A n d :=
  HomologicalComplex.homologyMap (matrixZeroCornerMap k A h) d

section SameCoefficientWorld

variable {B : Type v} [Ring B] [Algebra k B]

/-- The CE chain map of an entrywise algebra homomorphism.

An algebra map `f : A → B` induces a map between fixed-size matrix CE complexes by applying
`f` to every entry. -/
def matrixCoefficientMap (f : A →ₐ[k] B) (m : ℕ) : matrixComplex k A m ⟶ matrixComplex k B m :=
  nativeComplexMap k (Matrix (Fin m) (Fin m) A) (Matrix.coefficientLieHom k A f m)

/-- The pure-wedge formula for a matrix coefficient chain map.

The coefficient chain map sends a wedge of matrices to the wedge of their entrywise images
under `f`. -/
theorem matrixCoefficientMap_pure (f : A →ₐ[k] B) (m d : ℕ)
    (v : Fin d → Matrix (Fin m) (Fin m) A) :
    ((matrixCoefficientMap k A f m).f d).hom (exteriorPower.ιMulti k d v) =
      exteriorPower.ιMulti k d (fun i => (v i).map f) := by
  exact nativeComplexMap_f_ιMulti k (Matrix (Fin m) (Fin m) A)
    (Matrix.coefficientLieHom k A f m) d v

/-- Commutation of matrix coefficient maps and size inclusions.

Entrywise algebra maps commute with the CE chain maps of top-left zero extension. -/
theorem matrixCoefficientMap_naturality (f : A →ₐ[k] B) {m n : ℕ} (h : m ≤ n) :
    matrixZeroCornerMap k A h ≫ matrixCoefficientMap k A f n =
      matrixCoefficientMap k A f m ≫ matrixZeroCornerMap k B h := by
  rw [matrixZeroCornerMap, matrixCoefficientMap, matrixZeroCornerMap, matrixCoefficientMap,
    nativeComplexMap_comp, nativeComplexMap_comp, Matrix.coefficientLieHom_zeroExtend_comp]

/-- The coefficient natural transformation of finite matrix CE systems.

The fixed-size coefficient maps assemble into a natural transformation between the size-
indexed CE functors. -/
def matrixCoefficientNatTrans (f : A →ₐ[k] B) : matrixComplexFunctor k A ⟶ matrixComplexFunctor k B where
  app m := matrixCoefficientMap k A f m
  naturality m n h := matrixCoefficientMap_naturality k A f (leOfHom h)

end SameCoefficientWorld

section WorkingHeight

/-- The matrix CE complex at a chosen carrier height.

Lift the finite matrix CE complex to the universe joining the scalar ring, entry algebra, and
chosen height. -/
abbrev matrixComplexAtHeight (m : ℕ) :=
  canonicalComplexULift.{u,v,max u v z} k (Matrix (Fin m) (Fin m) A)

/-- The lifted CE map of matrix zero extension.

A top-left size inclusion induces a chain map between the matrix CE complexes at the chosen
carrier height. -/
def matrixZeroCornerMapAtHeight {m n : ℕ} (h : m ≤ n) :
    matrixComplexAtHeight.{u,v,z} k A m ⟶ matrixComplexAtHeight.{u,v,z} k A n :=
  nativeLiftedComplexMapAtHeight.{u,v,v,z} k (Matrix (Fin m) (Fin m) A)
    (Matrix.zeroExtendLieHom k A h)

/-- The pure-wedge formula for lifted matrix zero extension.

The lifted size map sends `up(⋀ᵢ X_i)` to the lift of the wedge of their zero extensions. -/
theorem matrixZeroCornerMapAtHeight_pure {m n : ℕ} (h : m ≤ n) (d : ℕ)
    (v : Fin d → Matrix (Fin m) (Fin m) A) :
    ((matrixZeroCornerMapAtHeight.{u,v,z} k A h).f d).hom
        (ULift.up (exteriorPower.ιMulti k d v)) =
      ULift.up (exteriorPower.ιMulti k d (fun i => Matrix.zeroExtend h (v i))) := by
  rw [matrixZeroCornerMapAtHeight, nativeLiftedComplexMapAtHeight_f_up]
  congr 1
  exact exteriorPower.map_apply_ιMulti (Matrix.zeroExtendLieHom k A h).toLinearMap v

/-- The size-indexed matrix CE functor at a chosen height.

Lift every finite matrix complex and zero-extension map into the same chosen module category. -/
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

/-- The lifted coefficient CE map between independent entry universes.

For `f : A → B`, lift its fixed-size matrix Lie map into the universe joining both entry-
algebra carriers and the ground ring. -/
def matrixCoefficientMapAtHeight (f : A →ₐ[k] B) (m : ℕ) :
    matrixComplexAtHeight.{u,v,max u v w z} k A m ⟶
      matrixComplexAtHeight.{u,w,max u v w z} k B m :=
  nativeLiftedComplexMapAtHeight.{u,v,w,z} k (Matrix (Fin m) (Fin m) A)
    (Matrix.coefficientLieHom k A f m)

/-- The pure-wedge formula for a lifted matrix coefficient map.

The map sends the lift of a matrix wedge to the lift of the wedge of its entrywise coefficient
images. -/
theorem matrixCoefficientMapAtHeight_pure (f : A →ₐ[k] B) (m d : ℕ)
    (v : Fin d → Matrix (Fin m) (Fin m) A) :
    ((matrixCoefficientMapAtHeight.{u,v,w,z} k A f m).f d).hom
        (ULift.up (exteriorPower.ιMulti k d v)) =
      ULift.up (exteriorPower.ιMulti k d (fun i => (v i).map f)) := by
  rw [matrixCoefficientMapAtHeight, nativeLiftedComplexMapAtHeight_f_up]
  congr 1
  exact exteriorPower.map_apply_ιMulti (Matrix.coefficientLieHom k A f m).toLinearMap v

/-- Size naturality of lifted matrix coefficient maps.

At a common carrier height, coefficient maps commute with zero-extension maps. -/
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

/-- The lifted coefficient natural transformation of matrix CE systems.

The chosen-height coefficient maps form a natural transformation between the lifted size
functors. -/
def matrixCoefficientNatTransAtHeight (f : A →ₐ[k] B) :
    matrixComplexFunctorAtHeight.{u,v,max u v w z} k A ⟶
      matrixComplexFunctorAtHeight.{u,w,max u v w z} k B where
  app m := matrixCoefficientMapAtHeight.{u,v,w,z} k A f m
  naturality m n h := matrixCoefficientMapAtHeight_naturality k A f (leOfHom h)

/-- The homology map of a lifted matrix coefficient chain map.

Take the degree-`d` homology map of the fixed-size lifted coefficient chain map. -/
def matrixCoefficientHomologyMapAtHeight (f : A →ₐ[k] B) (m d : ℕ) :
    (matrixComplexAtHeight.{u,v,max u v w z} k A m).homology d ⟶
      (matrixComplexAtHeight.{u,w,max u v w z} k B m).homology d :=
  HomologicalComplex.homologyMap (matrixCoefficientMapAtHeight.{u,v,w,z} k A f m) d

end WorkingHeight

end ChevalleyEilenberg
