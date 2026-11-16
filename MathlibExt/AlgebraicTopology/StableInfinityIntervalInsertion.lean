/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinitySFunctorMaps
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.StructureMap

/-!
# The native interval-coordinate source for K-theory structure maps

An inserted Ar[1] coordinate has the original whole diagram at (0,1)
and the constant zero diagram at both diagonal intervals. Every higher
circle simplex acts by the native ordinal restriction Ar[m] to Ar[1].
The contracts below specify this on the entire enriched diagram, rather
than just on its object set or on the nondegenerate circle edge.

The coherent zero-extension and circle descent are construction requests
in WantedExt. Their source and normalization are fixed here independently
of additivity, localization or K-theory corepresentability.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Section 7.1,
Definitions 7.1 and 7.5, pages 44--45.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinityIntervalInsertion

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityMappingSpaces
open StableInfinityFiniteDiagrams StableInfinityCategoryModels
open StableInfinitySConstruction StableInfinityMultiSConstruction
open StableInfinitySFunctorMaps MathlibExt.SpectraSource
open scoped Simplicial

universe u

/-- The new interval coordinate comes first, as in the native sphere action. -/
def prependLengths {q : ℕ} (n : Fin q → ℕ) (m : ℕ) :
    Fin (q + 1) → ℕ := Fin.cases m n

/-- Fix the entire new interval while retaining all old objects and arrows. -/
def intervalSlice {q : ℕ} {n : Fin q → ℕ} {m : ℕ}
    (r : IntervalCategory m) :
    MultiIntervalCategory q n ⥤
      MultiIntervalCategory (q + 1) (prependLengths n m) where
  obj p := Fin.cases r p
  map f := Fin.cases (𝟙 r) f
  map_id p := by funext i; cases i using Fin.cases <;> rfl
  map_comp f g := by funext i; cases i using Fin.cases <;> rfl

/-- Restrict only the new coordinate by the actual circle-simplex ordinal. -/
def insertionOrdinals {q : ℕ} {n : Fin q → ℕ} {m : ℕ}
    (a : Fin (m + 1) →o Fin 2) :
    ∀ i : Fin (q + 1),
      Fin (prependLengths n m i + 1) →o
        Fin (prependLengths n 1 i + 1) :=
  Fin.cases a (fun _ => OrderHom.id)

/-- Old-coordinate ordinal maps retain the inserted Ar[1] factor. -/
def oldOrdinals {q : ℕ} {m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1)) :
    ∀ i : Fin (q + 1),
      Fin (prependLengths m 1 i + 1) →o
        Fin (prependLengths n 1 i + 1) :=
  Fin.cases OrderHom.id a

/-- The native full constant diagram at the selected source zero object. -/
def zeroDiagram (C : StableInfinityCategory.{u}) (q : ℕ)
    (n : Fin q → ℕ) : indexNerve (MultiIntervalCategory q n) ⟶ C.toSSet :=
  SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.const C.zero

/-- The inclusion of the full multi-gap category into the native Hom object. -/
abbrev multiGapInclusion (C : StableInfinityCategory.{u}) (q : ℕ)
    (n : Fin q → ℕ) :=
  ((mapping (indexNerve (MultiIntervalCategory q n)) C.toSSet).fullEnhancedSubcategory (IsMultiGapVertex C q n)).ι

/-- The fixed whole zero diagram, as a constant enriched diagram map. -/
def constantZeroMap (C : StableInfinityCategory.{u}) (q : ℕ)
    (n : Fin q → ℕ) (X : SSet.{u}) :
    X ⟶ mapping (indexNerve (MultiIntervalCategory q n)) C.toSSet :=
  SSet.stdSimplex.isTerminalObj₀.from X ≫
    SSet.const (mappingZero _ _ (zeroDiagram C q n))

/-- A coherent zero-extension is normalized on all old parameter simplices. -/
structure IntervalInsertion (C : StableInfinityCategory.{u}) where
  one : ∀ (q : ℕ) (n : Fin q → ℕ),
    multiGapCategory C q n ⟶
      multiGapCategory C (q + 1) (prependLengths n 1)
  offdiagonal : ∀ (q : ℕ) (n : Fin q → ℕ),
    one q n ≫ multiGapInclusion C (q + 1) (prependLengths n 1) ≫
      precomposition (indexMap (intervalSlice
        (MathlibExt.AlgebraicGeometry.WaldhausenExactFlags.interval
          (0 : Fin 2) 1 (by decide)))) C.toSSet =
      multiGapInclusion C q n
  diagonal : ∀ (q : ℕ) (n : Fin q → ℕ) (i : Fin 2),
    one q n ≫ multiGapInclusion C (q + 1) (prependLengths n 1) ≫
      precomposition (indexMap (intervalSlice
        (MathlibExt.AlgebraicGeometry.WaldhausenExactFlags.interval
          i i le_rfl))) C.toSSet =
      constantZeroMap C q n (multiGapCategory C q n)
  naturality : ∀ (q : ℕ) (m n : Fin q → ℕ)
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1)),
    one q n ≫ multiGapRestriction (C := C) (oldOrdinals a) =
      multiGapRestriction (C := C) a ≫ one q m

/-- The actual map for every [m] to [1], including both constant ordinals. -/
def IntervalInsertion.restrict {C : StableInfinityCategory.{u}}
    (I : IntervalInsertion C) (q : ℕ) (n : Fin q → ℕ) (m : ℕ)
    (a : Fin (m + 1) →o Fin 2) :
    multiGapCategory C q n ⟶
      multiGapCategory C (q + 1) (prependLengths n m) :=
  I.one q n ≫ multiGapRestriction (C := C) (insertionOrdinals a)

/-- All actual circle-simplex diagrams are obtained by that same restriction. -/
def insertedSimplex {C : StableInfinityCategory.{u}}
    (I : IntervalInsertion C) (q : ℕ) (k : SimplexCategoryᵒᵖ)
    (a : k.unop ⟶ ⦋1⦌) (x : (multiSDiagonal C q).obj k) :
    (multiSDiagonal C (q + 1)).obj k := by
  have h : prependLengths (fun _ : Fin q => k.unop.len) k.unop.len =
      (fun _ : Fin (q + 1) => k.unop.len) := by
    funext i
    cases i using Fin.cases <;> rfl
  change (multiGapCore C (q + 1)
    (fun _ => k.unop.len)).obj k
  exact (eqToHom (congrArg (multiGapCore C (q + 1)) h)).app k
    ((coreMap (I.restrict q (fun _ => k.unop.len) k.unop.len
      a.toOrderHom)).app k x)

/-- Pointings are fixed by the entire native constant zero diagram. -/
structure MultiSPointing (C : StableInfinityCategory.{u}) where
  point : ∀ q : ℕ, Δ[0] ⟶ multiSDiagonal C q
  normalization : ∀ (q : ℕ) (k : SimplexCategoryᵒᵖ) (t : Δ[0].obj k),
    ((point q).app k t).val.val =
      (SSet.const (mappingZero _ _
        (zeroDiagram C q (fun _ => k.unop.len)))).app k t

/-- The actual q-th based diagonal space. -/
def pointedDiagonal {C : StableInfinityCategory.{u}}
    (P : MultiSPointing C) (q : ℕ) : PointedSSet.{u} :=
  Under.mk (P.point q)

/-- Circle descent must agree with the inserted diagram for every interval simplex. -/
structure CircleInsertion (C : StableInfinityCategory.{0}) where
  interval : IntervalInsertion C
  pointing : MultiSPointing C
  map : ∀ q : ℕ,
    PointedSSet.circle ⊗ pointedDiagonal pointing q ⟶
      pointedDiagonal pointing (q + 1)
  normalization : ∀ (q : ℕ) (k : SimplexCategoryᵒᵖ)
    (a : k.unop ⟶ ⦋1⦌) (x : (multiSDiagonal C q).obj k),
    (map q).right.app k
      (PointedSSet.smashMk
        (PointedSSet.circleQuotient.right.app k
          (SSet.stdSimplex.objEquiv.symm a)) x) =
      insertedSimplex interval q k a x

end MathlibExt.AlgebraicTopology.StableInfinityIntervalInsertion
