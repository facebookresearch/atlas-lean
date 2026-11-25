/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.StableInfinityMultiSConstruction

/-!
# Exact functors on the full iterated S-construction

Every map below is the native postcomposition map on the entire coherent
diagram category. The core and diagonal maps are taken afterwards. Thus the
maps retain the source finite-colimit data and all parameter simplices.

Source: Blumberg--Gepner--Tabuada, arXiv:1001.2282v4, Section 7.1,
especially the paragraphs following Definitions 7.1 and 7.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.StableInfinitySFunctorMaps

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open QuasicategoricalModels StableInfinityMappingSpaces
open StableInfinityFiniteDiagrams StableInfinityCategoryModels
open StableInfinitySConstruction StableInfinityMultiSConstruction
open scoped Simplicial

universe u

/-- Native postcomposition acts on every coherent functor simplex. -/
def postcomposition (X : SSet.{u}) {C D : SSet.{u}} (f : C ⟶ D) :
    mapping X C ⟶ mapping X D :=
  ((SimplicialCategory.sHomFunctor SSet).obj (op X)).map f

/-- On vertices this is the whole original diagram followed by the functor. -/
theorem mappingZero_postcomposition {X C D : SSet.{u}}
    (d : X ⟶ C) (f : C ⟶ D) :
    (postcomposition X f).app (op ⦋0⦌) (mappingZero X C d) =
      mappingZero X D (d ≫ f) := rfl

/-- Exact postcomposition preserves every original multi-gap condition. -/
theorem postcomposed_isMultiGap {C D : StableInfinityCategory.{u}}
    (f : ExactFunctor C D) {q : ℕ} {n : Fin q → ℕ}
    (d : indexNerve (MultiIntervalCategory q n) ⟶ C.toSSet)
    (hd : IsMultiGapDiagram C q n d) :
    IsMultiGapDiagram D q n (d ≫ f.map) := by
  constructor
  · intro p r h
    exact f.exact.1 _ (hd.1 p r h)
  · intro p r k h
    simpa only [Category.assoc] using
      f.exact.2 (indexMap (coordinateSquare p r k h) ≫ d)
        (hd.2 p r k h)

/-- The full q-fold S-functor is the actual enriched postcomposition. -/
def multiGapFunctor {C D : StableInfinityCategory.{u}}
    (f : ExactFunctor C D) (q : ℕ) (n : Fin q → ℕ) :
    multiGapCategory C q n ⟶ multiGapCategory D q n :=
  fullMap (postcomposition (indexNerve (MultiIntervalCategory q n)) f.map)
    (IsMultiGapVertex C q n) (IsMultiGapVertex D q n) (by
      intro x hx
      let d :=
        (mappingZero (indexNerve (MultiIntervalCategory q n)) C.toSSet).symm x
      have he := (mappingZero (indexNerve (MultiIntervalCategory q n))
        C.toSSet).apply_symm_apply x
      rw [← he, mappingZero_postcomposition]
      simpa only [IsMultiGapVertex, Equiv.symm_apply_apply] using
        postcomposed_isMultiGap f d hx)

/-- The full map retains the actual postcomposed parameter simplex. -/
theorem multiGapFunctor_app_val {C D : StableInfinityCategory.{u}}
    (f : ExactFunctor C D) (q : ℕ) (n : Fin q → ℕ)
    (k : SimplexCategoryᵒᵖ) (x : (multiGapCategory C q n).obj k) :
    ((multiGapFunctor f q n).app k x).val =
      (postcomposition (indexNerve (MultiIntervalCategory q n))
        f.map).app k x.val := rfl

/-- Exact postcomposition commutes with every actual coordinate ordinal map. -/
theorem multiGapFunctor_restriction {C D : StableInfinityCategory.{u}}
    (f : ExactFunctor C D) {q : ℕ} {m n : Fin q → ℕ}
    (a : ∀ i : Fin q, Fin (m i + 1) →o Fin (n i + 1)) :
    multiGapFunctor f q n ≫ multiGapRestriction (C := D) a =
      multiGapRestriction (C := C) a ≫ multiGapFunctor f q m := by
  ext k x
  apply Subtype.ext
  rfl

/-- The full S-construction sends the identity to the actual identity map. -/
theorem multiGapFunctor_id (C : StableInfinityCategory.{u})
    (q : ℕ) (n : Fin q → ℕ) :
    multiGapFunctor (ExactFunctor.id C) q n = 𝟙 _ := by
  ext k x
  apply Subtype.ext
  rfl

/-- The full S-construction sends composition to native composition. -/
theorem multiGapFunctor_comp {C D E : StableInfinityCategory.{u}}
    (f : ExactFunctor C D) (g : ExactFunctor D E)
    (q : ℕ) (n : Fin q → ℕ) :
    multiGapFunctor (f.comp g) q n =
      multiGapFunctor f q n ≫ multiGapFunctor g q n := by
  ext k x
  apply Subtype.ext
  rfl

/-- The core map is induced by this same full exact-functor map. -/
def multiCoreFunctor {C D : StableInfinityCategory.{u}}
    (f : ExactFunctor C D) (q : ℕ) (n : Fin q → ℕ) :
    multiGapCore C q n ⟶ multiGapCore D q n :=
  coreMap (multiGapFunctor f q n)

/-- Exact functors act naturally on the actual multisimplicial diagram. -/
def multiSNaturalMap {C D : StableInfinityCategory.{u}}
    (f : ExactFunctor C D) (q : ℕ) :
    multiSConstruction C q ⟶ multiSConstruction D q where
  app n := multiGapFunctor f q (fun i => (n i).unop.len)
  naturality _ _ a := (multiGapFunctor_restriction f
    (fun i => (a i).unop.toOrderHom)).symm

/-- The diagonal-core natural map is induced by those full maps. -/
def diagonalCoreNaturalMap {C D : StableInfinityCategory.{u}}
    (f : ExactFunctor C D) (q : ℕ) :
    diagonalCoreFunctor C q ⟶ diagonalCoreFunctor D q :=
  Functor.whiskerLeft (diagonalIndex q)
    (Functor.whiskerRight (multiSNaturalMap f q) coreFunctor)

/-- The actual q-th K space map is the native all-coordinate diagonal map. -/
def multiSDiagonalMap {C D : StableInfinityCategory.{u}}
    (f : ExactFunctor C D) (q : ℕ) :
    multiSDiagonal C q ⟶ multiSDiagonal D q where
  app n := (diagonalCoreNaturalMap f q).app n |>.app n
  naturality n m a := by
    have h := congrArg (fun t => t.app n)
      ((diagonalCoreNaturalMap f q).naturality a)
    simp only [NatTrans.comp_app] at h
    dsimp only [multiSDiagonal]
    rw [Category.assoc,
      ((diagonalCoreNaturalMap f q).app m).naturality a,
      ← Category.assoc, h, Category.assoc]

/-- Diagonal functor maps are the original maps on all native core simplices. -/
theorem multiSDiagonalMap_app {C D : StableInfinityCategory.{u}}
    (f : ExactFunctor C D) (q : ℕ) (n : SimplexCategoryᵒᵖ)
    (x : (multiSDiagonal C q).obj n) :
    (multiSDiagonalMap f q).app n x =
      (multiCoreFunctor f q (fun _ => n.unop.len)).app n x := rfl

end MathlibExt.AlgebraicTopology.StableInfinitySFunctorMaps
