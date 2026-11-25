/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
public import MathlibExt.CategoryTheory.DGAlgebraCategoryModels
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset

/-!
# The actual shuffle formula on normalized simplicial algebras

A shuffle is a subset of the p+q ordered steps with p left steps.
Its two simplex projections count the left and right steps before each
vertex. Multiplication is the signed sum of the products pulled back
along those literal degeneracy projections. The sign counts right steps
preceding left steps.

The underlying normalized complex and its inclusions are Mathlib's
Moore/Dold--Kan objects. A DG-algebra construction output is constrained
by this shuffle formula, the native scalar unit and commutativity. Its
functor maps must be the actual normalized simplicial-algebra maps.
No perfect-module, moduli-geometricity or cotangent theorem is assumed.

References: Eilenberg--Zilber, On products of complexes, Annals of
Mathematics 57 (1953), §2; Toën--Vaquié, arXiv:math/0503269v5, §2.1;
PTVV, arXiv:1111.3209v4, conventions. The complete underlying Dold--Kan
comparison is the native Mathlib source, not a new Wanted theorem.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open _root_.AlgebraicTopology
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.DGCyclicBarModels
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels

universe u

/-- The actual ordered partitions defining (p,q)-shuffles. -/
abbrev Shuffle (p q : ℕ) := {s : Finset (Fin (p + q)) // s.card = p}

/-- The number of right-before-left crossings of a shuffle. -/
def inversions {p q : ℕ} (s : Shuffle p q) : ℕ :=
  (Finset.univ.filter fun ij : Fin (p + q) × Fin (p + q) =>
    ij.1 ∉ s.val ∧ ij.2 ∈ s.val ∧ ij.1 < ij.2).card

/-- Count the selected steps before a vertex, as an actual monotone map. -/
def countProjection {n r : ℕ} (s : Finset (Fin n)) (hs : s.card = r) :
    SimplexCategory.mk n ⟶ SimplexCategory.mk r :=
  SimplexCategory.Hom.mk
    { toFun := fun i =>
        ⟨(s.filter fun j => j.val < i.val).card, by
          have hle := Finset.card_le_card (Finset.filter_subset (fun j => j.val < i.val) s)
          change (s.filter fun j => j.val < i.val).card < r + 1
          exact Nat.lt_succ_of_le (hs ▸ hle)⟩
      monotone' := by
        intro i j hij
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_filter] at ha ⊢
        exact ⟨ha.1, lt_of_lt_of_le ha.2 hij⟩ }

/-- Literal degeneracy projection onto the left factor. -/
def leftProjection {p q : ℕ} (s : Shuffle p q) :
    SimplexCategory.mk (p + q) ⟶ SimplexCategory.mk p :=
  countProjection s.val s.property

/-- Literal degeneracy projection onto the right factor. -/
def rightProjection {p q : ℕ} (s : Shuffle p q) :
    SimplexCategory.mk (p + q) ⟶ SimplexCategory.mk q :=
  countProjection s.valᶜ (by simp [Finset.card_compl, s.property])

variable {k : Type u} [CommRing k]

/-- The signed shuffle product in the actual simplicial-algebra term. -/
def rawShuffle (A : SAlg k) (p q : ℕ)
    (x : A.obj (op (SimplexCategory.mk p))) (y : A.obj (op (SimplexCategory.mk q))) :
    A.obj (op (SimplexCategory.mk (p + q))) :=
  ∑ s : Shuffle p q, (-1 : k) ^ inversions s •
    (A.map (leftProjection s).op x * A.map (rightProjection s).op y)

/-- The actual normalized simplicial-module cochain functor. -/
def normalizeFunctor (k : Type u) [CommRing k] : SAlg k ⥤ Cochains k :=
  (Functor.whiskeringRight _ _ _).obj (toModules k) ⋙
    normalizedMooreComplex (ModuleCat.{u} k) ⋙
    (ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{u} k)

/-- Its maps are computed by native Moore normalization and extension. -/
def normalizedMap {A B : SAlg k} (f : A ⟶ B) :
    normalizedComplex A ⟶ normalizedComplex B := (normalizeFunctor k).map f

/-- The native normalization comparison in a nonpositive cochain degree. -/
def normalizedDegreeIso (A : SAlg k) (p : ℕ) :
    (normalizedComplex A).X (-(p : ℤ)) ≅ (normalizedChain A).X p :=
  (normalizedChain A).extendXIso (ComplexShape.embeddingUpIntLE 0) (by simp)

/-- The literal normalized element as an element of the simplicial algebra. -/
def coefficient (A : SAlg k) (p : ℕ) (x : (normalizedComplex A).X (-(p : ℤ))) :
    A.obj (op (SimplexCategory.mk p)) :=
  ((inclusionOfMooreComplexMap (A ⋙ toModules k)).f p).hom
    ((normalizedDegreeIso A p).hom x)

/-- The tensor-unit cochain's degree-zero element is its actual scalar. -/
def unitScalar (x : (𝟙_ (Cochains k)).X 0) : k :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{u} k))).hom x

/-- A normalized DG algebra must implement the actual shuffle product
and scalar unit on the actual Moore complex. -/
structure ShuffleAlgebraModel (A : SAlg k) (N : DGAlgebra k) where
  complexIso : N.X ≅ normalizedComplex A
  product : ∀ (p q : ℕ) (x : N.X.X (-(p : ℤ))) (y : N.X.X (-(q : ℤ))),
    coefficient A (p + q)
      ((complexIso.hom.f (-((p + q : ℕ) : ℤ)))
        (multiplyHomogeneous N x y (by omega))) =
      rawShuffle A p q
        (coefficient A p ((complexIso.hom.f (-(p : ℤ))) x))
        (coefficient A q ((complexIso.hom.f (-(q : ℤ))) y))
  unit : ∀ x : (𝟙_ (Cochains k)).X 0,
    coefficient A 0 ((complexIso.hom.f 0) ((MonObj.one (X := N.X)).f 0 x)) =
      algebraMap k (A.obj (op (SimplexCategory.mk 0))) (unitScalar x)
  commutative : (β_ N.X N.X).hom ≫ MonObj.mul (X := N.X) = MonObj.mul (X := N.X)

/-- Functorial assembly fixes every algebra-map action by native normalization. -/
structure ShuffleAlgebraFunctor (k : Type u) [CommRing k] where
  functor : SAlg k ⥤ DGAlgebra k
  model : ∀ A, ShuffleAlgebraModel A (functor.obj A)
  map_eq : ∀ {A B : SAlg k} (f : A ⟶ B),
    (functor.map f).hom ≫ (model B).complexIso.hom =
      (model A).complexIso.hom ≫ normalizedMap f

end MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
