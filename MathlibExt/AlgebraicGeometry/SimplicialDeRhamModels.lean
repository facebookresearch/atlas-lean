/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
public import MathlibExt.RingTheory.OrdinaryDeRhamAlgebraModels
public import MathlibExt.Algebra.Homology.WeightedClosedFormSpaces

/-!
# Source-normalized derived affine graded mixed de Rham models

The simplicial p-forms have the actual exterior powers of Kähler
differentials as their terms. All algebra and simplicial maps are fixed
on the generating forms b0 db1 wedge ... wedge dbp. The de Rham map is
the completed ordinary differential in every simplicial degree.

For the actual cofibrant replacement QA, the pth weight is the native
Moore normalization of these p-forms, reindexed to nonpositive cochain
degrees and shifted by p. The mixed differential is that actual de Rham
map, of cochain degree -1 and weight +1. This fixes the PTVV convention
DR(A)(p) = L exterior^p_{A/k}[p] after derived scalar extension/comparison.
Those module comparisons are separate interfaces; a graded mixed
complex is not freely renamed de Rham.

References: PTVV, arXiv:1111.3209v4, §1.1; Toën--Vezzosi,
HAG II, Part 2; Stacks 0FKF/0FKG. Completed ordinary differential
proofs retain AxiomMath/Stacks attribution in DeRhamSource.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open _root_.AlgebraicTopology
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedClosedFormSpaces
open MathlibExt.CategoryTheory.DGModelContracts
open CochainComplex CochainComplex.HomComplex

universe u

variable {k : Type u} [CommRing k]

/-- The native ordinary p-form module in one actual simplicial algebra degree. -/
def formTerm (A : SAlg k) (p : ℕ) (n : SimplexCategoryᵒᵖ) : ModuleCat.{u} k :=
  ModuleCat.of k ↥(⋀[A.obj n]^p (Ω[A.obj n⁄k]))

/-- The native generating form, retaining its coefficient and every differential. -/
def formGenerator (A : SAlg k) (p : ℕ) (n : SimplexCategoryᵒᵖ)
    (b : Fin (p + 1) → A.obj n) : formTerm A p n :=
  b 0 • exteriorPower.ιMulti (A.obj n) p
    (fun i => KaehlerDifferential.D k (A.obj n) (b i.succ))

/-- The actual ordinary de Rham differential in that simplicial degree. -/
def termDifferential (A : SAlg k) (p : ℕ) (n : SimplexCategoryᵒᵖ) :
    formTerm A p n ⟶ formTerm A (p + 1) n :=
  ModuleCat.ofHom (MathlibExt.DeRhamSource.KaehlerDifferential.deRhamDifferential
    (A := k) (B := A.obj n) p)

/-- A simplicial de Rham model has every term, generator map and differential fixed. -/
structure SimplicialDRModel (A : SAlg k) where
  forms : ℕ → SimplicialObject (ModuleCat.{u} k)
  termIso : ∀ (p : ℕ) (n : SimplexCategoryᵒᵖ), (forms p).obj n ≅ formTerm A p n
  map_generator : ∀ (p : ℕ) (n m : SimplexCategoryᵒᵖ) (f : n ⟶ m)
    (b : Fin (p + 1) → A.obj n),
    ((termIso p n).inv ≫ (forms p).map f ≫ (termIso p m).hom) (formGenerator A p n b) =
      formGenerator A p m (fun i => A.map f (b i))
  differential : ∀ p : ℕ, forms p ⟶ forms (p + 1)
  differential_eq : ∀ (p : ℕ) (n : SimplexCategoryᵒᵖ),
    (differential p).app n ≫ (termIso (p + 1) n).hom =
      (termIso p n).hom ≫ termDifferential A p n

/-- Native Moore normalization and integer reindexing of the actual p-forms. -/
def normalizedForms {A : SAlg k} (M : SimplicialDRModel A) (p : ℕ) : Cochains k :=
  ((normalizedMooreComplex (ModuleCat.{u} k)).obj (M.forms p)).extend
    (ComplexShape.embeddingUpIntLE 0)

/-- The actual normalized ordinary de Rham cochain map. -/
def normalizedDifferential {A : SAlg k} (M : SimplicialDRModel A) (p : ℕ) :
    normalizedForms M p ⟶ normalizedForms M (p + 1) :=
  ((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{u} k)).map
    ((normalizedMooreComplex (ModuleCat.{u} k)).map (M.differential p))

/-- The shifted normalized de Rham map, in the source mixed degree -1. -/
def mixedComponent {A : SAlg k} (M : SimplicialDRModel A) (p : ℕ)
    (a b : ℤ) (h : a + (-1 : ℤ) = b) :
    ((normalizedForms M p)⟦(p : ℤ)⟧).X a ⟶
      ((normalizedForms M (p + 1))⟦((p + 1 : ℕ) : ℤ)⟧).X b :=
  ((normalizedForms M p).shiftFunctorObjXIso (p : ℤ) a (a + (p : ℤ)) rfl).hom ≫
    (normalizedDifferential M p).f (a + (p : ℤ)) ≫
    ((normalizedForms M (p + 1)).shiftFunctorObjXIso ((p + 1 : ℕ) : ℤ) b
      (a + (p : ℤ)) (by omega)).inv

/-- The affine graded mixed model is normalized on QA, every weight and epsilon. -/
structure AffineDRModel (Q : AlgebraReplacementFunctor k) (A : SAlg k)
    (M : SimplicialDRModel (Q.functor.obj A)) where
  graded : GradedMixed k
  weightIso : ∀ p : ℕ, graded.weight (p : ℤ) ≅ (normalizedForms M p)⟦(p : ℤ)⟧
  negative : ∀ w : ℤ, w < 0 → _root_.CategoryTheory.Limits.IsZero (graded.weight w)
  epsilon_eq : ∀ (p : ℕ) (a b : ℤ) (h : a + (-1 : ℤ) = b),
    (graded.epsilon (p : ℤ)).v a b h ≫
      eqToHom (by congr 2) ≫ (weightIso (p + 1)).hom.f b =
      (weightIso p).hom.f a ≫ mixedComponent M p a b h

/-- Actual closed affine p-form space, including all weighted NC closing data. -/
def affineClosedForms {Q : AlgebraReplacementFunctor k} {A : SAlg k}
    {M : SimplicialDRModel (Q.functor.obj A)} (D : AffineDRModel Q A M)
    (p : ℕ) (n : ℤ) (NC : NegativeCyclicModel D.graded (p : ℤ)) : SSet.{u} :=
  closedFormSpace p n NC

/-- A map of actual simplicial de Rham forms has all generator images fixed. -/
structure SimplicialDRMap {A B : SAlg k} (M : SimplicialDRModel A)
    (N : SimplicialDRModel B) (f : A ⟶ B) where
  map : ∀ p : ℕ, M.forms p ⟶ N.forms p
  generator : ∀ (p : ℕ) (n : SimplexCategoryᵒᵖ) (b : Fin (p + 1) → A.obj n),
    ((M.termIso p n).inv ≫ (map p).app n ≫ (N.termIso p n).hom)
      (formGenerator A p n b) = formGenerator B p n (fun i => f.app n (b i))
  differential : ∀ p : ℕ,
    M.differential p ≫ map (p + 1) = map p ≫ N.differential p

/-- The actual normalized p-form cochain map of a simplicial algebra map. -/
def normalizedFormMap {A B : SAlg k} {M : SimplicialDRModel A}
    {N : SimplicialDRModel B} {f : A ⟶ B} (g : SimplicialDRMap M N f) (p : ℕ) :
    normalizedForms M p ⟶ normalizedForms N p :=
  ((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{u} k)).map
    ((normalizedMooreComplex (ModuleCat.{u} k)).map (g.map p))

/-- A graded mixed pullback has its actual normalized cochain map in every weight. -/
structure AffineDRMap {Q : AlgebraReplacementFunctor k} {A B : SAlg k}
    {M : SimplicialDRModel (Q.functor.obj A)} {N : SimplicialDRModel (Q.functor.obj B)}
    (D : AffineDRModel Q A M) (E : AffineDRModel Q B N) (f : A ⟶ B)
    (g : SimplicialDRMap M N (Q.functor.map f)) where
  map : MixedMap D.graded E.graded
  weight_eq : ∀ p : ℕ,
    map.map (p : ℤ) ≫ (E.weightIso p).hom =
      (D.weightIso p).hom ≫
        (CategoryTheory.shiftFunctor (Cochains k) (p : ℤ)).map (normalizedFormMap g p)

end MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
