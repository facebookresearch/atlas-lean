/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.Free
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Actual compatible polynomial generators for simplicial algebras

The native splitting is a coproduct decomposition over all original
epimorphisms in the simplex category. Polynomial coordinates on its
nondegenerate summands are actual compatible free-generator data.
This structure contains no resolution comparison or homotopy certificate.

Chosen nondegenerate generator images extend by native polynomial evaluation
and the native coproduct universal property. Compatibility with every
original degeneracy follows from the decomposition, without choices in
degenerate simplices. The later face-compatible comparison induction must
still earn its face equations from the actual target boundary fillers.

Applying the existing free algebra functor to an actual simplicial set
earns this structure using native Eilenberg--Zilber splitting and the existing
free/forget adjunction. No compatible basis is inferred merely from separate
polynomial presentations in each degree.
References: Mathlib SimplicialObject.Splitting and SSet.splitting; Stacks017O;
the retained degeneracy qualification of Loday3.5.1--3.5.2.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k]

/-- Intrinsic nondegenerate polynomial summands and their native simplicial splitting. -/
structure PolynomialSplitting (P : SimplicialObject (CommAlgCat.{max u v} k)) where
  splitting : P.Splitting
  «variables» : ℕ → Type (max u v)
  polynomialIso : ∀ n, splitting.N n ≅ CommAlgCat.of k (MvPolynomial («variables» n) k)

namespace PolynomialSplitting

variable {k} {P Q : SimplicialObject (CommAlgCat.{max u v} k)}
  (s : PolynomialSplitting k P) (y : ∀ n, s.variables n → Q.obj (op ⦋n⦌))

/-- Original nondegenerate generator choices extend to the actual polynomial summand. -/
def generatorMap (n : ℕ) : s.splitting.N n ⟶ Q.obj (op ⦋n⦌) :=
  (s.polynomialIso n).hom ≫ CommAlgCat.ofHom (MvPolynomial.aeval (y n))

/-- All degenerate images are prescribed by their original native epimorphism. -/
def degreeMap (Δ : SimplexCategoryᵒᵖ) : P.obj Δ ⟶ Q.obj Δ :=
  s.splitting.desc Δ (fun a => s.generatorMap y a.1.unop.len ≫ Q.map a.e.op)

/-- The constructed map has the actual original summand restriction. -/
@[reassoc]
theorem summand_degreeMap (Δ : SimplexCategoryᵒᵖ) (a : SimplicialObject.Splitting.IndexSet Δ) :
    (s.splitting.cofan Δ).inj a ≫ s.degreeMap y Δ =
      s.generatorMap y a.1.unop.len ≫ Q.map a.e.op :=
  s.splitting.ι_desc Δ _ a

/-- The distinguished summand uses exactly its chosen original polynomial generator images. -/
@[reassoc]
theorem distinguished_degreeMap (n : ℕ) :
    s.splitting.ι n ≫ s.degreeMap y (op ⦋n⦌) = s.generatorMap y n := by
  have h := s.summand_degreeMap y (op ⦋n⦌) (SimplicialObject.Splitting.IndexSet.id _)
  rw [s.splitting.cofan_inj_id n] at h
  change s.splitting.ι n ≫ s.degreeMap y (op ⦋n⦌) =
    s.generatorMap y n ≫ Q.map (𝟙 (op ⦋n⦌)) at h
  exact h.trans ((congrArg (fun f => s.generatorMap y n ≫ f) (Q.map_id (op ⦋n⦌))).trans
    (Category.comp_id _))

/-- Compatibility with every original degeneracy is earned from the actual splitting. -/
theorem degreeMap_epi_naturality {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') [Epi θ.unop] :
    P.map θ ≫ s.degreeMap y Δ' = s.degreeMap y Δ ≫ Q.map θ := by
  apply s.splitting.hom_ext'
  intro a
  have hNat := s.splitting.cofan_inj_epi_naturality a θ
  have hNew := s.summand_degreeMap y Δ' (a.epiComp θ)
  have hOld := s.summand_degreeMap y Δ a
  dsimp only [SimplicialObject.Splitting.IndexSet.epiComp] at hNew
  have hF : Q.map (a.epiComp θ).e.op = Q.map a.e.op ≫ Q.map θ := by
    change Q.map (a.e.op ≫ θ) = Q.map a.e.op ≫ Q.map θ
    exact Q.map_comp _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ s.degreeMap y Δ') hNat).trans
      (hNew.trans
        ((congrArg (fun f => s.generatorMap y a.1.unop.len ≫ f) hF).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ Q.map θ) hOld.symm).trans
              (Category.assoc _ _ _))))))

end PolynomialSplitting

/-- The existing free algebra functor earns compatible generators on an actual simplicial set. -/
def polynomialSplittingOfSSet (X : SSet.{max u v}) :
    PolynomialSplitting k (X ⋙ free.{u, v} k) where
  splitting := X.splitting.map (free.{u, v} k)
  «variables» n := X.nonDegenerate n
  polynomialIso n := Iso.refl _

end CommAlgCat

end
