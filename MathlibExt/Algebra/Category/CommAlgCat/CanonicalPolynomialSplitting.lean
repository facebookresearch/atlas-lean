/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CanonicalPolynomialGeneratorDecomposition
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialSplitting
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Actual compatible polynomial splitting of the canonical resolution for every algebra

Native Eilenberg--Zilber decomposition gives an actual coproduct of the
canonical generator indices over every original epi. The existing free
functor preserves that coproduct. Generator computations identify its legs
with the original canonical algebra degeneracies, so its transported cofan
is precisely the native splitting cofan of the original polynomial resolution.

This earns PolynomialSplitting for every original commutative k-algebra A,
including zero ground rings. It supplies no new resolution model, contraction,
or desired splitting as input. The weaker printed free predicate and literal
algebraic BK are not identified with this canonical comonad construction.
Source proposals only; UNEXECUTED.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Splitting
open scoped Simplicial

universe u v

namespace CommAlgCat.CanonicalPolynomialSplitting

open CanonicalPolynomialGeneratorPoints CanonicalPolynomialGeneratorDecomposition

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The original inclusion of the actual nondegenerate polynomial generators. -/
def inclusion (n : ℕ) : (free.{u, v} k).obj (Variables k A n) ⟶ (resolution k A).obj (op ⦋n⦌) :=
  (free.{u, v} k).map (TypeCat.ofHom (Subtype.val : Variables k A n → Index k A n)) ≫
    (polynomialResolutionObjIso.{u, v} k A n).inv

@[simp]
theorem inclusion_X (n : ℕ) (x : Variables k A n) :
    (inclusion k A n).hom (MvPolynomial.X x) = point k A n x.val := by
  change (polynomialResolutionObjIso.{u, v} k A n).inv.hom
    (MvPolynomial.rename (R := k) Subtype.val (MvPolynomial.X x)) = point k A n x.val
  rw [MvPolynomial.rename_X, polynomialResolutionObjIso_inv]
  rfl

def algebraCofan (n : ℕ) :
    Cofan (fun a : IndexSet (op ⦋n⦌) => (free.{u, v} k).obj (Variables k A a.1.unop.len)) :=
  Cofan.mk ((resolution k A).obj (op ⦋n⦌))
    (fun a => inclusion k A a.1.unop.len ≫ (resolution k A).map a.e.op)

/-- Applying free to the actual index coproduct gives the original algebra
legs, characterized on their literal polynomial generators. -/
@[reassoc]
theorem algebraCofan_identification (n : ℕ) (a : IndexSet (op ⦋n⦌)) :
    (algebraCofan k A n).inj a ≫ (polynomialResolutionObjIso.{u, v} k A n).hom =
      (free.{u, v} k).map ((generatorCofan k A n).inj a) := by
  apply CommAlgCat.hom_ext
  apply MvPolynomial.algHom_ext
  intro x
  change (polynomialResolutionObjIso.{u, v} k A n).hom.hom
    (((resolution k A).map a.e.op).hom ((inclusion k A a.1.unop.len).hom (MvPolynomial.X x))) =
      MvPolynomial.rename (R := k) (summandIndex k A a) (MvPolynomial.X x)
  rw [inclusion_X, MvPolynomial.rename_X, ← point_summandIndex]
  exact polynomialResolutionObjIso_hom_generator.{u, v} k A n (summandIndex k A a x)

def algebraCofanIsColimit (n : ℕ) : IsColimit (algebraCofan k A n) := by
  let h := isColimitCofanMkObjOfIsColimit (free.{u, v} k)
    (fun a : IndexSet (op ⦋n⦌) => Variables k A a.1.unop.len)
    (fun a => (generatorCofan k A n).inj a) (generatorCofanIsColimit k A n)
  refine IsColimit.ofIsoColimit h (Cofan.ext (polynomialResolutionObjIso.{u, v} k A n).symm ?_)
  intro a
  apply (cancel_mono (polynomialResolutionObjIso.{u, v} k A n).hom).mp
  let e := polynomialResolutionObjIso.{u, v} k A n
  have hi := algebraCofan_identification k A n a
  let f := (free.{u, v} k).map ((generatorCofan k A n).inj a)
  have hcomp : (f ≫ e.inv) ≫ e.hom = f :=
    (Category.assoc f e.inv e.hom).trans
      ((congrArg (fun g => f ≫ g) e.inv_hom_id).trans (Category.comp_id f))
  exact hcomp.trans hi.symm

end CanonicalPolynomialSplitting

/-- Canonical compatible nondegenerate polynomial generators for every
original commutative k-algebra, earned from the existing canonical comonad. -/
def canonicalPolynomialSplitting (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k) :
    PolynomialSplitting k (polynomialResolution.{u, v} k A).left where
  splitting := {
    N := fun n => (free.{u, v} k).obj (CanonicalPolynomialGeneratorPoints.Variables k A n)
    ι := CanonicalPolynomialSplitting.inclusion k A
    isColimit' := by
      rintro ⟨⟨n⟩⟩
      exact CanonicalPolynomialSplitting.algebraCofanIsColimit k A n }
  «variables» := CanonicalPolynomialGeneratorPoints.Variables k A
  polynomialIso _ := Iso.refl _

@[simp]
theorem canonicalPolynomialSplitting_ι_X (k : Type u) [CommRing k]
    (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : CanonicalPolynomialGeneratorPoints.Variables k A n) :
    ((canonicalPolynomialSplitting.{u, v} k A).splitting.ι n).hom (MvPolynomial.X x) =
      CanonicalPolynomialGeneratorPoints.point k A n x.val :=
  CanonicalPolynomialSplitting.inclusion_X k A n x

end CommAlgCat

end
