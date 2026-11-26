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
# Compatible polynomial splitting of the canonical resolution

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. For the
polynomial-comonad resolution `P`, let `V_n` be the indices in `T^n A` whose generator points
in `P_n` are nondegenerate. Applying the free-algebra functor to their epimorphism-indexed
coproduct decomposition gives a simplicial splitting with nondegenerate summands
`Free_k(V_n)`.

The summand inclusion sends the variable at `x∈V_n` to the canonical generator point at
`x.val`. Thus `P` has a `PolynomialSplitting`: a simplicial splitting together with polynomial
coordinates on each nondegenerate summand.
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

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `V_n` the nondegenerate generator
indices of its polynomial resolution `P`. The morphism `inclusion k A n : Free_k(V_n) → P_n`
is the free algebra map on `Subtype.val : V_n → T^n A`, followed by the inverse degree-object
identification. It sends a variable indexed by `x` to `point_n(x.val)`. -/
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

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `n : ℕ`, and `a : [n] → [m]` an epimorphism
index. The injection of `Free_k(V_m)` into the degree-`n` algebra cofan, followed by `P_n ≅
Free_k(T^n A)`, equals the free-algebra map of `generatorCofan k A n`'s index injection. Thus
the algebra splitting leg is obtained from the nondegenerate index summand map. -/
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

/-- Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The polynomial
resolution admits a `PolynomialSplitting` whose nondegenerate degree-`n` summand is
`Free_k(Variables k A n)`, whose inclusion sends each variable to its generator point, and
whose splitting cofans are colimits over all simplex epimorphisms. The polynomial coordinate
isomorphism on each summand is the identity of that free algebra. -/
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
