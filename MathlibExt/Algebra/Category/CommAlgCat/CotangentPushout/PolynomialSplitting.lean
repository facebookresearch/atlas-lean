/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.Adjunction
public import MathlibExt.Algebra.Category.CommAlgCat.CanonicalPolynomialSplitting
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Polynomial splitting under tensor pushout

Let `k : Type u` and `K : Type w` be commutative rings with `Algebra k K`. Tensor pushout
identifies `K ⊗_k MvPolynomial σ k` with `MvPolynomial σ K` for any variable type `σ :
Type(max u v w)`.

Mapping a simplicial polynomial splitting by tensor pushout preserves its variable types and
sends each nondegenerate inclusion to its functor image. The polynomial coordinate maps are
the mapped coordinates followed by the free-algebra base-change comparison. Applying this to
the canonical splitting supplies a polynomial splitting of the polynomial resolution over `k`
after tensoring with `K`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]

/-- Let `k : Type u`, `K : Type w` be commutative rings with `Algebra k K`, and `σ : Type(max u v
w)`. The `K`-algebra isomorphism `freeAlgebraIso k K σ` identifies `K ⊗_k Free_k(σ)` with
`Free_K(σ)`, using polynomial tensor base change and preserving the variable indices. -/
def freeAlgebraIso (σ : Type (max u v w)) :
    (algebraFunctor.{u, v, w} k K).obj ((CommAlgCat.free.{u, max v w} k).obj σ) ≅
      (CommAlgCat.free.{w, max u v} K).obj σ :=
  CommAlgCat.isoMk (MvPolynomial.algebraTensorAlgEquiv (σ := σ) k K)

@[simp]
theorem freeAlgebraIso_generator (σ : Type (max u v w)) (i : σ) :
    (freeAlgebraIso.{u, v, w} k K σ).hom.hom ((1 : K) ⊗ₜ[k] (MvPolynomial.X i)) =
      (MvPolynomial.X i : MvPolynomial σ K) := by
  change MvPolynomial.algebraTensorAlgEquiv (σ := σ) k K
      ((1 : K) ⊗ₜ[k] MvPolynomial.X i) = MvPolynomial.X i
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.map_X, one_smul]

/-- Let `k,K` be commutative rings with `Algebra k K`, `P` a simplicial `k`-algebra, and `s :
PolynomialSplitting k P`. The pushed-out simplicial algebra `P ⋙ algebraFunctor k K` has a
polynomial splitting obtained by mapping `s.splitting`. Its variable types remain `s.variables
n`, and its coordinates are `E(s.polynomialIso n)` followed by `freeAlgebraIso` on those
variables. -/
def polynomialSplitting
    {P : SimplicialObject (CommAlgCat.{max u v w} k)} (s : PolynomialSplitting.{u, max v w} k P) :
    PolynomialSplitting.{w, max u v} K (P ⋙ algebraFunctor.{u, v, w} k K) where
  splitting := s.splitting.map (algebraFunctor.{u, v, w} k K)
  «variables» n := s.variables n
  polynomialIso n := (algebraFunctor.{u, v, w} k K).mapIso (s.polynomialIso n) ≪≫
    freeAlgebraIso.{u, v, w} k K (s.variables n)

/-- For commutative `k`-algebra `K`, a simplicial `k`-algebra `P`, `s : PolynomialSplitting k P`,
and `n : ℕ`, `(polynomialSplitting k K s).variables n = s.variables n`. The mapped
nondegenerate summand uses exactly the same polynomial variable type. -/
@[simp]
theorem polynomialSplitting_variables
    {P : SimplicialObject (CommAlgCat.{max u v w} k)} (s : PolynomialSplitting.{u, max v w} k P) (n : ℕ) :
    (polynomialSplitting.{u, v, w} k K s).variables n = s.variables n := rfl

/-- Let `K` be a commutative `k`-algebra, `P` a simplicial `k`-algebra, and `s :
PolynomialSplitting k P`. For `n : ℕ`, the nondegenerate inclusion in the pushed-out splitting
equals `(algebraFunctor k K).map (s.splitting.ι n)`. Thus the new splitting maps each summand
by the tensor-pushout functor. -/
@[simp]
theorem polynomialSplitting_inclusion
    {P : SimplicialObject (CommAlgCat.{max u v w} k)} (s : PolynomialSplitting.{u, max v w} k P) (n : ℕ) :
    (polynomialSplitting.{u, v, w} k K s).splitting.ι n =
      (algebraFunctor.{u, v, w} k K).map (s.splitting.ι n) := rfl

/-- For commutative rings `k : Type u`, `K : Type w` with `Algebra k K`, and `A : CommAlgCat.{max
u v w} k`, the simplicial `K`-algebra `(polynomialResolution k A).left ⋙ algebraFunctor k K`
has a `PolynomialSplitting`. It is obtained by tensoring the canonical polynomial splitting of
the resolution over `k`. -/
def canonicalSplitting (A : CommAlgCat.{max u v w} k) :
    PolynomialSplitting.{w, max u v} K
      ((polynomialResolution.{u, max v w} k A).left ⋙ algebraFunctor.{u, v, w} k K) :=
  polynomialSplitting.{u, v, w} k K (canonicalPolynomialSplitting.{u, max v w} k A)

end CommAlgCat.CotangentPushout

end
