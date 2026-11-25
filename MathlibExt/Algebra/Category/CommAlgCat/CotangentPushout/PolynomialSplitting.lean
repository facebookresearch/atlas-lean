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
# Actual compatible polynomial generators under tensor pushout

The native mapped simplicial splitting preserves every original coproduct
injection and degeneracy operator.  Native polynomial tensor base change
identifies the mapped nondegenerate summand with polynomials over K on the
SAME original index type.  Flatness is unnecessary for this generator data.

In particular the already constructed canonical PolynomialSplitting gives
actual compatible generators on the actual tensor-pushout polynomial model;
no uniform free-presentation or desired splitting certificate is supplied.
Native verification remains unexecuted.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]

/-- Native polynomial tensor base change with the original arbitrary generator type. -/
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

/-- Mapping the original splitting and original summand polynomial isos earns the new data. -/
def polynomialSplitting
    {P : SimplicialObject (CommAlgCat.{max u v w} k)} (s : PolynomialSplitting.{u, max v w} k P) :
    PolynomialSplitting.{w, max u v} K (P ⋙ algebraFunctor.{u, v, w} k K) where
  splitting := s.splitting.map (algebraFunctor.{u, v, w} k K)
  «variables» n := s.variables n
  polynomialIso n := (algebraFunctor.{u, v, w} k K).mapIso (s.polynomialIso n) ≪≫
    freeAlgebraIso.{u, v, w} k K (s.variables n)

/-- Nondegenerate generator index types are unchanged by actual base change. -/
@[simp]
theorem polynomialSplitting_variables
    {P : SimplicialObject (CommAlgCat.{max u v w} k)} (s : PolynomialSplitting.{u, max v w} k P) (n : ℕ) :
    (polynomialSplitting.{u, v, w} k K s).variables n = s.variables n := rfl

/-- The actual nondegenerate inclusion is the image of the original inclusion. -/
@[simp]
theorem polynomialSplitting_inclusion
    {P : SimplicialObject (CommAlgCat.{max u v w} k)} (s : PolynomialSplitting.{u, max v w} k P) (n : ℕ) :
    (polynomialSplitting.{u, v, w} k K s).splitting.ι n =
      (algebraFunctor.{u, v, w} k K).map (s.splitting.ι n) := rfl

/-- The canonical base-changed algebra model has earned compatible polynomial generators. -/
def canonicalSplitting (A : CommAlgCat.{max u v w} k) :
    PolynomialSplitting.{w, max u v} K
      ((polynomialResolution.{u, max v w} k A).left ⋙ algebraFunctor.{u, v, w} k K) :=
  polynomialSplitting.{u, v, w} k K (canonicalPolynomialSplitting.{u, max v w} k A)

end CommAlgCat.CotangentPushout

end
