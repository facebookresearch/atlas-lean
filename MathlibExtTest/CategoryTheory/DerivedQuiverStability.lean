/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.SingleHomology
public import MathlibExt.CategoryTheory.DerivedQuiverStability

@[expose] public section

namespace MathlibExt.CategoryTheory.DerivedQuiverStability

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

variable (k V : Type) [Field k] [Quiver V] [Fintype V]

-- The central charge is additive and sends a vertex vector to the vertex charge.
example (z : V → ℂ) [DecidableEq V] (v : V) :
    centralCharge V z (Pi.single v 1) = z v := by
  simp [centralCharge, Pi.single_apply]

example (z : V → ℂ) : centralCharge V z 0 = 0 := map_zero _

-- The zero object is bounded: all its cohomology vanishes.
example : Bounded k V 0 :=
  Set.finite_empty.subset fun n hn ↦
    hn (Functor.map_isZero (DerivedCategory.homologyFunctor (Representations k V) n)
      (isZero_zero (D k V)))

-- A representation `M` placed in degree `m` has numerical class `(-1)^m` times its
-- dimension vector: the class records the sign of odd degrees.
omit [Fintype V] in
theorem numericalClass_single (M : Representations k V) (m : ℤ)
    (h : Bounded k V ((DerivedCategory.singleFunctor _ m).obj M)) (v : V) :
    numericalClass k V ((DerivedCategory.singleFunctor _ m).obj M) h v =
      (m.negOnePow : ℤ) * dimensionVector k V M v := by
  let K := (DerivedCategory.singleFunctor (Representations k V) m).obj M
  have hzero : ∀ n, n ≠ m → IsZero (cohomology k V K n) := fun n hn ↦
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) m M n hn).of_iso
      ((DerivedCategory.homologyFunctorFactors (Representations k V) n).app _)
  have hfin : ∀ n, n ≠ m → Module.finrank k
      ((forget₂ (FGModuleCat.{0} k) (ModuleCat.{0} k)).obj
        ((cohomology k V K n).obj ((Paths.of V).obj v))) = 0 := fun n hn ↦ by
    have hz : IsZero ((forget₂ (FGModuleCat.{0} k) (ModuleCat.{0} k)).obj
        ((cohomology k V K n).obj ((Paths.of V).obj v))) :=
      Functor.map_isZero _ ((hzero n hn).obj _)
    have : Subsingleton ((forget₂ (FGModuleCat.{0} k) (ModuleCat.{0} k)).obj
        ((cohomology k V K n).obj ((Paths.of V).obj v))) :=
      ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton
  have e : (cohomology k V K m).obj ((Paths.of V).obj v) ≅ M.obj ((Paths.of V).obj v) :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Representations k V) m).app M).app _
  rw [numericalClass, GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset _ _ {m}
    (fun n hn ↦ by
      by_contra hnm
      exact hn (hfin n (by simpa using hnm))), Finset.sum_singleton]
  congr 1
  have := ((forget₂ (FGModuleCat.{0} k) (ModuleCat.{0} k)).mapIso e).toLinearEquiv.finrank_eq
  rw [dimensionVector]
  exact_mod_cast this

-- In degree `0` the class is the dimension vector, in degree `1` its negative.
example (M : Representations k V) (h) (v : V) :
    numericalClass k V ((DerivedCategory.singleFunctor _ 0).obj M) h v =
      dimensionVector k V M v := by
  simp [numericalClass_single]

example (M : Representations k V) (h) (v : V) :
    numericalClass k V ((DerivedCategory.singleFunctor _ 1).obj M) h v =
      -dimensionVector k V M v := by
  simp [numericalClass_single]

-- Elements of the bounded subcategory are bounded objects.
example (K : BoundedDerivedQuiver k V) : Bounded k V K.obj := K.property

-- Slicing objects are bounded, so their charge is defined.
noncomputable example (Z : VertexCharges V) (phi : ℝ) (K : D k V) (hK : slicing k Z phi K) :
    ℂ :=
  derivedCharge k V Z.charge K hK.1

-- With positive vertex charges, a nonzero heart object has charge in the upper half-plane,
-- unlike the zero charge, for which every phase would be `0`.
example (Z : VertexCharges V) (v : V) [DecidableEq V] :
    0 < (centralCharge V Z.charge (Pi.single v 1)).im := by
  simpa [centralCharge, Pi.single_apply] using Z.im_pos v

end MathlibExt.CategoryTheory.DerivedQuiverStability
