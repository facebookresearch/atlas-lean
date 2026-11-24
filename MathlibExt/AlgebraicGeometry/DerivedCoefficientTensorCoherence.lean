/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels

/-!
# Source unit, symmetry and associator of balanced coefficient tensors

Unitors are the actual coefficient actions. Symmetry is the native
Koszul braiding before the balanced quotient. The associator fixes
every nested quotient generator, with its three original homogeneous
factors unchanged. These equations determine the full module maps.
No independently chosen affine coherence isomorphism is accepted.

References: PTVV arXiv:1111.3209v4, §§1--2; the native module and
cochain tensor sources retained in DGSource. Generic coherent assembly
is a separate construction request.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorCoherence

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels

universe u
variable {R : Type u} [CommRing R] (C : DGCat R) (o : C) (T : DerivedTensorModel C o)

/-- The actual left-nested tensor generator, with all three factors retained. -/
def leftGenerator (P M N : DGDerivedModules R C) {p q r n : ℤ}
    (h : p + q + r = n) (a : (value C o P.obj).X p)
    (b : (value C o M.obj).X q) (c : (value C o N.obj).X r) :
    (value C o (T.functor.obj (T.functor.obj (P, M), N)).obj).X n :=
  (((T.value (T.functor.obj (P, M)) N).comparison.inv).f n).hom
    (generator C o (T.action (T.functor.obj (P, M)).obj) (T.action N.obj) h
      (((T.value P M).comparison.inv.f (p + q)).hom
        (generator C o (T.action P.obj) (T.action M.obj) rfl a b)) c)

/-- The actual right-nested tensor generator, retaining the same ordered factors. -/
def rightGenerator (P M N : DGDerivedModules R C) {p q r n : ℤ}
    (h : p + (q + r) = n) (a : (value C o P.obj).X p)
    (b : (value C o M.obj).X q) (c : (value C o N.obj).X r) :
    (value C o (T.functor.obj (P, T.functor.obj (M, N))).obj).X n :=
  (((T.value P (T.functor.obj (M, N))).comparison.inv).f n).hom
    (generator C o (T.action P.obj) (T.action (T.functor.obj (M, N)).obj) h a
      (((T.value M N).comparison.inv.f (q + r)).hom
        (generator C o (T.action M.obj) (T.action N.obj) rfl b c)))

/-- Every source coherence map is fixed by its actual balanced-tensor quotient. -/
structure CoherenceModel (unit : DGDerivedModules R C)
    (unit_eq : unit.obj = regularModule C o) where
  leftUnit : ∀ M : DGDerivedModules R C, (T.functor.obj (unit, M)).obj ≅ M.obj
  leftUnit_normalized : ∀ M : DGDerivedModules R C,
    HEq (quotientMap C o (T.action unit.obj) (T.action M.obj) ≫
      (T.value unit M).comparison.inv ≫ moduleComponent (leftUnit M).hom (op o))
      (T.action M.obj).map
  rightUnit : ∀ M : DGDerivedModules R C, (T.functor.obj (M, unit)).obj ≅ M.obj
  rightUnit_normalized : ∀ M : DGDerivedModules R C,
    HEq (quotientMap C o (T.action M.obj) (T.action unit.obj) ≫
      (T.value M unit).comparison.inv ≫ moduleComponent (rightUnit M).hom (op o))
      (rightAction C o (T.action M.obj))
  symmetry : ∀ M N : DGDerivedModules R C,
    (T.functor.obj (M, N)).obj ≅ (T.functor.obj (N, M)).obj
  symmetry_normalized : ∀ M N : DGDerivedModules R C,
    quotientMap C o (T.action M.obj) (T.action N.obj) ≫
        (T.value M N).comparison.inv ≫ moduleComponent (symmetry M N).hom (op o) ≫
          (T.value N M).comparison.hom =
      (β_ (value C o M.obj) (value C o N.obj)).hom ≫
        quotientMap C o (T.action N.obj) (T.action M.obj)
  associator : ∀ P M N : DGDerivedModules R C,
    (T.functor.obj (T.functor.obj (P, M), N)).obj ≅
      (T.functor.obj (P, T.functor.obj (M, N))).obj
  associator_normalized : ∀ (P M N : DGDerivedModules R C) (p q r n : ℤ)
    (h : p + q + r = n) (a : (value C o P.obj).X p)
    (b : (value C o M.obj).X q) (c : (value C o N.obj).X r),
    ((moduleComponent (associator P M N).hom (op o)).f n).hom
      (leftGenerator C o T P M N h a b c) =
    rightGenerator C o T P M N (by omega) a b c

end MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorCoherence
