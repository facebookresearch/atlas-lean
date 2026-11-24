/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Actual cochain-cycle classes for Li obstruction cocycles

The class is the native lift into cycles followed by the native homology
quotient, applied to1. No separately supplied obstruction quotient or
classifying map is substituted. Source: native Mathlib homological
complex kernels/quotients; Jun Li arXiv:math/0110113v1, Section1.4.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiCycleClasses

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {A : Type} [CommRing A] (C : CochainComplex (ModuleCat.{0} A) ℤ)
  (n : ℤ) (x : C.X n)

def vector : ModuleCat.of A A ⟶ C.X n := ModuleCat.ofHom (LinearMap.toSpanSingleton A (C.X n) x)

theorem vector_closed (closed : C.d n (n + 1) x = 0) : vector C n x ≫ C.d n (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change C.d n (n + 1) (r • x) = 0
  rw [(C.d n (n + 1)).hom.map_smul, closed, smul_zero]

def cycleClass (closed : C.d n (n + 1) x = 0) : C.homology n :=
  (C.homologyπ n)
    ((C.liftCycles' (vector C n x) (n + 1) (by simp) (vector_closed C n x closed)) (1 : A))

end MathlibExt.AlgebraicGeometry.LiCycleClasses
