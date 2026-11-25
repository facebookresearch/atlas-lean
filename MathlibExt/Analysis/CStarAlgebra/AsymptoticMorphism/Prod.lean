/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Basic

/-!
# Products of asymptotic star morphisms

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), φ:A→B and ψ:A→C asymptotic star
morphisms. Their product family sends a to (φ_t(a),ψ_t(a)) in B×C, whose C-star norm is
max(‖b‖,‖c‖). The four defects tend to zero in this product norm.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Topology
noncomputable section
namespace AsymptoticMorphism

universe uA uB uC
variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

/-- **Product-valued asymptotic family.**

Let A,B,C be nonunital complex C-star algebras, φ:A→B and ψ:A→C asymptotic star morphisms on
T=[1,∞). The family prod φ ψ:A→B×C is (prod φ ψ)_t(a)=(φ_t(a),ψ_t(a)).
-/
def prod (phi : AsymptoticMorphism A B) (psi : AsymptoticMorphism A C) :
    AsymptoticMorphism A (B × C) where
  toFun t a := (phi t a, psi t a)
  continuous_orbit a := (phi.continuous_orbit a).prodMk (psi.continuous_orbit a)
  add_defect_tendsto a b := by
    change Filter.Tendsto (fun t =>
      (phi t (a + b) - (phi t a + phi t b), psi t (a + b) - (psi t a + psi t b)))
      Filter.atTop (𝓝 ((0 : B), (0 : C)))
    exact (phi.add_defect_tendsto a b).prodMk_nhds (psi.add_defect_tendsto a b)
  smul_defect_tendsto z a := by
    change Filter.Tendsto (fun t =>
      (phi t (z • a) - z • phi t a, psi t (z • a) - z • psi t a))
      Filter.atTop (𝓝 ((0 : B), (0 : C)))
    exact (phi.smul_defect_tendsto z a).prodMk_nhds (psi.smul_defect_tendsto z a)
  mul_defect_tendsto a b := by
    change Filter.Tendsto (fun t =>
      (phi t (a * b) - phi t a * phi t b, psi t (a * b) - psi t a * psi t b))
      Filter.atTop (𝓝 ((0 : B), (0 : C)))
    exact (phi.mul_defect_tendsto a b).prodMk_nhds (psi.mul_defect_tendsto a b)
  star_defect_tendsto a := by
    change Filter.Tendsto (fun t => (phi t (star a) - star (phi t a), psi t (star a) - star (psi t a)))
      Filter.atTop (𝓝 ((0 : B), (0 : C)))
    exact (phi.star_defect_tendsto a).prodMk_nhds (psi.star_defect_tendsto a)

/-- **Value of the product asymptotic morphism.**

Let A,B,C be nonunital complex C-star algebras, φ:A→B and ψ:A→C asymptotic star morphisms. For
t≥1 and a∈A, prod φ ψ t a=(φ_t(a),ψ_t(a)).
-/
@[simp]
theorem prod_apply (phi : AsymptoticMorphism A B) (psi : AsymptoticMorphism A C)
    (t : AsymptoticTime) (a : A) : prod phi psi t a = (phi t a, psi t a) := by
  rw [← AsymptoticMorphism.toFun_eq_coe]
  rfl

end AsymptoticMorphism
