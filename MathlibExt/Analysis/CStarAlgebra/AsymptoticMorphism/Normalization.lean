/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Basic

import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Star
import Mathlib.Tactic.Abel

/-!
# Zero normalization of an asymptotic morphism

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
Put φ0_t(a)=φ_t(a)-φ_t(0). Then φ0 is an asymptotic star morphism, φ0_t(0)=0 at every time,
and φ0_t(a)-φ_t(a)→0 for every a as t→∞.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter

namespace AsymptoticMorphism

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Asymptotic morphism with its zero orbit subtracted.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
The asymptotic star morphism normalize φ has values φ0_t(a)=φ_t(a)-φ_t(0).
-/
def normalize (φ : AsymptoticMorphism A B) : AsymptoticMorphism A B := by
  let f : AsymptoticTime → A → B := fun t a => φ t a - φ t 0
  refine
    { toFun := f
      continuous_orbit := ?_
      add_defect_tendsto := ?_
      smul_defect_tendsto := ?_
      mul_defect_tendsto := ?_
      star_defect_tendsto := ?_ }
  · intro a
    change Continuous fun t => φ t a - φ t 0
    exact (φ.continuous_orbit a).fun_sub (φ.continuous_orbit 0)
  · intro a b
    have heq : (fun t => f t (a + b) - (f t a + f t b)) =
        (fun t => (φ t (a + b) - (φ t a + φ t b)) + φ t 0) := by
      funext t
      dsimp only [f]
      abel
    rw [heq]
    simpa only [toFun_eq_coe, zero_add] using (φ.add_defect_tendsto a b).add φ.zero_tendsto
  · intro z a
    have heq : (fun t => f t (z • a) - z • f t a) =
        (fun t => (φ t (z • a) - z • φ t a) - φ t 0 + z • φ t 0) := by
      funext t
      dsimp only [f]
      rw [smul_sub]
      abel
    rw [heq]
    have hz : Filter.Tendsto (fun t => z • φ t 0) Filter.atTop (nhds (z • (0 : B))) :=
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : AsymptoticTime => z) Filter.atTop (nhds z)).smul
          φ.zero_tendsto
    simpa only [toFun_eq_coe, sub_zero, zero_add, smul_zero] using
      ((φ.smul_defect_tendsto z a).sub φ.zero_tendsto).add hz
  · intro a b
    have heq : (fun t => f t (a * b) - f t a * f t b) =
        (fun t =>
          (φ t (a * b) - φ t a * φ t b) -
          (φ t (a * 0) - φ t a * φ t 0) -
          (φ t (0 * b) - φ t 0 * φ t b) + φ t 0 - φ t 0 * φ t 0) := by
      funext t
      dsimp only [f]
      simp only [mul_zero, zero_mul, sub_mul, mul_sub]
      abel
    rw [heq]
    have hz := φ.zero_tendsto.mul φ.zero_tendsto
    simpa only [toFun_eq_coe, sub_zero, zero_add, zero_mul] using
      ((((φ.mul_defect_tendsto a b).sub (φ.mul_defect_tendsto a 0)).sub
        (φ.mul_defect_tendsto 0 b)).add φ.zero_tendsto).sub hz
  · intro a
    have heq : (fun t => f t (star a) - star (f t a)) =
        (fun t => (φ t (star a) - star (φ t a)) - φ t 0 + star (φ t 0)) := by
      funext t
      dsimp only [f]
      rw [star_sub]
      abel
    rw [heq]
    simpa only [toFun_eq_coe, sub_zero, zero_add, star_zero] using
      ((φ.star_defect_tendsto a).sub φ.zero_tendsto).add φ.zero_tendsto.star

/-- **Value of the zero-normalized family.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
For t∈T and a∈A, normalize φ t a=φ_t(a)-φ_t(0).
-/
@[simp]
theorem normalize_apply (φ : AsymptoticMorphism A B)
    (t : AsymptoticTime) (a : A) : normalize φ t a = φ t a - φ t 0 := by
  rfl

/-- **Exact zero for the normalized family.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞. At
every t∈T, normalize φ t 0=0.
-/
theorem normalize_zero (φ : AsymptoticMorphism A B) (t : AsymptoticTime) :
    normalize φ t 0 = 0 := by
  rw [normalize_apply, sub_self]

/-- **Strict equivalence of normalization and the initial family.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
For every a∈A, normalize φ t a-φ_t(a)=-φ_t(0) tends to 0 as t→∞. Thus StrictlyEquivalent
(normalize φ) φ.
-/
theorem normalize_strictlyEquivalent (φ : AsymptoticMorphism A B) :
    StrictlyEquivalent (normalize φ) φ := by
  intro a
  have heq : (fun t => normalize φ t a - φ t a) = (fun t => -φ t 0) := by
    funext t
    rw [normalize_apply]
    abel
  rw [heq]
  simpa only [neg_zero] using φ.zero_tendsto.neg

end AsymptoticMorphism
