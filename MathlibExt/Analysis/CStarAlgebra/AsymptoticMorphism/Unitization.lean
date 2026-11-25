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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Normalization
public import Mathlib.Analysis.CStarAlgebra.Unitization

import Mathlib.Tactic.Abel

/-!
# Unitization of asymptotic star morphisms

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞. On
the complex C-star unitizations Ã and B̃, the family φ̃_t(z,a)=(z,φ_t(a)) is an asymptotic
star morphism. Applied to the zero-normalized family φ0_t(a)=φ_t(a)-φ_t(0), it preserves the
unit exactly at every time.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter

noncomputable section

namespace AsymptoticMorphism

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Asymptotic family on complex unitizations.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
The family unitization φ:Unitization ℂ A→Unitization ℂ B has values φ̃_t(z,a)=(z,φ_t(a)).
-/
def unitization (φ : AsymptoticMorphism A B) :
    AsymptoticMorphism (Unitization ℂ A) (Unitization ℂ B) := by
  let F : AsymptoticTime → Unitization ℂ A → Unitization ℂ B :=
    fun t x => Unitization.inl x.fst + Unitization.inr (φ t x.snd)
  have hinr {f : AsymptoticTime → B} (hf : Tendsto f atTop (nhds 0)) :
      Tendsto (fun t => (Unitization.inr (f t) : Unitization ℂ B))
        atTop (nhds 0) := by
    simpa only [Function.comp_def, Unitization.inr_zero] using
      (Unitization.continuous_inr.tendsto (0 : B)).comp hf
  refine
    { toFun := F
      continuous_orbit := ?_
      add_defect_tendsto := ?_
      smul_defect_tendsto := ?_
      mul_defect_tendsto := ?_
      star_defect_tendsto := ?_ }
  · intro x
    exact continuous_const.fun_add
      (Unitization.continuous_inr.comp (φ.continuous_orbit x.snd))
  · intro x y
    have heq :
        (fun t => F t (x + y) - (F t x + F t y)) =
        (fun t => (Unitization.inr
          (φ t (x.snd + y.snd) - (φ t x.snd + φ t y.snd)) :
            Unitization ℂ B)) := by
      funext t
      apply Unitization.ext <;> simp [F, sub_eq_add_neg]
    rw [heq]
    exact hinr (φ.add_defect_tendsto x.snd y.snd)
  · intro z x
    have heq :
        (fun t => F t (z • x) - z • F t x) =
        (fun t => (Unitization.inr
          (φ t (z • x.snd) - z • φ t x.snd) : Unitization ℂ B)) := by
      funext t
      apply Unitization.ext <;> simp [F, sub_eq_add_neg]
    rw [heq]
    exact hinr (φ.smul_defect_tendsto z x.snd)
  · intro x y
    let a := x.fst • y.snd
    let b := y.fst • x.snd
    let c := x.snd * y.snd
    let D : AsymptoticTime → B := fun t =>
      (φ t ((a + b) + c) - (φ t (a + b) + φ t c)) +
      (φ t (a + b) - (φ t a + φ t b)) +
      (φ t a - x.fst • φ t y.snd) +
      (φ t b - y.fst • φ t x.snd) +
      (φ t c - φ t x.snd * φ t y.snd)
    have hD : Tendsto D atTop (nhds 0) := by
      simpa only [toFun_eq_coe, D, a, b, c, zero_add] using
        ((((φ.add_defect_tendsto (a + b) c).add
          (φ.add_defect_tendsto a b)).add
          (φ.smul_defect_tendsto x.fst y.snd)).add
          (φ.smul_defect_tendsto y.fst x.snd)).add
          (φ.mul_defect_tendsto x.snd y.snd)
    have heq :
        (fun t => F t (x * y) - F t x * F t y) =
        (fun t => (Unitization.inr (D t) : Unitization ℂ B)) := by
      funext t
      apply Unitization.ext
      · simp [F, sub_eq_add_neg]
      · simp only [F, D, a, b, c, sub_eq_add_neg,
          Unitization.snd_add, Unitization.snd_neg, Unitization.snd_mul,
          Unitization.snd_inl, Unitization.snd_inr,
          Unitization.fst_add, Unitization.fst_inl, Unitization.fst_inr,
          add_zero, zero_add]
        abel
    rw [heq]
    exact hinr hD
  · intro x
    have heq :
        (fun t => F t (star x) - star (F t x)) =
        (fun t => (Unitization.inr
          (φ t (star x.snd) - star (φ t x.snd)) : Unitization ℂ B)) := by
      funext t
      apply Unitization.ext <;> simp [F, sub_eq_add_neg]
    rw [heq]
    exact hinr (φ.star_defect_tendsto x.snd)

/-- **Value of the unitized asymptotic family.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
For x=(z,a)∈Unitization ℂ A, unitization φ t x=Unitization.inl z+Unitization.inr(φ_t(a)) in
Unitization ℂ B.
-/
@[simp]
theorem unitization_apply (φ : AsymptoticMorphism A B)
    (t : AsymptoticTime) (x : Unitization ℂ A) :
    unitization φ t x =
      Unitization.inl x.fst + Unitization.inr (φ t x.snd) := by
  rfl

/-- **Restriction of unitization to the coefficient algebra.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
For a∈A and t∈T, unitization φ t (Unitization.inr a)=Unitization.inr(φ_t(a)).
-/
theorem unitization_inr_apply (φ : AsymptoticMorphism A B)
    (t : AsymptoticTime) (a : A) :
    unitization φ t (Unitization.inr a) =
      (Unitization.inr (φ t a) : Unitization ℂ B) := by
  simp only [unitization_apply, Unitization.fst_inr, Unitization.snd_inr,
    Unitization.inl_zero, zero_add]

/-- **Normalized unitization preserves the unit.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
With φ0=normalize φ and φ0_t(a)=φ_t(a)-φ_t(0), the unitized family satisfies unitization φ0 t
1=1 in Unitization ℂ B for every t≥1.
-/
theorem unitization_normalize_one (φ : AsymptoticMorphism A B)
    (t : AsymptoticTime) :
    unitization (normalize φ) t 1 = (1 : Unitization ℂ B) := by
  simp only [unitization_apply, Unitization.fst_one, Unitization.snd_one,
    normalize_zero, Unitization.inr_zero, Unitization.inl_one, add_zero]

end AsymptoticMorphism
