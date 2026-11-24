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

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Topology.UnitInterval

import Mathlib.Topology.Algebra.Star
import Mathlib.Tactic.Abel

/-!
# Nonlinear asymptotic *-morphisms

Only each fixed-coefficient time orbit is continuous. The slices are arbitrary
functions, not necessarily linear or continuous in the coefficient. Boundedness
and sharp asymptotic contractivity are the separate derived Proposition25.1.3,
not fields or premises of this definition. This generic data is motivated by
Blackadar's Definition25.1.1.

The source's four norm-defect limits are equivalently vector limits to zero in
the given normed topology. Homotopy data uses the ACTUAL compact continuous
function algebra and its norm, with exact endpoint values. No homotopy quotient,
E-group or KK object is defined before its own real prerequisites.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter

universe uA uB

/-- The half-line time domain, with its induced real topology and order. -/
abbrev AsymptoticTime := Set.Ici (1 : ℝ)

/-- An asymptotic *-morphism with arbitrary nonlinear slices and no boundedness premise. -/
structure AsymptoticMorphism
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] where
  /-- The raw time-indexed maps; individual slices need not be linear. -/
  toFun : AsymptoticTime → A → B
  continuous_orbit : ∀ a : A, Continuous fun t => toFun t a
  add_defect_tendsto : ∀ a b : A,
    Filter.Tendsto (fun t => toFun t (a + b) - (toFun t a + toFun t b))
      Filter.atTop (nhds 0)
  smul_defect_tendsto : ∀ (z : ℂ) (a : A),
    Filter.Tendsto (fun t => toFun t (z • a) - z • toFun t a)
      Filter.atTop (nhds 0)
  mul_defect_tendsto : ∀ a b : A,
    Filter.Tendsto (fun t => toFun t (a * b) - toFun t a * toFun t b)
      Filter.atTop (nhds 0)
  star_defect_tendsto : ∀ a : A,
    Filter.Tendsto (fun t => toFun t (star a) - star (toFun t a))
      Filter.atTop (nhds 0)

namespace AsymptoticMorphism

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

@[macro_inline]
instance instFunLike : FunLike (AsymptoticMorphism A B) AsymptoticTime (A → B) where
  coe := AsymptoticMorphism.toFun
  coe_injective := by
    intro φ ψ h
    cases φ
    cases ψ
    cases h
    rfl

/-- The stored nonlinear time family is the actual public function coercion. -/
@[simp]
theorem toFun_eq_coe (φ : AsymptoticMorphism A B) :
    φ.toFun = (φ : AsymptoticTime → A → B) := by
  rfl

/-- Asymptotic morphisms are determined by their values; their remaining fields are proofs. -/
@[ext]
theorem ext {φ ψ : AsymptoticMorphism A B}
    (h : ∀ (t : AsymptoticTime) (a : A), φ t a = ψ t a) : φ = ψ :=
  DFunLike.ext φ ψ (fun t => funext (h t))

/-- The zero orbit tends to zero; exact zero at every finite time is NOT assumed. -/
theorem zero_tendsto (φ : AsymptoticMorphism A B) :
    Filter.Tendsto (fun t => φ t 0) Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun t : AsymptoticTime => φ.toFun t (0 : A))
    Filter.atTop (nhds (0 : B))
  simpa only [zero_smul, sub_zero] using
    φ.smul_defect_tendsto (0 : ℂ) (0 : A)

/-- Strict equivalence is the source's pointwise-in-coefficient vanishing difference. -/
def StrictlyEquivalent (φ ψ : AsymptoticMorphism A B) : Prop :=
  ∀ a : A, Filter.Tendsto (fun t => φ t a - ψ t a) Filter.atTop (nhds 0)

theorem strictlyEquivalent_refl (φ : AsymptoticMorphism A B) :
    StrictlyEquivalent φ φ := by
  intro a
  simp only [sub_self]
  exact tendsto_const_nhds

theorem strictlyEquivalent_symm {φ ψ : AsymptoticMorphism A B}
    (h : StrictlyEquivalent φ ψ) : StrictlyEquivalent ψ φ := by
  intro a
  simpa only [neg_sub, neg_zero] using (h a).neg

theorem strictlyEquivalent_trans {φ ψ χ : AsymptoticMorphism A B}
    (h₁ : StrictlyEquivalent φ ψ) (h₂ : StrictlyEquivalent ψ χ) :
    StrictlyEquivalent φ χ := by
  intro a
  have heq : (fun t => φ t a - χ t a) =
      (fun t => (φ t a - ψ t a) + (ψ t a - χ t a)) := by
    funext t
    abel
  rw [heq]
  simpa only [zero_add] using (h₁ a).add (h₂ a)

theorem strictlyEquivalent_equivalence
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Equivalence (StrictlyEquivalent : AsymptoticMorphism A B →
      AsymptoticMorphism A B → Prop) :=
  { refl := strictlyEquivalent_refl
    symm := strictlyEquivalent_symm
    trans := strictlyEquivalent_trans }

/-- An actual strict-equivalence setoid, NOT the source's homotopy quotient [[A,B]]. -/
def strictSetoid
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Setoid (AsymptoticMorphism A B) where
  r := StrictlyEquivalent
  iseqv := strictlyEquivalent_equivalence A B

/-- A genuine homomorphism-valued time family with exactly its point-norm continuity. -/
def ofHomFamily (f : AsymptoticTime → A →⋆ₙₐ[ℂ] B)
    (hf : ∀ a : A, Continuous fun t => f t a) : AsymptoticMorphism A B where
  toFun t a := f t a
  continuous_orbit := hf
  add_defect_tendsto := by
    intro a b
    simpa only [map_add, sub_self] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : AsymptoticTime => (0 : B)) Filter.atTop (nhds 0))
  smul_defect_tendsto := by
    intro z a
    simpa only [map_smul, sub_self] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : AsymptoticTime => (0 : B)) Filter.atTop (nhds 0))
  mul_defect_tendsto := by
    intro a b
    simpa only [map_mul, sub_self] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : AsymptoticTime => (0 : B)) Filter.atTop (nhds 0))
  star_defect_tendsto := by
    intro a
    simpa only [map_star, sub_self] using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : AsymptoticTime => (0 : B)) Filter.atTop (nhds 0))

@[simp]
theorem ofHomFamily_apply (f : AsymptoticTime → A →⋆ₙₐ[ℂ] B)
    (hf : ∀ a : A, Continuous fun t => f t a) (t : AsymptoticTime) (a : A) :
    ofHomFamily f hf t a = f t a := by
  rfl

/-- The actual constant family of an ordinary star homomorphism. -/
def ofHom (f : A →⋆ₙₐ[ℂ] B) : AsymptoticMorphism A B :=
  ofHomFamily (fun _ => f) (fun _ => continuous_const)

@[simp]
theorem ofHom_apply (f : A →⋆ₙₐ[ℂ] B) (t : AsymptoticTime) (a : A) :
    ofHom f t a = f a := by
  rfl

/-- The actual zero input family, without any additive structure on all families. -/
def zero : AsymptoticMorphism A B :=
  ofHom (0 : A →⋆ₙₐ[ℂ] B)

@[simp]
theorem zero_apply (t : AsymptoticTime) (a : A) :
    zero (A := A) (B := B) t a = 0 := by
  rw [zero, ofHom_apply, NonUnitalStarAlgHom.zero_apply]

/-- Actual continuous proper-at-infinity reparametrization.
Increasing is not an additional premise. -/
def reparam (φ : AsymptoticMorphism A B)
    (r : AsymptoticTime → AsymptoticTime) (hr : Continuous r)
    (hrTop : Filter.Tendsto r Filter.atTop Filter.atTop) :
    AsymptoticMorphism A B where
  toFun t a := φ (r t) a
  continuous_orbit a := (φ.continuous_orbit a).comp hr
  add_defect_tendsto a b := (φ.add_defect_tendsto a b).comp hrTop
  smul_defect_tendsto z a := (φ.smul_defect_tendsto z a).comp hrTop
  mul_defect_tendsto a b := (φ.mul_defect_tendsto a b).comp hrTop
  star_defect_tendsto a := (φ.star_defect_tendsto a).comp hrTop

@[simp]
theorem reparam_apply (φ : AsymptoticMorphism A B)
    (r : AsymptoticTime → AsymptoticTime) (hr : Continuous r)
    (hrTop : Filter.Tendsto r Filter.atTop Filter.atTop)
    (t : AsymptoticTime) (a : A) : reparam φ r hr hrTop t a = φ (r t) a := by
  rfl

/-- An ACTUAL asymptotic family into C([0,1],B), with exact endpoint values.
The family's limits/continuity use this algebra's SUP norm, not pointwise s-limits. -/
structure Homotopy (φ₀ φ₁ : AsymptoticMorphism A B) where
  /-- The whole interval-valued asymptotic family defining this homotopy. -/
  family : AsymptoticMorphism A C(unitInterval, B)
  start : ∀ (t : AsymptoticTime) (a : A), family t a 0 = φ₀ t a
  finish : ∀ (t : AsymptoticTime) (a : A), family t a 1 = φ₁ t a

namespace Homotopy

/-- A homotopy is determined by its actual family; endpoint fields are proofs. -/
@[ext]
theorem ext {φ₀ φ₁ : AsymptoticMorphism A B} {H K : Homotopy φ₀ φ₁}
    (h : H.family = K.family) : H = K := by
  cases H
  cases K
  cases h
  rfl

end Homotopy

/-- Homotopy uses the actual family above, not an arbitrary supplied relation. -/
def Homotopic (φ₀ φ₁ : AsymptoticMorphism A B) : Prop :=
  Nonempty (Homotopy φ₀ φ₁)

end AsymptoticMorphism
