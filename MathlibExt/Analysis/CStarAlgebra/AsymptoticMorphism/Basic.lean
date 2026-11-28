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
# Asymptotic star morphisms and their homotopies

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. An asymptotic star morphism is a family φ_t:A→B whose orbit t↦φ_t(a) is
continuous for each a. For every a,b∈A and z∈ℂ, the four differences φ_t(a+b)-φ_t(a)-φ_t(b),
φ_t(z•a)-z•φ_t(a), φ_t(a*b)-φ_t(a)*φ_t(b) and φ_t(star(a))-star(φ_t(a)) tend to 0 in the norm
of B as t→∞. Its slices may be nonlinear. A homotopy
between φ0,φ1 is an asymptotic star morphism F:A→C([0,1],B) satisfying F_t(a)(0)=φ0_t(a) and
F_t(a)(1)=φ1_t(a); its time continuity and defect limits use the supremum norm on C([0,1],B).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter

universe uA uB

/-- **Half-line time for asymptotic morphisms.**

AsymptoticTime is the real half-line T={t∈ℝ:1≤t}=[1,∞), equipped with its subspace topology
and inherited order. The filter atTop describes t→∞.
-/
abbrev AsymptoticTime := Set.Ici (1 : ℝ)

/-- **Family defining an asymptotic star morphism.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. A family φ_t:A→B is an asymptotic star morphism when t↦φ_t(a) is
continuous for every a and for every a,b∈A and z∈ℂ, the four differences
φ_t(a+b)-φ_t(a)-φ_t(b), φ_t(z•a)-z•φ_t(a), φ_t(a*b)-φ_t(a)*φ_t(b) and
φ_t(star(a))-star(φ_t(a)) tend to 0 in the norm of B as t→∞. The time slices are arbitrary
functions subject to these conditions.
-/
structure AsymptoticMorphism
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] where
  /-- **Time-indexed coefficient values of an asymptotic morphism.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
The field toFun is the function T→A→B, (t,a)↦φ_t(a).
-/
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

/-- **Function values of an asymptotic morphism.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
The function φ.toFun:T→A→B equals the evaluation function (t,a)↦φ t a.
-/
@[simp]
theorem toFun_eq_coe (φ : AsymptoticMorphism A B) :
    φ.toFun = (φ : AsymptoticTime → A → B) := by
  rfl

/-- **Equality of asymptotic morphisms from coefficient values.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. If φ,ψ:A→B are asymptotic star morphisms with φ_t(a)=ψ_t(a) for every t∈T
and a∈A, then φ=ψ.
-/
@[ext]
theorem ext {φ ψ : AsymptoticMorphism A B}
    (h : ∀ (t : AsymptoticTime) (a : A), φ t a = ψ t a) : φ = ψ :=
  DFunLike.ext φ ψ (fun t => funext (h t))

/-- **The zero coefficient orbit tends to zero.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
The orbit t↦φ_t(0) tends to 0 in B as t→∞.
-/
theorem zero_tendsto (φ : AsymptoticMorphism A B) :
    Filter.Tendsto (fun t => φ t 0) Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun t : AsymptoticTime => φ.toFun t (0 : A))
    Filter.atTop (nhds (0 : B))
  simpa only [zero_smul, sub_zero] using
    φ.smul_defect_tendsto (0 : ℂ) (0 : A)

/-- **Strict equivalence of asymptotic morphisms.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Two asymptotic star morphisms φ,ψ:A→B are StrictlyEquivalent when
φ_t(a)-ψ_t(a)→0 in B as t→∞ for every fixed a∈A.
-/
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

/-- **Setoid of strict asymptotic equivalence.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. The setoid strictSetoid A B on asymptotic star morphisms has relation φ∼ψ
exactly when φ_t(a)-ψ_t(a) tends to 0 for every a∈A.
-/
def strictSetoid
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Setoid (AsymptoticMorphism A B) where
  r := StrictlyEquivalent
  iseqv := strictlyEquivalent_equivalence A B

/-- **Asymptotic morphism from a point-norm homomorphism family.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let f_t:A→B be nonunital complex star homomorphisms and assume t↦f_t(a) is
continuous for every a. The asymptotic morphism ofHomFamily f hf has values φ_t(a)=f_t(a),
with all four defects identically zero.
-/
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

/-- **Constant asymptotic morphism of a star homomorphism.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. For a nonunital complex star homomorphism f:A→B, ofHom f is the asymptotic
star morphism φ_t(a)=f(a) for every t∈T.
-/
def ofHom (f : A →⋆ₙₐ[ℂ] B) : AsymptoticMorphism A B :=
  ofHomFamily (fun _ => f) (fun _ => continuous_const)

@[simp]
theorem ofHom_apply (f : A →⋆ₙₐ[ℂ] B) (t : AsymptoticTime) (a : A) :
    ofHom f t a = f a := by
  rfl

/-- **Zero asymptotic morphism.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. The asymptotic morphism zero:A→B has values zero t a=0 for all t∈T and
a∈A.
-/
def zero : AsymptoticMorphism A B :=
  ofHom (0 : A →⋆ₙₐ[ℂ] B)

@[simp]
theorem zero_apply (t : AsymptoticTime) (a : A) :
    zero (A := A) (B := B) t a = 0 := by
  rw [zero, ofHom_apply, NonUnitalStarAlgHom.zero_apply]

/-- **Reparametrized asymptotic morphism.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. Let φ be an asymptotic star morphism A→B, a family φ_t:A→B with continuous
time orbits and vanishing additive, complex-scalar, multiplicative and star defects as t→∞.
Let r:T→T be continuous and tend to infinity as t→∞. The asymptotic morphism reparam φ r hr
hrTop has values (reparam φ r)_t(a)=φ_(r(t))(a).
-/
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

/-- **Homotopy through interval-valued asymptotic morphisms.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. For asymptotic star morphisms φ0,φ1:A→B, a homotopy between φ0,φ1 is an
asymptotic star morphism F:A→C([0,1],B) satisfying F_t(a)(0)=φ0_t(a) and F_t(a)(1)=φ1_t(a);
its time continuity and defect limits use the supremum norm on C([0,1],B). These families
constitute Homotopy φ0 φ1.
-/
structure Homotopy (φ₀ φ₁ : AsymptoticMorphism A B) where
  /-- **Interval-valued family of an asymptotic homotopy.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. A homotopy between φ0,φ1 is an asymptotic star morphism F:A→C([0,1],B)
satisfying F_t(a)(0)=φ0_t(a) and F_t(a)(1)=φ1_t(a); its time continuity and defect limits use
the supremum norm on C([0,1],B). The field family of Homotopy φ0 φ1 is this interval-valued
asymptotic morphism F.
-/
  family : AsymptoticMorphism A C(unitInterval, B)
  start : ∀ (t : AsymptoticTime) (a : A), family t a 0 = φ₀ t a
  finish : ∀ (t : AsymptoticTime) (a : A), family t a 1 = φ₁ t a

namespace Homotopy

/-- **Equality of asymptotic homotopies from their families.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. A homotopy between φ0,φ1 is an asymptotic star morphism F:A→C([0,1],B)
satisfying F_t(a)(0)=φ0_t(a) and F_t(a)(1)=φ1_t(a); its time continuity and defect limits use
the supremum norm on C([0,1],B). If homotopies H,K between φ0 and φ1 have equal
interval-valued families, then H=K.
-/
@[ext]
theorem ext {φ₀ φ₁ : AsymptoticMorphism A B} {H K : Homotopy φ₀ φ₁}
    (h : H.family = K.family) : H = K := by
  cases H
  cases K
  cases h
  rfl

end Homotopy

/-- **Homotopy relation on asymptotic morphisms.**

Let A,B be nonunital complex C-star algebras and T=AsymptoticTime=[1,∞), with its real
topology and order. A homotopy between φ0,φ1 is an asymptotic star morphism F:A→C([0,1],B)
satisfying F_t(a)(0)=φ0_t(a) and F_t(a)(1)=φ1_t(a); its time continuity and defect limits use
the supremum norm on C([0,1],B). The proposition Homotopic φ0 φ1 means that such an
interval-valued family F exists.
-/
def Homotopic (φ₀ φ₁ : AsymptoticMorphism A B) : Prop :=
  Nonempty (Homotopy φ₀ φ₁)

end AsymptoticMorphism
