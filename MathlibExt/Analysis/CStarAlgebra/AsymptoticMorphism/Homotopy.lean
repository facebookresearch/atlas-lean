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
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.IntervalGluing

import Mathlib.Topology.Constructions

/-!
# Asymptotic homotopy equivalence and classes

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. A homotopy H between asymptotic
families φ,ψ is an asymptotic family A→C([0,1],B) with H_t(a)(0)=φ_t(a) and H_t(a)(1)=ψ_t(a),
using the supremum norm for time continuity and all defect limits. Constant paths, interval
reversal and concatenation at the midpoint make this homotopy relation an equivalence
relation. Its quotient is HomotopyClasses A B, denoted [[A,B]].
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped CStarAlgebra

noncomputable section

namespace AsymptoticMorphism

universe uA uB uC

section Postcomposition

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- **Fixed-homomorphism postcomposition of an asymptotic family.**

Let A,B,C be nonunital complex C-star algebras, φ:A→B an asymptotic star morphism on T=[1,∞)
and g:B→C a nonunital complex star homomorphism. The family postcomp φ g has values
(g∘φ)_t(a)=g(φ_t(a)).
-/
def postcomp (φ : AsymptoticMorphism A B) (g : B →⋆ₙₐ[ℂ] C) :
    AsymptoticMorphism A C where
  toFun t a := g (φ t a)
  continuous_orbit a := (map_continuous g).comp (φ.continuous_orbit a)
  add_defect_tendsto := by
    intro a b
    have h := ((map_continuous g).tendsto 0).comp (φ.add_defect_tendsto a b)
    simpa only [Function.comp_def, toFun_eq_coe, map_sub, map_add, map_zero] using h
  smul_defect_tendsto := by
    intro z a
    have h := ((map_continuous g).tendsto 0).comp (φ.smul_defect_tendsto z a)
    simpa only [Function.comp_def, toFun_eq_coe, map_sub, map_smul, map_zero] using h
  mul_defect_tendsto := by
    intro a b
    have h := ((map_continuous g).tendsto 0).comp (φ.mul_defect_tendsto a b)
    simpa only [Function.comp_def, toFun_eq_coe, map_sub, map_mul, map_zero] using h
  star_defect_tendsto := by
    intro a
    have h := ((map_continuous g).tendsto 0).comp (φ.star_defect_tendsto a)
    simpa only [Function.comp_def, toFun_eq_coe, map_sub, map_star, map_zero] using h

@[simp]
theorem postcomp_apply (φ : AsymptoticMorphism A B) (g : B →⋆ₙₐ[ℂ] C)
    (t : AsymptoticTime) (a : A) : postcomp φ g t a = g (φ t a) := by
  rfl

end Postcomposition

section Homotopies

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {φ ψ χ : AsymptoticMorphism A B}

open ContinuousMap.IntervalGluing

namespace Homotopy

/-- **Pair of matching asymptotic homotopies.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. A homotopy H between asymptotic
families φ,ψ is an asymptotic family A→C([0,1],B) with H_t(a)(0)=φ_t(a) and H_t(a)(1)=ψ_t(a),
using the supremum norm for time continuity and all defect limits. Given H from φ to ψ and K
from ψ to χ, pairFamily H K has value a↦(H_t(a),K_t(a)) in MatchingPaths
B={(F,G)∈C([0,1],B)²:F(1)=G(0)}, with the inherited maximum of the two supremum norms.
-/
def pairFamily (H : Homotopy φ ψ) (K : Homotopy ψ χ) :
    AsymptoticMorphism A (MatchingPaths B) where
  toFun t a := NonUnitalCStarPullback.mk (evalAt B 1) (evalAt B 0)
    (H.family t a) (K.family t a) ((H.finish t a).trans (K.start t a).symm)
  continuous_orbit := by
    intro a
    exact ((H.family.continuous_orbit a).prodMk
      (K.family.continuous_orbit a)).subtype_mk
        (fun t => (H.finish t a).trans (K.start t a).symm)
  add_defect_tendsto := by
    intro a b
    apply tendsto_subtype_rng.mpr
    change Filter.Tendsto (fun t =>
      (H.family t (a + b) - (H.family t a + H.family t b),
        K.family t (a + b) - (K.family t a + K.family t b)))
      Filter.atTop (nhds ((0 : C(unitInterval, B)), (0 : C(unitInterval, B))))
    exact (H.family.add_defect_tendsto a b).prodMk_nhds
      (K.family.add_defect_tendsto a b)
  smul_defect_tendsto := by
    intro z a
    apply tendsto_subtype_rng.mpr
    change Filter.Tendsto (fun t =>
      (H.family t (z • a) - z • H.family t a,
        K.family t (z • a) - z • K.family t a))
      Filter.atTop (nhds ((0 : C(unitInterval, B)), (0 : C(unitInterval, B))))
    exact (H.family.smul_defect_tendsto z a).prodMk_nhds
      (K.family.smul_defect_tendsto z a)
  mul_defect_tendsto := by
    intro a b
    apply tendsto_subtype_rng.mpr
    change Filter.Tendsto (fun t =>
      (H.family t (a * b) - H.family t a * H.family t b,
        K.family t (a * b) - K.family t a * K.family t b))
      Filter.atTop (nhds ((0 : C(unitInterval, B)), (0 : C(unitInterval, B))))
    exact (H.family.mul_defect_tendsto a b).prodMk_nhds
      (K.family.mul_defect_tendsto a b)
  star_defect_tendsto := by
    intro a
    apply tendsto_subtype_rng.mpr
    change Filter.Tendsto (fun t =>
      (H.family t (star a) - star (H.family t a),
        K.family t (star a) - star (K.family t a)))
      Filter.atTop (nhds ((0 : C(unitInterval, B)), (0 : C(unitInterval, B))))
    exact (H.family.star_defect_tendsto a).prodMk_nhds
      (K.family.star_defect_tendsto a)

@[simp]
theorem pairFamily_val (H : Homotopy φ ψ) (K : Homotopy ψ χ)
    (t : AsymptoticTime) (a : A) :
    ((pairFamily H K t a : MatchingPaths B) :
      C(unitInterval, B) × C(unitInterval, B)) = (H.family t a, K.family t a) := by
  rfl

/-- **Constant asymptotic homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For φ:A→B, Homotopy.refl φ is the path
family H_t(a)(s)=φ_t(a) for s∈[0,1], with both endpoints φ.
-/
def refl (φ : AsymptoticMorphism A B) : Homotopy φ φ where
  family := postcomp φ (constantHom B)
  start := by
    intro t a
    rw [postcomp_apply, constantHom_apply]
  finish := by
    intro t a
    rw [postcomp_apply, constantHom_apply]

/-- **Reversal of an asymptotic homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. A homotopy H between asymptotic
families φ,ψ is an asymptotic family A→C([0,1],B) with H_t(a)(0)=φ_t(a) and H_t(a)(1)=ψ_t(a),
using the supremum norm for time continuity and all defect limits. The reversed homotopy
Homotopy.symm H runs from ψ to φ and has value H_t(a)(1-s).
-/
def symm (H : Homotopy φ ψ) : Homotopy ψ φ where
  family := postcomp H.family (reverseHom B)
  start := by
    intro t a
    rw [postcomp_apply, reverseHom_zero]
    exact H.finish t a
  finish := by
    intro t a
    rw [postcomp_apply, reverseHom_one]
    exact H.start t a

/-- **Concatenation of matching asymptotic homotopies.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. A homotopy H between asymptotic
families φ,ψ is an asymptotic family A→C([0,1],B) with H_t(a)(0)=φ_t(a) and H_t(a)(1)=ψ_t(a),
using the supremum norm for time continuity and all defect limits. For H from φ to ψ and K
from ψ to χ, Homotopy.trans H K runs from φ to χ. Its value at s≤1/2 is H_t(a)(2s), and at
s>1/2 it is K_t(a)(2s-1); both agree with ψ_t(a) at the midpoint.
-/
def trans (H : Homotopy φ ψ) (K : Homotopy ψ χ) : Homotopy φ χ where
  family := postcomp (pairFamily H K) (glueHom (B := B))
  start := by
    intro t a
    rw [postcomp_apply, glueHom_zero, pairFamily_val]
    exact H.start t a
  finish := by
    intro t a
    rw [postcomp_apply, glueHom_one, pairFamily_val]
    exact K.finish t a

end Homotopy

theorem homotopic_refl (φ : AsymptoticMorphism A B) : Homotopic φ φ :=
  ⟨Homotopy.refl φ⟩

theorem homotopic_symm {φ ψ : AsymptoticMorphism A B}
    (h : Homotopic φ ψ) : Homotopic ψ φ := by
  rcases h with ⟨H⟩
  exact ⟨H.symm⟩

theorem homotopic_trans {φ ψ χ : AsymptoticMorphism A B}
    (h₁ : Homotopic φ ψ) (h₂ : Homotopic ψ χ) : Homotopic φ χ := by
  rcases h₁ with ⟨H⟩
  rcases h₂ with ⟨K⟩
  exact ⟨H.trans K⟩

theorem homotopic_equivalence
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Equivalence (Homotopic : AsymptoticMorphism A B →
      AsymptoticMorphism A B → Prop) :=
  { refl := homotopic_refl
    symm := homotopic_symm
    trans := homotopic_trans }

/-- **Setoid of asymptotic homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. A homotopy H between asymptotic
families φ,ψ is an asymptotic family A→C([0,1],B) with H_t(a)(0)=φ_t(a) and H_t(a)(1)=ψ_t(a),
using the supremum norm for time continuity and all defect limits. The setoid homotopySetoid A
B has relation Homotopic φ ψ, meaning that a homotopy H with these endpoints exists.
-/
def homotopySetoid
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Setoid (AsymptoticMorphism A B) where
  r := Homotopic
  iseqv := homotopic_equivalence A B

/-- **Asymptotic homotopy classes.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. A homotopy H between asymptotic
families φ,ψ is an asymptotic family A→C([0,1],B) with H_t(a)(0)=φ_t(a) and H_t(a)(1)=ψ_t(a),
using the supremum norm for time continuity and all defect limits. HomotopyClasses A B is the
quotient of asymptotic star morphisms A→B by this homotopy relation, denoted [[A,B]].
-/
abbrev HomotopyClasses
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  Quotient (homotopySetoid A B)

/-- **Class of an asymptotic morphism.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. A homotopy H between asymptotic
families φ,ψ is an asymptotic family A→C([0,1],B) with H_t(a)(0)=φ_t(a) and H_t(a)(1)=ψ_t(a),
using the supremum norm for time continuity and all defect limits. The map mkClass sends φ to
its class in [[A,B]]=HomotopyClasses A B.
-/
def mkClass (φ : AsymptoticMorphism A B) : HomotopyClasses A B :=
  Quotient.mk _ φ

@[simp]
theorem mkClass_eq_mkClass_iff (φ ψ : AsymptoticMorphism A B) :
    mkClass φ = mkClass ψ ↔ Homotopic φ ψ := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

end Homotopies

end AsymptoticMorphism
