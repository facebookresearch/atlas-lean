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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Correspondence
public import MathlibExt.Analysis.CStarAlgebra.Pullback
public import MathlibExt.Analysis.CStarAlgebra.Extension.Basic

/-!
# Full-time pullback extension of an asymptotic morphism

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). The
projections p(a,F)=a and r(a,F)=F are star homomorphisms. The sequence 0→C₀(T,B)→Dφ→A→0 is
exact, with inclusion F↦(0,F) and quotient p. The orbit section a↦(a,t↦φ_t(a)) is a right
inverse of p, and evaluation ev_t(a,F)=F(t) is point-norm continuous in t.

Reference: Blackadar, K-Theory for Operator Algebras (1998), §25.6, the extension preceding
Proposition 25.6.2.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ZeroAtInfty BoundedContinuousFunction

noncomputable section

namespace AsymptoticMorphism

universe uA uB

variable {A : Type uA} {B : Type uB}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

attribute [local instance] _root_.AsymptoticAlgebra.cStarAlgebra

/-- **Closed full-time asymptotic pullback algebra.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞).
FullTimePullback φ is this closed nonunital C-star subalgebra Dφ of A×C_b(T,B).
-/
abbrev FullTimePullback (φ : AsymptoticMorphism A B) : Type (max uA uB) :=
  letI : NonUnitalCStarAlgebra (AsymptoticAlgebra B) :=
    _root_.AsymptoticAlgebra.cStarAlgebra B
  ↥(NonUnitalCStarPullback.Pullback (toHom φ)
    (_root_.AsymptoticAlgebra.quotientMap B))

namespace FullTimePullback

variable (φ : AsymptoticMorphism A B)

/-- **Coefficient projection of the full-time pullback.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). The nonunital
complex star homomorphism projection φ:Dφ→A is p(a,F)=a.
-/
def projection : FullTimePullback φ →⋆ₙₐ[ℂ] A :=
  NonUnitalCStarPullback.fstHom (toHom φ)
    (_root_.AsymptoticAlgebra.quotientMap B)

/-- **Bounded-function projection of the full-time pullback.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). The nonunital
complex star homomorphism orbitProjection φ:Dφ→C_b(T,B) is r(a,F)=F.
-/
def orbitProjection : FullTimePullback φ →⋆ₙₐ[ℂ] (AsymptoticTime →ᵇ B) :=
  NonUnitalCStarPullback.sndHom (toHom φ)
    (_root_.AsymptoticAlgebra.quotientMap B)

/-- **Value of the coefficient projection.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For
d=(a,F)∈Dφ, projection φ d=a.
-/
theorem projection_apply (d : FullTimePullback φ) :
    projection φ d = d.val.1 :=
  rfl

/-- **Value of the bounded-function projection.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For
d=(a,F)∈Dφ, orbitProjection φ d=F.
-/
theorem orbitProjection_apply (d : FullTimePullback φ) :
    orbitProjection φ d = d.val.2 :=
  rfl

/-- **Compatibility condition of the full-time pullback.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For d∈Dφ,
toHom φ (projection φ d)=q_B(orbitProjection φ d), where toHom φ=Φφ.
-/
theorem condition (d : FullTimePullback φ) :
    toHom φ (projection φ d) =
      _root_.AsymptoticAlgebra.quotientMap B (orbitProjection φ d) :=
  NonUnitalCStarPullback.condition (toHom φ)
    (_root_.AsymptoticAlgebra.quotientMap B) d

/-- **Orbit-valued set section of the coefficient projection.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). The map
setSection φ:A→Dφ is a↦(a,F_a), where F_a(t)=φ_t(a) is the bounded continuous coefficient
orbit.
-/
def setSection (a : A) : FullTimePullback φ :=
  NonUnitalCStarPullback.mk (toHom φ)
    (_root_.AsymptoticAlgebra.quotientMap B)
    a (orbitBCF φ a) (toHom_apply φ a)

/-- **Projection of the orbit set section.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For a∈A,
projection φ (setSection φ a)=a.
-/
@[simp]
theorem projection_setSection (a : A) :
    projection φ (setSection φ a) = a :=
  rfl

/-- **Bounded orbit coordinate of the set section.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For a∈A,
orbitProjection φ (setSection φ a)=orbitBCF φ a, the function t↦φ_t(a).
-/
@[simp]
theorem orbitProjection_setSection (a : A) :
    orbitProjection φ (setSection φ a) = orbitBCF φ a :=
  rfl

/-- **Inclusion of functions vanishing at infinity into the pullback kernel.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). The nonunital
complex star homomorphism kernelInclusion φ:C₀(T,B)→Dφ sends F to (0,F), regarding F as a
bounded continuous function on the whole ray T.
-/
def kernelInclusion : C₀(AsymptoticTime, B) →⋆ₙₐ[ℂ] FullTimePullback φ where
  toFun f :=
    NonUnitalCStarPullback.mk (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B) 0 f.toBCF
      ((map_zero (toHom φ)).trans
        (_root_.AsymptoticAlgebra.quotientMap_toBCF f).symm)
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' := by
    intro f g
    apply NonUnitalCStarPullback.ext (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B)
    · change (0 : A) = 0 + 0
      exact (zero_add 0).symm
    · change (f + g).toBCF = f.toBCF + g.toBCF
      apply BoundedContinuousFunction.ext
      intro t
      rfl
  map_smul' := by
    intro z f
    apply NonUnitalCStarPullback.ext (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B)
    · change (0 : A) = z • 0
      exact (smul_zero z).symm
    · change (z • f).toBCF = z • f.toBCF
      apply BoundedContinuousFunction.ext
      intro t
      rfl
  map_mul' := by
    intro f g
    apply NonUnitalCStarPullback.ext (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B)
    · change (0 : A) = 0 * 0
      exact (zero_mul 0).symm
    · change (f * g).toBCF = f.toBCF * g.toBCF
      apply BoundedContinuousFunction.ext
      intro t
      rfl
  map_star' := by
    intro f
    apply NonUnitalCStarPullback.ext (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B)
    · change (0 : A) = star 0
      exact (star_zero A).symm
    · change (star f).toBCF = star f.toBCF
      apply BoundedContinuousFunction.ext
      intro t
      rfl

/-- **Coefficient projection of a vanishing-function kernel element.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For F∈C₀(T,B),
projection φ (kernelInclusion φ F)=0.
-/
@[simp]
theorem projection_kernelInclusion (f : C₀(AsymptoticTime, B)) :
    projection φ (kernelInclusion φ f) = 0 :=
  rfl

/-- **Function coordinate of the full kernel inclusion.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For F∈C₀(T,B),
orbitProjection φ (kernelInclusion φ F)=F.toBCF, its bounded continuous function on T.
-/
@[simp]
theorem orbitProjection_kernelInclusion (f : C₀(AsymptoticTime, B)) :
    orbitProjection φ (kernelInclusion φ f) = f.toBCF :=
  rfl

/-- **Injectivity of the full vanishing-function kernel inclusion.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). The
homomorphism kernelInclusion φ:C₀(T,B)→Dφ, F↦(0,F), is injective.
-/
theorem kernelInclusion_injective : Function.Injective (kernelInclusion φ) := by
  intro f g h
  apply ZeroAtInftyContinuousMap.toBCF_injective AsymptoticTime B
  have hcoord := congrArg (orbitProjection φ) h
  simpa only [orbitProjection_kernelInclusion] using hcoord

/-- **Surjectivity of the full-time coefficient projection.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). The projection
p:Dφ→A is surjective, with set section a↦(a,t↦φ_t(a)).
-/
theorem projection_surjective : Function.Surjective (projection φ) :=
  fun a => ⟨setSection φ a, projection_setSection φ a⟩

/-- **Exact sequence of the full-time pullback.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For
k:C₀(T,B)→Dφ, k(F)=(0,F), and p:Dφ→A, p(a,F)=a, range(k)=ker(p).
-/
theorem exact : Function.Exact (kernelInclusion φ) (projection φ) := by
  intro d
  constructor
  · intro hd
    have hq :
        _root_.AsymptoticAlgebra.quotientMap B (orbitProjection φ d) = 0 := by
      rw [← condition φ d, hd, map_zero]
    have hmem :
        orbitProjection φ d ∈
          (BoundedContinuousFunction.vanishingIdeal AsymptoticTime B :
            Set (AsymptoticTime →ᵇ B)) :=
      (_root_.AsymptoticAlgebra.mem_vanishingIdeal_iff (orbitProjection φ d)).2
        ((_root_.AsymptoticAlgebra.quotientMap_eq_zero_iff
          (orbitProjection φ d)).1 hq)
    rw [BoundedContinuousFunction.vanishingIdeal_carrier AsymptoticTime B] at hmem
    obtain ⟨f, hf⟩ := hmem
    refine ⟨f, ?_⟩
    apply NonUnitalCStarPullback.ext (toHom φ)
      (_root_.AsymptoticAlgebra.quotientMap B)
    · change projection φ (kernelInclusion φ f) = projection φ d
      rw [projection_kernelInclusion, hd]
    · change orbitProjection φ (kernelInclusion φ f) = orbitProjection φ d
      exact (orbitProjection_kernelInclusion φ f).trans hf
  · rintro ⟨f, rfl⟩
    exact projection_kernelInclusion φ f

/-- **C-star extension with the full-time pullback as middle algebra.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). The extension
FullTimePullback.extension φ is 0→C₀(T,B)→Dφ→A→0, with kernel inclusion F↦(0,F) and quotient
(a,F)↦a.
-/
def extension : CStarExtension A C₀(AsymptoticTime, B) :=
  CStarExtension.ofExact (kernelInclusion φ) (projection φ)
    (kernelInclusion_injective φ) (projection_surjective φ) (exact φ)

/-- **Middle algebra of the full-time extension.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). The middle
algebra of FullTimePullback.extension φ is FullTimePullback φ=Dφ.
-/
theorem extension_middle :
    (extension φ).Middle = FullTimePullback φ :=
  rfl

/-- **Kernel inclusion of the full-time extension.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For F∈C₀(T,B),
(extension φ).inclusion F=kernelInclusion φ F=(0,F).
-/
theorem extension_inclusion_apply (f : C₀(AsymptoticTime, B)) :
    (extension φ).inclusion f = kernelInclusion φ f :=
  CStarExtension.ofExact_inclusion_apply (kernelInclusion φ) (projection φ)
    (kernelInclusion_injective φ) (projection_surjective φ) (exact φ) f

/-- **Quotient map of the full-time extension.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For
d=(a,F)∈Dφ, (extension φ).quotient d=projection φ d=a.
-/
theorem extension_quotient_apply (d : FullTimePullback φ) :
    (extension φ).quotient d = projection φ d :=
  CStarExtension.ofExact_quotient_apply (kernelInclusion φ) (projection φ)
    (kernelInclusion_injective φ) (projection_surjective φ) (exact φ) d

/-- **Evaluation homomorphism at a fixed asymptotic time.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For t≥1,
evaluation φ t:Dφ→B is the nonunital complex star homomorphism ev_t(a,F)=F(t).
-/
def evaluation (t : AsymptoticTime) : FullTimePullback φ →⋆ₙₐ[ℂ] B where
  toFun d := orbitProjection φ d t
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- **Value of full-time pullback evaluation.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For t≥1 and
d=(a,F)∈Dφ, evaluation φ t d=orbitProjection φ d t=F(t).
-/
@[simp]
theorem evaluation_apply (t : AsymptoticTime) (d : FullTimePullback φ) :
    evaluation φ t d = orbitProjection φ d t :=
  rfl

/-- **Evaluation of the orbit set section.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For t≥1 and
a∈A, evaluation φ t (setSection φ a)=φ_t(a).
-/
theorem evaluation_setSection (t : AsymptoticTime) (a : A) :
    evaluation φ t (setSection φ a) = φ t a := by
  rw [evaluation_apply, orbitProjection_setSection, orbitBCF_apply]

/-- **Evaluation of a vanishing-function kernel element.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For t≥1 and
F∈C₀(T,B), evaluation φ t (kernelInclusion φ F)=F(t), including t=1.
-/
theorem evaluation_kernelInclusion
    (t : AsymptoticTime) (f : C₀(AsymptoticTime, B)) :
    evaluation φ t (kernelInclusion φ f) = f t := by
  rw [evaluation_apply, orbitProjection_kernelInclusion]
  rfl

/-- **Point-norm continuity of pullback evaluations.**

Let A,B be nonunital complex C-star algebras in independent universes, T=[1,∞) and φ:A→B an
asymptotic star morphism. For q_B:C_b(T,B)→B∞=C_b(T,B)/C₀(T,B), put Φφ(a)=q_B(t↦φ_t(a)). Let
Dφ=FullTimePullback φ={(a,F)∈A×C_b(T,B):Φφ(a)=q_B(F)}, with norm max(‖a‖,‖F‖∞). For each
d=(a,F)∈Dφ, t↦evaluation φ t d=F(t) is norm-continuous on T.
-/
theorem evaluation_continuous (d : FullTimePullback φ) :
    Continuous (fun t : AsymptoticTime => evaluation φ t d) := by
  have hd : Continuous (fun t : AsymptoticTime => orbitProjection φ d t) :=
    (orbitProjection φ d).continuous
  simpa only [evaluation_apply] using hd

end FullTimePullback

end AsymptoticMorphism
