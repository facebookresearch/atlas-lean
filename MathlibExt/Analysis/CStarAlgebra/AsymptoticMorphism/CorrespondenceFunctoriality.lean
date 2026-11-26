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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.AsymptoticAlgebraMap
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Correspondence
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Homotopy

/-!
# Naturality of the strict asymptotic correspondence

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), Φ:A→B an asymptotic star morphism and
g:B→C a nonunital complex star homomorphism. The bounded coefficient orbit of g∘Φ is
g∘orbitBCF Φ, and toHom(g∘Φ)=(AsymptoticAlgebra.map g)∘toHom Φ. Constant asymptotic families
correspond to constant quotient classes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BoundedContinuousFunction

noncomputable section

namespace AsymptoticMorphism

universe uA uB uC

attribute [local instance] _root_.AsymptoticAlgebra.cStarAlgebra

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- **Bounded orbit under fixed-homomorphism postcomposition.**

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), Φ:A→B an asymptotic star morphism and
g:B→C a nonunital complex star homomorphism. For a∈A, orbitBCF(postcomp Φ g)(a)=g∘orbitBCF Φ a
as bounded continuous functions T→C.
-/
theorem orbitBCF_postcomp
    (Φ : AsymptoticMorphism A B) (g : B →⋆ₙₐ[ℂ] C) (a : A) :
    orbitBCF (postcomp Φ g) a =
      BoundedContinuousFunction.compNonUnitalStarAlgHom g (orbitBCF Φ a) := by
  apply BoundedContinuousFunction.ext
  intro t
  rw [orbitBCF_apply, postcomp_apply,
    BoundedContinuousFunction.compNonUnitalStarAlgHom_apply, orbitBCF_apply]

/-- **Naturality of the quotient homomorphism under postcomposition.**

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), Φ:A→B an asymptotic star morphism and
g:B→C a nonunital complex star homomorphism. For X∞=C_b(T,X)/C₀(T,X), toHom Φ(a)=[t↦Φ_t(a)],
and toHom(postcomp Φ g)=(AsymptoticAlgebra.map g)∘toHom Φ.
-/
theorem toHom_postcomp
    (Φ : AsymptoticMorphism A B) (g : B →⋆ₙₐ[ℂ] C) :
    toHom (postcomp Φ g) =
      (_root_.AsymptoticAlgebra.map g).comp (toHom Φ) := by
  apply NonUnitalStarAlgHom.ext
  intro a
  rw [toHom_apply, NonUnitalStarAlgHom.comp_apply, toHom_apply,
    _root_.AsymptoticAlgebra.map_quotientMap, orbitBCF_postcomp]

/-- **Constant asymptotic families give constant quotient classes.**

Let A,B be nonunital complex C-star algebras, T=[1,∞), A∞=C_b(T,A)/C₀(T,A) and
B∞=C_b(T,B)/C₀(T,B), with quotient maps q_A,q_B. For a nonunital complex star homomorphism
f:A→B, its constant family ofHom f has toHom(ofHom f)=constantHom B∘f, where constantHom B
sends b to q_B(t↦b).
-/
theorem toHom_ofHom_constant (f : A →⋆ₙₐ[ℂ] B) :
    toHom (ofHom f) =
      (_root_.AsymptoticAlgebra.constantHom B).comp f := by
  apply NonUnitalStarAlgHom.ext
  intro a
  rw [toHom_apply, NonUnitalStarAlgHom.comp_apply,
    _root_.AsymptoticAlgebra.constantHom_apply]
  congr 1
  apply BoundedContinuousFunction.ext
  intro t
  rw [orbitBCF_apply, ofHom_apply, BoundedContinuousFunction.const_apply]


end AsymptoticMorphism
