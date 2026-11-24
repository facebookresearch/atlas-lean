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
# Naturality of the strict asymptotic-algebra correspondence

This upper module is the first nontrivial consumer of the coefficient map.
It stays above both the strict correspondence and fixed-hom functoriality, so
neither lower provider imports a later consumer.
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

/-- Postcomposition of a raw family gives literal coefficient
postcomposition of every bounded time orbit. -/
theorem orbitBCF_postcomp
    (Φ : AsymptoticMorphism A B) (g : B →⋆ₙₐ[ℂ] C) (a : A) :
    orbitBCF (postcomp Φ g) a =
      BoundedContinuousFunction.compNonUnitalStarAlgHom g (orbitBCF Φ a) := by
  apply BoundedContinuousFunction.ext
  intro t
  rw [orbitBCF_apply, postcomp_apply,
    BoundedContinuousFunction.compNonUnitalStarAlgHom_apply, orbitBCF_apply]

/-- The actual strict correspondence is covariantly natural under a fixed
coefficient star homomorphism. -/
theorem toHom_postcomp
    (Φ : AsymptoticMorphism A B) (g : B →⋆ₙₐ[ℂ] C) :
    toHom (postcomp Φ g) =
      (_root_.AsymptoticAlgebra.map g).comp (toHom Φ) := by
  apply NonUnitalStarAlgHom.ext
  intro a
  rw [toHom_apply, NonUnitalStarAlgHom.comp_apply, toHom_apply,
    _root_.AsymptoticAlgebra.map_quotientMap, orbitBCF_postcomp]

/-- Ordinary fixed homomorphisms correspond exactly to the constant-class
inclusion into the actual asymptotic quotient. -/
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

#print axioms orbitBCF_postcomp
#print axioms toHom_postcomp
#print axioms toHom_ofHom_constant

end AsymptoticMorphism
