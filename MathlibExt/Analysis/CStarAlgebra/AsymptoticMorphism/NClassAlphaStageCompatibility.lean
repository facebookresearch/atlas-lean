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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.NClassFunctoriality

/-!
# Naturality and stage compatibility of literal alpha-next classes

The unambiguous alpha-next map is natural under source precomposition and
coefficient postcomposition. Precomposing it by the constant-class inclusion
of the source recovers the ordinary one-step stage transition.

This is finite-stage class data only. It does not construct the disputed
printed target, a path/alpha comparison, a direct-limit map, a class product,
flattening, or an E-theory operation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace IteratedAsymptoticAlgebra

universe uA uA' uB uC

/-! ## Naturality in the source -/

/-- Applying literal alpha commutes with source precomposition. -/
theorem alphaNextRepresentative_precomp (n : ℕ)
    {A : Type uA} {A' : Type uA'} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) (phi : HomN n A B) :
    alphaNextRepresentative n (precompRepresentative n u phi) =
      precompRepresentative (n + 1) (AsymptoticAlgebra.map u)
        (alphaNextRepresentative n phi) := by
  have hpre :
      precompRepresentative n u phi = phi.comp u := by
    apply NonUnitalStarAlgHom.ext
    intro a
    rw [precompRepresentative_apply,
      NonUnitalStarAlgHom.comp_apply]
  apply NonUnitalStarAlgHom.ext
  intro x
  rw [hpre, precompRepresentative_apply,
    alphaNextRepresentative_eq, alphaRepresentative_eq,
    alphaNextRepresentative_eq, alphaRepresentative_eq]
  exact DFunLike.congr_fun (AsymptoticAlgebra.map_comp u phi) x

/-- Source naturality descends to literal finite-stage homotopy classes. -/
theorem alphaNextClass_precomp (n : ℕ)
    {A : Type uA} {A' : Type uA'} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
    [NonUnitalCStarAlgebra B]
    (u : A' →⋆ₙₐ[ℂ] A) (q : NClasses n A B) :
    alphaNextClass n A' B (precompClass n u q) =
      precompClass (n + 1) (B := B) (AsymptoticAlgebra.map u)
        (alphaNextClass n A B q) := by
  refine Quotient.inductionOn q ?_
  intro phi
  change alphaNextClass n A' B (precompClass n u (classOf n phi)) =
    precompClass (n + 1) (B := B) (AsymptoticAlgebra.map u)
      (alphaNextClass n A B (classOf n phi))
  rw [precompClass_classOf, alphaNextClass_classOf,
    alphaNextClass_classOf, precompClass_classOf,
    alphaNextRepresentative_precomp]

/-! ## Naturality in the coefficient -/

/-- Applying literal alpha commutes with coefficient postcomposition. -/
theorem alphaNextRepresentative_postcomp (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) (phi : HomN n A B) :
    alphaNextRepresentative n (postcompRepresentative n g phi) =
      postcompRepresentative (n + 1) g
        (alphaNextRepresentative n phi) := by
  have hpost :
      postcompRepresentative n g phi = (map n g).comp phi := by
    apply NonUnitalStarAlgHom.ext
    intro a
    rw [postcompRepresentative_apply,
      NonUnitalStarAlgHom.comp_apply]
  apply NonUnitalStarAlgHom.ext
  intro x
  rw [hpost, postcompRepresentative_apply,
    alphaNextRepresentative_eq, alphaRepresentative_eq,
    alphaNextRepresentative_eq, alphaRepresentative_eq,
    map_succ]
  exact DFunLike.congr_fun
    (AsymptoticAlgebra.map_comp phi (map n g)) x

/-- Coefficient naturality descends to literal finite-stage homotopy classes. -/
theorem alphaNextClass_postcomp (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (g : B →⋆ₙₐ[ℂ] C) (q : NClasses n A B) :
    alphaNextClass n A C (postcompClass n g q) =
      postcompClass (n + 1) (A := AsymptoticAlgebra A) g
        (alphaNextClass n A B q) := by
  refine Quotient.inductionOn q ?_
  intro phi
  change alphaNextClass n A C (postcompClass n g (classOf n phi)) =
    postcompClass (n + 1) (A := AsymptoticAlgebra A) g
      (alphaNextClass n A B (classOf n phi))
  rw [postcompClass_classOf, alphaNextClass_classOf,
    alphaNextClass_classOf, postcompClass_classOf,
    alphaNextRepresentative_postcomp]

/-! ## Compatibility with the ordinary stage transition -/

/-- Restricting literal alpha along the source constant-class inclusion is the
ordinary one-step representative transition. -/
theorem alphaNextRepresentative_precomp_constantHom (n : ℕ)
    {A : Type uA} {B : Type uB}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : HomN n A B) :
    precompRepresentative (n + 1) (AsymptoticAlgebra.constantHom A)
        (alphaNextRepresentative n phi) =
      stageTransitionRepresentative n phi := by
  apply NonUnitalStarAlgHom.ext
  intro a
  rw [precompRepresentative_apply,
    alphaNextRepresentative_eq, alphaRepresentative_eq,
    stageTransitionRepresentative_apply,
    stageHom_eq_constantHom]
  exact DFunLike.congr_fun
    (AsymptoticAlgebra.map_comp_constantHom phi) a

/-- The alpha-next class map restricts along source constants to the ordinary
one-step stage transition. This is the true finite-stage compatibility
triangle; no alpha/path comparison is assumed. -/
theorem precompClass_comp_alphaNextClass (n : ℕ)
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Function.comp
        (precompClass (n + 1) (B := B)
          (AsymptoticAlgebra.constantHom A))
        (alphaNextClass n A B) =
      stageTransition n A B := by
  funext q
  change
    precompClass (n + 1) (B := B)
        (AsymptoticAlgebra.constantHom A)
        (alphaNextClass n A B q) =
      stageTransition n A B q
  refine Quotient.inductionOn q ?_
  intro phi
  change precompClass (n + 1) (B := B) (AsymptoticAlgebra.constantHom A)
    (alphaNextClass n A B (classOf n phi)) =
    stageTransition n A B (classOf n phi)
  rw [alphaNextClass_classOf, precompClass_classOf,
    stageTransition_classOf,
    alphaNextRepresentative_precomp_constantHom]

#print axioms alphaNextRepresentative_precomp
#print axioms alphaNextClass_precomp
#print axioms alphaNextRepresentative_postcomp
#print axioms alphaNextClass_postcomp
#print axioms alphaNextRepresentative_precomp_constantHom
#print axioms precompClass_comp_alphaNextClass

end IteratedAsymptoticAlgebra
