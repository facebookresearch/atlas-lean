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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.IteratedAlgebra

public import Mathlib.CategoryTheory.EqToHom

/-!
# Products of finite-stage representatives

Let A,B,C be nonunital complex C-star algebras in independent universes and n,m∈ℕ. For a
nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star
norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For representatives φ:A→αⁿB and ψ:B→αᵐC, let
θ_(n,m):αⁿ(αᵐC)→αⁿ⁺ᵐC be the canonical finite-iteration identification. The representative
product is θ_(n,m)∘αⁿ(ψ)∘φ:A→αⁿ⁺ᵐC. At n=0 it is ordinary composition with the canonical
target identification, and at m=0 it is αⁿ(ψ)∘φ.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped CStarAlgebra

noncomputable section

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace IteratedAsymptoticAlgebra

universe uA uB uC

/-- **Composition of representatives at summed stage.**

Let A,B,C be nonunital complex C-star algebras in independent universes and n,m∈ℕ. For a
nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star
norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For representatives φ:A→αⁿB and ψ:B→αᵐC, let
θ_(n,m):αⁿ(αᵐC)→αⁿ⁺ᵐC be the canonical finite-iteration identification. The homomorphism
productRepresentative n m φ ψ is θ_(n,m)∘(IteratedAsymptoticAlgebra.map n ψ)∘φ∈HomN(n+m) A C.
-/
def productRepresentative (n m : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (phi : HomN n A B) (psi : HomN m B C) : HomN (n + m) A C :=
  (iteratedAddHom n m C).comp ((map n psi).comp phi)

@[simp]
theorem productRepresentative_apply (n m : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (phi : HomN n A B) (psi : HomN m B C) (a : A) :
    productRepresentative n m phi psi a =
      iteratedAddHom n m C (map n psi (phi a)) :=
  rfl

/-- **Stage-zero iterate of a representative.**

Let B,C be nonunital complex C-star algebras and m∈ℕ. For a nonunital complex C-star algebra
X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star norm, and define α⁰X=X,
αⁿ⁺¹X=α(αⁿX). For ψ:B→αᵐC, map 0 ψ is ψ after the canonical identification α⁰(αᵐC)=αᵐC.
-/
private theorem map_zero_stage_eq_eqToHom_comp
    (m : ℕ)
    {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    (psi : HomN m B C) :
    map 0 psi =
      (eqToHom
        (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject_zero
          (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject m
            (NonUnitalCStarAlgCat.of C))).symm).comp psi := by
  rw [map_zero_stage]
  rfl

/-- **Representative product with stage zero on the left.**

Let A,B,C be nonunital complex C-star algebras in independent universes and n,m∈ℕ. For a
nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star
norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For representatives φ:A→αⁿB and ψ:B→αᵐC, let
θ_(n,m):αⁿ(αᵐC)→αⁿ⁺ᵐC be the canonical finite-iteration identification. If n=0,
productRepresentative 0 m φ ψ is ψ∘φ followed by the canonical identification of target stage
m with 0+m.
-/
theorem productRepresentative_zero_left (m : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (phi : HomN 0 A B) (psi : HomN m B C) :
    productRepresentative 0 m phi psi =
      (eqToHom
        (congrArg
          (fun k => NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject k
            (NonUnitalCStarAlgCat.of C))
          (Nat.zero_add m)).symm).comp (psi.comp phi) := by
  unfold productRepresentative
  rw [map_zero_stage_eq_eqToHom_comp]
  calc
    (iteratedAddHom 0 m C).comp
        (((eqToHom
          (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject_zero
            (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject m
              (NonUnitalCStarAlgCat.of C))).symm).comp psi).comp phi) =
      ((iteratedAddHom 0 m C).comp
        (eqToHom
          (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject_zero
            (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject m
              (NonUnitalCStarAlgCat.of C))).symm)).comp
        (psi.comp phi) := by
          apply NonUnitalStarAlgHom.ext
          intro a
          rfl
    _ = (eqToHom
          (congrArg
            (fun k => NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject k
              (NonUnitalCStarAlgCat.of C))
            (Nat.zero_add m)).symm).comp (psi.comp phi) := by
      exact congrArg (fun F => F.comp (psi.comp phi))
        (iteratedAddHom_zero_left m C)

/-- **Representative product with stage zero on the right.**

Let A,B,C be nonunital complex C-star algebras in independent universes and n,m∈ℕ. For a
nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient C-star
norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For representatives φ:A→αⁿB and ψ:B→αᵐC, let
θ_(n,m):αⁿ(αᵐC)→αⁿ⁺ᵐC be the canonical finite-iteration identification. If m=0,
productRepresentative n 0 φ ψ=(IteratedAsymptoticAlgebra.map n ψ)∘φ, with ψ:B→C.
-/
theorem productRepresentative_zero_right (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (phi : HomN n A B) (psi : HomN 0 B C) :
    productRepresentative n 0 phi psi = (map n psi).comp phi := by
  unfold productRepresentative
  rw [iteratedAddHom_zero_right]
  apply NonUnitalStarAlgHom.ext
  intro a
  rfl


end IteratedAsymptoticAlgebra
