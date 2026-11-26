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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositive
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Homotopy
public import MathlibExt.Analysis.CStarAlgebra.CompletelyPositiveMap.Basic

/-!
# Postcomposition of CP-contractive asymptotic morphisms

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. If C is a nonunital complex C-star algebra and g:B→C is a
nonunital complex star homomorphism, g∘φ has completely positive contraction slices with
values g(φ_t(a)).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace AsymptoticMorphism
namespace CompletelyPositiveContraction

universe uA uB uC

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- **CP-contractive family postcomposed by a star homomorphism.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For a nonunital complex C-star algebra C and a nonunital
complex star homomorphism g:B→C, CompletelyPositiveContraction.postcomp φ g is the family
(g∘φ)_t(a)=g(φ_t(a)).
-/
noncomputable def postcomp (phi : CompletelyPositiveContraction A B)
    (g : B →⋆ₙₐ[ℂ] C) : CompletelyPositiveContraction A C where
  toAsymptoticMorphism :=
    AsymptoticMorphism.postcomp phi.toAsymptoticMorphism g
  completelyPositiveContraction := by
    let _ : PartialOrder A := CStarAlgebra.spectralOrder A
    let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    let _ : PartialOrder B := CStarAlgebra.spectralOrder B
    let _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    let _ : PartialOrder C := CStarAlgebra.spectralOrder C
    let _ : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
    have hphi := phi.completelyPositiveContraction
    dsimp only [IsCompletelyPositiveContraction] at hphi ⊢
    intro t
    obtain ⟨s, hsNorm, hsValue⟩ := hphi t
    let gCP : B →CP C :=
      CompletelyPositiveMapClass.toCompletelyPositiveLinearMap g
    let gs : A →CP C := CompletelyPositiveMap.comp gCP s
    refine ⟨gs, ?_, ?_⟩
    · intro a
      calc
        ‖gs a‖ = ‖g (s a)‖ := rfl
        _ ≤ ‖s a‖ := NonUnitalStarAlgHom.norm_apply_le g (s a)
        _ ≤ ‖a‖ := hsNorm a
    · intro a
      rw [CompletelyPositiveMap.comp_apply, hsValue a,
        AsymptoticMorphism.postcomp_apply]
      rfl

/-- **Underlying asymptotic family of CP postcomposition.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For a nonunital complex star homomorphism g:B→C into a
nonunital complex C-star algebra, the underlying asymptotic morphism of
CompletelyPositiveContraction.postcomp φ g equals AsymptoticMorphism.postcomp
φ.toAsymptoticMorphism g.
-/
@[simp]
theorem postcomp_toAsymptoticMorphism
    (phi : CompletelyPositiveContraction A B) (g : B →⋆ₙₐ[ℂ] C) :
    (postcomp phi g).toAsymptoticMorphism =
      AsymptoticMorphism.postcomp phi.toAsymptoticMorphism g :=
  rfl

/-- **Value of CP-contractive postcomposition.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. For a completely positive family, each
slice φ_t is a completely positive complex-linear map for the canonical C-star positive cones,
including all matrix levels. For a completely positive contraction family, additionally
‖φ_t(a)‖≤‖a‖ for all a∈A and t∈T. For a nonunital complex star homomorphism g:B→C into a
nonunital complex C-star algebra, t≥1 and a∈A, (CompletelyPositiveContraction.postcomp φ
g)_t(a)=g(φ_t(a)).
-/
theorem postcomp_apply
    (phi : CompletelyPositiveContraction A B) (g : B →⋆ₙₐ[ℂ] C)
    (t : AsymptoticTime) (a : A) :
    (postcomp phi g).toAsymptoticMorphism t a =
      g (phi.toAsymptoticMorphism t a) :=
  rfl

end CompletelyPositiveContraction
end AsymptoticMorphism
