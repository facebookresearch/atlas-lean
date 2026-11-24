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
# Postcomposition of CPC asymptotic families

A genuine nonunital star homomorphism is completely positive and norm
contractive, so postcomposition preserves every finite-time CPC witness.
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

/-- Postcompose a CPC asymptotic family by an actual nonunital star hom. -/
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

/-- Forgetting CPC evidence gives exactly ordinary postcomposition. -/
@[simp]
theorem postcomp_toAsymptoticMorphism
    (phi : CompletelyPositiveContraction A B) (g : B →⋆ₙₐ[ℂ] C) :
    (postcomp phi g).toAsymptoticMorphism =
      AsymptoticMorphism.postcomp phi.toAsymptoticMorphism g :=
  rfl

/-- CPC postcomposition has the literal star-hom value. -/
theorem postcomp_apply
    (phi : CompletelyPositiveContraction A B) (g : B →⋆ₙₐ[ℂ] C)
    (t : AsymptoticTime) (a : A) :
    (postcomp phi g).toAsymptoticMorphism t a =
      g (phi.toAsymptoticMorphism t a) :=
  rfl

end CompletelyPositiveContraction
end AsymptoticMorphism
