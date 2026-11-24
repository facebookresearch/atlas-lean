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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositiveHomotopyEquivalence
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Functoriality

/-!
# Fixed-star-hom functoriality for CPC asymptotic families

Only one side is an actual star homomorphism. No composition of two arbitrary
asymptotic families is defined.
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

/-- Precompose a CPC asymptotic family by an actual nonunital star hom. -/
noncomputable def precomp (phi : CompletelyPositiveContraction A B)
    (f : C →⋆ₙₐ[ℂ] A) : CompletelyPositiveContraction C B where
  toAsymptoticMorphism :=
    AsymptoticMorphism.precomp phi.toAsymptoticMorphism f
  completelyPositiveContraction := by
    let _ : PartialOrder C := CStarAlgebra.spectralOrder C
    let _ : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
    let _ : PartialOrder A := CStarAlgebra.spectralOrder A
    let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    let _ : PartialOrder B := CStarAlgebra.spectralOrder B
    let _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    have hphi := phi.completelyPositiveContraction
    dsimp only [IsCompletelyPositiveContraction] at hphi ⊢
    intro t
    obtain ⟨s, hsNorm, hsValue⟩ := hphi t
    let fCP : C →CP A :=
      CompletelyPositiveMapClass.toCompletelyPositiveLinearMap f
    let sf : C →CP B := CompletelyPositiveMap.comp s fCP
    refine ⟨sf, ?_, ?_⟩
    · intro c
      calc
        ‖sf c‖ = ‖s (f c)‖ := rfl
        _ ≤ ‖f c‖ := hsNorm (f c)
        _ ≤ ‖c‖ := NonUnitalStarAlgHom.norm_apply_le f c
    · intro c
      change s (f c) = phi.toAsymptoticMorphism t (f c)
      exact hsValue (f c)

/-- Forgetting CPC evidence gives exactly ordinary fixed-hom precomposition. -/
@[simp]
theorem precomp_toAsymptoticMorphism
    (phi : CompletelyPositiveContraction A B) (f : C →⋆ₙₐ[ℂ] A) :
    (precomp phi f).toAsymptoticMorphism =
      AsymptoticMorphism.precomp phi.toAsymptoticMorphism f :=
  rfl

/-- CPC fixed-hom precomposition has the literal value. -/
theorem precomp_apply
    (phi : CompletelyPositiveContraction A B) (f : C →⋆ₙₐ[ℂ] A)
    (t : AsymptoticTime) (c : C) :
    (precomp phi f).toAsymptoticMorphism t c =
      phi.toAsymptoticMorphism t (f c) :=
  rfl

namespace Homotopy

variable {phi psi : CompletelyPositiveContraction A B}

/-- Precompose a whole CPC homotopy by a fixed source star hom. -/
noncomputable def precomp (H : Homotopy phi psi)
    (f : C →⋆ₙₐ[ℂ] A) : Homotopy (phi.precomp f) (psi.precomp f) where
  family := H.family.precomp f
  start := by
    intro t c
    rw [CompletelyPositiveContraction.precomp_apply,
      CompletelyPositiveContraction.precomp_apply]
    exact H.start t (f c)
  finish := by
    intro t c
    rw [CompletelyPositiveContraction.precomp_apply,
      CompletelyPositiveContraction.precomp_apply]
    exact H.finish t (f c)

/-- Postcompose a whole CPC homotopy by a fixed target star hom. -/
noncomputable def postcomp (H : Homotopy phi psi)
    (g : B →⋆ₙₐ[ℂ] C) : Homotopy (phi.postcomp g) (psi.postcomp g) where
  family := H.family.postcomp
    (ContinuousMap.compNonUnitalStarAlgHom unitInterval g)
  start := by
    intro t a
    rw [CompletelyPositiveContraction.postcomp_apply,
      ContinuousMap.compNonUnitalStarAlgHom_apply,
      CompletelyPositiveContraction.postcomp_apply]
    exact congrArg g (H.start t a)
  finish := by
    intro t a
    rw [CompletelyPositiveContraction.postcomp_apply,
      ContinuousMap.compNonUnitalStarAlgHom_apply,
      CompletelyPositiveContraction.postcomp_apply]
    exact congrArg g (H.finish t a)

/-- CPC homotopy precomposition forgets to ordinary homotopy precomposition. -/
@[simp]
theorem precomp_toAsymptoticHomotopy
    (H : Homotopy phi psi) (f : C →⋆ₙₐ[ℂ] A) :
    (precomp H f).toAsymptoticHomotopy =
      _root_.AsymptoticMorphism.Homotopy.precomp
        H.toAsymptoticHomotopy f := by
  apply _root_.AsymptoticMorphism.Homotopy.ext
  rfl

/-- CPC homotopy postcomposition forgets to ordinary homotopy
postcomposition. -/
@[simp]
theorem postcomp_toAsymptoticHomotopy
    (H : Homotopy phi psi) (g : B →⋆ₙₐ[ℂ] C) :
    (postcomp H g).toAsymptoticHomotopy =
      _root_.AsymptoticMorphism.Homotopy.postcomp
        H.toAsymptoticHomotopy g := by
  apply _root_.AsymptoticMorphism.Homotopy.ext
  rfl

end Homotopy

/-- Fixed source-star-hom precomposition preserves literal CPC homotopy. -/
theorem homotopic_precomp {phi psi : CompletelyPositiveContraction A B}
    (h : Homotopic phi psi) (f : C →⋆ₙₐ[ℂ] A) :
    Homotopic (phi.precomp f) (psi.precomp f) := by
  rcases h with ⟨H⟩
  exact ⟨H.precomp f⟩

/-- Fixed target-star-hom postcomposition preserves literal CPC homotopy. -/
theorem homotopic_postcomp {phi psi : CompletelyPositiveContraction A B}
    (h : Homotopic phi psi) (g : B →⋆ₙₐ[ℂ] C) :
    Homotopic (phi.postcomp g) (psi.postcomp g) := by
  rcases h with ⟨H⟩
  exact ⟨H.postcomp g⟩

/-- Contravariant fixed-star-hom action on CPC homotopy classes. -/
def precompClass (f : C →⋆ₙₐ[ℂ] A) :
    HomotopyClasses A B → HomotopyClasses C B :=
  Quotient.map (sa := homotopySetoid A B) (sb := homotopySetoid C B)
    (fun phi => phi.precomp f) (by
      intro phi psi h
      exact homotopic_precomp h f)

/-- Covariant fixed-star-hom action on CPC homotopy classes. -/
def postcompClass (g : B →⋆ₙₐ[ℂ] C) :
    HomotopyClasses A B → HomotopyClasses A C :=
  Quotient.map (sa := homotopySetoid A B) (sb := homotopySetoid A C)
    (fun phi => phi.postcomp g) (by
      intro phi psi h
      exact homotopic_postcomp h g)

/-- Fixed-hom precomposition computes on CPC class constructors. -/
@[simp]
theorem precompClass_mk
    (f : C →⋆ₙₐ[ℂ] A) (phi : CompletelyPositiveContraction A B) :
    precompClass f (mkClass phi) = mkClass (phi.precomp f) :=
  rfl

/-- Fixed-hom postcomposition computes on CPC class constructors. -/
@[simp]
theorem postcompClass_mk
    (g : B →⋆ₙₐ[ℂ] C) (phi : CompletelyPositiveContraction A B) :
    postcompClass g (mkClass phi) = mkClass (phi.postcomp g) :=
  rfl

end CompletelyPositiveContraction
end AsymptoticMorphism
