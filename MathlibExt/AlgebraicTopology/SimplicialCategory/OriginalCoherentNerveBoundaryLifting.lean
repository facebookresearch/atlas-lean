/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentOneBoundaryLift
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerGeneratingCofibrations

/-!
# Unrestricted original coherent-nerve trivial fibrations

Literal original object surjectivity and boundary lifting on every
complete original Hom give full boundary and mono lifting for the
SAME coherent nerve. No locally Kan target is required.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNerveBoundaryLifting
open SimplicialEnrichment

variable {C D : Carrier.{u}} (F : C ⟶ D)

/-- The original object map gives surjectivity on the SAME individual original coherent-nerve vertices. -/
theorem vertices_surjective (hObj : Function.Surjective F.obj) :
    Function.Surjective ((coherentNerveFunctor.map F).app (op ⦋0⦌)) := by
  intro σ
  obtain ⟨x,hx⟩ := hObj (verticesEquiv D σ)
  refine ⟨(verticesEquiv C).symm x, ?_⟩
  apply (verticesEquiv D).injective
  exact (verticesEquiv_map C D F _).trans
    ((congrArg F.obj ((verticesEquiv C).apply_symm_apply x)).trans hx)

/-- Literal original object surjectivity constructs a genuine lift of the original zero boundary. -/
theorem hasLiftingProperty_zero (hObj : Function.Surjective F.obj) :
    HasLiftingProperty (SSet.boundary.{u} 0).ι (coherentNerveFunctor.map F) where
  sq_hasLift {top bottom} sq := by
    obtain ⟨x,hx⟩ := vertices_surjective F hObj (SSet.yonedaEquiv bottom)
    let hinit : IsInitial (∂Δ[0] : SSet.{u}) :=
      (SSet.Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).ofIso
        (SSet.Subcomplex.eqToIso SSet.boundary_zero).symm
    refine CommSq.HasLift.mk' ⟨SSet.yonedaEquiv.symm x, hinit.hom_ext _ _, ?_⟩
    exact (SSet.yonedaEquiv_symm_comp x (coherentNerveFunctor.map F)).trans
      ((congrArg SSet.yonedaEquiv.symm hx).trans (Equiv.symm_apply_apply _ _))

/-- Genuine original Hom boundary lifting constructs full original coherent-nerve boundary lifts in every positive
degree. -/
theorem hasLiftingProperty_positive
    (hHom : ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y)) (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{u} (n+1)).ι (coherentNerveFunctor.map F) := by
  refine ⟨fun {f g} sq => ?_⟩
  let σ : coherentSimplex.{u} ⦋n+1⦌ ⟶ D := SSet.yonedaEquiv g
  have hσ : SSet.yonedaEquiv.symm σ = g := Equiv.symm_apply_apply _ _
  let sq' : CommSq f (SSet.boundary.{u} (n+1)).ι
      (coherentNerveFunctor.map F) (SSet.yonedaEquiv.symm σ) :=
    ⟨sq.w.trans (congrArg (fun q => (SSet.boundary.{u} (n+1)).ι ≫ q) hσ.symm)⟩
  have hLift : ∃ τ : coherentSimplex.{u} ⦋n+1⦌ ⟶ C,
      (SSet.boundary.{u} (n+1)).ι ≫ SSet.yonedaEquiv.symm τ = f ∧ τ ≫ F = σ := by
    cases n with
    | zero => exact RelativeCoherentOneBoundary.exists_enriched_boundary_lift F f σ sq' hHom
    | succ n => exact RelativeFullBoundaryLift.exists_enriched_boundary_lift F f σ sq' hHom
  obtain ⟨τ,hBoundary,hImage⟩ := hLift
  refine CommSq.HasLift.mk' ⟨SSet.yonedaEquiv.symm τ, hBoundary, ?_⟩
  exact (SSet.yonedaEquiv_symm_comp τ (coherentNerveFunctor.map F)).trans
    ((congrArg SSet.yonedaEquiv.symm hImage).trans hσ)

/-- EVERY original simplicial boundary lifts against the SAME original nerve without a local Kan premise. -/
theorem hasLiftingProperty_boundary
    (hObj : Function.Surjective F.obj)
    (hHom : ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y)) (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{u} n).ι (coherentNerveFunctor.map F) := by
  cases n with
  | zero => exact hasLiftingProperty_zero F hObj
  | succ n => exact hasLiftingProperty_positive F hHom n

/-- The SAME unrestricted original coherent nerve is in the actual full original simplicial boundary right class. -/
theorem boundaryRLP
    (hObj : Function.Surjective F.obj)
    (hHom : ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y)) :
    SSet.modelCategoryQuillen.I.rlp (coherentNerveFunctor.map F) := by
  intro A B i hi
  obtain ⟨n⟩ := hi
  exact hasLiftingProperty_boundary F hObj hHom n

/-- EVERY full original simplicial mono lifts against that SAME unrestricted original nerve map. -/
theorem hasLiftingProperty_mono
    (hObj : Function.Surjective F.obj)
    (hHom : ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y))
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i (coherentNerveFunctor.map F) := by
  have h := boundaryRLP F hObj hHom
  rw [← SSet.rlp_monomorphisms] at h
  exact h i (show Mono i from inferInstance)

/-- The original varying-object Bergner boundary right class gives unrestricted full coherent-nerve boundary lifting. -/
theorem bergnerRight_boundaryRLP (hF : Bergner.generatingCofibrations.rlp F) :
    SSet.modelCategoryQuillen.I.rlp (coherentNerveFunctor.map F) := by
  have h := (Bergner.generatingCofibrations_rlp_iff F).mp hF
  exact boundaryRLP F h.1 h.2

/-- The exact original varying-object generator right class gives ALL mono lifts in the SAME nerve. -/
theorem bergnerRight_monoLifting (hF : Bergner.generatingCofibrations.rlp F)
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i (coherentNerveFunctor.map F) := by
  have h := (Bergner.generatingCofibrations_rlp_iff F).mp hF
  exact hasLiftingProperty_mono F h.1 h.2 i

end CategoryTheory.CoherentRealization.OriginalNerveBoundaryLifting
