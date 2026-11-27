/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.TracedTransport
import Mathlib.Algebra.Category.FGModuleCat.Basic

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]

-- No rigidity or preexisting trace on the source is assumed.
example (S : SymmetricTrace D) (F : C ⥤ D) [F.Braided] [F.Full] [F.Faithful] :
    SymmetricTrace C := S.ofFullyFaithful F

example (S : SymmetricTrace D) (F : C ⥤ D) [F.Braided] [F.Full] [F.Faithful] :
    (S.ofFullyFaithful F).Preserves S F := S.preserves_ofFullyFaithful F

example (S : SymmetricTrace D) (F : C ⥤ D) [F.Braided] [F.Full] [F.Faithful]
    (T : SymmetricTrace C) (h : T.Preserves S F) : T = S.ofFullyFaithful F :=
  S.ofFullyFaithful_unique F T h

example (T : SymmetricTrace C) : T.ofFullyFaithful (𝟭 C) = T :=
  T.ofFullyFaithful_id

example (S : SymmetricTrace E) (F : C ⥤ D) (G : D ⥤ E)
    [F.Braided] [G.Braided] [F.Full] [F.Faithful] [G.Full] [G.Faithful] :
    (S.ofFullyFaithful G).ofFullyFaithful F = S.ofFullyFaithful (F ⋙ G) :=
  S.ofFullyFaithful_comp F G

-- Transport is compatible with the previously constructed canonical trace.
example [RightRigidCategory C] [RightRigidCategory D]
    (F : C ⥤ D) [F.Braided] [F.Full] [F.Faithful] :
    (symmetricTraceOfRigid D).ofFullyFaithful F = symmetricTraceOfRigid C :=
  SymmetricTrace.ofFullyFaithful_rigid F

-- Changing a feedback object does not require rigidity, only the trace axioms.
example (T : SymmetricTrace C) {X Y U V : C} (i : U ≅ V)
    (f : X ⊗ V ⟶ Y ⊗ V) :
    T.trace (X ◁ i.hom ≫ f ≫ Y ◁ i.inv) = T.trace f := T.trace_conjugate i f

-- A proper full monoidal subcategory: rational vector spaces isomorphic to the unit.
private def unitLines : ObjectProperty (FGModuleCat ℚ) :=
  fun X => Nonempty (X ≅ 𝟙_ (FGModuleCat ℚ))

private instance : unitLines.IsMonoidal where
  prop_unit := ⟨Iso.refl _⟩
  prop_tensor X Y hX hY := by
    obtain ⟨i⟩ := hX
    obtain ⟨j⟩ := hY
    exact ⟨tensorIso i j ≪≫ λ_ _⟩

-- The inclusion is fully faithful, but its image excludes two-dimensional spaces.
example : ¬ unitLines (FGModuleCat.of ℚ (Fin 2 → ℚ)) := by
  rintro ⟨i⟩
  have h := (FGModuleCat.isoToLinearEquiv i).finrank_eq
  change Module.finrank ℚ (Fin 2 → ℚ) = Module.finrank ℚ ℚ at h
  norm_num at h

-- No right-rigid structure on the subcategory is supplied to this construction.
private noncomputable def lineTrace : SymmetricTrace unitLines.FullSubcategory :=
  (symmetricTraceOfRigid (FGModuleCat ℚ)).ofFullyFaithful unitLines.ι

-- Pullback computes the zero map in the concrete subcategory.
example (X Y U : unitLines.FullSubcategory) :
    lineTrace.trace (0 : X ⊗ U ⟶ Y ⊗ U) = 0 := by
  unfold lineTrace
  apply unitLines.ι.map_injective
  rw [(symmetricTraceOfRigid (FGModuleCat ℚ)).preserves_ofFullyFaithful unitLines.ι]
  simp [symmetricTraceOfRigid, SymmetricTrace.traceOfPairing]

-- The constructed trace obeys yanking on every object of this proper subcategory.
example (X : unitLines.FullSubcategory) : lineTrace.trace (β_ X X).hom = 𝟙 X :=
  lineTrace.yanking X

-- Tracing a unit feedback loop recovers any scalar morphism, not only zero.
example {X Y : unitLines.FullSubcategory} (f : X ⟶ Y) :
    lineTrace.trace ((ρ_ X).hom ≫ f ≫ (ρ_ Y).inv) = f := by
  rw [lineTrace.vanishing_unit]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

#print axioms CategoryTheory.SymmetricTrace.ofFullyFaithful
#print axioms CategoryTheory.SymmetricTrace.ofFullyFaithful_unique
