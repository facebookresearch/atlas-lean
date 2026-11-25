/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.InnerIsoFibrations

/-! # Inner fibrations inducing isofibrations: API tests

These tests exercise the exact raw definition of `SSet.innerIsoFibrations`,
its membership criterion, its identity/composition/isomorphism/retract
instances, and its terminal-map characterization of quasicategories.
-/

@[expose] public section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace InnerIsoFibrationsTest

section DefinitionPin

example : SSet.innerIsoFibrations.{u} =
    SSet.innerFibrations.{u} ⊓
      CategoryTheory.isofibrations.{u}.inverseImage SSet.hoFunctor.{u} :=
  rfl

example : MorphismProperty SSet.{u} := SSet.innerIsoFibrations.{u}

end DefinitionPin

section Instances

example : SSet.innerIsoFibrations.{u}.ContainsIdentities := inferInstance
example : SSet.innerIsoFibrations.{u}.IsStableUnderComposition := inferInstance
example : SSet.innerIsoFibrations.{u}.IsMultiplicative := inferInstance
example : SSet.innerIsoFibrations.{u}.RespectsIso := inferInstance
example : SSet.innerIsoFibrations.{u}.IsStableUnderRetracts := inferInstance

-- The instances also exist at universe `0`.
example : SSet.innerIsoFibrations.{0}.IsMultiplicative := inferInstance
example : SSet.innerIsoFibrations.{0}.IsStableUnderRetracts := inferInstance

end Instances

section MembershipCriterion

variable {X Y : SSet.{u}} (f : X ⟶ Y)

example : SSet.innerIsoFibrations f ↔
    SSet.innerFibrations f ∧
      (SSet.hoFunctor.map f).toFunctor.IsIsofibration :=
  SSet.innerIsoFibrations.mem_iff f

example (h : SSet.innerIsoFibrations f) : SSet.innerFibrations f :=
  (SSet.innerIsoFibrations.mem_iff f).1 h |>.1

example (h : SSet.innerIsoFibrations f) :
    (SSet.hoFunctor.map f).toFunctor.IsIsofibration :=
  (SSet.innerIsoFibrations.mem_iff f).1 h |>.2

example (h₁ : SSet.innerFibrations f)
    (h₂ : (SSet.hoFunctor.map f).toFunctor.IsIsofibration) :
    SSet.innerIsoFibrations f :=
  (SSet.innerIsoFibrations.mem_iff f).2 ⟨h₁, h₂⟩

end MembershipCriterion

section IdentitiesAndIsomorphisms

variable (X Y : SSet.{u})

example : SSet.innerIsoFibrations (𝟙 X) :=
  MorphismProperty.id_mem _ X

example : SSet.innerIsoFibrations (𝟙 (Δ[0] : SSet.{u})) :=
  MorphismProperty.id_mem _ _

example : SSet.innerIsoFibrations (𝟙 (Δ[1] : SSet.{u})) :=
  MorphismProperty.id_mem _ _

example (e : X ≅ Y) : SSet.innerIsoFibrations e.hom :=
  MorphismProperty.of_isIso _ e.hom

example (f : X ⟶ Y) [IsIso f] : SSet.innerIsoFibrations f :=
  MorphismProperty.of_isIso _ f

end IdentitiesAndIsomorphisms

section CompositionAndRetracts

variable {X Y Z A B : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {g' : A ⟶ B}

example (hf : SSet.innerIsoFibrations f) (hg : SSet.innerIsoFibrations g) :
    SSet.innerIsoFibrations (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

example : SSet.innerIsoFibrations
    ((𝟙 (Δ[1] : SSet.{u})) ≫ (𝟙 (Δ[1] : SSet.{u}))) :=
  MorphismProperty.comp_mem _ _ _
    (MorphismProperty.id_mem _ _) (MorphismProperty.id_mem _ _)

example (h : RetractArrow f g') (hg : SSet.innerIsoFibrations g') :
    SSet.innerIsoFibrations f :=
  MorphismProperty.of_retract h hg

example : SSet.innerIsoFibrations (𝟙 (Δ[0] : SSet.{u})) :=
  MorphismProperty.of_retract (Retract.refl _)
    (MorphismProperty.id_mem _ _)

end CompositionAndRetracts

section IsomorphismStability

variable {X Y Z : SSet.{u}}

example (e : X ⟶ Y) [IsIso e] (f : Y ⟶ Z) (hf : SSet.innerIsoFibrations f) :
    SSet.innerIsoFibrations (e ≫ f) :=
  MorphismProperty.RespectsIso.precomp _ e f hf

example (f : X ⟶ Y) (hf : SSet.innerIsoFibrations f) (e : Y ⟶ Z) [IsIso e] :
    SSet.innerIsoFibrations (f ≫ e) :=
  MorphismProperty.RespectsIso.postcomp _ e f hf

end IsomorphismStability

section TerminalMaps

variable (X : SSet.{u})

example : SSet.innerIsoFibrations (terminal.from X) ↔ SSet.Quasicategory X :=
  SSet.innerIsoFibrations.terminalFrom_iff_quasicategory X

example (h : SSet.innerIsoFibrations (terminal.from X)) :
    SSet.Quasicategory X :=
  (SSet.innerIsoFibrations.terminalFrom_iff_quasicategory X).1 h

example [SSet.Quasicategory X] :
    SSet.innerIsoFibrations (terminal.from X) :=
  (SSet.innerIsoFibrations.terminalFrom_iff_quasicategory X).2 inferInstance

end TerminalMaps

end InnerIsoFibrationsTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet
