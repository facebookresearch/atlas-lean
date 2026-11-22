/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CodiscreteEnrichment
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanClasses
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnderHomFunctor
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Original component essential surjectivity at a genuine filtered root colimit

Every original target object comes from an actual original stage because
object forgetting has its genuine codiscrete right adjoint. Original
component essential surjectivity in that stage gives a genuine source
representative. The SAME full cocone functor carries its actual isomorphism
to the terminal target, retaining both original object equations.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredRoot
open ComponentCategory
attribute [local instance] IsFiltered.isConnected

/-- Genuine original stage component representatives give essential surjectivity of the SAME terminal root functor. -/
theorem component_essSurj {C : Carrier.{u}} {J : Type v} [Category.{w} J] [IsFiltered J]
    (U : J ⥤ Under C) (s : Cocone U) (hs : IsColimit s)
    (hU : ∀ i, (mapFunctor (U.obj i).hom).EssSurj) :
    (mapFunctor s.pt.hom).EssSurj := by
  let _ : PreservesColimitsOfSize.{w, v} forgetObjects.{u} :=
    CodiscreteEnrichment.adjunction.leftAdjoint_preservesColimits
  have ht := isColimitOfPreserves forgetObjects (isColimitOfPreserves (Under.forget C) hs)
  constructor
  intro b
  obtain ⟨i, bi, hbi⟩ := Types.jointly_surjective_of_isColimit ht b
  let _ : (mapFunctor (U.obj i).hom).EssSurj := hU i
  obtain ⟨a, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (mapFunctor (U.obj i).hom)
    (objectOf.{u} (U.obj i).right bi)
  let e' := (mapFunctor (s.ι.app i).right).mapIso e
  have hr := OriginalUnderHom.endpoint C (s.ι.app i) a
  let e₁ : (mapFunctor s.pt.hom).obj a ≅
      (mapFunctor (s.ι.app i).right).obj ((mapFunctor (U.obj i).hom).obj a) :=
    eqToIso hr.symm
  let e₂ : (mapFunctor (s.ι.app i).right).obj (objectOf.{u} (U.obj i).right bi) ≅ b :=
    eqToIso hbi
  exact ⟨a, ⟨e₁ ≪≫ e' ≪≫ e₂⟩⟩

end CategoryTheory.SimplicialEnrichment.OriginalFilteredRoot
