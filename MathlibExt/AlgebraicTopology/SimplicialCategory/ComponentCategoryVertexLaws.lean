/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategory

/-!
# Original identity and composition vertices in the component Hom category

The native Cartesian component tensorator carries actual pairs of
original vertices to their paired component. Consequently identity and
composition in the genuine component Hom category read back the same
original enriched vertices, without a Kan premise or object quotient.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.ComponentCategory

private theorem piZero_mu_mk {X Y : SSet.{u}} (a : X _⦋0⦌) (b : Y _⦋0⦌) :
    (Functor.LaxMonoidal.μ SSet.π₀Functor X Y) (SSet.π₀.mk a, SSet.π₀.mk b) =
      SSet.π₀.mk (SSet.componentTensorSimplex _ a b) := by
  apply (SSet.piZeroTensorEquiv X Y).injective
  change (SSet.mapπ₀ (CartesianMonoidalCategory.fst X Y)
    ((Functor.LaxMonoidal.μ SSet.π₀Functor X Y) (SSet.π₀.mk a, SSet.π₀.mk b)),
      SSet.mapπ₀ (CartesianMonoidalCategory.snd X Y)
        ((Functor.LaxMonoidal.μ SSet.π₀Functor X Y) (SSet.π₀.mk a, SSet.π₀.mk b))) =
          (SSet.π₀.mk a, SSet.π₀.mk b)
  apply Prod.ext
  · exact congr($(Functor.Monoidal.μ_fst SSet.π₀Functor X Y) (SSet.π₀.mk a, SSet.π₀.mk b))
  · exact congr($(Functor.Monoidal.μ_snd SSet.π₀Functor X Y) (SSet.π₀.mk a, SSet.π₀.mk b))

variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- The original enriched identity vertex represents the actual component-category identity. -/
theorem arrowOf_identity (x : C) :
    arrowOf C ((eId SSet.{u} x).app (op ⦋0⦌) PUnit.unit) = 𝟙 (objectOf.{u} C x) := by
  change SSet.π₀.mk ((eId SSet.{u} x).app (op ⦋0⦌) PUnit.unit) =
    SSet.mapπ₀ (eId SSet.{u} x) ((Functor.LaxMonoidal.ε SSet.π₀Functor) PUnit.unit)
  obtain ⟨v, hv⟩ := SSet.π₀.mk_surjective ((Functor.LaxMonoidal.ε SSet.π₀Functor) PUnit.unit)
  rw [← hv, SSet.mapπ₀_mk]
  have h : v = PUnit.unit := by
    change @Eq PUnit.{u + 1} _ _
    exact Subsingleton.elim _ _
  subst v
  rfl

/-- Actual original paired Hom vertices represent the same component-category composite. -/
theorem arrowOf_composition {x y z : C} (a : (x ⟶[SSet.{u}] y) _⦋0⦌) (b : (y ⟶[SSet.{u}] z) _⦋0⦌) :
    arrowOf C a ≫ arrowOf C b = arrowOf C ((eComp SSet.{u} x y z).app (op ⦋0⦌)
      (SSet.componentTensorSimplex _ a b)) := by
  change SSet.mapπ₀ (eComp SSet.{u} x y z)
    ((Functor.LaxMonoidal.μ SSet.π₀Functor _ _) (SSet.π₀.mk a, SSet.π₀.mk b)) = _
  rw [piZero_mu_mk, SSet.mapπ₀_mk]
  rfl

end CategoryTheory.SimplicialEnrichment.ComponentCategory
