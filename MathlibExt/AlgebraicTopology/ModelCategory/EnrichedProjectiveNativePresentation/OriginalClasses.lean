/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Native projective classes in the literal original presentation

Complete original evaluation comparisons and actual original adjunctions
identify all five classes on the same source maps. The constructor comes
from the real native model; no model dictionary or source acyclicity is input.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC uS

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]
  [OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

omit [OrderBot realizedGeneratorCardinal.{v}.ord.ToType] in
/-- A natural isomorphism compares complete evaluated arrows in every
iso-invariant base class. -/
theorem mappedProperty_iso_iff (P : MorphismProperty PointedCGWH.{u, v}) [P.RespectsIso]
    {F G : C ⥤ PointedCGWH.{u, v}} (h : F ≅ G) {X Y : C} (f : X ⟶ Y) :
    P (F.map f) ↔ P (G.map f) :=
  P.arrow_mk_iso_iff (Arrow.isoOfNatIso h (Arrow.mk f))

omit [OrderBot realizedGeneratorCardinal.{v}.ord.ToType] in
/-- Surjective original index labels and the complete evaluation comparison
retain precisely every native coefficient-object evaluation. -/
theorem evaluationProperty_iff_original
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (R : S → C ⥤ PointedCGWH.{u, v})
    (hR : ∀ s, e.functor ⋙ EnrichedFunctorCat.evaluation (j s) ≅ R s)
    (P : MorphismProperty PointedCGWH.{u, v}) [P.RespectsIso]
    {X Y : C} (f : X ⟶ Y) :
    (EvaluationTransfer.evaluationProperty
      (fun a : A => EnrichedFunctorCat.evaluation a) P).inverseImage e.functor f ↔
        ∀ s : S, P ((R s).map f) := by
  rw [MorphismProperty.inverseImage_iff, EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h s
    exact (mappedProperty_iso_iff P (hR s) f).mp (h (j s))
  · intro h a
    obtain ⟨s, rfl⟩ := hj a
    exact (mappedProperty_iso_iff P (hR s) f).mpr (h s)

/-- The source native weak class is detected by the ORIGINAL level maps. -/
theorem weakEquivalences_iff_original
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (R : S → C ⥤ PointedCGWH.{u, v})
    (hR : ∀ s, e.functor ⋙ EnrichedFunctorCat.evaluation (j s) ≅ R s)
    {X Y : C} (f : X ⟶ Y) :
    letI : ModelCategory C := modelCategory e
    weakEquivalences C f ↔ ∀ s : S, weakEquivalences PointedCGWH.{u, v} ((R s).map f) := by
  let _ : ModelCategory C := modelCategory e
  rw [weakEquivalences_eq e]
  exact evaluationProperty_iff_original e j hj R hR _ f

/-- The source native fibration class is detected by every ORIGINAL level map. -/
theorem fibrations_iff_original
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (R : S → C ⥤ PointedCGWH.{u, v})
    (hR : ∀ s, e.functor ⋙ EnrichedFunctorCat.evaluation (j s) ≅ R s)
    {X Y : C} (f : X ⟶ Y) :
    letI : ModelCategory C := modelCategory e
    fibrations C f ↔ ∀ s : S, fibrations PointedCGWH.{u, v} ((R s).map f) := by
  let _ : ModelCategory C := modelCategory e
  rw [fibrations_eq e]
  exact evaluationProperty_iff_original e j hj R hR _ f

/-- The source native intersection class is detected by the actual original levels. -/
theorem trivialFibrations_iff_original
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (R : S → C ⥤ PointedCGWH.{u, v})
    (hR : ∀ s, e.functor ⋙ EnrichedFunctorCat.evaluation (j s) ≅ R s)
    {X Y : C} (f : X ⟶ Y) :
    letI : ModelCategory C := modelCategory e
    trivialFibrations C f ↔ ∀ s : S, trivialFibrations PointedCGWH.{u, v} ((R s).map f) := by
  let _ : ModelCategory C := modelCategory e
  rw [trivialFibrations_eq e]
  exact evaluationProperty_iff_original e j hj R hR _ f

omit [OrderBot realizedGeneratorCardinal.{v}.ord.ToType] in
/-- Literal original free-arrow labels give the same right lifting class as
native free generators through the actual presentation functor. -/
theorem originalGenerators_rlp_eq
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (L : S → PointedCGWH.{u, v} ⥤ C) (R : S → C ⥤ PointedCGWH.{u, v})
    (adj : ∀ s, L s ⊣ R s)
    (hR : ∀ s, e.functor ⋙ EnrichedFunctorCat.evaluation (j s) ≅ R s)
    (P : MorphismProperty PointedCGWH.{u, v}) :
    (MorphismProperty.adjointFamilyGenerators L P).rlp =
      ((generators (A := A) P).rlp).inverseImage e.functor := by
  have hNative : (generators (A := A) P).rlp =
      EvaluationTransfer.evaluationProperty
        (fun a : A => EnrichedFunctorCat.evaluation a) P.rlp :=
    EvaluationTransfer.evaluatedGenerators_rlp_eq
      (fun a : A => EnrichedFunctorCat.Free.functor a)
      (fun a : A => EnrichedFunctorCat.evaluation a)
      (fun a : A => EnrichedFunctorCat.Free.adjunction a) P
  rw [hNative, EvaluationTransfer.evaluatedGenerators_rlp_eq L R adj P]
  ext X Y f
  exact (EvaluationTransfer.evaluationProperty_iff R P.rlp f).trans
    (evaluationProperty_iff_original e j hj R hR P.rlp f).symm

/-- The original free-I right class is the ACTUAL source-model trivial fibration class. -/
theorem trivialFibrations_eq_originalGenerators
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (L : S → PointedCGWH.{u, v} ⥤ C) (R : S → C ⥤ PointedCGWH.{u, v})
    (adj : ∀ s, L s ⊣ R s)
    (hR : ∀ s, e.functor ⋙ EnrichedFunctorCat.evaluation (j s) ≅ R s) :
    letI : ModelCategory C := modelCategory e
    trivialFibrations C =
      (MorphismProperty.adjointFamilyGenerators L PointedCGWH.realizedBoundaryInclusions.{u,
        v}).rlp := by
  let _ : ModelCategory C := modelCategory e
  ext X Y f
  rw [MorphismProperty.adjointFamilyGenerators_rlp_iff L R adj]
  have hBase : PointedCGWH.realizedBoundaryInclusions.{u, v}.rlp =
      trivialFibrations PointedCGWH.{u, v} := by
    let _ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
      instOrderBotToTypeOrdRealizedGeneratorCardinal.{v}
    exact PointedCGWH.cofibrantGenerationData.{u, v}.I_rlp
  rw [hBase]
  exact trivialFibrations_iff_original e j hj R hR f

/-- The original free-J right class is the actual source-model fibration class. -/
theorem fibrations_eq_originalGenerators
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (L : S → PointedCGWH.{u, v} ⥤ C) (R : S → C ⥤ PointedCGWH.{u, v})
    (adj : ∀ s, L s ⊣ R s)
    (hR : ∀ s, e.functor ⋙ EnrichedFunctorCat.evaluation (j s) ≅ R s) :
    letI : ModelCategory C := modelCategory e
    fibrations C =
      (MorphismProperty.adjointFamilyGenerators L PointedCGWH.realizedHornInclusions.{u, v}).rlp
        := by
  let _ : ModelCategory C := modelCategory e
  ext X Y f
  rw [MorphismProperty.adjointFamilyGenerators_rlp_iff L R adj]
  have hBase : PointedCGWH.realizedHornInclusions.{u, v}.rlp =
      fibrations PointedCGWH.{u, v} := by
    let _ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
      instOrderBotToTypeOrdRealizedGeneratorCardinal.{v}
    exact PointedCGWH.cofibrantGenerationData.{u, v}.J_rlp
  rw [hBase]
  exact fibrations_iff_original e j hj R hR f

/-- The actual source cofibration class uses the ORIGINAL literal free-I family. -/
theorem cofibrations_eq_originalGenerators
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (L : S → PointedCGWH.{u, v} ⥤ C) (R : S → C ⥤ PointedCGWH.{u, v})
    (adj : ∀ s, L s ⊣ R s)
    (hR : ∀ s, e.functor ⋙ EnrichedFunctorCat.evaluation (j s) ≅ R s) :
    letI : ModelCategory C := modelCategory e
    cofibrations C =
      (MorphismProperty.adjointFamilyGenerators L PointedCGWH.realizedBoundaryInclusions.{u,
        v}).rlp.llp := by
  let _ : ModelCategory C := modelCategory e
  rw [← trivialFibrations_llp, trivialFibrations_eq_originalGenerators e j hj L R adj hR]

/-- The actual source trivial cofibrations use the ORIGINAL literal free-J family. -/
theorem trivialCofibrations_eq_originalGenerators
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {S : Type uS} (j : S → A) (hj : Function.Surjective j)
    (L : S → PointedCGWH.{u, v} ⥤ C) (R : S → C ⥤ PointedCGWH.{u, v})
    (adj : ∀ s, L s ⊣ R s)
    (hR : ∀ s, e.functor ⋙ EnrichedFunctorCat.evaluation (j s) ≅ R s) :
    letI : ModelCategory C := modelCategory e
    trivialCofibrations C =
      (MorphismProperty.adjointFamilyGenerators L PointedCGWH.realizedHornInclusions.{u,
        v}).rlp.llp := by
  let _ : ModelCategory C := modelCategory e
  rw [← fibrations_llp, fibrations_eq_originalGenerators e j hj L R adj hR]

end HomotopicalAlgebra.EnrichedProjective.NativePresentation
