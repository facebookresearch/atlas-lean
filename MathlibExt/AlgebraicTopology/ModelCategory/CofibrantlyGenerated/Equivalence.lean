/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
import MathlibExt.AlgebraicTopology.ModelCategory.SmallGenerator
import MathlibExt.CategoryTheory.SmallObject.FullyFaithful
import MathlibExt.CategoryTheory.SmallObject.IsoEligibility
import MathlibExt.CategoryTheory.MorphismProperty.IndexEquivalence
import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence
import Mathlib.AlgebraicTopology.ModelCategory.Transport

/-!
# Original generation data through a genuine equivalence

The literal inverse images of original generator arrows are small at the
supplied working universe. The original cardinal and ordinal bottom remain
fixed. The given equivalence and normalized mapped-back family transport all
six eligibility fields. Chosen source factors remain the original target
values transported by the existing factor-equivalence API.
-/

set_option autoImplicit false
noncomputable section
universe w uC vC uD vD
open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.CofibrantGenerationData.Equivalence

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The entire original family sent by the actual given inverse, with literal source labels. -/
def family (e : C ≌ D) (P : MorphismProperty D) : MorphismProperty C :=
  P.strictMap e.inverse

/-- Literal inverse images of a genuinely small original family remain small. -/
theorem family_isSmall (e : C ≌ D) (P : MorphismProperty D) [P.IsSmall.{w}] :
    (family e P).IsSmall.{w} :=
  IsSmall.strictMap (inferInstance : P.IsSmall.{w}) e.inverse

/-- The actual inverse/forward adjunction gives the complete original right class. -/
theorem family_rlp (e : C ≌ D) (P : MorphismProperty D) :
    (family e P).rlp = P.rlp.inverseImage e.functor :=
  strictMap_rlp_eq_inverseImage_rlp P e.inverse e.functor e.symm.toAdjunction

/-- Mapped-back original generators lie in the original isomorphism saturation. -/
theorem mapped_family_le_isoClosure (e : C ≌ D) (P : MorphismProperty D) :
    (family e P).strictMap e.functor ≤ P.isoClosure := by
  intro X Y f hf
  cases hf with
  | map hf =>
    cases hf with
    | map hp =>
      refine ⟨_, _, _, hp, ⟨?_⟩⟩
      exact Arrow.isoMk (e.counitIso.app _).symm (e.counitIso.app _).symm (by
        simpa only [Functor.comp_map, Functor.id_map, Functor.id_obj,
          Functor.comp_obj, Iso.app_inv, Iso.symm_hom, Arrow.mk_left, Arrow.mk_right,
          Arrow.mk_hom] using
          (e.counitIso.inv.naturality _).symm)

/-- Normalize only by the actual small original and mapped-back families. -/
def normalizedTarget (e : C ≌ D) (P : MorphismProperty D) : MorphismProperty D :=
  P ⊔ (family e P).strictMap e.functor

/-- The normalized target is genuinely small, without making an isoClosure small. -/
theorem normalizedTarget_isSmall (e : C ≌ D) (P : MorphismProperty D) [P.IsSmall.{w}] :
    (normalizedTarget e P).IsSmall.{w} := by
  let _ : (family e P).IsSmall.{w} := family_isSmall e P
  let _ : ((family e P).strictMap e.functor).IsSmall.{w} :=
    IsSmall.strictMap (family_isSmall e P) e.functor
  rw [normalizedTarget, sup_eq_iSup]
  let _ (b : Bool) : (cond b P ((family e P).strictMap e.functor)).IsSmall.{w} := by
    cases b
    · exact inferInstanceAs (((family e P).strictMap e.functor).IsSmall.{w})
    · exact inferInstanceAs (P.IsSmall.{w})
  infer_instance

/-- This normalization retains precisely the original target saturation. -/
theorem normalizedTarget_le_isoClosure (e : C ≌ D) (P : MorphismProperty D) :
    normalizedTarget e P ≤ P.isoClosure :=
  sup_le P.le_isoClosure (mapped_family_le_isoClosure e P)

/-- The original inverse-family maps literally into its actual normalized target. -/
theorem family_le_normalized_inverseImage (e : C ≌ D) (P : MorphismProperty D) :
    family e P ≤ (normalizedTarget e P).inverseImage e.functor :=
  fun _ _ f hf => Or.inr (map_mem_strictMap _ _ f hf)

/-- The whole original inverse-family membership keeps the actual original generator arrow. -/
theorem family_membership (e : C ≌ D) (P : MorphismProperty D) {X Y : C} (f : X ⟶ Y) :
    family e P f ↔ ∃ q : P.toSet,
      Arrow.mk f = Arrow.mk (e.inverse.map q.1.hom) := by
  constructor
  · intro hf
    cases hf with
    | map hp => exact ⟨⟨Arrow.mk _, hp⟩, rfl⟩
  · rintro ⟨q, hq⟩
    have h : family e P (e.inverse.map q.1.hom) := map_mem_strictMap P e.inverse _ q.2
    have hq' : (Arrow.mk f ∈ (family e P).toSet) :=
      hq.symm ▸ h
    exact hq'

/-- Every original target generator Arrow is compared to its literal mapped-back image. -/
def originalGeneratorArrowIso (e : C ≌ D) (f : Arrow D) :
    f ≅ e.functor.mapArrow.obj (e.inverse.mapArrow.obj f) :=
  ((Functor.mapArrowFunctor D D).mapIso e.counitIso.symm).app f

/-- The complete recovery isomorphism retains the actual original endpoint counit maps. -/
theorem originalGeneratorArrowIso_fields (e : C ≌ D) (f : Arrow D) :
    (originalGeneratorArrowIso e f).hom.left = e.counitIso.inv.app f.left ∧
      (originalGeneratorArrowIso e f).hom.right = e.counitIso.inv.app f.right ∧
      (originalGeneratorArrowIso e f).inv.left = e.counitIso.hom.app f.left ∧
      (originalGeneratorArrowIso e f).inv.right = e.counitIso.hom.app f.right := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Original source Arrows retain the same unit comparison to forward-then-inverse maps. -/
def sourceArrowIso (e : C ≌ D) (f : Arrow C) :
    f ≅ e.inverse.mapArrow.obj (e.functor.mapArrow.obj f) :=
  ((Functor.mapArrowFunctor C C).mapIso e.unitIso).app f

/-- All source recovery components retain the original given unit and its inverse. -/
theorem sourceArrowIso_fields (e : C ≌ D) (f : Arrow C) :
    (sourceArrowIso e f).hom.left = e.unitIso.hom.app f.left ∧
      (sourceArrowIso e f).hom.right = e.unitIso.hom.app f.right ∧
      (sourceArrowIso e f).inv.left = e.unitIso.inv.app f.left ∧
      (sourceArrowIso e f).inv.right = e.unitIso.inv.app f.right := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The entire inverse-family, mapped back by the given functor, has original saturation. -/
theorem family_map_eq_isoClosure (e : C ≌ D) (P : MorphismProperty D) :
    (family e P).map e.functor = P.isoClosure := by
  have h : (family e P).map e.functor = (P.map e.inverse).map e.functor := by
    change (P.strictMap e.inverse).map e.functor = (P.map e.inverse).map e.functor
    rw [map_eq_isoClosure P e.inverse, map_isoClosure]
  rw [h, map_map, map_eq_of_iso P e.counitIso, map_id_eq_isoClosure]

/-- The normalized target retains exactly the original complete generator saturation. -/
theorem normalizedTarget_isoClosure (e : C ≌ D) (P : MorphismProperty D) :
    (normalizedTarget e P).isoClosure = P.isoClosure := by
  apply le_antisymm
  · exact (isoClosure_le_iff _ _).mpr (normalizedTarget_le_isoClosure e P)
  · exact monotone_isoClosure (le_sup_left : P ≤ normalizedTarget e P)

section SameCardinal

variable (e : C ≌ D) (P : MorphismProperty D)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (hP : P.IsCardinalForSmallObjectArgument κ)

include e P hP

/-- Actual working-size Homs reflect through the same faithful functor. -/
theorem source_locallySmall : LocallySmall.{w} C := by
  let _ : LocallySmall.{w} D := hP.locallySmall
  exact locallySmall_of_faithful e.functor

/-- The original actual pushout shapes transport through the given equivalence. -/
theorem source_hasPushouts : HasPushouts C := by
  let _ : HasPushouts D := hP.hasPushouts
  exact Adjunction.hasColimitsOfShape_of_equivalence e.functor

/-- Every actual original working-size coproduct transports through the same inverse. -/
theorem source_hasCoproducts : HasCoproducts.{w} C := by
  let _ : HasCoproducts.{w} D := hP.hasCoproducts
  intro J
  exact Adjunction.hasColimitsOfShape_of_equivalence e.functor

/-- Exactly the original ordinal and initial-segment iteration shapes are transported. -/
theorem source_hasIteration : HasIterationOfShape κ.ord.ToType C := by
  let _ : HasIterationOfShape κ.ord.ToType D := hP.hasIterationOfShape
  exact
    { hasColimitsOfShape :=
        Adjunction.hasColimitsOfShape_of_equivalence e.functor
      hasColimitsOfShape_of_isSuccLimit := fun j hj => by
        let _ : HasColimitsOfShape (Set.Iio j) D :=
          hP.hasIterationOfShape.hasColimitsOfShape_of_isSuccLimit j hj
        exact Adjunction.hasColimitsOfShape_of_equivalence e.functor }

/-- The original normalized target has all six fields at exactly the given κ. -/
theorem normalizedTarget_eligible :
    (normalizedTarget e P).IsCardinalForSmallObjectArgument κ := by
  let _ : P.IsCardinalForSmallObjectArgument κ := hP
  let _ : P.IsSmall.{w} := hP.isSmall
  let _ : (normalizedTarget e P).IsSmall.{w} := normalizedTarget_isSmall e P
  let _ : LocallySmall.{w} D := hP.locallySmall
  let _ : HasPushouts D := hP.hasPushouts
  let _ : HasCoproducts.{w} D := hP.hasCoproducts
  let _ : HasIterationOfShape κ.ord.ToType D := hP.hasIterationOfShape
  exact isCardinalForSmallObjectArgument_of_isoClosure
    (normalizedTarget e P) P κ (normalizedTarget_le_isoClosure e P)

/-- All six source eligibility fields retain the same cardinal, bottom and original chain. -/
theorem family_eligible : (family e P).IsCardinalForSmallObjectArgument κ := by
  let _ : P.IsSmall.{w} := hP.isSmall
  let _ : (family e P).IsSmall.{w} := family_isSmall e P
  let _ : LocallySmall.{w} C := source_locallySmall e P κ hP
  let _ : HasPushouts C := source_hasPushouts e P κ hP
  let _ : HasCoproducts.{w} C := source_hasCoproducts e P κ hP
  let _ : HasIterationOfShape κ.ord.ToType C := source_hasIteration e P κ hP
  let _ : (normalizedTarget e P).IsCardinalForSmallObjectArgument κ :=
    normalizedTarget_eligible e P κ hP
  exact IsCardinalForSmallObjectArgument.of_fullyFaithful
    e.functor (family e P) (normalizedTarget e P) κ
    (family_le_normalized_inverseImage e P)

end SameCardinal

section ModelAndData

variable [ModelCategory D]

/-- The actual original weak class transported by the supplied forward functor. -/
def weakProperty (e : C ≌ D) : MorphismProperty C :=
  (weakEquivalences D).inverseImage e.functor

/-- The actual original cofibration class transported by the same forward functor. -/
def cofibrationProperty (e : C ≌ D) : MorphismProperty C :=
  (cofibrations D).inverseImage e.functor

/-- The actual original fibration class transported by the same forward functor. -/
def fibrationProperty (e : C ≌ D) : MorphismProperty C :=
  (fibrations D).inverseImage e.functor

/-- Use stock transport on exactly the three original inverse-image source classes. -/
@[instance_reducible]
def modelCategory (e : C ≌ D) : ModelCategory C := by
  letI : CategoryWithCofibrations C := ⟨cofibrationProperty e⟩
  letI : CategoryWithFibrations C := ⟨fibrationProperty e⟩
  letI : CategoryWithWeakEquivalences C := ⟨weakProperty e⟩
  exact ModelCategory.transport e rfl rfl rfl

/-- All five transported model classes retain the original forward map and base properties. -/
theorem model_five_classes (e : C ≌ D) :
    letI : ModelCategory C := modelCategory e
    weakEquivalences C = (weakEquivalences D).inverseImage e.functor ∧
      cofibrations C = (cofibrations D).inverseImage e.functor ∧
      fibrations C = (fibrations D).inverseImage e.functor ∧
      trivialCofibrations C = (trivialCofibrations D).inverseImage e.functor ∧
      trivialFibrations C = (trivialFibrations D).inverseImage e.functor := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (e : C ≌ D) (d : CofibrantGenerationData D κ)

/-- The complete source generation record keeps the literal inverse-family maps and κ. -/
def generationData :
    letI : ModelCategory C := modelCategory e
    CofibrantGenerationData C κ := by
  letI : ModelCategory C := modelCategory e
  exact
    { I := family e d.I
      J := family e d.J
      I_smallObject := family_eligible e d.I κ d.I_smallObject
      J_smallObject := family_eligible e d.J κ d.J_smallObject
      I_rlp := by
        rw [family_rlp, d.I_rlp]
        rfl
      J_rlp := by
        rw [family_rlp, d.J_rlp]
        rfl }

/-- The whole original I family is sent by the actual inverse functor without saturation. -/
theorem generationData_I :
    letI : ModelCategory C := modelCategory e
    (generationData e d).I = d.I.strictMap e.inverse := rfl

/-- The whole original J family is sent by the actual inverse functor without saturation. -/
theorem generationData_J :
    letI : ModelCategory C := modelCategory e
    (generationData e d).J = d.J.strictMap e.inverse := rfl

/-- The original full I source dictionary is exactly the proved same-cardinal transfer. -/
theorem generationData_I_smallObject :
    letI : ModelCategory C := modelCategory e
    (generationData e d).I_smallObject = family_eligible e d.I κ d.I_smallObject := rfl

/-- The original full J source dictionary is exactly the proved same-cardinal transfer. -/
theorem generationData_J_smallObject :
    letI : ModelCategory C := modelCategory e
    (generationData e d).J_smallObject = family_eligible e d.J κ d.J_smallObject := rfl

/-- The full original inverse-I right class is the transported trivial-fibration class. -/
theorem generationData_I_rlp :
    letI : ModelCategory C := modelCategory e
    (generationData e d).I.rlp = trivialFibrations C := by
  let _ : ModelCategory C := modelCategory e
  exact (generationData e d).I_rlp

/-- The full original inverse-J right class is the transported fibration class. -/
theorem generationData_J_rlp :
    letI : ModelCategory C := modelCategory e
    (generationData e d).J.rlp = fibrations C := by
  let _ : ModelCategory C := modelCategory e
  exact (generationData e d).J_rlp

/-- The original inverse-I generated left class is the transported cofibration class. -/
theorem generationData_I_left :
    letI : ModelCategory C := modelCategory e
    (generationData e d).I.rlp.llp = cofibrations C := by
  let _ : ModelCategory C := modelCategory e
  rw [(generationData e d).I_rlp, trivialFibrations_llp]

/-- The original inverse-J generated left class is the transported trivial-cofibration class. -/
theorem generationData_J_left :
    letI : ModelCategory C := modelCategory e
    (generationData e d).J.rlp.llp = trivialCofibrations C := by
  let _ : ModelCategory C := modelCategory e
  rw [(generationData e d).J_rlp, fibrations_llp]

/-- The chosen source I factors are exactly the given target factors through the old transport. -/
def cofibrantFactorizationData :
    letI : ModelCategory C := modelCategory e
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) := by
  let _ : ModelCategory C := modelCategory e
  exact d.cofibrantFactorizationData.ofEquivalence e

/-- The chosen source J factors are exactly the same given target J factors through transport. -/
def fibrantFactorizationData :
    letI : ModelCategory C := modelCategory e
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) := by
  let _ : ModelCategory C := modelCategory e
  exact d.fibrantFactorizationData.ofEquivalence e

/-- The entire chosen source I factor value is the existing original equivalence transport. -/
theorem cofibrantFactorizationData_eq_original :
    letI : ModelCategory C := modelCategory e
    cofibrantFactorizationData e d = d.cofibrantFactorizationData.ofEquivalence e := rfl

/-- The entire chosen source J factor value is the existing original equivalence transport. -/
theorem fibrantFactorizationData_eq_original :
    letI : ModelCategory C := modelCategory e
    fibrantFactorizationData e d = d.fibrantFactorizationData.ofEquivalence e := rfl

/-- The whole original source I middle functor keeps the forward/inverse and target value. -/
theorem cofibrantFactorizationData_Z :
    (cofibrantFactorizationData e d).Z =
      e.functor.mapArrow ⋙ d.cofibrantFactorizationData.Z ⋙ e.inverse := rfl

/-- The whole original source J middle functor keeps the forward/inverse and target value. -/
theorem fibrantFactorizationData_Z :
    (fibrantFactorizationData e d).Z =
      e.functor.mapArrow ⋙ d.fibrantFactorizationData.Z ⋙ e.inverse := rfl

/-- The complete I inclusion function retains the actual source unit and given target arrows. -/
theorem cofibrantFactorizationData_i_function :
    (cofibrantFactorizationData e d).i.app =
      (fun f : Arrow C => e.unitIso.hom.app f.left ≫
        e.inverse.map (d.cofibrantFactorizationData.i.app (e.functor.mapArrow.obj f))) := rfl

/-- The complete I projection function retains the original inverse source unit. -/
theorem cofibrantFactorizationData_p_function :
    (cofibrantFactorizationData e d).p.app =
      (fun f : Arrow C =>
        e.inverse.map (d.cofibrantFactorizationData.p.app (e.functor.mapArrow.obj f)) ≫
          e.unitIso.inv.app f.right) := rfl

/-- The complete J inclusion function retains the actual source unit and given target arrows. -/
theorem fibrantFactorizationData_i_function :
    (fibrantFactorizationData e d).i.app =
      (fun f : Arrow C => e.unitIso.hom.app f.left ≫
        e.inverse.map (d.fibrantFactorizationData.i.app (e.functor.mapArrow.obj f))) := rfl

/-- The complete J projection function retains the original inverse source unit. -/
theorem fibrantFactorizationData_p_function :
    (fibrantFactorizationData e d).p.app =
      (fun f : Arrow C =>
        e.inverse.map (d.fibrantFactorizationData.p.app (e.functor.mapArrow.obj f)) ≫
          e.unitIso.inv.app f.right) := rfl

/-- Every original I middle map is the inverse image of the same target Arrow map. -/
theorem cofibrantFactorizationData_map {f g : Arrow C} (a : f ⟶ g) :
    (cofibrantFactorizationData e d).Z.map a =
      e.inverse.map (d.cofibrantFactorizationData.Z.map (e.functor.mapArrow.map a)) := rfl

/-- Every original J middle map is the inverse image of the same target Arrow map. -/
theorem fibrantFactorizationData_map {f g : Arrow C} (a : f ⟶ g) :
    (fibrantFactorizationData e d).Z.map a =
      e.inverse.map (d.fibrantFactorizationData.Z.map (e.functor.mapArrow.map a)) := rfl

/-- The actual target counit compares the whole given I middle functor after transport. -/
def cofibrantZComparisonIso :
    (cofibrantFactorizationData e d).Z ⋙ e.functor ≅ e.functor.mapArrow ⋙
      d.cofibrantFactorizationData.Z :=
  d.cofibrantFactorizationData.ofEquivalenceZComparisonIso e

/-- The actual target counit compares the whole given J middle functor after transport. -/
def fibrantZComparisonIso :
    (fibrantFactorizationData e d).Z ⋙ e.functor ≅ e.functor.mapArrow ⋙
      d.fibrantFactorizationData.Z :=
  d.fibrantFactorizationData.ofEquivalenceZComparisonIso e

/-- The entire mapped I inclusion retains its original target value through the actual counit. -/
theorem cofibrant_mapped_i (f : Arrow C) :
    e.functor.map ((cofibrantFactorizationData e d).i.app f) ≫
      (cofibrantZComparisonIso e d).hom.app f =
      d.cofibrantFactorizationData.i.app (e.functor.mapArrow.obj f) :=
  d.cofibrantFactorizationData.ofEquivalence_mapped_i e f

/-- The entire mapped I projection retains its original target value through the actual counit. -/
theorem cofibrant_mapped_p (f : Arrow C) :
    (cofibrantZComparisonIso e d).hom.app f ≫
      d.cofibrantFactorizationData.p.app (e.functor.mapArrow.obj f) =
      e.functor.map ((cofibrantFactorizationData e d).p.app f) :=
  d.cofibrantFactorizationData.ofEquivalence_mapped_p e f

/-- The entire mapped J inclusion retains its original target value through the actual counit. -/
theorem fibrant_mapped_i (f : Arrow C) :
    e.functor.map ((fibrantFactorizationData e d).i.app f) ≫
      (fibrantZComparisonIso e d).hom.app f =
      d.fibrantFactorizationData.i.app (e.functor.mapArrow.obj f) :=
  d.fibrantFactorizationData.ofEquivalence_mapped_i e f

/-- The entire mapped J projection retains its original target value through the actual counit. -/
theorem fibrant_mapped_p (f : Arrow C) :
    (fibrantZComparisonIso e d).hom.app f ≫
      d.fibrantFactorizationData.p.app (e.functor.mapArrow.obj f) =
      e.functor.map ((fibrantFactorizationData e d).p.app f) :=
  d.fibrantFactorizationData.ofEquivalence_mapped_p e f

/-- The transported cofibrant middle-object function keeps the actual original inverse. -/
theorem cofibrantFactorizationData_object_function :
    (fun f : Arrow C => (cofibrantFactorizationData e d).Z.obj f) =
      (fun f : Arrow C => e.inverse.obj
        (d.cofibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f))) := rfl

/-- The cofibrant comparison component is the actual target counit at its old middle object. -/
theorem cofibrantZComparisonIso_component (f : Arrow C) :
    (cofibrantZComparisonIso e d).hom.app f =
      e.counitIso.hom.app (d.cofibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f)) := rfl

/-- The inverse cofibrant comparison retains the original inverse counit component. -/
theorem cofibrantZComparisonIso_inverse_component (f : Arrow C) :
    (cofibrantZComparisonIso e d).inv.app f =
      e.counitIso.inv.app (d.cofibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f)) := rfl

/-- The transported fibrant middle-object function keeps the actual original inverse. -/
theorem fibrantFactorizationData_object_function :
    (fun f : Arrow C => (fibrantFactorizationData e d).Z.obj f) =
      (fun f : Arrow C => e.inverse.obj
        (d.fibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f))) := rfl

/-- The fibrant comparison component is the actual target counit at its old middle object. -/
theorem fibrantZComparisonIso_component (f : Arrow C) :
    (fibrantZComparisonIso e d).hom.app f =
      e.counitIso.hom.app (d.fibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f)) := rfl

/-- The inverse fibrant comparison retains the original inverse counit component. -/
theorem fibrantZComparisonIso_inverse_component (f : Arrow C) :
    (fibrantZComparisonIso e d).inv.app f =
      e.counitIso.inv.app (d.fibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f)) := rfl

end ModelAndData

end HomotopicalAlgebra.CofibrantGenerationData.Equivalence
