/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Equivalence

/-!# Complete expected original-generation contracts through a genuine equivalence -/

set_option autoImplicit false
noncomputable section
universe w uC vC uD vD
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.CofibrantGenerationEquivalence

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
open HomotopicalAlgebra.CofibrantGenerationData.Equivalence

section OriginalFamilies

variable (e : C ≌ D) (P : MorphismProperty D)

example : family e P = P.strictMap e.inverse := rfl
example [P.IsSmall.{w}] : (family e P).IsSmall.{w} := family_isSmall e P
example : (family e P).rlp = P.rlp.inverseImage e.functor := family_rlp e P
example : (family e P).strictMap e.functor ≤ P.isoClosure :=
  mapped_family_le_isoClosure e P
example [P.IsSmall.{w}] : (normalizedTarget e P).IsSmall.{w} :=
  normalizedTarget_isSmall e P
example : normalizedTarget e P ≤ P.isoClosure := normalizedTarget_le_isoClosure e P
example : family e P ≤ (normalizedTarget e P).inverseImage e.functor :=
  family_le_normalized_inverseImage e P
example {X Y : C} (f : X ⟶ Y) : family e P f ↔ ∃ q : P.toSet,
    Arrow.mk f = Arrow.mk (e.inverse.map q.1.hom) :=
  family_membership e P f
example (f : Arrow D) : f ≅ e.functor.mapArrow.obj (e.inverse.mapArrow.obj f) :=
  originalGeneratorArrowIso e f
example (f : Arrow D) :
    (originalGeneratorArrowIso e f).hom.left = e.counitIso.inv.app f.left ∧
      (originalGeneratorArrowIso e f).hom.right = e.counitIso.inv.app f.right ∧
      (originalGeneratorArrowIso e f).inv.left = e.counitIso.hom.app f.left ∧
      (originalGeneratorArrowIso e f).inv.right = e.counitIso.hom.app f.right :=
  originalGeneratorArrowIso_fields e f
example (f : Arrow C) : f ≅ e.inverse.mapArrow.obj (e.functor.mapArrow.obj f) :=
  sourceArrowIso e f
example (f : Arrow C) :
    (sourceArrowIso e f).hom.left = e.unitIso.hom.app f.left ∧
      (sourceArrowIso e f).hom.right = e.unitIso.hom.app f.right ∧
      (sourceArrowIso e f).inv.left = e.unitIso.inv.app f.left ∧
      (sourceArrowIso e f).inv.right = e.unitIso.inv.app f.right :=
  sourceArrowIso_fields e f
example : (family e P).map e.functor = P.isoClosure := family_map_eq_isoClosure e P
example : (normalizedTarget e P).isoClosure = P.isoClosure := normalizedTarget_isoClosure e P

variable (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (hP : P.IsCardinalForSmallObjectArgument κ)
example : LocallySmall.{w} C := source_locallySmall e P κ hP
example : HasPushouts C := source_hasPushouts e P κ hP
example : HasCoproducts.{w} C := source_hasCoproducts e P κ hP
example : HasIterationOfShape κ.ord.ToType C := source_hasIteration e P κ hP
example : (normalizedTarget e P).IsCardinalForSmallObjectArgument κ :=
  normalizedTarget_eligible e P κ hP
example : (family e P).IsCardinalForSmallObjectArgument κ := family_eligible e P κ hP

end OriginalFamilies

section ActualModelAndData

variable [ModelCategory D] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] (e : C ≌ D) (d : CofibrantGenerationData D κ)

example : ModelCategory C := modelCategory e
example :
    letI : ModelCategory C := modelCategory e
    CofibrantGenerationData C κ := generationData e d
example :
    letI : ModelCategory C := modelCategory e
    weakEquivalences C = (weakEquivalences D).inverseImage e.functor ∧
      cofibrations C = (cofibrations D).inverseImage e.functor ∧
      fibrations C = (fibrations D).inverseImage e.functor ∧
      trivialCofibrations C = (trivialCofibrations D).inverseImage e.functor ∧
      trivialFibrations C = (trivialFibrations D).inverseImage e.functor :=
  model_five_classes e

example :
    letI : ModelCategory C := modelCategory e
    (generationData e d).I = d.I.strictMap e.inverse := generationData_I e d
example :
    letI : ModelCategory C := modelCategory e
    (generationData e d).I_smallObject = family_eligible e d.I κ d.I_smallObject :=
  generationData_I_smallObject e d
example :
    letI : ModelCategory C := modelCategory e
    (generationData e d).I.rlp = trivialFibrations C := generationData_I_rlp e d
example :
    letI : ModelCategory C := modelCategory e
    (generationData e d).I.rlp.llp = cofibrations C := generationData_I_left e d

example :
    letI : ModelCategory C := modelCategory e
    (generationData e d).J = d.J.strictMap e.inverse := generationData_J e d
example :
    letI : ModelCategory C := modelCategory e
    (generationData e d).J_smallObject = family_eligible e d.J κ d.J_smallObject :=
  generationData_J_smallObject e d
example :
    letI : ModelCategory C := modelCategory e
    (generationData e d).J.rlp = fibrations C := generationData_J_rlp e d
example :
    letI : ModelCategory C := modelCategory e
    (generationData e d).J.rlp.llp = trivialCofibrations C := generationData_J_left e d

example :
    letI : ModelCategory C := modelCategory e
    cofibrantFactorizationData e d = d.cofibrantFactorizationData.ofEquivalence e :=
  cofibrantFactorizationData_eq_original e d
example :
    (cofibrantFactorizationData e d).Z =
      e.functor.mapArrow ⋙ d.cofibrantFactorizationData.Z ⋙ e.inverse :=
  cofibrantFactorizationData_Z e d
example :
    (cofibrantFactorizationData e d).i.app =
      (fun f : Arrow C => e.unitIso.hom.app f.left ≫
        e.inverse.map (d.cofibrantFactorizationData.i.app (e.functor.mapArrow.obj f))) :=
  cofibrantFactorizationData_i_function e d
example :
    (cofibrantFactorizationData e d).p.app =
      (fun f : Arrow C =>
        e.inverse.map (d.cofibrantFactorizationData.p.app (e.functor.mapArrow.obj f)) ≫
          e.unitIso.inv.app f.right) :=
  cofibrantFactorizationData_p_function e d
example {f g : Arrow C} (a : f ⟶ g) :
    (cofibrantFactorizationData e d).Z.map a =
      e.inverse.map (d.cofibrantFactorizationData.Z.map (e.functor.mapArrow.map a)) :=
  cofibrantFactorizationData_map e d a
example (f : Arrow C) :
    (cofibrantFactorizationData e d).i.app f ≫ (cofibrantFactorizationData e d).p.app f = f.hom :=
  (cofibrantFactorizationData e d).fac_app
example {f g : Arrow C} (a : f ⟶ g) :
    a.left ≫ (cofibrantFactorizationData e d).i.app g =
      (cofibrantFactorizationData e d).i.app f ≫ (cofibrantFactorizationData e d).Z.map a :=
  (cofibrantFactorizationData e d).i.naturality a
example {f g : Arrow C} (a : f ⟶ g) :
    (cofibrantFactorizationData e d).Z.map a ≫ (cofibrantFactorizationData e d).p.app g =
      (cofibrantFactorizationData e d).p.app f ≫ a.right :=
  (cofibrantFactorizationData e d).p.naturality a
example (f : Arrow C) :
    (cofibrantFactorizationData e d).Z.map (𝟙 f) = 𝟙 ((cofibrantFactorizationData e d).Z.obj f) :=
  (cofibrantFactorizationData e d).Z.map_id f
example {f g h : Arrow C} (a : f ⟶ g) (b : g ⟶ h) :
    (cofibrantFactorizationData e d).Z.map (a ≫ b) =
      (cofibrantFactorizationData e d).Z.map a ≫ (cofibrantFactorizationData e d).Z.map b :=
  (cofibrantFactorizationData e d).Z.map_comp a b
example (f : Arrow C) :
    e.functor.map ((cofibrantFactorizationData e d).i.app f) ≫
      (cofibrantZComparisonIso e d).hom.app f =
      d.cofibrantFactorizationData.i.app (e.functor.mapArrow.obj f) :=
  cofibrant_mapped_i e d f
example (f : Arrow C) :
    (cofibrantZComparisonIso e d).hom.app f ≫
      d.cofibrantFactorizationData.p.app (e.functor.mapArrow.obj f) =
      e.functor.map ((cofibrantFactorizationData e d).p.app f) :=
  cofibrant_mapped_p e d f

example :
    letI : ModelCategory C := modelCategory e
    fibrantFactorizationData e d = d.fibrantFactorizationData.ofEquivalence e :=
  fibrantFactorizationData_eq_original e d
example :
    (fibrantFactorizationData e d).Z =
      e.functor.mapArrow ⋙ d.fibrantFactorizationData.Z ⋙ e.inverse :=
  fibrantFactorizationData_Z e d
example :
    (fibrantFactorizationData e d).i.app =
      (fun f : Arrow C => e.unitIso.hom.app f.left ≫
        e.inverse.map (d.fibrantFactorizationData.i.app (e.functor.mapArrow.obj f))) :=
  fibrantFactorizationData_i_function e d
example :
    (fibrantFactorizationData e d).p.app =
      (fun f : Arrow C =>
        e.inverse.map (d.fibrantFactorizationData.p.app (e.functor.mapArrow.obj f)) ≫
          e.unitIso.inv.app f.right) :=
  fibrantFactorizationData_p_function e d
example {f g : Arrow C} (a : f ⟶ g) :
    (fibrantFactorizationData e d).Z.map a =
      e.inverse.map (d.fibrantFactorizationData.Z.map (e.functor.mapArrow.map a)) :=
  fibrantFactorizationData_map e d a
example (f : Arrow C) :
    (fibrantFactorizationData e d).i.app f ≫ (fibrantFactorizationData e d).p.app f = f.hom :=
  (fibrantFactorizationData e d).fac_app
example {f g : Arrow C} (a : f ⟶ g) :
    a.left ≫ (fibrantFactorizationData e d).i.app g =
      (fibrantFactorizationData e d).i.app f ≫ (fibrantFactorizationData e d).Z.map a :=
  (fibrantFactorizationData e d).i.naturality a
example {f g : Arrow C} (a : f ⟶ g) :
    (fibrantFactorizationData e d).Z.map a ≫ (fibrantFactorizationData e d).p.app g =
      (fibrantFactorizationData e d).p.app f ≫ a.right :=
  (fibrantFactorizationData e d).p.naturality a
example (f : Arrow C) :
    (fibrantFactorizationData e d).Z.map (𝟙 f) = 𝟙 ((fibrantFactorizationData e d).Z.obj f) :=
  (fibrantFactorizationData e d).Z.map_id f
example {f g h : Arrow C} (a : f ⟶ g) (b : g ⟶ h) :
    (fibrantFactorizationData e d).Z.map (a ≫ b) =
      (fibrantFactorizationData e d).Z.map a ≫ (fibrantFactorizationData e d).Z.map b :=
  (fibrantFactorizationData e d).Z.map_comp a b
example (f : Arrow C) :
    e.functor.map ((fibrantFactorizationData e d).i.app f) ≫
      (fibrantZComparisonIso e d).hom.app f =
      d.fibrantFactorizationData.i.app (e.functor.mapArrow.obj f) :=
  fibrant_mapped_i e d f
example (f : Arrow C) :
    (fibrantZComparisonIso e d).hom.app f ≫
      d.fibrantFactorizationData.p.app (e.functor.mapArrow.obj f) =
      e.functor.map ((fibrantFactorizationData e d).p.app f) :=
  fibrant_mapped_p e d f

example :
    letI : ModelCategory C := modelCategory e
    let data := generationData e d
    data.I.IsSmall.{w} ∧ LocallySmall.{w} C ∧ HasPushouts C ∧ HasCoproducts.{w} C ∧
      HasIterationOfShape κ.ord.ToType C ∧
      (∀ {X Y Z W : C} (i : X ⟶ Y) (_hi : data.I i) (f : Z ⟶ W)
        (c : RelativeCellComplex.{w} (fun _ : κ.ord.ToType => data.I.homFamily) f),
        PreservesColimit c.F (coyoneda.obj (Opposite.op X))) :=
  by
  let _ : ModelCategory C := modelCategory e
  let data := generationData e d
  exact ⟨data.I_smallObject.isSmall, data.I_smallObject.locallySmall,
    data.I_smallObject.hasPushouts, data.I_smallObject.hasCoproducts,
    data.I_smallObject.hasIterationOfShape, data.I_smallObject.preservesColimit⟩

example :
    (fun f : Arrow C => (cofibrantFactorizationData e d).Z.obj f) =
      (fun f : Arrow C => e.inverse.obj
        (d.cofibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f))) :=
  cofibrantFactorizationData_object_function e d

example (f : Arrow C) :
    letI : ModelCategory C := modelCategory e
    cofibrations C
        ((cofibrantFactorizationData e d).i.app f) ∧
      trivialFibrations C
        ((cofibrantFactorizationData e d).p.app f) :=
  by
  let _ : ModelCategory C := modelCategory e
  exact ⟨(cofibrantFactorizationData e d).hi f, (cofibrantFactorizationData e d).hp f⟩

example (f : Arrow C) :
    (cofibrantZComparisonIso e d).hom.app f =
      e.counitIso.hom.app (d.cofibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f)) :=
  cofibrantZComparisonIso_component e d f

example (f : Arrow C) :
    (cofibrantZComparisonIso e d).inv.app f =
      e.counitIso.inv.app (d.cofibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f)) :=
  cofibrantZComparisonIso_inverse_component e d f

example :
    letI : ModelCategory C := modelCategory e
    let data := generationData e d
    data.J.IsSmall.{w} ∧ LocallySmall.{w} C ∧ HasPushouts C ∧ HasCoproducts.{w} C ∧
      HasIterationOfShape κ.ord.ToType C ∧
      (∀ {X Y Z W : C} (i : X ⟶ Y) (_hi : data.J i) (f : Z ⟶ W)
        (c : RelativeCellComplex.{w} (fun _ : κ.ord.ToType => data.J.homFamily) f),
        PreservesColimit c.F (coyoneda.obj (Opposite.op X))) :=
  by
  let _ : ModelCategory C := modelCategory e
  let data := generationData e d
  exact ⟨data.J_smallObject.isSmall, data.J_smallObject.locallySmall,
    data.J_smallObject.hasPushouts, data.J_smallObject.hasCoproducts,
    data.J_smallObject.hasIterationOfShape, data.J_smallObject.preservesColimit⟩

example :
    (fun f : Arrow C => (fibrantFactorizationData e d).Z.obj f) =
      (fun f : Arrow C => e.inverse.obj
        (d.fibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f))) :=
  fibrantFactorizationData_object_function e d

example (f : Arrow C) :
    letI : ModelCategory C := modelCategory e
    trivialCofibrations C
        ((fibrantFactorizationData e d).i.app f) ∧
      fibrations C
        ((fibrantFactorizationData e d).p.app f) :=
  by
  let _ : ModelCategory C := modelCategory e
  exact ⟨(fibrantFactorizationData e d).hi f, (fibrantFactorizationData e d).hp f⟩

example (f : Arrow C) :
    (fibrantZComparisonIso e d).hom.app f =
      e.counitIso.hom.app (d.fibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f)) :=
  fibrantZComparisonIso_component e d f

example (f : Arrow C) :
    (fibrantZComparisonIso e d).inv.app f =
      e.counitIso.inv.app (d.fibrantFactorizationData.Z.obj (e.functor.mapArrow.obj f)) :=
  fibrantZComparisonIso_inverse_component e d f

end ActualModelAndData

section IndependentUniverses

variable {C' : Type (uC + 1)} [Category.{vC + 1} C']
  {D' : Type (uD + 1)} [Category.{vD + 1} D'] [ModelCategory D']
  (e : C' ≌ D') {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData D' κ)

example :
    letI : ModelCategory C' := modelCategory e
    CofibrantGenerationData C' κ := generationData e d

example (f : Arrow C') :
    (cofibrantFactorizationData e d).i.app f ≫
      (cofibrantFactorizationData e d).p.app f = f.hom :=
  (cofibrantFactorizationData e d).fac_app

end IndependentUniverses

end MathlibExtTest.CofibrantGenerationEquivalence
