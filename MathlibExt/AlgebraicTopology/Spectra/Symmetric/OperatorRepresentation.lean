/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.ExternalOperatorAction

/-!
# Actual representations of the generic sphere enriched operator

The sphere-module action satisfies the enriched composition equation on
the complete Hom tensor object, by tensor-colimit universal properties.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {T : V}

/-- The full original enriched operator representation, on its actual coefficient coends. -/
abbrev Representation (T : V) :=
  letI : EnrichedCategory V I := enrichedCategory T
  WholeRepresentation V I

/-- The entire original pair of coefficient generators retains the descended composition equation. -/
theorem generator_operatorAction_assoc (d : SphereData T) (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (d.diagram.obj n ◁ (generator T a n k f ⊗ₘ generator T b k l g)) ≫
      (α_ (d.diagram.obj n) (Hom T n k) (Hom T k l)).inv ≫
      (operatorAction d n k ▷ Hom T k l) ≫ operatorAction d k l =
    (d.diagram.obj n ◁ (generator T a n k f ⊗ₘ generator T b k l g)) ≫
      (d.diagram.obj n ◁ composition T n k l) ≫ operatorAction d n l := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let X := d.diagram.obj n
  let u : P.obj a ⟶ Hom T n k := generator T a n k f
  let v : P.obj b ⟶ Hom T k l := generator T b k l g
  let z : P.obj (b ⊗ a) ⟶ Hom T n l :=
    generator T (b ⊗ a) n l ((α_ b a n).hom ≫ (b ◁ f) ≫ g)
  have ha : (X ◁ (u ⊗ₘ v)) ≫ (α_ X (Hom T n k) (Hom T k l)).inv =
      (α_ X (P.obj a) (P.obj b)).inv ≫ ((X ◁ u) ⊗ₘ v) := by
    simpa only [id_tensorHom] using associator_inv_naturality (𝟙 X) u v
  have h1 : (X ◁ u) ≫ operatorAction d n k = actionLeg d a n k f :=
    generator_operatorAction d a n k f
  have h2 : (d.diagram.obj k ◁ v) ≫ operatorAction d k l = actionLeg d b k l g :=
    generator_operatorAction d b k l g
  have h3 : (X ◁ z) ≫ operatorAction d n l =
      actionLeg d (b ⊗ a) n l ((α_ b a n).hom ≫ (b ◁ f) ≫ g) :=
    generator_operatorAction d (b ⊗ a) n l ((α_ b a n).hom ≫ (b ◁ f) ≫ g)
  have hm : (u ⊗ₘ v) ≫ composition T n k l = reverseMultiplication T a b ≫ z :=
    generator_comp_label T n k l (CostructuredArrow.mk (Y := a) f) (CostructuredArrow.mk (Y := b) g)
  have hL : (X ◁ (u ⊗ₘ v)) ≫ (α_ X (Hom T n k) (Hom T k l)).inv ≫
      (operatorAction d n k ▷ Hom T k l) ≫ operatorAction d k l =
      (α_ X (P.obj a) (P.obj b)).inv ≫ actionLeg d a n k f ▷ P.obj b ≫ actionLeg d b k l g := by
    slice_lhs 1 2 => rw [ha]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [tensorHom_comp_whiskerRight, h1, tensorHom_def]
    simp only [Category.assoc]
    slice_lhs 3 4 => exact h2
  have hR : (X ◁ (u ⊗ₘ v)) ≫ (X ◁ composition T n k l) ≫ operatorAction d n l =
      (X ◁ reverseMultiplication T a b) ≫
        actionLeg d (b ⊗ a) n l ((α_ b a n).hom ≫ (b ◁ f) ≫ g) := by
    slice_lhs 1 2 => rw [← whiskerLeft_comp, hm, whiskerLeft_comp]
    simp only [Category.assoc]
    slice_lhs 2 3 => exact h3
  exact hL.trans ((actionLeg_assoc d a b n k l f g).trans hR.symm)

/-- The ordinary sphere-module action respects the entire enriched operator composition. -/
theorem operatorAction_assoc (d : SphereData T) (n k l : I) :
    (α_ (d.diagram.obj n) (Hom T n k) (Hom T k l)).inv ≫
      (operatorAction d n k ▷ Hom T k l) ≫ operatorAction d k l =
    (d.diagram.obj n ◁ composition T n k l) ≫ operatorAction d n l := by
  apply (isColimitOfPreserves (tensorLeft (d.diagram.obj n))
    ((colimit.isColimit (diagram T n k)).tensor₂ (colimit.isColimit (diagram T k l)))).hom_ext
  intro q
  have hi12 : ((colimit.cocone (diagram T n k)).tensor₂
      (colimit.cocone (diagram T k l))).ι.app q =
      generator T q.1.left n k q.1.hom ⊗ₘ generator T q.2.left k l q.2.hom := by
    simpa only [Cocone.tensor₂, Functor.mapCocone₂, curriedTensor] using!
      (tensorHom_def (generator T q.1.left n k q.1.hom)
        (generator T q.2.left k l q.2.hom)).symm
  have hi : ((tensorLeft (d.diagram.obj n)).mapCocone
      ((colimit.cocone (diagram T n k)).tensor₂ (colimit.cocone (diagram T k l)))).ι.app q =
      d.diagram.obj n ◁ (generator T q.1.left n k q.1.hom ⊗ₘ
        generator T q.2.left k l q.2.hom) :=
    congrArg (fun t => d.diagram.obj n ◁ t) hi12
  have h := generator_operatorAction_assoc d q.1.left q.2.left n k l q.1.hom q.2.hom
  exact (congrArg (fun t => t ≫ (α_ (d.diagram.obj n) (Hom T n k) (Hom T k l)).inv ≫
      (operatorAction d n k ▷ Hom T k l) ≫ operatorAction d k l) hi).trans
    (h.trans (congrArg (fun t => t ≫ (d.diagram.obj n ◁ composition T n k l) ≫
      operatorAction d n l) hi).symm)

/-- A complete ordinary sphere module produces its actual enriched operator representation. -/
def toRepresentation (d : SphereData T) : Representation T := by
  letI : EnrichedCategory V I := enrichedCategory T
  exact
    { obj n := d.diagram.obj n
      action := operatorAction d
      unit := operatorAction_unit d
      assoc := operatorAction_assoc d }

/-- Every full original coefficient and finite label remains the same whole action map. -/
theorem toRepresentation_generator (d : SphereData T) (a n k : I) (f : a ⊗ n ⟶ k) :
    letI : EnrichedCategory V I := enrichedCategory T
    (d.diagram.obj n ◁ generator T a n k f) ≫ (toRepresentation d).action n k =
      coefficientAction d a n ≫ d.diagram.map f := by
  let _ : EnrichedCategory V I := enrichedCategory T
  exact generator_operatorAction d a n k f

end CategoryTheory.Spectra.Symmetric.OperatorCoend
