/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.ExternalOperatorCoefficients
public import MathlibExt.CategoryTheory.Enriched.WholeRepresentationData

/-!
# Descending the actual sphere-module action to the operator coends

Every full label acts by its coefficient action and its original target map.
Tensor preservation descends these whole maps to the genuine Hom object.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {T : V}

/-- The whole right-ordered coefficient retains every original object-index map. -/
theorem coefficientAction_index_natural (d : SphereData T) (a : I) {n k : I} (f : n ⟶ k) :
    (d.diagram.map f ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) ≫
      coefficientAction d a k = coefficientAction d a n ≫ d.diagram.map (a ◁ f) := by
  simp only [coefficientAction, Category.assoc]
  slice_lhs 1 2 => rw [braiding_naturality_left]
  simp only [Category.assoc]
  slice_lhs 2 3 => exact index_natural d a f

/-- A whole original operator label acts by the full coefficient action and original target map. -/
def actionLeg (d : SphereData T) (a n k : I) (f : a ⊗ n ⟶ k) :
    d.diagram.obj n ⊗ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ⟶ d.diagram.obj k :=
  coefficientAction d a n ≫ d.diagram.map f

/-- Every original coefficient-index map retains its entire labelled action relation. -/
theorem actionLeg_relation (d : SphereData T) {a b n k : I} (r : a ⟶ b) (f : b ⊗ n ⟶ k) :
    (d.diagram.obj n ◁ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map r) ≫
      actionLeg d b n k f = actionLeg d a n k ((r ▷ n) ≫ f) := by
  simp only [actionLeg, coefficientAction, Category.assoc]
  slice_lhs 1 2 => rw [braiding_naturality_right]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [coefficient_natural]
  simp only [Category.assoc, Functor.map_comp]

/-- The original two labelled external actions compose through the genuine reversed coefficient block. -/
theorem actionLeg_assoc (d : SphereData T) (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (α_ (d.diagram.obj n) ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b)).inv ≫
      (actionLeg d a n k f ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b) ≫
      actionLeg d b k l g =
    (d.diagram.obj n ◁ reverseMultiplication T a b) ≫
      actionLeg d (b ⊗ a) n l ((α_ b a n).hom ≫ (b ◁ f) ≫ g) := by
  have hn := coefficientAction_index_natural d b f
  have ha := coefficientAction_assoc d a b n
  simp only [actionLeg, comp_whiskerRight, Category.assoc]
  slice_lhs 3 4 => rw [hn]
  simp only [Category.assoc]
  slice_lhs 1 3 => rw [ha]
  simp only [Category.assoc, Functor.map_comp]

/-- The complete original identity label acts by the actual value unitor. -/
theorem actionLeg_unit (d : SphereData T) (n : I) :
    actionLeg d (𝟙_ I) n n (λ_ n).hom = (ρ_ (d.diagram.obj n)).hom := by
  let X := d.diagram.obj n
  let z : (𝟙_ V) ⊗ X ⟶ d.diagram.obj ((𝟙_ I) ⊗ n) := coefficient d (𝟙_ I) n
  have hu : z = (λ_ X).hom ≫ d.diagram.map (λ_ n).inv := coefficient_unit d n
  have hi : d.diagram.map (λ_ n).inv ≫ d.diagram.map (λ_ n).hom = 𝟙 _ :=
    (d.diagram.mapIso (λ_ n)).inv_hom_id
  have hb : (β_ X (𝟙_ V)).hom ≫ (λ_ X).hom = (ρ_ X).hom := by
    rw [braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change ((β_ X (𝟙_ V)).hom ≫ z) ≫ d.diagram.map (λ_ n).hom = (ρ_ X).hom
  rw [hu]
  simp only [Category.assoc, hi]
  exact (congrArg (fun t => (β_ X (𝟙_ V)).hom ≫ t) (Category.comp_id (λ_ X).hom)).trans hb

/-- The complete original action legs form a cocone after tensoring the coefficient diagram. -/
def actionCocone (d : SphereData T) (n k : I) :
    Cocone (diagram T n k ⋙ tensorLeft (d.diagram.obj n)) where
  pt := d.diagram.obj k
  ι :=
    { app q := actionLeg d q.left n k q.hom
      naturality := by
        intro q q' r
        have h := actionLeg_relation d r.left q'.hom
        have hw : (r.left ▷ n) ≫ q'.hom = q.hom := r.w
        exact h.trans ((congrArg (actionLeg d q.left n k) hw).trans (Category.comp_id _).symm) }

/-- The whole ordinary module action descends to the actual value-enriched operator Hom object. -/
def operatorAction (d : SphereData T) (n k : I) :
    d.diagram.obj n ⊗ Hom T n k ⟶ d.diagram.obj k :=
  (isColimitOfPreserves (tensorLeft (d.diagram.obj n)) (colimit.isColimit (diagram T n k))).desc
    (actionCocone d n k)

/-- Every whole original coefficient generator retains its full descended action formula. -/
theorem generator_operatorAction (d : SphereData T) (a n k : I) (f : a ⊗ n ⟶ k) :
    (d.diagram.obj n ◁ generator T a n k f) ≫ operatorAction d n k = actionLeg d a n k f := by
  exact (isColimitOfPreserves (tensorLeft (d.diagram.obj n))
    (colimit.isColimit (diagram T n k))).fac (actionCocone d n k) (CostructuredArrow.mk (Y := a) f)

/-- The genuine operator identity acts on the entire ordinary module object by the actual unitor. -/
theorem operatorAction_unit (d : SphereData T) (n : I) :
    (d.diagram.obj n ◁ identity T n) ≫ operatorAction d n n = (ρ_ (d.diagram.obj n)).hom :=
  (generator_operatorAction d (𝟙_ I) n n (λ_ n).hom).trans (actionLeg_unit d n)

end CategoryTheory.Spectra.Symmetric.OperatorCoend
