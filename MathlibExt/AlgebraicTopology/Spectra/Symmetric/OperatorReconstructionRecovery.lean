/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorToExternal

/-!
# Both complete original sphere-module reconstruction laws

Restriction recovers every original index map and coefficient. Rebuilding
an enriched operator representation recovers its entire Hom action by the
preserved coend universal property, with every original label retained.
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
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] {T : V}

/-- Every original zero-coefficient arrow acts by the complete original diagram map. -/
theorem actionLeg_arrow (d : SphereData T) {n k : I} (f : n ⟶ k) :
    actionLeg d (𝟙_ I) n k ((λ_ n).hom ≫ f) = (ρ_ (d.diagram.obj n)).hom ≫ d.diagram.map f := by
  let A := d.diagram.obj n
  let B := d.diagram.obj ((𝟙_ I) ⊗ n)
  let c : A ⊗ (𝟙_ V) ⟶ B := coefficientAction d (𝟙_ I) n
  let r : B ⟶ A := d.diagram.map (λ_ n).hom
  let s : A ⟶ d.diagram.obj k := d.diagram.map f
  have hu : c ≫ r = (ρ_ A).hom := actionLeg_unit d n
  have hm : d.diagram.map ((λ_ n).hom ≫ f) = r ≫ s := d.diagram.map_comp (λ_ n).hom f
  change c ≫ d.diagram.map ((λ_ n).hom ≫ f) = (ρ_ A).hom ≫ s
  rw [hm, ← Category.assoc, hu]

variable [MonoidalClosed V]

/-- Every original finite-index map is recovered on the complete original ordinary module diagram. -/
theorem ordinaryDiagram_toRepresentation_map (d : SphereData T) {n k : I} (f : n ⟶ k) :
    (ordinaryDiagram (toRepresentation d)).map f = d.diagram.map f := by
  let A := d.diagram.obj n
  have hm : (ordinaryDiagram (toRepresentation d)).map f =
      (ρ_ A).inv ≫ (A ◁ arrow T f) ≫ operatorAction d n k := ordinaryDiagram_map (toRepresentation d) f
  have hg : (A ◁ arrow T f) ≫ operatorAction d n k = (ρ_ A).hom ≫ d.diagram.map f :=
    (generator_operatorAction d (𝟙_ I) n k ((λ_ n).hom ≫ f)).trans (actionLeg_arrow d f)
  rw [hm, hg, Iso.inv_hom_id_assoc]

omit [MonoidalClosed V] in
/-- Every original whole coefficient is recovered from the actual descended enriched operator. -/
theorem representationCoefficient_toRepresentation (d : SphereData T) (a n : I) :
    representationCoefficient (toRepresentation d) a n = coefficient d a n := by
  let A := d.diagram.obj n
  let P := (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a
  let j : P ⟶ Hom T n (a ⊗ n) := generator T a n (a ⊗ n) (𝟙 (a ⊗ n))
  have hg : (A ◁ j) ≫ operatorAction d n (a ⊗ n) = coefficientAction d a n := by
    have h : (A ◁ j) ≫ operatorAction d n (a ⊗ n) = actionLeg d a n (a ⊗ n) (𝟙 (a ⊗ n)) :=
      generator_operatorAction d a n (a ⊗ n) (𝟙 (a ⊗ n))
    simpa only [actionLeg, Functor.map_id, Category.comp_id] using h
  change (β_ P A).hom ≫ (A ◁ j) ≫ operatorAction d n (a ⊗ n) = coefficient d a n
  rw [hg]
  simp only [coefficientAction]
  exact SymmetricCategory.symmetry_assoc P A (coefficient d a n)

/-- The original entire ordinary diagram is recovered, with every finite-index arrow. -/
theorem from_to_diagram (d : SphereData T) : (fromRepresentation (toRepresentation d)).diagram = d.diagram := by
  refine Functor.ext (fun _ => rfl) ?_
  intro n k f
  change (ordinaryDiagram (toRepresentation d)).map f =
    (𝟙 (d.diagram.obj n)) ≫ d.diagram.map f ≫ (𝟙 (d.diagram.obj k))
  simpa only [Category.comp_id, Category.id_comp] using ordinaryDiagram_toRepresentation_map d f

/-- Every complete original action coefficient is recovered on the existing module presentation. -/
theorem from_to_coefficient (d : SphereData T) (a n : I) :
    coefficient (fromRepresentation (toRepresentation d)) a n = coefficient d a n :=
  representationCoefficient_toRepresentation d a n

/-- Both value braidings recover the original entire identity-labelled operator coefficient. -/
theorem coefficientAction_fromRepresentation (X : Representation T) (a n : I) :
    coefficientAction (fromRepresentation X) a n =
      representationLeg X a n (a ⊗ n) (𝟙 (a ⊗ n)) := by
  let A := representationObject X n
  let P := (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a
  change (β_ A P).hom ≫ representationCoefficient X a n = _
  rw [representationCoefficient_eq, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- Every whole labelled coefficient is recovered, including its original target-index map. -/
theorem actionLeg_fromRepresentation (X : Representation T) (a n k : I) (f : a ⊗ n ⟶ k) :
    actionLeg (fromRepresentation X) a n k f = representationLeg X a n k f := by
  have ht := representationLeg_target X a n (a ⊗ n) k (𝟙 (a ⊗ n)) f
  simp only [Category.id_comp] at ht
  have hc := coefficientAction_fromRepresentation X a n
  exact (congrArg (fun t => t ≫ (ordinaryDiagram X).map f) hc).trans ht

/-- The complete operator Hom action is recovered by the original preserved coend universal property. -/
theorem to_from_action (X : Representation T) (n k : I) :
    operatorAction (fromRepresentation X) n k = representationAction X n k := by
  apply (isColimitOfPreserves (tensorLeft (representationObject X n))
    (colimit.isColimit (diagram T n k))).hom_ext
  intro q
  exact (generator_operatorAction (fromRepresentation X) q.left n k q.hom).trans
    (actionLeg_fromRepresentation X q.left n k q.hom)

end CategoryTheory.Spectra.Symmetric.OperatorCoend
