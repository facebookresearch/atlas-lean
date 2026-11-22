/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorRepresentationLegs

/-!
# The original sphere-module laws recovered from the enriched operator

The whole identity-labelled generators give the original coefficient unit
and associativity. The source coefficient multiplication and index maps
are retained through every value braiding.
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
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] [MonoidalClosed V]
  {T : V}

/-- All original identity-labelled coefficient actions associate through the actual index associator. -/
theorem representationIdentity_assoc (X : Representation T) (a b n : I) :
    (α_ (representationObject X n) ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b)).inv ≫
      (representationLeg X a n (a ⊗ n) (𝟙 (a ⊗ n)) ▷
        (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b) ≫
      representationLeg X b (a ⊗ n) (b ⊗ (a ⊗ n)) (𝟙 (b ⊗ (a ⊗ n))) =
    (representationObject X n ◁ reverseMultiplication T a b) ≫
      representationLeg X (b ⊗ a) n ((b ⊗ a) ⊗ n) (𝟙 ((b ⊗ a) ⊗ n)) ≫
      (ordinaryDiagram X).map (α_ b a n).hom := by
  have h := representationLeg_assoc X a b n (a ⊗ n) (b ⊗ (a ⊗ n))
    (𝟙 (a ⊗ n)) (𝟙 (b ⊗ (a ⊗ n)))
  have ht := representationLeg_target X (b ⊗ a) n ((b ⊗ a) ⊗ n) (b ⊗ (a ⊗ n))
    (𝟙 ((b ⊗ a) ⊗ n)) (α_ b a n).hom
  simp only [whiskerLeft_id, Category.comp_id] at h
  simp only [Category.id_comp] at ht
  exact h.trans (congrArg (fun t => (representationObject X n ◁ reverseMultiplication T a b) ≫ t) ht.symm)

/-- The full empty coefficient followed by the original index unitor is the original value unitor. -/
theorem representationCoefficient_unit_hom (X : Representation T) (n : I) :
    representationCoefficient X (𝟙_ I) n ≫ (ordinaryDiagram X).map (λ_ n).hom =
      (λ_ (representationObject X n)).hom := by
  let A := representationObject X n
  let B := representationObject X ((𝟙_ I) ⊗ n)
  let c : (𝟙_ V) ⊗ A ⟶ B := representationCoefficient X (𝟙_ I) n
  let g : A ⊗ (𝟙_ V) ⟶ B := representationLeg X (𝟙_ I) n ((𝟙_ I) ⊗ n) (𝟙 ((𝟙_ I) ⊗ n))
  let r : B ⟶ A := (ordinaryDiagram X).map (λ_ n).hom
  have hc : c = (β_ (𝟙_ V) A).hom ≫ g := representationCoefficient_eq X (𝟙_ I) n
  have hg : g ≫ r = (ρ_ A).hom := by
    have h := representationLeg_target X (𝟙_ I) n ((𝟙_ I) ⊗ n) n (𝟙 ((𝟙_ I) ⊗ n)) (λ_ n).hom
    simp only [Category.id_comp] at h
    exact h.trans (representationLeg_unit X n)
  have hb : (β_ (𝟙_ V) A).hom ≫ (ρ_ A).hom = (λ_ A).hom := by
    rw [braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change c ≫ r = (λ_ A).hom
  rw [hc, Category.assoc, hg]
  exact hb

/-- The entire original empty coefficient is recovered with both original unitors. -/
theorem representationCoefficient_unit (X : Representation T) (n : I) :
    representationCoefficient X (𝟙_ I) n =
      (λ_ (representationObject X n)).hom ≫ (ordinaryDiagram X).map (λ_ n).inv := by
  let A := representationObject X n
  let B := representationObject X ((𝟙_ I) ⊗ n)
  let c : (𝟙_ V) ⊗ A ⟶ B := representationCoefficient X (𝟙_ I) n
  let r : B ⟶ A := (ordinaryDiagram X).map (λ_ n).hom
  let s : A ⟶ B := (ordinaryDiagram X).map (λ_ n).inv
  have hi : r ≫ s = 𝟙 B := ((ordinaryDiagram X).mapIso (λ_ n)).hom_inv_id
  have hu : c ≫ r = (λ_ A).hom := representationCoefficient_unit_hom X n
  have h := congrArg (fun t => t ≫ s) hu
  change c = (λ_ A).hom ≫ s
  simpa only [Category.assoc, hi, Category.comp_id] using h

/-- Both original full coefficient routes retain the source multiplication and target associator. -/
theorem representationCoefficient_assoc_hom (X : Representation T) (a b n : I) :
    (α_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b) (representationObject X n)).hom ≫
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ representationCoefficient X b n ≫
      representationCoefficient X a (b ⊗ n) =
    coefficientMultiplication T a b ▷ representationObject X n ≫
      representationCoefficient X (a ⊗ b) n ≫ (ordinaryDiagram X).map (α_ a b n).hom := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let A := P.obj a
  let B := P.obj b
  let N := representationObject X n
  let Y := representationObject X (b ⊗ n)
  let Z := representationObject X ((a ⊗ b) ⊗ n)
  let K := representationObject X (a ⊗ (b ⊗ n))
  let cb : B ⊗ N ⟶ Y := representationCoefficient X b n
  let ca : A ⊗ Y ⟶ K := representationCoefficient X a (b ⊗ n)
  let cab : P.obj (a ⊗ b) ⊗ N ⟶ Z := representationCoefficient X (a ⊗ b) n
  let gb : N ⊗ B ⟶ Y := representationLeg X b n (b ⊗ n) (𝟙 (b ⊗ n))
  let ga : Y ⊗ A ⟶ K := representationLeg X a (b ⊗ n) (a ⊗ (b ⊗ n)) (𝟙 (a ⊗ (b ⊗ n)))
  let gab : N ⊗ P.obj (a ⊗ b) ⟶ Z :=
    representationLeg X (a ⊗ b) n ((a ⊗ b) ⊗ n) (𝟙 ((a ⊗ b) ⊗ n))
  let m : A ⊗ B ⟶ P.obj (a ⊗ b) := coefficientMultiplication T a b
  let r : Z ⟶ K := (ordinaryDiagram X).map (α_ a b n).hom
  have hcb : cb = (β_ B N).hom ≫ gb := representationCoefficient_eq X b n
  have hca : ca = (β_ A Y).hom ≫ ga := representationCoefficient_eq X a (b ⊗ n)
  have hcab : cab = (β_ (P.obj (a ⊗ b)) N).hom ≫ gab := representationCoefficient_eq X (a ⊗ b) n
  have hn : (A ◁ gb) ≫ (β_ A Y).hom = (β_ A (N ⊗ B)).hom ≫ (gb ▷ A) :=
    braiding_naturality_right A gb
  have hAssoc : (α_ N B A).inv ≫ gb ▷ A ≫ ga =
      (N ◁ reverseMultiplication T b a) ≫ gab ≫ r := representationIdentity_assoc X b a n
  have hSwap : (β_ (B ⊗ A) N).hom ≫ (N ◁ (β_ B A).hom) =
      ((β_ B A).hom ▷ N) ≫ (β_ (A ⊗ B) N).hom :=
    (braiding_naturality_left (β_ B A).hom N).symm
  have hSym : ((β_ A B).hom ▷ N) ≫ ((β_ B A).hom ▷ N) = 𝟙 ((A ⊗ B) ⊗ N) := by
    rw [← comp_whiskerRight, SymmetricCategory.symmetry, id_whiskerRight]
  have hMult : (β_ (A ⊗ B) N).hom ≫ (N ◁ m) = (m ▷ N) ≫ (β_ (P.obj (a ⊗ b)) N).hom :=
    (braiding_naturality_left m N).symm
  change (α_ A B N).hom ≫ (A ◁ cb) ≫ ca = (m ▷ N) ≫ cab ≫ r
  rw [hcb, hca]
  simp only [whiskerLeft_comp, Category.assoc]
  slice_lhs 3 4 => rw [hn]
  simp only [Category.assoc]
  slice_lhs 1 3 => rw [← tripleReverse]
  simp only [Category.assoc]
  slice_lhs 3 5 => rw [hAssoc]
  simp only [reverseMultiplication, whiskerLeft_comp, Category.assoc]
  slice_lhs 2 3 => rw [hSwap]
  simp only [Category.assoc]
  slice_lhs 1 2 => rw [hSym]
  rw [Category.id_comp]
  slice_lhs 1 2 => rw [hMult]
  rw [hcab]
  simp only [Category.assoc]

/-- The recovered whole coefficients satisfy the exact original external module associativity. -/
theorem representationCoefficient_assoc (X : Representation T) (a b n : I) :
    coefficientMultiplication T a b ▷ representationObject X n ≫ representationCoefficient X (a ⊗ b) n =
    (α_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b) (representationObject X n)).hom ≫
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ representationCoefficient X b n ≫
      representationCoefficient X a (b ⊗ n) ≫ (ordinaryDiagram X).map (α_ a b n).inv := by
  let r : representationObject X ((a ⊗ b) ⊗ n) ⟶ representationObject X (a ⊗ (b ⊗ n)) :=
    (ordinaryDiagram X).map (α_ a b n).hom
  let s : representationObject X (a ⊗ (b ⊗ n)) ⟶ representationObject X ((a ⊗ b) ⊗ n) :=
    (ordinaryDiagram X).map (α_ a b n).inv
  have hi : r ≫ s = 𝟙 (representationObject X ((a ⊗ b) ⊗ n)) :=
    ((ordinaryDiagram X).mapIso (α_ a b n)).hom_inv_id
  have ha : (α_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b) (representationObject X n)).hom ≫
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ representationCoefficient X b n ≫
      representationCoefficient X a (b ⊗ n) =
      coefficientMultiplication T a b ▷ representationObject X n ≫
        representationCoefficient X (a ⊗ b) n ≫ r := representationCoefficient_assoc_hom X a b n
  have h := congrArg (fun t => t ≫ s) ha.symm
  change coefficientMultiplication T a b ▷ representationObject X n ≫ representationCoefficient X (a ⊗ b) n =
    (α_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b) (representationObject X n)).hom ≫
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ◁ representationCoefficient X b n ≫
      representationCoefficient X a (b ⊗ n) ≫ s
  simpa only [Category.assoc, hi, Category.comp_id] using h

end CategoryTheory.Spectra.Symmetric.OperatorCoend
