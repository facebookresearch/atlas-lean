/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorCoefficientLaws

/-!
# Reconstructing the complete ordinary sphere module from the genuine operator

Both original finite-index arrows act naturally on all tensor-power
coefficients. The coefficient unit and associativity are derived from
the actual enriched operator, before constructing the ordinary Day module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped ExternalProduct CategoryTheory.MonObj

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] [MonoidalClosed V]
  {T : V}

/-- Both complete original finite-index arrows act on the whole reconstructed coefficient. -/
theorem representationCoefficient_twoInputs (X : Representation T) {a b n k : I}
    (f : a ⟶ b) (g : n ⟶ k) :
    ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map f ⊗ₘ (ordinaryDiagram X).map g) ≫
      representationCoefficient X b k =
      representationCoefficient X a n ≫ (ordinaryDiagram X).map (f ⊗ₘ g) := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let r : representationObject X n ⟶ representationObject X k := (ordinaryDiagram X).map g
  let u : representationObject X (a ⊗ n) ⟶ representationObject X (b ⊗ n) :=
    (ordinaryDiagram X).map (f ▷ n)
  let v : representationObject X (b ⊗ n) ⟶ representationObject X (b ⊗ k) :=
    (ordinaryDiagram X).map (b ◁ g)
  let t : representationObject X (a ⊗ n) ⟶ representationObject X (b ⊗ k) :=
    (ordinaryDiagram X).map (f ⊗ₘ g)
  have hn : (P.obj b ◁ r) ≫ representationCoefficient X b k = representationCoefficient X b n ≫ v :=
    representationCoefficient_index X b g
  have hc : (P.map f ▷ representationObject X n) ≫ representationCoefficient X b n =
      representationCoefficient X a n ≫ u := representationCoefficient_natural X f n
  have hm : u ≫ v = t :=
    ((ordinaryDiagram X).map_comp (f ▷ n) (b ◁ g)).symm.trans
      (congrArg (ordinaryDiagram X).map (tensorHom_def f g).symm)
  change (P.map f ⊗ₘ r) ≫ representationCoefficient X b k = representationCoefficient X a n ≫ t
  rw [tensorHom_def, Category.assoc, hn, ← Category.assoc, hc, Category.assoc, hm]

variable [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The recovered action is the complete two-variable natural transformation on the original index. -/
def reconstructedAction (X : Representation T) :
    (genericSphereDayMonoid T).X.functor ⊠ ordinaryDiagram X ⟶ tensor I ⋙ ordinaryDiagram X where
  app q := representationCoefficient X q.1 q.2
  naturality := by
    rintro ⟨a, n⟩ ⟨b, k⟩ ⟨f, g⟩
    let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
    let r : representationObject X n ⟶ representationObject X k := (ordinaryDiagram X).map g
    have hs : ((genericSphereDayMonoid T).X.functor ⊠ ordinaryDiagram X).map (f, g) = P.map f ⊗ₘ r := by
      simp only [externalProductBifunctor_obj_map]
      exact (tensorHom_def (P.map f) r).symm
    have ht : (tensor I ⋙ ordinaryDiagram X).map (f, g) = (ordinaryDiagram X).map (f ⊗ₘ g) := rfl
    exact (congrArg (fun t => t ≫ representationCoefficient X b k) hs).trans
      ((representationCoefficient_twoInputs X f g).trans
        (congrArg (fun t => representationCoefficient X a n ≫ t) ht).symm)

/-- Every genuine operator representation gives the complete original ordinary sphere-module data. -/
def fromRepresentation (X : Representation T) : SphereData T where
  diagram := ordinaryDiagram X
  action := reconstructedAction X
  unit n := by
    let A := representationObject X n
    let z : (𝟙_ V) ⊗ A ⟶ representationObject X ((𝟙_ I) ⊗ n) := representationCoefficient X (𝟙_ I) n
    have hs := congrArg (fun t => (t ▷ A) ≫ z) (genericSphereDayMonoid_unit T)
    have hi : (𝟙 (𝟙_ V) ▷ A) ≫ z = z := by rw [id_whiskerRight, Category.id_comp]
    exact hs.trans (hi.trans (representationCoefficient_unit X n))
  assoc a b n := by
    have hs := congrArg
      (fun t => (t ▷ representationObject X n) ≫ representationCoefficient X (a ⊗ b) n)
      (genericSphereDayMonoid_multiplication T a b)
    exact hs.trans (representationCoefficient_assoc X a b n)

/-- Every original object is retained by the reconstructed sphere-module diagram. -/
theorem fromRepresentation_obj (X : Representation T) (n : I) :
    (fromRepresentation X).diagram.obj n = representationObject X n := rfl

/-- Every original index map is retained by the reconstructed sphere-module diagram. -/
theorem fromRepresentation_map (X : Representation T) {n k : I} (f : n ⟶ k) :
    (fromRepresentation X).diagram.map f = (ordinaryDiagram X).map f := rfl

/-- Every full original coefficient is retained by the reconstructed sphere-module action. -/
theorem fromRepresentation_coefficient (X : Representation T) (a n : I) :
    coefficient (fromRepresentation X) a n = representationCoefficient X a n := rfl

end CategoryTheory.Spectra.Symmetric.OperatorCoend
