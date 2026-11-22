/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorUnit

/-!
# Original finite-index arrows and whole sphere operator generators

Every original finite-index arrow enters the operator through its entire
degree-zero coefficient. Precomposition and postcomposition formulas retain
the complete finite labels and tensor-power coefficient objects.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

/-- Every original postcomposition label retains the original index left unitor. -/
theorem arrowLabel_right (a n k l : I) (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    compositionLabel n k l (CostructuredArrow.mk (Y := a) f)
      (CostructuredArrow.mk (Y := 𝟙_ I) ((λ_ k).hom ≫ g)) =
    ((λ_ a).hom ▷ n) ≫ f ≫ g := by
  have hi : (α_ (𝟙_ I) a n).hom ≫ ((𝟙_ I) ◁ f) ≫ (λ_ k).hom =
      ((λ_ a).hom ▷ n) ≫ f := identityLabel_right a n k f
  change (α_ (𝟙_ I) a n).hom ≫ ((𝟙_ I) ◁ f) ≫ (λ_ k).hom ≫ g = _
  simpa only [Category.assoc] using congrArg (fun t => t ≫ g) hi

/-- Every original precomposition label retains the original index right unitor. -/
theorem arrowLabel_left (a n k l : I) (h : n ⟶ k) (f : a ⊗ k ⟶ l) :
    compositionLabel n k l (CostructuredArrow.mk (Y := 𝟙_ I) ((λ_ n).hom ≫ h))
      (CostructuredArrow.mk (Y := a) f) =
    ((ρ_ a).hom ▷ n) ≫ (a ◁ h) ≫ f := by
  change (α_ a (𝟙_ I) n).hom ≫ (a ◁ ((λ_ n).hom ≫ h)) ≫ f = _
  simp only [whiskerLeft_comp, Category.assoc]
  slice_lhs 1 2 => rw [triangle]
  simp only [Category.assoc]

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]

/-- An original index arrow is the full degree-zero sphere coefficient at its unitor label. -/
def arrow (T : V) {n k : I} (f : n ⟶ k) : 𝟙_ V ⟶ Hom T n k :=
  generator T (𝟙_ I) n k ((λ_ n).hom ≫ f)

/-- The original index identity is the actual operator identity. -/
theorem arrow_id (T : V) (n : I) : arrow T (𝟙 n) = identity T n := by
  exact congrArg (generator T (𝟙_ I) n n) (Category.comp_id _)

variable [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/-- Every complete coefficient generator postcomposes by the original whole index arrow. -/
theorem generator_arrow (T : V) (a n k l : I) (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    (generator T a n k f ⊗ₘ arrow T g) ≫ composition T n k l =
      (ρ_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)).hom ≫
        generator T a n l (f ≫ g) := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let j : P.obj a ⟶ Hom T n l := generator T a n l (f ≫ g)
  let z : P.obj ((𝟙_ I) ⊗ a) ⟶ Hom T n l := generator T ((𝟙_ I) ⊗ a) n l
    (compositionLabel n k l (CostructuredArrow.mk (Y := a) f)
      (CostructuredArrow.mk (Y := 𝟙_ I) ((λ_ k).hom ≫ g)))
  let m : (𝟙_ V) ⊗ P.obj a ⟶ P.obj ((𝟙_ I) ⊗ a) := (tensorPowObj_add T 0 a.of.len).inv
  have hComp : (generator T a n k f ⊗ₘ arrow T g) ≫ composition T n k l =
      (β_ (P.obj a) (𝟙_ V)).hom ≫ m ≫ z :=
    generator_composition T a (𝟙_ I) n k l f ((λ_ k).hom ≫ g)
  have hLabel : z = P.map (λ_ a).hom ≫ j :=
    (congrArg (generator T ((𝟙_ I) ⊗ a) n l) (arrowLabel_right a n k l f g)).trans
      (generator_relation T (λ_ a).hom (f ≫ g)).symm
  have hPower : m ≫ P.map (λ_ a).hom = (λ_ (P.obj a)).hom :=
    genericSphereSequence_block_unit_left T a
  have hBraid : (β_ (P.obj a) (𝟙_ V)).hom ≫ (λ_ (P.obj a)).hom = (ρ_ (P.obj a)).hom := by
    rw [braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hMiddle : (β_ (P.obj a) (𝟙_ V)).hom ≫ m ≫ z = (ρ_ (P.obj a)).hom ≫ j := by
    rw [hLabel, ← Category.assoc m, hPower, ← Category.assoc, hBraid]
  exact hComp.trans hMiddle

/-- Every complete coefficient generator precomposes by the original whole index arrow. -/
theorem arrow_generator (T : V) (a n k l : I) (h : n ⟶ k) (f : a ⊗ k ⟶ l) :
    (arrow T h ⊗ₘ generator T a k l f) ≫ composition T n k l =
      (λ_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)).hom ≫
        generator T a n l ((a ◁ h) ≫ f) := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let j : P.obj a ⟶ Hom T n l := generator T a n l ((a ◁ h) ≫ f)
  let z : P.obj (a ⊗ (𝟙_ I)) ⟶ Hom T n l := generator T (a ⊗ (𝟙_ I)) n l
    (compositionLabel n k l (CostructuredArrow.mk (Y := 𝟙_ I) ((λ_ n).hom ≫ h))
      (CostructuredArrow.mk (Y := a) f))
  let m : P.obj a ⊗ (𝟙_ V) ⟶ P.obj (a ⊗ (𝟙_ I)) := (tensorPowObj_add T a.of.len 0).inv
  have hComp : (arrow T h ⊗ₘ generator T a k l f) ≫ composition T n k l =
      (β_ (𝟙_ V) (P.obj a)).hom ≫ m ≫ z :=
    generator_composition T (𝟙_ I) a n k l ((λ_ n).hom ≫ h) f
  have hLabel : z = P.map (ρ_ a).hom ≫ j :=
    (congrArg (generator T (a ⊗ (𝟙_ I)) n l) (arrowLabel_left a n k l h f)).trans
      (generator_relation T (ρ_ a).hom ((a ◁ h) ≫ f)).symm
  have hPower : m ≫ P.map (ρ_ a).hom = (ρ_ (P.obj a)).hom :=
    genericSphereSequence_block_unit_right T a
  have hBraid : (β_ (𝟙_ V) (P.obj a)).hom ≫ (ρ_ (P.obj a)).hom = (λ_ (P.obj a)).hom := by
    rw [braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hMiddle : (β_ (𝟙_ V) (P.obj a)).hom ≫ m ≫ z = (λ_ (P.obj a)).hom ≫ j := by
    rw [hLabel, ← Category.assoc m, hPower, ← Category.assoc, hBraid]
  exact hComp.trans hMiddle

/-- Original index composites retain the actual enriched underlying-category composition. -/
theorem arrow_comp (T : V) {n k l : I} (f : n ⟶ k) (g : k ⟶ l) :
    (λ_ (𝟙_ V)).inv ≫ (arrow T f ⊗ₘ arrow T g) ≫ composition T n k l = arrow T (f ≫ g) := by
  let u : (𝟙_ V) ⟶ Hom T n k := arrow T f
  let v : (𝟙_ V) ⟶ Hom T k l := arrow T g
  have h0 : (u ⊗ₘ v) ≫ composition T n k l = (ρ_ (𝟙_ V)).hom ≫
      generator T (𝟙_ I) n l (((λ_ n).hom ≫ f) ≫ g) :=
    generator_arrow T (𝟙_ I) n k l ((λ_ n).hom ≫ f) g
  have h1 := congrArg (generator T (𝟙_ I) n l) (Category.assoc (λ_ n).hom f g)
  have h : (arrow T f ⊗ₘ arrow T g) ≫ composition T n k l =
      (ρ_ (𝟙_ V)).hom ≫ arrow T (f ≫ g) :=
    h0.trans (congrArg (fun t => (ρ_ (𝟙_ V)).hom ≫ t) h1)
  rw [h, ← unitors_equal, Iso.inv_hom_id_assoc]

/-- Every full identity-labelled coefficient factors through its original whole target arrow. -/
theorem generator_identity_arrow (T : V) (a n k : I) (f : a ⊗ n ⟶ k) :
    (generator T a n (a ⊗ n) (𝟙 (a ⊗ n)) ⊗ₘ arrow T f) ≫ composition T n (a ⊗ n) k =
      (ρ_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)).hom ≫ generator T a n k f := by
  simpa only [Category.id_comp] using generator_arrow T a n (a ⊗ n) k (𝟙 (a ⊗ n)) f

/-- Every full identity-labelled coefficient retains its original whole source arrow. -/
theorem arrow_generator_identity (T : V) (a n k : I) (h : n ⟶ k) :
    (arrow T h ⊗ₘ generator T a k (a ⊗ k) (𝟙 (a ⊗ k))) ≫ composition T n k (a ⊗ k) =
      (λ_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)).hom ≫
        generator T a n (a ⊗ k) (a ◁ h) := by
  simpa only [Category.comp_id] using arrow_generator T a n k (a ⊗ k) h (𝟙 (a ⊗ k))

/-- The whole original generator is recovered from its identity coefficient and target arrow. -/
theorem generator_factorization (T : V) (a n k : I) (f : a ⊗ n ⟶ k) :
    generator T a n k f =
      (ρ_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)).inv ≫
        (generator T a n (a ⊗ n) (𝟙 (a ⊗ n)) ⊗ₘ arrow T f) ≫ composition T n (a ⊗ n) k := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let j : P.obj a ⟶ Hom T n k := generator T a n k f
  let q : P.obj a ⟶ Hom T n (a ⊗ n) := generator T a n (a ⊗ n) (𝟙 (a ⊗ n))
  let e : (𝟙_ V) ⟶ Hom T (a ⊗ n) k := arrow T f
  have h : (q ⊗ₘ e) ≫ composition T n (a ⊗ n) k = (ρ_ (P.obj a)).hom ≫ j :=
    generator_identity_arrow T a n k f
  have h' := congrArg (fun t => (ρ_ (P.obj a)).inv ≫ t) h
  have hFinal : (ρ_ (P.obj a)).inv ≫ (q ⊗ₘ e) ≫ composition T n (a ⊗ n) k = j := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h'
  exact hFinal.symm

end CategoryTheory.Spectra.Symmetric.OperatorCoend
