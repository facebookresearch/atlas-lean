/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.MorphismProperty.LiftingTest
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
import MathlibExt.CategoryTheory.MorphismProperty.Factorization.FactorArrowFunctors
import MathlibExt.CategoryTheory.SmallObject.FactorizationAccessibility
import MathlibExt.CategoryTheory.Presentable.LiftingTest

/-!
# Weak-equivalence tests from the same original factors

The test is the original J right-factor functor followed by the existing
tagged lifting test for the original I family. Its raw diagonals and
squares retain the original middle objects and both factor maps.

Detection uses the actual model laws and no local-presentability
assumption. Every original factor, generator and size universe remains
unchanged.
-/

set_option autoImplicit false
noncomputable section

universe w uC vC

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open Cardinal

namespace HomotopicalAlgebra.CofibrantGenerationData

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- The original J right factor followed by the actual original I lifting test. -/
def weakLiftingTest (d : CofibrantGenerationData C κ) :
    Arrow C ⥤ Arrow (Type w) := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  exact d.fibrantFactorizationData.originalRightFactorFunctor ⋙
    LiftingTest.smallFunctor.{w} (fun i : d.I.toSet ↦ i.1)

section OriginalFunctions

variable (d : CofibrantGenerationData C κ)

/-- The entire test functor is the literal composite of the two original functors. -/
theorem weakLiftingTest_eq :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    d.weakLiftingTest = d.fibrantFactorizationData.originalRightFactorFunctor ⋙
      LiftingTest.smallFunctor.{w} (fun i : d.I.toSet ↦ i.1) := rfl

/-- Every tested object is the original J right factor, with its original middle object. -/
theorem weakLiftingTest_obj (p : Arrow C) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    d.weakLiftingTest.obj p =
      (LiftingTest.smallFunctor.{w} (fun i : d.I.toSet ↦ i.1)).obj
        (Arrow.mk (d.fibrantFactorizationData.p.app p)) := rfl

/-- Every tested square uses the original J middle map and original right endpoint map. -/
theorem weakLiftingTest_map {p q : Arrow C} (τ : p ⟶ q) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    d.weakLiftingTest.map τ =
      (LiftingTest.smallFunctor.{w} (fun i : d.I.toSet ↦ i.1)).map
        (Arrow.homMk (f := Arrow.mk (d.fibrantFactorizationData.p.app p))
          (g := Arrow.mk (d.fibrantFactorizationData.p.app q))
          (d.fibrantFactorizationData.Z.map τ) τ.right
          (d.fibrantFactorizationData.p.naturality τ)) := rfl

/-- The whole normalized object function retains every original tag and diagonal. -/
theorem weakLiftingTest_hom_function (p : Arrow C) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    (d.weakLiftingTest.obj p).hom ∘
        LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p)) =
      LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p)) ∘
        LiftingTest.liftToSquare (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p)) := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  exact LiftingTest.smallFunctor_hom_function.{w}
    (fun i : d.I.toSet ↦ i.1) (Arrow.mk (d.fibrantFactorizationData.p.app p))

/-- The full normalized source map retains the same original J middle map. -/
theorem weakLiftingTest_map_left_function {p q : Arrow C} (τ : p ⟶ q) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    (d.weakLiftingTest.map τ).left ∘
        LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p)) =
      LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app q)) ∘
        LiftingTest.rawLiftMap (fun i : d.I.toSet ↦ i.1)
          (d.fibrantFactorizationData.originalRightFactorFunctor.map τ) := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  exact LiftingTest.smallFunctor_map_left_function.{w}
    (fun i : d.I.toSet ↦ i.1) (d.fibrantFactorizationData.originalRightFactorFunctor.map τ)

/-- The full normalized target map retains every original native J-factor square. -/
theorem weakLiftingTest_map_right_function {p q : Arrow C} (τ : p ⟶ q) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    (d.weakLiftingTest.map τ).right ∘
        LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p)) =
      LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app q)) ∘
        LiftingTest.rawSquareMap (fun i : d.I.toSet ↦ i.1)
          (d.fibrantFactorizationData.originalRightFactorFunctor.map τ) := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  exact LiftingTest.smallFunctor_map_right_function.{w}
    (fun i : d.I.toSet ↦ i.1) (d.fibrantFactorizationData.originalRightFactorFunctor.map τ)

/-- Decoding the full normalized test recovers the same original square function. -/
theorem weakLiftingTest_decoded_hom_function (p : Arrow C) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    (LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm ∘
        (d.weakLiftingTest.obj p).hom =
      LiftingTest.liftToSquare (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p)) ∘
        (LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  funext z
  exact (LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
    (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm_apply_apply _

/-- Decoding the whole source map recovers the same tagged original middle action. -/
theorem weakLiftingTest_decoded_map_left_function {p q : Arrow C} (τ : p ⟶ q) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    (LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app q))).symm ∘
        (d.weakLiftingTest.map τ).left =
      LiftingTest.rawLiftMap (fun i : d.I.toSet ↦ i.1)
          (d.fibrantFactorizationData.originalRightFactorFunctor.map τ) ∘
        (LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  funext z
  exact (LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
    (Arrow.mk (d.fibrantFactorizationData.p.app q))).symm_apply_apply _

/-- Decoding the whole target map recovers the same tagged original native squares. -/
theorem weakLiftingTest_decoded_map_right_function {p q : Arrow C} (τ : p ⟶ q) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    (LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app q))).symm ∘
        (d.weakLiftingTest.map τ).right =
      LiftingTest.rawSquareMap (fun i : d.I.toSet ↦ i.1)
          (d.fibrantFactorizationData.originalRightFactorFunctor.map τ) ∘
        (LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  funext z
  exact (LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
    (Arrow.mk (d.fibrantFactorizationData.p.app q))).symm_apply_apply _

/-- Encoding and decoding retains the entire original tagged square. -/
theorem weakLiftingTest_original_square (p : Arrow C)
    (z : LiftingTest.RawLifts (fun i : d.I.toSet ↦ i.1)
      (Arrow.mk (d.fibrantFactorizationData.p.app p))) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    (LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
      (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm
      ((d.weakLiftingTest.obj p).hom
        (LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p)) z)) =
      LiftingTest.liftToSquare (fun i : d.I.toSet ↦ i.1)
        (Arrow.mk (d.fibrantFactorizationData.p.app p)) z := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  have h := congrFun (d.weakLiftingTest_hom_function p) z
  dsimp only [Function.comp_apply] at h
  exact (congrArg
    (LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
      (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm h).trans
    ((LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
      (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm_apply_apply _)

/-- The original generator tag survives the full working-size test and decoding. -/
theorem weakLiftingTest_original_tag (p : Arrow C) (i : d.I.toSet)
    (l : i.1.right ⟶ d.fibrantFactorizationData.Z.obj p) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    ((LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
      (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm
      ((d.weakLiftingTest.obj p).hom
        (LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p)) ⟨i, l⟩))).1 = i := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  exact congrArg Sigma.fst (d.weakLiftingTest_original_square p ⟨i, l⟩)

/-- The decoded top is the original I generator followed by the original diagonal. -/
theorem weakLiftingTest_original_top (p : Arrow C) (i : d.I.toSet)
    (l : i.1.right ⟶ d.fibrantFactorizationData.Z.obj p) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    HEq (((LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
      (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm
      ((d.weakLiftingTest.obj p).hom
        (LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p)) ⟨i, l⟩))).2.left)
      (i.1.hom ≫ l) := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  have project {a b : LiftingTest.RawSquares (fun i : d.I.toSet ↦ i.1)
      (Arrow.mk (d.fibrantFactorizationData.p.app p))}
      (h : a = b) : HEq a.2.left b.2.left := by
    cases h
    rfl
  exact project (d.weakLiftingTest_original_square p ⟨i, l⟩)

/-- The decoded bottom is the original diagonal followed by the original J projection. -/
theorem weakLiftingTest_original_bottom (p : Arrow C) (i : d.I.toSet)
    (l : i.1.right ⟶ d.fibrantFactorizationData.Z.obj p) :
    let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
    let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
    HEq (((LiftingTest.squaresEquiv.{w} (fun i : d.I.toSet ↦ i.1)
      (Arrow.mk (d.fibrantFactorizationData.p.app p))).symm
      ((d.weakLiftingTest.obj p).hom
        (LiftingTest.liftsEquiv.{w} (fun i : d.I.toSet ↦ i.1)
          (Arrow.mk (d.fibrantFactorizationData.p.app p)) ⟨i, l⟩))).2.right)
      (l ≫ d.fibrantFactorizationData.p.app p) := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  have project {a b : LiftingTest.RawSquares (fun i : d.I.toSet ↦ i.1)
      (Arrow.mk (d.fibrantFactorizationData.p.app p))}
      (h : a = b) : HEq a.2.right b.2.right := by
    cases h
    rfl
  exact project (d.weakLiftingTest_original_square p ⟨i, l⟩)

end OriginalFunctions

section Detection

variable (d : CofibrantGenerationData C κ)

/-- The same original J right factor is weak exactly when the original arrow is weak. -/
theorem fibrantFactorizationData_p_weak_iff (p : Arrow C) :
    weakEquivalences C (d.fibrantFactorizationData.p.app p) ↔
      weakEquivalences C p.hom := by
  have hi : weakEquivalences C (d.fibrantFactorizationData.i.app p) :=
    (d.fibrantFactorizationData.hi p).2
  constructor
  · intro hp
    simpa only [d.fibrantFactorizationData.fac_app] using
      (weakEquivalences C).comp_mem _ _ hi hp
  · intro hp
    apply (weakEquivalences C).of_precomp
      (d.fibrantFactorizationData.i.app p) (d.fibrantFactorizationData.p.app p) hi
    rwa [d.fibrantFactorizationData.fac_app]

/-- Original I-right lifting of the same J projection is exactly original weakness. -/
theorem fibrantFactorizationData_p_I_rlp_iff (p : Arrow C) :
    d.I.rlp (d.fibrantFactorizationData.p.app p) ↔ weakEquivalences C p.hom := by
  rw [d.I_rlp]
  constructor
  · intro h
    exact (d.fibrantFactorizationData_p_weak_iff p).mp h.2
  · intro h
    exact ⟨d.fibrantFactorizationData.hp p,
      (d.fibrantFactorizationData_p_weak_iff p).mpr h⟩

/-- Surjectivity of the original composite tests the same original I right class. -/
theorem weakLiftingTest_surjective_iff_I_rlp (p : Arrow C) :
    Function.Surjective (d.weakLiftingTest.obj p).hom ↔
      d.I.rlp (d.fibrantFactorizationData.p.app p) := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  rw [d.weakLiftingTest_obj p, LiftingTest.smallFunctor_surjective_iff.{w}]
  change (ofHoms d.I.homFamily).rlp (d.fibrantFactorizationData.p.app p) ↔ _
  rw [ofHoms_homFamily]

/-- The actual small test is surjective exactly for the actual model weak class. -/
theorem weakLiftingTest_surjective_iff (p : Arrow C) :
    Function.Surjective (d.weakLiftingTest.obj p).hom ↔ weakEquivalences C p.hom :=
  (d.weakLiftingTest_surjective_iff_I_rlp p).trans
    (d.fibrantFactorizationData_p_I_rlp_iff p)

/-- The whole original weak-arrow predicate is the actual test-surjectivity predicate. -/
theorem weakLiftingTest_weak_predicate :
    (fun p : Arrow C ↦ weakEquivalences C p.hom) =
      (fun p : Arrow C ↦ Function.Surjective (d.weakLiftingTest.obj p).hom) := by
  funext p
  exact propext (d.weakLiftingTest_surjective_iff p).symm

end Detection

section Accessibility

variable [HasColimitsOfSize.{w, w} C] (d : CofibrantGenerationData C κ)
  (χ : Cardinal.{w}) [Fact χ.IsRegular]

/-- Both original endpoint bounds preserve the same original composite at χ. -/
theorem weakLiftingTest_isCardinalAccessible
    [∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ]
    [∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ]
    [∀ j : d.J.toSet, IsCardinalPresentable j.1.left χ]
    [∀ j : d.J.toSet, IsCardinalPresentable j.1.right χ] :
    d.weakLiftingTest.IsCardinalAccessible χ := by
  let _ : LocallySmall.{w} C := d.I_smallObject.locallySmall
  let _ : d.I.IsSmall.{w} := d.I_smallObject.isSmall
  let _ : d.fibrantFactorizationData.originalRightFactorFunctor.IsCardinalAccessible χ :=
    d.fibrantFactorizationData_right_isCardinalAccessible χ
  let _ : (LiftingTest.smallFunctor.{w} (fun i : d.I.toSet ↦ i.1)).IsCardinalAccessible χ :=
    CategoryTheory.Presentable.LiftingTest.smallFunctor_isCardinalAccessible
      (fun i : d.I.toSet ↦ i.1) χ
  change (d.fibrantFactorizationData.originalRightFactorFunctor ⋙
    LiftingTest.smallFunctor.{w} (fun i : d.I.toSet ↦ i.1)).IsCardinalAccessible χ
  infer_instance

end Accessibility

/-- Extend the original common-rank witness by the same composite, without choosing new factors. -/
theorem exists_common_weak_test_accessibility_cardinal
    (d : CofibrantGenerationData C κ) (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    ∃ (χ : Cardinal.{w}) (hχ : Fact χ.IsRegular),
      let _ : Fact χ.IsRegular := hχ
      ℵ₀ < χ ∧ κLP ≤ χ ∧ κ ≤ χ ∧ IsCardinalLocallyPresentable C χ ∧
        (∀ i : d.I.toSet,
          IsCardinalPresentable i.1.left χ ∧ IsCardinalPresentable i.1.right χ) ∧
        (∀ j : d.J.toSet,
          IsCardinalPresentable j.1.left χ ∧ IsCardinalPresentable j.1.right χ) ∧
        d.cofibrantFactorizationData.Z.IsCardinalAccessible χ ∧
        d.fibrantFactorizationData.Z.IsCardinalAccessible χ ∧
        d.cofibrantFactorizationData.originalLeftFactorFunctor.IsCardinalAccessible χ ∧
        d.cofibrantFactorizationData.originalRightFactorFunctor.IsCardinalAccessible χ ∧
        d.fibrantFactorizationData.originalLeftFactorFunctor.IsCardinalAccessible χ ∧
        d.fibrantFactorizationData.originalRightFactorFunctor.IsCardinalAccessible χ ∧
        d.weakLiftingTest.IsCardinalAccessible χ := by
  obtain ⟨χ, hχ, hω, hLP, hκ, hC, hI, hJ, hIZ, hJZ, hIL, hIR, hJL, hJR⟩ :=
    d.exists_common_factor_accessibility_cardinal κLP
  let _ : Fact χ.IsRegular := hχ
  let _ : IsCardinalLocallyPresentable C χ := hC
  let _ : ∀ i : d.I.toSet, IsCardinalPresentable i.1.left χ := fun i ↦ (hI i).1
  let _ : ∀ i : d.I.toSet, IsCardinalPresentable i.1.right χ := fun i ↦ (hI i).2
  let _ : ∀ j : d.J.toSet, IsCardinalPresentable j.1.left χ := fun j ↦ (hJ j).1
  let _ : ∀ j : d.J.toSet, IsCardinalPresentable j.1.right χ := fun j ↦ (hJ j).2
  exact ⟨χ, hχ, hω, hLP, hκ, hC, hI, hJ, hIZ, hJZ, hIL, hIR, hJL, hJR,
    d.weakLiftingTest_isCardinalAccessible χ⟩

end HomotopicalAlgebra.CofibrantGenerationData
