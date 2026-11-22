/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua
-/

-- Author: @toskua

import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.SourceConstruction

/-!
# Choice independence of the original ordinary injective model

The original five class identities determine the entire model record. Thus
independently chosen coefficient ranks, generators and small-index equivalences
give the same model on the unchanged original functor category. The two working
cardinal universes are independent.

The native factor algorithms retain their choices. For each original whole
Arrow, their actual lifting properties construct comparisons between the two
factor triangles. Each comparison is a natural transformation of the original
diagrams, is objectwise weak, and preserves the original source and target
legs. Both comparison Arrow maps have literal identity maps at the unchanged
endpoints. The construction selects lifts separately for each original Arrow.

The model statement follows from the original injective class identities in
*Higher Topos Theory*, Proposition A.2.8.2. The factor comparisons use the
original model weak factorization systems and their actual lifting squares.
-/

set_option autoImplicit false
noncomputable section

universe w w' uD vD uC vC uK vK

namespace HomotopicalAlgebra.FunctorInjective

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

private theorem modelCategory_eq_of_classes {K : Type uK} [Category.{vK} K]
    (M N : ModelCategory K)
    (hF : M.categoryWithFibrations.fibrations = N.categoryWithFibrations.fibrations)
    (hC : M.categoryWithCofibrations.cofibrations = N.categoryWithCofibrations.cofibrations)
    (hW : M.categoryWithWeakEquivalences.weakEquivalences =
      N.categoryWithWeakEquivalences.weakEquivalences) : M = N := by
  have hF' : M.categoryWithFibrations = N.categoryWithFibrations :=
    congrArg (fun P : MorphismProperty K => (⟨P⟩ : CategoryWithFibrations K)) hF
  have hC' : M.categoryWithCofibrations = N.categoryWithCofibrations :=
    congrArg (fun P : MorphismProperty K => (⟨P⟩ : CategoryWithCofibrations K)) hC
  have hW' : M.categoryWithWeakEquivalences = N.categoryWithWeakEquivalences :=
    congrArg (fun P : MorphismProperty K => (⟨P⟩ : CategoryWithWeakEquivalences K)) hW
  cases M
  cases N
  cases hF'
  cases hC'
  cases hW'
  rfl

section OriginalModelChoices

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)
  {kappa' : Cardinal.{w'}} [Fact kappa'.IsRegular]
  [OrderBot kappa'.ord.ToType] (d' : CofibrantGenerationData C kappa')
  (kappaLP' : Cardinal.{w'}) [Fact kappaLP'.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP'] (s' : Functor.EssentialIndexData.{w'} D C)

/-- Independent original generation, rank and index choices give the same
actual model record on the original carrier, even in different working universes. -/
theorem originalSmithModelCategory_eq :
    originalSmithModelCategory d kappaLP s = originalSmithModelCategory d' kappaLP' s' := by
  apply modelCategory_eq_of_classes
  · exact (originalInjectiveModel_fibrations d kappaLP s).trans
      (originalInjectiveModel_fibrations d' kappaLP' s').symm
  · exact (originalInjectiveModel_cofibrations d kappaLP s).trans
      (originalInjectiveModel_cofibrations d' kappaLP' s').symm
  · exact (originalSmithModel_weakEquivalences d kappaLP s).trans
      (originalSmithModel_weakEquivalences d' kappaLP' s').symm

end OriginalModelChoices

private def factorComparisonLift {K : Type uK} [Category.{vK} K]
    (P : MorphismProperty K) (a b : FunctorialFactorizationData P P.rlp) (f : Arrow K) :
    (CommSq.mk (b.fac_app.trans a.fac_app.symm) :
      CommSq (b.i.app f) (a.i.app f) (b.p.app f) (a.p.app f)).LiftStruct := by
  letI : HasLiftingProperty (a.i.app f) (b.p.app f) := b.hp f _ (a.hi f)
  exact (CommSq.HasLift.exists_lift (sq :=
    (CommSq.mk (b.fac_app.trans a.fac_app.symm) :
      CommSq (b.i.app f) (a.i.app f) (b.p.app f) (a.p.app f)))).some

namespace SourceConstruction.CoefficientData

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] (c : SourceConstruction.CoefficientData.{w} C)
  (s : Functor.EssentialIndexData.{w} D C)
  (c' : SourceConstruction.CoefficientData.{w'} C)
  (s' : Functor.EssentialIndexData.{w'} D C)

/-- The conventional source entry is independent of its actual coefficient
witness and of the original small-index equivalence. -/
theorem modelCategory_eq : c.modelCategory s = c'.modelCategory s' := by
  let : Fact c.cardinal.IsRegular := c.regular
  let : OrderBot c.cardinal.ord.ToType := c.bottom
  let : IsCardinalLocallyPresentable C c.cardinal := c.locallyPresentable
  let : Fact c'.cardinal.IsRegular := c'.regular
  let : OrderBot c'.cardinal.ord.ToType := c'.bottom
  let : IsCardinalLocallyPresentable C c'.cardinal := c'.locallyPresentable
  exact originalSmithModelCategory_eq c.generation c.cardinal s c'.generation c'.cardinal s'

/-- The actual first lifting square compares the two original first middle diagrams. -/
def cofibrantComparison (f : Arrow (D ⥤ C)) :
    (c.cofibrantFactorizationData s).Z.obj f ⟶ (c'.cofibrantFactorizationData s').Z.obj f :=
  (factorComparisonLift ((cofibrations C).functorCategory D)
    (c.cofibrantFactorizationData s) (c'.cofibrantFactorizationData s') f).l

/-- The same comparison keeps both original first-factor triangle equations. -/
theorem cofibrantComparison_triangles (f : Arrow (D ⥤ C)) :
    (c.cofibrantFactorizationData s).i.app f ≫ c.cofibrantComparison s c' s' f =
        (c'.cofibrantFactorizationData s').i.app f ∧
      c.cofibrantComparison s c' s' f ≫ (c'.cofibrantFactorizationData s').p.app f =
        (c.cofibrantFactorizationData s).p.app f :=
  ⟨(factorComparisonLift ((cofibrations C).functorCategory D)
      (c.cofibrantFactorizationData s) (c'.cofibrantFactorizationData s') f).fac_left,
    (factorComparisonLift ((cofibrations C).functorCategory D)
      (c.cofibrantFactorizationData s) (c'.cofibrantFactorizationData s') f).fac_right⟩

/-- The actual second lifting square compares the two original second middle diagrams. -/
def fibrantComparison (f : Arrow (D ⥤ C)) :
    (c.fibrantFactorizationData s).Z.obj f ⟶ (c'.fibrantFactorizationData s').Z.obj f :=
  (factorComparisonLift ((trivialCofibrations C).functorCategory D)
    (c.fibrantFactorizationData s) (c'.fibrantFactorizationData s') f).l

/-- Both original second-factor triangle equations hold for that same comparison. -/
theorem fibrantComparison_triangles (f : Arrow (D ⥤ C)) :
    (c.fibrantFactorizationData s).i.app f ≫ c.fibrantComparison s c' s' f =
        (c'.fibrantFactorizationData s').i.app f ∧
      c.fibrantComparison s c' s' f ≫ (c'.fibrantFactorizationData s').p.app f =
        (c.fibrantFactorizationData s).p.app f :=
  ⟨(factorComparisonLift ((trivialCofibrations C).functorCategory D)
      (c.fibrantFactorizationData s) (c'.fibrantFactorizationData s') f).fac_left,
    (factorComparisonLift ((trivialCofibrations C).functorCategory D)
      (c.fibrantFactorizationData s) (c'.fibrantFactorizationData s') f).fac_right⟩

/-- The first comparison is weak on every original object, as both original
projections are weak and its right triangle commutes. -/
theorem cofibrantComparison_weak (f : Arrow (D ⥤ C)) :
    (weakEquivalences C).functorCategory D (c.cofibrantComparison s c' s' f) := by
  let W := (weakEquivalences C).functorCategory D
  apply W.of_postcomp (c.cofibrantComparison s c' s' f)
    ((c'.cofibrantFactorizationData s').p.app f)
    (c'.cofibrantFactorizationData_right_weak s' f)
  rw [(c.cofibrantComparison_triangles s c' s' f).2]
  exact c.cofibrantFactorizationData_right_weak s f

/-- The second comparison is weak on every original object, using the actual
weak inclusion legs and its original left triangle. -/
theorem fibrantComparison_weak (f : Arrow (D ⥤ C)) :
    (weakEquivalences C).functorCategory D (c.fibrantComparison s c' s' f) := by
  let W := (weakEquivalences C).functorCategory D
  apply W.of_precomp ((c.fibrantFactorizationData s).i.app f)
    (c.fibrantComparison s c' s' f) (c.fibrantFactorizationData_left_weak s f)
  rw [(c.fibrantComparison_triangles s c' s' f).1]
  exact c'.fibrantFactorizationData_left_weak s' f

/-- The first-factor inclusion comparison fixes the entire original source. -/
def cofibrantComparisonLeftArrow (f : Arrow (D ⥤ C)) :
    Arrow.mk ((c.cofibrantFactorizationData s).i.app f) ⟶
      Arrow.mk ((c'.cofibrantFactorizationData s').i.app f) :=
  Arrow.homMk (𝟙 f.left) (c.cofibrantComparison s c' s' f)
    (by
      change (𝟙 f.left) ≫ (c'.cofibrantFactorizationData s').i.app f =
        (c.cofibrantFactorizationData s).i.app f ≫ c.cofibrantComparison s c' s' f
      simpa only [Category.id_comp] using (c.cofibrantComparison_triangles s c' s' f).1.symm)

/-- The first-factor projection comparison fixes the entire original target. -/
def cofibrantComparisonRightArrow (f : Arrow (D ⥤ C)) :
    Arrow.mk ((c.cofibrantFactorizationData s).p.app f) ⟶
      Arrow.mk ((c'.cofibrantFactorizationData s').p.app f) :=
  Arrow.homMk (c.cofibrantComparison s c' s' f) (𝟙 f.right)
    (by
      change c.cofibrantComparison s c' s' f ≫ (c'.cofibrantFactorizationData s').p.app f =
        (c.cofibrantFactorizationData s).p.app f ≫ 𝟙 f.right
      exact (c.cofibrantComparison_triangles s c' s' f).2.trans (Category.comp_id _).symm)

/-- The second-factor inclusion comparison retains the same original source. -/
def fibrantComparisonLeftArrow (f : Arrow (D ⥤ C)) :
    Arrow.mk ((c.fibrantFactorizationData s).i.app f) ⟶
      Arrow.mk ((c'.fibrantFactorizationData s').i.app f) :=
  Arrow.homMk (𝟙 f.left) (c.fibrantComparison s c' s' f)
    (by
      change (𝟙 f.left) ≫ (c'.fibrantFactorizationData s').i.app f =
        (c.fibrantFactorizationData s).i.app f ≫ c.fibrantComparison s c' s' f
      simpa only [Category.id_comp] using (c.fibrantComparison_triangles s c' s' f).1.symm)

/-- The second-factor projection comparison retains the same original target. -/
def fibrantComparisonRightArrow (f : Arrow (D ⥤ C)) :
    Arrow.mk ((c.fibrantFactorizationData s).p.app f) ⟶
      Arrow.mk ((c'.fibrantFactorizationData s').p.app f) :=
  Arrow.homMk (c.fibrantComparison s c' s' f) (𝟙 f.right)
    (by
      change c.fibrantComparison s c' s' f ≫ (c'.fibrantFactorizationData s').p.app f =
        (c.fibrantFactorizationData s).p.app f ≫ 𝟙 f.right
      exact (c.fibrantComparison_triangles s c' s' f).2.trans (Category.comp_id _).symm)

/-- The two first-factor Arrow comparisons retain their common actual middle
map and literal identity maps at both unchanged original endpoints. -/
theorem cofibrantComparisonArrow_endpoints (f : Arrow (D ⥤ C)) :
    (c.cofibrantComparisonLeftArrow s c' s' f).left = 𝟙 f.left ∧
      (c.cofibrantComparisonRightArrow s c' s' f).right = 𝟙 f.right ∧
      (c.cofibrantComparisonLeftArrow s c' s' f).right =
        (c.cofibrantComparisonRightArrow s c' s' f).left := ⟨rfl, rfl, rfl⟩

/-- The second-factor Arrow comparisons also keep both original endpoints
and the same whole natural transformation at the middle. -/
theorem fibrantComparisonArrow_endpoints (f : Arrow (D ⥤ C)) :
    (c.fibrantComparisonLeftArrow s c' s' f).left = 𝟙 f.left ∧
      (c.fibrantComparisonRightArrow s c' s' f).right = 𝟙 f.right ∧
      (c.fibrantComparisonLeftArrow s c' s' f).right =
        (c.fibrantComparisonRightArrow s c' s' f).left := ⟨rfl, rfl, rfl⟩

end SourceConstruction.CoefficientData

namespace SourceConstruction

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] [IsCombinatorialModelCategory.{w} C] [EssentiallySmall.{w} D]
  (c : CoefficientData.{w'} C) (s : Functor.EssentialIndexData.{w'} D C)

/-- The conventional existence entry agrees with every independently chosen
original coefficient witness and original small-index equivalence. -/
theorem modelCategory_eq_coefficientData :
    modelCategory (D := D) (C := C) = c.modelCategory s :=
  (coefficientData C).modelCategory_eq (essentialIndex (D := D) (C := C)) c s

end SourceConstruction

end HomotopicalAlgebra.FunctorInjective
