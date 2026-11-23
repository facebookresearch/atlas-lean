/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.CoefficientChainBicomplex
public import MathlibExt.CategoryTheory.CategoryHomology.BarFunctoriality
public import MathlibExt.Algebra.Homology.TotalComplexExact
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import MathlibExt.Algebra.Homology.TotalComplexDownNat

/-!
# The actual relative coefficient bar and its total quotient

The alternating coefficient bar preserves finite colimits: in each degree
it is restriction to the original left endpoints followed by a coproduct.
The existing finite-fiber total functor also preserves finite colimits.
Their actual cokernel comparisons therefore identify the bar and signed
total of a relative coefficient diagram with the respective cokernels of
the original bar and total maps. Both quotient squares retain the original
cokernel projections.

These are comparisons of the computed relative complexes. They supply no
acyclicity, cover-homology, spectral edge, or H-space Whitehead assumption.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe uJ vJ uA vA w

public section

namespace CategoryTheory.CategoryHomology

section Bar

variable {J : Type uJ} [Category.{vJ} J]
  {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{max uJ vJ} A]

/-- The existing alternating coefficient bar, with its actual coefficient maps. -/
abbrev alternatingCoefficientBarFunctor : (J ⥤ A) ⥤ ChainComplex A ℕ :=
  coefficientBarSimplicialFunctor ⋙ AlgebraicTopology.alternatingFaceMapComplex A

private def barLeftEndpoints (n : ℕ) : Discrete (ComposableArrows J n) ⥤ J :=
  Discrete.functor fun s => s.left

/-- Each degree is the coproduct after restriction to the same left endpoints. -/
private def alternatingCoefficientBarFunctor_evalIso (n : ℕ) :
    alternatingCoefficientBarFunctor (J := J) (A := A) ⋙
        HomologicalComplex.eval A (ComplexShape.down ℕ) n ≅
      (Functor.whiskeringLeft (Discrete (ComposableArrows J n)) J A).obj
          (barLeftEndpoints n) ⋙ colim := by
  let L := colim (J := Discrete (ComposableArrows J n)) (C := A)
  let F (D : J ⥤ A) := Discrete.functor (coefficientBarFamily D n)
  let G (D : J ⥤ A) := barLeftEndpoints n ⋙ D
  let e (D : J ⥤ A) : F D ≅ G D :=
    Discrete.natIso fun s => Iso.refl (D.obj s.as.left)
  refine NatIso.ofComponents (fun D => L.mapIso (e D)) ?_
  intro D E α
  let β : F D ⟶ F E := Discrete.natTrans fun s => α.app s.as.left
  let γ : G D ⟶ G E := Functor.whiskerLeft (barLeftEndpoints n) α
  have h : β ≫ (e E).hom = (e D).hom ≫ γ := by
    apply NatTrans.ext
    funext s
    change α.app s.as.left ≫ 𝟙 _ = 𝟙 _ ≫ α.app s.as.left
    rw [Category.comp_id, Category.id_comp]
  change L.map β ≫ L.map (e E).hom = L.map (e D).hom ≫ L.map γ
  exact (L.map_comp _ _).symm.trans ((congrArg L.map h).trans (L.map_comp _ _))

instance alternatingCoefficientBarFunctor_preservesFiniteColimits
    [HasFiniteColimits A] :
    PreservesFiniteColimits (alternatingCoefficientBarFunctor (J := J) (A := A)) where
  preservesFiniteColimits K := by
    intro _ _
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    exact preservesColimitsOfShape_of_natIso
      (alternatingCoefficientBarFunctor_evalIso (J := J) (A := A) n).symm

instance alternatingCoefficientBarFunctor_preservesFiniteLimits
    [HasFiniteLimits A]
    [∀ n : ℕ, HasExactColimitsOfShape (Discrete (ComposableArrows J n)) A] :
    PreservesFiniteLimits (alternatingCoefficientBarFunctor (J := J) (A := A)) where
  preservesFiniteLimits K := by
    intro _ _
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    exact preservesLimitsOfShape_of_natIso
      (alternatingCoefficientBarFunctor_evalIso (J := J) (A := A) n).symm

instance alternatingCoefficientBarFunctor_preservesZeroMorphisms :
    (alternatingCoefficientBarFunctor (J := J) (A := A)).PreservesZeroMorphisms where
  map_zero D E := by
    apply HomologicalComplex.hom_ext
    intro n
    change coefficientBarMap (0 : D ⟶ E) n = 0
    apply coefficientBar_hom_ext D
    intro s
    rw [coefficientBarι_map]
    change (0 : D.obj s.left ⟶ E.obj s.left) ≫ coefficientBarι E s =
      coefficientBarι D s ≫ 0
    rw [zero_comp, comp_zero]

end Bar

section Cokernel

variable {J : Type uJ} [Category.{vJ} J]
  {A : Type uA} [Category.{vA} A] [Abelian A]
  [HasCoproducts.{max uJ vJ} A] {D E : J ⥤ A} (α : D ⟶ E)

/-- The actual bar of the relative quotient is the cokernel of the actual bar map. -/
def coefficientBarCokernelIso :
    coefficientBarComplex (cokernel α) ≅
      cokernel ((alternatingCoefficientBarFunctor (J := J) (A := A)).map α) :=
  PreservesCokernel.iso (alternatingCoefficientBarFunctor (J := J) (A := A)) α

/-- The comparison retains the entire original quotient projection. -/
theorem coefficientBarCokernelIso_projection :
    (alternatingCoefficientBarFunctor (J := J) (A := A)).map (cokernel.π α) ≫
        (coefficientBarCokernelIso α).hom =
      cokernel.π ((alternatingCoefficientBarFunctor (J := J) (A := A)).map α) :=
  PreservesCokernel.π_iso_hom _ _

end Cokernel

-- Supply the stock pointwise colimit instance for each index explicitly;
-- do not ask typeclass search to invent a forall-index coproduct recipe.
local instance : HasCoproducts.{w} (ChainComplex AddCommGrpCat.{w} ℕ) := fun I =>
  let : Small.{w} (Discrete I) := small_self (Discrete I)
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{w} :=
    AddCommGrpCat.hasColimitsOfShape (J := Discrete I)
  HomologicalComplex.instHasColimitsOfShape

/-- A transparent name for the existing coefficient-bar/total functor composition. -/
abbrev coefficientChainTotalFunctor {J : Type w} [Category.{0} J] :
    (J ⥤ ChainComplex AddCommGrpCat.{w} ℕ) ⥤ ChainComplex AddCommGrpCat.{w} ℕ :=
  alternatingCoefficientBarFunctor ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)

/-- Exact coproducts of abelian groups remain exact after adding a differential.
The ordinary degree-forgetting functor reflects limits and preserves them
and coproducts by the existing evaluation criteria. -/
private theorem chainComplex_exactCoproducts (I : Type w) :
    HasExactColimitsOfShape (Discrete I) (ChainComplex AddCommGrpCat.{w} ℕ) := by
  let F : ChainComplex AddCommGrpCat.{w} ℕ ⥤ Discrete ℕ ⥤ AddCommGrpCat.{w} :=
    HomologicalComplex.forget AddCommGrpCat.{w} (ComplexShape.down ℕ) ⋙
      (piEquivalenceFunctorDiscrete ℕ AddCommGrpCat.{w}).functor
  let : PreservesFiniteLimits F :=
    { preservesFiniteLimits K := by
        intro _ _
        apply preservesLimitsOfShape_of_evaluation
        rintro ⟨n⟩
        change PreservesLimitsOfShape K
          (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.down ℕ) n)
        infer_instance }
  let : ReflectsFiniteLimits F :=
    { reflects K := by
        intro _ _
        exact
          { reflectsLimit := fun {D} =>
              { reflects := fun {c} hc => ⟨HomologicalComplex.isLimitOfEval D c (fun n => by
                  change IsLimit
                    (((evaluation (Discrete ℕ) AddCommGrpCat.{w}).obj ⟨n⟩).mapCone
                      (F.mapCone c))
                  exact isLimitOfPreserves
                    ((evaluation (Discrete ℕ) AddCommGrpCat.{w}).obj ⟨n⟩) hc)⟩ } } }
  let : PreservesColimitsOfShape (Discrete I) F := by
    apply preservesColimitsOfShape_of_evaluation
    rintro ⟨n⟩
    change PreservesColimitsOfShape (Discrete I)
      (HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.down ℕ) n)
    infer_instance
  exact HasExactColimitsOfShape.domain_of_functor
    (Discrete I) F

local instance (I : Type w) :
    HasExactColimitsOfShape (Discrete I) (ChainComplex AddCommGrpCat.{w} ℕ) :=
  chainComplex_exactCoproducts I

section Total

variable {J : Type w} [Category.{0} J]

instance coefficientChainTotalFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (coefficientChainTotalFunctor (J := J)) := by
  dsimp only [coefficientChainTotalFunctor]
  infer_instance

instance coefficientChainTotalFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (coefficientChainTotalFunctor (J := J)) := by
  dsimp only [coefficientChainTotalFunctor]
  infer_instance

instance coefficientChainTotalFunctor_preservesZeroMorphisms :
    (coefficientChainTotalFunctor (J := J)).PreservesZeroMorphisms := by
  dsimp only [coefficientChainTotalFunctor]
  infer_instance

variable {D E : J ⥤ ChainComplex AddCommGrpCat.{w} ℕ} (α : D ⟶ E)

/-- Signed totalization of the actual relative bar is the actual total-map cokernel. -/
def coefficientRelativeTotalIso :
    (coefficientChainTotalFunctor (J := J)).obj (cokernel α) ≅
      cokernel ((coefficientChainTotalFunctor (J := J)).map α) :=
  PreservesCokernel.iso (coefficientChainTotalFunctor (J := J)) α

/-- The whole total quotient square, using the original projections on both sides. -/
theorem coefficientRelativeTotalIso_projection :
    (coefficientChainTotalFunctor (J := J)).map (cokernel.π α) ≫
        (coefficientRelativeTotalIso α).hom =
      cokernel.π ((coefficientChainTotalFunctor (J := J)).map α) :=
  PreservesCokernel.π_iso_hom _ _

end Total

end CategoryTheory.CategoryHomology
