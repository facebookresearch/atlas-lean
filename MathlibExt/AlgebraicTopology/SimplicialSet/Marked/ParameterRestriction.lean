/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeUnderlying
import MathlibExt.AlgebraicTopology.Quasicategory.FunctionCoreFibration
import MathlibExt.CategoryTheory.Limits.Shapes.Pullback.FibreRestriction

/-!
# Native restriction of original fixed-base parameter prisms

The ordinary left-parameter mapping dictionary preserves both variables.
Its original pullback comparison is the same function-pullback comparison,
so restriction on fixed-base prisms is a categorical fibration for a
monomorphism and a genuinely categorical-fibrant projection. No Kan-base
hypothesis or choice of a different mapping carrier is used.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed BraidedCategory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Precomposition retains the full original left-parameter prism. -/
def parameterMappingPre {A D : SSet.{u}} (i : A ⟶ D) (E : SSet.{u}) :
    parameterMapping D E ⟶ parameterMapping A E where
  app n := ↾fun F => (SSet.stdSimplex.obj n.unop ◁ i) ≫ F
  naturality n m a := by
    apply ConcreteCategory.hom_ext
    intro F
    change (SSet.stdSimplex.map a.unop ▷ A) ≫ (SSet.stdSimplex.obj n.unop ◁ i) ≫ F =
      (SSet.stdSimplex.obj m.unop ◁ i) ≫ (SSet.stdSimplex.map a.unop ▷ D) ≫ F
    let F' : SSet.stdSimplex.obj n.unop ⊗ D ⟶ E := F
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ F') (whisker_exchange (SSet.stdSimplex.map a.unop) i)).trans
        (Category.assoc _ _ _))

/-- The original function dictionary respects the same source restriction. -/
theorem parameterMappingIsoIhom_pre {A D : SSet.{u}} (i : A ⟶ D) (E : SSet.{u}) :
    parameterMappingPre i E ≫ (parameterMappingIsoIhom A E).hom =
      (parameterMappingIsoIhom D E).hom ≫ (pre i).app E := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro F
  change leftIhomSimplexOfPrism ((SSet.stdSimplex.obj n.unop ◁ i) ≫ F) =
    ((pre i).app E).app n (leftIhomSimplexOfPrism F)
  let F' : (Δ[n.unop.len] : SSet.{u}) ⊗ D ⟶ E := F
  change leftIhomSimplexOfPrism (((Δ[n.unop.len] : SSet.{u}) ◁ i) ≫ F') =
    ((pre i).app E).app n (leftIhomSimplexOfPrism F')
  dsimp only [leftIhomSimplexOfPrism]
  rw [ihomSimplexOfPrism_pre_app]
  apply congrArg ihomSimplexOfPrism
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ F') (braiding_naturality_left i (Δ[n.unop.len] : SSet.{u}))).symm.trans
      (Category.assoc _ _ _))

/-- The full source prism and the original target map commute literally. -/
theorem parameterMappingPre_post {A D E B : SSet.{u}} (i : A ⟶ D) (p : E ⟶ B) :
    parameterMappingPre i E ≫ parameterMappingPost A p =
      parameterMappingPost D p ≫ parameterMappingPre i B := by
  ext n F
  exact Category.assoc _ _ _

/-- The original square comparison between full parameter mapping objects. -/
def parameterUnderlyingComparison {A D E B : SSet.{u}} (i : A ⟶ D) (p : E ⟶ B) :
    parameterMapping D E ⟶ pullback (parameterMappingPost A p) (parameterMappingPre i B) :=
  pullback.lift (parameterMappingPre i E) (parameterMappingPost D p)
    (parameterMappingPre_post i p)

/-- The native function-pullback packet on the same original parameter pullback object. -/
def parameterFunctionSquare {A D E B : SSet.{u}} (i : A ⟶ D) (p : E ⟶ B) :
    MonoidalClosed.internalHom.PullbackObjObj i p where
  pt := pullback (parameterMappingPost A p) (parameterMappingPre i B)
  fst := pullback.fst _ _ ≫ (parameterMappingIsoIhom A E).hom
  snd := pullback.snd _ _ ≫ (parameterMappingIsoIhom D B).hom
  isPullback :=
    (IsPullback.of_hasPullback (parameterMappingPost A p) (parameterMappingPre i B)).of_iso
      (Iso.refl _) (parameterMappingIsoIhom A E) (parameterMappingIsoIhom D B)
      (parameterMappingIsoIhom A B) (by simp) (by simp)
      (parameterMappingIsoIhom_post A p) (parameterMappingIsoIhom_pre i B)
  π := (parameterMappingIsoIhom D E).inv ≫ parameterUnderlyingComparison i p
  π_fst := by
    change ((parameterMappingIsoIhom D E).inv ≫ parameterUnderlyingComparison i p) ≫
      (pullback.fst (parameterMappingPost A p) (parameterMappingPre i B) ≫
        (parameterMappingIsoIhom A E).hom) = (pre i).app E
    rw [Category.assoc, ← Category.assoc (parameterUnderlyingComparison i p),
      parameterUnderlyingComparison, pullback.lift_fst, parameterMappingIsoIhom_pre]
    simp only [Iso.inv_hom_id_assoc]
  π_snd := by
    change ((parameterMappingIsoIhom D E).inv ≫ parameterUnderlyingComparison i p) ≫
      (pullback.snd (parameterMappingPost A p) (parameterMappingPre i B) ≫
        (parameterMappingIsoIhom D B).hom) = (ihom D).map p
    rw [Category.assoc, ← Category.assoc (parameterUnderlyingComparison i p),
      parameterUnderlyingComparison, pullback.lift_snd, parameterMappingIsoIhom_post]
    simp only [Iso.inv_hom_id_assoc]

/-- The actual original parameter comparison is a genuine categorical fibration. -/
theorem parameterUnderlyingComparison_categoricalFibrations {A D E B : SSet.{u}}
    (i : A ⟶ D) [Mono i] (p : E ⟶ B) [InnerFibration p] [Quasicategory B]
    [HasStrictEquivalenceLifting p] : categoricalFibrations (parameterUnderlyingComparison i p) := by
  have h := categoricalFibrations_pullbackObjObjπ i p (parameterFunctionSquare i p)
  change categoricalFibrations ((parameterMappingIsoIhom D E).inv ≫ parameterUnderlyingComparison i p) at h
  exact (MorphismProperty.cancel_left_of_respectsIso categoricalFibrations
    (parameterMappingIsoIhom D E).inv (parameterUnderlyingComparison i p)).mp h

end SSet.Marked
