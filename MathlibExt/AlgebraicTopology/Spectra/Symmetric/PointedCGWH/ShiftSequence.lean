/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.ShiftCotensorAction

/-!
# Underlying sequence maps of symmetric shifts

Shows that the native enriched right shift carries each ordinary index point to its right-tensored label. Consequently, restricting a shifted symmetric spectrum to its underlying sequence sends an arrow `f` to the original sequence map of `f ▷ r`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace NativeOmegaPreparation.NativeSymmetricShiftSequence
private abbrev I := Operad.SmallFinBijGroupoid
attribute [local instance] CategoryTheory.Operad.SmallFinBijGroupoid.instMonoidalCategory
  CategoryTheory.Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

open PointedCGWH.SymmetricModulePresentation

/-- The existing complete native Hom shift preserves each original entire
sphere-coefficient generator. -/
private theorem generator (r n k a : I) (f : a ⊗ n ⟶ k) :
    operatorGenerator.{u, v} a n k f ≫ PointedCGWH.SymmetricShift.hom.{u, v} r n k =
      operatorGenerator a (n ⊗ r) (k ⊗ r)
        (PointedCGWH.SymmetricShift.label r n k a f) := by
  apply Under.UnderMorphism.ext
  have hGenerators := congrArg
    (fun Φ => fun (r n k a : I) (f : a ⊗ n ⟶ k) => (Φ r n k a f).right)
    PointedCGWH.SymmetricShift.coendHom_generator_original_function.{u, v}
  have hMaps := congrArg
    (fun Φ => fun (r n k a : I) (f : a ⊗ n ⟶ k) =>
      (operatorGenerator.{u, v} a n k f ≫ Φ r n k).right)
    PointedCGWH.SymmetricShift.coendHom_original_function_via_block_iso.{u, v}
  have hGenerator := congrFun (congrFun (congrFun (congrFun (congrFun
    hGenerators r) n) k) a) f
  have hMap := congrFun (congrFun (congrFun (congrFun (congrFun
    hMaps r) n) k) a) f
  exact hMap.symm.trans hGenerator

/-- The original unit-coefficient label retains the actual right-tensored
ordinary source arrow. -/
private theorem unitLabel (r n k : I) (f : n ⟶ k) :
    PointedCGWH.SymmetricShift.label r n k (𝟙_ I) ((λ_ n).hom ≫ f) =
      (λ_ (n ⊗ r)).hom ≫ (f ▷ r) := by
  have h : (α_ (𝟙_ I) n r).inv ≫ ((λ_ n).hom ▷ r) =
      (λ_ (n ⊗ r)).hom := by monoidal
  simp only [PointedCGWH.SymmetricShift.label, tensorHom_id, comp_whiskerRight]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ (f ▷ r)) h)

/-- The original whole unit-graded index arrow, with its actual native inclusion. -/
private def indexPoint (n k : I) (f : n ⟶ k) :
    (𝟙_ PointedCGWH.{u, v}) ⟶
      (PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
        PointedCGWH.symmetricOperatorObj.{u, v} k) :=
  PointedCGWH.basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫
    PointedCGWH.symmetricIndexInclusion.{u, v}.map
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj k)

/-- Congruence and associativity propagate a proved coefficient-generator equation
through its proved unit insertion. -/
private theorem unit_generator_congruence
    {C : Type*} [Category C] {U A K K' : C}
    {ε : U ⟶ A} {p : U ⟶ K} {p' : U ⟶ K'}
    {q : A ⟶ K} {q₁ q' : A ⟶ K'} {t : K ⟶ K'}
    (hp : p = ε ≫ q) (hp' : p' = ε ≫ q')
    (hg : q ≫ t = q₁) (hl : q₁ = q') : p ≫ t = p' := by
  rw [hp, Category.assoc, hg, hl, ← hp']

set_option maxHeartbeats 300000 in
-- The unit insertion is compared with the complete native coend generator maps.
/-- The original index point is preserved by the unchanged native full-Hom shift. -/
theorem indexPoint_shift (r n k : Operad.SmallFinBijGroupoid) (f : n ⟶ k) :
    (PointedCGWH.basedDiscreteIncl.{u, v, 0} (n ⟶ k) f ≫
      PointedCGWH.symmetricIndexInclusion.{u, v}.map
        ((PointedCGWH.copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj n)
        ((PointedCGWH.copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj k)) ≫
        PointedCGWH.SymmetricShift.hom.{u, v} r n k =
      PointedCGWH.basedDiscreteIncl.{u, v, 0} ((n ⊗ r) ⟶ (k ⊗ r)) (f ▷ r) ≫
        PointedCGWH.symmetricIndexInclusion.{u, v}.map
          ((PointedCGWH.copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj (n ⊗ r))
          ((PointedCGWH.copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj (k ⊗ r)) := by
  apply Under.UnderMorphism.ext
  have hp := congrArg (fun z => z.right) (operatorGenerator_indexPoint.{u, v} f)
  have hp' := congrArg (fun z => z.right) (operatorGenerator_indexPoint.{u, v} (f ▷ r))
  have hg := congrArg (fun z => z.right) (generator r n k (𝟙_ I) ((λ_ n).hom ≫ f))
  have hl := congrArg (fun z => z.right)
    (congrArg (operatorGenerator.{u, v} (𝟙_ I) (n ⊗ r) (k ⊗ r))
      (unitLabel r n k f))
  exact unit_generator_congruence hp hp' hg hl

set_option maxHeartbeats 300000 in
-- The map comparison projects the complete enriched Hom shift and its unit insertion.
/-- Every original native ordinary sequence map is unchanged except for its actual
right-tensored source label. -/
theorem map
    (E : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (r : Operad.SmallFinBijGroupoid) {n k : Operad.SmallFinBijGroupoid} (f : n ⟶ k) :
    ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj
      ((PointedCGWH.SymmetricShift.functor.{u, v} r).obj E)).functor.map f =
      ((PointedCGWH.symmetricSequenceRestriction.{u, v}).obj E).functor.map (f ▷ r) := by
  rw [PointedCGWH.symmetricSequenceRestriction_map,
    PointedCGWH.symmetricSequenceRestriction_map,
    PointedCGWH.SymmetricShift.functor_fullHom]
  apply congrArg (eHomEquiv PointedCGWH.{u, v}).symm
  apply Under.UnderMorphism.ext
  exact congrArg
    (fun z => z ≫ (E.toEnrichedFunctor.map
      (PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ r))
      (PointedCGWH.symmetricOperatorObj.{u, v} (k ⊗ r))).right)
    (congrArg (fun z => z.right) (indexPoint_shift r n k f))



end NativeOmegaPreparation.NativeSymmetricShiftSequence
