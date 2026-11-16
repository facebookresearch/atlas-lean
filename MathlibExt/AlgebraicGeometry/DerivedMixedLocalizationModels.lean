/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Actual mixed localization and weighted NC on derived morphisms

Weighted NC is specified on every mixed complex by its complete product
terms, native differential and componentwise maps. Its derived functor
is the actual localization lift of this same cochain functor. Relative
de Rham and integration classes therefore do not require arbitrary
strict chain representatives between unrelated resolution models.

Reference: PTVV arXiv:1111.3209v4, §1.1 and §2.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels

open _root_.CategoryTheory
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams

universe u v w
variable {R : Type u} [CommRing R]
attribute [local instance] HasDerivedCategory.standard

/-- Mixed weak equivalence retains every actual weight cochain complex. -/
def mixedWeakEquivalences (R : Type u) [CommRing R] : MorphismProperty (GradedMixed R) :=
  fun _ _ f => ∀ p : ℤ, QuasiIso (f.map p)

abbrev mixedQ (R : Type u) [CommRing R] := (mixedWeakEquivalences R).Q

/-- The actual localization of a whole mixed diagram, retaining all naturality. -/
def mixedDiagramWeakEquivalences (R : Type u) [CommRing R] (J : Type v) [Category.{w} J] :
    MorphismProperty (J ⥤ GradedMixed R) := fun _ _ f => ∀ (j : J) (p : ℤ), QuasiIso ((f.app j).map p)

abbrev mixedDiagramQ (R : Type u) [CommRing R] (J : Type v) [Category.{w} J] :=
  (mixedDiagramWeakEquivalences R J).Q

/-- The complete actual weighted NC functor and its source weak-equivalence law. -/
structure NCCategoryModel (R : Type u) [CommRing R] (p : ℤ) where
  diagram : NegativeCyclicDiagram (𝟭 (GradedMixed R)) p
  weak : ∀ (E F : GradedMixed R) (f : MixedMap E F),
    (∀ w : ℤ, QuasiIso (f.map w)) → QuasiIso (diagram.complex.map f)

/-- The derived NC functor is the native localization lift, not a supplied invariant. -/
def derivedNC {p : ℤ} (N : NCCategoryModel R p) :
    (mixedWeakEquivalences R).Localization ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.Construction.lift (W := mixedWeakEquivalences R)
    (N.diagram.complex ⋙ DerivedCategory.Q) (by
      intro E F f h
      let _ := N.weak E F f h
      change IsIso (DerivedCategory.Q.map (N.diagram.complex.map f))
      infer_instance)

/-- The object comparison is the actual factorization of the native NC localization lift. -/
def derivedNCObjIso {p : ℤ} (N : NCCategoryModel R p) (E : GradedMixed R) :
    (derivedNC N).obj ((mixedQ R).obj E) ≅ DerivedCategory.Q.obj (N.diagram.complex.obj E) :=
  Iso.refl _

/-- The actual derived ordinary-weight functor, lifted through the same mixed localization. -/
def derivedWeight (R : Type u) [CommRing R] (p : ℤ) :
    (mixedWeakEquivalences R).Localization ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.Construction.lift (W := mixedWeakEquivalences R)
    (weightFunctor p ⋙ DerivedCategory.Q) (by
      intro E F f h
      have := h p
      change IsIso (DerivedCategory.Q.map (f.map p))
      infer_instance)

/-- Weight objects retain the actual factorization of the native localization lift. -/
def derivedWeightObjIso (R : Type u) [CommRing R] (p : ℤ) (E : GradedMixed R) :
    (derivedWeight R p).obj ((mixedQ R).obj E) ≅ DerivedCategory.Q.obj (E.weight p) := Iso.refl _

/-- Two actual NC models agree through their fixed complete coefficient comparisons. -/
def ncModelIso {E : GradedMixed R} {p : ℤ}
    (M N : NegativeCyclicModel E p) : M.complex ≅ N.complex :=
  HomologicalComplex.Hom.isoOfComponents (fun n => M.termIso n ≪≫ (N.termIso n).symm) (by
    intro n m h
    obtain rfl : m = n + 1 := h.symm
    simp only [Iso.trans_hom, Iso.symm_hom]
    apply (cancel_mono (N.termIso (n + 1)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [N.differential_eq]
    simp only [Iso.inv_hom_id_assoc]
    exact (M.differential_eq n).symm)

end MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels
