/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageProduct
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Equivalence

/-!
# Finite-stage product categorical equivalence

The categorical equivalence
`Stage (C × D) n ≌ Stage C n × Stage D n` with forward functor
`stageProject C D n` and inverse `stagePair C D n`.

Stage projection restricts the ambient inverse and stage pairing restricts the
ambient functor; the stage unit comes from the ambient counit inverse through
`ObjectProperty.isoMk` (the full-subcategory lift) and the stage counit is
assembled from the ambient unit constituents `prod'CompFst`/`prod'CompSnd`
through the same lift. Object and map behavior reuses the existing
projection/pairing equations (which hold by `rfl`) and proof irrelevance
for the stage predicates; no zero or cofiber-sequence facts are re-proved.

Proves no weak-stage comparison, simplicial object, realization, additivity
theorem, K/G-theory identification, spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D] (n : ℕ)

/-- Local product Waldhausen structure on `C × D`, explicitly scoped. -/
local instance prodWaldhausenLocalEquiv : WaldhausenCategoryWithoutGluing (C × D) := prodWaldhausen

/-- Unit component: the ambient counit restricted through the full subcategory. -/
noncomputable def stageProductUnitApp (X : Stage (C × D) n) :
    X ≅ (stageProject C D n ⋙ stagePair C D n).obj X :=
  ObjectProperty.isoMk _
    ((functorProdFunctorEquiv (Ar n) C D).counitIso.symm.app X.obj)

/-- Naturality of the restricted unit components. -/
theorem stageProductUnit_naturality {X Y : Stage (C × D) n}
    (f : X ⟶ Y) :
    (𝟭 (Stage (C × D) n)).map f ≫ (stageProductUnitApp C D n Y).hom =
      (stageProductUnitApp C D n X).hom ≫
        (stageProject C D n ⋙ stagePair C D n).map f := by
  apply ObjectProperty.hom_ext
  exact (functorProdFunctorEquiv (Ar n) C D).counitIso.inv.naturality f.hom

/-- Supplied pre-unit data for `Equivalence.mk` (not necessarily definitionally
the adjointified `unitIso`): projecting then pairing recovers the stage. -/
noncomputable def stageProductUnitIso :
    𝟭 (Stage (C × D) n) ≅ stageProject C D n ⋙ stagePair C D n :=
  NatIso.ofComponents (stageProductUnitApp C D n)
    (fun f => stageProductUnit_naturality C D n f)

/-- First-component underlying counit iso. -/
noncomputable def stageProductCounitFstUnderlying
    (p : Stage C n × Stage D n) :
    (((stagePair C D n ⋙ stageProject C D n).obj p).1).obj ≅ p.1.obj :=
  Functor.prod'CompFst p.1.obj p.2.obj

/-- Second-component underlying counit iso. -/
noncomputable def stageProductCounitSndUnderlying
    (p : Stage C n × Stage D n) :
    (((stagePair C D n ⋙ stageProject C D n).obj p).2).obj ≅ p.2.obj :=
  Functor.prod'CompSnd p.1.obj p.2.obj

/-- First-component counit iso through the full subcategory. -/
noncomputable def stageProductCounitFst (p : Stage C n × Stage D n) :
    ((stagePair C D n ⋙ stageProject C D n).obj p).1 ≅ p.1 :=
  ObjectProperty.isoMk _ (stageProductCounitFstUnderlying C D n p)

/-- Second-component counit iso through the full subcategory. -/
noncomputable def stageProductCounitSnd (p : Stage C n × Stage D n) :
    ((stagePair C D n ⋙ stageProject C D n).obj p).2 ≅ p.2 :=
  ObjectProperty.isoMk _ (stageProductCounitSndUnderlying C D n p)

/-- Counit component as a product of the restricted sides. -/
noncomputable def stageProductCounitApp (p : Stage C n × Stage D n) :
    (stagePair C D n ⋙ stageProject C D n).obj p ≅ p :=
  Iso.prod (stageProductCounitFst C D n p) (stageProductCounitSnd C D n p)

/-- Naturality of the restricted counit components. -/
theorem stageProductCounit_naturality {p q : Stage C n × Stage D n}
    (f : p ⟶ q) :
    (stagePair C D n ⋙ stageProject C D n).map f ≫
        (stageProductCounitApp C D n q).hom =
      (stageProductCounitApp C D n p).hom ≫ (𝟭 (Stage C n × Stage D n)).map f := by
  have h := (functorProdFunctorEquiv (Ar n) C D).unitIso.inv.naturality
    (CategoryTheory.Prod.mkHom f.1.hom f.2.hom)
  apply Prod.hom_ext
  · apply (forget C n).map_injective
    simpa [stagePair, stageProject, stageProjectFst, stageProjectSnd,
      stageProductCounitApp, stageProductCounitFst, stageProductCounitFstUnderlying,
      ObjectProperty.lift, ObjectProperty.isoMk, Iso.prod, Iso.trans, Iso.symm,
      NatIso.ofComponents, prod.etaIso, Functor.prod'CompFst, Functor.prod'CompSnd,
      functorProdFunctorEquiv, functorProdFunctorEquivUnitIso] using
        congrArg (fun k => k.1) h
  · apply (forget D n).map_injective
    simpa [stagePair, stageProject, stageProjectFst, stageProjectSnd,
      stageProductCounitApp, stageProductCounitSnd, stageProductCounitSndUnderlying,
      ObjectProperty.lift, ObjectProperty.isoMk, Iso.prod, Iso.trans, Iso.symm,
      NatIso.ofComponents, prod.etaIso, Functor.prod'CompFst, Functor.prod'CompSnd,
      functorProdFunctorEquiv, functorProdFunctorEquivUnitIso] using
        congrArg (fun k => k.2) h

/-- Supplied pre-counit data for `Equivalence.mk` (not necessarily definitionally
the adjointified `counitIso`): pairing then projecting recovers the stages. -/
noncomputable def stageProductCounitIso :
    stagePair C D n ⋙ stageProject C D n ≅ 𝟭 (Stage C n × Stage D n) :=
  NatIso.ofComponents (stageProductCounitApp C D n)
    (fun f => stageProductCounit_naturality C D n f)

/-- Let `C` and `D` each have a zero object and a Waldhausen structure
without gluing. For `n : ℕ`, use `prodWaldhausen` on `C × D`: cofibrations
and weak equivalences are defined componentwise. There is a categorical
equivalence `Stage (C × D) n ≌ Stage C n × Stage D n`. Its forward functor
is `stageProject C D n`, obtained by projecting a stage diagram and its
morphisms to the two factors. Its inverse is `stagePair C D n`, obtained
by pairing the two diagrams and morphisms componentwise. -/
noncomputable def stageProductEquivalence :
    Stage (C × D) n ≌ Stage C n × Stage D n :=
  Equivalence.mk (stageProject C D n) (stagePair C D n)
    (stageProductUnitIso C D n) (stageProductCounitIso C D n)

/-- Forward projection of the product equivalence. -/
@[simp]
theorem stageProductEquivalence_functor :
    (stageProductEquivalence C D n).functor = stageProject C D n :=
  rfl

/-- Inverse pairing functor of the product equivalence. -/
@[simp]
theorem stageProductEquivalence_inverse :
    (stageProductEquivalence C D n).inverse = stagePair C D n :=
  rfl

end CategoryTheory.Waldhausen.SConstruction
