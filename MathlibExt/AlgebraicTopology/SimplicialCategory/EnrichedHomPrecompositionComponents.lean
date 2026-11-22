/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomActionNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero

/-!
# The SAME full original precomposition maps recognize component equivalences

The original complete precomposition map acts on components by literal
original component-category composition. A supplied original equivalence
therefore acts weakly on every full Hom. Conversely, genuine weakness of
the two actual original precomposition maps constructs both inverse
component identities. Original objects and Hom maps are unchanged.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomPrecomposition
open ComponentCategory EnrichedHomWeakTransport
variable {C : Type v} [EnrichedCategory SSet.{u} C] {x y : C}

/-- The SAME original full precomposition acts on components by its literal original coefficient arrow. -/
theorem pre_mapπ₀ (z : C) (q : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y))
    (a : objectOf.{u} C y ⟶ objectOf.{u} C z) :
    SSet.mapπ₀ (pre z q) a = arrowOf C (SSet.unitHomEquiv _ q) ≫ a := by
  change SSet.mapπ₀ (pre z q) a =
    SSet.mapπ₀ (eComp SSet.{u} x y z)
      ((Functor.LaxMonoidal.μ SSet.π₀Functor _ _) (SSet.π₀.mk (SSet.unitHomEquiv _ q), a))
  induction a using SSet.π₀.rec with
  | mk a =>
    have hm := SSet.piZeroMonoidal_μ_mk (x ⟶[SSet.{u}] y) (y ⟶[SSet.{u}] z)
      (SSet.unitHomEquiv _ q) a
    have hv : (pre z q).app (op ⦋0⦌) a = (eComp SSet.{u} x y z).app (op ⦋0⦌)
        (SSet.componentTensorSimplex _ (SSet.unitHomEquiv _ q) a) := rfl
    exact (SSet.mapπ₀_mk (pre z q) a).trans
      ((congrArg SSet.π₀.mk hv).trans
        ((SSet.mapπ₀_mk (eComp SSet.{u} x y z)
          (SSet.componentTensorSimplex _ (SSet.unitHomEquiv _ q) a)).symm.trans
            (congrArg (SSet.mapπ₀ (eComp SSet.{u} x y z)) hm.symm)))

/-- Every supplied original invertible component coefficient acts weakly on its SAME full precomposition Hom map. -/
theorem pre_weak_of_isIso (z : C) (q : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y))
    (hq : IsIso (arrowOf C (SSet.unitHomEquiv _ q))) :
    SSet.realizationWeakEquivalences (pre z q) := by
  let e : objectOf.{u} C x ≅ objectOf.{u} C y :=
    @asIso _ _ _ _ (arrowOf C (SSet.unitHomEquiv _ q)) hq
  exact (pre_weak_of_component_iso_representatives z e q (inverseUnit e) rfl
    (inverseUnit_class e)).1

/-- Two SAME actual full precomposition weak maps construct both original inverse component identities. -/
theorem isIso_of_pre_weak (q : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y))
    (hx : SSet.realizationWeakEquivalences (pre x q))
    (hy : SSet.realizationWeakEquivalences (pre y q)) :
    IsIso (arrowOf C (SSet.unitHomEquiv _ q)) := by
  let f := arrowOf C (SSet.unitHomEquiv _ q)
  obtain ⟨g, hg⟩ := (SSet.realizationWeakEquivalences.bijective_mapπ₀ hx).2 (𝟙 (objectOf.{u} C x))
  have hfg : f ≫ g = 𝟙 (objectOf.{u} C x) := (pre_mapπ₀ x q g).symm.trans hg
  have hgf : g ≫ f = 𝟙 (objectOf.{u} C y) := by
    apply (SSet.realizationWeakEquivalences.bijective_mapπ₀ hy).1
    exact (pre_mapπ₀ y q (g ≫ f)).trans
      ((Category.assoc f g f).symm.trans
        ((congrArg (fun k => k ≫ f) hfg).trans
          ((Category.id_comp f).trans
            ((Category.comp_id f).symm.trans (pre_mapπ₀ y q (𝟙 (objectOf.{u} C y))).symm))))
  exact ⟨⟨g, hfg, hgf⟩⟩

end CategoryTheory.SimplicialEnrichment.EnrichedHomPrecomposition
