/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.KanMaps

/-!
# Actual Kan-source marking cells

The cell keeps the whole original Kan simplicial set and changes only its
minimal marking to its maximal marking. Its right lifting condition says
precisely that all original maps from that Kan source preserve its full
marking. Intrinsic Cartesian and cocartesian targets satisfy this condition
by the existing groupoidal-map theorem. No small generating-set or marked
model conclusion is assumed from this potentially large family.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original identity simplicial map from minimal to maximal marking. -/
def kanMarkCell (K : SSet.{u}) : min K ⟶ max K := toMax (𝟙 K)

/-- The marking cell keeps every original simplex. -/
@[simp]
theorem kanMarkCell_hom (K : SSet.{u}) : (kanMarkCell K).hom = 𝟙 K := rfl

/-- Enlarging only this marking is a genuine marked monomorphism. -/
theorem kanMarkCell_mono (K : SSet.{u}) : Mono (kanMarkCell K) := by
  let _ : Mono (kanMarkCell K).hom := inferInstanceAs (Mono (𝟙 K))
  exact Hom.mono_of_underlying _

/-- The native identity marking cell lifts exactly when all original maps preserve the full source marking. -/
theorem kanMarkCell_rlp_iff (K : SSet.{u}) {Y : Marked.{u}} {B : SSet.{u}} (p : Y ⟶ max B) :
    HasLiftingProperty (kanMarkCell K) p ↔
      ∀ (f : K ⟶ Y.toSSet) (e : K _⦋1⦌), f.app (op ⦋1⦌) e ∈ Y.marking := by
  constructor
  · intro hp f e
    let a : min K ⟶ Y := ofMin f
    let b : max K ⟶ max B := toMax (f ≫ p.hom)
    let _ : HasLiftingProperty (kanMarkCell K) p := hp
    have sq : CommSq a (kanMarkCell K) p b := ⟨Hom.ext (Category.id_comp _).symm⟩
    have hf : sq.lift.hom = f := by
      let F : K ⟶ Y.toSSet := sq.lift.hom
      have h : (𝟙 K) ≫ F = f := congrArg Hom.hom sq.fac_left
      exact (Category.id_comp F).symm.trans h
    have h := sq.lift.preserve (Set.mem_univ e)
    exact hf ▸ h
  · intro h
    refine ⟨fun {a b} sq => ?_⟩
    let f : max K ⟶ Y := ⟨a.hom, fun _ => h a.hom _⟩
    have hb : f.hom ≫ p.hom = b.hom := by
      let F : K ⟶ Y.toSSet := a.hom
      let G : K ⟶ (max B).toSSet := b.hom
      have h' : F ≫ p.hom = (𝟙 K) ≫ G := congrArg Hom.hom sq.w
      exact h'.trans (Category.id_comp G)
    exact CommSq.HasLift.mk' ⟨f, Hom.ext (Category.id_comp _), Hom.ext hb⟩

/-- Actual intrinsic Cartesian projections lift every original Kan-source marking cell. -/
theorem kanMarkCell_cartesian (K : SSet.{u}) [KanComplex K] {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    HasLiftingProperty (kanMarkCell K) (cartesianProjection p) := by
  apply (kanMarkCell_rlp_iff K (cartesianProjection p)).mpr
  intro f e
  exact (ofMaxKanCartesian p f).preserve (Set.mem_univ e)

/-- The same native Kan-source cells lift against the intrinsic cocartesian projection. -/
theorem kanMarkCell_cocartesian (K : SSet.{u}) [KanComplex K] {E B : SSet.{u}}
    (p : E ⟶ B) [InnerFibration p] [Quasicategory B] :
    HasLiftingProperty (kanMarkCell K) (cocartesianProjection p) := by
  apply (kanMarkCell_rlp_iff K (cocartesianProjection p)).mpr
  intro f e
  exact (ofMaxKanCocartesian p f).preserve (Set.mem_univ e)

end SSet.Marked
