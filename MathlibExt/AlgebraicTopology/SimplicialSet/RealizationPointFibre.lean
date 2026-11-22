/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationPullbackMono
import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange

/-!
# Realization of the whole pullback at a simplicial point

Realization preserves the original point pullback. The resulting isomorphism
retains its total-space leg and its actual map to the realized zero simplex.
The selected point is the realization of the given whole simplicial map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SSet

/-- The original simplicial point map evaluated at the unique realized zero simplex. -/
def realizedPoint {B : SSet.{u}} (b : (Δ[0] : SSet.{u}) ⟶ B) : SSet.toTop.obj B :=
  SSet.toTop.map b default

/-- The whole point map commutes with realization of the actual base map. -/
theorem realizedPoint_comp {B B' : SSet.{u}}
    (b : (Δ[0] : SSet.{u}) ⟶ B) (h : B ⟶ B') :
    realizedPoint (b ≫ h) = SSet.toTop.map h (realizedPoint b) := by
  rw [realizedPoint, Functor.map_comp]
  rfl

/-- At a Yoneda point this is the original realized vertex. -/
theorem realizedPoint_yoneda {B : SSet.{u}} (b : B _⦋0⦌) :
    realizedPoint (SSet.yonedaEquiv.symm b) = SSet.realizedVertex b := rfl

/-- The realized original zero simplex is terminal. -/
def realizedZeroIsTerminal : IsTerminal (SSet.toTop.obj (Δ[0] : SSet.{u})) := by
  let _ : ∀ Z : TopCat.{u}, Unique (Z ⟶ SSet.toTop.obj (Δ[0] : SSet.{u})) := fun Z =>
    { default := TopCat.ofHom ⟨fun _ => default, continuous_const⟩
      uniq := by
        intro g
        apply TopCat.hom_ext
        ext z
        exact Subsingleton.elim _ _ }
  exact IsTerminal.ofUnique _

/-- The whole realized point object is its actual terminal topological point. -/
def realizedZeroIso : SSet.toTop.obj (Δ[0] : SSet.{u}) ≅ TopCat.of PUnit :=
  realizedZeroIsTerminal.uniqueUpToIso TopCat.isTerminalPUnit

private theorem mono_point {B : SSet.{u}} (b : (Δ[0] : SSet.{u}) ⟶ B) : Mono b := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y _
  apply SSet.stdSimplex.objEquiv.injective
  subsingleton

/-- The given whole simplicial point realizes to its constant map at the actual selected point. -/
theorem toTop_map_point {B : SSet.{u}} (b : (Δ[0] : SSet.{u}) ⟶ B) :
    SSet.toTop.map b = realizedZeroIso.hom ≫ TopCat.const (realizedPoint b) := by
  apply TopCat.ext
  intro z
  have hz : z = (default : SSet.toTop.obj (Δ[0] : SSet.{u})) := Subsingleton.elim _ _
  subst z
  rfl

/-- The original point pullback is the actual topological strict point fibre after realization. -/
theorem isPullback_realizationPointFibre {X B : SSet.{u}}
    (p : X ⟶ B) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    IsPullback (SSet.toTop.map (pullback.fst p b))
      (SSet.toTop.map (pullback.snd p b) ≫ realizedZeroIso.hom)
      (SSet.toTop.map p) (TopCat.const (realizedPoint b)) := by
  let _ : Mono b := mono_point b
  have hs := ((IsPullback.of_hasPullback p b).flip.map_toTop_of_mono).flip
  apply hs.of_iso (Iso.refl _) (Iso.refl _) realizedZeroIso (Iso.refl _)
  · simp
  · rfl
  · simp
  · exact toTop_map_point b

/-- The whole point-fibre realization isomorphism keeps both original pullback projections. -/
def realizationPointFibreIso {X B : SSet.{u}}
    (p : X ⟶ B) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    SSet.toTop.obj (pullback p b) ≅
      pullback (SSet.toTop.map p) (TopCat.const (X := TopCat.of PUnit) (realizedPoint b)) :=
  (isPullback_realizationPointFibre p b).isoPullback

/-- The forward comparison retains the complete original total-space point. -/
@[reassoc]
theorem realizationPointFibreIso_fst {X B : SSet.{u}}
    (p : X ⟶ B) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    (realizationPointFibreIso p b).hom ≫ pullback.fst _ _ =
      SSet.toTop.map (pullback.fst p b) :=
  (isPullback_realizationPointFibre p b).isoPullback_hom_fst

/-- The forward comparison retains the given point leg and its whole realized terminal isomorphism. -/
@[reassoc]
theorem realizationPointFibreIso_snd {X B : SSet.{u}}
    (p : X ⟶ B) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    (realizationPointFibreIso p b).hom ≫ pullback.snd _ _ =
      SSet.toTop.map (pullback.snd p b) ≫ realizedZeroIso.hom :=
  (isPullback_realizationPointFibre p b).isoPullback_hom_snd

end SSet
