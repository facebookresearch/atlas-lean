/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SharpPullbackClosure
import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutHCTransport

/-!
# Pasting homotopy-cartesian squares over sharp maps

Actual HC pasting and cancellation between sharp vertical arrows.

The proof basechanges a weak ordinary comparison between two sharp maps,
then uses the actual nested-pullback Iso. No sharpness or fibrancy of a
horizontal inclusion or comparison is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkIncomingHC
open SharpComparisonDraft RezkCompatiblePushout

/-- The actual rectangle is HC iff its first square is HC, when the second
square is HC and the two actual vertical right maps are sharp. -/
theorem first_hc_iff_rectangle
    {A X E B Y Z : SSet.{u}}
    (f : A ⟶ X) (g : X ⟶ E) (pA : A ⟶ B)
    (pX : X ⟶ Y) (pE : E ⟶ Z) (u : B ⟶ Y) (v : Y ⟶ Z)
    (h1 : f ≫ pX = pA ≫ u) (h2 : g ≫ pE = pX ≫ v)
    (hpX : Sharp pX) (hpE : Sharp pE)
    (rightHC : WeakEquivalence (pullback.lift g pX h2 ≫ comparison pE v)) :
    WeakEquivalence (pullback.lift f pA h1 ≫ comparison pX u) ↔
      WeakEquivalence (pullback.lift (f ≫ g) pA (by
        calc
          (f ≫ g) ≫ pE = f ≫ (g ≫ pE) := Category.assoc _ _ _
          _ = f ≫ (pX ≫ v) := by rw [h2]
          _ = (f ≫ pX) ≫ v := (Category.assoc _ _ _).symm
          _ = (pA ≫ u) ≫ v := by rw [h1]
          _ = pA ≫ (u ≫ v) := Category.assoc _ _ _) ≫
        comparison pE (u ≫ v)) := by
  let k : X ⟶ pullback pE v := pullback.lift g pX h2
  let q : pullback pE v ⟶ Y := pullback.snd pE v
  have hkq : k ≫ q = pX := pullback.lift_snd _ _ _
  have hk : WeakEquivalence k :=
    (hc_iff_ordinaryLift_weak (CommSq.mk h2) hpE).mp rightHC
  have hq : Sharp q := SharpPullbackClosure.sharp_pullback_snd pE v hpE
  have hkp : Sharp (k ≫ q) := by rw [hkq]; exact hpX
  let sourceIso : pullback (k ≫ q) u ≅ pullback pX u := pullback.congrHom hkq rfl
  let targetIso := SharpPullbackClosure.nestedPullbackIso pE v u
  let t : pullback pX u ⟶ pullback pE (u ≫ v) :=
    sourceIso.inv ≫ ordinaryMap k q u ≫ targetIso.hom
  have ht : WeakEquivalence t := by
    let : WeakEquivalence (ordinaryMap k q u) := ordinaryMap_weak k q u hk hq hkp
    dsimp only [t]
    infer_instance
  have hrect : (f ≫ g) ≫ pE = pA ≫ (u ≫ v) := by
    calc
      (f ≫ g) ≫ pE = f ≫ (g ≫ pE) := Category.assoc _ _ _
      _ = f ≫ (pX ≫ v) := by rw [h2]
      _ = (f ≫ pX) ≫ v := (Category.assoc _ _ _).symm
      _ = (pA ≫ u) ≫ v := by rw [h1]
      _ = pA ≫ (u ≫ v) := Category.assoc _ _ _
  have hfactor : pullback.lift f pA h1 ≫ t = pullback.lift (f ≫ g) pA hrect := by
    apply pullback.hom_ext
    · simp [t, sourceIso, targetIso, k, q, ordinaryMap,
        SharpPullbackClosure.nestedPullbackIso, Category.assoc]
    · simp [t, sourceIso, targetIso, k, q, ordinaryMap,
        SharpPullbackClosure.nestedPullbackIso, Category.assoc]
  change WeakEquivalence (pullback.lift f pA h1 ≫ comparison pX u) ↔
    WeakEquivalence (pullback.lift (f ≫ g) pA hrect ≫ comparison pE (u ≫ v))
  rw [hc_iff_ordinaryLift_weak (CommSq.mk h1) hpX,
      hc_iff_ordinaryLift_weak (CommSq.mk hrect) hpE, ← hfactor]
  let : WeakEquivalence t := ht
  exact (weakEquivalence_postcomp_iff (pullback.lift f pA h1) t).symm

end SSet.RezkIncomingHC
