/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2SpanPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2SectionPairs

/-! The full actual section group acts on the intrinsic physical A2-plane carrier. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem span_neg_singleton (x : Fin 24 → ℝ) :
    Submodule.span ℝ {-x} = Submodule.span ℝ {x} := by
  simpa only [neg_one_smul] using
    Submodule.span_singleton_smul_eq (isUnit_neg_one : IsUnit (-1 : ℝ)) x

/-- The full genuine section group preserves the intrinsic actual A2-plane set. -/
theorem leechSeventhE8A2Planes_map_mem (g : leechSeventhE8SectionGroup)
    (W : Submodule ℝ (Fin 24 → ℝ)) (hW : W ∈ leechSeventhE8A2Planes) :
    W.map g.val.val.toLinearMap ∈ leechSeventhE8A2Planes := by
  rcases hW with ⟨r, s, hrs, rfl⟩
  refine ⟨leechSeventhE8SectionRootIndex g r, leechSeventhE8SectionRootIndex g s,
    leechSeventhE8SectionRoot_nonorthogonal g r s hrs, ?_⟩
  rw [Submodule.map_span, Set.image_pair]
  change Submodule.span ℝ {g.val.val (leechSeventhE8RealRoot r),
    g.val.val (leechSeventhE8RealRoot s)} =
      Submodule.span ℝ {leechSeventhE8RealRoot (leechSeventhE8SectionRootIndex g r),
        leechSeventhE8RealRoot (leechSeventhE8SectionRootIndex g s)}
  rcases leechSeventhE8SectionRoot_real_sign g r with hr | hr <;>
    rcases leechSeventhE8SectionRoot_real_sign g s with hs | hs <;>
    rw [hr, hs] <;>
    simp only [Submodule.span_insert, span_neg_singleton]

/-- The actual full section group acts by genuine real submodule images on all A2 planes. -/
instance : MulAction leechSeventhE8SectionGroup leechSeventhE8A2Planes where
  smul g W := ⟨W.val.map g.val.val.toLinearMap, leechSeventhE8A2Planes_map_mem g _ W.property⟩
  one_smul W := by
    apply Subtype.ext
    change W.val.map LinearMap.id = W.val
    exact Submodule.map_id _
  mul_smul g h W := by
    apply Subtype.ext
    change W.val.map (g * h).val.val.toLinearMap =
      (W.val.map h.val.val.toLinearMap).map g.val.val.toLinearMap
    rw [← Submodule.map_comp]
    rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
