/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ScottishBook42

/-! Check the fixed-point theorem in dimension zero and for reflection in the origin. -/

open MathlibExt.Topology.ScottishBook42Wanted

namespace MathlibExtTest.Topology.ScottishBook42

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
private noncomputable abbrev ball (n : ℕ) : Set (E n) := Metric.closedBall 0 1

example (f : Set (E 0) → Set (E 0))
    (hf : ∀ X : Set (E 0), X ⊆ ball 0 → IsCompact X → Convex ℝ X → X.Nonempty →
      f X ⊆ ball 0 ∧ IsCompact (f X) ∧ Convex ℝ (f X) ∧ (f X).Nonempty) :
    f {0} = {0} := by
  have eq_singleton (X : Set (E 0)) (hX : X.Nonempty) : X = {0} :=
    (Subsingleton.eq_univ_of_nonempty hX).trans
      (Subsingleton.eq_univ_of_nonempty (Set.singleton_nonempty 0)).symm
  have hcont : HausdorffContinuousOnConvexCompacts f (ball 0) := by
    intro X _ _ _ hX ε hε
    refine ⟨ε, hε, fun Y _ _ _ hY _ => ?_⟩
    simpa only [eq_singleton X hX, eq_singleton Y hY, Metric.hausdorffDist_self_zero] using hε
  obtain ⟨X, _, _, _, hX, hfix⟩ := fixed_point_for_convex_hyperspace_map 0 f hf hcont
  simpa only [eq_singleton X hX] using hfix

example : ∃ X : Set (E 1), X ⊆ ball 1 ∧ IsCompact X ∧ Convex ℝ X ∧ X.Nonempty ∧
    (fun x => -x) '' X = X := by
  apply fixed_point_for_convex_hyperspace_map 1 (fun X => (fun x => -x) '' X)
  · intro X hX hcompact hconv hne
    refine ⟨?_, hcompact.image continuous_neg, ?_, hne.image _⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxB := hX hx
      simpa [ball, Metric.mem_closedBall, dist_zero_right] using hxB
    · simpa only [Set.image_neg_eq_neg] using hconv.neg
  · intro X _ _ _ _ ε hε
    refine ⟨ε, hε, fun Y _ _ _ _ hXY => ?_⟩
    simpa only [Metric.hausdorffDist_image isometry_neg] using hXY

end MathlibExtTest.Topology.ScottishBook42
