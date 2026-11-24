/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.CompactlyGenerated.FiniteRealization

/-!
# Tests for finite realizations in compactly generated spaces

The owners exercise independent probe/carrier universes, the neutral class
values, the finite Sigma smallness argument, literal bundled carriers and
topologies, premise deletion, privacy, and trust.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u v

namespace MathlibExtTest.SSet.CompactlyGeneratedFiniteRealization

#check @SSet.uCompactlyGeneratedSpace_realization_of_finite
#check @SSet.uWeakHausdorffSpace_realization_of_finite
#check @SSet.toCompactlyGeneratedOfFinite

section Generic

variable (K : SSet.{v}) [K.Finite]

example : UCompactlyGeneratedSpace.{u} (SSet.toTop.obj K) :=
  SSet.uCompactlyGeneratedSpace_realization_of_finite K

example : UWeakHausdorffSpace.{u} (SSet.toTop.obj K) :=
  SSet.uWeakHausdorffSpace_realization_of_finite K

example : CompactlyGenerated.{u, v} :=
  SSet.toCompactlyGeneratedOfFinite K

example : (SSet.toCompactlyGeneratedOfFinite.{u, v} K).toTop =
    SSet.toTop.obj K := rfl

example :
    (inferInstance : TopologicalSpace
      (SSet.toCompactlyGeneratedOfFinite.{u, v} K)) =
        (inferInstance : TopologicalSpace (SSet.toTop.obj K)) := rfl

example : Small.{u}
    (Σ s : K.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) := by
  let _ : Small.{u} K.N := small_map (Finite.equivFin K.N)
  infer_instance

example : Small.{u} (SSet.toTop.obj K) := by
  let _ : Small.{u} K.N := small_map (Finite.equivFin K.N)
  let _ : ∀ s : K.N,
      Small.{u} (Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :=
    fun _ => inferInstance
  let _ : Small.{u}
      (Σ s : K.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :=
    inferInstance
  exact small_of_surjective (SSet.surjective_sigmaToTop K)

end Generic

section ExplicitUniverses

variable (K₀ : SSet.{0}) [K₀.Finite]
variable (K₁ : SSet.{1}) [K₁.Finite]

example : CompactlyGenerated.{0, 0} :=
  SSet.toCompactlyGeneratedOfFinite.{0, 0} K₀

example : CompactlyGenerated.{1, 1} :=
  SSet.toCompactlyGeneratedOfFinite.{1, 1} K₁

example : CompactlyGenerated.{0, 1} :=
  SSet.toCompactlyGeneratedOfFinite.{0, 1} K₁

example : CompactlyGenerated.{1, 0} :=
  SSet.toCompactlyGeneratedOfFinite.{1, 0} K₀

end ExplicitUniverses

section MissingFiniteness

variable (K : SSet.{v})

example : True := by
  fail_if_success
    let _ : UCompactlyGeneratedSpace.{u} (SSet.toTop.obj K) :=
      SSet.uCompactlyGeneratedSpace_realization_of_finite K
  fail_if_success
    let _ : UWeakHausdorffSpace.{u} (SSet.toTop.obj K) :=
      SSet.uWeakHausdorffSpace_realization_of_finite K
  fail_if_success
    let _ : CompactlyGenerated.{u, v} :=
      SSet.toCompactlyGeneratedOfFinite K
  trivial

end MissingFiniteness

#guard_msgs (error, substring := true) in
#check SSet.realization_small_of_finite

#guard_msgs (error, substring := true) in
#check SSet.uCompactlyGeneratedSpace_of_small_compact_t2

#print axioms SSet.uCompactlyGeneratedSpace_realization_of_finite
#print axioms SSet.uWeakHausdorffSpace_realization_of_finite
#print axioms SSet.toCompactlyGeneratedOfFinite

end MathlibExtTest.SSet.CompactlyGeneratedFiniteRealization
