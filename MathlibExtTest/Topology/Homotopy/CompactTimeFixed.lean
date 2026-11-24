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

public import MathlibExt.Topology.Homotopy.CompactTimeFixed

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open scoped unitInterval

namespace MathlibExtTest.Topology.Homotopy.CompactTimeFixed

example {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (x₀ : X) (y₀ : Y) (τ : Z → unitInterval)
    (z₀ : Z) :
    ContinuousAt (fun _ : Z => y₀) z₀ :=
  ContinuousMap.continuousAt_comp_arbitrary_compact_time_of_forall_eq
    (ContinuousMap.const (unitInterval × X) y₀) x₀ y₀ (fun _ => rfl)
    (fun _ => x₀) τ z₀ continuousAt_const rfl

example {T X Y Z : Type*} [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : C(T × X, Y)) (x₀ : X) (y₀ : Y)
    (hF : ∀ t : T, F (t, x₀) = y₀)
    (g : Z → X) (τ : Z → T) (z₀ : Z)
    (hg : ContinuousAt g z₀) (hg₀ : g z₀ = x₀) :
    ContinuousAt (fun z => F (τ z, g z)) z₀ :=
  ContinuousMap.continuousAt_comp_arbitrary_compact_time_of_forall_eq
    F x₀ y₀ hF g τ z₀ hg hg₀

example {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f₀ f₁ : C(X, Y)} {S : Set X}
    (F : ContinuousMap.HomotopyRel f₀ f₁ S)
    (g : Z → X) (τ : Z → unitInterval) (z₀ : Z)
    (hg : ContinuousAt g z₀) (hz₀ : g z₀ ∈ S) :
    ContinuousAt (fun z => F (τ z, g z)) z₀ :=
  ContinuousMap.HomotopyRel.continuousAt_comp_arbitrary_time_of_mem
    F g τ z₀ hg hz₀

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (τ : X → unitInterval) (x₀ : X) :
    ContinuousAt
      (fun z => ContinuousMap.HomotopyRel.refl f Set.univ (τ z, z))
      x₀ :=
  ContinuousMap.HomotopyRel.continuousAt_comp_arbitrary_time_of_mem
    (ContinuousMap.HomotopyRel.refl f Set.univ) id τ x₀
    continuousAt_id trivial

end MathlibExtTest.Topology.Homotopy.CompactTimeFixed

end
