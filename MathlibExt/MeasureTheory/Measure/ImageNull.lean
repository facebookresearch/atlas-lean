/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Topology.NhdsWithin

/-!
# Images of locally null sets

A set in a second-countable space whose image is locally null has null image.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory

variable {X Y : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y]
variable {μ : Measure Y} {f : X → Y} {s : Set X}

/-- **Sets with locally null image have null image.** Let $X$ be a second-countable topological
space, $Y$ a measurable space with a measure $\mu$, $f : X \to Y$ a function and $s \subseteq X$.
If every point $x \in s$ has a neighbourhood $V$ with $\mu(f(V \cap s)) = 0$, then
$\mu(f(s)) = 0$.

Here $\mu$ is evaluated as an outer measure, so the images need not be measurable. -/
theorem measure_image_null_of_locally_null
    (h : ∀ x ∈ s, ∃ V ∈ nhds x, μ (f '' (V ∩ s)) = 0) :
    μ (f '' s) = 0 := by
  have hall : ∀ x : X, ∃ V ∈ nhds x, (x ∈ s → μ (f '' (V ∩ s)) = 0) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨V, hVm, hVn⟩ := h x hx
      exact ⟨V, hVm, fun _ => hVn⟩
    · exact ⟨Set.univ, Filter.univ_mem, fun hcon => absurd hcon hx⟩
  choose V hVmem hVnull using hall
  have hmem : ∀ x ∈ s, V x ∈ nhdsWithin x s := fun x hx =>
    mem_nhdsWithin_of_mem_nhds (hVmem x)
  obtain ⟨T, hTsub, hTcount, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin hmem
  have hsub : f '' s ⊆ ⋃ x ∈ T, f '' (V x ∩ s) := by
    intro y hy
    obtain ⟨x, hxS, rfl⟩ := hy
    have hxU : x ∈ ⋃ x ∈ T, V x := hcover hxS
    simp only [Set.mem_iUnion] at hxU
    obtain ⟨z, hzT, hzx⟩ := hxU
    simp only [Set.mem_iUnion]
    exact ⟨z, hzT, Set.mem_image_of_mem f ⟨hzx, hxS⟩⟩
  have hnull : μ (⋃ x ∈ T, f '' (V x ∩ s)) = 0 := by
    rw [measure_biUnion_null_iff hTcount]
    intro z hz
    exact hVnull z (hTsub hz)
  exact measure_mono_null hsub hnull

end MathlibExt.MeasureTheory
