/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Compact

/-!
# Berge's maximum theorem

For a jointly continuous objective `f : X → Y → ℝ` and a correspondence `φ : X → Set Y` with
nonempty compact values that is both upper and lower hemicontinuous, the value function
`x ↦ sSup (f x '' φ x)` is continuous and the argmax correspondence
`x ↦ {y ∈ φ x | ∀ y' ∈ φ x, f x y' ≤ f x y}` is upper hemicontinuous. `X` and `Y` are arbitrary
topological spaces. Mathlib's `IsCompact.continuous_sSup` is the special case of a constant
feasible set.

## Main statements

* `MathlibExt.Topology.BergeMaximum.berge_maximum_continuous_value`
* `MathlibExt.Topology.BergeMaximum.berge_maximum_upperHemicontinuous_argmax`

## References

* C. Berge, *Topological Spaces* (1963), Chapter VI, §3, Maximum Theorem.
* C. D. Aliprantis and K. C. Border, *Infinite Dimensional Analysis*, 3rd ed. (2006),
  Theorem 17.31.
-/

@[expose] public section

open Topology Filter Set

namespace MathlibExt.Topology.BergeMaximum

private theorem m07t02_lowerSemicontinuousAt_value {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y → ℝ} {φ : X → Set Y} {x₀ : X}
    (hf : Continuous ↿f) (hφc : ∀ x, IsCompact (φ x)) (hφne : ∀ x, (φ x).Nonempty)
    (hφl : LowerHemicontinuous φ) :
    LowerSemicontinuousAt (fun x => sSup (f x '' φ x)) x₀ := by
  rw [lowerSemicontinuousAt_iff]
  intro z hz
  change z < sSup (f x₀ '' φ x₀) at hz
  obtain ⟨y₀, hy₀φ, hsup, -⟩ :=
    (hφc x₀).exists_sSup_image_eq_and_ge (hφne x₀)
      ((show Continuous (f x₀) from hf.comp (.prodMk_right x₀)).continuousOn)
  rw [hsup] at hz
  have hopen : IsOpen (↿f ⁻¹' Ioi z) := isOpen_Ioi.preimage hf
  obtain ⟨U, W, hU, hW, hx₀U, hy₀W, hUW⟩ := (isOpen_prod_iff.mp hopen) x₀ y₀ hz
  have hev := (lowerHemicontinuousAt_iff.mp (hφl x₀)) W hW ⟨y₀, hy₀φ, hy₀W⟩
  filter_upwards [hev, hU.mem_nhds hx₀U] with x' hx'W hx'U
  obtain ⟨y', hy'φ, hy'W⟩ := hx'W
  have hlt : z < f x' y' := hUW (mk_mem_prod hx'U hy'W)
  refine hlt.trans_le (le_csSup ?_ (mem_image_of_mem (f x') hy'φ))
  exact (hφc x').bddAbove_image
    ((show Continuous (f x') from hf.comp (.prodMk_right x')).continuousOn)

private theorem m07t02_upperSemicontinuousAt_value {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y → ℝ} {φ : X → Set Y} {x₀ : X}
    (hf : Continuous ↿f) (hφc : ∀ x, IsCompact (φ x)) (hφne : ∀ x, (φ x).Nonempty)
    (hφu : UpperHemicontinuous φ) :
    UpperSemicontinuousAt (fun x => sSup (f x '' φ x)) x₀ := by
  rw [upperSemicontinuousAt_iff]
  intro z hz
  change sSup (f x₀ '' φ x₀) < z at hz
  obtain ⟨_, _, hsup, hge⟩ :=
    (hφc x₀).exists_sSup_image_eq_and_ge (hφne x₀)
      ((show Continuous (f x₀) from hf.comp (.prodMk_right x₀)).continuousOn)
  rw [hsup] at hz
  have hsub : ({x₀} : Set X) ×ˢ φ x₀ ⊆ ↿f ⁻¹' Iio z := by
    rintro ⟨x', y'⟩ ⟨(rfl : x' = x₀), hy'⟩
    exact (hge y' hy').trans_lt hz
  obtain ⟨N, W, hN, hW, hx₀N, hφW, hNW⟩ :=
    generalized_tube_lemma isCompact_singleton (hφc x₀) (isOpen_Iio.preimage hf) hsub
  have hev := hφu.forall_isOpen x₀ W hW hφW
  filter_upwards [hev, hN.mem_nhds (singleton_subset_iff.mp hx₀N)] with x' hx'φ hx'N
  change sSup (f x' '' φ x') < z
  rw [(hφc x').sSup_lt_iff_of_continuous (hφne x')
    ((show Continuous (f x') from hf.comp (.prodMk_right x')).continuousOn) z]
  intro y' hy'
  exact hNW (mk_mem_prod hx'N (hx'φ hy'))

/--
Berge's maximum theorem, value part. Let `φ : X → Set Y` be a correspondence with nonempty
compact values that is both upper and lower hemicontinuous, and let the objective
`f : X → Y → ℝ` be jointly continuous. Then the value function
`x ↦ sSup (f x '' φ x)` is continuous. (With `φ` constant this is Mathlib's
`IsCompact.continuous_sSup`.)
-/
theorem berge_maximum_continuous_value {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y → ℝ} {φ : X → Set Y}
    (hf : Continuous ↿f) (hφc : ∀ x, IsCompact (φ x)) (hφne : ∀ x, (φ x).Nonempty)
    (hφu : UpperHemicontinuous φ) (hφl : LowerHemicontinuous φ) :
    Continuous fun x => sSup (f x '' φ x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [continuousAt_iff_lower_upperSemicontinuousAt]
  exact ⟨m07t02_lowerSemicontinuousAt_value hf hφc hφne hφl,
    m07t02_upperSemicontinuousAt_value hf hφc hφne hφu⟩

/--
Berge's maximum theorem, maximizer part. Under the same hypotheses, the argmax
correspondence `x ↦ {y ∈ φ x | ∀ y' ∈ φ x, f x y' ≤ f x y}` is upper hemicontinuous.
-/
theorem berge_maximum_upperHemicontinuous_argmax {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y → ℝ} {φ : X → Set Y}
    (hf : Continuous ↿f) (hφc : ∀ x, IsCompact (φ x)) (hφne : ∀ x, (φ x).Nonempty)
    (hφu : UpperHemicontinuous φ) (hφl : LowerHemicontinuous φ) :
    UpperHemicontinuous fun x => {y ∈ φ x | ∀ y' ∈ φ x, f x y' ≤ f x y} := by
  refine UpperHemicontinuous.of_forall_isOpen fun x₀ W hW hAW => ?_
  show ∀ᶠ x' in 𝓝 x₀, {y ∈ φ x' | ∀ y' ∈ φ x', f x' y' ≤ f x' y} ⊆ W
  have hK : IsCompact (φ x₀ ∩ Wᶜ) := (hφc x₀).inter_right hW.isClosed_compl
  rcases eq_empty_or_nonempty (φ x₀ ∩ Wᶜ) with hKe | hKne
  · have hφW : φ x₀ ⊆ W := by
      intro y hyφ
      by_contra hyW
      have hmem : y ∈ φ x₀ ∩ Wᶜ := ⟨hyφ, hyW⟩
      rw [hKe] at hmem
      simp at hmem
    filter_upwards [hφu.forall_isOpen x₀ W hW hφW] with x' hx'
    intro y hy
    exact hx' hy.1
  · obtain ⟨y₀, hy₀φ, hsup, hge⟩ :=
      (hφc x₀).exists_sSup_image_eq_and_ge (hφne x₀)
        ((show Continuous (f x₀) from hf.comp (.prodMk_right x₀)).continuousOn)
    have hcontK : ContinuousOn (f x₀) (φ x₀ ∩ Wᶜ) :=
      (show Continuous (f x₀) from hf.comp (.prodMk_right x₀)).continuousOn.mono
        inter_subset_left
    obtain ⟨yK, hyK, _, hgeK⟩ := hK.exists_sSup_image_eq_and_ge hKne hcontK
    have hyKφ : yK ∈ φ x₀ := hyK.1
    have hyKW : yK ∉ W := hyK.2
    have hnotmax : ∃ y' ∈ φ x₀, f x₀ yK < f x₀ y' := by
      by_contra hcon
      have hmem : yK ∈ {y ∈ φ x₀ | ∀ y' ∈ φ x₀, f x₀ y' ≤ f x₀ y} := by
        refine ⟨hyKφ, fun y' hy' => ?_⟩
        by_contra hle
        rw [not_le] at hle
        exact hcon ⟨y', hy', hle⟩
      exact hyKW (hAW hmem)
    obtain ⟨y', hy'φ, hlt'⟩ := hnotmax
    have hlt : f x₀ yK < sSup (f x₀ '' φ x₀) := by
      rw [hsup]
      exact hlt'.trans_le (hge y' hy'φ)
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hsubK : ({x₀} : Set X) ×ˢ (φ x₀ ∩ Wᶜ) ⊆ ↿f ⁻¹' Iio c := by
      rintro ⟨x', y⟩ ⟨(rfl : x' = x₀), hyKmem⟩
      exact (hgeK y hyKmem).trans_lt hc1
    obtain ⟨N, W', hN, hW', hx₀N, hKW', hNW'⟩ :=
      generalized_tube_lemma isCompact_singleton hK (isOpen_Iio.preimage hf) hsubK
    have hφWW' : φ x₀ ⊆ W ∪ W' := by
      intro y hyφ
      by_cases hyW : y ∈ W
      · exact Or.inl hyW
      · exact Or.inr (hKW' ⟨hyφ, hyW⟩)
    have hevU := hφu.forall_isOpen x₀ (W ∪ W') (hW.union hW') hφWW'
    have hLSC := m07t02_lowerSemicontinuousAt_value hf hφc hφne hφl (x₀ := x₀)
    have hevL := (lowerSemicontinuousAt_iff.mp hLSC) c hc2
    filter_upwards [hevU, hevL, hN.mem_nhds (singleton_subset_iff.mp hx₀N)] with x' hx'φ hcV hx'N
    intro y hy
    have hyφ : y ∈ φ x' := hy.1
    have hmax : ∀ y' ∈ φ x', f x' y' ≤ f x' y := hy.2
    rcases hx'φ hyφ with hyW | hyW'
    · exact hyW
    · have hlt2 : f x' y < c := hNW' (mk_mem_prod hx'N hyW')
      have hatt : f x' y = sSup (f x' '' φ x') := by
        apply le_antisymm
        · exact le_csSup ((hφc x').bddAbove_image
              ((show Continuous (f x') from hf.comp (.prodMk_right x')).continuousOn))
            (mem_image_of_mem (f x') hyφ)
        · exact csSup_le ((hφne x').image (f x'))
            (by rintro _ ⟨z, hz, rfl⟩; exact hmax z hz)
      rw [hatt] at hlt2
      exact (lt_irrefl _ (lt_trans hlt2 hcV)).elim

end MathlibExt.Topology.BergeMaximum
