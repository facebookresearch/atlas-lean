/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Path
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Induced length metric and length spaces

This module defines the induced length metric on a pseudoemetric space and the
property of being a length space.

Given `x y : X`, `Metric.inducedLengthEdist x y` is the infimum of the lengths
of all paths from `x` to `y`, where the length of a path is Mathlib's
`eVariationOn`. It takes the value `⊤` when no path joins `x` to `y`. For a
subset `A` with the inherited metric, the length metric of `A` is
`inducedLengthEdist` on the subtype `A`.

## Main definitions

* `Metric.inducedLengthEdist`: the induced length metric.
* `Metric.IsLengthSpace`: the property that the induced length metric agrees
  with `edist`.

## Main results

* `Metric.edist_le_inducedLengthEdist`: the distance is at most the induced
  length distance.
* `Metric.inducedLengthEdist_le_eVariationOn`: the induced length distance is
  at most the length of any joining path.
* `Metric.inducedLengthEdist_self`: the induced length distance from a point
  to itself is `0`.
* `Metric.inducedLengthEdist_comm`: symmetry of the induced length metric.
* `Metric.inducedLengthEdist_eq_top_of_isEmpty`: the induced length distance
  is `⊤` when there is no path.
* `Metric.isLengthSpace_iff_le`: `X` is a length space iff the induced length
  metric is everywhere at most `edist`.
* `Path.eVariationOn_trans_le`: the length of a concatenation is at most the
  sum of the lengths of the two pieces.
* `Metric.inducedLengthEdist_triangle`: the triangle inequality for the
  induced length metric.

## References

* AKP, *Alexandrov geometry: foundations*, AMS GSM 236, 2024
  (arXiv:1903.08539v6), Section "Length spaces".
-/

@[expose] public section

open scoped ENNReal unitInterval

noncomputable section

/-- A concatenation is no longer than its two pieces together. -/
theorem Path.eVariationOn_trans_le {X : Type*} [PseudoEMetricSpace X] {x y z : X}
    (γ : Path x y) (δ : Path y z) :
    eVariationOn (⇑(γ.trans δ)) Set.univ ≤
      eVariationOn (⇑γ) Set.univ + eVariationOn (⇑δ) Set.univ := by
  let b : ↥I := ⟨1 / 2, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩
  have h0b : (0 : ↥I) ≤ b := Subtype.coe_le_coe.mp (by change (0 : ℝ) ≤ 1 / 2; norm_num)
  have hb1 : b ≤ (1 : ↥I) := Subtype.coe_le_coe.mp (by change (1 : ℝ) / 2 ≤ 1; norm_num)
  let φ : ↥I → ↥I := fun t => Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (t : ℝ))
  let ψ : ↥I → ↥I := fun t => Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (t : ℝ) - 1)
  have hφ : Monotone φ := by
    intro a c hac
    exact Set.monotone_projIcc zero_le_one (by
      have hle : (a : ℝ) ≤ (c : ℝ) := Subtype.coe_le_coe.mp hac
      linarith)
  have hψ : Monotone ψ := by
    intro a c hac
    exact Set.monotone_projIcc zero_le_one (by
      have hle : (a : ℝ) ≤ (c : ℝ) := Subtype.coe_le_coe.mp hac
      linarith)
  have hφOn : MonotoneOn φ (Set.univ ∩ Set.Icc (0 : ↥I) b) := hφ.monotoneOn _
  have hψOn : MonotoneOn ψ (Set.univ ∩ Set.Icc b (1 : ↥I)) := hψ.monotoneOn _
  have hφmaps : Set.MapsTo φ (Set.univ ∩ Set.Icc (0 : ↥I) b) Set.univ :=
    fun _ _ => Set.mem_univ _
  have hψmaps : Set.MapsTo ψ (Set.univ ∩ Set.Icc b (1 : ↥I)) Set.univ :=
    fun _ _ => Set.mem_univ _
  have heq1 : Set.EqOn (⇑(γ.trans δ)) (⇑γ ∘ φ) (Set.univ ∩ Set.Icc (0 : ↥I) b) := by
    intro t ht
    obtain ⟨-, htIcc⟩ := ht
    rw [Set.mem_Icc] at htIcc
    obtain ⟨-, htb⟩ := htIcc
    have hle : (t : ℝ) ≤ 1 / 2 := Subtype.coe_le_coe.mp htb
    have hnn : (0 : ℝ) ≤ (t : ℝ) := unitInterval.nonneg t
    have hmem : (2 * (t : ℝ)) ∈ Set.Icc (0 : ℝ) (1 : ℝ) :=
      Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hproj : φ t = ⟨2 * (t : ℝ), hmem⟩ := Set.projIcc_of_mem _ hmem
    simp only [Function.comp_apply]
    rw [Path.trans_apply γ δ t, dite_eq_left hle, hproj]
  have heq2 : Set.EqOn (⇑(γ.trans δ)) (⇑δ ∘ ψ) (Set.univ ∩ Set.Icc b (1 : ↥I)) := by
    intro t ht
    obtain ⟨-, htIcc⟩ := ht
    rw [Set.mem_Icc] at htIcc
    obtain ⟨hbt, -⟩ := htIcc
    have hge : (1 : ℝ) / 2 ≤ (t : ℝ) := Subtype.coe_le_coe.mp hbt
    have hle1 : (t : ℝ) ≤ 1 := unitInterval.le_one t
    by_cases hle : (t : ℝ) ≤ 1 / 2
    · have heq : (t : ℝ) = 1 / 2 := le_antisymm hle hge
      have hL : (γ.trans δ) t = y := by
        simp only [Path.trans_apply γ δ t, dite_eq_left hle]
        have hval : (2 : ℝ) * (t : ℝ) = 1 := by rw [heq]; norm_num
        convert Path.target γ using 2
        apply Subtype.ext
        change (2 : ℝ) * (t : ℝ) = 1
        exact hval
      have hR : (⇑δ ∘ ψ) t = y := by
        simp only [Function.comp_apply]
        have h0 : (2 : ℝ) * (t : ℝ) - 1 = 0 := by rw [heq]; norm_num
        have hmem0 : (2 * (t : ℝ) - 1) ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by
          rw [h0]
          exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩
        have hproj0 : ψ t = ⟨2 * (t : ℝ) - 1, hmem0⟩ := Set.projIcc_of_mem _ hmem0
        rw [hproj0]
        convert Path.source δ using 2
        apply Subtype.ext
        change (2 : ℝ) * (t : ℝ) - 1 = 0
        exact h0
      exact hL.trans hR.symm
    · have hmem : (2 * (t : ℝ) - 1) ∈ Set.Icc (0 : ℝ) (1 : ℝ) :=
        Set.mem_Icc.mpr ⟨by
          have hlt : (1 : ℝ) / 2 < (t : ℝ) := not_le.mp hle
          linarith, by linarith⟩
      have hproj : ψ t = ⟨2 * (t : ℝ) - 1, hmem⟩ := Set.projIcc_of_mem _ hmem
      simp only [Function.comp_apply]
      rw [Path.trans_apply γ δ t, dite_eq_right hle, hproj]
  have h1 : eVariationOn (⇑(γ.trans δ)) (Set.univ ∩ Set.Icc (0 : ↥I) b) ≤
      eVariationOn (⇑γ) Set.univ := by
    rw [eVariationOn.eq_of_eqOn heq1]
    exact eVariationOn.comp_le_of_monotoneOn (⇑γ) φ hφOn hφmaps
  have h2 : eVariationOn (⇑(γ.trans δ)) (Set.univ ∩ Set.Icc b (1 : ↥I)) ≤
      eVariationOn (⇑δ) Set.univ := by
    rw [eVariationOn.eq_of_eqOn heq2]
    exact eVariationOn.comp_le_of_monotoneOn (⇑δ) ψ hψOn hψmaps
  have hIcc : Set.univ ∩ Set.Icc (0 : ↥I) (1 : ↥I) = (Set.univ : Set ↥I) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_univ, true_and, iff_true]
    constructor
    · exact Subtype.coe_le_coe.mp (by change (0 : ℝ) ≤ (t : ℝ); exact unitInterval.nonneg t)
    · exact Subtype.coe_le_coe.mp (by change (t : ℝ) ≤ (1 : ℝ); exact unitInterval.le_one t)
  have hsplit :=
    eVariationOn.Icc_add_Icc (⇑(γ.trans δ)) (s := Set.univ) h0b hb1 (Set.mem_univ b)
  rw [hIcc] at hsplit
  rw [←hsplit]
  exact add_le_add h1 h2

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X]

/-- The induced length metric of AKP, *Alexandrov geometry: foundations*, AMS GSM 236,
2024 (arXiv:1903.08539v6), Section "Length spaces": the infimum of the lengths
`eVariationOn γ Set.univ` over all paths `γ : Path x y`. The length is Mathlib's
`eVariationOn`, the supremum over finite monotone sequences of sums of `edist`. It is
`⊤` when no path joins `x` to `y`. For `A ⊆ X`, the length metric of `A` induced by
the inherited metric is `inducedLengthEdist` on the subtype `A`. -/
def inducedLengthEdist (x y : X) : ℝ≥0∞ :=
  ⨅ γ : Path x y, eVariationOn (⇑γ) Set.univ

/-- `X` is a length space if the induced length metric agrees with `edist` for all
pairs; see AKP, *Alexandrov geometry: foundations*, AMS GSM 236, 2024
(arXiv:1903.08539v6), Section "Length spaces", Definition `def:length-space`. -/
def IsLengthSpace (X : Type*) [PseudoEMetricSpace X] : Prop :=
  ∀ x y : X, inducedLengthEdist x y = edist x y

/-- Every path's length is at least the distance of its endpoints. -/
theorem edist_le_inducedLengthEdist (x y : X) :
    edist x y ≤ inducedLengthEdist x y := by
  unfold inducedLengthEdist
  apply le_iInf
  intro γ
  have hle : edist (γ 0) (γ 1) ≤ eVariationOn (⇑γ) Set.univ :=
    eVariationOn.edist_le (⇑γ) (Set.mem_univ (0 : ↥I)) (Set.mem_univ (1 : ↥I))
  rw [Path.source γ, Path.target γ] at hle
  exact hle

/-- The induced length distance is at most the length of any joining path; it is the
infimum of the lengths of all such paths. -/
theorem inducedLengthEdist_le_eVariationOn {x y : X} (γ : Path x y) :
    inducedLengthEdist x y ≤ eVariationOn γ Set.univ := by
  unfold inducedLengthEdist
  exact iInf_le _ γ

/-- The constant path has length `0`. -/
theorem inducedLengthEdist_self (x : X) : inducedLengthEdist x x = 0 := by
  have hsub : Set.Subsingleton (⇑(Path.refl x) '' Set.univ) := by
    intro a ha b hb
    obtain ⟨t₁, _, rfl⟩ := ha
    obtain ⟨t₂, _, rfl⟩ := hb
    simp [Path.refl_apply]
  have h0 : eVariationOn (⇑(Path.refl x)) Set.univ = 0 :=
    eVariationOn.constant_on hsub
  have hle : inducedLengthEdist x x ≤ 0 := by
    unfold inducedLengthEdist
    calc (⨅ γ : Path x x, eVariationOn (⇑γ) Set.univ)
        ≤ eVariationOn (⇑(Path.refl x)) Set.univ := iInf_le _ (Path.refl x)
      _ = 0 := h0
  exact le_antisymm hle bot_le

/-- Reversing paths preserves length, so the induced length metric is symmetric. -/
theorem inducedLengthEdist_comm (x y : X) :
    inducedLengthEdist x y = inducedLengthEdist y x := by
  have hanti : AntitoneOn σ (Set.univ : Set ↥I) := by
    intro a _ b _ hab
    have hle : (a : ℝ) ≤ (b : ℝ) := Subtype.coe_le_coe.mpr hab
    have hle' : 1 - (b : ℝ) ≤ 1 - (a : ℝ) := sub_le_sub_left hle 1
    apply Subtype.coe_le_coe.mp
    simp only [unitInterval.coe_symm_eq]
    exact hle'
  have himg : σ '' (Set.univ : Set ↥I) = Set.univ := by
    ext z
    simp only [Set.mem_image, Set.mem_univ, true_and]
    exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨σ z, unitInterval.symm_symm z⟩⟩
  have hsymm : ∀ {a b : X} (γ : Path a b),
      eVariationOn (⇑(γ.symm)) Set.univ = eVariationOn (⇑γ) Set.univ := by
    intro a b γ
    have hfun : (⇑(γ.symm) : ↥I → X) = ⇑γ ∘ σ :=
      funext fun t ↦ Path.symm_apply γ t
    rw [hfun, eVariationOn.comp_eq_of_antitoneOn (⇑γ) σ hanti, himg]
  apply le_antisymm
  · unfold inducedLengthEdist
    apply le_iInf
    intro δ
    calc (⨅ γ : Path x y, eVariationOn (⇑γ) Set.univ)
        ≤ eVariationOn (⇑(δ.symm)) Set.univ := iInf_le _ (δ.symm)
      _ = eVariationOn (⇑δ) Set.univ := hsymm δ
  · unfold inducedLengthEdist
    apply le_iInf
    intro γ
    calc (⨅ δ : Path y x, eVariationOn (⇑δ) Set.univ)
        ≤ eVariationOn (⇑(γ.symm)) Set.univ := iInf_le _ (γ.symm)
      _ = eVariationOn (⇑γ) Set.univ := hsymm γ

/-- The infimum over an empty family of paths is `⊤`. -/
theorem inducedLengthEdist_eq_top_of_isEmpty {x y : X} (h : IsEmpty (Path x y)) :
    inducedLengthEdist x y = ⊤ := by
  unfold inducedLengthEdist
  apply le_antisymm le_top
  apply le_iInf
  intro γ
  exact (h.false γ).elim

/-- `X` is a length space iff the induced length distance is everywhere at most
`edist`. -/
theorem isLengthSpace_iff_le :
    IsLengthSpace X ↔ ∀ x y : X, inducedLengthEdist x y ≤ edist x y := by
  constructor
  · intro h x y
    exact (h x y).le
  · intro h x y
    exact le_antisymm (h x y) (edist_le_inducedLengthEdist x y)

/-- The induced length metric satisfies the triangle inequality. -/
theorem inducedLengthEdist_triangle (x y z : X) :
    inducedLengthEdist x z ≤ inducedLengthEdist x y + inducedLengthEdist y z := by
  unfold inducedLengthEdist
  apply ENNReal.le_iInf_add_iInf
  intro γ δ
  calc (⨅ γ_ : Path x z, eVariationOn (⇑γ_) Set.univ)
      ≤ eVariationOn (⇑(γ.trans δ)) Set.univ := iInf_le _ _
    _ ≤ eVariationOn (⇑γ) Set.univ + eVariationOn (⇑δ) Set.univ :=
        Path.eVariationOn_trans_le γ δ

end Metric
