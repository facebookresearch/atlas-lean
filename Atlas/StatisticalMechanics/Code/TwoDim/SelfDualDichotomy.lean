/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Code.Universality.KestenHalf
import Code.RSW.SelfDuality

open MeasureTheory Set Filter Topology SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality














noncomputable def kdi_rotEdgeEquiv : Sym2 (Site 2) ≃ Sym2 (Site 2) := sym2Congr rot90Equiv





noncomputable def kdi_rotConfig :
    ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) kdi_rotEdgeEquiv



theorem kdi_measurable_rotConfig : Measurable kdi_rotConfig :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool) kdi_rotEdgeEquiv).measurable







theorem kdi_map_rotConfig :
    Measure.map kdi_rotConfig halfMeasure = halfMeasure := by
  rw [kdi_rotConfig, halfMeasure]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one) kdi_rotEdgeEquiv




theorem kdi_rotConfig_measurePreserving :
    MeasurePreserving kdi_rotConfig halfMeasure halfMeasure :=
  ⟨kdi_measurable_rotConfig, kdi_map_rotConfig⟩












theorem kdi_selfDualRotation_preserves_half
    (R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure) :
    Measure.map (R ∘ dualConfig) halfMeasure = halfMeasure :=
  selfDualRotation_preserves_half R hRmeas hRpres




























theorem kdi_selfDual_crossing_half
    {H : Set (ConfigSpace (Sym2 (Site 2)))} (hHm : MeasurableSet H)
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : Hᶜ = (R ∘ dualConfig) ⁻¹' H) :
    halfMeasure.real H = 1 / 2 :=
  half_crossingProb_of_selfDual_dichotomy hHm hRmeas hRpres hdich








theorem kdi_crossing_balance_family
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n)) :
    ∀ n : ℕ, halfMeasure.real (boxFam n) = 1 / 2 := fun n =>
  kdi_selfDual_crossing_half (hHm n) hRmeas hRpres (hdich n)















theorem kdi_crossingPair_incompatible (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) :
    ¬ (ω e = true ∧ dualConfig ω (crossEdge e) = true) :=
  StatMech.RSW.crossingPair_incompatible ω e









theorem kdi_blocking (ω : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y)
    {x' y' : Site 2} (w' : (openSubgraph 2 (dualConfig ω)).Walk x' y')
    (e : Sym2 (Site 2)) (he : e ∈ w.edges) (he' : crossEdge e ∈ w'.edges) :
    False :=
  StatMech.RSW.openWalk_blocks_dualWalk ω w w' e he he'

















theorem kdi_selfDual_crossing_half_rot
    {H : Set (ConfigSpace (Sym2 (Site 2)))} (hHm : MeasurableSet H)
    (hdich : Hᶜ = (kdi_rotConfig ∘ dualConfig) ⁻¹' H) :
    halfMeasure.real H = 1 / 2 :=
  kdi_selfDual_crossing_half hHm kdi_measurable_rotConfig kdi_map_rotConfig hdich







theorem kdi_crossing_balance_family_rot
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hdich : ∀ n, (boxFam n)ᶜ = (kdi_rotConfig ∘ dualConfig) ⁻¹' (boxFam n)) :
    ∀ n : ℕ, halfMeasure.real (boxFam n) = 1 / 2 := fun n =>
  kdi_selfDual_crossing_half_rot (hHm n) (hdich n)

end TwoDim

end StatMech
