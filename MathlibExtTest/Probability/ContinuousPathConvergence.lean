/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ContinuousPathConvergence
public import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Tests for continuous-path weak convergence

These tests restate the two public signatures, apply the convergence criterion
to constant and shrinking deterministic Dirac path laws on `C([0,2], ℝ)`, and
exercise the empty, singleton, repeated-coordinate, and endpoint projections.
The moving-spike counterexample to the theorem with tightness deleted is kept as
a non-proof numeric diagnostic in the associated review receipts.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

open MathlibExt.Probability.ContinuousPathConvergence

namespace MathlibExtTest.Probability.ContinuousPathConvergence

noncomputable section

/-- The finite-evaluation uniqueness theorem has no nonempty-coordinate
premise. -/
example (T : ℝ) (μ ν : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ))
    (h : ∀ I : Finset (Set.Icc (0 : ℝ) T),
      μ.map (fun f => I.restrict (fun t => f t)) =
        ν.map (fun f => I.restrict (fun t => f t))) :
    μ = ν :=
  continuousPath_measure_ext_of_finset_eval T μ ν h

/-- The convergence theorem exposes exactly tightness plus convergence of every
finite evaluation pushforward, while retaining the fixed positive horizon. -/
example (T : ℝ) (hT : 0 < T)
    (μs : ℕ → ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ))
    (μ : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ))
    (htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure C(Set.Icc (0 : ℝ) T, ℝ)) :
        Measure C(Set.Icc (0 : ℝ) T, ℝ)) | ν ∈ Set.range μs})
    (hfdd : ∀ I : Finset (Set.Icc (0 : ℝ) T),
      Tendsto
        (fun n => (μs n).map
          (fun f : C(Set.Icc (0 : ℝ) T, ℝ) =>
            I.restrict (fun t => f t)))
        atTop
        (𝓝 (μ.map
          (fun f : C(Set.Icc (0 : ℝ) T, ℝ) =>
            I.restrict (fun t => f t))))) :
    Tendsto μs atTop (𝓝 μ) :=
  tendsto_continuousPath_of_tight_of_finset_eval T hT μs μ htight hfdd

/-- A concrete nonconstant path used by the shrinking deterministic laws. -/
private noncomputable def unitPath : C(Set.Icc (0 : ℝ) 2, ℝ) where
  toFun t := t.1
  continuous_toFun := continuous_subtype_val

/-- The nonconstant deterministic path `t ↦ t / (n + 1)`. -/
private noncomputable def shrinkingPath (n : ℕ) :
    C(Set.Icc (0 : ℝ) 2, ℝ) :=
  (((n + 1 : ℕ) : ℝ)⁻¹) • unitPath

/-- The corresponding canonical probability law. -/
private noncomputable def shrinkingLaw (n : ℕ) :
    ProbabilityMeasure C(Set.Icc (0 : ℝ) 2, ℝ) :=
  diracProba (shrinkingPath n)

/-- The paths `t / (n + 1)` converge to zero in the canonical uniform path
topology, rather than merely in a pointwise function-space topology. -/
private theorem shrinkingPath_tendsto_zero :
    Tendsto shrinkingPath atTop
      (𝓝 (0 : C(Set.Icc (0 : ℝ) 2, ℝ))) := by
  have htop : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htop
  change Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹) • unitPath) atTop
    (𝓝 (0 : C(Set.Icc (0 : ℝ) 2, ℝ)))
  simpa only [zero_smul] using hinv.smul_const unitPath

/-- The shrinking Dirac laws converge directly by continuity of `diracProba`;
this supplies a compact range without assuming the criterion's conclusion. -/
private theorem shrinkingLaw_tendsto :
    Tendsto shrinkingLaw atTop
      (𝓝 (diracProba (0 : C(Set.Icc (0 : ℝ) 2, ℝ)))) := by
  exact (continuous_diracProba.tendsto _).comp shrinkingPath_tendsto_zero

/-- The shrinking-law family satisfies the theorem's genuine tightness
premise: its range has compact closure. -/
private theorem shrinkingLaw_isTightMeasureSet :
    IsTightMeasureSet
      {((ν : ProbabilityMeasure C(Set.Icc (0 : ℝ) 2, ℝ)) :
        Measure C(Set.Icc (0 : ℝ) 2, ℝ)) | ν ∈ Set.range shrinkingLaw} := by
  apply isTightMeasureSet_of_isCompact_closure
  have hcompact : IsCompact
      (insert (diracProba (0 : C(Set.Icc (0 : ℝ) 2, ℝ)))
        (Set.range shrinkingLaw)) :=
    shrinkingLaw_tendsto.isCompact_insert_range
  exact hcompact.of_isClosed_subset isClosed_closure
    (closure_minimal (Set.subset_insert _ _) hcompact.isClosed)

/-- The generic criterion applies to the concrete nonconstant laws
`dirac(t / (n + 1))` at horizon `T = 2`. Removing either tightness or the
uniform-path conclusion makes this compiled control fail. -/
private theorem shrinking_dirac_laws_converge_via_criterion :
    Tendsto shrinkingLaw atTop
      (𝓝 (diracProba (0 : C(Set.Icc (0 : ℝ) 2, ℝ)))) := by
  apply tendsto_continuousPath_of_tight_of_finset_eval 2 (by norm_num)
    shrinkingLaw (diracProba 0) shrinkingLaw_isTightMeasureSet
  intro I
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    shrinkingLaw (diracProba 0) shrinkingLaw_tendsto
    (continuous_pi fun t => continuous_eval_const
      (t : Set.Icc (0 : ℝ) 2))

/-- Constant Dirac laws give a second concrete satisfiability control, at a
nonzero constant path and horizon `T = 2`. -/
theorem constant_dirac_path_laws_converge (c : ℝ) :
    Tendsto
      (fun _ : ℕ => diracProba
        (ContinuousMap.const (Set.Icc (0 : ℝ) 2) c))
      atTop
      (𝓝 (diracProba
        (ContinuousMap.const (Set.Icc (0 : ℝ) 2) c))) := by
  apply tendsto_continuousPath_of_tight_of_finset_eval 2 (by norm_num)
  · have hsingleton : IsTightMeasureSet
        ({((diracProba (ContinuousMap.const (Set.Icc (0 : ℝ) 2) c) :
          ProbabilityMeasure C(Set.Icc (0 : ℝ) 2, ℝ)) :
          Measure C(Set.Icc (0 : ℝ) 2, ℝ))} :
          Set (Measure C(Set.Icc (0 : ℝ) 2, ℝ))) :=
      isTightMeasureSet_singleton
    apply IsTightMeasureSet.subset hsingleton
    rintro ρ ⟨ν, ⟨n, rfl⟩, rfl⟩
    rfl
  · intro I
    exact tendsto_const_nhds

/-- The canonical normalized sum of two distinct Dirac path laws. -/
private noncomputable def twoPathMixture :
    ProbabilityMeasure C(Set.Icc (0 : ℝ) 2, ℝ) :=
  (((diracProba
      (ContinuousMap.const (Set.Icc (0 : ℝ) 2) (0 : ℝ))).toFiniteMeasure +
    (diracProba
      (ContinuousMap.const (Set.Icc (0 : ℝ) 2)
        (1 : ℝ))).toFiniteMeasure).normalize)

/-- A finite two-path mixture supplies a non-Dirac probability-law control for
the generic convergence criterion. -/
private theorem two_path_mixture_laws_converge :
    Tendsto (fun _ : ℕ => twoPathMixture) atTop (𝓝 twoPathMixture) := by
  apply tendsto_continuousPath_of_tight_of_finset_eval 2 (by norm_num)
  · have hsingleton : IsTightMeasureSet
        ({(twoPathMixture : Measure C(Set.Icc (0 : ℝ) 2, ℝ))} :
          Set (Measure C(Set.Icc (0 : ℝ) 2, ℝ))) :=
      isTightMeasureSet_singleton
    apply IsTightMeasureSet.subset hsingleton
    rintro ρ ⟨ν, ⟨n, rfl⟩, rfl⟩
    rfl
  · intro I
    exact tendsto_const_nhds

/-- The required path topology and Borel separation instances synthesize at
the non-unit horizon used by the controls. -/
example : PolishSpace C(Set.Icc (0 : ℝ) 2, ℝ) := inferInstance
example : BorelSpace C(Set.Icc (0 : ℝ) 2, ℝ) := inferInstance
example : T2Space C(Set.Icc (0 : ℝ) 2, ℝ) := inferInstance

/-- The empty finite-dimensional projection is accepted. -/
example (μ : ProbabilityMeasure C(Set.Icc (0 : ℝ) 2, ℝ)) :
    ProbabilityMeasure ((∅ : Finset (Set.Icc (0 : ℝ) 2)) → ℝ) :=
  μ.map (fun f => (∅ : Finset (Set.Icc (0 : ℝ) 2)).restrict
    (fun t => f t))

/-- Singleton evaluation is accepted without a cardinality side condition. -/
example (μ : ProbabilityMeasure C(Set.Icc (0 : ℝ) 2, ℝ))
    (t : Set.Icc (0 : ℝ) 2) :
    ProbabilityMeasure (({t} : Finset (Set.Icc (0 : ℝ) 2)) → ℝ) :=
  μ.map (fun f => ({t} : Finset (Set.Icc (0 : ℝ) 2)).restrict
    (fun s => f s))

/-- Repeating a coordinate does not create an ordered duplicate: `Finset`
collapses it. -/
theorem repeated_coordinate_finset_collapses (t : Set.Icc (0 : ℝ) 2) :
    ({t, t} : Finset (Set.Icc (0 : ℝ) 2)) = {t} := by
  simp

/-- Both endpoints `0` and `T = 2` form a valid finite projection. -/
example (μ : ProbabilityMeasure C(Set.Icc (0 : ℝ) 2, ℝ)) :
    ProbabilityMeasure (
      ({⟨0, by norm_num⟩, ⟨2, by norm_num⟩} :
        Finset (Set.Icc (0 : ℝ) 2)) → ℝ) :=
  μ.map (fun f =>
    ({⟨0, by norm_num⟩, ⟨2, by norm_num⟩} :
      Finset (Set.Icc (0 : ℝ) 2)).restrict (fun t => f t))

#print axioms continuousPath_measure_ext_of_finset_eval
#print axioms tendsto_continuousPath_of_tight_of_finset_eval
#check @continuousPath_measure_ext_of_finset_eval
#check @tendsto_continuousPath_of_tight_of_finset_eval

end

end MathlibExtTest.Probability.ContinuousPathConvergence
