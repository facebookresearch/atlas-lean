/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise

/-!
# Tests for `MathlibExt.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise`

* `StatMech.BirkhoffAE.tendsto_birkhoffAverage_condExp_ae` (Birkhoff's pointwise ergodic
  theorem): instantiated for the identity map on an arbitrary probability space and a constant
  function, where the conditional expectation is computed to be the constant.
* `StatMech.BirkhoffAE.tendsto_birkhoffAverage_ae` and `birkhoffLimit`: for the identity map the
  limit of an arbitrary integrable `f` is `f` itself almost everywhere.
* `StatMech.BirkhoffAE.birkhoffLimit_ae_eq_integral_of_ergodic`: the identity map is proved
  ergodic for the Dirac measure on `Unit`; the limit is the integral.
* `StatMech.BirkhoffAE.IsInvariantSet`: decided for `not : Bool → Bool`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise

open MeasureTheory Filter Topology
open _root_.StatMech _root_.StatMech.BirkhoffAE

/-- `univ` is invariant under `not`. -/
example : IsInvariantSet (not : Bool → Bool) Set.univ := fun _ => by simp

/-- `{true}` is not invariant under `not`. -/
example : ¬ IsInvariantSet (not : Bool → Bool) {true} := fun h => by simpa using h true

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

omit [MeasurableSpace α] in
/-- Birkhoff averages of the identity map are eventually constant. -/
lemma birkhoffAverage_id_eq (f : α → ℝ) {n : ℕ} (hn : 1 ≤ n) (x : α) :
    birkhoffAverage ℝ id f n x = f x := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  simp [birkhoffAverage, birkhoffSum, hn']

/-- Birkhoff's theorem for the identity map and a constant: the averages converge a.e. to the
conditional expectation, which is the constant. -/
example (c : ℝ) : ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ id (fun _ => c) n x) atTop
    (𝓝 c) := by
  have h := tendsto_birkhoffAverage_condExp_ae (MeasurePreserving.id μ)
    (integrable_const (μ := μ) c)
  rw [condExp_const (MeasurableSpace.invariants_le id) c] at h
  exact h

/-- For the identity map, the Birkhoff limit of any integrable `f` is `f` a.e. -/
example (f : α → ℝ) (hf : Integrable f μ) : ∀ᵐ x ∂μ, birkhoffLimit id f x = f x := by
  filter_upwards [tendsto_birkhoffAverage_ae (MeasurePreserving.id μ) hf] with x hx
  refine tendsto_nhds_unique hx (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (birkhoffAverage_id_eq f hn x).symm

/-- The identity map is ergodic for the Dirac measure on `Unit`. -/
theorem ergodic_id_dirac : Ergodic (id : Unit → Unit) (Measure.dirac ()) :=
  Ergodic.of_preimage_eq (MeasurePreserving.id _) fun s _ _ => by
    rcases s.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · exact eventuallyEmptyOrUniv_iff'.2 (Or.inl EventuallyEq.rfl)
    · have : s = Set.univ := Set.eq_univ_of_forall fun v => by rwa [Subsingleton.elim v u]
      subst this
      exact eventuallyEmptyOrUniv_iff'.2 (Or.inr EventuallyEq.rfl)

/-- The ergodic form: the Birkhoff limit of a constant is its integral. -/
example (c : ℝ) :
    ∀ᵐ x ∂(Measure.dirac ()), birkhoffLimit (id : Unit → Unit) (fun _ => c) x = c := by
  filter_upwards [birkhoffLimit_ae_eq_integral_of_ergodic ergodic_id_dirac
    (integrable_const (μ := Measure.dirac ()) c)] with x hx
  simpa using hx

end MathlibExtTest.StatMech.Dynamics.Ergodic.KingmanSigned.BirkhoffPointwise
