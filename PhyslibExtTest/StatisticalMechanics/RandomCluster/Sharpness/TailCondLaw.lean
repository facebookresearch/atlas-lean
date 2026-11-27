/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailCondLaw

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.TailCondLaw`

* `atc_tailCondLawFixed` for the FK mass on the complete graph `K₂` at `p = 1/2`, `q = 2`
  (monotonic by `fkMass_isMonotonic`) and the indicator of "edge `s(0, 1)` is open";
* `atc_hasFKG_ubfTail` at explicit sizes;
* `atc_tailCondLawFixed` in its conditional form for an arbitrary monotonic measure.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.TailCondLaw

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptDisintegration
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.OSSS.Monotonic _root_.StatMech.Probability

/-- The event that the edge `s(0, 1)` of `K₂` is open. -/
def edgeOpen : Set (ConfigSpace (Sym2 (Fin 2))) := {ω | ω s(0, 1) = true}

/-- The indicator of `edgeOpen`. -/
noncomputable def ind : ConfigSpace (Sym2 (Fin 2)) → ℝ := edgeOpen.indicator (fun _ => 1)

/-- The indicator of `edgeOpen` is monotone. -/
theorem ind_monotone : Monotone ind := by
  refine IsIncreasing.indicator_monotone (fun x y hxy hx => ?_)
  simp only [edgeOpen, Set.mem_ofPred_eq] at hx ⊢
  have hle := hxy s(0, 1)
  rw [hx] at hle
  exact le_antisymm (by simp) hle

/-- The indicator of `edgeOpen` is bounded by `1` in absolute value. -/
theorem abs_ind_le_one (ω : ConfigSpace (Sym2 (Fin 2))) : |ind ω| ≤ 1 := by
  by_cases h : ω ∈ edgeOpen <;> simp [ind, h]

-- The fixed-switch tail law for the FK mass on `K₂`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    atc_TailCondLawFixed (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ ind :=
  atc_tailCondLawFixed (fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num))
    (fkMass_isMonotonic ⊤ (by norm_num) (by norm_num) (by norm_num)) σ ind_monotone
    abs_ind_le_one

-- The tail block of the uniform cube has the FKG property.
example : HasFKG (ubfTail 3 1) := atc_hasFKG_ubfTail 3 1

-- The fixed-switch tail law for any monotonic measure.
example {E : Type*} [Fintype E] [DecidableEq E] {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) :
    atc_TailCondLawFixed μ σ f :=
  atc_tailCondLawFixed hpos hμ1 hmono σ hf hfC

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.TailCondLaw
