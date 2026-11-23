/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletForm.QuasiRegular
public import MathlibExtTest.Probability.DirichletForm.Basic

import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for regular and quasi-regular forms

On the two-point discrete space `Bool` with counting measure, the `L²` inner-product form (a
Dirichlet form, `MathlibExtTest.Probability.DirichletForm.Basic.innerForm`) is both regular and
quasi-regular: every function is continuous with compact support, the constant nest `Bool, Bool,
…` consists of compact sets, and the indicator of `{true}` separates the two points. This
exercises all three conditions (QR1)–(QR3) and both halves of regularity on a nonzero form.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped CompactlySupported
open MathlibExt.Probability.DirichletForm MathlibExtTest.Probability.DirichletForm.Basic

namespace MathlibExtTest.Probability.DirichletForm.QuasiRegular

/-- A function on `Bool` as a compactly supported continuous function. -/
def toCc (f : Bool → ℝ) : Bool →C_c ℝ :=
  ⟨⟨f, continuous_of_discreteTopology⟩, HasCompactSupport.of_compactSpace f⟩

/-- The `L²` form on `Bool` with counting measure is regular. -/
theorem innerForm_isRegular : (innerForm (Measure.count : Measure Bool)).IsRegular := by
  refine ⟨fun u _ ε hε => ⟨u, Submodule.mem_top, ⟨toCc u, ae_of_all _ fun _ => rfl⟩, ?_⟩,
    fun g ε hε => ⟨g, ⟨MemLp.toLp g MemLp.of_discrete, Submodule.mem_top,
      MemLp.coeFn_toLp _⟩, fun x => by simpa using hε⟩⟩
  simpa [innerForm_energyOne] using hε

/-- The `L²` form on `Bool` with counting measure is quasi-regular. -/
theorem innerForm_isQuasiRegular :
    (innerForm (Measure.count : Measure Bool)).IsQuasiRegular := by
  set E := innerForm (Measure.count : Measure Bool)
  refine ⟨⟨_, E.isNest_const_univ, fun _ => isCompact_univ⟩,
    ⟨Set.univ, Set.subset_univ _, fun u _ ε hε => ⟨u, Set.mem_univ _, ?_⟩,
      fun v _ => ⟨v, SymmetricForm.isQuasiContinuous_of_continuous _
        continuous_of_discreteTopology, ae_of_all _ fun _ => rfl⟩⟩, ?_⟩
  · simpa [E, innerForm_energyOne] using hε
  · -- The indicator of `{true}` separates the two points.
    let f : Bool → ℝ := ({true} : Set Bool).indicator fun _ => 1
    refine ⟨fun _ => indicatorConstLp 2 (measurableSet_singleton true) (measure_ne_top _ _) 1,
      fun _ => f, ∅, fun _ => ⟨Submodule.mem_top,
        SymmetricForm.isQuasiContinuous_of_continuous _ continuous_of_discreteTopology,
        indicatorConstLp_coeFn⟩, E.isExceptional_empty, fun x _ y _ hxy => ⟨0, ?_⟩⟩
    cases x <;> cases y <;> simp_all [f]

end MathlibExtTest.Probability.DirichletForm.QuasiRegular
