/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.C0DirectSum
import MathlibExt.Analysis.CStarAlgebra.HilbertDirectSum
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!
# Nonunital coefficient sums and empty Hilbert sums

Exercise computed inclusions, coordinate evaluation, inherited norm, cutoff,
and coefficient maps on a countable C0-sum of actual nonunital algebras.
Empty coefficient and Hilbert index sets are checked without nonempty premises.
-/

noncomputable section
open scoped ZeroAtInfty
namespace C0DirectSumSmoke

private abbrev Coefficients := C₀(ℝ, ℂ)
private abbrev Family := fun _ : ℕ => Coefficients

example (f : Coefficients) :
    CStarC0Sum.eval Family 0 (CStarC0Sum.single Family 0 f) = f := by
  rw [CStarC0Sum.eval_apply, CStarC0Sum.single_apply_self]

example (f : Coefficients) : CStarC0Sum.single Family 0 f 1 = 0 :=
  CStarC0Sum.single_apply_ne Family 0 f (by decide)

example (f : Coefficients) : ‖CStarC0Sum.single Family 0 f‖ = ‖f‖ :=
  CStarC0Sum.norm_single Family 0 f

-- Empty cutoff drops every coordinate in the actual supremum-norm sum.
example (f : CStarC0Sum Family) : CStarC0Sum.truncate Family ∅ f = 0 := by
  apply CStarC0Sum.ext
  intro i
  rw [CStarC0Sum.zero_apply]
  exact CStarC0Sum.truncate_apply_of_not_mem Family ∅ f (Finset.notMem_empty i)

-- A family of zero coefficient homomorphisms gives the actual zero image.
example (f : CStarC0Sum Family) :
    CStarC0Sum.map Family Family (fun _ => 0) f = 0 := by
  apply CStarC0Sum.ext
  intro i
  simp only [CStarC0Sum.map_apply, NonUnitalStarAlgHom.zero_apply, CStarC0Sum.zero_apply]

-- There are no coordinates, so the original empty-family norm is zero.
example (f : CStarC0Sum (fun _ : Fin 0 => Coefficients)) : ‖f‖ = 0 := by
  have hzero : f = 0 := by
    apply CStarC0Sum.ext
    intro i
    exact Fin.elim0 i
  rw [hzero, norm_zero]

-- The nonunital Hilbert direct-sum constructor also accepts an empty index
-- and computes a zero vector in the actual lp-two Hilbert carrier.
example (a : Coefficients) (x : lp (fun _ : Fin 0 => ℂ) 2) :
    NonUnitalStarAlgHom.hilbertDirectSum
        (A := Coefficients) (H := fun _ : Fin 0 => ℂ)
        (fun i => Fin.elim0 i) a x = 0 := by
  apply lp.ext
  funext i
  exact Fin.elim0 i

end C0DirectSumSmoke
