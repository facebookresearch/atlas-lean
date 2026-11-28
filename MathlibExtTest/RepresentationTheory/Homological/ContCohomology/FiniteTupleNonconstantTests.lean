/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.Homological.ContCohomology.FiniteTupleEvaluation
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
meta import Mathlib.Tactic.NormNum

/-!
# Nonconstant continuous coefficients and signed tuple differentials

A discrete order-two group acts trivially on a universe-lifted integer module. The scalar
and group types lie in universe zero, while the coefficient carrier lies in universe one.
A genuine continuous cochain takes value zero at the identity and three at the nonidentity.
Nested evaluation retains the second coordinate. Its homogeneous differential has values
three and minus three on the two ordered tuples, detecting the deletion sign.
-/

open CategoryTheory ContinuousCohomology

noncomputable section
set_option autoImplicit false

namespace FiniteTupleNonconstantTests

private abbrev G := Multiplicative (ZMod 2)
private abbrev V := ULift.{1} ℤ

private instance : TopologicalSpace ℤ := ⊥
private instance : DiscreteTopology ℤ := ⟨rfl⟩
private instance : TopologicalSpace G := ⊥
private instance : DiscreteTopology G := ⟨rfl⟩
private instance : TopologicalSpace V := ⊥
private instance : DiscreteTopology V := ⟨rfl⟩
private instance : ContinuousSMul ℤ V := ⟨continuous_of_discreteTopology⟩

private abbrev X : TopRep.{1, 0, 0} ℤ G :=
  TopRep.of (ContRepresentation.trivial ℤ G V)

private def s : G := Multiplicative.ofAdd (1 : ZMod 2)
private lemma s_ne_one : s ≠ 1 := by decide

private def first : TopRep.resolutionX X 1 :=
  { toFun := fun g => ULift.up (if g = 1 then (0 : ℤ) else 3)
    continuous_toFun := continuous_of_discreteTopology }

private def nested : TopRep.resolutionX X 2 := ContinuousMap.const G first

private def forward : Fin 2 → G := Fin.cons 1 (fun _ : Fin 1 => s)
private def reverse : Fin 2 → G := Fin.cons s (fun _ : Fin 1 => 1)

example : (resolutionFinUncurry X 1 first (fun _ => s)).down = 3 := by
  change (if s = 1 then (0 : ℤ) else 3) = 3
  rw [if_neg s_ne_one]

example : (resolutionFinUncurry X 1 first (fun _ => 1)).down = 0 := by
  change (if (1 : G) = 1 then (0 : ℤ) else 3) = 0
  rw [if_pos rfl]

example : first ≠ 0 := by
  intro h
  have he := congrArg (fun f : TopRep.resolutionX X 1 => (f s).down) h
  have hv : (first s).down = 3 := by
    change (if s = 1 then (0 : ℤ) else 3) = 3
    rw [if_neg s_ne_one]
  rw [hv] at he
  exact (by norm_num : (3 : ℤ) ≠ 0) he

example : (resolutionFinUncurry X 2 nested forward).down = 3 := by
  change (if s = 1 then (0 : ℤ) else 3) = 3
  rw [if_neg s_ne_one]

example : (resolutionFinUncurry X 2 nested reverse).down = 0 := by
  change (if (1 : G) = 1 then (0 : ℤ) else 3) = 0
  rw [if_pos rfl]

example : (resolutionFinUncurry X 2 ((TopRep.d X 1).hom first) forward).down = 3 := by
  have h := resolutionFinUncurry_d X 0 first forward
  rw [Fin.sum_univ_two] at h
  have he := congrArg ULift.down h
  simpa [resolutionFinUncurry, forward, first, s_ne_one] using he

example : (resolutionFinUncurry X 2 ((TopRep.d X 1).hom first) reverse).down = -3 := by
  have h := resolutionFinUncurry_d X 0 first reverse
  rw [Fin.sum_univ_two] at h
  have he := congrArg ULift.down h
  simpa [resolutionFinUncurry, reverse, first, s_ne_one] using he

example : Continuous (resolutionFinUncurry X 2 nested) :=
  continuous_resolutionFinUncurry_left X 2 nested

end FiniteTupleNonconstantTests
