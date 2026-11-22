/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.SvarcMilnor
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace MathlibExtTest.SvarcMilnor

open Metric Set

/-! A non-degenerate instance of the Švarc–Milnor hypotheses: the infinite cyclic group
`Multiplicative ℤ` acting on the real line by integer translations. -/

/-- Integer translations of the real line, as an action of `Multiplicative ℤ`. -/
@[instance_reducible]
def translation : MulAction (Multiplicative ℤ) ℝ where
  smul n x := x + ((Multiplicative.toAdd n : ℤ) : ℝ)
  one_smul x := by change x + ((Multiplicative.toAdd (1 : Multiplicative ℤ) : ℤ) : ℝ) = x; simp
  mul_smul m n x := by
    change x + ((Multiplicative.toAdd (m * n) : ℤ) : ℝ) =
      x + ((Multiplicative.toAdd n : ℤ) : ℝ) + ((Multiplicative.toAdd m : ℤ) : ℝ)
    rw [toAdd_mul]; push_cast; ring

attribute [local instance] translation

theorem smul_def (n : Multiplicative ℤ) (x : ℝ) :
    n • x = x + ((Multiplicative.toAdd n : ℤ) : ℝ) := rfl

instance : IsIsometricSMul (Multiplicative ℤ) ℝ :=
  ⟨fun n => Isometry.of_dist_eq fun x y => by simp [smul_def]⟩

instance : ProperlyDiscontinuousSMul (Multiplicative ℤ) ℝ := by
  refine ⟨fun {K L} hK hL => ?_⟩
  obtain ⟨a, ha⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨b, hb⟩ := hL.isBounded.subset_closedBall (0 : ℝ)
  refine ((Set.finite_Icc (-⌈a + b⌉) ⌈a + b⌉).preimage
    (Multiplicative.toAdd.injective.injOn)).subset ?_
  rintro n ⟨_, ⟨x, hx, rfl⟩, hxL⟩
  simp only at hxL
  have h1 := mem_closedBall.mp (ha hx)
  have h2 := mem_closedBall.mp (hb hxL)
  rw [smul_def, Real.dist_eq, sub_zero] at h2
  rw [Real.dist_eq, sub_zero] at h1
  have h3 : |((Multiplicative.toAdd n : ℤ) : ℝ)| ≤ a + b := by
    calc |((Multiplicative.toAdd n : ℤ) : ℝ)| = |(x + ((Multiplicative.toAdd n : ℤ) : ℝ)) - x| := by ring_nf
      _ ≤ |x + ((Multiplicative.toAdd n : ℤ) : ℝ)| + |x| := abs_sub _ _
      _ ≤ a + b := by linarith
  have h4 := Int.le_ceil (a + b)
  rw [abs_le] at h3
  simp only [mem_preimage, mem_Icc]
  constructor
  · have : (-(⌈a + b⌉ : ℝ)) ≤ ((Multiplicative.toAdd n : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  · have : ((Multiplicative.toAdd n : ℤ) : ℝ) ≤ (⌈a + b⌉ : ℝ) := by linarith
    exact_mod_cast this

/-- Every orbit of the translation action meets `[0, 1]`. -/
theorem cocompact (x : ℝ) : ∃ n : Multiplicative ℤ, n • x ∈ Icc (0 : ℝ) 1 := by
  refine ⟨Multiplicative.ofAdd (-⌊x⌋), ?_⟩
  rw [smul_def, toAdd_ofAdd, Int.cast_neg, mem_Icc]
  constructor <;> linarith [Int.floor_le x, Int.lt_floor_add_one x]

/-- Švarc–Milnor applied to `ℤ` acting on `ℝ`: `ℤ` is finitely generated. -/
example : Group.FG (Multiplicative ℤ) :=
  MathlibExt.SvarcMilnor.fg (isGeodesicSpace_of_normedSpace ℝ) isCompact_Icc cocompact

/-- Švarc–Milnor applied to `ℤ` acting on `ℝ`: the orbit map `n ↦ n • 0` is a quasi-isometry for
the word metric of a finite generating set. -/
example : ∃ (S : Set (Multiplicative ℤ)) (_ : S.Finite) (P : Group.Generators (Multiplicative ℤ) S)
    (L C : ℝ), @IsQuasiIsometry (Multiplicative ℤ) ℝ P.normedGroup.toPseudoMetricSpace _
      (fun g => g • (0 : ℝ)) L C :=
  MathlibExt.SvarcMilnor.isQuasiIsometry (isGeodesicSpace_of_normedSpace ℝ) isCompact_Icc
    cocompact 0

end MathlibExtTest.SvarcMilnor
