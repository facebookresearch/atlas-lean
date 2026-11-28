/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.FiniteTransport
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped BigOperators

namespace MathlibExtTest.Probability.FiniteTransport

open MathlibExt.Probability.FiniteTransport

@[expose] public section

/-- The discrete two-point ground distance on `Fin 2`: distance `0` on the
diagonal and `1` off the diagonal. -/
def d2 : Fin 2 → Fin 2 → ℝ := fun x y => if x = y then 0 else 1

/-- Total variation distance takes the value `1` on opposite point masses
and `0` on identical uniform distributions over `Fin 2`. -/
theorem g1_tvDist_values :
    MathlibExt.Probability.MarkovMixing.tvDist (fun i : Fin 2 => if i = 0 then (1 : ℝ) else (0 : ℝ))
      (fun i : Fin 2 => if i = 0 then (0 : ℝ) else (1 : ℝ)) = 1
    ∧ MathlibExt.Probability.MarkovMixing.tvDist (fun _ : Fin 2 => (1 / 2 : ℝ))
        (fun _ : Fin 2 => (1 / 2 : ℝ)) = 0 := by
  constructor
  · norm_num [MathlibExt.Probability.MarkovMixing.tvDist, Fin.sum_univ_two]
  · norm_num [MathlibExt.Probability.MarkovMixing.tvDist, Fin.sum_univ_two]

/-- The point-mass coupling between opposite corners of `Fin 2` is a
coupling of the corner distributions, with transport cost `1`. -/
theorem g2_coupling_cost :
    IsCoupling (fun i : Fin 2 => if i = 0 then (1 : ℝ) else (0 : ℝ))
      (fun i : Fin 2 => if i = 0 then (0 : ℝ) else (1 : ℝ))
      (fun x y : Fin 2 => if x = 0 ∧ y = 1 then (1 : ℝ) else (0 : ℝ))
    ∧ transportCost d2
        (fun x y : Fin 2 => if x = 0 ∧ y = 1 then (1 : ℝ) else (0 : ℝ))
        = 1 := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x y
      show 0 ≤ (if x = 0 ∧ y = 1 then (1 : ℝ) else (0 : ℝ))
      by_cases h : x = 0 ∧ y = 1 <;> simp [h]
    · rw [Fin.forall_fin_two]
      constructor
      · norm_num [Fin.sum_univ_two]
      · norm_num [Fin.sum_univ_two]
    · rw [Fin.forall_fin_two]
      constructor
      · norm_num [Fin.sum_univ_two]
      · norm_num [Fin.sum_univ_two]
  · norm_num [transportCost, d2, Fin.sum_univ_two]

/-- The `0` point mass on `Fin 2`, as a probability-distribution subtype
element. -/
def delta0D : {p : Fin 2 → ℝ // IsDist p} :=
  ⟨fun i => if i = 0 then (1 : ℝ) else 0, by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : i = 0 <;> simp [h]
    · norm_num [Fin.sum_univ_two]⟩

/-- The `1` point mass on `Fin 2`, as a probability-distribution subtype
element. -/
def delta1D : {p : Fin 2 → ℝ // IsDist p} :=
  ⟨fun i => if i = 0 then (0 : ℝ) else 1, by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : i = 0 <;> simp [h]
    · norm_num [Fin.sum_univ_two]⟩

/-- G3: the earthmover value between the two opposite point masses is
`1`, computed directly: the coupling is unique and has cost `1`. -/
theorem g3_earthmover_point_masses :
    earthmover d2 delta0D delta1D = 1 := by
  have hcost : ∀ π : {π // IsCoupling delta0D.1 delta1D.1 π},
      transportCost d2 π.1 = 1 := by
    intro π
    obtain ⟨hnn, hrow, hcol⟩ := π.2
    have r0 := hrow 0
    have r1 := hrow 1
    have c0 := hcol 0
    have c1 := hcol 1
    simp only [delta0D, delta1D, Fin.sum_univ_two] at r0 r1 c0 c1
    norm_num at r0 r1 c0 c1
    have n00 := hnn 0 0
    have n01 := hnn 0 1
    have n10 := hnn 1 0
    have n11 := hnn 1 1
    have h01 : π.1 0 1 = 1 := by linarith
    have h00 : π.1 0 0 = 0 := by linarith
    have h10 : π.1 1 0 = 0 := by linarith
    have h11 : π.1 1 1 = 0 := by linarith
    unfold transportCost
    norm_num [Fin.sum_univ_two, d2, h00, h01, h10, h11]
  unfold earthmover
  have hne : Nonempty {π // IsCoupling delta0D.1 delta1D.1 π} :=
    ⟨⟨_, g2_coupling_cost.1⟩⟩
  have hfun : (fun π : {π // IsCoupling delta0D.1 delta1D.1 π} =>
      transportCost d2 π.1) = fun _ => (1 : ℝ) :=
    funext hcost
  rw [hfun]
  exact ciInf_const

/-- G4: the score expectation gap between the point masses for the
`0`-indicator score is `1`, matching the earthmover bound. -/
theorem g4_bias_le_earthmover_example :
    bias delta0D.1 delta1D.1 (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) = 1
    ∧ bias delta0D.1 delta1D.1 (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
      ≤ earthmover d2 delta0D delta1D := by
  have hval : bias delta0D.1 delta1D.1
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) = 1 := by
    norm_num [bias, delta0D, delta1D, Fin.sum_univ_two]
  refine ⟨hval, ?_⟩
  apply bias_le_earthmover
  intro x y
  fin_cases x <;> fin_cases y <;> norm_num [d2]

/-- G4b: `bias` is an absolute value: with the point masses swapped, the weighted score sums
differ by `-1`, and the gap is `1`. -/
theorem g4b_bias_swapped_point_masses :
    bias delta1D.1 delta0D.1 (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) = 1 := by
  norm_num [bias, delta0D, delta1D, Fin.sum_univ_two]

/-- G5: the earthmover value is at most the cost of the exhibited
coupling, by direct application of `earthmover_le_transportCost`. -/
theorem g5_earthmover_le_transportCost_example :
    earthmover d2 delta0D delta1D ≤ 1 := by
  have h : earthmover d2 delta0D delta1D ≤
      transportCost d2
        (fun x y : Fin 2 => if x = 0 ∧ y = 1 then (1 : ℝ) else (0 : ℝ)) :=
    earthmover_le_transportCost g2_coupling_cost.1
  rwa [g2_coupling_cost.2] at h

/-- The uniform distribution on `Fin 2`, as a probability-distribution subtype element. -/
noncomputable def uniformD : {p : Fin 2 → ℝ // IsDist p} :=
  ⟨fun _ => 1 / 2, by
    refine ⟨fun _ => by norm_num, ?_⟩
    norm_num [Fin.sum_univ_two]⟩

/-- G5b: `isCoupling_mul` names its witness. For the `0` point mass and the uniform
distribution, the independent coupling is the matrix with entries `δ₀ x * (1 / 2)`, its
transport cost under the discrete cost is `1 / 2`, and so the earthmover value is at most
`1 / 2`. -/
theorem g5b_independent_coupling_cost :
    transportCost d2 (fun x y => delta0D.1 x * uniformD.1 y) = 1 / 2
    ∧ earthmover d2 delta0D uniformD ≤ 1 / 2 := by
  have hcost : transportCost d2 (fun x y => delta0D.1 x * uniformD.1 y) = 1 / 2 := by
    norm_num [transportCost, d2, delta0D, uniformD, Fin.sum_univ_two]
  exact ⟨hcost,
    (earthmover_le_transportCost (isCoupling_mul delta0D.2 uniformD.2)).trans_eq hcost⟩

/-- A signed ground cost on `Fin 2`: `-2` on the diagonal and `-1` off
the diagonal. -/
def dSigned : Fin 2 → Fin 2 → ℝ := fun x y => if x = y then -2 else -1

/-- G6: `earthmover_le_transportCost` needs no sign assumption on the
ground cost: for the signed cost above, the same coupling bounds the
earthmover value by `-1`, so for signed ground costs the value can
be negative and is not a distance. -/
theorem g6_earthmover_le_transportCost_signed :
    earthmover dSigned delta0D delta1D ≤ -1 := by
  have h : earthmover dSigned delta0D delta1D ≤
      transportCost dSigned
        (fun x y : Fin 2 => if x = 0 ∧ y = 1 then (1 : ℝ) else (0 : ℝ)) :=
    earthmover_le_transportCost g2_coupling_cost.1
  have hcost : transportCost dSigned
      (fun x y : Fin 2 => if x = 0 ∧ y = 1 then (1 : ℝ) else (0 : ℝ))
      = -1 := by
    norm_num [transportCost, dSigned, Fin.sum_univ_two]
  rwa [hcost] at h

/-- G7: for the signed ground cost, the earthmover value between the
point masses is exactly `-1`: the coupling is unique and has cost
`-1`, so the value is negative and is not a distance. -/
theorem g7_earthmover_signed_eq :
    earthmover dSigned delta0D delta1D = -1 := by
  have hcost : ∀ π : {π // IsCoupling delta0D.1 delta1D.1 π},
      transportCost dSigned π.1 = -1 := by
    intro π
    obtain ⟨hnn, hrow, hcol⟩ := π.2
    have r0 := hrow 0
    have r1 := hrow 1
    have c0 := hcol 0
    have c1 := hcol 1
    simp only [delta0D, delta1D, Fin.sum_univ_two] at r0 r1 c0 c1
    norm_num at r0 r1 c0 c1
    have n00 := hnn 0 0
    have n01 := hnn 0 1
    have n10 := hnn 1 0
    have n11 := hnn 1 1
    have h01 : π.1 0 1 = 1 := by linarith
    have h00 : π.1 0 0 = 0 := by linarith
    have h10 : π.1 1 0 = 0 := by linarith
    have h11 : π.1 1 1 = 0 := by linarith
    unfold transportCost
    norm_num [Fin.sum_univ_two, dSigned, h00, h01, h10, h11]
  unfold earthmover
  have hne : Nonempty {π // IsCoupling delta0D.1 delta1D.1 π} :=
    ⟨⟨_, g2_coupling_cost.1⟩⟩
  have hfun : (fun π : {π // IsCoupling delta0D.1 delta1D.1 π} =>
      transportCost dSigned π.1) = fun _ => (-1 : ℝ) :=
    funext hcost
  rw [hfun]
  exact ciInf_const

end

end MathlibExtTest.Probability.FiniteTransport
