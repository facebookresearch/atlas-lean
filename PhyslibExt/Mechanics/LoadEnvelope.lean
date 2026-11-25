/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.TrussCompatibility

/-!
# Independent-pattern load-box envelope

## i. Overview

The index `ι` is a finite set of load coordinates. The
influence vector `eta : ι → ℝ` is fixed throughout; the
response to a load `f : ι → ℝ` is the pairing `eta ⬝ᵥ f`.
A pattern load varies independently in each coordinate
inside the box `0 ≤ f i ≤ cap i`, where `cap : ι → ℝ` is
the pattern capacity in each coordinate. The upper
envelope value is `∑ i, cap i * max (eta i) 0` and the
lower envelope value is `∑ i, cap i * min (eta i) 0`, with
the capacity factor first as written. The endpoint loads
`upperBoxLoad` and `lowerBoxLoad` choose, in each
coordinate, the box endpoint that the sign of the
influence coefficient selects: full capacity where the
coefficient pushes the response toward that envelope,
zero otherwise. At a zero coefficient both endpoints give
the same response contribution and the definitions fix
the choice as stated.

One fixed linear response: the same influence vector for
every pattern load, with coordinates varying
independently. The envelope claims are order algebra of
the pairing itself; they use no solve, definiteness or
equilibrium premise, and they identify no displacement
output. The supported-truss bridge at the end reads the
general claims at the single exported influence vector
`influenceVector` and its retained response map
`unitLoadResponse`, whose coordinates are consumed once
there and involve no further inverse. No universal design
factor is applied to the capacities or the response, and
no nonlinear or contact response is modelled: a
load-dependent influence vector would need a different
envelope statement.

## ii. Key results

- `upperBoxLoad`, `lowerBoxLoad`: the endpoint loads
  attaining the two envelope values.
- `dotProduct_le_boxUpper`, `boxLower_le_dotProduct`:
  every pattern load in the box has response between the
  lower and upper envelope values.
- `supported_unitLoadResponse_le_boxUpper`,
  `supported_boxLower_le_unitLoadResponse`: the same
  bounds at the exported supported influence vector, with
  attainment at the endpoint loads.

## iii. Table of contents

- A. Generic box envelope
- B. Supported bridge

## iv. References

- `PhyslibExt.Mechanics.TrussCompatibility` for the
  supported influence vector and unit-load response.
-/

@[expose] public section

open Matrix

namespace Mechanics.LoadEnvelope

/-! ## A. Generic box envelope -/

/-- Upper endpoint load for the box `0 ≤ f i ≤ cap i` at the fixed
influence vector `eta`: full capacity in each coordinate whose
influence coefficient is nonnegative, zero load elsewhere. At a
zero coefficient the capacity endpoint is chosen; its response
contribution is zero either way. -/
noncomputable def upperBoxLoad {ι : Type*} (eta cap : ι → ℝ) :
    ι → ℝ :=
  fun i => if 0 ≤ eta i then cap i else 0

/-- Lower endpoint load for the box `0 ≤ f i ≤ cap i` at the fixed
influence vector `eta`: full capacity in each coordinate whose
influence coefficient is nonpositive, zero load elsewhere. At a
zero coefficient the capacity endpoint is chosen; its response
contribution is zero either way. -/
noncomputable def lowerBoxLoad {ι : Type*} (eta cap : ι → ℝ) :
    ι → ℝ :=
  fun i => if eta i ≤ 0 then cap i else 0

/-- Upper box bound: for the fixed influence vector `eta`, every
pattern load in the box `0 ≤ f i ≤ cap i` has response at most the
upper envelope value `∑ i, cap i * max (eta i) 0`. Each coordinate
contributes at most its envelope term, whatever the sign of its
influence coefficient. No separate capacity sign premise is
stated: the box hypotheses at each coordinate already force
`0 ≤ cap i` there. -/
lemma dotProduct_le_boxUpper {ι : Type*} [Fintype ι]
    (eta cap f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i)
    (hfc : ∀ i, f i ≤ cap i) :
    eta ⬝ᵥ f ≤ ∑ i, cap i * max (eta i) 0 := by
  unfold dotProduct
  apply Finset.sum_le_sum
  intro i _
  by_cases h : 0 ≤ eta i
  · rw [max_eq_left h]
    rw [mul_comm (cap i) (eta i)]
    exact mul_le_mul_of_nonneg_left (hfc i) h
  · have hlt : eta i < 0 := lt_of_not_ge h
    rw [max_eq_right (le_of_lt hlt)]
    rw [mul_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hlt) (hf0 i)

/-- Upper attainment: for nonnegative pattern capacities, the
upper endpoint load lies in the box `0 ≤ f i ≤ cap i` and its
response is the upper envelope value
`∑ i, cap i * max (eta i) 0`, so the upper box bound is attained.
Nonnegativity of the capacities is the feasibility premise for
the endpoint load. -/
lemma upperBoxLoad_attains_boxUpper {ι : Type*} [Fintype ι]
    (eta cap : ι → ℝ) (hcap : ∀ i, 0 ≤ cap i) :
    (∀ i, 0 ≤ upperBoxLoad eta cap i)
      ∧ (∀ i, upperBoxLoad eta cap i ≤ cap i)
      ∧ eta ⬝ᵥ upperBoxLoad eta cap
        = ∑ i, cap i * max (eta i) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold upperBoxLoad
    by_cases h : 0 ≤ eta i
    · simp only [h, ↓reduceIte]
      exact hcap i
    · simp only [h, ↓reduceIte]
      exact le_rfl
  · intro i
    unfold upperBoxLoad
    by_cases h : 0 ≤ eta i
    · simp only [h, ↓reduceIte]
      exact le_rfl
    · simp only [h, ↓reduceIte]
      exact hcap i
  · unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    unfold upperBoxLoad
    by_cases h : 0 ≤ eta i
    · simp only [h, ↓reduceIte, max_eq_left h, mul_comm]
    · have hlt : eta i < 0 := lt_of_not_ge h
      simp only [h, ↓reduceIte, max_eq_right (le_of_lt hlt), mul_zero]

/-- Lower box bound: for the fixed influence vector `eta`, every
pattern load in the box `0 ≤ f i ≤ cap i` has response at least
the lower envelope value `∑ i, cap i * min (eta i) 0`. Each
coordinate contributes at least its envelope term, whatever the
sign of its influence coefficient. No separate capacity sign
premise is stated: the box hypotheses at each coordinate already
force `0 ≤ cap i` there. -/
lemma boxLower_le_dotProduct {ι : Type*} [Fintype ι]
    (eta cap f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i)
    (hfc : ∀ i, f i ≤ cap i) :
    ∑ i, cap i * min (eta i) 0 ≤ eta ⬝ᵥ f := by
  unfold dotProduct
  apply Finset.sum_le_sum
  intro i _
  by_cases h : eta i ≤ 0
  · rw [min_eq_left h]
    rw [mul_comm (cap i) (eta i)]
    exact mul_le_mul_of_nonpos_left (hfc i) h
  · have hlt : 0 < eta i := lt_of_not_ge h
    rw [min_eq_right (le_of_lt hlt)]
    rw [mul_zero]
    exact mul_nonneg (le_of_lt hlt) (hf0 i)

/-- Lower attainment: for nonnegative pattern capacities, the
lower endpoint load lies in the box `0 ≤ f i ≤ cap i` and its
response is the lower envelope value
`∑ i, cap i * min (eta i) 0`, so the lower box bound is attained.
Nonnegativity of the capacities is the feasibility premise for
the endpoint load. -/
lemma lowerBoxLoad_attains_boxLower {ι : Type*} [Fintype ι]
    (eta cap : ι → ℝ) (hcap : ∀ i, 0 ≤ cap i) :
    (∀ i, 0 ≤ lowerBoxLoad eta cap i)
      ∧ (∀ i, lowerBoxLoad eta cap i ≤ cap i)
      ∧ eta ⬝ᵥ lowerBoxLoad eta cap
        = ∑ i, cap i * min (eta i) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold lowerBoxLoad
    by_cases h : eta i ≤ 0
    · simp only [h, ↓reduceIte]
      exact hcap i
    · simp only [h, ↓reduceIte]
      exact le_rfl
  · intro i
    unfold lowerBoxLoad
    by_cases h : eta i ≤ 0
    · simp only [h, ↓reduceIte]
      exact le_rfl
    · simp only [h, ↓reduceIte]
      exact hcap i
  · unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    unfold lowerBoxLoad
    by_cases h : eta i ≤ 0
    · simp only [h, ↓reduceIte, min_eq_left h, mul_comm]
    · have hlt : 0 < eta i := lt_of_not_ge h
      simp only [h, ↓reduceIte, min_eq_right (le_of_lt hlt), mul_zero]

/-! ## B. Supported bridge -/

/-- Supported upper box bound: for the fixed output `aout`, every supported pattern load in the box
`0 ≤ f i ≤ cap i` over the free coordinates has unit-load response at most the upper envelope value
at the exported influence vector. The influence coordinates are those of the one vector
`Mechanics.TrussCompatibility.influenceVector r a b S k aout`; no further inverse is formed and no
solve reading of the response is used. No positivity of `k` or definiteness of the supported
stiffness is assumed: its inverse is the totalized matrix inverse, zero for a singular stiffness,
and then the influence vector and every response are `0`. -/
lemma supported_unitLoadResponse_le_boxUpper {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] [DecidableEq F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ)
    (cap f : F → ℝ) (hf0 : ∀ i, 0 ≤ f i)
    (hfc : ∀ i, f i ≤ cap i) :
    Mechanics.TrussCompatibility.unitLoadResponse r a b S k aout f
      ≤ ∑ i, cap i * max (Mechanics.TrussCompatibility.influenceVector r a b S k aout i) 0 := by
  rw [Mechanics.TrussCompatibility.unitLoadResponse_apply]
  exact dotProduct_le_boxUpper _ _ _ hf0 hfc

/-- Supported upper attainment: for nonnegative pattern capacities over the free coordinates, the
upper endpoint load at the exported influence vector lies in the box and its unit-load response is
the supported upper envelope value, so the supported upper box bound is attained without forming
another inverse. No positivity of `k` or definiteness of the supported stiffness is assumed: its
inverse is the totalized matrix inverse, zero for a singular stiffness, and then the influence
vector and every response are `0`. -/
lemma supported_boxUpper_attained {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] [DecidableEq F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ)
    (cap : F → ℝ) (hcap : ∀ i, 0 ≤ cap i) :
    (∀ i, 0 ≤ upperBoxLoad (Mechanics.TrussCompatibility.influenceVector r a b S k aout) cap i)
      ∧ (∀ i,
        upperBoxLoad (Mechanics.TrussCompatibility.influenceVector r a b S k aout) cap i ≤ cap i)
      ∧ Mechanics.TrussCompatibility.unitLoadResponse r a b S k aout
          (upperBoxLoad (Mechanics.TrussCompatibility.influenceVector r a b S k aout) cap)
        = ∑ i, cap i * max (Mechanics.TrussCompatibility.influenceVector r a b S k aout i) 0 := by
  rw [Mechanics.TrussCompatibility.unitLoadResponse_apply]
  exact upperBoxLoad_attains_boxUpper _ _ hcap

/-- Supported lower box bound: for the fixed output `aout`, every supported pattern load in the box
`0 ≤ f i ≤ cap i` over the free coordinates has unit-load response at least the lower envelope value
at the exported influence vector. The influence coordinates are those of the one vector
`Mechanics.TrussCompatibility.influenceVector r a b S k aout`; no further inverse is formed and no
solve reading of the response is used. No positivity of `k` or definiteness of the supported
stiffness is assumed: its inverse is the totalized matrix inverse, zero for a singular stiffness,
and then the influence vector and every response are `0`. -/
lemma supported_boxLower_le_unitLoadResponse {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] [DecidableEq F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ)
    (cap f : F → ℝ) (hf0 : ∀ i, 0 ≤ f i)
    (hfc : ∀ i, f i ≤ cap i) :
    ∑ i, cap i * min (Mechanics.TrussCompatibility.influenceVector r a b S k aout i) 0
      ≤ Mechanics.TrussCompatibility.unitLoadResponse r a b S k aout f := by
  rw [Mechanics.TrussCompatibility.unitLoadResponse_apply]
  exact boxLower_le_dotProduct _ _ _ hf0 hfc

/-- Supported lower attainment: for nonnegative pattern capacities over the free coordinates, the
lower endpoint load at the exported influence vector lies in the box and its unit-load response is
the supported lower envelope value, so the supported lower box bound is attained without forming
another inverse. No positivity of `k` or definiteness of the supported stiffness is assumed: its
inverse is the totalized matrix inverse, zero for a singular stiffness, and then the influence
vector and every response are `0`. -/
lemma supported_boxLower_attained {J M F : Type*}
    [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]
    [Fintype F] [DecidableEq F] (r : J → (Fin 2 → ℝ)) (a b : M → J)
    (S : Matrix (J × Fin 2) F ℝ) (k : M → ℝ) (aout : F → ℝ)
    (cap : F → ℝ) (hcap : ∀ i, 0 ≤ cap i) :
    (∀ i, 0 ≤ lowerBoxLoad (Mechanics.TrussCompatibility.influenceVector r a b S k aout) cap i)
      ∧ (∀ i,
        lowerBoxLoad (Mechanics.TrussCompatibility.influenceVector r a b S k aout) cap i ≤ cap i)
      ∧ Mechanics.TrussCompatibility.unitLoadResponse r a b S k aout
          (lowerBoxLoad (Mechanics.TrussCompatibility.influenceVector r a b S k aout) cap)
        = ∑ i, cap i * min (Mechanics.TrussCompatibility.influenceVector r a b S k aout i) 0 := by
  rw [Mechanics.TrussCompatibility.unitLoadResponse_apply]
  exact lowerBoxLoad_attains_boxLower _ _ hcap

end Mechanics.LoadEnvelope
