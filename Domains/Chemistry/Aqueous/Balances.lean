/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import PhyslibExt.Chemistry.Stoichiometry.Balance

import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!

# Aqueous mass balance, charge balance and the proton condition

Charge balance and component mass balances are linear constraints on species concentrations.
Relative to a proton reference level, the proton condition follows from them. Formation
reactions conserve charge and every component, and their number is a rank-nullity count. An
invertible change of component basis changes none of this.

## i. Overview

Species are indexed by a finite type `ι` and conserved components by a finite type `κ`.
Concentrations are `c : ι → ℝ`, charges `z : ι → ℤ`, component totals `T : κ → ℝ`, and the
component matrix `B : Matrix κ ι ℚ` is over `ℚ` (integer subscripts are cast, and `ℚ` gives
ranks over a field and invertible basis changes). Charge balance `∑ i, (z i : ℝ) * c i = 0` and
the component totals `T k = ∑ i, (B k i : ℝ) * c i` are linear constraints on `c`.

A proton reference level `R : ProtonReferenceLevel z B` takes `H⁺` as the proton. It designates
water, hydronium and hydroxide species, with charges `0`, `1` and `-1`, and a zero level of
species that contains water. Its proton excess is the charge row plus a weighted sum of the
component rows, `R.protonExcess i = z i + ∑ k, R.w k * B k i`, so the charge coefficient is
normalized to `1`, and the structure requires the excess to be `0` on the zero level, `1` on
hydronium and `-1` on hydroxide. Under charge and mass balance the excess-weighted
concentrations sum to the weighted totals `∑ k, R.w k * T k`. The proton condition
`∑ i, R.protonExcess i * c i = 0` therefore follows when these vanish, and they vanish when the
totals come from an electroneutral recipe of zero-level species. The proton condition is
equivalent to the textbook form in which the proton-excess species balance the
proton-deficient ones, and it is a genuine constraint: hydronium alone violates it.

The balance matrix `balanceMatrix z B` stacks the charge row on the component rows: it is a
composition matrix for `Chemistry.Stoichiometry.IsBalanced` whose balance coordinates are the
components and charge. Its kernel is the space of formation reactions, which conserve charge
and every component. With `S = Fintype.card ι` species this space has dimension
`S - (balanceMatrix z B).rank`, by Mathlib rank-nullity, and `S - Matrix.rank B` when every
species charge is the combination `zc ᵥ* B` of its component content, as when each component
carries a fixed charge. This is a dimension count only: not every kernel vector is a chemically
realizable reaction.

For an invertible `P` over `ℚ`, the component matrix `P * B` with the totals `P *ᵥ T`, `P` cast
to `ℝ`, has the same mass-balance solutions as `B` with `T`, and the formation count is
unchanged. A proton reference level transports to the new basis with the same proton excess,
and its weighted totals agree with the old ones. No invariance is claimed for singular `P`.

Scope: bulk electroneutrality only (interfaces are out of scope). Spectator ions are included in
every sum. There are no equilibrium constants, pH values, activity corrections, ionic-strength
models or precipitation equilibria here; the proton condition is linear algebra, not a pH
solver.

## ii. Key results

- `ChargeBalanced`, `MassBalanced`, `HomMassBalanced` : the balance predicates, and
  `massBalanced_iff_mulVec` : mass balance as a matrix equation.
- `ChargeBalanced.add`, `ChargeBalanced.smul`, `HomMassBalanced.add`,
  `HomMassBalanced.smul`, `MassBalanced.sub` : linearity in the concentrations.
- `balanceCombination`, `sum_balanceCombination_mul_eq` : a linear combination of the balance
  rows, and the identity it satisfies under charge and mass balance.
- `ProtonReferenceLevel`, `ProtonReferenceLevel.protonExcess`,
  `ProtonReferenceLevel.ProtonCondition` : a validated proton reference level, its proton excess
  and the proton condition.
- `ProtonReferenceLevel.protonExcess_eq_of_content` : the proton excess of a species made of
  zero-level species plus `m` protons is `m`.
- `ProtonReferenceLevel.protonCondition_of_balances`,
  `ProtonReferenceLevel.protonCondition_of_recipe` : charge and mass balances imply the proton
  condition when the weighted totals vanish, in particular for a recipe of zero-level species.
- `ProtonReferenceLevel.protonCondition_iff`,
  `ProtonReferenceLevel.not_protonCondition_single_hydronium` : the textbook form of the proton
  condition, and a concentration vector that violates it.
- `balanceMatrix`, `isBalanced_balanceMatrix_iff`, `isBalanced_balanceMatrix_iff_balances`,
  `mem_ker_balanceMatrix_iff` : formation reactions conserve charge and every component.
- `independentFormationCount`, `independentFormationCount_eq`,
  `independentFormationCount_eq_of_charge_eq` : the formation-reaction count `S - rank`.
- `massBalanced_basisChange_iff`, `solutionSet_basisChange`,
  `independentFormationCount_basisChange` : invariance of the real mass balances and of the
  formation count under an invertible component basis change.
- `ProtonReferenceLevel.basisChange`, `ProtonReferenceLevel.protonExcess_basisChange`,
  `ProtonReferenceLevel.protonWeightTotal_basisChange`,
  `ProtonReferenceLevel.protonSet_basisChange` : the proton condition survives the same basis
  change.

## iii. Table of contents

- A. Charge and mass balances
- B. Linearity in the concentrations
- C. The proton condition
- D. The formation-equilibrium count
- E. Change of component basis

## iv. References

- W. Stumm and J. J. Morgan, *Aquatic Chemistry: Chemical Equilibria and Rates in Natural
  Waters*, 3rd ed., Wiley, 1996, Ch. 3, "Acids and Bases".
- OpenStax, *Chemistry 2e*, Ch. 14, "Acid-Base Equilibria", §14.1,
  "Brønsted-Lowry Acids and Bases".
- OpenStax, *Chemistry 2e*, Ch. 14, "Acid-Base Equilibria", §14.2, "pH and pOH".
- OpenStax, *Chemistry 2e*, §4.1, "Writing and Balancing Chemical Equations".
- OpenStax, *Chemistry 2e*, §4.3, "Reaction Stoichiometry".
- IUPAC, *Quantities, Units and Symbols in Physical Chemistry* (the Green Book),
  for quantity symbols.

-/

@[expose] public section

namespace Chemistry.Aqueous

open Matrix

open scoped BigOperators

/-!

## A. Charge and mass balances

-/

/-- Bulk charge balance: the charge-weighted concentrations sum to zero.
Spectator ions are included in the sum. -/
def ChargeBalanced {ι : Type*} [Fintype ι] (z : ι → ℤ) (c : ι → ℝ) : Prop :=
  ∑ i, (z i : ℝ) * c i = 0

/-- Component mass balances: each component total `T k` is the `B`-weighted sum
of the concentrations. -/
def MassBalanced {κ ι : Type*} [Fintype ι] (B : Matrix κ ι ℚ) (T : κ → ℝ)
    (c : ι → ℝ) : Prop :=
  ∀ k, T k = ∑ i, (B k i : ℝ) * c i

/-- Homogeneous mass balances: the `B`-weighted sums vanish. These are the
linear (homogeneous) form of the component totals. -/
def HomMassBalanced {κ ι : Type*} [Fintype ι] (B : Matrix κ ι ℚ) (c : ι → ℝ) :
    Prop :=
  ∀ k, (∑ i, (B k i : ℝ) * c i) = 0

/-- Mass balance as a matrix equation: the totals are the component matrix, cast to `ℝ`,
applied to the concentrations. -/
lemma massBalanced_iff_mulVec {κ ι : Type*} [Fintype ι] (B : Matrix κ ι ℚ) (T : κ → ℝ)
    (c : ι → ℝ) : MassBalanced B T c ↔ T = B.map (Rat.cast : ℚ → ℝ) *ᵥ c := by
  rw [funext_iff]
  rfl

/-!

## B. Linearity in the concentrations

The homogeneous balances are closed under addition and scaling; the difference
of two solutions of the inhomogeneous mass balances satisfies the homogeneous
system.

-/

/-- Charge-balanced concentrations are closed under addition. -/
lemma ChargeBalanced.add {ι : Type*} [Fintype ι] {z : ι → ℤ} {c₁ c₂ : ι → ℝ}
    (h₁ : ChargeBalanced z c₁) (h₂ : ChargeBalanced z c₂) :
    ChargeBalanced z (c₁ + c₂) := by
  simp only [ChargeBalanced] at h₁ h₂ ⊢
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h₁, h₂, add_zero]

/-- Charge-balanced concentrations are closed under scaling. -/
lemma ChargeBalanced.smul {ι : Type*} [Fintype ι] {z : ι → ℤ} {c : ι → ℝ}
    {r : ℝ} (h : ChargeBalanced z c) : ChargeBalanced z (r • c) := by
  simp only [ChargeBalanced] at h ⊢
  simp only [Pi.smul_apply, smul_eq_mul] at ⊢
  have e : (∑ i, (z i : ℝ) * (r * c i)) = r * (∑ i, (z i : ℝ) * c i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e, h, mul_zero]

/-- Zero concentrations are charge-balanced. -/
lemma ChargeBalanced.zero {ι : Type*} [Fintype ι] (z : ι → ℤ) :
    ChargeBalanced z 0 := by
  simp [ChargeBalanced]

/-- Homogeneous mass balances are closed under addition. -/
lemma HomMassBalanced.add {κ ι : Type*} [Fintype ι] {B : Matrix κ ι ℚ}
    {c₁ c₂ : ι → ℝ} (h₁ : HomMassBalanced B c₁) (h₂ : HomMassBalanced B c₂) :
    HomMassBalanced B (c₁ + c₂) := by
  simp only [HomMassBalanced] at h₁ h₂ ⊢
  intro k
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h₁ k, h₂ k, add_zero]

/-- Homogeneous mass balances are closed under scaling. -/
lemma HomMassBalanced.smul {κ ι : Type*} [Fintype ι] {B : Matrix κ ι ℚ}
    {c : ι → ℝ} {r : ℝ} (h : HomMassBalanced B c) :
    HomMassBalanced B (r • c) := by
  simp only [HomMassBalanced] at h ⊢
  intro k
  simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
  have e : (∑ i, (B k i : ℝ) * (r * c i))
      = r * (∑ i, (B k i : ℝ) * c i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [e, h k, mul_zero]

/-- Zero concentrations satisfy the homogeneous mass balances. -/
lemma HomMassBalanced.zero {κ ι : Type*} [Fintype ι] (B : Matrix κ ι ℚ) :
    HomMassBalanced B 0 := by
  simp [HomMassBalanced]

/-- The difference of two solutions of the inhomogeneous mass balances
satisfies the homogeneous system. -/
lemma MassBalanced.sub {κ ι : Type*} [Fintype ι] {B : Matrix κ ι ℚ}
    {T : κ → ℝ} {c₁ c₂ : ι → ℝ} (h₁ : MassBalanced B T c₁)
    (h₂ : MassBalanced B T c₂) : HomMassBalanced B (c₁ - c₂) := by
  simp only [MassBalanced] at h₁ h₂
  simp only [HomMassBalanced]
  intro k
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, ← h₁ k, ← h₂ k,
    sub_self]

/-- The set of concentrations satisfying both homogeneous balances is closed
under addition. -/
lemma balances_add {κ ι : Type*} [Fintype ι] {z : ι → ℤ} {B : Matrix κ ι ℚ}
    {c₁ c₂ : ι → ℝ} (h₁ : ChargeBalanced z c₁ ∧ HomMassBalanced B c₁)
    (h₂ : ChargeBalanced z c₂ ∧ HomMassBalanced B c₂) :
    ChargeBalanced z (c₁ + c₂) ∧ HomMassBalanced B (c₁ + c₂) :=
  ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

/-- The set of concentrations satisfying both homogeneous balances is closed
under scaling. -/
lemma balances_smul {κ ι : Type*} [Fintype ι] {z : ι → ℤ} {B : Matrix κ ι ℚ}
    {c : ι → ℝ} {r : ℝ} (h : ChargeBalanced z c ∧ HomMassBalanced B c) :
    ChargeBalanced z (r • c) ∧ HomMassBalanced B (r • c) :=
  ⟨h.1.smul, h.2.smul⟩

/-!

## C. The proton condition

The proton condition is a linear combination of the charge and mass balances. A proton
reference level fixes the combination: the charge coefficient is `1`, and the proton excess is
required to be `0` on the zero level, which contains water, `1` on hydronium and `-1` on
hydroxide.

-/

/-- The coefficient row of a linear combination of the balance equations: `a₀` times the charge
row plus the component rows weighted by `w`, that is `a₀ * z i + ∑ k, w k * B k i`. -/
def balanceCombination {κ ι : Type*} [Fintype κ] (z : ι → ℤ) (B : Matrix κ ι ℚ)
    (a₀ : ℚ) (w : κ → ℚ) : ι → ℚ :=
  fun i => a₀ * (z i : ℚ) + ∑ k, w k * B k i

/-- Under charge and mass balance, the concentrations weighted by a balance combination sum to
the same combination of the component totals; the charge row contributes nothing. -/
lemma sum_balanceCombination_mul_eq {κ ι : Type*} [Fintype ι] [Fintype κ] {z : ι → ℤ}
    {B : Matrix κ ι ℚ} {T : κ → ℝ} {c : ι → ℝ} (a₀ : ℚ) (w : κ → ℚ)
    (hcharge : ChargeBalanced z c) (hmass : MassBalanced B T c) :
    ∑ i, (balanceCombination z B a₀ w i : ℝ) * c i = ∑ k, (w k : ℝ) * T k := by
  simp only [ChargeBalanced] at hcharge
  simp only [MassBalanced] at hmass
  have e1 : (∑ i, (a₀ : ℝ) * (z i : ℝ) * c i)
      = (a₀ : ℝ) * (∑ i, (z i : ℝ) * c i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have e2 : (∑ i, (∑ k, (w k : ℝ) * (B k i : ℝ)) * c i)
      = ∑ k, (w k : ℝ) * T k := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp only [show ∀ i, ((w k : ℝ) * (B k i : ℝ)) * c i
      = (w k : ℝ) * ((B k i : ℝ) * c i) from fun i => by ring]
    rw [← Finset.mul_sum, ← hmass k]
  simp only [balanceCombination, Rat.cast_add, Rat.cast_mul, Rat.cast_sum, Rat.cast_intCast]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [e1, e2, hcharge, mul_zero, zero_add]

/-- A proton reference level for species with charges `z` and component matrix `B`, with `H⁺`
as the proton. It designates water `H₂O`, hydronium `H₃O⁺` and hydroxide `OH⁻` species and a
zero level of species, containing water, that carry no proton excess. The proton excess is the
charge row plus the component rows weighted by `w`, so the charge coefficient is normalized to
`1`; it vanishes on the zero level and equals `1` on hydronium and `-1` on hydroxide, which
carry one proton more and one proton less than water. -/
structure ProtonReferenceLevel {κ ι : Type*} [Fintype κ] (z : ι → ℤ) (B : Matrix κ ι ℚ) where
  /-- The weights of the component rows in the proton excess. -/
  w : κ → ℚ
  /-- The zero-level species, which carry no proton excess. -/
  zeroLevel : Set ι
  /-- The water species `H₂O`. -/
  water : ι
  /-- The hydronium species `H₃O⁺`. -/
  hydronium : ι
  /-- The hydroxide species `OH⁻`. -/
  hydroxide : ι
  /-- Water is neutral. -/
  charge_water : z water = 0
  /-- Hydronium carries charge `1`. -/
  charge_hydronium : z hydronium = 1
  /-- Hydroxide carries charge `-1`. -/
  charge_hydroxide : z hydroxide = -1
  /-- Water belongs to the zero level. -/
  water_mem_zeroLevel : water ∈ zeroLevel
  /-- Every zero-level species has proton excess `0`. -/
  balanceCombination_eq_zero : ∀ i ∈ zeroLevel, balanceCombination z B 1 w i = 0
  /-- Hydronium carries one proton more than water. -/
  balanceCombination_hydronium : balanceCombination z B 1 w hydronium = 1
  /-- Hydroxide carries one proton less than water. -/
  balanceCombination_hydroxide : balanceCombination z B 1 w hydroxide = -1

namespace ProtonReferenceLevel

/-- The proton excess of each species relative to `R`: the charge row plus the component rows
weighted by `R.w`. It is `0` on the zero level, `1` on hydronium and `-1` on hydroxide, so it
counts the protons a species carries in excess of (positive) or short of (negative) the zero
level (`protonExcess_eq_of_content`). -/
def protonExcess {κ ι : Type*} [Fintype κ] {z : ι → ℤ} {B : Matrix κ ι ℚ}
    (R : ProtonReferenceLevel z B) : ι → ℚ :=
  balanceCombination z B 1 R.w

/-- The proton condition relative to `R`: the concentrations weighted by proton excess sum to
zero. -/
def ProtonCondition {κ ι : Type*} [Fintype κ] [Fintype ι] {z : ι → ℤ} {B : Matrix κ ι ℚ}
    (R : ProtonReferenceLevel z B) (c : ι → ℝ) : Prop :=
  ∑ i, (R.protonExcess i : ℝ) * c i = 0

/-- A zero-level species has proton excess `0`. -/
lemma protonExcess_eq_zero {κ ι : Type*} [Fintype κ] {z : ι → ℤ} {B : Matrix κ ι ℚ}
    (R : ProtonReferenceLevel z B) {i : ι} (hi : i ∈ R.zeroLevel) : R.protonExcess i = 0 :=
  R.balanceCombination_eq_zero i hi

/-- Water has proton excess `0`. -/
lemma protonExcess_water {κ ι : Type*} [Fintype κ] {z : ι → ℤ} {B : Matrix κ ι ℚ}
    (R : ProtonReferenceLevel z B) : R.protonExcess R.water = 0 :=
  R.protonExcess_eq_zero R.water_mem_zeroLevel

/-- Hydronium has proton excess `1`. -/
lemma protonExcess_hydronium {κ ι : Type*} [Fintype κ] {z : ι → ℤ} {B : Matrix κ ι ℚ}
    (R : ProtonReferenceLevel z B) : R.protonExcess R.hydronium = 1 :=
  R.balanceCombination_hydronium

/-- Hydroxide has proton excess `-1`. -/
lemma protonExcess_hydroxide {κ ι : Type*} [Fintype κ] {z : ι → ℤ} {B : Matrix κ ι ℚ}
    (R : ProtonReferenceLevel z B) : R.protonExcess R.hydroxide = -1 :=
  R.balanceCombination_hydroxide

/-- The proton excess counts protons: a species whose charge and component content are those of
a combination `a` of zero-level species plus `m` protons (the content of hydronium minus that of
water) has proton excess `m`. -/
lemma protonExcess_eq_of_content {κ ι : Type*} [Fintype κ] [Fintype ι] {z : ι → ℤ}
    {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) {i : ι} (a : ι → ℚ) (m : ℚ)
    (ha : ∀ j, j ∉ R.zeroLevel → a j = 0)
    (hz : (z i : ℚ) = ∑ j, a j * z j + m * (z R.hydronium - z R.water))
    (hB : ∀ k, B k i = ∑ j, a j * B k j + m * (B k R.hydronium - B k R.water)) :
    R.protonExcess i = m := by
  have hexp : ∀ j, R.protonExcess j = (z j : ℚ) + ∑ k, R.w k * B k j := by
    intro j
    simp [protonExcess, balanceCombination]
  have hzero : ∑ j, a j * R.protonExcess j = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ∈ R.zeroLevel
    · rw [R.protonExcess_eq_zero hj, mul_zero]
    · rw [ha j hj, zero_mul]
  calc R.protonExcess i
      = (∑ j, a j * z j + m * (z R.hydronium - z R.water)) +
          ∑ k, R.w k * (∑ j, a j * B k j + m * (B k R.hydronium - B k R.water)) := by
        rw [hexp, hz]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => by rw [hB k])
    _ = ∑ j, a j * R.protonExcess j +
          m * (R.protonExcess R.hydronium - R.protonExcess R.water) := by
        simp only [hexp, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
          (f := fun k j => R.w k * (a j * B k j))]
        have e1 : ∀ j, ∑ k, R.w k * (a j * B k j) = ∑ k, a j * (R.w k * B k j) :=
          fun j => Finset.sum_congr rfl fun k _ => by ring
        have e2 : ∑ k, R.w k * (m * B k R.hydronium) = ∑ k, m * (R.w k * B k R.hydronium) :=
          Finset.sum_congr rfl fun k _ => by ring
        have e3 : ∑ k, R.w k * (m * B k R.water) = ∑ k, m * (R.w k * B k R.water) :=
          Finset.sum_congr rfl fun k _ => by ring
        simp only [e1, e2, e3]
        ring
    _ = m := by rw [hzero, R.protonExcess_hydronium, R.protonExcess_water]; ring

/-- Under charge and mass balance, the proton-excess-weighted concentrations sum to the weighted
component totals `∑ k, R.w k * T k`. -/
lemma sum_protonExcess_mul_eq {κ ι : Type*} [Fintype κ] [Fintype ι] {z : ι → ℤ}
    {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) {T : κ → ℝ} {c : ι → ℝ}
    (hcharge : ChargeBalanced z c) (hmass : MassBalanced B T c) :
    ∑ i, (R.protonExcess i : ℝ) * c i = ∑ k, (R.w k : ℝ) * T k :=
  sum_balanceCombination_mul_eq 1 R.w hcharge hmass

/-- **Proton condition.** Charge balance and the component mass balances imply the proton
condition whenever the reference weights annihilate the component totals. -/
theorem protonCondition_of_balances {κ ι : Type*} [Fintype κ] [Fintype ι] {z : ι → ℤ}
    {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) {T : κ → ℝ} {c : ι → ℝ}
    (hcharge : ChargeBalanced z c) (hmass : MassBalanced B T c)
    (hT : ∑ k, (R.w k : ℝ) * T k = 0) : R.ProtonCondition c := by
  rw [ProtonCondition, R.sum_protonExcess_mul_eq hcharge hmass, hT]

/-- If the totals `T` are the component content of an electroneutral recipe `n₀` made only of
zero-level species, the weighted component totals vanish. -/
lemma weightedTotal_eq_zero_of_recipe {κ ι : Type*} [Fintype κ] [Fintype ι] {z : ι → ℤ}
    {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) {T : κ → ℝ} {n₀ : ι → ℝ}
    (hneutral : ChargeBalanced z n₀) (hrecipe : MassBalanced B T n₀)
    (hzero : ∀ i, i ∉ R.zeroLevel → n₀ i = 0) : ∑ k, (R.w k : ℝ) * T k = 0 := by
  rw [← R.sum_protonExcess_mul_eq hneutral hrecipe]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i ∈ R.zeroLevel
  · rw [R.protonExcess_eq_zero hi, Rat.cast_zero, zero_mul]
  · rw [hzero i hi, mul_zero]

/-- **Proton condition from the recipe.** A charge- and mass-balanced solution whose component
totals come from an electroneutral recipe of zero-level species satisfies the proton
condition. -/
theorem protonCondition_of_recipe {κ ι : Type*} [Fintype κ] [Fintype ι] {z : ι → ℤ}
    {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) {T : κ → ℝ} {c n₀ : ι → ℝ}
    (hcharge : ChargeBalanced z c) (hmass : MassBalanced B T c)
    (hneutral : ChargeBalanced z n₀) (hrecipe : MassBalanced B T n₀)
    (hzero : ∀ i, i ∉ R.zeroLevel → n₀ i = 0) : R.ProtonCondition c :=
  R.protonCondition_of_balances hcharge hmass
    (R.weightedTotal_eq_zero_of_recipe hneutral hrecipe hzero)

/-- The proton condition in textbook form: the concentrations of the proton-excess species,
weighted by their excess, sum to those of the proton-deficient species, weighted by their
deficit. -/
lemma protonCondition_iff {κ ι : Type*} [Fintype κ] [Fintype ι] {z : ι → ℤ}
    {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) (c : ι → ℝ) :
    R.ProtonCondition c ↔
      ∑ i ∈ Finset.univ.filter (fun i => 0 < R.protonExcess i), (R.protonExcess i : ℝ) * c i =
        ∑ i ∈ Finset.univ.filter (fun i => R.protonExcess i < 0),
          -(R.protonExcess i : ℝ) * c i := by
  have hsplit : ∀ i, (R.protonExcess i : ℝ) * c i =
      (if 0 < R.protonExcess i then (R.protonExcess i : ℝ) * c i else 0) +
        (if R.protonExcess i < 0 then (R.protonExcess i : ℝ) * c i else 0) := by
    intro i
    rcases lt_trichotomy (R.protonExcess i) 0 with h | h | h
    · simp [h, not_lt.2 h.le]
    · simp [h]
    · simp [h, not_lt.2 h.le]
  rw [ProtonCondition, Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter]
  simp only [neg_mul, Finset.sum_neg_distrib]
  constructor <;> intro h <;> linarith

/-- The proton condition is a genuine constraint: hydronium alone violates it. -/
lemma not_protonCondition_single_hydronium {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] {z : ι → ℤ} {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) :
    ¬ R.ProtonCondition (Pi.single R.hydronium 1) := by
  simp [ProtonCondition, Pi.single_apply, R.protonExcess_hydronium]

end ProtonReferenceLevel

/-!

## D. The formation-equilibrium count

Formation reactions are the reactions that conserve electric charge and every component: the
kernel of the balance matrix, which stacks the charge row on the component rows. Their number
is a rank-nullity count; a kernel vector need not be a realizable reaction.

-/

/-- The balance matrix: the component rows of `B` with one more row, indexed by `none`, for
electric charge. It is a composition matrix for `Chemistry.Stoichiometry.IsBalanced` whose
balance coordinates are the components and charge. -/
def balanceMatrix {κ ι : Type*} (z : ι → ℤ) (B : Matrix κ ι ℚ) : Matrix (Option κ) ι ℚ :=
  Matrix.of fun r i => r.elim (z i : ℚ) fun k => B k i

/-- The charge row of the balance matrix. -/
@[simp]
lemma balanceMatrix_none {κ ι : Type*} (z : ι → ℤ) (B : Matrix κ ι ℚ) (i : ι) :
    balanceMatrix z B none i = z i :=
  rfl

/-- The component rows of the balance matrix. -/
@[simp]
lemma balanceMatrix_some {κ ι : Type*} (z : ι → ℤ) (B : Matrix κ ι ℚ) (k : κ) (i : ι) :
    balanceMatrix z B (some k) i = B k i :=
  rfl

/-- A reaction `ν` is balanced for the balance matrix exactly when it conserves electric charge
and every component. -/
lemma isBalanced_balanceMatrix_iff {κ ι : Type*} [Fintype ι] (z : ι → ℤ) (B : Matrix κ ι ℚ)
    (ν : ι → ℚ) :
    Stoichiometry.IsBalanced (balanceMatrix z B) ν ↔
      ∑ i, (z i : ℚ) * ν i = 0 ∧ B *ᵥ ν = 0 := by
  rw [Stoichiometry.IsBalanced, funext_iff, Option.forall, funext_iff]
  rfl

/-- A rational reaction is balanced for the balance matrix exactly when, read as real
concentrations, it satisfies both homogeneous balances. -/
lemma isBalanced_balanceMatrix_iff_balances {κ ι : Type*} [Fintype ι] (z : ι → ℤ)
    (B : Matrix κ ι ℚ) (ν : ι → ℚ) :
    Stoichiometry.IsBalanced (balanceMatrix z B) ν ↔
      ChargeBalanced z (fun i => (ν i : ℝ)) ∧ HomMassBalanced B (fun i => (ν i : ℝ)) := by
  rw [isBalanced_balanceMatrix_iff, funext_iff]
  simp only [ChargeBalanced, HomMassBalanced, Matrix.mulVec, dotProduct, Pi.zero_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast congrArg (Rat.cast : ℚ → ℝ) h1,
      fun k => by exact_mod_cast congrArg (Rat.cast : ℚ → ℝ) (h2 k)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, fun k => by exact_mod_cast h2 k⟩

/-- The dimension of the space of formation reactions: reactions with rational stoichiometric
coefficients that conserve electric charge and every component, the kernel of the balance
matrix. -/
noncomputable def independentFormationCount {κ ι : Type*} [Fintype ι] (z : ι → ℤ)
    (B : Matrix κ ι ℚ) : ℕ :=
  Module.finrank ℚ (LinearMap.ker (balanceMatrix z B).mulVecLin)

/-- A reaction lies in the kernel counted by `independentFormationCount` exactly when it is
balanced, in the sense of `Chemistry.Stoichiometry.IsBalanced`, for the balance matrix. -/
lemma mem_ker_balanceMatrix_iff {κ ι : Type*} [Fintype ι] (z : ι → ℤ) (B : Matrix κ ι ℚ)
    (ν : ι → ℚ) :
    ν ∈ LinearMap.ker (balanceMatrix z B).mulVecLin ↔
      Stoichiometry.IsBalanced (balanceMatrix z B) ν := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rfl

/-- **Formation count.** With `S = Fintype.card ι` species, the formation reactions form a space
of dimension `S` minus the rank of the balance matrix. -/
theorem independentFormationCount_eq {κ ι : Type*} [Fintype ι] (z : ι → ℤ)
    (B : Matrix κ ι ℚ) :
    independentFormationCount z B = Fintype.card ι - (balanceMatrix z B).rank := by
  have h := (balanceMatrix z B).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at h
  have hr : (balanceMatrix z B).rank =
      Module.finrank ℚ (LinearMap.range (balanceMatrix z B).mulVecLin) := rfl
  unfold independentFormationCount
  omega

/-- **Formation count with charged components.** If every species charge is the combination
`zc ᵥ* B` of its component content, as when each component carries a fixed charge `zc k`,
conserving the components conserves charge, and the formation reactions form a space of
dimension `S - C` with `C = Matrix.rank B`. -/
theorem independentFormationCount_eq_of_charge_eq {κ ι : Type*} [Fintype ι] [Fintype κ]
    (z : ι → ℤ) (B : Matrix κ ι ℚ) (zc : κ → ℚ) (hz : ∀ i, (z i : ℚ) = (zc ᵥ* B) i) :
    independentFormationCount z B = Fintype.card ι - B.rank := by
  have hker : LinearMap.ker (balanceMatrix z B).mulVecLin = LinearMap.ker B.mulVecLin := by
    ext ν
    rw [mem_ker_balanceMatrix_iff, isBalanced_balanceMatrix_iff, LinearMap.mem_ker,
      Matrix.mulVecLin_apply]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    have hdot : (fun i => (z i : ℚ)) ⬝ᵥ ν = zc ⬝ᵥ (B *ᵥ ν) := by
      rw [Matrix.dotProduct_mulVec]
      congr 1
      funext i
      exact hz i
    rw [h, dotProduct_zero] at hdot
    exact hdot
  have h := B.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at h
  have hr : B.rank = Module.finrank ℚ (LinearMap.range B.mulVecLin) := rfl
  unfold independentFormationCount
  rw [hker]
  omega

/-!

## E. Change of component basis

An invertible change of component basis `P` over `ℚ` replaces `B` by `P * B` and the real
totals `T` by `P *ᵥ T`, with `P` cast to `ℝ`. It preserves the mass-balance solutions, the
formation count, and the proton condition of the transported reference level. Nothing is
claimed for singular changes.

-/

/-- An invertible change of component basis leaves the mass-balance solutions unchanged: `c`
balances `P * B` against `P *ᵥ T`, with `P` cast to `ℝ`, exactly when it balances `B` against
`T`. -/
lemma massBalanced_basisChange_iff {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix κ ι ℚ) (T : κ → ℝ) (P : Matrix κ κ ℚ) (hP : IsUnit P.det) (c : ι → ℝ) :
    MassBalanced (P * B) (P.map (Rat.cast : ℚ → ℝ) *ᵥ T) c ↔ MassBalanced B T c := by
  have hmap : (P * B).map (Rat.cast : ℚ → ℝ) =
      P.map (Rat.cast : ℚ → ℝ) * B.map (Rat.cast : ℚ → ℝ) :=
    Matrix.map_mul (f := Rat.castHom ℝ)
  have hPℝ : IsUnit (P.map (Rat.cast : ℚ → ℝ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← Rat.cast_det]
    exact hP.map (Rat.castHom ℝ)
  rw [massBalanced_iff_mulVec, massBalanced_iff_mulVec, hmap, ← Matrix.mulVec_mulVec]
  exact (Matrix.mulVec_injective_of_isUnit hPℝ).eq_iff

/-- **Basis invariance of the mass balances.** An invertible change of component basis leaves
the set of mass-balanced concentrations unchanged. -/
theorem solutionSet_basisChange {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : Matrix κ ι ℚ) (T : κ → ℝ) (P : Matrix κ κ ℚ) (hP : IsUnit P.det) :
    {c | MassBalanced B T c} =
      {c | MassBalanced (P * B) (P.map (Rat.cast : ℚ → ℝ) *ᵥ T) c} :=
  Set.ext fun c => (massBalanced_basisChange_iff B T P hP c).symm

/-- An invertible change of component basis leaves the formation count unchanged. -/
lemma independentFormationCount_basisChange {κ ι : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (z : ι → ℤ) (B : Matrix κ ι ℚ) (P : Matrix κ κ ℚ) (hP : IsUnit P.det) :
    independentFormationCount z (P * B) = independentFormationCount z B := by
  have hinj := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det P).2 hP)
  have hker : LinearMap.ker (balanceMatrix z (P * B)).mulVecLin =
      LinearMap.ker (balanceMatrix z B).mulVecLin := by
    ext ν
    rw [mem_ker_balanceMatrix_iff, mem_ker_balanceMatrix_iff, isBalanced_balanceMatrix_iff,
      isBalanced_balanceMatrix_iff, ← Matrix.mulVec_mulVec]
    refine and_congr_right fun _ => ⟨fun h => hinj ?_, fun h => by rw [h, Matrix.mulVec_zero]⟩
    rw [h, Matrix.mulVec_zero]
  unfold independentFormationCount
  rw [hker]

/-- The balance combination built in the new basis, with weights transported by `P⁻¹`, equals
the one built in the old basis. -/
lemma balanceCombination_basisChange {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (z : ι → ℤ) (B : Matrix κ ι ℚ) (a₀ : ℚ) (w : κ → ℚ) (P : Matrix κ κ ℚ)
    (hP : IsUnit P.det) :
    balanceCombination z (P * B) a₀ (w ᵥ* P⁻¹) = balanceCombination z B a₀ w := by
  have key : (w ᵥ* P⁻¹) ᵥ* (P * B) = w ᵥ* B := by
    have h1 : (w ᵥ* P⁻¹) ᵥ* P = w := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul P hP, Matrix.vecMul_one]
    rw [← Matrix.vecMul_vecMul, h1]
  funext i
  change a₀ * (z i : ℚ) + ∑ k, (w ᵥ* P⁻¹) k * (P * B) k i
    = a₀ * (z i : ℚ) + ∑ k, w k * B k i
  congr 1
  exact congrFun key i

namespace ProtonReferenceLevel

/-- The reference level `R` in the component basis `P * B`: the same designated species and
zero level, with the weights `R.w ᵥ* P⁻¹`. -/
noncomputable def basisChange {κ ι : Type*} [Fintype κ] [DecidableEq κ] {z : ι → ℤ}
    {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) (P : Matrix κ κ ℚ) (hP : IsUnit P.det) :
    ProtonReferenceLevel z (P * B) where
  w := R.w ᵥ* P⁻¹
  zeroLevel := R.zeroLevel
  water := R.water
  hydronium := R.hydronium
  hydroxide := R.hydroxide
  charge_water := R.charge_water
  charge_hydronium := R.charge_hydronium
  charge_hydroxide := R.charge_hydroxide
  water_mem_zeroLevel := R.water_mem_zeroLevel
  balanceCombination_eq_zero := by
    rw [balanceCombination_basisChange z B 1 R.w P hP]
    exact R.balanceCombination_eq_zero
  balanceCombination_hydronium := by
    rw [balanceCombination_basisChange z B 1 R.w P hP]
    exact R.balanceCombination_hydronium
  balanceCombination_hydroxide := by
    rw [balanceCombination_basisChange z B 1 R.w P hP]
    exact R.balanceCombination_hydroxide

/-- The transported reference level has the same proton excess. -/
lemma protonExcess_basisChange {κ ι : Type*} [Fintype κ] [DecidableEq κ] {z : ι → ℤ}
    {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) (P : Matrix κ κ ℚ)
    (hP : IsUnit P.det) : (R.basisChange P hP).protonExcess = R.protonExcess :=
  balanceCombination_basisChange z B 1 R.w P hP

/-- The transported weights give the same weighted total of the transported real totals, so
they annihilate `P *ᵥ T` exactly when `R.w` annihilates `T`. -/
lemma protonWeightTotal_basisChange {κ ι : Type*} [Fintype κ] [DecidableEq κ] {z : ι → ℤ}
    {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) (P : Matrix κ κ ℚ)
    (hP : IsUnit P.det) (T : κ → ℝ) :
    ∑ k, ((R.basisChange P hP).w k : ℝ) * (P.map (Rat.cast : ℚ → ℝ) *ᵥ T) k =
      ∑ k, (R.w k : ℝ) * T k := by
  have key : (R.w ᵥ* P⁻¹) ᵥ* P = R.w := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul P hP, Matrix.vecMul_one]
  have hcast : (fun k => (((R.w ᵥ* P⁻¹) k : ℚ) : ℝ)) ᵥ* P.map (Rat.cast : ℚ → ℝ) =
      fun k => ((R.w k : ℚ) : ℝ) := by
    funext k
    have := (Rat.castHom ℝ).map_vecMul P (R.w ᵥ* P⁻¹) k
    rw [key] at this
    exact this.symm
  change (fun k => (((R.w ᵥ* P⁻¹) k : ℚ) : ℝ)) ⬝ᵥ (P.map (Rat.cast : ℚ → ℝ) *ᵥ T) =
    (fun k => ((R.w k : ℚ) : ℝ)) ⬝ᵥ T
  rw [Matrix.dotProduct_mulVec, hcast]

/-- The proton condition of the transported reference level is the same constraint. -/
lemma protonSet_basisChange {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    {z : ι → ℤ} {B : Matrix κ ι ℚ} (R : ProtonReferenceLevel z B) (P : Matrix κ κ ℚ)
    (hP : IsUnit P.det) :
    {c | (R.basisChange P hP).ProtonCondition c} = {c | R.ProtonCondition c} := by
  ext c
  simp only [Set.mem_ofPred_eq, ProtonCondition, protonExcess_basisChange]

end ProtonReferenceLevel

end Chemistry.Aqueous
