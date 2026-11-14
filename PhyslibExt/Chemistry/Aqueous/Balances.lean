/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.Tactic.Ring
/-!

# Aqueous mass balance, charge balance and the proton condition

Charge balance and component mass balances are linear constraints on species
concentrations. The proton condition is a linear combination of them, not an
independent equation. The count of independent formation equilibria is a
rank-nullity dimension count. All of it is invariant under an invertible change
of component basis.

## i. Overview

Species are indexed by a finite type `ι` and conserved components by a finite
type `κ`. Concentrations are `c : ι → ℝ`, charges `z : ι → ℤ`, component totals
`T : κ → ℝ`, and the component matrix `B : Matrix κ ι ℚ` is over `ℚ` (this
choice is fixed here: integer subscripts are cast, and `ℚ` is needed for the
rank over a field and for invertible basis changes). Charge balance
`∑ i, (z i : ℝ) * c i = 0` and the component totals
`T k = ∑ i, (B k i : ℝ) * c i` are linear constraints on `c`.

The proton reference level is the `H2O / H3O+ / OH-` reference with `H+` as the
proton. It is encoded by a row `(a₀, w)` over the balance coordinates: the
proton excess of species `i` is `p i = a₀ * z i + ∑ k, w k * B k i`, defined
from the charges and the component matrix. The proton condition
`∑ i, (p i : ℝ) * c i = 0` then follows from charge and mass balances whenever
the weights annihilate the totals, `∑ k, (w k : ℝ) * T k = 0`.

With `S = Fintype.card ι` species and `C = Matrix.rank B` independent
components, the space of independent formation reactions has dimension `S - C`,
by Mathlib rank-nullity applied to `B.mulVecLin`. This is a dimension count
only: not every kernel vector is a chemically realizable equilibrium, and
realizability is chemistry beyond the linear algebra. The rank argument is
re-derived from Mathlib here; this module imports no ATLAS chemistry module.

If `B' = P * B` and `T' = P *ᵥ T` for an invertible `P`, the solution sets
coincide, and the derived proton condition is unchanged as a constraint set.
No invariance is claimed for singular `P`.

Scope: bulk electroneutrality only (interfaces are out of scope). Spectator
ions are included in every sum. There are no equilibrium constants, pH values,
activity corrections, ionic-strength models or precipitation equilibria here;
the proton condition is linear algebra, not a pH solver.

## ii. Key results

- `ChargeBalanced`, `MassBalanced`, `HomMassBalanced` : the balance predicates.
- `ChargeBalanced.add`, `ChargeBalanced.smul`, `HomMassBalanced.add`,
  `HomMassBalanced.smul`, `MassBalanced.sub` : linearity in the concentrations.
- `protonExcess`, `ProtonCondition` : the proton row built from `(z, B)` and
  the proton-condition equation.
- `protonCondition_of_balances` : charge plus mass balances derive the proton
  condition, with exhibited reference coefficients.
- `independentFormationCount`, `independentFormationCount_eq` : the `S - C`
  formation-equilibrium count.
- `solutionSet_basisChange` : the solution set is unchanged by an invertible
  component basis change.
- `protonExcess_basisChange`, `protonWeightTotal_basisChange`,
  `protonSet_basisChange` : the derived proton condition survives the same
  basis change.

## iii. Table of contents

- A. Charge and mass balances
- B. Linearity in the concentrations
- C. The proton condition
- D. The formation-equilibrium count
- E. Change of component basis

## iv. References

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

The proton condition is a linear combination of the charge and mass balances,
never an independent hypothesis: the proton row is built from the charges and
the component matrix, and the equation follows from the balances.

-/

/-- Proton excess of species `i` relative to the `H2O / H3O+ / OH-` reference
level with `H+` as the proton, defined from the charges `z` and the component
matrix `B`. The pair `(a₀, w)` is the reference level, written as a row over
the charge coordinate and the component rows. -/
def protonExcess {κ ι : Type*} [Fintype κ] (z : ι → ℤ) (B : Matrix κ ι ℚ)
    (a₀ : ℚ) (w : κ → ℚ) : ι → ℚ :=
  fun i => a₀ * (z i : ℚ) + ∑ k, w k * B k i

/-- The proton condition for a proton row `p`: proton excesses weighted by
concentrations sum to zero. -/
def ProtonCondition {ι : Type*} [Fintype ι] (p : ι → ℚ) (c : ι → ℝ) : Prop :=
  ∑ i, (p i : ℝ) * c i = 0

/-- Charge and mass balances derive the proton condition for the proton row
built from them, whenever the reference weights annihilate the totals. The
coefficients `(a₀, w)` are exhibited, not assumed. -/
theorem protonCondition_of_balances {κ ι : Type*} [Fintype ι] [Fintype κ]
    (z : ι → ℤ) (B : Matrix κ ι ℚ) (T : κ → ℝ) (c : ι → ℝ) (a₀ : ℚ)
    (w : κ → ℚ) (hcharge : ChargeBalanced z c) (hmass : MassBalanced B T c)
    (hT : ∑ k, (w k : ℝ) * T k = 0) :
    ProtonCondition (protonExcess z B a₀ w) c := by
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
  simp only [ProtonCondition, protonExcess, Rat.cast_add, Rat.cast_mul,
    Rat.cast_sum, Rat.cast_intCast]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [e1, e2, hcharge, hT, mul_zero, add_zero]

/-!

## D. The formation-equilibrium count

With `S` species and `C` independent components, the space of independent
formation reactions has dimension `S - C`, by rank-nullity. This re-derives the
rank argument from Mathlib; it is a dimension count, and a kernel vector need
not be a realizable equilibrium.

-/

/-- The dimension of the space of independent formation reactions: the
`ℚ`-dimension of the kernel of the component matrix as a linear map. -/
noncomputable def independentFormationCount {κ ι : Type*} [Fintype ι]
    (B : Matrix κ ι ℚ) : ℕ :=
  Module.finrank ℚ (LinearMap.ker B.mulVecLin)

/-- `S` species and `C = Matrix.rank B` independent components give `S - C`
independent formation reactions. -/
theorem independentFormationCount_eq {κ ι : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix κ ι ℚ) :
    independentFormationCount B = Fintype.card ι - B.rank := by
  have h := B.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at h
  show Module.finrank ℚ (LinearMap.ker B.mulVecLin) = Fintype.card ι - B.rank
  have hr : B.rank = Module.finrank ℚ (LinearMap.range B.mulVecLin) := rfl
  omega

/-!

## E. Change of component basis

An invertible change of component basis preserves the solution set and the
derived proton condition. Nothing is claimed for singular changes.

-/

/-- If `B' = P * B` and `T' = P *ᵥ T` for an invertible `P`, the solution sets
coincide. -/
theorem solutionSet_basisChange {κ ι : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (B : Matrix κ ι ℚ) (T : κ → ℚ) (P : Matrix κ κ ℚ)
    (hP : IsUnit P.det) :
    {c | B *ᵥ c = T} = {c | (P * B) *ᵥ c = P *ᵥ T} := by
  apply Set.ext
  intro c
  show (B *ᵥ c = T) ↔ ((P * B) *ᵥ c = P *ᵥ T)
  constructor
  · intro h
    rw [← Matrix.mulVec_mulVec, h]
  · intro h
    have h2 : P *ᵥ (B *ᵥ c) = P *ᵥ T := by
      rw [Matrix.mulVec_mulVec]
      exact h
    have inv_cancel : ∀ x : κ → ℚ, P⁻¹ *ᵥ (P *ᵥ x) = x := by
      intro x
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP,
        Matrix.one_mulVec]
    have h3 := congrArg (P⁻¹ *ᵥ ·) h2
    rw [inv_cancel, inv_cancel] at h3
    exact h3

/-- The proton row built in the new basis, with weights transported by `P⁻¹`,
equals the proton row built in the old basis. -/
theorem protonExcess_basisChange {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    (z : ι → ℤ) (B : Matrix κ ι ℚ) (a₀ : ℚ) (w : κ → ℚ) (P : Matrix κ κ ℚ)
    (hP : IsUnit P.det) :
    protonExcess z (P * B) a₀ (w ᵥ* P⁻¹) = protonExcess z B a₀ w := by
  have key : (w ᵥ* P⁻¹) ᵥ* (P * B) = w ᵥ* B := by
    have h1 : (w ᵥ* P⁻¹) ᵥ* P = w := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul P hP, Matrix.vecMul_one]
    rw [← Matrix.vecMul_vecMul, h1]
  funext i
  show a₀ * (z i : ℚ) + ∑ k, (w ᵥ* P⁻¹) k * (P * B) k i
    = a₀ * (z i : ℚ) + ∑ k, w k * B k i
  congr 1
  exact congrFun key i

/-- The reference weights annihilate the new totals exactly when they
annihilate the old ones, up to the basis change. -/
theorem protonWeightTotal_basisChange {κ : Type*} [Fintype κ] [DecidableEq κ]
    (T : κ → ℚ) (w : κ → ℚ) (P : Matrix κ κ ℚ) (hP : IsUnit P.det) :
    ∑ j, (w ᵥ* P⁻¹) j * (P *ᵥ T) j = ∑ k, w k * T k := by
  have key : (w ᵥ* P⁻¹) ᵥ* P = w := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul P hP, Matrix.vecMul_one]
  have h : (w ᵥ* P⁻¹) ⬝ᵥ (P *ᵥ T) = w ⬝ᵥ T := by
    rw [Matrix.dotProduct_mulVec, key]
  exact h

/-- The derived proton condition is unchanged as a constraint set by an
invertible component basis change. -/
theorem protonSet_basisChange {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] (z : ι → ℤ) (B : Matrix κ ι ℚ) (a₀ : ℚ) (w : κ → ℚ)
    (P : Matrix κ κ ℚ) (hP : IsUnit P.det) :
    {c | ProtonCondition (protonExcess z (P * B) a₀ (w ᵥ* P⁻¹)) c}
      = {c | ProtonCondition (protonExcess z B a₀ w) c} := by
  rw [protonExcess_basisChange z B a₀ w P hP]

end Chemistry.Aqueous
