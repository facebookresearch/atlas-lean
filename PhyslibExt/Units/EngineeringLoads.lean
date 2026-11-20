/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Units.EngineeringQuantities
public import PhyslibExt.Mechanics.HarmonicMechanics
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dimensioned planar load projection

## i. Overview

Forces are `WithDim forceDim (ι → ℝ)` component vectors in one
frame (`ι = Fin 2` for moments); lever arms are
`WithDim (single .length) (Fin 2 → ℝ)` positions relative to the
moment point; the planar moment `forceMoment2D` is a sum of
`WithDim` products, of dimension `forceDim * single .length`.
Scalar projection is `.val`, and retagging is `⟨x⟩` at a declared
dimension only (`forceDim`, `single .length`,
`forceDim * single .length`). `WithDim` carriers are in `Type`,
so the typed component lemmas take `ι : Type`; the
coordinate-only round trip
`force_components_dimScale_round_trip` is
universe-polymorphic. The canonical balance is
`IsEquilibrated` and `moment2D` of
`PhyslibExt.Mechanics.HarmonicMechanics` on the projected
coordinates. A change of units multiplies a coordinate of
dimension `d` by `u1.dimScale u2 d`, with `UnitScale` over
`ISQDimensionBase`. The pressure force is the outward-normal
component `-p A` of a uniform pressure `p` on a face of positive
area `A`, in the tension-positive convention of
`PhyslibExt.Units.EngineeringFrames`: pressure is the negative
of tension-positive normal stress.

Not claimed: type safety of physical roles. Equal dimensions are
not distinguished (a moment has the dimension of work, a line
load that of a translational stiffness), and `WithDim` adds any
two quantities with the same index, for example two absolute
temperatures. That a force plus a pressure does not elaborate is
a fact about the type interface, checked in tests, not a theorem.

## ii. Key results

- `Units.EngineeringLoads.planarLoad_balance_iff`: typed force
  and moment balance iff the projected coordinates are
  equilibrated with zero canonical moment.
- `Units.EngineeringLoads.forceMoment2D` and
  `forceMoment2D_val`: the typed planar moment and its scalar
  projection.
- `Units.EngineeringLoads.forceMoment2D_dimScale` and
  `planarLoad_balance_dimScale_iff`: unit conversion of the
  moment and invariance of the balance.
- `Units.EngineeringLoads.pressureForce`,
  `normalStress_pressureForce`, `pressureForce_normalStress`:
  pressure on a positive area gives the outward-normal force
  `-p A`, whose tension-positive normal stress is `-p`.

## iii. Table of contents

- A. Declared dimensions
- B. One force balance
- C. Force-times-length moment balance
- D. Unit conversion at the declared dimensions
- E. Pressure on a positive area

## iv. References

- ISO 80000-4, *Quantities and units — Part 4: Mechanics*: force,
  pressure (stress) and moment of force.
- `PhyslibExt.Units.QuantityDimensions` and
  `PhyslibExt.Units.EngineeringQuantities` for the ISQ dimension
  names and `dimScale` rescaling lemmas.
- `PhyslibExt.Mechanics.HarmonicMechanics` for `resultantForce`,
  `IsEquilibrated` and `moment2D`.
-/

@[expose] public section

namespace Units.EngineeringLoads

open Dimension Units.QuantityDimensions Units.EngineeringQuantities
open PhyslibExt.Mechanics.HarmonicMechanics

/-! ## A. Declared dimensions -/

/-- A force is not a pressure: `forceDim ≠ stressDim`, so no `WithDim.cast` relates a force and
a pressure. -/
lemma forceDim_ne_stressDim : forceDim ≠ stressDim := by
  decide

/-- Force, pressure (the stress dimension), moment (force times lever arm) and line load (force
per length) are four distinct dimensions. Equal dimensions with different roles are not
separated: a moment has the energy dimension and a line load the translational stiffness
dimension. -/
lemma forceDim_stressDim_moment_lineLoad_nodup :
    [forceDim, stressDim, forceDim * single ISQDimensionBase.length,
      forceDim / single ISQDimensionBase.length].Nodup := by
  decide

/-! ## B. One force balance -/

/-- The scalar projection of the `WithDim` resultant of a force family is the canonical
resultant of the projected coordinates. -/
lemma sum_force_val {ρ : Type*} [Fintype ρ] {ι : Type}
    (F : ρ → WithDim forceDim (ι → ℝ)) :
    (∑ r, F r).val = resultantForce (fun r => (F r).val) := by
  exact map_sum (⟨⟨WithDim.val, rfl⟩, fun _ _ => rfl⟩ :
    WithDim forceDim (ι → ℝ) →+ (ι → ℝ)) F Finset.univ

/-- A force family balances as `WithDim` quantities exactly when its projected coordinates are
equilibrated in the canonical sense. -/
lemma sum_force_eq_zero_iff {ρ : Type*} [Fintype ρ] {ι : Type}
    (F : ρ → WithDim forceDim (ι → ℝ)) :
    ∑ r, F r = 0 ↔ IsEquilibrated (fun r => (F r).val) := by
  unfold IsEquilibrated
  rw [← sum_force_val]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact WithDim.ext _ _ h

/-- Retagging at `forceDim`: the `WithDim` resultant of coordinates retagged as forces is the
canonical resultant retagged as a force. -/
lemma sum_retag_force {ρ : Type*} [Fintype ρ] {ι : Type} (f : ρ → ι → ℝ) :
    ∑ r, (⟨f r⟩ : WithDim forceDim (ι → ℝ)) = ⟨resultantForce f⟩ := by
  apply WithDim.ext
  rw [sum_force_val]

/-! ## C. Force-times-length moment balance -/

/-- The planar moment about the moment point of forces `F i` applied at lever arms `x i`
(positions relative to the moment point, in one frame), formed from `WithDim` products of force
and length components, so its dimension `forceDim * single .length` is computed by the type
system. The dimension equals `energyDim`; the type does not distinguish a moment from work. -/
def forceMoment2D {ρ : Type*} [Fintype ρ]
    (x : ρ → WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ))
    (F : ρ → WithDim forceDim (Fin 2 → ℝ)) :
    WithDim (forceDim * single ISQDimensionBase.length) ℝ :=
  ∑ i, ((⟨(F i).val 1⟩ : WithDim forceDim ℝ) *
      (⟨(x i).val 0⟩ : WithDim (single ISQDimensionBase.length) ℝ) -
    (⟨(F i).val 0⟩ : WithDim forceDim ℝ) *
      (⟨(x i).val 1⟩ : WithDim (single ISQDimensionBase.length) ℝ))

/-- The scalar projection of the typed moment is the canonical planar moment of the projected
lever arms and forces. -/
lemma forceMoment2D_val {ρ : Type*} [Fintype ρ]
    (x : ρ → WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ))
    (F : ρ → WithDim forceDim (Fin 2 → ℝ)) :
    (forceMoment2D x F).val = moment2D (fun i => (x i).val) (fun i => (F i).val) := by
  unfold forceMoment2D moment2D
  have hval : ∀ G : ρ → WithDim (forceDim * single ISQDimensionBase.length) ℝ,
      (∑ i, G i).val = ∑ i, (G i).val := fun G =>
    map_sum (⟨⟨WithDim.val, rfl⟩, fun _ _ => rfl⟩ :
      WithDim (forceDim * single ISQDimensionBase.length) ℝ →+ ℝ) G Finset.univ
  rw [hval]
  apply Finset.sum_congr rfl
  intro i _
  simp only [WithDim.val_sub, WithDim.withDim_hMul_val]
  ring

/-- Retagging at `single .length` and `forceDim`: the typed moment of retagged coordinates is
the canonical planar moment retagged at `forceDim * single .length`. -/
lemma forceMoment2D_retag {ρ : Type*} [Fintype ρ] (r f : ρ → Fin 2 → ℝ) :
    forceMoment2D (fun i => (⟨r i⟩ : WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ)))
        (fun i => (⟨f i⟩ : WithDim forceDim (Fin 2 → ℝ))) =
      ⟨moment2D r f⟩ := by
  apply WithDim.ext
  rw [forceMoment2D_val]

/-- The typed moment vanishes exactly when the canonical planar moment of the projected
coordinates vanishes. -/
lemma forceMoment2D_eq_zero_iff {ρ : Type*} [Fintype ρ]
    (x : ρ → WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ))
    (F : ρ → WithDim forceDim (Fin 2 → ℝ)) :
    forceMoment2D x F = 0 ↔ moment2D (fun i => (x i).val) (fun i => (F i).val) = 0 := by
  constructor
  · intro h
    rw [← forceMoment2D_val, h]
    rfl
  · intro h
    apply WithDim.ext
    rw [forceMoment2D_val]
    exact h

/-- Main result: a planar load system with forces typed at `forceDim` and lever arms typed at
`single .length` satisfies the typed force balance and the typed force-times-length moment
balance exactly when its projected coordinates are equilibrated and have zero canonical planar
moment. -/
lemma planarLoad_balance_iff {ρ : Type*} [Fintype ρ]
    (x : ρ → WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ))
    (F : ρ → WithDim forceDim (Fin 2 → ℝ)) :
    (∑ i, F i = 0 ∧ forceMoment2D x F = 0) ↔
      (IsEquilibrated (fun i => (F i).val) ∧
        moment2D (fun i => (x i).val) (fun i => (F i).val) = 0) := by
  rw [sum_force_eq_zero_iff, forceMoment2D_eq_zero_iff]

/-! ## D. Unit conversion at the declared dimensions -/

/-- Converting force coordinates from `u1` to `u2` and back returns them. -/
private lemma force_coord_dimScale_round_trip_of
    (hround : ∀ {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
      (d : Dimension B) (x : ℝ), (u2.dimScale u1 d : ℝ) * ((u1.dimScale u2 d : ℝ) * x) = x)
    (u1 u2 : UnitScale ISQDimensionBase) {ι : Type*} (f : ι → ℝ) :
    (u2.dimScale u1 forceDim : ℝ) • ((u1.dimScale u2 forceDim : ℝ) • f) = f := by
  funext i
  simp only [Pi.smul_apply]
  exact hround _ _ _ _


/-- Converting force coordinates from `u1` to `u2` and back
returns them: the component form of
`Units.QuantityDimensions.dimScale_round_trip` at `forceDim`
(the scalar form is
`Units.EngineeringQuantities.forceDim_dimScale_round_trip`). -/
lemma force_components_dimScale_round_trip
    (u1 u2 : UnitScale ISQDimensionBase) {ι : Type*} (f : ι → ℝ) :
    (u2.dimScale u1 forceDim : ℝ) • ((u1.dimScale u2 forceDim : ℝ) • f) = f :=
  force_coord_dimScale_round_trip_of
    Units.QuantityDimensions.dimScale_round_trip u1 u2 f

/-- A force vector typed as `WithDim forceDim (ι → ℝ)` converts from `u1` to `u2` and back to
itself. -/
private lemma force_withDim_dimScale_round_trip_of
    (hround : ∀ {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
      (d : Dimension B) (x : ℝ), (u2.dimScale u1 d : ℝ) * ((u1.dimScale u2 d : ℝ) * x) = x)
    (u1 u2 : UnitScale ISQDimensionBase) {ι : Type} (F : WithDim forceDim (ι → ℝ)) :
    (⟨(u2.dimScale u1 forceDim : ℝ) • ((u1.dimScale u2 forceDim : ℝ) • F.val)⟩ :
      WithDim forceDim (ι → ℝ)) = F := by
  apply WithDim.ext
  exact force_coord_dimScale_round_trip_of hround u1 u2 F.val


/-- A force vector typed as `WithDim forceDim (ι → ℝ)`
converts from `u1` to `u2` and back to itself (the scalar
form is `Units.EngineeringQuantities.force_withDim_round_trip`). -/
lemma force_vector_withDim_dimScale_round_trip
    (u1 u2 : UnitScale ISQDimensionBase) {ι : Type}
    (F : WithDim forceDim (ι → ℝ)) :
    (⟨(u2.dimScale u1 forceDim : ℝ) • ((u1.dimScale u2 forceDim : ℝ) • F.val)⟩ :
      WithDim forceDim (ι → ℝ)) = F :=
  force_withDim_dimScale_round_trip_of
    Units.QuantityDimensions.dimScale_round_trip u1 u2 F

/-- Converting a moment coordinate from `u1` to `u2` and back returns it. -/
private lemma moment_dimScale_round_trip_of
    (hround : ∀ {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
      (d : Dimension B) (x : ℝ), (u2.dimScale u1 d : ℝ) * ((u1.dimScale u2 d : ℝ) * x) = x)
    (u1 u2 : UnitScale ISQDimensionBase) (m : ℝ) :
    (u2.dimScale u1 (forceDim * single ISQDimensionBase.length) : ℝ) *
      ((u1.dimScale u2 (forceDim * single ISQDimensionBase.length) : ℝ) * m) = m := by
  exact hround _ _ _ _


/-- Converting a moment coordinate from `u1` to `u2` and
back returns it. -/
lemma moment_dimScale_round_trip
    (u1 u2 : UnitScale ISQDimensionBase) (m : ℝ) :
    (u2.dimScale u1 (forceDim * single ISQDimensionBase.length) : ℝ) *
      ((u1.dimScale u2 (forceDim * single ISQDimensionBase.length) : ℝ) * m) = m :=
  moment_dimScale_round_trip_of
    Units.QuantityDimensions.dimScale_round_trip u1 u2 m

/-- A moment typed as `WithDim (forceDim * single .length) ℝ` converts from `u1` to `u2` and
back to itself. -/
private lemma moment_withDim_dimScale_round_trip_of
    (hround : ∀ {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
      (d : Dimension B) (x : ℝ), (u2.dimScale u1 d : ℝ) * ((u1.dimScale u2 d : ℝ) * x) = x)
    (u1 u2 : UnitScale ISQDimensionBase)
    (M : WithDim (forceDim * single ISQDimensionBase.length) ℝ) :
    (⟨(u2.dimScale u1 (forceDim * single ISQDimensionBase.length) : ℝ) *
        ((u1.dimScale u2 (forceDim * single ISQDimensionBase.length) : ℝ) * M.val)⟩ :
      WithDim (forceDim * single ISQDimensionBase.length) ℝ) = M := by
  apply WithDim.ext
  exact moment_dimScale_round_trip_of hround u1 u2 M.val


/-- A moment typed as
`WithDim (forceDim * single .length) ℝ` converts from `u1`
to `u2` and back to itself. -/
lemma moment_withDim_dimScale_round_trip
    (u1 u2 : UnitScale ISQDimensionBase)
    (M : WithDim (forceDim * single ISQDimensionBase.length) ℝ) :
    (⟨(u2.dimScale u1 (forceDim * single ISQDimensionBase.length) : ℝ) *
        ((u1.dimScale u2 (forceDim * single ISQDimensionBase.length) : ℝ) * M.val)⟩ :
      WithDim (forceDim * single ISQDimensionBase.length) ℝ) = M :=
  moment_withDim_dimScale_round_trip_of
    Units.QuantityDimensions.dimScale_round_trip u1 u2 M

/-- Converting the lever arms by the length factor and the forces by the force factor converts
the typed moment by the moment factor. -/
private lemma forceMoment2D_dimScale_of
    (hmul : ∀ {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
      (d₁ d₂ : Dimension B),
      (u1.dimScale u2 (d₁ * d₂) : ℝ) = (u1.dimScale u2 d₁ : ℝ) * (u1.dimScale u2 d₂ : ℝ))
    (u1 u2 : UnitScale ISQDimensionBase) {ρ : Type*} [Fintype ρ]
    (x : ρ → WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ))
    (F : ρ → WithDim forceDim (Fin 2 → ℝ)) :
    forceMoment2D
        (fun i => (⟨(u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) • (x i).val⟩ :
          WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ)))
        (fun i => (⟨(u1.dimScale u2 forceDim : ℝ) • (F i).val⟩ :
          WithDim forceDim (Fin 2 → ℝ))) =
      ⟨(u1.dimScale u2 (forceDim * single ISQDimensionBase.length) : ℝ) *
        (forceMoment2D x F).val⟩ := by
  apply WithDim.ext
  simp only [forceMoment2D_val]
  unfold moment2D
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply]
  rw [hmul u1 u2 _ _]
  ring


/-- Converting the lever arms by the length factor and the
forces by the force factor converts the typed moment by
the moment factor. -/
lemma forceMoment2D_dimScale
    (u1 u2 : UnitScale ISQDimensionBase) {ρ : Type*} [Fintype ρ]
    (x : ρ → WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ))
    (F : ρ → WithDim forceDim (Fin 2 → ℝ)) :
    forceMoment2D
        (fun i => (⟨(u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) • (x i).val⟩ :
          WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ)))
        (fun i => (⟨(u1.dimScale u2 forceDim : ℝ) • (F i).val⟩ :
          WithDim forceDim (Fin 2 → ℝ))) =
      ⟨(u1.dimScale u2 (forceDim * single ISQDimensionBase.length) : ℝ) *
        (forceMoment2D x F).val⟩ :=
  forceMoment2D_dimScale_of Units.QuantityDimensions.dimScale_mul
    u1 u2 x F

/-- The planar balance does not depend on the unit choice: converted forces and lever arms
balance exactly when the original ones do. -/
private lemma planarLoad_balance_dimScale_iff_of
    (hpos : ∀ {B : Type} [DimensionBasis B] [Fintype B] (u1 u2 : UnitScale B)
      (d : Dimension B), 0 < u1.dimScale u2 d)
    (u1 u2 : UnitScale ISQDimensionBase) {ρ : Type*} [Fintype ρ]
    (x : ρ → WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ))
    (F : ρ → WithDim forceDim (Fin 2 → ℝ)) :
    (∑ i, (⟨(u1.dimScale u2 forceDim : ℝ) • (F i).val⟩ : WithDim forceDim (Fin 2 → ℝ)) = 0 ∧
      forceMoment2D
          (fun i => (⟨(u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) • (x i).val⟩ :
            WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ)))
          (fun i => (⟨(u1.dimScale u2 forceDim : ℝ) • (F i).val⟩ :
            WithDim forceDim (Fin 2 → ℝ))) = 0) ↔
      (∑ i, F i = 0 ∧ forceMoment2D x F = 0) := by
  have hne : ∀ d : Dimension ISQDimensionBase,
      ((u1.dimScale u2 d : NNReal) : ℝ) ≠ 0 := fun d => by
    have h := ne_of_gt (hpos u1 u2 d)
    exact_mod_cast h
  have hcancel : ∀ S : Fin 2 → ℝ,
      ((u1.dimScale u2 forceDim : ℝ) • S = 0) ↔ (S = 0) := fun S => by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      simp only [Pi.smul_apply, Pi.zero_apply] at hi
      exact (mul_eq_zero.mp hi).resolve_left (hne forceDim)
    · intro h
      rw [h, smul_zero]
  have hsum : (∑ i, (u1.dimScale u2 forceDim : ℝ) • (F i).val) =
      (u1.dimScale u2 forceDim : ℝ) • (∑ i, (F i).val) :=
    (map_sum (⟨⟨fun S : Fin 2 → ℝ => (u1.dimScale u2 forceDim : ℝ) • S,
      smul_zero _⟩, fun _ _ => smul_add _ _ _⟩ :
      (Fin 2 → ℝ) →+ (Fin 2 → ℝ)) _ _).symm
  have hforce : (∑ i, (⟨(u1.dimScale u2 forceDim : ℝ) • (F i).val⟩ :
      WithDim forceDim (Fin 2 → ℝ)) = 0) ↔ (∑ i, F i = 0) := by
    rw [sum_force_eq_zero_iff, sum_force_eq_zero_iff]
    change (IsEquilibrated (fun r => (u1.dimScale u2 forceDim : ℝ) • (F r).val) ↔
      IsEquilibrated (fun r => (F r).val))
    unfold IsEquilibrated resultantForce
    rw [hsum]
    exact hcancel _
  have hmoment : (forceMoment2D
        (fun i => (⟨(u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) • (x i).val⟩ :
          WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ)))
        (fun i => (⟨(u1.dimScale u2 forceDim : ℝ) • (F i).val⟩ :
          WithDim forceDim (Fin 2 → ℝ))) = 0) ↔ (forceMoment2D x F = 0) := by
    rw [forceMoment2D_eq_zero_iff, forceMoment2D_eq_zero_iff]
    change (moment2D (fun i => (u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) • (x i).val)
        (fun i => (u1.dimScale u2 forceDim : ℝ) • (F i).val) = 0 ↔
      moment2D (fun i => (x i).val) (fun i => (F i).val) = 0)
    have hmsum : moment2D
          (fun i => (u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) • (x i).val)
          (fun i => (u1.dimScale u2 forceDim : ℝ) • (F i).val) =
        ((u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) *
          (u1.dimScale u2 forceDim : ℝ)) *
          moment2D (fun i => (x i).val) (fun i => (F i).val) := by
      unfold moment2D
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply]
      ring
    rw [hmsum]
    constructor
    · intro h
      exact (mul_eq_zero.mp h).resolve_left
        (mul_ne_zero (hne _) (hne _))
    · intro h
      rw [h, mul_zero]
  exact and_congr hforce hmoment


/-- The planar balance does not depend on the unit choice:
converted forces and lever arms balance exactly when the
original ones do. -/
lemma planarLoad_balance_dimScale_iff
    (u1 u2 : UnitScale ISQDimensionBase) {ρ : Type*} [Fintype ρ]
    (x : ρ → WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ))
    (F : ρ → WithDim forceDim (Fin 2 → ℝ)) :
    (∑ i, (⟨(u1.dimScale u2 forceDim : ℝ) • (F i).val⟩ : WithDim forceDim (Fin 2 → ℝ)) = 0 ∧
      forceMoment2D
          (fun i => (⟨(u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) • (x i).val⟩ :
            WithDim (single ISQDimensionBase.length) (Fin 2 → ℝ)))
          (fun i => (⟨(u1.dimScale u2 forceDim : ℝ) • (F i).val⟩ :
            WithDim forceDim (Fin 2 → ℝ))) = 0) ↔
      (∑ i, F i = 0 ∧ forceMoment2D x F = 0) :=
  planarLoad_balance_dimScale_iff_of Units.QuantityDimensions.dimScale_pos
    u1 u2 x F

/-! ## E. Pressure on a positive area -/

/-- The outward-normal force component `F = -p A` of a
uniform pressure `p` on a plane area `A > 0`: the negated
`WithDim` product, cast to `forceDim` by
`stressDim_mul_area`. The sign is the tension-positive
convention of `PhyslibExt.Units.EngineeringFrames`:
pressure is the negative of tension-positive normal
stress, so a positive pressure pushes against the
outward unit normal. -/
def pressureForce (p : WithDim stressDim ℝ)
    (A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ) (_hA : 0 < A.val) :
    WithDim forceDim ℝ :=
  WithDim.cast (-(p * A)) stressDim_mul_area

/-- The coordinate of the pressure force is `-p A` on
the input coordinates. -/
lemma pressureForce_val (p : WithDim stressDim ℝ)
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hA : 0 < A.val) :
    (pressureForce p A hA).val = -(p.val * A.val) := by
  change (-(p * A)).val = -(p.val * A.val)
  rw [WithDim.val_neg, WithDim.withDim_hMul_val]

/-- On a positive area, the tension-positive normal
stress of the pressure force is `-p`: pressure is the
negative of normal stress. -/
lemma normalStress_pressureForce (p : WithDim stressDim ℝ)
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hA : 0 < A.val) :
    normalStress (pressureForce p A hA) A hA = -p := by
  apply WithDim.ext
  change (pressureForce p A hA).val / A.val = (-p).val
  rw [pressureForce_val, WithDim.val_neg, neg_div,
    mul_div_cancel_right₀ p.val (ne_of_gt hA)]

/-- Feeding a tension-positive normal stress into the
pressure slot negates the force: the conversion records
pressure `= -(normal stress)`, so `pressureForce` is
not an inverse of `normalStress`. -/
lemma pressureForce_normalStress (F : WithDim forceDim ℝ)
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hA : 0 < A.val) :
    pressureForce (normalStress F A hA) A hA = -F := by
  apply WithDim.ext
  change -((normalStress F A hA).val * A.val) = (-F).val
  have h1 : (normalStress F A hA).val = F.val / A.val := rfl
  rw [h1, WithDim.val_neg, div_mul_cancel₀ F.val (ne_of_gt hA)]

end Units.EngineeringLoads
