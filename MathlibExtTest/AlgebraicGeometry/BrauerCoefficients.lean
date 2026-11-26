/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BrauerCoefficients
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.NormNum

/-!
# Separable-closure unit coefficients and native Brauer classes

The coefficient object is discrete, its action is a genuine continuous action
by `K`-automorphisms (base units are fixed and stabilizers are open), and the
inhomogeneous coordinates are additive with the `(1,g,g*h)` normalization.
The locally compact hypothesis of `locallyConstantValues` is satisfiable over
`ℚ`. The invariant maps are probed at degrees `0`, `1` and `3`.
-/

noncomputable section

namespace MathlibExtTest.BrauerCoefficients

/-! ## The discrete coefficient topology is scoped -/

section Unscoped

variable (K : Type) [Field K] [TopologicalSpace (SeparableClosure K)]

-- Without opening `AlgebraicGeometry.BrauerCoefficients`, the bare additive units keep Mathlib's
-- topology, the units topology, rather than the discrete coefficient topology.
example : (inferInstance : TopologicalSpace (Additive (SeparableClosure K)ˣ)) =
    (inferInstance : TopologicalSpace (SeparableClosure K)ˣ) := rfl

end Unscoped

open AlgebraicGeometry.BrauerCoefficients

variable (K : Type) [Field K]

/-! ## Coefficients and action -/

example : (inferInstance : TopologicalSpace (SepUnits K)) = ⊥ := rfl
example : DiscreteTopology (SepUnits K) := inferInstance
example : DiscreteTopology (unitsRep K).V := inferInstance
example : ContinuousSMul (Field.absoluteGaloisGroup K) (unitsRep K).V := inferInstance
example : DistribMulAction (Field.absoluteGaloisGroup K) (SepUnits K) := inferInstance

example (g : Field.absoluteGaloisGroup K) (u : (SeparableClosure K)ˣ) :
    Additive.toMul (unitAction K g (Additive.ofMul u)) =
      Units.map g.separableClosure.toMonoidHom u := by
  simp

example (g : Field.absoluteGaloisGroup K) (u : SepUnits K) :
    (unitsRep K).ρ g u = unitAction K g u := rfl

example (g : Field.absoluteGaloisGroup K) (u : SepUnits K) : g • u = unitAction K g u := rfl

example (u : SepUnits K) : unitsEquiv K u = u := rfl

example (u : SepUnits K) : unitAction K 1 u = u := by
  rw [← unitsRep_action, map_one]
  rfl

example (g h : Field.absoluteGaloisGroup K) (u : SepUnits K) :
    unitAction K (g * h) u = unitAction K g (unitAction K h u) := by
  simp only [← unitsRep_action, map_mul]
  rfl

/-- Base-field units are fixed: the action is by `K`-automorphisms. -/
example (g : Field.absoluteGaloisGroup K) (a : Kˣ) :
    unitAction K g (Additive.ofMul (Units.map (algebraMap K (SeparableClosure K)) a)) =
      Additive.ofMul (Units.map (algebraMap K (SeparableClosure K)) a) := by
  apply Additive.toMul.injective
  rw [unitAction_apply]
  apply Units.ext
  exact g.separableClosure.commutes (a : K)

/-- Stabilizers of the discrete coefficients are open. -/
example (u : (unitsRep K).V) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup K) u :
      Set (Field.absoluteGaloisGroup K)) :=
  continuousSMul_iff_stabilizer_isOpen.mp inferInstance u

/-! ## Cocycles and classes -/

example : cocycleClass K 0 = 0 := by simp

example (c d : TwoCocycles K) : cocycleClass K (c + d) = cocycleClass K c + cocycleClass K d :=
  map_add _ c d

example (g h : Field.absoluteGaloisGroup K) : inhomogeneousValue K 0 g h = 0 := by simp

/-- The inhomogeneous coordinates use `(1,g,g*h)`. -/
example (c : TwoCocycles K) (g h : Field.absoluteGaloisGroup K) :
    inhomogeneousValue K c g h =
      ((TopRep.homogeneousCochains (unitsRep K)).iCycles 2 c).val 1 g (g * h) := rfl

example (c d : TwoCocycles K) (g h : Field.absoluteGaloisGroup K) :
    inhomogeneousValue K (c + d) g h = inhomogeneousValue K c g h + inhomogeneousValue K d g h := by
  simp only [inhomogeneousValue, inhomogeneousTwoCocycleValue, map_add]
  rfl

example [LocallyCompactSpace (Field.absoluteGaloisGroup K)] (c : TwoCocycles K)
    (g h : Field.absoluteGaloisGroup K) :
    locallyConstantValues K c (g, h) = inhomogeneousValue K c g h := by
  simp

/-- The locally compact hypothesis holds for the perfect field `ℚ`. -/
instance : LocallyCompactSpace (Field.absoluteGaloisGroup ℚ) :=
  inferInstanceAs (LocallyCompactSpace Gal(AlgebraicClosure ℚ/ℚ))

example (c : TwoCocycles ℚ) (g h : Field.absoluteGaloisGroup ℚ) :
    locallyConstantValues ℚ c (g, h) = inhomogeneousValue ℚ c g h := by
  simp

/-! ## Invariant maps -/

example (q : InvariantTarget) : invariantRestriction 0 q = 0 := by simp

example (q : InvariantTarget) : invariantRestriction 1 q = q := by simp

example (q : InvariantTarget) : invariantCorestriction q = q := by simp

example (n : ℕ) (q : InvariantTarget) :
    invariantCorestriction (invariantRestriction n q) = n • q := by
  simp

example : invariantRestriction 3 ((1 / 3 : ℚ) : InvariantTarget) = 0 := by
  rw [invariantRestriction_apply, ← AddCircle.coe_nsmul]
  exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨1, by norm_num⟩

example : invariantRestriction 3 ((1 / 4 : ℚ) : InvariantTarget) =
    ((3 / 4 : ℚ) : InvariantTarget) := by
  rw [invariantRestriction_apply, ← AddCircle.coe_nsmul]
  congr 1
  norm_num

/-- Degree three does not annihilate `1/4`. -/
example : ((3 / 4 : ℚ) : InvariantTarget) ≠ 0 := by
  intro h
  rw [← AddCircle.coe_zero] at h
  have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (by norm_num : (3 / 4 : ℚ) ∈ Set.Ico 0 (0 + 1))
    (by norm_num : (0 : ℚ) ∈ Set.Ico 0 (0 + 1))).mp h
  norm_num at heq

end MathlibExtTest.BrauerCoefficients
