/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# General coefficient fields for relative p-adic comparison

The coefficient field is a complete ultrametric extension of `Q_p`.
Its actual norm-unit subring is required to be a discrete valuation ring,
and its actual residue field has characteristic `p` and is perfect.
These are the field hypotheses of Scholze, arXiv:1205.3463v2,
Definition 6.8 and Theorem 8.8.

The norm-unit subring argument is adapted from this repository's
`MathlibExt/AlgebraicGeometry/FormalGenericFibreModels.lean`, commit
`8b07dc902f707a43fa2d01f11e7a196910cfa9a3`. The field scope here is the
general discrete coefficient field used in relative de Rham comparison.
The algebraically closed perfectoid extension used for geometric local
calculations remains separate source data.

Native algebraic and topological definitions are from Mathlib, Apache 2.0,
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralPadicCoefficientFields

variable (p : ℕ) [Fact p.Prime]

/-- A complete nonarchimedean coefficient field with its actual `Q_p` scalars. -/
structure CoefficientField where
  carrier : Type
  [normedField : NormedField carrier]
  [ultrametric : IsUltrametricDist carrier]
  [complete : CompleteSpace carrier]
  [algebra : Algebra ℚ_[p] carrier]
  [normedAlgebra : NormedAlgebra ℚ_[p] carrier]

attribute [instance] CoefficientField.normedField CoefficientField.ultrametric
  CoefficientField.complete CoefficientField.algebra CoefficientField.normedAlgebra

/-- The actual ring of integers, defined by the original field norm. -/
def integers (K : CoefficientField p) : Subring K.carrier where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ‖a + b‖ ≤ 1
    have h : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
      simpa [dist_eq_norm, sub_eq_add_neg] using dist_triangle_max a (0 : K.carrier) (-b)
    exact h.trans (max_le ha hb)
  mul_mem' := by
    intro a b ha hb
    change ‖a * b‖ ≤ 1
    rw [norm_mul]
    simpa using mul_le_mul ha hb (norm_nonneg _) (show (0 : ℝ) ≤ 1 from zero_le_one)
  neg_mem' ha := by simpa using ha

/-- The general complete discrete base of Definition 6.8, with its actual residue field. -/
structure BaseField where
  field : CoefficientField p
  [discrete : IsDiscreteValuationRing (integers p field)]
  [residueCharacteristic : CharP (IsLocalRing.ResidueField (integers p field)) p]
  [perfectResidue : PerfectField (IsLocalRing.ResidueField (integers p field))]

attribute [instance] BaseField.discrete BaseField.residueCharacteristic BaseField.perfectResidue

namespace BaseField

abbrev carrier (K : BaseField p) := K.field.carrier
abbrev integralRing (K : BaseField p) := integers p K.field
abbrev residueField (K : BaseField p) := IsLocalRing.ResidueField (integralRing p K)

instance (K : BaseField p) : NormedField (carrier p K) := K.field.normedField
instance (K : BaseField p) : IsUltrametricDist (carrier p K) := K.field.ultrametric
instance (K : BaseField p) : CompleteSpace (carrier p K) := K.field.complete
instance (K : BaseField p) : Algebra ℚ_[p] (carrier p K) := K.field.algebra
instance (K : BaseField p) : NormedAlgebra ℚ_[p] (carrier p K) := K.field.normedAlgebra

/-- The native quotient map to the actual residue field. -/
def reduction (K : BaseField p) : integralRing p K →+* residueField p K :=
  IsLocalRing.residue (integralRing p K)

/-- The fixed embedding of the original `Q_p` coefficient field. -/
def rationalScalars (K : BaseField p) : ℚ_[p] →+* carrier p K :=
  algebraMap ℚ_[p] (carrier p K)

end BaseField

end MathlibExt.AlgebraicGeometry.GeneralPadicCoefficientFields
