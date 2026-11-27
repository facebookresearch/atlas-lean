/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TemperedDistributionSectionModels
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The actual coordinate tempered Dolbeault differential

Terms are the original Db^t coefficient spaces indexed by increasing
conjugate coordinate wedges. The differential inserts partial-zbar with
the actual exterior-position sign. Square-zero is a structural proof
request about these already fixed operators. The same local model glues
through the source subanalytic/coordinate construction of O^t.

Source: DK arXiv:1311.2374v2, Definition 5.2.1 and the preceding
Dolbeault realization. Native LF and complex APIs: Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TemperedDolbeaultCoordinateModels

open _root_.CategoryTheory TopologicalSpace
open TemperedDistributionSectionModels

variable (n : ℕ) (S : DerivativeRestrictionSource (ComplexCoordinates n))
  (U : Opens (ComplexCoordinates n))

abbrev WedgeIndex (p : ℤ) := {I : Finset (Fin n) // (I.card : ℤ) = p}

abbrev FormCoefficients (p : ℤ) := WedgeIndex n p → TemperedSections (ComplexCoordinates n) U

def eraseWedge (p : ℤ) (J : WedgeIndex n (p + 1)) (j : J.val) : WedgeIndex n p :=
  ⟨J.val.erase j.val, by
    have h := Finset.card_erase_add_one j.property
    have hJ := J.property
    omega⟩

def wedgeSign (J : Finset (Fin n)) (j : Fin n) : ℂ :=
  (-1 : ℂ) ^ (J.filter (fun i => i < j)).card

/-- Native partial-zbar followed by the original wedge insertion sign. -/
def dolbeaultDifferential (p : ℤ) : FormCoefficients n U p →ₗ[ℂ] FormCoefficients n U (p + 1) where
  toFun ω J := ∑ j : J.val,
    wedgeSign n J.val j.val • partialZBar n S U j.val (ω (eraseWedge n p J j))
  map_add' ω η := by
    funext J
    simp [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' a ω := by
    funext J
    simp [map_smul, smul_smul, mul_comm, Finset.smul_sum]

/-- Only square-zero of the actual original differential is supplied. -/
structure DolbeaultSquareZeroSource : Prop where
  squareZero : ∀ p : ℤ,
    ModuleCat.ofHom (dolbeaultDifferential n S U p) ≫
      ModuleCat.ofHom (dolbeaultDifferential n S U (p + 1)) = 0

/-- The actual signed finite-coordinate cochain model. -/
def dolbeaultComplex (D : DolbeaultSquareZeroSource n S U) : CochainComplex (ModuleCat.{0} ℂ) ℤ :=
  CochainComplex.of (fun p => ModuleCat.of ℂ (FormCoefficients n U p))
    (fun p => ModuleCat.ofHom (dolbeaultDifferential n S U p)) D.squareZero

end MathlibExt.AlgebraicGeometry.TemperedDolbeaultCoordinateModels
