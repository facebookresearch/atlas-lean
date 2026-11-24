/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticSpaces
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Actual affine formal models and their bounded generic points

The model is an actual adically complete algebra with a completed finite
polynomial presentation. Its generic Banach algebra is the actual
localization at the chosen base parameter, with compatible scalar maps.
Its special fibre is the actual quotient ring. A reduction comparison is
normalized by the strict inequality `|a(x)| < 1`, on every model element.

These are signature contracts, including ramified and equal-characteristic
DVR bases. They are not a definition of global formal schemes or a proof of
Raynaud's equivalence. The external formal/adic gluing implementations are
available dependencies, separate from this weak-spectrum model comparison.

References: Berkovich, *Vanishing cycles for formal schemes*, Invent.
Math. 115 (1994), §1, https://doi.org/10.1007/BF01231772;
Bosch, *Lectures on Formal and Rigid Geometry*,
the construction of generic fibres, https://doi.org/10.1007/978-3-319-04417-0.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffinoidFormalModels

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticSpaces

variable (R : Type) [CommRing R] (K : Type) [NormedField K]
  [IsUltrametricDist K] [Algebra R K] (π : R)

/-- The actual base ideal defining the adic completion. -/
def parameterIdeal : Ideal R := Ideal.span {π}

/-- A topologically finitely presented affine formal model: the `π`-adic completion of
`R[X₁, …, Xₙ] / I` for a finitely generated ideal `I`, with its actual complete ring and actual
localized generic affinoid algebra. -/
structure AffinoidFormalModel where
  modelRing : Type
  [commRing : CommRing modelRing]
  [modelAlgebra : Algebra R modelRing]
  [complete : IsAdicComplete (parameterIdeal R π) modelRing]
  finitePresentation : ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)), I.FG ∧
    Nonempty (AdicCompletion ((parameterIdeal R π).map
      (algebraMap R (MvPolynomial (Fin n) R ⧸ I)))
      (MvPolynomial (Fin n) R ⧸ I) ≃ₐ[R] modelRing)
  genericAlgebra : AffinoidAlgebra K
  [genericBaseAlgebra : Algebra R genericAlgebra]
  [genericScalarTower : IsScalarTower R K genericAlgebra]
  [genericModelAlgebra : Algebra modelRing genericAlgebra]
  [modelScalarTower : IsScalarTower R modelRing genericAlgebra]
  [localization : IsLocalization.Away (algebraMap R modelRing π) genericAlgebra]

attribute [instance] AffinoidFormalModel.commRing
  AffinoidFormalModel.modelAlgebra
  AffinoidFormalModel.complete AffinoidFormalModel.genericBaseAlgebra
  AffinoidFormalModel.genericScalarTower AffinoidFormalModel.genericModelAlgebra
  AffinoidFormalModel.modelScalarTower AffinoidFormalModel.localization

namespace AffinoidFormalModel

variable {R K π} (M : AffinoidFormalModel R K π)

/-- The actual ideal of definition in the model ring. -/
def ideal : Ideal M.modelRing :=
  (parameterIdeal R π).map (algebraMap R M.modelRing)

/-- The scheme-theoretic special-fibre ring. -/
abbrev SpecialRing := M.modelRing ⧸ M.ideal

def specialFibre : Scheme := Spec (CommRingCat.of M.SpecialRing)

/-- Bounded generic points are pinned to every actual model element. -/
def GenericPoint :=
  {p : BoundedPoint M.genericAlgebra //
    ∀ a : M.modelRing,
      p.seminorm (algebraMap M.modelRing M.genericAlgebra a) ≤ 1}

instance : TopologicalSpace M.GenericPoint := inferInstanceAs
  (TopologicalSpace {p : BoundedPoint M.genericAlgebra //
    ∀ a : M.modelRing,
      p.seminorm (algebraMap M.modelRing M.genericAlgebra a) ≤ 1})

def genericSpace : TopCat := TopCat.of M.GenericPoint

/-- Reduction to the actual special fibre, with its valuation ideal fixed.
The anticontinuity clause is on the weak Berkovich topology. -/
structure ReductionComparison where
  map : M.GenericPoint → PrimeSpectrum M.SpecialRing
  ideal_normalized : ∀ (p : M.GenericPoint) (a : M.modelRing),
    Ideal.Quotient.mk M.ideal a ∈ (map p).asIdeal ↔
      p.1.seminorm (algebraMap M.modelRing M.genericAlgebra a) < 1
  anticontinuous : ∀ U : Set (PrimeSpectrum M.SpecialRing), IsOpen U →
    IsClosed (map ⁻¹' U)

end AffinoidFormalModel

end MathlibExt.AlgebraicGeometry.AffinoidFormalModels
