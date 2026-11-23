/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall.AnnulusDeformation
public import MathlibExt.AlgebraicTopology.PlusConstruction.SquarePerimeterWinding

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Winding in the original square-cell annulus

The actual lifted closed-ball annulus has its original radius-five-eighths
bottom-left basepoint. Mapping the same original square perimeter through
the constructed radius section gives its based generator. The existing
annulus homotopy equivalence induces an equivalence of the original End
groups, whose forward map is the original normalized-direction map. The
square winding equivalence then gives winding one and integer-power
generation by that same annular perimeter, at every carrier universe.

An explicit connector to each original annular point follows a prefix of
the original perimeter at radius five-eighths and then the actual radial
segment to the point. No connectedness of an indexed family is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped unitInterval

universe u

namespace Topology.CWComplex

/-- The actual component annulus in the original lifted classical two-cell. -/
abbrev classicalCellSquareAnnulus : Type u :=
  TopPair.closedUnitBallAnnulus.{u} (Fin 2 → ℝ)

/-- The original normalized direction of the constructed annulus homotopy equivalence. -/
def classicalCellSquareAnnulusDirection :
    C(classicalCellSquareAnnulus.{u}, classicalCellSquareBoundary.{u}) :=
  (TopPair.closedUnitBallAnnulusHomotopyEquiv.{u} (Fin 2 → ℝ)).toFun

/-- Its actual inverse map is the original boundary section at radius five-eighths. -/
def classicalCellSquareAnnulusSection :
    C(classicalCellSquareBoundary.{u}, classicalCellSquareAnnulus.{u}) :=
  (TopPair.closedUnitBallAnnulusHomotopyEquiv.{u} (Fin 2 → ℝ)).invFun

/-- The normalized direction retains the same original lifted vector divided by its norm. -/
theorem classicalCellSquareAnnulusDirection_val (z : classicalCellSquareAnnulus.{u}) :
    (classicalCellSquareAnnulusDirection.{u} z).down.val =
      ‖z.1.down.val‖⁻¹ • z.1.down.val := by
  exact TopPair.closedUnitBallAnnulusSphereProd_direction z

/-- The actual section scales the same original boundary vector by five-eighths. -/
theorem classicalCellSquareAnnulusSection_val (b : classicalCellSquareBoundary.{u}) :
    (classicalCellSquareAnnulusSection.{u} b).1.down.val =
      ((5 : ℝ) / 8) • b.down.val := by
  exact TopPair.closedUnitBallAnnulusSphereProd_symm_val (b, TopPair.cellAnnulusMidRadius)

/-- Every original boundary point is recovered by the actual direction after the section. -/
theorem classicalCellSquareAnnulusDirection_section (b : classicalCellSquareBoundary.{u}) :
    classicalCellSquareAnnulusDirection.{u} (classicalCellSquareAnnulusSection.{u} b) = b := by
  exact TopPair.AnnulusCoordinates.direction_section classicalCellSquareBoundary.{u}
    (TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin 2 → ℝ)) b

/-- The section has its stated original disk norm, independent of the carrier lift. -/
theorem classicalCellSquareAnnulusSection_norm (b : classicalCellSquareBoundary.{u}) :
    ‖(classicalCellSquareAnnulusSection.{u} b).1.down.val‖ = (5 : ℝ) / 8 := by
  rw [classicalCellSquareAnnulusSection_val, norm_smul,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8), classicalCellSquare_norm, mul_one]

/-- The actual annular basepoint lies on the original bottom-left radius at five-eighths. -/
def classicalCellSquareAnnulusBasepoint : classicalCellSquareAnnulus.{u} :=
  classicalCellSquareAnnulusSection.{u} classicalCellSquareBottomLeft.{u}

/-- Its underlying original vector is the scaled original bottom-left corner. -/
theorem classicalCellSquareAnnulusBasepoint_val :
    classicalCellSquareAnnulusBasepoint.{u}.1.down.val =
      ((5 : ℝ) / 8) • classicalCellSquareBottomLeft.{u}.down.val :=
  classicalCellSquareAnnulusSection_val classicalCellSquareBottomLeft.{u}

/-- The actual basepoint has original disk radius five-eighths. -/
theorem classicalCellSquareAnnulusBasepoint_norm :
    ‖classicalCellSquareAnnulusBasepoint.{u}.1.down.val‖ = (5 : ℝ) / 8 :=
  classicalCellSquareAnnulusSection_norm classicalCellSquareBottomLeft.{u}

/-- The original annular basepoint maps to the original chosen square corner. -/
theorem classicalCellSquareAnnulusDirection_basepoint :
    classicalCellSquareAnnulusDirection.{u} classicalCellSquareAnnulusBasepoint.{u} =
      classicalCellSquareBottomLeft.{u} :=
  classicalCellSquareAnnulusDirection_section classicalCellSquareBottomLeft.{u}

/-- The same original four-edge perimeter, mapped through the actual five-eighths section. -/
def classicalCellSquareAnnulusPerimeter :
    Path classicalCellSquareAnnulusBasepoint.{u} classicalCellSquareAnnulusBasepoint.{u} :=
  classicalCellSquarePerimeter.{u}.map classicalCellSquareAnnulusSection.{u}.continuous

/-- The original perimeter vector is retained at the fixed annular radius at every time. -/
theorem classicalCellSquareAnnulusPerimeter_val (t : I) :
    (classicalCellSquareAnnulusPerimeter.{u} t).1.down.val =
      ((5 : ℝ) / 8) • (classicalCellSquarePerimeter.{u} t).down.val :=
  classicalCellSquareAnnulusSection_val (classicalCellSquarePerimeter.{u} t)

/-- The original direction carries the same annular perimeter to the original square perimeter. -/
theorem classicalCellSquareAnnulusPerimeter_map_direction :
    (classicalCellSquareAnnulusPerimeter.{u}.map
        classicalCellSquareAnnulusDirection.{u}.continuous).cast
        classicalCellSquareAnnulusDirection_basepoint.{u}.symm
        classicalCellSquareAnnulusDirection_basepoint.{u}.symm =
      classicalCellSquarePerimeter.{u} := by
  apply Path.ext
  funext t
  change classicalCellSquareAnnulusDirection.{u}
      (classicalCellSquareAnnulusSection.{u} (classicalCellSquarePerimeter.{u} t)) =
    classicalCellSquarePerimeter.{u} t
  exact classicalCellSquareAnnulusDirection_section (classicalCellSquarePerimeter.{u} t)

/-- The original annular perimeter class in its original based End group. -/
def classicalCellSquareAnnulusPerimeterClass :
    FundamentalGroup classicalCellSquareAnnulus.{u} classicalCellSquareAnnulusBasepoint.{u} :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk classicalCellSquareAnnulusPerimeter.{u})

/-- The actual based direction map carries the original annular perimeter class to the square
class. -/
theorem classicalCellSquareAnnulusPerimeterClass_map_direction :
    FundamentalGroup.mapOfEq classicalCellSquareAnnulusDirection.{u}
        classicalCellSquareAnnulusDirection_basepoint.{u}
        classicalCellSquareAnnulusPerimeterClass.{u} = classicalCellSquarePerimeterClass.{u} := by
  rw [FundamentalGroup.mapOfEq_apply]
  change FundamentalGroup.fromPath
      ((Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk classicalCellSquareAnnulusPerimeter.{u})
        classicalCellSquareAnnulusDirection.{u}).cast
          classicalCellSquareAnnulusDirection_basepoint.{u}.symm
          classicalCellSquareAnnulusDirection_basepoint.{u}.symm) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk classicalCellSquarePerimeter.{u})
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
    classicalCellSquareAnnulusPerimeter_map_direction]

/-- The constructed annulus homotopy equivalence induces the original based End equivalence. -/
def classicalCellSquareAnnulusFundamentalGroupEquiv :
    FundamentalGroup classicalCellSquareAnnulus.{u} classicalCellSquareAnnulusBasepoint.{u} ≃*
      FundamentalGroup classicalCellSquareBoundary.{u} classicalCellSquareBottomLeft.{u} := by
  let F := FundamentalGroupoid.map classicalCellSquareAnnulusDirection.{u}
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (TopPair.closedUnitBallAnnulusHomotopyEquiv.{u} (Fin 2 → ℝ))
  let _ : F.IsEquivalence := by exact E.isEquivalence_functor
  let changeBase : End (F.obj (FundamentalGroupoid.mk classicalCellSquareAnnulusBasepoint.{u})) ≃*
      End (FundamentalGroupoid.mk classicalCellSquareBottomLeft.{u}) :=
    (eqToIso (congrArg FundamentalGroupoid.mk
      classicalCellSquareAnnulusDirection_basepoint.{u})).conj
  exact ((Functor.FullyFaithful.ofFullyFaithful F).mulEquivEnd
    (FundamentalGroupoid.mk classicalCellSquareAnnulusBasepoint.{u})).trans changeBase

/-- Its forward map is the original equality-pointed normalized-direction homomorphism. -/
@[simp]
theorem classicalCellSquareAnnulusFundamentalGroupEquiv_apply
    (q : FundamentalGroup classicalCellSquareAnnulus.{u} classicalCellSquareAnnulusBasepoint.{u}) :
    classicalCellSquareAnnulusFundamentalGroupEquiv.{u} q =
      FundamentalGroup.mapOfEq classicalCellSquareAnnulusDirection.{u}
        classicalCellSquareAnnulusDirection_basepoint.{u} q :=
  rfl

/-- The winding equivalence of the original component End group at its actual annular basepoint. -/
def classicalCellSquareAnnulusWindingIso :
    FundamentalGroup classicalCellSquareAnnulus.{u} classicalCellSquareAnnulusBasepoint.{u} ≃*
      Multiplicative ℤ :=
  classicalCellSquareAnnulusFundamentalGroupEquiv.{u}.trans classicalCellSquareWindingIso.{u}

/-- This same original section-perimeter class has winding positive one. -/
theorem classicalCellSquareAnnulusWindingIso_perimeter :
    classicalCellSquareAnnulusWindingIso.{u} classicalCellSquareAnnulusPerimeterClass.{u} =
      Multiplicative.ofAdd (1 : ℤ) := by
  change classicalCellSquareWindingIso.{u}
      (classicalCellSquareAnnulusFundamentalGroupEquiv.{u}
        classicalCellSquareAnnulusPerimeterClass.{u}) = Multiplicative.ofAdd (1 : ℤ)
  rw [classicalCellSquareAnnulusFundamentalGroupEquiv_apply,
    classicalCellSquareAnnulusPerimeterClass_map_direction, classicalCellSquareWindingIso_perimeter]

/-- Every original based component class is an integer power of that same annular perimeter. -/
theorem classicalCellSquareAnnulus_exists_perimeter_zpow
    (q : FundamentalGroup classicalCellSquareAnnulus.{u} classicalCellSquareAnnulusBasepoint.{u}) :
    ∃ n : ℤ, q = classicalCellSquareAnnulusPerimeterClass.{u} ^ n := by
  refine ⟨(classicalCellSquareAnnulusWindingIso.{u} q).toAdd, ?_⟩
  apply classicalCellSquareAnnulusWindingIso.{u}.injective
  rw [map_zpow, classicalCellSquareAnnulusWindingIso_perimeter]
  exact (Multiplicative.toAdd : Multiplicative ℤ ≃ ℤ).injective (by
    simp only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, mul_one, Int.cast_id])

/-- The actual prefix of the original perimeter from its basepoint to a selected boundary point. -/
def classicalCellSquareBoundaryPrefix (b : classicalCellSquareBoundary.{u}) :
    Path classicalCellSquareBottomLeft.{u} b :=
  (classicalCellSquarePerimeter.{u}.truncateOfLE
      (t₀ := 0) (t₁ := (classicalCellSquarePerimeterParameter b : ℝ))
      (unitInterval.nonneg (classicalCellSquarePerimeterParameter b))).cast
    classicalCellSquarePerimeter.{u}.extend_zero.symm
    ((classicalCellSquarePerimeter.{u}.extend_apply
      (classicalCellSquarePerimeterParameter b).2).trans
        (classicalCellSquarePerimeter_parameter b)).symm

/-- The prefix starts at the original square corner. -/
theorem classicalCellSquareBoundaryPrefix_source (b : classicalCellSquareBoundary.{u}) :
    classicalCellSquareBoundaryPrefix b (0 : I) = classicalCellSquareBottomLeft.{u} :=
  (classicalCellSquareBoundaryPrefix b).source

/-- The actual selected perimeter parameter gives the original selected boundary endpoint. -/
theorem classicalCellSquareBoundaryPrefix_target (b : classicalCellSquareBoundary.{u}) :
    classicalCellSquareBoundaryPrefix b (1 : I) = b :=
  (classicalCellSquareBoundaryPrefix b).target

/-- The reverse of the actual radius deformation joins the section to the original annular point. -/
def classicalCellSquareAnnulusRadialPath (z : classicalCellSquareAnnulus.{u}) :
    Path (classicalCellSquareAnnulusSection.{u} (classicalCellSquareAnnulusDirection.{u} z)) z :=
  ((TopPair.AnnulusCoordinates.deformation classicalCellSquareBoundary.{u}
    (TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin 2 → ℝ))).toHomotopy.evalAt z).symm

/-- Its actual normalized original direction is fixed at every time. -/
theorem classicalCellSquareAnnulusRadialPath_direction (z : classicalCellSquareAnnulus.{u})
    (t : I) :
    classicalCellSquareAnnulusDirection.{u} (classicalCellSquareAnnulusRadialPath z t) =
      classicalCellSquareAnnulusDirection.{u} z := by
  exact TopPair.AnnulusCoordinates.deformation_direction classicalCellSquareBoundary.{u}
    (TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin 2 → ℝ)) (unitInterval.symm t) z

/-- Its original disk radius interpolates from five-eighths to the same original point radius. -/
theorem classicalCellSquareAnnulusRadialPath_norm (z : classicalCellSquareAnnulus.{u}) (t : I) :
    ‖(classicalCellSquareAnnulusRadialPath z t).1.down.val‖ =
      (1 - (t : ℝ)) * ((5 : ℝ) / 8) + (t : ℝ) * ‖z.1.down.val‖ := by
  have h := TopPair.AnnulusCoordinates.deformation_radius classicalCellSquareBoundary.{u}
    (TopPair.closedUnitBallAnnulusSphereProd.{u} (Fin 2 → ℝ)) (unitInterval.symm t) z
  calc
    _ = (1 - ((unitInterval.symm t) : ℝ)) * ‖z.1.down.val‖ +
        ((unitInterval.symm t) : ℝ) * (TopPair.cellAnnulusMidRadius : ℝ) := h
    _ = (1 - (t : ℝ)) * ((5 : ℝ) / 8) + (t : ℝ) * ‖z.1.down.val‖ := by
      rw [unitInterval.coe_symm_eq]
      change (1 - (1 - (t : ℝ))) * ‖z.1.down.val‖ +
        (1 - (t : ℝ)) * ((5 : ℝ) / 8) = _
      ring

/-- An actual connector follows the section-perimeter prefix and then the original radial
segment. -/
def classicalCellSquareAnnulusConnector (z : classicalCellSquareAnnulus.{u}) :
    Path classicalCellSquareAnnulusBasepoint.{u} z :=
  ((classicalCellSquareBoundaryPrefix (classicalCellSquareAnnulusDirection.{u} z)).map
    classicalCellSquareAnnulusSection.{u}.continuous).trans (classicalCellSquareAnnulusRadialPath z)

/-- The connector retains the same original annular basepoint. -/
theorem classicalCellSquareAnnulusConnector_source (z : classicalCellSquareAnnulus.{u}) :
    classicalCellSquareAnnulusConnector z (0 : I) = classicalCellSquareAnnulusBasepoint.{u} :=
  (classicalCellSquareAnnulusConnector z).source

/-- It reaches every actual original annular point without a supplied connecting-path premise. -/
theorem classicalCellSquareAnnulusConnector_target (z : classicalCellSquareAnnulus.{u}) :
    classicalCellSquareAnnulusConnector z (1 : I) = z :=
  (classicalCellSquareAnnulusConnector z).target

end Topology.CWComplex
