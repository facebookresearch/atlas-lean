/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicPowerQuotientModels
public import MathlibExt.AlgebraicGeometry.FiniteBundleCycleRealization

/-!
# Actual cycle descent and diagonal in Construction 5.3

The upper cycle is the literal external n-fold cycle times the original
U identity. Its target map is the already normalized vector quotient.
The descended cycle is fixed by pullback along the original free source
quotient and by its two equal maps to U/G. The diagonal then uses the
native X-to-X^n map, descended along that same U quotient.

The resulting finite cycle lifts to the actual pullback of the associated
bundle. Both source and target module maps are retained as whole scheme
maps. Equality of cycles follows from those same maps; a final power
operation or Thom-class identity is not an input.

Source: Voevodsky, arXiv:math/0107109v1, Construction 5.3. Here the
upper cycle is Z tensor n, and the diagonal is X to X^n, correcting the
two apparent typographical slips in the extracted v1 text.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPowerDescentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels MotivicStandardSchemes
open MotivicFinitePermutationModels MotivicPermutationBundleModels
open MotivicFinitePowerCycles MotivicPowerQuotientModels
open MotivicBundleModels GeneralMotivicBundleFrameMaps

variable {k H : Type} [Field k] [Group H] [Fintype H]
  [C : ConstantGroupGeometry (k := k) (H := H)]
  (P : SmoothProductSystem k) (U : FreeQuotient (k := k) (H := H))
  {n : ℕ} (r : H →* Equiv.Perm (Fin n))
  {X : SmoothScheme k} (Q : PowerQuotient P U r X)

/-- The native diagonal times the original U identity. -/
def upperDiagonal : P.obj X U.total ⟶ powerTotal P U (n := n) X :=
  productMap P (powerDiagonal P X n) (𝟙 U.total)

/-- The source quotient is the original identity-X times U-to-U/G map. -/
def upperBaseQuotient : P.obj X U.total ⟶ P.obj X U.base :=
  productMap P (𝟙 X) U.projection

/-- The actual descended diagonal is normalized on the entire original free cover. -/
structure DiagonalDescent where
  map : P.obj X U.base ⟶ Q.quotient.base
  baseEquation : map ≫ Q.baseMap = (P.geometry X U.base).snd
  normalization : upperDiagonal P U (n := n) ≫ Q.map P U r =
    upperBaseQuotient P U ≫ map
  unique : ∀ f : P.obj X U.base ⟶ Q.quotient.base,
    upperDiagonal P U (n := n) ≫ Q.map P U r = upperBaseQuotient P U ≫ f → f = map

variable (D : CompositionSystem k) (G : GraphSystem k)
  (R : Type 1) [CommRing R] (A : StandardSchemes P) (i : ℕ)
  (V : VectorQuotient P U r A i) (z : CoefficientCycles X (A.affine i) R)

/-- The original coefficient graph of a scheme map. -/
def coefficientGraph {Y Z : SmoothScheme k} (f : Y ⟶ Z) : CoefficientCycles Y Z R :=
  cycleWithCoefficient R (graphCycle G f) 1

/-- The actual upper external power followed by its normalized quotient vector map. -/
def upperQuotientCycle (E : ExternalSystem P) :
    CoefficientCycles (powerTotal P U (n := n) X) V.bundle.smoothTotal R :=
  composeCoefficient D R (externalPowerWithU E G R z n U.total)
    (coefficientGraph G R (V.map P U r))

/-- A support is over the original common U/G precisely as a whole scheme equation. -/
def IsOverGenerator (g : Generator Q.quotient.base V.bundle.smoothTotal) : Prop :=
  g.presentation.inclusion ≫
    pullback.fst Q.quotient.base.scheme.hom V.bundle.smoothTotal.scheme.hom ≫ Q.baseMap.left =
  g.presentation.inclusion ≫
    pullback.snd Q.quotient.base.scheme.hom V.bundle.smoothTotal.scheme.hom ≫ V.bundle.projection.left

/-- The descended finite cycle is the unique cycle whose actual free pullback is the source power. -/
structure CycleDescent (E : ExternalSystem P) where
  value : CoefficientCycles Q.quotient.base V.bundle.smoothTotal R
  relative : ∀ g : Generator Q.quotient.base V.bundle.smoothTotal,
    value g ≠ 0 → IsOverGenerator P U r Q A i V g
  normalization : composeCoefficient D R (coefficientGraph G R (Q.map P U r)) value =
    upperQuotientCycle P U r D G R A i V z E
  unique : ∀ w : CoefficientCycles Q.quotient.base V.bundle.smoothTotal R,
    composeCoefficient D R (coefficientGraph G R (Q.map P U r)) w =
      upperQuotientCycle P U r D G R A i V z E → w = value

/-- The diagonal cycle uses the already fixed quotient diagonal and native graph composition. -/
def diagonalCycle {E : ExternalSystem P} (B : CycleDescent P U r Q D G R A i V z E)
    (d : DiagonalDescent P U r Q) : CoefficientCycles (P.obj X U.base) V.bundle.smoothTotal R :=
  composeCoefficient D R (coefficientGraph G R d.map) B.value

/-- The pullback bundle is on the literal original X times U/G base. -/
structure PullbackPowerBundle where
  bundle : BundleGeometry (P.obj X U.base)
    ((Scheme.Modules.pullback (P.geometry X U.base).snd.left).obj V.module.module) (n * i)
  cartesian : IsPullback
    (moduleSmoothMap bundle V.bundle (P.geometry X U.base).snd (𝟙 _)).left
    bundle.projection.left V.bundle.projection.left (P.geometry X U.base).snd.left

/-- The vector map is computed by the actual pulled module identity and universal section. -/
def PullbackPowerBundle.map (B : PullbackPowerBundle P U r A i V (X := X)) :
    B.bundle.smoothTotal ⟶ V.bundle.smoothTotal :=
  moduleSmoothMap B.bundle V.bundle (P.geometry X U.base).snd (𝟙 _)

/-- The original relative support generators with actual R coefficients. -/
abbrev RelativePowerCycles (B : PullbackPowerBundle P U r A i V (X := X)) :=
  B.bundle.RelativeGenerator →₀ R

/-- Forgetting the relative condition retains the same original closed supports and coefficients. -/
def forgetRelativePowerCycles (B : PullbackPowerBundle P U r A i V (X := X))
    (s : RelativePowerCycles P U r R A i V B) :
    CoefficientCycles (P.obj X U.base) B.bundle.smoothTotal R :=
  Finsupp.mapDomain Subtype.val s

/-- The relative associated-bundle cycle is fixed by the original descended diagonal value. -/
structure RelativePowerCycle {E : ExternalSystem P}
    (B : CycleDescent P U r Q D G R A i V z E) (d : DiagonalDescent P U r Q)
    (W : PullbackPowerBundle P U r A i V (X := X)) where
  value : RelativePowerCycles P U r R A i V W
  normalization : composeCoefficient D R
    (forgetRelativePowerCycles P U r R A i V W value)
    (coefficientGraph G R (W.map P U r A i V)) =
      diagonalCycle P U r Q D G R A i V z B d

end MathlibExt.AlgebraicGeometry.MotivicPowerDescentModels
