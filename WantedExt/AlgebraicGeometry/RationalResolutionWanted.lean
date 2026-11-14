/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RationalResolution

/-!
# Rational singularities and Grauert–Riemenschneider vanishing

These requests use actual resolutions, their normalized structure maps,
canonical lines characterized by natural Serre duality, and actual higher
direct-image sheaves. Generic depth and surface-resolution facts already
in the public sources are not requested separately.

References: Grauert–Riemenschneider, *Verschwindungssätze für analytische
Kohomologiegruppen auf komplexen Räumen*, Invent. Math. 11 (1970), 263–292;
Kollár–Mori, *Birational Geometry of Algebraic Varieties*, Chapter 5.
Covered surface source: AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/RationalSingularities/`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RationalResolutionWanted

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.BirationalResolution
open MathlibExt.AlgebraicGeometry.RationalResolution
open MathlibExt.AlgebraicGeometry.PlurigenusFamilies

universe u

/-- Rationality is independent of the chosen resolution. -/
theorem_wanted resolution_independence (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
   (hX : IsNormalIntegral X.left)
    (R T : ResolutionModel X) (hR : IsRationalResolution R) :
    IsRationalResolution T

/-- Rational singularities are Cohen–Macaulay. -/
theorem_wanted rational_isCohenMacaulay (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
   (hX : IsNormalIntegral X.left)
    (R : ResolutionModel X) (hR : IsRationalResolution R) :
    IsCohenMacaulayStalkwise X.left

/-- Canonical higher direct images of a resolution vanish. -/
theorem_wanted grauertRiemenschneider (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
   (hX : IsNormalIntegral X.left)
    (R : ResolutionModel X) (n : ℕ)
    [SmoothOfRelativeDimension n R.source.hom]
    (K : R.source.left.Modules)
    (hK : SerreDualizingLine R.source.hom K n) :
    ∀ i : ℕ, 0 < i → IsZero (higherDirectImage R.morphism.left K i)

end WantedExt.AlgebraicGeometry.RationalResolutionWanted
