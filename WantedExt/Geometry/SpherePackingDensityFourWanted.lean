/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.SpherePackingDensityFour

@[expose] public section

open Filter MeasureTheory

namespace MathlibExt.Geometry.SpherePackingDensityFourWanted

/-!
# Sphere-packing density in four dimensions

Source: optimizationproblems `constants/36a.md`, frozen catalogue SHA256
`5be76ae842abb1b5154ab2fd538c4c5c4cebd91ee72b0fc009bd6ba99fd9b89b`;
H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of
Mathematics 157 (2003), 689--714, arXiv:math/0110009, Appendix A and Table 3;
D. de Laat, F. M. de Oliveira Filho and F. Vallentin, *Upper bounds for packings
of spheres of several radii*, Forum of Mathematics, Sigma 2 (2014),
DOI 10.1017/fms.2014.24, arXiv:1206.2608, Section 1.4 and Table 1.

The observation-center supremum is taken before the radius limsup. The region
is the union of closed congruent balls; disjoint open interiors allow tangency.
Positive observation radii exclude a zero-volume denominator. `ENNReal` is
the complete-lattice measure codomain; the proved bound by one makes the
optimized value finite. No optimum-attainment assertion is made.

The three displayed upper decimals and the displayed lower decimal are
approximations to the exact converted expressions, not extra exact bounds.
The primary tables call their center-density numbers bounds. Their numerical
certificates have not been replayed here. The four deep bound statements and
periodic approximation are `theorem_wanted` goals, not proofs or axioms.
The catalogue states no open exact-value conjecture, so this is a WantedExt
entry, not an OpenConjectures entry.
-/

noncomputable section

/-- Source: CE2003 introduction and Appendix A, periodic packings come arbitrarily
close to the greatest density. Positive error does not assert attainment. -/
def periodicApproximation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ P : Packing,
    P.IsPeriodic ∧ spherePackingDensity4 ≤ upperDensity P + ENNReal.ofReal ε

/-- Source: CE2003 Table 3, Rogers center-density upper bound `0.13127`,
converted exactly; displayed `0.647791…` is only an approximation. -/
def upperBound_CE2003_Rogers : Prop :=
  spherePackingDensity4 ≤ ENNReal.ofReal ((Real.pi ^ 2 / 2) * ((13127 : ℝ) / 100000))

/-- Source: CE2003 Table 3, new center-density upper bound `0.13126`,
converted exactly; displayed `0.647742…` is only an approximation. -/
def upperBound_CE2003_new : Prop :=
  spherePackingDensity4 ≤ ENNReal.ofReal ((Real.pi ^ 2 / 2) * ((13126 : ℝ) / 100000))

/-- Source: dLOV2014 Table 1, center-density upper bound `0.130587`,
converted exactly; displayed `0.644421…` is only an approximation. -/
def upperBound_dLOV2014 : Prop :=
  spherePackingDensity4 ≤ ENNReal.ofReal ((Real.pi ^ 2 / 2) * ((130587 : ℝ) / 1000000))

/-- Source: dLOV2014 Table 1, center-density lower bound `0.12500 = 1/8`,
converted exactly to `π²/16`; `0.616850` is only an approximation. -/
def lowerBound_dLOV2014 : Prop :=
  ENNReal.ofReal (Real.pi ^ 2 / 16) ≤ spherePackingDensity4

/-- Source: CE2003 Table 3. Known literature bound; no Lean proof supplied. -/
theorem_wanted upperBound_CE2003_Rogers_wanted : upperBound_CE2003_Rogers

/-- Source: CE2003 Table 3. Known literature bound; no Lean proof supplied. -/
theorem_wanted upperBound_CE2003_new_wanted : upperBound_CE2003_new

/-- Source: dLOV2014 Table 1. Known literature bound; no Lean proof supplied. -/
theorem_wanted upperBound_dLOV2014_wanted : upperBound_dLOV2014

/-- Source: dLOV2014 Table 1. Known literature bound; no Lean proof supplied. -/
theorem_wanted lowerBound_dLOV2014_wanted : lowerBound_dLOV2014

/-- Source: CE2003 introduction and Appendix A. Known periodic approximation;
no Lean proof supplied and no exact optimum-attainment claim. -/
theorem_wanted periodicApproximation_wanted : periodicApproximation

end
end MathlibExt.Geometry.SpherePackingDensityFourWanted
