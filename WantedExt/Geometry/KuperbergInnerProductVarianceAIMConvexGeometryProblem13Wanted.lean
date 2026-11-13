/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kuperberg's variance conjecture for random inner products fails (AIM Mahler duality list, item 17)

Problems from the AIM workshop Mahler's conjecture and duality in convex geometry (notes by J. Kim,
2010), item 17 (G. Kuperberg): for random vectors `X` and `Y` distributed in a symmetric convex body
`K ⊆ ℝⁿ` and in its polar `K°`, is the variance of `⟨X, Y⟩` largest when `K` is an ellipsoid?
Klartag showed that it is not, in sufficiently high dimension.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import MathlibExt.Analysis.InnerProductSpace.PolarSet
public import MathlibExt.Geometry.Convex.Covering

@[expose] public section

namespace MathlibExt.Geometry.KuperbergInnerProductVarianceAIMConvexGeometryProblem13Wanted

/-!
Source: Problems from the workshop Mahler's conjecture and duality in convex geometry, American
Institute of Mathematics, August 9-13, 2010, notes by J. Kim, item 17 (G. Kuperberg),
https://aimath.org/WWN/mahlerduality/mahlerduality.pdf. UnsolvedMath record UM-20001281
(`AIM-CONVEX_GEOMETRY-0013`), dataset ulamai/UnsolvedMath v1.8.0.

`X` is uniform on `K` and `Y` uniform on the polar body `K° = {y | ∀ x ∈ K, ⟪x, y⟫ ≤ 1}`,
independent, so `E f(X, Y) = (|K| |K°|)⁻¹ ∫_K ∫_{K°} f`, and the variance is
`E ⟨X, Y⟩² - (E ⟨X, Y⟩)²` (the mean vanishes for symmetric `K`; the second moment is Klartag's
`φ(K)`). Symmetric convex bodies are compact, convex, with nonempty interior and `K = -K`. The
variance is invariant under linear maps (`φ(TK) = φ(K)`), so every ellipsoid has the value of the
Euclidean unit ball, `n / (n + 2)²`; 'largest for ellipsoids' is stated as comparison with the unit
ball. The item's weaker integral conjecture, which this refutation does not decide, is the
OpenConjectures entry AIMConvexGeometryProblem13.
-/

open MeasureTheory

/-- `Var ⟨X, Y⟩` for independent `X` uniform on `K` and `Y` uniform on the polar body
`K° = {y | ∀ x ∈ K, ⟪x, y⟫ ≤ 1}`: with `E f = (|K| |K°|)⁻¹ ∫_K ∫_{K°} f(x, y) dy dx`, the value
`E ⟨X, Y⟩² - (E ⟨X, Y⟩)²`. -/
noncomputable def innerProductVariance {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  let m := volume.real K * volume.real (MetaMathlibExt.polarSet K)
  (∫ x in K, ∫ y in MetaMathlibExt.polarSet K, inner ℝ x y ^ 2) / m -
    ((∫ x in K, ∫ y in MetaMathlibExt.polarSet K, inner ℝ x y) / m) ^ 2

/-- Kuperberg's conjecture (AIM Mahler-duality workshop list, item 17): for every origin-symmetric
convex body `K ⊆ ℝⁿ`, `Var ⟨X, Y⟩` is at most its value for the Euclidean unit ball (every ellipsoid
gives the same value, `n / (n + 2)²`). -/
def innerProductVarianceMaximalForEllipsoids : Prop :=
  ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))), ConvexCovering.IsConvexBody K →
    (∀ x ∈ K, -x ∈ K) →
      innerProductVariance K ≤
        innerProductVariance (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/--
Resolved false: in some dimension there is a symmetric convex body `K` with `Var ⟨X, Y⟩` larger than
for the Euclidean ball. Klartag, §1, quotes the conjecture as 'φ(K) ≤ n/(n + 2)² for any
centrally-symmetric convex body K ⊆ ℝⁿ' (Kuperberg's Conjecture 5.1, φ(K) = E⟨X, Y⟩²) and writes
'Our next proposition shows that this conjecture is indeed false in a sufficiently high dimension';
Proposition 1.5 gives, for every n ≥ 1, an unconditional convex body K ⊆ ℝⁿ with φ(K) ≥ c for a
universal constant c > 0. Source: Problems from the workshop Mahler's conjecture and duality in
convex geometry, American Institute of Mathematics, August 9-13, 2010, notes by J. Kim, item 17 (G.
Kuperberg), https://aimath.org/WWN/mahlerduality/mahlerduality.pdf; resolution: B. Klartag,
Isotropic constants and Mahler volumes, Adv. Math. 330 (2018), 74-108, arXiv:1710.08084, §1,
equation (8) and the paragraph before Proposition 1.5 (Kuperberg's conjecture φ(K) ≤ n/(n + 2)² is
false in sufficiently high dimension), Proposition 1.5, proved in §5,
https://doi.org/10.1016/j.aim.2018.03.009.
-/
public theorem_wanted innerProductVarianceMaximalForEllipsoids_refuted :
    ¬ innerProductVarianceMaximalForEllipsoids

end MathlibExt.Geometry.KuperbergInnerProductVarianceAIMConvexGeometryProblem13Wanted
