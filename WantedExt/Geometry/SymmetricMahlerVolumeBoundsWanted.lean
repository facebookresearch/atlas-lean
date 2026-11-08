/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Convex.HannerPolytope
public import MathlibExt.Analysis.InnerProductSpace.PolarSet
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# Known bounds and Hanner formulas for the symmetric Mahler volume product

These private requests are data, not assumed or proved theorems. The lower
bounds use the same actual positive-dimensional Euclidean convex bodies,
one-sided polar and factorial normalization as the optimal-base problem.
They do not import or assume an OpenConjectures target.
-/

open MeasureTheory
open scoped ENNReal

namespace WantedExt.Geometry.SymmetricMahlerVolumeBoundsWanted

/--
Source: Bourgain–Milman (1987), constant 25a lower-bound row. One positive
real base is chosen before every dimension and every symmetric convex body.
The complete theorem is unproved here.
-/
private theorem_wanted bourgainMilman_positive_base :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 0 < n →
        ∀ K : Set (EuclideanSpace ℝ (Fin n)),
          Convex ℝ K → IsCompact K →
          (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K →
          (∀ x, x ∈ K ↔ -x ∈ K) →
            (ENNReal.ofReal c) ^ n ≤
              (n.factorial : ℝ≥0∞) * volume K * volume (MetaMathlibExt.polarSet K)

/--
Source: Nazarov (2012), constant 25a; the normalization is recorded by
Berndtsson, arXiv:2008.00837v1, Section 5. The endpoint is exactly π³/16,
not its approximate decimal. This request does not supply Nazarov's proof.
-/
private theorem_wanted nazarov_lower_bound :
    ∀ (n : ℕ), 0 < n →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)),
        Convex ℝ K → IsCompact K →
        (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K →
        (∀ x, x ∈ K ↔ -x ∈ K) →
          (ENNReal.ofReal (Real.pi ^ 3 / 16)) ^ n ≤
            (n.factorial : ℝ≥0∞) * volume K * volume (MetaMathlibExt.polarSet K)

/--
Source: Kuperberg, arXiv:math/0610904v3, Corollary c:bound; constant 25a.
After the catalogue's factorial normalization the universal lower base is π.
The geometric lower-bound proof is not implemented here.
-/
private theorem_wanted kuperberg_lower_bound :
    ∀ (n : ℕ), 0 < n →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)),
        Convex ℝ K → IsCompact K →
        (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K →
        (∀ x, x ∈ K ↔ -x ∈ K) →
          (ENNReal.ofReal Real.pi) ^ n ≤
            (n.factorial : ℝ≥0∞) * volume K * volume (MetaMathlibExt.polarSet K)

/--
Source: Fradelizi–Meyer–Zvavitch, arXiv:2301.06131v1, lines 618–622.
The known product formula is requested only for actual recursively constructed
Hanner bodies. It is separate from the conjectural equality iff for arbitrary
symmetric convex bodies; no converse or universal sharp inequality is assumed.
-/
private theorem_wanted normalizedVolumeProduct_eq_four_pow_of_isHannerPolytope
    {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MetaMathlibExt.IsHannerPolytope K) :
    (n.factorial : ℝ≥0∞) * volume K * volume (MetaMathlibExt.polarSet K) =
      (4 : ℝ≥0∞) ^ n

/--
Source: Fradelizi–Meyer–Zvavitch, arXiv:2301.06131v1, Definition hanner
and the cube/cross-polytope discussion. This coordinate identification of the
actual recursive ℓ1 construction is an unproved semantic bridge.
-/
private theorem_wanted hannerCrossPolytope_eq_coordinateCrossPolytope (n : ℕ) :
    MetaMathlibExt.hannerCrossPolytope n =
      {x : EuclideanSpace ℝ (Fin (n + 1)) | ∑ i, |x i| ≤ 1}

/--
Source: Fradelizi–Meyer–Zvavitch, arXiv:2301.06131v1, Hanner properties
following Definition hanner. Actual Hanner bodies are closed under polarity;
the recursive polar-sum identities needed for this request remain unproved.
-/
private theorem_wanted isHannerPolytope_polarSet
    {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MetaMathlibExt.IsHannerPolytope K) :
    MetaMathlibExt.IsHannerPolytope (MetaMathlibExt.polarSet K)

end WantedExt.Geometry.SymmetricMahlerVolumeBoundsWanted
