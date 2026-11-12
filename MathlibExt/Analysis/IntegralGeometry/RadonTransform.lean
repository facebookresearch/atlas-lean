/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 383, Analysis 384

/-!
# Euclidean Radon Transform; Sectional Volume Function

## References

* This is the standard Euclidean Radon transform. See, for example: S. Helgason, The Radon
  Transform, Birkhäuser. See also: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis
  and Mathematical Physics 12 (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x (for
  `euclideanRadonTransform`)
* See: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis and Mathematical Physics 12
  (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x, See also: M. Agranovsky, Convex
  Bodies with Algebraic Section Volume Functions, Journal d'Analyse Mathématique 158 (2026),
  635-656. https://doi.org/10.1007/s11854-025-0412-1 (for `sectionalVolume`)

## References

* This is the standard Euclidean Radon transform. See, for example: S. Helgason, The Radon
  Transform, Birkhäuser. See also: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis
  and Mathematical Physics 12 (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x (for
  `euclideanRadonTransform`)
* See: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis and Mathematical Physics 12
  (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x, See also: M. Agranovsky, Convex
  Bodies with Algebraic Section Volume Functions, Journal d'Analyse Mathématique 158 (2026),
  635-656. https://doi.org/10.1007/s11854-025-0412-1 (for `sectionalVolume`)

## References

* This is the standard Euclidean Radon transform. See, for example: S. Helgason, The Radon
  Transform, Birkhäuser. See also: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis
  and Mathematical Physics 12 (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x (for
  `euclideanRadonTransform`)
* See: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis and Mathematical Physics 12
  (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x, See also: M. Agranovsky, Convex
  Bodies with Algebraic Section Volume Functions, Journal d'Analyse Mathématique 158 (2026),
  635-656. https://doi.org/10.1007/s11854-025-0412-1 (for `sectionalVolume`)

## References

* This is the standard Euclidean Radon transform. See, for example: S. Helgason, The Radon
  Transform, Birkhäuser. See also: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis
  and Mathematical Physics 12 (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x (for
  `euclideanRadonTransform`)
* See: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis and Mathematical Physics 12
  (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x, See also: M. Agranovsky, Convex
  Bodies with Algebraic Section Volume Functions, Journal d'Analyse Mathématique 158 (2026),
  635-656. https://doi.org/10.1007/s11854-025-0412-1 (for `sectionalVolume`)

## References

* This is the standard Euclidean Radon transform. See, for example: S. Helgason, The Radon
  Transform, Birkhäuser. See also: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis
  and Mathematical Physics 12 (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x (for
  `euclideanRadonTransform`)
* See: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis and Mathematical Physics 12
  (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x, See also: M. Agranovsky, Convex
  Bodies with Algebraic Section Volume Functions, Journal d'Analyse Mathématique 158 (2026),
  635-656. https://doi.org/10.1007/s11854-025-0412-1 (for `sectionalVolume`)

## References

* This is the standard Euclidean Radon transform. See, for example: S. Helgason, The Radon
  Transform, Birkhäuser. See also: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis
  and Mathematical Physics 12 (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x (for
  `euclideanRadonTransform`)
* See: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis and Mathematical Physics 12
  (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x, See also: M. Agranovsky, Convex
  Bodies with Algebraic Section Volume Functions, Journal d'Analyse Mathématique 158 (2026),
  635-656. https://doi.org/10.1007/s11854-025-0412-1 (for `sectionalVolume`)

## References

* This is the standard Euclidean Radon transform. See, for example: S. Helgason, The Radon
  Transform, Birkhäuser. See also: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis
  and Mathematical Physics 12 (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x (for
  `euclideanRadonTransform`)
* See: M. Agranovsky, Domains with Algebraic X-Ray Transform, Analysis and Mathematical Physics 12
  (2022), Article 60. https://doi.org/10.1007/s13324-022-00657-x, See also: M. Agranovsky, Convex
  Bodies with Algebraic Section Volume Functions, Journal d'Analyse Mathématique 158 (2026),
  635-656. https://doi.org/10.1007/s11854-025-0412-1 (for `sectionalVolume`)
-/

namespace MetaMathlibExt

-- Analysis 383: Euclidean Radon Transform

/-- Let

f:ℝⁿ→ℝ.

For a direction

ξ∈ℝⁿ

and t∈ℝ, define the Euclidean Radon transform by

Rf(ξ,t)=∫_{{x∈ℝⁿ:⟨ x,ξ⟩=t}} f(x) dℋⁿ⁻¹(x),

where ℋⁿ⁻¹ denotes (n-1)-dimensional Euclidean Hausdorff measure.

When ‖ξ‖=1, the parameter t is the signed distance of the hyperplane from the origin.
-/
noncomputable def euclideanRadonTransform
    {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n))
    (t : ℝ) : ℝ :=
  ∫ x in {x : EuclideanSpace ℝ (Fin n) | inner ℝ x ξ = t},
    f x ∂(MeasureTheory.Measure.euclideanHausdorffMeasure (n - 1))

-- Analysis 384: Sectional Volume Function

/-- For a set

K⊂ℝⁿ,

a direction

ξ∈ℝⁿ

and t∈ℝ, define

A_K(ξ,t)=volₙ₋₁(K∩{x:⟨ x,ξ⟩=t}).

For unit ξ, this is the (n-1)-dimensional volume of the section of K by the hyperplane at signed
distance t from the origin.
-/
noncomputable def sectionalVolume
    {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (ξ : EuclideanSpace ℝ (Fin n))
    (t : ℝ) : ENNReal :=
  (MeasureTheory.Measure.euclideanHausdorffMeasure (n - 1))
    (K ∩
      {x : EuclideanSpace ℝ (Fin n) |
        inner ℝ x ξ = t})

end MetaMathlibExt

end
