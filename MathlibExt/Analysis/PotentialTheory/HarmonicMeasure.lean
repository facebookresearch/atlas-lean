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

public import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Analysis 370, Analysis 371, Analysis 372

/-!
# Superharmonic On A Set; Upper Perron Solution; Harmonic Measure

## References

* See Definition 3.4 on page 258 in this paper
  https://link.springer.com/article/10.1007/s13348-021-00317-6. (for `IsSuperharmonicOn`)
* See Definition 4.1 on page 258 in this paper
  https://link.springer.com/article/10.1007/s13348-021-00317-6 (for `upperPerronSolution`)
* Classical definition via the Perron solution and Riesz representation theorem. See Encyclopedia
  of Mathematics: https://encyclopediaofmath.org/index.php?title=Harmonic_measure&lang=en (for
  `IsHarmonicMeasure`)
-/

namespace MetaMathlibExt

-- Analysis 370: Superharmonic On A Set

/-- Let Ω⊂ℝⁿ. A real-valued function u is superharmonic on Ω if it is lower semicontinuous there and
satisfies the harmonic comparison principle: whenever V is open with compact closure contained in Ω,
and h is harmonic on V and continuous on V̅, h≤ u on ∂ V implies h≤ u throughout V.
-/
def IsSuperharmonicOn
    {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  LowerSemicontinuousOn u Ω ∧
    ∀ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V →
      IsCompact (closure V) →
      closure V ⊆ Ω →
      ∀ h : EuclideanSpace ℝ (Fin n) → ℝ,
        InnerProductSpace.HarmonicContOnCl h V →
        (∀ y ∈ frontier V, h y ≤ u y) →
        ∀ y ∈ V, h y ≤ u y

-- Analysis 371: Upper Perron Solution

/-- Let Ω⊂ℝⁿ be a domain and let f:∂Ω→ℝ be boundary data. The upper Perron class consists of
superharmonic functions u on Ω, bounded below,
satisfying

liminf_{Ω∋ y→ξ}u(y)≥ f(ξ)

for every ξ∈∂Ω.

The upper Perron solution is the extended-real-valued function

P̅_Ω f(x)=inf_{u∈𝒰_f}u(x).

The infimum is taken in

[-∞,+∞].

In particular, if the upper Perron class is empty, then

P̅_Ω f(x)=+∞.

This defines a value for every dimension and every set; it asserts neither that the class is
nonempty nor that the infimum is finite. For n = 0 and Ω = ℝ⁰, a bounded domain with empty boundary,
no function is superharmonic on Ω, so the value is +∞.
-/
noncomputable def upperPerronSolution
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  sInf {
    r : EReal |
      ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
        IsSuperharmonicOn u Ω ∧
        (∃ C : ℝ, ∀ y ∈ Ω, C ≤ u y) ∧
        (∀ ξ ∈ frontier Ω,
          ∀ a : ℝ, a < f ξ →
            ∀ᶠ y in nhdsWithin ξ Ω, a < u y) ∧
        r = (u x : EReal)
  }

-- Analysis 372: Harmonic Measure

/-- Let Ω⊂ℝⁿ be a bounded domain and let x∈Ω.

A probability measure μ is a harmonic measure ω_Ωˣ when it is concentrated on ∂Ω and represents
the generalized Dirichlet solution. This is a predicate on a candidate measure, not a statement that
one exists; for n = 0 and Ω = ℝ⁰ the boundary is empty and no measure qualifies.

More precisely, for every continuous boundary datum f:∂Ω→ℝ, one has

H_f(x)=∫_{∂Ω} f dω_Ωˣ,

where H_f is the Perron, or generalized, solution of the Dirichlet problem on Ω with boundary data
f.

The formal `upperPerronSolution` is `EReal`-valued; the predicate requires it to equal the
coercion to `EReal` of the ordinary real-valued integral.
-/
def IsHarmonicMeasure
    {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n))
    (μ : MeasureTheory.ProbabilityMeasure
      (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsOpen Ω ∧
  IsConnected Ω ∧
  Bornology.IsBounded Ω ∧
  x ∈ Ω ∧
  (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
      ((frontier Ω)ᶜ) = 0 ∧
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
    ContinuousOn f (frontier Ω) →
      (↑(∫ y, f y ∂(μ : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin n)))) : EReal) =
        upperPerronSolution Ω f x

end MetaMathlibExt

end
