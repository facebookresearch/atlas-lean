/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantStablePageCanonicalNaturality

/-! # Tests for stable-page/canonical-abutment naturality -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ComposableArrows

universe v u

namespace HomologicalComplex₂.FirstQuadrantStablePageCanonicalNaturalityTests

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalStablePageMapOfBicomplex
#check horizontalCanonicalAbutmentMapOfBicomplex
#check horizontalCanonicalAbutmentMapOfBicomplex_eq
#check horizontalStablePageCanonicalAbutmentIso_naturality

/-- The arbitrary stable-page theorem retains all three exact negative
degrees in its canonical-abutment map. -/
example (f : K ⟶ L) (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    (let data :=
        CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
      let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
      let n₁ : ℤ := -((p + q : ℕ) : ℤ)
      let n₂ : ℤ := -((p + q : ℕ) : ℤ) + 1
      let eK :=
        (horizontalCompleteFiltrationSpectralObject K).spectralSequencePageXIso
          data r hr (p, q) (horizontalSpectralPageLowerIndex r p)
          (horizontalFirstPageLowerIndex p) (horizontalFirstPageUpperIndex p)
          (horizontalSpectralPageUpperIndex r p) rfl rfl rfl rfl
          n₀ n₁ n₂ (by
            change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
            push_cast
            omega)
      let eL :=
        (horizontalCompleteFiltrationSpectralObject L).spectralSequencePageXIso
          data r hr (p, q) (horizontalSpectralPageLowerIndex r p)
          (horizontalFirstPageLowerIndex p) (horizontalFirstPageUpperIndex p)
          (horizontalSpectralPageUpperIndex r p) rfl rfl rfl rfl
          n₀ n₁ n₂ (by
            change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
            push_cast
            omega)
      let m := CategoryTheory.Abelian.SpectralObject.Hom.EMap
        (horizontalCompleteFiltrationSpectralObjectMap f)
        (homOfLE (data.le₀₁ r (p, q)))
        (homOfLE (data.le₁₂ (p, q)))
        (homOfLE (data.le₂₃ r (p, q))) n₀ n₁ n₂
      eK.hom ≫ m ≫ eL.inv) ≫
        (horizontalStablePageCanonicalAbutmentIso
          L r hr p q hlower hupper).hom =
      (horizontalStablePageCanonicalAbutmentIso
          K r hr p q hlower hupper).hom ≫
        horizontalCanonicalAbutmentMapOfBicomplex f p q :=
  horizontalStablePageCanonicalAbutmentIso_naturality
    f r hr p q hlower hupper

/-- Specialization to the first index satisfying both stability bounds. -/
example (f : K ⟶ L) (p q : ℕ) :
    horizontalStablePageMapOfBicomplex f p q ≫
        (horizontalStablePageCanonicalAbutmentIso L
          (horizontalStablePageIndex p q)
          (horizontalStablePageIndex_one_le p q) p q
          (horizontalStablePageIndex_lower_bound p q)
          (horizontalStablePageIndex_upper_bound p q)).hom =
      (horizontalStablePageCanonicalAbutmentIso K
          (horizontalStablePageIndex p q)
          (horizontalStablePageIndex_one_le p q) p q
          (horizontalStablePageIndex_lower_bound p q)
          (horizontalStablePageIndex_upper_bound p q)).hom ≫
        horizontalCanonicalAbutmentMapOfBicomplex f p q := by
  simpa [horizontalStablePageMapOfBicomplex,
    horizontalFirstQuadrantSpectralSequence] using
    horizontalStablePageCanonicalAbutmentIso_naturality f
      (horizontalStablePageIndex p q)
      (horizontalStablePageIndex_one_le p q) p q
      (horizontalStablePageIndex_lower_bound p q)
      (horizontalStablePageIndex_upper_bound p q)

/-- The corner `(0,0)` is accepted at its first stable index. -/
example (f : K ⟶ L) :
    horizontalStablePageMapOfBicomplex f 0 0 ≫
        (horizontalStablePageCanonicalAbutmentIso L
          (horizontalStablePageIndex 0 0)
          (horizontalStablePageIndex_one_le 0 0) 0 0
          (horizontalStablePageIndex_lower_bound 0 0)
          (horizontalStablePageIndex_upper_bound 0 0)).hom =
      (horizontalStablePageCanonicalAbutmentIso K
          (horizontalStablePageIndex 0 0)
          (horizontalStablePageIndex_one_le 0 0) 0 0
          (horizontalStablePageIndex_lower_bound 0 0)
          (horizontalStablePageIndex_upper_bound 0 0)).hom ≫
        horizontalCanonicalAbutmentMapOfBicomplex f 0 0 := by
  simpa [horizontalStablePageMapOfBicomplex,
    horizontalFirstQuadrantSpectralSequence] using
    horizontalStablePageCanonicalAbutmentIso_naturality f
      (horizontalStablePageIndex 0 0)
      (horizontalStablePageIndex_one_le 0 0) 0 0
      (horizontalStablePageIndex_lower_bound 0 0)
      (horizontalStablePageIndex_upper_bound 0 0)

/-- Boundary with zero horizontal index. -/
example (f : K ⟶ L) (q : ℕ) :
    horizontalStablePageMapOfBicomplex f 0 q ≫
        (horizontalStablePageCanonicalAbutmentIso L
          (horizontalStablePageIndex 0 q)
          (horizontalStablePageIndex_one_le 0 q) 0 q
          (horizontalStablePageIndex_lower_bound 0 q)
          (horizontalStablePageIndex_upper_bound 0 q)).hom =
      (horizontalStablePageCanonicalAbutmentIso K
          (horizontalStablePageIndex 0 q)
          (horizontalStablePageIndex_one_le 0 q) 0 q
          (horizontalStablePageIndex_lower_bound 0 q)
          (horizontalStablePageIndex_upper_bound 0 q)).hom ≫
        horizontalCanonicalAbutmentMapOfBicomplex f 0 q := by
  simpa [horizontalStablePageMapOfBicomplex,
    horizontalFirstQuadrantSpectralSequence] using
    horizontalStablePageCanonicalAbutmentIso_naturality f
      (horizontalStablePageIndex 0 q)
      (horizontalStablePageIndex_one_le 0 q) 0 q
      (horizontalStablePageIndex_lower_bound 0 q)
      (horizontalStablePageIndex_upper_bound 0 q)

/-- Boundary with zero vertical index. -/
example (f : K ⟶ L) (p : ℕ) :
    horizontalStablePageMapOfBicomplex f p 0 ≫
        (horizontalStablePageCanonicalAbutmentIso L
          (horizontalStablePageIndex p 0)
          (horizontalStablePageIndex_one_le p 0) p 0
          (horizontalStablePageIndex_lower_bound p 0)
          (horizontalStablePageIndex_upper_bound p 0)).hom =
      (horizontalStablePageCanonicalAbutmentIso K
          (horizontalStablePageIndex p 0)
          (horizontalStablePageIndex_one_le p 0) p 0
          (horizontalStablePageIndex_lower_bound p 0)
          (horizontalStablePageIndex_upper_bound p 0)).hom ≫
        horizontalCanonicalAbutmentMapOfBicomplex f p 0 := by
  simpa [horizontalStablePageMapOfBicomplex,
    horizontalFirstQuadrantSpectralSequence] using
    horizontalStablePageCanonicalAbutmentIso_naturality f
      (horizontalStablePageIndex p 0)
      (horizontalStablePageIndex_one_le p 0) p 0
      (horizontalStablePageIndex_lower_bound p 0)
      (horizontalStablePageIndex_upper_bound p 0)

/-- At `(1,0)`, the two branches defining the stable maximum are equal. -/
example (f : K ⟶ L) :
    horizontalStablePageMapOfBicomplex f 1 0 ≫
        (horizontalStablePageCanonicalAbutmentIso L
          (horizontalStablePageIndex 1 0)
          (horizontalStablePageIndex_one_le 1 0) 1 0
          (horizontalStablePageIndex_lower_bound 1 0)
          (horizontalStablePageIndex_upper_bound 1 0)).hom =
      (horizontalStablePageCanonicalAbutmentIso K
          (horizontalStablePageIndex 1 0)
          (horizontalStablePageIndex_one_le 1 0) 1 0
          (horizontalStablePageIndex_lower_bound 1 0)
          (horizontalStablePageIndex_upper_bound 1 0)).hom ≫
        horizontalCanonicalAbutmentMapOfBicomplex f 1 0 := by
  simpa [horizontalStablePageMapOfBicomplex,
    horizontalFirstQuadrantSpectralSequence] using
    horizontalStablePageCanonicalAbutmentIso_naturality f
      (horizontalStablePageIndex 1 0)
      (horizontalStablePageIndex_one_le 1 0) 1 0
      (horizontalStablePageIndex_lower_bound 1 0)
      (horizontalStablePageIndex_upper_bound 1 0)

/-- Identity bicomplex maps are accepted by the arbitrary-`r` theorem. -/
example
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :=
  horizontalStablePageCanonicalAbutmentIso_naturality
    (𝟙 K) r hr p q hlower hupper

/-- Exact target type of the canonical map, including all negative degrees. -/
example (f : K ⟶ L) (p q : ℕ) :
    horizontalFirstQuadrantCanonicalAbutmentTerm K p q ⟶
      horizontalFirstQuadrantCanonicalAbutmentTerm L p q :=
  horizontalCanonicalAbutmentMapOfBicomplex f p q

#print axioms horizontalStablePageMapOfBicomplex
#print axioms horizontalCanonicalAbutmentMapOfBicomplex
#print axioms horizontalStablePageCanonicalAbutmentIso_naturality

end HomologicalComplex₂.FirstQuadrantStablePageCanonicalNaturalityTests

end
