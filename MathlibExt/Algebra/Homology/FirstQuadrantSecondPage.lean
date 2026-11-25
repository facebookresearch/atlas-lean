/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageDifferential
public import MathlibExt.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.Embedding.Boundary
public import MathlibExt.Algebra.Homology.VerticalHomologyComplex
import Mathlib.Tactic.Ring

/-!
# The second page of the first-quadrant bicomplex spectral sequence

The coherent first-page comparison is normalized by
`(-1)^(p*(q+1))`.  In each fixed vertical degree, these normalized maps
assemble into an isomorphism from the corresponding first-page row complex
to the horizontal complex of vertical homology.  Taking homology identifies
the second-page object with horizontal homology of vertical homology.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The coherent first-page/vertical-homology isomorphism, normalized in
column `p` by `(-1)^(p*(q+1))`. -/
noncomputable def horizontalFirstPageNormalizedVerticalHomologyIso
    (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      (K.X p).homology q :=
  (((p : ℤ) * ((q : ℤ) + 1)).negOnePow • Iso.refl _) ≪≫
    horizontalFirstPageCoherentVerticalHomologyIso K p q

/-- Forward map of the normalized first-page isomorphism. -/
theorem horizontalFirstPageNormalizedVerticalHomologyIso_hom
    (p q : ℕ) :
    (horizontalFirstPageNormalizedVerticalHomologyIso K p q).hom =
      ((p : ℤ) * ((q : ℤ) + 1)).negOnePow •
        (horizontalFirstPageCoherentVerticalHomologyIso K p q).hom := by
  simp [horizontalFirstPageNormalizedVerticalHomologyIso]

/-- The normalized first-page isomorphisms intertwine the actual page-one
differential with the unsigned horizontal homology map. -/
theorem horizontalFirstPage_d_normalizedVerticalHomology
    (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).d
        (p + 1, q) (p, q) ≫
      (horizontalFirstPageNormalizedVerticalHomologyIso K p q).hom =
    (horizontalFirstPageNormalizedVerticalHomologyIso K (p + 1) q).hom ≫
      horizontalFirstPageHorizontalHomologyMap K p q := by
  have hsign :
      ((p : ℤ) * ((q : ℤ) + 1)).negOnePow *
          (((q : ℕ) + 1 : ℕ) : ℤ).negOnePow =
        (((p + 1 : ℕ) : ℤ) * ((q : ℤ) + 1)).negOnePow := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    refine ⟨0, ?_⟩
    push_cast
    ring
  rw [horizontalFirstPageNormalizedVerticalHomologyIso_hom,
    horizontalFirstPageNormalizedVerticalHomologyIso_hom]
  rw [Linear.comp_units_smul]
  rw [horizontalFirstPage_d_coherentVerticalHomology_eq_horizontal K p q]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  rw [hsign]

/-- Embedding of the horizontal row at vertical degree `q` into the index
shape of the first page. -/
noncomputable def horizontalFirstPageRowEmbedding (q : ℕ) :
    ComplexShape.Embedding (ComplexShape.down ℕ)
      (ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩) :=
  ComplexShape.Embedding.mk' _ _ (fun p => (p, q))
    (fun _ _ h => congrArg Prod.fst h)
    (by
      intro i j
      simp only [ComplexShape.down, ComplexShape.down',
        ComplexShape.spectralSequenceNat_rel_iff]
      constructor
      · intro h
        constructor <;> push_cast <;> omega
      · rintro ⟨h, _⟩
        omega)

/-- A first-page differential relates two indices in the fixed row exactly
when the corresponding horizontal chain degrees are related. -/
noncomputable instance horizontalFirstPageRowEmbedding_isRelIff (q : ℕ) :
    (horizontalFirstPageRowEmbedding q).IsRelIff := by
  unfold horizontalFirstPageRowEmbedding
  infer_instance

/-- The fixed first-page row is closed under successors. -/
noncomputable instance horizontalFirstPageRowEmbedding_isTruncGE (q : ℕ) :
    (horizontalFirstPageRowEmbedding q).IsTruncGE where
  toIsRelIff := inferInstance
  mem_next {j k'} h := by
    refine ⟨k'.1, ?_⟩
    change (k'.1, q) = k'
    ext
    · rfl
    · have h2 : (q : ℤ) = (k'.2 : ℤ) := by
        simpa [horizontalFirstPageRowEmbedding] using h.2
      exact_mod_cast h2

/-- The fixed first-page row is closed under predecessors. -/
noncomputable instance horizontalFirstPageRowEmbedding_isTruncLE (q : ℕ) :
    (horizontalFirstPageRowEmbedding q).IsTruncLE where
  toIsRelIff := inferInstance
  mem_prev {i' j} h := by
    refine ⟨i'.1, ?_⟩
    change (i'.1, q) = i'
    ext
    · rfl
    · have h2 : (i'.2 : ℤ) = (q : ℤ) := by
        simpa [horizontalFirstPageRowEmbedding] using h.2
      exact_mod_cast h2.symm

/-- The fixed-`q` row of the first page, restricted to a chain complex over
the horizontal degree. -/
noncomputable def horizontalFirstPageRowComplex (q : ℕ) :
    ChainComplex C ℕ :=
  ((horizontalFirstQuadrantSpectralSequence K).page 1).restriction
    (horizontalFirstPageRowEmbedding q)

/-- Objects of the restricted first-page row. -/
@[simp]
theorem horizontalFirstPageRowComplex_X (p q : ℕ) :
    (horizontalFirstPageRowComplex K q).X p =
      ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) :=
  rfl

/-- Differentials of the restricted first-page row. -/
@[simp]
theorem horizontalFirstPageRowComplex_d (p p' q : ℕ) :
    (horizontalFirstPageRowComplex K q).d p p' =
      ((horizontalFirstQuadrantSpectralSequence K).page 1).d (p, q) (p', q) :=
  rfl

/-- The normalized first-page row is isomorphic to the horizontal complex of
vertical homology. -/
noncomputable def horizontalFirstPageRowComplexIsoVerticalHomologyComplex
    (q : ℕ) :
    horizontalFirstPageRowComplex K q ≅ K.verticalHomologyComplex q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => horizontalFirstPageNormalizedVerticalHomologyIso K p q) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      exact (horizontalFirstPage_d_normalizedVerticalHomology K j q).symm)

/-- The fixed-row embedding sends horizontal degree `p` to the bidegree `(p, q)`. -/
@[simp]
theorem horizontalFirstPageRowEmbedding_f (p q : ℕ) :
    (horizontalFirstPageRowEmbedding q).f p = (p, q) :=
  rfl

/-- Components of the normalized first-page row-complex isomorphism. -/
theorem horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_f
    (p q : ℕ) :
    (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q).hom.f p =
      (horizontalFirstPageNormalizedVerticalHomologyIso K p q).hom :=
  rfl

/-- Homology of a restricted first-page row agrees with homology of the full
first page at the corresponding bidegree. -/
noncomputable def horizontalFirstPageRowHomologyIso (p q : ℕ) :
    (horizontalFirstPageRowComplex K q).homology p ≅
      ((horizontalFirstQuadrantSpectralSequence K).page 1).homology (p, q) :=
  let E := horizontalFirstPageRowEmbedding q
  let P := (horizontalFirstQuadrantSpectralSequence K).page 1
  P.restrictionHomologyIsoAt E p (E.prev_f rfl) (E.next_f rfl)

/-- The second-page object at `(p,q)` is horizontal homology in degree `p`
of the vertical-homology complex in degree `q`. -/
noncomputable def horizontalSecondPageVerticalHorizontalHomologyIso
    (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q) ≅
      (K.verticalHomologyComplex q).homology p :=
  ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (p, q)).symm ≪≫
    (horizontalFirstPageRowHomologyIso K p q).symm ≪≫
    HomologicalComplex.homologyMapIso
      (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q) p

end HomologicalComplex₂
