/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageDifferential
public import MathlibExt.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.Embedding.Boundary
public import MathlibExt.Algebra.Homology.VerticalHomologyComplex
import Mathlib.Tactic.Ring

/-!
# The second page as horizontal homology of vertical homology

Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). For p,q ∈ ℕ, the
first-page comparison E¹_{p,q} ≅ H_q(K_p) is normalized by the sign (−1)^{p(q+1)}. The
normalized maps intertwine the differential E¹_{p+1,q} → E¹_{p,q} with H_q(K.d_{p+1,p}).

Restricting E¹ to the row of fixed vertical degree q therefore gives a chain complex
isomorphic to the horizontal complex of vertical homology. Its degree-p homology identifies
E²_{p,q} with H_p(H_q^vertical(K)).
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

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. Define
E¹_{p,q} ≅ H_q(K_p) by multiplying the coherent first-page/vertical-homology isomorphism by
(−1)^{p(q+1)} on its source. The sign is the integer unit ((p:ℤ)((q:ℤ)+1)).negOnePow acting on
the identity morphism before the coherent comparison. This normalization makes the first-page
differential correspond to the horizontal map on vertical homology. -/
noncomputable def horizontalFirstPageNormalizedVerticalHomologyIso
    (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      (K.X p).homology q :=
  (((p : ℤ) * ((q : ℤ) + 1)).negOnePow • Iso.refl _) ≪≫
    horizontalFirstPageCoherentVerticalHomologyIso K p q

/-- For a bicomplex K of shape (down ℕ,down ℕ) in an abelian category C and p,q ∈ ℕ, let e_{p,q} :
E¹_{p,q} ≅ H_q(K_p) be the coherent first-page comparison. The forward morphism of the
normalized comparison is (−1)^{p(q+1)}·e_{p,q}.hom. The exponent is computed in ℤ, and the
integer sign acts through the preadditive structure of C. -/
theorem horizontalFirstPageNormalizedVerticalHomologyIso_hom
    (p q : ℕ) :
    (horizontalFirstPageNormalizedVerticalHomologyIso K p q).hom =
      ((p : ℤ) * ((q : ℤ) + 1)).negOnePow •
        (horizontalFirstPageCoherentVerticalHomologyIso K p q).hom := by
  simp [horizontalFirstPageNormalizedVerticalHomologyIso]

/-- Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). For p,q ∈ ℕ, let
e′_{p,q} : E¹_{p,q} ≅ H_q(K_p) be the coherent comparison normalized by (−1)^{p(q+1)}. Then
d¹_{(p+1,q),(p,q)} ≫ e′_{p,q}.hom = e′_{p+1,q}.hom ≫ H_q(K.d_{p+1,p}). Thus the first-page
differential becomes the horizontal homology map without an additional sign. -/
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

/-- For q ∈ ℕ, the map p ↦ (p,q) defines an embedding of the chain shape down ℕ into the
first-page spectral shape with differential bidegree (−1,0). It is injective and preserves
differential relations: j+1=i in the horizontal chain shape exactly when the spectral shape
relates (i,q) to (j,q). The vertical coordinate q is fixed. -/
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

/-- For q ∈ ℕ, the embedding p ↦ (p,q) from down ℕ to the spectral shape of bidegree (−1,0)
satisfies IsRelIff. Explicitly, for horizontal indices i,j ∈ ℕ, the source relation j+1=i
holds if and only if the target shape relates (i,q) to (j,q). Thus restricting the first page
to this row retains exactly its horizontal differential relations. -/
noncomputable instance horizontalFirstPageRowEmbedding_isRelIff (q : ℕ) :
    (horizontalFirstPageRowEmbedding q).IsRelIff := by
  unfold horizontalFirstPageRowEmbedding
  infer_instance

/-- For q ∈ ℕ, the image of the row embedding p ↦ (p,q) is closed under outgoing relations in the
first-page spectral shape of bidegree (−1,0). Any differential relation with source (p,q) has
target with second coordinate q and hence lies in the same row. Together with reflection of
relations, this gives the embedding its IsTruncGE structure. -/
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

/-- For q ∈ ℕ, the image of the row embedding p ↦ (p,q) is closed under incoming relations in the
first-page spectral shape of bidegree (−1,0). Any differential relation with target (p,q) has
source with second coordinate q and hence lies in the same row. Together with reflection of
relations, this gives the embedding its IsTruncLE structure. -/
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

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and q ∈ ℕ. Restrict the
first page of its horizontal spectral sequence along p ↦ (p,q) to define a chain complex of
shape down ℕ. Its degree-p object is E¹_{p,q}, and its differential from p to p′ is
d¹_{(p,q),(p′,q)}. The first-page shape preserves the fixed vertical coordinate q. -/
noncomputable def horizontalFirstPageRowComplex (q : ℕ) :
    ChainComplex C ℕ :=
  ((horizontalFirstQuadrantSpectralSequence K).page 1).restriction
    (horizontalFirstPageRowEmbedding q)

/-- For a bicomplex K of shape (down ℕ,down ℕ) in an abelian category C and p,q ∈ ℕ, the degree-p
object of the first-page row complex at vertical degree q is exactly the page object E¹_{p,q}.
This is the object equality obtained by restricting the first-page complex along the embedding
p ↦ (p,q). -/
@[simp]
theorem horizontalFirstPageRowComplex_X (p q : ℕ) :
    (horizontalFirstPageRowComplex K q).X p =
      ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) :=
  rfl

/-- For a bicomplex K of shape (down ℕ,down ℕ) in an abelian category C and p,p′,q ∈ ℕ, the
row-complex differential from p to p′ equals d¹_{(p,q),(p′,q)} in the full first page. The
equality holds for all index pairs; both sides vanish when the down ℕ differential relation
p′+1=p fails. -/
@[simp]
theorem horizontalFirstPageRowComplex_d (p p' q : ℕ) :
    (horizontalFirstPageRowComplex K q).d p p' =
      ((horizontalFirstQuadrantSpectralSequence K).page 1).d (p, q) (p', q) :=
  rfl

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and q ∈ ℕ. The
first-page row complex with degree-p term E¹_{p,q} is isomorphic to K.verticalHomologyComplex
q, whose term is H_q(K_p) and whose differential is H_q(K.d_{p+1,p}). The component at p is
the coherent vertical-homology comparison multiplied by (−1)^{p(q+1)}. These normalized
components commute with the row differentials. -/
noncomputable def horizontalFirstPageRowComplexIsoVerticalHomologyComplex
    (q : ℕ) :
    horizontalFirstPageRowComplex K q ≅ K.verticalHomologyComplex q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => horizontalFirstPageNormalizedVerticalHomologyIso K p q) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      exact (horizontalFirstPage_d_normalizedVerticalHomology K j q).symm)

/-- For p,q ∈ ℕ, the index map of the first-page row embedding at q sends p to the bidegree (p,q).
Its source is the horizontal chain shape down ℕ and its target is the spectral shape of
bidegree (−1,0). -/
@[simp]
theorem horizontalFirstPageRowEmbedding_f (p q : ℕ) :
    (horizontalFirstPageRowEmbedding q).f p = (p, q) :=
  rfl

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. The
degree-p component of the chain isomorphism from the first-page row at q to the
vertical-homology complex is the forward normalized isomorphism E¹_{p,q} → H_q(K_p). It is
(−1)^{p(q+1)} times the coherent first-page comparison. -/
theorem horizontalFirstPageRowComplexIsoVerticalHomologyComplex_hom_f
    (p q : ℕ) :
    (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q).hom.f p =
      (horizontalFirstPageNormalizedVerticalHomologyIso K p q).hom :=
  rfl

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. The
degree-p homology of the first-page row complex at q is canonically isomorphic to the homology
of the full page-one complex at (p,q). The row embedding contains every incoming and outgoing
differential relation at that bidegree, so restricting the complex leaves its homology
unchanged. -/
noncomputable def horizontalFirstPageRowHomologyIso (p q : ℕ) :
    (horizontalFirstPageRowComplex K q).homology p ≅
      ((horizontalFirstQuadrantSpectralSequence K).page 1).homology (p, q) :=
  let E := horizontalFirstPageRowEmbedding q
  let P := (horizontalFirstQuadrantSpectralSequence K).page 1
  P.restrictionHomologyIsoAt E p (E.prev_f rfl) (E.next_f rfl)

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. There is an
isomorphism E²_{p,q} ≅ H_p(K.verticalHomologyComplex q), where the latter complex has objects
H_q(K_a) and horizontal differentials H_q(K.d_{a+1,a}). It first identifies E²_{p,q} with
page-one homology, then with the degree-p homology of the fixed-q row, and finally applies
homology to the row isomorphism normalized by (−1)^{a(q+1)}. -/
noncomputable def horizontalSecondPageVerticalHorizontalHomologyIso
    (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 2).X (p, q) ≅
      (K.verticalHomologyComplex q).homology p :=
  ((horizontalFirstQuadrantSpectralSequence K).iso 1 2 (p, q)).symm ≪≫
    (horizontalFirstPageRowHomologyIso K p q).symm ≪≫
    HomologicalComplex.homologyMapIso
      (horizontalFirstPageRowComplexIsoVerticalHomologyComplex K q) p

end HomologicalComplex₂
