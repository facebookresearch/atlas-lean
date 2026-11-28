/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.Embedding.StupidTruncInclusion
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Removing a top cochain degree and recovering it by a cone

For an integer-indexed cochain complex K in an abelian category, let L be its brutal
truncation in degrees below b and let A be the single-degree complex on K_b at b. If K is zero
above b, the inclusion A → K and projection K → L give a degreewise split short exact
sequence.

The connecting map δ : L → A[1] has component σ_j.s ≫ d_K(j,j+1) ≫ σ_{j+1}.r. In degree b−1 it
is the last differential d_K(b−1,b) through the truncation, shift and single-degree charts.
The shifted cone Cone(δ)[−1] is canonically isomorphic to K. All integer degrees and the
category object and morphism universes remain as stated.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Brutal truncation below a chosen top degree.

For K and b ∈ ℤ, retain the degrees j < b using stupid truncation along the embedding up to
b−1. -/
abbrev topCutLower (K : CochainComplex C ℤ) (b : ℤ) : CochainComplex C ℤ :=
  K.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))

/-- The single complex on the chosen top term.

Place K_b in cochain degree b and zero in every other degree. -/
abbrev topCutSingle (K : CochainComplex C ℤ) (b : ℤ) : CochainComplex C ℤ :=
  (HomologicalComplex.single C (.up ℤ) b).obj (K.X b)

/-- The truncation chart in a retained degree.

For j < b, the degree-j object of topCutLower K b is canonically isomorphic to K_j. -/
def topCutLowerXIso (K : CochainComplex C ℤ) (b j : ℤ) (hj : j < b) :
    (topCutLower K b).X j ≅ K.X j :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntLE (b - 1))
    (show (ComplexShape.embeddingUpIntLE (b - 1)).f (b - 1 - j).toNat = j by
      change b - 1 - ((b - 1 - j).toNat : ℤ) = j
      omega)

/-- The lower truncation vanishes at and above the cut.

For b ≤ j, the degree-j object of topCutLower K b is zero. -/
theorem topCutLower_isZero_above (K : CochainComplex C ℤ) (b j : ℤ) (hj : b ≤ j) :
    IsZero ((topCutLower K b).X j) :=
  K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE (b - 1)) j
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff (b - 1) j).2 (by omega))

/-- Support of a lower truncation with a lower bound.

If K is zero below a, its truncation below b is zero whenever j < a or j > b−1. -/
theorem topCutLower_isZero_outside (K : CochainComplex C ℤ) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a → IsZero (K.X j)) (j : ℤ)
    (hj : j < a ∨ b - 1 < j) : IsZero ((topCutLower K b).X j) := by
  rcases hj with hj | hj
  · by_cases h : j < b
    · exact (hK j hj).of_iso (topCutLowerXIso K b j h)
    · exact topCutLower_isZero_above K b j (by omega)
  · exact topCutLower_isZero_above K b j (by omega)

/-- The differential in retained truncation degrees.

For i,j < b, the truncated differential is the original K.d i j conjugated by the truncation
charts at i and j. -/
theorem topCutLower_d (K : CochainComplex C ℤ) (b i j : ℤ)
    (hi : i < b) (hj : j < b) :
    (topCutLower K b).d i j =
      (topCutLowerXIso K b i hi).hom ≫ K.d i j ≫ (topCutLowerXIso K b j hj).inv := by
  dsimp only [topCutLower, topCutLowerXIso]
  exact K.stupidTrunc_d_eq _ _ _

/-- The projection onto the lower brutal truncation.

In degree j < b, use the inverse truncation chart K_j → L_j; at and above b, use zero. These
components form a cochain map. -/
def πTopCutLower (K : CochainComplex C ℤ) (b : ℤ) : K ⟶ topCutLower K b where
  f j := if hj : j < b then (topCutLowerXIso K b j hj).inv else 0
  comm' i j hij := by
    by_cases hj : j < b
    · have hi : i < b := by
        have h : i + 1 = j := hij
        omega
      simp only [dite_eq_left hi, dite_eq_left hj]
      rw [topCutLower_d K b i j hi hj]
      simp only [Iso.inv_hom_id_assoc]
    · exact (topCutLower_isZero_above K b j (by omega)).eq_of_tgt _ _

/-- The projection component below the cut.

For j < b, the degree-j projection onto topCutLower K b is the inverse of its object chart
with K_j. -/
theorem πTopCutLower_f (K : CochainComplex C ℤ) (b j : ℤ) (hj : j < b) :
    (πTopCutLower K b).f j = (topCutLowerXIso K b j hj).inv :=
  dite_eq_left hj

/-- The inclusion of the top single term.

If K is zero above b, the identity on K_b extends to a cochain map from the single complex on
K_b in degree b to K. -/
def topTermInclusion (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) : topCutSingle K b ⟶ K :=
  HomologicalComplex.mkHomFromSingle (𝟙 (K.X b))
    (fun j (hj : b + 1 = j) => (hupper j (by omega)).eq_of_tgt _ _)

/-- The top-degree component of the single-term inclusion.

In degree b, the inclusion is the canonical chart from the single complex's degree-b object to
K_b. -/
theorem topTermInclusion_f (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    (topTermInclusion K b hupper).f b =
      (HomologicalComplex.singleObjXSelf (.up ℤ) b (K.X b)).hom := by
  dsimp only [topTermInclusion]
  exact (HomologicalComplex.mkHomFromSingle_f _ _).trans (Category.comp_id _)

private theorem topTermInclusion_πTopCutLower (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    topTermInclusion K b hupper ≫ πTopCutLower K b = 0 := by
  refine HomologicalComplex.hom_ext _ _ (fun j => ?_)
  change (topTermInclusion K b hupper).f j ≫ (πTopCutLower K b).f j = 0
  by_cases hj : j < b
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) b (K.X b) j (by omega)).eq_of_src _ _
  · exact (topCutLower_isZero_above K b j (by omega)).eq_of_tgt _ _

/-- The short complex obtained by removing the top degree.

For K zero above b, form the short complex A → K → L from the top-term inclusion and lower-
truncation projection. -/
@[no_expose]
def topCutShortComplex (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (topTermInclusion K b hupper) (πTopCutLower K b)
    (topTermInclusion_πTopCutLower K b hupper)

/-- The top-term inclusion followed by truncation is zero.

For K zero above b, the composite from the single top term through K to its lower truncation
is zero. -/
theorem topCutZero (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    topTermInclusion K b hupper ≫ πTopCutLower K b = 0 :=
  topTermInclusion_πTopCutLower K b hupper

/-- The maps defining the top-degree short complex.

The short complex consists of topTermInclusion and πTopCutLower with their zero-composite
relation. -/
theorem topCutShortComplex_eq (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    topCutShortComplex K b hupper =
      ShortComplex.mk (topTermInclusion K b hupper) (πTopCutLower K b)
        (topCutZero K b hupper) := by
  dsimp only [topCutShortComplex]

/-- The degreewise splitting of the top-degree short complex.

For each j, the evaluated sequence A_j → K_j → L_j has the splitting determined by its
truncation and single-term charts, under the upper-zero hypothesis. -/
def topCutSplitting (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) (j : ℤ) :
    ((ShortComplex.mk (topTermInclusion K b hupper) (πTopCutLower K b)
      (topCutZero K b hupper)).map (HomologicalComplex.eval C (.up ℤ) j)).Splitting := by
  by_cases hj : j < b
  · refine ShortComplex.Splitting.ofIsZeroOfIsIso _
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) b (K.X b) j (by omega)) ?_
    change IsIso ((πTopCutLower K b).f j)
    rw [πTopCutLower_f K b j hj]
    infer_instance
  · refine ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_
      (topCutLower_isZero_above K b j (by omega))
    change IsIso ((topTermInclusion K b hupper).f j)
    by_cases h : j = b
    · subst j
      rw [topTermInclusion_f]
      infer_instance
    · exact IsZero.isIso
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) b (K.X b) j h)
        (hupper j (by omega)) ((topTermInclusion K b hupper).f j)

/-- Exactness of the top-degree short complex.

For K zero above b, the sequence single(K_b,b) → K → topCutLower K b is short exact in the
category of cochain complexes. -/
theorem topCutShortComplex_shortExact (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    (topCutShortComplex K b hupper).ShortExact := by
  rw [topCutShortComplex_eq, HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro j
  exact (topCutSplitting K b hupper j).shortExact

/-- The connecting map determined by the degreewise splitting.

The degreewise split top-term sequence gives a cochain map from the lower truncation L to the
shifted single-term complex A[1]. -/
def topCutConnecting (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    topCutLower K b ⟶ (topCutSingle K b)⟦(1 : ℤ)⟧ :=
  homOfDegreewiseSplit
    (ShortComplex.mk (topTermInclusion K b hupper) (πTopCutLower K b) (topCutZero K b hupper))
    (topCutSplitting K b hupper)

/-- The component formula of the top-cut connecting map.

The component at j is the section of the splitting at j, followed by K.d j (j+1), followed by
the retraction at j+1. -/
theorem topCutConnecting_f (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) (j : ℤ) :
    (topCutConnecting K b hupper).f j =
      (topCutSplitting K b hupper j).s ≫ K.d j (j + 1) ≫
        (topCutSplitting K b hupper (j + 1)).r := by
  dsimp only [topCutConnecting]
  rw [homOfDegreewiseSplit_f]
  rfl

private theorem topCutConnecting_last_f_aux (K : CochainComplex C ℤ) (p b : ℤ)
    (hp : p + 1 = b) (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    (topCutConnecting K b hupper).f p ≫
        ((topCutSingle K b).shiftFunctorObjXIso 1 p b hp.symm).hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) b (K.X b)).hom =
      (topCutLowerXIso K b p (by omega)).hom ≫ K.d p b := by
  subst b
  let σ := topCutSplitting K (p + 1) hupper
  let t := topCutLowerXIso K (p + 1) p (by omega)
  let s := HomologicalComplex.singleObjXSelf (.up ℤ) (p + 1) (K.X (p + 1))
  have hs : (σ p).s = t.hom := by
    have h := (σ p).s_g
    change (σ p).s ≫ (πTopCutLower K (p + 1)).f p = 𝟙 _ at h
    rw [πTopCutLower_f K (p + 1) p (by omega)] at h
    exact (cancel_mono t.inv).1 (h.trans t.hom_inv_id.symm)
  have hr : (σ (p + 1)).r = s.inv := by
    have h := (σ (p + 1)).f_r
    change (topTermInclusion K (p + 1) hupper).f (p + 1) ≫ (σ (p + 1)).r = 𝟙 _ at h
    rw [topTermInclusion_f] at h
    exact (cancel_epi s.hom).1 (h.trans s.hom_inv_id.symm)
  rw [topCutConnecting_f]
  change ((σ p).s ≫ K.d p (p + 1) ≫ (σ (p + 1)).r) ≫
      ((topCutSingle K (p + 1)).XIsoOfEq rfl).hom ≫ s.hom = t.hom ≫ K.d p (p + 1)
  rw [hs, hr]
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.assoc]
  have htail : s.inv ≫ (𝟙 ((topCutSingle K (p + 1)).X (p + 1)) ≫ s.hom) =
      𝟙 (K.X (p + 1)) :=
    (congrArg (fun f => s.inv ≫ f) (Category.id_comp s.hom)).trans s.inv_hom_id
  simpa only [Category.assoc, Category.comp_id] using
    congrArg (fun f => t.hom ≫ K.d p (p + 1) ≫ f) htail

/-- The connecting map retains the last cochain differential.

In degree b−1, composing the connecting component with the canonical shift and single-term
charts gives the truncation chart followed by K.d (b−1) b. -/
theorem topCutConnecting_last_f (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    (topCutConnecting K b hupper).f (b - 1) ≫
        ((topCutSingle K b).shiftFunctorObjXIso 1 (b - 1) b (by omega)).hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) b (K.X b)).hom =
      (topCutLowerXIso K b (b - 1) (by omega)).hom ≫ K.d (b - 1) b :=
  topCutConnecting_last_f_aux K (b - 1) b (by omega) hupper

/-- Recovery of the cochain complex from the shifted connecting cone.

For K zero above b, the mapping cone of topCutConnecting K b, shifted by −1, is canonically
isomorphic to K. -/
def topCutConeIso (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    (mappingCone (topCutConnecting K b hupper))⟦(-1 : ℤ)⟧ ≅ K := by
  let S := ShortComplex.mk (topTermInclusion K b hupper) (πTopCutLower K b) (topCutZero K b hupper)
  let σ := topCutSplitting K b hupper
  let E : mappingCone (topCutConnecting K b hupper) ≅ K⟦(1 : ℤ)⟧ :=
    mappingConeHomOfDegreewiseSplitIso S σ
  exact (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1)).mapIso E ≪≫
    (shiftEquiv (CochainComplex C ℤ) (1 : ℤ)).unitIso.symm.app K

end CochainComplex

end
