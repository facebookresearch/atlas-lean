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
# The original top-degree brutal truncation as a stock cone

For an original cochain complex `K` zero above `b`, its stock brutal
truncation `L` below `b` is the quotient by the stock single on `K.X b`.
The original terms and differentials determine the projection and the
degreewise splitting. The stock connecting map `L ⟶ single(K.X b,b)⟦1⟧`
retains the literal original last differential through its original charts.

The stock degreewise-split cone isomorphism, shifted by `-1`, reconstructs
the whole original complex `K`. This is the successor presentation for
induction on its finite support.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual stock brutal truncation that removes the top degree `b`. -/
abbrev topCutLower (K : CochainComplex C ℤ) (b : ℤ) : CochainComplex C ℤ :=
  K.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))

/-- The stock single complex on the literal original top term. -/
abbrev topCutSingle (K : CochainComplex C ℤ) (b : ℤ) : CochainComplex C ℤ :=
  (HomologicalComplex.single C (.up ℤ) b).obj (K.X b)

/-- The original term chart of the stock brutal truncation below `b`. -/
def topCutLowerXIso (K : CochainComplex C ℤ) (b j : ℤ) (hj : j < b) :
    (topCutLower K b).X j ≅ K.X j :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntLE (b - 1))
    (show (ComplexShape.embeddingUpIntLE (b - 1)).f (b - 1 - j).toNat = j by
      change b - 1 - ((b - 1 - j).toNat : ℤ) = j
      omega)

/-- The lower brutal truncation is zero in and above the removed degree. -/
theorem topCutLower_isZero_above (K : CochainComplex C ℤ) (b j : ℤ) (hj : b ≤ j) :
    IsZero ((topCutLower K b).X j) :=
  K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE (b - 1)) j
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff (b - 1) j).2 (by omega))

/-- The original lower support is retained by the stock brutal truncation. -/
theorem topCutLower_isZero_outside (K : CochainComplex C ℤ) (a b : ℤ)
    (hK : ∀ j : ℤ, j < a → IsZero (K.X j)) (j : ℤ)
    (hj : j < a ∨ b - 1 < j) : IsZero ((topCutLower K b).X j) := by
  rcases hj with hj | hj
  · by_cases h : j < b
    · exact (hK j hj).of_iso (topCutLowerXIso K b j h)
    · exact topCutLower_isZero_above K b j (by omega)
  · exact topCutLower_isZero_above K b j (by omega)

/-- The lower truncation retains each original differential through the
two actual original truncation charts. -/
theorem topCutLower_d (K : CochainComplex C ℤ) (b i j : ℤ)
    (hi : i < b) (hj : j < b) :
    (topCutLower K b).d i j =
      (topCutLowerXIso K b i hi).hom ≫ K.d i j ≫ (topCutLowerXIso K b j hj).inv := by
  dsimp only [topCutLower, topCutLowerXIso]
  exact K.stupidTrunc_d_eq _ _ _

/-- The actual projection from the original complex to its lower
brutal truncation, using the inverse original term charts. -/
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

/-- Below the removed degree, the projection is its actual original chart. -/
theorem πTopCutLower_f (K : CochainComplex C ℤ) (b j : ℤ) (hj : j < b) :
    (πTopCutLower K b).f j = (topCutLowerXIso K b j hj).inv :=
  dite_eq_left hj

/-- The top-term inclusion is defined by the identity on the literal
original top term, using the original upper-support hypothesis. -/
def topTermInclusion (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) : topCutSingle K b ⟶ K :=
  HomologicalComplex.mkHomFromSingle (𝟙 (K.X b))
    (fun j (hj : b + 1 = j) => (hupper j (by omega)).eq_of_tgt _ _)

/-- At the actual top degree, the inclusion is the stock original single chart. -/
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

/-- The original top term, original complex, and actual lower projection
form the concrete successor short complex. -/
@[no_expose]
def topCutShortComplex (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (topTermInclusion K b hupper) (πTopCutLower K b)
    (topTermInclusion_πTopCutLower K b hupper)

/-- The original top inclusion followed by the original lower projection is zero. -/
theorem topCutZero (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    topTermInclusion K b hupper ≫ πTopCutLower K b = 0 :=
  topTermInclusion_πTopCutLower K b hupper

/-- The whole original short-complex readout retains its literal stock
single, original complex, lower truncation, inclusion, and projection. -/
theorem topCutShortComplex_eq (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    topCutShortComplex K b hupper =
      ShortComplex.mk (topTermInclusion K b hupper) (πTopCutLower K b)
        (topCutZero K b hupper) := by
  dsimp only [topCutShortComplex]

/-- The actual degreewise splitting is earned from the original zero
terms and the original chart isomorphisms. -/
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

/-- The concrete original successor sequence is degreewise split exact. -/
theorem topCutShortComplex_shortExact (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    (topCutShortComplex K b hupper).ShortExact := by
  rw [topCutShortComplex_eq, HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro j
  exact (topCutSplitting K b hupper j).shortExact

/-- The actual stock connecting morphism is constructed from the
original successor sequence and its earned degreewise splitting. -/
def topCutConnecting (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    topCutLower K b ⟶ (topCutSingle K b)⟦(1 : ℤ)⟧ :=
  homOfDegreewiseSplit
    (ShortComplex.mk (topTermInclusion K b hupper) (πTopCutLower K b) (topCutZero K b hupper))
    (topCutSplitting K b hupper)

/-- Every component of the actual connecting map uses the literal
original differential and the earned original degreewise splitting. -/
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

/-- Through the actual original truncation, shift, and single-object
charts, the connecting map contains the literal original last differential. -/
theorem topCutConnecting_last_f (K : CochainComplex C ℤ) (b : ℤ)
    (hupper : ∀ j : ℤ, b < j → IsZero (K.X j)) :
    (topCutConnecting K b hupper).f (b - 1) ≫
        ((topCutSingle K b).shiftFunctorObjXIso 1 (b - 1) b (by omega)).hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) b (K.X b)).hom =
      (topCutLowerXIso K b (b - 1) (by omega)).hom ≫ K.d (b - 1) b :=
  topCutConnecting_last_f_aux K (b - 1) b (by omega) hupper

/-- The actual stock cone of the original connecting map, shifted by
`-1`, is canonically isomorphic to the whole original complex. -/
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
