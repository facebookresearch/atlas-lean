/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module


public import MathlibExt.Algebra.Homology.PartialTotalNested
public import MathlibExt.Algebra.Homology.PartialTotalCoordinates
public import MathlibExt.Algebra.Homology.PartialTotalRow
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Successor quotients of first-coordinate partial totals

The quotient of the partial total through row `p` by its predecessor stage is
the signed `p`th row placed in total degree.  This file constructs the
quotient map, proves its naturality, and packages the successor filtration
step as a degreewise split short complex.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

local instance : HasBinaryBiproducts C :=
  hasBinaryBiproducts_of_finite_biproducts C

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- A retained row of a first-coordinate stupid truncation, indexed by its
exact initial-segment witness. -/
noncomputable def partialTotalRowIsoAt (p : ℕ) (i : Fin (p + 1)) :
    (B.firstStupidTrunc p).X i.1 ≅ B.X i.1 :=
  B.stupidTruncXIso (ComplexShape.embeddingDownNatInitialSegment p)
    (i := i) rfl

/-- A retained row of a first-coordinate stupid truncation, identified with
the corresponding row of the original bicomplex. -/
noncomputable def partialTotalRowIso (p i : ℕ) (h : i ≤ p) :
    (B.firstStupidTrunc p).X i ≅ B.X i :=
  B.partialTotalRowIsoAt p ⟨i, by omega⟩

/-- The last retained row of the first-coordinate stupid truncation, identified
with the corresponding row of the original bicomplex. -/
noncomputable def partialTotalLastRowIso (p : ℕ) :
    (B.firstStupidTrunc p).X p ≅ B.X p :=
  B.stupidTruncXIso (ComplexShape.embeddingDownNatInitialSegment p)
    (i := ⟨p, Nat.lt_succ_self p⟩) rfl

/-- In total degree `n`, the projection from the partial total through row
`p` onto its last signed row. -/
noncomputable def partialTotalRowQuotientF (p n : ℕ) :
    ((B.firstStupidTrunc p).total (ComplexShape.down ℕ)).X n ⟶
      (B.totalRow p).X n :=
  (B.firstStupidTrunc p).totalDesc fun i j h ↦
    if hi : i = p then
      by
        subst i
        exact (B.partialTotalLastRowIso p).hom.f j ≫
          (B.totalRowXIso p j n h).inv
    else 0

section Quotient

set_option backward.isDefEq.respectTransparency false

/-- The last-row projection on the retained row. -/
@[reassoc (attr := simp)]
theorem ιTotal_partialTotalRowQuotientF (p j n : ℕ) (h : p + j = n) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) p j n h ≫
        B.partialTotalRowQuotientF p n =
      (B.partialTotalLastRowIso p).hom.f j ≫
        (B.totalRowXIso p j n h).inv := by
  rw [partialTotalRowQuotientF, HomologicalComplex₂.ι_totalDesc]
  dsimp
  exact ite_eq_left rfl

/-- The last-row projection vanishes on every other row. -/
@[reassoc (attr := simp)]
theorem ιTotal_partialTotalRowQuotientF_eq_zero (p i j n : ℕ)
    (h : i + j = n) (hi : i ≠ p) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) i j n h ≫
        B.partialTotalRowQuotientF p n = 0 := by
  rw [partialTotalRowQuotientF, HomologicalComplex₂.ι_totalDesc]
  dsimp
  rw [dite_eq_right hi]

/-- The inclusion of a possibly mismatched total summand followed by the
last-row projection is zero away from the last row. -/
theorem ιTotalOrZero_partialTotalRowQuotientF_eq_zero (p i j n : ℕ)
    (hi : i ≠ p) :
    (B.firstStupidTrunc p).ιTotalOrZero
        (ComplexShape.down ℕ) i j n ≫
      B.partialTotalRowQuotientF p n = 0 := by
  by_cases h : i + j = n
  · rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h,
      B.ιTotal_partialTotalRowQuotientF_eq_zero p i j n h hi]
  · rw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h,
      zero_comp]

/-- Every horizontal differential is killed by the last-row projection. -/
theorem d₁_partialTotalRowQuotientF_eq_zero (p i j n : ℕ) :
    (B.firstStupidTrunc p).d₁ (ComplexShape.down ℕ) i j n ≫
      B.partialTotalRowQuotientF p n = 0 := by
  by_cases hi : i ≤ p
  · by_cases hrel : (ComplexShape.down ℕ).Rel i
        ((ComplexShape.down ℕ).next i)
    · have hnext : (ComplexShape.down ℕ).next i ≠ p := by
        intro heq
        change (ComplexShape.down ℕ).next i + 1 = i at hrel
        omega
      rw [HomologicalComplex₂.d₁_eq'
        (B.firstStupidTrunc p) (ComplexShape.down ℕ) hrel j n,
        Linear.units_smul_comp, Category.assoc,
        B.ιTotalOrZero_partialTotalRowQuotientF_eq_zero
          p ((ComplexShape.down ℕ).next i) j n hnext,
        comp_zero, smul_zero]
    · rw [HomologicalComplex₂.d₁_eq_zero
        (B.firstStupidTrunc p) (ComplexShape.down ℕ) i j n hrel,
        zero_comp]
  · have hzero : IsZero (((B.firstStupidTrunc p).X i).X j) := by
      apply (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero
      apply B.isZero_stupidTrunc_X
        (ComplexShape.embeddingDownNatInitialSegment p)
      intro a ha
      change a.1 = i at ha
      omega
    exact hzero.eq_of_src _ _

/-- Away from the last row, every vertical differential is killed by the
last-row projection. -/
theorem d₂_partialTotalRowQuotientF_eq_zero (p i j n : ℕ) (hi : i ≠ p) :
    (B.firstStupidTrunc p).d₂ (ComplexShape.down ℕ) i j n ≫
      B.partialTotalRowQuotientF p n = 0 := by
  by_cases hip : i ≤ p
  · by_cases hrel : (ComplexShape.down ℕ).Rel j
        ((ComplexShape.down ℕ).next j)
    · rw [HomologicalComplex₂.d₂_eq'
        (B.firstStupidTrunc p) (ComplexShape.down ℕ) i hrel n,
        Linear.units_smul_comp, Category.assoc,
        B.ιTotalOrZero_partialTotalRowQuotientF_eq_zero
          p i ((ComplexShape.down ℕ).next j) n hi,
        comp_zero, smul_zero]
    · rw [HomologicalComplex₂.d₂_eq_zero
        (B.firstStupidTrunc p) (ComplexShape.down ℕ) i j n hrel,
        zero_comp]
  · have hzero : IsZero (((B.firstStupidTrunc p).X i).X j) := by
      apply (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero
      apply B.isZero_stupidTrunc_X
        (ComplexShape.embeddingDownNatInitialSegment p)
      intro a ha
      change a.1 = i at ha
      omega
    exact hzero.eq_of_src _ _

/-- On the last row, the surviving vertical differential agrees with the
signed row differential. -/
theorem d₂_partialTotalRowQuotientF (p r n : ℕ) (h : p + r = n) :
    (B.firstStupidTrunc p).d₂ (ComplexShape.down ℕ) p (r + 1) n ≫
        B.partialTotalRowQuotientF p n =
      (B.partialTotalLastRowIso p).hom.f (r + 1) ≫
        ((ComplexShape.down ℕ).ε p • (B.X p).d (r + 1) r) ≫
        (B.totalRowXIso p r n h).inv := by
  rw [HomologicalComplex₂.d₂_eq
      (B.firstStupidTrunc p) (ComplexShape.down ℕ) p
      (show (ComplexShape.down ℕ).Rel (r + 1) r from rfl) n h,
    Linear.units_smul_comp, Category.assoc,
    B.ιTotal_partialTotalRowQuotientF p r n h]
  have heps : (ComplexShape.down ℕ).ε₂ (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, r + 1) = (ComplexShape.down ℕ).ε p := rfl
  rw [heps]
  apply (cancel_mono (B.totalRowXIso p r n h).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Linear.units_smul_comp, Linear.comp_units_smul]
  rw [(B.partialTotalLastRowIso p).hom.comm]

/-- The canonical quotient from the partial total through row `p` to its
last signed row. -/
noncomputable def partialTotalRowQuotient (p : ℕ) :
    B.partialTotal p ⟶ B.totalRow p where
  f n := B.partialTotalRowQuotientF p n
  comm' n n' hnn' := by
    change B.partialTotalRowQuotientF p n ≫ (B.totalRow p).d n n' =
      ((B.firstStupidTrunc p).total (ComplexShape.down ℕ)).d n n' ≫
        B.partialTotalRowQuotientF p n'
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    by_cases hip : i = p
    · subst i
      cases j with
      | zero =>
          have hn : n = p := by
            change p + 0 = n at hij
            omega
          have hn' : n' < p := by
            change n' + 1 = n at hnn'
            omega
          have hz := B.totalRow_isZero_X p n' hn'
          have hd : (B.totalRowXIso p 0 n (by omega)).inv ≫
              (B.totalRow p).d n n' = 0 := hz.eq_of_tgt _ _
          rw [← Category.assoc,
            B.ιTotal_partialTotalRowQuotientF p 0 n (by omega),
            Category.assoc, hd, comp_zero]
          rw [HomologicalComplex₂.total_d, Preadditive.add_comp,
            Preadditive.comp_add,
            HomologicalComplex₂.ι_D₁_assoc,
            HomologicalComplex₂.ι_D₂_assoc,
            B.d₁_partialTotalRowQuotientF_eq_zero p p 0 n',
            HomologicalComplex₂.d₂_eq_zero
              (B.firstStupidTrunc p) (ComplexShape.down ℕ) p 0 n'
              (by simp), zero_comp, add_zero]
      | succ r =>
          have hn : p + (r + 1) = n := by
            change p + (r + 1) = n at hij
            exact hij
          have hn' : p + r = n' := by
            change n' + 1 = n at hnn'
            omega
          rw [← Category.assoc,
            B.ιTotal_partialTotalRowQuotientF p (r + 1) n hn,
            Category.assoc,
            B.totalRowXIso_inv_comp_d p (r + 1) r n n' hn hn']
          rw [HomologicalComplex₂.total_d, Preadditive.add_comp,
            Preadditive.comp_add,
            HomologicalComplex₂.ι_D₁_assoc,
            HomologicalComplex₂.ι_D₂_assoc,
            B.d₁_partialTotalRowQuotientF_eq_zero p p (r + 1) n',
            B.d₂_partialTotalRowQuotientF p r n' hn', zero_add]
    · by_cases hi : i ≤ p
      · rw [← Category.assoc,
          B.ιTotal_partialTotalRowQuotientF_eq_zero p i j n hij hip,
          zero_comp]
        rw [HomologicalComplex₂.total_d, Preadditive.add_comp,
          Preadditive.comp_add,
          HomologicalComplex₂.ι_D₁_assoc,
          HomologicalComplex₂.ι_D₂_assoc,
          B.d₁_partialTotalRowQuotientF_eq_zero p i j n',
          B.d₂_partialTotalRowQuotientF_eq_zero p i j n' hip,
          zero_add]
      · have hzero : IsZero (((B.firstStupidTrunc p).X i).X j) := by
          apply (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero
          apply B.isZero_stupidTrunc_X
            (ComplexShape.embeddingDownNatInitialSegment p)
          intro a ha
          change a.1 = i at ha
          omega
        exact hzero.eq_of_src _ _

/-- The quotient chain map on the retained last row. -/
@[reassoc (attr := simp)]
theorem ιTotal_partialTotalRowQuotient (p j n : ℕ) (h : p + j = n) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) p j n h ≫
        (B.partialTotalRowQuotient p).f n =
      (B.partialTotalLastRowIso p).hom.f j ≫
        (B.totalRowXIso p j n h).inv :=
  B.ιTotal_partialTotalRowQuotientF p j n h

/-- The quotient chain map vanishes on every row other than its last row. -/
@[reassoc (attr := simp)]
theorem ιTotal_partialTotalRowQuotient_eq_zero (p i j n : ℕ)
    (h : i + j = n) (hi : i ≠ p) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) i j n h ≫
        (B.partialTotalRowQuotient p).f n = 0 :=
  B.ιTotal_partialTotalRowQuotientF_eq_zero p i j n h hi

set_option backward.isDefEq.respectTransparency false in
/-- On the last retained row, the partial-total coordinate followed by the
successor quotient is the native signed-row coordinate. -/
@[reassoc]
theorem partialTotalComponent_comp_partialTotalRowQuotient
    (p j n : ℕ) (hn : p + j = n) :
    B.partialTotalComponent p ⟨p, Nat.lt_succ_self p⟩ j n hn ≫
        (B.partialTotalRowQuotient p).f n =
      (B.totalRowXIso p j n hn).inv := by
  unfold partialTotalComponent partialTotalRowQuotient
  dsimp only
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [B.ιTotal_partialTotalRowQuotientF p j n hn]
  change (B.partialTotalLastRowIso p).inv.f j ≫
      (B.partialTotalLastRowIso p).hom.f j ≫
        (B.totalRowXIso p j n hn).inv = _
  have hid := HomologicalComplex.congr_hom
    (Iso.inv_hom_id (B.partialTotalLastRowIso p)) j
  have hId : ((𝟙 (B.X p) : B.X p ⟶ B.X p).f j) = 𝟙 _ := rfl
  simpa only [HomologicalComplex.comp_f, Category.assoc, hId,
    Category.id_comp] using congrArg
      (fun k => k ≫ (B.totalRowXIso p j n hn).inv) hid

set_option backward.isDefEq.respectTransparency false in
/-- Every retained coordinate away from the last row is killed by the
successor quotient. -/
@[reassoc (attr := simp)]
theorem partialTotalComponent_comp_partialTotalRowQuotient_eq_zero
    (p : ℕ) (i : Fin (p + 1)) (j n : ℕ) (hn : i.1 + j = n)
    (hi : i.1 ≠ p) :
    B.partialTotalComponent p i j n hn ≫
        (B.partialTotalRowQuotient p).f n = 0 := by
  unfold partialTotalComponent partialTotalRowQuotient
  dsimp only
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [B.ιTotal_partialTotalRowQuotientF_eq_zero p i.1 j n hn hi,
    comp_zero]



variable {B}
variable {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Naturality of the last-row truncation coordinate isomorphism, evaluated
in a vertical degree. -/
theorem stupidTruncMap_partialTotalLastRowIso_hom_f
    (φ : B ⟶ B') (p j : ℕ) :
    (((HomologicalComplex.stupidTruncMap φ
        (ComplexShape.embeddingDownNatInitialSegment p)).f p).f j) ≫
        (B'.partialTotalLastRowIso p).hom.f j =
      (B.partialTotalLastRowIso p).hom.f j ≫ (φ.f p).f j := by
  have h := HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom φ
    (ComplexShape.embeddingDownNatInitialSegment p)
    (i := ⟨p, Nat.lt_succ_self p⟩) rfl
  exact congrArg (fun f ↦ f.f j) h

/-- The last-row quotient is natural in morphisms of bicomplexes. -/
@[reassoc]
theorem partialTotalRowQuotient_naturality (φ : B ⟶ B') (p : ℕ) :
    B.partialTotalHom φ p ≫ B'.partialTotalRowQuotient p =
      B.partialTotalRowQuotient p ≫ totalRowMap φ p := by
  apply B.partialTotal_hom_ext p
  intro i j n hij
  simp only [HomologicalComplex.comp_f]
  rw [B.partialTotalComponent_naturality_assoc φ]
  by_cases hi : i.1 = p
  · have hi' : i = ⟨p, Nat.lt_succ_self p⟩ := by
      apply Fin.ext
      exact hi
    subst i
    rw [B'.partialTotalComponent_comp_partialTotalRowQuotient,
      B.partialTotalComponent_comp_partialTotalRowQuotient_assoc,
      totalRowMap_f φ p j n hij]
    simp only [Iso.inv_hom_id_assoc]
  · rw [B'.partialTotalComponent_comp_partialTotalRowQuotient_eq_zero
        p i j n hij hi,
      comp_zero, ← Category.assoc,
      B.partialTotalComponent_comp_partialTotalRowQuotient_eq_zero
        p i j n hij hi,
      zero_comp]


variable (B)

/-- A successor filtration map followed by projection to the new last row is
zero. -/
@[reassoc (attr := simp)]
theorem partialTotalMap_comp_partialTotalRowQuotient (m : ℕ) :
    B.partialTotalMap (Nat.le_succ m) ≫
      B.partialTotalRowQuotient (m + 1) = 0 := by
  ext n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    partialTotalRowQuotient]
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  rw [comp_zero]
  by_cases hi : i ≤ m
  · let a : Fin (m + 1) := ⟨i, by omega⟩
    have hmap := B.ιTotal_partialTotalMap (Nat.le_succ m) a j n hij
    change (B.firstStupidTrunc m).ιTotal
        (ComplexShape.down ℕ) i j n hij ≫
      ((B.partialTotalMap (Nat.le_succ m)).f n ≫
        (B.partialTotalRowQuotientF (m + 1) n)) = 0
    rw [← Category.assoc, hmap, Category.assoc,
      B.ιTotal_partialTotalRowQuotientF_eq_zero
        (m + 1) i j n hij (by omega), comp_zero]
  · have hzero : IsZero (((B.firstStupidTrunc m).X i).X j) := by
      apply (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero
      apply B.isZero_stupidTrunc_X
        (ComplexShape.embeddingDownNatInitialSegment m)
      intro a ha
      change a.1 = i at ha
      omega
    exact hzero.eq_of_src _ _

/-- The short complex formed by two consecutive partial-total stages and the
new signed row. -/
noncomputable def partialTotalSuccShortComplex (m : ℕ) :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (B.partialTotalMap (Nat.le_succ m))
    (B.partialTotalRowQuotient (m + 1))
    (B.partialTotalMap_comp_partialTotalRowQuotient m)

/-- The raw degree component of a successor filtration inclusion. -/
noncomputable def partialTotalSuccInclusionF (m n : ℕ) :
    ((B.firstStupidTrunc m).total (ComplexShape.down ℕ)).X n ⟶
      ((B.firstStupidTrunc (m + 1)).total (ComplexShape.down ℕ)).X n :=
  (B.partialTotalMap (Nat.le_succ m)).f n

/-- On an old row, the successor filtration inclusion is the hom of this
coordinate isomorphism. -/
noncomputable def partialTotalSuccOldRowIso (m : ℕ) (i : Fin (m + 1)) :
    (B.firstStupidTrunc m).X i.1 ≅
      (B.firstStupidTrunc (m + 1)).X i.1 :=
  B.partialTotalRowIsoAt m i ≪≫
    (B.stupidTruncXIso
      (ComplexShape.embeddingDownNatInitialSegment (m + 1))
      (i := (ComplexShape.downNatInitialSegmentEmbedding
        (Nat.le_succ m)).f i)
      (ComplexShape.downNatInitialSegmentEmbedding_f_embedding_f
        (Nat.le_succ m) i)).symm

/-- Formula for a successor filtration inclusion on an old retained row. -/
@[reassoc (attr := simp)]
theorem ιTotal_partialTotalSuccInclusionF (m : ℕ) (i : Fin (m + 1))
    (j n : ℕ) (h : i.1 + j = n) :
    (B.firstStupidTrunc m).ιTotal
        (ComplexShape.down ℕ) i.1 j n h ≫
      B.partialTotalSuccInclusionF m n =
    (B.partialTotalSuccOldRowIso m i).hom.f j ≫
      (B.firstStupidTrunc (m + 1)).ιTotal
        (ComplexShape.down ℕ) i.1 j n h := by
  simpa only [partialTotalSuccInclusionF, partialTotalSuccOldRowIso,
    partialTotalRowIsoAt, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.comp_f, Nat.succ_eq_add_one] using
      B.ιTotal_partialTotalMap (Nat.le_succ m) i j n h

/-- In a fixed total degree, retract the successor partial-total stage onto
its predecessor stage by discarding the new last row. -/
noncomputable def partialTotalSuccRetractionF (m n : ℕ) :
    ((B.firstStupidTrunc (m + 1)).total (ComplexShape.down ℕ)).X n ⟶
      ((B.firstStupidTrunc m).total (ComplexShape.down ℕ)).X n :=
  (B.firstStupidTrunc (m + 1)).totalDesc fun i j h ↦
    if hi : i ≤ m then
      (B.partialTotalSuccOldRowIso m ⟨i, by omega⟩).inv.f j ≫
        (B.firstStupidTrunc m).ιTotal (ComplexShape.down ℕ) i j n h
    else 0

/-- The predecessor retraction on a retained old row. -/
@[reassoc (attr := simp)]
theorem ιTotal_partialTotalSuccRetractionF (m : ℕ) (i : Fin (m + 1))
    (j n : ℕ) (h : i.1 + j = n) :
    (B.firstStupidTrunc (m + 1)).ιTotal
        (ComplexShape.down ℕ) i.1 j n h ≫
      B.partialTotalSuccRetractionF m n =
    (B.partialTotalSuccOldRowIso m i).inv.f j ≫
      (B.firstStupidTrunc m).ιTotal
        (ComplexShape.down ℕ) i.1 j n h := by
  rw [partialTotalSuccRetractionF, HomologicalComplex₂.ι_totalDesc]
  rw [dite_eq_left (Nat.le_of_lt_succ i.2)]

/-- The predecessor retraction vanishes on the new row and on all rows above
it. -/
@[reassoc (attr := simp)]
theorem ιTotal_partialTotalSuccRetractionF_eq_zero (m i j n : ℕ)
    (h : i + j = n) (hi : ¬ i ≤ m) :
    (B.firstStupidTrunc (m + 1)).ιTotal
        (ComplexShape.down ℕ) i j n h ≫
      B.partialTotalSuccRetractionF m n = 0 := by
  rw [partialTotalSuccRetractionF, HomologicalComplex₂.ι_totalDesc]
  rw [dite_eq_right hi]

/-- In a fixed total degree, include the signed last row back into the chosen
partial-total coproduct. -/
noncomputable def partialTotalRowQuotientSectionF (p n : ℕ) :
    (B.totalRow p).X n ⟶
      ((B.firstStupidTrunc p).total (ComplexShape.down ℕ)).X n :=
  if hpn : p ≤ n then
    (B.totalRowXIso p (n - p) n (Nat.add_sub_of_le hpn)).hom ≫
      (B.partialTotalLastRowIso p).inv.f (n - p) ≫
      (B.firstStupidTrunc p).ιTotal
        (ComplexShape.down ℕ) p (n - p) n (Nat.add_sub_of_le hpn)
  else 0

/-- Formula for the section of the last-row quotient in a degree belonging
to the shifted row. -/
theorem partialTotalRowQuotientSectionF_eq (p q n : ℕ) (h : p + q = n) :
    B.partialTotalRowQuotientSectionF p n =
      (B.totalRowXIso p q n h).hom ≫
        (B.partialTotalLastRowIso p).inv.f q ≫
        (B.firstStupidTrunc p).ιTotal
          (ComplexShape.down ℕ) p q n h := by
  have hpn : p ≤ n := by omega
  rw [partialTotalRowQuotientSectionF, dite_eq_left hpn]
  have hq : n - p = q := by omega
  subst q
  rfl

/-- The chosen inclusion of the last row is a section of the quotient in
each total degree. -/
theorem partialTotalRowQuotientSectionF_comp_quotientF (p n : ℕ) :
    B.partialTotalRowQuotientSectionF p n ≫
      B.partialTotalRowQuotientF p n = 𝟙 _ := by
  by_cases h : p ≤ n
  · let q := n - p
    have hn : p + q = n := Nat.add_sub_of_le h
    rw [B.partialTotalRowQuotientSectionF_eq p q n hn,
      Category.assoc, Category.assoc,
      B.ιTotal_partialTotalRowQuotientF p q n hn]
    have ha := congrArg (fun f ↦ f.f q)
      (B.partialTotalLastRowIso p).inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at ha
    rw [← Category.assoc
      ((B.partialTotalLastRowIso p).inv.f q)
      ((B.partialTotalLastRowIso p).hom.f q)
      (B.totalRowXIso p q n hn).inv,
      ha, Category.id_comp, Iso.hom_inv_id]
  · exact (B.totalRow_isZero_X p n (by omega)).eq_of_src _ _

/-- The successor filtration inclusion followed by the degreewise
predecessor retraction is the identity. -/
theorem partialTotalMap_f_comp_partialTotalSuccRetractionF (m n : ℕ) :
    B.partialTotalSuccInclusionF m n ≫
      B.partialTotalSuccRetractionF m n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  by_cases hi : i ≤ m
  · let a : Fin (m + 1) := ⟨i, by omega⟩
    have ha := congrArg (fun f ↦ f.f j)
      (B.partialTotalSuccOldRowIso m a).hom_inv_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at ha
    rw [← Category.assoc,
      B.ιTotal_partialTotalSuccInclusionF m a j n hij,
      Category.assoc,
      B.ιTotal_partialTotalSuccRetractionF m a j n hij]
    rw [← Category.assoc
      ((B.partialTotalSuccOldRowIso m a).hom.f j)
      ((B.partialTotalSuccOldRowIso m a).inv.f j)
      ((B.firstStupidTrunc m).ιTotal
        (ComplexShape.down ℕ) i j n hij),
      ha, Category.id_comp, Category.comp_id]
  · have hzero : IsZero (((B.firstStupidTrunc m).X i).X j) := by
      apply (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero
      apply B.isZero_stupidTrunc_X
        (ComplexShape.embeddingDownNatInitialSegment m)
      intro a ha
      change a.1 = i at ha
      omega
    exact hzero.eq_of_src _ _

/-- In every total degree, the predecessor coordinate and the new-row
coordinate sum to the identity of the successor stage. -/
theorem partialTotalSuccRetractionF_comp_map_f_add_quotientF_comp_sectionF
    (m n : ℕ) :
    B.partialTotalSuccRetractionF m n ≫
        B.partialTotalSuccInclusionF m n +
      B.partialTotalRowQuotientF (m + 1) n ≫
        B.partialTotalRowQuotientSectionF (m + 1) n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  by_cases hi : i ≤ m
  · let a : Fin (m + 1) := ⟨i, by omega⟩
    have ha := congrArg (fun f ↦ f.f j)
      (B.partialTotalSuccOldRowIso m a).inv_hom_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at ha
    rw [Preadditive.comp_add, ← Category.assoc,
      B.ιTotal_partialTotalSuccRetractionF m a j n hij,
      Category.assoc,
      B.ιTotal_partialTotalSuccInclusionF m a j n hij]
    rw [← Category.assoc
      ((B.partialTotalSuccOldRowIso m a).inv.f j)
      ((B.partialTotalSuccOldRowIso m a).hom.f j)
      ((B.firstStupidTrunc (m + 1)).ιTotal
        (ComplexShape.down ℕ) i j n hij),
      ha, Category.id_comp]
    rw [← Category.assoc,
      B.ιTotal_partialTotalRowQuotientF_eq_zero
        (m + 1) i j n hij (by omega), zero_comp, add_zero]
    rw [Category.comp_id]
  · by_cases hnew : i = m + 1
    · subst i
      rw [Preadditive.comp_add, ← Category.assoc,
        B.ιTotal_partialTotalSuccRetractionF_eq_zero
          m (m + 1) j n hij (by omega), zero_comp, zero_add,
        ← Category.assoc,
        B.ιTotal_partialTotalRowQuotientF (m + 1) j n hij,
        B.partialTotalRowQuotientSectionF_eq (m + 1) j n hij]
      have ha := congrArg (fun f ↦ f.f j)
        (B.partialTotalLastRowIso (m + 1)).hom_inv_id
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at ha
      rw [Category.assoc,
        Iso.inv_hom_id_assoc,
        ← Category.assoc
          ((B.partialTotalLastRowIso (m + 1)).hom.f j)
          ((B.partialTotalLastRowIso (m + 1)).inv.f j)
          ((B.firstStupidTrunc (m + 1)).ιTotal
            (ComplexShape.down ℕ) (m + 1) j n hij),
        ha, Category.id_comp, Category.comp_id]
    · have hzero : IsZero (((B.firstStupidTrunc (m + 1)).X i).X j) := by
        apply (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero
        apply B.isZero_stupidTrunc_X
          (ComplexShape.embeddingDownNatInitialSegment (m + 1))
        intro a ha
        change a.1 = i at ha
        omega
      exact hzero.eq_of_src _ _

/-- Each total degree of a successor filtration step has its canonical
old-row/new-row splitting. -/
noncomputable def partialTotalSuccDegreeSplitting (m n : ℕ) :
    ((B.partialTotalSuccShortComplex m).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Splitting where
  r := B.partialTotalSuccRetractionF m n
  s := B.partialTotalRowQuotientSectionF (m + 1) n
  f_r := by
    exact B.partialTotalMap_f_comp_partialTotalSuccRetractionF m n
  s_g := by
    exact B.partialTotalRowQuotientSectionF_comp_quotientF (m + 1) n
  id := by
    exact partialTotalSuccRetractionF_comp_map_f_add_quotientF_comp_sectionF
      B m n

/-- The degreewise old-row/new-row biproduct decomposition of a successor
partial-total stage. -/
noncomputable def partialTotalSuccDegreeIso (m n : ℕ) :
    (B.partialTotal (m + 1)).X n ≅
      (B.partialTotal m).X n ⊞ (B.totalRow (m + 1)).X n :=
  (B.partialTotalSuccDegreeSplitting m n).isoBinaryBiproduct

/-- Every evaluated successor filtration step is short exact. -/
theorem partialTotalSuccDegreewiseShortExact (m n : ℕ) :
    ((B.partialTotalSuccShortComplex m).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).ShortExact :=
  (B.partialTotalSuccDegreeSplitting m n).shortExact

/-- A bicomplex morphism induces a morphism between its successor
partial-total short complexes. -/
noncomputable def partialTotalSuccShortComplexMap (φ : B ⟶ B') (m : ℕ) :
    B.partialTotalSuccShortComplex m ⟶
      B'.partialTotalSuccShortComplex m where
  τ₁ := B.partialTotalHom φ m
  τ₂ := B.partialTotalHom φ (m + 1)
  τ₃ := totalRowMap φ (m + 1)
  comm₁₂ := B.partialTotalMap_naturality φ (Nat.le_succ m)
  comm₂₃ := B.partialTotalRowQuotient_naturality φ (m + 1)

@[simp]
theorem partialTotalSuccShortComplexMap_id (B : HomologicalComplex₂ C
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)) (m : ℕ) :
    B.partialTotalSuccShortComplexMap (𝟙 B) m = 𝟙 _ := by
  apply ShortComplex.Hom.ext
  · exact B.partialTotalHom_id m
  · exact B.partialTotalHom_id (m + 1)
  · exact totalRowMap_id B (m + 1)

@[reassoc]
theorem partialTotalSuccShortComplexMap_comp
    {B'' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : B ⟶ B') (ψ : B' ⟶ B'') (m : ℕ) :
    B.partialTotalSuccShortComplexMap (φ ≫ ψ) m =
      B.partialTotalSuccShortComplexMap φ m ≫
        B'.partialTotalSuccShortComplexMap ψ m := by
  apply ShortComplex.Hom.ext
  · exact B.partialTotalHom_comp φ ψ m
  · exact B.partialTotalHom_comp φ ψ (m + 1)
  · exact totalRowMap_comp φ ψ (m + 1)

end Quotient

section Abelian

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- In an abelian category, the degreewise split successor filtration step is
a short exact sequence of chain complexes. -/
theorem partialTotalSuccShortExact
    (B : HomologicalComplex₂ D (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (m : ℕ) :
    (B.partialTotalSuccShortComplex m).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    B.partialTotalSuccDegreewiseShortExact m n

end Abelian

end HomologicalComplex₂

end
