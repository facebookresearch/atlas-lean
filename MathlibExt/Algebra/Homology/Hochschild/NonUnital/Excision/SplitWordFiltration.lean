/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.SplitWords
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.NaiveFiltrationComplex
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.PositiveBarAssociatedGraded
public meta import Lean.Elab.Tactic.Omega

/-!
# Ideal-count spans in split-word coordinates

Ideal-count spans consist of tensors whose
color coordinates vanish below the required
number of ideal positions. Pullback identifies
the naive and positive bar stages. Associated
quotients map to the corresponding finite
color-coordinate families; these are
degreewise coordinate maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

/-- The number of ideal positions in an arbitrary original colour. -/
def splitWordIdealPositionCount {N : ℕ} (colour : Fin N → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => colour i = false)).card

/-- The source quotient-position count and ideal-position count exhaust all positions. -/
theorem splitWordPositionCounts_add {N : ℕ} (colour : Fin N → Bool) :
    quotientEntryCount colour + splitWordIdealPositionCount colour = N := by
  classical
  have hfalse :
      Finset.univ.filter (fun i : Fin N => ¬ colour i = true) =
        Finset.univ.filter (fun i : Fin N => colour i = false) := by
    apply Finset.ext
    intro i
    cases colour i <;> simp
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun i => colour i = true)
  rw [hfalse, Finset.card_univ, Fintype.card_fin] at h
  exact h

/-- Every original colour with the source quotient count p. -/
abbrev splitWordGradeColours (p N : ℕ) :=
  {colour : Fin N → Bool // quotientEntryCount colour = p}

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]
  (splitting : I.KSplit)

variable {N : ℕ}

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Too many original ideal entries force a zero original quotient coordinate. -/
theorem splitAmbientToWord_tprod_zero_of_count (colour : Fin N → Bool) (a : Fin N → A)
    (ha : splitWordIdealPositionCount colour < idealEntryCount k A I a) :
    splitAmbientToWord k A I splitting colour (PiTensorProduct.tprod k a) = 0 := by
  classical
  by_cases h : ∃ i : Fin N, colour i = true ∧ a i ∈ I.toSubmodule
  · rcases h with ⟨i, hi, hai⟩
    rw [splitAmbientToWord_tprod]
    exact (PiTensorProduct.tprod k).map_coord_zero i
      (splitWordPositionProjection_ideal_zero k A I splitting colour i hi (a i) hai)
  · have hs : (Finset.univ.filter (fun i : Fin N => a i ∈ I.toSubmodule)) ⊆
        Finset.univ.filter (fun i => colour i = false) := by
      intro i hi
      have hai := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ i, ?_⟩
      cases hc : colour i
      · rfl
      · exact False.elim (h ⟨i, hc, hai⟩)
    have hc := Finset.card_le_card hs
    change idealEntryCount k A I a ≤ splitWordIdealPositionCount colour at hc
    omega

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The count span is annihilated below its required ideal-position count. -/
theorem idealWordSpan_le_ker_splitAmbientToWord (colour : Fin N → Bool) (required : ℕ)
    (h : splitWordIdealPositionCount colour < required) :
    idealWordSpan k A I N required ≤
      LinearMap.ker (splitAmbientToWord k A I splitting colour) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  change splitAmbientToWord k A I splitting colour (PiTensorProduct.tprod k a) = 0
  exact splitAmbientToWord_tprod_zero_of_count k A I splitting colour a (h.trans_le ha)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem splitWordEntryMap_mem_ideal (colour : Bool) (h : colour = false)
    (a : splitWordEntry k A I colour) :
    splitWordEntryMap k A I splitting colour a ∈ I.toSubmodule := by
  cases colour with
  | false => exact a.property
  | true => cases h

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- A coloured tensor has at least the ideal entries at its original false positions. -/
theorem splitWordToAmbient_range_le_idealWordSpan (colour : Fin N → Bool) (required : ℕ)
    (h : required ≤ splitWordIdealPositionCount colour) :
    LinearMap.range (splitWordToAmbient k A I splitting colour) ≤
      idealWordSpan k A I N required := by
  classical
  rw [splitWordToAmbient, PiTensorProduct.map_range_eq_span_tprod]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  apply Submodule.subset_span
  refine ⟨fun i => splitWordPositionMap k A I splitting colour i (a i), ?_, rfl⟩
  have hs : (Finset.univ.filter (fun i : Fin N => colour i = false)) ⊆
      Finset.univ.filter
        (fun i => splitWordPositionMap k A I splitting colour i (a i) ∈ I.toSubmodule) := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    exact splitWordEntryMap_mem_ideal k A I splitting (colour i)
      (Finset.mem_filter.mp hi).2 (a i)
  exact h.trans (Finset.card_le_card hs)

/-- The finite coordinates supported at the required original ideal-position count. -/
def splitWordCoordinateStage (N required : ℕ) : Submodule k (splitWordCoordinates k A I N) where
  carrier := {x | ∀ colour : Fin N → Bool,
    splitWordIdealPositionCount colour < required → x colour = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {x y} hx hy colour hc := by
    change x colour + y colour = (0 : splitWordTensor k A I colour)
    rw [hx colour hc, hy colour hc, add_zero]
  smul_mem' := fun r x hx colour hc => by
    change r • x colour = (0 : splitWordTensor k A I colour)
    rw [hx colour hc, smul_zero]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- All original count spans are exactly the supported coordinates of the ambient tensor. -/
theorem idealWordSpan_eq_splitWordCoordinateStage_comap (N required : ℕ) :
    idealWordSpan k A I N required =
      (splitWordCoordinateStage k A I N required).comap
        (ambientToSplitWordCoordinates k A I splitting N) := by
  classical
  apply le_antisymm
  · intro x hx
    change ∀ colour : Fin N → Bool,
      splitWordIdealPositionCount colour < required →
        splitAmbientToWord k A I splitting colour x = 0
    intro colour hc
    exact idealWordSpan_le_ker_splitAmbientToWord k A I splitting colour required hc hx
  · intro x hx
    change ∀ colour : Fin N → Bool,
      splitWordIdealPositionCount colour < required →
        splitAmbientToWord k A I splitting colour x = 0 at hx
    rw [← splitWord_reconstruct k A I splitting x]
    apply Submodule.sum_mem
    intro colour _
    by_cases hc : required ≤ splitWordIdealPositionCount colour
    · exact splitWordToAmbient_range_le_idealWordSpan k A I splitting colour required hc
        ⟨splitAmbientToWord k A I splitting colour x, rfl⟩
    · rw [hx colour (Nat.lt_of_not_ge hc), map_zero]
      exact Submodule.zero_mem _

/-- Actual original naive stages are the original kernel pullbacks of their supported coordinates. -/
theorem naiveWordFiltration_eq_splitWordCoordinateStage_comap (p n : ℕ) :
    naiveWordFiltration k A I p n =
      (splitWordCoordinateStage k A I (n + 1) (n + 1 - p)).comap
        ((ambientToSplitWordCoordinates k A I splitting (n + 1)).comp
          (relativeNaiveWordMap k A I n)) := by
  unfold naiveWordFiltration
  rw [idealWordSpan_eq_splitWordCoordinateStage_comap k A I splitting]
  rfl

/-- Read any colour of the original naive stage by its original word getter. -/
def naiveStageToSplitWord (p n : ℕ) (colour : Fin (n + 1) → Bool) :
    naiveWordFiltration k A I p n →ₗ[k] splitWordTensor k A I colour :=
  (splitAmbientToWord k A I splitting colour).comp
    ((relativeNaiveWordMap k A I n).comp (naiveWordFiltration k A I p n).subtype)

/-- Every colour with too many original quotient positions vanishes on the original stage. -/
theorem naiveStageToSplitWord_zero_of_quotient_count (p n : ℕ)
    (colour : Fin (n + 1) → Bool) (h : p < quotientEntryCount colour)
    (x : naiveWordFiltration k A I p n) :
    naiveStageToSplitWord k A I splitting p n colour x = 0 := by
  have hc := splitWordPositionCounts_add colour
  have hrequired : splitWordIdealPositionCount colour < n + 1 - p := by omega
  have hxw : relativeNaiveWordMap k A I n ((naiveWordFiltration k A I p n).subtype x) ∈
      idealWordSpan k A I (n + 1) (n + 1 - p) := Submodule.mem_comap.mp x.property
  change splitAmbientToWord k A I splitting colour
    (relativeNaiveWordMap k A I n ((naiveWordFiltration k A I p n).subtype x)) = 0
  exact idealWordSpan_le_ker_splitAmbientToWord k A I splitting colour (n + 1 - p)
    hrequired hxw

/-- The complete finite coordinate reconstruction retains the original naive stage word. -/
theorem naiveStage_splitWord_reconstruct (p n : ℕ)
    (x : naiveWordFiltration k A I p n) :
    (∑ colour : Fin (n + 1) → Bool,
      splitWordToAmbient k A I splitting colour
        (naiveStageToSplitWord k A I splitting p n colour x)) =
      relativeNaiveWordMap k A I n x.val :=
  splitWord_reconstruct k A I splitting (relativeNaiveWordMap k A I n x.val)

/-- The original preceding stage annihilates every colour at its source quotient count. -/
theorem naiveLowerFiltration_le_ker_stageToSplitWord (p n : ℕ)
    (colour : Fin (n + 1) → Bool) (hcolour : quotientEntryCount colour = p) :
    (naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype ≤
      LinearMap.ker (naiveStageToSplitWord k A I splitting p n colour) := by
  intro x hx
  change naiveStageToSplitWord k A I splitting p n colour x = 0
  have hxl : (naiveWordFiltration k A I p n).subtype x ∈
      naiveLowerFiltration k A I p n := Submodule.mem_comap.mp hx
  by_cases hp : p = 0
  · rw [naiveLowerFiltration, ite_eq_left hp] at hxl
    have hx0 : (naiveWordFiltration k A I p n).subtype x = 0 := by
      simpa only [Submodule.mem_bot] using hxl
    change splitAmbientToWord k A I splitting colour
      (relativeNaiveWordMap k A I n ((naiveWordFiltration k A I p n).subtype x)) = 0
    rw [hx0, map_zero, map_zero]
  · rw [naiveLowerFiltration, ite_eq_right hp] at hxl
    have hxw : relativeNaiveWordMap k A I n ((naiveWordFiltration k A I p n).subtype x) ∈
        idealWordSpan k A I (n + 1) (n + 1 - (p - 1)) := Submodule.mem_comap.mp hxl
    have hc := splitWordPositionCounts_add colour
    have hrequired : splitWordIdealPositionCount colour < n + 1 - (p - 1) := by omega
    change splitAmbientToWord k A I splitting colour
      (relativeNaiveWordMap k A I n ((naiveWordFiltration k A I p n).subtype x)) = 0
    exact idealWordSpan_le_ker_splitAmbientToWord k A I splitting colour
      (n + 1 - (p - 1)) hrequired hxw

/-- The native quotient universal property reads every source-count colour of the original naive layer. -/
def naiveLayerToSplitWord (p n : ℕ) (colour : Fin (n + 1) → Bool)
    (hcolour : quotientEntryCount colour = p) :
    naiveWordLayer k A I p n →ₗ[k] splitWordTensor k A I colour :=
  ((naiveLowerFiltration k A I p n).comap (naiveWordFiltration k A I p n).subtype).liftQ
    (naiveStageToSplitWord k A I splitting p n colour)
    (naiveLowerFiltration_le_ker_stageToSplitWord k A I splitting p n colour hcolour)

/-- Actual original naive quotient projection evaluates by the original word getter and original colour maps. -/
theorem naiveLayerToSplitWord_projection (p n : ℕ) (colour : Fin (n + 1) → Bool)
    (hcolour : quotientEntryCount colour = p) (x : naiveWordFiltration k A I p n) :
    naiveLayerToSplitWord k A I splitting p n colour hcolour
        (naiveWordLayerProjection k A I p n x) =
      splitAmbientToWord k A I splitting colour (relativeNaiveWordMap k A I n x.val) := rfl

/-- The internal finite family of every source-count naive colour coordinate. -/
abbrev naiveSplitWordGradeCoordinates (p n : ℕ) : Type (max u v) :=
  ∀ colour : splitWordGradeColours p (n + 1), splitWordTensor k A I colour.val

/-- The native family map collects every colour coordinate of the original naive associated quotient. -/
def naiveLayerToSplitWordCoordinates (p n : ℕ) :
    naiveWordLayer k A I p n →ₗ[k] naiveSplitWordGradeCoordinates k A I p n :=
  LinearMap.pi (fun colour : splitWordGradeColours p (n + 1) =>
    naiveLayerToSplitWord k A I splitting p n colour.val colour.property)

/-- The original associated-complex term maps to every original source-count coordinate. -/
def naiveAssociatedSplitWordMap (p n : ℕ) :
    (naiveAssociatedWordComplex k A I p).X n ⟶
      ModuleCat.of k (naiveSplitWordGradeCoordinates k A I p n) :=
  ModuleCat.ofHom (naiveLayerToSplitWordCoordinates k A I splitting p n)

/-- Every collected original naive coordinate has the original quotient-stage evaluation formula. -/
theorem naiveLayerToSplitWordCoordinates_projection (p n : ℕ)
    (x : naiveWordFiltration k A I p n) (colour : splitWordGradeColours p (n + 1)) :
    naiveLayerToSplitWordCoordinates k A I splitting p n
        (naiveWordLayerProjection k A I p n x) colour =
      splitAmbientToWord k A I splitting colour.val (relativeNaiveWordMap k A I n x.val) := rfl

variable (V : Type w) [AddCommGroup V] [Module k V]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The coefficient count span is annihilated below the required original ideal-position count. -/
theorem coefficientIdealWordSpan_le_ker_splitAmbientToWord (colour : Fin N → Bool)
    (required : ℕ) (h : splitWordIdealPositionCount colour < required) :
    coefficientIdealWordSpan k A I V N required ≤
      LinearMap.ker (coefficientSplitAmbientToWord k A I V splitting colour) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, a, ha, rfl⟩
  change coefficientSplitAmbientToWord k A I V splitting colour
    (v ⊗ₜ[k] PiTensorProduct.tprod k a) = 0
  rw [coefficientSplitAmbientToWord, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [splitAmbientToWord_tprod_zero_of_count k A I splitting colour a (h.trans_le ha),
    TensorProduct.tmul_zero]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Every coefficient-colour tensor lies in its original required ideal-count span. -/
theorem coefficientSplitWordToAmbient_range_le_coefficientIdealWordSpan
    (colour : Fin N → Bool) (required : ℕ)
    (h : required ≤ splitWordIdealPositionCount colour) :
    LinearMap.range (coefficientSplitWordToAmbient k A I V splitting colour) ≤
      coefficientIdealWordSpan k A I V N required := by
  rw [coefficientSplitWordToAmbient, TensorProduct.range_map_eq_span_tmul]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, y, rfl⟩
  have hy : splitWordToAmbient k A I splitting colour y ∈ idealWordSpan k A I N required :=
    splitWordToAmbient_range_le_idealWordSpan k A I splitting colour required h ⟨y, rfl⟩
  have hv : idealWordSpan k A I N required ≤
      (coefficientIdealWordSpan k A I V N required).comap
        (TensorProduct.mk k V (TensorPower k N A) v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.subset_span ⟨v, a, ha, rfl⟩
  have hmem := hv hy
  change v ⊗ₜ[k] splitWordToAmbient k A I splitting colour y ∈
    coefficientIdealWordSpan k A I V N required at hmem
  change v ⊗ₜ[k] splitWordToAmbient k A I splitting colour y ∈
    coefficientIdealWordSpan k A I V N required
  exact hmem

/-- The coefficient coordinates supported at the original required ideal-position count. -/
def coefficientSplitWordCoordinateStage (N required : ℕ) :
    Submodule k (coefficientSplitWordCoordinates k A I V N) where
  carrier := {x | ∀ colour : Fin N → Bool,
    splitWordIdealPositionCount colour < required → x colour = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {x y} hx hy colour hc := by
    change x colour + y colour = (0 : V ⊗[k] splitWordTensor k A I colour)
    rw [hx colour hc, hy colour hc, add_zero]
  smul_mem' := fun r x hx colour hc => by
    change r • x colour = (0 : V ⊗[k] splitWordTensor k A I colour)
    rw [hx colour hc, smul_zero]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- All original coefficient count spans are exactly the supported coordinates under the original identity map. -/
theorem coefficientIdealWordSpan_eq_splitWordCoordinateStage_comap (N required : ℕ) :
    coefficientIdealWordSpan k A I V N required =
      (coefficientSplitWordCoordinateStage k A I V N required).comap
        (coefficientAmbientToSplitWordCoordinates k A I V splitting N) := by
  classical
  apply le_antisymm
  · intro x hx
    change ∀ colour : Fin N → Bool,
      splitWordIdealPositionCount colour < required →
        coefficientSplitAmbientToWord k A I V splitting colour x = 0
    intro colour hc
    exact coefficientIdealWordSpan_le_ker_splitAmbientToWord
      k A I splitting V colour required hc hx
  · intro x hx
    change ∀ colour : Fin N → Bool,
      splitWordIdealPositionCount colour < required →
        coefficientSplitAmbientToWord k A I V splitting colour x = 0 at hx
    rw [← coefficientSplitWord_reconstruct k A I V splitting x]
    apply Submodule.sum_mem
    intro colour _
    by_cases hc : required ≤ splitWordIdealPositionCount colour
    · exact coefficientSplitWordToAmbient_range_le_coefficientIdealWordSpan
        k A I splitting V colour required hc
        ⟨coefficientSplitAmbientToWord k A I V splitting colour x, rfl⟩
    · rw [hx colour (Nat.lt_of_not_ge hc), map_zero]
      exact Submodule.zero_mem _

/-- Actual original bar stages are the original arbitrary-coefficient kernel pullbacks of supported coordinates. -/
theorem barWordFiltration_eq_splitWordCoordinateStage_comap (p n : ℕ) :
    barWordFiltration k A I V p n =
      (coefficientSplitWordCoordinateStage k A I V (n + 1) (n + 1 - p)).comap
        ((coefficientAmbientToSplitWordCoordinates k A I V splitting (n + 1)).comp
          (relativePositiveBarWordMap k A I V n)) := by
  unfold barWordFiltration
  rw [coefficientIdealWordSpan_eq_splitWordCoordinateStage_comap k A I splitting V]
  rfl

/-- Every colour of the original arbitrary-coefficient stage is read by the original maps. -/
def barStageToSplitWord (p n : ℕ) (colour : Fin (n + 1) → Bool) :
    barWordFiltration k A I V p n →ₗ[k] V ⊗[k] splitWordTensor k A I colour :=
  (coefficientSplitAmbientToWord k A I V splitting colour).comp
    ((relativePositiveBarWordMap k A I V n).comp (barWordFiltration k A I V p n).subtype)

/-- Original coefficient-stage coordinates vanish at every colour with too many original quotient positions. -/
theorem barStageToSplitWord_zero_of_quotient_count (p n : ℕ)
    (colour : Fin (n + 1) → Bool) (h : p < quotientEntryCount colour)
    (x : barWordFiltration k A I V p n) :
    barStageToSplitWord k A I splitting V p n colour x = 0 := by
  have hc := splitWordPositionCounts_add colour
  have hrequired : splitWordIdealPositionCount colour < n + 1 - p := by omega
  have hxw : relativePositiveBarWordMap k A I V n ((barWordFiltration k A I V p n).subtype x) ∈
      coefficientIdealWordSpan k A I V (n + 1) (n + 1 - p) := Submodule.mem_comap.mp x.property
  change coefficientSplitAmbientToWord k A I V splitting colour
    (relativePositiveBarWordMap k A I V n ((barWordFiltration k A I V p n).subtype x)) = 0
  exact coefficientIdealWordSpan_le_ker_splitAmbientToWord k A I splitting V colour
    (n + 1 - p) hrequired hxw

/-- The full finite coefficient-coordinate reconstruction retains the original bar stage word. -/
theorem barStage_splitWord_reconstruct (p n : ℕ)
    (x : barWordFiltration k A I V p n) :
    (∑ colour : Fin (n + 1) → Bool,
      coefficientSplitWordToAmbient k A I V splitting colour
        (barStageToSplitWord k A I splitting V p n colour x)) =
      relativePositiveBarWordMap k A I V n x.val :=
  coefficientSplitWord_reconstruct k A I V splitting
    (relativePositiveBarWordMap k A I V n x.val)

/-- The original bar predecessor annihilates every colour at its original source quotient count. -/
theorem barLowerFiltration_le_ker_stageToSplitWord (p n : ℕ)
    (colour : Fin (n + 1) → Bool) (hcolour : quotientEntryCount colour = p) :
    (barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype ≤
      LinearMap.ker (barStageToSplitWord k A I splitting V p n colour) := by
  intro x hx
  change barStageToSplitWord k A I splitting V p n colour x = 0
  have hxl : (barWordFiltration k A I V p n).subtype x ∈
      barLowerFiltration k A I V p n := Submodule.mem_comap.mp hx
  by_cases hp : p = 0
  · rw [barLowerFiltration, ite_eq_left hp] at hxl
    have hx0 : (barWordFiltration k A I V p n).subtype x = 0 := by
      simpa only [Submodule.mem_bot] using hxl
    change coefficientSplitAmbientToWord k A I V splitting colour
      (relativePositiveBarWordMap k A I V n ((barWordFiltration k A I V p n).subtype x)) = 0
    rw [hx0, map_zero, map_zero]
  · rw [barLowerFiltration, ite_eq_right hp] at hxl
    have hxw : relativePositiveBarWordMap k A I V n ((barWordFiltration k A I V p n).subtype x) ∈
        coefficientIdealWordSpan k A I V (n + 1) (n + 1 - (p - 1)) := Submodule.mem_comap.mp hxl
    have hc := splitWordPositionCounts_add colour
    have hrequired : splitWordIdealPositionCount colour < n + 1 - (p - 1) := by omega
    change coefficientSplitAmbientToWord k A I V splitting colour
      (relativePositiveBarWordMap k A I V n ((barWordFiltration k A I V p n).subtype x)) = 0
    exact coefficientIdealWordSpan_le_ker_splitAmbientToWord k A I splitting V colour
      (n + 1 - (p - 1)) hrequired hxw

/-- The original positive associated quotient maps to every colour at its source quotient count. -/
def barLayerToSplitWord (p n : ℕ) (colour : Fin (n + 1) → Bool)
    (hcolour : quotientEntryCount colour = p) :
    barWordLayer k A I V p n →ₗ[k] V ⊗[k] splitWordTensor k A I colour :=
  ((barLowerFiltration k A I V p n).comap (barWordFiltration k A I V p n).subtype).liftQ
    (barStageToSplitWord k A I splitting V p n colour)
    (barLowerFiltration_le_ker_stageToSplitWord k A I splitting V p n colour hcolour)

/-- Actual bar quotient projection reads the original coefficient, word getter and original colour coordinates. -/
theorem barLayerToSplitWord_projection (p n : ℕ) (colour : Fin (n + 1) → Bool)
    (hcolour : quotientEntryCount colour = p) (x : barWordFiltration k A I V p n) :
    barLayerToSplitWord k A I splitting V p n colour hcolour
        (barWordLayerProjection k A I V p n x) =
      coefficientSplitAmbientToWord k A I V splitting colour
        (relativePositiveBarWordMap k A I V n x.val) := rfl

/-- The internal finite family of all original source-count positive colour coordinates. -/
abbrev barSplitWordGradeCoordinates (p n : ℕ) : Type (max u v w) :=
  ∀ colour : splitWordGradeColours p (n + 1), V ⊗[k] splitWordTensor k A I colour.val

/-- The native family map collects every original positive associated-quotient coordinate. -/
def barLayerToSplitWordCoordinates (p n : ℕ) :
    barWordLayer k A I V p n →ₗ[k] barSplitWordGradeCoordinates k A I V p n :=
  LinearMap.pi (fun colour : splitWordGradeColours p (n + 1) =>
    barLayerToSplitWord k A I splitting V p n colour.val colour.property)

/-- The original positive associated-complex term maps to the full source-count colour family. -/
def barAssociatedSplitWordMap (p n : ℕ) :
    (barAssociatedWordComplex k A I V p).X (n + 1) ⟶
      ModuleCat.of k (barSplitWordGradeCoordinates k A I V p n) :=
  ModuleCat.ofHom (barLayerToSplitWordCoordinates k A I splitting V p n)

/-- Every collected original bar coordinate retains the original quotient-stage formula. -/
theorem barLayerToSplitWordCoordinates_projection (p n : ℕ)
    (x : barWordFiltration k A I V p n) (colour : splitWordGradeColours p (n + 1)) :
    barLayerToSplitWordCoordinates k A I splitting V p n
        (barWordLayerProjection k A I V p n x) colour =
      coefficientSplitAmbientToWord k A I V splitting colour.val
        (relativePositiveBarWordMap k A I V n x.val) := rfl

end ModuleCat.Algebra.Hochschild.NonUnital
