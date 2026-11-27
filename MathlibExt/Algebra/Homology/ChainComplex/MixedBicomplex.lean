/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.FirstQuadrantTotalQuasiIso

public import MathlibExt.Algebra.Homology.Homotopy.HomologyDegree
public import MathlibExt.Algebra.Homology.Embedding.MapExtend
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.TotalComplex
public import MathlibExt.CategoryTheory.GradedObject.FiniteFibers

public meta import Lean.Elab.Tactic.Omega

/-!
# The bicomplex of a square-zero boundary homotopy

A degree-one homotopy from zero to zero with square-zero components gives
a bicomplex. Column p is the translation of the chain complex by p with
sign (-1)^p, and the homotopy components give its horizontal maps.
The totalization sign cancels the column sign on the supporting triangle.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v w

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  (K : ChainComplex C ℕ)

/-- The translated column, with its constant sign on the original differential. -/
def mixedColumn (p : ℕ) : ChainComplex C ℕ where
  X q := (K.extend (c' := ComplexShape.down ℕ) (ComplexShape.embeddingDown'Add (1 : ℕ) p)).X q
  d q q' := ((-1 : ℤˣ) ^ p) •
    (K.extend (c' := ComplexShape.down ℕ) (ComplexShape.embeddingDown'Add (1 : ℕ) p)).d q q'
  shape q q' h := by
    rw [(K.extend (c' := ComplexShape.down ℕ)
      (ComplexShape.embeddingDown'Add (1 : ℕ) p)).shape q q' h, smul_zero]
  d_comp_d' q q' q'' _ _ := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, d_comp_d,
      smul_zero, smul_zero]

/-- Supported column coordinates are the native zero-extension coordinates. -/
def mixedColumnIso (p n q : ℕ) (h : n + p = q) : (mixedColumn K p).X q ≅ K.X n :=
  K.extendXIso (c' := ComplexShape.down ℕ)
    (ComplexShape.embeddingDown'Add (1 : ℕ) p) h

/-- Cells strictly below the supporting triangle are the native zero objects. -/
theorem mixedColumn_isZero (p q : ℕ) (h : q < p) : IsZero ((mixedColumn K p).X q) :=
  K.isZero_extend_X (c' := ComplexShape.down ℕ)
    (ComplexShape.embeddingDown'Add (1 : ℕ) p) q (by
    intro n hn
    change n + p = q at hn
    omega)

/-- Coordinate evaluation retains the signed original differential. -/
theorem mixedColumn_d_eq (p n m q q' : ℕ) (hn : n + p = q) (hm : m + p = q') :
    (mixedColumn K p).d q q' =
      (mixedColumnIso K p n q hn).hom ≫ (((-1 : ℤˣ) ^ p) • K.d n m) ≫
        (mixedColumnIso K p m q' hm).inv := by
  change ((-1 : ℤˣ) ^ p) •
    (K.extend (c' := ComplexShape.down ℕ) (ComplexShape.embeddingDown'Add (1 : ℕ) p)).d q q' = _
  rw [K.extend_d_eq (c' := ComplexShape.down ℕ)
    (ComplexShape.embeddingDown'Add (1 : ℕ) p) hn hm]
  simp only [mixedColumnIso, Category.assoc, Linear.units_smul_comp,
    Linear.comp_units_smul]

/-- The mixed column zero recovers the original complex through its native coordinates. -/
def mixedColumnZeroIso : mixedColumn K 0 ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => mixedColumnIso K 0 n n rfl)
    (fun i j _ => by
      have hD : (mixedColumn K 0).d i j =
          (mixedColumnIso K 0 i i rfl).hom ≫ K.d i j ≫
            (mixedColumnIso K 0 j j rfl).inv := by
        simpa only [pow_zero, one_smul] using mixedColumn_d_eq K 0 i j i j rfl rfl
      have hRight : (mixedColumn K 0).d i j ≫ (mixedColumnIso K 0 j j rfl).hom =
          (mixedColumnIso K 0 i i rfl).hom ≫ K.d i j := by
        calc
          (mixedColumn K 0).d i j ≫ (mixedColumnIso K 0 j j rfl).hom =
              ((mixedColumnIso K 0 i i rfl).hom ≫ K.d i j ≫
                (mixedColumnIso K 0 j j rfl).inv) ≫ (mixedColumnIso K 0 j j rfl).hom :=
            congrArg (fun d => d ≫ (mixedColumnIso K 0 j j rfl).hom) hD
          _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact hRight.symm)

/-- The zero-column comparison retains the original forward coordinate in every degree. -/
lemma mixedColumnZeroIso_hom_f (n : ℕ) :
    (mixedColumnZeroIso K).hom.f n = (mixedColumnIso K 0 n n rfl).hom := by
  simp only [mixedColumnZeroIso, HomologicalComplex.Hom.isoOfComponents_hom_f]

/-- Its inverse retains the inverse coordinate in every degree. -/
lemma mixedColumnZeroIso_inv_f (n : ℕ) :
    (mixedColumnZeroIso K).inv.f n = (mixedColumnIso K 0 n n rfl).inv := by
  simp only [mixedColumnZeroIso, HomologicalComplex.Hom.isoOfComponents_inv_f]


variable (H : Homotopy (0 : K ⟶ K) 0)

/-- The original degree-one component, conjugated by the supported column coordinates. -/
def mixedHorizontalComponent (p q : ℕ) :
    (mixedColumn K (p + 1)).X q ⟶ (mixedColumn K p).X q :=
  if h : p + 1 ≤ q then
    (mixedColumnIso K (p + 1) (q - (p + 1)) q (Nat.sub_add_cancel h)).hom ≫
      H.hom (q - (p + 1)) (q - (p + 1) + 1) ≫
        (mixedColumnIso K p (q - (p + 1) + 1) q (by omega)).inv
  else 0

/-- The supported horizontal map is precisely the original homotopy component. -/
theorem mixedHorizontalComponent_eq (p n q : ℕ) (h : n + (p + 1) = q) :
    mixedHorizontalComponent K H p q =
      (mixedColumnIso K (p + 1) n q h).hom ≫ H.hom n (n + 1) ≫
        (mixedColumnIso K p (n + 1) q (by omega)).inv := by
  have hpq : p + 1 ≤ q := by omega
  let component (a : {m : ℕ // m + (p + 1) = q}) :
      (mixedColumn K (p + 1)).X q ⟶ (mixedColumn K p).X q :=
    (mixedColumnIso K (p + 1) a.val q a.property).hom ≫
      H.hom a.val (a.val + 1) ≫
        (mixedColumnIso K p (a.val + 1) q (by
          have ha := a.property
          omega)).inv
  have hIndex :
      (⟨q - (p + 1), Nat.sub_add_cancel hpq⟩ : {m : ℕ // m + (p + 1) = q}) =
        ⟨n, h⟩ := by
    apply Subtype.ext
    change q - (p + 1) = n
    rw [← h, Nat.add_sub_cancel]
  rw [mixedHorizontalComponent, dite_eq_left hpq]
  exact congrArg component hIndex

omit [HasZeroObject C] in
private theorem component_anticommutes (n : ℕ) :
    H.hom (n + 1) (n + 2) ≫ K.d (n + 2) (n + 1) =
      -(K.d (n + 1) n ≫ H.hom n (n + 1)) := by
  have h := H.comm (n + 1)
  rw [HomologicalComplex.zero_f_apply, add_zero,
    dNext_eq H.hom (by show (ComplexShape.down ℕ).Rel (n + 1) n; rfl),
    prevD_eq H.hom (by show (ComplexShape.down ℕ).Rel (n + 2) (n + 1); rfl)] at h
  exact eq_neg_of_add_eq_zero_right h.symm

omit [HasZeroObject C] in
private theorem signed_component_commutes (p n : ℕ) :
    H.hom (n + 1) (n + 2) ≫ (((-1 : ℤˣ) ^ p) • K.d (n + 2) (n + 1)) =
      (((-1 : ℤˣ) ^ (p + 1)) • K.d (n + 1) n) ≫ H.hom n (n + 1) := by
  rw [Linear.comp_units_smul, Linear.units_smul_comp,
    component_anticommutes K H n]
  simp only [pow_succ, mul_smul, Units.neg_smul, one_smul]

omit [HasZeroObject C] in
private theorem component_bottom : H.hom 0 1 ≫ K.d 1 0 = 0 := by
  have h := H.comm 0
  rw [HomologicalComplex.zero_f_apply, add_zero,
    dNext_eq_zero H.hom 0 (by simp [ComplexShape.down_Rel]),
    prevD_eq H.hom (by show (ComplexShape.down ℕ).Rel 1 0; rfl), zero_add] at h
  exact h.symm

private theorem mixedHorizontalComponent_comm (p q : ℕ) :
    mixedHorizontalComponent K H p (q + 1) ≫ (mixedColumn K p).d (q + 1) q =
      (mixedColumn K (p + 1)).d (q + 1) q ≫ mixedHorizontalComponent K H p q := by
  by_cases hq : p + 1 ≤ q
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hq
    have hs : n + (p + 1) = q := by omega
    have hs' : (n + 1) + (p + 1) = q + 1 := by omega
    have ht : (n + 1) + p = q := by omega
    have ht' : (n + 2) + p = q + 1 := by omega
    rw [mixedHorizontalComponent_eq K H p (n + 1) (q + 1) hs',
      mixedHorizontalComponent_eq K H p n q hs,
      mixedColumn_d_eq K p (n + 2) (n + 1) (q + 1) q ht' ht,
      mixedColumn_d_eq K (p + 1) (n + 1) n (q + 1) q hs' hs]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using congrArg
      (fun a : K.X (n + 1) ⟶ K.X (n + 1) =>
        (mixedColumnIso K (p + 1) (n + 1) (q + 1) hs').hom ≫ a ≫
          (mixedColumnIso K p (n + 1) q ht).inv)
      (signed_component_commutes K H p n)
  · by_cases hqp : q = p
    · subst q
      rw [mixedHorizontalComponent_eq K H p 0 (p + 1) (by omega),
        mixedColumn_d_eq K p 1 0 (p + 1) p (by omega) (by omega)]
      have hz : mixedHorizontalComponent K H p p = 0 :=
        dite_eq_right (by omega)
      rw [hz, comp_zero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Nat.zero_add]
      rw [← Category.assoc (H.hom 0 1), Linear.comp_units_smul,
        component_bottom K H, smul_zero, zero_comp, comp_zero]
    · exact (mixedColumn_isZero K (p + 1) (q + 1) (by omega)).eq_of_src _ _

/-- Anticommutation and the bottom identity give an actual map of translated columns. -/
def mixedHorizontalMap (p : ℕ) : mixedColumn K (p + 1) ⟶ mixedColumn K p :=
  ChainComplex.ofHom (mixedHorizontalComponent K H p)
    (by exact mixedHorizontalComponent_comm K H p)

/-- The native column map has the conjugated component. -/
@[simp]
theorem mixedHorizontalMap_f (p q : ℕ) :
    (mixedHorizontalMap K H p).f q = mixedHorizontalComponent K H p q := rfl

variable (hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0)

include hSquare in
/-- The original component square-zero identity is the horizontal square-zero law. -/
theorem mixedHorizontalMap_square (p : ℕ) :
    mixedHorizontalMap K H (p + 1) ≫ mixedHorizontalMap K H p = 0 := by
  apply HomologicalComplex.hom_ext
  intro q
  change mixedHorizontalComponent K H (p + 1) q ≫
    mixedHorizontalComponent K H p q = 0
  by_cases hq : p + 2 ≤ q
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hq
    have hs : n + (p + 1 + 1) = q := by omega
    have hm : (n + 1) + (p + 1) = q := by omega
    have ht : (n + 2) + p = q := by omega
    rw [mixedHorizontalComponent_eq K H (p + 1) n q hs,
      mixedHorizontalComponent_eq K H p (n + 1) q hm]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (H.hom n (n + 1)), hSquare n, zero_comp, comp_zero]
  · exact (mixedColumn_isZero K (p + 1 + 1) q (by omega)).eq_of_src _ _

/-- The (b,B) construction uses the native bicomplex type and original translated columns. -/
def mixedBicomplex : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ChainComplex.of (mixedColumn K) (mixedHorizontalMap K H)
    (mixedHorizontalMap_square K H hSquare)

/-- Coordinates on the supporting triangle retain the original degree q-p. -/
def mixedBicomplexCellIso (p q : ℕ) (hpq : p ≤ q) :
    ((mixedBicomplex K H hSquare).X p).X q ≅ K.X (q - p) :=
  mixedColumnIso K p (q - p) q (Nat.sub_add_cancel hpq)

/-- The unsupported cells are zero, rather than a discarded bottom term. -/
theorem mixedBicomplex_isZero_cell (p q : ℕ) (hpq : q < p) :
    IsZero (((mixedBicomplex K H hSquare).X p).X q) :=
  mixedColumn_isZero K p q hpq

private theorem sign_square (p : ℕ) : ((-1 : ℤˣ) ^ p) * ((-1 : ℤˣ) ^ p) = 1 := by
  apply Units.ext
  change ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1
  rw [← mul_pow, neg_mul_neg, one_mul, one_pow]

/-- Native totalization cancels the constant column sign and retains positive b. -/
theorem mixedBicomplex_total_vertical (p n m q q' : ℕ)
    (hn : n + p = q) (hm : m + p = q') :
    (ComplexShape.down ℕ).ε p • ((mixedBicomplex K H hSquare).X p).d q q' =
      (mixedColumnIso K p n q hn).hom ≫ K.d n m ≫
        (mixedColumnIso K p m q' hm).inv := by
  change (ComplexShape.down ℕ).ε p • (mixedColumn K p).d q q' = _
  rw [ComplexShape.ε_down_ℕ, mixedColumn_d_eq K p n m q q' hn hm]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    sign_square, one_smul]

/-- The original contraction transports through the signed native column translation. -/
def mixedColumnContraction (h : Homotopy (𝟙 K) 0) (p : ℕ) :
    Homotopy (𝟙 (mixedColumn K p)) 0 where
  hom q q' := ((-1 : ℤˣ) ^ p) •
    (h.extend (c' := ComplexShape.down ℕ) (ComplexShape.embeddingDown'Add (1 : ℕ) p)).hom q q'
  zero q q' hqq := by
    rw [(h.extend (c' := ComplexShape.down ℕ)
      (ComplexShape.embeddingDown'Add (1 : ℕ) p)).zero q q' hqq, smul_zero]
  comm q := by
    let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
      ComplexShape.embeddingDown'Add (1 : ℕ) p
    let T : ChainComplex C ℕ := K.extend E
    let hT := h.extend E
    have hq := hT.comm q
    simp only [extendMap_id, extendMap_zero, HomologicalComplex.id_f,
      HomologicalComplex.zero_f_apply, add_zero] at hq
    dsimp only [mixedColumn]
    change (𝟙 (T.X q) : T.X q ⟶ T.X q) =
      (((-1 : ℤˣ) ^ p) • T.d q ((ComplexShape.down ℕ).next q)) ≫
        (((-1 : ℤˣ) ^ p) • hT.hom ((ComplexShape.down ℕ).next q) q) +
      (((-1 : ℤˣ) ^ p) • hT.hom q ((ComplexShape.down ℕ).prev q)) ≫
        (((-1 : ℤˣ) ^ p) • T.d ((ComplexShape.down ℕ).prev q) q) + (0 : T.X q ⟶ T.X q)
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      sign_square, one_smul, add_zero]
    exact hq

/-- The signed contraction keeps the extended homotopy component. -/
@[simp]
theorem mixedColumnContraction_hom (h : Homotopy (𝟙 K) 0) (p q q' : ℕ) :
    (mixedColumnContraction K h p).hom q q' =
      ((-1 : ℤˣ) ^ p) •
        (h.extend (c' := ComplexShape.down ℕ)
          (ComplexShape.embeddingDown'Add (1 : ℕ) p)).hom q q' := rfl

section Maps

variable {K} {L : ChainComplex C ℕ} (f : K ⟶ L)

/-- Native zero extension gives the map on each constant-sign column. -/
def mixedColumnMap (p : ℕ) : mixedColumn K p ⟶ mixedColumn L p :=
  ChainComplex.ofHom (HomologicalComplex.extendMap f (c' := ComplexShape.down ℕ)
    (ComplexShape.embeddingDown'Add (1 : ℕ) p)).f (fun q => by
      change (HomologicalComplex.extendMap f (c' := ComplexShape.down ℕ)
        (ComplexShape.embeddingDown'Add (1 : ℕ) p)).f (q + 1) ≫
        (((-1 : ℤˣ) ^ p) • (L.extend (c' := ComplexShape.down ℕ)
          (ComplexShape.embeddingDown'Add (1 : ℕ) p)).d (q + 1) q) =
          (((-1 : ℤˣ) ^ p) • (K.extend (c' := ComplexShape.down ℕ)
            (ComplexShape.embeddingDown'Add (1 : ℕ) p)).d (q + 1) q) ≫
            (HomologicalComplex.extendMap f (c' := ComplexShape.down ℕ)
        (ComplexShape.embeddingDown'Add (1 : ℕ) p)).f q
      rw [Linear.comp_units_smul, Linear.units_smul_comp,
        (HomologicalComplex.extendMap f (c' := ComplexShape.down ℕ)
        (ComplexShape.embeddingDown'Add (1 : ℕ) p)).comm])

/-- Actual column-map coordinates are the original chain-map component. -/
theorem mixedColumnMap_f_eq (p n q : ℕ) (h : n + p = q) :
    (mixedColumnMap f p).f q =
      (mixedColumnIso K p n q h).hom ≫ f.f n ≫ (mixedColumnIso L p n q h).inv :=
  HomologicalComplex.extendMap_f f (c' := ComplexShape.down ℕ)
    (ComplexShape.embeddingDown'Add (1 : ℕ) p) h

/-- Column translation preserves the order of composition of chain maps. -/
theorem mixedColumnMap_comp {M : ChainComplex C ℕ} (g : L ⟶ M) (p : ℕ) :
    mixedColumnMap (f ≫ g) p = mixedColumnMap f p ≫ mixedColumnMap g p := by
  apply HomologicalComplex.hom_ext
  intro q
  exact congrArg
    (fun a : K.extend (c' := ComplexShape.down ℕ) (ComplexShape.embeddingDown'Add (1 : ℕ) p) ⟶
      M.extend (c' := ComplexShape.down ℕ) (ComplexShape.embeddingDown'Add (1 : ℕ) p) => a.f q)
        (HomologicalComplex.extendMap_comp f g (c' := ComplexShape.down ℕ)
          (ComplexShape.embeddingDown'Add (1 : ℕ) p))

variable {H hSquare} (H' : Homotopy (0 : L ⟶ L) 0)
  (hSquare' : ∀ n, H'.hom n (n + 1) ≫ H'.hom (n + 1) (n + 2) = 0)
  (hComponent : ∀ n, f.f n ≫ H'.hom n (n + 1) = H.hom n (n + 1) ≫ f.f (n + 1))

include hComponent in
/-- Original component compatibility gives commutation with the horizontal column map. -/
@[reassoc]
theorem mixedColumnMap_horizontal_comm (p : ℕ) :
    mixedColumnMap f (p + 1) ≫ mixedHorizontalMap L H' p =
      mixedHorizontalMap K H p ≫ mixedColumnMap f p := by
  apply HomologicalComplex.hom_ext
  intro q
  change (mixedColumnMap f (p + 1)).f q ≫ mixedHorizontalComponent L H' p q =
    mixedHorizontalComponent K H p q ≫ (mixedColumnMap f p).f q
  by_cases hq : p + 1 ≤ q
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hq
    have hs : n + (p + 1) = q := by omega
    have ht : (n + 1) + p = q := by omega
    rw [mixedColumnMap_f_eq f (p + 1) n q hs,
      mixedColumnMap_f_eq f p (n + 1) q ht,
      mixedHorizontalComponent_eq L H' p n q hs,
      mixedHorizontalComponent_eq K H p n q hs]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using congrArg
      (fun a : K.X n ⟶ L.X (n + 1) =>
        (mixedColumnIso K (p + 1) n q hs).hom ≫ a ≫
          (mixedColumnIso L p (n + 1) q ht).inv)
      (hComponent n)
  · exact (mixedColumn_isZero K (p + 1) q (by omega)).eq_of_src _ _

include hComponent in
private theorem mixedColumnMap_comm (p : ℕ) :
    mixedColumnMap f (p + 1) ≫ mixedHorizontalMap L H' p =
      mixedHorizontalMap K H p ≫ mixedColumnMap f p :=
  mixedColumnMap_horizontal_comm (H := H) (f := f) (H' := H')
    (hComponent := hComponent) (p := p)

include hComponent in
/-- Compatible original chain maps give an actual map of the native mixed bicomplexes. -/
def mixedBicomplexMap : mixedBicomplex K H hSquare ⟶ mixedBicomplex L H' hSquare' :=
  ChainComplex.ofHom (mixedColumnMap f) (fun p => by
    simp only [mixedBicomplex, ChainComplex.of_d]
    exact mixedColumnMap_horizontal_comm (H := H) (f := f) (H' := H')
      (hComponent := hComponent) (p := p))

/-- Each actual bicomplex map is the native extended original chain map. -/
@[simp]
theorem mixedBicomplexMap_f (p : ℕ) :
    (mixedBicomplexMap (H := H) (hSquare := hSquare) (f := f)
      (H' := H') (hSquare' := hSquare') (hComponent := hComponent)).f p = mixedColumnMap f p := rfl

end Maps

/-- The signed column is the native zero extension in unit-diagonal coordinates. -/
def mixedColumnExtendIso (p : ℕ) :
    mixedColumn K p ≅ K.extend (c' := ComplexShape.down ℕ)
      (ComplexShape.embeddingDown'Add (1 : ℕ) p) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (((-1 : ℤˣ) ^ p) ^ q) • Iso.refl
      ((K.extend (c' := ComplexShape.down ℕ)
        (ComplexShape.embeddingDown'Add (1 : ℕ) p)).X q)) (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      change (((-1 : ℤˣ) ^ p) ^ (j + 1) • 𝟙 _) ≫ (K.extend (c' := ComplexShape.down ℕ)
        (ComplexShape.embeddingDown'Add (1 : ℕ) p)).d (j + 1) j =
        (((-1 : ℤˣ) ^ p) • (K.extend (c' := ComplexShape.down ℕ)
          (ComplexShape.embeddingDown'Add (1 : ℕ) p)).d (j + 1) j) ≫
          (((-1 : ℤˣ) ^ p) ^ j • 𝟙 _)
      simp only [Linear.units_smul_comp, Linear.comp_units_smul,
        Category.id_comp, Category.comp_id, smul_smul, pow_succ])

/-- The unit-diagonal comparison retains the original degree object and sign. -/
@[simp]
theorem mixedColumnExtendIso_hom_f (p q : ℕ) :
    (mixedColumnExtendIso K p).hom.f q =
      (((-1 : ℤˣ) ^ p) ^ q) • 𝟙 ((K.extend (c' := ComplexShape.down ℕ)
        (ComplexShape.embeddingDown'Add (1 : ℕ) p)).X q) := rfl

/-- Original chain maps commute with the unit-diagonal column comparisons. -/
@[reassoc]
theorem mixedColumnMap_comp_extendIso {K L : ChainComplex C ℕ} (f : K ⟶ L) (p : ℕ) :
    mixedColumnMap f p ≫ (mixedColumnExtendIso L p).hom =
      (mixedColumnExtendIso K p).hom ≫
        HomologicalComplex.extendMap f (c' := ComplexShape.down ℕ)
          (ComplexShape.embeddingDown'Add (1 : ℕ) p) := by
  apply HomologicalComplex.hom_ext
  intro q
  change (HomologicalComplex.extendMap f (c' := ComplexShape.down ℕ)
        (ComplexShape.embeddingDown'Add (1 : ℕ) p)).f q ≫
      (((-1 : ℤˣ) ^ p) ^ q • 𝟙 _) =
    (((-1 : ℤˣ) ^ p) ^ q • 𝟙 _) ≫ (HomologicalComplex.extendMap f (c' := ComplexShape.down ℕ)
        (ComplexShape.embeddingDown'Add (1 : ℕ) p)).f q
  simp only [Linear.units_smul_comp, Linear.comp_units_smul,
    Category.id_comp, Category.comp_id]

section QuasiIsomorphisms

variable {D : Type u} [Category.{v} D] [Abelian D] {K' L' : ChainComplex D ℕ}

/-- An original quasi-isomorphism induces a quasi-isomorphism on every actual signed column. -/
theorem quasiIso_mixedColumnMap (f : K' ⟶ L') (hf : QuasiIso f) (p : ℕ) :
    QuasiIso (mixedColumnMap f p) := by
  let _ : QuasiIso f := hf
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) p
  let _ : QuasiIso (HomologicalComplex.extendMap f E) :=
    (HomologicalComplex.quasiIso_extendMap_iff (φ := f) (e := E)).2 hf
  have h : QuasiIso (mixedColumnMap f p ≫ (mixedColumnExtendIso L' p).hom) := by
    rw [mixedColumnMap_comp_extendIso]
    infer_instance
  let _ : QuasiIso (mixedColumnMap f p ≫ (mixedColumnExtendIso L' p).hom) := h
  exact quasiIso_of_comp_right (mixedColumnMap f p) (mixedColumnExtendIso L' p).hom

/-- The existing first-quadrant theorem applies to the original mixed column maps. -/
theorem quasiIso_total_mixedBicomplexMap (f : K' ⟶ L')
    (H₁ : Homotopy (0 : K' ⟶ K') 0) (H₂ : Homotopy (0 : L' ⟶ L') 0)
    (h₁ : ∀ n, H₁.hom n (n + 1) ≫ H₁.hom (n + 1) (n + 2) = 0)
    (h₂ : ∀ n, H₂.hom n (n + 1) ≫ H₂.hom (n + 1) (n + 2) = 0)
    (hComponent : ∀ n, f.f n ≫ H₂.hom n (n + 1) = H₁.hom n (n + 1) ≫ f.f (n + 1))
    (hf : QuasiIso f) :
    QuasiIso (HomologicalComplex₂.total.map
      (mixedBicomplexMap (H := H₁) (hSquare := h₁) (f := f)
        (H' := H₂) (hSquare' := h₂) (hComponent := hComponent))
      (ComplexShape.down ℕ)) := by
  apply HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant
  intro p
  exact quasiIso_mixedColumnMap f hf p

end QuasiIsomorphisms

section FunctorColumns

universe x

variable {D : Type w} [Category.{x} D] [Preadditive D] [HasZeroObject D]

/-- Native supported coordinates commute with an additive functor; unsupported cells remain zero. -/
def mixedColumnFunctorObjIso (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : ChainComplex C ℕ) (p q : ℕ) :
    F.obj ((mixedColumn K p).X q) ≅
      (mixedColumn ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) p).X q := by
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) p
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let e : L.extend E ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (K.extend E) :=
    (F.mapHomologicalComplexExtendIso E).app K
  exact ((HomologicalComplex.eval D (ComplexShape.down ℕ) q).mapIso e).symm

/-- The forward supported coordinate is the mapped source coordinate and target inverse. -/
theorem mixedColumnFunctorObjIso_hom_eq (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : ChainComplex C ℕ) (p n q : ℕ) (h : n + p = q) :
    (mixedColumnFunctorObjIso F K p q).hom =
      F.map (mixedColumnIso K p n q h).hom ≫
        (mixedColumnIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) p n q h).inv := by
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) p
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let e : (L.extend E).X q ≅ F.obj ((K.extend E).X q) :=
    (HomologicalComplex.eval D (ComplexShape.down ℕ) q).mapIso
      ((F.mapHomologicalComplexExtendIso E).app K)
  let a := K.extendXIso E h
  let b := L.extendXIso E h
  have he : e.hom ≫ F.map a.hom = b.hom :=
    F.mapHomologicalComplexExtendIso_hom_app_f E K n q h
  change e.inv = F.map a.hom ≫ b.inv
  apply (cancel_mono b.hom).1
  calc
    e.inv ≫ b.hom = e.inv ≫ (e.hom ≫ F.map a.hom) :=
      congrArg (fun f => e.inv ≫ f) he.symm
    _ = F.map a.hom := e.inv_hom_id_assoc _
    _ = (F.map a.hom ≫ b.inv) ≫ b.hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse supported coordinate restores the original zero-extension object. -/
theorem mixedColumnFunctorObjIso_inv_eq (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : ChainComplex C ℕ) (p n q : ℕ) (h : n + p = q) :
    (mixedColumnFunctorObjIso F K p q).inv =
      (mixedColumnIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) p n q h).hom ≫
        F.map (mixedColumnIso K p n q h).inv := by
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) p
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let e : (L.extend E).X q ≅ F.obj ((K.extend E).X q) :=
    (HomologicalComplex.eval D (ComplexShape.down ℕ) q).mapIso
      ((F.mapHomologicalComplexExtendIso E).app K)
  let a := K.extendXIso E h
  let b := L.extendXIso E h
  have he : e.hom ≫ F.map a.hom = b.hom :=
    F.mapHomologicalComplexExtendIso_hom_app_f E K n q h
  change e.hom = b.hom ≫ F.map a.inv
  apply (cancel_mono (F.map a.hom)).1
  calc
    e.hom ≫ F.map a.hom = b.hom := he
    _ = (b.hom ≫ F.map a.inv) ≫ F.map a.hom := by
      rw [Category.assoc, ← F.map_comp, a.inv_hom_id, F.map_id]
      simpa only [L, Functor.mapHomologicalComplex_obj_X] using (Category.comp_id b.hom).symm

/-- The original signed translated column commutes with any additive functor. -/
def mixedColumnFunctorIso (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) (p : ℕ) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (mixedColumn K p) ≅
      mixedColumn ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) p := by
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) p
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let e : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (K.extend E) ≅
      L.extend E := ((F.mapHomologicalComplexExtendIso E).app K).symm
  refine HomologicalComplex.Hom.isoOfComponents (mixedColumnFunctorObjIso F K p) ?_
  intro i j _
  let s : ℤˣ := (-1 : ℤˣ) ^ p
  let d : (K.extend E).X i ⟶ (K.extend E).X j := (K.extend E).d i j
  have hs : F.map (s • d) = s • F.map d := by
    simpa only [Units.smul_def] using (F.map_zsmul (f := d) (r := (s : ℤ)))
  change e.hom.f i ≫ (s • (L.extend E).d i j) = F.map (s • d) ≫ e.hom.f j
  rw [hs, Linear.comp_units_smul, Linear.units_smul_comp]
  exact congrArg (fun f : F.obj ((K.extend E).X i) ⟶ (L.extend E).X j => s • f)
    (e.hom.comm i j)

/-- The column comparison retains its actual component coordinate map. -/
@[simp]
theorem mixedColumnFunctorIso_hom_f (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) (p q : ℕ) :
    (mixedColumnFunctorIso F K p).hom.f q = (mixedColumnFunctorObjIso F K p q).hom := by
  simp only [mixedColumnFunctorIso, HomologicalComplex.Hom.isoOfComponents_hom_f]

/-- The inverse column map uses the same supported-coordinate inverse. -/
@[simp]
theorem mixedColumnFunctorIso_inv_f (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) (p q : ℕ) :
    (mixedColumnFunctorIso F K p).inv.f q = (mixedColumnFunctorObjIso F K p q).inv := by
  simp only [mixedColumnFunctorIso, HomologicalComplex.Hom.isoOfComponents_inv_f]

/-- The column comparison is natural for every actual original chain map. -/
theorem mixedColumnFunctorIso_hom_naturality (F : C ⥤ D) [F.Additive]
    {K L : ChainComplex C ℕ} (f : K ⟶ L) (p : ℕ) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (mixedColumnMap f p) ≫
        (mixedColumnFunctorIso F L p).hom =
      (mixedColumnFunctorIso F K p).hom ≫
        mixedColumnMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f) p := by
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) p
  let e := F.mapHomologicalComplexExtendIso E
  let FL := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L
  have hn : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (HomologicalComplex.extendMap f E) ≫ e.inv.app L =
      e.inv.app K ≫ HomologicalComplex.extendMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f) E :=
    e.inv.naturality f
  apply HomologicalComplex.hom_ext
  intro q
  have hq := congrArg (fun g :
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (K.extend E) ⟶ FL.extend E =>
        g.f q) hn
  change F.map ((HomologicalComplex.extendMap f E).f q) ≫ (e.inv.app L).f q =
    (e.inv.app K).f q ≫
      (HomologicalComplex.extendMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f) E).f q
    at hq
  have hK : (mixedColumnFunctorObjIso F K p q).hom = (e.inv.app K).f q := rfl
  have hL : (mixedColumnFunctorObjIso F L p q).hom = (e.inv.app L).f q := rfl
  change F.map ((HomologicalComplex.extendMap f E).f q) ≫
      (mixedColumnFunctorIso F L p).hom.f q =
    (mixedColumnFunctorIso F K p).hom.f q ≫
      (HomologicalComplex.extendMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map f) E).f q
  rw [mixedColumnFunctorIso_hom_f, mixedColumnFunctorIso_hom_f, hL, hK]
  exact hq

omit [HasZeroObject C] [HasZeroObject D] in
/-- The target square-zero law is from the mapped source components. -/
theorem mixedFunctorHomotopySquare (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : ChainComplex C ℕ) (H : Homotopy (0 : K ⟶ K) 0)
    (hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0)
    (H' : Homotopy
      (0 : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) 0)
    (hComponent : ∀ n, H'.hom n (n + 1) = F.map (H.hom n (n + 1))) (n : ℕ) :
    H'.hom n (n + 1) ≫ H'.hom (n + 1) (n + 2) = 0 :=
  (congrArg₂ (fun f g => f ≫ g) (hComponent n) (hComponent (n + 1))).trans
    ((F.map_comp _ _).symm.trans
      ((congrArg (fun f => F.map f) (hSquare n)).trans
        (F.map_zero (K.X n) (K.X (n + 2)))))

/-- Native mapped columns and the mapped degree-one components give the same bicomplex. -/
def mixedBicomplexFunctorIso (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) (H : Homotopy (0 : K ⟶ K) 0)
    (hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0)
    (H' : Homotopy
      (0 : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) 0)
    (hComponent : ∀ n, H'.hom n (n + 1) = F.map (H.hom n (n + 1))) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (mixedBicomplex K H hSquare) ≅
      mixedBicomplex ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) H'
        (mixedFunctorHomotopySquare F K H hSquare H' hComponent) := by
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  refine HomologicalComplex.Hom.isoOfComponents (mixedColumnFunctorIso F K) ?_
  intro i p hip
  change p + 1 = i at hip
  subst i
  simp only [mixedBicomplex, Functor.mapHomologicalComplex_obj_d, ChainComplex.of_d]
  change (mixedColumnFunctorIso F K (p + 1)).hom ≫ mixedHorizontalMap L H' p =
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (mixedHorizontalMap K H p) ≫
      (mixedColumnFunctorIso F K p).hom
  apply HomologicalComplex.hom_ext
  intro q
  by_cases hq : p + 1 ≤ q
  · let n := q - (p + 1)
    have hn : n + (p + 1) = q := by dsimp only [n]; omega
    have hn' : (n + 1) + p = q := by omega
    let a := mixedColumnIso K (p + 1) n q hn
    let b := mixedColumnIso K p (n + 1) q hn'
    let a' := mixedColumnIso L (p + 1) n q hn
    let b' := mixedColumnIso L p (n + 1) q hn'
    let A := F.mapIso a
    let B := F.mapIso b
    let δ : F.obj (K.X n) ⟶ F.obj (K.X (n + 1)) := F.map (H.hom n (n + 1))
    have hSource : (mixedHorizontalMap K H p).f q =
        a.hom ≫ H.hom n (n + 1) ≫ b.inv :=
      mixedHorizontalComponent_eq K H p n q hn
    have hMap :
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          (mixedHorizontalMap K H p)).f q = A.hom ≫ δ ≫ B.inv :=
      (congrArg (fun f => F.map f) hSource).trans
        ((F.map_comp a.hom _).trans
          (congrArg (fun f => A.hom ≫ f) (F.map_comp _ b.inv)))
    have hTarget : (mixedHorizontalMap L H' p).f q = a'.hom ≫ δ ≫ b'.inv :=
      (mixedHorizontalComponent_eq L H' p n q hn).trans
        (congrArg (fun f => a'.hom ≫ f ≫ b'.inv) (hComponent n))
    have hi : (mixedColumnFunctorIso F K (p + 1)).hom.f q = A.hom ≫ a'.inv := by
      rw [mixedColumnFunctorIso_hom_f]
      exact mixedColumnFunctorObjIso_hom_eq F K (p + 1) n q hn
    have hj : (mixedColumnFunctorIso F K p).hom.f q = B.hom ≫ b'.inv := by
      rw [mixedColumnFunctorIso_hom_f]
      exact mixedColumnFunctorObjIso_hom_eq F K p (n + 1) q hn'
    change (mixedColumnFunctorIso F K (p + 1)).hom.f q ≫
        (mixedHorizontalMap L H' p).f q =
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
        (mixedHorizontalMap K H p)).f q ≫ (mixedColumnFunctorIso F K p).hom.f q
    calc
      _ = (A.hom ≫ a'.inv) ≫ (a'.hom ≫ δ ≫ b'.inv) :=
        congrArg₂ (fun f g => f ≫ g) hi hTarget
      _ = A.hom ≫ δ ≫ b'.inv := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = (A.hom ≫ δ ≫ B.inv) ≫ (B.hom ≫ b'.inv) := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = _ := congrArg₂ (fun f g => f ≫ g) hMap.symm hj.symm
  · have hZero : IsZero (F.obj ((mixedColumn K (p + 1)).X q)) :=
      (mixedColumn_isZero L (p + 1) q (by omega)).of_iso
        (mixedColumnFunctorObjIso F K (p + 1) q)
    exact hZero.eq_of_src _ _

/-- Every mapped-column component retains the original column comparison. -/
@[simp]
theorem mixedBicomplexFunctorIso_hom_f (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) (H : Homotopy (0 : K ⟶ K) 0)
    (hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0)
    (H' : Homotopy
      (0 : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) 0)
    (hComponent : ∀ n, H'.hom n (n + 1) = F.map (H.hom n (n + 1))) (p : ℕ) :
    (mixedBicomplexFunctorIso F K H hSquare H' hComponent).hom.f p =
      (mixedColumnFunctorIso F K p).hom := by
  simp only [mixedBicomplexFunctorIso, HomologicalComplex.Hom.isoOfComponents_hom_f]

/-- The inverse mapped bicomplex restores each original column through its inverse. -/
@[simp]
theorem mixedBicomplexFunctorIso_inv_f (F : C ⥤ D) [F.Additive]
    (K : ChainComplex C ℕ) (H : Homotopy (0 : K ⟶ K) 0)
    (hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0)
    (H' : Homotopy
      (0 : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) 0)
    (hComponent : ∀ n, H'.hom n (n + 1) = F.map (H.hom n (n + 1))) (p : ℕ) :
    (mixedBicomplexFunctorIso F K H hSquare H' hComponent).inv.f p =
      (mixedColumnFunctorIso F K p).inv := by
  simp only [mixedBicomplexFunctorIso, HomologicalComplex.Hom.isoOfComponents_inv_f]

universe y z

variable {E : Type y} [Category.{z} E] [Preadditive E] [HasZeroObject E]

/-- An actual map between two functor images intertwining the mapped atoms gives a mixed map. -/
def mixedBicomplexFunctorMap (F : C ⥤ E) [F.Additive] (G : D ⥤ E) [G.Additive]
    (K : ChainComplex C ℕ) (L : ChainComplex D ℕ)
    (H : Homotopy (0 : K ⟶ K) 0) (H' : Homotopy (0 : L ⟶ L) 0)
    (hSquare : ∀ n, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0)
    (hSquare' : ∀ n, H'.hom n (n + 1) ≫ H'.hom (n + 1) (n + 2) = 0)
    (HF : Homotopy
      (0 : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) 0)
    (HG : Homotopy
      (0 : (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj L ⟶
        (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj L) 0)
    (hF : ∀ n, HF.hom n (n + 1) = F.map (H.hom n (n + 1)))
    (hG : ∀ n, HG.hom n (n + 1) = G.map (H'.hom n (n + 1)))
    (φ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj L)
    (hφ : ∀ n, φ.f n ≫ HG.hom n (n + 1) = HF.hom n (n + 1) ≫ φ.f (n + 1)) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (mixedBicomplex K H hSquare) ⟶
        ((G.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (mixedBicomplex L H' hSquare') := by
  let FK := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let GL := (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj L
  let hFK := mixedFunctorHomotopySquare F K H hSquare HF hF
  let hGL := mixedFunctorHomotopySquare G L H' hSquare' HG hG
  let eF := mixedBicomplexFunctorIso F K H hSquare HF hF
  let eG := mixedBicomplexFunctorIso G L H' hSquare' HG hG
  let m : mixedBicomplex FK HF hFK ⟶ mixedBicomplex GL HG hGL :=
    mixedBicomplexMap (H := HF) (hSquare := hFK) (f := φ)
      (H' := HG) (hSquare' := hGL) (hComponent := hφ)
  exact eF.hom ≫ m ≫ eG.inv

/-- The map between functor images retains the supported source and target coordinates. -/
theorem mixedBicomplexFunctorMap_component (F : C ⥤ E) [F.Additive]
    (G : D ⥤ E) [G.Additive] (K : ChainComplex C ℕ) (L : ChainComplex D ℕ)
    (H : Homotopy (0 : K ⟶ K) 0) (H' : Homotopy (0 : L ⟶ L) 0)
    (hSquare : ∀ j, H.hom j (j + 1) ≫ H.hom (j + 1) (j + 2) = 0)
    (hSquare' : ∀ j, H'.hom j (j + 1) ≫ H'.hom (j + 1) (j + 2) = 0)
    (HF : Homotopy
      (0 : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
        (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K) 0)
    (HG : Homotopy
      (0 : (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj L ⟶
        (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj L) 0)
    (hF : ∀ j, HF.hom j (j + 1) = F.map (H.hom j (j + 1)))
    (hG : ∀ j, HG.hom j (j + 1) = G.map (H'.hom j (j + 1)))
    (φ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ⟶
      (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj L)
    (hφ : ∀ j, φ.f j ≫ HG.hom j (j + 1) = HF.hom j (j + 1) ≫ φ.f (j + 1))
    (p n q : ℕ) (h : n + p = q) :
    ((mixedBicomplexFunctorMap F G K L H H' hSquare hSquare' HF HG hF hG φ hφ).f p).f q =
      F.map (mixedColumnIso K p n q h).hom ≫ φ.f n ≫
        G.map (mixedColumnIso L p n q h).inv := by
  let FK := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  let GL := (G.mapHomologicalComplex (ComplexShape.down ℕ)).obj L
  let hFK := mixedFunctorHomotopySquare F K H hSquare HF hF
  let hGL := mixedFunctorHomotopySquare G L H' hSquare' HG hG
  let eF := mixedBicomplexFunctorIso F K H hSquare HF hF
  let eG := mixedBicomplexFunctorIso G L H' hSquare' HG hG
  let m : mixedBicomplex FK HF hFK ⟶ mixedBicomplex GL HG hGL :=
    mixedBicomplexMap (H := HF) (hSquare := hFK) (f := φ)
      (H' := HG) (hSquare' := hGL) (hComponent := hφ)
  let M := mixedBicomplexFunctorMap F G K L H H' hSquare hSquare' HF HG hF hG φ hφ
  let a := mixedColumnIso K p n q h
  let b := mixedColumnIso L p n q h
  let a' := mixedColumnIso FK p n q h
  let b' := mixedColumnIso GL p n q h
  have hPack : M = eF.hom ≫ m ≫ eG.inv := rfl
  have hFields : (M.f p).f q = (eF.hom.f p).f q ≫ (m.f p).f q ≫ (eG.inv.f p).f q :=
    (congrArg (fun f => (f.f p).f q) hPack).trans (by rfl)
  have heF : (eF.hom.f p).f q = F.map a.hom ≫ a'.inv := by
    simpa only [eF, mixedBicomplexFunctorIso_hom_f, mixedColumnFunctorIso_hom_f,
      a, a', FK] using mixedColumnFunctorObjIso_hom_eq F K p n q h
  have hm : (m.f p).f q = a'.hom ≫ φ.f n ≫ b'.inv := by
    simpa only [m, mixedBicomplexMap_f, a', b', FK, GL] using
      mixedColumnMap_f_eq φ p n q h
  have heG : (eG.inv.f p).f q = b'.hom ≫ G.map b.inv := by
    simpa only [eG, mixedBicomplexFunctorIso_inv_f, mixedColumnFunctorIso_inv_f,
      b, b', GL] using mixedColumnFunctorObjIso_inv_eq G L p n q h
  change (M.f p).f q = F.map a.hom ≫ φ.f n ≫ G.map b.inv
  exact hFields.trans
    ((congrArg₂ (fun f g => f ≫ g) heF (congrArg₂ (fun f g => f ≫ g) hm heG)).trans
      (by simp only [Category.assoc, Iso.inv_hom_id_assoc]))

end FunctorColumns

end ChainComplex
