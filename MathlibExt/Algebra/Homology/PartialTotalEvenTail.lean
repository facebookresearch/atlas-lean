/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import MathlibExt.Algebra.Homology.PartialTotalCokernel
public import MathlibExt.Algebra.Homology.Embedding.DownNatToIntShift
public import MathlibExt.Algebra.Homology.Embedding.Composition
public import MathlibExt.Algebra.Homology.TotalComplexExact
public import MathlibExt.Algebra.Homology.TotalComplexDownNat

/-!
# Total coordinates of outer zero extensions

Zero extension of the outer coordinate by s identifies total degree n
with original degree q when q + s = n, and gives zero terms below s.
The coordinate maps respect the translation signs in both differentials.
For even s they form a natural chain isomorphism.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v

/-- A nominal down-Nat type for the same original native translation embedding. -/
abbrev partialTotalOuterEmbedding (s : ℕ) :
    (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.embeddingDown'Add (1 : ℕ) s

instance partialTotalOuterEmbedding_isRelIff (s : ℕ) :
    (partialTotalOuterEmbedding s).IsRelIff :=
  inferInstanceAs ((ComplexShape.embeddingDown'Add (1 : ℕ) s).IsRelIff)

instance partialTotalOuterEmbedding_isTruncLE (s : ℕ) :
    (partialTotalOuterEmbedding s).IsTruncLE :=
  inferInstanceAs ((ComplexShape.embeddingDown'Add (1 : ℕ) s).IsTruncLE)

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (B : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))

/-- The finite total of a native outer zero extension has no terms below its actual offset. -/
theorem isZero_outerExtensionTotal_X (s n : ℕ) (hn : n < s) :
    IsZero ((HomologicalComplex₂.total (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
      (ComplexShape.down ℕ)).X n) := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  let D : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := B.extend e
  apply (IsZero.iff_id_eq_zero _).mpr
  apply total.hom_ext
  intro p q hpq
  have hp : p < s := by change p + q = n at hpq; omega
  have hColumn : IsZero (D.X p) := B.isZero_extend_X e p (by
    intro i hi
    change i + s = p at hi
    omega)
  have hCell : IsZero ((D.X p).X q) :=
    (HomologicalComplex.eval C (ComplexShape.down ℕ) q).map_isZero hColumn
  exact hCell.eq_of_src _ _

/-- The original degree-q finite total is the total in degree q+s of the native outer
zero extension. No chain-comparison or periodicity is supplied as data. -/
def outerExtensionTotalXIso (s n q : ℕ) (h : q + s = n) :
    (HomologicalComplex₂.total (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
      (ComplexShape.down ℕ)).X n ≅ (B.total (ComplexShape.down ℕ)).X q where
  hom := totalDesc (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
    (c₁₂ := ComplexShape.down ℕ) (fun i j hij =>
      if hi : s ≤ i then
        ((B.extendXIso (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s)
          (show (i - s) + s = i from Nat.sub_add_cancel hi)).hom.f j) ≫
          B.ιTotal (ComplexShape.down ℕ) (i - s) j q (by
            change (i - s) + j = q
            change i + j = n at hij
            omega)
      else 0)
  inv := totalDesc B (c₁₂ := ComplexShape.down ℕ) (fun i j hij =>
    ((B.extendXIso (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s)
      (show i + s = i + s from rfl)).inv.f j) ≫
        HomologicalComplex₂.ιTotal (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
          (ComplexShape.down ℕ) (i + s) j n (by
            change (i + s) + j = n
            change i + j = q at hij
            omega))
  hom_inv_id := by
    let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := partialTotalOuterEmbedding s
    let D : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := B.extend e
    apply total.hom_ext
    intro i j hij
    by_cases hi : s ≤ i
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + s :=
        ⟨i - s, (Nat.sub_add_cancel hi).symm⟩
      have hk : s ≤ k + s := by omega
      have hCancel (r t : ℕ) (ht : e.f r = t) (htj : t + j = n) :
          (B.extendXIso e ht).hom.f j ≫
            (B.extendXIso e (rfl : e.f r = e.f r)).inv.f j ≫
              D.ιTotal (ComplexShape.down ℕ) (e.f r) j n
                (by change e.f r + j = n; rw [ht]; exact htj) =
            D.ιTotal (ComplexShape.down ℕ) t j n htj := by
        subst t
        let a : D.X (e.f r) ≅ B.X r := B.extendXIso e rfl
        let aCell : (D.X (e.f r)).X j ≅ (B.X r).X j :=
          (HomologicalComplex.eval C (ComplexShape.down ℕ) j).mapIso a
        change aCell.hom ≫ aCell.inv ≫
            D.ιTotal (ComplexShape.down ℕ) (e.f r) j n htj =
          D.ιTotal (ComplexShape.down ℕ) (e.f r) j n htj
        exact aCell.hom_inv_id_assoc _
      rw [ι_totalDesc_assoc, dite_eq_left hk, Category.assoc, ι_totalDesc]
      simp only [Category.comp_id]
      exact hCancel ((k + s) - s) (k + s)
        (by change ((k + s) - s) + s = k + s; exact Nat.sub_add_cancel hk) hij
    · have hColumn : IsZero (D.X i) := B.isZero_extend_X e i (by
        intro k hk
        change k + s = i at hk
        omega)
      have hCell : IsZero ((D.X i).X j) :=
        (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero hColumn
      exact hCell.eq_of_src _ _
  inv_hom_id := by
    let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := partialTotalOuterEmbedding s
    let D : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := B.extend e
    apply total.hom_ext
    intro i j hij
    have hi : s ≤ i + s := by omega
    have hCancel (r : ℕ) (hr : e.f r = e.f i) (hrj : r + j = q) :
        (B.extendXIso e (rfl : e.f i = e.f i)).inv.f j ≫
          (B.extendXIso e hr).hom.f j ≫ B.ιTotal (ComplexShape.down ℕ) r j q hrj =
          B.ιTotal (ComplexShape.down ℕ) i j q hij := by
      have hri : r = i := e.injective_f hr
      subst r
      let a : D.X (e.f i) ≅ B.X i := B.extendXIso e rfl
      let aCell : (D.X (e.f i)).X j ≅ (B.X i).X j :=
        (HomologicalComplex.eval C (ComplexShape.down ℕ) j).mapIso a
      change aCell.inv ≫ aCell.hom ≫ B.ιTotal (ComplexShape.down ℕ) i j q hij =
        B.ιTotal (ComplexShape.down ℕ) i j q hij
      exact aCell.inv_hom_id_assoc _
    rw [ι_totalDesc_assoc, Category.assoc, ι_totalDesc]
    simp only [dite_eq_left hi, Category.comp_id]
    exact hCancel ((i + s) - s)
      (by change ((i + s) - s) + s = i + s; exact Nat.sub_add_cancel hi)
      (by change ((i + s) - s) + j = q; change i + j = q at hij; omega)

/-- Forward total coordinates preserve each actual surviving coprojection. -/
@[reassoc]
theorem outerExtensionTotalXIso_hom_ι (s n q i j : ℕ) (h : q + s = n)
    (hij : i + j = q) :
    (B.extendXIso (c' := ComplexShape.down ℕ)
      (partialTotalOuterEmbedding s) rfl).inv.f j ≫
        HomologicalComplex₂.ιTotal (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
          (ComplexShape.down ℕ) (i + s) j n (by change (i + s) + j = n; omega) ≫
        (outerExtensionTotalXIso B s n q h).hom =
      B.ιTotal (ComplexShape.down ℕ) i j q hij := by
  have hInv : B.ιTotal (ComplexShape.down ℕ) i j q hij ≫
      (outerExtensionTotalXIso B s n q h).inv =
        (B.extendXIso (c' := ComplexShape.down ℕ)
          (partialTotalOuterEmbedding s) rfl).inv.f j ≫
            HomologicalComplex₂.ιTotal
              (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
              (ComplexShape.down ℕ) (i + s) j n
              (by change (i + s) + j = n; omega) := by
    dsimp only [outerExtensionTotalXIso]
    exact ι_totalDesc B (c₁₂ := ComplexShape.down ℕ) _ i j hij
  exact (Category.assoc _ _ _).symm.trans
    ((outerExtensionTotalXIso B s n q h).eq_comp_inv.mp hInv.symm)

/-- Inverse coordinates put the original coprojection in its true translated degree. -/
@[reassoc]
theorem outerExtensionTotalXIso_inv_ι (s n q i j : ℕ) (h : q + s = n)
    (hij : i + j = q) :
    B.ιTotal (ComplexShape.down ℕ) i j q hij ≫
        (outerExtensionTotalXIso B s n q h).inv =
      (B.extendXIso (c' := ComplexShape.down ℕ)
        (partialTotalOuterEmbedding s) rfl).inv.f j ≫
        HomologicalComplex₂.ιTotal (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
          (ComplexShape.down ℕ) (i + s) j n (by change (i + s) + j = n; omega) := by
  dsimp only [outerExtensionTotalXIso]
  exact ι_totalDesc B (c₁₂ := ComplexShape.down ℕ) _ i j hij

/-- Evaluation of the forward comparison on a surviving extended cell uses the extension coordinate followed by the original total coprojection. -/
@[reassoc]
theorem ι_outerExtensionTotalXIso_hom (s n q i j : ℕ) (h : q + s = n)
    (hij : i + j = q) :
    HomologicalComplex₂.ιTotal (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
        (ComplexShape.down ℕ) (i + s) j n (by change (i + s) + j = n; omega) ≫
        (outerExtensionTotalXIso B s n q h).hom =
      (B.extendXIso (c' := ComplexShape.down ℕ)
        (partialTotalOuterEmbedding s) rfl).hom.f j ≫
        B.ιTotal (ComplexShape.down ℕ) i j q hij := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  let D : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := B.extend e
  let a : D.X (e.f i) ≅ B.X i := B.extendXIso e rfl
  let aCell : (D.X (e.f i)).X j ≅ (B.X i).X j :=
    (HomologicalComplex.eval C (ComplexShape.down ℕ) j).mapIso a
  exact aCell.inv_comp_eq.mp
    (outerExtensionTotalXIso_hom_ι B s n q i j h hij)

/-- Outer zero extension does not change the horizontal total differential in its actual
positive-degree coordinates. -/
theorem outerExtensionTotalXIso_D₁ (s n₀ n₁ q₀ q₁ : ℕ)
    (h₀ : q₀ + s = n₀) (h₁ : q₁ + s = n₁)
    (hq : (ComplexShape.down ℕ).Rel q₀ q₁) :
    HomologicalComplex₂.D₁ (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
        (ComplexShape.down ℕ) n₀ n₁ ≫ (outerExtensionTotalXIso B s n₁ q₁ h₁).hom =
      (outerExtensionTotalXIso B s n₀ q₀ h₀).hom ≫
        B.D₁ (ComplexShape.down ℕ) q₀ q₁ := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  let D : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := B.extend e
  have hq' : q₁ + 1 = q₀ := hq
  apply total.hom_ext
  intro p j hpj
  by_cases hp : s ≤ p
  · obtain ⟨i, rfl⟩ : ∃ i, p = i + s :=
      ⟨p - s, (Nat.sub_add_cancel hp).symm⟩
    have hij : i + j = q₀ := by change (i + s) + j = n₀ at hpj; omega
    rw [D.ι_D₁_assoc,
      ι_outerExtensionTotalXIso_hom_assoc B s n₀ q₀ i j h₀ hij,
      B.ι_D₁ (ComplexShape.down ℕ) q₀ q₁ i j hij]
    cases i with
    | zero =>
        have hD : D.d₁ (ComplexShape.down ℕ) (0 + s) j n₁ = 0 := by
          by_cases hr : (ComplexShape.down ℕ).Rel (0 + s)
              ((ComplexShape.down ℕ).next (0 + s))
          · rw [D.d₁_eq' (ComplexShape.down ℕ) hr j n₁]
            have hd : D.d (0 + s) ((ComplexShape.down ℕ).next (0 + s)) = 0 :=
              B.extend_d_from_eq_zero e (0 + s)
                ((ComplexShape.down ℕ).next (0 + s)) 0 rfl
                (by simp [ComplexShape.down_Rel])
            rw [hd, HomologicalComplex.zero_f, zero_comp, smul_zero]
          · exact D.d₁_eq_zero (ComplexShape.down ℕ) (0 + s) j n₁ hr
        have hB : B.d₁ (ComplexShape.down ℕ) 0 j q₁ = 0 :=
          B.d₁_eq_zero (ComplexShape.down ℕ) 0 j q₁
            (by simp [ComplexShape.down_Rel])
        rw [hD, hB, zero_comp, comp_zero]
    | succ i =>
        have hp' : (ComplexShape.down ℕ).Rel ((i + 1) + s) (i + s) := by
          change (i + s) + 1 = (i + 1) + s
          omega
        have hsum : (i + s) + j = n₁ := by omega
        have hsum' : i + j = q₁ := by omega
        rw [D.d₁_eq (ComplexShape.down ℕ) hp' j n₁ hsum,
          B.d₁_eq (ComplexShape.down ℕ)
            (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl) j q₁ hsum']
        have hε₀ : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) ((i + 1) + s, j) = 1 := rfl
        have hε₁ : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) (i + 1, j) = 1 := rfl
        rw [hε₀, hε₁, one_smul, one_smul, Category.assoc,
          ι_outerExtensionTotalXIso_hom]
        let a₀ := B.extendXIso e (show (i + 1) + s = (i + 1) + s from rfl)
        let a₁ := B.extendXIso e (show i + s = i + s from rfl)
        have hd : (D.d ((i + 1) + s) (i + s)).f j =
            a₀.hom.f j ≫ (B.d (i + 1) i).f j ≫ a₁.inv.f j := by
          have hh := HomologicalComplex.congr_hom (B.extend_d_eq e
            (show (i + 1) + s = (i + 1) + s from rfl)
            (show i + s = i + s from rfl)) j
          simpa only [HomologicalComplex.comp_f] using hh
        have ha : a₁.inv.f j ≫ a₁.hom.f j = 𝟙 _ := by
          have hh := HomologicalComplex.congr_hom a₁.inv_hom_id j
          simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using hh
        have hMap : (D.d ((i + 1) + s) (i + s)).f j ≫ a₁.hom.f j =
            a₀.hom.f j ≫ (B.d (i + 1) i).f j := by
          rw [hd]
          simp only [Category.assoc]
          rw [ha, Category.comp_id]
        simpa only [Category.assoc] using
          congrArg (fun m => m ≫ B.ιTotal
            (ComplexShape.down ℕ) i j q₁ hsum') hMap
  · have hColumn : IsZero (D.X p) := B.isZero_extend_X e p (by
      intro i hi
      change i + s = p at hi
      omega)
    have hCell : IsZero ((D.X p).X j) :=
      (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero hColumn
    exact hCell.eq_of_src _ _

/-- The vertical total differential gains precisely the native offset sign. For an
even outer offset this scalar is one. -/
theorem outerExtensionTotalXIso_D₂ (s n₀ n₁ q₀ q₁ : ℕ)
    (h₀ : q₀ + s = n₀) (h₁ : q₁ + s = n₁)
    (hq : (ComplexShape.down ℕ).Rel q₀ q₁) :
    HomologicalComplex₂.D₂ (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
        (ComplexShape.down ℕ) n₀ n₁ ≫ (outerExtensionTotalXIso B s n₁ q₁ h₁).hom =
      (ComplexShape.down ℕ).ε s •
        ((outerExtensionTotalXIso B s n₀ q₀ h₀).hom ≫
          B.D₂ (ComplexShape.down ℕ) q₀ q₁) := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  let D : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := B.extend e
  have hq' : q₁ + 1 = q₀ := hq
  apply total.hom_ext
  intro p j hpj
  by_cases hp : s ≤ p
  · obtain ⟨i, rfl⟩ : ∃ i, p = i + s :=
      ⟨p - s, (Nat.sub_add_cancel hp).symm⟩
    have hij : i + j = q₀ := by change (i + s) + j = n₀ at hpj; omega
    rw [D.ι_D₂_assoc, Linear.comp_units_smul,
      ι_outerExtensionTotalXIso_hom_assoc B s n₀ q₀ i j h₀ hij,
      B.ι_D₂ (ComplexShape.down ℕ) q₀ q₁ i j hij]
    cases j with
    | zero =>
        have hD : D.d₂ (ComplexShape.down ℕ) (i + s) 0 n₁ = 0 :=
          D.d₂_eq_zero (ComplexShape.down ℕ) (i + s) 0 n₁
            (by simp [ComplexShape.down_Rel])
        have hB : B.d₂ (ComplexShape.down ℕ) i 0 q₁ = 0 :=
          B.d₂_eq_zero (ComplexShape.down ℕ) i 0 q₁
            (by simp [ComplexShape.down_Rel])
        rw [hD, hB, zero_comp, comp_zero, smul_zero]
    | succ j =>
        have hsum : (i + s) + j = n₁ := by omega
        have hsum' : i + j = q₁ := by omega
        rw [D.d₂_eq (ComplexShape.down ℕ) (i + s)
            (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl) n₁ hsum,
          B.d₂_eq (ComplexShape.down ℕ) i
            (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl) q₁ hsum']
        let a := B.extendXIso e (show i + s = i + s from rfl)
        change ((ComplexShape.down ℕ).ε (i + s) •
            ((D.X (i + s)).d (j + 1) j ≫
              D.ιTotal (ComplexShape.down ℕ) (i + s) j n₁ hsum)) ≫
            (outerExtensionTotalXIso B s n₁ q₁ h₁).hom =
          (ComplexShape.down ℕ).ε s • (a.hom.f (j + 1) ≫
            ((ComplexShape.down ℕ).ε i •
              ((B.X i).d (j + 1) j ≫
                B.ιTotal (ComplexShape.down ℕ) i j q₁ hsum')))
        rw [Linear.units_smul_comp, Category.assoc,
          ι_outerExtensionTotalXIso_hom, Linear.comp_units_smul, smul_smul]
        have hε : (ComplexShape.down ℕ).ε (i + s) =
            (ComplexShape.down ℕ).ε s * (ComplexShape.down ℕ).ε i := by
          rw [ComplexShape.ε_add]
          exact mul_comm _ _
        rw [hε]
        have hComm : (D.X (i + s)).d (j + 1) j ≫ a.hom.f j =
            a.hom.f (j + 1) ≫ (B.X i).d (j + 1) j :=
          (a.hom.comm (j + 1) j).symm
        apply congrArg (fun m =>
          ((ComplexShape.down ℕ).ε s * (ComplexShape.down ℕ).ε i) • m)
        simpa only [Category.assoc] using congrArg
          (fun m => m ≫ B.ιTotal (ComplexShape.down ℕ) i j q₁ hsum') hComm
  · have hColumn : IsZero (D.X p) := B.isZero_extend_X e p (by
      intro i hi
      change i + s = p at hi
      omega)
    have hCell : IsZero ((D.X p).X j) :=
      (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero hColumn
    exact hCell.eq_of_src _ _

/-- The total in every degree of an outer zero extension identifies with the native
zero extension of the original total as an object. The differential sign is treated below. -/
def outerExtensionTotalDegreeIso (s n : ℕ) :
    (HomologicalComplex₂.total (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s))
      (ComplexShape.down ℕ)).X n ≅
    ((B.total (ComplexShape.down ℕ)).extend (c' := ComplexShape.down ℕ)
      (partialTotalOuterEmbedding s)).X n :=
  if hn : s ≤ n then
    outerExtensionTotalXIso B s n (n - s) (Nat.sub_add_cancel hn) ≪≫
      ((B.total (ComplexShape.down ℕ)).extendXIso (c' := ComplexShape.down ℕ)
        (partialTotalOuterEmbedding s) (Nat.sub_add_cancel hn)).symm
  else
    (isZero_outerExtensionTotal_X B s n (by omega)).iso
      ((B.total (ComplexShape.down ℕ)).isZero_extend_X
        (partialTotalOuterEmbedding s) n (by
          intro i hi
          change i + s = n at hi
          omega))

/-- Even outer zero extension commutes with the finite total complex. Both maps are
constructed from the original coprojections; degrees below the offset are zeros. -/
def evenOuterExtensionTotalIso (r : ℕ) :
    HomologicalComplex₂.total (B.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding (2 * r)))
        (ComplexShape.down ℕ) ≅
      (B.total (ComplexShape.down ℕ)).extend (c' := ComplexShape.down ℕ)
        (partialTotalOuterEmbedding (2 * r)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => outerExtensionTotalDegreeIso B (2 * r) n)
    (fun n₀ n₁ hn => by
      let s := 2 * r
      let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
        partialTotalOuterEmbedding s
      let D : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := B.extend e
      let T := B.total (ComplexShape.down ℕ)
      have hn' : n₁ + 1 = n₀ := hn
      by_cases h₀ : s ≤ n₀
      · by_cases h₁ : s ≤ n₁
        · let q₀ := n₀ - s
          let q₁ := n₁ - s
          have hq₀ : q₀ + s = n₀ := Nat.sub_add_cancel h₀
          have hq₁ : q₁ + s = n₁ := Nat.sub_add_cancel h₁
          have hq : (ComplexShape.down ℕ).Rel q₀ q₁ := by
            change q₁ + 1 = q₀
            dsimp only [q₀, q₁]
            omega
          have hε : (ComplexShape.down ℕ).ε s = 1 := by
            have hSquare : (-1 : ℤˣ) ^ 2 = 1 := by decide
            rw [ComplexShape.ε_down_ℕ]
            change (-1 : ℤˣ) ^ (2 * r) = 1
            rw [pow_mul, hSquare, one_pow]
          have hD₁ : D.D₁ (ComplexShape.down ℕ) n₀ n₁ ≫
                (outerExtensionTotalXIso B s n₁ q₁ hq₁).hom =
              (outerExtensionTotalXIso B s n₀ q₀ hq₀).hom ≫
                B.D₁ (ComplexShape.down ℕ) q₀ q₁ :=
            outerExtensionTotalXIso_D₁ B s n₀ n₁ q₀ q₁ hq₀ hq₁ hq
          have hD₂ : D.D₂ (ComplexShape.down ℕ) n₀ n₁ ≫
                (outerExtensionTotalXIso B s n₁ q₁ hq₁).hom =
              (ComplexShape.down ℕ).ε s •
                (outerExtensionTotalXIso B s n₀ q₀ hq₀).hom ≫
                  B.D₂ (ComplexShape.down ℕ) q₀ q₁ :=
            outerExtensionTotalXIso_D₂ B s n₀ n₁ q₀ q₁ hq₀ hq₁ hq
          have hTotal : (D.total (ComplexShape.down ℕ)).d n₀ n₁ ≫
                (outerExtensionTotalXIso B s n₁ q₁ hq₁).hom =
              (outerExtensionTotalXIso B s n₀ q₀ hq₀).hom ≫ T.d q₀ q₁ := by
            rw [total_d, Preadditive.add_comp, hD₁, hD₂, hε, one_smul,
              ← Preadditive.comp_add]
            rfl
          change (outerExtensionTotalDegreeIso B s n₀).hom ≫
              (T.extend e).d n₀ n₁ =
            (D.total (ComplexShape.down ℕ)).d n₀ n₁ ≫
              (outerExtensionTotalDegreeIso B s n₁).hom
          simp only [outerExtensionTotalDegreeIso, dite_eq_left h₀, dite_eq_left h₁,
            Iso.trans_hom, Iso.symm_hom]
          rw [T.extend_d_eq e hq₀ hq₁]
          change
            ((outerExtensionTotalXIso B s n₀ q₀ hq₀).hom ≫
                (T.extendXIso (c' := ComplexShape.down ℕ) e hq₀).inv) ≫
              ((T.extendXIso (c' := ComplexShape.down ℕ) e hq₀).hom ≫
                T.d q₀ q₁ ≫ (T.extendXIso (c' := ComplexShape.down ℕ) e hq₁).inv) =
            (D.total (ComplexShape.down ℕ)).d n₀ n₁ ≫
              ((outerExtensionTotalXIso B s n₁ q₁ hq₁).hom ≫
                (T.extendXIso (c' := ComplexShape.down ℕ) e hq₁).inv)
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
          simpa only [Category.assoc] using congrArg
            (fun m => m ≫ (T.extendXIso e hq₁).inv) hTotal.symm
        · have hTarget : IsZero ((T.extend e).X n₁) :=
            T.isZero_extend_X e n₁ (by
              intro i hi
              change i + s = n₁ at hi
              omega)
          exact hTarget.eq_of_tgt _ _
      · have hSource : IsZero ((D.total (ComplexShape.down ℕ)).X n₀) :=
          isZero_outerExtensionTotal_X B s n₀ (by omega)
        exact hSource.eq_of_src _ _)

section Naturality

variable {B} {L : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

/-- The object comparison commutes with every original bicomplex map. -/
@[reassoc]
theorem outerExtensionTotalXIso_hom_naturality (φ : B ⟶ L) (s n q : ℕ)
    (h : q + s = n) :
    (total.map (HomologicalComplex.extendMap (c' := ComplexShape.down ℕ) φ
        (partialTotalOuterEmbedding s)) (ComplexShape.down ℕ)).f n ≫
        (outerExtensionTotalXIso L s n q h).hom =
      (outerExtensionTotalXIso B s n q h).hom ≫
        (total.map φ (ComplexShape.down ℕ)).f q := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  let D : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := B.extend e
  let E : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := L.extend e
  let ψ := HomologicalComplex.extendMap (c' := ComplexShape.down ℕ) φ e
  apply total.hom_ext
  intro p j hpj
  by_cases hp : s ≤ p
  · obtain ⟨i, rfl⟩ : ∃ i, p = i + s :=
      ⟨p - s, (Nat.sub_add_cancel hp).symm⟩
    have hij : i + j = q := by change (i + s) + j = n at hpj; omega
    let aB := B.extendXIso e (show i + s = i + s from rfl)
    let aL := L.extendXIso e (show i + s = i + s from rfl)
    have hMap : D.ιTotal (ComplexShape.down ℕ) (i + s) j n hpj ≫
          (total.map ψ (ComplexShape.down ℕ)).f n =
        (ψ.f (i + s)).f j ≫ E.ιTotal (ComplexShape.down ℕ) (i + s) j n hpj :=
      ιTotal_map D E ψ (ComplexShape.down ℕ) (i + s) j n hpj
    have hB : D.ιTotal (ComplexShape.down ℕ) (i + s) j n hpj ≫
          (outerExtensionTotalXIso B s n q h).hom =
        aB.hom.f j ≫ B.ιTotal (ComplexShape.down ℕ) i j q hij :=
      ι_outerExtensionTotalXIso_hom B s n q i j h hij
    have hL : E.ιTotal (ComplexShape.down ℕ) (i + s) j n hpj ≫
          (outerExtensionTotalXIso L s n q h).hom =
        aL.hom.f j ≫ L.ιTotal (ComplexShape.down ℕ) i j q hij :=
      ι_outerExtensionTotalXIso_hom L s n q i j h hij
    have hOriginal : B.ιTotal (ComplexShape.down ℕ) i j q hij ≫
          (total.map φ (ComplexShape.down ℕ)).f q =
        (φ.f i).f j ≫ L.ιTotal (ComplexShape.down ℕ) i j q hij :=
      ιTotal_map B L φ (ComplexShape.down ℕ) i j q hij
    have hPoint : (ψ.f (i + s)).f j =
        aB.hom.f j ≫ (φ.f i).f j ≫ aL.inv.f j := by
      have hh := HomologicalComplex.congr_hom
        (HomologicalComplex.extendMap_f (c' := ComplexShape.down ℕ)
          φ e (show i + s = i + s from rfl)) j
      simpa only [HomologicalComplex.comp_f] using hh
    have hCancel : aL.inv.f j ≫ aL.hom.f j = 𝟙 _ := by
      have hh := HomologicalComplex.congr_hom aL.inv_hom_id j
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using hh
    calc
      _ = (ψ.f (i + s)).f j ≫
          (E.ιTotal (ComplexShape.down ℕ) (i + s) j n hpj ≫
            (outerExtensionTotalXIso L s n q h).hom) := by
        simpa only [Category.assoc] using congrArg
          (fun m => m ≫ (outerExtensionTotalXIso L s n q h).hom) hMap
      _ = (aB.hom.f j ≫ (φ.f i).f j ≫ aL.inv.f j) ≫
          aL.hom.f j ≫ L.ιTotal (ComplexShape.down ℕ) i j q hij := by
        rw [hL, hPoint]
      _ = aB.hom.f j ≫ (φ.f i).f j ≫
          L.ιTotal (ComplexShape.down ℕ) i j q hij := by
        simp only [Category.assoc]
        rw [← Category.assoc (aL.inv.f j) (aL.hom.f j)
          (L.ιTotal (ComplexShape.down ℕ) i j q hij), hCancel, Category.id_comp]
      _ = aB.hom.f j ≫ B.ιTotal (ComplexShape.down ℕ) i j q hij ≫
          (total.map φ (ComplexShape.down ℕ)).f q := by
        rw [hOriginal]
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun m => m ≫ (total.map φ (ComplexShape.down ℕ)).f q) hB.symm
  · have hColumn : IsZero (D.X p) := B.isZero_extend_X e p (by
      intro i hi
      change i + s = p at hi
      omega)
    have hCell : IsZero ((D.X p).X j) :=
      (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero hColumn
    exact hCell.eq_of_src _ _

/-- The computed chain isomorphism is natural in the original bicomplex map. -/
@[reassoc]
theorem evenOuterExtensionTotalIso_hom_naturality (φ : B ⟶ L) (r : ℕ) :
    total.map (HomologicalComplex.extendMap (c' := ComplexShape.down ℕ) φ
        (partialTotalOuterEmbedding (2 * r))) (ComplexShape.down ℕ) ≫
        (evenOuterExtensionTotalIso L r).hom =
      (evenOuterExtensionTotalIso B r).hom ≫
        HomologicalComplex.extendMap (c' := ComplexShape.down ℕ) (total.map φ (ComplexShape.down ℕ))
          (partialTotalOuterEmbedding (2 * r)) := by
  let s := 2 * r
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  let T := B.total (ComplexShape.down ℕ)
  let U := L.total (ComplexShape.down ℕ)
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : s ≤ n
  · let q := n - s
    have hq : q + s = n := Nat.sub_add_cancel hn
    have h := outerExtensionTotalXIso_hom_naturality φ s n q hq
    change (total.map (HomologicalComplex.extendMap (c' := ComplexShape.down ℕ)
      φ e) (ComplexShape.down ℕ)).f n ≫
        (outerExtensionTotalDegreeIso L s n).hom =
      (outerExtensionTotalDegreeIso B s n).hom ≫
        (HomologicalComplex.extendMap (c' := ComplexShape.down ℕ)
          (total.map φ (ComplexShape.down ℕ)) e).f n
    simp only [outerExtensionTotalDegreeIso, dite_eq_left hn,
      Iso.trans_hom, Iso.symm_hom]
    rw [HomologicalComplex.extendMap_f (c' := ComplexShape.down ℕ)
      (total.map φ (ComplexShape.down ℕ)) e hq]
    change
      (total.map (HomologicalComplex.extendMap (c' := ComplexShape.down ℕ) φ e)
          (ComplexShape.down ℕ)).f n ≫
        ((outerExtensionTotalXIso L s n q hq).hom ≫
          (U.extendXIso (c' := ComplexShape.down ℕ) e hq).inv) =
      ((outerExtensionTotalXIso B s n q hq).hom ≫
          (T.extendXIso (c' := ComplexShape.down ℕ) e hq).inv) ≫
        ((T.extendXIso (c' := ComplexShape.down ℕ) e hq).hom ≫
          (total.map φ (ComplexShape.down ℕ)).f q ≫
            (U.extendXIso (c' := ComplexShape.down ℕ) e hq).inv)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using congrArg
      (fun m => m ≫ (U.extendXIso e hq).inv) h
  · have hSource : IsZero ((HomologicalComplex₂.total (B.extend e) (ComplexShape.down ℕ)).X n) :=
      isZero_outerExtensionTotal_X B s n (by omega)
    exact hSource.eq_of_src _ _

end Naturality

end HomologicalComplex₂

namespace HomologicalComplex

universe uD vD

variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D] [HasZeroObject D]

/-- The native restriction to degrees at least s, zero-extended back, is an actual quotient
chain map. The additive Nat embedding has no incoming outside boundary. -/
def natTailProjection (K : ChainComplex D ℕ) (s : ℕ) :
    K ⟶ K.stupidTrunc (partialTotalOuterEmbedding s) := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  have hLift : (e).HasLift (𝟙 (K.restriction e)) := by
    intro j hj i' hij
    exact hj.false_of_isTruncLE.elim
  exact e.liftExtend (𝟙 (K.restriction e)) hLift

/-- A supported component is the inverse restriction/extension coordinate. -/
lemma natTailProjection_f (K : ChainComplex D ℕ) (s i i' : ℕ) (hi : i + s = i') :
    (natTailProjection K s).f i' =
      (K.restrictionXIso (c := ComplexShape.down ℕ)
        (partialTotalOuterEmbedding s) hi).inv ≫
        ((K.restriction (c := ComplexShape.down ℕ)
          (partialTotalOuterEmbedding s)).extendXIso (c' := ComplexShape.down ℕ)
          (partialTotalOuterEmbedding s) hi).inv := by
  dsimp only [natTailProjection]
  rw [ComplexShape.Embedding.liftExtend_f _ _ _ hi]
  simp only [HomologicalComplex.id_f, Category.id_comp, Category.comp_id]

/-- On the retained tail, the quotient component is the inverse native truncation coordinate. -/
lemma natTailProjection_f_eq_inv (K : ChainComplex D ℕ) (s i i' : ℕ)
    (hi : i + s = i') :
    (natTailProjection K s).f i' =
      (K.stupidTruncXIso (partialTotalOuterEmbedding s) hi).inv := by
  rw [natTailProjection_f K s i i' hi]
  rfl

/-- The quotient projection is natural in the original complex. -/
@[reassoc]
theorem natTailProjection_naturality {K L : ChainComplex D ℕ} (φ : K ⟶ L) (s : ℕ) :
    φ ≫ natTailProjection L s =
      natTailProjection K s ≫
        stupidTruncMap φ (partialTotalOuterEmbedding s) := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  apply HomologicalComplex.hom_ext
  intro i'
  change φ.f i' ≫ (natTailProjection L s).f i' =
    (natTailProjection K s).f i' ≫ (stupidTruncMap φ e).f i'
  by_cases hi : ∃ i, (e).f i = i'
  · obtain ⟨i, hi⟩ := hi
    let a := K.stupidTruncXIso e hi
    let b := L.stupidTruncXIso e hi
    have hMap : (stupidTruncMap φ e).f i' ≫ b.hom = a.hom ≫ φ.f i' :=
      stupidTruncMap_stupidTruncXIso_hom φ e hi
    apply (cancel_mono b.hom).1
    rw [natTailProjection_f_eq_inv K s i i' hi,
      natTailProjection_f_eq_inv L s i i' hi]
    change (φ.f i' ≫ b.inv) ≫ b.hom = (a.inv ≫ (stupidTruncMap φ e).f i') ≫ b.hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hMap,
      Iso.inv_hom_id_assoc]
  · have hZero : IsZero ((L.stupidTrunc e).X i') :=
      L.isZero_stupidTrunc_X e i' (by simpa only [not_exists] using hi)
    exact hZero.eq_of_tgt _ _

end HomologicalComplex

namespace HomologicalComplex₂

universe uA vA

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  (K : HomologicalComplex₂ A (ComplexShape.down ℕ) (ComplexShape.down ℕ))

/-- The original outer complex decomposes by its actual initial columns and native quotient
tail. Its degreewise sections are not claimed to be chain maps. -/
def initialOuterTailSequence (p : ℕ) : ShortComplex
    (HomologicalComplex₂ A (ComplexShape.down ℕ) (ComplexShape.down ℕ)) := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding (p + 1)
  let e₀ := ComplexShape.embeddingDownNatInitialSegment p
  let f := K.ιStupidTrunc e₀
  let g := HomologicalComplex.natTailProjection K (p + 1)
  have hfg : f ≫ g = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    change f.f i ≫ g.f i = 0
    by_cases hi : i < p + 1
    · have hZero : IsZero ((K.stupidTrunc e).X i) := K.isZero_stupidTrunc_X e i (by
        intro j hj
        change j + (p + 1) = i at hj
        omega)
      exact hZero.eq_of_tgt _ _
    · have hZero : IsZero ((K.stupidTrunc e₀).X i) := K.isZero_stupidTrunc_X e₀ i (by
        intro j hj
        have hBound := j.isLt
        change j.val = i at hj
        omega)
      exact hZero.eq_of_src _ _
  exact ShortComplex.mk f g hfg

/-- This canonical sequence is short exact by native degreewise split-sequence criteria. -/
theorem initialOuterTailSequence_shortExact (p : ℕ) :
    (initialOuterTailSequence K p).ShortExact := by
  let S := initialOuterTailSequence K p
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding (p + 1)
  let e₀ := ComplexShape.embeddingDownNatInitialSegment p
  apply HomologicalComplex.shortExact_of_degreewise_shortExact S
  intro i
  let Si := S.map (HomologicalComplex.eval (ChainComplex A ℕ) (ComplexShape.down ℕ) i)
  by_cases hi : i < p + 1
  · let j : Fin (p + 1) := ⟨i, hi⟩
    have hFi : Si.f = (K.stupidTruncXIso e₀ (show e₀.f j = i from rfl)).hom := by
      change (K.ιStupidTrunc e₀).f i = _
      rw [HomologicalComplex.ιStupidTrunc_f K e₀ i]
      simpa only [HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso,
        Iso.trans_hom] using
        (HomologicalComplex.ιStupidTruncf'_eq K e₀ (show e₀.f j = i from rfl))
    have hf : IsIso Si.f := by rw [hFi]; infer_instance
    have hZero : IsZero Si.X₃ := by
      change IsZero ((K.stupidTrunc e).X i)
      exact K.isZero_stupidTrunc_X e i (by
        intro j hj
        change j + (p + 1) = i at hj
        omega)
    exact (ShortComplex.Splitting.ofIsIsoOfIsZero (S := Si) hf hZero).shortExact
  · have hge : p + 1 ≤ i := by omega
    let j := i - (p + 1)
    have hj : j + (p + 1) = i := Nat.sub_add_cancel hge
    have hGi : Si.g =
        (K.restrictionXIso e hj).inv ≫ ((K.restriction e).extendXIso e hj).inv := by
      change (HomologicalComplex.natTailProjection K (p + 1)).f i = _
      exact HomologicalComplex.natTailProjection_f K (p + 1) j i hj
    let : IsIso Si.g := by rw [hGi]; infer_instance
    have hZero : IsZero Si.X₁ := by
      change IsZero ((K.stupidTrunc e₀).X i)
      exact K.isZero_stupidTrunc_X e₀ i (by
        intro j hj'
        have hBound := j.isLt
        change j.val = i at hj'
        omega)
    have hf : IsIso Si.op.f := by change IsIso Si.g.op; infer_instance
    have hZeroOp : IsZero Si.op.X₃ := hZero.op
    exact ((ShortComplex.Splitting.ofIsIsoOfIsZero (S := Si.op) hf hZeroOp).shortExact).unop

/-- The cokernel of the initial-column inclusion is the computed native outer tail. -/
def initialOuterTailCokernelIso (p : ℕ) :
    cokernel (K.ιStupidTrunc (ComplexShape.embeddingDownNatInitialSegment p)) ≅
      K.stupidTrunc (partialTotalOuterEmbedding (p + 1)) := by
  let S := initialOuterTailSequence K p
  exact (cokernelIsCokernel S.f).coconePointUniqueUpToIso
    (initialOuterTailSequence_shortExact K p).gIsCokernel

/-- The cokernel comparison carries the original projection to the tail map. -/
@[reassoc]
theorem initialOuterTailCokernelIso_π (p : ℕ) :
    cokernel.π (K.ιStupidTrunc (ComplexShape.embeddingDownNatInitialSegment p)) ≫
        (initialOuterTailCokernelIso K p).hom =
      HomologicalComplex.natTailProjection K (p + 1) := by
  let S := initialOuterTailSequence K p
  change cokernel.π S.f ≫
      ((cokernelIsCokernel S.f).coconePointUniqueUpToIso
        (initialOuterTailSequence_shortExact K p).gIsCokernel).hom = S.g
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel S.f)
    (initialOuterTailSequence_shortExact K p).gIsCokernel WalkingParallelPair.one

/-- Totalization identifies the partial-total cokernel with the native outer tail.
Only the finite first-quadrant total fibers are used. -/
def partialTotalCokernelTailIso (p : ℕ) :
    cokernel (K.partialTotalι p) ≅
      HomologicalComplex₂.total (K.stupidTrunc (partialTotalOuterEmbedding (p + 1)))
        (ComplexShape.down ℕ) := by
  let F := totalFunctor A (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)
  let f := K.ιStupidTrunc (ComplexShape.embeddingDownNatInitialSegment p)
  change cokernel (F.map f) ≅
    F.obj (K.stupidTrunc (partialTotalOuterEmbedding (p + 1)))
  exact (PreservesCokernel.iso F f).symm ≪≫ F.mapIso (initialOuterTailCokernelIso K p)

/-- The total cokernel isomorphism retains the prescribed quotient map. -/
@[reassoc]
theorem partialTotalCokernelTailIso_π (p : ℕ) :
    cokernel.π (K.partialTotalι p) ≫ (partialTotalCokernelTailIso K p).hom =
      total.map (HomologicalComplex.natTailProjection K (p + 1))
        (ComplexShape.down ℕ) := by
  let F := totalFunctor A (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)
  let f := K.ιStupidTrunc (ComplexShape.embeddingDownNatInitialSegment p)
  let g := HomologicalComplex.natTailProjection K (p + 1)
  let a := PreservesCokernel.iso F f
  let b := initialOuterTailCokernelIso K p
  have hπ : cokernel.π (F.map f) ≫ a.inv = F.map (cokernel.π f) := by
    rw [PreservesCokernel.iso_inv]
    exact π_comp_cokernelComparison f F
  have hOriginal : cokernel.π f ≫ b.hom = g := initialOuterTailCokernelIso_π K p
  change cokernel.π (F.map f) ≫ (a.inv ≫ F.map b.hom) = F.map g
  calc
    cokernel.π (F.map f) ≫ (a.inv ≫ F.map b.hom) =
        (cokernel.π (F.map f) ≫ a.inv) ≫ F.map b.hom :=
      (Category.assoc _ _ _).symm
    _ = F.map (cokernel.π f) ≫ F.map b.hom := by rw [hπ]
    _ = F.map (cokernel.π f ≫ b.hom) := (F.map_comp _ _).symm
    _ = F.map g := F.congr_map hOriginal

variable {K} {L : HomologicalComplex₂ A (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

/-- The computed total-cokernel comparison is natural in every original bicomplex map. -/
@[reassoc]
theorem partialTotalCokernelTailIso_hom_naturality (φ : K ⟶ L) (p : ℕ) :
    partialTotalCokernelMap φ p ≫ (partialTotalCokernelTailIso L p).hom =
      (partialTotalCokernelTailIso K p).hom ≫
        total.map (HomologicalComplex.stupidTruncMap φ
          (partialTotalOuterEmbedding (p + 1))) (ComplexShape.down ℕ) := by
  let F := totalFunctor A (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)
  let gK := HomologicalComplex.natTailProjection K (p + 1)
  let gL := HomologicalComplex.natTailProjection L (p + 1)
  let φTail := HomologicalComplex.stupidTruncMap φ
    (partialTotalOuterEmbedding (p + 1))
  have hTail : φ ≫ gL = gK ≫ φTail :=
    HomologicalComplex.natTailProjection_naturality φ (p + 1)
  apply (cancel_epi (cokernel.π (K.partialTotalι p))).1
  calc
    cokernel.π (K.partialTotalι p) ≫
          (partialTotalCokernelMap φ p ≫ (partialTotalCokernelTailIso L p).hom) =
        (cokernel.π (K.partialTotalι p) ≫ partialTotalCokernelMap φ p) ≫
          (partialTotalCokernelTailIso L p).hom := (Category.assoc _ _ _).symm
    _ = (F.map φ ≫ cokernel.π (L.partialTotalι p)) ≫
          (partialTotalCokernelTailIso L p).hom := by
      simpa only [F, totalFunctor_map] using congrArg
        (fun m => m ≫ (partialTotalCokernelTailIso L p).hom)
        (partialTotalCokernel_π_naturality φ p)
    _ = F.map φ ≫ (cokernel.π (L.partialTotalι p) ≫
          (partialTotalCokernelTailIso L p).hom) := Category.assoc _ _ _
    _ = F.map φ ≫ F.map gL := by
      simpa only [F, gL, totalFunctor_map] using congrArg
        (fun m => F.map φ ≫ m) (partialTotalCokernelTailIso_π L p)
    _ = F.map (φ ≫ gL) := (F.map_comp _ _).symm
    _ = F.map (gK ≫ φTail) := F.congr_map hTail
    _ = F.map gK ≫ F.map φTail := F.map_comp _ _
    _ = (cokernel.π (K.partialTotalι p) ≫ (partialTotalCokernelTailIso K p).hom) ≫
          F.map φTail := by
      simpa only [F, gK, totalFunctor_map] using congrArg
        (fun m => m ≫ F.map φTail) (partialTotalCokernelTailIso_π K p).symm
    _ = cokernel.π (K.partialTotalι p) ≫
          ((partialTotalCokernelTailIso K p).hom ≫ F.map φTail) := Category.assoc _ _ _

variable (K)

/-- Quotienting by the first two columns gives the zero-extended total of the tail.
The even displacement cancels exactly the native vertical total sign. -/
def firstTwoColumnCokernelTailIso :
    cokernel (K.partialTotalι 1) ≅
      (HomologicalComplex₂.total (K.restriction (c := ComplexShape.down ℕ) (partialTotalOuterEmbedding 2))
        (ComplexShape.down ℕ)).extend (c' := ComplexShape.down ℕ)
          (partialTotalOuterEmbedding 2) :=
  partialTotalCokernelTailIso K 1 ≪≫
    evenOuterExtensionTotalIso (K.restriction (c := ComplexShape.down ℕ)
      (partialTotalOuterEmbedding 2)) 1

end HomologicalComplex₂

namespace HomologicalComplex

universe uE vE

variable {E : Type uE} [Category.{vE} E] [HasZeroMorphisms E] [HasZeroObject E]

/-- The double native zero extension restricted to its actual shifted integer range has
the original object in each degree. Both extension coordinates are retained. -/
def extendNatAddIntRestrictionXIso (K : ChainComplex E ℕ) (s n : ℕ) :
    (((K.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s)).extend
        (ComplexShape.embeddingDownNatToIntShift 0)).restriction
      (ComplexShape.embeddingDownNatToIntShift (s : ℤ))).X n ≅ K.X n :=
  extendCompSourceXIso K (partialTotalOuterEmbedding s)
    (ComplexShape.embeddingDownNatToIntShift 0) n ((s : ℤ) + n) (by
      change (0 : ℤ) + ((n + s : ℕ) : ℤ) = (s : ℤ) + (n : ℤ)
      rw [zero_add, Nat.cast_add, add_comm])

/-- Restricting the two native zero extensions to the computed shifted range gives the
original complex, including its true differential. -/
def extendNatAddIntRestrictionIso (K : ChainComplex E ℕ) (s : ℕ) :
    ((K.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s)).extend
        (ComplexShape.embeddingDownNatToIntShift 0)).restriction
      (ComplexShape.embeddingDownNatToIntShift (s : ℤ)) ≅ K :=
  Hom.isoOfComponents (extendNatAddIntRestrictionXIso K s) (by
    intro i j hij
    exact extendCompSourceXIso_comm K (partialTotalOuterEmbedding s)
      (ComplexShape.embeddingDownNatToIntShift 0) i j ((s : ℤ) + i) ((s : ℤ) + j)
      (by
        change (0 : ℤ) + ((i + s : ℕ) : ℤ) = (s : ℤ) + (i : ℤ)
        rw [zero_add, Nat.cast_add, add_comm])
      (by
        change (0 : ℤ) + ((j + s : ℕ) : ℤ) = (s : ℤ) + (j : ℤ)
        rw [zero_add, Nat.cast_add, add_comm]))

/-- The double zero extension vanishes outside the shifted integer range. -/
theorem isStrictlySupported_extendNatAddInt (K : ChainComplex E ℕ) (s : ℕ) :
    ((K.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s)).extend
      (ComplexShape.embeddingDownNatToIntShift 0)).IsStrictlySupported
        (ComplexShape.embeddingDownNatToIntShift (s : ℤ)) := by
  refine ⟨?_⟩
  intro z hz
  apply isZero_extendExtend_X_of_notMem K (partialTotalOuterEmbedding s)
    (ComplexShape.embeddingDownNatToIntShift 0) z
  intro n hn
  apply hz n
  have hIndex :
      (ComplexShape.embeddingDownNatToIntShift 0).f
          ((partialTotalOuterEmbedding s).f n) =
        (ComplexShape.embeddingDownNatToIntShift (s : ℤ)).f n := by
    change (0 : ℤ) + ((n + s : ℕ) : ℤ) = (s : ℤ) + (n : ℤ)
    rw [zero_add, Nat.cast_add, add_comm]
  exact hIndex.symm.trans hn

/-- A Nat zero extension followed by the unshifted integer embedding is the shifted integer zero extension. The comparison is computed, not supplied by a caller. -/
def extendNatAddIntIso (K : ChainComplex E ℕ) (s : ℕ) :
    (K.extend (c' := ComplexShape.down ℕ) (partialTotalOuterEmbedding s)).extend
        (ComplexShape.embeddingDownNatToIntShift 0) ≅
      K.extend (ComplexShape.embeddingDownNatToIntShift (s : ℤ)) := by
  let e₁ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  let e₂ := ComplexShape.embeddingDownNatToIntShift 0
  let e₃ := ComplexShape.embeddingDownNatToIntShift (s : ℤ)
  have hIndex : ∀ n, e₂.f (e₁.f n) = e₃.f n := by
    intro n
    change (0 : ℤ) + ((n + s : ℕ) : ℤ) = (s : ℤ) + (n : ℤ)
    rw [zero_add, Nat.cast_add, add_comm]
  exact extendCompIsoOfEq K e₁ e₂ e₃ hIndex

/-- The computed comparison retains the original double extension coordinate in every
supported integer degree. -/
lemma extendNatAddIntIso_hom_f (K : ChainComplex E ℕ) (s n : ℕ) :
    (extendNatAddIntIso K s).hom.f ((s : ℤ) + n) =
      (extendNatAddIntRestrictionXIso K s n).hom ≫
        (K.extendXIso (ComplexShape.embeddingDownNatToIntShift (s : ℤ))
          (show (ComplexShape.embeddingDownNatToIntShift (s : ℤ)).f n =
            (s : ℤ) + n from rfl)).inv := by
  let e₁ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  let e₂ := ComplexShape.embeddingDownNatToIntShift 0
  let e₃ := ComplexShape.embeddingDownNatToIntShift (s : ℤ)
  have hIndex : ∀ i, e₂.f (e₁.f i) = e₃.f i := by
    intro i
    change (0 : ℤ) + ((i + s : ℕ) : ℤ) = (s : ℤ) + (i : ℤ)
    rw [zero_add, Nat.cast_add, add_comm]
  change (extendCompIsoOfEq K e₁ e₂ e₃ hIndex).hom.f (e₃.f n) =
    (extendCompSourceXIso K e₁ e₂ n (e₃.f n) (hIndex n)).hom ≫
      (K.extendXIso e₃ (show e₃.f n = e₃.f n from rfl)).inv
  exact extendCompIsoOfEq_hom_f K e₁ e₂ e₃ hIndex n (e₃.f n) rfl

/-- Restriction of the computed double extension commutes with every original chain map. -/
@[reassoc]
theorem extendNatAddIntRestrictionIso_hom_naturality {K L : ChainComplex E ℕ}
    (φ : K ⟶ L) (s : ℕ) :
    restrictionMap (extendMap (extendMap φ (partialTotalOuterEmbedding s))
          (ComplexShape.embeddingDownNatToIntShift 0))
        (ComplexShape.embeddingDownNatToIntShift (s : ℤ)) ≫
          (extendNatAddIntRestrictionIso L s).hom =
      (extendNatAddIntRestrictionIso K s).hom ≫ φ := by
  apply HomologicalComplex.hom_ext
  intro n
  exact extendCompSourceXIso_hom_naturality
    (partialTotalOuterEmbedding s)
    (ComplexShape.embeddingDownNatToIntShift 0) φ n ((s : ℤ) + n) (by
      change (0 : ℤ) + ((n + s : ℕ) : ℤ) = (s : ℤ) + (n : ℤ)
      rw [zero_add, Nat.cast_add, add_comm])

/-- The double-extension comparison is natural in the original chain map. -/
@[reassoc]
theorem extendNatAddIntIso_hom_naturality {K L : ChainComplex E ℕ}
    (φ : K ⟶ L) (s : ℕ) :
    extendMap (extendMap φ (partialTotalOuterEmbedding s))
        (ComplexShape.embeddingDownNatToIntShift 0) ≫ (extendNatAddIntIso L s).hom =
      (extendNatAddIntIso K s).hom ≫
        extendMap φ (ComplexShape.embeddingDownNatToIntShift (s : ℤ)) := by
  let e₁ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding s
  let e₂ := ComplexShape.embeddingDownNatToIntShift 0
  let e₃ := ComplexShape.embeddingDownNatToIntShift (s : ℤ)
  have hIndex : ∀ n, e₂.f (e₁.f n) = e₃.f n := by
    intro n
    change (0 : ℤ) + ((n + s : ℕ) : ℤ) = (s : ℤ) + (n : ℤ)
    rw [zero_add, Nat.cast_add, add_comm]
  exact extendCompIsoOfEq_hom_naturality e₁ e₂ e₃ hIndex φ

end HomologicalComplex

namespace HomologicalComplex₂

universe uF vF

variable {F : Type uF} [Category.{vF} F] [Abelian F]
  {K L : HomologicalComplex₂ F (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

/-- The first-two-column quotient comparison is natural in the original bicomplex map. -/
@[reassoc]
theorem firstTwoColumnCokernelTailIso_hom_naturality (φ : K ⟶ L) :
    partialTotalCokernelMap φ 1 ≫ (firstTwoColumnCokernelTailIso L).hom =
      (firstTwoColumnCokernelTailIso K).hom ≫
        HomologicalComplex.extendMap (c' := ComplexShape.down ℕ)
          (total.map (HomologicalComplex.restrictionMap (c := ComplexShape.down ℕ) φ
            (partialTotalOuterEmbedding 2)) (ComplexShape.down ℕ))
          (partialTotalOuterEmbedding 2) := by
  let e : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    partialTotalOuterEmbedding 2
  let φTail := HomologicalComplex.restrictionMap (c := ComplexShape.down ℕ) φ e
  let aK := partialTotalCokernelTailIso K 1
  let aL := partialTotalCokernelTailIso L 1
  let bK := evenOuterExtensionTotalIso (K.restriction e) 1
  let bL := evenOuterExtensionTotalIso (L.restriction e) 1
  have ha : partialTotalCokernelMap φ 1 ≫ aL.hom =
      aK.hom ≫ total.map (HomologicalComplex.extendMap (c' := ComplexShape.down ℕ)
        φTail e) (ComplexShape.down ℕ) :=
    partialTotalCokernelTailIso_hom_naturality φ 1
  have hb : total.map (HomologicalComplex.extendMap (c' := ComplexShape.down ℕ)
    φTail e) (ComplexShape.down ℕ) ≫
      bL.hom = bK.hom ≫
        HomologicalComplex.extendMap (c' := ComplexShape.down ℕ)
          (total.map φTail (ComplexShape.down ℕ)) e :=
    evenOuterExtensionTotalIso_hom_naturality φTail 1
  change partialTotalCokernelMap φ 1 ≫ (aL.hom ≫ bL.hom) =
    (aK.hom ≫ bK.hom) ≫
      HomologicalComplex.extendMap (c' := ComplexShape.down ℕ)
        (total.map φTail (ComplexShape.down ℕ)) e
  calc
    partialTotalCokernelMap φ 1 ≫ (aL.hom ≫ bL.hom) =
        (partialTotalCokernelMap φ 1 ≫ aL.hom) ≫ bL.hom := (Category.assoc _ _ _).symm
    _ = (aK.hom ≫ total.map (HomologicalComplex.extendMap (c' := ComplexShape.down ℕ) φTail e)
          (ComplexShape.down ℕ)) ≫ bL.hom := by rw [ha]
    _ = aK.hom ≫ (total.map (HomologicalComplex.extendMap (c' := ComplexShape.down ℕ) φTail e)
          (ComplexShape.down ℕ) ≫ bL.hom) := Category.assoc _ _ _
    _ = aK.hom ≫ (bK.hom ≫
          HomologicalComplex.extendMap (c' := ComplexShape.down ℕ)
            (total.map φTail (ComplexShape.down ℕ)) e) := by
      rw [hb]
    _ = (aK.hom ≫ bK.hom) ≫
          HomologicalComplex.extendMap (c' := ComplexShape.down ℕ)
            (total.map φTail (ComplexShape.down ℕ)) e :=
      (Category.assoc _ _ _).symm

end HomologicalComplex₂
