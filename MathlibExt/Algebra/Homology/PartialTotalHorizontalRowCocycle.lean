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

public import MathlibExt.Algebra.Homology.PartialTotalHorizontalRow
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Horizontal row cocycles and their homology maps

Let `B` be a first-quadrant bicomplex in a preadditive category with finite coproducts. The
horizontal components `F_m(n)` from signed row `m + 1` in degree `n + 1` to signed row `m` in
degree `n` satisfy `d F_m + F_m d = 0`.

Regrade natural chain degree `n` as integer cochain degree `-n`. The components then define a
degree-one cocycle, and hence a morphism from the extended source row to the target row
shifted by one. In an abelian category this induces `H_(m+1+q)(B.totalRow (m+1)) ⟶
H_(m+q)(B.totalRow m)`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

section Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- Adjacent horizontal row components anticommute with row differentials.

For natural `m` and `n`, the composite of the source differential from `n + 2` to `n + 1` with
`F_m(n)`, plus the composite of `F_m(n + 1)` with the target differential from `n + 1` to `n`,
is zero. -/
theorem partialTotalHorizontalRowF_anticomm (m n : ℕ) :
    (B.totalRow (m + 1)).d (n + 2) (n + 1) ≫
          B.partialTotalHorizontalRowF m n +
      B.partialTotalHorizontalRowF m (n + 1) ≫
          (B.totalRow m).d (n + 1) n = 0 := by
  by_cases hmn : m ≤ n
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have hF₁ := B.partialTotalHorizontalRowF_eq m (q + 1)
    have hF₀ := B.partialTotalHorizontalRowF_eq m q
    have hε := ComplexShape.ε_succ
      (c := ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl)
    have hε' :
        (ComplexShape.down ℕ).ε (m + 1) =
          -(ComplexShape.down ℕ).ε m := by
      have := congrArg Neg.neg hε
      simpa only [neg_neg] using this.symm
    rw [B.totalRow_d_eq (m + 1) (q + 1) q
        (m + q + 2) (m + q + 1) (by omega) (by omega),
      hF₀]
    have hF₁' :
        B.partialTotalHorizontalRowF m (m + q + 1) =
          (B.totalRowXIso (m + 1) (q + 1) (m + q + 2) (by omega)).hom ≫
            (B.d (m + 1) m).f (q + 1) ≫
            (B.totalRowXIso m (q + 1) (m + q + 1) (by omega)).inv := by
      convert hF₁ using 1
    rw [hF₁', B.totalRow_d_eq m (q + 1) q
      (m + q + 1) (m + q) (by omega) rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      Linear.units_smul_comp, Linear.comp_units_smul]
    rw [(B.d (m + 1) m).comm_assoc]
    rw [hε']
    simp only [Units.neg_smul]
    abel
  · have hnm : n < m := by omega
    rw [B.partialTotalHorizontalRowF_eq_zero_of_lt m n hnm,
      comp_zero, zero_add]
    exact (B.totalRow_isZero_X m n hnm).eq_of_tgt _ _

/-- Horizontal row components as a degree-one cochain.

Extend the two signed total rows along the embedding `n ↦ -n`. The component from degree `-(n
+ 1)` to `-n` is `B.partialTotalHorizontalRowF m n` in extension coordinates. Components with
source outside the embedding, and the component from degree zero to one, are zero. -/
noncomputable def partialTotalHorizontalRowCochain (m : ℕ) :
    CochainComplex.HomComplex.Cochain
      ((B.totalRow (m + 1)).extend ComplexShape.embeddingDownNat)
      ((B.totalRow m).extend ComplexShape.embeddingDownNat) 1 :=
  CochainComplex.HomComplex.Cochain.mk fun p q hpq =>
    let e := ComplexShape.embeddingDownNat
    match hr : e.r p with
    | none => 0
    | some 0 => 0
    | some (n + 1) =>
        have hp : e.f (n + 1) = p := e.f_eq_of_r_eq_some hr
        have hq : e.f n = q := by
          change -(((n + 1 : ℕ) : ℤ)) = p at hp
          change p + 1 = q at hpq
          change -((n : ℕ) : ℤ) = q
          omega
        ((B.totalRow (m + 1)).extendXIso e hp).hom ≫
          B.partialTotalHorizontalRowF m n ≫
          ((B.totalRow m).extendXIso e hq).inv

/-- Supported component of the regraded horizontal cochain.

At source degree `-(n + 1)` and target degree `-n`, the horizontal cochain is the source
extension-coordinate map followed by `B.partialTotalHorizontalRowF m n` and the inverse target
extension-coordinate map. -/
theorem partialTotalHorizontalRowCochain_v (m n : ℕ) :
    (B.partialTotalHorizontalRowCochain m).v
        (ComplexShape.embeddingDownNat.f (n + 1))
        (ComplexShape.embeddingDownNat.f n) (by
          change -(((n + 1 : ℕ) : ℤ)) + 1 = -((n : ℕ) : ℤ)
          omega) =
      ((B.totalRow (m + 1)).extendXIso
          ComplexShape.embeddingDownNat rfl).hom ≫
        B.partialTotalHorizontalRowF m n ≫
        ((B.totalRow m).extendXIso
          ComplexShape.embeddingDownNat rfl).inv := by
  simp only [partialTotalHorizontalRowCochain,
    CochainComplex.HomComplex.Cochain.v,
    CochainComplex.HomComplex.Cochain.mk]
  split
  · rename_i hr
    have hbad : (none : Option ℕ) = some (n + 1) :=
      hr.symm.trans (ComplexShape.embeddingDownNat.r_f (n + 1))
    cases hbad
  · rename_i hr
    have hbad : 0 = n + 1 :=
      Option.some.inj
        (hr.symm.trans (ComplexShape.embeddingDownNat.r_f (n + 1)))
    omega
  · rename_i k hr
    have hk : k = n := by
      have hsucc : k + 1 = n + 1 :=
        Option.some.inj
          (hr.symm.trans (ComplexShape.embeddingDownNat.r_f (n + 1)))
      omega
    subst k
    rfl

/-- Horizontal cochain vanishes outside the chain-degree embedding.

If the inverse index of an integer source degree `p` under `n ↦ -n` is absent, every degree-
one horizontal cochain component from `p` to `q = p + 1` is zero. -/
theorem partialTotalHorizontalRowCochain_v_of_r_eq_none
    (m : ℕ) {p q : ℤ} (hpq : p + 1 = q)
    (hp : ComplexShape.embeddingDownNat.r p = none) :
    (B.partialTotalHorizontalRowCochain m).v p q hpq = 0 := by
  simp only [partialTotalHorizontalRowCochain,
    CochainComplex.HomComplex.Cochain.v,
    CochainComplex.HomComplex.Cochain.mk]
  split
  · rfl
  · rename_i hr
    have hbad : (none : Option ℕ) = some 0 := hp.symm.trans hr
    cases hbad
  · rename_i k hr
    have hbad : (none : Option ℕ) = some (k + 1) := hp.symm.trans hr
    cases hbad

/-- Horizontal degree-one cochain has zero component from zero to one.

For every row index `m`, the component of `B.partialTotalHorizontalRowCochain m` from cochain
degree zero to degree one is zero. -/
theorem partialTotalHorizontalRowCochain_v_zero (m : ℕ) :
    (B.partialTotalHorizontalRowCochain m).v 0 1 rfl = 0 := by
  have h01 : ComplexShape.embeddingDownNat.f 0 + 1 = (1 : ℤ) := by
    change -(((0 : ℕ) : ℤ)) + 1 = (1 : ℤ)
    omega
  change (B.partialTotalHorizontalRowCochain m).v
    (ComplexShape.embeddingDownNat.f 0) 1 h01 = 0
  simp only [partialTotalHorizontalRowCochain,
    CochainComplex.HomComplex.Cochain.v,
    CochainComplex.HomComplex.Cochain.mk]
  split
  · rename_i hr
    have hbad : (none : Option ℕ) = some 0 :=
      hr.symm.trans (ComplexShape.embeddingDownNat.r_f 0)
    cases hbad
  · rfl
  · rename_i k hr
    have hbad : k + 1 = 0 :=
      Option.some.inj
        (hr.symm.trans (ComplexShape.embeddingDownNat.r_f 0))
    omega

/-- Horizontal row cocycle of degree one.

The regraded horizontal cochain is closed because its row components satisfy `d F_m + F_m d =
0`. It therefore defines a degree-one cocycle from the extended signed row `m + 1` to the
extended signed row `m`. -/
noncomputable def partialTotalHorizontalRowCocycle (m : ℕ) :
    CochainComplex.HomComplex.Cocycle
      ((B.totalRow (m + 1)).extend ComplexShape.embeddingDownNat)
      ((B.totalRow m).extend ComplexShape.embeddingDownNat) 1 :=
  CochainComplex.HomComplex.Cocycle.mk
    (B.partialTotalHorizontalRowCochain m) 2 rfl (by
      apply CochainComplex.HomComplex.Cochain.ext
      intro p q hpq
      let e := ComplexShape.embeddingDownNat
      let K := B.totalRow (m + 1)
      let L := B.totalRow m
      obtain hpnone | ⟨k, hk⟩ := (e.r p).eq_none_or_eq_some
      · exact (K.isZero_extend_X' e p hpnone).eq_of_src _ _
      · rcases k with _ | k
        · have hp : e.f 0 = p := e.f_eq_of_r_eq_some hk
          have hK0 := B.totalRow_isZero_X (m + 1) 0 (by omega)
          exact (hK0.of_iso (K.extendXIso e hp)).eq_of_src _ _
        · rcases k with _ | n
          · have hp : e.f 1 = p := e.f_eq_of_r_eq_some hk
            have hq : q = 1 := by
              change -((1 : ℕ) : ℤ) = p at hp
              change p + 2 = q at hpq
              omega
            have hL : IsZero ((L.extend e).X q) := by
              apply L.isZero_extend_X e q
              intro i hi
              change -((i : ℕ) : ℤ) = q at hi
              omega
            exact hL.eq_of_tgt _ _
          · have hp : e.f (n + 2) = p := e.f_eq_of_r_eq_some hk
            have hp₂ : e.f n = q := by
              change -(((n + 2 : ℕ) : ℤ)) = p at hp
              change p + 2 = q at hpq
              change -((n : ℕ) : ℤ) = q
              omega
            obtain rfl := hp
            obtain rfl := hp₂
            have hq₁ : e.f (n + 1) = e.f n - 1 := by
              change -(((n + 1 : ℕ) : ℤ)) = -((n : ℕ) : ℤ) - 1
              omega
            have hp₁ : e.f (n + 2) + 1 = e.f (n + 1) := by
              change -(((n + 2 : ℕ) : ℤ)) + 1 = -(((n + 1 : ℕ) : ℤ))
              omega
            have hz₀deg : e.f (n + 1) + 1 = e.f n := by
              rw [hq₁]
              omega
            let hK₂ : e.f (n + 2) = e.f (n + 2) := rfl
            let hK₁ : e.f (n + 1) = e.f (n + 1) := rfl
            let hL₁ : e.f (n + 1) = e.f (n + 1) := rfl
            let hL₀ : e.f n = e.f n := rfl
            let k₂ : (K.extend e).X (e.f (n + 2)) ≅ K.X (n + 2) :=
              K.extendXIso e hK₂
            let k₁ : (K.extend e).X (e.f (n + 1)) ≅ K.X (n + 1) :=
              K.extendXIso e hK₁
            let l₁ : (L.extend e).X (e.f (n + 1)) ≅ L.X (n + 1) :=
              L.extendXIso e hL₁
            let l₀ : (L.extend e).X (e.f n) ≅ L.X n :=
              L.extendXIso e hL₀
            have hz₁ :
                (B.partialTotalHorizontalRowCochain m).v
                    (e.f (n + 2)) (e.f (n + 1)) hp₁ =
                  k₂.hom ≫ B.partialTotalHorizontalRowF m (n + 1) ≫ l₁.inv := by
              convert B.partialTotalHorizontalRowCochain_v m (n + 1) using 1
            have hz₀ :
                (B.partialTotalHorizontalRowCochain m).v
                    (e.f (n + 1)) (e.f n) hz₀deg =
                  k₁.hom ≫ B.partialTotalHorizontalRowF m n ≫ l₀.inv := by
              convert B.partialTotalHorizontalRowCochain_v m n using 1
            have hdK :
                (K.extend e).d (e.f (n + 2)) (e.f (n + 1)) =
                  k₂.hom ≫ K.d (n + 2) (n + 1) ≫ k₁.inv :=
              K.extend_d_eq e hK₂ hK₁
            have hdL :
                (L.extend e).d (e.f (n + 1)) (e.f n) =
                  l₁.hom ≫ L.d (n + 1) n ≫ l₀.inv :=
              L.extend_d_eq e hL₁ hL₀
            rw [CochainComplex.HomComplex.δ_v 1 2 rfl _
              (e.f (n + 2)) (e.f n) hpq
              (e.f (n + 1)) (e.f (n + 1)) hq₁ hp₁]
            rw [hz₁, hz₀, hdK, hdL]
            simp only [show Int.negOnePow 2 = 1 by rfl, one_smul,
              CochainComplex.HomComplex.Cochain.zero_v,
              Category.assoc, l₁.inv_hom_id_assoc, k₁.inv_hom_id_assoc]
            have h := congrArg
              (fun f ↦ k₂.hom ≫ f ≫ l₀.inv)
              (B.partialTotalHorizontalRowF_anticomm m n)
            simp only [Preadditive.comp_add, Preadditive.add_comp,
              Category.assoc, comp_zero, zero_comp] at h
            simpa only [add_comm] using h)

/-- Supported component of the horizontal row cocycle.

The underlying degree-one cochain of `B.partialTotalHorizontalRowCocycle m` has component from
`-(n + 1)` to `-n` equal to `B.partialTotalHorizontalRowF m n`, conjugated by the source and
target extension-coordinate isomorphisms. -/
theorem partialTotalHorizontalRowCocycle_v (m n : ℕ) :
    (B.partialTotalHorizontalRowCocycle m :
      CochainComplex.HomComplex.Cochain _ _ 1).v
        (ComplexShape.embeddingDownNat.f (n + 1))
        (ComplexShape.embeddingDownNat.f n) (by
          change -(((n + 1 : ℕ) : ℤ)) + 1 = -((n : ℕ) : ℤ)
          omega) =
      ((B.totalRow (m + 1)).extendXIso
          ComplexShape.embeddingDownNat rfl).hom ≫
        B.partialTotalHorizontalRowF m n ≫
        ((B.totalRow m).extendXIso
          ComplexShape.embeddingDownNat rfl).inv := by
  simpa only [partialTotalHorizontalRowCocycle,
    CochainComplex.HomComplex.Cocycle.mk_coe] using
      B.partialTotalHorizontalRowCochain_v m n

/-- Horizontal row cocycle as a morphism to a shifted row.

The degree-one cocycle gives a cochain-complex morphism from the extension of `B.totalRow (m +
1)` to the extension of `B.totalRow m` shifted by `1`. The shift incorporates the sign in the
cocycle equation. -/
noncomputable def partialTotalHorizontalRowShift (m : ℕ) :
    (B.totalRow (m + 1)).extend ComplexShape.embeddingDownNat ⟶
      ((B.totalRow m).extend ComplexShape.embeddingDownNat)⟦(1 : ℤ)⟧ :=
  CochainComplex.HomComplex.Cocycle.equivHomShift.symm
    (B.partialTotalHorizontalRowCocycle m)

/-- Shifted horizontal morphism in unshifted target coordinates.

Compose the component of `B.partialTotalHorizontalRowShift m` in degree `-(n + 1)` with the
target shift-coordinate isomorphism to degree `-n`. The resulting map is
`B.partialTotalHorizontalRowF m n` conjugated by the two extension coordinates. -/
theorem partialTotalHorizontalRowShift_f_comp_shiftIso (m n : ℕ) :
    (B.partialTotalHorizontalRowShift m).f
        (ComplexShape.embeddingDownNat.f (n + 1)) ≫
      (CochainComplex.shiftFunctorObjXIso
        ((B.totalRow m).extend ComplexShape.embeddingDownNat)
        1 (ComplexShape.embeddingDownNat.f (n + 1))
          (ComplexShape.embeddingDownNat.f n) (by
            change -((n : ℕ) : ℤ) = -(((n + 1 : ℕ) : ℤ)) + 1
            omega)).hom =
      ((B.totalRow (m + 1)).extendXIso
          ComplexShape.embeddingDownNat rfl).hom ≫
        B.partialTotalHorizontalRowF m n ≫
        ((B.totalRow m).extendXIso
          ComplexShape.embeddingDownNat rfl).inv := by
  have hdeg :
      ComplexShape.embeddingDownNat.f (n + 1) + 1 =
        ComplexShape.embeddingDownNat.f n := by
    change -(((n + 1 : ℕ) : ℤ)) + 1 = -((n : ℕ) : ℤ)
    omega
  rw [partialTotalHorizontalRowShift,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply]
  simp only [CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cocycle.rightShift_coe]
  rw [CochainComplex.HomComplex.Cochain.rightShift_v
    (B.partialTotalHorizontalRowCocycle m).1
    1 0 (zero_add 1)
    (ComplexShape.embeddingDownNat.f (n + 1))
    (ComplexShape.embeddingDownNat.f (n + 1))
    (add_zero _)
    (ComplexShape.embeddingDownNat.f n) hdeg]
  rw [B.partialTotalHorizontalRowCocycle_v m n]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Cochain

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- Homology map induced by the horizontal row cocycle.

In an abelian category, the shifted horizontal morphism induces a map from
`H_(m+1+q)(B.totalRow (m+1))` to `H_(m+q)(B.totalRow m)`. The definition uses extension
homology coordinates and the homology functor's shift map. -/
noncomputable def partialTotalHorizontalRowHomology (m q : ℕ) :
    (B.totalRow (m + 1)).homology (m + 1 + q) ⟶
      (B.totalRow m).homology (m + q) :=
  ((B.totalRow (m + 1)).extendHomologyIso
      ComplexShape.embeddingDownNat (show
        ComplexShape.embeddingDownNat.f (m + 1 + q) =
          -((m + 1 + q : ℕ) : ℤ) by rfl)).inv ≫
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (B.partialTotalHorizontalRowShift m)
      (-((m + 1 + q : ℕ) : ℤ)) (-((m + q : ℕ) : ℤ)) (by omega) ≫
    ((B.totalRow m).extendHomologyIso
      ComplexShape.embeddingDownNat (show
        ComplexShape.embeddingDownNat.f (m + q) =
          -((m + q : ℕ) : ℤ) by rfl)).hom

/-- Regrading formula for the horizontal row homology map.

The horizontal row homology map is the inverse source extension-homology isomorphism, followed
by the shift map in cochain degrees `-(m + 1 + q)` and `-(m + q)`, followed by the target
extension-homology isomorphism. -/
theorem partialTotalHorizontalRowHomology_eq (m q : ℕ) :
    B.partialTotalHorizontalRowHomology m q =
      ((B.totalRow (m + 1)).extendHomologyIso
        ComplexShape.embeddingDownNat (show
          ComplexShape.embeddingDownNat.f (m + 1 + q) =
            -((m + 1 + q : ℕ) : ℤ) by rfl)).inv ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (B.partialTotalHorizontalRowShift m)
        (-((m + 1 + q : ℕ) : ℤ)) (-((m + q : ℕ) : ℤ)) (by omega) ≫
      ((B.totalRow m).extendHomologyIso
        ComplexShape.embeddingDownNat (show
          ComplexShape.embeddingDownNat.f (m + q) =
            -((m + q : ℕ) : ℤ) by rfl)).hom :=
  rfl

end Homology

end HomologicalComplex₂

end
