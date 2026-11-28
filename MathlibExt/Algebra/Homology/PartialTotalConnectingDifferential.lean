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

public import MathlibExt.Algebra.Homology.PartialTotalStepHomology

/-!
# Connecting maps between adjacent signed partial-total rows

Let `B` be a first-quadrant bicomplex in an abelian category. The lower complex of filtration
step `m+1` is the middle complex of step `m`, and their cochain extensions have the same
supported components.

The successor short exact sequence gives a connecting morphism from the new signed row to the
preceding filtered stage. Follow it by the quotient onto row `m` and the row-coordinate
comparisons. In vertical degree `q`, the resulting map is `H_(m+1+q)(row_(m+1)) →
H_(m+q)(row_m)`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The common filtered-stage isomorphism of adjacent cochain steps.

The source complex of step `m+1` is isomorphic to the middle complex of step `m` after chain-
to-cochain extension. -/
noncomputable def partialTotalAdjacentStepCochainIso (m : ℕ) :
    (B.partialTotalStepCochainShortComplex (m + 1)).X₁ ≅
      (B.partialTotalStepCochainShortComplex m).X₂ :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    (eqToIso (by
      rw [B.partialTotalStepShortComplex_X₁_succ,
        B.partialTotalStepShortComplex_X₂]))

set_option backward.isDefEq.respectTransparency false in
/-- The supported component identity of adjacent-step coordinates.

At the cochain degree corresponding to total degree `n`, the adjacent-step comparison is
heterogeneously equal to the identity of the common partial-total component. -/
theorem partialTotalAdjacentStepCochainIso_hom_f_heq
    (m n : ℕ) :
    HEq ((B.partialTotalAdjacentStepCochainIso m).hom.f
      (ComplexShape.embeddingDownNat.f n))
      (𝟙 ((B.partialTotal m).X n)) := by
  let e := ComplexShape.embeddingDownNat
  let K := (B.partialTotalStepShortComplex (m + 1)).X₁
  let L := (B.partialTotalStepShortComplex m).X₂
  let P := B.partialTotal m
  let hStep : K = L := by
    dsimp only [K, L]
    rw [B.partialTotalStepShortComplex_X₁_succ,
      B.partialTotalStepShortComplex_X₂]
  have hK : (K.extend e).X (e.f n) = K.X n := by
    change HomologicalComplex.extend.X K (e.r (e.f n)) = K.X n
    rw [e.r_eq_some rfl]
    rfl
  have hL : (L.extend e).X (e.f n) = L.X n := by
    change HomologicalComplex.extend.X L (e.r (e.f n)) = L.X n
    rw [e.r_eq_some rfl]
    rfl
  let hX : K.X n = L.X n :=
    congr_fun (congr_arg HomologicalComplex.X hStep) n
  have hTgt : L.X n = P.X n := by
    simpa only [L, P] using
      congrArg (fun (T : ChainComplex C ℕ) => T.X n)
        (B.partialTotalStepShortComplex_X₂ m)
  have hLeft : (K.extendXIso e rfl).hom = eqToHom hK := by
    dsimp only [HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso]
    rfl
  have hRight : (L.extendXIso e rfl).inv = eqToHom hL.symm := by
    dsimp only [HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso]
    rfl
  change HEq
    ((HomologicalComplex.extendMap (eqToHom hStep) e).f (e.f n))
    (𝟙 (P.X n))
  rw [HomologicalComplex.extendMap_f (φ := eqToHom hStep) (e := e) rfl,
    HomologicalComplex.eqToHom_f, hLeft, hRight]
  have hConj :
      HEq (eqToHom hK ≫ eqToHom hX ≫ eqToHom hL.symm)
        (eqToHom hX) :=
    (CategoryTheory.conj_eqToHom_iff_heq
      (eqToHom hK ≫ eqToHom hX ≫ eqToHom hL.symm)
      (eqToHom hX) hK hL).mp rfl
  exact hConj.trans
    ((CategoryTheory.eqToHom_heq_id_cod _ _ hX).trans
      ((CategoryTheory.eqToHom_heq_id_dom _ _ hTgt).symm.trans
        (CategoryTheory.eqToHom_heq_id_cod _ _ hTgt)))

set_option backward.isDefEq.respectTransparency false in
/-- The row-quotient coordinate of an adjacent-step target map.

At adjacent supported cochain degrees, the step comparison and row quotient followed by the
shift coordinate agree heterogeneously with the finite row quotient and its extension
coordinate. The adjacent degree equality is inferred from `k` by default. -/
theorem partialTotalAdjacentTargetMap_f_comp_shiftIso_heq
    (m k : ℕ)
    (hkdeg : ComplexShape.embeddingDownNat.f k =
      ComplexShape.embeddingDownNat.f (k + 1) + 1 := by
        simp only [ComplexShape.embeddingDownNat_f, Nat.cast_add, Nat.cast_one]
        omega) :
    let Q :
        (B.partialTotalStepCochainShortComplex (m + 1)).X₁ ⟶
          (B.totalRow m).extend ComplexShape.embeddingDownNat :=
      (B.partialTotalAdjacentStepCochainIso m).hom ≫
        (B.partialTotalStepCochainShortComplex m).g ≫
        (B.partialTotalStepCochainX₃Iso m).hom
    HEq
      (Q.f (ComplexShape.embeddingDownNat.f (k + 1) + 1) ≫
        (CochainComplex.shiftFunctorObjXIso
          ((B.totalRow m).extend ComplexShape.embeddingDownNat) 1
          (ComplexShape.embeddingDownNat.f (k + 1))
          (ComplexShape.embeddingDownNat.f k) hkdeg).hom)
      (B.partialTotalRowQuotientF m k ≫
        ((B.totalRow m).extendXIso ComplexShape.embeddingDownNat
          (i := k) (i' := ComplexShape.embeddingDownNat.f k) rfl).inv) := by
  let e := ComplexShape.embeddingDownNat
  let S := B.partialTotalStepShortComplex m
  let A := S.X₂
  let Z := S.X₃
  let P := B.partialTotal m
  let T := B.totalRow m
  let U := B.partialTotalStepCochainShortComplex m
  let V := B.partialTotalStepCochainShortComplex (m + 1)
  let Q : V.X₁ ⟶ T.extend e :=
    (B.partialTotalAdjacentStepCochainIso m).hom ≫ U.g ≫
      (B.partialTotalStepCochainX₃Iso m).hom
  have hidx : e.f (k + 1) + 1 = e.f k := hkdeg.symm
  have hA : A = P := B.partialTotalStepShortComplex_X₂ m
  have hZ : Z = T := B.partialTotalStepShortComplex_X₃ m
  have hAext : (A.extend e).X (e.f k) = A.X k := by
    change HomologicalComplex.extend.X A (e.r (e.f k)) = A.X k
    rw [e.r_eq_some rfl]
    rfl
  have hZext : (Z.extend e).X (e.f k) = Z.X k := by
    change HomologicalComplex.extend.X Z (e.r (e.f k)) = Z.X k
    rw [e.r_eq_some rfl]
    rfl
  have hAP : A.X k = P.X k :=
    congrArg (fun K : ChainComplex C ℕ => K.X k) hA
  have hZT : Z.X k = T.X k :=
    congrArg (fun K : ChainComplex C ℕ => K.X k) hZ
  have hSource : V.X₁.X (e.f k) = P.X k := by
    change
      ((((B.partialTotalStepShortComplex (m + 1)).X₁).extend e).X
        (e.f k)) = P.X k
    have hExt :
        ((((B.partialTotalStepShortComplex (m + 1)).X₁).extend e).X
          (e.f k)) =
          ((B.partialTotalStepShortComplex (m + 1)).X₁).X k := by
      change HomologicalComplex.extend.X
        (B.partialTotalStepShortComplex (m + 1)).X₁
          (e.r (e.f k)) = _
      rw [e.r_eq_some rfl]
      rfl
    exact hExt.trans
      (congrArg (fun K : ChainComplex C ℕ => K.X k)
        (B.partialTotalStepShortComplex_X₁_succ m))
  have hMiddle : U.X₂.X (e.f k) = P.X k := by
    change (A.extend e).X (e.f k) = P.X k
    exact hAext.trans hAP
  have hTarget : U.X₃.X (e.f k) = T.X k := by
    change (Z.extend e).X (e.f k) = T.X k
    exact hZext.trans hZT
  have hSourceIdx : V.X₁.X (e.f (k + 1) + 1) = P.X k :=
    (congrArg (fun i => V.X₁.X i) hidx).trans hSource
  have hShiftSource :
      ((T.extend e)⟦(1 : ℤ)⟧).X (e.f (k + 1)) =
        (T.extend e).X (e.f k) := by
    change (T.extend e).X (e.f (k + 1) + 1) =
      (T.extend e).X (e.f k)
    exact congrArg (T.extend e).X hidx
  have hRawG : HEq (S.g.f k) (B.partialTotalRowQuotientF m k) := by
    cases m with
    | zero =>
        change HEq
          ((B.partialTotalStepShortComplex 0).g.f k)
          ((B.partialTotalRowQuotient 0).f k)
        exact heq_of_eq
          (congrArg (fun f => f.f k)
            B.partialTotalStepShortComplex_g_zero)
    | succ m =>
        change HEq
          ((B.partialTotalStepShortComplex (m + 1)).g.f k)
          ((B.partialTotalRowQuotient (m + 1)).f k)
        exact heq_of_eq
          (congrArg (fun f => f.f k)
            (B.partialTotalStepShortComplex_g_succ m))
  have hRawGEq :
      S.g.f k =
        eqToHom hAP ≫ B.partialTotalRowQuotientF m k ≫
          eqToHom hZT.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq
      (S.g.f k) (B.partialTotalRowQuotientF m k) hAP hZT).mpr hRawG
  have hAiso : (A.extendXIso e rfl).hom = eqToHom hAext := by
    dsimp only [HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso]
    rfl
  have hZiso : (Z.extendXIso e rfl).inv = eqToHom hZext.symm := by
    dsimp only [HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso]
    rfl
  have hGSource : (A.extend e).X (e.f k) = P.X k :=
    hAext.trans hAP
  have hGTarget : (Z.extend e).X (e.f k) = T.X k :=
    hZext.trans hZT
  have hG : HEq (U.g.f (e.f k))
      (B.partialTotalRowQuotientF m k) := by
    change HEq ((HomologicalComplex.extendMap S.g e).f (e.f k)) _
    apply (CategoryTheory.conj_eqToHom_iff_heq
      ((HomologicalComplex.extendMap S.g e).f (e.f k))
      (B.partialTotalRowQuotientF m k) hGSource hGTarget).mp
    rw [HomologicalComplex.extendMap_f (φ := S.g) (e := e) rfl,
      hAiso, hRawGEq, hZiso]
    simp only [Category.assoc]
    slice_lhs 1 2 => rw [CategoryTheory.eqToHom_trans]
    slice_lhs 3 4 => rw [CategoryTheory.eqToHom_trans]
  have hAdj := B.partialTotalAdjacentStepCochainIso_hom_f_heq m k
  have hRow := B.partialTotalStepCochainX₃Iso_hom_f_heq m k
  have hAdjG : HEq
      ((B.partialTotalAdjacentStepCochainIso m).hom.f (e.f k) ≫
        U.g.f (e.f k))
      (𝟙 (P.X k) ≫ B.partialTotalRowQuotientF m k) :=
    CategoryTheory.heq_comp hSource hMiddle hTarget hAdj hG
  have hQ_f : Q.f (e.f k) =
      ((B.partialTotalAdjacentStepCochainIso m).hom.f (e.f k) ≫
        U.g.f (e.f k)) ≫
        (B.partialTotalStepCochainX₃Iso m).hom.f (e.f k) := by
    dsimp only [Q]
    simp only [HomologicalComplex.comp_f, Category.assoc]
  have hComposite : HEq
      (((B.partialTotalAdjacentStepCochainIso m).hom.f (e.f k) ≫
        U.g.f (e.f k)) ≫
        (B.partialTotalStepCochainX₃Iso m).hom.f (e.f k))
      ((𝟙 (P.X k) ≫ B.partialTotalRowQuotientF m k) ≫
        (T.extendXIso e (i := k) (i' := e.f k) rfl).inv) := by
    exact CategoryTheory.heq_comp hSource hTarget rfl hAdjG hRow
  have hQSupported : HEq (Q.f (e.f k))
      ((𝟙 (P.X k) ≫ B.partialTotalRowQuotientF m k) ≫
        (T.extendXIso e (i := k) (i' := e.f k) rfl).inv) :=
    (heq_of_eq hQ_f).trans hComposite
  have hQ : HEq (Q.f (e.f k))
      (B.partialTotalRowQuotientF m k ≫
        (T.extendXIso e (i := k) (i' := e.f k) rfl).inv) :=
    hQSupported.trans (heq_of_eq (by simp only [Category.id_comp]))
  have hQIndex : HEq
      (Q.f (e.f (k + 1) + 1)) (Q.f (e.f k)) :=
    congr_arg_heq Q.f hidx
  have hQOriginal : HEq
      (Q.f (e.f (k + 1) + 1))
      (B.partialTotalRowQuotientF m k ≫
        (T.extendXIso e (i := k) (i' := e.f k) rfl).inv) :=
    hQIndex.trans hQ
  let tIso := CochainComplex.shiftFunctorObjXIso
    (T.extend e) 1 (e.f (k + 1)) (e.f k) hkdeg
  have hShiftEq : tIso.hom =
      eqToHom (congrArg (T.extend e).X hidx) := by
    dsimp only [tIso, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq]
    rfl
  have hShift : HEq tIso.hom (𝟙 ((T.extend e).X (e.f k))) := by
    rw [hShiftEq]
    exact CategoryTheory.eqToHom_heq_id_cod _ _ _
  have hFinal := CategoryTheory.heq_comp
    hSourceIdx hShiftSource rfl hQOriginal hShift
  exact hFinal.trans
    (heq_of_eq (Category.comp_id
      (B.partialTotalRowQuotientF m k ≫
        (T.extendXIso e (i := k) (i' := e.f k) rfl).inv)))

/-- The connecting-map model between adjacent first-page rows.

The successor-step connecting morphism followed by projection onto the preceding signed row
gives a map from total-row homology degree `m+1+q` to degree `m+q`. -/
noncomputable def partialTotalE₁ConnectingDifferential (m q : ℕ) :
    (B.totalRow (m + 1)).homology (m + 1 + q) ⟶
      (B.totalRow m).homology (m + q) := by
  let S := B.partialTotalStepCochainShortComplex (m + 1)
  let T := B.partialTotalStepCochainShortComplex m
  let hS : S.ShortExact := B.partialTotalStepCochainShortExact (m + 1)
  let n : ℤ := -((m + 1 + q : ℕ) : ℤ)
  let n' : ℤ := -((m + q : ℕ) : ℤ)
  have hnn' : n + 1 = n' := by
    dsimp [n, n']
    omega
  exact ((B.totalRow (m + 1)).extendHomologyIso
      ComplexShape.embeddingDownNat rfl).inv ≫
    (HomologicalComplex.homologyMapIso
      (B.partialTotalStepCochainX₃Iso (m + 1)) n).inv ≫
    hS.δ n n' hnn' ≫
    (HomologicalComplex.homologyMapIso
      (B.partialTotalAdjacentStepCochainIso m) n').hom ≫
    HomologicalComplex.homologyMap T.g n' ≫
    (HomologicalComplex.homologyMapIso
      (B.partialTotalStepCochainX₃Iso m) n').hom ≫
    ((B.totalRow m).extendHomologyIso
      ComplexShape.embeddingDownNat rfl).hom

end HomologicalComplex₂

end
