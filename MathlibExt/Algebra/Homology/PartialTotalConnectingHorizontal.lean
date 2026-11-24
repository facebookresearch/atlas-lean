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

public import MathlibExt.Algebra.Homology.PartialTotalConnectingDifferential
public import MathlibExt.Algebra.Homology.PartialTotalHorizontalRowCocycle
public import MathlibExt.Algebra.Homology.PartialTotalSuccessorCochainSplitting
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# The partial-total connecting map is the horizontal row map

The connecting morphism of the successor filtration step agrees with the
homology map induced by the horizontal degree-one cocycle between adjacent
signed rows.  This comparison is chain-level and makes no spectral-page,
E₂, Tor, abutment, or convergence claim.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem shortExact_delta_eq_shiftMap_homOfDegreewiseSplit
    {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact)
    (σ : ∀ i, (S.map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting)
    (n n' : ℤ) (hnn' : n + 1 = n') :
    hS.δ n n' hnn' =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (CochainComplex.homOfDegreewiseSplit S σ) n n' (by omega) := by
  subst n'
  let φ : S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧ :=
    CochainComplex.homOfDegreewiseSplit S σ
  let E₀ := HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let E₁ := HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1)
  let S₀ := S.map E₀
  let S₁ := S.map E₁
  let A := S.X₃.cycles n
  let x₃₀ : A ⟶ S₀.X₃ := S.X₃.iCycles n
  let d₂ : S₀.X₂ ⟶ S₁.X₂ := S.X₂.d n (n + 1)
  let d₃ : S₀.X₃ ⟶ S₁.X₃ := S.X₃.d n (n + 1)
  let x₂₀ : A ⟶ S₀.X₂ := x₃₀ ≫ (σ n).s
  let x₂₁ : A ⟶ S₁.X₂ := x₂₀ ≫ d₂
  let x₁₁ : A ⟶ S₁.X₁ := x₂₁ ≫ (σ (n + 1)).r
  have hx₂₀ : x₂₀ ≫ S₀.g = x₃₀ := by
    dsimp only [x₂₀]
    rw [Category.assoc, (σ n).s_g, Category.comp_id]
  have hcomm : d₂ ≫ S₁.g = S₀.g ≫ d₃ := by
    dsimp only [d₂, d₃, S₀, S₁, E₀, E₁]
    simpa only [ShortComplex.map_g, HomologicalComplex.eval_map] using
      (S.g.comm n (n + 1)).symm
  have hx₃₀ : x₃₀ ≫ d₃ = 0 := by
    dsimp only [x₃₀, d₃]
    exact S.X₃.iCycles_d n (n + 1)
  have hcycle₁ : x₂₁ ≫ S₁.g = 0 := by
    dsimp only [x₂₁]
    rw [Category.assoc, hcomm, ← Category.assoc, hx₂₀, hx₃₀]
  have hx₁₁ : x₁₁ ≫ S₁.f = x₂₁ := by
    dsimp only [x₁₁]
    rw [Category.assoc, (σ (n + 1)).r_f]
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      hcycle₁, zero_comp, sub_zero]
  let x₃ : A ⟶ S.X₃.X n := x₃₀
  let x₂ : A ⟶ S.X₂.X n := x₂₀
  let x₁ : A ⟶ S.X₁.X (n + 1) := x₁₁
  have hx₃ : x₃ ≫ S.X₃.d n (n + 1) = 0 := by
    simpa only [x₃, x₃₀, d₃, S₀, S₁, E₀, E₁,
      ShortComplex.map_X₃, HomologicalComplex.eval_obj] using hx₃₀
  have hx₂ : x₂ ≫ S.g.f n = x₃ := by
    simpa only [x₂, x₃, x₂₀, x₃₀, S₀, E₀,
      ShortComplex.map_X₂, ShortComplex.map_X₃,
      ShortComplex.map_g, HomologicalComplex.eval_obj,
      HomologicalComplex.eval_map] using hx₂₀
  have hx₁ :
      x₁ ≫ S.f.f (n + 1) = x₂ ≫ S.X₂.d n (n + 1) := by
    simpa only [x₁, x₂, x₁₁, x₂₁, x₂₀, d₂, S₀, S₁, E₀, E₁,
      ShortComplex.map_X₁, ShortComplex.map_X₂,
      ShortComplex.map_f, HomologicalComplex.eval_obj,
      HomologicalComplex.eval_map] using hx₁₁
  have hx₁cycle : x₁ ≫ S.X₁.d (n + 1) (n + 2) = 0 := by
    have := hS.mono_f
    rw [← cancel_mono (S.f.f (n + 2)), Category.assoc, ← S.f.comm,
      reassoc_of% hx₁, HomologicalComplex.d_comp_d, comp_zero, zero_comp]
  have hnext : (ComplexShape.up ℤ).next n = n + 1 :=
    CochainComplex.next ℤ n
  have hnext' : (ComplexShape.up ℤ).next (n + 1) = n + 2 := by
    simpa only [add_assoc, one_add_one_eq_two] using
      (CochainComplex.next ℤ (n + 1))
  have hlift₃ :
      S.X₃.liftCycles x₃ (n + 1) hnext hx₃ = 𝟙 _ := by
    rw [← cancel_mono (S.X₃.iCycles n),
      HomologicalComplex.liftCycles_i, Category.id_comp]
  have hδ := hS.δ_eq n (n + 1) rfl x₃ hx₃ x₂ hx₂ x₁ hx₁
    (n + 2) hnext'
  rw [hlift₃, Category.id_comp] at hδ
  have hφf :
      x₃ ≫ φ.f n ≫
          (CochainComplex.shiftFunctorObjXIso S.X₁ 1 n (n + 1)
            (by omega)).hom = x₁ := by
    dsimp only [φ, x₁, x₂, x₁₁, x₂₁, x₂₀, x₃, x₃₀,
      d₂, S₀, S₁, E₀, E₁]
    rw [CochainComplex.homOfDegreewiseSplit_f]
    simp only [CochainComplex.cocycleOfDegreewiseSplit,
      CochainComplex.HomComplex.Cocycle.mk_coe,
      CochainComplex.HomComplex.Cochain.mk_v,
      CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    cat_disch
  let y : A ⟶ S.X₁.X (n + 1) :=
    (x₃ ≫ φ.f n) ≫
      (CochainComplex.shiftFunctorObjXIso S.X₁ 1 n (n + 1)
        (by omega)).hom
  have hyx : y = x₁ := by
    dsimp only [y]
    rw [Category.assoc]
    exact hφf
  have hy : y ≫ S.X₁.d (n + 1) (n + 2) = 0 := by
    rw [hyx, hx₁cycle]
  have hlift :
      S.X₁.liftCycles y (n + 2) hnext' hy =
        S.X₁.liftCycles x₁ (n + 2) hnext' hx₁cycle := by
    rw [← cancel_mono (S.X₁.iCycles (n + 1)),
      HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i]
    exact hyx
  have hlift' := hlift
  dsimp only [y] at hlift'
  simp only [CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom] at hlift'
  have hliftπ := congrArg
    (fun f => f ≫ S.X₁.homologyπ (n + 1)) hlift'
  have hliftπid :=
    (Category.assoc _ _ (𝟙 _)).symm.trans
      ((Category.comp_id _).trans hliftπ)
  have hcycles :
      HomologicalComplex.cyclesMap φ n =
        (S.X₁⟦(1 : ℤ)⟧).liftCycles (x₃ ≫ φ.f n) (n + 1) hnext
          (by rw [Category.assoc, φ.comm, reassoc_of% hx₃, zero_comp]) := by
    rw [← cancel_mono ((S.X₁⟦(1 : ℤ)⟧).iCycles n),
      HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i]
  have hshift :
      S.X₃.homologyπ n ≫
          (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
            φ n (n + 1) (by omega) =
        S.X₁.liftCycles x₁ (n + 2) hnext' (by
          exact hx₁cycle) ≫ S.X₁.homologyπ (n + 1) := by
    dsimp [CategoryTheory.Functor.shiftMap,
      CochainComplex.homologyFunctor_shift]
    rw [HomologicalComplex.homologyπ_naturality_assoc, hcycles,
      CochainComplex.liftCycles_shift_homologyπ_assoc
        S.X₁ (x₃ ≫ φ.f n) (n + 1) hnext _
        (n + 1) (by omega) (n + 2) hnext',
      Iso.inv_hom_id_app]
    dsimp [CochainComplex.homologyFunctor_shift]
    exact hliftπid
  rw [← cancel_epi (S.X₃.homologyπ n)]
  exact hδ.trans hshift.symm

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

private noncomputable def partialTotalSplitTargetMap (m : ℕ) :
    (B.partialTotalStepCochainShortComplex (m + 1)).X₁ ⟶
      (B.totalRow m).extend ComplexShape.embeddingDownNat :=
  (B.partialTotalAdjacentStepCochainIso m).hom ≫
    (B.partialTotalStepCochainShortComplex m).g ≫
    (B.partialTotalStepCochainX₃Iso m).hom

private noncomputable def partialTotalTransportedSplitShift (m : ℕ) :
    (B.totalRow (m + 1)).extend ComplexShape.embeddingDownNat ⟶
      ((B.totalRow m).extend ComplexShape.embeddingDownNat)⟦(1 : ℤ)⟧ :=
  (B.partialTotalStepCochainX₃Iso (m + 1)).inv ≫
    CochainComplex.homOfDegreewiseSplit
      (B.partialTotalStepCochainShortComplex (m + 1))
      (B.partialTotalSuccessorCochainSplitting m) ≫
    (B.partialTotalSplitTargetMap m)⟦(1 : ℤ)⟧'

set_option backward.isDefEq.respectTransparency false in
private theorem partialTotalTransportedSplitShift_eq (m : ℕ) :
    B.partialTotalTransportedSplitShift m =
      B.partialTotalHorizontalRowShift m := by
  ext i
  let e := ComplexShape.embeddingDownNat
  let K := B.totalRow (m + 1)
  let L := B.totalRow m
  obtain hi | ⟨k, hk⟩ := (e.r i).eq_none_or_eq_some
  · exact (K.isZero_extend_X' e i hi).eq_of_src _ _
  · rcases k with _ | k
    · have hi₀ : e.f 0 = i := e.f_eq_of_r_eq_some hk
      exact ((B.totalRow_isZero_X (m + 1) 0 (by omega)).of_iso
        (K.extendXIso e hi₀)).eq_of_src _ _
    · have hik : e.f (k + 1) = i := e.f_eq_of_r_eq_some hk
      subst i
      let P := B.partialTotal (m + 1)
      let P₀ := B.partialTotal m
      let S := B.partialTotalStepCochainShortComplex (m + 1)
      let Q := B.partialTotalSplitTargetMap m
      let iPlus := e.f (k + 1)
      let iZero := e.f (k + 1) + 1
      have hkdeg : e.f k = iZero := by
        dsimp only [iZero]
        change -((k : ℕ) : ℤ) = -(((k + 1 : ℕ) : ℤ)) + 1
        omega
      let tIso := CochainComplex.shiftFunctorObjXIso
        (L.extend e) 1 iPlus (e.f k) hkdeg
      have hX₃ : S.X₃.X iPlus = (K.extend e).X iPlus := by
        change (K.extend e).X iPlus = (K.extend e).X iPlus
        rfl
      have hX₂Plus : S.X₂.X iPlus = (P.extend e).X iPlus := by
        change (P.extend e).X iPlus = (P.extend e).X iPlus
        rfl
      have hX₂Zero : S.X₂.X iZero = (P.extend e).X iZero := by
        change (P.extend e).X iZero = (P.extend e).X iZero
        rfl
      have hX₁Zero : S.X₁.X iZero = P₀.X k := by
        change (P₀.extend e).X iZero = P₀.X k
        have hidx : iZero = e.f k := hkdeg.symm
        exact (congrArg (fun j => (P₀.extend e).X j) hidx).trans (by
          change HomologicalComplex.extend.X P₀ (e.r (e.f k)) = P₀.X k
          rw [e.r_eq_some rfl]
          rfl)
      have hInv :=
        B.partialTotalStepCochainX₃Iso_inv_f_heq (m + 1) (k + 1)
      have hS := B.partialTotalSuccessorCochainSplitting_s m (k + 1)
      have hR := B.partialTotalSuccessorCochainSplitting_r m k hkdeg
      have hQ :=
        B.partialTotalAdjacentTargetMap_f_comp_shiftIso_heq m k hkdeg
      change HEq
        (Q.f iZero ≫ tIso.hom)
        (B.partialTotalRowQuotientF m k ≫
          (L.extendXIso e (i := k) (i' := e.f k) rfl).inv) at hQ
      have hKext : (K.extend e).X iPlus = K.X (k + 1) := by
        change HomologicalComplex.extend.X K (e.r (e.f (k + 1))) = _
        rw [e.r_eq_some rfl]
        rfl
      have hKhom :
          (K.extendXIso e (i := k + 1) (i' := iPlus) rfl).hom =
            eqToHom hKext := by
        dsimp only [HomologicalComplex.extendXIso,
          HomologicalComplex.extend.XIso]
        rfl
      have hKhomId : HEq
          (K.extendXIso e (i := k + 1) (i' := iPlus) rfl).hom
          (𝟙 ((K.extend e).X iPlus)) :=
        (heq_of_eq hKhom).trans
          (CategoryTheory.eqToHom_heq_id_dom _ _ hKext)
      have hInvNorm : HEq
          ((B.partialTotalStepCochainX₃Iso (m + 1)).inv.f iPlus)
          (𝟙 ((K.extend e).X iPlus)) :=
        hInv.trans hKhomId
      have hInvS := CategoryTheory.heq_comp
        rfl hX₃ hX₂Plus hInvNorm hS
      have hInvS' : HEq
          ((B.partialTotalStepCochainX₃Iso (m + 1)).inv.f iPlus ≫
            (B.partialTotalSuccessorCochainSplitting m iPlus).s)
          ((K.extendXIso e (i := k + 1) (i' := iPlus) rfl).hom ≫
            B.partialTotalRowQuotientSectionF (m + 1) (k + 1) ≫
            (P.extendXIso e (i := k + 1) (i' := iPlus) rfl).inv) := by
        simpa only [iPlus, K, P, e, Category.id_comp] using hInvS
      have hD :
          S.X₂.d iPlus iZero =
            (P.extendXIso e (i := k + 1) (i' := iPlus) rfl).hom ≫
              P.d (k + 1) k ≫
              (P.extendXIso e (i := k) (i' := iZero) hkdeg).inv := by
        change (P.extend e).d iPlus iZero = _
        exact P.extend_d_eq e rfl hkdeg
      have hInvSD := CategoryTheory.heq_comp
        rfl hX₂Plus hX₂Zero hInvS' (heq_of_eq hD)
      have hP₀ext : (P₀.extend e).X iZero = P₀.X k := by
        change HomologicalComplex.extend.X P₀ (e.r iZero) = P₀.X k
        rw [← hkdeg, e.r_eq_some rfl]
        rfl
      have hP₀inv :
          (P₀.extendXIso e (i := k) (i' := iZero) hkdeg).inv =
            eqToHom hP₀ext.symm := by
        dsimp only [HomologicalComplex.extendXIso,
          HomologicalComplex.extend.XIso]
        rfl
      have hP₀invId : HEq
          (P₀.extendXIso e (i := k) (i' := iZero) hkdeg).inv
          (𝟙 (P₀.X k)) :=
        (heq_of_eq hP₀inv).trans
          (CategoryTheory.eqToHom_heq_id_dom _ _ hP₀ext.symm)
      let rPrefix :=
        (P.extendXIso e (i := k) (i' := iZero) hkdeg).hom ≫
          B.partialTotalSuccRetractionF m k
      have hRCoord := CategoryTheory.heq_comp
        rfl rfl hP₀ext (HEq.rfl : HEq rPrefix rPrefix) hP₀invId
      have hR' : HEq
          (B.partialTotalSuccessorCochainSplitting m iZero).r
          (rPrefix ≫
            (P₀.extendXIso e (i := k) (i' := iZero) hkdeg).inv) := by
        simpa only [rPrefix, P, P₀, iZero, Category.assoc] using hR
      have hRNorm : HEq
          (B.partialTotalSuccessorCochainSplitting m iZero).r rPrefix :=
        hR'.trans (hRCoord.trans
          (heq_of_eq (Category.comp_id rPrefix)))
      have hRQ := CategoryTheory.heq_comp
        hX₂Zero hX₁Zero rfl hRNorm hQ
      have hWhole := CategoryTheory.heq_comp
        rfl hX₂Zero rfl hInvSD hRQ
      have hWholeEq := eq_of_heq hWhole
      simp only [iPlus, iZero, S, Q, e, Category.assoc] at hWholeEq
      rw [← cancel_mono tIso.hom]
      rw [B.partialTotalHorizontalRowShift_f_comp_shiftIso m k]
      simp only [partialTotalTransportedSplitShift,
        HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
        Category.assoc]
      rw [CochainComplex.homOfDegreewiseSplit_f]
      simp only [CochainComplex.cocycleOfDegreewiseSplit,
        CochainComplex.HomComplex.Cocycle.mk_coe,
        CochainComplex.HomComplex.Cochain.mk_v]
      simp only [Category.assoc]
      rw [hWholeEq]
      dsimp only [rPrefix]
      dsimp only [e]
      slice_lhs 3 4 => rw [Iso.inv_hom_id]
      simp only [Category.id_comp]
      slice_lhs 4 5 => rw [Iso.inv_hom_id]
      simp only [Category.id_comp]
      dsimp only [partialTotalHorizontalRowF]
      simp only [Category.assoc]
      dsimp only [K, L, P]

set_option backward.isDefEq.respectTransparency false in
/-- The connecting morphism of a successor partial-total step is the homology
map induced by the horizontal degree-one cocycle between its adjacent signed
rows. -/
@[reassoc]
theorem partialTotalE₁ConnectingDifferential_eq_horizontalRowHomology
    (m q : ℕ) :
    B.partialTotalE₁ConnectingDifferential m q =
      B.partialTotalHorizontalRowHomology m q := by
  let S := B.partialTotalStepCochainShortComplex (m + 1)
  let T := B.partialTotalStepCochainShortComplex m
  let hS : S.ShortExact := B.partialTotalStepCochainShortExact (m + 1)
  let n : ℤ := -((m + 1 + q : ℕ) : ℤ)
  let n' : ℤ := -((m + q : ℕ) : ℤ)
  have hnn' : n + 1 = n' := by
    dsimp only [n, n']
    omega
  let e₃ := B.partialTotalStepCochainX₃Iso (m + 1)
  let Q : S.X₁ ⟶ (B.totalRow m).extend ComplexShape.embeddingDownNat :=
    (B.partialTotalAdjacentStepCochainIso m).hom ≫ T.g ≫
      (B.partialTotalStepCochainX₃Iso m).hom
  have hE₃ :
      (HomologicalComplex.homologyMapIso e₃ n).inv =
        HomologicalComplex.homologyMap e₃.inv n :=
    rfl
  have hQ :
      HomologicalComplex.homologyMap Q n' =
        (HomologicalComplex.homologyMapIso
          (B.partialTotalAdjacentStepCochainIso m) n').hom ≫
          HomologicalComplex.homologyMap T.g n' ≫
          (HomologicalComplex.homologyMapIso
            (B.partialTotalStepCochainX₃Iso m) n').hom := by
    dsimp only [Q]
    simp only [HomologicalComplex.homologyMapIso_hom,
      HomologicalComplex.homologyMap_comp]
  have hδ := shortExact_delta_eq_shiftMap_homOfDegreewiseSplit hS
    (B.partialTotalSuccessorCochainSplitting m) n n' hnn'
  let F := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0
  let φ : S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧ :=
    CochainComplex.homOfDegreewiseSplit S
      (B.partialTotalSuccessorCochainSplitting m)
  have hMapE₃ :
      HomologicalComplex.homologyMap e₃.inv n =
        (F.shift n).map e₃.inv :=
    by
      change HomologicalComplex.homologyMap e₃.inv n =
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map
          e₃.inv
      rfl
  have hMapQ :
      HomologicalComplex.homologyMap Q n' =
        (F.shift n').map Q :=
    by
      change HomologicalComplex.homologyMap Q n' =
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n').map Q
      rfl
  have hShiftCompF :
      (F.shift n).map e₃.inv ≫
          F.shiftMap φ n n' (by omega) ≫
          (F.shift n').map Q =
        F.shiftMap (e₃.inv ≫ φ ≫ Q⟦(1 : ℤ)⟧') n n' (by omega) := by
    slice_lhs 1 2 => rw [← CategoryTheory.Functor.shiftMap_comp']
    rw [← CategoryTheory.Functor.shiftMap_comp]
    simp only [Category.assoc]
  have hTransport :
      e₃.inv ≫ φ ≫ Q⟦(1 : ℤ)⟧' =
        B.partialTotalTransportedSplitShift m :=
    rfl
  rw [partialTotalE₁ConnectingDifferential,
    B.partialTotalHorizontalRowHomology_eq]
  rw [hE₃]
  slice_lhs 4 6 => rw [← hQ]
  change
    ((B.totalRow (m + 1)).extendHomologyIso
        ComplexShape.embeddingDownNat rfl).inv ≫
      HomologicalComplex.homologyMap e₃.inv n ≫
      hS.δ n n' hnn' ≫
      HomologicalComplex.homologyMap Q n' ≫
      ((B.totalRow m).extendHomologyIso
        ComplexShape.embeddingDownNat rfl).hom =
    ((B.totalRow (m + 1)).extendHomologyIso
        ComplexShape.embeddingDownNat rfl).inv ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (B.partialTotalHorizontalRowShift m) n n' (by omega) ≫
      ((B.totalRow m).extendHomologyIso
        ComplexShape.embeddingDownNat rfl).hom
  rw [hδ]
  rw [hMapE₃, hMapQ]
  slice_lhs 2 4 => rw [hShiftCompF]
  rw [hTransport]
  rw [B.partialTotalTransportedSplitShift_eq m]

set_option backward.isDefEq.respectTransparency false in
/-- The connecting morphism of a successor partial-total step agrees with
the horizontal row map at arbitrary supported total degrees. -/
theorem partialTotalE₁Connecting_eq_horizontalRowAt
    (m q nPlus nZero : ℕ)
    (hPlus : (m + 1) + q = nPlus)
    (hZero : m + q = nZero) :
    let eNat := ComplexShape.embeddingDownNat
    let νPlus : ℤ := -((nPlus : ℕ) : ℤ)
    let νZero : ℤ := -((nZero : ℕ) : ℤ)
    let S := B.partialTotalStepCochainShortComplex (m + 1)
    let T := B.partialTotalStepCochainShortComplex m
    let hS : S.ShortExact :=
      B.partialTotalStepCochainShortExact (m + 1)
    let cAt :
        (B.totalRow (m + 1)).homology nPlus ⟶
          (B.totalRow m).homology nZero :=
      ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalStepCochainX₃Iso (m + 1)) νPlus).inv ≫
        hS.δ νPlus νZero (by
          have hPlusZ := congrArg (fun x : ℕ => (x : ℤ)) hPlus
          have hZeroZ := congrArg (fun x : ℕ => (x : ℤ)) hZero
          change -((nPlus : ℕ) : ℤ) + 1 = -((nZero : ℕ) : ℤ)
          rw [← hPlusZ, ← hZeroZ]
          omega) ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalAdjacentStepCochainIso m) νZero).hom ≫
        HomologicalComplex.homologyMap T.g νZero ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalStepCochainX₃Iso m) νZero).hom ≫
        ((B.totalRow m).extendHomologyIso eNat rfl).hom
    let rAt :
        (B.totalRow (m + 1)).homology nPlus ⟶
          (B.totalRow m).homology nZero :=
      ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
        (HomologicalComplex.homologyFunctor C
          (ComplexShape.up ℤ) 0).shiftMap
            (B.partialTotalHorizontalRowShift m)
            νPlus νZero (by
              have hPlusZ := congrArg (fun x : ℕ => (x : ℤ)) hPlus
              have hZeroZ := congrArg (fun x : ℕ => (x : ℤ)) hZero
              change 1 + -((nPlus : ℕ) : ℤ) = -((nZero : ℕ) : ℤ)
              rw [← hPlusZ, ← hZeroZ]
              omega) ≫
        ((B.totalRow m).extendHomologyIso eNat rfl).hom
    cAt = rAt := by
  dsimp only
  let eNat := ComplexShape.embeddingDownNat
  let νPlus : ℤ := -((nPlus : ℕ) : ℤ)
  let νZero : ℤ := -((nZero : ℕ) : ℤ)
  let S := B.partialTotalStepCochainShortComplex (m + 1)
  let T := B.partialTotalStepCochainShortComplex m
  let hS : S.ShortExact :=
    B.partialTotalStepCochainShortExact (m + 1)
  have hPlusZ := congrArg (fun x : ℕ => (x : ℤ)) hPlus
  have hZeroZ := congrArg (fun x : ℕ => (x : ℤ)) hZero
  have hν : νPlus + 1 = νZero := by
    change -((nPlus : ℕ) : ℤ) + 1 = -((nZero : ℕ) : ℤ)
    rw [← hPlusZ, ← hZeroZ]
    omega
  have hνShift : 1 + νPlus = νZero := by
    omega
  let e₃ := B.partialTotalStepCochainX₃Iso (m + 1)
  let Q : S.X₁ ⟶ (B.totalRow m).extend eNat :=
    (B.partialTotalAdjacentStepCochainIso m).hom ≫ T.g ≫
      (B.partialTotalStepCochainX₃Iso m).hom
  have hE₃ :
      (HomologicalComplex.homologyMapIso e₃ νPlus).inv =
        HomologicalComplex.homologyMap e₃.inv νPlus :=
    rfl
  have hQ :
      HomologicalComplex.homologyMap Q νZero =
        (HomologicalComplex.homologyMapIso
          (B.partialTotalAdjacentStepCochainIso m) νZero).hom ≫
          HomologicalComplex.homologyMap T.g νZero ≫
          (HomologicalComplex.homologyMapIso
            (B.partialTotalStepCochainX₃Iso m) νZero).hom := by
    dsimp only [Q]
    simp only [HomologicalComplex.homologyMapIso_hom,
      HomologicalComplex.homologyMap_comp]
  have hδ := shortExact_delta_eq_shiftMap_homOfDegreewiseSplit hS
    (B.partialTotalSuccessorCochainSplitting m) νPlus νZero hν
  let F := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0
  let φ : S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧ :=
    CochainComplex.homOfDegreewiseSplit S
      (B.partialTotalSuccessorCochainSplitting m)
  have hMapE₃ :
      HomologicalComplex.homologyMap e₃.inv νPlus =
        (F.shift νPlus).map e₃.inv := by
    change HomologicalComplex.homologyMap e₃.inv νPlus =
      (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) νPlus).map e₃.inv
    rfl
  have hMapQ :
      HomologicalComplex.homologyMap Q νZero =
        (F.shift νZero).map Q := by
    change HomologicalComplex.homologyMap Q νZero =
      (HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) νZero).map Q
    rfl
  have hShiftCompF :
      (F.shift νPlus).map e₃.inv ≫
          F.shiftMap φ νPlus νZero (by omega) ≫
          (F.shift νZero).map Q =
        F.shiftMap (e₃.inv ≫ φ ≫ Q⟦(1 : ℤ)⟧')
          νPlus νZero (by omega) := by
    slice_lhs 1 2 => rw [← CategoryTheory.Functor.shiftMap_comp']
    rw [← CategoryTheory.Functor.shiftMap_comp]
    simp only [Category.assoc]
  have hTransport :
      e₃.inv ≫ φ ≫ Q⟦(1 : ℤ)⟧' =
        B.partialTotalTransportedSplitShift m :=
    rfl
  rw [hE₃]
  slice_lhs 4 6 => rw [← hQ]
  change
    ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
      HomologicalComplex.homologyMap e₃.inv νPlus ≫
      hS.δ νPlus νZero hν ≫
      HomologicalComplex.homologyMap Q νZero ≫
      ((B.totalRow m).extendHomologyIso eNat rfl).hom =
    ((B.totalRow (m + 1)).extendHomologyIso eNat rfl).inv ≫
      F.shiftMap (B.partialTotalHorizontalRowShift m)
        νPlus νZero hνShift ≫
      ((B.totalRow m).extendHomologyIso eNat rfl).hom
  rw [hδ]
  rw [hMapE₃, hMapQ]
  slice_lhs 2 4 => rw [hShiftCompF]
  rw [hTransport]
  rw [B.partialTotalTransportedSplitShift_eq m]

end HomologicalComplex₂

end
