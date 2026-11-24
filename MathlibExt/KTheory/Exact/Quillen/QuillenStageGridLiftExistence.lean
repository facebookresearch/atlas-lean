/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.AdmissibleMonoFlagStage
public import MathlibExt.KTheory.Exact.Quillen.QuillenSimplexSpanFiltration
public import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellNormalized

/-!
# Existence of Stage-grid lifts for Quillen simplices

An explicit adjacent-span presentation of a finite Quillen simplex determines
the kernel/apex filtration constructed in
`QuillenSimplexSpanFiltration`.  Quotient-completing that admissible-mono flag
produces a material edgewise Stage.  Its shell representatives are compared
with the fixed right-associated interval spans, yielding an isomorphism from
the extracted Quillen simplex to the retained simplex.

The final theorem is existence-valued.  No public grid selector, functorial
choice of presentation, strict inverse, fiber contractibility, simplicial
object, bar construction, Quillen Theorem A/B, weak equivalence, realization,
or Q/S comparison is asserted.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenStageGridLiftExistenceWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

namespace QuillenSimplexSpanPresentation

variable {a : SimplexCategory} {q : QuillenQSimplex C a}

theorem apexIsoOfSpanIso_symm
    {X Y : C} {S T : QuillenSpan X Y} (e : S ≅ T) :
    Span.SpanBicat.apexIso e.symm = (Span.SpanBicat.apexIso e).symm := by
  ext
  rfl

theorem apexIsoOfSpanEq_hom
    {X Y : C} {S T : QuillenSpan X Y} (h : S = T) :
    (Span.SpanBicat.apexIso (eqToIso h)).hom =
      eqToHom (congrArg Span.apex h) := by
  cases h
  rfl

theorem apexIsoOfSpanEq_inv
    {X Y : C} {S T : QuillenSpan X Y} (h : S = T) :
    (Span.SpanBicat.apexIso (eqToIso h)).inv =
      eqToHom (congrArg Span.apex h).symm := by
  cases h
  rfl

/-- Adapter from the Quillen filtration packet to the generic admissible-mono
flag consumed by quotient completion. -/
noncomputable def admissibleMonoFlag
    (P : QuillenSimplexSpanPresentation q) :
    AdmissibleMonoFlag C (edgewiseQ.obj a).len where
  chain := P.filtration.chain
  first_isZero := P.filtration.first_isZero
  step_admissible i hi :=
    P.filtration.step_admissible ⟨i, hi⟩

/-- Quotient-completed material edgewise Stage attached to an explicit
simplex presentation. -/
noncomputable def filtrationStage
    (P : QuillenSimplexSpanPresentation q) :
    Stage C (edgewiseQ.obj a).len :=
  P.admissibleMonoFlag.toStage

@[simp]
theorem filtrationStage_obj_interval
    (P : QuillenSimplexSpanPresentation q)
    (i j : Fin ((edgewiseQ.obj a).len + 1)) (hij : i ≤ j) :
    P.filtrationStage.obj.obj (interval i j hij) =
      P.admissibleMonoFlag.intervalQuotient i j hij :=
  rfl

/-- The kernel and apex successor maps form the commutative ladder carried by
the recursive QGRID-A pullback construction. -/
theorem tailKernel_apex_succ
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) :
    P.tailKernelSuccFromNat k hk ≫
        (tailKernelPresentationFromNat P k (by omega)).ι ≫
        P.tailApexSuccFromNat k hk =
      (tailKernelPresentationFromNat P (k + 1) hk).ι := by
  have hk0 : k < a.len := by omega
  let S := P.span ⟨k, by omega⟩
  let T := tailSpanFromNat P (k + 1) hk
  let Qnext := tailKernelPresentationFromNat P (k + 1) hk
  let R := tailCompositeBaseChange S T Qnext
  have hRobj : R.obj = (Span.comp S T).apex := rfl
  have hRhom : eqToHom hRobj = 𝟙 R.obj := by
    with_unfolding_all
      have hh : hRobj =
          (rfl : R.obj = (Span.comp S T).apex) := Subsingleton.elim _ _
      rw [hh]
      rfl
  let Pproj := R.kernelPresentation
  let Qadj := P.adjacentKernelPresentation ⟨k, by omega⟩
  let U := Pproj.composite Qadj
  have hSpan : tailSpanFromNat P k hk0 = Span.comp S T :=
    P.tailSpanFromNat_step k hk
  let spanIso : Span.comp S T ≅ tailSpanFromNat P k hk0 :=
    (eqToIso hSpan).symm
  let e : (Span.comp S T).apex ≅ (tailSpanFromNat P k hk0).apex :=
    Span.SpanBicat.apexIso
      (X := ⟨(q.obj' k (by omega)).obj⟩)
      (Y := ⟨(q.obj (Fin.last a.len)).obj⟩) spanIso
  have he : e.hom ≫ (tailSpanFromNat P k hk0).l = R.fst ≫ S.l :=
    spanIso.hom.hom_l.trans (tailCompositeBaseChange_comp_l S T Qnext)
  let Qcur := tailKernelPresentationFromNat P k hk0
  let Qexp := transportKernelPresentationSource U e
    (tailSpanFromNat P k hk0).l he
  have hKernelU : Qcur.kernel = U.kernel := by
    dsimp only [Qcur]
    rw [tailKernelPresentationFromNat]
    split
    · omega
    · apply eq_of_heq
      rfl
  have hIota : HEq Qcur.ι Qexp.ι := by
    dsimp only [Qcur, Qexp]
    rw [tailKernelPresentationFromNat]
    rw [dite_eq_right (by omega : ¬ (k + 1 = a.len))]
  have hCurrent :
      Qcur.ι = eqToHom hKernelU ≫ U.ι ≫
        eqToHom hRobj ≫ e.hom := by
    apply eq_of_heq
    rw [heq_eqToHom_comp_iff]
    refine hIota.trans ?_
    dsimp only [Qexp, transportKernelPresentationSource]
    exact heq_comp rfl rfl rfl (HEq.rfl)
      (eqToHom_comp_heq e.hom hRobj).symm
  have hSource : Qnext.kernel = Pproj.kernel :=
    R.kernelPresentation_kernel.symm
  let f : Pproj.kernel ⟶ U.kernel :=
    (Pproj.compositeKernelSequence Qadj).f
  have hKernelSucc : P.tailKernelSuccFromNat k hk =
      eqToHom hSource ≫ f ≫ eqToHom hKernelU.symm := by
    apply eq_of_heq
    rfl
  let hA := congrArg Span.apex hSpan
  let eF : (tailSpanFromNat P k hk0).apex ≅ (Span.comp S T).apex :=
    Span.SpanBicat.apexIso
      (X := ⟨(q.obj' k (by omega)).obj⟩)
      (Y := ⟨(q.obj (Fin.last a.len)).obj⟩) (eqToIso hSpan)
  have hE : e.hom = eF.inv := rfl
  have heHom : e.hom = eqToHom hA.symm :=
    hE.trans (apexIsoOfSpanEq_inv hSpan)
  have hApexSucc : P.tailApexSuccFromNat k hk =
      eqToHom hA ≫ eqToHom hRobj.symm ≫ R.snd := by
    apply eq_of_heq
    have hL : HEq (P.tailApexSuccFromNat k hk) R.snd := by
      unfold tailApexSuccFromNat
      exact eqToHom_comp_heq R.snd _
    have hR : HEq (eqToHom hA ≫ eqToHom hRobj.symm ≫ R.snd)
        R.snd := by
      simp only [eqToHom_comp_heq_iff]
      rfl
    exact hL.trans hR.symm
  rw [hKernelSucc, hCurrent, heHom, hApexSucc]
  simp only [ComposableArrows.obj', Span.comp_apex, eqToHom_trans,
    eqToHom_trans_assoc, Category.assoc, eqToHom_refl, Category.id_comp]
  apply eq_of_heq
  rw [eqToHom_comp_heq_iff]
  dsimp only [f, U]
  simp only [
    AdmissibleEpiKernelPresentation.compositeKernelSequence_f,
    AdmissibleEpiKernelPresentation.composite_ι]
  let R₂ := Pproj.compositeBaseChange Qadj
  have hAssoc : HEq (R₂.kernelLift ≫ R₂.snd ≫ R.snd)
      ((R₂.kernelLift ≫ R₂.snd) ≫ R.snd) :=
    heq_of_eq (Category.assoc _ _ _).symm
  have hFirst : HEq ((R₂.kernelLift ≫ R₂.snd) ≫ R.snd)
      (Pproj.ι ≫ R.snd) :=
    heq_comp rfl rfl rfl (heq_of_eq R₂.kernelLift_snd) (HEq.rfl)
  have hMiddle : HEq (Pproj.ι ≫ R.snd)
      (R.kernelLift ≫ R.snd) :=
    heq_comp rfl rfl rfl (heq_of_eq R.kernelPresentation_ι) (HEq.rfl)
  exact hAssoc.trans (hFirst.trans (hMiddle.trans (heq_of_eq R.kernelLift_snd)))

/-- At vertex zero, the filtration map from the reversed-left index to the
straight-right index is the stored kernel inclusion, up to endpoint
transport. -/
theorem filtration_map_left_zero_right_zero_heq
    (P : QuillenSimplexSpanPresentation q) (hn : 0 < a.len) :
    HEq
      (P.filtration.chain.map' a.len (a.len + 1) (by omega)
        (by simp only [edgewiseQ_obj_len]; omega))
      (P.tailKernelPresentation (⟨0, hn⟩ : Fin a.len)).ι := by
  let i : Fin (edgewiseQ.obj a).len :=
    ⟨a.len, by simp only [edgewiseQ_obj_len]; omega⟩
  change HEq (P.filtration.chain.map' i.val (i.val + 1) (by omega) (by omega)) _
  rw [P.filtration_chain_map_succ i]
  unfold filtrationStep
  dsimp only [i]
  split
  · omega
  · split
    · omega
    · split
      · with_unfolding_all
          change HEq (eqToHom _ ≫
            (P.tailKernelPresentation (⟨0, hn⟩ : Fin a.len)).ι ≫
              eqToHom _) _
        rw [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      · omega

theorem tailKernelSuccFromNat_heq
    (P : QuillenSimplexSpanPresentation q)
    {k l : ℕ} (h : k = l)
    (hk : k + 1 < a.len) (hl : l + 1 < a.len) :
    HEq (P.tailKernelSuccFromNat k hk)
      (P.tailKernelSuccFromNat l hl) := by
  subst l
  rfl

theorem rightTailSuccFromNat_heq
    (P : QuillenSimplexSpanPresentation q)
    {k l : ℕ} (h : k = l)
    (hk : k < a.len) (hl : l < a.len) :
    HEq (P.rightTailSuccFromNat k hk)
      (P.rightTailSuccFromNat l hl) := by
  subst l
  rfl

theorem filtration_chain_obj_left_nat
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k < a.len) :
    P.filtration.chain.obj' (a.len - k)
        (by simp only [edgewiseQ_obj_len]; omega) =
      (tailKernelPresentationFromNat P k hk).kernel := by
  let k' : Fin a.len := ⟨k, hk⟩
  let i : Fin ((edgewiseQ.obj a).len + 1) :=
    ⟨a.len - k, by simp only [edgewiseQ_obj_len]; omega⟩
  have hi : i = edgewiseLeftIndex a k'.castSucc := by
    apply Fin.ext
    simp [i, k']
  change P.filtration.chain.obj i = _
  rw [hi, P.filtration_chain_obj_left k']
  rfl

theorem filtration_chain_obj_right_nat
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k < a.len) :
    P.filtration.chain.obj' (a.len + 1 + k)
        (by simp only [edgewiseQ_obj_len]; omega) =
      (tailSpanFromNat P k hk).apex := by
  let k' : Fin (a.len + 1) := ⟨k, by omega⟩
  let i : Fin ((edgewiseQ.obj a).len + 1) :=
    ⟨a.len + 1 + k, by simp only [edgewiseQ_obj_len]; omega⟩
  have hi : i = edgewiseRightIndex a k' := by
    apply Fin.ext
    simp [i, k']
    omega
  change P.filtration.chain.obj i = _
  rw [hi, P.filtration_chain_obj_right k', P.rightTailObject_of_lt k hk]

theorem composableArrows_map'_heq
    {D : Type u} [Category.{v} D] {n : ℕ}
    (F : ComposableArrows D n)
    {i i' j j' : ℕ} (hi : i = i') (hj : j = j')
    (hij : i ≤ j) (hjn : j ≤ n)
    (hi'j' : i' ≤ j') (hj'n : j' ≤ n) :
    HEq (F.map' i j hij hjn) (F.map' i' j' hi'j' hj'n) := by
  subst i'
  subst j'
  rfl

theorem admissibleMonoFlag_intervalπ_heq
    {n : ℕ} (F : AdmissibleMonoFlag C n)
    {i i' j j' : Fin (n + 1)} (hi : i = i') (hj : j = j')
    (hij : i ≤ j) (hi'j' : i' ≤ j') :
    HEq (F.intervalπ i j hij) (F.intervalπ i' j' hi'j') := by
  subst i'
  subst j'
  rfl

/-- Successor on the reversed-left block is the kernel-tower successor. -/
theorem filtration_map_left_succ_heq
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) :
    HEq
      (P.filtration.chain.map' (a.len - (k + 1))
        (a.len - (k + 1) + 1) (by omega)
        (by simp only [edgewiseQ_obj_len]; omega))
      (P.tailKernelSuccFromNat k hk) := by
  let i : Fin (edgewiseQ.obj a).len :=
    ⟨a.len - (k + 1), by simp only [edgewiseQ_obj_len]; omega⟩
  change HEq (P.filtration.chain.map' i.val (i.val + 1) (by omega) (by omega)) _
  rw [P.filtration_chain_map_succ i]
  unfold filtrationStep
  dsimp only [i]
  split
  · omega
  · split
    · let m := a.len - (a.len - (k + 1) + 1)
      have hm : m + 1 < a.len := by dsimp only [m]; omega
      have hcalc : m = k := by dsimp only [m]; omega
      with_unfolding_all
        change HEq (eqToHom _ ≫ P.tailKernelSuccFromNat m hm ≫
          eqToHom _) _
      rw [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      exact P.tailKernelSuccFromNat_heq hcalc hm hk
    · omega

/-- Successor on the straight-right block is the tail-apex successor before
the last vertex. -/
theorem filtration_map_right_succ_heq
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) :
    HEq
      (P.filtration.chain.map' (a.len + 1 + k)
        (a.len + 1 + k + 1) (by omega)
        (by simp only [edgewiseQ_obj_len]; omega))
      (P.tailApexSuccFromNat k hk) := by
  let i : Fin (edgewiseQ.obj a).len :=
    ⟨a.len + 1 + k, by simp only [edgewiseQ_obj_len]; omega⟩
  change HEq (P.filtration.chain.map' i.val (i.val + 1) (by omega) (by omega)) _
  rw [P.filtration_chain_map_succ i]
  unfold filtrationStep
  dsimp only [i]
  split
  · omega
  · split
    · omega
    · split
      · omega
      · let m := a.len + 1 + k - (a.len + 1)
        have hm : m < a.len := by dsimp only [m]; omega
        have hcalc : m = k := by dsimp only [m]; omega
        with_unfolding_all
          change HEq (eqToHom _ ≫ P.rightTailSuccFromNat m hm ≫
            eqToHom _) _
        rw [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
        refine (P.rightTailSuccFromNat_heq hcalc hm (by omega)).trans ?_
        unfold rightTailSuccFromNat
        rw [dite_eq_left hk]
        rw [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]

/-- Every successor on the straight-right block is the corresponding
`rightTailSuccFromNat`, including the final right leg. -/
theorem filtration_map_right_succ_general_heq
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k < a.len) :
    HEq
      (P.filtration.chain.map' (a.len + 1 + k)
        (a.len + 1 + k + 1) (by omega)
        (by simp only [edgewiseQ_obj_len]; omega))
      (P.rightTailSuccFromNat k hk) := by
  let i : Fin (edgewiseQ.obj a).len :=
    ⟨a.len + 1 + k, by simp only [edgewiseQ_obj_len]; omega⟩
  change HEq (P.filtration.chain.map' i.val (i.val + 1)
    (by omega) (by omega)) _
  rw [P.filtration_chain_map_succ i]
  unfold filtrationStep
  dsimp only [i]
  split
  · omega
  · split
    · omega
    · split
      · omega
      · let m := a.len + 1 + k - (a.len + 1)
        have hm : m < a.len := by dsimp only [m]; omega
        have hcalc : m = k := by dsimp only [m]; omega
        with_unfolding_all
          change HEq (eqToHom _ ≫ P.rightTailSuccFromNat m hm ≫
            eqToHom _) _
        rw [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
        exact P.rightTailSuccFromNat_heq hcalc hm hk

/-- Every cross map of the filtration is the corresponding tail-kernel
inclusion, up to the literal edgewise endpoint equalities. -/
theorem filtration_map_left_right_heq
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k < a.len) :
    HEq
      (P.filtration.chain.map' (a.len - k) (a.len + 1 + k)
        (by omega) (by simp only [edgewiseQ_obj_len]; omega))
      (tailKernelPresentationFromNat P k hk).ι := by
  induction k with
  | zero =>
      refine (P.filtration_map_left_zero_right_zero_heq hk).trans ?_
      rfl
  | succ k ih =>
      have hk0 : k < a.len := by omega
      have hstep : k + 1 < a.len := hk
      let Ls := a.len - (k + 1)
      let L := a.len - k
      let R := a.len + 1 + k
      let Rs := a.len + 1 + (k + 1)
      have hLs : Ls + 1 = L := by dsimp only [Ls, L]; omega
      have hRs : R + 1 = Rs := by dsimp only [R, Rs]; omega
      have hDecomp :
          P.filtration.chain.map' Ls Rs (by omega)
              (by simp only [edgewiseQ_obj_len]; dsimp only [Rs]; omega) =
            P.filtration.chain.map' Ls L (by omega)
                (by simp only [edgewiseQ_obj_len]; dsimp only [L]; omega) ≫
              P.filtration.chain.map' L R (by omega)
                (by simp only [edgewiseQ_obj_len]; dsimp only [R]; omega) ≫
              P.filtration.chain.map' R Rs (by omega)
                (by simp only [edgewiseQ_obj_len]; dsimp only [Rs]; omega) := by
        rw [P.filtration.chain.map'_comp Ls L Rs (by omega) (by omega)
            (by simp only [edgewiseQ_obj_len]; omega),
          P.filtration.chain.map'_comp L R Rs (by omega) (by omega)
            (by simp only [edgewiseQ_obj_len]; omega)]
      have hLeft : HEq
          (P.filtration.chain.map' Ls L (by omega)
            (by simp only [edgewiseQ_obj_len]; dsimp only [L]; omega))
          (P.tailKernelSuccFromNat k hstep) :=
        (composableArrows_map'_heq P.filtration.chain rfl hLs
          (by omega) (by simp only [edgewiseQ_obj_len]; omega)
          (by omega) (by simp only [edgewiseQ_obj_len]; omega)).symm.trans
            (P.filtration_map_left_succ_heq k hstep)
      have hMid : HEq
          (P.filtration.chain.map' L R (by omega)
            (by simp only [edgewiseQ_obj_len]; dsimp only [R]; omega))
          (tailKernelPresentationFromNat P k hk0).ι := by
        simpa only [L, R] using ih hk0
      have hRight : HEq
          (P.filtration.chain.map' R Rs (by omega)
            (by simp only [edgewiseQ_obj_len]; dsimp only [Rs]; omega))
          (P.tailApexSuccFromNat k hstep) :=
        (composableArrows_map'_heq P.filtration.chain rfl hRs
          (by omega) (by simp only [edgewiseQ_obj_len]; omega)
          (by omega) (by simp only [edgewiseQ_obj_len]; omega)).symm.trans
            (P.filtration_map_right_succ_heq k hstep)
      have eLs := P.filtration_chain_obj_left_nat (k + 1) hstep
      have eL := P.filtration_chain_obj_left_nat k hk0
      have eR := P.filtration_chain_obj_right_nat k hk0
      have eRs := P.filtration_chain_obj_right_nat (k + 1) hstep
      have hMidRight := heq_comp eL eR eRs hMid hRight
      have hTriple := heq_comp eLs eL eRs hLeft hMidRight
      exact (heq_of_eq hDecomp).trans
        (hTriple.trans (heq_of_eq (P.tailKernel_apex_succ k hstep)))

theorem filtration_map_edgewise_left_right_heq
    (P : QuillenSimplexSpanPresentation q) (k : Fin a.len) :
    HEq
      (P.filtration.chain.map
        (homOfLE (show edgewiseLeftIndex a k.castSucc ≤
          edgewiseRightIndex a k.castSucc by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_castSucc]
            omega)))
      (P.tailKernelPresentation k).ι := by
  change HEq
    (P.filtration.chain.map'
      (edgewiseLeftIndex a k.castSucc).val
      (edgewiseRightIndex a k.castSucc).val
      (by simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
        Fin.val_castSucc]; omega)
      (by simp only [edgewiseQ_obj_len, edgewiseRightIndex_val,
        Fin.val_castSucc]; omega)) _
  have hMap := composableArrows_map'_heq P.filtration.chain
    (edgewiseLeftIndex_val a k.castSucc)
    (edgewiseRightIndex_val a k.castSucc)
    (by simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
      Fin.val_castSucc]; omega)
    (by simp only [edgewiseQ_obj_len, edgewiseRightIndex_val,
      Fin.val_castSucc]; omega)
    (by omega) (by simp only [edgewiseQ_obj_len]; omega)
  exact hMap.trans ((P.filtration_map_left_right_heq k.val k.isLt).trans (by rfl))

/-- The filtration segment from `L(k+1)` to `R(k)` is the kernel map used
by the adjacent apex quotient. -/
theorem filtration_map_adjacent_apex_heq
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) :
    HEq
      (P.filtration.chain.map' (a.len - (k + 1)) (a.len + 1 + k)
        (by omega) (by simp only [edgewiseQ_obj_len]; omega))
      (P.tailKernelSuccFromNat k hk ≫
        (tailKernelPresentationFromNat P k (by omega)).ι) := by
  have hk0 : k < a.len := by omega
  let Ls := a.len - (k + 1)
  let L := a.len - k
  let R := a.len + 1 + k
  have hLs : Ls + 1 = L := by dsimp only [Ls, L]; omega
  have hDecomp :
      P.filtration.chain.map' Ls R (by omega)
          (by simp only [edgewiseQ_obj_len]; dsimp only [R]; omega) =
        P.filtration.chain.map' Ls L (by omega)
            (by simp only [edgewiseQ_obj_len]; dsimp only [L]; omega) ≫
          P.filtration.chain.map' L R (by omega)
            (by simp only [edgewiseQ_obj_len]; dsimp only [R]; omega) := by
    rw [P.filtration.chain.map'_comp Ls L R (by omega) (by omega)
      (by simp only [edgewiseQ_obj_len]; omega)]
  have hLeft : HEq
      (P.filtration.chain.map' Ls L (by omega)
        (by simp only [edgewiseQ_obj_len]; dsimp only [L]; omega))
      (P.tailKernelSuccFromNat k hk) :=
    (composableArrows_map'_heq P.filtration.chain rfl hLs
      (by omega) (by simp only [edgewiseQ_obj_len]; omega)
      (by omega) (by simp only [edgewiseQ_obj_len]; omega)).symm.trans
        (P.filtration_map_left_succ_heq k hk)
  have hCross : HEq
      (P.filtration.chain.map' L R (by omega)
        (by simp only [edgewiseQ_obj_len]; dsimp only [R]; omega))
      (tailKernelPresentationFromNat P k hk0).ι := by
    simpa only [L, R] using P.filtration_map_left_right_heq k hk0
  have eLs := P.filtration_chain_obj_left_nat (k + 1) hk
  have eL := P.filtration_chain_obj_left_nat k hk0
  have eR := P.filtration_chain_obj_right_nat k hk0
  exact (heq_of_eq hDecomp).trans (heq_comp eLs eL eR hLeft hCross)

/-- Cross vertex comparison at every nonfinal simplex vertex. -/
noncomputable def filtrationStageVertexIsoCast
    (P : QuillenSimplexSpanPresentation q) (k : Fin a.len) :
    edgewiseStageVertex P.filtrationStage k.castSucc ≅
      (q.obj k.castSucc).obj := by
  let iL := edgewiseLeftIndex a k.castSucc
  let iR := edgewiseRightIndex a k.castSucc
  let hLR : iL ≤ iR := by
    rw [Fin.le_iff_val_le_val]
    simp only [iL, iR, edgewiseLeftIndex_val, edgewiseRightIndex_val,
      Fin.val_castSucc]
    omega
  let Q := P.tailKernelPresentation k
  let hL : P.filtration.chain.obj iL = Q.kernel :=
    P.filtration_chain_obj_left k
  let hR : P.filtration.chain.obj iR =
      (tailSpanFromNat P k.val k.isLt).apex :=
    (P.filtration_chain_obj_right k.castSucc).trans
      (P.rightTailObject_of_lt k.val k.isLt)
  let eL := eqToIso hL
  let eR := eqToIso hR
  let p : P.filtration.chain.obj iR ⟶ (q.obj k.castSucc).obj :=
    eR.hom ≫ (tailSpanFromNat P k.val k.isLt).l
  have hMap : HEq (P.filtration.chain.map (homOfLE hLR)) Q.ι := by
    exact P.filtration_map_edgewise_left_right_heq k
  have hConj : P.filtration.chain.map (homOfLE hLR) =
      eL.hom ≫ Q.ι ≫ eR.inv := by
    change P.filtration.chain.map (homOfLE hLR) =
      eqToHom hL ≫ Q.ι ≫ eqToHom hR.symm
    exact (conj_eqToHom_iff_heq _ _ hL hR).2 hMap
  have w : P.filtration.chain.map (homOfLE hLR) ≫ p = 0 := by
    rw [hConj]
    simp only [p, Category.assoc, Iso.inv_hom_id_assoc, Q.zero, comp_zero]
  let Sflag : ShortComplex C :=
    ShortComplex.mk (P.filtration.chain.map (homOfLE hLR)) p w
  let Stail : ShortComplex C :=
    ShortComplex.mk Q.ι (tailSpanFromNat P k.val k.isLt).l Q.zero
  let eS : Sflag ≅ Stail :=
    ShortComplex.isoMk eL eR (Iso.refl _)
      (by
        dsimp only [Sflag, Stail]
        rw [hConj]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by
        dsimp only [Sflag, Stail, p]
        simp)
  have hExact : IsAdmissibleExact Sflag :=
    isAdmissibleExact_of_iso eS.symm Q.exact
  exact P.admissibleMonoFlag.intervalIsoOfExact hLR p w hExact

theorem filtrationStageVertexIsoCast_hom
    (P : QuillenSimplexSpanPresentation q) (k : Fin a.len) :
    P.admissibleMonoFlag.intervalπ
          (edgewiseLeftIndex a k.castSucc)
          (edgewiseRightIndex a k.castSucc) (by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_castSucc]
            omega) ≫
        (P.filtrationStageVertexIsoCast k).hom =
      eqToHom ((P.filtration_chain_obj_right k.castSucc).trans
        (P.rightTailObject_of_lt k.val k.isLt)) ≫
        (tailSpanFromNat P k.val k.isLt).l := by
  unfold filtrationStageVertexIsoCast
  apply AdmissibleMonoFlag.intervalπ_intervalIsoOfExact_hom

/-- Cross vertex comparison at the last simplex vertex, obtained from the
zero-row isomorphism of quotient completion. -/
noncomputable def filtrationStageVertexIsoLast
    (P : QuillenSimplexSpanPresentation q) :
    edgewiseStageVertex P.filtrationStage (Fin.last a.len) ≅
      (q.obj (Fin.last a.len)).obj := by
  let k := Fin.last a.len
  let iL := edgewiseLeftIndex a k
  let iR := edgewiseRightIndex a k
  let F := P.admissibleMonoFlag
  have hiL : iL = 0 := by
    apply Fin.ext
    simp [iL, k]
  let h0R : (0 : Fin ((edgewiseQ.obj a).len + 1)) ≤ iR :=
    Fin.zero_le iR
  have hCell₀ : edgewiseStageVertex P.filtrationStage k =
      P.filtrationStage.obj.obj (interval 0 iR h0R) := by
    unfold edgewiseStageVertex
    apply congrArg P.filtrationStage.obj.obj
    refine Arrow.ext hiL rfl ?_
    exact Subsingleton.elim _ _
  have hStage : P.filtrationStage.obj.obj (interval 0 iR h0R) =
      F.toStage.obj.obj (interval 0 iR h0R) := by
    rfl
  have hCell : edgewiseStageVertex P.filtrationStage k =
      F.toStage.obj.obj (interval 0 iR h0R) := hCell₀.trans hStage
  have hFR : F.chain.obj iR = P.filtration.chain.obj iR := by
    rfl
  have hRight : F.chain.obj iR = (q.obj (Fin.last a.len)).obj :=
    hFR.trans ((P.filtration_chain_obj_right k).trans
      P.rightTailObject_last)
  exact (eqToIso hCell).trans
    ((F.zeroRowIso iR).symm.trans (eqToIso hRight))

/-- Vertexwise comparison between the extracted Stage simplex and the
retained Quillen simplex. -/
noncomputable def filtrationStageVertexIso
    (P : QuillenSimplexSpanPresentation q)
    (k : Fin (a.len + 1)) :
    edgewiseStageVertex P.filtrationStage k ≅ (q.obj k).obj :=
  Fin.lastCases P.filtrationStageVertexIsoLast
    (fun i ↦ P.filtrationStageVertexIsoCast i) k

theorem filtrationStageVertexIso_last_heq
    (P : QuillenSimplexSpanPresentation q)
    {k : Fin (a.len + 1)} (hk : k = Fin.last a.len) :
    HEq (P.filtrationStageVertexIso k).hom
      (P.filtrationStageVertexIsoLast).hom := by
  subst k
  simp only [filtrationStageVertexIso, Fin.lastCases_last]
  rfl

theorem filtrationStageVertexIso_of_eq_last_hom_heq
    (P : QuillenSimplexSpanPresentation q)
    {k : Fin (a.len + 1)} (hk : k = Fin.last a.len)
    (hD : P.admissibleMonoFlag.chain.obj (edgewiseRightIndex a k) =
      (q.obj k).obj) :
    HEq (P.filtrationStageVertexIso k).hom
      ((P.admissibleMonoFlag.zeroRowIso
        (edgewiseRightIndex a k)).inv ≫ eqToHom hD) := by
  subst k
  simp only [filtrationStageVertexIso, Fin.lastCases_last]
  unfold filtrationStageVertexIsoLast
  dsimp only
  simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom]
  refine (eqToHom_comp_heq _ _).trans ?_
  with_reducible_and_instances rfl

/-- Exact quotient data identifying the filtration segment from `L(k+1)`
to `R(k)` with the apex of the adjacent presented span. -/
structure AdjacentTailQuotientData
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) where
  projection : (tailSpanFromNat P k (by omega)).apex ⟶
    (P.span ⟨k, by omega⟩).apex
  zero :
    (P.tailKernelSuccFromNat k hk ≫
      (tailKernelPresentationFromNat P k (by omega)).ι) ≫ projection = 0
  exact : IsAdmissibleExact
    (ShortComplex.mk
      (P.tailKernelSuccFromNat k hk ≫
        (tailKernelPresentationFromNat P k (by omega)).ι)
      projection zero)
  left_compat : projection ≫ (P.span ⟨k, by omega⟩).l =
    (tailSpanFromNat P k (by omega)).l
  right_compat : projection ≫ (P.span ⟨k, by omega⟩).r =
    P.tailApexSuccFromNat k hk ≫
      (tailSpanFromNat P (k + 1) hk).l

/-- Construct the adjacent apex quotient from the actual tail-composition
pullback and QGRID-A kernel presentation. -/
noncomputable def adjacentTailQuotientData
    (P : QuillenSimplexSpanPresentation q)
    (k : ℕ) (hk : k + 1 < a.len) :
    AdjacentTailQuotientData P k hk := by
  have hk0 : k < a.len := by omega
  let S := P.span ⟨k, hk0⟩
  let T := tailSpanFromNat P (k + 1) hk
  let Qnext := tailKernelPresentationFromNat P (k + 1) hk
  let R := tailCompositeBaseChange S T Qnext
  have hRobj : R.obj = (Span.comp S T).apex := rfl
  have hRhom : eqToHom hRobj = 𝟙 R.obj := by
    with_unfolding_all
      have hh : hRobj =
          (rfl : R.obj = (Span.comp S T).apex) := Subsingleton.elim _ _
      rw [hh]
      rfl
  let Pproj := R.kernelPresentation
  have hSource : Qnext.kernel = Pproj.kernel :=
    R.kernelPresentation_kernel.symm
  have hSpan : tailSpanFromNat P k hk0 = Span.comp S T :=
    P.tailSpanFromNat_step k hk
  let spanIso : Span.comp S T ≅ tailSpanFromNat P k hk0 :=
    (eqToIso hSpan).symm
  let e : (Span.comp S T).apex ≅ (tailSpanFromNat P k hk0).apex :=
    Span.SpanBicat.apexIso
      (X := ⟨(q.obj' k (by omega)).obj⟩)
      (Y := ⟨(q.obj (Fin.last a.len)).obj⟩) spanIso
  have he : e.hom ≫ (tailSpanFromNat P k hk0).l = R.fst ≫ S.l :=
    spanIso.hom.hom_l.trans
      (tailCompositeBaseChange_comp_l S T Qnext)
  let eMid : R.obj ≅ (tailSpanFromNat P k hk0).apex :=
    (eqToIso hRobj).trans e
  let p : (tailSpanFromNat P k hk0).apex ⟶ S.apex :=
    eMid.inv ≫ R.fst
  let g : Qnext.kernel ⟶ (tailSpanFromNat P k hk0).apex :=
    eqToHom hSource ≫ Pproj.ι ≫ eMid.hom
  let hA := congrArg Span.apex hSpan
  let eF : (tailSpanFromNat P k hk0).apex ≅ (Span.comp S T).apex :=
    Span.SpanBicat.apexIso
      (X := ⟨(q.obj' k (by omega)).obj⟩)
      (Y := ⟨(q.obj (Fin.last a.len)).obj⟩) (eqToIso hSpan)
  have hE : e.hom = eF.inv := rfl
  have heHom : e.hom = eqToHom hA.symm :=
    hE.trans (apexIsoOfSpanEq_inv hSpan)
  have hEMid : eMid.hom = eqToHom hRobj ≫ e.hom := rfl
  have hApex : P.tailApexSuccFromNat k hk =
      eqToHom hA ≫ eqToHom hRobj.symm ≫ R.snd := by
    apply eq_of_heq
    have hL : HEq (P.tailApexSuccFromNat k hk) R.snd := by
      unfold tailApexSuccFromNat
      exact eqToHom_comp_heq R.snd _
    have hR : HEq (eqToHom hA ≫ eqToHom hRobj.symm ≫ R.snd)
        R.snd := by
      simp only [eqToHom_comp_heq_iff]
      rfl
    exact hL.trans hR.symm
  have hMidApex : eMid.hom ≫ P.tailApexSuccFromNat k hk = R.snd := by
    rw [hEMid, hApex, heHom]
    simp
  have hgApex : g ≫ P.tailApexSuccFromNat k hk = Qnext.ι := by
    dsimp only [g]
    simp only [Category.assoc]
    rw [hMidApex]
    apply eq_of_heq
    rw [eqToHom_comp_heq_iff]
    rw [R.kernelPresentation_ι]
    exact heq_of_eq R.kernelLift_snd
  have hFirst :
      P.tailKernelSuccFromNat k hk ≫
          (tailKernelPresentationFromNat P k hk0).ι = g := by
    let _ : Mono (P.tailApexSuccFromNat k hk) :=
      (P.tailApexSuccFromNat_admissible k hk).mono
    apply (cancel_mono (P.tailApexSuccFromNat k hk)).1
    rw [Category.assoc, P.tailKernel_apex_succ k hk, hgApex]
  have hp : eMid.hom ≫ p = R.fst := by
    dsimp only [p]
    exact eMid.hom_inv_id_assoc R.fst
  let Qmid := transportKernelPresentationSource Pproj eMid p hp
  have hQmidKernel : Qmid.kernel = Pproj.kernel := rfl
  have hSourceMid : Qnext.kernel = Qmid.kernel :=
    hSource.trans hQmidKernel.symm
  have hFirst' :
      P.tailKernelSuccFromNat k hk ≫
          (tailKernelPresentationFromNat P k hk0).ι =
        eqToHom hSourceMid ≫ Qmid.ι := by
    rw [hFirst]
    apply eq_of_heq
    rw [heq_eqToHom_comp_iff]
    dsimp only [g, Qmid, transportKernelPresentationSource]
    rw [eqToHom_comp_heq_iff]
  let fnew := P.tailKernelSuccFromNat k hk ≫
    (tailKernelPresentationFromNat P k hk0).ι
  have w : fnew ≫ p = 0 := by
    dsimp only [fnew]
    rw [hFirst']
    calc
      (eqToHom hSourceMid ≫ Qmid.ι) ≫ p =
          eqToHom hSourceMid ≫ (Qmid.ι ≫ p) := Category.assoc _ _ _
      _ = 0 := by rw [Qmid.zero, comp_zero]
  let Snew : ShortComplex C := ShortComplex.mk fnew p w
  let Smid : ShortComplex C := ShortComplex.mk Qmid.ι p Qmid.zero
  let eS : Snew ≅ Smid :=
    ShortComplex.isoMk (eqToIso hSourceMid) (Iso.refl _) (Iso.refl _)
      (by
        dsimp only [Snew, Smid]
        rw [Iso.refl_hom, Category.comp_id]
        rw [show (eqToIso hSourceMid).hom = eqToHom hSourceMid from rfl]
        exact hFirst'.symm)
      (by simp [Snew, Smid])
  have heMid : HEq (eMid.hom ≫ (tailSpanFromNat P k hk0).l)
      (R.fst ≫ S.l) := by
    have h1 : HEq eMid.hom e.hom := by
      rw [hEMid]
      exact eqToHom_comp_heq e.hom hRobj
    exact (heq_comp rfl rfl rfl h1 (HEq.rfl)).trans (heq_of_eq he)
  have hLeftCompat : p ≫ S.l = (tailSpanFromNat P k hk0).l := by
    apply (cancel_epi eMid.hom).1
    rw [← Category.assoc, hp]
    exact eq_of_heq heMid.symm
  have hRightCompat : p ≫ S.r =
      P.tailApexSuccFromNat k hk ≫ (tailSpanFromNat P (k + 1) hk).l := by
    apply (cancel_epi eMid.hom).1
    rw [← Category.assoc eMid.hom p S.r, hp,
      ← Category.assoc eMid.hom (P.tailApexSuccFromNat k hk)
        (tailSpanFromNat P (k + 1) hk).l,
      hMidApex]
    exact R.square.w
  exact
    { projection := p
      zero := w
      exact := isAdmissibleExact_of_iso eS.symm Qmid.exact
      left_compat := hLeftCompat
      right_compat := hRightCompat }

/-- Adjacent shell-apex comparison away from the final edge. -/
noncomputable def filtrationStageAdjacentApexIsoOfStep
    (P : QuillenSimplexSpanPresentation q)
    (i : Fin a.len) (hi : i.val + 1 < a.len) :
    P.filtrationStage.obj.obj
        (interval (edgewiseLeftIndex a i.succ)
          (edgewiseRightIndex a i.castSucc) (by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_succ, Fin.val_castSucc]
            omega)) ≅
      (P.span i).apex := by
  let iL := edgewiseLeftIndex a i.succ
  let iR := edgewiseRightIndex a i.castSucc
  let hLR : iL ≤ iR := by
    rw [Fin.le_iff_val_le_val]
    simp only [iL, iR, edgewiseLeftIndex_val, edgewiseRightIndex_val,
      Fin.val_succ, Fin.val_castSucc]
    omega
  let D := P.adjacentTailQuotientData i.val hi
  let inext : Fin a.len := ⟨i.val + 1, hi⟩
  let hL : P.filtration.chain.obj iL =
      (tailKernelPresentationFromNat P (i.val + 1) hi).kernel :=
    P.filtration_chain_obj_left inext
  let hR : P.filtration.chain.obj iR =
      (tailSpanFromNat P i.val i.isLt).apex :=
    (P.filtration_chain_obj_right i.castSucc).trans
      (P.rightTailObject_of_lt i.val i.isLt)
  let eL := eqToIso hL
  let eR := eqToIso hR
  have hMap : HEq (P.filtration.chain.map (homOfLE hLR))
      (P.tailKernelSuccFromNat i.val hi ≫
        (tailKernelPresentationFromNat P i.val i.isLt).ι) := by
    change HEq
      (P.filtration.chain.map'
        (edgewiseLeftIndex a i.succ).val
        (edgewiseRightIndex a i.castSucc).val (by omega)
        (by simp only [edgewiseQ_obj_len, edgewiseRightIndex_val,
          Fin.val_castSucc]; omega)) _
    have hIndex := composableArrows_map'_heq P.filtration.chain
      (edgewiseLeftIndex_val a i.succ)
      (edgewiseRightIndex_val a i.castSucc)
      (by simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
        Fin.val_succ, Fin.val_castSucc]; omega)
      (by simp only [edgewiseQ_obj_len, edgewiseRightIndex_val,
        Fin.val_castSucc]; omega)
      (by omega) (by simp only [edgewiseQ_obj_len]; omega)
    exact hIndex.trans (P.filtration_map_adjacent_apex_heq i.val hi)
  let p : P.filtration.chain.obj iR ⟶ (P.span i).apex :=
    eR.hom ≫ D.projection
  have hConj : P.filtration.chain.map (homOfLE hLR) =
      eL.hom ≫
        (P.tailKernelSuccFromNat i.val hi ≫
          (tailKernelPresentationFromNat P i.val i.isLt).ι) ≫
        eR.inv := by
    change P.filtration.chain.map (homOfLE hLR) =
      eqToHom hL ≫
        (P.tailKernelSuccFromNat i.val hi ≫
          (tailKernelPresentationFromNat P i.val i.isLt).ι) ≫
        eqToHom hR.symm
    exact (conj_eqToHom_iff_heq _ _ hL hR).2 hMap
  have w : P.filtration.chain.map (homOfLE hLR) ≫ p = 0 := by
    rw [hConj]
    simp only [p, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (P.tailKernelSuccFromNat i.val hi)
        (tailKernelPresentationFromNat P i.val i.isLt).ι D.projection,
      D.zero, comp_zero]
  let Sflag : ShortComplex C :=
    ShortComplex.mk (P.filtration.chain.map (homOfLE hLR)) p w
  let Stail : ShortComplex C :=
    ShortComplex.mk
      (P.tailKernelSuccFromNat i.val hi ≫
        (tailKernelPresentationFromNat P i.val i.isLt).ι)
      D.projection D.zero
  let eS : Sflag ≅ Stail :=
    ShortComplex.isoMk eL eR (Iso.refl _)
      (by
        dsimp only [Sflag, Stail]
        rw [hConj]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by simp [Sflag, Stail, p])
  have hExact : IsAdmissibleExact Sflag :=
    isAdmissibleExact_of_iso eS.symm D.exact
  exact P.admissibleMonoFlag.intervalIsoOfExact hLR p w hExact

theorem filtrationStageAdjacentApexIsoOfStep_hom
    (P : QuillenSimplexSpanPresentation q)
    (i : Fin a.len) (hi : i.val + 1 < a.len) :
    P.admissibleMonoFlag.intervalπ
          (edgewiseLeftIndex a i.succ)
          (edgewiseRightIndex a i.castSucc) (by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_succ, Fin.val_castSucc]
            omega) ≫
        (P.filtrationStageAdjacentApexIsoOfStep i hi).hom =
      eqToHom ((P.filtration_chain_obj_right i.castSucc).trans
        (P.rightTailObject_of_lt i.val i.isLt)) ≫
        (P.adjacentTailQuotientData i.val hi).projection := by
  unfold filtrationStageAdjacentApexIsoOfStep
  apply AdmissibleMonoFlag.intervalπ_intervalIsoOfExact_hom

/-- Adjacent shell-apex comparison on the final edge. -/
noncomputable def filtrationStageAdjacentApexIsoLast
    (P : QuillenSimplexSpanPresentation q)
    (i : Fin a.len) (hi : i.val + 1 = a.len) :
    P.filtrationStage.obj.obj
        (interval (edgewiseLeftIndex a i.succ)
          (edgewiseRightIndex a i.castSucc) (by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_succ, Fin.val_castSucc]
            omega)) ≅
      (P.span i).apex := by
  let iL := edgewiseLeftIndex a i.succ
  let iR := edgewiseRightIndex a i.castSucc
  have hiL : iL = 0 := by
    apply Fin.ext
    simp only [iL, edgewiseLeftIndex_val, Fin.val_succ, Fin.val_zero]
    omega
  let h0R : (0 : Fin ((edgewiseQ.obj a).len + 1)) ≤ iR :=
    Fin.zero_le iR
  have hCell : P.filtrationStage.obj.obj
        (interval iL iR (by
          rw [Fin.le_iff_val_le_val]
          simp only [iL, iR, edgewiseLeftIndex_val, edgewiseRightIndex_val,
            Fin.val_succ, Fin.val_castSucc]
          omega)) =
      P.filtrationStage.obj.obj (interval 0 iR h0R) := by
    apply congrArg P.filtrationStage.obj.obj
    refine Arrow.ext hiL rfl ?_
    exact Subsingleton.elim _ _
  have hTailApex : (tailSpanFromNat P i.val i.isLt).apex =
      (P.span i).apex := by
    rw [tailSpanFromNat, dite_eq_left hi]
  have hRight : P.filtration.chain.obj iR = (P.span i).apex :=
    (P.filtration_chain_obj_right i.castSucc).trans
      ((P.rightTailObject_of_lt i.val i.isLt).trans hTailApex)
  exact (eqToIso hCell).trans
    ((P.admissibleMonoFlag.zeroRowIso iR).symm.trans (eqToIso hRight))

/-- Adjacent shell-apex comparison for every generating edge. -/
noncomputable def filtrationStageAdjacentApexIso
    (P : QuillenSimplexSpanPresentation q) (i : Fin a.len) :
    P.filtrationStage.obj.obj
        (interval (edgewiseLeftIndex a i.succ)
          (edgewiseRightIndex a i.castSucc) (by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_succ, Fin.val_castSucc]
            omega)) ≅
      (P.span i).apex := by
  by_cases hi : i.val + 1 < a.len
  · exact P.filtrationStageAdjacentApexIsoOfStep i hi
  · exact P.filtrationStageAdjacentApexIsoLast i (by omega)

/-- The normalized adjacent shell span with both endpoints carried to the
retained Quillen objects, away from the final edge. -/
noncomputable def filtrationStageAdjacentSpanToQOfStep
    (P : QuillenSimplexSpanPresentation q)
    (i : Fin a.len) (hi : i.val + 1 < a.len) :
    QuillenSpan (q.obj i.castSucc).obj
      (q.obj (⟨i.val + 1, by omega⟩ : Fin a.len).castSucc).obj := by
  let j : Fin a.len := ⟨i.val + 1, hi⟩
  let h : i.castSucc ≤ j.castSucc := by
    rw [Fin.le_iff_val_le_val]
    simp only [Fin.val_castSucc, j]
    omega
  let F := P.admissibleMonoFlag
  let A := edgewiseLeftIndex a j.castSucc
  let B := edgewiseLeftIndex a i.castSucc
  let C₀ := edgewiseRightIndex a i.castSucc
  let D₀ := edgewiseRightIndex a j.castSucc
  let hAB : A ≤ B := edgewiseLeftIndex_anti h
  let hBC : B ≤ C₀ := by
    rw [Fin.le_iff_val_le_val]
    simp only [B, C₀, edgewiseLeftIndex_val, edgewiseRightIndex_val,
      Fin.val_castSucc]
    omega
  let hAC : A ≤ C₀ := hAB.trans hBC
  let hCD : C₀ ≤ D₀ := edgewiseRightIndex_mono h
  let hAD : A ≤ D₀ := hAC.trans hCD
  let l := F.intervalMap hAC hBC hAB le_rfl
  let r := F.intervalMap hAC hAD le_rfl hCD
  let eX : F.intervalQuotient B C₀ hBC ≅ (q.obj i.castSucc).obj := by
    with_unfolding_all exact P.filtrationStageVertexIsoCast i
  let eY : F.intervalQuotient A D₀ hAD ≅ (q.obj j.castSucc).obj := by
    with_unfolding_all exact P.filtrationStageVertexIsoCast j
  have hl : IsAdmissibleEpi l :=
    isAdmissibleEpi_g (F.interval_triple_exact hAB hBC)
  have hr : IsAdmissibleMono r :=
    isAdmissibleMono_f (F.interval_triple_exact hAC hCD)
  exact
    { apex := F.intervalQuotient A C₀ hAC
      l := l ≫ eX.hom
      r := r ≫ eY.hom
      wl := admissibleEpi_comp.comp_mem _ _ hl
        (IsAdmissibleEpi.of_isIso eX.hom)
      wr := admissibleMono_comp.comp_mem _ _ hr
        (IsAdmissibleMono.of_isIso eY.hom) }

/-- The adjacent normalized shell span is isomorphic to the stored adjacent
representative. -/
noncomputable def filtrationStageAdjacentSpanIsoOfStep
    (P : QuillenSimplexSpanPresentation q)
    (i : Fin a.len) (hi : i.val + 1 < a.len) :
    P.filtrationStageAdjacentSpanToQOfStep i hi ≅ P.span i := by
  let j : Fin a.len := ⟨i.val + 1, hi⟩
  let hAC : edgewiseLeftIndex a j.castSucc ≤
      edgewiseRightIndex a i.castSucc := by
    rw [Fin.le_iff_val_le_val]
    simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
      Fin.val_castSucc, j]
    omega
  let F := P.admissibleMonoFlag
  let A := edgewiseLeftIndex a j.castSucc
  let B := edgewiseLeftIndex a i.castSucc
  let C₀ := edgewiseRightIndex a i.castSucc
  let D₀ := edgewiseRightIndex a j.castSucc
  let hBC : B ≤ C₀ := by
    rw [Fin.le_iff_val_le_val]
    simp only [B, C₀, edgewiseLeftIndex_val, edgewiseRightIndex_val,
      Fin.val_castSucc]
    omega
  let hAD : A ≤ D₀ := by
    rw [Fin.le_iff_val_le_val]
    simp only [A, D₀, edgewiseLeftIndex_val, edgewiseRightIndex_val,
      Fin.val_castSucc]
    omega
  let hAB : A ≤ B := edgewiseLeftIndex_anti (show i.castSucc ≤ j.castSucc by
    rw [Fin.le_iff_val_le_val]
    simp only [Fin.val_castSucc, j]
    omega)
  let hCD : C₀ ≤ D₀ := edgewiseRightIndex_mono (show i.castSucc ≤ j.castSucc by
    rw [Fin.le_iff_val_le_val]
    simp only [Fin.val_castSucc, j]
    omega)
  let π := F.intervalπ A C₀ hAC
  let πN := π
  have hπ : IsAdmissibleEpi π :=
    isAdmissibleEpi_g (F.interval_exact A C₀ hAC)
  have hπN : IsAdmissibleEpi πN := hπ
  let hC₀ : P.filtration.chain.obj C₀ =
      (tailSpanFromNat P i.val i.isLt).apex :=
    (P.filtration_chain_obj_right i.castSucc).trans
      (P.rightTailObject_of_lt i.val i.isLt)
  have hFC : F.chain.obj C₀ = P.filtration.chain.obj C₀ := by
    rfl
  let hC : F.chain.obj C₀ =
      (tailSpanFromNat P i.val i.isLt).apex := hFC.trans hC₀
  let QD := P.adjacentTailQuotientData i.val hi
  let eX : F.intervalQuotient B C₀ hBC ≅ (q.obj i.castSucc).obj := by
    with_unfolding_all exact P.filtrationStageVertexIsoCast i
  have hVX : F.intervalπ B C₀ hBC ≫ eX.hom =
      eqToHom hC ≫ (tailSpanFromNat P i.val i.isLt).l := by
    apply eq_of_heq
    exact heq_of_eq (P.filtrationStageVertexIsoCast_hom i)
  let hD₀ : P.filtration.chain.obj D₀ =
      (tailSpanFromNat P (i.val + 1) hi).apex :=
    (P.filtration_chain_obj_right j.castSucc).trans
      (P.rightTailObject_of_lt (i.val + 1) hi)
  have hFD : F.chain.obj D₀ = P.filtration.chain.obj D₀ := by
    rfl
  let hD : F.chain.obj D₀ =
      (tailSpanFromNat P (i.val + 1) hi).apex := hFD.trans hD₀
  let eY : F.intervalQuotient A D₀ hAD ≅ (q.obj j.castSucc).obj := by
    with_unfolding_all exact P.filtrationStageVertexIsoCast j
  have hVY : F.intervalπ A D₀ hAD ≫ eY.hom =
      eqToHom hD ≫ (tailSpanFromNat P (i.val + 1) hi).l := by
    apply eq_of_heq
    exact heq_of_eq (P.filtrationStageVertexIsoCast_hom j)
  have hStep : HEq (F.chain.map (homOfLE hCD))
      (P.tailApexSuccFromNat i.val hi) := by
    change HEq (P.filtration.chain.map' C₀.val D₀.val (by omega)
      (by simp only [edgewiseQ_obj_len, D₀, edgewiseRightIndex_val,
        Fin.val_castSucc, j]; omega)) _
    have hIndex := composableArrows_map'_heq P.filtration.chain
      (edgewiseRightIndex_val a i.castSucc)
      (edgewiseRightIndex_val a j.castSucc)
      (by simp only [edgewiseRightIndex_val, Fin.val_castSucc, j]; omega)
      (by simp only [edgewiseQ_obj_len, edgewiseRightIndex_val,
        Fin.val_castSucc, j]; omega)
      (by omega : a.len + 1 + i.val ≤ a.len + 1 + i.val + 1)
      (by simp only [edgewiseQ_obj_len]; omega)
    exact hIndex.trans (P.filtration_map_right_succ_heq i.val hi)
  let inext : Fin a.len := ⟨i.val + 1, hi⟩
  let hL₀ : P.filtration.chain.obj A =
      (tailKernelPresentationFromNat P (i.val + 1) hi).kernel :=
    P.filtration_chain_obj_left inext
  have hFA : F.chain.obj A = P.filtration.chain.obj A := by
    rfl
  let hL : F.chain.obj A =
      (tailKernelPresentationFromNat P (i.val + 1) hi).kernel := hFA.trans hL₀
  have hMap : HEq (F.chain.map (homOfLE hAC))
      (P.tailKernelSuccFromNat i.val hi ≫
        (tailKernelPresentationFromNat P i.val i.isLt).ι) := by
    change HEq
      (P.filtration.chain.map' A.val C₀.val (by omega)
        (by simp only [edgewiseQ_obj_len, C₀, edgewiseRightIndex_val,
          Fin.val_castSucc]; omega)) _
    have hIndex := composableArrows_map'_heq P.filtration.chain
      (edgewiseLeftIndex_val a j.castSucc)
      (edgewiseRightIndex_val a i.castSucc)
      (by simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
        Fin.val_castSucc, j]; omega)
      (by simp only [edgewiseQ_obj_len, edgewiseRightIndex_val,
        Fin.val_castSucc]; omega)
      (by omega) (by simp only [edgewiseQ_obj_len]; omega)
    exact hIndex.trans (P.filtration_map_adjacent_apex_heq i.val hi)
  let eL := eqToIso hL
  let eC := eqToIso hC
  let pA : F.chain.obj C₀ ⟶ (P.span i).apex :=
    eC.hom ≫ QD.projection
  have hConj : F.chain.map (homOfLE hAC) =
      eL.hom ≫
        (P.tailKernelSuccFromNat i.val hi ≫
          (tailKernelPresentationFromNat P i.val i.isLt).ι) ≫
        eC.inv := by
    change F.chain.map (homOfLE hAC) =
      eqToHom hL ≫
        (P.tailKernelSuccFromNat i.val hi ≫
          (tailKernelPresentationFromNat P i.val i.isLt).ι) ≫
        eqToHom hC.symm
    exact (conj_eqToHom_iff_heq _ _ hL hC).2 hMap
  have wA : F.chain.map (homOfLE hAC) ≫ pA = 0 := by
    rw [hConj]
    dsimp only [eC, pA]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (P.tailKernelSuccFromNat i.val hi)
        (tailKernelPresentationFromNat P i.val i.isLt).ι QD.projection,
      QD.zero, comp_zero]
  let SA : ShortComplex C :=
    ShortComplex.mk (F.chain.map (homOfLE hAC)) pA wA
  let SD : ShortComplex C :=
    ShortComplex.mk
      (P.tailKernelSuccFromNat i.val hi ≫
        (tailKernelPresentationFromNat P i.val i.isLt).ι)
      QD.projection QD.zero
  let eS : SA ≅ SD :=
    ShortComplex.isoMk eL eC (Iso.refl _)
      (by
        dsimp only [SA, SD]
        rw [hConj]
        dsimp only [eL, eC]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by
        dsimp only [SA, SD, pA, eC]
        simp)
  have hExactA : IsAdmissibleExact SA :=
    isAdmissibleExact_of_iso eS.symm QD.exact
  let eA := F.intervalIsoOfExact hAC pA wA hExactA
  have hAcomp : πN ≫ eA.hom = eqToHom hC ≫ QD.projection := by
    exact F.intervalπ_intervalIsoOfExact_hom hAC pA wA hExactA
  have hSpanApex : (P.filtrationStageAdjacentSpanToQOfStep i hi).apex =
      F.intervalQuotient A C₀ hAC := rfl
  let eAT : (P.filtrationStageAdjacentSpanToQOfStep i hi).apex ≅
      (P.span i).apex := (eqToIso hSpanApex).trans eA
  let πT := πN ≫ (eqToIso hSpanApex).inv
  have hπT : IsAdmissibleEpi πT :=
    admissibleEpi_comp.comp_mem _ _ hπN (IsAdmissibleEpi.of_isIso _)
  have hAcompT : πT ≫ eAT.hom = eqToHom hC ≫ QD.projection := by
    dsimp only [πT, eAT]
    simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
    exact hAcomp
  refine Span.mkIso eAT ?_ ?_
  · let _ : Epi πT := hπT.epi
    apply (cancel_epi πT).1
    have hNat :
        F.intervalπ A C₀ hAC ≫
            F.intervalMap hAC hBC hAB le_rfl =
          F.chain.map (homOfLE (le_rfl : C₀ ≤ C₀)) ≫
            F.intervalπ B C₀ hBC :=
      F.intervalπ_naturality hAC hBC hAB le_rfl
    have hLeftBase : πN ≫
          (F.intervalMap hAC hBC hAB le_rfl ≫ eX.hom) =
        eqToHom hC ≫ (tailSpanFromNat P i.val i.isLt).l := by
      dsimp only [πN, π]
      rw [← Category.assoc, hNat, Category.assoc, hVX]
      rw [Subsingleton.elim (homOfLE _) (𝟙 C₀), F.chain.map_id]
      with_reducible_and_instances
        simp only [Category.id_comp]
    have hSpanL : (P.filtrationStageAdjacentSpanToQOfStep i hi).l =
        F.intervalMap hAC hBC hAB le_rfl ≫ eX.hom := by
      with_unfolding_all rfl
    have hSpanLTransport :
        (eqToIso hSpanApex).inv ≫
            (P.filtrationStageAdjacentSpanToQOfStep i hi).l =
          F.intervalMap hAC hBC hAB le_rfl ≫ eX.hom := by
      apply eq_of_heq
      exact (eqToHom_comp_heq
        (P.filtrationStageAdjacentSpanToQOfStep i hi).l
        hSpanApex.symm).trans (heq_of_eq hSpanL)
    have hLeftT : πT ≫ (P.filtrationStageAdjacentSpanToQOfStep i hi).l =
        eqToHom hC ≫ (tailSpanFromNat P i.val i.isLt).l := by
      dsimp only [πT]
      rw [Category.assoc, hSpanLTransport]
      exact hLeftBase
    rw [← Category.assoc, hAcompT]
    have hCompat : QD.projection ≫ (P.span i).l =
        (tailSpanFromNat P i.val i.isLt).l := by
      apply eq_of_heq
      exact heq_of_eq QD.left_compat
    apply eq_of_heq
    exact (heq_of_eq (Category.assoc _ _ _)).trans
      ((heq_of_eq (congrArg (fun z ↦ eqToHom hC ≫ z) hCompat)).trans
        (heq_of_eq hLeftT.symm))
  · let _ : Epi πT := hπT.epi
    apply (cancel_epi πT).1
    have hNat :
        F.intervalπ A C₀ hAC ≫
            F.intervalMap hAC hAD le_rfl hCD =
          F.chain.map (homOfLE hCD) ≫ F.intervalπ A D₀ hAD :=
      F.intervalπ_naturality hAC hAD le_rfl hCD
    have hRightBase : πN ≫
          (F.intervalMap hAC hAD le_rfl hCD ≫ eY.hom) =
        eqToHom hC ≫
          (P.tailApexSuccFromNat i.val hi ≫
            (tailSpanFromNat P (i.val + 1) hi).l) := by
      dsimp only [πN, π]
      rw [← Category.assoc, hNat, Category.assoc, hVY]
      apply eq_of_heq
      have hChain : HEq
          (F.chain.map (homOfLE hCD) ≫
            (eqToHom hD ≫ (tailSpanFromNat P (i.val + 1) hi).l))
          (P.tailApexSuccFromNat i.val hi ≫
            (tailSpanFromNat P (i.val + 1) hi).l) :=
        heq_comp hC hD rfl hStep
          (eqToHom_comp_heq (tailSpanFromNat P (i.val + 1) hi).l hD)
      exact hChain.trans
        (eqToHom_comp_heq
          (P.tailApexSuccFromNat i.val hi ≫
            (tailSpanFromNat P (i.val + 1) hi).l) hC).symm
    have hSpanR : (P.filtrationStageAdjacentSpanToQOfStep i hi).r =
        F.intervalMap hAC hAD le_rfl hCD ≫ eY.hom := by
      with_unfolding_all rfl
    have hSpanRTransport :
        (eqToIso hSpanApex).inv ≫
            (P.filtrationStageAdjacentSpanToQOfStep i hi).r =
          F.intervalMap hAC hAD le_rfl hCD ≫ eY.hom := by
      apply eq_of_heq
      exact (eqToHom_comp_heq
        (P.filtrationStageAdjacentSpanToQOfStep i hi).r
        hSpanApex.symm).trans (heq_of_eq hSpanR)
    have hRightT : πT ≫ (P.filtrationStageAdjacentSpanToQOfStep i hi).r =
        eqToHom hC ≫
          (P.tailApexSuccFromNat i.val hi ≫
            (tailSpanFromNat P (i.val + 1) hi).l) := by
      dsimp only [πT]
      rw [Category.assoc, hSpanRTransport]
      exact hRightBase
    rw [← Category.assoc, hAcompT]
    have hCompat : QD.projection ≫ (P.span i).r =
        P.tailApexSuccFromNat i.val hi ≫
          (tailSpanFromNat P (i.val + 1) hi).l := by
      apply eq_of_heq
      exact heq_of_eq QD.right_compat
    apply eq_of_heq
    exact (heq_of_eq (Category.assoc _ _ _)).trans
      ((heq_of_eq (congrArg (fun z ↦ eqToHom hC ≫ z) hCompat)).trans
        (heq_of_eq hRightT.symm))

/-- The endpoint-normalized shell span of the completed filtration, with its
two endpoints carried by the vertex comparisons to the retained simplex. -/
noncomputable def filtrationStageShellSpanToQ
    (P : QuillenSimplexSpanPresentation q)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenSpan (q.obj k).obj (q.obj l).obj := by
  let S := edgewiseStageShellSpanNormalized P.filtrationStage k l hkl
  let eX := P.filtrationStageVertexIso k
  let eY := P.filtrationStageVertexIso l
  exact
    { apex := S.apex
      l := S.l ≫ eX.hom
      r := S.r ≫ eY.hom
      wl := admissibleEpi_comp.comp_mem _ _ S.wl
        (IsAdmissibleEpi.of_isIso eX.hom)
      wr := admissibleMono_comp.comp_mem _ _ S.wr
        (IsAdmissibleMono.of_isIso eY.hom) }

/-- Quotient-class formula for the shell span after carrying its two
endpoints to the retained simplex. -/
theorem filtrationStageShellSpanToQ_mkHom
    (P : QuillenSimplexSpanPresentation q)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenQ.mkHom (P.filtrationStageShellSpanToQ k l hkl) =
      (QuillenQ.underlyingIso (P.filtrationStageVertexIso k)).inv ≫
        edgewiseStageShellClassNormalized P.filtrationStage k l hkl ≫
          (QuillenQ.underlyingIso
            (P.filtrationStageVertexIso l)).hom := by
  let S := edgewiseStageShellSpanNormalized P.filtrationStage k l hkl
  let T := P.filtrationStageShellSpanToQ k l hkl
  let eX := P.filtrationStageVertexIso k
  let eY := P.filtrationStageVertexIso l
  have h := QuillenQ.mkHom_naturality_of_span_iso S T eX eY
    (Iso.refl S.apex)
    (by simp [S, T, eX, filtrationStageShellSpanToQ])
    (by simp [S, T, eY, filtrationStageShellSpanToQ])
  change QuillenQ.mkHom T =
    (QuillenQ.underlyingIso eX).inv ≫
      edgewiseStageShellClassNormalized P.filtrationStage k l hkl ≫
        (QuillenQ.underlyingIso eY).hom
  apply (cancel_epi (QuillenQ.underlyingIso eX).hom).1
  simp only [Iso.hom_inv_id_assoc]
  have hS : QuillenQ.mkHom S =
      edgewiseStageShellClassNormalized P.filtrationStage k l hkl :=
    edgewiseStageShellSpanNormalized_mkHom _ _ _ _
  exact h.symm.trans
    (congrArg (fun z ↦ z ≫ (QuillenQ.underlyingIso eY).hom) hS)

/-- The left leg of an adjacent completed shell is the canonical interval
map, followed by the retained-source vertex comparison. -/
theorem filtrationStageShellSpanToQ_adjacent_l_heq
    (P : QuillenSimplexSpanPresentation q) (i : Fin a.len) :
    HEq
      (P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i)).l
      (P.admissibleMonoFlag.intervalMap
        (show edgewiseLeftIndex a i.succ ≤
          edgewiseRightIndex a i.castSucc by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_succ, Fin.val_castSucc]
            omega)
        (edgewiseStageVertex_le a i.castSucc)
        (edgewiseLeftIndex_anti (Fin.castSucc_le_succ i)) le_rfl ≫
          (P.filtrationStageVertexIso i.castSucc).hom) := by
  let N := edgewiseStageShellSpanNormalized P.filtrationStage
    i.castSucc i.succ (Fin.castSucc_le_succ i)
  let R := edgewiseStageShellPacket P.filtrationStage
    i.castSucc i.succ (Fin.castSucc_le_succ i)
  let eV := P.filtrationStageVertexIso i.castSucc
  have hGeneral : HEq
      (P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i)).l (N.l ≫ eV.hom) := by
    rfl
  have hNorm : HEq N.l R.span.l := by
    rw [show N.l = R.span.l ≫
        (eqToIso (edgewiseStageShellSourceEqVertex
          P.filtrationStage i.castSucc i.succ
            (Fin.castSucc_le_succ i))).hom by
      exact edgewiseStageShellSpanNormalized_l _ _ _ _]
    change HEq (R.span.l ≫ eqToHom
      (edgewiseStageShellSourceEqVertex P.filtrationStage
        i.castSucc i.succ (Fin.castSucc_le_succ i))) R.span.l
    exact comp_eqToHom_heq _ _
  have hRaw : HEq R.span.l
      (P.admissibleMonoFlag.intervalMap
        (show edgewiseLeftIndex a i.succ ≤
          edgewiseRightIndex a i.castSucc by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_succ, Fin.val_castSucc]
            omega)
        (edgewiseStageVertex_le a i.castSucc)
        (edgewiseLeftIndex_anti (Fin.castSucc_le_succ i)) le_rfl) := by
    with_unfolding_all rfl
  have hComposed : HEq (N.l ≫ eV.hom)
      (P.admissibleMonoFlag.intervalMap
        (show edgewiseLeftIndex a i.succ ≤
          edgewiseRightIndex a i.castSucc by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_succ, Fin.val_castSucc]
            omega)
        (edgewiseStageVertex_le a i.castSucc)
        (edgewiseLeftIndex_anti (Fin.castSucc_le_succ i)) le_rfl ≫
          eV.hom) := by
    with_unfolding_all
      exact heq_comp rfl rfl rfl (hNorm.trans hRaw) (HEq.rfl)
  exact hGeneral.trans hComposed

/-- The right leg of an adjacent completed shell is the canonical interval
map, followed by the retained-target vertex comparison. -/
theorem filtrationStageShellSpanToQ_adjacent_r_heq
    (P : QuillenSimplexSpanPresentation q) (i : Fin a.len) :
    HEq
      (P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i)).r
      (P.admissibleMonoFlag.intervalMap
        (show edgewiseLeftIndex a i.succ ≤
          edgewiseRightIndex a i.castSucc by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_succ, Fin.val_castSucc]
            omega)
        (edgewiseStageVertex_le a i.succ) le_rfl
        (edgewiseRightIndex_mono (Fin.castSucc_le_succ i)) ≫
          (P.filtrationStageVertexIso i.succ).hom) := by
  let N := edgewiseStageShellSpanNormalized P.filtrationStage
    i.castSucc i.succ (Fin.castSucc_le_succ i)
  let R := edgewiseStageShellPacket P.filtrationStage
    i.castSucc i.succ (Fin.castSucc_le_succ i)
  let eV := P.filtrationStageVertexIso i.succ
  have hGeneral : HEq
      (P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i)).r (N.r ≫ eV.hom) := by
    rfl
  have hNorm : HEq N.r R.span.r := by
    rw [show N.r = R.span.r ≫
        (eqToIso (edgewiseStageShellTargetEqVertex
          P.filtrationStage i.castSucc i.succ
            (Fin.castSucc_le_succ i))).hom by
      exact edgewiseStageShellSpanNormalized_r _ _ _ _]
    change HEq (R.span.r ≫ eqToHom
      (edgewiseStageShellTargetEqVertex P.filtrationStage
        i.castSucc i.succ (Fin.castSucc_le_succ i))) R.span.r
    exact comp_eqToHom_heq _ _
  have hRaw : HEq R.span.r
      (P.admissibleMonoFlag.intervalMap
        (show edgewiseLeftIndex a i.succ ≤
          edgewiseRightIndex a i.castSucc by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_succ, Fin.val_castSucc]
            omega)
        (edgewiseStageVertex_le a i.succ) le_rfl
        (edgewiseRightIndex_mono (Fin.castSucc_le_succ i))) := by
    with_unfolding_all rfl
  have hComposed : HEq (N.r ≫ eV.hom)
      (P.admissibleMonoFlag.intervalMap
        (show edgewiseLeftIndex a i.succ ≤
          edgewiseRightIndex a i.castSucc by
            rw [Fin.le_iff_val_le_val]
            simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
              Fin.val_succ, Fin.val_castSucc]
            omega)
        (edgewiseStageVertex_le a i.succ) le_rfl
        (edgewiseRightIndex_mono (Fin.castSucc_le_succ i)) ≫ eV.hom) := by
    with_unfolding_all
      exact heq_comp rfl rfl rfl (hNorm.trans hRaw) (HEq.rfl)
  exact hGeneral.trans hComposed

/-- Away from the final edge, the normalized shell carrier is the explicit
interval-quotient carrier used in the six-cell comparison. -/
noncomputable def filtrationStageShellSpanToQIsoOfStep
    (P : QuillenSimplexSpanPresentation q)
    (i : Fin a.len) (hi : i.val + 1 < a.len) :
    P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i) ≅
      P.filtrationStageAdjacentSpanToQOfStep i hi := by
  have hApex :
      (P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i)).apex =
      (P.filtrationStageAdjacentSpanToQOfStep i hi).apex := by
    rfl
  refine Span.mkIso (eqToIso hApex) ?_ ?_
  · apply eq_of_heq
    change HEq (eqToHom hApex ≫
      (P.filtrationStageAdjacentSpanToQOfStep i hi).l) _
    rw [eqToHom_comp_heq_iff]
    let N := edgewiseStageShellSpanNormalized P.filtrationStage
      i.castSucc i.succ (Fin.castSucc_le_succ i)
    let R := edgewiseStageShellPacket P.filtrationStage
      i.castSucc i.succ (Fin.castSucc_le_succ i)
    let eV := P.filtrationStageVertexIso i.castSucc
    let eX := P.filtrationStageVertexIsoCast i
    have hGeneral : HEq
        (P.filtrationStageShellSpanToQ i.castSucc i.succ
          (Fin.castSucc_le_succ i)).l (N.l ≫ eV.hom) := by
      rfl
    have hNorm : HEq N.l R.span.l := by
      rw [show N.l = R.span.l ≫
          (eqToIso (edgewiseStageShellSourceEqVertex
            P.filtrationStage i.castSucc i.succ
              (Fin.castSucc_le_succ i))).hom by
        exact edgewiseStageShellSpanNormalized_l _ _ _ _]
      change HEq (R.span.l ≫ eqToHom
        (edgewiseStageShellSourceEqVertex P.filtrationStage
          i.castSucc i.succ (Fin.castSucc_le_succ i))) R.span.l
      exact comp_eqToHom_heq _ _
    have hRaw : HEq R.span.l
        (P.admissibleMonoFlag.intervalMap
          (show edgewiseLeftIndex a i.succ ≤
            edgewiseRightIndex a i.castSucc by
              rw [Fin.le_iff_val_le_val]
              simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
                Fin.val_succ, Fin.val_castSucc]
              omega)
          (show edgewiseLeftIndex a i.castSucc ≤
            edgewiseRightIndex a i.castSucc by
              exact edgewiseStageVertex_le a i.castSucc)
          (edgewiseLeftIndex_anti (Fin.castSucc_le_succ i)) le_rfl) := by
      with_unfolding_all rfl
    have hVertex : HEq eV.hom eX.hom := by
      dsimp only [eV, eX]
      simp only [filtrationStageVertexIso, Fin.lastCases_castSucc]
      rfl
    have hComposed : HEq (N.l ≫ eV.hom)
        ((P.admissibleMonoFlag.intervalMap
          (show edgewiseLeftIndex a i.succ ≤
            edgewiseRightIndex a i.castSucc by
              rw [Fin.le_iff_val_le_val]
              simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
                Fin.val_succ, Fin.val_castSucc]
              omega)
          (show edgewiseLeftIndex a i.castSucc ≤
            edgewiseRightIndex a i.castSucc by
              exact edgewiseStageVertex_le a i.castSucc)
          (edgewiseLeftIndex_anti (Fin.castSucc_le_succ i)) le_rfl) ≫
            eX.hom) := by
      with_unfolding_all
        exact heq_comp rfl rfl rfl (hNorm.trans hRaw) hVertex
    have hCustom : HEq
        (P.filtrationStageAdjacentSpanToQOfStep i hi).l
        ((P.admissibleMonoFlag.intervalMap
          (show edgewiseLeftIndex a i.succ ≤
            edgewiseRightIndex a i.castSucc by
              rw [Fin.le_iff_val_le_val]
              simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
                Fin.val_succ, Fin.val_castSucc]
              omega)
          (show edgewiseLeftIndex a i.castSucc ≤
            edgewiseRightIndex a i.castSucc by
              exact edgewiseStageVertex_le a i.castSucc)
          (edgewiseLeftIndex_anti (Fin.castSucc_le_succ i)) le_rfl) ≫
            eX.hom) := by
      with_unfolding_all rfl
    exact hCustom.trans (hComposed.symm.trans hGeneral.symm)
  · apply eq_of_heq
    change HEq (eqToHom hApex ≫
      (P.filtrationStageAdjacentSpanToQOfStep i hi).r) _
    rw [eqToHom_comp_heq_iff]
    let N := edgewiseStageShellSpanNormalized P.filtrationStage
      i.castSucc i.succ (Fin.castSucc_le_succ i)
    let R := edgewiseStageShellPacket P.filtrationStage
      i.castSucc i.succ (Fin.castSucc_le_succ i)
    let j : Fin a.len := ⟨i.val + 1, hi⟩
    let eV := P.filtrationStageVertexIso i.succ
    let eY := P.filtrationStageVertexIsoCast j
    have hGeneral : HEq
        (P.filtrationStageShellSpanToQ i.castSucc i.succ
          (Fin.castSucc_le_succ i)).r (N.r ≫ eV.hom) := by
      rfl
    have hNorm : HEq N.r R.span.r := by
      rw [show N.r = R.span.r ≫
          (eqToIso (edgewiseStageShellTargetEqVertex
            P.filtrationStage i.castSucc i.succ
              (Fin.castSucc_le_succ i))).hom by
        exact edgewiseStageShellSpanNormalized_r _ _ _ _]
      change HEq (R.span.r ≫ eqToHom
        (edgewiseStageShellTargetEqVertex P.filtrationStage
          i.castSucc i.succ (Fin.castSucc_le_succ i))) R.span.r
      exact comp_eqToHom_heq _ _
    have hRaw : HEq R.span.r
        (P.admissibleMonoFlag.intervalMap
          (show edgewiseLeftIndex a i.succ ≤
            edgewiseRightIndex a i.castSucc by
              rw [Fin.le_iff_val_le_val]
              simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
                Fin.val_succ, Fin.val_castSucc]
              omega)
          (show edgewiseLeftIndex a i.succ ≤
            edgewiseRightIndex a i.succ by
              exact edgewiseStageVertex_le a i.succ)
          le_rfl (edgewiseRightIndex_mono (Fin.castSucc_le_succ i))) := by
      with_unfolding_all rfl
    have hVertex : HEq eV.hom eY.hom := by
      have hs : i.succ = j.castSucc := by
        apply Fin.ext
        rfl
      dsimp only [eV, eY]
      rw [hs]
      simp only [filtrationStageVertexIso, Fin.lastCases_castSucc]
      rfl
    have hComposed : HEq (N.r ≫ eV.hom)
        ((P.admissibleMonoFlag.intervalMap
          (show edgewiseLeftIndex a i.succ ≤
            edgewiseRightIndex a i.castSucc by
              rw [Fin.le_iff_val_le_val]
              simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
                Fin.val_succ, Fin.val_castSucc]
              omega)
          (show edgewiseLeftIndex a i.succ ≤
            edgewiseRightIndex a i.succ by
              exact edgewiseStageVertex_le a i.succ)
          le_rfl (edgewiseRightIndex_mono (Fin.castSucc_le_succ i))) ≫
            eY.hom) := by
      with_unfolding_all
        exact heq_comp rfl rfl rfl (hNorm.trans hRaw) hVertex
    have hCustom : HEq
        (P.filtrationStageAdjacentSpanToQOfStep i hi).r
        ((P.admissibleMonoFlag.intervalMap
          (show edgewiseLeftIndex a i.succ ≤
            edgewiseRightIndex a i.castSucc by
              rw [Fin.le_iff_val_le_val]
              simp only [edgewiseLeftIndex_val, edgewiseRightIndex_val,
                Fin.val_succ, Fin.val_castSucc]
              omega)
          (show edgewiseLeftIndex a i.succ ≤
            edgewiseRightIndex a i.succ by
              exact edgewiseStageVertex_le a i.succ)
          le_rfl (edgewiseRightIndex_mono (Fin.castSucc_le_succ i))) ≫
            eY.hom) := by
      with_unfolding_all rfl
    exact hCustom.trans (hComposed.symm.trans hGeneral.symm)

/-- The normalized adjacent shell is the stored span away from the final
edge. -/
noncomputable def filtrationStageShellSpanIsoOfStep
    (P : QuillenSimplexSpanPresentation q)
    (i : Fin a.len) (hi : i.val + 1 < a.len) :
    P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i) ≅ P.span i :=
  (P.filtrationStageShellSpanToQIsoOfStep i hi).trans
    (P.filtrationStageAdjacentSpanIsoOfStep i hi)

/-- On the final edge, the zero row of quotient completion identifies the
normalized shell apex with the stored adjacent-span apex. -/
noncomputable def filtrationStageShellSpanIsoLast
    (P : QuillenSimplexSpanPresentation q)
    (i : Fin a.len) (hi : i.val + 1 = a.len) :
    P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i) ≅ P.span i := by
  let T := P.filtrationStageShellSpanToQ i.castSucc i.succ
    (Fin.castSucc_le_succ i)
  let F := P.admissibleMonoFlag
  let A := edgewiseLeftIndex a i.succ
  let B := edgewiseLeftIndex a i.castSucc
  let C₀ := edgewiseRightIndex a i.castSucc
  let D₀ := edgewiseRightIndex a i.succ
  let hAB : A ≤ B := edgewiseLeftIndex_anti (Fin.castSucc_le_succ i)
  let hBC : B ≤ C₀ := edgewiseStageVertex_le a i.castSucc
  let hAC : A ≤ C₀ := hAB.trans hBC
  let hCD : C₀ ≤ D₀ := edgewiseRightIndex_mono
    (Fin.castSucc_le_succ i)
  let hAD : A ≤ D₀ := hAC.trans hCD
  have hA0 : A = 0 := by
    apply Fin.ext
    simp only [A, edgewiseLeftIndex_val, Fin.val_succ, Fin.val_zero]
    omega
  let h0C : (0 : Fin ((edgewiseQ.obj a).len + 1)) ≤ C₀ := Fin.zero_le C₀
  have hApexInterval : T.apex = F.intervalQuotient A C₀ hAC := by
    rfl
  have hInterval0 : F.intervalQuotient A C₀ hAC =
      F.toStage.obj.obj (interval 0 C₀ h0C) := by
    change F.toStage.obj.obj (interval A C₀ hAC) = _
    apply congrArg F.toStage.obj.obj
    refine Arrow.ext hA0 rfl ?_
    exact Subsingleton.elim _ _
  have hApex0 : T.apex =
      F.toStage.obj.obj (interval 0 C₀ h0C) :=
    hApexInterval.trans hInterval0
  have hFC : F.chain.obj C₀ = P.filtration.chain.obj C₀ := by
    rfl
  have hTailApex : (tailSpanFromNat P i.val i.isLt).apex =
      (P.span i).apex := by
    rw [tailSpanFromNat, dite_eq_left hi]
  let hRight : F.chain.obj C₀ = (P.span i).apex :=
    hFC.trans ((P.filtration_chain_obj_right i.castSucc).trans
      ((P.rightTailObject_of_lt i.val i.isLt).trans hTailApex))
  let Z := F.zeroRowIso C₀
  let eAT : T.apex ≅ (P.span i).apex :=
    (eqToIso hApex0).trans (Z.symm.trans (eqToIso hRight))
  let πT : F.chain.obj C₀ ⟶ T.apex :=
    Z.hom ≫ (eqToIso hApex0).inv
  have hπT : πT ≫ eAT.hom = eqToHom hRight := by
    dsimp only [πT, eAT]
    simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
    change Z.hom ≫ Z.inv ≫ eqToHom hRight = eqToHom hRight
    exact Z.hom_inv_id_assoc _
  refine Span.mkIso eAT ?_ ?_
  · let _ : Epi πT := by
      dsimp only [πT]
      infer_instance
    apply (cancel_epi πT).1
    rw [← Category.assoc, hπT]
    have hZ : Z.hom = F.intervalπ 0 C₀ h0C := by
      exact F.zeroRowIso_hom C₀
    have hIndex := admissibleMonoFlag_intervalπ_heq F hA0.symm rfl h0C hAC
    have hPi : HEq πT (F.intervalπ A C₀ hAC) := by
      have hTransport := comp_eqToHom_heq Z.hom hApex0.symm
      exact hTransport.trans ((heq_of_eq hZ).trans hIndex)
    let eX : F.intervalQuotient B C₀ hBC ≅
        (q.obj i.castSucc).obj := by
      with_unfolding_all exact P.filtrationStageVertexIsoCast i
    have hLeg0 := P.filtrationStageShellSpanToQ_adjacent_l_heq i
    have hVertex : HEq (P.filtrationStageVertexIso i.castSucc).hom
        eX.hom := by
      simp only [filtrationStageVertexIso, Fin.lastCases_castSucc]
      with_unfolding_all rfl
    have hLeg : HEq T.l
        (F.intervalMap hAC hBC hAB le_rfl ≫
          eX.hom) :=
      hLeg0.trans (heq_comp (by rfl) (by rfl) rfl (HEq.rfl) hVertex)
    have hComp : HEq (πT ≫ T.l)
        (F.intervalπ A C₀ hAC ≫
          (F.intervalMap hAC hBC hAB le_rfl ≫
            eX.hom)) := by
      exact heq_comp rfl (by rfl) rfl hPi hLeg
    have hC₀ : F.chain.obj C₀ =
        (tailSpanFromNat P i.val i.isLt).apex :=
      hFC.trans ((P.filtration_chain_obj_right i.castSucc).trans
        (P.rightTailObject_of_lt i.val i.isLt))
    have hVX : F.intervalπ B C₀ hBC ≫
          eX.hom =
        eqToHom hC₀ ≫ (tailSpanFromNat P i.val i.isLt).l := by
      apply eq_of_heq
      exact heq_of_eq (P.filtrationStageVertexIsoCast_hom i)
    have hNat := F.intervalπ_naturality hAC hBC hAB le_rfl
    have hBase : F.intervalπ A C₀ hAC ≫
          (F.intervalMap hAC hBC hAB le_rfl ≫
            eX.hom) =
        eqToHom hC₀ ≫ (tailSpanFromNat P i.val i.isLt).l := by
      rw [← Category.assoc, hNat, Category.assoc, hVX]
      rw [Subsingleton.elim (homOfLE _) (𝟙 C₀), F.chain.map_id]
      simp only [Category.id_comp]
    have hFinal : HEq
        (eqToHom hC₀ ≫ (tailSpanFromNat P i.val i.isLt).l)
        (eqToHom hRight ≫ (P.span i).l) := by
      have hTailL : HEq (tailSpanFromNat P i.val i.isLt).l
          (P.span i).l := by
        rw [tailSpanFromNat, dite_eq_left hi]
      exact (eqToHom_comp_heq _ hC₀).trans
        (hTailL.trans
          (eqToHom_comp_heq _ hRight).symm)
    apply eq_of_heq
    exact hFinal.symm.trans
      ((heq_of_eq hBase).symm.trans hComp.symm)
  · let _ : Epi πT := by
      dsimp only [πT]
      infer_instance
    apply (cancel_epi πT).1
    rw [← Category.assoc, hπT]
    have hZ : Z.hom = F.intervalπ 0 C₀ h0C := by
      exact F.zeroRowIso_hom C₀
    have hIndex := admissibleMonoFlag_intervalπ_heq F hA0.symm rfl h0C hAC
    have hPi : HEq πT (F.intervalπ A C₀ hAC) := by
      have hTransport := comp_eqToHom_heq Z.hom hApex0.symm
      exact hTransport.trans ((heq_of_eq hZ).trans hIndex)
    let eY : F.intervalQuotient A D₀ hAD ≅ (q.obj i.succ).obj := by
      with_unfolding_all exact P.filtrationStageVertexIso i.succ
    have hLeg0 := P.filtrationStageShellSpanToQ_adjacent_r_heq i
    have hVertexY : HEq (P.filtrationStageVertexIso i.succ).hom eY.hom := by
      with_unfolding_all rfl
    have hLeg : HEq T.r (F.intervalMap hAC hAD le_rfl hCD ≫ eY.hom) :=
      hLeg0.trans (heq_comp (by rfl) (by rfl) rfl (HEq.rfl) hVertexY)
    have hComp : HEq (πT ≫ T.r)
        (F.intervalπ A C₀ hAC ≫
          (F.intervalMap hAC hAD le_rfl hCD ≫
            eY.hom)) := by
      exact heq_comp rfl (by rfl) rfl hPi hLeg
    have hLast : i.succ = Fin.last a.len := by
      apply Fin.ext
      simpa only [Fin.val_succ, Fin.val_last] using hi
    let hD : F.chain.obj D₀ = (q.obj i.succ).obj := by
      calc
        F.chain.obj D₀ = P.filtration.chain.obj D₀ := rfl
        _ = P.rightTailObject i.succ := P.filtration_chain_obj_right i.succ
        _ = P.rightTailObject (Fin.last a.len) := congrArg P.rightTailObject hLast
        _ = (q.obj (Fin.last a.len)).obj := P.rightTailObject_last
        _ = (q.obj i.succ).obj :=
          congrArg (fun k ↦ (q.obj k).obj) hLast.symm
    have hVY : F.intervalπ A D₀ hAD ≫
          eY.hom = eqToHom hD := by
      apply eq_of_heq
      let ZD := F.zeroRowIso D₀
      have hAD0 : F.intervalQuotient A D₀ hAD =
          F.toStage.obj.obj (interval 0 D₀ (Fin.zero_le _)) := by
        change F.toStage.obj.obj (interval A D₀ hAD) = _
        apply congrArg F.toStage.obj.obj
        refine Arrow.ext hA0 rfl ?_
        exact Subsingleton.elim _ _
      have hZD : HEq (F.intervalπ A D₀ hAD) ZD.hom := by
        have hZD0 : ZD.hom = F.intervalπ 0 D₀ (Fin.zero_le _) :=
          F.zeroRowIso_hom D₀
        exact (admissibleMonoFlag_intervalπ_heq F hA0 rfl hAD
          (Fin.zero_le _)).trans (heq_of_eq hZD0).symm
      have hEY : HEq eY.hom (ZD.inv ≫ eqToHom hD) := by
        have hGeneral := P.filtrationStageVertexIso_of_eq_last_hom_heq
          hLast hD
        exact hVertexY.symm.trans hGeneral
      have hPair := heq_comp rfl hAD0 rfl hZD hEY
      exact hPair.trans (heq_of_eq (ZD.hom_inv_id_assoc _))
    have hMap0 : HEq (F.chain.map (homOfLE hCD))
        (P.rightTailSuccFromNat i.val i.isLt) := by
      change HEq (F.chain.map' C₀.val D₀.val (by omega)
        (by simp only [edgewiseQ_obj_len, D₀, edgewiseRightIndex_val,
          Fin.val_succ]; omega)) _
      have hIndex := composableArrows_map'_heq F.chain
        (edgewiseRightIndex_val a i.castSucc)
        (edgewiseRightIndex_val a i.succ)
        (by simp only [edgewiseRightIndex_val, Fin.val_castSucc,
          Fin.val_succ]; omega)
        (by simp only [edgewiseQ_obj_len, edgewiseRightIndex_val,
          Fin.val_succ]; omega)
        (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
        (by simp only [edgewiseQ_obj_len]; omega)
      exact hIndex.trans
        (P.filtration_map_right_succ_general_heq i.val i.isLt)
    let next : Fin (a.len + 1) := ⟨i.val + 1, by omega⟩
    have hNext : next = i.succ := by
      apply Fin.ext
      rfl
    let hNextObj : (q.obj next).obj = (q.obj i.succ).obj :=
      congrArg (fun k ↦ (q.obj k).obj) hNext
    let rI : (P.span i).apex ⟶ (q.obj i.succ).obj :=
      (P.span i).r ≫ eqToHom hNextObj
    have hSucc : HEq (P.rightTailSuccFromNat i.val i.isLt) rI := by
      unfold rightTailSuccFromNat
      rw [dite_eq_right (by omega : ¬ i.val + 1 < a.len)]
      rw [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      have hTailR : HEq (tailSpanFromNat P i.val i.isLt).r
          (P.span i).r := by
        let i₀ : Fin a.len := ⟨i.val, i.isLt⟩
        have hi₀ : i₀ = i := by
          apply Fin.ext
          rfl
        have hiLast : i₀.succ = Fin.last a.len := by
          apply Fin.ext
          simpa only [i₀, Fin.val_succ, Fin.val_last] using hi
        let hObjLast : (q.obj i₀.succ).obj =
            (q.obj (Fin.last a.len)).obj :=
          congrArg (fun k ↦ (q.obj k).obj) hiLast
        let eLast := eqToIso hObjLast
        let Sfinal : QuillenSpan (q.obj' i.val (by omega)).obj
            (q.obj (Fin.last a.len)).obj :=
          { apex := (P.span i₀).apex
            l := (P.span i₀).l
            r := (P.span i₀).r ≫ eLast.hom
            wl := (P.span i₀).wl
            wr := admissibleMono_comp.comp_mem _ _ (P.span i₀).wr
              (IsAdmissibleMono.of_isIso eLast.hom) }
        have hTail : tailSpanFromNat P i.val i.isLt = Sfinal := by
          rw [tailSpanFromNat]
          split
          · rfl
          · omega
        have hDef : HEq (tailSpanFromNat P i.val i.isLt).r
            ((P.span i₀).r ≫ eqToHom hObjLast) := by
          rw [hTail]
          rfl
        exact hDef.trans
          ((comp_eqToHom_heq (P.span i₀).r hObjLast).trans (by
            subst i₀
            rfl))
      have hRIRaw : HEq rI (P.span i).r := by
        dsimp only [rI]
        exact comp_eqToHom_heq (P.span i).r hNextObj
      exact hTailR.trans hRIRaw.symm
    have hNat := F.intervalπ_naturality hAC hAD le_rfl hCD
    have hCalc : F.intervalπ A C₀ hAC ≫
          (F.intervalMap hAC hAD le_rfl hCD ≫
            eY.hom) =
        F.chain.map (homOfLE hCD) ≫ eqToHom hD := by
      with_reducible_and_instances
        rw [← Category.assoc, hNat, Category.assoc, hVY]
    have hBase : HEq
        (F.intervalπ A C₀ hAC ≫
          (F.intervalMap hAC hAD le_rfl hCD ≫ eY.hom))
        (eqToHom hRight ≫ rI) :=
      (heq_of_eq hCalc).trans
        ((comp_eqToHom_heq (F.chain.map (homOfLE hCD)) hD).trans
          ((hMap0.trans hSucc).trans
            (eqToHom_comp_heq rI hRight).symm))
    have hRIRaw : HEq rI (P.span i).r := by
      dsimp only [rI]
      exact comp_eqToHom_heq _ _
    have hTarget : HEq (eqToHom hRight ≫ rI)
        (eqToHom hRight ≫ (P.span i).r) :=
      heq_comp rfl rfl rfl (HEq.rfl) hRIRaw
    apply eq_of_heq
    exact (hComp.trans (hBase.trans hTarget)).symm

/-- Every adjacent normalized shell is isomorphic to the stored adjacent
representative, with the final edge handled by the zero row. -/
noncomputable def filtrationStageShellSpanIsoAdjacent
    (P : QuillenSimplexSpanPresentation q) (i : Fin a.len) :
    P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i) ≅ P.span i := by
  by_cases hi : i.val + 1 < a.len
  · exact P.filtrationStageShellSpanIsoOfStep i hi
  · exact P.filtrationStageShellSpanIsoLast i (by omega)

/-- The completed filtration realizes every generating arrow of the retained
Quillen simplex. -/
theorem filtrationStageShellSpanToQ_adjacent_mkHom
    (P : QuillenSimplexSpanPresentation q) (i : Fin a.len) :
    QuillenQ.mkHom
        (P.filtrationStageShellSpanToQ i.castSucc i.succ
          (Fin.castSucc_le_succ i)) =
      q.map' i.val (i.val + 1) (by omega) (by omega) :=
  (QuillenQ.mkHom_sound (P.filtrationStageShellSpanIsoAdjacent i)).trans
    (P.class_eq i)

/-- Vertex quotient isomorphisms assemble to an all-interval natural
isomorphism from the simplex extracted from the completed Stage to the
retained simplex. -/
noncomputable def filtrationStageAgreementIso
    (P : QuillenSimplexSpanPresentation q) :
    edgewiseStageQuillenSimplex P.filtrationStage ≅ q :=
  ComposableArrows.isoMk
    (fun k ↦ QuillenQ.underlyingIso (P.filtrationStageVertexIso k))
    (fun k hk ↦ by
      let i : Fin a.len := ⟨k, hk⟩
      let eX := QuillenQ.underlyingIso
        (P.filtrationStageVertexIso i.castSucc)
      let eY := QuillenQ.underlyingIso
        (P.filtrationStageVertexIso i.succ)
      let T := P.filtrationStageShellSpanToQ i.castSucc i.succ
        (Fin.castSucc_le_succ i)
      have hFormula := P.filtrationStageShellSpanToQ_mkHom
        i.castSucc i.succ (Fin.castSucc_le_succ i)
      have hClass := P.filtrationStageShellSpanToQ_adjacent_mkHom i
      have hTransport : eX.inv ≫
          edgewiseStageShellClassNormalized P.filtrationStage
            i.castSucc i.succ (Fin.castSucc_le_succ i) ≫ eY.hom =
        q.map' i.val (i.val + 1) (by omega) (by omega) :=
        hFormula.symm.trans hClass
      change edgewiseStageShellClassNormalized P.filtrationStage
          i.castSucc i.succ (Fin.castSucc_le_succ i) ≫ eY.hom =
        eX.hom ≫ q.map' i.val (i.val + 1) (by omega) (by omega)
      apply (cancel_epi eX.inv).1
      simp only [Iso.inv_hom_id_assoc]
      exact hTransport)

/-- The transported normalized shell has the retained interval class for
every ordered pair of vertices. -/
theorem filtrationStageShellSpanToQ_mkHom_eq_map
    (P : QuillenSimplexSpanPresentation q)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenQ.mkHom (P.filtrationStageShellSpanToQ k l hkl) =
      q.map (homOfLE hkl) := by
  rw [P.filtrationStageShellSpanToQ_mkHom]
  have hNat := (P.filtrationStageAgreementIso).hom.naturality
    (homOfLE hkl)
  change edgewiseStageShellClassNormalized P.filtrationStage k l hkl ≫
      (QuillenQ.underlyingIso (P.filtrationStageVertexIso l)).hom =
    (QuillenQ.underlyingIso (P.filtrationStageVertexIso k)).hom ≫
      q.map (homOfLE hkl) at hNat
  rw [hNat]
  exact (QuillenQ.underlyingIso
    (P.filtrationStageVertexIso k)).inv_hom_id_assoc _

/-- Every normalized completed shell is isomorphic to the fixed
right-associated interval representative.  The result remains
existence-valued, so it exposes no chosen all-interval grid data. -/
theorem filtrationStageShellSpan_iso_intervalSpan_nonempty
    (P : QuillenSimplexSpanPresentation q)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    Nonempty (P.filtrationStageShellSpanToQ k l hkl ≅
      P.intervalSpan k l hkl) := by
  apply QuillenQ.mkHom_eq_iff.mp
  rw [P.filtrationStageShellSpanToQ_mkHom_eq_map,
    P.intervalSpan_mkHom]

/-- Grid-lift packet attached to an explicit adjacent-span presentation.  It
is not a selector from bare Quillen simplices: the presentation remains an
input. -/
noncomputable def filtrationStageGridLift
    (P : QuillenSimplexSpanPresentation q) :
    QuillenStageGridLift C a := by
  let A : StageWeakCategory C (edgewiseQ.obj a).len :=
    ⟨P.filtrationStage⟩
  let X : QuillenStageGridAgreement C a :=
    { left := A
      right := Discrete.mk q
      hom := (P.filtrationStageAgreementIso).hom }
  exact ⟨X, by
    change IsIso (P.filtrationStageAgreementIso).hom
    infer_instance⟩

@[simp]
theorem filtrationStageGridLift_grid
    (P : QuillenSimplexSpanPresentation q) :
    P.filtrationStageGridLift.grid.obj = P.filtrationStage :=
  rfl

@[simp]
theorem filtrationStageGridLift_q
    (P : QuillenSimplexSpanPresentation q) :
    P.filtrationStageGridLift.q = q :=
  rfl

end QuillenSimplexSpanPresentation

/-- Every finite Quillen simplex has a material edgewise Stage-grid lift.
The statement is existence-valued and makes no functorial choice of
presentation or lift. -/
theorem quillenStageGridLift_exists
    {a : SimplexCategory} (q : QuillenQSimplex C a) :
    Nonempty { X : QuillenStageGridLift C a // X.q = q } := by
  obtain ⟨P⟩ := QuillenSimplexSpanPresentation.nonempty q
  exact ⟨⟨P.filtrationStageGridLift, rfl⟩⟩

/-- The projection from material Stage-grid lifts to retained Quillen
simplices is essentially surjective in every finite degree.  This is a
theorem value, not a global instance. -/
theorem quillenStageGridQProjection_essSurj
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    (quillenStageGridQProjection C a).EssSurj := by
  refine ⟨?_⟩
  rintro ⟨q⟩
  obtain ⟨⟨X, hX⟩⟩ := quillenStageGridLift_exists q
  refine ⟨X, ⟨?_⟩⟩
  apply eqToIso
  apply Discrete.ext
  exact hX

end AlgebraicKTheory

end
