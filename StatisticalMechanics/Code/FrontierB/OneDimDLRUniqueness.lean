/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.OneDimFiniteVolumeBridge
import Code.Ising.GibbsSimplexInfinite

open scoped BigOperators
open Finset Matrix
namespace StatMech.FrontierB

def fixedWordProduct {E R : Type*} [CommMonoid R] (A : Matrix E E R)
    {k : ℕ} (p : Fin (k + 1) → E) : R :=
  ∏ i : Fin k, A (p i.castSucc) (p i.succ)

def pathCastEquiv (E : Type*) {m n : ℕ} (h : m = n) :
    (Fin m → E) ≃ (Fin n → E) :=
  Equiv.arrowCongr (finCongr h) (Equiv.refl E)

lemma pathCastEquiv_apply (E : Type*) {m n : ℕ} (h : m = n)
    (q : Fin m → E) (i : Fin n) :
    pathCastEquiv E h q i = q (Fin.cast h.symm i) := by
  rfl

lemma pathCastEquiv_symm_apply (E : Type*) {m n : ℕ} (h : m = n)
    (q : Fin n → E) (i : Fin m) :
    (pathCastEquiv E h).symm q i = q (Fin.cast h i) := by
  subst n
  rfl

lemma openMatrixProduct_pathCast {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a b : E) {m n : ℕ}
    (h : m = n) (q : Fin m → E) :
    openMatrixProduct A a b (pathCastEquiv E h q) = openMatrixProduct A a b q := by
  subst n
  rfl

def pathContainsWord {E : Type*} {m k n : ℕ} (p : Fin (k + 1) → E)
    (q : Fin (m + (n + k) + 1) → E) : Prop :=
  ∀ i : Fin (k + 1), q ⟨m + i.val, by omega⟩ = p i

instance instDecidablePathContainsWord {E : Type*} [DecidableEq E]
    {m k n : ℕ} (p : Fin (k + 1) → E) (q : Fin (m + (n + k) + 1) → E) :
    Decidable (pathContainsWord p q) := by
  unfold pathContainsWord
  infer_instance

def wordHeadSplitEquiv (E : Type*) (m k n : ℕ) :
    E × ((Fin m → E) × (Fin (n + k + 1) → E)) ≃
      (Fin (m + (n + k + 1) + 1) → E) :=
  splitPathEquiv E m (n + k + 1)

lemma wordHeadSplitEquiv_center (E : Type*) (m k n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin (n + k + 1) → E) :
    wordHeadSplitEquiv E m k n (s, (l, r)) ⟨m, by omega⟩ = s := by
  exact splitPathEquiv_center E m (n + k + 1) s l r

lemma wordHeadSplitEquiv_right (E : Type*) (m k n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin (n + k + 1) → E) (i : Fin (n + k + 1)) :
    wordHeadSplitEquiv E m k n (s, (l, r)) ⟨m + 1 + i.val, by omega⟩ = r i := by
  exact splitPathEquiv_right E m (n + k + 1) s l r i

lemma openMatrixProduct_wordHeadSplit {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a s b : E) (m k n : ℕ)
    (l : Fin m → E) (r : Fin (n + k + 1) → E) :
    openMatrixProduct A a b (wordHeadSplitEquiv E m k n (s, (l, r))) =
      openMatrixProduct A a s l * openMatrixProduct A s b r :=
  openMatrixProduct_split_factor A a s b m (n + k + 1) l r

lemma pathContainsWord_succ_split {E : Type*} (m k n : ℕ)
    (p : Fin (k + 2) → E) (s : E) (l : Fin m → E)
    (r : Fin (n + k + 1) → E) :
    pathContainsWord p (wordHeadSplitEquiv E m k n (s, (l, r))) ↔
      s = p 0 ∧ pathContainsWord (m := 0) (n := n) (Fin.tail p)
        ((pathCastEquiv E (by omega : 0 + (n + k) + 1 = n + k + 1)).symm r) := by
  constructor
  · intro hp
    constructor
    · have hi := hp 0
      rw [show (⟨m + (0 : Fin (k + 2)).val, by omega⟩ :
        Fin (m + (n + k + 1) + 1)) = ⟨m, by omega⟩ by apply Fin.ext; simp] at hi
      rw [wordHeadSplitEquiv_center] at hi
      exact hi
    · intro i
      have hi := hp (Fin.succ i)
      rw [show (⟨m + (Fin.succ i).val, by omega⟩ :
        Fin (m + (n + k + 1) + 1)) = ⟨m + 1 + i.val, by omega⟩ by
          apply Fin.ext
          change m + (i.val + 1) = m + 1 + i.val
          omega] at hi
      rw [wordHeadSplitEquiv_right E m k n s l r ⟨i.val, by omega⟩] at hi
      rw [pathCastEquiv_symm_apply E
        (by omega : 0 + (n + k) + 1 = n + k + 1) r]
      rw [show Fin.cast (by omega : 0 + (n + k) + 1 = n + k + 1)
        (⟨0 + i.val, by omega⟩ : Fin (0 + (n + k) + 1)) =
          ⟨i.val, by omega⟩ by apply Fin.ext; simp]
      exact hi
  · rintro ⟨hs, hp⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [show (⟨m + (0 : Fin (k + 2)).val, by omega⟩ :
        Fin (m + (n + k + 1) + 1)) = ⟨m, by omega⟩ by apply Fin.ext; simp]
      rw [wordHeadSplitEquiv_center, hs]
    · have hj := hp j
      rw [show (⟨m + (Fin.succ j).val, by omega⟩ :
        Fin (m + (n + k + 1) + 1)) = ⟨m + 1 + j.val, by omega⟩ by
          apply Fin.ext
          change m + (j.val + 1) = m + 1 + j.val
          omega]
      rw [wordHeadSplitEquiv_right E m k n s l r ⟨j.val, by omega⟩]
      rw [pathCastEquiv_symm_apply E
        (by omega : 0 + (n + k) + 1 = n + k + 1) r] at hj
      rw [show Fin.cast (by omega : 0 + (n + k) + 1 = n + k + 1)
        (⟨0 + j.val, by omega⟩ : Fin (0 + (n + k) + 1)) =
          ⟨j.val, by omega⟩ by apply Fin.ext; simp] at hj
      exact hj

lemma pathContainsWord_zero {E : Type*} (m n : ℕ) (p : Fin 1 → E)
    (q : Fin (m + (n + 0) + 1) → E) :
    pathContainsWord p q ↔ q ⟨m, by omega⟩ = p 0 := by
  constructor
  · intro hp
    exact hp 0
  · intro hp i
    fin_cases i
    exact hp

lemma fixedWordProduct_tail {E R : Type*} [CommMonoid R] (A : Matrix E E R)
    {k : ℕ} (p : Fin (k + 2) → E) :
    fixedWordProduct A p = A (p 0) (p 1) * fixedWordProduct A (Fin.tail p) := by
  unfold fixedWordProduct
  rw [Fin.prod_univ_succ]
  rfl

theorem sum_openMatrixProduct_fixedWord {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a b : E) :
    ∀ (k m n : ℕ) (p : Fin (k + 1) → E),
    (∑ q : Fin (m + (n + k) + 1) → E,
      if pathContainsWord p q then openMatrixProduct A a b q else 0) =
      (A ^ (m + 1)) a (p 0) * fixedWordProduct A p *
        (A ^ (n + 1)) (p (Fin.last k)) b := by
  classical
  intro k
  induction k generalizing a b with
  | zero =>
      intro m n p
      simp_rw [pathContainsWord_zero]
      simpa only [Nat.add_zero, fixedWordProduct, Fin.prod_univ_zero, mul_one,
        Fin.last_zero] using sum_openMatrixProduct_split A a (p 0) b m n
  | succ k ih =>
      intro m n p
      change (∑ q : Fin (m + (n + k + 1) + 1) → E,
        if pathContainsWord p q then openMatrixProduct A a b q else 0) = _
      rw [← Equiv.sum_comp (wordHeadSplitEquiv E m k n)
        (fun q => if pathContainsWord p q then openMatrixProduct A a b q else 0)]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      simp_rw [pathContainsWord_succ_split, openMatrixProduct_wordHeadSplit]
      rw [Finset.sum_eq_single (p 0)]
      · simp only [true_and]
        have hif (l : Fin m → E) (r : Fin (n + k + 1) → E) :
            (if pathContainsWord (m := 0) (n := n) (Fin.tail p)
                ((pathCastEquiv E
                  (by omega : 0 + (n + k) + 1 = n + k + 1)).symm r) then
              openMatrixProduct A a (p 0) l * openMatrixProduct A (p 0) b r else 0) =
            openMatrixProduct A a (p 0) l *
              (if pathContainsWord (m := 0) (n := n) (Fin.tail p)
                  ((pathCastEquiv E
                    (by omega : 0 + (n + k) + 1 = n + k + 1)).symm r) then
                openMatrixProduct A (p 0) b r else 0) := by
          by_cases hpw : pathContainsWord (m := 0) (n := n) (Fin.tail p)
            ((pathCastEquiv E
              (by omega : 0 + (n + k) + 1 = n + k + 1)).symm r) <;> simp [hpw]
        simp_rw [hif]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
        rw [← matrix_pow_apply_eq_sum_open]
        let e : (Fin (0 + (n + k) + 1) → E) ≃ (Fin (n + k + 1) → E) :=
          pathCastEquiv E (by omega)
        have hsum : (∑ r : Fin (n + k + 1) → E,
              if pathContainsWord (m := 0) (n := n) (Fin.tail p) (e.symm r) then
                openMatrixProduct A (p 0) b r else 0) =
            ∑ q : Fin (0 + (n + k) + 1) → E,
              if pathContainsWord (m := 0) (n := n) (Fin.tail p) q then
                openMatrixProduct A (p 0) b q else 0 := by
          rw [← Equiv.sum_comp e]
          apply Finset.sum_congr rfl
          intro q hq
          simp only [Equiv.symm_apply_apply, e]
          rw [openMatrixProduct_pathCast]
        rw [hsum]
        rw [show (∑ q : Fin (0 + (n + k) + 1) → E,
            if pathContainsWord (m := 0) (n := n) (Fin.tail p) q then
              openMatrixProduct A (p 0) b q else 0) =
            (A ^ (0 + 1)) (p 0) ((Fin.tail p) 0) *
              fixedWordProduct A (Fin.tail p) *
                (A ^ (n + 1)) ((Fin.tail p) (Fin.last k)) b by
          exact ih (a := p 0) (b := b) 0 n (Fin.tail p)]
        rw [fixedWordProduct_tail]
        change (A ^ (m + 1)) a (p 0) *
            ((A ^ 1) (p 0) (p 1) * fixedWordProduct A (Fin.tail p) *
              (A ^ (n + 1)) (p (Fin.last (k + 1))) b) = _
        simp only [pow_one]
        ring
      · intro c hc hcp
        simp [hcp]
      · simp



open StatMech.Lattice StatMech.Ising StatMech.FrontierC


def blockStateEvent (r : ℕ) (p : Fin (2 * r + 1) → Fin 2) :
    Set (ConfigSpace (Site 1)) :=
  {sigma | ∀ i, boolTransferState
    (sigma (site1 (-(r : ℤ) + (i.val : ℤ)))) = p i}

instance instDecidableMemBlockStateEvent (r : ℕ) (p : Fin (2 * r + 1) → Fin 2)
    (sigma : ConfigSpace (Site 1)) : Decidable (sigma ∈ blockStateEvent r p) := by
  unfold blockStateEvent
  infer_instance

lemma measurableSet_blockStateEvent (r : ℕ) (p : Fin (2 * r + 1) → Fin 2) :
    MeasurableSet (blockStateEvent r p) := by
  rw [blockStateEvent, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hcoord : Measurable
      (fun sigma : ConfigSpace (Site 1) => sigma (site1 (-(r : ℤ) + (i.val : ℤ)))) :=
    measurable_pi_apply _
  have hstate : Measurable (fun b : Bool => boolTransferState b) :=
    measurable_of_finite _
  exact (hstate.comp hcoord) (measurableSet_singleton (p i))



noncomputable def blockInteriorStateEquiv (r m : ℕ) :
    ({x // x ∈ box 1 (r + m)} → Bool) ≃
      (Fin (m + (m + 2 * r) + 1) → Fin 2) :=
  (interiorStateEquiv (r + m)).trans
    (pathCastEquiv (Fin 2) (by omega))

lemma blockInteriorStateEquiv_apply
    (eta : ConfigSpace (Site 1)) (r m : ℕ)
    (tau : {x // x ∈ box 1 (r + m)} → Bool)
    (i : Fin (2 * r + 1)) :
    blockInteriorStateEquiv r m tau ⟨m + i.val, by omega⟩ =
      boolTransferState
        (glue eta tau (site1 (-(r : ℤ) + (i.val : ℤ)))) := by
  rw [blockInteriorStateEquiv]
  change pathCastEquiv (Fin 2) (by omega)
    (interiorStateEquiv (r + m) tau) ⟨m + i.val, by omega⟩ = _
  rw [pathCastEquiv_apply]
  rw [interiorStateEquiv_apply eta]
  unfold fvPathState
  congr 3
  simp only [Fin.val_cast]
  push_cast
  ring

lemma pathContainsWord_block_iff
    (eta : ConfigSpace (Site 1)) (r m : ℕ)
    (tau : {x // x ∈ box 1 (r + m)} → Bool)
    (p : Fin (2 * r + 1) → Fin 2) :
    pathContainsWord (m := m) (n := m) p (blockInteriorStateEquiv r m tau) ↔
      glue eta tau ∈ blockStateEvent r p := by
  constructor
  · intro hp i
    exact (blockInteriorStateEquiv_apply eta r m tau i).symm.trans (hp i)
  · intro hp i
    exact (blockInteriorStateEquiv_apply eta r m tau i).trans (hp i)

theorem sum_fvTransferProduct_block_eq_matrix_pow
    (eta : ConfigSpace (Site 1)) (r m : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    (∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
      if glue eta tau ∈ blockStateEvent r p then
        fvTransferProduct eta (r + m) tau beta h else 0) =
      (isingTransferReal beta (beta * h) ^ (m + 1))
          (fvLeftBoundaryState eta (r + m)) (p 0) *
        fixedWordProduct (isingTransferReal beta (beta * h)) p *
          (isingTransferReal beta (beta * h) ^ (m + 1))
            (p (Fin.last (2 * r))) (fvRightBoundaryState eta (r + m)) := by
  let A := isingTransferReal beta (beta * h)
  calc
    _ = ∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
        if pathContainsWord (m := m) (n := m) p (blockInteriorStateEquiv r m tau) then
          openMatrixProduct A (fvLeftBoundaryState eta (r + m))
            (fvRightBoundaryState eta (r + m)) (blockInteriorStateEquiv r m tau) else 0 := by
      apply Finset.sum_congr rfl
      intro tau htau
      simp only [pathContainsWord_block_iff eta]
      by_cases hp : glue eta tau ∈ blockStateEvent r p
      · simp only [hp, if_true]
        rw [blockInteriorStateEquiv]
        change fvTransferProduct eta (r + m) tau beta h =
          openMatrixProduct A _ _
            (pathCastEquiv (Fin 2)
              (show 2 * (r + m) + 1 = m + (m + 2 * r) + 1 by omega)
              (interiorStateEquiv (r + m) tau))
        rw [openMatrixProduct_pathCast]
        exact fvTransferProduct_eq_openMatrixProduct eta (r + m) tau beta h
      · simp [hp]
    _ = ∑ q : Fin (m + (m + 2 * r) + 1) → Fin 2,
        if pathContainsWord (m := m) (n := m) p q then
          openMatrixProduct A (fvLeftBoundaryState eta (r + m))
            (fvRightBoundaryState eta (r + m)) q else 0 :=
      by
        simpa only using Equiv.sum_comp (blockInteriorStateEquiv r m)
          (fun q => if pathContainsWord (m := m) (n := m) p q then
            openMatrixProduct A (fvLeftBoundaryState eta (r + m))
              (fvRightBoundaryState eta (r + m)) q else 0)
    _ = _ := sum_openMatrixProduct_fixedWord A
      (fvLeftBoundaryState eta (r + m)) (fvRightBoundaryState eta (r + m))
      (2 * r) m m p

noncomputable def fvBlockStateProb (eta : ConfigSpace (Site 1)) (r m : ℕ)
    (beta h : ℝ) (p : Fin (2 * r + 1) → Fin 2) : ℝ :=
  ∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
    if glue eta tau ∈ blockStateEvent r p then
      fvProb eta (r + m) (bondFinsetTouch 1 (r + m)) beta h tau else 0

theorem sum_fvWeight_block_eq_matrix_pow
    (eta : ConfigSpace (Site 1)) (r m : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    (∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
      if glue eta tau ∈ blockStateEvent r p then
        fvWeight eta (r + m) (bondFinsetTouch 1 (r + m)) beta h tau else 0) =
      fvEndpointFactor eta (r + m) beta h *
        ((isingTransferReal beta (beta * h) ^ (m + 1))
            (fvLeftBoundaryState eta (r + m)) (p 0) *
          fixedWordProduct (isingTransferReal beta (beta * h)) p *
            (isingTransferReal beta (beta * h) ^ (m + 1))
              (p (Fin.last (2 * r))) (fvRightBoundaryState eta (r + m))) := by
  simp_rw [fvWeight_eq_endpointFactor_mul_openProduct]
  have hfactor :
      (∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
        if glue eta tau ∈ blockStateEvent r p then
          fvEndpointFactor eta (r + m) beta h *
            fvTransferProduct eta (r + m) tau beta h else 0) =
        fvEndpointFactor eta (r + m) beta h *
          ∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
            if glue eta tau ∈ blockStateEvent r p then
              fvTransferProduct eta (r + m) tau beta h else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau htau
    by_cases hp : glue eta tau ∈ blockStateEvent r p <;> simp [hp]
  rw [hfactor, sum_fvTransferProduct_block_eq_matrix_pow]

theorem fvBlockStateProb_eq_matrix_ratio
    (eta : ConfigSpace (Site 1)) (r m : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    fvBlockStateProb eta r m beta h p =
      ((isingTransferReal beta (beta * h) ^ (m + 1))
          (fvLeftBoundaryState eta (r + m)) (p 0) *
        fixedWordProduct (isingTransferReal beta (beta * h)) p *
          (isingTransferReal beta (beta * h) ^ (m + 1))
            (p (Fin.last (2 * r))) (fvRightBoundaryState eta (r + m))) /
      (isingTransferReal beta (beta * h) ^ (2 * (r + m) + 2))
        (fvLeftBoundaryState eta (r + m))
        (fvRightBoundaryState eta (r + m)) := by
  unfold fvBlockStateProb fvProb
  have hdiv :
      (∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
        if glue eta tau ∈ blockStateEvent r p then
          fvWeight eta (r + m) (bondFinsetTouch 1 (r + m)) beta h tau /
            fvZ eta (r + m) (bondFinsetTouch 1 (r + m)) beta h else 0) =
        (∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
          if glue eta tau ∈ blockStateEvent r p then
            fvWeight eta (r + m) (bondFinsetTouch 1 (r + m)) beta h tau else 0) /
          fvZ eta (r + m) (bondFinsetTouch 1 (r + m)) beta h := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro tau htau
    by_cases hp : glue eta tau ∈ blockStateEvent r p <;> simp [hp]
  rw [hdiv, sum_fvWeight_block_eq_matrix_pow,
    fvZ_eq_endpointFactor_mul_matrix_pow]
  apply mul_div_mul_left
  exact (Real.exp_pos _).ne'

theorem fvMeasure_blockStateEvent_real
    (eta : ConfigSpace (Site 1)) (r m : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    (fvMeasure eta (r + m) (bondFinsetTouch 1 (r + m)) beta h).real
        (blockStateEvent r p) = fvBlockStateProb eta r m beta h p := by
  rw [fvMeasure_real_eq eta (r + m) (bondFinsetTouch 1 (r + m)) beta h
    (measurableSet_blockStateEvent r p)]
  unfold fvBlockStateProb
  apply Finset.sum_congr rfl
  intro tau htau
  by_cases hp : glue eta tau ∈ blockStateEvent r p
  · rw [if_pos hp]
    simp [Set.indicator_of_mem hp]
  · rw [if_neg hp]
    simp [Set.indicator_of_notMem hp]





lemma isingTransferProjectorPlus_cross_general (beta h : ℝ) (a c d b : Fin 2) :
    isingTransferProjectorPlus beta h a c *
        isingTransferProjectorPlus beta h d b =
      isingTransferProjectorPlus beta h a b *
        isingTransferProjectorPlus beta h d c := by
  have hd := isingTransferProjectorPlus_det beta h
  rw [Matrix.det_fin_two] at hd
  fin_cases a <;> fin_cases c <;> fin_cases d <;> fin_cases b <;>
    simp_all <;> ring_nf at * <;> nlinarith

theorem isingTransfer_fixedWord_weight_tendsto
    (beta h : ℝ) (k : ℕ) (p : Fin (k + 1) → Fin 2) (a b : Fin 2) :
    Filter.Tendsto
      (fun m : ℕ =>
        (isingTransferReal beta h ^ (m + 1)) a (p 0) *
          fixedWordProduct (isingTransferReal beta h) p *
            (isingTransferReal beta h ^ (m + 1)) (p (Fin.last k)) b /
          (isingTransferReal beta h ^ (2 * (m + 1) + k)) a b)
      Filter.atTop
      (nhds (isingTransferProjectorPlus beta h (p (Fin.last k)) (p 0) *
        fixedWordProduct (isingTransferReal beta h) p *
          (isingTransferEigenPlus beta h)⁻¹ ^ k)) := by
  let c : ℝ := (isingTransferEigenPlus beta h)⁻¹
  let A := isingTransferReal beta h
  let P := isingTransferProjectorPlus beta h
  let W := fixedWordProduct A p
  have hc : c ≠ 0 := inv_ne_zero (isingTransfer_eigenPlus_pos beta h).ne'
  have hshift : Filter.Tendsto (fun m : ℕ => m + 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    omega
  have hdenShift : Filter.Tendsto (fun m : ℕ => 2 * (m + 1) + k)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    omega
  have hleft := (isingTransfer_normalized_entry_tendsto beta h a (p 0)).comp hshift
  have hright :=
    (isingTransfer_normalized_entry_tendsto beta h (p (Fin.last k)) b).comp hshift
  have hden := (isingTransfer_normalized_entry_tendsto beta h a b).comp hdenShift
  have hleft' : Filter.Tendsto
      (fun m : ℕ => (c ^ (m + 1) • A ^ (m + 1)) a (p 0))
      Filter.atTop (nhds (P a (p 0))) := by
    simpa only [Function.comp_apply, c, A, P] using hleft
  have hright' : Filter.Tendsto
      (fun m : ℕ => (c ^ (m + 1) • A ^ (m + 1)) (p (Fin.last k)) b)
      Filter.atTop (nhds (P (p (Fin.last k)) b)) := by
    simpa only [Function.comp_apply, c, A, P] using hright
  have hden' : Filter.Tendsto
      (fun m : ℕ => (c ^ (2 * (m + 1) + k) • A ^ (2 * (m + 1) + k)) a b)
      Filter.atTop (nhds (P a b)) := by
    simpa only [Function.comp_apply, c, A, P] using hden
  have hratio := ((hleft'.mul hright').mul_const W).div hden'
    (ne_of_gt (isingTransferProjectorPlus_pos beta h a b))
  have hscaled := hratio.mul_const (c ^ k)
  have hlimit :
      (P a (p 0) * P (p (Fin.last k)) b * W / P a b) * c ^ k =
        P (p (Fin.last k)) (p 0) * W * c ^ k := by
    have hpab : P a b ≠ 0 := ne_of_gt (isingTransferProjectorPlus_pos beta h a b)
    rw [show P a (p 0) * P (p (Fin.last k)) b =
      P a b * P (p (Fin.last k)) (p 0) by
        exact isingTransferProjectorPlus_cross_general beta h a (p 0)
          (p (Fin.last k)) b]
    rw [show P a b * P (p (Fin.last k)) (p 0) * W =
      P a b * (P (p (Fin.last k)) (p 0) * W) by ring]
    rw [mul_div_cancel_left₀ _ hpab]
  rw [hlimit] at hscaled
  simpa only [c, A, P, W] using hscaled.congr' (Filter.Eventually.of_forall (fun m => by
    simp only [Pi.div_apply, Matrix.smul_apply, smul_eq_mul]
    have hpow : c ^ (2 * (m + 1) + k) = (c ^ (m + 1)) ^ 2 * c ^ k := by
      rw [pow_add, show 2 * (m + 1) = (m + 1) * 2 by omega, pow_mul, pow_two]
    rw [hpow]
    field_simp
    ring))

noncomputable def blockStateLimit (r : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) : ℝ :=
  isingTransferProjectorPlus beta (beta * h) (p (Fin.last (2 * r))) (p 0) *
    fixedWordProduct (isingTransferReal beta (beta * h)) p *
      (isingTransferEigenPlus beta (beta * h))⁻¹ ^ (2 * r)

theorem fvBlockStateProb_tendsto
    (eta : ℕ → ConfigSpace (Site 1)) (r : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    Filter.Tendsto (fun m => fvBlockStateProb (eta m) r m beta h p)
      Filter.atTop (nhds (blockStateLimit r beta h p)) := by
  have hfixed (a b : Fin 2) : Filter.Tendsto
      (fun m : ℕ =>
        (isingTransferReal beta (beta * h) ^ (m + 1)) a (p 0) *
          fixedWordProduct (isingTransferReal beta (beta * h)) p *
            (isingTransferReal beta (beta * h) ^ (m + 1))
              (p (Fin.last (2 * r))) b /
          (isingTransferReal beta (beta * h) ^ (2 * (r + m) + 2)) a b)
      Filter.atTop (nhds (blockStateLimit r beta h p)) := by
    simpa only [blockStateLimit, show ∀ m : ℕ,
      2 * (r + m) + 2 = 2 * (m + 1) + 2 * r by omega] using
      isingTransfer_fixedWord_weight_tendsto beta (beta * h) (2 * r) p a b
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N00, h00⟩ := (Metric.tendsto_atTop.mp (hfixed 0 0)) eps heps
  obtain ⟨N01, h01⟩ := (Metric.tendsto_atTop.mp (hfixed 0 1)) eps heps
  obtain ⟨N10, h10⟩ := (Metric.tendsto_atTop.mp (hfixed 1 0)) eps heps
  obtain ⟨N11, h11⟩ := (Metric.tendsto_atTop.mp (hfixed 1 1)) eps heps
  refine ⟨max (max N00 N01) (max N10 N11), fun m hm => ?_⟩
  rw [fvBlockStateProb_eq_matrix_ratio]
  have hm00 : N00 ≤ m := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm)
  have hm01 : N01 ≤ m := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm)
  have hm10 : N10 ≤ m := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hm)
  have hm11 : N11 ≤ m := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hm)
  generalize hL : fvLeftBoundaryState (eta m) (r + m) = L
  generalize hR : fvRightBoundaryState (eta m) (r + m) = R
  fin_cases L <;> fin_cases R
  · simpa only [hL, hR] using h00 m hm00
  · simpa only [hL, hR] using h01 m hm01
  · simpa only [hL, hR] using h10 m hm10
  · simpa only [hL, hR] using h11 m hm11

theorem fvMeasure_blockStateEvent_tendsto
    (eta : ℕ → ConfigSpace (Site 1)) (r : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    Filter.Tendsto
      (fun m => (fvMeasure (eta m) (r + m) (bondFinsetTouch 1 (r + m)) beta h).real
        (blockStateEvent r p))
      Filter.atTop (nhds (blockStateLimit r beta h p)) := by
  simpa only [fvMeasure_blockStateEvent_real] using
    fvBlockStateProb_tendsto eta r beta h p




open MeasureTheory Filter

theorem dlr_blockStateEvent_real_eq_limit
    (beta h : ℝ) (mu : Measure (ConfigSpace (Site 1))) [IsProbabilityMeasure mu]
    (hmu : IsDLRState 1 beta h mu) (r : ℕ)
    (p : Fin (2 * r + 1) → Fin 2) :
    mu.real (blockStateEvent r p) = blockStateLimit r beta h p := by
  let F : ℕ → ConfigSpace (Site 1) → ℝ := fun m eta =>
    (fvMeasure eta (r + m) (bondFinsetTouch 1 (r + m)) beta h).real
      (blockStateEvent r p)
  have hmeas (m : ℕ) : AEStronglyMeasurable (F m) mu :=
    (fvMeasure_real_integrable beta h mu (r + m) _
      (measurableSet_blockStateEvent r p)).aestronglyMeasurable
  have hbound (m : ℕ) : ∀ᵐ eta ∂mu, ‖F m eta‖ ≤ (1 : ℝ) := by
    filter_upwards with eta
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hlim : ∀ᵐ eta ∂mu,
      Tendsto (fun m => F m eta) atTop (nhds (blockStateLimit r beta h p)) := by
    filter_upwards with eta
    exact fvMeasure_blockStateEvent_tendsto (fun _ => eta) r beta h p
  have hdct := tendsto_integral_of_dominated_convergence
    (fun _ : ConfigSpace (Site 1) => (1 : ℝ)) hmeas (integrable_const 1) hbound hlim
  have hintegral (m : ℕ) : ∫ eta, F m eta ∂mu = mu.real (blockStateEvent r p) := by
    rw [gsi_dlr_real_eq_integral beta h mu hmu (r + m)
      (measurableSet_blockStateEvent r p)]
  have hconst : Tendsto (fun _ : ℕ => mu.real (blockStateEvent r p)) atTop
      (nhds (mu.real (blockStateEvent r p))) := tendsto_const_nhds
  have hdct' : Tendsto (fun _ : ℕ => mu.real (blockStateEvent r p)) atTop
      (nhds (blockStateLimit r beta h p)) := by
    simpa only [F, hintegral, integral_const, probReal_univ, smul_eq_mul, one_mul]
      using hdct
  exact tendsto_nhds_unique hconst hdct'


def intervalStatePattern (r : ℕ) (sigma : ConfigSpace (Site 1)) :
    Fin (2 * r + 1) → Fin 2 := fun i =>
  boolTransferState (sigma (site1 (-(r : ℤ) + (i.val : ℤ))))

lemma measurable_intervalStatePattern (r : ℕ) : Measurable (intervalStatePattern r) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_of_finite _).comp (measurable_pi_apply _)

lemma intervalStatePattern_preimage_singleton (r : ℕ)
    (p : Fin (2 * r + 1) → Fin 2) :
    intervalStatePattern r ⁻¹' {p} = blockStateEvent r p := by
  ext sigma
  change intervalStatePattern r sigma = p ↔ ∀ i,
    boolTransferState (sigma (site1 (-(r : ℤ) + (i.val : ℤ)))) = p i
  exact funext_iff

theorem map_intervalStatePattern_eq_of_block_eq
    {mu nu : Measure (ConfigSpace (Site 1))} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2),
      mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p)) (r : ℕ) :
    Measure.map (intervalStatePattern r) mu = Measure.map (intervalStatePattern r) nu := by
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_intervalStatePattern r) (measurableSet_singleton p),
    Measure.map_apply (measurable_intervalStatePattern r) (measurableSet_singleton p),
    intervalStatePattern_preimage_singleton]
  have hr := hblock r p
  unfold Measure.real at hr
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top mu _) (measure_ne_top nu _)).mp hr



noncomputable def intervalPatternRestriction (r : ℕ) (t : Finset (Site 1))
    (ht : (t : Set (Site 1)) ⊆ box 1 r) (p : Fin (2 * r + 1) → Fin 2) : t → Bool :=
  fun x => boolEquivFin2.symm
    (p (box1EquivFin r ⟨x.1, ht x.2⟩))

lemma intervalPatternRestriction_pattern (r : ℕ) (t : Finset (Site 1))
    (ht : (t : Set (Site 1)) ⊆ box 1 r) (sigma : ConfigSpace (Site 1)) :
    intervalPatternRestriction r t ht (intervalStatePattern r sigma) =
      fun x : t => sigma x.1 := by
  funext x
  unfold intervalPatternRestriction intervalStatePattern
  change boolEquivFin2.symm
      (boolEquivFin2 (sigma (site1 (-(r : ℤ) +
        (((box1EquivFin r) ⟨x.1, ht x.2⟩).val : ℤ))))) = sigma x.1
  rw [Equiv.symm_apply_apply]
  congr 2
  have hx := congrArg Subtype.val
    ((box1EquivFin r).symm_apply_apply ⟨x.1, ht x.2⟩)
  change site1 ((((site1Coord x.1 + (r : ℤ)).toNat : ℕ) : ℤ) - (r : ℤ)) = x.1 at hx
  change site1 (-(r : ℤ) +
    (((site1Coord x.1 + (r : ℤ)).toNat : ℕ) : ℤ)) = x.1
  rw [show -(r : ℤ) + (((site1Coord x.1 + (r : ℤ)).toNat : ℕ) : ℤ) =
    (((site1Coord x.1 + (r : ℤ)).toNat : ℕ) : ℤ) - (r : ℤ) by ring]
  exact hx

theorem map_finsetRestriction_eq_of_block_eq
    {mu nu : Measure (ConfigSpace (Site 1))} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2),
      mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p))
    (t : Finset (Site 1)) :
    Measure.map (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) mu =
      Measure.map (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) nu := by
  let r := t.sup (fun x => (site1Coord x).natAbs)
  have ht : (t : Set (Site 1)) ⊆ box 1 r := by
    intro x hx
    rw [← site1_site1Coord x, site1_mem_box_iff]
    have hle : (site1Coord x).natAbs ≤ r := Finset.le_sup (f := fun y =>
      (site1Coord y).natAbs) hx
    have habs : |site1Coord x| ≤ (r : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hle
    exact abs_le.mp habs
  let proj : ConfigSpace (Site 1) → (t → Bool) := fun sigma x => sigma x.1
  let recover : (Fin (2 * r + 1) → Fin 2) → (t → Bool) :=
    intervalPatternRestriction r t ht
  have hproj : Measurable proj := by
    apply measurable_pi_lambda
    intro x
    exact measurable_pi_apply _
  have hrecover : Measurable recover := measurable_of_finite _
  have hpattern := measurable_intervalStatePattern r
  have hmap := map_intervalStatePattern_eq_of_block_eq hblock r
  have hfac : recover ∘ intervalStatePattern r = proj := by
    funext sigma
    exact intervalPatternRestriction_pattern r t ht sigma
  change Measure.map proj mu = Measure.map proj nu
  calc
    Measure.map proj mu = Measure.map recover (Measure.map (intervalStatePattern r) mu) := by
      rw [Measure.map_map hrecover hpattern, hfac]
    _ = Measure.map recover (Measure.map (intervalStatePattern r) nu) := by rw [hmap]
    _ = Measure.map proj nu := by
      rw [Measure.map_map hrecover hpattern, hfac]

theorem measure_cylinder_eq_of_block_eq
    {mu nu : Measure (ConfigSpace (Site 1))} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2),
      mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p))
    (t : Finset (Site 1)) (S : Set (t → Bool)) (hS : MeasurableSet S) :
    mu (cylinder t S) = nu (cylinder t S) := by
  have hproj : Measurable
      (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) := by
    apply measurable_pi_lambda
    intro x
    exact measurable_pi_apply _
  have hmap := map_finsetRestriction_eq_of_block_eq hblock t
  calc
    mu (cylinder t S) = (Measure.map
        (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) mu) S := by
      rw [Measure.map_apply hproj hS]
      rfl
    _ = (Measure.map
        (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) nu) S := by
      rw [hmap]
    _ = nu (cylinder t S) := by
      rw [Measure.map_apply hproj hS]
      rfl



theorem oneDim_isDLRState_unique (beta h : ℝ)
    (mu nu : Measure (ConfigSpace (Site 1))) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (hmu : IsDLRState 1 beta h mu)
    (hnu : IsDLRState 1 beta h nu) : mu = nu := by
  have hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2),
      mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p) := by
    intro r p
    rw [dlr_blockStateEvent_real_eq_limit beta h mu hmu r p,
      dlr_blockStateEvent_real_eq_limit beta h nu hnu r p]
  apply ext_of_generate_finite (measurableCylinders (fun _ : Site 1 => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro A hA
    rw [mem_measurableCylinders] at hA
    obtain ⟨t, S, hS, rfl⟩ := hA
    exact measure_cylinder_eq_of_block_eq hblock t S hS
  · rw [measure_univ, measure_univ]


end StatMech.FrontierB
