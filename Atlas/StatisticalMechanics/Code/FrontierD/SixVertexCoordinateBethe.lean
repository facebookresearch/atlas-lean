/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheScattering
import Code.FrontierD.SixVertexBetheSymmetricProduct
import Code.FrontierD.SixVertexPerron
import Mathlib.GroupTheory.Perm.Fin

open Finset Matrix
open scoped symmDiff

namespace StatMech.FrontierD

noncomputable section

private theorem coordinate_zip_map_same {ι α β : Type*} (l : List ι)
    (f : ι → α) (g : ι → β) :
    (l.map f).zip (l.map g) = l.map fun i => (f i, g i) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem pairwise_flatMap_pairs_onlyIf {ι α : Type*} [Preorder α]
    (f g : ι → α) {l : List ι}
    (h : (l.flatMap fun i => [f i, g i]).Pairwise (· ≤ ·)) :
    (∀ i ∈ l, f i ≤ g i) ∧ l.Pairwise fun i j => g i ≤ f j := by
  induction l with
  | nil => simp
  | cons a l ih =>
      change List.Pairwise (· ≤ ·)
        (f a :: g a :: (l.flatMap fun i => [f i, g i])) at h
      rw [List.pairwise_cons_cons_iff_of_trans] at h
      rw [List.pairwise_cons] at h
      have htail := ih h.2.2
      constructor
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact h.1
        · exact htail.1 i hi
      · rw [List.pairwise_cons]
        refine ⟨?_, htail.2⟩
        intro j hj
        apply h.2.1
        exact List.mem_flatMap.mpr ⟨j, hj, by simp⟩


theorem sixVertexForwardInterlaced_iff_positions {N n : ℕ}
    (x y : SixVertexSector N n) :
    SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) ↔
      SixVertexPositionsForwardInterlaced x y := by
  constructor
  · intro h
    have hp := h.2
    rw [sixVertexAlternating, sixVertexSector_upPositions_eq_map_position,
      sixVertexSector_upPositions_eq_map_position,
      coordinate_zip_map_same] at hp
    simp only [List.flatMap_map] at hp
    have hparts := pairwise_flatMap_pairs_onlyIf
      (sixVertexSectorPosition x) (sixVertexSectorPosition y) hp
    constructor
    · intro i
      exact hparts.1 i (by simp)
    · intro k hk
      have hrel := hparts.2.rel_get_of_lt
        (a := ⟨k, by simpa using (show k < n by omega)⟩)
        (b := ⟨k + 1, by simpa using hk⟩) (by simp)
      simpa using hrel
  · exact sixVertexForwardInterlaced_of_positions x y



def sixVertexBethePairFactor (c : ℝ) (u v : ℂ) : ℂ :=
  1 + u * v - 2 * sixVertexDelta c * u

theorem sixVertexBethePairFactor_phase (c p q : ℝ) :
    sixVertexBethePairFactor c (sixVertexBethePhase p)
        (sixVertexBethePhase q) =
      sixVertexBethePhase p *
        (sixVertexBethePhase (-p) + sixVertexBethePhase q -
          2 * sixVertexDelta c) := by
  have hunit : sixVertexBethePhase p * sixVertexBethePhase (-p) = 1 := by
    rw [sixVertexBethePhase_neg]
    calc
      sixVertexBethePhase p * star (sixVertexBethePhase p) =
          (Complex.normSq (sixVertexBethePhase p) : ℂ) :=
        Complex.mul_conj (sixVertexBethePhase p)
      _ = (‖sixVertexBethePhase p‖ ^ 2 : ℝ) := by
        rw [Complex.normSq_eq_norm_sq]
      _ = 1 := by rw [sixVertexBethePhase_norm]; norm_num
  unfold sixVertexBethePairFactor
  rw [← hunit]
  ring

theorem sixVertexScatteringDenominator_eq_phase (c p q : ℝ) :
    sixVertexScatteringDenominator c p q =
      sixVertexBethePhase p + sixVertexBethePhase (-q) -
        2 * sixVertexDelta c := by
  unfold sixVertexScatteringDenominator sixVertexBethePhase
  congr 2
  push_cast
  ring_nf

theorem sixVertexBethePairFactor_eq_phase_mul_conj_denominator
    (c p q : ℝ) :
    sixVertexBethePairFactor c (sixVertexBethePhase p)
        (sixVertexBethePhase q) =
      sixVertexBethePhase p *
        star (sixVertexScatteringDenominator c p q) := by
  rw [sixVertexBethePairFactor_phase,
    sixVertexScatteringDenominator_eq_phase]
  congr 1
  apply Complex.ext <;> simp [sixVertexBethePhase_neg]

theorem sixVertexBethePairFactor_swap_eq_phase_mul_denominator
    (c p q : ℝ) :
    sixVertexBethePairFactor c (sixVertexBethePhase q)
        (sixVertexBethePhase p) =
      sixVertexBethePhase q * sixVertexScatteringDenominator c p q := by
  rw [sixVertexBethePairFactor_phase,
    sixVertexScatteringDenominator_eq_phase]
  ring

theorem sixVertexBethePairFactor_phase_ne_zero {c : ℝ} (hc : 2 < c)
    (p q : ℝ) :
    sixVertexBethePairFactor c (sixVertexBethePhase p)
      (sixVertexBethePhase q) ≠ 0 := by
  rw [sixVertexBethePairFactor_eq_phase_mul_conj_denominator]
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (star_ne_zero.mpr (sixVertexScatteringDenominator_ne_zero hc p q))

theorem sixVertexBethePhase_sub_mul (p q : ℝ) :
    Complex.exp (Complex.I * (p - q)) * sixVertexBethePhase q =
      sixVertexBethePhase p := by
  unfold sixVertexBethePhase
  rw [← Complex.exp_add]
  congr 1
  ring_nf

theorem sixVertexBethePhase_injective_on_Ioo :
    Set.InjOn sixVertexBethePhase (Set.Ioo (-Real.pi) Real.pi) := by
  intro p hp q hq heq
  rw [sixVertexBethePhase, sixVertexBethePhase] at heq
  rcases Complex.exp_eq_exp_iff_exists_int.mp heq with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  norm_num at him
  have htwopi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmlo : (-1 : ℝ) < (m : ℝ) := by
    by_contra h
    have hmle : (m : ℝ) ≤ -1 := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hmle htwopi.le
    nlinarith [hp.1, hq.2, Real.pi_pos]
  have hmhi : (m : ℝ) < 1 := by
    by_contra h
    have hmge : (1 : ℝ) ≤ m := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hmge htwopi.le
    nlinarith [hp.2, hq.1, Real.pi_pos]
  have hmlo' : (-1 : ℤ) < m := by exact_mod_cast hmlo
  have hmhi' : m < (1 : ℤ) := by exact_mod_cast hmhi
  have hm0 : m = 0 := by omega
  subst m
  norm_num at him
  exact him

theorem SixVertexOpenRootSimplex.phase_injective
    {n : ℕ} {p : Fin n → ℝ} (hp : SixVertexOpenRootSimplex p) :
    Function.Injective fun j => sixVertexBethePhase (p j) := by
  intro j k hjk
  apply hp.1.injective
  exact sixVertexBethePhase_injective_on_Ioo (hp.2.2 j) (hp.2.2 k) hjk

theorem SixVertexOpenRootSimplex.ne_zero_of_even
    {k : ℕ} {p : Fin (k + k) → ℝ} (hp : SixVertexOpenRootSimplex p)
    (j : Fin (k + k)) : p j ≠ 0 := by
  intro hjzero
  have hrevzero : p j.rev = 0 := by rw [hp.2.1, hjzero, neg_zero]
  have hjrev : j.rev = j := hp.1.injective (hrevzero.trans hjzero.symm)
  have hval := congrArg Fin.val hjrev
  simp only [Fin.rev, Fin.val_mk] at hval
  omega

theorem SixVertexOpenRootSimplex.phase_ne_one_of_even
    {k : ℕ} {p : Fin (k + k) → ℝ} (hp : SixVertexOpenRootSimplex p)
    (j : Fin (k + k)) : sixVertexBethePhase (p j) ≠ 1 := by
  intro hphase
  have hphase0 : sixVertexBethePhase (p j) = sixVertexBethePhase 0 := by
    simpa [sixVertexBethePhase] using hphase
  have hpzero := sixVertexBethePhase_injective_on_Ioo (hp.2.2 j)
    ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩ hphase0
  exact hp.ne_zero_of_even j hpzero


theorem sixVertexBethePairFactor_exchange {c : ℝ} (hc : 2 < c)
    (p q : ℝ) :
    Complex.exp (-Complex.I * sixVertexTheta c p q) *
        sixVertexBethePairFactor c (sixVertexBethePhase q)
          (sixVertexBethePhase p) =
      sixVertexBethePairFactor c (sixVertexBethePhase p)
        (sixVertexBethePhase q) := by
  rw [sixVertexTheta_exp_identity hc,
    sixVertexBethePairFactor_swap_eq_phase_mul_denominator,
    sixVertexBethePairFactor_eq_phase_mul_conj_denominator]
  field_simp [sixVertexScatteringDenominator_ne_zero hc p q]
  rw [sixVertexBethePhase_sub_mul]

theorem sixVertexBethePhase_pow (N : ℕ) (p : ℝ) :
    sixVertexBethePhase p ^ N =
      Complex.exp (Complex.I * ((N : ℝ) * p)) := by
  rw [sixVertexBethePhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring_nf



theorem SixVertexSatisfiesMultiplicativeBetheEquations.pairFactor_periodic
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N n p)
    (j : Fin n) :
    sixVertexBethePhase (p j) ^ N *
        (∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p k))
          (sixVertexBethePhase (p j))) =
      (-1 : ℂ) ^ (n - 1) *
        ∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p j))
          (sixVertexBethePhase (p k)) := by
  have hsum :
      -Complex.I *
          ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ) =
        ∑ k, -Complex.I * sixVertexTheta c (p j) (p k) := by
    push_cast
    rw [Finset.mul_sum]
  have hexchange :
      Complex.exp (-Complex.I *
          ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ)) *
          (∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p k))
            (sixVertexBethePhase (p j))) =
        ∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p j))
          (sixVertexBethePhase (p k)) := by
    rw [hsum, Complex.exp_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    exact sixVertexBethePairFactor_exchange hc (p j) (p k)
  rw [sixVertexBethePhase_pow, hp j]
  calc
    ((-1 : ℂ) ^ (n - 1) *
        Complex.exp (-Complex.I *
          ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ))) *
          ∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p k))
            (sixVertexBethePhase (p j)) =
      (-1 : ℂ) ^ (n - 1) *
        (Complex.exp (-Complex.I *
          ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ)) *
          ∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p k))
            (sixVertexBethePhase (p j))) := by ring
    _ = _ := by rw [hexchange]


def sixVertexBethePairProduct {n : ℕ} (c : ℝ) (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  ∏ k, ∏ l ∈ Finset.Ioi k,
    sixVertexBethePairFactor c (sixVertexBethePhase (p (σ k)))
      (sixVertexBethePhase (p (σ l)))


def sixVertexBetheAmplitude {n : ℕ} (c : ℝ) (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
    sixVertexBethePairProduct c p σ

theorem sixVertexBetheAmplitude_eq_source {n : ℕ} (c : ℝ)
    (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    sixVertexBetheAmplitude c p σ =
      (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
        ∏ k, ∏ l ∈ Finset.Ioi k,
          sixVertexBethePhase (p (σ k)) *
            (sixVertexBethePhase (-(p (σ k))) +
              sixVertexBethePhase (p (σ l)) - 2 * sixVertexDelta c) := by
  unfold sixVertexBetheAmplitude sixVertexBethePairProduct
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  apply Finset.prod_congr rfl
  intro l _
  exact sixVertexBethePairFactor_phase c (p (σ k)) (p (σ l))

theorem sixVertexBethePairProduct_ne_zero {c : ℝ} (hc : 2 < c)
    {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    sixVertexBethePairProduct c p σ ≠ 0 := by
  unfold sixVertexBethePairProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  apply Finset.prod_ne_zero_iff.mpr
  intro l _
  exact sixVertexBethePairFactor_phase_ne_zero hc _ _

theorem sixVertexBetheAmplitude_ne_zero {c : ℝ} (hc : 2 < c)
    {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    sixVertexBetheAmplitude c p σ ≠ 0 := by
  unfold sixVertexBetheAmplitude
  apply mul_ne_zero
  · norm_cast
    exact Units.ne_zero (Equiv.Perm.sign σ)
  · exact sixVertexBethePairProduct_ne_zero hc p σ




def sixVertexBetheMonomial {N n : ℕ} (p : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (x : SixVertexSector N n) : ℂ :=
  ∏ k, (sixVertexBethePhase (p (σ k))) ^
    (sixVertexSectorPosition x k).val


def sixVertexCoordinateBetheWave {N n : ℕ} (c : ℝ) (p : Fin n → ℝ) :
    SixVertexSector N n → ℂ :=
  fun x => ∑ σ : Equiv.Perm (Fin n),
    sixVertexBetheAmplitude c p σ * sixVertexBetheMonomial p σ x



def sixVertexSectorTransferComplex (N n : ℕ) (c : ℝ) :
    Matrix (SixVertexSector N n) (SixVertexSector N n) ℂ :=
  (sixVertexSectorTransfer N n c).map (fun r => (r : ℂ))

@[simp] theorem sixVertexSectorTransferComplex_apply
    (N n : ℕ) (c : ℝ) (x y : SixVertexSector N n) :
    sixVertexSectorTransferComplex N n c x y =
      (sixVertexSectorTransfer N n c x y : ℂ) := rfl

theorem sixVertexSectorTransferComplex_mulVec_apply
    (N n : ℕ) (c : ℝ) (v : SixVertexSector N n → ℂ)
    (x : SixVertexSector N n) :
    (sixVertexSectorTransferComplex N n c).mulVec v x =
      ∑ y, (sixVertexSectorTransfer N n c x y : ℂ) * v y := rfl

theorem sixVertexSectorRowDistance_eq_card_symmDiff
    {N n : ℕ} (x y : SixVertexSector N n) :
    sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) =
      ((x : Finset (Fin N)) ∆ (y : Finset (Fin N))).card := by
  unfold sixVertexRowDistance
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_symmDiff]
  simp [sixVertexSectorRow]
  tauto

theorem sixVertexSectorRowDistance_eq_two_mul_sdiff
    {N n : ℕ} (x y : SixVertexSector N n) :
    sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) =
      2 * ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
  rw [sixVertexSectorRowDistance_eq_card_symmDiff]
  change (((x : Finset (Fin N)) \ (y : Finset (Fin N))) ∪
    ((y : Finset (Fin N)) \ (x : Finset (Fin N)))).card = _
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop]
    rw [Finset.inter_comm]
    omega
  · rw [Finset.disjoint_left]
    intro i hix hiy
    simp only [Finset.mem_sdiff] at hix hiy
    exact hix.2 hiy.1



theorem sixVertexSectorTransferComplex_mulVec_eq_interlacedSum
    (N n : ℕ) (c : ℝ) (v : SixVertexSector N n → ℂ)
    (x : SixVertexSector N n) :
    (sixVertexSectorTransferComplex N n c).mulVec v x =
      2 * v x +
        ∑ y ∈ (Finset.univ.erase x),
          if SixVertexInterlaced (sixVertexSectorRow x)
              (sixVertexSectorRow y) then
            (c : ℂ) ^ sixVertexRowDistance (sixVertexSectorRow x)
              (sixVertexSectorRow y) * v y
          else 0 := by
  rw [sixVertexSectorTransferComplex_mulVec_apply]
  have hxmem : x ∈ (Finset.univ : Finset (SixVertexSector N n)) :=
    Finset.mem_univ x
  rw [← Finset.sum_erase_add _ _ hxmem]
  have hdiag : (sixVertexSectorTransfer N n c x x : ℂ) * v x =
      2 * v x := by
    simp [sixVertexSectorTransfer, sixVertexTransfer]
  rw [hdiag]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hxy : sixVertexSectorRow x ≠ sixVertexSectorRow y := by
    intro hrow
    apply hyx
    apply Subtype.ext
    ext i
    have hi := congrFun hrow i
    simpa [sixVertexSectorRow] using hi.symm
  by_cases hinter : SixVertexInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y)
  · simp [sixVertexSectorTransfer, sixVertexTransfer, hxy, hinter]
  · simp [sixVertexSectorTransfer, sixVertexTransfer, hxy, hinter]


def sixVertexBetheEigenvalueCandidate {n : ℕ} (c : ℝ)
    (p : Fin n → ℝ) : ℂ :=
  (∏ j, sixVertexBetheL c (sixVertexBethePhase (p j))) +
    ∏ j, sixVertexBetheM c (sixVertexBethePhase (p j))



def sixVertexPairedRootFamily {k : ℕ} (p : Fin k → ℝ) :
    Fin (k + k) → ℝ :=
  fun i => match finSumFinEquiv.symm i with
    | Sum.inl j => p j
    | Sum.inr j => -p j

theorem prod_sixVertexPairedRootFamily {k : ℕ} (p : Fin k → ℝ)
    (f : ℝ → ℂ) :
    (∏ i, f (sixVertexPairedRootFamily p i)) =
      (∏ j, f (p j)) * ∏ j, f (-p j) := by
  let g : Fin k ⊕ Fin k → ℂ := fun s => match s with
    | Sum.inl j => f (p j)
    | Sum.inr j => f (-p j)
  calc
    (∏ i, f (sixVertexPairedRootFamily p i)) = ∏ s, g s := by
      symm
      apply Fintype.prod_equiv finSumFinEquiv
      intro s
      change g s = f (sixVertexPairedRootFamily p (finSumFinEquiv s))
      unfold sixVertexPairedRootFamily
      rw [Equiv.symm_apply_apply]
      dsimp [g]
      cases s <;> rfl
    _ = (∏ j, f (p j)) * ∏ j, f (-p j) := by
      rw [Fintype.prod_sum_type]

theorem sixVertexBetheEigenvalueCandidate_paired {k : ℕ} (c : ℝ)
    (p : Fin k → ℝ) :
    sixVertexBetheEigenvalueCandidate c (sixVertexPairedRootFamily p) =
      sixVertexSymmetricBetheEigenvalueCandidate c p := by
  unfold sixVertexBetheEigenvalueCandidate
  unfold sixVertexSymmetricBetheEigenvalueCandidate
  rw [prod_sixVertexPairedRootFamily p
      (fun r => sixVertexBetheL c (sixVertexBethePhase r)),
    prod_sixVertexPairedRootFamily p
      (fun r => sixVertexBetheM c (sixVertexBethePhase r)),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]


def SixVertexCoordinateBetheEigenrelation {N n : ℕ} (c : ℝ)
    (p : Fin n → ℝ) : Prop :=
  (sixVertexSectorTransferComplex N n c).mulVec
      (sixVertexCoordinateBetheWave c p) =
    sixVertexBetheEigenvalueCandidate c p •
      sixVertexCoordinateBetheWave c p

@[simp] theorem sixVertexBethePairProduct_zero (c : ℝ)
    (p : Fin 0 → ℝ) (σ : Equiv.Perm (Fin 0)) :
    sixVertexBethePairProduct c p σ = 1 := by
  simp [sixVertexBethePairProduct]

@[simp] theorem sixVertexBetheAmplitude_zero (c : ℝ)
    (p : Fin 0 → ℝ) (σ : Equiv.Perm (Fin 0)) :
    sixVertexBetheAmplitude c p σ = 1 := by
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst σ
  simp [sixVertexBetheAmplitude]

@[simp] theorem sixVertexBetheEigenvalueCandidate_zero (c : ℝ)
    (p : Fin 0 → ℝ) : sixVertexBetheEigenvalueCandidate c p = 2 := by
  simp [sixVertexBetheEigenvalueCandidate]
  norm_num

theorem sixVertexCoordinateBetheEigenrelation_zero (N : ℕ) (c : ℝ)
    (p : Fin 0 → ℝ) :
    SixVertexCoordinateBetheEigenrelation (N := N) c p := by
  classical
  let emptySector : SixVertexSector N 0 := ⟨∅, by simp⟩
  letI : Unique (SixVertexSector N 0) := {
    default := emptySector
    uniq := fun y => by
      apply Subtype.ext
      exact Finset.card_eq_zero.mp y.prop }
  unfold SixVertexCoordinateBetheEigenrelation
  funext x
  rw [sixVertexSectorTransferComplex_mulVec_apply,
    Fintype.sum_subsingleton _ x]
  simp [sixVertexCoordinateBetheWave, sixVertexBetheMonomial,
    sixVertexBetheEigenvalueCandidate, sixVertexSectorTransfer,
    sixVertexTransfer]
  norm_num

end

end StatMech.FrontierD
