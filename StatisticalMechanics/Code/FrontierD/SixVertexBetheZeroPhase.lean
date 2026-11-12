/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargeRoots
import Code.FrontierD.SixVertexCoordinateBetheOne

open Finset

namespace StatMech.FrontierD

noncomputable section




theorem continuous_sixVertexCoordinateBetheWave_roots
    {N n : Nat} (c : Real) (x : SixVertexSector N n) :
    Continuous (fun p : Fin n -> Real => sixVertexCoordinateBetheWave c p x) := by
  unfold sixVertexCoordinateBetheWave sixVertexBetheAmplitude
    sixVertexBethePairProduct sixVertexBetheMonomial
    sixVertexBethePairFactor sixVertexBethePhase
  fun_prop




theorem sixVertexBethe_intervalLocalSum_one
    (c : Real) {a b : Int} (hab : a < b) :
    (∑ y ∈ Finset.Icc a b,
      (if y = a ∨ y = b then 1 else (c : Complex) ^ 2) *
        (1 : Complex) ^ y) =
      2 + ((b - a - 1).toNat : Complex) * (c : Complex) ^ 2 := by
  have hIcc : Finset.Icc a b =
      insert a (insert b (Finset.Ioo a b)) := by
    ext y
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hIcc, Finset.sum_insert, Finset.sum_insert]
  · simp only [true_or, if_true, or_true, one_zpow, mul_one]
    have hinter :
        (∑ y ∈ Finset.Ioo a b,
          if y = a ∨ y = b then 1 else (c : Complex) ^ 2) =
          ((b - a - 1).toNat : Complex) * (c : Complex) ^ 2 := by
      calc
        _ = ∑ _y ∈ Finset.Ioo a b, (c : Complex) ^ 2 := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [if_neg]
          exact fun h => by
            rcases h with rfl | rfl <;> simpa using hy
        _ = ((Finset.Ioo a b).card : Complex) * (c : Complex) ^ 2 := by
          simp
        _ = _ := by rw [Int.card_Ioo]
    rw [hinter]
    ring
  · simp
  · simp only [Finset.mem_insert, Finset.mem_Ioo, not_or]
    omega

theorem sixVertexBetheIntervalTupleWeight_factor
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x q : Fin (n + 1) -> Int) :
    sixVertexBetheIntervalTupleWeight N c z x q =
      ((c : Complex) ^ 2) ^ (sixVertexBetheInteriorSet N x q).card *
        ∏ i, z i ^ q i := by
  unfold sixVertexBetheIntervalTupleWeight
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 2
  ext i
  simp [sixVertexBetheInteriorSet]





theorem sixVertexBetheCollisionConstrainedIntervalSum_zeroPhase
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) -> Real)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (hS : SixVertexBetheNoAdjacent S)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i) :
    sixVertexBetheCollisionConstrainedIntervalSum N c
        (fun i => sixVertexBethePhase (p i)) x S =
      (if ell ∈ S then 1
        else if (finRotate (n + 1)).symm ell ∈ S then 1
        else 2 +
          ((x ell - sixVertexBetheShiftCoordinates N x ell - 1).toNat :
            Complex) * (c : Complex) ^ 2) *
        ∏ i ∈ (Finset.univ.erase ell),
          ∑ y ∈ sixVertexBetheConstrainedCoordinateSet N x S i,
            (if y = sixVertexBetheShiftCoordinates N x i ∨ y = x i
              then 1 else (c : Complex) ^ 2) *
              sixVertexBethePhase (p i) ^ y := by
  let F : Fin (n + 1) -> Complex := fun i =>
    ∑ y ∈ sixVertexBetheConstrainedCoordinateSet N x S i,
      (if y = sixVertexBetheShiftCoordinates N x i ∨ y = x i
        then 1 else (c : Complex) ^ 2) *
        sixVertexBethePhase (p i) ^ y
  rw [sixVertexBetheCollisionConstrainedIntervalSum_eq_prod N c _ x S hS
    (fun i => (hgap i).le)]
  change (∏ i, F i) = _
  rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ ell)]
  congr 1
  by_cases hellS : ell ∈ S
  · simp [F, sixVertexBetheConstrainedCoordinateSet, hellS, hell,
      sixVertexBethePhase]
  · by_cases hpred : (finRotate (n + 1)).symm ell ∈ S
    · have hpred' : ell - 1 ∈ S := by simpa using hpred
      simp [F, sixVertexBetheConstrainedCoordinateSet, hellS, hpred,
        hpred', hell, sixVertexBethePhase]
    · have hpred' : ell - 1 ∉ S := by simpa using hpred
      simp only [F, sixVertexBetheConstrainedCoordinateSet, hellS,
        hpred, hpred', if_false, hell, sixVertexBethePhase,
        Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      exact sixVertexBethe_intervalLocalSum_one c (hgap ell)

theorem sixVertexBetheCollisionConstrainedIntervalSum_zero_of_adjacent
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
    (hS : ¬ SixVertexBetheNoAdjacent S) :
    sixVertexBetheCollisionConstrainedIntervalSum N c z x S = 0 := by
  classical
  simp only [SixVertexBetheNoAdjacent, not_forall] at hS
  obtain ⟨i, hi⟩ := hS
  simp only [Classical.not_imp, not_not] at hi
  unfold sixVertexBetheCollisionConstrainedIntervalSum
  apply Finset.sum_eq_zero
  intro q hq
  have hsubset := (Finset.mem_filter.mp hq).2
  have hcoli := (mem_sixVertexBetheCollisionSet N x q i).mp
    (hsubset hi.1)
  have hcolnext := (mem_sixVertexBetheCollisionSet N x q
    (finRotate (n + 1) i)).mp (hsubset hi.2)
  exfalso
  exact (hgap (finRotate (n + 1) i)).ne
    (hcoli.2.symm.trans hcolnext.1)

def sixVertexBetheNoAdjacentCollisionSets (n : Nat) :
    Finset (Finset (Fin (n + 1))) := by
  classical
  exact (Finset.univ : Finset (Fin (n + 1))).powerset.filter
    SixVertexBetheNoAdjacent

def sixVertexBetheZeroPhaseRegularizedIntervalSum
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) -> Real)
    (x : Fin (n + 1) -> Int) (ell : Fin (n + 1)) : Complex := by
  classical
  exact ∑ S ∈ sixVertexBetheNoAdjacentCollisionSets n,
    (-1 : Complex) ^ S.card *
      ((if ell ∈ S then 1
        else if (finRotate (n + 1)).symm ell ∈ S then 1
        else 2 +
          ((x ell - sixVertexBetheShiftCoordinates N x ell - 1).toNat :
            Complex) * (c : Complex) ^ 2) *
        ∏ i ∈ (Finset.univ.erase ell),
          ∑ y ∈ sixVertexBetheConstrainedCoordinateSet N x S i,
            (if y = sixVertexBetheShiftCoordinates N x i ∨ y = x i
              then 1 else (c : Complex) ^ 2) *
              sixVertexBethePhase (p i) ^ y)




theorem sixVertexBetheCollisionFreeIntervalSum_zeroPhase
    {n : Nat} (N : Nat) (c : Real) (p : Fin (n + 1) -> Real)
    (x : Fin (n + 1) -> Int) (ell : Fin (n + 1)) (hell : p ell = 0)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i) :
    sixVertexBetheCollisionFreeIntervalSum N c
        (fun i => sixVertexBethePhase (p i)) x =
      sixVertexBetheZeroPhaseRegularizedIntervalSum N c p x ell := by
  classical
  unfold sixVertexBetheZeroPhaseRegularizedIntervalSum
  rw [sixVertexBetheCollisionFreeIntervalSum_inclusionExclusion]
  let P := (Finset.univ : Finset (Fin (n + 1))).powerset
  let Q := sixVertexBetheNoAdjacentCollisionSets n
  calc
    (∑ S ∈ P, (-1 : Complex) ^ S.card *
        sixVertexBetheCollisionConstrainedIntervalSum N c
          (fun i => sixVertexBethePhase (p i)) x S) =
      ∑ S ∈ Q, (-1 : Complex) ^ S.card *
        sixVertexBetheCollisionConstrainedIntervalSum N c
          (fun i => sixVertexBethePhase (p i)) x S := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro S hSP hSQ
        have hnS : ¬ SixVertexBetheNoAdjacent S := by
          simpa [Q, sixVertexBetheNoAdjacentCollisionSets, P, hSP] using hSQ
        rw [sixVertexBetheCollisionConstrainedIntervalSum_zero_of_adjacent
          N c _ x S hgap hnS, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      have hno : SixVertexBetheNoAdjacent S := by
        simpa [Q, sixVertexBetheNoAdjacentCollisionSets, P] using hS
      rw [sixVertexBetheCollisionConstrainedIntervalSum_zeroPhase
        N c p x S ell hell hno hgap]





theorem SixVertexSatisfiesMultiplicativeBetheEquations.physicalZeroPhaseIntervalExpansion
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin (n + 1) -> Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (ell : Fin (n + 1)) (hell : p ell = 0)
    (x : SixVertexSector N (n + 1)) :
    (sixVertexSectorTransferComplex N (n + 1) c).mulVec
        (sixVertexCoordinateBetheWave c p) x =
      ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheZeroPhaseRegularizedIntervalSum N c
            (fun i => p (sigma i)) (sixVertexSectorIntCoordinates x)
            (sigma.symm ell) := by
  rw [hp.physicalCyclicIntervalExpansion hc p x]
  let Q := sixVertexBetheCollisionFreeTuples N
    (sixVertexSectorIntCoordinates x)
  calc
    (∑ q ∈ Q, sixVertexBetheTupleWaveWeight N c p
        (sixVertexSectorIntCoordinates x) q) =
      ∑ q ∈ Q, ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheIntervalTupleWeight N c
            (fun i => sixVertexBethePhase (p (sigma i)))
            (sixVertexSectorIntCoordinates x) q := by
      apply Finset.sum_congr rfl
      intro q hq
      symm
      rw [show (∑ sigma : Equiv.Perm (Fin (n + 1)),
          sixVertexBetheAmplitude c p sigma *
            sixVertexBetheIntervalTupleWeight N c
              (fun i => sixVertexBethePhase (p (sigma i)))
              (sixVertexSectorIntCoordinates x) q) =
          sixVertexBetheTupleBoltzmann N c
              (sixVertexSectorIntCoordinates x) q *
            ∑ sigma, sixVertexBetheAmplitude c p sigma *
              sixVertexBetheIntMonomial p sigma q by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro sigma _
        rw [sixVertexBetheIntervalTupleWeight_factor]
        unfold sixVertexBetheTupleBoltzmann sixVertexBetheIntMonomial
        ring]
      rfl
    _ = ∑ sigma : Equiv.Perm (Fin (n + 1)),
        sixVertexBetheAmplitude c p sigma *
          sixVertexBetheCollisionFreeIntervalSum N c
            (fun i => sixVertexBethePhase (p (sigma i)))
            (sixVertexSectorIntCoordinates x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sigma _
      unfold sixVertexBetheCollisionFreeIntervalSum
      dsimp only [Q, sixVertexBetheCollisionFreeTuples]
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro sigma _
      rw [sixVertexBetheCollisionFreeIntervalSum_zeroPhase N c
        (fun i => p (sigma i)) (sixVertexSectorIntCoordinates x)
        (sigma.symm ell)]
      · simp [hell]
      · exact sixVertexBetheShiftCoordinates_lt_sector x


def sixVertexThetaLeftDerivAtZero (c y : Real) : Real :=
  4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
    sixVertexThetaDerivativeDenominator c 0 y

theorem hasDerivAt_sixVertexTheta_zero_left
    {c : Real} (hc : 2 < c) (y : Real) :
    HasDerivAt (fun x => sixVertexTheta c x y)
      (sixVertexThetaLeftDerivAtZero c y) 0 := by
  simpa [sixVertexThetaLeftDerivAtZero,
    sixVertexBetheIntegratingFactor,
    sixVertexThetaDerivativeDenominator] using
      hasDerivAt_sixVertexTheta_left hc 0 y

theorem sixVertexThetaLeftDerivAtZero_self
    {c : Real} (hc : 2 < c) :
    sixVertexThetaLeftDerivAtZero c 0 = 2 / c ^ 2 - 1 := by
  have hc0 : c ≠ 0 := by linarith
  have hint : sixVertexBetheIntegratingFactor c 0 = c ^ 2 / 2 := by
    unfold sixVertexBetheIntegratingFactor sixVertexDelta
    rw [Real.cos_zero]
    ring
  have hden : sixVertexThetaDerivativeDenominator c 0 0 = c ^ 4 := by
    unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
      sixVertexDelta
    rw [Real.cos_zero, Real.sin_zero]
    ring
  rw [sixVertexThetaLeftDerivAtZero, hint, hden]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
  field_simp [hc2]
  unfold sixVertexDelta
  ring



theorem neg_two_lt_sixVertexThetaLeftDerivAtZero
    {c : Real} (hc : 2 < c) (y : Real) :
    -2 < sixVertexThetaLeftDerivAtZero c y := by
  let a : Real := -sixVertexDelta c
  let t : Real := Real.cos y
  have ha : 1 < a := by
    dsimp [a]
    nlinarith [sixVertexDelta_lt_neg_one hc]
  have htLower : -1 <= t := Real.neg_one_le_cos y
  have htUpper : t <= 1 := Real.cos_le_one y
  have hsin := Real.sin_sq_add_cos_sq y
  have hden : 0 < sixVertexThetaDerivativeDenominator c 0 y :=
    sixVertexThetaDerivativeDenominator_pos hc 0 y
  have hgap :
      2 * a * (t + a) < sixVertexThetaDerivativeDenominator c 0 y := by
    dsimp [a, t, sixVertexThetaDerivativeDenominator,
      sixVertexThetaDenominator]
    simp only [Real.cos_zero, Real.sin_zero, zero_sub]
    nlinarith [mul_pos (by linarith : 0 < a + 1)
      (by linarith : 0 < a + 1 + Real.cos y)]
  unfold sixVertexThetaLeftDerivAtZero sixVertexBetheIntegratingFactor
  rw [lt_div_iff₀ hden]
  dsimp [a, t] at hgap
  nlinarith


def sixVertexZeroPhaseBethePrefactor
    {n : Nat} (c : Real) (N : Nat) (p : Fin n -> Real) (ell : Fin n) : Real :=
  2 + c ^ 2 * ((N : Real) - 1) +
    c ^ 2 * ∑ j ∈ (Finset.univ.erase ell),
      sixVertexThetaLeftDerivAtZero c (p j)



theorem sixVertexZeroPhaseBethePrefactor_eq
    {n : Nat} {c : Real} (hc : 2 < c) (N : Nat)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    sixVertexZeroPhaseBethePrefactor c N p ell =
      c ^ 2 * ((N : Real) +
        ∑ j, sixVertexThetaLeftDerivAtZero c (p j)) := by
  have hc0 : c ≠ 0 := by linarith
  have hsplit :
      (∑ j, sixVertexThetaLeftDerivAtZero c (p j)) =
        sixVertexThetaLeftDerivAtZero c (p ell) +
          ∑ j ∈ (Finset.univ.erase ell),
            sixVertexThetaLeftDerivAtZero c (p j) := by
    have herase := Finset.sum_erase_add Finset.univ
      (fun j => sixVertexThetaLeftDerivAtZero c (p j))
      (Finset.mem_univ ell)
    rw [← herase]
    ring
  rw [hsplit, hell, sixVertexThetaLeftDerivAtZero_self hc]
  unfold sixVertexZeroPhaseBethePrefactor
  field_simp [hc0]
  ring

theorem sixVertexZeroPhaseBethePrefactor_pos
    {n N : Nat} {c : Real} (hc : 2 < c) (hhalf : 2 * n <= N)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    0 < sixVertexZeroPhaseBethePrefactor c N p ell := by
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨ell, Finset.mem_univ ell⟩
  have hsum : ∑ _j : Fin n, (-2 : Real) <
      ∑ j : Fin n, sixVertexThetaLeftDerivAtZero c (p j) := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact (neg_two_lt_sixVertexThetaLeftDerivAtZero hc (p j)).le
    · obtain ⟨j, hj⟩ := hnonempty
      exact ⟨j, hj, neg_two_lt_sixVertexThetaLeftDerivAtZero hc (p j)⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  rw [sixVertexZeroPhaseBethePrefactor_eq hc N p ell hell]
  have hn : (2 : Real) * n <= N := by exact_mod_cast hhalf
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos (by linarith)
  apply mul_pos hc2
  linarith

theorem sixVertexThetaLeftDerivAtZero_neg
    {c : Real} (hc : 2 < c) (y : Real) :
    sixVertexThetaLeftDerivAtZero c y < 0 := by
  exact sixVertexTheta_left_deriv_neg hc 0 y

theorem sixVertexZeroPhaseBethePrefactor_bounds
    {n N : Nat} {c : Real} (hc : 2 < c)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    c ^ 2 * ((N : Real) - 2 * (n : Real)) <
        sixVertexZeroPhaseBethePrefactor c N p ell ∧
      sixVertexZeroPhaseBethePrefactor c N p ell <= c ^ 2 * (N : Real) := by
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨ell, Finset.mem_univ ell⟩
  have hlower : ∑ _j : Fin n, (-2 : Real) <
      ∑ j : Fin n, sixVertexThetaLeftDerivAtZero c (p j) := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact (neg_two_lt_sixVertexThetaLeftDerivAtZero hc (p j)).le
    · obtain ⟨j, hj⟩ := hnonempty
      exact ⟨j, hj, neg_two_lt_sixVertexThetaLeftDerivAtZero hc (p j)⟩
  have hupper :
      ∑ j : Fin n, sixVertexThetaLeftDerivAtZero c (p j) <= 0 := by
    exact Finset.sum_nonpos fun j hj =>
      (sixVertexThetaLeftDerivAtZero_neg hc (p j)).le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hlower
  rw [sixVertexZeroPhaseBethePrefactor_eq hc N p ell hell]
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos (by linarith)
  constructor
  · exact mul_lt_mul_of_pos_left (by linarith) hc2
  · exact mul_le_mul_of_nonneg_left (by linarith) hc2.le



def sixVertexZeroPhaseBetheEigenvalueCandidate
    {n : Nat} (c : Real) (N : Nat) (p : Fin n -> Real) (ell : Fin n) : Complex :=
  (sixVertexZeroPhaseBethePrefactor c N p ell : Complex) *
    ∏ j ∈ (Finset.univ.erase ell),
      sixVertexBetheM c (sixVertexBethePhase (p j))


def SixVertexCoordinateBetheZeroPhaseEigenrelation
    {N n : Nat} (c : Real) (p : Fin n -> Real) (ell : Fin n) : Prop :=
  (sixVertexSectorTransferComplex N n c).mulVec
      (sixVertexCoordinateBetheWave c p) =
    sixVertexZeroPhaseBetheEigenvalueCandidate c N p ell •
      sixVertexCoordinateBetheWave c p




theorem sixVertexCoordinateBetheZeroPhaseEigenrelation_one
    {N : Nat} (c : Real) (p : Fin 1 -> Real) (hp : p 0 = 0) :
    SixVertexCoordinateBetheZeroPhaseEigenrelation (N := N) c p 0 := by
  classical
  let e := sixVertexOneSectorEquiv N
  unfold SixVertexCoordinateBetheZeroPhaseEigenrelation
  funext x
  rw [sixVertexSectorTransferComplex_mulVec_apply]
  have heval (y : SixVertexSector N 1) :
      e y = sixVertexSectorPosition y 0 := rfl
  have hreindex :
      (∑ y, (sixVertexSectorTransfer N 1 c x y : Complex) *
          sixVertexCoordinateBetheWave c p y) =
        ∑ i : Fin N, if e x = i then (2 : Complex) else (c : Complex) ^ 2 := by
    apply Fintype.sum_equiv e
    intro y
    rw [sixVertexSectorTransfer_one_apply,
      sixVertexCoordinateBetheWave_one, hp]
    simp only [sixVertexBethePhase, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_pow, mul_one]
    by_cases hxy : x = y
    · subst y
      simp [heval]
    · have hpos : sixVertexSectorPosition x 0 ≠
          sixVertexSectorPosition y 0 := by
        intro h
        apply hxy
        apply e.injective
        simpa [heval] using h
      simp [hxy, hpos, heval]
  rw [hreindex]
  have hsum :
      (∑ i : Fin N, if e x = i then (2 : Complex) else (c : Complex) ^ 2) =
        2 + (N - 1 : Nat) * (c : Complex) ^ 2 := by
    by_cases hN : N = 0
    · subst N
      exact Fin.elim0 (e x)
    · have hrewrite :
          (∑ i : Fin N, if e x = i then (2 : Complex) else (c : Complex) ^ 2) =
            ∑ i : Fin N,
              ((if e x = i then 2 - (c : Complex) ^ 2 else 0) +
                (c : Complex) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hxi : e x = i <;> simp [hxi]
      rw [hrewrite, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN)]
      push_cast
      ring
  rw [hsum]
  simp only [Pi.smul_apply, sixVertexCoordinateBetheWave_one, hp,
    sixVertexBethePhase, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    one_pow, smul_eq_mul, mul_one]
  unfold sixVertexZeroPhaseBetheEigenvalueCandidate
    sixVertexZeroPhaseBethePrefactor
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.erase_singleton, Finset.sum_empty, mul_zero, add_zero,
    Complex.ofReal_add, Complex.ofReal_ofNat, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_natCast,
    Complex.ofReal_one, Finset.prod_empty, mul_one, add_right_inj]
  have hNpos : 0 < N := by
    have := (sixVertexSectorPosition x 0).isLt
    omega
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hNpos.ne')]
  push_cast
  ring



def sixVertexZeroPhaseBetheEigenvalueValue
    {n : Nat} (c : Real) (N : Nat) (p : Fin n -> Real) (ell : Fin n) : Real :=
  sixVertexZeroPhaseBethePrefactor c N p ell *
    ∏ j ∈ (Finset.univ.erase ell),
      ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖



theorem norm_sixVertexZeroPhaseBetheEigenvalueCandidate
    {n N : Nat} {c : Real} (hc : 2 < c) (hhalf : 2 * n <= N)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    ‖sixVertexZeroPhaseBetheEigenvalueCandidate c N p ell‖ =
      sixVertexZeroPhaseBetheEigenvalueValue c N p ell := by
  have hpref := sixVertexZeroPhaseBethePrefactor_pos hc hhalf p ell hell
  unfold sixVertexZeroPhaseBetheEigenvalueCandidate
    sixVertexZeroPhaseBetheEigenvalueValue
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpref,
    norm_prod]

theorem sixVertexZeroPhaseBetheEigenvalueValue_pos
    {n N : Nat} {c : Real} (hc : 2 < c) (hhalf : 2 * n <= N)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    0 < sixVertexZeroPhaseBetheEigenvalueValue c N p ell := by
  unfold sixVertexZeroPhaseBetheEigenvalueValue
  apply mul_pos (sixVertexZeroPhaseBethePrefactor_pos hc hhalf p ell hell)
  apply Finset.prod_pos
  intro j hj
  exact norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc (p j))

theorem sixVertexZeroPhaseBetheEigenvalueValue_log
    {n N : Nat} {c : Real} (hc : 2 < c) (hhalf : 2 * n <= N)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    Real.log (sixVertexZeroPhaseBetheEigenvalueValue c N p ell) =
      Real.log (sixVertexZeroPhaseBethePrefactor c N p ell) +
        ∑ j ∈ (Finset.univ.erase ell),
          Real.log ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ := by
  have hpref := sixVertexZeroPhaseBethePrefactor_pos hc hhalf p ell hell
  have hnorm (j : Fin n) :
      ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sixVertexBetheM_phase_ne_zero hc (p j))
  unfold sixVertexZeroPhaseBetheEigenvalueValue
  rw [Real.log_mul hpref.ne' (Finset.prod_ne_zero_iff.mpr
    (fun j hj => hnorm j)), Real.log_prod]
  exact fun j hj => hnorm j


def sixVertexFixedOddChargeBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (r k : Nat) : Real :=
  sixVertexZeroPhaseBetheEigenvalueValue c (sixVertexFourWidth r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)

def sixVertexFixedOddChargeBetheEigenvalueCandidate
    {c : Real} (hc : 2 < c) (r k : Nat) : Complex :=
  sixVertexZeroPhaseBetheEigenvalueCandidate c (sixVertexFourWidth r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)

theorem norm_sixVertexFixedOddChargeBetheEigenvalueCandidate
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    ‖sixVertexFixedOddChargeBetheEigenvalueCandidate hc r k‖ =
      sixVertexFixedOddChargeBetheEigenvalueValue hc r k := by
  exact norm_sixVertexZeroPhaseBetheEigenvalueCandidate hc
    (sixVertexFixedChargeBetheParticleCount_twice_le r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)



theorem sixVertexFixedOddChargeBethePrefactor_div_width_eq
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexFixedChargeBetheCentralIndex r k) /
          (sixVertexFourWidth r k : Real) =
      c ^ 2 * (1 +
        (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real)) := by
  rw [sixVertexZeroPhaseBethePrefactor_eq hc _ _ _
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)]
  have hN : (sixVertexFourWidth r k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos r k).ne'
  field_simp [hN]

theorem sixVertexFixedOddChargeBethePrefactor_bounds
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    c ^ 2 * (2 * (r : Real)) <
        sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheRoots hc r k)
          (sixVertexFixedChargeBetheCentralIndex r k) ∧
      sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheRoots hc r k)
          (sixVertexFixedChargeBetheCentralIndex r k) <=
        c ^ 2 * (sixVertexFourWidth r k : Real) := by
  have hb := sixVertexZeroPhaseBethePrefactor_bounds
    (N := sixVertexFourWidth r k) hc
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)
  have hcount : (sixVertexFourWidth r k : Real) -
      2 * (sixVertexFixedChargeBetheParticleCount r k : Real) =
        2 * (r : Real) := by
    rw [sixVertexFixedChargeBetheParticleCount_eq, sixVertexFourWidth]
    push_cast
    ring
  rwa [hcount] at hb


theorem sixVertexFixedOddChargeEmpiricalThetaDerivative_bounds
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    -(1 : Real) + 2 * (r : Real) / (sixVertexFourWidth r k : Real) <
        (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real) ∧
      (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real) <= 0 := by
  have hb := sixVertexFixedOddChargeBethePrefactor_bounds hc hr k
  have heq := sixVertexFixedOddChargeBethePrefactor_div_width_eq hc hr k
  have hN : (0 : Real) < sixVertexFourWidth r k := by
    exact_mod_cast sixVertexFourWidth_pos r k
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos (by linarith)
  constructor
  · rw [← sub_pos, show
        (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real) -
          (-(1 : Real) + 2 * (r : Real) /
            (sixVertexFourWidth r k : Real)) =
        (1 + (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real)) -
          2 * (r : Real) / (sixVertexFourWidth r k : Real) by ring]
    have hdiv := div_lt_div_of_pos_right hb.1 hN
    rw [heq] at hdiv
    have hdiv' : c ^ 2 *
          (2 * (r : Real) / (sixVertexFourWidth r k : Real)) <
        c ^ 2 * (1 + (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real)) := by
      convert hdiv using 1 <;> ring
    have hcancel : 2 * (r : Real) / (sixVertexFourWidth r k : Real) <
        1 + (∑ j, sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j)) /
            (sixVertexFourWidth r k : Real) :=
      lt_of_mul_lt_mul_left hdiv' hc2.le
    exact sub_pos.mpr hcancel
  · have hneg (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
        sixVertexThetaLeftDerivAtZero c
          (sixVertexFixedChargeBetheRoots hc r k j) <= 0 :=
      (sixVertexThetaLeftDerivAtZero_neg hc _).le
    exact div_nonpos_of_nonpos_of_nonneg
      (Finset.sum_nonpos fun j hj => hneg j) hN.le

theorem sixVertexFixedOddChargeBetheEigenvalueValue_pos
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    0 < sixVertexFixedOddChargeBetheEigenvalueValue hc r k := by
  exact sixVertexZeroPhaseBetheEigenvalueValue_pos hc
    (sixVertexFixedChargeBetheParticleCount_twice_le r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)

theorem sixVertexFixedOddChargeBetheEigenvalueValue_log
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    Real.log (sixVertexFixedOddChargeBetheEigenvalueValue hc r k) =
      Real.log (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexFixedChargeBetheCentralIndex r k)) +
      ∑ j ∈ (Finset.univ.erase
          (sixVertexFixedChargeBetheCentralIndex r k)),
        Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j))‖ := by
  exact sixVertexZeroPhaseBetheEigenvalueValue_log hc
    (sixVertexFixedChargeBetheParticleCount_twice_le r k)
    (sixVertexFixedChargeBetheRoots hc r k)
    (sixVertexFixedChargeBetheCentralIndex r k)
    (sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k)

end

end StatMech.FrontierD
