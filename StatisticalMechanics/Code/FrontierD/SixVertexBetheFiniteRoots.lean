/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheVariational
import Code.FrontierD.SixVertexBetheScattering
import Code.FrontierD.SixVertexCoordinateBethe
import Code.FrontierD.SixVertexBetheThermodynamicReduction

namespace StatMech.FrontierD

noncomputable section


def sixVertexHalfFilledBetheRoots
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    Fin ((k + 1) + (k + 1)) → ℝ :=
  sixVertexChosenBetheSolution hc (N := sixVertexFourWidth 0 k)
    (n := (k + 1) + (k + 1)) (by unfold sixVertexFourWidth; omega)



def sixVertexPositiveHalfBetheRoots
    {c : ℝ} (hc : 2 < c) (k : ℕ) : Fin (k + 1) → ℝ :=
  fun j => sixVertexHalfFilledBetheRoots hc k (Fin.natAdd (k + 1) j)



def sixVertexPositiveHalfBetheRootFamily
    {c : ℝ} (hc : 2 < c) : SixVertexSymmetricHalfFilledRoots :=
  fun k => sixVertexPositiveHalfBetheRoots hc k

theorem sixVertexHalfFilledBetheRoots_mem_open
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    SixVertexOpenRootSimplex (sixVertexHalfFilledBetheRoots hc k) := by
  exact sixVertexChosenBetheSolution_mem_open hc
    (N := sixVertexFourWidth 0 k) (n := (k + 1) + (k + 1))
    (by unfold sixVertexFourWidth; omega)

theorem sixVertexHalfFilledBetheRoots_is_solution
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) := by
  exact sixVertexChosenBetheSolution_is_solution hc
    (N := sixVertexFourWidth 0 k) (n := (k + 1) + (k + 1))
    (by unfold sixVertexFourWidth; omega)

theorem sixVertexHalfFilledBetheRoots_is_multiplicativeSolution
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    SixVertexSatisfiesMultiplicativeBetheEquations c
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
      (sixVertexHalfFilledBetheRoots hc k) :=
  (sixVertexHalfFilledBetheRoots_is_solution hc k).multiplicative

theorem sixVertexHalfFilledBetheRoots_phase_ne_one
    {c : ℝ} (hc : 2 < c) (k : ℕ)
    (j : Fin ((k + 1) + (k + 1))) :
    sixVertexBethePhase (sixVertexHalfFilledBetheRoots hc k j) ≠ 1 := by
  have hopen := sixVertexHalfFilledBetheRoots_mem_open hc k
  intro hphase
  have hphase0 : sixVertexBethePhase (sixVertexHalfFilledBetheRoots hc k j) =
      sixVertexBethePhase 0 := by
    simpa [sixVertexBethePhase] using hphase
  have hjzero := sixVertexBethePhase_injective_on_Ioo (hopen.2.2 j)
    ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩ hphase0
  have hrevzero : sixVertexHalfFilledBetheRoots hc k j.rev = 0 := by
    rw [hopen.2.1, hjzero, neg_zero]
  have hjrev : j.rev = j := hopen.1.injective (hrevzero.trans hjzero.symm)
  have hval := congrArg Fin.val hjrev
  simp only [Fin.rev, Fin.val_mk] at hval
  omega

theorem sixVertexPositiveHalfBetheRoots_pos
    {c : ℝ} (hc : 2 < c) (k : ℕ) (j : Fin (k + 1)) :
    0 < sixVertexPositiveHalfBetheRoots hc k j := by
  let p := sixVertexHalfFilledBetheRoots hc k
  let i : Fin ((k + 1) + (k + 1)) := Fin.natAdd (k + 1) j
  have hopen := sixVertexHalfFilledBetheRoots_mem_open hc k
  have hlt : i.rev < i := by
    rw [Fin.lt_def]
    dsimp [i]
    omega
  have hmono := hopen.1 hlt
  have hsymm := hopen.2.1 i
  change p i.rev < p i at hmono
  change p i.rev = -p i at hsymm
  change 0 < p i
  rw [hsymm] at hmono
  linarith

theorem sixVertexPositiveHalfBetheRoots_lt_pi
    {c : ℝ} (hc : 2 < c) (k : ℕ) (j : Fin (k + 1)) :
    sixVertexPositiveHalfBetheRoots hc k j < Real.pi :=
  (sixVertexHalfFilledBetheRoots_mem_open hc k).2.2
    (Fin.natAdd (k + 1) j) |>.2

theorem sixVertexPositiveHalfBetheRoots_strictMono
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    StrictMono (sixVertexPositiveHalfBetheRoots hc k) := by
  intro i j hij
  exact (sixVertexHalfFilledBetheRoots_mem_open hc k).1
    ((Fin.natAdd_lt_natAdd_iff (k + 1)).mpr hij)

theorem prod_sixVertexHalfFilledBetheRoots
    {c : ℝ} (hc : 2 < c) (k : ℕ) (f : ℝ → ℂ) :
    (∏ i, f (sixVertexHalfFilledBetheRoots hc k i)) =
      (∏ j, f (sixVertexPositiveHalfBetheRoots hc k j)) *
        ∏ j, f (-sixVertexPositiveHalfBetheRoots hc k j) := by
  let p := sixVertexHalfFilledBetheRoots hc k
  let q := sixVertexPositiveHalfBetheRoots hc k
  have hsymm := (sixVertexHalfFilledBetheRoots_mem_open hc k).2.1
  have hfirst : (∏ i : Fin (k + 1), f (p (Fin.castAdd (k + 1) i))) =
      ∏ i : Fin (k + 1), f (-q i) := by
    calc
      (∏ i : Fin (k + 1), f (p (Fin.castAdd (k + 1) i))) =
          ∏ i : Fin (k + 1), f (-q i.rev) := by
        apply Finset.prod_congr rfl
        intro i _
        have hi := hsymm (Fin.castAdd (k + 1) i).rev
        rw [Fin.rev_rev] at hi
        change p (Fin.castAdd (k + 1) i) =
          -p (Fin.castAdd (k + 1) i).rev at hi
        rw [hi]
        congr 2
        simp [q, sixVertexPositiveHalfBetheRoots, p, Fin.rev_castAdd]
      _ = ∏ i : Fin (k + 1), f (-q i) := by
        simpa using (Equiv.prod_comp Fin.revPerm (fun i => f (-q i)))
  change (∏ i, f (p i)) = _
  rw [Fin.prod_univ_add, hfirst]
  change (∏ i, f (-q i)) * (∏ i, f (q i)) =
    (∏ i, f (q i)) * ∏ i, f (-q i)
  rw [mul_comm]

theorem sixVertexHalfFilledBetheEigenvalueCandidate_eq_symmetric
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    sixVertexBetheEigenvalueCandidate c (sixVertexHalfFilledBetheRoots hc k) =
      sixVertexSymmetricBetheEigenvalueCandidate c
        (sixVertexPositiveHalfBetheRoots hc k) := by
  unfold sixVertexBetheEigenvalueCandidate
    sixVertexSymmetricBetheEigenvalueCandidate
  rw [prod_sixVertexHalfFilledBetheRoots hc k
      (fun r => sixVertexBetheL c (sixVertexBethePhase r)),
    prod_sixVertexHalfFilledBetheRoots hc k
      (fun r => sixVertexBetheM c (sixVertexBethePhase r)),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]

theorem sixVertexHalfFilledBetheEigenvalueCandidate_eq_value
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    sixVertexBetheEigenvalueCandidate c (sixVertexHalfFilledBetheRoots hc k) =
      (sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc k) : ℂ) := by
  rw [sixVertexHalfFilledBetheEigenvalueCandidate_eq_symmetric hc k,
    sixVertexSymmetricBetheEigenvalueCandidate_eq_value]

theorem sixVertexHalfFilledBetheEigenvalueCandidate_isPositiveReal
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    (sixVertexBetheEigenvalueCandidate c
        (sixVertexHalfFilledBetheRoots hc k)).im = 0 ∧
      0 < (sixVertexBetheEigenvalueCandidate c
        (sixVertexHalfFilledBetheRoots hc k)).re := by
  rw [sixVertexHalfFilledBetheEigenvalueCandidate_eq_symmetric hc k]
  exact sixVertexSymmetricBetheEigenvalueCandidate_isPositiveReal hc _



noncomputable def sixVertexHalfFilledBetheCandidateRate
    {c : ℝ} (hc : 2 < c) (k : ℕ) : ℝ :=
  Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexPositiveHalfBetheRoots hc k)) /
    (sixVertexFourWidth 0 k : ℝ)

theorem sixVertexHalfFilledBetheCandidateRate_eq_rootAverage
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    sixVertexHalfFilledBetheCandidateRate hc k =
      Real.log 2 / (sixVertexFourWidth 0 k : ℝ) +
        sixVertexSymmetricBetheRootAverage c
          (sixVertexPositiveHalfBetheRootFamily hc) k := by
  rw [sixVertexHalfFilledBetheCandidateRate,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexPositiveHalfBetheRootFamily
  ring

theorem sixVertexSelectedRootAverage_eq_logKernel
    {c : ℝ} (hc : 2 < c) (k : ℕ) :
    sixVertexSymmetricBetheRootAverage c
        (sixVertexPositiveHalfBetheRootFamily hc) k =
      (∑ j, Real.log
        (((c ^ 2 - 1) ^ 2 + 1 +
            2 * (c ^ 2 - 1) *
              Real.cos (sixVertexPositiveHalfBetheRoots hc k j)) /
          (2 - 2 * Real.cos (sixVertexPositiveHalfBetheRoots hc k j)))) /
        (sixVertexFourWidth 0 k : ℝ) := by
  have hlog (j : Fin (k + 1)) :=
    sixVertexBetheM_phase_log_norm c
      (sixVertexPositiveHalfBetheRoots hc k j)
      (sixVertexHalfFilledBetheRoots_phase_ne_one hc k
        (Fin.natAdd (k + 1) j))
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexPositiveHalfBetheRootFamily
  simp_rw [hlog]
  rw [Finset.mul_sum]
  apply congrArg (fun t : ℝ => t / (sixVertexFourWidth 0 k : ℝ))
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sixVertexSelectedLogKernel_pos
    {c : ℝ} (hc : 2 < c) (k : ℕ) (j : Fin (k + 1)) :
    0 < (((c ^ 2 - 1) ^ 2 + 1 +
          2 * (c ^ 2 - 1) *
            Real.cos (sixVertexPositiveHalfBetheRoots hc k j)) /
        (2 - 2 * Real.cos (sixVertexPositiveHalfBetheRoots hc k j))) := by
  let p := sixVertexPositiveHalfBetheRoots hc k j
  have hM := Complex.normSq_pos.mpr (sixVertexBetheM_phase_ne_zero hc p)
  have hphase := sixVertexHalfFilledBetheRoots_phase_ne_one hc k
    (Fin.natAdd (k + 1) j)
  rw [sixVertexBetheM_phase_normSq c p hphase] at hM
  exact hM

end

end StatMech.FrontierD
