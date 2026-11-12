/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexPerronAnalytic

open Filter Topology

namespace StatMech.FrontierD

noncomputable section


def sixVertexHalfFilledPerronNormalized (k : Nat) (c : Real) : Real :=
  sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) (by
        unfold sixVertexFourWidth
        omega) c /
    (c ^ 2 - 2) ^ ((k + 1) + (k + 1))



theorem analyticOnNhd_sixVertexHalfFilledPerronNormalized (k : Nat) :
    AnalyticOnNhd Real (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2) := by
  intro c hc
  change 2 < c at hc
  let N := sixVertexFourWidth 0 k
  let n := (k + 1) + (k + 1)
  have hn : n ≤ N := by
    dsimp [n, N, sixVertexFourWidth]
    omega
  have htop : AnalyticAt Real (sixVertexSectorTopEigenvalue N n hn) c :=
    analyticAt_sixVertexSectorTopEigenvalue hn (by linarith)
  have hscale : AnalyticAt Real
      (fun t : Real => (t ^ 2 - 2) ^ n) c := by fun_prop
  have hscale_ne : (c ^ 2 - 2) ^ n ≠ 0 := by
    apply pow_ne_zero
    nlinarith
  simpa [sixVertexHalfFilledPerronNormalized, N, n] using
    htop.div hscale hscale_ne



def sixVertexHalfFilledCandidateKernelAt (k : Nat) (c : Real) : Real :=
  (2 * ∏ j : Fin (k + 1),
    (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) *
        Real.cos (sixVertexHalfFilledBetheRootAt k
          (Fin.natAdd (k + 1) j) c)) /
      (2 - 2 * Real.cos (sixVertexHalfFilledBetheRootAt k
        (Fin.natAdd (k + 1) j) c)))) /
    (c ^ 2 - 2) ^ ((k + 1) + (k + 1))

theorem sixVertexHalfFilledCandidateNormalized_eq_kernelAt
    (k : Nat) {c : Real} (hc : 2 < c) :
    sixVertexHalfFilledBetheCandidateNormalized k c =
      sixVertexHalfFilledCandidateKernelAt k c := by
  rw [sixVertexHalfFilledBetheCandidateNormalized, dif_pos hc]
  unfold sixVertexHalfFilledCandidateKernelAt
    sixVertexSymmetricBetheEigenvalueValue
  apply congrArg (fun x : Real => (2 * x) /
    (c ^ 2 - 2) ^ ((k + 1) + (k + 1)))
  apply Finset.prod_congr rfl
  intro j _
  rw [sixVertexHalfFilledBetheRootAt_eq hc]
  rw [← Complex.normSq_eq_norm_sq]
  exact sixVertexBetheM_phase_normSq c
    (sixVertexPositiveHalfBetheRoots hc k j)
    (sixVertexHalfFilledBetheRoots_phase_ne_one hc k
      (Fin.natAdd (k + 1) j))



theorem analyticOnNhd_sixVertexHalfFilledBetheCandidateNormalized_of_roots
    (k : Nat)
    (hroots : ∀ j : Fin (k + 1), AnalyticOnNhd Real
      (fun c => sixVertexHalfFilledBetheRootAt k
        (Fin.natAdd (k + 1) j) c) (Set.Ioi 2)) :
    AnalyticOnNhd Real (sixVertexHalfFilledBetheCandidateNormalized k)
      (Set.Ioi 2) := by
  have hkernel : AnalyticOnNhd Real (sixVertexHalfFilledCandidateKernelAt k)
      (Set.Ioi 2) := by
    intro c hc
    change 2 < c at hc
    have hroot (j : Fin (k + 1)) : AnalyticAt Real
        (fun t => sixVertexHalfFilledBetheRootAt k
          (Fin.natAdd (k + 1) j) t) c := hroots j c hc
    have hden (j : Fin (k + 1)) :
        2 - 2 * Real.cos (sixVertexHalfFilledBetheRootAt k
          (Fin.natAdd (k + 1) j) c) ≠ 0 := by
      have hqpos : 0 < sixVertexHalfFilledBetheRootAt k
          (Fin.natAdd (k + 1) j) c := by
        rw [sixVertexHalfFilledBetheRootAt_eq hc]
        exact sixVertexPositiveHalfBetheRoots_pos hc k j
      have hqpi : sixVertexHalfFilledBetheRootAt k
          (Fin.natAdd (k + 1) j) c < Real.pi := by
        rw [sixVertexHalfFilledBetheRootAt_eq hc]
        exact sixVertexPositiveHalfBetheRoots_lt_pi hc k j
      have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
        (show (0 : Real) ≤ 0 by rfl) hqpi.le hqpos
      rw [Real.cos_zero] at hcos
      nlinarith
    have hscale : c ^ 2 - 2 ≠ 0 := by nlinarith
    have hterm (j : Fin (k + 1)) : AnalyticAt Real
        (fun t =>
          (((t ^ 2 - 1) ^ 2 + 1 + 2 * (t ^ 2 - 1) *
              Real.cos (sixVertexHalfFilledBetheRootAt k
                (Fin.natAdd (k + 1) j) t)) /
            (2 - 2 * Real.cos (sixVertexHalfFilledBetheRootAt k
              (Fin.natAdd (k + 1) j) t)))) c := by
      apply AnalyticAt.div
      · fun_prop
      · fun_prop
      · exact hden j
    have hprod : AnalyticAt Real
        (fun t => ∏ j : Fin (k + 1),
          (((t ^ 2 - 1) ^ 2 + 1 + 2 * (t ^ 2 - 1) *
              Real.cos (sixVertexHalfFilledBetheRootAt k
                (Fin.natAdd (k + 1) j) t)) /
            (2 - 2 * Real.cos (sixVertexHalfFilledBetheRootAt k
              (Fin.natAdd (k + 1) j) t)))) c := by
      simpa using Finset.analyticAt_fun_prod Finset.univ
        (fun j _ => hterm j)
    have hscaleAnalytic : AnalyticAt Real
        (fun t : Real => (t ^ 2 - 2) ^ ((k + 1) + (k + 1))) c := by
      fun_prop
    unfold sixVertexHalfFilledCandidateKernelAt
    exact (analyticAt_const.mul hprod).div hscaleAnalytic
      (pow_ne_zero _ hscale)
  exact AnalyticOnNhd.congr isOpen_Ioi hkernel (fun c hc =>
    (sixVertexHalfFilledCandidateNormalized_eq_kernelAt k hc).symm)

theorem eventually_sixVertexHalfFilledCandidateNormalized_eq_perronNormalized
    (k : Nat) :
    sixVertexHalfFilledBetheCandidateNormalized k =ᶠ[atTop]
      sixVertexHalfFilledPerronNormalized k := by
  filter_upwards
    [eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top_vandermonde k]
      with c hc
  simpa only [sixVertexHalfFilledPerronNormalized] using hc



theorem sixVertexHalfFilledCandidateNormalized_eq_perronNormalized_of_analytic
    (k : Nat)
    (hcandidate : AnalyticOnNhd Real
      (sixVertexHalfFilledBetheCandidateNormalized k) (Set.Ioi 2))
    (hperron : AnalyticOnNhd Real
      (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2)) :
    Set.EqOn (sixVertexHalfFilledBetheCandidateNormalized k)
      (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2) :=
  AnalyticOnNhd.eqOn_Ioi_of_eventuallyEq_atTop hcandidate hperron
    (eventually_sixVertexHalfFilledCandidateNormalized_eq_perronNormalized k)



theorem sixVertexHalfFilledCandidate_eq_perron_of_analytic
    {c : Real} (hc : 2 < c) (k : Nat)
    (hcandidate : AnalyticOnNhd Real
      (sixVertexHalfFilledBetheCandidateNormalized k) (Set.Ioi 2))
    (hperron : AnalyticOnNhd Real
      (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2)) :
    sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc k) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega) c := by
  have heq := sixVertexHalfFilledCandidateNormalized_eq_perronNormalized_of_analytic
    k hcandidate hperron hc
  have hscale : (c ^ 2 - 2) ^ ((k + 1) + (k + 1)) ≠ 0 := by
    apply pow_ne_zero
    nlinarith
  unfold sixVertexHalfFilledBetheCandidateNormalized at heq
  rw [dif_pos hc] at heq
  unfold sixVertexHalfFilledPerronNormalized at heq
  exact (div_left_inj' hscale).mp heq


theorem sixVertexHasSymmetricBetheIdentification_of_analyticBranches
    {c : Real} (hc : 2 < c)
    (hcandidate : ∀ k, AnalyticOnNhd Real
      (sixVertexHalfFilledBetheCandidateNormalized k) (Set.Ioi 2))
    (hperron : ∀ k, AnalyticOnNhd Real
      (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2)) :
    SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc) := by
  intro k
  have heq := sixVertexHalfFilledCandidate_eq_perron_of_analytic hc k
    (hcandidate k) (hperron k)
  let N := sixVertexFourWidth 0 k
  let n := (k + 1) + (k + 1)
  let hleft : N / 2 ≤ N := Nat.div_le_self N 2
  let hright : n ≤ N := by
    dsimp [n, N, sixVertexFourWidth]
    omega
  have hidx : (⟨N / 2, hleft⟩ : {m : Nat // m ≤ N}) =
      ⟨n, hright⟩ := by
    apply Subtype.ext
    dsimp [n, N, sixVertexFourWidth]
    omega
  have htop := congrArg
    (fun q : {m : Nat // m ≤ N} =>
      sixVertexSectorTopEigenvalue N q.1 q.2 c) hidx
  change sixVertexSectorTopEigenvalue N (N / 2) _ c =
    sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexPositiveHalfBetheRoots hc k)
  exact htop.trans (by simpa [N, n] using heq.symm)




theorem sixVertexHasSymmetricBetheIdentification_of_analyticRoots
    {c : Real} (hc : 2 < c)
    (hroots : ∀ k (j : Fin (k + 1)), AnalyticOnNhd Real
      (fun t => sixVertexHalfFilledBetheRootAt k
        (Fin.natAdd (k + 1) j) t) (Set.Ioi 2)) :
    SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc) := by
  apply sixVertexHasSymmetricBetheIdentification_of_analyticBranches hc
  · intro k
    exact analyticOnNhd_sixVertexHalfFilledBetheCandidateNormalized_of_roots k
      (hroots k)
  · exact analyticOnNhd_sixVertexHalfFilledPerronNormalized

end

end StatMech.FrontierD
