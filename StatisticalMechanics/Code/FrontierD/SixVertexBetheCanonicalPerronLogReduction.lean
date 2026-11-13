/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalPerronBulk





open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheLogObservable (c p : Real) : Real :=
  Real.log ‖sixVertexBetheM c (sixVertexBethePhase p)‖

theorem sixVertexBetheLogObservable_neg (c p : Real) :
    sixVertexBetheLogObservable c (-p) =
      sixVertexBetheLogObservable c p := by
  unfold sixVertexBetheLogObservable
  rw [sixVertexBetheM_phase_neg]
  simp

theorem sum_sixVertexBetheLogObservable_evenSymmetricLift
    (c : Real) (m : Nat) (q : Fin m -> Real) :
    (∑ i : Fin (m + m),
        sixVertexBetheLogObservable c (sixVertexEvenSymmetricLift m q i)) =
      2 * ∑ j : Fin m, sixVertexBetheLogObservable c (q j) := by
  rw [Fin.sum_univ_add]
  simp only [sixVertexEvenSymmetricLift_castAdd,
    sixVertexEvenSymmetricLift_natAdd, sixVertexBetheLogObservable_neg]
  have hrev :
      (∑ j : Fin m, sixVertexBetheLogObservable c (q j.rev)) =
        ∑ j : Fin m, sixVertexBetheLogObservable c (q j) := by
    apply Fintype.sum_equiv Fin.revPerm
    intro j
    rfl
  rw [hrev]
  ring



theorem sixVertexCanonicalDensityPerronEmpiricalLogObservable_eq_rootAverage
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexCanonicalDensityPerronEmpiricalObservable hc
        (sixVertexBetheLogObservable c) k =
      sixVertexSymmetricBetheRootAverage c
        (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k := by
  let p := sixVertexCanonicalDensityPerronBetheRoots hc k
  let q := sixVertexCanonicalDensityPerronPositiveHalfRoots hc k
  have hlift : sixVertexEvenSymmetricLift (k + 1) q = p := by
    exact sixVertexEvenSymmetricLift_projection (k + 1)
      (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k).2.1
  have hsum := sum_sixVertexBetheLogObservable_evenSymmetricLift
    c (k + 1) q
  rw [hlift] at hsum
  unfold sixVertexCanonicalDensityPerronEmpiricalObservable
    sixVertexSymmetricBetheRootAverage
    sixVertexCanonicalDensityPerronPositiveHalfRootFamily
    sixVertexBetheLogObservable
  exact congrArg (fun x : Real => x / (sixVertexFourWidth 0 k : Real)) hsum



theorem sixVertexCentralWidthRate_eventuallyEq_canonicalDensityEmpiricalLog
    {c : Real} (hc : 2 < c) :
    sixVertexCentralWidthRate c =ᶠ[atTop] fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexBetheLogObservable c) k := by
  filter_upwards
    [eventually_sixVertexLambdaAlongFour_eq_canonicalDensityPerronValue hc]
      with k hk
  rw [sixVertexCanonicalDensityPerronEmpiricalLogObservable_eq_rootAverage]
  unfold sixVertexCentralWidthRate
  rw [hk, sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexCanonicalDensityPerronPositiveHalfRootFamily
  ring



theorem sixVertexCentralWidthRate_tendsto_iff_canonicalDensityEmpiricalLog
    {c a : Real} (hc : 2 < c) :
    Tendsto (sixVertexCentralWidthRate c) atTop (nhds a) ↔
      Tendsto (sixVertexCanonicalDensityPerronEmpiricalObservable hc
        (sixVertexBetheLogObservable c)) atTop (nhds a) := by
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hwidthReal : Tendsto (fun k =>
      (sixVertexFourWidth 0 k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidth
  have hfinite : Tendsto (fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) :=
    hwidthReal.const_div_atTop (Real.log 2)
  have heq :=
    sixVertexCentralWidthRate_eventuallyEq_canonicalDensityEmpiricalLog hc
  constructor
  · intro h
    have hsum : Tendsto (fun k =>
        Real.log 2 / (sixVertexFourWidth 0 k : Real) +
          sixVertexCanonicalDensityPerronEmpiricalObservable hc
            (sixVertexBetheLogObservable c) k) atTop (nhds a) :=
      h.congr' heq
    simpa using hsum.sub hfinite
  · intro h
    have hsum : Tendsto (fun k =>
        Real.log 2 / (sixVertexFourWidth 0 k : Real) +
          sixVertexCanonicalDensityPerronEmpiricalObservable hc
            (sixVertexBetheLogObservable c) k) atTop (nhds a) := by
      simpa using hfinite.add h
    exact hsum.congr' heq.symm

end

end StatMech.FrontierD
