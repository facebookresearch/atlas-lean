/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalFixedOffset
import Code.FrontierD.SixVertexBetheOffsetSymmetry





namespace StatMech.FrontierD

open Finset

noncomputable section

theorem sixVertexCanonicalEvenHalfIndex_rev (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCanonicalEvenHalfIndex s k j.rev =
      (sixVertexCanonicalEvenHalfIndex s k j).rev := by
  apply Fin.ext
  simp [sixVertexCanonicalEvenHalfIndex, Fin.rev]
  omega

theorem sixVertexCanonicalEvenAlignedHalfRoots_rev
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCanonicalEvenAlignedHalfRoots hc s k j.rev =
      -sixVertexCanonicalEvenAlignedHalfRoots hc s k j := by
  unfold sixVertexCanonicalEvenAlignedHalfRoots
  rw [sixVertexCanonicalEvenHalfIndex_rev]
  exact (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc (2 * s + k)).2.1 _

theorem sixVertexCanonicalEvenChargeOffset_rev
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCanonicalEvenChargeOffset hc s k j.rev =
      -sixVertexCanonicalEvenChargeOffset hc s k j := by
  unfold sixVertexCanonicalEvenChargeOffset
  rw [hfixed.1.2.1 j, sixVertexCanonicalEvenAlignedHalfRoots_rev]
  ring

theorem sixVertexCanonicalOddLowerHalfIndex_rev (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    sixVertexCanonicalOddLowerHalfIndex s k j.rev =
      (sixVertexCanonicalOddUpperHalfIndex s k j).rev := by
  apply Fin.ext
  simp [sixVertexCanonicalOddLowerHalfIndex,
    sixVertexCanonicalOddUpperHalfIndex, Fin.rev]
  omega

theorem sixVertexCanonicalOddUpperHalfIndex_rev (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    sixVertexCanonicalOddUpperHalfIndex s k j.rev =
      (sixVertexCanonicalOddLowerHalfIndex s k j).rev := by
  apply Fin.ext
  simp [sixVertexCanonicalOddLowerHalfIndex,
    sixVertexCanonicalOddUpperHalfIndex, Fin.rev]
  omega

theorem sixVertexCanonicalOddAlignedHalfRoots_rev
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    sixVertexCanonicalOddAlignedHalfRoots hc s k j.rev =
      -sixVertexCanonicalOddAlignedHalfRoots hc s k j := by
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  have hp := (sixVertexCanonicalDensityPerronBetheRoots_mem_open
    hc (2 * s + 1 + k)).2.1
  unfold sixVertexCanonicalOddAlignedHalfRoots
  rw [sixVertexCanonicalOddLowerHalfIndex_rev,
    sixVertexCanonicalOddUpperHalfIndex_rev, hp, hp]
  ring

theorem sixVertexCanonicalOddChargeOffset_rev
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedOddChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k))
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    sixVertexCanonicalOddChargeOffset hc s k j.rev =
      -sixVertexCanonicalOddChargeOffset hc s k j := by
  unfold sixVertexCanonicalOddChargeOffset
  rw [hfixed.1.2.1 j, sixVertexCanonicalOddAlignedHalfRoots_rev]
  ring



theorem sum_weightedOffsetError_div_weight_density_eq_zero_of_rev
    {c : Real} {N n : Nat} {p eps : Fin n -> Real}
    (hp : forall j, p j.rev = -p j)
    (heps : forall j, eps j.rev = -eps j)
    {tau : Real -> Real} (htau : Function.Odd tau) (a : Real) :
    ∑ j, (sixVertexFiniteRootDensity c N n p (p j) * eps j -
        a * tau (p j)) /
      (sixVertexRootDensityWeight c (p j) *
        sixVertexFiniteRootDensity c N n p (p j)) = 0 := by
  let rho := sixVertexFiniteRootDensity c N n p
  let f : Fin n -> Real := fun j =>
    (rho (p j) * eps j - a * tau (p j)) /
      (sixVertexRootDensityWeight c (p j) * rho (p j))
  change ∑ j, f j = 0
  apply sum_fin_eq_zero_of_rev_neg
  intro j
  have hrho := sixVertexFiniteRootDensity_neg_of_symmetric
    (c := c) (N := N) (p := p) hp (p j)
  change rho (-p j) = rho (p j) at hrho
  dsimp [f]
  change (rho (p j.rev) * eps j.rev - a * tau (p j.rev)) /
      (sixVertexRootDensityWeight c (p j.rev) * rho (p j.rev)) = _
  rw [hp, heps, htau, sixVertexRootDensityWeight_neg, hrho]
  ring

theorem sum_sixVertexCanonicalEvenWeightedOffsetError_eq_zero
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedEvenChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
    {tau : Real -> Real} (htau : Function.Odd tau) (a : Real) :
    ∑ j, (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1))
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) *
        sixVertexCanonicalEvenChargeOffset hc s k j -
        a * tau (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)) /
      (sixVertexRootDensityWeight c
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) *
        sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1))
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)) = 0 := by
  exact sum_weightedOffsetError_div_weight_density_eq_zero_of_rev
    hfixed.1.2.1 (sixVertexCanonicalEvenChargeOffset_rev hc s k hfixed)
      htau a

theorem sum_sixVertexCanonicalOddWeightedOffsetError_eq_zero
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexFixedOddChargePerronBranchWitness c s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k))
    {tau : Real -> Real} (htau : Function.Odd tau) (a : Real) :
    ∑ j, (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1))
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) *
        sixVertexCanonicalOddChargeOffset hc s k j -
        a * tau (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)) /
      (sixVertexRootDensityWeight c
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) *
        sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1))
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)) = 0 := by
  exact sum_weightedOffsetError_div_weight_density_eq_zero_of_rev
    hfixed.1.2.1 (sixVertexCanonicalOddChargeOffset_rev hc s k hfixed)
      htau a

end

end StatMech.FrontierD
