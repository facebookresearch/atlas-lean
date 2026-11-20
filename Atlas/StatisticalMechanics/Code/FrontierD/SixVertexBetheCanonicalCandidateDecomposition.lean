/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalFixedDensityCandidate
import Code.FrontierD.SixVertexBetheOffsetLogSingularity










namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexCanonicalEvenCommonHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) : Real :=
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + k)
    ⟨j.val, by omega⟩

def sixVertexCanonicalEvenBoundaryHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (i : Fin s) : Real :=
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + k)
    ⟨s + k + 1 + i.val, by omega⟩

def sixVertexCanonicalOddLeftHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) : Real :=
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
    ⟨j.val, by omega⟩

def sixVertexCanonicalOddRightHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) : Real :=
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
    ⟨j.val + 1, by omega⟩

def sixVertexCanonicalOddMidpointHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) : Real :=
  (sixVertexCanonicalOddLeftHalfRoot hc s k j +
    sixVertexCanonicalOddRightHalfRoot hc s k j) / 2

def sixVertexCanonicalOddBoundaryHalfRoot
    {c : Real} (hc : 2 < c) (s k : Nat) (i : Fin (s + 1)) : Real :=
  sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
    ⟨s + k + 1 + i.val, by omega⟩

theorem sixVertexCanonicalEvenAlignedHalfRoots_positive
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexCanonicalEvenAlignedHalfRoots hc s k
        (Fin.natAdd (s + k + 1) j) =
      sixVertexCanonicalEvenCommonHalfRoot hc s k j := by
  unfold sixVertexCanonicalEvenAlignedHalfRoots
    sixVertexCanonicalEvenCommonHalfRoot
    sixVertexCanonicalDensityPerronPositiveHalfRoots
  congr 1
  apply Fin.ext
  simp [sixVertexCanonicalEvenHalfIndex, Fin.natAdd]
  omega

theorem sixVertexCanonicalOddAlignedHalfRoots_positive
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexCanonicalOddAlignedHalfRoots hc s k
        (sixVertexOddPositiveIndex (s + k + 1) j) =
      sixVertexCanonicalOddMidpointHalfRoot hc s k j := by
  unfold sixVertexCanonicalOddAlignedHalfRoots
    sixVertexCanonicalOddMidpointHalfRoot
    sixVertexCanonicalOddLeftHalfRoot
    sixVertexCanonicalOddRightHalfRoot
    sixVertexCanonicalDensityPerronPositiveHalfRoots
  congr 2
  · congr 1
    apply Fin.ext
    simp [sixVertexCanonicalOddLowerHalfIndex, sixVertexOddPositiveIndex,
      Fin.natAdd]
    omega
  · congr 1
    apply Fin.ext
    simp [sixVertexCanonicalOddUpperHalfIndex, sixVertexOddPositiveIndex,
      Fin.natAdd]
    omega

theorem sum_sixVertexCanonicalEvenHalfRoots_eq_common_add_boundary
    (f : Real -> Real) {c : Real} (hc : 2 < c) (s k : Nat) :
    (∑ j, f (sixVertexCanonicalDensityPerronPositiveHalfRoots hc
        (2 * s + k) j)) =
      (∑ j, f (sixVertexCanonicalEvenCommonHalfRoot hc s k j)) +
        ∑ i, f (sixVertexCanonicalEvenBoundaryHalfRoot hc s k i) := by
  let hsize : 2 * s + k + 1 = (s + k + 1) + s := by omega
  let g : Fin ((s + k + 1) + s) -> Real := fun j =>
    f (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + k)
      (Fin.cast hsize.symm j))
  calc
    (∑ j, f (sixVertexCanonicalDensityPerronPositiveHalfRoots hc
        (2 * s + k) j)) = ∑ j, g j := by
      simpa [g] using (Equiv.sum_comp (finCongr hsize) g)
    _ = (∑ j : Fin (s + k + 1), g (Fin.castAdd s j)) +
        ∑ i : Fin s, g (Fin.natAdd (s + k + 1) i) :=
      Fin.sum_univ_add g
    _ = _ := by
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro j _
        rfl
      · apply Finset.sum_congr rfl
        intro i _
        rfl

theorem sum_sixVertexCanonicalOddHalfRoots_eq_left_add_boundary
    (f : Real -> Real) {c : Real} (hc : 2 < c) (s k : Nat) :
    (∑ j, f (sixVertexCanonicalDensityPerronPositiveHalfRoots hc
        (2 * s + 1 + k) j)) =
      (∑ j, f (sixVertexCanonicalOddLeftHalfRoot hc s k j)) +
        ∑ i, f (sixVertexCanonicalOddBoundaryHalfRoot hc s k i) := by
  let hsize : 2 * s + 1 + k + 1 = (s + k + 1) + (s + 1) := by omega
  let g : Fin ((s + k + 1) + (s + 1)) -> Real := fun j =>
    f (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)
      (Fin.cast hsize.symm j))
  calc
    (∑ j, f (sixVertexCanonicalDensityPerronPositiveHalfRoots hc
        (2 * s + 1 + k) j)) = ∑ j, g j := by
      simpa [g] using (Equiv.sum_comp (finCongr hsize) g)
    _ = (∑ j : Fin (s + k + 1), g (Fin.castAdd (s + 1) j)) +
        ∑ i : Fin (s + 1), g (Fin.natAdd (s + k + 1) i) :=
      Fin.sum_univ_add g
    _ = _ := by
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro j _
        rfl
      · apply Finset.sum_congr rfl
        intro i _
        rfl

theorem abs_sixVertexCanonicalEvenBoundaryHalfRoot_sub_pi_le
    {c : Real} (hc : 2 < c) (s k : Nat)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + k))
        ((2 * s + k + 1) + (2 * s + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)) x)
    (i : Fin s) :
    |sixVertexCanonicalEvenBoundaryHalfRoot hc s k i - Real.pi| <=
      (s : Real) /
        ((sixVertexFourWidth 0 (2 * s + k) : Real) * lower) := by
  let t := 2 * s + k
  let m := s + k + 1
  let L := t + 1
  let H := L + L
  let N := sixVertexFourWidth 0 t
  let p := sixVertexCanonicalDensityPerronBetheRoots hc t
  let q : Fin H := ⟨m + i.val + L, by dsimp [H, L, m, t]; omega⟩
  have hN : 0 < N := sixVertexFourWidth_pos 0 t
  have hhalf : N = 2 * H := by
    dsimp [N, H, L, t]
    unfold sixVertexFourWidth
    omega
  have hopen : SixVertexOpenRootSimplex p :=
    sixVertexCanonicalDensityPerronBetheRoots_mem_open hc t
  have hsol : SixVertexSatisfiesBetheEquations c N H p :=
    sixVertexCanonicalDensityPerronBetheRoots_is_solution hc t
  have h := sixVertexBetheSolution_last_endpoint_le_of_finiteDensityLower
    hc hN hhalf hopen hsol hlower hdensity q
  have hindex : (((q.rev.val : Nat) : Real) + 1) <= s := by
    have hnat : q.rev.val + 1 <= s := by
      simp only [q, Fin.rev, Fin.val_mk]
      dsimp [H, L, m, t]
      omega
    exact_mod_cast hnat
  have hden : 0 <= (N : Real) * lower := by positivity
  have hroot : Real.pi - p q <= (s : Real) / ((N : Real) * lower) :=
    h.trans (div_le_div_of_nonneg_right hindex hden)
  change |_ - Real.pi| <= _
  rw [abs_of_nonpos]
  · simpa [sixVertexCanonicalEvenBoundaryHalfRoot, p, q, N, L, H, m, t,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection] using hroot
  · apply sub_nonpos.mpr
    simpa [sixVertexCanonicalEvenBoundaryHalfRoot, p, q, L, H, m, t,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection] using (hopen.2.2 q).2.le

theorem abs_sixVertexCanonicalOddBoundaryHalfRoot_sub_pi_le
    {c : Real} (hc : 2 < c) (s k : Nat)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k))
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x)
    (i : Fin (s + 1)) :
    |sixVertexCanonicalOddBoundaryHalfRoot hc s k i - Real.pi| <=
      (s + 1 : Real) /
        ((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower) := by
  let t := 2 * s + 1 + k
  let m := s + k + 1
  let L := t + 1
  let H := L + L
  let N := sixVertexFourWidth 0 t
  let p := sixVertexCanonicalDensityPerronBetheRoots hc t
  let q : Fin H := ⟨m + i.val + L, by dsimp [H, L, m, t]; omega⟩
  have hN : 0 < N := sixVertexFourWidth_pos 0 t
  have hhalf : N = 2 * H := by
    dsimp [N, H, L, t]
    unfold sixVertexFourWidth
    omega
  have hopen : SixVertexOpenRootSimplex p :=
    sixVertexCanonicalDensityPerronBetheRoots_mem_open hc t
  have hsol : SixVertexSatisfiesBetheEquations c N H p :=
    sixVertexCanonicalDensityPerronBetheRoots_is_solution hc t
  have h := sixVertexBetheSolution_last_endpoint_le_of_finiteDensityLower
    hc hN hhalf hopen hsol hlower hdensity q
  have hindex : (((q.rev.val : Nat) : Real) + 1) <= s + 1 := by
    have hnat : q.rev.val + 1 <= s + 1 := by
      simp only [q, Fin.rev, Fin.val_mk]
      dsimp [H, L, m, t]
      omega
    exact_mod_cast hnat
  have hden : 0 <= (N : Real) * lower := by positivity
  have hroot : Real.pi - p q <=
      (s + 1 : Real) / ((N : Real) * lower) :=
    h.trans (div_le_div_of_nonneg_right hindex hden)
  change |_ - Real.pi| <= _
  rw [abs_of_nonpos]
  · simpa [sixVertexCanonicalOddBoundaryHalfRoot, p, q, N, L, H, m, t,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection] using hroot
  · apply sub_nonpos.mpr
    simpa [sixVertexCanonicalOddBoundaryHalfRoot, p, q, L, H, m, t,
      sixVertexCanonicalDensityPerronPositiveHalfRoots,
      sixVertexEvenPositiveHalfProjection] using (hopen.2.2 q).2.le



theorem sixVertexCanonicalFixedEvenDensityCandidateLogRatio_decomposition
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexCanonicalFixedEvenDensityCandidateLogRatio hc s k =
      2 * (
        (∑ j, (sixVertexBetheLogObservable c
              (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
            sixVertexBetheLogObservable c
              (sixVertexCanonicalEvenCommonHalfRoot hc s k j))) -
        ∑ i, sixVertexBetheLogObservable c
          (sixVertexCanonicalEvenBoundaryHalfRoot hc s k i)) := by
  rw [sixVertexCanonicalFixedEvenDensityCandidateLogRatio_eq hc]
  rw [sum_sixVertexCanonicalEvenHalfRoots_eq_common_add_boundary
    (sixVertexBetheLogObservable c) hc]
  rw [Finset.sum_sub_distrib]
  ring




theorem sixVertexCanonicalFixedOddDensityCandidateLogRatio_decomposition
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
    sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s k =
      Real.log (sixVertexZeroPhaseBethePrefactor c
        (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
        (sixVertexOddCentralIndex (s + k + 1))) - Real.log 2 +
      2 * (∑ j, (sixVertexBetheLogObservable c
            (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) -
          sixVertexBetheLogObservable c
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j))) +
      2 * (∑ j, (sixVertexBetheLogObservable c
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          sixVertexBetheLogObservable c
            (sixVertexCanonicalOddLeftHalfRoot hc s k j))) -
      2 * ∑ i, sixVertexBetheLogObservable c
        (sixVertexCanonicalOddBoundaryHalfRoot hc s k i) := by
  rw [sixVertexCanonicalFixedOddDensityCandidateLogRatio_eq hc s k hfixed]
  rw [sum_sixVertexCanonicalOddHalfRoots_eq_left_add_boundary
    (sixVertexBetheLogObservable c) hc]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

end

end StatMech.FrontierD
