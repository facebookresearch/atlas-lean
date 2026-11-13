/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheWaveNormalization

open Finset Matrix

namespace StatMech.FrontierD

noncomputable section




theorem sixVertexHalfFilledBetheCandidate_le_perron_of_nonzero
    {c : Real} (hc : 2 < c) (k : Nat) (a : Complex)
    (hne : sixVertexHalfFilledBetheRotatedRealWave hc k a ≠ 0) :
    sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc k) ≤
      sixVertexLambdaAlongFour c 0 k := by
  let N := sixVertexFourWidth 0 k
  let n := (k + 1) + (k + 1)
  let v : EuclideanSpace Real (SixVertexSector N n) :=
    WithLp.toLp 2 (sixVertexHalfFilledBetheRotatedRealWave hc k a)
  have hn : n ≤ N := by
    dsimp [n, N, sixVertexFourWidth]
    omega
  have hvne : v ≠ 0 := by
    intro hv
    apply hne
    funext x
    have hx := congrArg (fun w : EuclideanSpace Real (SixVertexSector N n) => w x) hv
    simpa [v, N, n] using hx
  have heig : sixVertexSectorTransfer N n c *ᵥ (fun i => v i) =
      sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc k) • (fun i => v i) := by
    simpa [v, N, n] using
      sixVertexHalfFilledBetheRotatedRealWave_eigenrelation hc k a
  have habs := sixVertexSector_eigenvalue_abs_le_top_of_nonzero
    hn (show 0 < c by linarith) hvne heig
  have hcandidate : 0 < sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexPositiveHalfBetheRoots hc k) :=
    sixVertexSymmetricBetheEigenvalueValue_pos hc _
  rw [abs_of_pos hcandidate] at habs
  have hhalf : N / 2 = n := by
    dsimp [N, n, sixVertexFourWidth]
    omega
  unfold sixVertexLambdaAlongFour sixVertexLambda
  simp only [Nat.sub_zero]
  let hnHalf : N / 2 ≤ N := Nat.div_le_self N 2
  change sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexPositiveHalfBetheRoots hc k) ≤
    sixVertexSectorTopEigenvalue N (N / 2) hnHalf c
  have hidx : (⟨n, hn⟩ : {m : Nat // m ≤ N}) =
      ⟨N / 2, hnHalf⟩ := by
    apply Subtype.ext
    exact hhalf.symm
  have htop := congrArg
    (fun q : {m : Nat // m ≤ N} =>
      sixVertexSectorTopEigenvalue N q.1 q.2 c) hidx
  exact habs.trans_eq htop



theorem sixVertexHalfFilledBetheCandidate_le_perron_width_four
    {c : Real} (hc : 2 < c) :
    sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc 0) ≤
      sixVertexLambdaAlongFour c 0 0 := by
  let w := sixVertexHalfFilledBethePhaseCorrectedWaveTwo hc
  have hwne : w ≠ 0 := by
    intro hw
    have hx := congrFun hw (sixVertexPackedSector 4 2 (by omega))
    have hpos := sixVertexHalfFilledBethePhaseCorrectedWaveTwo_packed_pos hc
    dsimp [w] at hx
    rw [hx] at hpos
    exact (lt_irrefl 0) hpos
  exact sixVertexHalfFilledBetheCandidate_le_perron_of_nonzero
    hc 0 (-Complex.I) hwne

end

end StatMech.FrontierD
