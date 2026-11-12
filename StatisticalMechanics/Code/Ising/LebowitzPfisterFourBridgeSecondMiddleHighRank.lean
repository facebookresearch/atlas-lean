/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeSecondMiddleFaces
import Code.Ising.LebowitzPfisterFourBridgeRankSimplex
import Code.Ising.LebowitzPfisterFourBridgeMomentBounds












namespace StatMech.Ising

noncomputable section



theorem fourBridgeSecondMiddleNumerator_rankZeroFace_nonneg_of_two_le
    {a b d : Real} (ha2 : 2 <= a)
    (hp1 : 0 <= fourBridgeRankMass a b (1 - a + b + d) d 1)
    (hp2 : 0 <= fourBridgeRankMass a b (1 - a + b + d) d 2)
    (hp3 : 0 <= fourBridgeRankMass a b (1 - a + b + d) d 3) :
    0 <= fourBridgeSecondMiddleNumerator a b (1 - a + b + d) d := by
  let u := 3 * fourBridgeRankMass a b (1 - a + b + d) d 1
  let v := 2 * fourBridgeRankMass a b (1 - a + b + d) d 2
  let w := (a - 2) / 2
  let q := fourBridgeRankMass a b (1 - a + b + d) d 3
  have hu : 0 <= u := mul_nonneg (by norm_num) hp1
  have hv : 0 <= v := mul_nonneg (by norm_num) hp2
  have hw : 0 <= w := by dsimp [w]; linarith
  have hq : 0 <= q := hp3
  have hid :
      fourBridgeSecondMiddleNumerator a b (1 - a + b + d) d =
        128 / 3 * u ^ 4 + 160 * u ^ 3 * v + 704 / 3 * u ^ 3 * w +
        128 * u ^ 3 * q + 544 / 3 * u ^ 2 * v ^ 2 +
        1792 / 3 * u ^ 2 * v * w + 832 / 3 * u ^ 2 * v * q +
        384 * u ^ 2 * w ^ 2 + 1600 / 3 * u ^ 2 * w * q +
        256 / 3 * u ^ 2 * q ^ 2 + 64 * u * v ^ 3 +
        336 * u * v ^ 2 * w + 416 / 3 * u * v ^ 2 * q +
        512 * u * v * w ^ 2 + 1664 / 3 * u * v * w * q +
        224 / 3 * u * v * q ^ 2 + 192 * u * w ^ 3 +
        512 * u * w ^ 2 * q + 128 * u * w * q ^ 2 +
        16 * v ^ 2 * w * q + 32 * v * w ^ 2 * q := by
    dsimp [u, v, w, q]
    simp only [fourBridgeRankMass]
    unfold fourBridgeSecondMiddleNumerator
    ring
  rw [hid]
  positivity



theorem fourBridgeSecondMiddleNumerator_rankThreeFace_nonneg_of_two_le
    {a b d : Real} (ha2 : 2 <= a)
    (hp0 : 0 <= fourBridgeRankMass a b (2 + a - 2 * d) d 0)
    (hp1 : 0 <= fourBridgeRankMass a b (2 + a - 2 * d) d 1)
    (hp2 : 0 <= fourBridgeRankMass a b (2 + a - 2 * d) d 2) :
    0 <= fourBridgeSecondMiddleNumerator a b (2 + a - 2 * d) d := by
  let u := 4 * fourBridgeRankMass a b (2 + a - 2 * d) d 0
  let v := 3 * fourBridgeRankMass a b (2 + a - 2 * d) d 1
  let w := 2 * fourBridgeRankMass a b (2 + a - 2 * d) d 2
  let q := (a - 2) / 2
  have hu : 0 <= u := mul_nonneg (by norm_num) hp0
  have hv : 0 <= v := mul_nonneg (by norm_num) hp1
  have hw : 0 <= w := mul_nonneg (by norm_num) hp2
  have hq : 0 <= q := by dsimp [q]; linarith
  have hid :
      fourBridgeSecondMiddleNumerator a b (2 + a - 2 * d) d =
        192 * v * q ^ 3 + 512 * v * w * q ^ 2 +
        336 * v * w ^ 2 * q + 64 * v * w ^ 3 +
        384 * v ^ 2 * q ^ 2 + 1792 / 3 * v ^ 2 * w * q +
        544 / 3 * v ^ 2 * w ^ 2 + 704 / 3 * v ^ 3 * q +
        160 * v ^ 3 * w + 128 / 3 * v ^ 4 +
        1536 * u * q ^ 3 + 4096 * u * w * q ^ 2 +
        2944 * u * w ^ 2 * q + 640 * u * w ^ 3 +
        4176 * u * v * q ^ 2 + 19616 / 3 * u * v * w * q +
        6608 / 3 * u * v * w ^ 2 + 10048 / 3 * u * v ^ 2 * q +
        7168 / 3 * u * v ^ 2 * w + 816 * u * v ^ 3 +
        3456 * u ^ 2 * q ^ 2 + 5696 * u ^ 2 * w * q +
        1984 * u ^ 2 * w ^ 2 + 5648 * u ^ 2 * v * q +
        12512 / 3 * u ^ 2 * v * w + 6304 / 3 * u ^ 2 * v ^ 2 +
        2496 * u ^ 3 * q + 1920 * u ^ 3 * w +
        1904 * u ^ 3 * v + 576 * u ^ 4 := by
    dsimp [u, v, w, q]
    simp only [fourBridgeRankMass]
    unfold fourBridgeSecondMiddleNumerator
    ring
  rw [hid]
  positivity

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_of_two_le_oneCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha2 : 2 <= fourBridgeOneCoeff G J hf w x y z) :
    fourBridgeVarianceSkewBernsteinCoeff
      (fourBridgeOneCoeff G J hf w x y z)
      (fourBridgeTwoCoeff G J hf w x y z)
      (fourBridgeThreeCoeff G J hf w x y z)
      (fourBridgeFourCoeff G J hf w x y z) 2 <= 0 := by
  let a := fourBridgeOneCoeff G J hf w x y z
  let b := fourBridgeTwoCoeff G J hf w x y z
  let c := fourBridgeThreeCoeff G J hf w x y z
  let d := fourBridgeFourCoeff G J hf w x y z
  let p := fourBridgeRankMass a b c d
  let L := a + 2 * d - 2
  let U0 := 1 - a + b + d
  let U3 := 2 + a - 2 * d
  have hpi (i : Fin 5) : 0 <= p i := by
    exact fourBridgeRankMass_nonneg G J hf w x y z i
  have hsum : p 0 + p 1 + p 2 + p 3 + p 4 = 1 := by
    exact fourBridgeRankMass_sum a b c d
  have ha4 : a <= 4 := by
    have ha := fourBridge_rankMass_recover_one a b c d
    dsimp only [p] at hsum hpi
    linarith [hpi 0, hpi 1, hpi 2, hpi 3, hpi 4]
  have hb0 : 0 <= b := by dsimp [b, fourBridgeTwoCoeff]; positivity
  have hb6 : b <= 6 := by
    have hb := fourBridge_rankMass_recover_two a b c d
    dsimp only [p] at hsum hpi
    linarith [hpi 0, hpi 1, hpi 2, hpi 3, hpi 4]
  have hd0 : 0 <= d := by dsimp [d, fourBridgeFourCoeff]; positivity
  have hd1 : d <= 1 := by
    have hd := fourBridge_rankMass_recover_four a b c d
    dsimp only [p] at hsum hpi
    linarith [hpi 0, hpi 1, hpi 2, hpi 3, hpi 4]
  have hLc : L <= c := by
    have h1 := hpi 1
    dsimp [p, L, fourBridgeRankMass] at h1 ⊢
    linarith
  have hcU0 : c <= U0 := by
    have h0 := hpi 0
    dsimp [p, U0, fourBridgeRankMass] at h0 ⊢
    linarith
  have hcU3 : c <= U3 := by
    have h3 := hpi 3
    dsimp [p, U3, fourBridgeRankMass] at h3 ⊢
    linarith
  have hp0 : 2 * a + d <= b + 3 := by
    have h0 := hpi 0
    have h1 := hpi 1
    dsimp [p, fourBridgeRankMass] at h0 h1
    linarith
  have hpair : 3 * a <= 6 + b := by
    exact fourBridgeOneCoeff_three_mul_le_six_add_twoCoeff
      G J hf hJ hhf hwx hwy hwz hxy hxz hyz
  have hL : 0 <= fourBridgeSecondMiddleNumerator a b L d := by
    dsimp only [L]
    exact fourBridgeSecondMiddleNumerator_rankFace_nonneg_of_two_le
      ha2 ha4 hb0 hb6 hd0 hd1 hp0 hpair
  rcases le_total U0 U3 with h03 | h30
  · have hU : 0 <= fourBridgeSecondMiddleNumerator a b U0 d := by
      apply fourBridgeSecondMiddleNumerator_rankZeroFace_nonneg_of_two_le ha2
      · have h1 := hpi 1
        dsimp [p, U0, fourBridgeRankMass] at h1 ⊢
        linarith
      · have h2 := hpi 2
        simpa [p, U0, fourBridgeRankMass] using h2
      · dsimp [U0, U3, fourBridgeRankMass] at h03 ⊢
        linarith
    apply fourBridge_bernsteinTwo_nonpos_of_enclosingFaces
      (a := a) (b := b) (c := c) (d := d) (L := L) (U := U0)
    · dsimp [a, fourBridgeOneCoeff]
      positivity
    · exact hLc.trans hcU0
    · exact hLc
    · exact hcU0
    · exact hL
    · exact hU
  · have hU : 0 <= fourBridgeSecondMiddleNumerator a b U3 d := by
      apply fourBridgeSecondMiddleNumerator_rankThreeFace_nonneg_of_two_le ha2
      · dsimp [U0, U3, fourBridgeRankMass] at h30 ⊢
        linarith
      · have h1 := hpi 1
        dsimp [p, U3, fourBridgeRankMass] at h1 ⊢
        linarith
      · have h2 := hpi 2
        simpa [p, U3, fourBridgeRankMass] using h2
    apply fourBridge_bernsteinTwo_nonpos_of_enclosingFaces
      (a := a) (b := b) (c := c) (d := d) (L := L) (U := U3)
    · dsimp [a, fourBridgeOneCoeff]
      positivity
    · exact hLc.trans hcU3
    · exact hLc
    · exact hcU3
    · exact hL
    · exact hU

end

end StatMech.Ising
