/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryIncidenceScheduledCapstone
import Mathlib.Data.Nat.Choose.Bounds



open Filter Topology MeasureTheory

namespace StatMech.FrontierD

noncomputable section



def fkRectPIMSDecayDepth (a : Real) (p : Nat → Real) (k : Nat) : Nat :=
  Nat.findGreatest (fun d => p k ≤ a ^ d) k


theorem fkRectPIMSDecayDepth_spec
    {a : Real} {p : Nat → Real} (hp_one : ∀ k, p k ≤ 1) (k : Nat) :
    p k ≤ a ^ fkRectPIMSDecayDepth a p k := by
  unfold fkRectPIMSDecayDepth
  apply Nat.findGreatest_spec (P := fun d => p k ≤ a ^ d) (Nat.zero_le k)
  simpa using hp_one k



theorem tendsto_fkRectPIMSDecayDepth_atTop
    {a : Real} (ha : 0 < a) {p : Nat → Real}
    (hp : Tendsto p atTop (nhds 0)) :
    Tendsto (fkRectPIMSDecayDepth a p) atTop atTop := by
  refine tendsto_atTop.2 (fun N => ?_)
  have haN : 0 < a ^ N := pow_pos ha N
  have hpN : ∀ᶠ k in atTop, p k < a ^ N :=
    (tendsto_order.1 hp).2 _ haN
  filter_upwards [hpN, eventually_ge_atTop N] with k hpk hk
  exact Nat.le_findGreatest hk hpk.le




def fkRectPIMSSublinearThreshold (depth height : Nat) : Nat :=
  if depth = 0 then height else height / depth



theorem tendsto_fkRectPIMSSublinearThreshold_div_height_zero
    (depth height : Nat → Nat)
    (hdepth : Tendsto depth atTop atTop)
    (hheight_pos : ∀ k, 0 < height k) :
    Tendsto (fun k =>
      (fkRectPIMSSublinearThreshold (depth k) (height k) : Real) /
        height k) atTop (nhds 0) := by
  have hdepthReal : Tendsto (fun k => (depth k : Real)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hdepth
  have hupper : Tendsto (fun k => (1 : Real) / depth k)
      atTop (nhds 0) := hdepthReal.const_div_atTop 1
  apply squeeze_zero' (g := fun k => (1 : Real) / depth k)
  · filter_upwards [] with k
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [tendsto_atTop.1 hdepth 1] with k hk
    have hdpos : 0 < depth k := by omega
    have hdne : depth k ≠ 0 := Nat.ne_of_gt hdpos
    rw [fkRectPIMSSublinearThreshold, if_neg hdne]
    have hcast : ((height k / depth k : Nat) : Real) ≤
        (height k : Real) / depth k := Nat.cast_div_le
    have hhreal : (0 : Real) < height k := by exact_mod_cast hheight_pos k
    calc
      ((height k / depth k : Nat) : Real) / height k ≤
          ((height k : Real) / depth k) / height k :=
        div_le_div_of_nonneg_right hcast hhreal.le
      _ = (1 : Real) / depth k := by
        field_simp
  · exact hupper





theorem fkRect_choose_mul_pow_le_finiteEnergy_of_pimsDepth
    {p c : Real} (hp0 : 0 ≤ p) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (width height depth : Nat) (hdepth : 0 < depth)
    (hpdepth : p ≤ (c / 4) ^ depth)
    (hheight : (c / 2) ^ height ≤ c ^ (2 * width + height) / 2) :
    Nat.choose height (height / depth + 1) * p ^ (height / depth + 1) ≤
      c ^ (2 * width + height) / 2 := by
  have ha0 : 0 ≤ c / 4 := by positivity
  have ha1 : c / 4 ≤ 1 := by linarith
  have hexponent : height ≤ depth * (height / depth + 1) := by
    have hmod := Nat.mod_lt height hdepth
    calc
      height = depth * (height / depth) + height % depth :=
        (Nat.div_add_mod height depth).symm
      _ ≤ depth * (height / depth) + depth := Nat.add_le_add_left hmod.le _
      _ = depth * (height / depth + 1) := by ring
  have hprob : p ^ (height / depth + 1) ≤ (c / 4) ^ height := by
    calc
      p ^ (height / depth + 1) ≤
          ((c / 4) ^ depth) ^ (height / depth + 1) := by
        gcongr
      _ = (c / 4) ^ (depth * (height / depth + 1)) := by
        rw [pow_mul]
      _ ≤ (c / 4) ^ height :=
        pow_le_pow_of_le_one ha0 ha1 hexponent
  have hchoose : (Nat.choose height (height / depth + 1) : Real) ≤
      (2 : Real) ^ height := by
    exact_mod_cast Nat.choose_le_two_pow height (height / depth + 1)
  calc
    Nat.choose height (height / depth + 1) *
          p ^ (height / depth + 1) ≤
        (2 : Real) ^ height * (c / 4) ^ height :=
      mul_le_mul hchoose hprob (pow_nonneg hp0 _) (pow_nonneg (by positivity) _)
    _ = (c / 2) ^ height := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ c ^ (2 * width + height) / 2 := hheight



theorem exists_fkRectPIMSHeightDominating
    (c : Real) (width : Nat) :
    ∃ height : Nat, 2 / c ^ (2 * width) ≤ (2 : Real) ^ height := by
  have ht : Tendsto (fun height : Nat => (2 : Real) ^ height)
      atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  exact (tendsto_atTop.1 ht (2 / c ^ (2 * width))).exists



noncomputable def fkRectPIMSHeightLower
    (c : Real) (width : Nat) : Nat :=
  max width (Nat.find (exists_fkRectPIMSHeightDominating c width))

theorem fkRectPIMSHeightLower_width_le
    (c : Real) (width : Nat) :
    width ≤ fkRectPIMSHeightLower c width :=
  le_max_left _ _



theorem fkRectPIMSHeightLower_domination
    {c : Real} (hc0 : 0 < c) (width height : Nat)
    (hheight : fkRectPIMSHeightLower c width ≤ height) :
    (c / 2) ^ height ≤ c ^ (2 * width + height) / 2 := by
  let first := Nat.find (exists_fkRectPIMSHeightDominating c width)
  have hfirst : first ≤ height := by
    exact (le_max_right width first).trans hheight
  have hbase : 2 / c ^ (2 * width) ≤ (2 : Real) ^ first :=
    Nat.find_spec (exists_fkRectPIMSHeightDominating c width)
  have htwo : (2 : Real) ^ first ≤ (2 : Real) ^ height := by
    exact pow_le_pow_right₀ (by norm_num : (1 : Real) ≤ 2) hfirst
  have hcwidth : 0 < c ^ (2 * width) := pow_pos hc0 _
  have hmul : (2 : Real) ≤ (2 : Real) ^ height * c ^ (2 * width) := by
    exact (div_le_iff₀ hcwidth).mp (hbase.trans htwo)
  have hcHeight : 0 ≤ c ^ height := (pow_pos hc0 _).le
  have hcross := mul_le_mul_of_nonneg_right hmul hcHeight
  have htwoPow : 0 < (2 : Real) ^ height := pow_pos (by norm_num) _
  rw [div_pow, pow_add]
  apply (div_le_div_iff₀ htwoPow (by norm_num : (0 : Real) < 2)).2
  calc
    c ^ height * 2 = 2 * c ^ height := by ring
    _ ≤ ((2 : Real) ^ height * c ^ (2 * width)) * c ^ height := hcross
    _ = (c ^ (2 * width) * c ^ height) * 2 ^ height := by ring




theorem fkRect_pimsDecay_scheduled_binomialSmallness
    {c : Real} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (p : Nat → Real) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hp : Tendsto p atTop (nhds 0))
    (width height : Nat → Nat)
    (hheight_pos : ∀ k, 0 < height k)
    (hheightLower : ∀ k,
      fkRectPIMSHeightLower c (width k) ≤ height k) :
    let depth := fkRectPIMSDecayDepth (c / 4) p
    let threshold := fun k =>
      fkRectPIMSSublinearThreshold (depth k) (height k)
    (∀ k, Nat.choose (height k) (threshold k + 1) *
        (p k) ^ (threshold k + 1) ≤
          c ^ (2 * width k + height k) / 2) ∧
      Tendsto (fun k => (threshold k : Real) / height k)
        atTop (nhds 0) := by
  dsimp only
  let depth := fkRectPIMSDecayDepth (c / 4) p
  have hc4 : 0 < c / 4 := by positivity
  have hdepth : Tendsto depth atTop atTop :=
    tendsto_fkRectPIMSDecayDepth_atTop hc4 hp
  constructor
  · intro k
    change Nat.choose (height k)
        (fkRectPIMSSublinearThreshold (depth k) (height k) + 1) *
          p k ^ (fkRectPIMSSublinearThreshold (depth k) (height k) + 1) ≤
        c ^ (2 * width k + height k) / 2
    by_cases hzero : depth k = 0
    · simp [fkRectPIMSSublinearThreshold, hzero]
      positivity
    · rw [fkRectPIMSSublinearThreshold, if_neg hzero]
      exact fkRect_choose_mul_pow_le_finiteEnergy_of_pimsDepth
        (hp0 k) hc0 hc1 (width k) (height k) (depth k)
        (Nat.pos_of_ne_zero hzero)
        (fkRectPIMSDecayDepth_spec hp1 k)
        (fkRectPIMSHeightLower_domination hc0 _ _ (hheightLower k))
  · exact tendsto_fkRectPIMSSublinearThreshold_div_height_zero
      depth height hdepth hheight_pos



theorem fkRect_boxBdryConnEvent_real_tendsto_zero_of_percolation_zero
    (mu : MeasureTheory.Measure
      (ConfigSpace (Sym2 (StatMech.Lattice.Site 2))))
    [MeasureTheory.IsFiniteMeasure mu]
    (hperc : mu.real (Percolation.percolationEvent 2) = 0) :
    Tendsto (fun n => mu.real (FK.boxBdryConnEvent 2 n))
      atTop (nhds 0) := by
  simpa [hperc] using
    (FK.boxBdryConnEvent_real_tendsto_percolation (d := 2) mu)



noncomputable def fkRectFixedChargeFreeOneArm
    {q : Real} (hq : 1 ≤ q) (r k : Nat) : Real :=
  (FK.freeInfiniteVolume 2
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
      (zero_lt_one.trans_le hq) :
    MeasureTheory.Measure (ConfigSpace
      (Sym2 (StatMech.Lattice.Site 2)))).real
    (FK.boxBdryConnEvent 2
      ((fkRectFixedChargeVerticalFamily r k 0).width - 2))



noncomputable def fkRectBoundaryIncidencePIMSHeightLower
    (q : Real) (r k : Nat) : Nat :=
  let width := (fkRectFixedChargeVerticalFamily r k 0).width
  k * width + fkRectPIMSHeightLower (FK.cFE (fkRectCriticalP q) q) width



theorem tendsto_fkRectFixedChargeFreeOneArm_zero_of_percolation_zero
    {q : Real} (hq : 1 ≤ q) (r : Nat)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
        (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
        (zero_lt_one.trans_le hq) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0) :
    Tendsto (fkRectFixedChargeFreeOneArm hq r) atTop (nhds 0) := by
  let mu := (FK.freeInfiniteVolume 2
    (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
    (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
    (zero_lt_one.trans_le hq) :
      MeasureTheory.Measure (ConfigSpace
        (Sym2 (StatMech.Lattice.Site 2))))
  have hbox :=
    fkRect_boxBdryConnEvent_real_tendsto_zero_of_percolation_zero
      mu hperc
  have hradius : Tendsto (fun k =>
      (fkRectFixedChargeVerticalFamily r k 0).width - 2) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    filter_upwards [eventually_ge_atTop N] with k hk
    simp only [fkRectFixedChargeVerticalFamily_width]
    omega
  simpa [fkRectFixedChargeFreeOneArm, mu] using hbox.comp hradius

set_option maxHeartbeats 800000 in




theorem
    fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_freePIMS_fourCopy
    {q xiInv : Real} (hq : 4 < q) (r : Nat) (hr : 2 ≤ r)
    (hperc :
      let mu := (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (by linarith : 0 < q))
        (fkRectCriticalP_lt_one (by linarith : 0 < q))
        (by linarith : 0 < q) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2))))
      mu.real (Percolation.percolationEvent 2) = 0)
    (hwind : ∀ m : Nat → Nat,
      (∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) →
      Tendsto (fun k =>
        -Real.log
            (fkRectCriticalWindingTailMass
              (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds (((r - 1 : Nat) : Real) * xiInv)))
    (hfourCopy : ∀ m : Nat → Nat,
      (∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) →
      Tendsto (fun k =>
        fkRectFourCopyShareCost
            (fkRectFixedChargeVerticalFamily r k (m k)) q /
          (fkRectFixedChargeVerticalFamily r k (m k)).height)
        atTop (nhds 0)) :
    ((r - 1 : Nat) : Real) * xiInv ≤
      (r : Real) * fkQgt4SixVertexGapRate q := by
  let hq1 : 1 ≤ q := by linarith
  let c := FK.cFE (fkRectCriticalP q) q
  let p := fkRectFixedChargeFreeOneArm hq1 r
  let depth := fkRectPIMSDecayDepth (c / 4) p
  let threshold : (Nat → Nat) → Nat → Nat := fun m k =>
    fkRectPIMSSublinearThreshold (depth k)
      (fkRectFixedChargeVerticalFamily r k (m k)).height
  have hc0 : 0 < c := by
    exact FK.cFE_pos
      (fkRectCriticalP_pos (by linarith : 0 < q))
      (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith)
  have hc1 : c ≤ 1 := fkRectCritical_cFE_le_one hq1
  have hp0 : ∀ k, 0 ≤ p k := fun _ => measureReal_nonneg
  have hp1 : ∀ k, p k ≤ 1 := fun _ => measureReal_le_one
  have hp : Tendsto p atTop (nhds 0) := by
    exact tendsto_fkRectFixedChargeFreeOneArm_zero_of_percolation_zero
      hq1 r hperc
  have scheduled (m : Nat → Nat)
      (hm : ∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) :=
    fkRect_pimsDecay_scheduled_binomialSmallness hc0 hc1 p hp0 hp1 hp
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).width)
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height)
      (fun k => (fkRectFixedChargeVerticalFamily r k (m k)).height_pos)
      (fun k => by
        change fkRectPIMSHeightLower c
            (fkRectFixedChargeVerticalFamily r k (m k)).width ≤
          (fkRectFixedChargeVerticalFamily r k (m k)).height
        simp only [fkRectFixedChargeVerticalFamily_width,
          fkRectFixedChargeVerticalFamily_height]
        have hm' := hm k
        dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
        dsimp [c]
        omega)
  apply
    fkQgt4_fixedCharge_bound_of_uniformDiagonalWinding_boundaryIncidenceTail_fourCopy
      hq r hr (fkRectBoundaryIncidencePIMSHeightLower q r) threshold hwind
  · intro m hm k
    simpa [threshold, depth, p, c, fkRectFixedChargeFreeOneArm] using
      (scheduled m hm).1 k
  · intro m hm
    have hupper : Tendsto (fun k : Nat => (1 : Real) / k) atTop (nhds 0) :=
      (tendsto_natCast_atTop_atTop (R := Real)).const_div_atTop 1
    apply squeeze_zero' (g := fun k : Nat => (1 : Real) / k)
    · filter_upwards [] with k
      positivity
    · filter_upwards [eventually_ge_atTop 1] with k hk
      let W := (fkRectFixedChargeVerticalFamily r k (m k)).width
      let H := (fkRectFixedChargeVerticalFamily r k (m k)).height
      have hm' := hm k
      have hmul : k * W ≤ m k := by
        dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
        exact (Nat.le_add_right _ _).trans hm'
      have hkreal : (0 : Real) < k := by exact_mod_cast hk
      have hHreal : (0 : Real) < H := by
        exact_mod_cast (fkRectFixedChargeVerticalFamily r k (m k)).height_pos
      apply (div_le_div_iff₀ hHreal hkreal).2
      have hnat : W * k ≤ H := by
        have hmk : W * k ≤ m k := by
          simpa [Nat.mul_comm] using hmul
        exact hmk.trans (by
          dsimp [H]
          omega)
      change (W : Real) * (k : Real) ≤ 1 * (H : Real)
      norm_num
      exact_mod_cast hnat
    · exact hupper
  · intro m hm
    simpa [threshold, depth, p, c] using (scheduled m hm).2
  · intro m hm
    refine tendsto_atTop.2 (fun N => ?_)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hm' := hm k
    dsimp [fkRectBoundaryIncidencePIMSHeightLower] at hm'
    have hmk : k ≤ m k := by
      have hw : 1 ≤ (fkRectFixedChargeVerticalFamily r k 0).width :=
        (fkRectFixedChargeVerticalFamily r k 0).width_pos
      exact (Nat.le_mul_of_pos_right k hw).trans
        ((Nat.le_add_right _ _).trans hm')
    simp only [fkRectFixedChargeVerticalFamily_height]
    omega
  · exact hfourCopy

end

end StatMech.FrontierD
