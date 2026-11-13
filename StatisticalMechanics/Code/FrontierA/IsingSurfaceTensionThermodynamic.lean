/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.FrontierA.Z2GaugeWilsonFreeEnergy

open Filter Topology Set
open scoped BigOperators Topology

namespace StatMech.FrontierA

noncomputable section


def rectangularSurfaceDensity (F : Nat → Nat → Real) (m n : Nat) : Real :=
  F m n / ((m : Real) * (n : Real))


def positiveRectangularSurfaceDensities
    (F : Nat → Nat → Real) : Set Real :=
  {x | ∃ m n : Nat, 0 < m ∧ 0 < n ∧ rectangularSurfaceDensity F m n = x}



def rectangularSurfaceRate (F : Nat → Nat → Real) : Real :=
  sInf (positiveRectangularSurfaceDensities F)





def HasRectangularBlockGluing (F : Nat → Nat → Real) : Prop :=
  ∀ m k : Nat, 0 < m → 0 < k →
    ∃ C : Real, 0 ≤ C ∧ ∀ n : Nat, 0 < n →
      rectangularSurfaceDensity F n n ≤
        rectangularSurfaceDensity F m k + C / n



def HorizontallySubadditive (F : Nat → Nat → Real) : Prop :=
  ∀ k : Nat, Subadditive (fun m => F m k)



def VerticallySubadditive (F : Nat → Nat → Real) : Prop :=
  ∀ m : Nat, Subadditive (F m)



theorem fixedHeightSurfaceDensity_tendsto
    {F : Nat → Nat → Real} (hF : ∀ m n, 0 ≤ F m n)
    (hsub : HorizontallySubadditive F) (k : Nat) :
    Tendsto (fun m : Nat => rectangularSurfaceDensity F m k) atTop
      (nhds ((hsub k).lim / (k : Real))) := by
  have hbdd : BddBelow (Set.range fun m : Nat => F m k / (m : Real)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨m, rfl⟩
    exact div_nonneg (hF m k) (Nat.cast_nonneg m)
  have hFekete : Tendsto (fun m : Nat => F m k / (m : Real)) atTop
      (nhds (hsub k).lim) := (hsub k).tendsto_lim hbdd
  have hdiv := hFekete.div_const (k : Real)
  simpa [rectangularSurfaceDensity, div_div, Nat.cast_mul] using hdiv



theorem horizontalStripRate_nonneg
    {F : Nat → Nat → Real} (hF : ∀ m n, 0 ≤ F m n)
    (hh : HorizontallySubadditive F) (k : Nat) :
    0 ≤ (hh k).lim := by
  have hbdd : BddBelow (Set.range fun m : Nat => F m k / (m : Real)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨m, rfl⟩
    exact div_nonneg (hF m k) (Nat.cast_nonneg m)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ((hh k).tendsto_lim hbdd)
  exact Filter.Eventually.of_forall fun m =>
    div_nonneg (hF m k) (Nat.cast_nonneg m)





theorem horizontalStripRate_subadditive
    {F : Nat → Nat → Real} (hF : ∀ m n, 0 ≤ F m n)
    (hh : HorizontallySubadditive F) (hv : VerticallySubadditive F) :
    Subadditive (fun k => (hh k).lim) := by
  intro k l
  have hk : Tendsto (fun m : Nat => F m k / (m : Real)) atTop
      (nhds (hh k).lim) := by
    apply (hh k).tendsto_lim
    refine ⟨0, ?_⟩
    rintro x ⟨m, rfl⟩
    exact div_nonneg (hF m k) (Nat.cast_nonneg m)
  have hl : Tendsto (fun m : Nat => F m l / (m : Real)) atTop
      (nhds (hh l).lim) := by
    apply (hh l).tendsto_lim
    refine ⟨0, ?_⟩
    rintro x ⟨m, rfl⟩
    exact div_nonneg (hF m l) (Nat.cast_nonneg m)
  have hkl : Tendsto (fun m : Nat => F m (k + l) / (m : Real)) atTop
      (nhds (hh (k + l)).lim) := by
    apply (hh (k + l)).tendsto_lim
    refine ⟨0, ?_⟩
    rintro x ⟨m, rfl⟩
    exact div_nonneg (hF m (k + l)) (Nat.cast_nonneg m)
  apply le_of_tendsto_of_tendsto hkl (hk.add hl)
  filter_upwards [eventually_gt_atTop 0] with m hm
  rw [← add_div]
  exact div_le_div_of_nonneg_right (hv m k l) (Nat.cast_nonneg m)







theorem iteratedRectangularSurfaceDensity_tendsto
    {F : Nat → Nat → Real} (hF : ∀ m n, 0 ≤ F m n)
    (hh : HorizontallySubadditive F) (hv : VerticallySubadditive F) :
    Tendsto (fun k : Nat => (hh k).lim / (k : Real)) atTop
      (nhds (horizontalStripRate_subadditive hF hh hv).lim) := by
  let u : Nat → Real := fun k => (hh k).lim
  have hu : Subadditive u := horizontalStripRate_subadditive hF hh hv
  have hbdd : BddBelow (Set.range fun k : Nat => u k / (k : Real)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    apply div_nonneg
    · exact horizontalStripRate_nonneg hF hh k
    · exact Nat.cast_nonneg k
  simpa only [u] using hu.tendsto_lim hbdd

theorem positiveRectangularSurfaceDensities_nonempty
    (F : Nat → Nat → Real) :
    (positiveRectangularSurfaceDensities F).Nonempty := by
  refine ⟨rectangularSurfaceDensity F 1 1, 1, 1, by norm_num, by norm_num, rfl⟩

theorem positiveRectangularSurfaceDensities_bddBelow
    {F : Nat → Nat → Real} (hF : ∀ m n, 0 ≤ F m n) :
    BddBelow (positiveRectangularSurfaceDensities F) := by
  refine ⟨0, ?_⟩
  rintro x ⟨m, n, hm, hn, rfl⟩
  exact div_nonneg (hF m n)
    (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))



theorem rectangularSurfaceRate_le_density
    {F : Nat → Nat → Real} (hF : ∀ m n, 0 ≤ F m n)
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    rectangularSurfaceRate F ≤ rectangularSurfaceDensity F m n := by
  apply csInf_le (positiveRectangularSurfaceDensities_bddBelow hF)
  exact ⟨m, n, hm, hn, rfl⟩



theorem rectangularSurfaceRate_nonneg
    {F : Nat → Nat → Real} (hF : ∀ m n, 0 ≤ F m n) :
    0 ≤ rectangularSurfaceRate F := by
  apply le_csInf (positiveRectangularSurfaceDensities_nonempty F)
  rintro x ⟨m, n, hm, hn, rfl⟩
  exact div_nonneg (hF m n)
    (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n))



theorem exists_rectangularDensity_lt_rate_add
    (F : Nat → Nat → Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ m n : Nat, 0 < m ∧ 0 < n ∧
      rectangularSurfaceDensity F m n < rectangularSurfaceRate F + epsilon := by
  obtain ⟨x, hx, hlt⟩ := Real.lt_sInf_add_pos
    (positiveRectangularSurfaceDensities_nonempty F) hepsilon
  rcases hx with ⟨m, n, hm, hn, rfl⟩
  exact ⟨m, n, hm, hn, hlt⟩




theorem rectangularSurfaceDensity_tendsto_rate
    {F : Nat → Nat → Real} (hF : ∀ m n, 0 ≤ F m n)
    (hglue : HasRectangularBlockGluing F) :
    Tendsto (fun n : Nat => rectangularSurfaceDensity F n n)
      atTop (nhds (rectangularSurfaceRate F)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact ha.trans_le (rectangularSurfaceRate_le_density hF hn hn)
  · intro b hb
    let epsilon := b - rectangularSurfaceRate F
    have hepsilon : 0 < epsilon := sub_pos.mpr hb
    obtain ⟨m, k, hm, hk, hblock⟩ :=
      exists_rectangularDensity_lt_rate_add F hepsilon
    have hblock' : rectangularSurfaceDensity F m k < b := by
      simpa [epsilon] using hblock
    obtain ⟨C, hC, hglueC⟩ := hglue m k hm hk
    have hvanish : Tendsto (fun n : Nat => C / (n : Real))
        atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat C
    have hevent : ∀ᶠ n : Nat in atTop,
        C / (n : Real) < b - rectangularSurfaceDensity F m k := by
      have hopen : Set.Iio (b - rectangularSurfaceDensity F m k) ∈ nhds 0 := by
        exact Iio_mem_nhds (sub_pos.mpr hblock')
      exact hvanish.eventually hopen
    filter_upwards [eventually_gt_atTop 0, hevent] with n hn herr
    exact (hglueC n hn).trans_lt (by linarith)



theorem surfaceRate_shape_independent
    {f g : Nat → Real} {tau : Real}
    (hf : Tendsto f atTop (nhds tau))
    (hboundary : Tendsto (fun n => g n - f n) atTop (nhds 0)) :
    Tendsto g atTop (nhds tau) := by
  have hsum := hboundary.add hf
  convert hsum using 1 <;> simp



def cubicalSquareWilsonFreeEnergy (beta : Real) (n : Nat) : Real :=
  -Real.log
    (gaugeWilsonExpectation
      (cubicalPlaquetteIncidence (a := n + 1) (b := n + 1) (c := n + 1))
      (fun _ : CubicalPlaquette (n + 1) (n + 1) (n + 1) => beta)
      (cubicalXYLoop (a := n + 1) (b := n + 1) (c := n + 1)
        (0 : Fin (n + 1 + 1))))


def cubicalSquareDisorderFreeEnergy (beta : Real) (n : Nat) : Real :=
  multibondDisorderFreeEnergy
    (cubicalDualEnds (a := n + 1) (b := n + 1) (c := n + 1))
    (fun _ : CubicalPlaquette (n + 1) (n + 1) (n + 1) =>
      gaugeDualCoupling beta)
    (cubicalXYSheet (a := n + 1) (b := n + 1) (c := n + 1)
      (0 : Fin (n + 1 + 1)))



theorem cubicalSquareWilsonFreeEnergy_eq_disorderFreeEnergy
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    cubicalSquareWilsonFreeEnergy beta n =
      cubicalSquareDisorderFreeEnergy beta n := by
  let L := n + 1
  have hL : 0 < L := by omega
  simpa [cubicalSquareWilsonFreeEnergy, cubicalSquareDisorderFreeEnergy, L]
    using neg_log_cubicalXYWilsonExpectation_eq_disorderFreeEnergy
    hL hL hL (0 : Fin (L + 1))
      (fun _ : CubicalPlaquette L L L => beta) (fun _ => hbeta)


def cubicalSquareWilsonDensity (beta : Real) (n : Nat) : Real :=
  cubicalSquareWilsonFreeEnergy beta n / ((n + 1 : Nat) : Real) ^ 2


def cubicalSquareDisorderDensity (beta : Real) (n : Nat) : Real :=
  cubicalSquareDisorderFreeEnergy beta n / ((n + 1 : Nat) : Real) ^ 2


theorem cubicalSquareWilsonDensity_eq_disorderDensity
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    cubicalSquareWilsonDensity beta n = cubicalSquareDisorderDensity beta n := by
  rw [cubicalSquareWilsonDensity, cubicalSquareDisorderDensity,
    cubicalSquareWilsonFreeEnergy_eq_disorderFreeEnergy hbeta n]



theorem cubicalSquareWilsonDensity_mem_Icc
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    cubicalSquareWilsonDensity beta n ∈
      Set.Icc 0 (2 * gaugeDualCoupling beta) := by
  let L := n + 1
  have hL : 0 < L := by omega
  have hcost := cubicalXYWilsonFreeEnergy_mem_Icc
    hL hL hL (0 : Fin (L + 1))
      (fun _ : CubicalPlaquette L L L => beta) (fun _ => hbeta)
  have hdual : 0 < gaugeDualCoupling beta := gaugeDualCoupling_pos hbeta
  constructor
  · rw [cubicalSquareWilsonDensity]
    apply div_nonneg
    · simpa [cubicalSquareWilsonFreeEnergy, L] using hcost.1
    · exact sq_nonneg _
  · have harea : (0 : Real) < (L : Real) ^ 2 := by positivity
    rw [cubicalSquareWilsonDensity]
    apply (div_le_iff₀ harea).2
    have hupper := cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling
      hL hL hL (0 : Fin (L + 1)) beta hbeta
    have hupper' : cubicalSquareWilsonFreeEnergy beta n ≤
        2 * (L * L : Nat) * gaugeDualCoupling beta := by
      simpa [cubicalSquareWilsonFreeEnergy, L] using hupper
    rw [cubicalSquareWilsonFreeEnergy]
    change -Real.log _ ≤ _
    calc
      -Real.log _ ≤ 2 * (L * L : Nat) * gaugeDualCoupling beta := by
        simpa [cubicalSquareWilsonFreeEnergy] using hupper'
      _ = 2 * gaugeDualCoupling beta * (L : Real) ^ 2 := by
        push_cast
        ring



theorem cubicalSquareDisorderDensity_tendsto_iff_wilsonDensity
    {beta tau : Real} (hbeta : 0 < beta) :
    Tendsto (cubicalSquareDisorderDensity beta) atTop (nhds tau) ↔
      Tendsto (cubicalSquareWilsonDensity beta) atTop (nhds tau) := by
  constructor <;> intro h
  · exact h.congr' (Filter.Eventually.of_forall fun n =>
      (cubicalSquareWilsonDensity_eq_disorderDensity hbeta n).symm)
  · exact h.congr' (Filter.Eventually.of_forall fun n =>
      cubicalSquareWilsonDensity_eq_disorderDensity hbeta n)






theorem exists_cubicalSquareSurfaceRate_subseq
    {beta : Real} (hbeta : 0 < beta) :
    ∃ tau ∈ Set.Icc 0 (2 * gaugeDualCoupling beta),
      ∃ phi : Nat → Nat, StrictMono phi ∧
        Tendsto (cubicalSquareWilsonDensity beta ∘ phi) atTop (nhds tau) ∧
        Tendsto (cubicalSquareDisorderDensity beta ∘ phi) atTop (nhds tau) := by
  obtain ⟨tau, htau, phi, hphi, hwilson⟩ :=
    isCompact_Icc.tendsto_subseq
      (fun n => cubicalSquareWilsonDensity_mem_Icc hbeta n)
  refine ⟨tau, htau, phi, hphi, hwilson, ?_⟩
  exact hwilson.congr' (Filter.Eventually.of_forall fun n => by
    simp only [Function.comp_apply]
    exact cubicalSquareWilsonDensity_eq_disorderDensity hbeta (phi n))

end

end StatMech.FrontierA
