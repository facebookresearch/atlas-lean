/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingRectangularDobrushinSpinFlip
import Code.FrontierA.IsingSurfaceTensionRectangularModel
import Code.FrontierA.IsingSurfaceTensionReduction
import Code.FrontierA.IsingSurfaceTensionFiniteVolume
import Code.FrontierA.Z2GaugeDisorderGluing
import Code.Ising.PressureSurfaceVolume

open Filter Topology
open scoped symmDiff

namespace StatMech.FrontierA

noncomputable section




def rectangularPrismInterfaceDensity (beta : Real) (n : Nat) : Real :=
  StatMech.Ising.rectangularDobrushinFreeEnergy
      1 beta (2 * n + 1) (2 * n + 1) n /
    ((2 * n + 1 : Nat) : Real) ^ 2



def oddCubicalIsingDisorderDensity (beta : Real) (n : Nat) : Real :=
  rectangularSurfaceDensity (rectangularIsingDobrushinFreeEnergy beta)
    (2 * n + 1) (2 * n + 1)



def standardCubicInterfaceDensity (beta : Real) (n : Nat) : Real :=
  StatMech.Ising.finiteInterfaceFreeEnergy
      (d := 3) (⟨2, by omega⟩ : Fin 3) n beta /
    ((2 * n + 1 : Nat) : Real) ^ 2



def centralCubicalIsingDisorderDensity (beta : Real) (n : Nat) : Real :=
  let L := 2 * n + 1
  multibondDisorderFreeEnergy
      (cubicalDualEnds (a := L) (b := L) (c := L))
      (fun _ : CubicalPlaquette L L L => beta)
      (cubicalXYSheet (a := L) (b := L) (c := L)
        (⟨n + 1, by omega⟩ : Fin (L + 1))) /
    ((L : Nat) : Real) ^ 2


theorem rectangularPrismInterfaceDensity_eq_boundaryRatio
    (beta : Real) (n : Nat) :
    rectangularPrismInterfaceDensity beta n =
      (Real.log (StatMech.Ising.rectangularPrismPlusPartition
          1 beta (2 * n + 1) (2 * n + 1) n) -
        Real.log (StatMech.Ising.rectangularPrismDobrushinPartition
          1 beta (2 * n + 1) (2 * n + 1) n)) /
        ((2 * n + 1 : Nat) : Real) ^ 2 := by
  rw [rectangularPrismInterfaceDensity,
    StatMech.Ising.rectangularDobrushinFreeEnergy_eq_boundaryRatio]



theorem oddCubicalIsingDisorderDensity_tendsto
    {beta : Real} (hbeta : 0 < beta) :
    Tendsto (oddCubicalIsingDisorderDensity beta) atTop
      (nhds (rectangularIsingSurfaceTension beta)) := by
  have hsquare :=
    (rectangularIsingDobrushin_square_and_iterated_tendsto hbeta).1
  have hodd : Tendsto (fun n : Nat => 2 * n + 1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    omega
  simpa [oddCubicalIsingDisorderDensity, Function.comp_def] using
    hsquare.comp hodd



def HasPrismCubicalSurfaceComparison (beta : Real) : Prop :=
  Tendsto (fun n => rectangularPrismInterfaceDensity beta n -
    oddCubicalIsingDisorderDensity beta n) atTop (nhds 0)



def HasStandardPrismSurfaceComparison (beta : Real) : Prop :=
  Tendsto (fun n => standardCubicInterfaceDensity beta n -
    rectangularPrismInterfaceDensity beta n) atTop (nhds 0)



theorem multibondDisorderFreeEnergy_sheet_sub_abs_le
    {P V : Type*} [Fintype P] [DecidableEq P]
    [Fintype V] [DecidableEq V]
    (ends : P -> V × V) (J : P -> Real) (D D' : Finset P) :
    |multibondDisorderFreeEnergy ends J D -
        multibondDisorderFreeEnergy ends J D'| <=
      2 * ∑ p ∈ D ∆ D', |J p| := by
  classical
  have hlog := multibondIsing_logPartition_coupling_sub_abs_le ends
    (multibondTwistCoupling J D') (multibondTwistCoupling J D)
  have hsum :
      (∑ p : P,
        |multibondTwistCoupling J D' p -
          multibondTwistCoupling J D p|) =
        2 * ∑ p ∈ D ∆ D', |J p| := by
    calc
      (∑ p : P,
          |multibondTwistCoupling J D' p -
            multibondTwistCoupling J D p|) =
          ∑ p : P, if p ∈ D ∆ D' then 2 * |J p| else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        have htwo : |(2 : Real) * J p| = 2 * |J p| := by
          rw [abs_mul]
          norm_num
        by_cases hpD : p ∈ D
        · by_cases hpD' : p ∈ D'
          · simp [multibondTwistCoupling, hpD, hpD', Finset.mem_symmDiff]
          · simp only [multibondTwistCoupling_apply_not_mem J D' hpD',
              multibondTwistCoupling_apply_mem J D hpD,
              Finset.mem_symmDiff, hpD, hpD', not_false_eq_true]
            calc
              |J p - -J p| = |(2 : Real) * J p| := by
                rw [show J p - -J p = (2 : Real) * J p by ring]
              _ = 2 * |J p| := htwo
        · by_cases hpD' : p ∈ D'
          · simp only [multibondTwistCoupling_apply_mem J D' hpD',
              multibondTwistCoupling_apply_not_mem J D hpD,
              Finset.mem_symmDiff, hpD, hpD', not_false_eq_true]
            calc
              |-J p - J p| = |(2 : Real) * J p| := by
                rw [show -J p - J p = -((2 : Real) * J p) by ring, abs_neg]
              _ = 2 * |J p| := htwo
          · simp [multibondTwistCoupling, hpD, hpD', Finset.mem_symmDiff]
      _ = ∑ p ∈ D ∆ D', 2 * |J p| := by
        rw [← Finset.sum_filter]
        simp
      _ = 2 * ∑ p ∈ D ∆ D', |J p| := by rw [Finset.mul_sum]
  unfold multibondDisorderFreeEnergy
  rw [hsum] at hlog
  calc
    |(Real.log (multibondIsingPartition ends J) -
        Real.log (multibondIsingPartition ends (multibondTwistCoupling J D))) -
      (Real.log (multibondIsingPartition ends J) -
        Real.log (multibondIsingPartition ends
          (multibondTwistCoupling J D')))| =
        |Real.log (multibondIsingPartition ends
            (multibondTwistCoupling J D')) -
          Real.log (multibondIsingPartition ends
            (multibondTwistCoupling J D))| := by
      congr 1
      ring
    _ <= 2 * ∑ p ∈ D ∆ D', |J p| := hlog




theorem rectangularPrismInterfaceDensity_abs_le
    (beta : Real) (n : Nat) :
    |rectangularPrismInterfaceDensity beta n| <= 2 * |beta| := by
  let L : Nat := 2 * n + 1
  have hL : (0 : Real) < L := by positivity
  have henergy := StatMech.Ising.rectangularDobrushinFreeEnergy_abs_le
    1 beta L L n
  rw [rectangularPrismInterfaceDensity, abs_div]
  change |StatMech.Ising.rectangularDobrushinFreeEnergy 1 beta L L n| /
      |(L : Real) ^ 2| <= 2 * |beta|
  rw [abs_of_pos (sq_pos_of_pos hL)]
  rw [div_le_iff₀ (sq_pos_of_pos hL)]
  simpa [L, pow_two] using henergy




theorem oddCubicalIsingDisorderDensity_abs_le
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    |oddCubicalIsingDisorderDensity beta n| <= 2 * beta := by
  let L : Nat := 2 * n + 1
  have hL : 0 < L := by omega
  have hdisorder := multibondDisorderFreeEnergy_abs_le
    (cubicalDualEnds (a := L) (b := L) (c := L))
    (fun _ : CubicalPlaquette L L L => beta)
    (cubicalXYSheet (a := L) (b := L) (c := L) (0 : Fin (L + 1)))
  rw [oddCubicalIsingDisorderDensity, rectangularSurfaceDensity,
    rectangularIsingDobrushinFreeEnergy_eq_disorder hbeta hL hL,
    finiteRectangularIsingDisorderFreeEnergy, Nat.max_self, abs_div]
  have hLreal : (0 : Real) < L := by positivity
  change |multibondDisorderFreeEnergy
      (cubicalDualEnds (a := L) (b := L) (c := L))
      (fun _ : CubicalPlaquette L L L => beta)
      (cubicalXYSheet (a := L) (b := L) (c := L) (0 : Fin (L + 1)))| /
      |(L : Real) * L| <= 2 * beta
  rw [abs_of_pos (mul_pos hLreal hLreal)]
  rw [div_le_iff₀ (mul_pos hLreal hLreal)]
  calc
    |multibondDisorderFreeEnergy
        (cubicalDualEnds (a := L) (b := L) (c := L))
        (fun _ : CubicalPlaquette L L L => beta)
        (cubicalXYSheet (a := L) (b := L) (c := L)
          (0 : Fin (L + 1)))| <=
        2 * ∑ p ∈ cubicalXYSheet (a := L) (b := L) (c := L)
          (0 : Fin (L + 1)), |(fun _ : CubicalPlaquette L L L => beta) p| :=
      hdisorder
    _ = 2 * beta * ((L : Real) * L) := by
      simp [Finset.sum_const, nsmul_eq_mul, abs_of_pos hbeta]
      ring





theorem oddCubical_sub_centralCubical_abs_le
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    |oddCubicalIsingDisorderDensity beta n -
        centralCubicalIsingDisorderDensity beta n| <= 4 * beta := by
  let L : Nat := 2 * n + 1
  have hL : 0 < L := by omega
  let D0 : Finset (CubicalPlaquette L L L) :=
    cubicalXYSheet (a := L) (b := L) (c := L) (0 : Fin (L + 1))
  let Dc : Finset (CubicalPlaquette L L L) :=
    cubicalXYSheet (a := L) (b := L) (c := L)
      (⟨n + 1, by omega⟩ : Fin (L + 1))
  have hheight : (0 : Fin (L + 1)) ≠
      (⟨n + 1, by omega⟩ : Fin (L + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hdisjoint : Disjoint D0 Dc := by
    rw [Finset.disjoint_left]
    intro p hp0 hpc
    simp only [D0, cubicalXYSheet, Finset.mem_image] at hp0
    obtain ⟨ij, _, rfl⟩ := hp0
    simp only [Dc, cubicalXYSheet, Finset.mem_image] at hpc
    obtain ⟨ij', _, heq⟩ := hpc
    apply hheight
    exact (congrArg (fun q => match q with
      | CubicalPlaquette.xy _ _ k => k
      | _ => 0) heq).symm
  have hcard : (D0 ∆ Dc).card = 2 * (L * L) := by
    rw [Finset.symmDiff_eq_union hdisjoint,
      Finset.card_union_of_disjoint hdisjoint]
    simp [D0, Dc]
    omega
  have hsheet := multibondDisorderFreeEnergy_sheet_sub_abs_le
    (cubicalDualEnds (a := L) (b := L) (c := L))
    (fun _ : CubicalPlaquette L L L => beta) D0 Dc
  have hraw :
      |multibondDisorderFreeEnergy
          (cubicalDualEnds (a := L) (b := L) (c := L))
          (fun _ : CubicalPlaquette L L L => beta) D0 -
        multibondDisorderFreeEnergy
          (cubicalDualEnds (a := L) (b := L) (c := L))
          (fun _ : CubicalPlaquette L L L => beta) Dc| <=
        4 * beta * ((L : Real) ^ 2) := by
    calc
      |multibondDisorderFreeEnergy
          (cubicalDualEnds (a := L) (b := L) (c := L))
          (fun _ : CubicalPlaquette L L L => beta) D0 -
        multibondDisorderFreeEnergy
          (cubicalDualEnds (a := L) (b := L) (c := L))
          (fun _ : CubicalPlaquette L L L => beta) Dc| <=
          2 * ∑ p ∈ D0 ∆ Dc,
            |(fun _ : CubicalPlaquette L L L => beta) p| := hsheet
      _ = 2 * ((D0 ∆ Dc).card : Real) * beta := by
        simp [Finset.sum_const, nsmul_eq_mul, abs_of_pos hbeta]
        ring
      _ <= 2 * (2 * (L * L) : Nat) * beta := by
        gcongr
        exact hcard.le
      _ = 4 * beta * ((L : Real) ^ 2) := by
        push_cast
        ring
  rw [oddCubicalIsingDisorderDensity, rectangularSurfaceDensity,
    rectangularIsingDobrushinFreeEnergy_eq_disorder hbeta hL hL,
    finiteRectangularIsingDisorderFreeEnergy, Nat.max_self,
    centralCubicalIsingDisorderDensity]
  change |multibondDisorderFreeEnergy
      (cubicalDualEnds (a := L) (b := L) (c := L))
      (fun _ : CubicalPlaquette L L L => beta) D0 /
        ((L : Real) * L) -
      multibondDisorderFreeEnergy
      (cubicalDualEnds (a := L) (b := L) (c := L))
      (fun _ : CubicalPlaquette L L L => beta) Dc /
        ((L : Real) ^ 2)| <= 4 * beta
  rw [show (L : Real) * L = (L : Real) ^ 2 by ring]
  rw [div_sub_div_same]
  have hLreal : (0 : Real) < L := by positivity
  rw [abs_div, abs_of_pos (sq_pos_of_pos hLreal),
    div_le_iff₀ (sq_pos_of_pos hLreal)]
  simpa [pow_two] using hraw





theorem prismCubicalDensity_sub_abs_le
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    |rectangularPrismInterfaceDensity beta n -
        oddCubicalIsingDisorderDensity beta n| <= 4 * beta := by
  calc
    |rectangularPrismInterfaceDensity beta n -
        oddCubicalIsingDisorderDensity beta n| <=
        |rectangularPrismInterfaceDensity beta n| +
          |oddCubicalIsingDisorderDensity beta n| := abs_sub _ _
    _ <= 2 * |beta| + 2 * beta := add_le_add
      (rectangularPrismInterfaceDensity_abs_le beta n)
      (oddCubicalIsingDisorderDensity_abs_le hbeta n)
    _ = 4 * beta := by rw [abs_of_pos hbeta]; ring




theorem standardCubicInterfaceDensity_abs_le
    (beta : Real) (n : Nat) :
    |standardCubicInterfaceDensity beta n| <= 1296 * |beta| := by
  let L : Real := 2 * (n : Real) + 1
  have hL : 0 < L := by positivity
  have hfinite := StatMech.Ising.finiteInterfaceFreeEnergy_abs_le
    (⟨2, by omega⟩ : Fin 3) n beta
  have hcardNat := StatMech.Ising.psv_numerator_card_le (d := 3) n
  have hcard :
      (((StatMech.Ising.bondFinsetTouch 3 n) \
        (StatMech.Ising.bondFinsetInternal 3 n)).card : Real) <=
        ((StatMech.Ising.psv_Bdry 3 n).card : Real) * 12 := by
    exact_mod_cast hcardNat
  have hboundary := StatMech.Ising.psv_Bdry_card_real_le 3 n
  have hnum :
      (((StatMech.Ising.bondFinsetTouch 3 n) \
        (StatMech.Ising.bondFinsetInternal 3 n)).card : Real) <=
        72 * (2 * (n : Real) + 3) ^ 2 := by
    calc
      (((StatMech.Ising.bondFinsetTouch 3 n) \
          (StatMech.Ising.bondFinsetInternal 3 n)).card : Real) <=
          ((StatMech.Ising.psv_Bdry 3 n).card : Real) * 12 := hcard
      _ <= (2 * (3 * (2 * (n : Real) + 3) ^ (3 - 1))) * 12 := by
        have hb : ((StatMech.Ising.psv_Bdry 3 n).card : Real) <=
            2 * (3 * (2 * (n : Real) + 3) ^ (3 - 1)) := by
          simpa using hboundary
        gcongr
      _ = 72 * (2 * (n : Real) + 3) ^ 2 := by norm_num; ring
  have hshift : 2 * (n : Real) + 3 <= 3 * L := by
    dsimp [L]
    have hn : (0 : Real) <= n := Nat.cast_nonneg n
    linarith
  have hnumL :
      (((StatMech.Ising.bondFinsetTouch 3 n) \
        (StatMech.Ising.bondFinsetInternal 3 n)).card : Real) <=
        648 * L ^ 2 := by
    calc
      (((StatMech.Ising.bondFinsetTouch 3 n) \
          (StatMech.Ising.bondFinsetInternal 3 n)).card : Real) <=
          72 * (2 * (n : Real) + 3) ^ 2 := hnum
      _ <= 72 * (3 * L) ^ 2 := by gcongr
      _ = 648 * L ^ 2 := by ring
  rw [standardCubicInterfaceDensity, abs_div]
  have hL_eq : (((2 * n + 1 : Nat) : Real)) = L := by
    dsimp [L]
    push_cast
    ring
  rw [hL_eq]
  change |StatMech.Ising.finiteInterfaceFreeEnergy
      (⟨2, by omega⟩ : Fin 3) n beta| / |L ^ 2| <= 1296 * |beta|
  rw [abs_of_pos (sq_pos_of_pos hL), div_le_iff₀ (sq_pos_of_pos hL)]
  calc
    |StatMech.Ising.finiteInterfaceFreeEnergy
        (⟨2, by omega⟩ : Fin 3) n beta| <=
        2 * |beta| *
          ((StatMech.Ising.bondFinsetTouch 3 n \
            StatMech.Ising.bondFinsetInternal 3 n).card : Real) := hfinite
    _ <= 2 * |beta| * (648 * L ^ 2) := by gcongr
    _ = 1296 * |beta| * L ^ 2 := by ring



theorem standardPrismDensity_sub_abs_le
    (beta : Real) (n : Nat) :
    |standardCubicInterfaceDensity beta n -
        rectangularPrismInterfaceDensity beta n| <= 1298 * |beta| := by
  calc
    |standardCubicInterfaceDensity beta n -
        rectangularPrismInterfaceDensity beta n| <=
        |standardCubicInterfaceDensity beta n| +
          |rectangularPrismInterfaceDensity beta n| := abs_sub _ _
    _ <= 1296 * |beta| + 2 * |beta| := add_le_add
      (standardCubicInterfaceDensity_abs_le beta n)
      (rectangularPrismInterfaceDensity_abs_le beta n)
    _ = 1298 * |beta| := by ring



theorem rectangularPrismInterfaceDensity_tendsto_of_comparison
    {beta : Real} (hbeta : 0 < beta)
    (hcompare : HasPrismCubicalSurfaceComparison beta) :
    Tendsto (rectangularPrismInterfaceDensity beta) atTop
      (nhds (rectangularIsingSurfaceTension beta)) :=
  surfaceRate_shape_independent
    (oddCubicalIsingDisorderDensity_tendsto hbeta) hcompare



theorem hasPrismCubicalSurfaceComparison_of_tendsto
    {beta : Real} (hbeta : 0 < beta)
    (hlim : Tendsto (rectangularPrismInterfaceDensity beta) atTop
      (nhds (rectangularIsingSurfaceTension beta))) :
    HasPrismCubicalSurfaceComparison beta := by
  unfold HasPrismCubicalSurfaceComparison
  simpa using hlim.sub (oddCubicalIsingDisorderDensity_tendsto hbeta)

theorem hasPrismCubicalSurfaceComparison_iff_tendsto
    {beta : Real} (hbeta : 0 < beta) :
    HasPrismCubicalSurfaceComparison beta <->
      Tendsto (rectangularPrismInterfaceDensity beta) atTop
        (nhds (rectangularIsingSurfaceTension beta)) :=
  ⟨rectangularPrismInterfaceDensity_tendsto_of_comparison hbeta,
    hasPrismCubicalSurfaceComparison_of_tendsto hbeta⟩




theorem standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension
    {beta : Real} (hbeta : 0 < beta)
    (hprism : HasPrismCubicalSurfaceComparison beta)
    (hstandard : HasStandardPrismSurfaceComparison beta) :
    Tendsto (standardCubicInterfaceDensity beta) atTop
      (nhds (rectangularIsingSurfaceTension beta)) :=
  surfaceRate_shape_independent
    (rectangularPrismInterfaceDensity_tendsto_of_comparison hbeta hprism)
    hstandard





theorem rectangularIsingSurfaceTension_pos_iff_ordered_of_weak_bounds
    {betaC : Real}
    (hregime : StatMech.Ising.HasOrderedMagnetizationRegime
      (StatMech.Ising.magnetization 3) betaC)
    (hzero : 0 <= rectangularIsingSurfaceTension 0)
    (hupper : forall beta, 0 <= beta ->
      rectangularIsingSurfaceTension beta <=
        2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
    (hweak : StatMech.Ising.HasWeakSurfaceTensionLowerBound 1
      (StatMech.Ising.magnetization 3) rectangularIsingSurfaceTension) :
    forall beta, 0 <= beta ->
      (0 < rectangularIsingSurfaceTension beta <-> betaC < beta) := by
  apply StatMech.Ising.surfaceTension_pos_iff_ordered_of_weak_bounds
    1 betaC (StatMech.Ising.magnetization 3)
      rectangularIsingSurfaceTension (by norm_num) hregime
  · intro beta hbeta
    rcases hbeta.eq_or_lt with rfl | hbeta
    · exact hzero
    · exact rectangularIsingSurfaceTension_nonneg hbeta
  · intro beta hbeta
    simpa using hupper beta hbeta
  · exact hweak




theorem rectangularIsingSurfaceTension_pos_iff_ordered_of_weak_bounds_pos
    {betaC : Real}
    (hregime : StatMech.Ising.HasOrderedMagnetizationRegime
      (StatMech.Ising.magnetization 3) betaC)
    (hupper : forall beta, 0 < beta ->
      rectangularIsingSurfaceTension beta <=
        2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
    (hweak : StatMech.Ising.HasWeakSurfaceTensionLowerBound 1
      (StatMech.Ising.magnetization 3) rectangularIsingSurfaceTension) :
    forall beta, 0 < beta ->
      (0 < rectangularIsingSurfaceTension beta <-> betaC < beta) := by
  intro beta hbeta
  constructor
  · intro htau
    by_contra hnot
    have hle : beta <= betaC := not_lt.mp hnot
    have hMzero := hregime.2.1 beta hbeta.le hle
    have hup := hupper beta hbeta
    rw [hMzero] at hup
    norm_num at hup
    exact (not_lt_of_ge hup) htau
  · intro hcb
    let a := (betaC + beta) / 2
    have hca : betaC < a := by dsimp [a]; linarith
    have hab : a < beta := by dsimp [a]; linarith
    have ha0 : 0 < a := hregime.1.trans hca
    have hMa : 0 < StatMech.Ising.magnetization 3 a :=
      hregime.2.2 a hca
    have hinc := hweak a beta ha0 hab.le
    have hpositive :
        0 < 2 * (StatMech.Ising.magnetization 3 a) ^ 2 * (beta - a) := by
      positivity
    have htauA : 0 <= rectangularIsingSurfaceTension a :=
      rectangularIsingSurfaceTension_nonneg ha0
    norm_num at hinc
    linarith



theorem weakSurfaceTensionLowerBound_of_positive_pointwise_tendsto
    (J : Real) (M tau : Real -> Real) (tauN : Nat -> Real -> Real)
    (hlim : forall beta, 0 < beta ->
      Tendsto (fun n => tauN n beta) atTop (nhds (tau beta)))
    (hweak : forall n,
      StatMech.Ising.HasWeakSurfaceTensionLowerBound J M (tauN n)) :
    StatMech.Ising.HasWeakSurfaceTensionLowerBound J M tau := by
  intro a b ha hab
  have hb : 0 < b := ha.trans_le hab
  have hright : Tendsto (fun n => tauN n b - tauN n a) atTop
      (nhds (tau b - tau a)) := (hlim b hb).sub (hlim a ha)
  exact ge_of_tendsto hright
    (Filter.Eventually.of_forall fun n => hweak n a b ha hab)



theorem surfaceTensionUpperBound_of_positive_pointwise_tendsto
    (J : Real) (M tau : Real -> Real) (tauN : Nat -> Real -> Real)
    (hlim : forall beta, 0 < beta ->
      Tendsto (fun n => tauN n beta) atTop (nhds (tau beta)))
    (hupper : forall n beta, 0 < beta ->
      tauN n beta <= 2 * J * beta * (M beta) ^ 2) :
    forall beta, 0 < beta -> tau beta <=
      2 * J * beta * (M beta) ^ 2 := by
  intro beta hbeta
  exact le_of_tendsto (hlim beta hbeta)
    (Filter.Eventually.of_forall fun n => hupper n beta hbeta)




theorem rectangularIsingSurfaceTension_pos_iff_ordered_of_standard_bounds
    {betaC : Real}
    (hregime : StatMech.Ising.HasOrderedMagnetizationRegime
      (StatMech.Ising.magnetization 3) betaC)
    (hprism : forall beta, 0 < beta ->
      HasPrismCubicalSurfaceComparison beta)
    (hstandard : forall beta, 0 < beta ->
      HasStandardPrismSurfaceComparison beta)
    (hupper : forall n beta, 0 < beta ->
      standardCubicInterfaceDensity beta n <=
        2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
    (hweak : forall n,
      StatMech.Ising.HasWeakSurfaceTensionLowerBound 1
        (StatMech.Ising.magnetization 3)
        (fun beta => standardCubicInterfaceDensity beta n)) :
    forall beta, 0 < beta ->
      (0 < rectangularIsingSurfaceTension beta <-> betaC < beta) := by
  let tauN : Nat -> Real -> Real :=
    fun n beta => standardCubicInterfaceDensity beta n
  have hlim : forall beta, 0 < beta ->
      Tendsto (fun n => tauN n beta) atTop
        (nhds (rectangularIsingSurfaceTension beta)) := by
    intro beta hbeta
    exact standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension
      hbeta (hprism beta hbeta) (hstandard beta hbeta)
  have hupperLimit :=
    surfaceTensionUpperBound_of_positive_pointwise_tendsto
      1 (StatMech.Ising.magnetization 3) rectangularIsingSurfaceTension
      tauN hlim (by
        intro n beta hbeta
        simpa [tauN] using hupper n beta hbeta)
  have hweakLimit :=
    weakSurfaceTensionLowerBound_of_positive_pointwise_tendsto
      1 (StatMech.Ising.magnetization 3) rectangularIsingSurfaceTension
      tauN hlim (by simpa [tauN] using hweak)
  apply rectangularIsingSurfaceTension_pos_iff_ordered_of_weak_bounds_pos
    hregime
  · intro beta hbeta
    simpa using hupperLimit beta hbeta
  · exact hweakLimit

end

end StatMech.FrontierA
