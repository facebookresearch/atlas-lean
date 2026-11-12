/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingDyadicGreenLowMomentum
import Code.FrontierA.IsingInfraredSpatial
import Code.Lattice.HypercubicLattice
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Order.UpperLower

open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology

namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

abbrev IsingMomentumCoordinates (d : Nat) := Fin d → Real


def isingNormalizedCoordinateCube (d : Nat) :
    Set (IsingMomentumCoordinates d) :=
  {q | ∀ i, (-1 / 2 : Real) < q i ∧ q i ≤ 1 / 2}


def isingUnitMomentumLattice (d : Nat) :
    Submodule Int (IsingMomentumCoordinates d) :=
  Submodule.span Int (Set.range (Pi.basisFun Real (Fin d)))

noncomputable def isingNormalizedCoordinateDispersion
    (q : IsingMomentumCoordinates d) : Real :=
  ∑ i : Fin d, (2 - 2 * Real.cos (2 * Real.pi * q i))


noncomputable def isingRegularizedInverseDispersion
    (eta : Real) (q : IsingMomentumCoordinates d) : Real :=
  (max (isingNormalizedCoordinateDispersion q) eta)⁻¹


noncomputable def isingRegularizedGreenIntegrand
    (eta : Real) (x : Fin d → Int) (q : IsingMomentumCoordinates d) : Real :=
  Real.cos (2 * Real.pi * ∑ i : Fin d, q i * (x i : Real)) *
    isingRegularizedInverseDispersion eta q


noncomputable def isingRegularizedGridGreen
    (eta : Real) (x : Fin d → Int) (n : Nat) : Real :=
  (∑' q : ↑(isingNormalizedCoordinateCube d ∩
      (n : Real)⁻¹ • isingUnitMomentumLattice d),
      isingRegularizedGreenIntegrand eta x q) / n ^ d


noncomputable def isingRegularizedContinuumGreen
    (eta : Real) (x : Fin d → Int) : Real :=
  ∫ q in isingNormalizedCoordinateCube d,
    isingRegularizedGreenIntegrand eta x q

theorem isingTorusCenteredMomentumFun_mem_cube
    {k : Nat} (p : IsingDyadicTorus d k) :
    isingTorusCenteredMomentumFun p ∈
      isingNormalizedCoordinateCube d := by
  intro i
  have h := isingTorusCenteredMomentum_mem p i
  simpa only [isingTorusCenteredMomentum_apply,
    isingTorusCenteredMomentumFun_apply] using h

theorem isingTorusCenteredMomentumFun_mem_lattice
    {k : Nat} (p : IsingDyadicTorus d k) :
    isingTorusCenteredMomentumFun p ∈
      ((isingDyadicSide k : Real)⁻¹ • isingUnitMomentumLattice d) := by
  let y : IsingMomentumCoordinates d :=
    fun i => ((p i).valMinAbs : Real)
  have hy : y ∈ isingUnitMomentumLattice d := by
    rw [isingUnitMomentumLattice,
      (Pi.basisFun Real (Fin d)).mem_span_iff_repr_mem Int]
    intro i
    rw [Pi.basisFun_repr]
    exact ⟨(p i).valMinAbs, rfl⟩
  change isingTorusCenteredMomentumFun p ∈
    (isingDyadicSide k : Real)⁻¹ •
      (↑(isingUnitMomentumLattice d) : Set (IsingMomentumCoordinates d))
  rw [Set.mem_smul_set]
  refine ⟨y, hy, ?_⟩
  funext i
  simp only [Pi.smul_apply, smul_eq_mul,
    isingTorusCenteredMomentumFun_apply]
  dsimp [y]
  rw [div_eq_inv_mul]



noncomputable def isingTorusMomentumGridEquiv (d k : Nat) :
    IsingDyadicTorus d k ≃
      ↑(isingNormalizedCoordinateCube d ∩
        ((isingDyadicSide k : Real)⁻¹ • isingUnitMomentumLattice d)) := by
  let f : IsingDyadicTorus d k →
      ↑(isingNormalizedCoordinateCube d ∩
        ((isingDyadicSide k : Real)⁻¹ • isingUnitMomentumLattice d)) :=
    fun p => ⟨isingTorusCenteredMomentumFun p,
      isingTorusCenteredMomentumFun_mem_cube p,
      isingTorusCenteredMomentumFun_mem_lattice p⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    apply isingTorusCenteredMomentumFun_injective
    exact congr_arg Subtype.val hpq
  · intro q
    obtain ⟨y, hyLattice, hyq⟩ := Set.mem_smul_set.mp q.property.2
    have hyInt : ∀ i : Fin d, ∃ z : Int, (z : Real) = y i := by
      intro i
      have hi := ((Pi.basisFun Real (Fin d)).mem_span_iff_repr_mem Int y).mp
        (show y ∈ Submodule.span Int
          (Set.range (Pi.basisFun Real (Fin d))) from hyLattice) i
      simpa only [Pi.basisFun_repr] using hi
    choose z hz using hyInt
    let p : IsingDyadicTorus d k :=
      fun i => (z i : ZMod (isingDyadicSide k))
    refine ⟨p, Subtype.ext ?_⟩
    funext i
    have hside : (0 : Real) < isingDyadicSide k := by
      exact_mod_cast isingDyadicSide_pos k
    have hcoord := congr_fun hyq i
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    have hqz : q.val i = (z i : Real) / isingDyadicSide k := by
      calc
        q.val i = (isingDyadicSide k : Real)⁻¹ * y i := hcoord.symm
        _ = (isingDyadicSide k : Real)⁻¹ * (z i : Real) := by rw [hz i]
        _ = (z i : Real) / isingDyadicSide k := by
          rw [div_eq_inv_mul, mul_comm]
    have hqCube := q.property.1 i
    have hlowReal : -(isingDyadicSide k : Real) <
        2 * (z i : Real) := by
      rw [hqz] at hqCube
      rw [lt_div_iff₀ hside] at hqCube
      nlinarith [hqCube.1]
    have huppReal : 2 * (z i : Real) ≤
        isingDyadicSide k := by
      rw [hqz] at hqCube
      rw [div_le_iff₀ hside] at hqCube
      nlinarith [hqCube.2]
    have hbounds : z i * 2 ∈
        Set.Ioc (-(isingDyadicSide k : Int)) (isingDyadicSide k : Int) := by
      constructor
      · have : -(isingDyadicSide k : Int) < 2 * z i := by
          exact_mod_cast hlowReal
        simpa [mul_comm] using this
      · have : 2 * z i ≤ (isingDyadicSide k : Int) := by
          exact_mod_cast huppReal
        simpa [mul_comm] using this
    have hpval :
        ((p i).valMinAbs : Int) = z i := by
      apply (ZMod.valMinAbs_spec (p i) (z i)).2
      refine ⟨?_, hbounds⟩
      change (z i : ZMod (isingDyadicSide k)) =
        (z i : ZMod (isingDyadicSide k))
      rfl
    change isingTorusCenteredMomentumFun p i = q.val i
    rw [isingTorusCenteredMomentumFun_apply, hpval]
    exact hqz.symm

@[simp] theorem isingTorusMomentumGridEquiv_apply
    {k : Nat} (p : IsingDyadicTorus d k) :
    (isingTorusMomentumGridEquiv d k p).val =
      isingTorusCenteredMomentumFun p := rfl

theorem isingNormalizedCoordinateDispersion_centered
    {k : Nat} (p : IsingDyadicTorus d k) :
    isingNormalizedCoordinateDispersion
        (isingTorusCenteredMomentumFun p) =
      isingTorusCharacterDispersion (isingTorusMomentumChar p) := by
  rw [isingTorusCharacterDispersion_centered]
  unfold isingNormalizedCoordinateDispersion
  rfl


noncomputable def isingRegularizedTorusGreen
    (eta : Real) (x : Fin d → Int) (k : Nat) : Real :=
  (∑ p : IsingDyadicTorus d k,
      isingRegularizedGreenIntegrand eta x
        (isingTorusCenteredMomentumFun p)) /
    (isingDyadicSide k : Real) ^ d


noncomputable def isingDyadicTorusGreen
    (x : Fin d → Int) (k : Nat) : Real :=
  (∑ p : IsingDyadicTorus d k,
      if p = 0 then 0 else
        Real.cos (2 * Real.pi * ∑ i : Fin d,
          isingTorusCenteredMomentumFun p i * (x i : Real)) *
        (isingTorusCharacterDispersion
          (isingTorusMomentumChar p))⁻¹) /
    (isingDyadicSide k : Real) ^ d



def isingSiteToDyadicTorus (k : Nat) (x : Site d) :
    IsingDyadicTorus d k :=
  fun i => (x i : ZMod (isingDyadicSide k))

theorem isingMomentumChar_site_re
    {k : Nat} (p : IsingDyadicTorus d k) (x : Site d) :
    (conj (isingTorusMomentumChar p
      (isingSiteToDyadicTorus k x))).re =
      Real.cos (2 * Real.pi * ∑ i : Fin d,
        isingTorusCenteredMomentumFun p i * (x i : Real)) := by
  rw [Complex.conj_re, isingTorusMomentumChar_apply]
  have hterm (i : Fin d) :
      ZMod.stdAddChar (p i * isingSiteToDyadicTorus k x i) =
        Complex.exp (((2 * Real.pi *
          isingTorusCenteredMomentumFun p i * (x i : Real) : Real) :
            Complex) * Complex.I) := by
    have harg : p i * isingSiteToDyadicTorus k x i =
        (((p i).valMinAbs * x i : Int) : ZMod (2 ^ (k + 2))) := by
      unfold isingSiteToDyadicTorus
      calc
        p i * (x i : ZMod (2 ^ (k + 2))) =
            ((p i).valMinAbs : ZMod (2 ^ (k + 2))) *
              (x i : ZMod (2 ^ (k + 2))) := by
          rw [ZMod.coe_valMinAbs]
        _ = (((p i).valMinAbs * x i : Int) :
            ZMod (2 ^ (k + 2))) := (Int.cast_mul _ _).symm
    rw [harg]
    rw [ZMod.stdAddChar_coe]
    congr 1
    simp only [isingTorusCenteredMomentumFun_apply]
    push_cast
    have hside : ((isingDyadicSide k : Real) : Complex) ≠ 0 := by
      exact_mod_cast (isingDyadicSide_pos k).ne'
    field_simp [isingDyadicSide, hside]
    simp only [isingDyadicSide, pow_add]
    norm_num
  simp_rw [hterm]
  rw [← Complex.exp_sum]
  have hsum :
      ∑ i : Fin d,
          (((2 * Real.pi * isingTorusCenteredMomentumFun p i *
            (x i : Real) : Real) : Complex) * Complex.I) =
        ((2 * Real.pi * ∑ i : Fin d,
          isingTorusCenteredMomentumFun p i * (x i : Real) : Real) :
            Complex) * Complex.I := by
    rw [← Finset.sum_mul]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, Complex.exp_ofReal_mul_I_re]

theorem isingDyadicTorus_card (d k : Nat) :
    Fintype.card (IsingDyadicTorus d k) = isingDyadicSide k ^ d := by
  simp [IsingDyadicTorus, isingDyadicSide, Fintype.card_fun]



theorem isingDyadicTorusGreen_eq_character_sum
    {k : Nat} (x : Site d) :
    isingDyadicTorusGreen x k =
      (1 / Fintype.card (IsingDyadicTorus d k) : Real) *
        ∑ p : IsingDyadicTorus d k,
          if p = 0 then 0 else
            (conj (isingTorusMomentumChar p
              (isingSiteToDyadicTorus k x))).re *
            (isingTorusCharacterDispersion
              (isingTorusMomentumChar p))⁻¹ := by
  unfold isingDyadicTorusGreen
  rw [isingDyadicTorus_card, Nat.cast_pow]
  simp_rw [isingMomentumChar_site_re]
  ring

theorem isingNormalizedCoordinateDispersion_zero :
    isingNormalizedCoordinateDispersion
      (0 : IsingMomentumCoordinates d) = 0 := by
  simp [isingNormalizedCoordinateDispersion]




theorem isingDyadicTorusGreen_sub_regularized_abs_le
    {k M : Nat} (eta : Real) (heta : 0 < eta) (x : Fin d → Int)
    (hsmall : ∀ p : IsingDyadicTorus d k, p ≠ 0 →
      isingTorusCharacterDispersion (isingTorusMomentumChar p) < eta →
      p ∈ isingTorusLowMomentum d k M) :
    |isingDyadicTorusGreen x k -
        isingRegularizedTorusGreen eta x k| ≤
      (1 / (isingDyadicSide k : Real) ^ d) *
        (eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M,
          (isingTorusCharacterDispersion
            (isingTorusMomentumChar p))⁻¹) := by
  classical
  let D : IsingDyadicTorus d k → Real := fun p =>
    isingTorusCharacterDispersion (isingTorusMomentumChar p)
  let phase : IsingDyadicTorus d k → Real := fun p =>
    Real.cos (2 * Real.pi * ∑ i : Fin d,
      isingTorusCenteredMomentumFun p i * (x i : Real))
  have hDpos (p : IsingDyadicTorus d k) (hp : p ≠ 0) : 0 < D p :=
    isingTorusCharacterDispersion_pos_of_ne_zero
      (isingTorusMomentumChar p)
      (by
        intro hzero
        exact hp ((isingTorusMomentumChar_eq_zero_iff p).mp hzero))
  have hpoint (p : IsingDyadicTorus d k) :
      |(if p = 0 then 0 else phase p * (D p)⁻¹) -
          phase p * (max (D p) eta)⁻¹| ≤
        if p = 0 then eta⁻¹ else
          if p ∈ isingTorusLowMomentum d k M then (D p)⁻¹ else 0 := by
    by_cases hp0 : p = 0
    · subst p
      have hcenter : isingTorusCenteredMomentumFun
          (0 : IsingDyadicTorus d k) = 0 := by
        funext i
        simp
      have hD0 : D (0 : IsingDyadicTorus d k) = 0 := by
        dsimp [D]
        rw [← isingNormalizedCoordinateDispersion_centered]
        rw [hcenter, isingNormalizedCoordinateDispersion_zero]
      simp only [if_true, hD0, max_eq_right heta.le]
      have hphase0 : phase (0 : IsingDyadicTorus d k) = 1 := by
        simp [phase, hcenter]
      rw [hphase0, one_mul, zero_sub, abs_neg,
        abs_of_pos (inv_pos.mpr heta)]
    · simp only [hp0, if_false]
      by_cases hlow : p ∈ isingTorusLowMomentum d k M
      · simp only [hlow, if_true]
        have hDp := hDpos p hp0
        have hmax : 0 < max (D p) eta :=
          lt_of_lt_of_le hDp (le_max_left _ _)
        have hinv : (max (D p) eta)⁻¹ ≤ (D p)⁻¹ :=
          (inv_le_inv₀ hmax hDp).2 (le_max_left _ _)
        rw [← mul_sub]
        calc
          |phase p * ((D p)⁻¹ - (max (D p) eta)⁻¹)| =
              |phase p| * ((D p)⁻¹ - (max (D p) eta)⁻¹) := by
            rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hinv)]
          _ ≤ 1 * ((D p)⁻¹ - (max (D p) eta)⁻¹) := by
            gcongr
            exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
          _ ≤ (D p)⁻¹ := by
            have : 0 ≤ (max (D p) eta)⁻¹ := inv_nonneg.mpr hmax.le
            linarith
      · simp only [hlow, if_false]
        have hnotSmall : eta ≤ D p := by
          by_contra hlt
          exact hlow (hsmall p hp0 (lt_of_not_ge hlt))
        rw [max_eq_left hnotSmall, sub_self, abs_zero]
  have hsum :
      |∑ p : IsingDyadicTorus d k,
          ((if p = 0 then 0 else phase p * (D p)⁻¹) -
            phase p * (max (D p) eta)⁻¹)| ≤
        eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M, (D p)⁻¹ := by
    calc
      |∑ p : IsingDyadicTorus d k,
          ((if p = 0 then 0 else phase p * (D p)⁻¹) -
            phase p * (max (D p) eta)⁻¹)| ≤
          ∑ p : IsingDyadicTorus d k,
            |(if p = 0 then 0 else phase p * (D p)⁻¹) -
              phase p * (max (D p) eta)⁻¹| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : IsingDyadicTorus d k,
          (if p = 0 then eta⁻¹ else
            if p ∈ isingTorusLowMomentum d k M then (D p)⁻¹ else 0) :=
        Finset.sum_le_sum fun p _ => hpoint p
      _ = eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M, (D p)⁻¹ := by
        let f : IsingDyadicTorus d k → Real := fun p =>
          if p = 0 then eta⁻¹ else
            if p ∈ isingTorusLowMomentum d k M then (D p)⁻¹ else 0
        calc
          ∑ p : IsingDyadicTorus d k, f p =
              ∑ p ∈ (Finset.univ.erase
                (0 : IsingDyadicTorus d k)), f p + f 0 :=
            (Finset.sum_erase_add Finset.univ f
              (Finset.mem_univ 0)).symm
          _ = f 0 + ∑ p ∈ (Finset.univ.erase
                (0 : IsingDyadicTorus d k)), f p := by ring
          _ = eta⁻¹ + ∑ p ∈ (Finset.univ.erase
                (0 : IsingDyadicTorus d k)), f p := by
            simp [f]
          _ = eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M, f p := by
            congr 1
            symm
            apply Finset.sum_subset
            · intro p hp
              rw [Finset.mem_erase]
              exact ⟨(isingTorusLowMomentum_mem_iff p).mp hp |>.1,
                Finset.mem_univ p⟩
            · intro p hpErase hpNotLow
              have hp0 := (Finset.mem_erase.mp hpErase).1
              simp [f, hp0, hpNotLow]
          _ = eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M,
              (D p)⁻¹ := by
            apply congrArg (eta⁻¹ + ·)
            apply Finset.sum_congr rfl
            intro p hp
            have hp0 := (isingTorusLowMomentum_mem_iff p).mp hp |>.1
            simp [f, hp0, hp]
  have hsideBase : (0 : Real) < isingDyadicSide k := by
    exact_mod_cast isingDyadicSide_pos k
  have hside : (0 : Real) < (isingDyadicSide k : Real) ^ d :=
    pow_pos hsideBase _
  unfold isingDyadicTorusGreen isingRegularizedTorusGreen
  simp only [isingRegularizedGreenIntegrand,
    isingRegularizedInverseDispersion,
    isingNormalizedCoordinateDispersion_centered]
  change |(∑ p, if p = 0 then 0 else phase p * (D p)⁻¹) /
      (isingDyadicSide k : Real) ^ d -
    (∑ p, phase p * (max (D p) eta)⁻¹) /
      (isingDyadicSide k : Real) ^ d| ≤ _
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, abs_div,
    abs_of_pos hside]
  calc
    |∑ p, ((if p = 0 then 0 else phase p * (D p)⁻¹) -
        phase p * (max (D p) eta)⁻¹)| /
        (isingDyadicSide k : Real) ^ d ≤
      (eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M, (D p)⁻¹) /
        (isingDyadicSide k : Real) ^ d :=
      div_le_div_of_nonneg_right hsum hside.le
    _ = (1 / (isingDyadicSide k : Real) ^ d) *
        (eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M,
          (isingTorusCharacterDispersion
            (isingTorusMomentumChar p))⁻¹) := by
      dsimp [D]
      ring



theorem isingTorus_smallDispersion_mem_lowMomentum
    {k : Nat} (delta eta : Real) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ 1 / 2) (heta : eta ≤ 16 * delta ^ 2)
    (p : IsingDyadicTorus d k) (hp0 : p ≠ 0)
    (hpeta : isingTorusCharacterDispersion
      (isingTorusMomentumChar p) < eta) :
    p ∈ isingTorusLowMomentum d k
      ⌈delta * isingDyadicSide k⌉₊ := by
  let L : Real := isingDyadicSide k
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast isingDyadicSide_pos k
  have hpFull : p ∈ isingTorusLowMomentum d k
      (isingDyadicSide k / 2) := by
    rw [isingTorusLowMomentum_mem_iff]
    exact ⟨hp0, fun i => ZMod.natAbs_valMinAbs_le (p i)⟩
  have hlower := isingTorusCharacterDispersion_centered_lower
    hpFull (le_refl (isingDyadicSide k / 2))
  rw [isingTorusLowMomentum_mem_iff]
  refine ⟨hp0, ?_⟩
  intro i
  let z : Real := ((p i).valMinAbs : Real)
  have hzSqLe : z ^ 2 ≤
      integerMomentumNormSq (isingTorusCenteredIntMomentum p) := by
    unfold integerMomentumNormSq
    dsimp [z, isingTorusCenteredIntMomentum]
    exact Finset.single_le_sum (s := Finset.univ)
      (fun j _ => sq_nonneg (((p j).valMinAbs : Int) : Real))
      (Finset.mem_univ i)
  have hzLower : (16 / L ^ 2) * z ^ 2 ≤
      isingTorusCharacterDispersion (isingTorusMomentumChar p) := by
    calc
      (16 / L ^ 2) * z ^ 2 ≤
          (16 / L ^ 2) *
            integerMomentumNormSq (isingTorusCenteredIntMomentum p) := by
        gcongr
      _ ≤ isingTorusCharacterDispersion (isingTorusMomentumChar p) :=
        hlower
  have hzScaled :
      ((16 / L ^ 2) * z ^ 2) * L ^ 2 <
        (16 * delta ^ 2) * L ^ 2 := by
    apply mul_lt_mul_of_pos_right _ (sq_pos_of_pos hL)
    exact lt_of_le_of_lt hzLower (hpeta.trans_le heta)
  have hzSq : z ^ 2 < (delta * L) ^ 2 := by
    field_simp [hL.ne'] at hzScaled
    nlinarith
  have hzAbs : |z| < delta * L := by
    rw [sq_lt_sq] at hzSq
    simpa [abs_of_pos (mul_pos hdelta hL)] using hzSq
  have hnatAbsCast : (((p i).valMinAbs.natAbs : Nat) : Real) = |z| := by
    dsimp [z]
    generalize (p i).valMinAbs = a
    cases a with
    | ofNat n => simp
    | negSucc n =>
        simp only [Int.cast_negSucc, Int.natAbs_negSucc,
          Nat.cast_add, Nat.cast_one]
        have hn : -((n : Real) + 1) ≤ 0 := neg_nonpos.mpr (by positivity)
        rw [abs_of_nonpos hn]
        norm_cast
  have hceil := Nat.le_ceil (delta * L)
  exact_mod_cast (show (((p i).valMinAbs.natAbs : Nat) : Real) ≤
      (⌈delta * L⌉₊ : Nat) by
    rw [hnatAbsCast]
    exact hzAbs.le.trans hceil)

theorem isingLowMomentumRadius_le_half
    {k : Nat} (delta : Real) (hdelta : 0 ≤ delta)
    (hdeltaHalf : delta ≤ 1 / 2) :
    ⌈delta * isingDyadicSide k⌉₊ ≤ isingDyadicSide k / 2 := by
  rw [Nat.ceil_le]
  have hsideEven : 2 ∣ isingDyadicSide k := by
    simp [isingDyadicSide]
  have hcast : ((isingDyadicSide k / 2 : Nat) : Real) =
      (isingDyadicSide k : Real) / 2 := by
    rw [Nat.cast_div hsideEven (by norm_num)]
    norm_num
  rw [hcast]
  have hside : (0 : Real) ≤ isingDyadicSide k := by positivity
  nlinarith

theorem isingRegularizedTorusGreen_eq_grid
    (eta : Real) (x : Fin d → Int) (k : Nat) :
    isingRegularizedTorusGreen eta x k =
      isingRegularizedGridGreen eta x (isingDyadicSide k) := by
  unfold isingRegularizedTorusGreen isingRegularizedGridGreen
  rw [← (isingTorusMomentumGridEquiv d k).tsum_eq
    (fun q => isingRegularizedGreenIntegrand eta x q)]
  simp only [isingTorusMomentumGridEquiv_apply, tsum_fintype,
    Nat.cast_pow]

theorem measurableSet_isingNormalizedCoordinateCube (d : Nat) :
    MeasurableSet (isingNormalizedCoordinateCube d) := by
  unfold isingNormalizedCoordinateCube
  rw [show {q : IsingMomentumCoordinates d |
      ∀ i, (-1 / 2 : Real) < q i ∧ q i ≤ 1 / 2} =
      ⋂ i : Fin d, ({q | (-1 / 2 : Real) < q i} ∩
        {q | q i ≤ 1 / 2}) by ext q; simp]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (measurable_pi_apply i) measurable_const)

theorem isBounded_isingNormalizedCoordinateCube (d : Nat) :
    IsBounded (isingNormalizedCoordinateCube d) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  intro q hq
  rw [Pi.norm_def]
  rw [← NNReal.coe_one, NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm,
    Real.norm_eq_abs]
  have hi := hq i
  exact (abs_le.mpr ⟨by linarith, hi.2⟩).trans (by norm_num)

theorem ordConnected_isingNormalizedCoordinateCube (d : Nat) :
    (isingNormalizedCoordinateCube d).OrdConnected := by
  constructor
  intro x hx y hy z hz i
  exact ⟨lt_of_lt_of_le (hx i).1 (hz.1 i),
    le_trans (hz.2 i) (hy i).2⟩

theorem volume_frontier_isingNormalizedCoordinateCube (d : Nat) :
    volume (frontier (isingNormalizedCoordinateCube d)) = 0 :=
  (ordConnected_isingNormalizedCoordinateCube d).null_frontier

theorem continuous_isingNormalizedCoordinateDispersion (d : Nat) :
    Continuous (isingNormalizedCoordinateDispersion :
      IsingMomentumCoordinates d → Real) := by
  unfold isingNormalizedCoordinateDispersion
  fun_prop

theorem continuous_isingRegularizedInverseDispersion
    (eta : Real) (heta : 0 < eta) :
    Continuous (isingRegularizedInverseDispersion eta :
      IsingMomentumCoordinates d → Real) := by
  unfold isingRegularizedInverseDispersion
  apply Continuous.inv₀
  · exact (continuous_isingNormalizedCoordinateDispersion d).max continuous_const
  · intro q
    exact (lt_of_lt_of_le heta (le_max_right _ _)).ne'

theorem continuous_isingRegularizedGreenIntegrand
    (eta : Real) (heta : 0 < eta) (x : Fin d → Int) :
    Continuous (isingRegularizedGreenIntegrand eta x :
      IsingMomentumCoordinates d → Real) := by
  unfold isingRegularizedGreenIntegrand
  apply Continuous.mul
  · fun_prop
  · exact continuous_isingRegularizedInverseDispersion eta heta


noncomputable def isingCoordinateFrequency (x : Fin d → Int) :
    StrongDual Real (IsingMomentumCoordinates d) :=
  ∑ i : Fin d, (x i : Real) •
    ContinuousLinearMap.proj i

@[simp] theorem isingCoordinateFrequency_apply
    (x : Fin d → Int) (q : IsingMomentumCoordinates d) :
    isingCoordinateFrequency x q =
      ∑ i : Fin d, q i * (x i : Real) := by
  unfold isingCoordinateFrequency
  simp only [ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring



noncomputable def isingRegularizedCoordinateDensity
    (eta : Real) : IsingMomentumCoordinates d → Complex :=
  (isingNormalizedCoordinateCube d).indicator
    (fun q => (isingRegularizedInverseDispersion eta q : Complex))

theorem integrable_isingRegularizedCoordinateDensity
    (eta : Real) (heta : 0 < eta) :
    Integrable (isingRegularizedCoordinateDensity eta :
      IsingMomentumCoordinates d → Complex) := by
  have hcontinuous : Continuous
      (fun q : IsingMomentumCoordinates d =>
        (isingRegularizedInverseDispersion eta q : Complex)) :=
    Complex.continuous_ofReal.comp
      (continuous_isingRegularizedInverseDispersion eta heta)
  have hbound : ∀ q : IsingMomentumCoordinates d,
      ‖(isingRegularizedInverseDispersion eta q : Complex)‖ ≤ eta⁻¹ := by
    intro q
    have hmax : 0 < max (isingNormalizedCoordinateDispersion q) eta :=
      lt_of_lt_of_le heta (le_max_right _ _)
    rw [isingRegularizedInverseDispersion, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmax)]
    exact (inv_le_inv₀ hmax heta).2 (le_max_right _ _)
  have hOn : IntegrableOn
      (fun q : IsingMomentumCoordinates d =>
        (isingRegularizedInverseDispersion eta q : Complex))
      (isingNormalizedCoordinateCube d) := by
    apply IntegrableOn.of_bound
      (isBounded_isingNormalizedCoordinateCube d).measure_lt_top
      hcontinuous.aestronglyMeasurable.restrict eta⁻¹
    exact Filter.Eventually.of_forall hbound
  exact hOn.integrable_indicator
    (measurableSet_isingNormalizedCoordinateCube d)

noncomputable def isingRegularizedCoordinateGreenComplex
    (eta : Real) : StrongDual Real (IsingMomentumCoordinates d) → Complex :=
  fun w => ∫ q, Real.fourierChar (-w q) •
    isingRegularizedCoordinateDensity eta q

theorem isingRegularizedCoordinateGreenComplex_tendsto_zero
    (eta : Real) (heta : 0 < eta) :
    Tendsto (isingRegularizedCoordinateGreenComplex (d := d) eta)
      (cocompact (StrongDual Real (IsingMomentumCoordinates d))) (nhds 0) := by
  have _ := integrable_isingRegularizedCoordinateDensity (d := d) eta heta
  simpa only [isingRegularizedCoordinateGreenComplex] using
    (tendsto_integral_exp_smul_cocompact
      (isingRegularizedCoordinateDensity eta) volume)

theorem isingRegularizedContinuumGreen_eq_re
    (eta : Real) (heta : 0 < eta) (x : Fin d → Int) :
    isingRegularizedContinuumGreen eta x =
      (isingRegularizedCoordinateGreenComplex eta
        (isingCoordinateFrequency x)).re := by
  unfold isingRegularizedContinuumGreen
    isingRegularizedCoordinateGreenComplex
  have hDensity := integrable_isingRegularizedCoordinateDensity
    (d := d) eta heta
  have hPhaseContinuous : Continuous
      (fun q : IsingMomentumCoordinates d =>
        (Real.fourierChar (-(isingCoordinateFrequency x) q) : Complex)) := by
    fun_prop
  have hIntegrable : Integrable
      (fun q : IsingMomentumCoordinates d =>
        Real.fourierChar (-(isingCoordinateFrequency x) q) •
          isingRegularizedCoordinateDensity eta q) := by
    rw [show (fun q : IsingMomentumCoordinates d =>
        Real.fourierChar (-(isingCoordinateFrequency x) q) •
          isingRegularizedCoordinateDensity eta q) =
        fun q => (Real.fourierChar
          (-(isingCoordinateFrequency x) q) : Complex) *
            isingRegularizedCoordinateDensity eta q by
      funext q
      rfl]
    apply hDensity.mono
      (hPhaseContinuous.aestronglyMeasurable.mul
        hDensity.aestronglyMeasurable)
    filter_upwards [] with q
    change ‖(Real.fourierChar
        (-(isingCoordinateFrequency x) q) : Complex) *
          isingRegularizedCoordinateDensity eta q‖ ≤ _
    rw [norm_mul, Circle.norm_coe, one_mul]
  calc
    (∫ q in isingNormalizedCoordinateCube d,
        isingRegularizedGreenIntegrand eta x q) =
        ∫ q, (Real.fourierChar
          (-(isingCoordinateFrequency x) q) •
            isingRegularizedCoordinateDensity eta q).re := by
      rw [← integral_indicator
        (measurableSet_isingNormalizedCoordinateCube d)]
      apply integral_congr_ae
      filter_upwards [] with q
      by_cases hq : q ∈ isingNormalizedCoordinateCube d
      · simp only [Set.indicator_of_mem hq]
        rw [isingRegularizedCoordinateDensity,
          Set.indicator_of_mem hq, Circle.smul_def,
          Real.fourierChar_apply, smul_eq_mul, Complex.mul_re]
        simp only [Complex.exp_ofReal_mul_I_re,
          Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
        rw [isingCoordinateFrequency_apply]
        unfold isingRegularizedGreenIntegrand
        rw [show 2 * Real.pi *
            -(∑ i : Fin d, q i * (x i : Real)) =
            -(2 * Real.pi * ∑ i : Fin d, q i * (x i : Real)) by ring,
          Real.cos_neg]
      · simp [Set.indicator_of_notMem hq,
          isingRegularizedCoordinateDensity]
    _ = (∫ q, Real.fourierChar
          (-(isingCoordinateFrequency x) q) •
            isingRegularizedCoordinateDensity eta q).re :=
      integral_re hIntegrable

theorem isingCoordinateFrequency_coord_abs_le_norm
    (x : Fin d → Int) (i : Fin d) :
    |(x i : Real)| ≤ ‖isingCoordinateFrequency x‖ := by
  let e : IsingMomentumCoordinates d := Pi.single i 1
  have heNorm : ‖e‖ = 1 := by
    change ‖(Pi.single i 1 : Fin d → Real)‖ = 1
    rw [Pi.norm_single]
    norm_num
  have happ : isingCoordinateFrequency x e = (x i : Real) := by
    rw [isingCoordinateFrequency_apply]
    rw [Finset.sum_eq_single i]
    · simp [e]
    · intro j _ hji
      simp [e, hji]
    · simp
  calc
    |(x i : Real)| = ‖isingCoordinateFrequency x e‖ := by
      rw [happ, Real.norm_eq_abs]
    _ ≤ ‖isingCoordinateFrequency x‖ * ‖e‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖isingCoordinateFrequency x‖ := by rw [heNorm, mul_one]



theorem isingRegularizedContinuumGreen_decay
    (eta : Real) (heta : 0 < eta) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ R : Nat, ∀ x : Site d, x ∉ box d R →
      |isingRegularizedContinuumGreen eta x| < epsilon := by
  have htend := isingRegularizedCoordinateGreenComplex_tendsto_zero
    (d := d) eta heta
  have hevent : ∀ᶠ w : StrongDual Real (IsingMomentumCoordinates d) in
      cocompact (StrongDual Real (IsingMomentumCoordinates d)),
      ‖isingRegularizedCoordinateGreenComplex eta w‖ < epsilon := by
    have hmetric := (Metric.tendsto_nhds.mp htend) epsilon hepsilon
    filter_upwards [hmetric] with w hw
    simpa only [dist_zero_right] using hw
  obtain ⟨K, hKcompact, hKsub⟩ := Filter.mem_cocompact.mp hevent
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hKcompact.isBounded
  obtain ⟨R, hR⟩ := exists_nat_gt C
  refine ⟨R, ?_⟩
  intro x hx
  have hxExists : ∃ i : Fin d, R < (x i).natAbs := by
    simpa only [mem_box, not_forall, not_le] using hx
  obtain ⟨i, hi⟩ := hxExists
  have habs : (R : Real) < |(x i : Real)| := by
    have hiInt : (R : Int) < |x i| := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hi
    exact_mod_cast hiInt
  have hfreqNotMem : isingCoordinateFrequency x ∉ K := by
    intro hmem
    have hnorm := hC _ hmem
    have hcoord := isingCoordinateFrequency_coord_abs_le_norm x i
    linarith
  have hcomplex :
      ‖isingRegularizedCoordinateGreenComplex eta
        (isingCoordinateFrequency x)‖ < epsilon :=
    hKsub (by simpa using hfreqNotMem)
  rw [isingRegularizedContinuumGreen_eq_re eta heta x]
  exact (Complex.abs_re_le_norm _).trans_lt hcomplex



theorem isingRegularizedGridGreen_tendsto
    (eta : Real) (heta : 0 < eta) (x : Fin d → Int) :
    Tendsto (isingRegularizedGridGreen eta x) atTop
      (nhds (isingRegularizedContinuumGreen eta x)) := by
  simpa only [isingRegularizedGridGreen, isingRegularizedContinuumGreen,
    isingUnitMomentumLattice, Fintype.card_fin] using
    (tendsto_tsum_div_pow_atTop_integral
      (isingNormalizedCoordinateCube d)
      (isingRegularizedGreenIntegrand eta x)
      (continuous_isingRegularizedGreenIntegrand eta heta x)
      (isBounded_isingNormalizedCoordinateCube d)
      (measurableSet_isingNormalizedCoordinateCube d)
      (volume_frontier_isingNormalizedCoordinateCube d))


theorem isingRegularizedDyadicGridGreen_tendsto
    (eta : Real) (heta : 0 < eta) (x : Fin d → Int) :
    Tendsto (fun k =>
      isingRegularizedGridGreen eta x (isingDyadicSide k)) atTop
      (nhds (isingRegularizedContinuumGreen eta x)) := by
  have hside : Tendsto isingDyadicSide atTop atTop := by
    unfold isingDyadicSide
    rw [Filter.tendsto_add_atTop_iff_nat]
    exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
  exact (isingRegularizedGridGreen_tendsto eta heta x).comp
    hside


theorem isingRegularizedTorusGreen_tendsto
    (eta : Real) (heta : 0 < eta) (x : Fin d → Int) :
    Tendsto (isingRegularizedTorusGreen eta x) atTop
      (nhds (isingRegularizedContinuumGreen eta x)) := by
  rw [show isingRegularizedTorusGreen eta x =
      fun k => isingRegularizedGridGreen eta x (isingDyadicSide k) by
    funext k
    exact isingRegularizedTorusGreen_eq_grid eta x k]
  exact isingRegularizedDyadicGridGreen_tendsto eta heta x



theorem isingDyadicTorusGreen_eventually_close_continuum
    (hd : 2 < d) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ eta : Real, 0 < eta ∧ ∀ x : Site d,
      ∀ᶠ k : Nat in atTop,
        |isingDyadicTorusGreen x k -
          isingRegularizedContinuumGreen eta x| < epsilon := by
  obtain ⟨C, hCpos, hC⟩ :=
    isingTorusLowMomentum_inverseDispersion_le hd
  let delta : Real := min (1 / 4) (epsilon / (16 * C))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by norm_num) (div_pos hepsilon (mul_pos (by norm_num) hCpos))
  have hdeltaQuarter : delta ≤ 1 / 4 := min_le_left _ _
  have hdeltaHalf : delta ≤ 1 / 2 := hdeltaQuarter.trans (by norm_num)
  have hdeltaEps : delta ≤ epsilon / (16 * C) := min_le_right _ _
  let eta : Real := 16 * delta ^ 2
  have heta : 0 < eta := by dsimp [eta]; positivity
  refine ⟨eta, heta, ?_⟩
  intro x
  have hsideNat : Tendsto isingDyadicSide atTop atTop := by
    unfold isingDyadicSide
    rw [Filter.tendsto_add_atTop_iff_nat]
    exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
  have hsideReal : Tendsto (fun k => (isingDyadicSide k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hsideNat
  have hlargeDelta : ∀ᶠ k : Nat in atTop,
      1 / delta ≤ (isingDyadicSide k : Real) :=
    hsideReal.eventually_ge_atTop (1 / delta)
  have hlargeZero : ∀ᶠ k : Nat in atTop,
      8 * eta⁻¹ / epsilon ≤ (isingDyadicSide k : Real) :=
    hsideReal.eventually_ge_atTop (8 * eta⁻¹ / epsilon)
  have hreg := isingRegularizedTorusGreen_tendsto eta heta x
  have hregClose : ∀ᶠ k : Nat in atTop,
      |isingRegularizedTorusGreen eta x k -
        isingRegularizedContinuumGreen eta x| < epsilon / 2 := by
    have hmetric := (Metric.tendsto_nhds.mp hreg)
      (epsilon / 2) (half_pos hepsilon)
    filter_upwards [hmetric] with k hk
    simpa only [Real.dist_eq] using hk
  filter_upwards [hlargeDelta, hlargeZero, hregClose] with k hkDelta hkZero hkReg
  let M : Nat := ⌈delta * isingDyadicSide k⌉₊
  have hMpos : 1 ≤ M := by
    dsimp [M]
    have hsReal : (0 : Real) < (isingDyadicSide k : Real) := by
      exact_mod_cast isingDyadicSide_pos k
    have hpos := Nat.ceil_pos.mpr (mul_pos hdelta hsReal)
    exact hpos
  have hMhalf : M ≤ isingDyadicSide k / 2 := by
    exact isingLowMomentumRadius_le_half delta hdelta.le hdeltaHalf
  have hsupport : ∀ p : IsingDyadicTorus d k, p ≠ 0 →
      isingTorusCharacterDispersion (isingTorusMomentumChar p) < eta →
      p ∈ isingTorusLowMomentum d k M := by
    intro p hp0 hpeta
    exact isingTorus_smallDispersion_mem_lowMomentum
      delta eta hdelta hdeltaHalf (le_refl eta) p hp0 hpeta
  have hfinite := isingDyadicTorusGreen_sub_regularized_abs_le
    eta heta x hsupport
  have hLpos : (0 : Real) < isingDyadicSide k := by
    exact_mod_cast isingDyadicSide_pos k
  have hLone : (1 : Real) ≤ isingDyadicSide k := by
    exact_mod_cast (show 1 ≤ isingDyadicSide k by
      exact Nat.one_le_iff_ne_zero.mpr (isingDyadicSide_pos k).ne')
  have hdOne : 1 ≤ d := by omega
  have hLpow : (isingDyadicSide k : Real) ≤
      (isingDyadicSide k : Real) ^ d := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hLone hdOne :
        (isingDyadicSide k : Real) ^ 1 ≤
          (isingDyadicSide k : Real) ^ d)
  have hzero :
      (1 / (isingDyadicSide k : Real) ^ d) * eta⁻¹ ≤ epsilon / 8 := by
    have hetaInv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
    have hfirst :
        (1 / (isingDyadicSide k : Real) ^ d) * eta⁻¹ ≤
          eta⁻¹ / (isingDyadicSide k : Real) := by
      rw [one_div, div_eq_mul_inv, mul_comm eta⁻¹]
      gcongr
    calc
      (1 / (isingDyadicSide k : Real) ^ d) * eta⁻¹ ≤
          eta⁻¹ / (isingDyadicSide k : Real) := hfirst
      _ ≤ epsilon / 8 := by
        apply (div_le_iff₀ hLpos).2
        have hprod := mul_le_mul_of_nonneg_left hkZero hepsilon.le
        have hetaInvPos : 0 < eta⁻¹ := inv_pos.mpr heta
        field_simp [hepsilon.ne', heta.ne'] at hprod ⊢
        nlinarith
  have hMratio : (M : Real) / isingDyadicSide k < 2 * delta := by
    have hceil := Nat.ceil_lt_add_one
      (mul_nonneg hdelta.le (by positivity) :
        0 ≤ delta * (isingDyadicSide k : Real))
    have hceilM : (M : Real) <
        delta * (isingDyadicSide k : Real) + 1 := by
      simpa only [M] using hceil
    apply (div_lt_iff₀ hLpos).2
    have hinvBound : 1 ≤ delta * (isingDyadicSide k : Real) := by
      calc
        1 = delta * (1 / delta) := by field_simp
        _ ≤ delta * (isingDyadicSide k : Real) :=
          mul_le_mul_of_nonneg_left hkDelta hdelta.le
    nlinarith [hceilM]
  have hbase : 0 ≤ (M : Real) / isingDyadicSide k := by positivity
  have hlowRaw := hC k M hMpos hMhalf
  have hlow :
      (1 / (isingDyadicSide k : Real) ^ d) *
          ∑ p ∈ isingTorusLowMomentum d k M,
            (isingTorusCharacterDispersion
              (isingTorusMomentumChar p))⁻¹ ≤ epsilon / 8 := by
    have htwoDelta : 0 ≤ 2 * delta := by positivity
    have hpowMono :
        ((M : Real) / isingDyadicSide k) ^ (d - 2) ≤
          (2 * delta) ^ (d - 2) :=
      pow_le_pow_left₀ hbase hMratio.le _
    have htwoLeOne : 2 * delta ≤ 1 := by linarith
    have hexp : 1 ≤ d - 2 := by omega
    have hpowSmall : (2 * delta) ^ (d - 2) ≤ 2 * delta := by
      simpa only [pow_one] using
        (pow_le_pow_of_le_one htwoDelta htwoLeOne hexp :
          (2 * delta) ^ (d - 2) ≤ (2 * delta) ^ 1)
    calc
      (1 / (isingDyadicSide k : Real) ^ d) *
          ∑ p ∈ isingTorusLowMomentum d k M,
            (isingTorusCharacterDispersion
              (isingTorusMomentumChar p))⁻¹ ≤
          C * ((M : Real) / isingDyadicSide k) ^ (d - 2) := hlowRaw
      _ ≤ C * (2 * delta) ^ (d - 2) := by gcongr
      _ ≤ C * (2 * delta) := by gcongr
      _ ≤ epsilon / 8 := by
        have hmul := mul_le_mul_of_nonneg_left hdeltaEps hCpos.le
        field_simp [hCpos.ne'] at hmul ⊢
        nlinarith
  have hfiniteSmall : |isingDyadicTorusGreen x k -
      isingRegularizedTorusGreen eta x k| ≤ epsilon / 4 := by
    calc
      |isingDyadicTorusGreen x k - isingRegularizedTorusGreen eta x k| ≤
          (1 / (isingDyadicSide k : Real) ^ d) *
            (eta⁻¹ + ∑ p ∈ isingTorusLowMomentum d k M,
              (isingTorusCharacterDispersion
                (isingTorusMomentumChar p))⁻¹) := hfinite
      _ = (1 / (isingDyadicSide k : Real) ^ d) * eta⁻¹ +
          (1 / (isingDyadicSide k : Real) ^ d) *
            ∑ p ∈ isingTorusLowMomentum d k M,
              (isingTorusCharacterDispersion
                (isingTorusMomentumChar p))⁻¹ := by ring
      _ ≤ epsilon / 8 + epsilon / 8 := add_le_add hzero hlow
      _ = epsilon / 4 := by ring
  calc
    |isingDyadicTorusGreen x k - isingRegularizedContinuumGreen eta x| ≤
        |isingDyadicTorusGreen x k - isingRegularizedTorusGreen eta x k| +
          |isingRegularizedTorusGreen eta x k -
            isingRegularizedContinuumGreen eta x| := by
      simpa only [sub_add_sub_cancel] using
        (abs_add_le
          (isingDyadicTorusGreen x k - isingRegularizedTorusGreen eta x k)
          (isingRegularizedTorusGreen eta x k -
            isingRegularizedContinuumGreen eta x))
    _ < epsilon / 4 + epsilon / 2 := add_lt_add_of_le_of_lt hfiniteSmall hkReg
    _ < epsilon := by linarith



theorem isingDyadicTorusGreen_eventually_small_outside_box
    (hd : 2 < d) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ R : Nat, ∀ x : Site d, x ∉ box d R →
      ∀ᶠ k : Nat in atTop, |isingDyadicTorusGreen x k| < epsilon := by
  obtain ⟨eta, heta, hclose⟩ :=
    isingDyadicTorusGreen_eventually_close_continuum
      hd (epsilon / 2) (half_pos hepsilon)
  obtain ⟨R, hR⟩ := isingRegularizedContinuumGreen_decay
    eta heta (epsilon / 2) (half_pos hepsilon)
  refine ⟨R, ?_⟩
  intro x hx
  have hlimit := hR x hx
  filter_upwards [hclose x] with k hk
  calc
    |isingDyadicTorusGreen x k| =
        |(isingDyadicTorusGreen x k -
            isingRegularizedContinuumGreen eta x) +
          isingRegularizedContinuumGreen eta x| := by ring_nf
    _ ≤ |isingDyadicTorusGreen x k -
          isingRegularizedContinuumGreen eta x| +
        |isingRegularizedContinuumGreen eta x| := abs_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hk hlimit
    _ = epsilon := by ring

end StatMech.FrontierA
