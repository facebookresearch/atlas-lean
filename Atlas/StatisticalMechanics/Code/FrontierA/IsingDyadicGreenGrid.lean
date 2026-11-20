/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingInfraredContinuumGreen
import Mathlib.Data.ZMod.ValMinAbs

open Finset Set
open scoped BigOperators

namespace StatMech.FrontierA

variable {d k : Nat}


def isingDyadicSide (k : Nat) : Nat := 2 ^ (k + 2)


def isingTorusCenteredIntMomentum
    (p : IsingDyadicTorus d k) : Fin d → Int :=
  fun i => (p i).valMinAbs



noncomputable def isingTorusCenteredMomentum
    (p : IsingDyadicTorus d k) : IsingMomentumSpace d :=
  WithLp.toLp 2 fun i => ((p i).valMinAbs : Real) / isingDyadicSide k


noncomputable def isingTorusCenteredMomentumFun
    (p : IsingDyadicTorus d k) : Fin d → Real :=
  fun i => ((p i).valMinAbs : Real) / isingDyadicSide k

@[simp] theorem isingTorusCenteredMomentum_apply
    (p : IsingDyadicTorus d k) (i : Fin d) :
    isingTorusCenteredMomentum p i =
      ((p i).valMinAbs : Real) / isingDyadicSide k := rfl

@[simp] theorem isingTorusCenteredMomentumFun_apply
    (p : IsingDyadicTorus d k) (i : Fin d) :
    isingTorusCenteredMomentumFun p i =
      ((p i).valMinAbs : Real) / isingDyadicSide k := rfl



def isingNormalizedMomentumCube (d : Nat) : Set (IsingMomentumSpace d) :=
  {q | ∀ i, (-1 / 2 : Real) < q i ∧ q i ≤ 1 / 2}



def isingTorusLowMomentum (d k M : Nat) :
    Finset (IsingDyadicTorus d k) :=
  Finset.univ.filter fun p =>
    p ≠ 0 ∧ ∀ i : Fin d, (p i).valMinAbs.natAbs ≤ M

@[simp] theorem isingDyadicSide_eq (k : Nat) :
    isingDyadicSide k = 2 ^ (k + 2) := rfl

theorem isingDyadicSide_pos (k : Nat) : 0 < isingDyadicSide k := by
  simp [isingDyadicSide]

theorem isingTorusCenteredMomentum_mem
    (p : IsingDyadicTorus d k) :
    isingTorusCenteredMomentum p ∈ isingNormalizedMomentumCube d := by
  intro i
  have h := (p i).valMinAbs_mem_Ioc
  have hside : (0 : Real) < isingDyadicSide k := by
    exact_mod_cast isingDyadicSide_pos k
  constructor
  · rw [isingTorusCenteredMomentum_apply]
    have hInt : -(isingDyadicSide k : Int) <
        2 * (p i).valMinAbs := by
      simpa [isingDyadicSide, mul_comm] using h.1
    have hreal : -(isingDyadicSide k : Real) <
        2 * ((p i).valMinAbs : Real) := by exact_mod_cast hInt
    rw [lt_div_iff₀ hside]
    nlinarith
  · rw [isingTorusCenteredMomentum_apply]
    have hInt : 2 * (p i).valMinAbs ≤
        (isingDyadicSide k : Int) := by
      simpa [isingDyadicSide, mul_comm] using h.2
    have hreal : 2 * ((p i).valMinAbs : Real) ≤
        (isingDyadicSide k : Real) := by exact_mod_cast hInt
    rw [div_le_iff₀ hside]
    nlinarith

theorem isingTorusCenteredIntMomentum_injective :
    Function.Injective
      (isingTorusCenteredIntMomentum :
        IsingDyadicTorus d k → Fin d → Int) := by
  intro p q hpq
  funext i
  exact ZMod.injective_valMinAbs (congr_fun hpq i)

theorem isingTorusCenteredMomentum_injective :
    Function.Injective
      (isingTorusCenteredMomentum :
        IsingDyadicTorus d k → IsingMomentumSpace d) := by
  intro p q hpq
  apply isingTorusCenteredIntMomentum_injective
  funext i
  have hi := congr_fun (congr_arg WithLp.ofLp hpq) i
  simp only [isingTorusCenteredMomentum_apply] at hi
  have hside : (isingDyadicSide k : Real) ≠ 0 := by
    exact_mod_cast (isingDyadicSide_pos k).ne'
  exact_mod_cast ((div_left_inj' hside).mp hi)

theorem isingTorusCenteredMomentumFun_injective :
    Function.Injective
      (isingTorusCenteredMomentumFun :
        IsingDyadicTorus d k → Fin d → Real) := by
  intro p q hpq
  apply isingTorusCenteredIntMomentum_injective
  funext i
  have hi := congr_fun hpq i
  simp only [isingTorusCenteredMomentumFun_apply] at hi
  have hside : (isingDyadicSide k : Real) ≠ 0 := by
    exact_mod_cast (isingDyadicSide_pos k).ne'
  exact_mod_cast ((div_left_inj' hside).mp hi)

@[simp] theorem isingTorusCenteredMomentum_eq_zero_iff
    (p : IsingDyadicTorus d k) :
    isingTorusCenteredMomentum p = 0 ↔ p = 0 := by
  constructor
  · intro hp
    apply isingTorusCenteredMomentum_injective
    have hz : isingTorusCenteredMomentum
        (0 : IsingDyadicTorus d k) = 0 := by
      ext i
      simp
    exact hp.trans hz.symm
  · rintro rfl
    ext i
    simp

theorem isingTorusLowMomentum_mem_iff
    (p : IsingDyadicTorus d k) :
    p ∈ isingTorusLowMomentum d k M ↔
      p ≠ 0 ∧ ∀ i : Fin d, (p i).valMinAbs.natAbs ≤ M := by
  simp [isingTorusLowMomentum]


theorem isingTorusCharacterDispersion_centered
    (p : IsingDyadicTorus d k) :
    isingTorusCharacterDispersion (isingTorusMomentumChar p) =
      ∑ i : Fin d,
        (2 - 2 * Real.cos
          (2 * Real.pi * isingTorusCenteredMomentum p i)) := by
  rw [isingTorusCharacterDispersion_momentum_cos]
  apply Finset.sum_congr rfl
  intro i _
  have hside : (isingDyadicSide k : Real) ≠ 0 := by
    exact_mod_cast (isingDyadicSide_pos k).ne'
  change 2 - 2 * Real.cos
      (2 * Real.pi * ((p i).val : Real) / isingDyadicSide k) = _
  have hval : ((p i).val : Real) = ((p i).valMinAbs : Real) +
      if (p i).val ≤ isingDyadicSide k / 2 then 0 else isingDyadicSide k := by
    exact_mod_cast (ZMod.val_eq_ite_valMinAbs (p i))
  rw [hval]
  split_ifs with hi
  · simp only [Nat.cast_zero, add_zero,
      isingTorusCenteredMomentum_apply]
    congr 2
    ring
  · rw [isingTorusCenteredMomentum_apply]
    have harg :
        2 * Real.pi *
            (((p i).valMinAbs : Real) + isingDyadicSide k) /
              isingDyadicSide k =
          2 * Real.pi *
              (((p i).valMinAbs : Real) / isingDyadicSide k) +
            (1 : Int) * (2 * Real.pi) := by
      field_simp
      ring
    rw [harg, Real.cos_add_int_mul_two_pi]

end StatMech.FrontierA
