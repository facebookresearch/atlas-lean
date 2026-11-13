/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeMomentBounds



open Finset SimpleGraph
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]




theorem expJ_spinProd_sq_mul_sq_le_symmDiff_sq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    (A B : Finset V) :
    (expJ G.edgeFinset J hf (spinProd A)) ^ 2 *
        (expJ G.edgeFinset J hf (spinProd B)) ^ 2 <=
      (expJ G.edgeFinset J hf (spinProd (A ∆ B))) ^ 2 := by
  have hA : 0 <= expJ G.edgeFinset J hf (spinProd A) :=
    ghsvp_expJ_nonneg G.edgeFinset J hf (fun e _ => hJ e) hhf A
  have hB : 0 <= expJ G.edgeFinset J hf (spinProd B) :=
    ghsvp_expJ_nonneg G.edgeFinset J hf (fun e _ => hJ e) hhf B
  have hgks := gks_second_J G.edgeFinset J hf
    (fun e _ => hJ e) hhf A B
  have hsq := mul_self_le_mul_self (mul_nonneg hA hB) hgks
  nlinarith

set_option maxHeartbeats 2000000 in



theorem fourBridgeOneCoeff_mul_fourCoeff_le_threeCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeOneCoeff G J hf w x y z *
        fourBridgeFourCoeff G J hf w x y z <=
      fourBridgeThreeCoeff G J hf w x y z := by
  let M : Finset V := {w, x, y, z}
  have hMw : ({w} : Finset V) ∆ M = {x, y, z} := by
    ext a
    simp only [mem_symmDiff, mem_singleton, mem_insert]
    by_cases haw : a = w <;> by_cases hax : a = x <;>
      by_cases hay : a = y <;> by_cases haz : a = z <;>
      simp_all [M]
  have hMx : ({x} : Finset V) ∆ M = {w, y, z} := by
    ext a
    simp only [mem_symmDiff, mem_singleton, mem_insert]
    by_cases haw : a = w <;> by_cases hax : a = x <;>
      by_cases hay : a = y <;> by_cases haz : a = z <;>
      simp_all [M]
  have hMy : ({y} : Finset V) ∆ M = {w, x, z} := by
    ext a
    simp only [mem_symmDiff, mem_singleton, mem_insert]
    by_cases haw : a = w <;> by_cases hax : a = x <;>
      by_cases hay : a = y <;> by_cases haz : a = z <;>
      simp_all [M]
  have hMz : ({z} : Finset V) ∆ M = {w, x, y} := by
    ext a
    simp only [mem_symmDiff, mem_singleton, mem_insert]
    by_cases haw : a = w <;> by_cases hax : a = x <;>
      by_cases hay : a = y <;> by_cases haz : a = z <;>
      simp_all [M]
  have hM : spinProd M =
      fun s => spin s w * (spin s x * (spin s y * spin s z)) := by
    funext s
    simp [M, spinProd, hwx, hwy, hwz, hxy, hxz, hyz]
  have htw : spinProd ({x, y, z} : Finset V) =
      fun s => spin s x * (spin s y * spin s z) := by
    funext s
    simp [spinProd, hxy, hxz, hyz]
  have htx : spinProd ({w, y, z} : Finset V) =
      fun s => spin s w * (spin s y * spin s z) := by
    funext s
    simp [spinProd, hwy, hwz, hyz]
  have hty : spinProd ({w, x, z} : Finset V) =
      fun s => spin s w * (spin s x * spin s z) := by
    funext s
    simp [spinProd, hwx, hwz, hxz]
  have htz : spinProd ({w, x, y} : Finset V) =
      fun s => spin s w * (spin s x * spin s y) := by
    funext s
    simp [spinProd, hwx, hwy, hxy]
  have hw := expJ_spinProd_sq_mul_sq_le_symmDiff_sq
    G J hf hJ hhf ({w} : Finset V) M
  have hx := expJ_spinProd_sq_mul_sq_le_symmDiff_sq
    G J hf hJ hhf ({x} : Finset V) M
  have hy := expJ_spinProd_sq_mul_sq_le_symmDiff_sq
    G J hf hJ hhf ({y} : Finset V) M
  have hz := expJ_spinProd_sq_mul_sq_le_symmDiff_sq
    G J hf hJ hhf ({z} : Finset V) M
  rw [spinProd_singleton, hM, hMw, htw] at hw
  rw [spinProd_singleton, hM, hMx, htx] at hx
  rw [spinProd_singleton, hM, hMy, hty] at hy
  rw [spinProd_singleton, hM, hMz, htz] at hz
  dsimp [fourBridgeOneCoeff, fourBridgeThreeCoeff,
    fourBridgeFourCoeff]
  nlinarith

set_option maxHeartbeats 2000000 in



theorem fourBridgeThreeCoeff_mul_fourCoeff_le_oneCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeThreeCoeff G J hf w x y z *
        fourBridgeFourCoeff G J hf w x y z <=
      fourBridgeOneCoeff G J hf w x y z := by
  let M : Finset V := {w, x, y, z}
  have hMw : ({x, y, z} : Finset V) ∆ M = {w} := by
    ext a
    simp only [mem_symmDiff, mem_singleton, mem_insert]
    by_cases haw : a = w <;> by_cases hax : a = x <;>
      by_cases hay : a = y <;> by_cases haz : a = z <;>
      simp_all [M]
  have hMx : ({w, y, z} : Finset V) ∆ M = {x} := by
    ext a
    simp only [mem_symmDiff, mem_singleton, mem_insert]
    by_cases haw : a = w <;> by_cases hax : a = x <;>
      by_cases hay : a = y <;> by_cases haz : a = z <;>
      simp_all [M]
  have hMy : ({w, x, z} : Finset V) ∆ M = {y} := by
    ext a
    simp only [mem_symmDiff, mem_singleton, mem_insert]
    by_cases haw : a = w <;> by_cases hax : a = x <;>
      by_cases hay : a = y <;> by_cases haz : a = z <;>
      simp_all [M]
  have hMz : ({w, x, y} : Finset V) ∆ M = {z} := by
    ext a
    simp only [mem_symmDiff, mem_singleton, mem_insert]
    by_cases haw : a = w <;> by_cases hax : a = x <;>
      by_cases hay : a = y <;> by_cases haz : a = z <;>
      simp_all [M]
  have hM : spinProd M =
      fun s => spin s w * (spin s x * (spin s y * spin s z)) := by
    funext s
    simp [M, spinProd, hwx, hwy, hwz, hxy, hxz, hyz]
  have htw : spinProd ({x, y, z} : Finset V) =
      fun s => spin s x * (spin s y * spin s z) := by
    funext s
    simp [spinProd, hxy, hxz, hyz]
  have htx : spinProd ({w, y, z} : Finset V) =
      fun s => spin s w * (spin s y * spin s z) := by
    funext s
    simp [spinProd, hwy, hwz, hyz]
  have hty : spinProd ({w, x, z} : Finset V) =
      fun s => spin s w * (spin s x * spin s z) := by
    funext s
    simp [spinProd, hwx, hwz, hxz]
  have htz : spinProd ({w, x, y} : Finset V) =
      fun s => spin s w * (spin s x * spin s y) := by
    funext s
    simp [spinProd, hwx, hwy, hxy]
  have hw := expJ_spinProd_sq_mul_sq_le_symmDiff_sq
    G J hf hJ hhf ({x, y, z} : Finset V) M
  have hx := expJ_spinProd_sq_mul_sq_le_symmDiff_sq
    G J hf hJ hhf ({w, y, z} : Finset V) M
  have hy := expJ_spinProd_sq_mul_sq_le_symmDiff_sq
    G J hf hJ hhf ({w, x, z} : Finset V) M
  have hz := expJ_spinProd_sq_mul_sq_le_symmDiff_sq
    G J hf hJ hhf ({w, x, y} : Finset V) M
  rw [htw, hM, hMw, spinProd_singleton] at hw
  rw [htx, hM, hMx, spinProd_singleton] at hx
  rw [hty, hM, hMy, spinProd_singleton] at hy
  rw [htz, hM, hMz, spinProd_singleton] at hz
  dsimp [fourBridgeOneCoeff, fourBridgeThreeCoeff,
    fourBridgeFourCoeff]
  nlinarith



theorem fourBridge_four_by_four_product_sum_le
    {u0 u1 u2 u3 t0 t1 t2 t3 p01 p02 p03 p12 p13 p23 r : Real}
    (h00 : u0 * t0 <= r) (h11 : u1 * t1 <= r)
    (h22 : u2 * t2 <= r) (h33 : u3 * t3 <= r)
    (h01 : u0 * t1 <= p23) (h02 : u0 * t2 <= p13)
    (h03 : u0 * t3 <= p12) (h10 : u1 * t0 <= p23)
    (h12 : u1 * t2 <= p03) (h13 : u1 * t3 <= p02)
    (h20 : u2 * t0 <= p13) (h21 : u2 * t1 <= p03)
    (h23 : u2 * t3 <= p01) (h30 : u3 * t0 <= p12)
    (h31 : u3 * t1 <= p02) (h32 : u3 * t2 <= p01) :
    (u0 + u1 + u2 + u3) * (t0 + t1 + t2 + t3) <=
      2 * (p01 + p02 + p03 + p12 + p13 + p23) + 4 * r := by
  nlinarith



theorem fourBridge_four_by_six_product_sum_le
    {u0 u1 u2 u3 p01 p02 p03 p12 p13 p23 t0 t1 t2 t3 : Real}
    (h001 : u0 * p01 <= u1) (h002 : u0 * p02 <= u2)
    (h003 : u0 * p03 <= u3) (h012 : u0 * p12 <= t3)
    (h013 : u0 * p13 <= t2) (h023 : u0 * p23 <= t1)
    (h101 : u1 * p01 <= u0) (h102 : u1 * p02 <= t3)
    (h103 : u1 * p03 <= t2) (h112 : u1 * p12 <= u2)
    (h113 : u1 * p13 <= u3) (h123 : u1 * p23 <= t0)
    (h201 : u2 * p01 <= t3) (h202 : u2 * p02 <= u0)
    (h203 : u2 * p03 <= t1) (h212 : u2 * p12 <= u1)
    (h213 : u2 * p13 <= t0) (h223 : u2 * p23 <= u3)
    (h301 : u3 * p01 <= t2) (h302 : u3 * p02 <= t1)
    (h303 : u3 * p03 <= u0) (h312 : u3 * p12 <= t0)
    (h313 : u3 * p13 <= u1) (h323 : u3 * p23 <= u2) :
    (u0 + u1 + u2 + u3) * (p01 + p02 + p03 + p12 + p13 + p23) <=
      3 * ((u0 + u1 + u2 + u3) + (t0 + t1 + t2 + t3)) := by
  nlinarith

set_option maxHeartbeats 4000000 in




theorem fourBridgeOneCoeff_mul_threeCoeff_le_two_mul_twoCoeff_add_four_mul_fourCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeOneCoeff G J hf w x y z *
        fourBridgeThreeCoeff G J hf w x y z <=
      2 * fourBridgeTwoCoeff G J hf w x y z +
        4 * fourBridgeFourCoeff G J hf w x y z := by
  let M : Finset V := {w, x, y, z}
  let uw := (expJ G.edgeFinset J hf (spinProd {w})) ^ 2
  let ux := (expJ G.edgeFinset J hf (spinProd {x})) ^ 2
  let uy := (expJ G.edgeFinset J hf (spinProd {y})) ^ 2
  let uz := (expJ G.edgeFinset J hf (spinProd {z})) ^ 2
  let tw := (expJ G.edgeFinset J hf (spinProd {x, y, z})) ^ 2
  let tx := (expJ G.edgeFinset J hf (spinProd {w, y, z})) ^ 2
  let ty := (expJ G.edgeFinset J hf (spinProd {w, x, z})) ^ 2
  let tz := (expJ G.edgeFinset J hf (spinProd {w, x, y})) ^ 2
  let pwx := (expJ G.edgeFinset J hf (spinProd {w, x})) ^ 2
  let pwy := (expJ G.edgeFinset J hf (spinProd {w, y})) ^ 2
  let pwz := (expJ G.edgeFinset J hf (spinProd {w, z})) ^ 2
  let pxy := (expJ G.edgeFinset J hf (spinProd {x, y})) ^ 2
  let pxz := (expJ G.edgeFinset J hf (spinProd {x, z})) ^ 2
  let pyz := (expJ G.edgeFinset J hf (spinProd {y, z})) ^ 2
  let r := (expJ G.edgeFinset J hf (spinProd M)) ^ 2
  have hcut (A B C : Finset V) (hAB : A ∆ B = C) :
      (expJ G.edgeFinset J hf (spinProd A)) ^ 2 *
          (expJ G.edgeFinset J hf (spinProd B)) ^ 2 <=
        (expJ G.edgeFinset J hf (spinProd C)) ^ 2 := by
    simpa only [hAB] using
      expJ_spinProd_sq_mul_sq_le_symmDiff_sq G J hf hJ hhf A B
  have h00 : uw * tw <= r := by
    dsimp [uw, tw, r]
    apply hcut
    ext a
    simp [M, mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h11 : ux * tx <= r := by
    dsimp [ux, tx, r]
    apply hcut
    ext a
    simp [M, mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h22 : uy * ty <= r := by
    dsimp [uy, ty, r]
    apply hcut
    ext a
    simp [M, mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h33 : uz * tz <= r := by
    dsimp [uz, tz, r]
    apply hcut
    ext a
    simp [M, mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h01 : uw * tx <= pyz := by
    dsimp [uw, tx, pyz]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h02 : uw * ty <= pxz := by
    dsimp [uw, ty, pxz]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h03 : uw * tz <= pxy := by
    dsimp [uw, tz, pxy]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h10 : ux * tw <= pyz := by
    dsimp [ux, tw, pyz]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h12 : ux * ty <= pwz := by
    dsimp [ux, ty, pwz]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h13 : ux * tz <= pwy := by
    dsimp [ux, tz, pwy]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h20 : uy * tw <= pxz := by
    dsimp [uy, tw, pxz]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h21 : uy * tx <= pwz := by
    dsimp [uy, tx, pwz]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h23 : uy * tz <= pwx := by
    dsimp [uy, tz, pwx]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h30 : uz * tw <= pxy := by
    dsimp [uz, tw, pxy]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h31 : uz * tx <= pwy := by
    dsimp [uz, tx, pwy]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h32 : uz * ty <= pwx := by
    dsimp [uz, ty, pwx]
    apply hcut
    ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h := fourBridge_four_by_four_product_sum_le
    h00 h11 h22 h33 h01 h02 h03 h10 h12 h13 h20 h21 h23 h30 h31 h32
  dsimp [uw, ux, uy, uz, tw, tx, ty, tz, pwx, pwy, pwz,
    pxy, pxz, pyz, r, M] at h
  rw [spinProd_singleton, spinProd_singleton, spinProd_singleton,
    spinProd_singleton, spinProd_pair w x hwx, spinProd_pair w y hwy,
    spinProd_pair w z hwz, spinProd_pair x y hxy, spinProd_pair x z hxz,
    spinProd_pair y z hyz] at h
  have htw : spinProd ({x, y, z} : Finset V) =
      fun s => spin s x * (spin s y * spin s z) := by
    funext s
    simp [spinProd, hxy, hxz, hyz]
  have htx : spinProd ({w, y, z} : Finset V) =
      fun s => spin s w * (spin s y * spin s z) := by
    funext s
    simp [spinProd, hwy, hwz, hyz]
  have hty : spinProd ({w, x, z} : Finset V) =
      fun s => spin s w * (spin s x * spin s z) := by
    funext s
    simp [spinProd, hwx, hwz, hxz]
  have htz : spinProd ({w, x, y} : Finset V) =
      fun s => spin s w * (spin s x * spin s y) := by
    funext s
    simp [spinProd, hwx, hwy, hxy]
  have hM : spinProd ({w, x, y, z} : Finset V) =
      fun s => spin s w * (spin s x * (spin s y * spin s z)) := by
    funext s
    simp [spinProd, hwx, hwy, hwz, hxy, hxz, hyz]
  rw [htw, htx, hty, htz, hM] at h
  simpa [fourBridgeOneCoeff, fourBridgeTwoCoeff, fourBridgeThreeCoeff,
    fourBridgeFourCoeff, add_assoc, add_left_comm, add_comm] using h

set_option maxHeartbeats 4000000 in




theorem fourBridgeOneCoeff_mul_twoCoeff_le_three_mul_one_add_three
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeOneCoeff G J hf w x y z *
        fourBridgeTwoCoeff G J hf w x y z <=
      3 * (fourBridgeOneCoeff G J hf w x y z +
        fourBridgeThreeCoeff G J hf w x y z) := by
  let uw := (expJ G.edgeFinset J hf (spinProd {w})) ^ 2
  let ux := (expJ G.edgeFinset J hf (spinProd {x})) ^ 2
  let uy := (expJ G.edgeFinset J hf (spinProd {y})) ^ 2
  let uz := (expJ G.edgeFinset J hf (spinProd {z})) ^ 2
  let pwx := (expJ G.edgeFinset J hf (spinProd {w, x})) ^ 2
  let pwy := (expJ G.edgeFinset J hf (spinProd {w, y})) ^ 2
  let pwz := (expJ G.edgeFinset J hf (spinProd {w, z})) ^ 2
  let pxy := (expJ G.edgeFinset J hf (spinProd {x, y})) ^ 2
  let pxz := (expJ G.edgeFinset J hf (spinProd {x, z})) ^ 2
  let pyz := (expJ G.edgeFinset J hf (spinProd {y, z})) ^ 2
  let tw := (expJ G.edgeFinset J hf (spinProd {x, y, z})) ^ 2
  let tx := (expJ G.edgeFinset J hf (spinProd {w, y, z})) ^ 2
  let ty := (expJ G.edgeFinset J hf (spinProd {w, x, z})) ^ 2
  let tz := (expJ G.edgeFinset J hf (spinProd {w, x, y})) ^ 2
  have hcut (A B C : Finset V) (hAB : A ∆ B = C) :
      (expJ G.edgeFinset J hf (spinProd A)) ^ 2 *
          (expJ G.edgeFinset J hf (spinProd B)) ^ 2 <=
        (expJ G.edgeFinset J hf (spinProd C)) ^ 2 := by
    simpa only [hAB] using
      expJ_spinProd_sq_mul_sq_le_symmDiff_sq G J hf hJ hhf A B
  have hsymm (A B C : Finset V) (hAB : A ∆ B = C) :
      (expJ G.edgeFinset J hf (spinProd A)) ^ 2 *
          (expJ G.edgeFinset J hf (spinProd B)) ^ 2 <=
        (expJ G.edgeFinset J hf (spinProd C)) ^ 2 := hcut A B C hAB
  have hs (A B C : Finset V) (hAB : A ∆ B = C) := hsymm A B C hAB
  have h001 : uw * pwx <= ux := by
    apply hs
    ext a; simp [mem_symmDiff, hwx, hwx.symm] <;> aesop
  have h002 : uw * pwy <= uy := by
    apply hs
    ext a; simp [mem_symmDiff, hwy, hwy.symm] <;> aesop
  have h003 : uw * pwz <= uz := by
    apply hs
    ext a; simp [mem_symmDiff, hwz, hwz.symm] <;> aesop
  have h012 : uw * pxy <= tz := by
    apply hs
    ext a
    simp [mem_symmDiff, hwx, hwy, hxy, hwx.symm, hwy.symm, hxy.symm] <;> aesop
  have h013 : uw * pxz <= ty := by
    apply hs
    ext a
    simp [mem_symmDiff, hwx, hwz, hxz, hwx.symm, hwz.symm, hxz.symm] <;> aesop
  have h023 : uw * pyz <= tx := by
    apply hs
    ext a
    simp [mem_symmDiff, hwy, hwz, hyz, hwy.symm, hwz.symm, hyz.symm] <;> aesop
  have h101 : ux * pwx <= uw := by
    apply hs
    ext a; simp [mem_symmDiff, hwx, hwx.symm] <;> aesop
  have h102 : ux * pwy <= tz := by
    apply hs
    ext a
    simp [mem_symmDiff, hwx, hwy, hxy, hwx.symm, hwy.symm, hxy.symm] <;> aesop
  have h103 : ux * pwz <= ty := by
    apply hs
    ext a
    simp [mem_symmDiff, hwx, hwz, hxz, hwx.symm, hwz.symm, hxz.symm] <;> aesop
  have h112 : ux * pxy <= uy := by
    apply hs
    ext a; simp [mem_symmDiff, hxy, hxy.symm] <;> aesop
  have h113 : ux * pxz <= uz := by
    apply hs
    ext a; simp [mem_symmDiff, hxz, hxz.symm] <;> aesop
  have h123 : ux * pyz <= tw := by
    apply hs
    ext a
    simp [mem_symmDiff, hxy, hxz, hyz, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h201 : uy * pwx <= tz := by
    apply hs
    ext a
    simp [mem_symmDiff, hwx, hwy, hxy, hwx.symm, hwy.symm, hxy.symm] <;> aesop
  have h202 : uy * pwy <= uw := by
    apply hs
    ext a; simp [mem_symmDiff, hwy, hwy.symm] <;> aesop
  have h203 : uy * pwz <= tx := by
    apply hs
    ext a
    simp [mem_symmDiff, hwy, hwz, hyz, hwy.symm, hwz.symm, hyz.symm] <;> aesop
  have h212 : uy * pxy <= ux := by
    apply hs
    ext a; simp [mem_symmDiff, hxy, hxy.symm] <;> aesop
  have h213 : uy * pxz <= tw := by
    apply hs
    ext a
    simp [mem_symmDiff, hxy, hxz, hyz, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h223 : uy * pyz <= uz := by
    apply hs
    ext a; simp [mem_symmDiff, hyz, hyz.symm] <;> aesop
  have h301 : uz * pwx <= ty := by
    apply hs
    ext a
    simp [mem_symmDiff, hwx, hwz, hxz, hwx.symm, hwz.symm, hxz.symm] <;> aesop
  have h302 : uz * pwy <= tx := by
    apply hs
    ext a
    simp [mem_symmDiff, hwy, hwz, hyz, hwy.symm, hwz.symm, hyz.symm] <;> aesop
  have h303 : uz * pwz <= uw := by
    apply hs
    ext a; simp [mem_symmDiff, hwz, hwz.symm] <;> aesop
  have h312 : uz * pxy <= tw := by
    apply hs
    ext a
    simp [mem_symmDiff, hxy, hxz, hyz, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h313 : uz * pxz <= ux := by
    apply hs
    ext a; simp [mem_symmDiff, hxz, hxz.symm] <;> aesop
  have h323 : uz * pyz <= uy := by
    apply hs
    ext a; simp [mem_symmDiff, hyz, hyz.symm] <;> aesop
  have h := fourBridge_four_by_six_product_sum_le
    h001 h002 h003 h012 h013 h023 h101 h102 h103 h112 h113 h123
    h201 h202 h203 h212 h213 h223 h301 h302 h303 h312 h313 h323
  dsimp [uw, ux, uy, uz, pwx, pwy, pwz, pxy, pxz, pyz,
    tw, tx, ty, tz] at h
  rw [spinProd_singleton, spinProd_singleton, spinProd_singleton,
    spinProd_singleton, spinProd_pair w x hwx, spinProd_pair w y hwy,
    spinProd_pair w z hwz, spinProd_pair x y hxy, spinProd_pair x z hxz,
    spinProd_pair y z hyz] at h
  have htw : spinProd ({x, y, z} : Finset V) =
      fun s => spin s x * (spin s y * spin s z) := by
    funext s; simp [spinProd, hxy, hxz, hyz]
  have htx : spinProd ({w, y, z} : Finset V) =
      fun s => spin s w * (spin s y * spin s z) := by
    funext s; simp [spinProd, hwy, hwz, hyz]
  have hty : spinProd ({w, x, z} : Finset V) =
      fun s => spin s w * (spin s x * spin s z) := by
    funext s; simp [spinProd, hwx, hwz, hxz]
  have htz : spinProd ({w, x, y} : Finset V) =
      fun s => spin s w * (spin s x * spin s y) := by
    funext s; simp [spinProd, hwx, hwy, hxy]
  rw [htw, htx, hty, htz] at h
  simpa [fourBridgeOneCoeff, fourBridgeTwoCoeff, fourBridgeThreeCoeff,
    add_assoc, add_left_comm, add_comm] using h

set_option maxHeartbeats 4000000 in




theorem fourBridgeTwoCoeff_mul_threeCoeff_le_three_mul_one_add_three
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeTwoCoeff G J hf w x y z *
        fourBridgeThreeCoeff G J hf w x y z <=
      3 * (fourBridgeOneCoeff G J hf w x y z +
        fourBridgeThreeCoeff G J hf w x y z) := by
  let uw := (expJ G.edgeFinset J hf (spinProd {w})) ^ 2
  let ux := (expJ G.edgeFinset J hf (spinProd {x})) ^ 2
  let uy := (expJ G.edgeFinset J hf (spinProd {y})) ^ 2
  let uz := (expJ G.edgeFinset J hf (spinProd {z})) ^ 2
  let pwx := (expJ G.edgeFinset J hf (spinProd {w, x})) ^ 2
  let pwy := (expJ G.edgeFinset J hf (spinProd {w, y})) ^ 2
  let pwz := (expJ G.edgeFinset J hf (spinProd {w, z})) ^ 2
  let pxy := (expJ G.edgeFinset J hf (spinProd {x, y})) ^ 2
  let pxz := (expJ G.edgeFinset J hf (spinProd {x, z})) ^ 2
  let pyz := (expJ G.edgeFinset J hf (spinProd {y, z})) ^ 2
  let tw := (expJ G.edgeFinset J hf (spinProd {x, y, z})) ^ 2
  let tx := (expJ G.edgeFinset J hf (spinProd {w, y, z})) ^ 2
  let ty := (expJ G.edgeFinset J hf (spinProd {w, x, z})) ^ 2
  let tz := (expJ G.edgeFinset J hf (spinProd {w, x, y})) ^ 2
  have hs (A B C : Finset V) (hAB : A ∆ B = C) :
      (expJ G.edgeFinset J hf (spinProd A)) ^ 2 *
          (expJ G.edgeFinset J hf (spinProd B)) ^ 2 <=
        (expJ G.edgeFinset J hf (spinProd C)) ^ 2 := by
    simpa only [hAB] using
      expJ_spinProd_sq_mul_sq_le_symmDiff_sq G J hf hJ hhf A B
  have h001 : tw * pwx <= tx := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h002 : tw * pwy <= ty := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h003 : tw * pwz <= tz := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h012 : tw * pxy <= uz := by
    apply hs; ext a
    simp [mem_symmDiff, hxy, hxz, hyz, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h013 : tw * pxz <= uy := by
    apply hs; ext a
    simp [mem_symmDiff, hxy, hxz, hyz, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h023 : tw * pyz <= ux := by
    apply hs; ext a
    simp [mem_symmDiff, hxy, hxz, hyz, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h101 : tx * pwx <= tw := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h102 : tx * pwy <= uz := by
    apply hs; ext a
    simp [mem_symmDiff, hwy, hwz, hyz, hwy.symm, hwz.symm, hyz.symm] <;> aesop
  have h103 : tx * pwz <= uy := by
    apply hs; ext a
    simp [mem_symmDiff, hwy, hwz, hyz, hwy.symm, hwz.symm, hyz.symm] <;> aesop
  have h112 : tx * pxy <= ty := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h113 : tx * pxz <= tz := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h123 : tx * pyz <= uw := by
    apply hs; ext a
    simp [mem_symmDiff, hwy, hwz, hyz, hwy.symm, hwz.symm, hyz.symm] <;> aesop
  have h201 : ty * pwx <= uz := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwz, hxz, hwx.symm, hwz.symm, hxz.symm] <;> aesop
  have h202 : ty * pwy <= tw := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h203 : ty * pwz <= ux := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwz, hxz, hwx.symm, hwz.symm, hxz.symm] <;> aesop
  have h212 : ty * pxy <= tx := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h213 : ty * pxz <= uw := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwz, hxz, hwx.symm, hwz.symm, hxz.symm] <;> aesop
  have h223 : ty * pyz <= tz := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h301 : tz * pwx <= uy := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hxy, hwx.symm, hwy.symm, hxy.symm] <;> aesop
  have h302 : tz * pwy <= ux := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hxy, hwx.symm, hwy.symm, hxy.symm] <;> aesop
  have h303 : tz * pwz <= tw := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h312 : tz * pxy <= uw := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hxy, hwx.symm, hwy.symm, hxy.symm] <;> aesop
  have h313 : tz * pxz <= tx := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h323 : tz * pyz <= ty := by
    apply hs; ext a
    simp [mem_symmDiff, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have h := fourBridge_four_by_six_product_sum_le
    h001 h002 h003 h012 h013 h023 h101 h102 h103 h112 h113 h123
    h201 h202 h203 h212 h213 h223 h301 h302 h303 h312 h313 h323
  dsimp [uw, ux, uy, uz, pwx, pwy, pwz, pxy, pxz, pyz,
    tw, tx, ty, tz] at h
  rw [spinProd_singleton, spinProd_singleton, spinProd_singleton,
    spinProd_singleton, spinProd_pair w x hwx, spinProd_pair w y hwy,
    spinProd_pair w z hwz, spinProd_pair x y hxy, spinProd_pair x z hxz,
    spinProd_pair y z hyz] at h
  have htw : spinProd ({x, y, z} : Finset V) =
      fun s => spin s x * (spin s y * spin s z) := by
    funext s; simp [spinProd, hxy, hxz, hyz]
  have htx : spinProd ({w, y, z} : Finset V) =
      fun s => spin s w * (spin s y * spin s z) := by
    funext s; simp [spinProd, hwy, hwz, hyz]
  have hty : spinProd ({w, x, z} : Finset V) =
      fun s => spin s w * (spin s x * spin s z) := by
    funext s; simp [spinProd, hwx, hwz, hxz]
  have htz : spinProd ({w, x, y} : Finset V) =
      fun s => spin s w * (spin s x * spin s y) := by
    funext s; simp [spinProd, hwx, hwy, hxy]
  rw [htw, htx, hty, htz] at h
  simpa [fourBridgeOneCoeff, fourBridgeTwoCoeff, fourBridgeThreeCoeff,
    add_assoc, add_left_comm, add_comm, mul_comm] using h

end

end StatMech.Ising
