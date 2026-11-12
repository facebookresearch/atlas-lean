/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeSingletonCuts



open Finset SimpleGraph
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section



theorem fourBridge_three_sqsum_le_six_add_pairSqsum
    {w x y z wx wy wz xy xz yz : Real}
    (hw0 : 0 <= w) (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hw1 : w <= 1) (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (hwx : w * x <= wx) (hwy : w * y <= wy) (hwz : w * z <= wz)
    (hxy : x * y <= xy) (hxz : x * z <= xz) (hyz : y * z <= yz) :
    3 * (w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) <=
      6 + (wx ^ 2 + wy ^ 2 + wz ^ 2 + xy ^ 2 + xz ^ 2 + yz ^ 2) := by
  have pairSq {a b p : Real} (ha0 : 0 <= a) (hb0 : 0 <= b)
      (hab : a * b <= p) : a ^ 2 * b ^ 2 <= p ^ 2 := by
    have h := mul_self_le_mul_self (mul_nonneg ha0 hb0) hab
    nlinarith
  have unitPair {a b : Real} (ha0 : 0 <= a) (hb0 : 0 <= b)
      (ha1 : a <= 1) (hb1 : b <= 1) :
      a ^ 2 + b ^ 2 <= 1 + a ^ 2 * b ^ 2 := by
    have haSq : a ^ 2 <= 1 := by nlinarith
    have hbSq : b ^ 2 <= 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr haSq) (sub_nonneg.mpr hbSq)]
  have hsqwx := pairSq hw0 hx0 hwx
  have hsqwy := pairSq hw0 hy0 hwy
  have hsqwz := pairSq hw0 hz0 hwz
  have hsqxy := pairSq hx0 hy0 hxy
  have hsqxz := pairSq hx0 hz0 hxz
  have hsqyz := pairSq hy0 hz0 hyz
  have huwx := unitPair hw0 hx0 hw1 hx1
  have huwy := unitPair hw0 hy0 hw1 hy1
  have huwz := unitPair hw0 hz0 hw1 hz1
  have huxy := unitPair hx0 hy0 hx1 hy1
  have huxz := unitPair hx0 hz0 hx1 hz1
  have huyz := unitPair hy0 hz0 hy1 hz1
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem fourBridgeOneCoeff_three_mul_le_six_add_twoCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    3 * fourBridgeOneCoeff G J hf w x y z <=
      6 + fourBridgeTwoCoeff G J hf w x y z := by
  let m (v : V) := expJ G.edgeFinset J hf (fun s => spin s v)
  let q (u v : V) := expJ G.edgeFinset J hf (fun s => spin s u * spin s v)
  have hm (v : V) : 0 <= m v /\ m v <= 1 := by
    constructor
    · have h := ghsvp_expJ_nonneg G.edgeFinset J hf
        (fun e _ => hJ e) hhf ({v} : Finset V)
      simpa [m, spinProd_singleton] using h
    · exact expJ_monomial_le_one G.edgeFinset J hf _ (fun s => by
        rcases spin_eq_pm s v with hv | hv <;> simp [m, hv])
  have hpair (u v : V) (huv : u ≠ v) : m u * m v <= q u v := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({u} : Finset V) ({v} : Finset V)
    rw [spinProd_singleton, spinProd_singleton,
      symmDiff_singleton_pair u v huv, spinProd_pair u v huv] at h
    simpa [m, q] using h
  apply fourBridge_three_sqsum_le_six_add_pairSqsum
  · exact (hm w).1
  · exact (hm x).1
  · exact (hm y).1
  · exact (hm z).1
  · exact (hm w).2
  · exact (hm x).2
  · exact (hm y).2
  · exact (hm z).2
  · exact hpair w x hwx
  · exact hpair w y hwy
  · exact hpair w z hwz
  · exact hpair x y hxy
  · exact hpair x z hxz
  · exact hpair y z hyz

set_option maxHeartbeats 1000000 in




theorem fourBridgeThreeCoeff_three_mul_le_six_add_twoCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    3 * fourBridgeThreeCoeff G J hf w x y z <=
      6 + fourBridgeTwoCoeff G J hf w x y z := by
  classical
  let M := fourBridgeMarkedSet w x y z
  let t (u : V) := expJ G.edgeFinset J hf (spinProd (M \ {u}))
  let q (u v : V) := expJ G.edgeFinset J hf (spinProd {u, v})
  have hwM : w ∈ M := by simp [M, fourBridgeMarkedSet]
  have hxM : x ∈ M := by simp [M, fourBridgeMarkedSet]
  have hyM : y ∈ M := by simp [M, fourBridgeMarkedSet]
  have hzM : z ∈ M := by simp [M, fourBridgeMarkedSet]
  have ht (u : V) : 0 <= t u /\ t u <= 1 := by
    constructor
    · exact ghsvp_expJ_nonneg G.edgeFinset J hf
        (fun e _ => hJ e) hhf (M \ {u})
    · exact expJ_monomial_le_one G.edgeFinset J hf _ (fun s => by
        linarith [one_sub_spinProd_nonneg (M \ {u}) s])
  have hsymm (u v : V) (hu : u ∈ M) (hv : v ∈ M) (huv : u ≠ v) :
      (M \ {u}) ∆ (M \ {v}) = {u, v} := by
    ext a
    simp only [mem_symmDiff, mem_sdiff, mem_singleton, mem_insert]
    by_cases haM : a ∈ M <;> by_cases hau : a = u <;>
      by_cases hav : a = v <;> simp_all
  have hpair (u v : V) (hu : u ∈ M) (hv : v ∈ M) (huv : u ≠ v) :
      t u * t v <= q u v := by
    have h := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf (M \ {u}) (M \ {v})
    rw [hsymm u v hu hv huv] at h
    simpa [t, q] using h
  have h := fourBridge_three_sqsum_le_six_add_pairSqsum
    (ht w).1 (ht x).1 (ht y).1 (ht z).1
    (ht w).2 (ht x).2 (ht y).2 (ht z).2
    (hpair w x hwM hxM hwx) (hpair w y hwM hyM hwy)
    (hpair w z hwM hzM hwz) (hpair x y hxM hyM hxy)
    (hpair x z hxM hzM hxz) (hpair y z hyM hzM hyz)
  dsimp only [t, q] at h
  have hMw : M \ {w} = {x, y, z} := by
    ext a
    simp [M, fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have hMx : M \ {x} = {w, y, z} := by
    ext a
    simp [M, fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have hMy : M \ {y} = {w, x, z} := by
    ext a
    simp [M, fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  have hMz : M \ {z} = {w, x, y} := by
    ext a
    simp [M, fourBridgeMarkedSet, hwx, hwy, hwz, hxy, hxz, hyz,
      hwx.symm, hwy.symm, hwz.symm, hxy.symm, hxz.symm, hyz.symm] <;> aesop
  rw [hMw, hMx, hMy, hMz] at h
  rw [spinProd_pair w x hwx, spinProd_pair w y hwy,
    spinProd_pair w z hwz, spinProd_pair x y hxy,
    spinProd_pair x z hxz, spinProd_pair y z hyz] at h
  have htxyz : spinProd ({x, y, z} : Finset V) =
      fun s => spin s x * (spin s y * spin s z) := by
    funext s
    simp [spinProd, hxy, hxz, hyz]
  have htwxyz : spinProd ({w, y, z} : Finset V) =
      fun s => spin s w * (spin s y * spin s z) := by
    funext s
    simp [spinProd, hwy, hwz, hyz]
  have htwxz : spinProd ({w, x, z} : Finset V) =
      fun s => spin s w * (spin s x * spin s z) := by
    funext s
    simp [spinProd, hwx, hwz, hxz]
  have htwxy : spinProd ({w, x, y} : Finset V) =
      fun s => spin s w * (spin s x * spin s y) := by
    funext s
    simp [spinProd, hwx, hwy, hxy]
  rw [htxyz, htwxyz, htwxz, htwxy] at h
  simpa [fourBridgeThreeCoeff, fourBridgeTwoCoeff,
    add_assoc, add_left_comm, add_comm] using h




theorem fourBridge_pairSqsum_sq_le_five_mul_add_six
    {a b c d e f r : Real}
    (ha0 : 0 <= a) (hb0 : 0 <= b) (hc0 : 0 <= c)
    (hd0 : 0 <= d) (he0 : 0 <= e) (hf0 : 0 <= f)
    (ha1 : a <= 1) (hb1 : b <= 1) (hc1 : c <= 1)
    (hd1 : d <= 1) (he1 : e <= 1) (hf1 : f <= 1)
    (hab : a * b <= d) (hac : a * c <= e)
    (had : a * d <= b) (hae : a * e <= c)
    (hbc : b * c <= f) (hbd : b * d <= a) (hbf : b * f <= c)
    (hce : c * e <= a) (hcf : c * f <= b)
    (hde : d * e <= f) (hdf : d * f <= e) (hef : e * f <= d)
    (haf : a * f <= r) (hbe : b * e <= r) (hcd : c * d <= r) :
    (a + b + c + d + e + f) ^ 2 <=
      5 * (a + b + c + d + e + f) + 6 * r := by
  have hsquare {u : Real} (hu0 : 0 <= u) (hu1 : u <= 1) : u ^ 2 <= u := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have ha2 := hsquare ha0 ha1
  have hb2 := hsquare hb0 hb1
  have hc2 := hsquare hc0 hc1
  have hd2 := hsquare hd0 hd1
  have he2 := hsquare he0 he1
  have hf2 := hsquare hf0 hf1
  nlinarith



theorem fourBridgeTwoCoeff_sq_le_five_mul_add_six_fourCoeff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (hJ : forall e, 0 <= J e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeTwoCoeff G J hf w x y z ^ 2 <=
      5 * fourBridgeTwoCoeff G J hf w x y z +
        6 * fourBridgeFourCoeff G J hf w x y z := by
  let p (u v : V) :=
    (expJ G.edgeFinset J hf (fun s => spin s u * spin s v)) ^ 2
  let r := fourBridgeFourCoeff G J hf w x y z
  have hp (u v : V) (huv : u ≠ v) : 0 <= p u v /\ p u v <= 1 := by
    have hnonneg : 0 <= expJ G.edgeFinset J hf
        (fun s => spin s u * spin s v) := by
      have h := ghsvp_expJ_nonneg G.edgeFinset J hf
        (fun e _ => hJ e) hhf ({u, v} : Finset V)
      simpa [spinProd_pair u v huv] using h
    have hone : expJ G.edgeFinset J hf
        (fun s => spin s u * spin s v) <= 1 :=
      expJ_monomial_le_one G.edgeFinset J hf _ (fun s => by
        rcases spin_eq_pm s u with hu | hu <;>
          rcases spin_eq_pm s v with hv | hv <;> simp [hu, hv])
    constructor
    · dsimp [p]
      positivity
    · dsimp [p]
      nlinarith
  have hinter (u v s : V) (huv : u ≠ v) (hus : u ≠ s) (hvs : v ≠ s) :
      p u v * p u s <= p v s := by
    simpa [p] using threeBridge_pair_mul_pair_sq_le
      G J hf hJ hhf huv hus hvs
  have hcomp (a b c d : V)
      (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
      (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
      p a b * p c d <=
        (expJ G.edgeFinset J hf
          (fun s => spin s a * (spin s b * (spin s c * spin s d)))) ^ 2 := by
    have hsymm : ({a, b} : Finset V) ∆ {c, d} = {a, b, c, d} := by
      ext u
      by_cases hua : u = a <;> by_cases hub : u = b <;>
        by_cases huc : u = c <;> by_cases hud : u = d <;>
        simp [mem_symmDiff, hua, hub, huc, hud, hab, hac, had,
          hbc, hbd, hcd, hab.symm, hac.symm, had.symm,
          hbc.symm, hbd.symm, hcd.symm]
    have hfour : spinProd ({a, b, c, d} : Finset V) =
        fun s => spin s a * (spin s b * (spin s c * spin s d)) := by
      funext s
      simp [spinProd, hab, hac, had, hbc, hbd, hcd]
    have hgks := gks_second_J G.edgeFinset J hf
      (fun e _ => hJ e) hhf ({a, b} : Finset V) ({c, d} : Finset V)
    rw [spinProd_pair a b hab, spinProd_pair c d hcd, hsymm, hfour] at hgks
    dsimp only [p] at ⊢
    have hleft : 0 <=
        expJ G.edgeFinset J hf (fun s => spin s a * spin s b) *
          expJ G.edgeFinset J hf (fun s => spin s c * spin s d) := by
      have habn : 0 <= expJ G.edgeFinset J hf
          (fun s => spin s a * spin s b) := by
        have h := ghsvp_expJ_nonneg G.edgeFinset J hf
          (fun e _ => hJ e) hhf ({a, b} : Finset V)
        simpa [spinProd_pair a b hab] using h
      have hcdn : 0 <= expJ G.edgeFinset J hf
          (fun s => spin s c * spin s d) := by
        have h := ghsvp_expJ_nonneg G.edgeFinset J hf
          (fun e _ => hJ e) hhf ({c, d} : Finset V)
        simpa [spinProd_pair c d hcd] using h
      exact mul_nonneg habn hcdn
    have hsquare' := mul_self_le_mul_self hleft hgks
    nlinarith [hsquare']
  have hpwx := hp w x hwx
  have hpwy := hp w y hwy
  have hpwz := hp w z hwz
  have hpxy := hp x y hxy
  have hpxz := hp x z hxz
  have hpyz := hp y z hyz
  have h := fourBridge_pairSqsum_sq_le_five_mul_add_six
    hpwx.1 hpwy.1 hpwz.1 hpxy.1 hpxz.1 hpyz.1
    hpwx.2 hpwy.2 hpwz.2 hpxy.2 hpxz.2 hpyz.2
    (hinter w x y hwx hwy hxy) (hinter w x z hwx hwz hxz)
    (by simpa [p, mul_comm] using hinter x w y hwx.symm hxy hwy)
    (by simpa [p, mul_comm] using hinter x w z hwx.symm hxz hwz)
    (hinter w y z hwy hwz hyz)
    (by simpa [p, mul_comm] using hinter y w x hwy.symm hxy.symm hwx)
    (by simpa [p, mul_comm] using hinter y w z hwy.symm hyz hwz)
    (by simpa [p, mul_comm] using hinter z w x hwz.symm hxz.symm hwx)
    (by simpa [p, mul_comm] using hinter z w y hwz.symm hyz.symm hwy)
    (hinter x y z hxy hxz hyz)
    (by simpa [p, mul_comm] using hinter y x z hxy.symm hyz hxz)
    (by simpa [p, mul_comm] using hinter z x y hxz.symm hyz.symm hxy)
    (by simpa [p, r, fourBridgeFourCoeff, mul_assoc] using
      hcomp w x y z hwx hwy hwz hxy hxz hyz)
    (by simpa [p, r, fourBridgeFourCoeff, mul_assoc, mul_left_comm,
        mul_comm] using
      hcomp w y x z hwy hwx hwz hxy.symm hyz hxz)
    (by simpa [p, r, fourBridgeFourCoeff, mul_assoc, mul_left_comm,
        mul_comm] using
      hcomp w z x y hwz hwx hwy hxz.symm hyz.symm hxy)
  simpa [p, r, fourBridgeTwoCoeff, add_assoc] using h

end

end StatMech.Ising
