/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4DiagonalRate
import Code.FK.FKGeneralQConnectionSymmetry
import Code.FK.RotationInvariance
import Code.Lattice.BoxSurfaceVolume

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section


noncomputable def fkQgt4CriticalFreeTwoPoint
    {q : Real} (hq : 4 < q) (x : Site 2) : Real :=
  FK.infiniteTwoPointReal
    ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
    (origin 2) x

theorem fkQgt4CriticalFreeTwoPoint_pos
    {q : Real} (hq : 4 < q) (x : Site 2) :
    0 < fkQgt4CriticalFreeTwoPoint hq x := by
  unfold fkQgt4CriticalFreeTwoPoint FK.infiniteTwoPointReal
  exact FK.fkgq_freeInfiniteVolume_connection_pos
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    (by linarith : (1 : Real) <= q) (origin 2) x



theorem fkQgt4CriticalFreeTwoPoint_add_supermultiplicative
    {q : Real} (hq : 4 < q) (x y : Site 2) :
    fkQgt4CriticalFreeTwoPoint hq x *
        fkQgt4CriticalFreeTwoPoint hq y <=
      fkQgt4CriticalFreeTwoPoint hq (x + y) := by
  let hp := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).1
  let hp1 := (BeffaraDC.selfDualPoint_mem_Ioo
    (by linarith : (0 : Real) < q)).2
  let hq0 : (0 : Real) < q := by linarith
  let hq1 : (1 : Real) <= q := by linarith
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 hq0
  have htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu := by
    simpa [mu, hp, hp1, hq0] using
      (FK.fkgqt_freeIV_isTranslationInvariant
        (d := 2) hp hp1 hq1)
  have hshift : FK.infiniteTwoPointReal mu x (x + y) =
      fkQgt4CriticalFreeTwoPoint hq y := by
    have h := infiniteTwoPointReal_add_eq_of_translationInvariant
      mu htrans x (origin 2) y
    rw [show x + origin 2 = x by
          funext i
          simp [origin]] at h
    simpa [mu, hp, hp1, hq0,
      fkQgt4CriticalFreeTwoPoint] using h
  have hfkg := FK.fkgq_freeInfiniteVolume_connection_fkg
    hp hp1 hq1 (origin 2) x x (x + y)
  have hsubset :
      {omega | Connected 2 omega (origin 2) x} ∩
          {omega | Connected 2 omega x (x + y)} <=
        {omega | Connected 2 omega (origin 2) (x + y)} := by
    rintro omega ⟨hox, hxy⟩
    exact hox.trans hxy
  have hall := hfkg.trans (measureReal_mono (μ := mu) hsubset)
  change FK.infiniteTwoPointReal mu (origin 2) x *
      FK.infiniteTwoPointReal mu x (x + y) <=
        FK.infiniteTwoPointReal mu (origin 2) (x + y) at hall
  rw [hshift] at hall
  simpa [mu, hp, hp1, hq0, fkQgt4CriticalFreeTwoPoint,
    FK.infiniteTwoPointReal] using hall



theorem fkQgt4CriticalFreeTwoPoint_boxSym
    {q : Real} (hq : 4 < q) (S : FK.BoxSym 2) (x : Site 2) :
    fkQgt4CriticalFreeTwoPoint hq (S.τ x) =
      fkQgt4CriticalFreeTwoPoint hq x := by
  have h := FK.fkgq_freeInfiniteVolume_connection_boxSym
    (d := 2) (by norm_num) S
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
    (by linarith : (1 : Real) <= q) (origin 2) x
  have hzero : S.τ (origin 2) = origin 2 := by
    simpa [origin] using FK.rot_boxSym_fixes_zero S
  rw [hzero] at h
  simpa [fkQgt4CriticalFreeTwoPoint, FK.infiniteTwoPointReal] using h


def fkQgt4CoordinateSignBoxSym (flip : Fin 2 -> Bool) : FK.BoxSym 2 where
  τ :=
    { toFun := fun x i => if flip i then -(x i) else x i
      invFun := fun x i => if flip i then -(x i) else x i
      left_inv := by
        intro x
        funext i
        cases h : flip i <;> simp [h]
      right_inv := by
        intro x
        funext i
        cases h : flip i <;> simp [h] }
  adj := by
    intro x y
    simp only [hypercubicLattice_adj, Equiv.coe_fn_mk]
    rw [show (∑ i,
        ((if flip i then -(x i) else x i) -
          (if flip i then -(y i) else y i)).natAbs) =
        ∑ i, (x i - y i).natAbs by
      apply Finset.sum_congr rfl
      intro i _
      cases h : flip i
      · simp [h]
      · simp only [h, Bool.true_eq, ↓reduceIte]
        rw [show -x i - -y i = -(x i - y i) by ring,
          Int.natAbs_neg]]
  box_mem := by
    intro n x
    simp only [mem_box, Equiv.coe_fn_mk]
    constructor <;> intro h i
    · simpa [show (if flip i then -x i else x i).natAbs = (x i).natAbs by
          cases hflip : flip i <;> simp [hflip]] using h i
    · simpa [show (if flip i then -x i else x i).natAbs = (x i).natAbs by
          cases hflip : flip i <;> simp [hflip]] using h i


def fkQgt4NonnegativeSite (x : Site 2) : Site 2 :=
  fun i => if x i < 0 then -x i else x i

theorem fkQgt4NonnegativeSite_apply (x : Site 2) (i : Fin 2) :
    fkQgt4NonnegativeSite x i = ((x i).natAbs : Int) := by
  by_cases h : x i < 0
  · rw [fkQgt4NonnegativeSite, if_pos h, ← Int.natAbs_neg]
    exact (Int.natAbs_of_nonneg (by linarith : 0 <= -x i)).symm
  · rw [fkQgt4NonnegativeSite, if_neg h]
    exact (Int.natAbs_of_nonneg (le_of_not_gt h)).symm

theorem fkQgt4CoordinateSignBoxSym_normalizes (x : Site 2) :
    (fkQgt4CoordinateSignBoxSym
      (fun i => decide (x i < 0))).τ x =
        fkQgt4NonnegativeSite x := by
  funext i
  simp only [fkQgt4CoordinateSignBoxSym, Equiv.coe_fn_mk]
  by_cases h : x i < 0 <;> simp [h, fkQgt4NonnegativeSite]


def fkQgt4SiteRadius (x : Site 2) : Nat :=
  (x 0).natAbs + (x 1).natAbs



def fkQgt4SiteSphere (n : Nat) : Finset (Site 2) :=
  (box_finite 2 n).toFinset.filter (fun x => fkQgt4SiteRadius x = n)

theorem fkQgt4SiteSphere_card_le (n : Nat) :
    (fkQgt4SiteSphere n).card <= (2 * n + 1) ^ 2 := by
  calc
    (fkQgt4SiteSphere n).card <= (box_finite 2 n).toFinset.card :=
      Finset.card_filter_le _ _
    _ = (2 * n + 1) ^ 2 := by
      rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]



def fkQgt4CriticalFreeSphereConnectionEvent (n : Nat) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ x ∈ fkQgt4SiteSphere n,
    {omega | Connected 2 omega (origin 2) x}

theorem fkQgt4Nonnegative_add_swap (x : Site 2) :
    fkQgt4NonnegativeSite x +
        (FK.rot_permBoxSym 2 (Equiv.swap (0 : Fin 2) 1)).τ
          (fkQgt4NonnegativeSite x) =
      fkQgt4ExactDiagonalSite (fkQgt4SiteRadius x) := by
  funext i
  fin_cases i <;>
    simp [fkQgt4NonnegativeSite_apply, fkQgt4SiteRadius,
      FK.rot_permBoxSym, FK.rot_permEquiv,
      fkQgt4ExactDiagonalSite] <;> omega



theorem fkQgt4CriticalFreeTwoPoint_sq_le_diagonal
    {q : Real} (hq : 4 < q) (x : Site 2) :
    fkQgt4CriticalFreeTwoPoint hq x ^ 2 <=
      fkQgt4CriticalFreeExactDiagonalTwoPoint hq
        (fkQgt4SiteRadius x) := by
  let z := fkQgt4NonnegativeSite x
  let S := FK.rot_permBoxSym 2 (Equiv.swap (0 : Fin 2) 1)
  have hnorm : fkQgt4CriticalFreeTwoPoint hq z =
      fkQgt4CriticalFreeTwoPoint hq x := by
    dsimp [z]
    rw [← fkQgt4CoordinateSignBoxSym_normalizes x]
    exact fkQgt4CriticalFreeTwoPoint_boxSym hq _ x
  have hswap : fkQgt4CriticalFreeTwoPoint hq (S.τ z) =
      fkQgt4CriticalFreeTwoPoint hq z :=
    fkQgt4CriticalFreeTwoPoint_boxSym hq S z
  have hadd := fkQgt4CriticalFreeTwoPoint_add_supermultiplicative
    hq z (S.τ z)
  rw [hswap, hnorm] at hadd
  rw [show z + S.τ z = fkQgt4ExactDiagonalSite
      (fkQgt4SiteRadius x) by
        simpa [z, S] using fkQgt4Nonnegative_add_swap x] at hadd
  simpa [pow_two, fkQgt4CriticalFreeTwoPoint,
    fkQgt4CriticalFreeExactDiagonalTwoPoint] using hadd



theorem fkQgt4CriticalFreeTwoPoint_eventually_exponential
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    exists N : Nat, forall x : Site 2, N <= fkQgt4SiteRadius x ->
      fkQgt4CriticalFreeTwoPoint hq x <=
        Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
          (fkQgt4SiteRadius x : Real)) := by
  let L := fkQgt4CriticalFreeExactDiagonalRateLimit hq
  have hhalf : L / 2 < L := by dsimp [L]; linarith
  have hevent : ∀ᶠ n : Nat in atTop,
      L / 2 <
        -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n) /
          (n : Real) :=
    (fkQgt4CriticalFreeExactDiagonalRate_tendsto hq).eventually
      (Ioi_mem_nhds hhalf)
  rw [eventually_atTop] at hevent
  obtain ⟨N0, hN0⟩ := hevent
  refine ⟨max N0 1, ?_⟩
  intro x hx
  let n := fkQgt4SiteRadius x
  have hnN : N0 <= n := le_trans (Nat.le_max_left _ _) hx
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_one)
    (le_trans (Nat.le_max_right _ _) hx)
  have hrate := hN0 n hnN
  have hdiagpos := fkQgt4CriticalFreeExactDiagonalTwoPoint_pos hq n
  have hlog : Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq n) <
      -(L / 2) * (n : Real) := by
    have hnreal : (0 : Real) < n := by exact_mod_cast hnpos
    rw [lt_div_iff₀ hnreal] at hrate
    nlinarith
  have hdiag : fkQgt4CriticalFreeExactDiagonalTwoPoint hq n <=
      Real.exp (-(L / 2) * (n : Real)) := by
    exact (Real.log_lt_iff_lt_exp hdiagpos).mp hlog |>.le
  have hsq := fkQgt4CriticalFreeTwoPoint_sq_le_diagonal hq x
  have hpoint : 0 <= fkQgt4CriticalFreeTwoPoint hq x :=
    (fkQgt4CriticalFreeTwoPoint_pos hq x).le
  have hexp : 0 <= Real.exp (-(L / 4) * (n : Real)) :=
    (Real.exp_pos _).le
  have hexpSq :
      Real.exp (-(L / 4) * (n : Real)) ^ 2 =
        Real.exp (-(L / 2) * (n : Real)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsquares : fkQgt4CriticalFreeTwoPoint hq x ^ 2 <=
      Real.exp (-(L / 4) * (n : Real)) ^ 2 := by
    rw [hexpSq]
    exact hsq.trans hdiag
  have := (sq_le_sq₀ hpoint hexp).mp hsquares
  simpa [L, n] using this



theorem fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    exists N : Nat, forall n : Nat, N <= n ->
      ((FK.freeInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (fkQgt4CriticalFreeSphereConnectionEvent n) <=
        ((2 * n + 1 : Nat) : Real) ^ 2 *
          Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
            (n : Real)) := by
  obtain ⟨N, hN⟩ :=
    fkQgt4CriticalFreeTwoPoint_eventually_exponential hq hpos
  refine ⟨N, ?_⟩
  intro n hn
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q)
  calc
    mu.real (fkQgt4CriticalFreeSphereConnectionEvent n) <=
        ∑ x ∈ fkQgt4SiteSphere n,
          mu.real {omega | Connected 2 omega (origin 2) x} := by
      exact measureReal_biUnion_finset_le _ _
    _ <= ∑ _x ∈ fkQgt4SiteSphere n,
        Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
          (n : Real)) := by
      apply Finset.sum_le_sum
      intro x hx
      have hradius : fkQgt4SiteRadius x = n :=
        (Finset.mem_filter.mp hx).2
      change fkQgt4CriticalFreeTwoPoint hq x <= _
      simpa [hradius] using hN x (hradius.symm ▸ hn)
    _ = ((fkQgt4SiteSphere n).card : Real) *
        Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
          (n : Real)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ <= ((2 * n + 1 : Nat) : Real) ^ 2 *
        Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) *
          (n : Real)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast fkQgt4SiteSphere_card_le n

end

end StatMech.FrontierD
