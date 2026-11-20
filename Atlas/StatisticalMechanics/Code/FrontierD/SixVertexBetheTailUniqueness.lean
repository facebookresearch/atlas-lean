/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge





open Finset Filter Topology Matrix

namespace StatMech.FrontierD

noncomputable section

private theorem sixVertexBetheRootJacobian_apply_pos_of_max
    {N n : Nat} {c : Real} (hc : 2 < c)
    (hdom : 2 * ((n : Real) - 1) *
        (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) < (N : Real))
    (p v : Fin n → Real) (j : Fin n) (hvj : 0 < v j)
    (hjmax : ∀ k, |v k| ≤ |v j|) :
    0 < sixVertexBetheRootJacobian N n c p v j := by
  let A := sixVertexBetheJacobianMatrix N n c p
  let R := sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨j⟩
  have hR : 0 < R := div_pos
    ((one_lt_sixVertexAnisotropyMagnitude hc).trans' zero_lt_one)
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
  have hcard : ((Finset.univ.erase j).card : Real) = (n : Real) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
    simp [Nat.cast_sub hn]
  have hoffPos (k : Fin n) (hjk : j ≠ k) : 0 < A j k := by
    dsimp [A, sixVertexBetheJacobianMatrix]
    rw [if_neg hjk]
    exact div_pos
      (mul_pos
        (by nlinarith [sixVertexDelta_lt_neg_one hc])
        (sixVertexBetheIntegratingFactor_pos hc (p j)))
      (sixVertexThetaDerivativeDenominator_pos hc (p j) (p k))
  have hoffBound (k : Fin n) (hjk : j ≠ k) : A j k ≤ R := by
    have h := norm_sixVertexTheta_rightDerivative_le hc (p j) (p k)
    rw [Real.norm_eq_abs] at h
    dsimp [A, R, sixVertexBetheJacobianMatrix]
    rw [if_neg hjk]
    have hpos : 0 < -4 * sixVertexDelta c *
        sixVertexBetheIntegratingFactor c (p j) /
          sixVertexThetaDerivativeDenominator c (p j) (p k) := by
      simpa only [A, sixVertexBetheJacobianMatrix, if_neg hjk] using
        hoffPos k hjk
    rw [← abs_of_pos hpos]
    exact h
  have hleftLower (k : Fin n) :
      -R ≤ 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
        sixVertexThetaDerivativeDenominator c (p j) (p k) := by
    have h := norm_sixVertexTheta_leftDerivative_le hc (p j) (p k)
    rw [Real.norm_eq_abs] at h
    exact (neg_le_neg h).trans (neg_abs_le _)
  have hoffSum : (∑ k ∈ Finset.univ.erase j, A j k) ≤
      ((n : Real) - 1) * R := by
    calc
      (∑ k ∈ Finset.univ.erase j, A j k) ≤
          ∑ _k ∈ Finset.univ.erase j, R := by
        apply Finset.sum_le_sum
        intro k hk
        exact hoffBound k (Ne.symm (Finset.mem_erase.mp hk).1)
      _ = ((n : Real) - 1) * R := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hleftSum : -((n : Real) - 1) * R ≤
      ∑ k ∈ Finset.univ.erase j,
        4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p k) /
          sixVertexThetaDerivativeDenominator c (p j) (p k) := by
    calc
      -((n : Real) - 1) * R =
          ∑ _k ∈ Finset.univ.erase j, -R := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
      _ ≤ _ := Finset.sum_le_sum fun k _ => hleftLower k
  have hdiag : (N : Real) - ((n : Real) - 1) * R ≤ A j j := by
    dsimp [A, sixVertexBetheJacobianMatrix]
    rw [if_pos rfl]
    linarith
  have hrow : 0 < A j j - ∑ k ∈ Finset.univ.erase j, A j k := by
    linarith
  have hmatrix : LinearMap.toMatrix'
      (sixVertexBetheRootJacobian N n c p).toLinearMap = A := by
    ext i k
    exact sixVertexBetheRootJacobian_toMatrix'_apply hc p i k
  have hJv : sixVertexBetheRootJacobian N n c p v j =
      ∑ k, A j k * v k := by
    have hm := congrFun (LinearMap.toMatrix'_mulVec
      (sixVertexBetheRootJacobian N n c p).toLinearMap v) j
    rw [hmatrix] at hm
    simpa [Matrix.mulVec] using hm.symm
  have hjabs : |v j| = v j := abs_of_pos hvj
  have hvLower (k : Fin n) : -v j ≤ v k := by
    have hk := hjmax k
    rw [hjabs] at hk
    linarith [neg_abs_le (v k)]
  have hsumLower :
      -(∑ k ∈ Finset.univ.erase j, A j k) * v j ≤
        ∑ k ∈ Finset.univ.erase j, A j k * v k := by
    calc
      -(∑ k ∈ Finset.univ.erase j, A j k) * v j =
          ∑ k ∈ Finset.univ.erase j, A j k * (-v j) := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left (hvLower k)
          (hoffPos k (Ne.symm (Finset.mem_erase.mp hk).1)).le
  rw [hJv, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hmain : 0 < (A j j - ∑ k ∈ Finset.univ.erase j, A j k) * v j :=
    mul_pos hrow hvj
  nlinarith



theorem sixVertexBetheSolution_unique_of_diagonalDominance
    {N n : Nat} {c : Real} (hc : 2 < c)
    (hdom : 2 * ((n : Real) - 1) *
        (sixVertexAnisotropyMagnitude c /
          (sixVertexAnisotropyMagnitude c - 1)) < (N : Real))
    {p q : Fin n → Real}
    (hp : SixVertexSatisfiesBetheEquations c N n p)
    (hq : SixVertexSatisfiesBetheEquations c N n q) : p = q := by
  by_contra hpq
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact hpq (Subsingleton.elim p q)
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact Finset.univ_nonempty
  obtain ⟨j, _, hjmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => |p i - q i|) huniv
  have hex : ∃ i, p i ≠ q i := by
    simpa only [Function.ne_iff] using hpq
  obtain ⟨i, hi⟩ := hex
  have hjne : p j - q j ≠ 0 := by
    intro hj
    have hzero : |p j - q j| = 0 := by rw [hj, abs_zero]
    have hiabs := hjmax i (Finset.mem_univ i)
    rw [hzero, abs_nonpos_iff] at hiabs
    exact hi (sub_eq_zero.mp hiabs)
  have runContradiction (r s : Fin n → Real)
      (hr : SixVertexSatisfiesBetheEquations c N n r)
      (hs : SixVertexSatisfiesBetheEquations c N n s)
      (hpos : 0 < s j - r j)
      (hmax : ∀ k, |s k - r k| ≤ |s j - r j|) : False := by
    let v : Fin n → Real := s - r
    let path : Real → (Fin n → Real) := fun t => r + t • v
    let residual : (Fin n → Real) → (Fin n → Real) := fun z i =>
      sixVertexBetheResidual c N n z i
    let f : Real → Real := fun t => residual (path t) j
    have hvj : 0 < v j := by simpa only [v, Pi.sub_apply] using hpos
    have hvmax : ∀ k, |v k| ≤ |v j| := by
      intro k
      simpa only [v, Pi.sub_apply] using hmax k
    have hderiv (t : Real) : HasDerivAt f
        (sixVertexBetheRootJacobian N n c (path t) v j) t := by
      have hres : HasFDerivAt residual
          (sixVertexBetheRootJacobian N n c (path t)) (path t) := by
        exact (analyticAt_sixVertexBetheResidual_family N n (c, path t) hc).comp
          (x := path t) (f := fun z : Fin n → Real => (c, z))
          (analyticAt_const.prod analyticAt_id) |>.hasStrictFDerivAt.hasFDerivAt
      have hpath : HasDerivAt path v t := by
        dsimp [path]
        convert (hasDerivAt_const t r).add ((hasDerivAt_id t).smul_const v) using 1 <;>
          simp
      have hcomp := hres.comp_hasDerivAt t hpath
      have hproj := (hasFDerivAt_apply (𝕜 := Real) j
        (residual (path t))).comp_hasDerivAt t hcomp
      simpa only [f, Function.comp_apply] using hproj
    have hderivPos (t : Real) :
        0 < sixVertexBetheRootJacobian N n c (path t) v j :=
      sixVertexBetheRootJacobian_apply_pos_of_max hc hdom (path t) v j hvj hvmax
    have hmono : StrictMono f := strictMono_of_hasDerivAt_pos hderiv hderivPos
    have hf01 := hmono zero_lt_one
    have hrzero : f 0 = 0 := by
      have := (sixVertexBetheResidual_eq_zero_iff c N n r).2 hr j
      simpa [f, residual, path] using this
    have hszero : f 1 = 0 := by
      have := (sixVertexBetheResidual_eq_zero_iff c N n s).2 hs j
      simpa [f, residual, path, v] using this
    linarith
  by_cases hsign : 0 < p j - q j
  · apply runContradiction q p hq hp hsign
    intro k
    exact hjmax k (Finset.mem_univ k)
  · have hneg : 0 < q j - p j := by
      have : p j - q j < 0 := lt_of_le_of_ne (le_of_not_gt hsign) hjne
      linarith
    apply runContradiction p q hp hq hneg
    intro k
    simpa only [abs_sub_comm] using hjmax k (Finset.mem_univ k)

theorem sixVertexBetheSolution_unique_of_anisotropyMagnitude
    {N n : Nat} {c : Real} (hc : 2 < c) (hhalf : 2 * n ≤ N)
    (htail : (n : Real) < sixVertexAnisotropyMagnitude c)
    {p q : Fin n → Real}
    (hp : SixVertexSatisfiesBetheEquations c N n p)
    (hq : SixVertexSatisfiesBetheEquations c N n q) : p = q := by
  apply sixVertexBetheSolution_unique_of_diagonalDominance hc _ hp hq
  let d := sixVertexAnisotropyMagnitude c
  have hd : 1 < d := one_lt_sixVertexAnisotropyMagnitude hc
  have hN : (2 * n : Real) ≤ (N : Real) := by exact_mod_cast hhalf
  have hstrict :
      2 * ((n : Real) - 1) * (d / (d - 1)) < 2 * (n : Real) := by
    rw [show 2 * ((n : Real) - 1) * (d / (d - 1)) =
      (2 * ((n : Real) - 1) * d) / (d - 1) by ring]
    rw [div_lt_iff₀ (sub_pos.mpr hd)]
    dsimp [d] at htail ⊢
    nlinarith
  exact hstrict.trans_le hN

end

end StatMech.FrontierD
