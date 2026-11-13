/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheTailCauchy








namespace StatMech.FrontierD

noncomputable section

open Filter Topology

private def sixVertexHalfFilledBetheRootDataRecast
    {c : Real} (hc : 2 < c) (k : Nat) :
    {p : Fin ((k + (k + 1)) + 1) → Real //
      SixVertexOpenRootSimplex p ∧
        SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
          ((k + (k + 1)) + 1) p} := by
  let hcount : (k + (k + 1)) + 1 = (k + 1) + (k + 1) := by omega
  exact hcount.symm ▸
    ⟨sixVertexHalfFilledBetheRoots hc k,
      sixVertexHalfFilledBetheRoots_mem_open hc k,
      sixVertexHalfFilledBetheRoots_is_solution hc k⟩

private def sixVertexHalfFilledBetheRootsRecast
    {c : Real} (hc : 2 < c) (k : Nat) :
    Fin ((k + (k + 1)) + 1) → Real :=
  (sixVertexHalfFilledBetheRootDataRecast hc k).1

def sixVertexSelectedFiniteRootDensity
    {c : Real} (hc : 2 < c) (k : Nat) : Real → Real :=
  sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
    ((k + (k + 1)) + 1) (sixVertexHalfFilledBetheRootsRecast hc k)

private theorem sixVertexFiniteRootDensity_transport
    (c : Real) (N : Nat) {n m : Nat} (h : n = m)
    (p : Fin n → Real) (x : Real) :
    sixVertexFiniteRootDensity c N m (h ▸ p) x =
      sixVertexFiniteRootDensity c N n p x := by
  subst m
  rfl

private theorem subtype_transport_val
    {A : Type*} {B : A → Type*}
    {P : (a : A) → B a → Prop} {a b : A}
    (h : a = b) (x : B a) (hx : P a x) :
    (h ▸ (⟨x, hx⟩ : {y : B a // P a y})).1 = h ▸ x := by
  subst b
  rfl

theorem sixVertexSelectedFiniteRootDensity_eq_halfFilled
    {c : Real} (hc : 2 < c) (k : Nat) (x : Real) :
    sixVertexSelectedFiniteRootDensity hc k x =
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) x := by
  let hcount : (k + 1) + (k + 1) = (k + (k + 1)) + 1 := by omega
  let P : (n : Nat) → (Fin n → Real) → Prop := fun n p =>
    SixVertexOpenRootSimplex p ∧
      SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k) n p
  have hp : P ((k + 1) + (k + 1))
      (sixVertexHalfFilledBetheRoots hc k) :=
    ⟨sixVertexHalfFilledBetheRoots_mem_open hc k,
      sixVertexHalfFilledBetheRoots_is_solution hc k⟩
  have hrecast : sixVertexHalfFilledBetheRootsRecast hc k =
      hcount ▸ sixVertexHalfFilledBetheRoots hc k := by
    unfold sixVertexHalfFilledBetheRootsRecast
      sixVertexHalfFilledBetheRootDataRecast
    dsimp only
    exact subtype_transport_val (P := P) hcount
      (sixVertexHalfFilledBetheRoots hc k) hp
  unfold sixVertexSelectedFiniteRootDensity
  rw [hrecast]
  exact sixVertexFiniteRootDensity_transport c (sixVertexFourWidth 0 k)
    hcount (sixVertexHalfFilledBetheRoots hc k) x

private theorem sixVertexHalfFilledBetheRootsRecast_mem_open
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexOpenRootSimplex (sixVertexHalfFilledBetheRootsRecast hc k) := by
  exact (sixVertexHalfFilledBetheRootDataRecast hc k).2.1

private theorem sixVertexHalfFilledBetheRootsRecast_is_solution
    {c : Real} (hc : 2 < c) (k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
      ((k + (k + 1)) + 1) (sixVertexHalfFilledBetheRootsRecast hc k) := by
  exact (sixVertexHalfFilledBetheRootDataRecast hc k).2.2

theorem sixVertexTailConvolutionError_fourWidth_tendsto_zero
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) :
    Tendsto (fun k : Nat =>
      sixVertexTailConvolutionError c (sixVertexFourWidth 0 k))
      atTop (nhds 0) := by
  let A := sixVertexRootDensityKernelLipschitzBound c *
    sixVertexFiniteRootDensityUniformBound c * (2 * Real.pi) /
      (4 * sixVertexTailFiniteDensityFloor c)
  have hfloor := sixVertexTailFiniteDensityFloor_pos hc htail
  have h := (tendsto_const_div_atTop_nhds_zero_nat A).comp
    (tendsto_add_atTop_nat 1)
  apply h.congr'
  filter_upwards [] with k
  unfold sixVertexTailConvolutionError sixVertexFourWidth
  dsimp [A]
  have hk : (0 : Real) < k + 1 := by positivity
  field_simp [hfloor.ne', hk.ne']
  push_cast
  ring


theorem sixVertexSelectedFiniteRootDensity_weighted_cauchy_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (k l : Nat) :
    ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexSelectedFiniteRootDensity hc k x -
          sixVertexSelectedFiniteRootDensity hc l x)| <=
      ((sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) +
          sixVertexTailConvolutionError c (sixVertexFourWidth 0 l)) /
        (2 * Real.pi)) /
          (1 - sixVertexRootDensityContractionRate c) := by
  let nk := k + (k + 1)
  let nl := l + (l + 1)
  let pk := sixVertexHalfFilledBetheRootsRecast hc k
  let pl := sixVertexHalfFilledBetheRootsRecast hc l
  have hkhalf : sixVertexFourWidth 0 k = 2 * (nk + 1) := by
    dsimp [nk, sixVertexFourWidth]
    omega
  have hlhalf : sixVertexFourWidth 0 l = 2 * (nl + 1) := by
    dsimp [nl, sixVertexFourWidth]
    omega
  have hbound := sixVertexFiniteRootDensity_weighted_cauchy_tail
    hc htail (sixVertexFourWidth_pos 0 k) (sixVertexFourWidth_pos 0 l)
    hkhalf hlhalf
    (sixVertexHalfFilledBetheRootsRecast_mem_open hc k)
    (sixVertexHalfFilledBetheRootsRecast_mem_open hc l)
    (sixVertexHalfFilledBetheRootsRecast_is_solution hc k)
    (sixVertexHalfFilledBetheRootsRecast_is_solution hc l)
  simpa [sixVertexSelectedFiniteRootDensity, pk, pl, nk, nl] using hbound



theorem sixVertexSelectedFiniteRootDensity_approximateEquation_tail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (k : Nat) (x : Real) :
    |sixVertexRootDensityWeight c x *
          sixVertexSelectedFiniteRootDensity hc k x -
        (sixVertexRootDensityWeight c x / (2 * Real.pi) -
          (1 / (2 * Real.pi)) *
            ∫ y in -Real.pi..Real.pi,
              sixVertexRootDensityKernel c x y *
                sixVertexSelectedFiniteRootDensity hc k y)| <=
      sixVertexTailConvolutionError c (sixVertexFourWidth 0 k) /
        (2 * Real.pi) := by
  let n := k + (k + 1)
  let p := sixVertexHalfFilledBetheRootsRecast hc k
  let N := sixVertexFourWidth 0 k
  have hhalf : N = 2 * (n + 1) := by
    dsimp [N, n, sixVertexFourWidth]
    omega
  have hdef := abs_sixVertexFiniteConvolutionDefect_le_tail
    hc htail (sixVertexFourWidth_pos 0 k) hhalf
    (sixVertexHalfFilledBetheRootsRecast_mem_open hc k)
    (sixVertexHalfFilledBetheRootsRecast_is_solution hc k) x
  have hfinite := sixVertexRootDensityWeight_mul_finiteRootDensity
    hc (sixVertexFourWidth_pos 0 k) p x
  have heq : sixVertexRootDensityWeight c x *
          sixVertexSelectedFiniteRootDensity hc k x -
        (sixVertexRootDensityWeight c x / (2 * Real.pi) -
          (1 / (2 * Real.pi)) *
            ∫ y in -Real.pi..Real.pi,
              sixVertexRootDensityKernel c x y *
                sixVertexSelectedFiniteRootDensity hc k y) =
      -(1 / (2 * Real.pi)) *
        sixVertexFiniteConvolutionDefect c N (n + 1) p x := by
    dsimp [sixVertexSelectedFiniteRootDensity, N, n, p,
      sixVertexFiniteConvolutionDefect]
    rw [hfinite]
    have hN0 : (sixVertexFourWidth 0 k : Real) ≠ 0 := by
      exact_mod_cast (sixVertexFourWidth_pos 0 k).ne'
    field_simp [Real.pi_ne_zero, hN0]
    ring
  rw [heq, abs_mul, abs_neg,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  exact (mul_le_mul_of_nonneg_left hdef (by positivity)).trans_eq (by ring)

end

end StatMech.FrontierD
