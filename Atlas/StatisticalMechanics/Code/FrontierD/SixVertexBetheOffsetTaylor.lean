/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetLinearBound





namespace StatMech.FrontierD

noncomputable section

def sixVertexThetaDerivativeLipschitzNNReal (c : Real) : NNReal :=
  Real.toNNReal (sixVertexThetaLeftKernelLipschitzBound c)

def sixVertexThetaCrossLipschitzBound (c : Real) : Real :=
  sixVertexRootDensityKernelLipschitzBound c /
    ((sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c)

def sixVertexThetaTaylorBound (c : Real) : Real :=
  sixVertexThetaLeftKernelLipschitzBound c +
    sixVertexThetaCrossLipschitzBound c

theorem coe_sixVertexThetaDerivativeLipschitzNNReal
    {c : Real} (hc : 2 < c) :
    (sixVertexThetaDerivativeLipschitzNNReal c : Real) =
      sixVertexThetaLeftKernelLipschitzBound c := by
  exact Real.coe_toNNReal _ (sixVertexThetaLeftKernelLipschitzBound_pos hc).le

theorem lipschitzWith_sixVertexThetaLeftDerivative
    {c : Real} (hc : 2 < c) (y : Real) :
    LipschitzWith (sixVertexThetaDerivativeLipschitzNNReal c)
      (fun x => 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
        sixVertexThetaDerivativeDenominator c x y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq, Real.dist_eq,
    coe_sixVertexThetaDerivativeLipschitzNNReal hc]
  exact sixVertexThetaLeftKernel_lipschitz hc x z y

theorem lipschitzWith_sixVertexThetaRightDerivative
    {c : Real} (hc : 2 < c) (x : Real) :
    LipschitzWith (sixVertexThetaDerivativeLipschitzNNReal c)
      (fun y => -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
        sixVertexThetaDerivativeDenominator c x y) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [Real.dist_eq, Real.dist_eq,
    coe_sixVertexThetaDerivativeLipschitzNNReal hc]
  have h := sixVertexRootDensityKernel_div_weight_lipschitz hc x y z
  rw [sixVertexRootDensityKernel_div_weight hc,
    sixVertexRootDensityKernel_div_weight hc] at h
  exact h

theorem abs_intervalIntegral_sub_const_mul_le_of_lipschitz'
    {f : Real → Real} {C : NNReal} (hf : Continuous f)
    (hlip : LipschitzWith C f) (a b u : Real)
    (hu : u ∈ Set.uIcc a b) :
    |(∫ x in a..b, f x) - f u * (b - a)| ≤
      (C : Real) * |b - a| ^ 2 := by
  by_cases hab : a ≤ b
  · have hu' : u ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hu
    have h := abs_intervalIntegral_sub_const_mul_le_of_lipschitz
      hf hlip hab hu'
    simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using h
  · have hba : b ≤ a := le_of_not_ge hab
    have hu' : u ∈ Set.Icc b a := by
      simpa [Set.uIcc_of_ge hba] using hu
    have h := abs_intervalIntegral_sub_const_mul_le_of_lipschitz
      hf hlip hba hu'
    rw [intervalIntegral.integral_symm]
    have hrearrange :
        -(∫ x in b..a, f x) - f u * (b - a) =
          -((∫ x in b..a, f x) - f u * (a - b)) := by ring
    rw [hrearrange, abs_neg]
    calc
      |(∫ x in b..a, f x) - f u * (a - b)| ≤
          (C : Real) * (a - b) ^ 2 := h
      _ = (C : Real) * |b - a| ^ 2 := by
        have habs : |b - a| = a - b := by
          rw [abs_of_nonpos (sub_nonpos.mpr hba)]
          ring
        rw [habs]


theorem abs_sub_sub_deriv_mul_le_of_lipschitz
    {f f' : Real → Real} {C : NNReal}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hlip : LipschitzWith C f') (a b : Real) :
    |f b - f a - f' a * (b - a)| ≤ (C : Real) * |b - a| ^ 2 := by
  have hf' : Continuous f' := hlip.continuous
  have hFTC : (∫ x in a..b, f' x) = f b - f a := by
    let g' := deriv f
    have hg' : g' = f' := by
      funext x
      exact (hderiv x).deriv
    have hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt Real f x :=
      fun x _ => (hderiv x).differentiableAt
    have hcont : ContinuousOn g' (Set.uIcc a b) := by
      rw [hg']
      exact hf'.continuousOn
    have h := intervalIntegral.integral_deriv_eq_sub' f rfl hdiff hcont
    simpa [g', hg'] using h
  rw [← hFTC]
  exact abs_intervalIntegral_sub_const_mul_le_of_lipschitz'
    hf' hlip a b a Set.left_mem_uIcc



theorem abs_sixVertexThetaLeftDerivative_sub_right_le
    {c : Real} (hc : 2 < c) (x y z : Real) :
    |4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
          sixVertexThetaDerivativeDenominator c x y -
        4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c z /
          sixVertexThetaDerivativeDenominator c x z| ≤
      sixVertexThetaCrossLipschitzBound c * |y - z| := by
  let w := sixVertexRootDensityWeight c x
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let K := sixVertexRootDensityKernelLipschitzBound c
  have hw : 0 < w := sixVertexRootDensityWeight_pos hc x
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hwlower : wmin ≤ w := sixVertexRootDensityWeight_lower hc x
  have hK : 0 ≤ K := (sixVertexRootDensityKernelLipschitzBound_pos hc).le
  have hkernel := sixVertexRootDensityKernel_lipschitz_right hc x y z
  have hDy := (sixVertexThetaDerivativeDenominator_pos hc x y).ne'
  have hDz := (sixVertexThetaDerivativeDenominator_pos hc x z).ne'
  have hw0 : sixVertexRootDensityWeight c x ≠ 0 :=
    (sixVertexRootDensityWeight_pos hc x).ne'
  have hyrepr :
      4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
          sixVertexThetaDerivativeDenominator c x y =
        -sixVertexRootDensityKernel c x y / w := by
    have h := sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative hc x y
    dsimp [w]
    rw [h]
    field_simp [hw0, hDy]
  have hzrepr :
      4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c z /
          sixVertexThetaDerivativeDenominator c x z =
        -sixVertexRootDensityKernel c x z / w := by
    have h := sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative hc x z
    dsimp [w]
    rw [h]
    field_simp [hw0, hDz]
  have hrearrange :
      4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
            sixVertexThetaDerivativeDenominator c x y -
          4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c z /
            sixVertexThetaDerivativeDenominator c x z =
        -(sixVertexRootDensityKernel c x y -
          sixVertexRootDensityKernel c x z) / w := by
    rw [hyrepr, hzrepr]
    ring
  rw [hrearrange, abs_div, abs_neg, abs_of_pos hw]
  calc
    |sixVertexRootDensityKernel c x y - sixVertexRootDensityKernel c x z| / w ≤
        (K * |y - z|) / w :=
      div_le_div_of_nonneg_right hkernel hw.le
    _ ≤ (K * |y - z|) / wmin :=
      div_le_div_of_nonneg_left (mul_nonneg hK (abs_nonneg _)) hwmin hwlower
    _ = sixVertexThetaCrossLipschitzBound c * |y - z| := by
      dsimp [sixVertexThetaCrossLipschitzBound, K, wmin]
      ring



theorem abs_sixVertexTheta_sub_linearization_le
    {c : Real} (hc : 2 < c) (x y x' y' : Real) :
    |sixVertexTheta c x' y' - sixVertexTheta c x y -
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
            sixVertexThetaDerivativeDenominator c x y) * (x' - x) +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
            sixVertexThetaDerivativeDenominator c x y) * (y' - y))| ≤
      sixVertexThetaTaylorBound c *
        (|x' - x| + |y' - y|) ^ 2 := by
  let L := sixVertexThetaLeftKernelLipschitzBound c
  let X := sixVertexThetaCrossLipschitzBound c
  let T := sixVertexThetaTaylorBound c
  let AxY' := 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y' /
    sixVertexThetaDerivativeDenominator c x y'
  let Axy := 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
    sixVertexThetaDerivativeDenominator c x y
  let Bxy := -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
    sixVertexThetaDerivativeDenominator c x y
  let dx := x' - x
  let dy := y' - y
  have hx := abs_sub_sub_deriv_mul_le_of_lipschitz
    (f := fun u => sixVertexTheta c u y')
    (f' := fun u => 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y' /
      sixVertexThetaDerivativeDenominator c u y')
    (fun u => hasDerivAt_sixVertexTheta_left hc u y')
    (lipschitzWith_sixVertexThetaLeftDerivative hc y') x x'
  have hy := abs_sub_sub_deriv_mul_le_of_lipschitz
    (f := fun v => sixVertexTheta c x v)
    (f' := fun v => -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
      sixVertexThetaDerivativeDenominator c x v)
    (fun v => hasDerivAt_sixVertexTheta_right hc x v)
    (lipschitzWith_sixVertexThetaRightDerivative hc x) y y'
  rw [coe_sixVertexThetaDerivativeLipschitzNNReal hc] at hx hy
  change |sixVertexTheta c x' y' - sixVertexTheta c x y' - AxY' * dx| ≤
    L * |dx| ^ 2 at hx
  change |sixVertexTheta c x y' - sixVertexTheta c x y - Bxy * dy| ≤
    L * |dy| ^ 2 at hy
  have hA : |AxY' - Axy| ≤ X * |dy| := by
    dsimp [AxY', Axy, X, dy]
    exact abs_sixVertexThetaLeftDerivative_sub_right_le hc x y' y
  have hAcross : |(AxY' - Axy) * dx| ≤ X * |dy| * |dx| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hA (abs_nonneg dx)
  have hrearrange :
      sixVertexTheta c x' y' - sixVertexTheta c x y -
          (Axy * dx + Bxy * dy) =
        (sixVertexTheta c x' y' - sixVertexTheta c x y' - AxY' * dx) +
        (sixVertexTheta c x y' - sixVertexTheta c x y - Bxy * dy) +
        (AxY' - Axy) * dx := by ring
  rw [hrearrange]
  calc
    |(sixVertexTheta c x' y' - sixVertexTheta c x y' - AxY' * dx) +
        (sixVertexTheta c x y' - sixVertexTheta c x y - Bxy * dy) +
        (AxY' - Axy) * dx| ≤
      |sixVertexTheta c x' y' - sixVertexTheta c x y' - AxY' * dx| +
        |sixVertexTheta c x y' - sixVertexTheta c x y - Bxy * dy| +
        |(AxY' - Axy) * dx| := by
          exact (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ L * |dx| ^ 2 + L * |dy| ^ 2 + X * |dy| * |dx| :=
      add_le_add (add_le_add hx hy) hAcross
    _ ≤ T * (|dx| + |dy|) ^ 2 := by
      have hL : 0 ≤ L := (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
      have hX : 0 ≤ X := by
        dsimp [X, sixVertexThetaCrossLipschitzBound]
        exact div_nonneg (sixVertexRootDensityKernelLipschitzBound_pos hc).le
          (div_nonneg
            (sub_nonneg.mpr (one_lt_sixVertexAnisotropyMagnitude hc).le)
            (sixVertexRootDensityScale_pos hc).le)
      have hdx : 0 ≤ |dx| := abs_nonneg _
      have hdy : 0 ≤ |dy| := abs_nonneg _
      dsimp [T, sixVertexThetaTaylorBound]
      nlinarith [mul_nonneg hdx hdy,
        mul_nonneg (mul_nonneg hX hdx) hdy]




theorem abs_sum_sixVertexTheta_sub_linearization_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N) (hn : n ≤ N)
    {p q : Fin n → Real} {B : Real} (hB : 0 ≤ B)
    (hoffset : ∀ j, |(N : Real) * (q j - p j)| ≤ B)
    (i : Fin n) :
    |∑ j, (sixVertexTheta c (p i) (p j) -
        sixVertexTheta c (q i) (q j) -
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q i) (q j)) *
              (p i - q i) +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q i) /
            sixVertexThetaDerivativeDenominator c (q i) (q j)) *
              (p j - q j)))| ≤
      4 * sixVertexThetaTaylorBound c * B ^ 2 / N := by
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hT : 0 ≤ sixVertexThetaTaylorBound c := by
    unfold sixVertexThetaTaylorBound sixVertexThetaCrossLipschitzBound
    exact add_nonneg (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
      (div_nonneg (sixVertexRootDensityKernelLipschitzBound_pos hc).le
        (div_nonneg
          (sub_nonneg.mpr (one_lt_sixVertexAnisotropyMagnitude hc).le)
          (sixVertexRootDensityScale_pos hc).le))
  have hdisp (j : Fin n) : |p j - q j| ≤ B / N := by
    have h := hoffset j
    rw [abs_mul, abs_of_pos hNreal, abs_sub_comm] at h
    exact (le_div_iff₀ hNreal).2 (by simpa [mul_comm] using h)
  let R : Fin n → Real := fun j =>
    sixVertexTheta c (p i) (p j) - sixVertexTheta c (q i) (q j) -
      ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q i) (q j)) *
            (p i - q i) +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q i) /
          sixVertexThetaDerivativeDenominator c (q i) (q j)) *
            (p j - q j))
  have hterm (j : Fin n) : |R j| ≤
      sixVertexThetaTaylorBound c * (2 * B / N) ^ 2 := by
    have htaylor := abs_sixVertexTheta_sub_linearization_le
      hc (q i) (q j) (p i) (p j)
    change |R j| ≤ _ at htaylor ⊢
    have hsum : |p i - q i| + |p j - q j| ≤ 2 * B / N := by
      have hi := hdisp i
      have hj := hdisp j
      calc
        |p i - q i| + |p j - q j| ≤ B / N + B / N := add_le_add hi hj
        _ = 2 * B / N := by ring
    have hright : 0 ≤ 2 * B / N := by positivity
    have hsq : (|p i - q i| + |p j - q j|) ^ 2 ≤
        (2 * B / N) ^ 2 := by
      exact (sq_le_sq₀
        (add_nonneg (abs_nonneg _) (abs_nonneg _)) hright).2 hsum
    exact htaylor.trans (mul_le_mul_of_nonneg_left hsq hT)
  change |∑ j, R j| ≤ _
  calc
    |∑ j, R j| ≤ ∑ j, |R j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n,
        sixVertexThetaTaylorBound c * (2 * B / N) ^ 2 :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = (n : Real) *
        (sixVertexThetaTaylorBound c * (2 * B / N) ^ 2) := by simp
    _ ≤ (N : Real) *
        (sixVertexThetaTaylorBound c * (2 * B / N) ^ 2) := by
      gcongr
    _ = 4 * sixVertexThetaTaylorBound c * B ^ 2 / N := by
      field_simp [hNreal.ne']
      ring

end

end StatMech.FrontierD
