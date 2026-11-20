/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheRootGapFirstOrder
import Code.FrontierD.SixVertexBetheOffsetTaylor





namespace StatMech.FrontierD

noncomputable section




theorem abs_width_mul_matchedBetheRoot_sub_le_of_weightedDensityClose
    {c : Real} (hc : 2 < c) {N np nq : Nat} (hN : 0 < N)
    {p : Fin np -> Real} {q : Fin nq -> Real}
    (hpOpen : SixVertexOpenRootSimplex p)
    (hqOpen : SixVertexOpenRootSimplex q)
    (hpSol : SixVertexSatisfiesBetheEquations c N np p)
    (hqSol : SixVertexSatisfiesBetheEquations c N nq q)
    {rho : Real -> Real} {E0 Er lower : Real}
    (hE0 : 0 <= E0) (hEr : 0 <= Er) (hlower : 0 < lower)
    (hpClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi ->
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N np p x - rho x)| <= E0 / N)
    (hqClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi ->
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N nq q x - rho x)| <= Er / N)
    (hqDensity : forall x,
      lower <= sixVertexFiniteRootDensity c N nq q x)
    (ip : Fin np) (iq : Fin nq)
    (hquantum : sixVertexCentralQuantumNumber ip =
      sixVertexCentralQuantumNumber iq) :
    |(N : Real) * (q iq - p ip)| <=
      Real.pi * (E0 + Er) /
        (((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) * lower) := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hipIcc : p ip ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(hpOpen.2.2 ip).1.le, (hpOpen.2.2 ip).2.le⟩
  have hcountBound :=
    abs_sixVertexBetheCountingFunction_sub_le_of_weightedDensityClose
      hc hN hpOpen.2.1 hqOpen.2.1 hE0 hEr hpClose hqClose hipIcc
  have hpAt := sixVertexBetheCountingFunction_at_root hN hpSol ip
  have hqAt := sixVertexBetheCountingFunction_at_root hN hqSol iq
  have hcountEq :
      sixVertexBetheCountingFunction c N np p (p ip) =
        sixVertexBetheCountingFunction c N nq q (q iq) := by
    rw [hpAt, hqAt, hquantum]
  have hlowerCount :=
    lower_mul_abs_sub_le_abs_sixVertexBetheCountingFunction_sub
      hc hN q hlower.le hqDensity (a := p ip) (b := q iq)
  rw [<- hcountEq] at hlowerCount
  have hcombined : lower * |q iq - p ip| <=
      (((E0 + Er) / wmin) / N) * Real.pi :=
    hlowerCount.trans hcountBound
  have hdiff : |q iq - p ip| <=
      ((((E0 + Er) / wmin) / N) * Real.pi) / lower :=
    (le_div_iff₀ hlower).2 (by simpa [mul_comm] using hcombined)
  rw [abs_mul, abs_of_pos hNreal]
  calc
    (N : Real) * |q iq - p ip| <=
        (N : Real) * (((((E0 + Er) / wmin) / N) * Real.pi) / lower) :=
      mul_le_mul_of_nonneg_left hdiff hNreal.le
    _ = Real.pi * (E0 + Er) / (wmin * lower) := by
      field_simp [hNreal.ne', hwmin.ne', hlower.ne']



theorem abs_width_mul_BetheRoot_sub_le_of_weightedDensityClose
    {c : Real} (hc : 2 < c) {N np nq : Nat} (hN : 0 < N)
    {p : Fin np -> Real} {q : Fin nq -> Real}
    (hpOpen : SixVertexOpenRootSimplex p)
    (hqOpen : SixVertexOpenRootSimplex q)
    (hpSol : SixVertexSatisfiesBetheEquations c N np p)
    (hqSol : SixVertexSatisfiesBetheEquations c N nq q)
    {rho : Real -> Real} {E0 Er lower Q : Real}
    (hE0 : 0 <= E0) (hEr : 0 <= Er) (hlower : 0 < lower)
    (hQ : 0 <= Q)
    (hpClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi ->
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N np p x - rho x)| <= E0 / N)
    (hqClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi ->
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N nq q x - rho x)| <= Er / N)
    (hqDensity : forall x,
      lower <= sixVertexFiniteRootDensity c N nq q x)
    (ip : Fin np) (iq : Fin nq)
    (hquantum : |sixVertexCentralQuantumNumber ip -
      sixVertexCentralQuantumNumber iq| <= Q) :
    |(N : Real) * (q iq - p ip)| <=
      (Q + Real.pi * (E0 + Er) /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) / lower := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hwmin : 0 < wmin := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  have hipIcc : p ip ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(hpOpen.2.2 ip).1.le, (hpOpen.2.2 ip).2.le⟩
  have hcountBound :=
    abs_sixVertexBetheCountingFunction_sub_le_of_weightedDensityClose
      hc hN hpOpen.2.1 hqOpen.2.1 hE0 hEr hpClose hqClose hipIcc
  have hpAt := sixVertexBetheCountingFunction_at_root hN hpSol ip
  have hqAt := sixVertexBetheCountingFunction_at_root hN hqSol iq
  have hquantumCount :
      |sixVertexBetheCountingFunction c N nq q (q iq) -
        sixVertexBetheCountingFunction c N np p (p ip)| <= Q / N := by
    rw [hpAt, hqAt, <- sub_div, abs_div, abs_of_pos hNreal]
    exact div_le_div_of_nonneg_right
      (by simpa [abs_sub_comm] using hquantum) hNreal.le
  have htotal :
      |sixVertexBetheCountingFunction c N nq q (q iq) -
        sixVertexBetheCountingFunction c N nq q (p ip)| <=
      Q / N + (((E0 + Er) / wmin) / N) * Real.pi := by
    calc
      |_ - _| <=
          |sixVertexBetheCountingFunction c N nq q (q iq) -
            sixVertexBetheCountingFunction c N np p (p ip)| +
          |sixVertexBetheCountingFunction c N np p (p ip) -
            sixVertexBetheCountingFunction c N nq q (p ip)| :=
        abs_sub_le _ _ _
      _ <= _ := add_le_add hquantumCount hcountBound
  have hlowerCount :=
    lower_mul_abs_sub_le_abs_sixVertexBetheCountingFunction_sub
      hc hN q hlower.le hqDensity (a := p ip) (b := q iq)
  have hcombined : lower * |q iq - p ip| <=
      Q / N + (((E0 + Er) / wmin) / N) * Real.pi :=
    hlowerCount.trans (by simpa [abs_sub_comm] using htotal)
  have hdiff : |q iq - p ip| <=
      (Q / N + (((E0 + Er) / wmin) / N) * Real.pi) / lower :=
    (le_div_iff₀ hlower).2 (by simpa [mul_comm] using hcombined)
  rw [abs_mul, abs_of_pos hNreal]
  calc
    (N : Real) * |q iq - p ip| <=
        (N : Real) *
          ((Q / N + (((E0 + Er) / wmin) / N) * Real.pi) / lower) :=
      mul_le_mul_of_nonneg_left hdiff hNreal.le
    _ = (Q + Real.pi * (E0 + Er) / wmin) / lower := by
      field_simp [hNreal.ne', hwmin.ne', hlower.ne']


theorem abs_genericOffsetNodalResidual_le
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N) (hn : n <= N)
    {p q : Fin n -> Real} {eps boundary : Fin n -> Real}
    {B : Real} (hB : 0 <= B)
    (heps : forall j, eps j = (N : Real) * (q j - p j))
    (hoffset : forall j, |eps j| <= B)
    (hcommon : forall i, eps i - boundary i =
      ∑ j, (sixVertexTheta c (p i) (p j) -
        sixVertexTheta c (q i) (q j)))
    (i : Fin n) :
    |eps i - boundary i + (1 / (N : Real)) * ∑ j,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q i) (q j)) * eps i +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q i) /
            sixVertexThetaDerivativeDenominator c (q i) (q j)) * eps j)| <=
      4 * sixVertexThetaTaylorBound c * B ^ 2 / N := by
  have hoffset' : forall j, |(N : Real) * (q j - p j)| <= B := by
    intro j
    rw [<- heps j]
    exact hoffset j
  have htaylor := abs_sum_sixVertexTheta_sub_linearization_le
    hc hN hn hB hoffset' i
  let R : Fin n -> Real := fun j =>
    sixVertexTheta c (p i) (p j) - sixVertexTheta c (q i) (q j) -
      ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
          sixVertexThetaDerivativeDenominator c (q i) (q j)) *
            (p i - q i) +
        (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q i) /
          sixVertexThetaDerivativeDenominator c (q i) (q j)) *
            (p j - q j))
  change |∑ j, R j| <= 4 * sixVertexThetaTaylorBound c * B ^ 2 / N
    at htaylor
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hpoint (j : Fin n) : p j - q j = -(eps j) / N := by
    rw [heps j]
    field_simp [hN0]
    ring
  rw [hcommon i, Finset.mul_sum, <- Finset.sum_add_distrib]
  have heq :
      (∑ j, (sixVertexTheta c (p i) (p j) -
          sixVertexTheta c (q i) (q j) +
        (1 / (N : Real)) *
          ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
              sixVertexThetaDerivativeDenominator c (q i) (q j)) * eps i +
            (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q i) /
              sixVertexThetaDerivativeDenominator c (q i) (q j)) * eps j))) =
        ∑ j, R j := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [R]
    rw [hpoint i, hpoint j]
    field_simp [hN0]
    ring
  rw [heq]
  exact htaylor

end

end StatMech.FrontierD
