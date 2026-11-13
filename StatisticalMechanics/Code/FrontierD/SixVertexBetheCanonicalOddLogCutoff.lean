/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOddOffsetLinear
import Code.FrontierD.SixVertexBetheLogRegularizationCutoff





namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

private theorem card_filter_fin_val_lt_le_odd (n T : Nat) :
    (Finset.univ.filter (fun j : Fin n => j.val < T)).card <= T := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => j.val < T)
  let f : {j // j ∈ S} -> Fin T := fun j =>
    ⟨j.1.val, (Finset.mem_filter.mp j.2).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hv : (f a).val = (f b).val :=
      congrArg (fun z : Fin T => z.val) hab
    apply Subtype.ext
    apply Fin.ext
    exact hv
  have hcard := Fintype.card_le_of_injective f hf
  change S.card <= T
  rw [<- Fintype.card_coe]
  simpa using hcard

theorem abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff_additive
    {c epsilon delta C D : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hC : 0 <= C) (hD : 0 <= D)
    {N n T : Nat} (hN : 0 < N) {p q : Fin n -> Real}
    (hp : forall j, p j ∈ Set.Ioo 0 Real.pi)
    (hq : forall j, q j ∈ Set.Ioo 0 Real.pi)
    (hscale : forall j, Real.pi <= (N : Real) * p j)
    (hclose : forall j, |q j - p j| <= p j / 2)
    (hdiff : forall j,
      |q j - p j| <= C * p j / N + D / (N : Real) ^ 2)
    (hfar : forall j, T <= j.val -> delta <= p j) :
    |∑ j, (sixVertexBetheLogRegularizationError c epsilon (q j) -
        sixVertexBetheLogRegularizationError c epsilon (p j))| <=
      (T : Real) * ((2 * Real.pi * C + 2 * D) / N) +
        (n : Real) *
          ((epsilon * Real.pi ^ 4 / delta ^ 4) *
            ((C * Real.pi + D) / N)) := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => j.val < T)
  let f : Fin n -> Real := fun j =>
    sixVertexBetheLogRegularizationError c epsilon (q j) -
      sixVertexBetheLogRegularizationError c epsilon (p j)
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hsmall (j : Fin n) (hj : j ∈ S) :
      |f j| <= (2 * Real.pi * C + 2 * D) / N := by
    have hs := abs_sixVertexBetheLogRegularizationError_sub_le_singular
      hc hepsilon (hp j) (hq j) (hclose j)
    have hp0 := (hp j).1
    have hNp := hscale j
    have hNpPos : 0 < (N : Real) * p j := mul_pos hNreal hp0
    have hratio : Real.pi / ((N : Real) * p j) <= 1 :=
      (div_le_one hNpPos).2 hNp
    have hDterm :
        (2 * Real.pi / p j) * (D / (N : Real) ^ 2) <= 2 * D / N := by
      rw [show (2 * Real.pi / p j) * (D / (N : Real) ^ 2) =
        (2 * D / N) * (Real.pi / ((N : Real) * p j)) by
          field_simp [hp0.ne', hNreal.ne']
          ]
      simpa using mul_le_mul_of_nonneg_left hratio (by positivity :
        0 <= 2 * D / (N : Real))
    calc
      |f j| <= (2 * Real.pi / p j) * |q j - p j| := hs
      _ <= (2 * Real.pi / p j) *
          (C * p j / N + D / (N : Real) ^ 2) :=
        mul_le_mul_of_nonneg_left (hdiff j) (by positivity)
      _ = (2 * Real.pi / p j) * (C * p j / N) +
          (2 * Real.pi / p j) * (D / (N : Real) ^ 2) := by ring
      _ <= 2 * Real.pi * C / N + 2 * D / N := by
        have hCterm : (2 * Real.pi / p j) * (C * p j / N) =
            2 * Real.pi * C / N := by
          field_simp [hp0.ne']
        rw [hCterm]
        exact add_le_add le_rfl hDterm
      _ = (2 * Real.pi * C + 2 * D) / N := by ring
  have hlarge (j : Fin n) (hj : j ∉ S) :
      |f j| <= (epsilon * Real.pi ^ 4 / delta ^ 4) *
          ((C * Real.pi + D) / N) := by
    have hjFar : T <= j.val := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
      exact hj
    have hs := abs_sixVertexBetheLogRegularizationError_sub_le_far
      hc hepsilon hdelta (hp j) (hq j) (hfar j hjFar) (hclose j)
    have hdiff' : |q j - p j| <= (C * Real.pi + D) / N := by
      calc
        |q j - p j| <= C * p j / N + D / (N : Real) ^ 2 := hdiff j
        _ <= C * Real.pi / N + D / N := by
          apply add_le_add
          · exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hp j).2.le hC) hNreal.le
          · have hNN : (N : Real) <= (N : Real) ^ 2 := by
              have hNone : (1 : Real) <= N := by exact_mod_cast hN
              nlinarith
            exact div_le_div_of_nonneg_left hD hNreal hNN
        _ = (C * Real.pi + D) / N := by ring
    exact hs.trans (mul_le_mul_of_nonneg_left hdiff' (by positivity))
  rw [show (∑ j, f j) = (∑ j ∈ S, f j) + ∑ j ∈ Sᶜ, f j by
    rw [Finset.sum_add_sum_compl]]
  calc
    |(∑ j ∈ S, f j) + ∑ j ∈ Sᶜ, f j| <=
        |∑ j ∈ S, f j| + |∑ j ∈ Sᶜ, f j| := abs_add_le _ _
    _ <= (∑ j ∈ S, |f j|) + ∑ j ∈ Sᶜ, |f j| := by
      exact add_le_add (Finset.abs_sum_le_sum_abs _ _)
        (Finset.abs_sum_le_sum_abs _ _)
    _ <= (∑ _j ∈ S, (2 * Real.pi * C + 2 * D) / N) +
        ∑ _j ∈ Sᶜ,
          (epsilon * Real.pi ^ 4 / delta ^ 4) *
            ((C * Real.pi + D) / N) := by
      apply add_le_add <;> apply Finset.sum_le_sum
      · intro j hj
        exact hsmall j hj
      · intro j hj
        exact hlarge j (by simpa using hj)
    _ <= (T : Real) * ((2 * Real.pi * C + 2 * D) / N) +
        (n : Real) *
          ((epsilon * Real.pi ^ 4 / delta ^ 4) *
            ((C * Real.pi + D) / N)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right
        · exact_mod_cast card_filter_fin_val_lt_le_odd n T
        · positivity
      · apply mul_le_mul_of_nonneg_right
        · have hcard : (Sᶜ).card <= n := by
            simpa using (Finset.card_le_univ Sᶜ)
          exact_mod_cast hcard
        · positivity

theorem eventually_abs_sum_sixVertexCanonicalOddLogRegularizationError_le_cutoff
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (s : Nat) {M : Nat} (hM : 0 < M) :
    ∀ᶠ k : Nat in atTop,
      let N := sixVertexFourWidth (2 * s + 1) k
      let n := s + k + 1
      let C := sixVertexCanonicalOddOffsetLinearBound c hc s
      let D := sixVertexCanonicalOddOffsetRemainderBound c hc s
      |∑ j : Fin n,
          (sixVertexBetheLogRegularizationError c epsilon
              (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) -
            sixVertexBetheLogRegularizationError c epsilon
              (sixVertexCanonicalOddMidpointHalfRoot hc s k j))| <=
        (2 * Real.pi * C + 2 * D) * (1 / M + 1 / N) +
          epsilon * (C * Real.pi + D) * M ^ 4 / 16 := by
  let C := sixVertexCanonicalOddOffsetLinearBound c hc s
  let D := sixVertexCanonicalOddOffsetRemainderBound c hc s
  have hC : 0 <= C := sixVertexCanonicalOddOffsetLinearBound_nonneg hc s
  have hD : 0 <= D := sixVertexCanonicalOddOffsetRemainderBound_nonneg hc s
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hwide : ∀ᶠ k : Nat in atTop,
      2 * (C + D / Real.pi) <=
        (sixVertexFourWidth (2 * s + 1) k : Real) :=
    hwidth.eventually (eventually_ge_atTop (2 * (C + D / Real.pi)))
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s,
      eventually_abs_sixVertexCanonicalOddChargeOffset_le_linear_add hc s,
      hwide] with k hk hoff hNk
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := s + k + 1
  let p : Fin n -> Real := sixVertexCanonicalOddMidpointHalfRoot hc s k
  let q : Fin n -> Real :=
    sixVertexCanonicalFixedOddDensityPositiveRoots hc s k
  have hN : 0 < N := sixVertexFourWidth_pos (2 * s + 1) k
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hMreal : 0 < (M : Real) := by exact_mod_cast hM
  have hp (j : Fin n) : p j ∈ Set.Ioo 0 Real.pi := by
    have hL := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩
    have hR := sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + 1 + k) ⟨j.val + 1, by dsimp [n] at j ⊢; omega⟩
    change (sixVertexCanonicalDensityPerronPositiveHalfRoots hc
        (2 * s + 1 + k) ⟨j.val, by omega⟩ +
      sixVertexCanonicalDensityPerronPositiveHalfRoots hc
        (2 * s + 1 + k) ⟨j.val + 1, by omega⟩) / 2 ∈
        Set.Ioo 0 Real.pi
    constructor <;> linarith [hL.1, hL.2, hR.1, hR.2]
  have hq (j : Fin n) : q j ∈ Set.Ioo 0 Real.pi := by
    let i := sixVertexOddPositiveIndex n j
    let z := sixVertexOddCentralIndex n
    have hzi : z < i := by
      rw [Fin.lt_def]
      simp [z, i, sixVertexOddCentralIndex, sixVertexOddPositiveIndex]
      omega
    have hpos : 0 < q j := by
      have h := hk.1.1.1 hzi
      change sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k z <
        sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i at h
      rw [sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero
        hc s k hk] at h
      exact h
    have hpi := (hk.1.1.2.2 i).2
    exact ⟨hpos, by simpa [q, sixVertexCanonicalFixedOddDensityPositiveRoots,
      sixVertexOddPositiveHalfProjection, i] using hpi⟩
  have hscale (j : Fin n) : Real.pi <= (N : Real) * p j := by
    have hquant :=
      sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower hc
        (2 * s + 1 + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩
    have hwidthEq : sixVertexFourWidth 0 (2 * s + 1 + k) = N := by
      dsimp [N]
      unfold sixVertexFourWidth
      omega
    have hmidLower :
        sixVertexCanonicalDensityPerronPositiveHalfRoots hc
            (2 * s + 1 + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩ <= p j := by
      have horder := (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
        (2 * s + 1 + k)).1
      dsimp [p, sixVertexCanonicalOddMidpointHalfRoot,
        sixVertexCanonicalOddLeftHalfRoot, sixVertexCanonicalOddRightHalfRoot,
        sixVertexCanonicalDensityPerronPositiveHalfRoots,
        sixVertexEvenPositiveHalfProjection]
      have h := horder (show
        Fin.natAdd (2 * s + 1 + k + 1) ⟨j.val, by omega⟩ <
          Fin.natAdd (2 * s + 1 + k + 1) ⟨j.val + 1, by omega⟩ by
            simp [Fin.lt_def])
      have h' :
          sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
              ⟨2 * s + 1 + k + 1 + j.val, by omega⟩ <
            sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
              ⟨2 * s + 1 + k + 1 + (j.val + 1), by omega⟩ := by
        simpa [Fin.natAdd] using h
      linarith
    rw [hwidthEq] at hquant
    have hmul := mul_le_mul_of_nonneg_left hmidLower hNreal.le
    have hquant' : Real.pi < (N : Real) *
        sixVertexCanonicalDensityPerronPositiveHalfRoots hc
          (2 * s + 1 + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩ := by
      have hj0 : 0 <= (j.val : Real) := by positivity
      nlinarith [hquant, Real.pi_pos]
    exact (le_of_lt hquant').trans hmul
  have hdiff (j : Fin n) :
      |q j - p j| <= C * p j / N + D / (N : Real) ^ 2 := by
    let i := sixVertexOddPositiveIndex n j
    have hi := hoff i
    have haligned : sixVertexCanonicalOddAlignedHalfRoots hc s k i = p j := by
      dsimp [i, n, p]
      exact sixVertexCanonicalOddAlignedHalfRoots_positive hc s k j
    have hfixed :
        sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i = q j := by
      rfl
    rw [sixVertexCanonicalOddChargeOffset, haligned, hfixed,
      abs_mul, abs_of_pos hNreal, abs_of_pos (hp j).1] at hi
    calc
      |q j - p j| <= (C * p j + D / N) / N :=
        (le_div_iff₀ hNreal).2
          (by simpa [N, C, D, Nat.mul_comm, mul_comm, mul_left_comm,
            mul_assoc] using hi)
      _ = C * p j / N + D / (N : Real) ^ 2 := by
        field_simp [hNreal.ne']
  have hclose (j : Fin n) : |q j - p j| <= p j / 2 := by
    calc
      |q j - p j| <= C * p j / N + D / (N : Real) ^ 2 := hdiff j
      _ <= (C / N + D / (Real.pi * N)) * p j := by
        have hs := hscale j
        have hNpPos : 0 < (N : Real) * p j := mul_pos hNreal (hp j).1
        have hratio : Real.pi / ((N : Real) * p j) <= 1 :=
          (div_le_one hNpPos).2 hs
        have hDscale : D / (N : Real) ^ 2 <=
            (D / (Real.pi * N)) * p j := by
          rw [show D / (N : Real) ^ 2 =
            ((D / (Real.pi * N)) * p j) *
              (Real.pi / ((N : Real) * p j)) by
                field_simp [Real.pi_ne_zero, hNreal.ne', (hp j).1.ne']
                ]
          have hcoefD : 0 <= (D / (Real.pi * N)) * p j :=
            mul_nonneg (div_nonneg hD
              (mul_nonneg Real.pi_pos.le hNreal.le)) (hp j).1.le
          simpa using mul_le_mul_of_nonneg_left hratio
            hcoefD
        calc
          _ <= C * p j / N + (D / (Real.pi * N)) * p j :=
            add_le_add_right hDscale _
          _ = _ := by ring
      _ <= p j / 2 := by
        have hw : 2 * (C + D / Real.pi) <= (N : Real) := by
          simpa [N, C, D] using hNk
        have hp0 := (hp j).1
        have hcoef : C / N + D / (Real.pi * N) <= 1 / 2 := by
          apply (le_div_iff₀ (by norm_num : (0 : Real) < 2)).2
          rw [show (C / N + D / (Real.pi * N)) * 2 =
            2 * (C + D / Real.pi) / N by ring]
          exact (div_le_one hNreal).2 hw
        convert mul_le_mul_of_nonneg_right hcoef hp0.le using 1 <;> ring
  have hfar (j : Fin n) (hj : N / M + 1 <= j.val) :
      2 * Real.pi / M <= p j := by
    have hjdiv : N / M < j.val := by omega
    have hNjM : N < j.val * M :=
      (Nat.div_lt_iff_lt_mul hM).1 hjdiv
    have hNjMreal : (N : Real) < (j.val : Real) * M := by
      exact_mod_cast hNjM
    have hjpos : 0 < (j.val : Real) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ _) hj)
    have hquant :=
      sixVertexCanonicalDensityPerronPositiveHalfRoots_quantile_lower hc
        (2 * s + 1 + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩
    have hwidthEq : sixVertexFourWidth 0 (2 * s + 1 + k) = N := by
      dsimp [N]
      unfold sixVertexFourWidth
      omega
    have hleftMid :
        sixVertexCanonicalDensityPerronPositiveHalfRoots hc
            (2 * s + 1 + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩ <= p j := by
      have hs := hscale j
      have hq0 : 0 < sixVertexCanonicalDensityPerronPositiveHalfRoots hc
          (2 * s + 1 + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩ :=
        (sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc _ _).1
      dsimp [p, sixVertexCanonicalOddMidpointHalfRoot,
        sixVertexCanonicalOddLeftHalfRoot, sixVertexCanonicalOddRightHalfRoot]
      have horder := (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc
        (2 * s + 1 + k)).1
      have h := horder (show
        Fin.natAdd (2 * s + 1 + k + 1) ⟨j.val, by omega⟩ <
          Fin.natAdd (2 * s + 1 + k + 1) ⟨j.val + 1, by omega⟩ by
            simp [Fin.lt_def])
      dsimp [sixVertexCanonicalDensityPerronPositiveHalfRoots,
        sixVertexEvenPositiveHalfProjection] at h ⊢
      linarith
    rw [hwidthEq] at hquant
    have hquant' : Real.pi * (2 * (j.val : Real) + 1) <
        (N : Real) * p j :=
      hquant.trans_le (mul_le_mul_of_nonneg_left hleftMid hNreal.le)
    have hNp : (N : Real) * p j <
        ((j.val : Real) * M) * p j :=
      mul_lt_mul_of_pos_right hNjMreal (hp j).1
    apply (div_le_iff₀ hMreal).2
    by_contra hbad
    rw [not_le] at hbad
    have hbad' : (M : Real) * p j < 2 * Real.pi := by
      simpa [mul_comm] using hbad
    have hjbad := mul_lt_mul_of_pos_left hbad' hjpos
    nlinarith
  have hcut :=
    abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff_additive
      hc hepsilon (div_pos (mul_pos (by norm_num) Real.pi_pos) hMreal)
      hC hD hN hp hq hscale hclose hdiff hfar
  have hcastDiv : ((N / M : Nat) : Real) <= (N : Real) / M :=
    Nat.cast_div_le
  have hnN : n <= N := by
    dsimp [n, N]
    unfold sixVertexFourWidth
    omega
  calc
    |∑ j : Fin n,
        (sixVertexBetheLogRegularizationError c epsilon (q j) -
          sixVertexBetheLogRegularizationError c epsilon (p j))| <=
        ((N / M + 1 : Nat) : Real) *
            ((2 * Real.pi * C + 2 * D) / N) +
          (n : Real) *
            ((epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) *
              ((C * Real.pi + D) / N)) := hcut
    _ <= (2 * Real.pi * C + 2 * D) * (1 / M + 1 / N) +
        epsilon * (C * Real.pi + D) * M ^ 4 / 16 := by
      apply add_le_add
      · calc
          ((N / M + 1 : Nat) : Real) *
              ((2 * Real.pi * C + 2 * D) / N) <=
              ((N : Real) / M + 1) *
                ((2 * Real.pi * C + 2 * D) / N) := by
            apply mul_le_mul_of_nonneg_right
            · push_cast
              linarith
            · positivity
          _ = (2 * Real.pi * C + 2 * D) * (1 / M + 1 / N) := by
            field_simp [hMreal.ne', hNreal.ne']
      · calc
          (n : Real) *
              ((epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) *
                ((C * Real.pi + D) / N)) <=
              (N : Real) *
                ((epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) *
                  ((C * Real.pi + D) / N)) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hnN
            · positivity
          _ = epsilon * (C * Real.pi + D) * M ^ 4 / 16 := by
            field_simp [hMreal.ne', hNreal.ne', Real.pi_ne_zero]
            ring

end

end StatMech.FrontierD
