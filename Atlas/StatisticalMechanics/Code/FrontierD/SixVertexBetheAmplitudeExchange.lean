/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexCoordinateBethe

open Finset

namespace StatMech.FrontierD

noncomputable section

private def orderedPairProduct {n : ℕ} {α M : Type*} [CommMonoid M]
    (F : α → α → M) (a : Fin n → α) : M :=
  ∏ k, ∏ l ∈ Finset.Ioi k, F (a k) (a l)

private theorem prod_Ioi_zero {n : ℕ} {M : Type*} [CommMonoid M]
    (f : Fin (n + 1) → M) :
    ∏ l ∈ Finset.Ioi (0 : Fin (n + 1)), f l = ∏ l : Fin n, f l.succ := by
  symm
  apply Finset.prod_bij (fun l _ ↦ l.succ)
  · intro l _
    simp
  · intro l _ k _ h
    exact Fin.succ_injective _ h
  · intro l hl
    have hl0 : l ≠ 0 := by simpa using hl
    have hlval : 0 < l.val := by
      by_contra h
      apply hl0
      apply Fin.ext
      have hzero : l.val = 0 := by omega
      simpa only [Fin.val_zero] using hzero
    let k : Fin n := ⟨l.val - 1, by omega⟩
    refine ⟨k, by simp, ?_⟩
    apply Fin.ext
    simp [k]
    omega
  · simp

private theorem prod_Ioi_succ {n : ℕ} {M : Type*} [CommMonoid M]
    (f : Fin (n + 1) → M) (k : Fin n) :
    ∏ l ∈ Finset.Ioi k.succ, f l =
      ∏ l ∈ Finset.Ioi k, f l.succ := by
  symm
  apply Finset.prod_bij (fun l _ ↦ l.succ)
  · intro l hl
    simpa using hl
  · intro l _ m _ h
    exact Fin.succ_injective _ h
  · intro l hl
    have hl' : k.succ < l := by simpa using hl
    have hl0 : l ≠ 0 := by
      intro h
      subst l
      simp at hl
    have hlval : 0 < l.val := by omega
    let m : Fin n := ⟨l.val - 1, by omega⟩
    refine ⟨m, ?_, ?_⟩
    · simp only [Finset.mem_Ioi]
      change k.val < m.val
      dsimp [m]
      have hv : k.val + 1 < l.val := by exact_mod_cast hl'
      omega
    · apply Fin.ext
      simp [m]
      omega
  · simp

private theorem orderedPairProduct_cons {n : ℕ} {α M : Type*}
    [CommMonoid M] (F : α → α → M) (a : Fin (n + 1) → α) :
    orderedPairProduct F a =
      (∏ l : Fin n, F (a 0) (a l.succ)) *
        orderedPairProduct F (fun l ↦ a l.succ) := by
  unfold orderedPairProduct
  rw [Fin.prod_univ_succ, prod_Ioi_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact prod_Ioi_succ (fun l ↦ F (a k.succ) (a l)) k

private theorem prod_Ioi_castSucc {n : ℕ} {M : Type*} [CommMonoid M]
    (f : Fin (n + 1) → M) (k : Fin n) :
    ∏ l ∈ Finset.Ioi k.castSucc, f l =
      (∏ l ∈ Finset.Ioi k, f l.castSucc) * f (Fin.last n) := by
  have hlast : Fin.last n ∈ Finset.Ioi k.castSucc := by simp
  rw [Finset.prod_eq_prod_diff_singleton_mul hlast]
  congr 1
  have hset : (Finset.Ioi k.castSucc).erase (Fin.last n) =
      (Finset.Ioi k).map Fin.castSuccEmb := by
    ext l
    simp only [Finset.mem_erase, Finset.mem_Ioi, Finset.mem_map]
    constructor
    · rintro ⟨hlast, hkl⟩
      let m := l.castPred hlast
      refine ⟨m, ?_, Fin.castSucc_castPred l hlast⟩
      exact (Fin.castSucc_lt_castSucc_iff.mp
        (Fin.castSucc_castPred l hlast ▸ hkl))
    · rintro ⟨m, hkm, rfl⟩
      exact ⟨Fin.ne_of_lt (Fin.castSucc_lt_last m),
        Fin.castSucc_lt_castSucc_iff.mpr hkm⟩
  rw [Finset.sdiff_singleton_eq_erase, hset, Finset.prod_map]
  rfl

private theorem orderedPairProduct_snoc {n : ℕ} {α M : Type*}
    [CommMonoid M] (F : α → α → M) (a : Fin (n + 1) → α) :
    orderedPairProduct F a =
      orderedPairProduct F (fun k : Fin n ↦ a k.castSucc) *
        ∏ k : Fin n, F (a k.castSucc) (a (Fin.last n)) := by
  unfold orderedPairProduct
  rw [Fin.prod_univ_castSucc]
  have hempty : Finset.Ioi (Fin.last n) = ∅ := by
    ext l
    simp only [Finset.mem_Ioi]
    constructor
    · intro h
      exact ((not_lt_of_ge (Fin.le_last l)) h).elim
    · intro h
      simp at h
  rw [hempty]
  simp only [Finset.prod_empty, mul_one]
  simp_rw [prod_Ioi_castSucc]
  rw [Finset.prod_mul_distrib]

private theorem orderedPairProduct_rotate {n : ℕ} {α M : Type*}
    [CommMonoid M] (F : α → α → M) (a : Fin (n + 1) → α) :
    orderedPairProduct F (fun k ↦ a (finRotate (n + 1) k)) =
      orderedPairProduct F (fun k : Fin n ↦ a k.succ) *
        ∏ k : Fin n, F (a k.succ) (a 0) := by
  rw [orderedPairProduct_snoc]
  have hcast (k : Fin n) : finRotate (n + 1) k.castSucc = k.succ := by
    exact finRotate_of_lt k.isLt
  have hlast : finRotate (n + 1) (Fin.last n) = 0 := finRotate_last'
  simp_rw [hcast, hlast]

private theorem swap_zero_one_succ_succ {n : ℕ} (k : Fin n) :
    Equiv.swap (0 : Fin (n + 2)) (Fin.succ 0) k.succ.succ =
      k.succ.succ := by
  rw [Equiv.swap_apply_def]
  split <;> rename_i h
  · have hv := congrArg Fin.val h
    simp at hv
  · split <;> rename_i h'
    · have hv := congrArg Fin.val h'
      simp at hv
    · rfl

private theorem swap_succ_succ_zero {n : ℕ} (i : Fin n) :
    Equiv.swap i.succ.castSucc i.succ.succ (0 : Fin (n + 2)) = 0 := by
  rw [show i.succ.castSucc = i.castSucc.succ from Fin.castSucc_succ i]
  exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm
    (Fin.succ_ne_zero _).symm

private theorem swap_succ_succ_succ {n : ℕ} (i : Fin n) (k : Fin (n + 1)) :
    Equiv.swap i.succ.castSucc i.succ.succ k.succ =
      (Equiv.swap i.castSucc i.succ k).succ := by
  rw [show i.succ.castSucc = i.castSucc.succ from Fin.castSucc_succ i]
  rcases eq_or_ne k i.castSucc with rfl | hk
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  rcases eq_or_ne k i.succ with rfl | hk'
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_of_ne_of_ne]
  · exact hk
  · exact hk'
  · exact fun h ↦ hk (Fin.succ_injective _ h)
  · exact fun h ↦ hk' (Fin.succ_injective _ h)



private theorem orderedPairProduct_adjacent_swap {n : ℕ} {α M : Type*}
    [CommMonoid M] (F : α → α → M) (a : Fin (n + 1) → α)
    (i : Fin n) :
    F (a i.castSucc) (a i.succ) *
        orderedPairProduct F (fun k ↦ a (Equiv.swap i.castSucc i.succ k)) =
      F (a i.succ) (a i.castSucc) * orderedPairProduct F a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · rw [orderedPairProduct_cons, orderedPairProduct_cons]
        simp only [Fin.castSucc_zero, Equiv.swap_apply_left,
          Equiv.swap_apply_right]
        simp_rw [swap_zero_one_succ_succ]
        rw [Fin.prod_univ_succ]
        simp only [Equiv.swap_apply_right]
        simp_rw [swap_zero_one_succ_succ]
        rw [orderedPairProduct_cons]
        have hhead :
            (∏ l : Fin (n + 1), F (a 0) (a l.succ)) =
              F (a 0) (a (Fin.succ 0)) *
                ∏ l : Fin n, F (a 0) (a l.succ.succ) := by
          rw [Fin.prod_univ_succ]
        have htail :
            orderedPairProduct F (fun l : Fin (n + 1) ↦ a l.succ) =
              (∏ l : Fin n, F (a (Fin.succ 0)) (a l.succ.succ)) *
                orderedPairProduct F (fun l : Fin n ↦ a l.succ.succ) := by
          exact orderedPairProduct_cons F (fun l ↦ a l.succ)
        rw [hhead, htail]
        ac_rfl
      · rw [orderedPairProduct_cons]
        simp only [swap_succ_succ_zero, swap_succ_succ_succ]
        have hhead :
            (∏ l : Fin (n + 1), F (a 0)
                (a ((Equiv.swap i.castSucc i.succ l).succ))) =
              ∏ l : Fin (n + 1), F (a 0) (a l.succ) :=
          Equiv.prod_comp (Equiv.swap i.castSucc i.succ)
            (fun l ↦ F (a 0) (a l.succ))
        rw [hhead]
        have htail := ih (fun k ↦ a k.succ) i
        have hright := orderedPairProduct_cons F a
        rw [hright]
        have hcast : i.succ.castSucc = i.castSucc.succ := Fin.castSucc_succ i
        rw [hcast]
        calc
          F (a i.castSucc.succ) (a i.succ.succ) *
                ((∏ l : Fin (n + 1), F (a 0) (a l.succ)) *
                  orderedPairProduct F
                    (fun l ↦ a ((Equiv.swap i.castSucc i.succ l).succ))) =
              (∏ l : Fin (n + 1), F (a 0) (a l.succ)) *
                (F (a i.castSucc.succ) (a i.succ.succ) *
                  orderedPairProduct F
                    (fun l ↦ a ((Equiv.swap i.castSucc i.succ l).succ))) := by
            ac_rfl
          _ = (∏ l : Fin (n + 1), F (a 0) (a l.succ)) *
                (F (a i.succ.succ) (a i.castSucc.succ) *
                  orderedPairProduct F (fun l ↦ a l.succ)) := by
            rw [htail]
          _ = F (a i.succ.succ) (a i.castSucc.succ) *
                ((∏ l : Fin (n + 1), F (a 0) (a l.succ)) *
                  orderedPairProduct F (fun l ↦ a l.succ)) := by
            ac_rfl




theorem sixVertexBetheAmplitude_adjacent_exchange {c : ℝ} (hc : 2 < c)
    {n : ℕ} (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (i : Fin n) :
    Complex.exp (-Complex.I * sixVertexTheta c (p (σ i.castSucc))
          (p (σ i.succ))) *
        sixVertexBetheAmplitude c p
          (σ * Equiv.swap i.castSucc i.succ) =
      -sixVertexBetheAmplitude c p σ := by
  let F : ℝ → ℝ → ℂ := fun q r ↦
    sixVertexBethePairFactor c (sixVertexBethePhase q)
      (sixVertexBethePhase r)
  have hprod :
      F (p (σ i.castSucc)) (p (σ i.succ)) *
          sixVertexBethePairProduct c p
            (σ * Equiv.swap i.castSucc i.succ) =
        F (p (σ i.succ)) (p (σ i.castSucc)) *
          sixVertexBethePairProduct c p σ := by
    simpa only [F, orderedPairProduct, sixVertexBethePairProduct,
      Equiv.Perm.mul_apply] using
        orderedPairProduct_adjacent_swap F (fun k ↦ p (σ k)) i
  have hpq : F (p (σ i.castSucc)) (p (σ i.succ)) ≠ 0 := by
    exact sixVertexBethePairFactor_phase_ne_zero hc _ _
  have hlocal :
      Complex.exp (-Complex.I * sixVertexTheta c (p (σ i.castSucc))
            (p (σ i.succ))) *
          F (p (σ i.succ)) (p (σ i.castSucc)) =
        F (p (σ i.castSucc)) (p (σ i.succ)) := by
    exact sixVertexBethePairFactor_exchange hc _ _
  have hexchange :
      Complex.exp (-Complex.I * sixVertexTheta c (p (σ i.castSucc))
            (p (σ i.succ))) *
          sixVertexBethePairProduct c p
            (σ * Equiv.swap i.castSucc i.succ) =
        sixVertexBethePairProduct c p σ := by
    apply (mul_left_cancel₀ hpq)
    calc
      F (p (σ i.castSucc)) (p (σ i.succ)) *
          (Complex.exp (-Complex.I * sixVertexTheta c (p (σ i.castSucc))
              (p (σ i.succ))) *
            sixVertexBethePairProduct c p
              (σ * Equiv.swap i.castSucc i.succ)) =
        Complex.exp (-Complex.I * sixVertexTheta c (p (σ i.castSucc))
              (p (σ i.succ))) *
          (F (p (σ i.castSucc)) (p (σ i.succ)) *
            sixVertexBethePairProduct c p
              (σ * Equiv.swap i.castSucc i.succ)) := by ring
      _ = Complex.exp (-Complex.I * sixVertexTheta c (p (σ i.castSucc))
              (p (σ i.succ))) *
            (F (p (σ i.succ)) (p (σ i.castSucc)) *
              sixVertexBethePairProduct c p σ) := by rw [hprod]
      _ = (Complex.exp (-Complex.I * sixVertexTheta c (p (σ i.castSucc))
              (p (σ i.succ))) *
            F (p (σ i.succ)) (p (σ i.castSucc))) *
              sixVertexBethePairProduct c p σ := by ring
      _ = F (p (σ i.castSucc)) (p (σ i.succ)) *
              sixVertexBethePairProduct c p σ := by rw [hlocal]
  have hij : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  unfold sixVertexBetheAmplitude
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  have hsign :
      (((↑(Equiv.Perm.sign σ * (-1 : ℤˣ)) : ℤ) : ℂ)) =
        -(((↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) := by
    norm_num
  rw [hsign]
  calc
    Complex.exp (-Complex.I * sixVertexTheta c (p (σ i.castSucc))
          (p (σ i.succ))) *
        (-(((↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) *
          sixVertexBethePairProduct c p
            (σ * Equiv.swap i.castSucc i.succ)) =
      -(((↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) *
        (Complex.exp (-Complex.I * sixVertexTheta c (p (σ i.castSucc))
            (p (σ i.succ))) *
          sixVertexBethePairProduct c p
            (σ * Equiv.swap i.castSucc i.succ)) := by ring
    _ = -(((↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) *
        sixVertexBethePairProduct c p σ := by rw [hexchange]
    _ = -((((↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) *
        sixVertexBethePairProduct c p σ) := by ring




theorem SixVertexSatisfiesMultiplicativeBetheEquations.amplitude_rotate
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
    (σ : Equiv.Perm (Fin (n + 1))) :
    sixVertexBethePhase (p (σ 0)) ^ N *
        sixVertexBetheAmplitude c p (σ * finRotate (n + 1)) =
      sixVertexBetheAmplitude c p σ := by
  let F : ℝ → ℝ → ℂ := fun q r ↦
    sixVertexBethePairFactor c (sixVertexBethePhase q)
      (sixVertexBethePhase r)
  let a : Fin (n + 1) → ℝ := fun k ↦ p (σ k)
  have horiginal :
      sixVertexBethePairProduct c p σ =
        (∏ k : Fin n, F (a 0) (a k.succ)) *
          orderedPairProduct F (fun k : Fin n ↦ a k.succ) := by
    simpa only [F, a, orderedPairProduct, sixVertexBethePairProduct,
      Equiv.Perm.mul_apply] using orderedPairProduct_cons F a
  have hrotate :
      sixVertexBethePairProduct c p (σ * finRotate (n + 1)) =
        orderedPairProduct F (fun k : Fin n ↦ a k.succ) *
          ∏ k : Fin n, F (a k.succ) (a 0) := by
    simpa only [F, a, orderedPairProduct, sixVertexBethePairProduct,
      Equiv.Perm.mul_apply] using orderedPairProduct_rotate F a
  have hleft :
      (∏ k, F (p k) (a 0)) =
        F (a 0) (a 0) * ∏ k : Fin n, F (a k.succ) (a 0) := by
    calc
      (∏ k, F (p k) (a 0)) = ∏ k, F (p (σ k)) (a 0) :=
        (Equiv.prod_comp σ (fun k ↦ F (p k) (a 0))).symm
      _ = _ := by rw [Fin.prod_univ_succ]
  have hright :
      (∏ k, F (a 0) (p k)) =
        F (a 0) (a 0) * ∏ k : Fin n, F (a 0) (a k.succ) := by
    calc
      (∏ k, F (a 0) (p k)) = ∏ k, F (a 0) (p (σ k)) :=
        (Equiv.prod_comp σ (fun k ↦ F (a 0) (p k))).symm
      _ = _ := by rw [Fin.prod_univ_succ]
  have hperiod := hp.pairFactor_periodic hc (σ 0)
  change sixVertexBethePhase (a 0) ^ N * (∏ k, F (p k) (a 0)) =
      (-1 : ℂ) ^ n * ∏ k, F (a 0) (p k) at hperiod
  rw [hleft, hright] at hperiod
  have hself : F (a 0) (a 0) ≠ 0 := by
    exact sixVertexBethePairFactor_phase_ne_zero hc _ _
  have hsign :
      ((((Equiv.Perm.sign (σ * finRotate (n + 1)) : ℤ) : ℂ))) =
        ((((Equiv.Perm.sign σ : ℤ) : ℂ))) * (-1 : ℂ) ^ n := by
    rw [Equiv.Perm.sign_mul, sign_finRotate]
    simp only [Nat.add_sub_cancel]
    norm_num
  have hsquare : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_pow]
    norm_num
  apply mul_left_cancel₀ hself
  unfold sixVertexBetheAmplitude
  rw [hsign, hrotate, horiginal]
  calc
    F (a 0) (a 0) *
        (sixVertexBethePhase (a 0) ^ N *
          (((((Equiv.Perm.sign σ : ℤ) : ℂ)) * (-1 : ℂ) ^ n) *
            (orderedPairProduct F (fun k : Fin n ↦ a k.succ) *
              ∏ k : Fin n, F (a k.succ) (a 0)))) =
      ((((Equiv.Perm.sign σ : ℤ) : ℂ)) * (-1 : ℂ) ^ n) *
        orderedPairProduct F (fun k : Fin n ↦ a k.succ) *
          (sixVertexBethePhase (a 0) ^ N *
            (F (a 0) (a 0) *
              ∏ k : Fin n, F (a k.succ) (a 0))) := by ring
    _ = ((((Equiv.Perm.sign σ : ℤ) : ℂ)) * (-1 : ℂ) ^ n) *
        orderedPairProduct F (fun k : Fin n ↦ a k.succ) *
          (((-1 : ℂ) ^ n) *
            (F (a 0) (a 0) *
              ∏ k : Fin n, F (a 0) (a k.succ))) := by rw [hperiod]
    _ = F (a 0) (a 0) *
        (((((Equiv.Perm.sign σ : ℤ) : ℂ))) *
          ((∏ k : Fin n, F (a 0) (a k.succ)) *
            orderedPairProduct F (fun k : Fin n ↦ a k.succ))) := by
      calc
        ((((Equiv.Perm.sign σ : ℤ) : ℂ)) * (-1 : ℂ) ^ n) *
            orderedPairProduct F (fun k : Fin n ↦ a k.succ) *
              (((-1 : ℂ) ^ n) *
                (F (a 0) (a 0) *
                  ∏ k : Fin n, F (a 0) (a k.succ))) =
          (((-1 : ℂ) ^ n) * (-1 : ℂ) ^ n) *
            (F (a 0) (a 0) *
              (((((Equiv.Perm.sign σ : ℤ) : ℂ))) *
                ((∏ k : Fin n, F (a 0) (a k.succ)) *
                  orderedPairProduct F (fun k : Fin n ↦ a k.succ)))) := by ring
        _ = _ := by rw [hsquare, one_mul]




theorem SixVertexSatisfiesMultiplicativeBetheEquations.amplitude_boundary_exchange
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin (n + 2) → ℝ}
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (σ : Equiv.Perm (Fin (n + 2))) :
    Complex.exp (-Complex.I * sixVertexTheta c
          (p (σ (Fin.last (n + 1)))) (p (σ 0))) *
        sixVertexBethePhase (p (σ 0)) ^ N *
        sixVertexBetheAmplitude c p
          (σ * ((finRotate (n + 2)).symm *
            Equiv.swap 0 1 * finRotate (n + 2))) =
      -(sixVertexBethePhase (p (σ (Fin.last (n + 1)))) ^ N *
        sixVertexBetheAmplitude c p σ) := by
  let r : Equiv.Perm (Fin (n + 2)) := finRotate (n + 2)
  let ρ : Equiv.Perm (Fin (n + 2)) := σ * r.symm
  have hback := hp.amplitude_rotate hc ρ
  have hadj := sixVertexBetheAmplitude_adjacent_exchange hc p ρ (0 : Fin (n + 1))
  have hfront := hp.amplitude_rotate hc
    (ρ * Equiv.swap (0 : Fin (n + 2)) (1 : Fin (n + 2)))
  have hr0 : r.symm 0 = Fin.last (n + 1) := by
    dsimp [r]
    rw [finRotate_symm_apply]
    apply Fin.ext
    simp
  have hr1 : r.symm 1 = 0 := by
    dsimp [r]
    rw [finRotate_symm_apply]
    apply Fin.ext
    simp
  have hρ0 : ρ 0 = σ (Fin.last (n + 1)) := by
    simp [ρ, Equiv.Perm.mul_apply, hr0]
  have hρ1 : ρ 1 = σ 0 := by
    simp [ρ, Equiv.Perm.mul_apply, hr1]
  have hrr : r.symm * r = 1 := by
    ext j
    simp [Equiv.Perm.mul_apply]
  change sixVertexBethePhase (p (ρ 0)) ^ N *
      sixVertexBetheAmplitude c p (ρ * r) =
    sixVertexBetheAmplitude c p ρ at hback
  change sixVertexBethePhase (p ((ρ *
      Equiv.swap (0 : Fin (n + 2)) (1 : Fin (n + 2))) 0)) ^ N *
      sixVertexBetheAmplitude c p
        ((ρ * Equiv.swap (0 : Fin (n + 2)) (1 : Fin (n + 2))) * r) =
    sixVertexBetheAmplitude c p
      (ρ * Equiv.swap (0 : Fin (n + 2)) (1 : Fin (n + 2))) at hfront
  have hback' :
      sixVertexBethePhase (p (σ (Fin.last (n + 1)))) ^ N *
          sixVertexBetheAmplitude c p σ =
        sixVertexBetheAmplitude c p ρ := by
    rw [show ρ * r = σ by simp [ρ, mul_assoc, hrr]] at hback
    simpa [hρ0] using hback
  have hfront' :
      sixVertexBethePhase (p (σ 0)) ^ N *
          sixVertexBetheAmplitude c p
            (ρ * Equiv.swap (0 : Fin (n + 2)) (1 : Fin (n + 2)) * r) =
        sixVertexBetheAmplitude c p
          (ρ * Equiv.swap (0 : Fin (n + 2)) (1 : Fin (n + 2))) := by
    simpa [ρ, hρ1, Equiv.Perm.mul_apply, mul_assoc] using hfront
  rw [show σ * (r.symm * Equiv.swap 0 1 * r) =
      ρ * Equiv.swap 0 1 * r by simp [ρ, mul_assoc]]
  rw [mul_assoc, hfront']
  rw [show sixVertexTheta c (p (σ (Fin.last (n + 1)))) (p (σ 0)) =
      sixVertexTheta c (p (ρ (0 : Fin (n + 2))))
        (p (ρ (1 : Fin (n + 2)))) by rw [hρ0, hρ1]]
  have hadj' :
      Complex.exp (-Complex.I * sixVertexTheta c (p (ρ 0)) (p (ρ 1))) *
          sixVertexBetheAmplitude c p (ρ * Equiv.swap 0 1) =
        -sixVertexBetheAmplitude c p ρ := by
    simpa using hadj
  rw [hadj', hback']

end

end StatMech.FrontierD
