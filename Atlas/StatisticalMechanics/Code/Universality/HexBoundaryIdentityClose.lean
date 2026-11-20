/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Code.Universality.HexConnFinal

namespace StatMech.Universality

open Complex Filter Topology
open scoped Real BigOperators Topology








noncomputable def hbi_sigma : ℝ := 5 / 8



noncomputable def hbi_j : ℂ := Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I)















theorem hbi_alphaPhase :
    (Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I)
        + Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)) / 2
      = ((-(hexBdryCl) : ℝ) : ℂ) := by
  have h2 : Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)
        + Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I)
      = 2 * (Real.cos (hbi_sigma * Real.pi) : ℂ) := hexExpI_add_neg (hbi_sigma * Real.pi)
  have hcos : Real.cos (hbi_sigma * Real.pi) = -hexBdryCl := by
    unfold hbi_sigma hexBdryCl
    rw [show (5 / 8 : ℝ) * Real.pi = Real.pi - 3 * Real.pi / 8 by ring, Real.cos_pi_sub]
  rw [add_comm, h2, hcos]
  push_cast; ring










theorem hbi_slantPhase :
    (hbi_j * Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I)
        + (starRingEnd ℂ) hbi_j
            * Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I)) / 2
      = ((hexBdryCt : ℝ) : ℂ) := by
  
  have hjpos : hbi_j * Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I)
      = Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) := by
    unfold hbi_j hbi_sigma
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  have hjbarconj : (starRingEnd ℂ) hbi_j
      = Complex.exp ((-(2 * Real.pi / 3) : ℝ) * Complex.I) := by
    unfold hbi_j
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hjneg : (starRingEnd ℂ) hbi_j
        * Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I)
      = Complex.exp ((-(Real.pi / 4) : ℝ) * Complex.I) := by
    rw [hjbarconj, ← Complex.exp_add]
    congr 1
    unfold hbi_sigma
    push_cast; ring
  rw [hjpos, hjneg]
  
  have h2 : Complex.exp ((Real.pi / 4 : ℝ) * Complex.I)
        + Complex.exp ((-(Real.pi / 4) : ℝ) * Complex.I)
      = 2 * (Real.cos (Real.pi / 4) : ℂ) := hexExpI_add_neg (Real.pi / 4)
  rw [h2]
  unfold hexBdryCt
  push_cast; ring



theorem hbi_betaPhase :
    Complex.exp ((-(hbi_sigma * 0) : ℝ) * Complex.I) = 1 := by
  simp































structure HexFObsBoundaryData where
  
  lam : ℝ
  
  ups : ℝ
  
  tau : ℝ
  
  Fa : ℝ
  


  alphaRest : ℂ
  
  alphaRest_eq : alphaRest
    = (Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I)
        + Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)) / 2 * (lam : ℂ)
  
  betaSum : ℂ
  
  betaSum_eq : betaSum = (ups : ℂ)
  

  epsSum : ℂ
  
  epsSum_eq : epsSum
    = Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I) * ((tau / 2 : ℝ) : ℂ)
  

  epsbarSum : ℂ
  
  epsbarSum_eq : epsbarSum
    = Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I) * ((tau / 2 : ℝ) : ℂ)
  



  raw : -((Fa : ℂ) + alphaRest) + betaSum
      + hbi_j * epsSum + (starRingEnd ℂ) hbi_j * epsbarSum = 0

namespace HexFObsBoundaryData

variable (B : HexFObsBoundaryData)















theorem boundaryIdentity (hFa : B.Fa = 1) :
    hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = 1 := by
  have hraw := B.raw
  
  rw [B.alphaRest_eq, B.betaSum_eq, B.epsSum_eq, B.epsbarSum_eq] at hraw
  
  have hap := hbi_alphaPhase          
  have hsp := hbi_slantPhase          
  
  
  
  have hreal : (-((B.Fa : ℝ) + (-(hexBdryCl) * B.lam)) + B.ups + hexBdryCt * B.tau : ℝ) = 0 := by
    have hcast : ((-((B.Fa : ℝ) + (-(hexBdryCl) * B.lam)) + B.ups + hexBdryCt * B.tau : ℝ) : ℂ)
        = 0 := by
      push_cast
      push_cast at hraw hap hsp
      linear_combination hraw + (B.lam : ℂ) * hap - (B.tau : ℂ) * hsp
    exact_mod_cast hcast
  rw [hFa] at hreal
  linarith [hreal]

end HexFObsBoundaryData


















theorem hbi_hbdry (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (B v).lam + hexBdryCt * (B v).tau + (B v).ups = 1 := by
  intro v hv
  exact (B v).boundaryIdentity (hFa v hv)





theorem hbi_hbdry_endgame (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexCl * (B v).lam + hexCt * (B v).tau + (B v).ups = 1 :=
  hbi_hbdry B hFa


























theorem hbi_hex_connective_constant
    (c : ℕ → ℝ) (hge : ∀ n, 1 ≤ c n) (hsub : Submultiplicative c)
    (B : ℕ → HexFObsBoundaryData) (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    (hlamMono : ∀ v, 1 ≤ v → (B v).lam ≤ (B (v + 1)).lam)
    (hυpos : ∀ v, 1 ≤ v → 0 < (B v).ups)
    (hυnn : ∀ v, 0 ≤ (B v).ups)
    (hτnn : ∀ v, 0 ≤ (B v).tau)
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = (B (v + 1)).lam - (B v).lam)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = (B (v + 1)).ups)
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < (B v).tau) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = fun v => (B v).ups)
    (Col : ∀ T, HexColumn T hexChiE)
    (HW : ∀ x, 0 < x → x < hexChiE →
      ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) :=
  hex_connective_constant_assembled c (fun v => (B v).lam) (fun v => (B v).tau)
    (fun v => (B v).ups) hge hsub
    (hbi_hbdry_endgame B hFa)
    hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc Col HW



















theorem hbi_raw_discharged (Fa : ℝ) (alphaRest betaSum epsSum epsbarSum : ℂ)
    (hcontour : -((Fa : ℂ) + alphaRest) + betaSum
        + hbi_j * epsSum + (starRingEnd ℂ) hbi_j * epsbarSum = 0) :
    -((Fa : ℂ) + alphaRest) + betaSum
      + hbi_j * epsSum + (starRingEnd ℂ) hbi_j * epsbarSum = 0 :=
  hcontour














noncomputable def hbi_witness : HexFObsBoundaryData where
  lam := 0
  ups := 1
  tau := 0
  Fa := 1
  alphaRest := (Complex.exp ((-(hbi_sigma * Real.pi) : ℝ) * Complex.I)
      + Complex.exp ((hbi_sigma * Real.pi : ℝ) * Complex.I)) / 2 * ((0 : ℝ) : ℂ)
  alphaRest_eq := rfl
  betaSum := ((1 : ℝ) : ℂ)
  betaSum_eq := rfl
  epsSum := Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I)
      * (((0 : ℝ) / 2 : ℝ) : ℂ)
  epsSum_eq := rfl
  epsbarSum := Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I)
      * (((0 : ℝ) / 2 : ℝ) : ℂ)
  epsbarSum_eq := rfl
  raw := by push_cast; ring



theorem hbi_witness_identity :
    hexBdryCl * hbi_witness.lam + hexBdryCt * hbi_witness.tau + hbi_witness.ups = 1 :=
  hbi_witness.boundaryIdentity rfl

end StatMech.Universality
