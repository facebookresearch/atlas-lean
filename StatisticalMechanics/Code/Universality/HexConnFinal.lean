/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.Universality.HexConnAssembly
import Code.Universality.HexBoundaryUncond

namespace StatMech.Universality

open Filter Topology
open scoped Topology Real NNReal











noncomputable def hexConnFinalLam {a : ℕ → ℂ} {h0 : ℕ → ℤ}
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v))) :
    ℕ → ℝ := fun v => (B v).lam


noncomputable def hexConnFinalTau {a : ℕ → ℂ} {h0 : ℕ → ℤ}
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v))) :
    ℕ → ℝ := fun v => (B v).taup + (B v).taum


noncomputable def hexConnFinalUps {a : ℕ → ℂ} {h0 : ℕ → ℤ}
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v))) :
    ℕ → ℝ := fun v => (B v).ups
















theorem hexConnFinal_bdry (a : ℕ → ℂ) (h0 : ℕ → ℤ)
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v)))
    (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexCl * hexConnFinalLam B v + hexCt * hexConnFinalTau B v + hexConnFinalUps B v = 1 := by
  intro v hv
  
  
  have h := hexBoundary_identity_uncond_via_decomp (a v) (h0 v) (B v) (hFa v hv)
  exact h










































theorem hex_connective_constant_final
    (c : ℕ → ℝ)
    (hge : ∀ n, 1 ≤ c n) (hsub : Submultiplicative c)
    
    (a : ℕ → ℂ) (h0 : ℕ → ℤ)
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v)))
    (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    
    (hlamMono : ∀ v, 1 ≤ v → hexConnFinalLam B v ≤ hexConnFinalLam B (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < hexConnFinalUps B v)
    (hυnn : ∀ v, 0 ≤ hexConnFinalUps B v)
    (hτnn : ∀ v, 0 ≤ hexConnFinalTau B v)
    
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) =
      hexConnFinalLam B (v + 1) - hexConnFinalLam B v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = hexConnFinalUps B (v + 1))
    
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < hexConnFinalTau B v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = hexConnFinalUps B)
    
    (Col : ∀ T, HexColumn T hexChiE)
    (HW : ∀ x, 0 < x → x < hexChiE →
      ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) :=
  hex_connective_constant_assembled c (hexConnFinalLam B) (hexConnFinalTau B)
    (hexConnFinalUps B) hge hsub
    (hexConnFinal_bdry a h0 B hFa)
    hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc Col HW





























theorem hexConnFinal_residue_satisfiable :
    ∃ lam tau ups Fa : ℝ,
      hexCl * lam + hexCt * tau + ups = 1 ∧ Fa = 1 ∧ 0 < ups ∧ 0 ≤ ups ∧ 0 ≤ tau := by
  exact ⟨0, 0, 1, 1, by ring, rfl, one_pos, zero_le_one, le_refl 0⟩

end StatMech.Universality
