/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.OSSS.RevealmentSum
import Code.Walls.oc3_core

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.Coding
open StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]























noncomputable def oc4_codingProb {α : Type*} (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n → E) (g : α → ℕ → ConfigSpace E → ℝ) (x : α) (j : ℕ) : ℝ :=
  ∫ u, g x j (codeMap μ σ u) ∂(Vcube n)










theorem oc4_codingProb_eq_mean {α : Type*} (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : α → ℕ → ConfigSpace E → ℝ)
    (x : α) (j : ℕ) :
    oc4_codingProb μ (σ : Fin n → E) g x j = Lindeberg.mean μ (g x j) :=
  (oc3_expectAsCube_codingFrame μ hpos hμ1 σ (g x j)).symm









theorem oc4_codingProb_nonneg {α : Type*} (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n → E) (g : α → ℕ → ConfigSpace E → ℝ) (hg : ∀ x j ω, 0 ≤ g x j ω)
    (x : α) (j : ℕ) :
    0 ≤ oc4_codingProb μ σ g x j := by
  unfold oc4_codingProb
  exact integral_nonneg (fun u => hg x j _)






theorem oc4_codingProb_nonneg_of_mean {α : Type*} (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : α → ℕ → ConfigSpace E → ℝ)
    (hg : ∀ x j ω, 0 ≤ g x j ω) (x : α) (j : ℕ) :
    0 ≤ oc4_codingProb μ (σ : Fin n → E) g x j := by
  rw [oc4_codingProb_eq_mean μ hpos hμ1 σ g x j]
  unfold Lindeberg.mean
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hg x j ω) (hpos ω).le)



























theorem oc4_codingScaleSum_le_fourD {α : Type*} (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n → E) (g : α → ℕ → ConfigSpace E → ℝ) (hg : ∀ x j ω, 0 ≤ g x j ω)
    (Λ : Finset α) (hne : Λ.Nonempty) (ru rv : ℕ) (hru : ru ≤ n) (hrv : rv ≤ n)
    (u v : α) (hu : u ∈ Λ) (hv : v ∈ Λ) (qu qv : ℕ → ℝ)
    (hcompu : ∀ k, qu k ≤ oc4_codingProb μ σ g u ((k : ℤ) - (ru : ℤ)).natAbs)
    (hcompv : ∀ k, qv k ≤ oc4_codingProb μ σ g v ((k : ℤ) - (rv : ℤ)).natAbs) :
    ∑ k ∈ Finset.Icc 1 n, (qu k + qv k)
      ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), oc4_codingProb μ σ g x j) :=
  revealment_family_sum_le Λ hne (fun x j => oc4_codingProb μ σ g x j)
    (fun x j => oc4_codingProb_nonneg μ σ g hg x j) n ru rv hru hrv u v hu hv qu qv hcompu hcompv
























theorem oc4_box_crossing_scale_sum_codingFrame {α : Type*} (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n → E) (g : α → ℕ → ConfigSpace E → ℝ) (hg : ∀ x j ω, 0 ≤ g x j ω)
    (Λ : Finset α) (hne : Λ.Nonempty) (ru rv : ℕ) (hru : ru ≤ n) (hrv : rv ≤ n)
    (u v : α) (hu : u ∈ Λ) (hv : v ∈ Λ) (qu qv : ℕ → ℝ)
    (hcompu : ∀ k, qu k
      ≤ ∫ uu, g u ((k : ℤ) - (ru : ℤ)).natAbs (codeMap μ σ uu) ∂(Vcube n))
    (hcompv : ∀ k, qv k
      ≤ ∫ uu, g v ((k : ℤ) - (rv : ℤ)).natAbs (codeMap μ σ uu) ∂(Vcube n)) :
    ∑ k ∈ Finset.Icc 1 n, (qu k + qv k)
      ≤ 4 * Λ.sup' hne
          (fun x => ∑ j ∈ Finset.range (n + 1),
            ∫ uu, g x j (codeMap μ σ uu) ∂(Vcube n)) :=
  oc4_codingScaleSum_le_fourD μ σ g hg Λ hne ru rv hru hrv u v hu hv qu qv hcompu hcompv











theorem oc4_box_crossing_scale_sum_mean {α : Type*} (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E)
    (g : α → ℕ → ConfigSpace E → ℝ) (hg : ∀ x j ω, 0 ≤ g x j ω)
    (Λ : Finset α) (hne : Λ.Nonempty) (ru rv : ℕ) (hru : ru ≤ n) (hrv : rv ≤ n)
    (u v : α) (hu : u ∈ Λ) (hv : v ∈ Λ) (qu qv : ℕ → ℝ)
    (hcompu : ∀ k, qu k ≤ Lindeberg.mean μ (g u ((k : ℤ) - (ru : ℤ)).natAbs))
    (hcompv : ∀ k, qv k ≤ Lindeberg.mean μ (g v ((k : ℤ) - (rv : ℤ)).natAbs)) :
    ∑ k ∈ Finset.Icc 1 n, (qu k + qv k)
      ≤ 4 * Λ.sup' hne
          (fun x => ∑ j ∈ Finset.range (n + 1), Lindeberg.mean μ (g x j)) := by
  refine revealment_family_sum_le Λ hne (fun x j => Lindeberg.mean μ (g x j))
    (fun x j => ?_) n ru rv hru hrv u v hu hv qu qv hcompu hcompv
  unfold Lindeberg.mean
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hg x j ω) (hpos ω).le)















theorem oc4_eq_revealment_family_sum_le {α : Type*} (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n → E) (g : α → ℕ → ConfigSpace E → ℝ) (hg : ∀ x j ω, 0 ≤ g x j ω)
    (Λ : Finset α) (hne : Λ.Nonempty) (ru rv : ℕ) (hru : ru ≤ n) (hrv : rv ≤ n)
    (u v : α) (hu : u ∈ Λ) (hv : v ∈ Λ) (qu qv : ℕ → ℝ)
    (hcompu : ∀ k, qu k ≤ oc4_codingProb μ σ g u ((k : ℤ) - (ru : ℤ)).natAbs)
    (hcompv : ∀ k, qv k ≤ oc4_codingProb μ σ g v ((k : ℤ) - (rv : ℤ)).natAbs) :
    oc4_codingScaleSum_le_fourD μ σ g hg Λ hne ru rv hru hrv u v hu hv qu qv hcompu hcompv
      = revealment_family_sum_le Λ hne (fun x j => oc4_codingProb μ σ g x j)
          (fun x j => oc4_codingProb_nonneg μ σ g hg x j) n ru rv hru hrv u v hu hv qu qv
          hcompu hcompv :=
  rfl









theorem oc4_scale_sum_nonvacuous {α : Type*} (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n → E) (Λ : Finset α) (hne : Λ.Nonempty) (ru rv : ℕ) (hru : ru ≤ n) (hrv : rv ≤ n)
    (u v : α) (hu : u ∈ Λ) (hv : v ∈ Λ) :
    ∑ k ∈ Finset.Icc 1 n, ((fun _ => (0 : ℝ)) k + (fun _ => (0 : ℝ)) k)
      ≤ 4 * Λ.sup' hne
          (fun x => ∑ j ∈ Finset.range (n + 1),
            oc4_codingProb μ σ (fun _ _ _ => (0 : ℝ)) x j) := by
  refine oc4_codingScaleSum_le_fourD μ σ (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => le_refl 0)
    Λ hne ru rv hru hrv u v hu hv (fun _ => 0) (fun _ => 0) (fun k => ?_) (fun k => ?_)
  · exact oc4_codingProb_nonneg μ σ (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => le_refl 0) u _
  · exact oc4_codingProb_nonneg μ σ (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => le_refl 0) v _




theorem oc4_scale_sum_empty_scales {α : Type*} (μ : ConfigSpace E → ℝ)
    (σ : Fin 0 → E) (g : α → ℕ → ConfigSpace E → ℝ) (hg : ∀ x j ω, 0 ≤ g x j ω)
    (Λ : Finset α) (hne : Λ.Nonempty) (u v : α) (hu : u ∈ Λ) (hv : v ∈ Λ)
    (qu qv : ℕ → ℝ)
    (hcompu : ∀ k, qu k ≤ oc4_codingProb μ σ g u ((k : ℤ) - (0 : ℤ)).natAbs)
    (hcompv : ∀ k, qv k ≤ oc4_codingProb μ σ g v ((k : ℤ) - (0 : ℤ)).natAbs) :
    ∑ k ∈ Finset.Icc 1 0, (qu k + qv k)
      ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (0 + 1), oc4_codingProb μ σ g x j) :=
  oc4_codingScaleSum_le_fourD μ σ g hg Λ hne 0 0 (le_refl 0) (le_refl 0) u v hu hv qu qv
    hcompu hcompv








section FK

open StatMech.OSSS.MonotonicFK












theorem oc4_fk_box_crossing_scale_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {α : Type*} {n : ℕ} (σ : Fin n → Sym2 V)
    (g : α → ℕ → ConfigSpace (Sym2 V) → ℝ) (hg : ∀ x j ω, 0 ≤ g x j ω)
    (Λ : Finset α) (hne : Λ.Nonempty) (ru rv : ℕ) (hru : ru ≤ n) (hrv : rv ≤ n)
    (u v : α) (hu : u ∈ Λ) (hv : v ∈ Λ) (qu qv : ℕ → ℝ)
    (hcompu : ∀ k, qu k
      ≤ ∫ uu, g u ((k : ℤ) - (ru : ℤ)).natAbs (codeMap (fkMass G p q) σ uu) ∂(Vcube n))
    (hcompv : ∀ k, qv k
      ≤ ∫ uu, g v ((k : ℤ) - (rv : ℤ)).natAbs (codeMap (fkMass G p q) σ uu) ∂(Vcube n)) :
    ∑ k ∈ Finset.Icc 1 n, (qu k + qv k)
      ≤ 4 * Λ.sup' hne
          (fun x => ∑ j ∈ Finset.range (n + 1),
            ∫ uu, g x j (codeMap (fkMass G p q) σ uu) ∂(Vcube n)) :=
  oc4_box_crossing_scale_sum_codingFrame (fkMass G p q) σ g hg Λ hne ru rv hru hrv
    u v hu hv qu qv hcompu hcompv

end FK

end Walls
end StatMech
