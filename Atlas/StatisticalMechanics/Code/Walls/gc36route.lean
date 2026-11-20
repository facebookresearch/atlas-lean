/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Walls.gc35bridge
import Code.Walls.gc28ghsrigid
import Code.Walls.gc29hdom
import Code.Walls.gc9core
import Code.Walls.gc15core
import Code.Walls.ghc_urselleqgap
import Code.Walls.FaithfulnessAudit

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]












theorem gc36_resummation_lhs_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (g : V) (zero x : V) :
    0 ≤ ∑' m₀ : ↥G.edgeFinset → ℕ,
        (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S
              ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = ({zero, x} : Finset V)
          then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) {zero, x} else 0) := by
  refine tsum_nonneg (fun m₀ => ?_)
  by_cases h : notConnComp G (Sharpness.ofEdgeFun G m₀) g = S
      ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = ({zero, x} : Finset V)
  · rw [if_pos h]; exact hnw_mass_nonneg G β J hβ hJ _ _
  · rw [if_neg h]




theorem gc36_resummation_sourceless_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (g : V) :
    0 ≤ ∑' m₀ : ↥G.edgeFinset → ℕ,
        (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S
              ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = (∅ : Finset V)
          then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) ∅ else 0) := by
  refine tsum_nonneg (fun m₀ => ?_)
  by_cases h : notConnComp G (Sharpness.ofEdgeFun G m₀) g = S
      ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = (∅ : Finset V)
  · rw [if_pos h]; exact hnw_mass_nonneg G β J hβ hJ _ _
  · rw [if_neg h]





theorem gc36_resummation_rhs_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (g : V) (zero x : V) :
    0 ≤ expectationJ G β (couplingIn J S) {zero, x}
      * (∑' m₀ : ↥G.edgeFinset → ℕ,
          (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S
                ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = (∅ : Finset V)
            then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) ∅ else 0)) := by
  refine mul_nonneg ?_ (gc36_resummation_sourceless_nonneg G β J hβ hJ S g)
  exact (gc34_resummation_factor_mem_Icc G β J hβ hJ S {zero, x}).1









theorem gc36_resummation_preserves_sign (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (g : V) (hg : g ∉ S) (zero x : V) (h0 : zero ∈ S) (hx : x ∈ S)
    (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0) :
    (0 ≤ ∑' m₀ : ↥G.edgeFinset → ℕ,
        (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S
              ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = ({zero, x} : Finset V)
          then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) {zero, x} else 0))
    ∧ (∑' m₀ : ↥G.edgeFinset → ℕ,
        (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S
              ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = ({zero, x} : Finset V)
          then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) {zero, x} else 0))
      = expectationJ G β (couplingIn J S) {zero, x}
        * (∑' m₀ : ↥G.edgeFinset → ℕ,
            (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S
                  ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = (∅ : Finset V)
              then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) ∅ else 0)) :=
  ⟨gc36_resummation_lhs_nonneg G β J hβ hJ S g zero x,
    gc35_native_resummation G β J S g hg zero x h0 hx hZ⟩

















theorem gc36_delta_native_eq_Z0sq_cov3 (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc25_nativeAllConnMass G β h o x y
      = (gc15_Z0 G β h) ^ 2 * cov3sym G β h o s(x, y) :=
  gc28_delta_eq_Z0sq_cov3 G β h o x y hox hoy hxy













theorem gc36_ghs_route_forces_rigid (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc25_NativeResummation G β h o x y) :
    (gc15_Z0 G β h + 2) * cov3sym G β h o s(x, y)
      = gc15_Z0 G β h * ghsBoundSym G β h o s(x, y) :=
  gc28_nativeResummation_forces_rigid G β h o x y hox hoy hxy hres







theorem gc36_resummation_delivers_cov3_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    0 ≤ cov3sym G β h o s(x, y) :=
  gc28_cov3_nonneg G β h hβ hh o x y hox hoy hxy












theorem gc36_resummation_is_beta_not_h (β h : ℝ) (o x y : V) :
    cov3sym G β h o s(x, y) - eg_ursell3 G β h o x y = ghsBoundSym G β h o s(x, y) := by
  have := ghc_ursellEqGap G β h o x y
  linarith [this]

















theorem gc36_ghs_of_hdom (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m A o x y :=
  gc28_native_closure_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom






theorem gc36_native_ursell_decomp (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
    ∑ m ∈ M, hnw_gap G β J m A o x y
      = (∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A)
        - 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) :=
  gc28_native_ursell_decomp G β J M hnd A hm hox hoy hxy hcoh














theorem gc36_resummation_factor_mem_Icc (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (S : Finset V) (zero x : V) :
    0 ≤ expectationJ G β (couplingIn J S) {zero, x}
      ∧ expectationJ G β (couplingIn J S) {zero, x} ≤ 1 :=
  gc35_native_resummation_factor_mem_Icc G β J hβ hJ S zero x








theorem gc36_h0_beta_route_consistent (β : ℝ) (o x y : V) :
    eg_ursell3 G β 0 o x y = 0
      ∧ cov3sym G β 0 o s(x, y) = ghsBoundSym G β 0 o s(x, y) := by
  refine ⟨fa_ghs_ursell3_h0_eq_zero G β o x y, ?_⟩
  have hgap := gc36_resummation_is_beta_not_h G β 0 o x y
  have h0 := fa_ghs_ursell3_h0_eq_zero G β o x y
  rw [h0] at hgap; linarith [hgap]







theorem gc36_degenerate_h_direction (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x y : V) (hxy : x ≠ y) :
    eg_ursell3 G β h x x y ≤ 0 :=
  ghc_ursell_nonpos_degenerate G β h hβ hh x y hxy
















theorem gc36_status (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    
    (gc25_nativeAllConnMass G β h o x y = (gc15_Z0 G β h) ^ 2 * cov3sym G β h o s(x, y)
        ∧ 0 ≤ cov3sym G β h o s(x, y))
    
      ∧ cov3sym G β h o s(x, y) - eg_ursell3 G β h o x y = ghsBoundSym G β h o s(x, y) := by
  refine ⟨⟨gc36_delta_native_eq_Z0sq_cov3 G β h o x y hox hoy hxy,
      gc36_resummation_delivers_cov3_nonneg G β h hβ hh o x y hox hoy hxy⟩,
    gc36_resummation_is_beta_not_h G β h o x y⟩
















theorem gc36_betaSign_does_not_give_hSign :
    ∃ c b : ℝ, 0 ≤ c ∧ 0 ≤ b ∧ 0 < c - b := by
  exact ⟨1, 0, by norm_num, by norm_num, by norm_num⟩








theorem gc36_rigid_relation_refuted :
    ∃ Z c b : ℝ, 0 < Z ∧ 0 ≤ c ∧ 0 ≤ b ∧ (Z + 2) * c ≠ Z * b := by
  refine ⟨1, 1, 0, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

end StatMech.Walls
