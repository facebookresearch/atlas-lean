/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompact

/-!
# Cardinal bound for realized TopCat generators

This file is part of the KQ3 layer. It fixes one regular cardinal,
`realizedGeneratorCardinal = succ 𝔠`, and bounds real standard simplices,
realized standard simplices, realized finite simplicial sets, realized
boundaries, and realized horns by `𝔠`. The index types `ℕ` and
`Σ n : ℕ, Fin (n + 2)` mirror `TopCat.realizedBoundaryInclusions` and
`TopCat.realizedHornInclusions`; only the index types themselves are
referenced, so no import of the generator module is needed. No
presentability, `IsSmall`, small-object-argument, cofibration,
weak-equivalence, or model-category claim is made here.
-/

@[expose] public section

open scoped Simplicial
open scoped Cardinal

universe u

/-- Regular cardinal bound for realized TopCat generators. -/
noncomputable def realizedGeneratorCardinal : Cardinal.{u} :=
  Order.succ Cardinal.continuum

/-- The generator bound is regular. -/
theorem isRegular_realizedGeneratorCardinal :
    Cardinal.IsRegular realizedGeneratorCardinal :=
  Cardinal.isRegular_succ Cardinal.aleph0_le_continuum

/-- Real standard simplices are bounded by the continuum. -/
private theorem mk_stdSimplex_set_le (k : ℕ) :
    #(Convexity.StdSimplex ℝ (Fin (k + 1))) ≤ Cardinal.continuum := by
  calc #(Convexity.StdSimplex ℝ (Fin (k + 1)))
        ≤ #(Fin (k + 1) → ℝ) :=
          Cardinal.mk_le_of_injective
            (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
              (Fin (k + 1))).injective
      _ = #ℝ ^ #(Fin (k + 1)) := (Cardinal.power_def ℝ (Fin (k + 1))).symm
      _ = Cardinal.continuum ^ ((k + 1 : ℕ) : Cardinal) := by
          rw [Cardinal.mk_real, Cardinal.mk_fin]
      _ = Cardinal.continuum ^ (k + 1) := by rw [Cardinal.power_natCast]
      _ ≤ Cardinal.continuum :=
          Cardinal.power_nat_le Cardinal.aleph0_le_continuum

/-- Realizations of finite simplicial sets are bounded by the continuum. -/
theorem mk_realizedFinite_le (T : SSet.{u}) [T.Finite] :
    #(↥(SSet.toTop.obj T)) ≤ Cardinal.continuum := by
  have hsurj : Function.Surjective (SSet.sigmaToTop (T := T)) :=
    SSet.surjective_sigmaToTop T
  calc #(↥(SSet.toTop.obj T))
        ≤ #(Σ s : T.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :=
          Cardinal.mk_le_of_surjective hsurj
      _ = Cardinal.sum
          (fun s : T.N => #(Convexity.StdSimplex ℝ (Fin (s.dim + 1)))) :=
          Cardinal.mk_sigma _
      _ ≤ Cardinal.sum (fun _ : T.N => Cardinal.continuum) :=
          Cardinal.sum_le_sum _ _ (fun s => mk_stdSimplex_set_le _)
      _ ≤ Cardinal.continuum := by
          rw [Cardinal.sum_const, Cardinal.lift_uzero, Cardinal.lift_continuum]
          calc #(T.N) * Cardinal.continuum
              ≤ Cardinal.aleph0 * Cardinal.continuum :=
                mul_le_mul' Cardinal.mk_le_aleph0 le_rfl
            _ = Cardinal.continuum := Cardinal.aleph0_mul_continuum

/-- Realized standard simplices are bounded by the continuum. -/
theorem mk_realizedStdSimplex_le (n : ℕ) :
    #(↥(SSet.toTop.{u}.obj (SSet.stdSimplex.obj ⦋n⦌))) ≤ Cardinal.continuum :=
  mk_realizedFinite_le _

/-- Realized boundaries are bounded by the continuum. -/
theorem mk_realizedBoundary_le (n : ℕ) :
    #(↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n))) ≤ Cardinal.continuum :=
  mk_realizedFinite_le _

/-- Realized horns are bounded by the continuum. -/
theorem mk_realizedHorn_le (n : ℕ) (i : Fin (n + 1)) :
    #(↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i))) ≤ Cardinal.continuum :=
  mk_realizedFinite_le _

/-- The boundary-generator index type is strictly below the bound. -/
theorem mk_nat_lt_realizedGeneratorCardinal :
    Cardinal.lift #(ℕ) < realizedGeneratorCardinal := by
  change Cardinal.lift #(ℕ) < Order.succ Cardinal.continuum
  rw [Cardinal.mk_nat]
  refine lt_of_le_of_lt ?_ (Order.lt_succ _)
  rw [Cardinal.lift_aleph0]
  exact Cardinal.aleph0_le_continuum

/-- The horn-generator index type is strictly below the bound. -/
theorem mk_sigmaHornIndex_lt_realizedGeneratorCardinal :
    Cardinal.lift #(Σ n : ℕ, Fin (n + 2)) < realizedGeneratorCardinal := by
  change Cardinal.lift #(Σ n : ℕ, Fin (n + 2)) <
    Order.succ Cardinal.continuum
  have hcount : #(Σ n : ℕ, Fin (n + 2)) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0
  have h0 : #(Σ n : ℕ, Fin (n + 2)) ≤ Cardinal.continuum :=
    hcount.trans Cardinal.aleph0_le_continuum
  have hle : Cardinal.lift #(Σ n : ℕ, Fin (n + 2)) ≤ Cardinal.continuum :=
    calc Cardinal.lift #(Σ n : ℕ, Fin (n + 2))
        ≤ Cardinal.lift Cardinal.continuum := Cardinal.lift_le.mpr h0
      _ = Cardinal.continuum := Cardinal.lift_continuum
  exact lt_of_le_of_lt hle (Order.lt_succ _)
