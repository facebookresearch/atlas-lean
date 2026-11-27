/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompact

/-!
# Cardinality bounds for realized finite simplicial sets

In universe `u`, set `κ=Order.succ Cardinal.continuum`. This cardinal is regular. The real
standard simplices, the realizations of finite simplicial sets, and in particular realized
standard simplices, boundaries, and horns all have cardinality at most the continuum. The
index types `ℕ` and `Σ n : ℕ, Fin (n+2)` have lifted cardinality strictly below `κ`.
-/

@[expose] public section

open scoped Simplicial
open scoped Cardinal

universe u

/-- For every universe `u`, `realizedGeneratorCardinal : Cardinal.{u}` is `Order.succ
Cardinal.continuum`, the successor of the continuum cardinal in that universe. It bounds the
cardinalities and index families of realized boundary and horn generators. -/
noncomputable def realizedGeneratorCardinal : Cardinal.{u} :=
  Order.succ Cardinal.continuum

/-- The cardinal `realizedGeneratorCardinal.{u}=Order.succ Cardinal.continuum` is regular. The
continuum is infinite, so its successor satisfies `Cardinal.IsRegular`. -/
theorem isRegular_realizedGeneratorCardinal :
    Cardinal.IsRegular realizedGeneratorCardinal :=
  Cardinal.isRegular_succ Cardinal.aleph0_le_continuum

/-- For `k : ℕ`, the underlying set `Convexity.StdSimplex ℝ (Fin (k+1))` has cardinality at most
`Cardinal.continuum`. Its inclusion into the finite real-coordinate function space gives this
bound. -/
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

/-- For `T : SSet.{u}` with `T.Finite`,
`#(SSet.toTop.obj T) ≤ Cardinal.continuum`.
The realization is covered by finitely many real standard simplices indexed by the nondegenerate simplices of `T`. -/
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

/-- For `n : ℕ` and universe `u`,
`#(SSet.toTop.{u}.obj (SSet.stdSimplex.obj ⦋n⦌)) ≤ Cardinal.continuum`.
The standard simplicial simplex is finite, so its realization satisfies the finite-realization cardinal bound. -/
theorem mk_realizedStdSimplex_le (n : ℕ) :
    #(↥(SSet.toTop.{u}.obj (SSet.stdSimplex.obj ⦋n⦌))) ≤ Cardinal.continuum :=
  mk_realizedFinite_le _

/-- For `n : ℕ` and universe `u`,
`#(SSet.toTop.{u}.obj (SSet.boundary.{u} n)) ≤ Cardinal.continuum`.
The boundary is a finite simplicial set. -/
theorem mk_realizedBoundary_le (n : ℕ) :
    #(↥(SSet.toTop.{u}.obj (SSet.boundary.{u} n))) ≤ Cardinal.continuum :=
  mk_realizedFinite_le _

/-- For `n : ℕ`, `i : Fin (n+1)`, and universe `u`,
`#(SSet.toTop.{u}.obj (SSet.horn.{u} n i)) ≤ Cardinal.continuum`.
The horn is a finite simplicial set. -/
theorem mk_realizedHorn_le (n : ℕ) (i : Fin (n + 1)) :
    #(↥(SSet.toTop.{u}.obj (SSet.horn.{u} n i))) ≤ Cardinal.continuum :=
  mk_realizedFinite_le _

/-- In universe `u`,
`Cardinal.lift #(ℕ) < realizedGeneratorCardinal.{u}`.
The natural-number index family for realized boundary generators is strictly smaller than the successor-continuum
cardinal. -/
theorem mk_nat_lt_realizedGeneratorCardinal :
    Cardinal.lift #(ℕ) < realizedGeneratorCardinal := by
  change Cardinal.lift #(ℕ) < Order.succ Cardinal.continuum
  rw [Cardinal.mk_nat]
  refine lt_of_le_of_lt ?_ (Order.lt_succ _)
  rw [Cardinal.lift_aleph0]
  exact Cardinal.aleph0_le_continuum

/-- In universe `u`,
`Cardinal.lift #(Σ n : ℕ, Fin (n+2)) < realizedGeneratorCardinal.{u}`.
The index family of positive-dimensional realized horn generators is countable and lies strictly below the successor of
the continuum. -/
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
