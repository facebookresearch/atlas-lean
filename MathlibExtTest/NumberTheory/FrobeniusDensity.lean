/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FrobeniusDensity

@[expose] public section

open Filter Topology Asymptotics

/-- Exact-source consumer for the degree-one asymptotic statement. -/
theorem exactSource_degOneAsymptotic (L : Type*) [Field L] [NumberField L]
    [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L :=
  FrobeniusDensity.degOneAsymptotic L

/-- Exact-source consumer for the prime-sum logarithmic pole. -/
theorem exactSource_primeSum (K : Type*) [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1 : ℝ)) :=
  FrobeniusDensity.primeSum_toReal_add_log_isBigO K

/-- Exact-source consumer for the conjugacy-class centralizer count. -/
theorem exactSource_card {G : Type*} [Group G] (σ : G) :
    Nat.card {τ : G | IsConj σ τ} *
      Nat.card (Subgroup.centralizer ({σ} : Set G)) = Nat.card G := by
  simpa only [Nat.card, Cardinal.toNat_mul] using
    congrArg Cardinal.toNat (FrobeniusDensity.mk_setOf_isConj_mul_mk_centralizer σ)

/-- Boundary example: in the trivial group the count is `1 * 1 = 1`. -/
example : Cardinal.mk {τ : PUnit.{1} | IsConj PUnit.unit τ} *
    Cardinal.mk (Subgroup.centralizer ({PUnit.unit} : Set PUnit.{1})) =
    Cardinal.mk PUnit.{1} :=
  FrobeniusDensity.mk_setOf_isConj_mul_mk_centralizer (G := PUnit.{1}) PUnit.unit

/-- Infinite case: in an abelian group every conjugacy class is a singleton, so the identity
gives `#(centralizer {σ}) = #G` also for infinite `G`, where `Nat.card` would only say
`1 * 0 = 0`. -/
example {G : Type*} [CommGroup G] (σ : G) :
    Cardinal.mk (Subgroup.centralizer ({σ} : Set G)) = Cardinal.mk G := by
  have hclass : {τ : G | IsConj σ τ} = {σ} := by
    ext τ
    simp [isConj_iff_eq, eq_comm]
  have h := FrobeniusDensity.mk_setOf_isConj_mul_mk_centralizer σ
  rwa [hclass, Cardinal.mk_singleton, one_mul] at h
