/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.CriticalIndexChart
public import MathlibExtTest.AlgebraicGeometry.CerednikDrinfeld.Cartier.GradedPiece

@[expose] public noncomputable section

namespace CriticalIndexChartTest

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

universe u

variable {p : ℕ} [Fact p.Prime]

/-- Consumer with the original binders for the invariants. -/
theorem exactSource {B : Type u} [CommRing B] [CharP B p] (X : FormalODModule p B)
    (j : Zp2 p →+* B) (i : ℕ) (m : CartierModule p X.F) :
    m ∈ CritChart.invariants X j i ↔
      m ∈ X.gradedPiece j i ∧ endAct X.varpiEnd m = verschiebung m :=
  CritChart.mem_invariants_iff X j i m

/-- The truncation at level `0` is trivial. -/
example {B : Type u} [CommRing B] [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (i : ℕ) : Subsingleton (CritChart.truncInvariants X j i 0) :=
  CritChart.truncInvariants_zero_subsingleton X j i

/-- In the standard special formal `O_D`-module over a domain, if `j [c] ^ p ≠ j [c]` for some
`c`, every invariant in degree `0` has zero tangent vector: the graded piece kills the second
coordinate and `ϖ = V` kills the first. -/
theorem tangent_eq_zero_of_mem_invariants_zero {B : Type} [CommRing B] [IsDomain B] [CharP B p]
    (j : Zp2 p →+* B) {c : GaloisField p 2}
    (hc : j (WittVector.teichmuller p c) ^ p ≠ j (WittVector.teichmuller p c))
    {m : CartierModule p (SpecialFormalODModule.standard j).F}
    (hm : m ∈ CritChart.invariants (SpecialFormalODModule.standard j).toFormalODModule j 0) :
    tangent m = 0 := by
  have hl : tangent (endAct (SpecialFormalODModule.standard j).varpiEnd m) 1 = tangent m 0 :=
    (congrFun (tangent_map (SpecialFormalODModule.standard j).varpiEnd m) 1).trans (by
      rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      change MvPowerSeries.coeff (Finsupp.single 0 1)
          (MvPowerSeries.map j (Standard.varpiSeries p 1)) * tangent m 0 +
        MvPowerSeries.coeff (Finsupp.single 1 1)
          (MvPowerSeries.map j (Standard.varpiSeries p 1)) * tangent m 1 = tangent m 0
      rw [Standard.varpiSeries_one, MvPowerSeries.map_X]
      simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero])
  have hv := congrArg (fun g => tangent g 1) hm.2
  simp only [tangent_verschiebung, Pi.zero_apply] at hv
  rw [hl] at hv
  funext i
  fin_cases i
  · exact hv
  · exact CartierGradedPieceTest.tangent_one_eq_zero_of_mem_gradedPiece_zero j hc hm.1

end CriticalIndexChartTest
