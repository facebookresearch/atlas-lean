/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.CriticalIndexChart

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

/-- Non-vacuity: zero is invariant in every degree of the standard module. -/
example {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B) (i : ℕ) :
    (0 : CartierModule p (SpecialFormalODModule.standard j).F) ∈
      CritChart.invariants (SpecialFormalODModule.standard j).toFormalODModule j i :=
  zero_mem _

end CriticalIndexChartTest
