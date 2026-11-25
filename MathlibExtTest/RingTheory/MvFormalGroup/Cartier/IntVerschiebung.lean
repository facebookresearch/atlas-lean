/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.IntVerschiebung

@[expose] public noncomputable section

namespace CartierModuleIntVerschiebungTest

open MvFormalGroup MvFormalGroup.CartierModule

universe u

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]

/-- Consumer with the original binders: over any base, `F ∘ V` is multiplication by `p`. -/
theorem exactSource {Φ : MvFormalGroup d R} [Φ.IsComm] (f : CartierModule p Φ) :
    frobenius (verschiebungInt f) = (p : ℕ) • f :=
  frobenius_verschiebungInt f

/-- In characteristic `p` the two Verschiebungs agree. -/
example {Φ : MvFormalGroup d R} [Φ.IsComm] [CharP R p] :
    (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ) = verschiebung :=
  verschiebungInt_eq_verschiebung

end CartierModuleIntVerschiebungTest
