/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.Operators

@[expose] public noncomputable section

namespace CartierModuleOperatorsTest

open MvFormalGroup MvFormalGroup.CartierModule

universe u

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]

/-- Consumer with the original binders: in characteristic `p`, `F ∘ V` is multiplication by
`p`. -/
theorem exactSource {Φ : MvFormalGroup d R} [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    frobenius (verschiebung f) = (p : ℕ) • f :=
  frobenius_verschiebung_eq_nsmul f

/-- Verschiebung is injective. -/
example {Φ : MvFormalGroup d R} [Φ.IsComm] [CharP R p] :
    Function.Injective (verschiebung (p := p) (Φ := Φ)) :=
  verschiebung_injective

/-- Endomorphisms act through `map`. -/
example {Φ : MvFormalGroup d R} [Φ.IsComm] (φ : MvFormalGroup.End Φ) (f : CartierModule p Φ) :
    endAct φ f = map φ f :=
  endAct_apply φ f

end CartierModuleOperatorsTest
