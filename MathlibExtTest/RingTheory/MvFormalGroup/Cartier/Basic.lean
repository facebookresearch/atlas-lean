/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.Basic

@[expose] public noncomputable section

namespace CartierModuleBasicTest

open MvFormalGroup MvPowerSeries

universe u

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]

/-- The Cartier module of a commutative formal group law is an additive group. -/
example (Φ : MvFormalGroup d R) [Φ.IsComm] : AddCommGroup (CartierModule p Φ) := inferInstance

/-- Consumer with the original binders: addition is the formal group law applied to the two
families. -/
theorem exactSource (Φ : MvFormalGroup d R) [Φ.IsComm] (f g : CartierModule p Φ) :
    (f + g).toPowerSeries =
      fun j => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j) :=
  CartierModule.toPowerSeries_add f g

/-- The zero element is the zero family. -/
example (Φ : MvFormalGroup d R) :
    (0 : CartierModule p Φ).toPowerSeries = fun _ => 0 :=
  CartierModule.toPowerSeries_zero

/-- The Witt addition family is a valid substitution, over a ring in a higher universe. -/
example (S : Type (u + 1)) [CommRing S] : HasSubst (WittLaw.addFam p S) :=
  WittLaw.hasSubst_addFam p S

end CartierModuleBasicTest
