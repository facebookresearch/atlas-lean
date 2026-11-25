/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.WittAction

@[expose] public noncomputable section

namespace CartierModuleWittActionTest

open MvFormalGroup MvFormalGroup.CartierModule

universe u

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]

/-- The Cartier module is a module over the Witt vectors. -/
example (Φ : MvFormalGroup d R) [Φ.IsComm] : Module (WittVector p R) (CartierModule p Φ) :=
  inferInstance

/-- Consumer with the original binders: Teichmüller representatives act by homotheties. -/
theorem exactSource {Φ : MvFormalGroup d R} [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    WittVector.teichmuller p a • f = homothety a f :=
  teichmuller_smul a f

end CartierModuleWittActionTest
