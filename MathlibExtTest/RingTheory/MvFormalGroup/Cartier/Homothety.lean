/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.Homothety

@[expose] public noncomputable section

namespace CartierModuleHomothetyTest

open MvFormalGroup MvFormalGroup.CartierModule

universe u

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]

/-- Consumer with the original binders: homotheties are multiplicative. -/
theorem exactSource {Φ : MvFormalGroup d R} [Φ.IsComm] (a b : R) (f : CartierModule p Φ) :
    homothety (a * b) f = homothety a (homothety b f) :=
  homothety_mul a b f

/-- The homothety by `1` is the identity. -/
example {Φ : MvFormalGroup d R} [Φ.IsComm] (f : CartierModule p Φ) : homothety 1 f = f :=
  homothety_one f

open MvFormalGroup.CartierModule.Examples in
/-- Homotheties do not commute with Verschiebung: on the Cartier module of the additive formal
group law in dimension one over a ring of characteristic `p`, the relation
`[a] (V f) = V ([a] f)` at `f = addLinear p 1` forces `a ^ p = a`. -/
theorem homothety_verschiebung_ne {S : Type u} [CommRing S] [CharP S p] {a : S}
    (ha : a ^ p ≠ a) :
    homothety a (verschiebung (addLinear p (fun _ : Fin 1 => (1 : S)))) ≠
      verschiebung (homothety a (addLinear p (fun _ : Fin 1 => (1 : S)))) := by
  intro h
  rw [homothety_verschiebung] at h
  have h' := congrArg (fun f => tangent f 0) (verschiebung_injective h)
  simp only [homothety_addLinear, tangent_addLinear, Pi.smul_apply, smul_eq_mul, mul_one] at h'
  exact ha h'

open MvFormalGroup.CartierModule.Examples in
/-- A concrete instance over `(ZMod 2)[X]` with `a = X`. -/
example : homothety (Polynomial.X : Polynomial (ZMod 2))
      (verschiebung (addLinear 2 (fun _ : Fin 1 => (1 : Polynomial (ZMod 2))))) ≠
    verschiebung (homothety Polynomial.X
      (addLinear 2 (fun _ : Fin 1 => (1 : Polynomial (ZMod 2))))) :=
  homothety_verschiebung_ne fun h => by
    have := congrArg Polynomial.natDegree h
    simp at this

end CartierModuleHomothetyTest
