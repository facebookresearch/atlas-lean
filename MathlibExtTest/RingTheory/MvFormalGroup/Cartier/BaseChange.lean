/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.BaseChange

@[expose] public noncomputable section

namespace CartierModuleBaseChangeTest

open MvFormalGroup MvFormalGroup.CartierModule

universe u v

variable {p : ℕ} [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- Consumer with the original binders: base change commutes with Frobenius. -/
theorem exactSource {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d S} [Φ.IsComm] [Ψ.IsComm]
    (f : R →+* S) (h : Φ.map f = Ψ) (m : CartierModule p Φ) :
    baseChangeEq f h (frobenius m) = frobenius (baseChangeEq f h m) :=
  baseChangeEq_frobenius f h m

/-- Base change along the identity is the identity. -/
example {Φ : MvFormalGroup d R} [Φ.IsComm] (h : Φ.map (RingHom.id R) = Φ)
    (m : CartierModule p Φ) : baseChangeEq (RingHom.id R) h m = m :=
  baseChangeEq_id h m

/-- Base change along an injective ring homomorphism is injective. -/
example {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d S} [Φ.IsComm] [Ψ.IsComm] (f : R →+* S)
    (h : Φ.map f = Ψ) (hf : Function.Injective f) :
    Function.Injective (baseChangeEq (p := p) f h) :=
  baseChangeEq_injective f h hf

end CartierModuleBaseChangeTest
