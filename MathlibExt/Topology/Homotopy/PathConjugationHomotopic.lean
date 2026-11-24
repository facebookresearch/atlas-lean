/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Homotopy.Path

/-!
# Endpoint-fixed path conjugation homotopies

Transport of loop conjugation along an endpoint-fixed path homotopy, with a
null-conjugation corollary. G4 K-space maps send `γ` to
`p.symm.trans (γ.trans p)`; these lemmas move that conjugate across `p ~ q`.

Nonclaims: no equality of paths, group structure, K-space law, pointed
functoriality, additivity, or `π₀` theorem.
-/

@[expose] public section

namespace Path.Homotopic

variable {X : Type*} [TopologicalSpace X]

/-- Transport conjugation along `h : p.Homotopic q`:
`p.symm.trans (γ.trans p)` is endpoint-fixed homotopic to
`q.symm.trans (γ.trans q)`.

Nonclaim: no equality of paths or group law, only the stated homotopy. -/
theorem conj_transport {x₀ x₁ : X} {p q : Path x₀ x₁} {γ : Path x₀ x₀}
    (h : p.Homotopic q) :
    (p.symm.trans (γ.trans p)).Homotopic (q.symm.trans (γ.trans q)) :=
  h.symm₂.hcomp ((refl γ).hcomp h)

/-- Null-conjugation corollary: when `p ~ refl`, the conjugate of `γ` by `p`
is homotopic to `γ` itself.

Nonclaim: no equality of paths, group structure, or `π₀` statement. -/
theorem conj_null {x : X} {p γ : Path x x}
    (h : p.Homotopic (Path.refl x)) :
    (p.symm.trans (γ.trans p)).Homotopic γ := by
  have hconj := conj_transport (γ := γ) h
  have h1 : (γ.trans (Path.refl x)).Homotopic γ := trans_refl γ
  have h2 : ((Path.refl x).trans (γ.trans (Path.refl x))).Homotopic
      ((Path.refl x).trans γ) :=
    (refl _).hcomp h1
  have h3 : ((Path.refl x).trans γ).Homotopic γ := refl_trans γ
  have hstep : ((Path.refl x).symm.trans (γ.trans (Path.refl x))).Homotopic γ := by
    rw [Path.refl_symm]
    exact h2.trans h3
  exact hconj.trans hstep

end Path.Homotopic
