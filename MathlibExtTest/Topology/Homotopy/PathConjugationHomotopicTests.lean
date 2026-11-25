/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Homotopy.PathConjugationHomotopic

@[expose] public section

/-!
# Path conjugation homotopy consumer tests

Focused downstream checks for the public path-conjugation homotopy API:
transport of `p.symm.trans (γ.trans p)` along `h : p.Homotopic q` and
collapse when `p` is homotopic to `Path.refl`. Uses only public declarations;
claims only `Path.Homotopic`, never path equality, group laws, K-space laws,
pointed functoriality, additivity, or `π₀`.
-/

set_option autoImplicit false

namespace MathlibExtTest.Topology.Homotopy.PathConjugationHomotopicTests

/-- Transport of conjugation along `h : p.Homotopic q`. -/
example {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    {p q : Path x₀ x₁} {γ : Path x₀ x₀}
    (h : p.Homotopic q) :
    (p.symm.trans (γ.trans p)).Homotopic (q.symm.trans (γ.trans q)) :=
  Path.Homotopic.conj_transport h

/-- Collapse of conjugation when `p` is homotopic to `Path.refl`. -/
example {X : Type*} [TopologicalSpace X] {x : X}
    {p γ : Path x x} (h : p.Homotopic (Path.refl x)) :
    (p.symm.trans (γ.trans p)).Homotopic γ :=
  Path.Homotopic.conj_null h

end MathlibExtTest.Topology.Homotopy.PathConjugationHomotopicTests

end
