/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/RepresentationTheory/BrauerCharacterInCyclotomic.lean` (leanprover/lean-eval),
at commit 38361be884302c7edce1908c4aef8296eb2cb27e, for the statement and docstring of
`brauer_character_in_cyclotomic`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License");
you may not use these portions except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Modification notice: ATLAS placed the statement in its current namespace and
deferred its proof in the former wanted module. This module supplies the proof.
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RepresentationTheory.Character
import Mathlib.Analysis.Complex.Polynomial.Basic
import MathlibExt.RepresentationTheory.CharacterRootsOfUnity

/-!
# Character values of a finite group lie in a cyclotomic field

For a group of exponent `n`, each eigenvalue of a representation operator is an `n`-th root
of unity. Any complex embedding of the cyclotomic field contains all these roots in its range,
so it also contains their sum with multiplicities, the character value.
-/

namespace MathlibExt.GroupTheory.BrauerCharacterInCyclotomicWanted.RepresentationTheory

set_option linter.unusedFintypeInType false in
/-- **Character values of a finite group lie in a cyclotomic field.** Let $G$ be a finite group of
exponent $n$, and let $\mathbb{Q}(\zeta_n)$ be the $n$-th cyclotomic field. There is a ring
homomorphism $\varphi \colon \mathbb{Q}(\zeta_n) \to \mathbb{C}$ such that for every
finite-dimensional complex representation $\rho$ of $G$ on a vector space $V$ and every $g \in G$,
the trace of $\rho(g)$ lies in the image of $\varphi$.

Source: R. Brauer, On the representation of a group of order g in the field of g-th roots of
unity, Amer. J. Math. 67 (1945). Via leanprover/lean-eval@38361be, problem
`brauer_character_in_cyclotomic`. -/
public theorem brauer_character_in_cyclotomic
    (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  let n := Monoid.exponent G
  let φ : CyclotomicField n ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ)).toRingHom
  obtain ⟨ζ, hζ⟩ := (CyclotomicField.isCyclotomicExtension n ℚ).exists_isPrimitiveRoot
    (Set.mem_singleton n) (NeZero.ne n)
  refine ⟨φ, ?_⟩
  intro V _ _ _ ρ g
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply φ.range.multiset_sum_mem
  intro μ hμ
  have heig := (Module.End.hasEigenvalue_iff_isRoot_charpoly (ρ g) μ).2
    (Polynomial.isRoot_of_mem_roots hμ)
  have hμn : μ ^ n = 1 := by
    obtain ⟨k, hk⟩ := Monoid.order_dvd_exponent g
    rw [show n = orderOf g * k from hk, pow_mul,
      CharacterTheory.hasEigenvalue_pow_orderOf_eq_one ρ g heig, one_pow]
  obtain ⟨i, -, rfl⟩ := (hζ.map_of_injective φ.injective).eq_pow_of_pow_eq_one hμn
  exact ⟨_, map_pow φ ζ i⟩

end MathlibExt.GroupTheory.BrauerCharacterInCyclotomicWanted.RepresentationTheory
