/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Field
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Descent of orthogonal vectors along field extensions

An `F`-linear functional detecting one nonzero coordinate of the extension vector
sends it coordinatewise to a nonzero vector over `F` and preserves the dot-product equations.
-/

namespace MetaMathlibExt

/-- **Orthogonal vectors descend from field extensions.** Let $F$ be a field, let $G$ be a field
extension of $F$ (a field with an $F$-algebra structure), let $n \in \mathbb{N}$ and let
$S \subseteq F^n$. If some nonzero $t \in G^n$ satisfies $\sum_{i=1}^n s_i t_i = 0$ in $G$ for
every $s \in S$, then some nonzero $u \in F^n$ satisfies $\sum_{i=1}^n s_i u_i = 0$ for every
$s \in S$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Lemma 3 (`jis-2024-24.1.3-lem-3`). -/
public theorem exists_orthogonal_of_orthogonal_over_extension {F G : Type*} [Field F]
    [Field G] [Algebra F G] {n : ℕ} (S : Set (Fin n → F)) (t : Fin n → G) (ht : t ≠ 0)
    (horth : ∀ s ∈ S, ∑ i, algebraMap F G (s i) * t i = 0) :
    ∃ u : Fin n → F, u ≠ 0 ∧ ∀ s ∈ S, ∑ i, s i * u i = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, t j ≠ 0 := Function.ne_iff.mp ht
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero F hj
  refine ⟨fun i ↦ φ (t i), Function.ne_iff.mpr ⟨j, hφ⟩, ?_⟩
  intro s hs
  simpa only [← Algebra.smul_def, map_sum, map_smul, smul_eq_mul, map_zero] using
    congrArg φ (horth s hs)

end MetaMathlibExt
