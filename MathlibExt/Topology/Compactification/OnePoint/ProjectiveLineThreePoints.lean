/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Moving three points of the projective line to `0`, `1` and `∞`

For a field `K`, Mathlib identifies the projective line `ℙ¹(K)` with `OnePoint K` and lets
`GL (Fin 2) K` act on it by fractional linear transformations
`z ↦ (a z + b) / (c z + d)`, with `ad - bc ≠ 0` (`OnePoint.instGLAction`). This file shows
that any three distinct points of `ℙ¹(K)` can be moved to `0`, `1` and `∞` by such a
transformation, the step "after composing with an appropriate fractional linear transformation"
of Köck's proof of Belyi's theorem.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265,
proof of Lemma 3.6, p. 263: "If r ≤ 3, there is a fractional linear transformation q with
q(T) ⊆ {0, 1, ∞}".

## Main results

* `OnePoint.exists_smul_eq_infty`: every point of `ℙ¹(K)` can be moved to `∞`.
* `OnePoint.exists_smul_coe_eq_zero_one_infty`: two distinct finite points can be moved to `0`
  and `1` by a transformation fixing `∞`.
* `OnePoint.exists_smul_eq_zero_one_infty`: three distinct points can be moved to `0`, `1` and
  `∞`.
-/

@[expose] public section

open Matrix

namespace OnePoint

variable {K : Type*} [Field K] [DecidableEq K]

/-- Every point of the projective line `OnePoint K` over a field is moved to `∞` by some
element of `GL (Fin 2) K`: `∞` by the identity, and `c ∈ K` by `z ↦ 1 / (z - c)`. -/
theorem exists_smul_eq_infty (t : OnePoint K) : ∃ g : GL (Fin 2) K, g • t = ∞ := by
  induction t using OnePoint.rec with
  | infty => exact ⟨1, one_smul _ _⟩
  | coe c =>
    refine ⟨GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, -c] (by simp [det_fin_two]), ?_⟩
    rw [smul_some_eq_ite]
    simp [GeneralLinearGroup.mkOfDetNeZero]

/-- For distinct `a, b ∈ K`, the transformation `z ↦ (z - a) / (b - a)` in `GL (Fin 2) K` maps
`a`, `b` and `∞` of the projective line `OnePoint K` to `0`, `1` and `∞`. -/
theorem exists_smul_coe_eq_zero_one_infty {a b : K} (hab : a ≠ b) :
    ∃ g : GL (Fin 2) K, g • (a : OnePoint K) = (0 : K) ∧ g • (b : OnePoint K) = (1 : K) ∧
      g • (∞ : OnePoint K) = ∞ := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  refine ⟨GeneralLinearGroup.mkOfDetNeZero !![1, -a; 0, b - a]
    (by simp [det_fin_two, hba]), ?_, ?_, ?_⟩
  · rw [smul_some_eq_ite]
    simp [GeneralLinearGroup.mkOfDetNeZero, hba]
  · rw [smul_some_eq_ite]
    simp [GeneralLinearGroup.mkOfDetNeZero, hba, ← sub_eq_add_neg]
  · rw [smul_infty_eq_ite]
    simp [GeneralLinearGroup.mkOfDetNeZero]

/-- **Moving three points of the projective line to `0`, `1` and `∞`.** Let `K` be a field and
`t₁`, `t₂`, `t₃` three distinct points of the projective line `ℙ¹(K) = OnePoint K`. Then some
`g ∈ GL (Fin 2) K`, acting by the fractional linear transformation
`z ↦ (g₀₀ z + g₀₁) / (g₁₀ z + g₁₁)`, maps `t₁`, `t₂` and `t₃` to `0`, `1` and `∞`.

B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, proof of
Lemma 3.6, p. 263 ("If r ≤ 3, there is a fractional linear transformation q with
q(T) ⊆ {0, 1, ∞}"); A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi
curves*, Algebra Number Theory 8 (2014), 89–140, proof of Theorem 4.5.2 (arXiv:1403.6404v1,
p. 29: "We may and do assume that π : Y → P¹ is unramified over P¹ − {0, 1, ∞}"). -/
theorem exists_smul_eq_zero_one_infty {t₁ t₂ t₃ : OnePoint K} (h₁₂ : t₁ ≠ t₂) (h₁₃ : t₁ ≠ t₃)
    (h₂₃ : t₂ ≠ t₃) :
    ∃ g : GL (Fin 2) K, g • t₁ = (0 : K) ∧ g • t₂ = (1 : K) ∧ g • t₃ = ∞ := by
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq_infty t₃
  have h₁ : g₀ • t₁ ≠ ∞ := hg₀ ▸ (MulAction.injective g₀).ne h₁₃
  have h₂ : g₀ • t₂ ≠ ∞ := hg₀ ▸ (MulAction.injective g₀).ne h₂₃
  obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.mp h₁
  obtain ⟨b, hb⟩ := OnePoint.ne_infty_iff_exists.mp h₂
  have hab : a ≠ b := by
    rintro rfl
    exact h₁₂ ((MulAction.injective g₀) (ha.symm.trans hb))
  obtain ⟨g₁, h0, h1, hinf⟩ := exists_smul_coe_eq_zero_one_infty hab
  refine ⟨g₁ * g₀, ?_, ?_, ?_⟩
  · rw [mul_smul, ← ha, h0]
  · rw [mul_smul, ← hb, h1]
  · rw [mul_smul, hg₀, hinf]

end OnePoint
