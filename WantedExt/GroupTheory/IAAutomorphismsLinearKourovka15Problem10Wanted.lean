/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linearity of the IA-automorphism group of a free group (Kourovka Notebook Problem 15.10)

Kourovka Notebook, Archive of Solved Problems, Problem 15.10 (Yu. I. Merzlyakov; V. G. Bardakov): is
the group of automorphisms of the free group `Fₙ` acting trivially on `Fₙ/[Fₙ, Fₙ]` linear for `n ≥
3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.IAAutomorphismsLinearKourovka15Problem10Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.10 (Yu. I.
Merzlyakov; V. G. Bardakov). UnsolvedMath record UM-00701098 (`KOU-15.10`), dataset
ulamai/UnsolvedMath v1.8.0.

Linear means a faithful representation in `GLₘ(K)` for some field `K` and some `m`; fields are taken
in `Type`, which suffices because `IA(Fₙ)` is finitely generated, so the entries of a faithful
representation generate a countable field. The target is stated for some `n ≥ 3`, so its refutation
covers every `n ≥ 3` (for `n = 2`, `IA(F₂) = Inn(F₂) ≅ F₂` is linear).
-/

/-- `IA(F_n)`: the automorphisms of the free group `F_n` that act trivially on its abelianization
`F_n / [F_n, F_n]`. -/
def iaAut (n : ℕ) : Subgroup (MulAut (FreeGroup (Fin n))) where
  carrier := {φ | ∀ x, Abelianization.of (φ x) = Abelianization.of x}
  one_mem' _ := rfl
  mul_mem' {φ ψ} hφ hψ x := (hφ (ψ x)).trans (hψ x)
  inv_mem' {φ} hφ x := by
    have h := hφ (φ⁻¹ x)
    simp only [MulAut.apply_inv_self] at h
    exact h.symm

/-- Kourovka 15.10 (Yu. I. Merzlyakov; V. G. Bardakov), for some `n ≥ 3`: `IA(F_n)` is linear,
i.e. has a faithful finite-dimensional representation over a field. -/
def iaAutLinear : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ ∃ (K : Type) (_ : Field K) (m : ℕ)
    (ρ : iaAut n →* Matrix.GeneralLinearGroup (Fin m) K), Function.Injective ρ

/--
Resolved false: the Kourovka Archive answers 15.10 No: `IA(Fₙ)` is not linear for `n ≥ 5` (Pettet)
and for every `n ≥ 3` (Bardakov and Mikhailov). Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 15.10 (Yu. I. Merzlyakov; V. G. Bardakov); resolution: V. G.
Bardakov and R. Mikhailov, Commun. Algebra 36 (2008), no. 4, 1489-1499 (n ≥ 3); A. Pettet,
Cohomology of some subgroups of the automorphism group of a free group, Ph.D. thesis, 2006 (n ≥ 5),
Kourovka Archive, Problem 15.10.
-/
public theorem_wanted iaAutLinear_refuted : ¬ iaAutLinear

end MathlibExt.GroupTheory.IAAutomorphismsLinearKourovka15Problem10Wanted
