/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FreeGroupEquationFiniteQuotientKourovka14Problem48

open MathlibExt.GroupTheory.FreeGroupEquationFiniteQuotientKourovka14Problem48Wanted

-- Recover one fixed equation and a possibly different solution for each finite quotient.
example : ∃ (α : Type) (n : ℕ) (w : Monoid.Coprod (FreeGroup α) (FreeGroup (Fin n))),
    (∀ x : Fin n → FreeGroup α, Monoid.Coprod.lift (MonoidHom.id _) (FreeGroup.lift x) w ≠ 1) ∧
    ∀ (N : Subgroup (FreeGroup α)) [N.Normal] [N.FiniteIndex],
      ∃ x : Fin n → FreeGroup α ⧸ N,
        Monoid.Coprod.lift (QuotientGroup.mk' N) (FreeGroup.lift x) w = 1 := by
  classical
  by_contra h
  apply unsolvableEquationUnsolvableInFiniteQuotient_refuted
  intro α n w hw
  by_contra noQuotient
  apply h
  refine ⟨α, n, w, hw, ?_⟩
  intro N hN hfin
  by_contra! hx
  exact noQuotient ⟨N, hN, hfin, hx⟩
