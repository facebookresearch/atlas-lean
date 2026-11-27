/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_AdicThickening.lean`
and
`P2M/Sol/S_AlgebraicGeometry_eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_
of_isClosedImmersion_proj.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Adic thickenings of a scheme over an affine base

For a scheme `X` over `Spec R` and an ideal `I` of `R`, the `n`-th adic thickening of `X` is
the base change of `X` to `Spec (R ⧸ I ^ (n + 1))`. It comes with a closed immersion into `X`
and transition morphisms from the `n`-th to the `(n + 1)`-st thickening.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)

/-- The closed immersion `Spec (R ⧸ I ^ (n + 1)) ⟶ Spec R`. -/
abbrev adicThickeningBase (n : ℕ) : Spec (.of (R ⧸ I ^ (n + 1))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))

/-- The `n`-th adic thickening of `X` over `Spec R` along `I`: the pullback of
`f : X ⟶ Spec R` along `Spec (R ⧸ I ^ (n + 1)) ⟶ Spec R`. -/
def adicThickening (n : ℕ) : Scheme.{u} := pullback f (adicThickeningBase I n)

/-- The inclusion of the `n`-th adic thickening into `X`. -/
def adicThickeningι (n : ℕ) : adicThickening f I n ⟶ X :=
  pullback.fst f (adicThickeningBase I n)

/-- The structure morphism of the `n`-th adic thickening to `Spec (R ⧸ I ^ (n + 1))`. -/
def adicThickeningToBase (n : ℕ) : adicThickening f I n ⟶ Spec (.of (R ⧸ I ^ (n + 1))) :=
  pullback.snd f (adicThickeningBase I n)

theorem adicThickening_def (n : ℕ) :
    adicThickening f I n = pullback f (adicThickeningBase I n) := rfl

theorem adicThickeningι_def (n : ℕ) :
    adicThickeningι f I n = pullback.fst f (adicThickeningBase I n) := rfl

theorem adicThickeningToBase_def (n : ℕ) :
    adicThickeningToBase f I n = pullback.snd f (adicThickeningBase I n) := rfl

theorem adicThickeningι_comp (n : ℕ) :
    adicThickeningι f I n ≫ f = adicThickeningToBase f I n ≫ adicThickeningBase I n :=
  pullback.condition

/-- The defining square of the `n`-th adic thickening is a pullback square. -/
theorem isPullback_adicThickening (n : ℕ) :
    IsPullback (adicThickeningι f I n) (adicThickeningToBase f I n) f
      (adicThickeningBase I n) :=
  IsPullback.of_hasPullback f (adicThickeningBase I n)

theorem adicThickeningBase_succ_comp (n : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) ≫
      adicThickeningBase I (n + 1) = adicThickeningBase I n := by
  rw [adicThickeningBase, adicThickeningBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]

/-- The transition morphism from the `n`-th to the `(n + 1)`-st adic thickening. -/
def adicThickeningTransition (n : ℕ) : adicThickening f I n ⟶ adicThickening f I (n + 1) :=
  pullback.lift (adicThickeningι f I n)
    (adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))))
    (by rw [adicThickeningι_comp, Category.assoc, adicThickeningBase_succ_comp])

@[simp] theorem adicThickeningTransition_ι (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningι f I (n + 1) = adicThickeningι f I n := by
  rw [adicThickeningTransition]; exact pullback.lift_fst _ _ _

theorem adicThickeningTransition_toBase (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningToBase f I (n + 1) =
      adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) := by
  rw [adicThickeningTransition]; exact pullback.lift_snd _ _ _

instance isClosedImmersion_adicThickeningι (n : ℕ) :
    IsClosedImmersion (adicThickeningι f I n) := by
  have : IsClosedImmersion (adicThickeningBase I n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact inferInstanceAs (IsClosedImmersion (pullback.fst _ _))

end AlgebraicGeometry

end
