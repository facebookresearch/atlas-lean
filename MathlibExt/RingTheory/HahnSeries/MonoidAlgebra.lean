/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
generalize the coefficient ring and exponent monoids, factor the finite Hahn embedding through
Mathlib's monoid-algebra equivalences, and add coefficient laws.
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.HahnSeries.Multiplication

/-! # Finite monoid algebras as Hahn series

A finitely supported additive monoid algebra embeds in Hahn series by interpreting every basis
element as a singleton series. For two exponent variables, swapping and currying the finite
algebra before applying this embedding makes the second coordinate the outer Hahn exponent.

Adapted from `eth/proof/rates/GeneralPieces/Series/Rings.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace HahnSeries

variable {Γ G H R : Type*}

section Finite

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommSemiring R]

/-- Embed a finite additive monoid algebra into Hahn series. -/
noncomputable def ofAddMonoidAlgebra :
    AddMonoidAlgebra R Γ →+* HahnSeries Γ R := by
  let F : Multiplicative Γ →* HahnSeries Γ R :=
    { toFun := fun g => single g.toAdd 1
      map_one' := rfl
      map_mul' := fun g h => by
        change single (g.toAdd + h.toAdd) 1 = single g.toAdd 1 * single h.toAdd 1
        rw [single_mul_single, one_mul] }
  exact (AddMonoidAlgebra.lift R (HahnSeries Γ R) Γ F).toRingHom

/-- The finite Hahn embedding preserves every coefficient. -/
@[simp] theorem coeff_ofAddMonoidAlgebra (f : AddMonoidAlgebra R Γ) (g : Γ) :
    (ofAddMonoidAlgebra f).coeff g = f.coeff g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simpa using congr($h₁ + $h₂)
  | single a r =>
      by_cases h : g = a
      · simp [ofAddMonoidAlgebra, AddMonoidAlgebra.lift_single, h]
      · simp [ofAddMonoidAlgebra, AddMonoidAlgebra.lift_single, h]

/-- The finite Hahn embedding is Mathlib's `ofFinsupp`, bundled as a ring homomorphism. -/
theorem ofAddMonoidAlgebra_apply (f : AddMonoidAlgebra R Γ) :
    ofAddMonoidAlgebra f = ofFinsupp f.coeff := by
  ext g
  simp

/-- The finite Hahn embedding is injective. -/
theorem ofAddMonoidAlgebra_injective :
    Function.Injective (ofAddMonoidAlgebra : AddMonoidAlgebra R Γ → HahnSeries Γ R) :=
  fun f₁ f₂ h => by
    ext g
    rw [← coeff_ofAddMonoidAlgebra f₁ g, ← coeff_ofAddMonoidAlgebra f₂ g, h]

end Finite

section Bivariate

variable [CommSemiring R]
  [AddCommMonoid G] [AddCommMonoid H] [PartialOrder H] [IsOrderedCancelAddMonoid H]

/-- Embed a bivariate finite monoid algebra into Hahn series, with the second coordinate outer. -/
noncomputable def ofBivariateAddMonoidAlgebra :
    AddMonoidAlgebra R (G × H) →+* HahnSeries H (AddMonoidAlgebra R G) :=
  (ofAddMonoidAlgebra (Γ := H) (R := AddMonoidAlgebra R G)).comp
    ((AddMonoidAlgebra.curryRingEquiv (R := R) (M := H) (N := G)).toRingHom.comp
      (AddMonoidAlgebra.mapDomainRingEquiv R
        (AddEquiv.prodComm (M := G) (N := H))).toRingHom)

/-- The two coefficient projections of the bivariate embedding recover the original coefficient. -/
@[simp] theorem coeff_coeff_ofBivariateAddMonoidAlgebra
    (f : AddMonoidAlgebra R (G × H)) (g : G) (h : H) :
    ((ofBivariateAddMonoidAlgebra f).coeff h).coeff g = f.coeff (g, h) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simpa using congr($h₁ + $h₂)
  | single p r =>
      obtain ⟨g', h'⟩ := p
      by_cases hg : g = g' <;> by_cases hh : h = h' <;>
        simp [ofBivariateAddMonoidAlgebra, hg, hh]

/-- The bivariate finite Hahn embedding is injective. -/
theorem ofBivariateAddMonoidAlgebra_injective :
    Function.Injective
      (ofBivariateAddMonoidAlgebra :
        AddMonoidAlgebra R (G × H) → HahnSeries H (AddMonoidAlgebra R G)) :=
  fun f₁ f₂ h => by
    ext ⟨g, h'⟩
    rw [← coeff_coeff_ofBivariateAddMonoidAlgebra f₁ g h',
      ← coeff_coeff_ofBivariateAddMonoidAlgebra f₂ g h', h]

end Bivariate

end HahnSeries
