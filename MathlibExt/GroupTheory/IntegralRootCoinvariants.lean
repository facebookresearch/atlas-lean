/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Integral coroot and inertia coinvariants

The lattice quotient uses the native coroot span and native representation
coinvariant relations over Z. It retains torsion; passing through a real
root apartment would lose the connected-fixer information in Kottwitz.
All maps below are ordinary quotient/universal maps. An actual group-scheme
root datum and its geometric inertia action are separate input dictionaries,
not inferred from a free lattice or from these algebraic quotients.

References: Kottwitz, *Isocrystals with additional structureII*, Section7;
Zhu, arXiv:1407.8519v3, Proposition1.21 and Section1.4.
Native Mathlib coroot-span and coinvariant constructions are reused.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.GroupTheory.IntegralRootCoinvariants

open _root_.Submodule _root_.Set

section General

variable {R Γ N : Type} [CommRing R] [Group Γ] [AddCommGroup N] [Module R N]

/-- Both relations remain integral, with no rationalization or real tensor. -/
def relations (C : Submodule R N) (ρ : Representation R Γ N) : Submodule R N :=
  C ⊔ Representation.Coinvariants.ker ρ

/-- The actual integral quotient by coroot and inertia differences. -/
def Quotient (C : Submodule R N) (ρ : Representation R Γ N) : Type :=
  N ⧸ relations C ρ

instance quotientAddCommGroup (C : Submodule R N) (ρ : Representation R Γ N) :
    AddCommGroup (Quotient C ρ) := inferInstanceAs (AddCommGroup (N ⧸ relations C ρ))

instance quotientModule (C : Submodule R N) (ρ : Representation R Γ N) :
    Module R (Quotient C ρ) := inferInstanceAs (Module R (N ⧸ relations C ρ))

/-- Its native quotient map. -/
def quotientMap (C : Submodule R N) (ρ : Representation R Γ N) :
    N →ₗ[R] Quotient C ρ := (relations C ρ).mkQ

theorem quotientMap_coroot (C : Submodule R N) (ρ : Representation R Γ N)
    {x : N} (hx : x ∈ C) : quotientMap C ρ x = 0 := by
  have hc : C ≤ relations C ρ := le_sup_left
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hc hx)

theorem quotientMap_action (C : Submodule R N) (ρ : Representation R Γ N)
    (g : Γ) (x : N) : quotientMap C ρ (ρ g x) = quotientMap C ρ x := by
  change Submodule.Quotient.mk (ρ g x) = (Submodule.Quotient.mk x : N ⧸ relations C ρ)
  apply (Submodule.Quotient.eq _).mpr
  have hc : Representation.Coinvariants.ker ρ ≤ relations C ρ := le_sup_right
  exact hc (Representation.Coinvariants.sub_mem_ker g x)

/-- The actual universal map of the integral quotient. -/
def descend {W : Type} [AddCommGroup W] [Module R W]
    (C : Submodule R N) (ρ : Representation R Γ N) (f : N →ₗ[R] W)
    (coroot : C ≤ LinearMap.ker f) (inertia : ∀ g x, f (ρ g x) = f x) :
    Quotient C ρ →ₗ[R] W :=
  (relations C ρ).liftQ f (sup_le coroot (by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨g, y⟩, rfl⟩
    change f (ρ g y - y) = 0
    rw [map_sub, inertia, sub_self]))

@[simp] theorem descend_quotientMap {W : Type} [AddCommGroup W] [Module R W]
    (C : Submodule R N) (ρ : Representation R Γ N) (f : N →ₗ[R] W)
    (coroot : C ≤ LinearMap.ker f) (inertia : ∀ g x, f (ρ g x) = f x) (x : N) :
    descend C ρ f coroot inertia (quotientMap C ρ x) = f x := by
  change (relations C ρ).liftQ f _ ((relations C ρ).mkQ x) = f x
  exact Submodule.liftQ_apply _ _ _

end General

variable {Γ N : Type} [Group Γ] [AddCommGroup N] [Module ℤ N]
variable {ι M : Type} [AddCommGroup M] [Module ℤ M]

/-- The coweight/coroot quotient for an actual native root pairing. -/
abbrev RootCoinvariants (P : RootPairing ι ℤ M N) (ρ : Representation ℤ Γ N) :=
  Quotient (P.corootSpan ℤ) ρ

end MathlibExt.GroupTheory.IntegralRootCoinvariants
