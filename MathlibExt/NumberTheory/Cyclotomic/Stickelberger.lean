/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Stickelberger_Basic.lean` and
`Definitions/Def_ClassGroup_ModP.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
public import Mathlib.RingTheory.ClassGroup
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

open scoped NumberField nonZeroDivisors

namespace Stickelberger


def exponentSet (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun c => 0 < c ∧ 2 * c < p

@[simp] lemma mem_exponentSet {p c : ℕ} :
    c ∈ exponentSet p ↔ 0 < c ∧ 2 * c < p := by
  simp only [exponentSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

def eigenvalueScalar (p : ℕ) : ℕ := ∑ c ∈ exponentSet p, c

noncomputable def expUnit (p : ℕ) (c : ℕ) : (ZMod p)ˣ :=
  if h : Nat.Coprime c p then ZMod.unitOfCoprime c h else 1

variable {p : ℕ} {A : Type*} [AddCommGroup A] [Module (ZMod p) A]

noncomputable def stickelbergerEnd (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) :
    Module.End (ZMod p) A :=
  ∑ c ∈ exponentSet p, ρ (expUnit p c)⁻¹

def StickelbergerAnnihilates (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) : Prop :=
  ∀ a : A, stickelbergerEnd ρ a = 0

def IsOmegaEigenvector (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) (i : ℕ) (a : A) : Prop :=
  ∀ d : (ZMod p)ˣ, ρ d a = ((d : ZMod p) ^ i) • a


/-- The Stickelberger endomorphism annihilates every element exactly when
its defining sum acts as zero on the module. -/
theorem stickelbergerAnnihilates_iff {A : Type*} [AddCommGroup A]
    [Module (ZMod p) A] (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) :
    StickelbergerAnnihilates ρ ↔ ∀ a : A, stickelbergerEnd ρ a = 0 :=
  Iff.rfl

/-- A zero vector is an omega eigenvector for every exponent. -/
theorem isOmegaEigenvector_zero {A : Type*} [AddCommGroup A]
    [Module (ZMod p) A] (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) (i : ℕ) :
    IsOmegaEigenvector ρ i (0 : A) := by
  intro d
  simp

end Stickelberger

namespace JacobiSumStickelberger


section ModP

variable (p : ℕ) (M : Type*) [AddCommGroup M]

def nsmulRange : AddSubgroup M where
  carrier := Set.range fun x : M => p • x
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, smul_add p x y⟩
  zero_mem' := ⟨0, smul_zero p⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by simp⟩

@[simp] lemma mem_nsmulRange {x : M} : x ∈ nsmulRange p M ↔ ∃ y, p • y = x := Iff.rfl

lemma nsmul_mem_nsmulRange (x : M) : p • x ∈ nsmulRange p M := ⟨x, rfl⟩

abbrev ModP : Type _ := M ⧸ nsmulRange p M

instance instModuleZModModP [NeZero p] : Module (ZMod p) (ModP p M) :=
  QuotientAddGroup.zmodModule (nsmul_mem_nsmulRange p M)

def ModP.proj : M →+ ModP p M := QuotientAddGroup.mk' (nsmulRange p M)

@[simp] lemma ModP.proj_apply (x : M) : ModP.proj p M x = QuotientAddGroup.mk x := rfl

theorem ModP.proj_surjective : Function.Surjective (ModP.proj p M) :=
  QuotientAddGroup.mk'_surjective _

theorem ModP.proj_eq_zero_iff {x : M} : ModP.proj p M x = 0 ↔ ∃ y, p • y = x :=
  (QuotientAddGroup.eq_zero_iff x).trans (mem_nsmulRange p M)

variable {M} in

lemma nsmulRange_le_comap (f : M →+ M) : nsmulRange p M ≤ (nsmulRange p M).comap f := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (map_nsmul f p x).symm⟩

variable {M} in

def ModP.mapHom (f : M →+ M) : ModP p M →+ ModP p M :=
  QuotientAddGroup.map (nsmulRange p M) (nsmulRange p M) f (nsmulRange_le_comap p f)

variable {M} in
@[simp] lemma ModP.mapHom_proj (f : M →+ M) (x : M) :
    ModP.mapHom p f (ModP.proj p M x) = ModP.proj p M (f x) := rfl

variable {M} in

noncomputable def ModP.mapEnd [NeZero p] (f : M →+ M) : Module.End (ZMod p) (ModP p M) :=
  (ModP.mapHom p f).toZModLinearMap p

variable {M} in
@[simp] lemma ModP.mapEnd_proj [NeZero p] (f : M →+ M) (x : M) :
    ModP.mapEnd p f (ModP.proj p M x) = ModP.proj p M (f x) := rfl

end ModP

section ClassGroupCarrier

variable (p : ℕ) [NeZero p]
variable (R : Type*) [CommRing R] [IsDomain R]

abbrev ClGalModule : Type _ := ModP p (Additive (ClassGroup R))

noncomputable def clProj : Additive (ClassGroup R) →+ ClGalModule p R :=
  ModP.proj p (Additive (ClassGroup R))

omit [NeZero p] in
theorem clProj_surjective : Function.Surjective (clProj p R) :=
  ModP.proj_surjective p (Additive (ClassGroup R))

variable {R}

noncomputable def clEnd (g : R ≃+* R) : Module.End (ZMod p) (ClGalModule p R) :=
  ModP.mapEnd p (MonoidHom.toAdditive (ClassGroup.mulEquiv g).toMonoidHom)

@[simp] lemma clEnd_clProj (g : R ≃+* R) (C : ClassGroup R) :
    clEnd p g (clProj p R (Additive.ofMul C)) =
      clProj p R (Additive.ofMul (ClassGroup.mulEquiv g C)) := rfl

end ClassGroupCarrier


end JacobiSumStickelberger
