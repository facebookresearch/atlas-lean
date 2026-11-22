/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_GradedCartierModuleData.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
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

public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Verschiebung
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Graded Cartier module data

A graded Cartier module datum over a ring `B` consists of a module `M` over
the Witt vectors of `B`, equipped with Frobenius, Verschiebung, and a
uniformizer operator `varpi`, together with a decomposition of `M` into two
complementary graded pieces. We also record homogeneous `V`-bases, `V`-adic
completeness, structure constants for `varpi`, and base change.
-/

@[expose] public section

universe u v

namespace CerednikDrinfeld

/-- The ring of Witt vectors over the field with `p ^ 2` elements. -/
abbrev Zp2 (p : ℕ) [Fact p.Prime] : Type :=
  WittVector p (GaloisField p 2)

/-- Graded Cartier module data: a Witt-vector module with Frobenius,
Verschiebung, and uniformizer operators and two complementary pieces. -/
structure GradedCartierModuleData (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (j : Zp2 p →+* B) : Type (max u (v + 1)) where
  /-- The underlying module. -/
  M : Type v
  [addCommGroup : AddCommGroup M]
  [module : Module (WittVector p B) M]
  /-- The Frobenius operator. -/
  frobenius : M →+ M
  /-- The Verschiebung operator. -/
  verschiebung : M →+ M
  /-- The uniformizer operator. -/
  varpi : M →ₗ[WittVector p B] M
  /-- The two graded pieces. -/
  piece : Fin 2 → Submodule (WittVector p B) M
  /-- Frobenius is semilinear for the Witt-vector Frobenius. -/
  frobenius_smul : ∀ (w : WittVector p B) (x : M),
    frobenius (w • x) = WittVector.frobenius w • frobenius x
  /-- Scalar multiplication commutes with Verschiebung up to Frobenius. -/
  smul_verschiebung : ∀ (w : WittVector p B) (x : M),
    w • verschiebung x = verschiebung (WittVector.frobenius w • x)
  /-- Verschiebung after Frobenius-scaled scalars is given by Verschiebung
  of the scalar. -/
  verschiebung_smul_frobenius : ∀ (w : WittVector p B) (x : M),
    verschiebung (w • frobenius x) = WittVector.verschiebung w • x
  /-- Frobenius after Verschiebung is multiplication by `p`. -/
  frobenius_verschiebung : ∀ x : M, frobenius (verschiebung x) = (p : ℕ) • x
  /-- The uniformizer commutes with Verschiebung. -/
  varpi_verschiebung : ∀ x : M, varpi (verschiebung x) = verschiebung (varpi x)
  /-- The uniformizer commutes with Frobenius. -/
  varpi_frobenius : ∀ x : M, varpi (frobenius x) = frobenius (varpi x)
  /-- The uniformizer squares to multiplication by `p`. -/
  varpi_varpi : ∀ x : M, varpi (varpi x) = (p : ℕ) • x
  /-- The two graded pieces are complementary. -/
  isCompl_piece : IsCompl (piece 0) (piece 1)
  /-- Verschiebung shifts the grading. -/
  verschiebung_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → verschiebung x ∈ piece (i + 1)
  /-- Frobenius shifts the grading. -/
  frobenius_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → frobenius x ∈ piece (i + 1)
  /-- The uniformizer shifts the grading. -/
  varpi_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → varpi x ∈ piece (i + 1)

namespace GradedCartierModuleData

attribute [instance] GradedCartierModuleData.addCommGroup
  GradedCartierModuleData.module

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {j : Zp2 p →+* B}

/-- The scalar action of `b : B` on `M` through the Teichmüller lift. -/
noncomputable def homothety (D : GradedCartierModuleData p j) (b : B) : D.M →+ D.M :=
  DistribSMul.toAddMonoidHom D.M (WittVector.teichmuller p b)

@[simp] theorem homothety_apply (D : GradedCartierModuleData p j) (b : B) (x : D.M) :
    D.homothety b x = WittVector.teichmuller p b • x :=
  rfl

/-- The graded piece reached from piece `i` after `m + 1` shifts. -/
def piIndex (m : ℕ) (i : Fin 2) : Fin 2 :=
  ⟨(m + i + 1) % 2, Nat.mod_lt _ two_pos⟩

/-- A homogeneous `V`-basis: homogeneous elements `γ i` in piece `i` such
that every element has a unique expansion in Teichmüller multiples of the
`γ i` plus a Verschiebung term. -/
def IsHomogeneousVBasis (D : GradedCartierModuleData p j) (γ : Fin 2 → D.M) :
    Prop :=
  (∀ i : Fin 2, γ i ∈ D.piece i) ∧
    ∀ x : D.M, ∃! cy : (Fin 2 → B) × D.M,
      x = (∑ i : Fin 2, WittVector.teichmuller p (cy.1 i) • γ i) +
        D.verschiebung cy.2

/-- `V`-adic completeness, stated through unique limits of Verschiebung
series. -/
def IsVAdicallyComplete (D : GradedCartierModuleData p j) : Prop :=
  ∀ x : ℕ → D.M, ∃! s : D.M, ∀ N : ℕ, ∃ t : D.M,
    s = (∑ m ∈ Finset.range N, (⇑D.verschiebung)^[m] (x m)) +
      (⇑D.verschiebung)^[N] t

/-- A special Cartier module: one with a homogeneous `V`-basis that is
`V`-adically complete. -/
def IsSpecialCartierModule (D : GradedCartierModuleData p j) : Prop :=
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ) ∧ D.IsVAdicallyComplete

/-- Structure constants for `varpi`: its values on the basis elements `γ i`
admit Verschiebung expansions with Teichmüller coefficients `a m i`. -/
def HasStructureConstants (D : GradedCartierModuleData p j) (γ : Fin 2 → D.M)
    (a : ℕ → Fin 2 → B) : Prop :=
  ∀ (i : Fin 2) (N : ℕ), ∃ h : D.M,
    D.varpi (γ i) =
      (∑ m : Fin N, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) +
        (⇑D.verschiebung)^[N] h

/-- Base change of graded Cartier module data along a ring homomorphism,
witnessed by an additive map `f` compatible with all structure. -/
def IsBaseChangeAlong {B' : Type u} [CommRing B'] (φ : B →+* B')
    (D : GradedCartierModuleData p j) (D' : GradedCartierModuleData p (φ.comp j))
    (f : D.M →+ D'.M) : Prop :=
  (∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x) ∧
  (∀ x, f (D.frobenius x) = D'.frobenius (f x)) ∧
  (∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) ∧
  (∀ x, f (D.varpi x) = D'.varpi (f x)) ∧
  (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) ∧
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ ∧
    D'.IsHomogeneousVBasis (fun i => f (γ i)))

/-- The uniformizer is Witt-linear, hence commutes with scalar
multiplication. -/
theorem varpi_smul (D : GradedCartierModuleData p j) (w : WittVector p B)
    (x : D.M) :
    D.varpi (w • x) = w • D.varpi x :=
  map_smul _ _ _

/-- Verschiebung after Frobenius is scalar multiplication by the
Verschiebung of `1`. -/
theorem verschiebung_frobenius (D : GradedCartierModuleData p j) (x : D.M) :
    D.verschiebung (D.frobenius x) =
      WittVector.verschiebung (1 : WittVector p B) • x := by
  rw [← D.verschiebung_smul_frobenius 1 x, one_smul]

/-- Multiplication by `p` agrees with Frobenius after Verschiebung. -/
theorem natCast_smul_eq_frobenius_verschiebung (D : GradedCartierModuleData p j)
    (x : D.M) :
    (p : ℕ) • x = D.frobenius (D.verschiebung x) :=
  (D.frobenius_verschiebung x).symm

/-- Structure constants at order zero: the expansion is vacuous. -/
theorem hasStructureConstants_order_zero (D : GradedCartierModuleData p j)
    (γ : Fin 2 → D.M) (a : ℕ → Fin 2 → B) (i : Fin 2) :
    ∃ h : D.M, D.varpi (γ i) =
      (∑ m : Fin 0, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) +
        (⇑D.verschiebung)^[0] h :=
  ⟨D.varpi (γ i), by simp⟩

/-- Verschiebung is injective on a graded Cartier module with a homogeneous
`V`-basis. -/
theorem IsHomogeneousVBasis.verschiebung_injective
    {D : GradedCartierModuleData p j} {γ : Fin 2 → D.M}
    (h : D.IsHomogeneousVBasis γ) : Function.Injective D.verschiebung := by
  intro y y' hyy
  have key := h.2 (D.verschiebung y)
  obtain ⟨cy, hcy, huniq⟩ := key
  have h1 : ((fun _ => (0 : B)), y) = cy :=
    huniq ((fun _ => (0 : B)), y) (by simp)
  have h2 : ((fun _ => (0 : B)), y') = cy :=
    huniq ((fun _ => (0 : B)), y') (by simp [hyy])
  have h3 := h1.trans h2.symm
  simpa using congrArg Prod.snd h3

end GradedCartierModuleData

end CerednikDrinfeld
