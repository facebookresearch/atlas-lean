/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from
`Definitions/Def_CerednikDrinfeld_GradedCartierModuleData.lean`
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

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor

/-!
# Graded Cartier module data

`CerednikDrinfeld.GradedCartierModuleData p B j` packages an abstract Cartier module over
`WittVector p B`: Frobenius and Verschiebung with the Cartier relations, a linear operator `ϖ`
commuting with both and with `ϖ ∘ ϖ = p`, and a splitting into two submodules that Frobenius,
Verschiebung and `ϖ` shift by one. The predicates `IsHomogeneousVBasis`,
`IsVAdicallyComplete`, `IsSpecialCartierModule`, `HasStructureConstants` and
`IsBaseChangeAlong` describe the special Cartier modules of the Cerednik-Drinfeld
construction.

## References

* J.-F. Boutot and H. Carayol, *Uniformisation p-adique des courbes de Shimura : les théorèmes
  de Čerednik et de Drinfeld*, in *Courbes modulaires et courbes de Shimura*, Astérisque
  196–197 (1991), 45–158, for special formal `O_D`-modules and their Cartier modules.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld

/-- **Graded Cartier module data.** Let `p` be a prime, `B` a commutative ring and
`j : Zp2 p →+* B` a ring homomorphism, where `Zp2 p` is the ring of Witt vectors of
`GaloisField p 2`; write `σ` for the Frobenius of `WittVector p B`. The data consist of a
`WittVector p B`-module `M` with additive maps `F` and `V` satisfying `F (w • x) = σ w • F x`,
`w • V x = V (σ w • x)`, `V (w • F x) = WittVector.verschiebung w • x` and
`F (V x) = p • x`, a `WittVector p B`-linear map `ϖ` with `ϖ (V x) = V (ϖ x)`,
`ϖ (F x) = F (ϖ x)` and `ϖ (ϖ x) = p • x`, and complementary submodules `piece 0` and
`piece 1` such that `F`, `V` and `ϖ` each map one piece into the other. No field involves `j`;
it appears in `IsBaseChangeAlong`, where data over `B'` carry `φ.comp j`. The intended pieces are
the `j`-graded pieces of the Cartier module of a formal `O_D`-module, as in
`FormalODModule.toGradedCartierModuleData`. -/
structure GradedCartierModuleData (p : ℕ) [Fact p.Prime] (B : Type u) [CommRing B]
    (j : Zp2 p →+* B) : Type (max u (v + 1)) where

  M : Type v
  [addCommGroup : AddCommGroup M]
  [module : Module (WittVector p B) M]
  frobenius : M →+ M

  verschiebung : M →+ M

  varpi : M →ₗ[WittVector p B] M

  piece : Fin 2 → Submodule (WittVector p B) M

  frobenius_smul : ∀ (w : WittVector p B) (x : M),
    frobenius (w • x) = WittVector.frobenius w • frobenius x

  smul_verschiebung : ∀ (w : WittVector p B) (x : M),
    w • verschiebung x = verschiebung (WittVector.frobenius w • x)

  verschiebung_smul_frobenius : ∀ (w : WittVector p B) (x : M),
    verschiebung (w • frobenius x) = WittVector.verschiebung w • x

  frobenius_verschiebung : ∀ x : M, frobenius (verschiebung x) = (p : ℕ) • x

  varpi_verschiebung : ∀ x : M, varpi (verschiebung x) = verschiebung (varpi x)

  varpi_frobenius : ∀ x : M, varpi (frobenius x) = frobenius (varpi x)

  varpi_varpi : ∀ x : M, varpi (varpi x) = (p : ℕ) • x

  isCompl_piece : IsCompl (piece 0) (piece 1)

  verschiebung_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → verschiebung x ∈ piece (i + 1)

  frobenius_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → frobenius x ∈ piece (i + 1)

  varpi_mem : ∀ (i : Fin 2) (x : M), x ∈ piece i → varpi x ∈ piece (i + 1)

namespace GradedCartierModuleData

attribute [instance] GradedCartierModuleData.addCommGroup GradedCartierModuleData.module

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {j : Zp2 p →+* B}

def homothety (D : GradedCartierModuleData p B j) (b : B) : D.M →+ D.M :=
  DistribSMul.toAddMonoidHom D.M (WittVector.teichmuller p b)

@[simp] theorem homothety_apply (D : GradedCartierModuleData p B j) (b : B) (x : D.M) :
    D.homothety b x = WittVector.teichmuller p b • x := rfl

def piIndex (m : ℕ) (i : Fin 2) : Fin 2 := ⟨(m + i + 1) % 2, Nat.mod_lt _ two_pos⟩

/-- **Homogeneous `V`-basis.** For graded Cartier module data over `B` with module `M`,
Verschiebung `V` and pieces `piece 0` and `piece 1`, a pair `γ 0 ∈ piece 0`, `γ 1 ∈ piece 1` such
that every `x : M` can be written uniquely as `[c 0] • γ 0 + [c 1] • γ 1 + V y` with
`c : Fin 2 → B` and `y : M`, where `[b]` is the Teichmüller representative of `b`. -/
def IsHomogeneousVBasis (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) : Prop :=
  (∀ i : Fin 2, γ i ∈ D.piece i) ∧
    ∀ x : D.M, ∃! cy : (Fin 2 → B) × D.M,
      x = (∑ i : Fin 2, WittVector.teichmuller p (cy.1 i) • γ i) + D.verschiebung cy.2

/-- **`V`-adic completeness.** Graded Cartier module data with module `M` and Verschiebung `V`
are `V`-adically complete when every sequence `x : ℕ → M` has exactly one `V`-adic sum: there is
exactly one `s : M` such that, for every `N`, `s - ∑ m < N, V ^ m (x m)` lies in the image of
`V ^ N`. -/
def IsVAdicallyComplete (D : GradedCartierModuleData p B j) : Prop :=
  ∀ x : ℕ → D.M, ∃! s : D.M, ∀ N : ℕ, ∃ t : D.M,
    s = (∑ m ∈ Finset.range N, (⇑D.verschiebung)^[m] (x m)) + (⇑D.verschiebung)^[N] t

/-- **Special Cartier module data.** Graded Cartier module data that have a homogeneous
`V`-basis and are `V`-adically complete. -/
def IsSpecialCartierModule (D : GradedCartierModuleData p B j) : Prop :=
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ) ∧ D.IsVAdicallyComplete

/-- **Structure constants of `ϖ`.** For graded Cartier module data over `B` with module `M`,
Verschiebung `V` and operator `ϖ`, a family `γ : Fin 2 → M` and `a : ℕ → Fin 2 → B`, for every
`i : Fin 2` and every `N` there is `h : M` with
`ϖ (γ i) = ∑ m < N, V ^ m ([a m i] • γ (piIndex m i)) + V ^ N h`, where `piIndex m i` is
`m + i + 1` modulo `2` and `[b]` is the Teichmüller representative of `b`. -/
def HasStructureConstants (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M)
    (a : ℕ → Fin 2 → B) : Prop :=
  ∀ (i : Fin 2) (N : ℕ), ∃ h : D.M,
    D.varpi (γ i) =
      (∑ m : Fin N, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) + (⇑D.verschiebung)^[N] h

/-- **Base change of graded Cartier module data.** For a ring homomorphism `φ : B →+* B'` and
graded Cartier module data `D` over `B` (with `j`) and `D'` over `B'` (with `φ.comp j`), an
additive map `f : D.M →+ D'.M` is a base change along `φ` when
`f (w • x) = WittVector.map φ w • f x`, `f` commutes with `F`, `V` and `ϖ`, maps each piece of
`D` into the same piece of `D'`, and sends some homogeneous `V`-basis of `D` to a homogeneous
`V`-basis of `D'`. -/
def IsBaseChangeAlong {B' : Type*} [CommRing B'] (φ : B →+* B')
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' (φ.comp j))
    (f : D.M →+ D'.M) : Prop :=
  (∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x) ∧
  (∀ x, f (D.frobenius x) = D'.frobenius (f x)) ∧
  (∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) ∧
  (∀ x, f (D.varpi x) = D'.varpi (f x)) ∧
  (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) ∧
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ ∧ D'.IsHomogeneousVBasis (fun i => f (γ i)))

theorem varpi_smul (D : GradedCartierModuleData p B j) (w : WittVector p B) (x : D.M) :
    D.varpi (w • x) = w • D.varpi x := map_smul _ _ _

theorem verschiebung_frobenius (D : GradedCartierModuleData p B j) (x : D.M) :
    D.verschiebung (D.frobenius x) = WittVector.verschiebung (1 : WittVector p B) • x := by
  rw [← D.verschiebung_smul_frobenius 1 x, one_smul]

theorem natCast_smul_eq_frobenius_verschiebung (D : GradedCartierModuleData p B j) (x : D.M) :
    (p : ℕ) • x = D.frobenius (D.verschiebung x) := (D.frobenius_verschiebung x).symm

theorem hasStructureConstants_order_zero (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M)
    (a : ℕ → Fin 2 → B) (i : Fin 2) :
    ∃ h : D.M, D.varpi (γ i) =
      (∑ m : Fin 0, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) + (⇑D.verschiebung)^[0] h :=
  ⟨D.varpi (γ i), by simp⟩

theorem IsHomogeneousVBasis.verschiebung_injective {D : GradedCartierModuleData p B j}
    {γ : Fin 2 → D.M} (h : D.IsHomogeneousVBasis γ) : Function.Injective D.verschiebung := by
  intro y y' hyy
  have key := h.2 (D.verschiebung y)
  obtain ⟨cy, hcy, huniq⟩ := key
  have h1 : ((fun _ => (0 : B)), y) = cy := huniq ((fun _ => (0 : B)), y) (by simp)
  have h2 : ((fun _ => (0 : B)), y') = cy := huniq ((fun _ => (0 : B)), y') (by simp [hyy])
  have := h1.trans h2.symm
  simpa using congrArg Prod.snd this

end GradedCartierModuleData

end CerednikDrinfeld

end
