/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_GradedCartierModuleData.lean`
(every declaration except `teichmullerAct` and `teichmullerAct_of_mem`, which
are additions here).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Verschiebung
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Projection
public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.SpecialFormalFunctor

/-!
# Graded Cartier module data

A graded Cartier module datum over a ring `B` consists of a module `M` over
the Witt vectors of `B`, equipped with Frobenius, Verschiebung, and a
uniformizer operator `varpi`, together with a decomposition of `M` into two
complementary graded pieces. We also record homogeneous `V`-bases, `V`-adic
completeness, structure constants for `varpi`, maps along a ring map that
preserve this structure and a homogeneous `V`-basis (`IsBaseChangeAlong`, which
is weaker than base change), and the action of the Teichmüller representatives
of `Zp2 p` that the pieces and the coefficient map `j` determine.

## References

* J.-F. Boutot and H. Carayol, *Uniformisation p-adique des courbes de Shimura :
  les théorèmes de Čerednik et de Drinfeld*, Astérisque 196–197 (1991), 45–158.
  Chapter II: §2.2 defines graded Cartier modules and special ones, §2.3
  homogeneous `V`-bases and the structure constants of `Π` (here `varpi`), and
  §2.4 base change, the completed extension of scalars `E(B') ⊗ M`.
-/

@[expose] public section

universe u v

namespace CerednikDrinfeld

/-- **Graded Cartier module data.** For a prime `p`, a commutative ring `B` and
a ring map `j : Zp2 p →+* B`: a module `M` over `WittVector p B` with additive
maps `F` (`frobenius`) and `V` (`verschiebung`), a `WittVector p B`-linear map
`ϖ` (`varpi`) and submodules `piece 0` and `piece 1`, such that, writing `σ`
for the Frobenius of `WittVector p B`, `F (w • x) = σ w • F x`,
`w • V x = V (σ w • x)`, `V (w • F x) = WittVector.verschiebung w • x`,
`F (V x) = p • x`, `ϖ (V x) = V (ϖ x)`, `ϖ (F x) = F (ϖ x)` and
`ϖ (ϖ x) = p • x`; the two pieces are complementary, and `F`, `V` and `ϖ` each
map `piece i` into `piece (i + 1)`. No field involves `j`: with the pieces it
determines how the Teichmüller representatives of `Zp2 p` act
(`teichmullerAct`), and a map along a ring map `φ` (`IsBaseChangeAlong`) goes
to data with coefficient map `φ.comp j`. -/
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

/-- **Homothety.** The action of `b : B` on `M` through its Teichmüller
representative: `x ↦ [b] • x`. -/
noncomputable def homothety (D : GradedCartierModuleData p j) (b : B) : D.M →+ D.M :=
  DistribSMul.toAddMonoidHom D.M (WittVector.teichmuller p b)

@[simp] theorem homothety_apply (D : GradedCartierModuleData p j) (b : B) (x : D.M) :
    D.homothety b x = WittVector.teichmuller p b • x :=
  rfl

/-- **Teichmüller action.** The action of the Teichmüller representative `[c]`
of `Zp2 p`, for `c` in the field with `p ^ 2` elements, that the pieces and `j`
determine: the homothety by `j [c]` on piece `0` and by `j [c] ^ p` on piece
`1`, extended additively along the decomposition of `M` into the two pieces. -/
noncomputable def teichmullerAct (D : GradedCartierModuleData p j) (c : GaloisField p 2) :
    D.M →+ D.M :=
  (D.homothety (j (WittVector.teichmuller p c))).comp
      ((D.piece 0).projection (D.piece 1) D.isCompl_piece).toAddMonoidHom +
    (D.homothety (j (WittVector.teichmuller p c) ^ p)).comp
      ((D.piece 1).projection (D.piece 0) D.isCompl_piece.symm).toAddMonoidHom

theorem teichmullerAct_of_mem (D : GradedCartierModuleData p j) (c : GaloisField p 2)
    {i : Fin 2} {x : D.M} (hx : x ∈ D.piece i) :
    D.teichmullerAct c x = D.homothety (j (WittVector.teichmuller p c) ^ p ^ (i : ℕ)) x := by
  fin_cases i
  · simp only [teichmullerAct, AddMonoidHom.add_apply, AddMonoidHom.coe_comp,
      LinearMap.toAddMonoidHom_coe, Function.comp_apply,
      Submodule.projection_apply_of_mem_left D.isCompl_piece hx,
      Submodule.projection_apply_of_mem_right D.isCompl_piece.symm hx, map_zero, add_zero]
    simp
  · simp only [teichmullerAct, AddMonoidHom.add_apply, AddMonoidHom.coe_comp,
      LinearMap.toAddMonoidHom_coe, Function.comp_apply,
      Submodule.projection_apply_of_mem_right D.isCompl_piece hx,
      Submodule.projection_apply_of_mem_left D.isCompl_piece.symm hx, map_zero, zero_add]
    simp

/-- **Index after `m + 1` shifts.** The index `(m + i + 1) mod 2` of the graded
piece reached from piece `i` after `m + 1` shifts. -/
def piIndex (m : ℕ) (i : Fin 2) : Fin 2 :=
  ⟨(m + i + 1) % 2, Nat.mod_lt _ two_pos⟩

/-- **Homogeneous `V`-basis.** Elements `γ 0 ∈ piece 0` and `γ 1 ∈ piece 1`
such that every `x : M` is `[b 0] • γ 0 + [b 1] • γ 1 + V y` for exactly one
pair of `b : Fin 2 → B` and `y : M`, where `[b i]` is the Teichmüller
representative of `b i`. -/
def IsHomogeneousVBasis (D : GradedCartierModuleData p j) (γ : Fin 2 → D.M) :
    Prop :=
  (∀ i : Fin 2, γ i ∈ D.piece i) ∧
    ∀ x : D.M, ∃! cy : (Fin 2 → B) × D.M,
      x = (∑ i : Fin 2, WittVector.teichmuller p (cy.1 i) • γ i) +
        D.verschiebung cy.2

/-- **`V`-adic completeness.** Every series `∑ V^m (x m)` has exactly one sum:
for each `x : ℕ → M` there is a unique `s : M` such that, for every `N`,
`s - ∑_{m < N} V^m (x m)` lies in the image of `V^N`. -/
def IsVAdicallyComplete (D : GradedCartierModuleData p j) : Prop :=
  ∀ x : ℕ → D.M, ∃! s : D.M, ∀ N : ℕ, ∃ t : D.M,
    s = (∑ m ∈ Finset.range N, (⇑D.verschiebung)^[m] (x m)) +
      (⇑D.verschiebung)^[N] t

/-- **Special Cartier module.** Graded Cartier module data that has a
homogeneous `V`-basis and is `V`-adically complete. -/
def IsSpecialCartierModule (D : GradedCartierModuleData p j) : Prop :=
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ) ∧ D.IsVAdicallyComplete

/-- **Structure constants of `ϖ`.** For `γ : Fin 2 → M` and
`a : ℕ → Fin 2 → B`: for every `i` and every `N`,
`ϖ (γ i) = ∑_{m < N} V^m ([a m i] • γ (piIndex m i)) + V^N h` for some `h`,
so `ϖ (γ i)` expands in powers of `V` with Teichmüller coefficients `[a m i]`.
The index `piIndex m i` of the `m`-th term alternates between `0` and `1`. The
family `γ` need not be homogeneous; when it is (`γ k ∈ piece k`), the vector
`γ (piIndex m i)` of the `m`-th term lies in piece `piIndex m i`. -/
def HasStructureConstants (D : GradedCartierModuleData p j) (γ : Fin 2 → D.M)
    (a : ℕ → Fin 2 → B) : Prop :=
  ∀ (i : Fin 2) (N : ℕ), ∃ h : D.M,
    D.varpi (γ i) =
      (∑ m : Fin N, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) +
        (⇑D.verschiebung)^[N] h

/-- **Basis-preserving semilinear map along a ring map.** For `φ : B →+* B'`,
data `D` over `B` with coefficient map `j` and `D'` over `B'` with coefficient
map `φ.comp j`: an additive map `f : D.M →+ D'.M` with
`f (w • x) = WittVector.map φ w • f x` that commutes with `F`, `V` and `ϖ`, maps
`piece i` of `D` into `piece i` of `D'`, and sends some homogeneous `V`-basis of
`D` to a homogeneous `V`-basis of `D'`. This is weaker than base change along
`φ`, the completed extension of scalars, which along the identity is an
isomorphism: if `D` has a homogeneous `V`-basis and `T` is a nonzero datum on
which `V` is bijective, the inclusion of `D` into `D × T` satisfies it along the
identity but is not surjective. As the target is indexed by `φ.comp j`, `f`
intertwines the Teichmüller actions (`IsBaseChangeAlong.map_teichmullerAct`). -/
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

/-- **The uniformizer commutes with scalars.** `ϖ (w • x) = w • ϖ x`, as `ϖ`
is `WittVector p B`-linear. -/
theorem varpi_smul (D : GradedCartierModuleData p j) (w : WittVector p B)
    (x : D.M) :
    D.varpi (w • x) = w • D.varpi x :=
  map_smul _ _ _

/-- **Verschiebung after Frobenius.** `V (F x) = V 1 • x`, where `V 1` is the
Verschiebung of `1` in `WittVector p B`. -/
theorem verschiebung_frobenius (D : GradedCartierModuleData p j) (x : D.M) :
    D.verschiebung (D.frobenius x) =
      WittVector.verschiebung (1 : WittVector p B) • x := by
  rw [← D.verschiebung_smul_frobenius 1 x, one_smul]

/-- **Multiplication by `p`.** `p • x = F (V x)`. -/
theorem natCast_smul_eq_frobenius_verschiebung (D : GradedCartierModuleData p j)
    (x : D.M) :
    (p : ℕ) • x = D.frobenius (D.verschiebung x) :=
  (D.frobenius_verschiebung x).symm

/-- **Structure constants at order zero.** The expansion of `ϖ (γ i)` to
order `0` holds with `h = ϖ (γ i)`, the sum being empty. -/
theorem hasStructureConstants_order_zero (D : GradedCartierModuleData p j)
    (γ : Fin 2 → D.M) (a : ℕ → Fin 2 → B) (i : Fin 2) :
    ∃ h : D.M, D.varpi (γ i) =
      (∑ m : Fin 0, (⇑D.verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) • γ (piIndex m i))) +
        (⇑D.verschiebung)^[0] h :=
  ⟨D.varpi (γ i), by simp⟩

/-- **A homogeneous `V`-basis makes `V` injective.** If `D` has a homogeneous
`V`-basis, then `V` is injective. -/
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
