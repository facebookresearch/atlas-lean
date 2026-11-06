/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

/-!
# Algebraic p-adic Pontryagin duals

This file defines the `ℤ_p`-linear dual `Hom(·, ℚ_p / ℤ_p)` and its
contragredient group action. No topology or continuity condition is imposed.
-/

namespace MetaMathlibExt

/-- **The quotient $\mathbb{Q}_p/\mathbb{Z}_p$.** For a prime $p$, $\mathbb{Q}_p/\mathbb{Z}_p$ is
the quotient of $\mathbb{Q}_p$, viewed as a $\mathbb{Z}_p$-module, by the image of
$\mathbb{Z}_p$ under the canonical inclusion $\mathbb{Z}_p \to \mathbb{Q}_p$. -/
noncomputable abbrev PadicQuotientInt (p : ℕ) [Fact p.Prime] :=
  ℚ_[p] ⧸ LinearMap.range (Algebra.linearMap ℤ_[p] ℚ_[p])

/-- **Algebraic $p$-adic Pontryagin dual.** For a prime $p$ and a $\mathbb{Z}_p$-module $A$, the
algebraic $p$-adic Pontryagin dual of $A$ is the $\mathbb{Z}_p$-module
$\operatorname{Hom}_{\mathbb{Z}_p}(A, \mathbb{Q}_p/\mathbb{Z}_p)$ of all $\mathbb{Z}_p$-linear maps
from $A$ to $\mathbb{Q}_p/\mathbb{Z}_p$; no topology or continuity condition is imposed. -/
noncomputable abbrev PadicPontryaginDual (p : ℕ) [Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Module ℤ_[p] A] :=
  A →ₗ[ℤ_[p]] PadicQuotientInt p

/-- **Extensionality for the $p$-adic Pontryagin dual.** Let $p$ be a prime and $A$ a
$\mathbb{Z}_p$-module. If two elements $\varphi, \psi$ of the algebraic $p$-adic Pontryagin dual
of $A$ satisfy $\varphi(a) = \psi(a)$ for every $a \in A$, then $\varphi = \psi$. -/
@[ext]
theorem PadicPontryaginDual_ext {p : ℕ} [Fact p.Prime]
    {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
    {φ ψ : PadicPontryaginDual p A} (h : ∀ a, φ a = ψ a) : φ = ψ :=
  LinearMap.ext fun a => h a

/-- **The quotient map $\mathbb{Q}_p \to \mathbb{Q}_p/\mathbb{Z}_p$.** For a prime $p$, this is
the canonical projection $\mathbb{Q}_p \to \mathbb{Q}_p/\mathbb{Z}_p$, $x \mapsto x + \mathbb{Z}_p$,
as a $\mathbb{Z}_p$-linear map. -/
noncomputable def padicQuotientMap (p : ℕ) [Fact p.Prime] :
    ℚ_[p] →ₗ[ℤ_[p]] PadicQuotientInt p :=
  (LinearMap.range (Algebra.linearMap ℤ_[p] ℚ_[p])).mkQ

/-- **The quotient map vanishes on $\mathbb{Z}_p$.** For a prime $p$ and every
$z \in \mathbb{Z}_p$, the quotient map $\mathbb{Q}_p \to \mathbb{Q}_p/\mathbb{Z}_p$ sends the
image of $z$ in $\mathbb{Q}_p$ to $0$. -/
theorem padicQuotientMap_algebraMap_eq_zero (p : ℕ) [Fact p.Prime] (z : ℤ_[p]) :
    padicQuotientMap p (algebraMap ℤ_[p] ℚ_[p] z) = 0 := by
  unfold padicQuotientMap
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨z, rfl⟩

/-- **The quotient map is the quotient projection.** For a prime $p$ and every
$x \in \mathbb{Q}_p$, the quotient map $\mathbb{Q}_p \to \mathbb{Q}_p/\mathbb{Z}_p$ sends $x$ to
its class $x + \mathbb{Z}_p$ in the quotient module. -/
theorem padicQuotientMap_mkQ_eq (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    padicQuotientMap p x = Submodule.Quotient.mk x := rfl

/-- **Contragredient action on the $p$-adic Pontryagin dual.** Let $p$ be a prime, $G$ a group
and $A$ a $\mathbb{Z}_p$-module on which $G$ acts by additive maps commuting with the
$\mathbb{Z}_p$-action. For $g \in G$ and $\varphi$ in the algebraic $p$-adic Pontryagin dual of
$A$, $g \cdot \varphi$ is the element $a \mapsto \varphi(g^{-1} a)$ of the dual. -/
noncomputable def contragredientSMul (p : ℕ) [Fact p.Prime] (G A : Type*) [Group G]
    [AddCommGroup A] [Module ℤ_[p] A] [DistribMulAction G A] [SMulCommClass G ℤ_[p] A]
    (g : G) (φ : PadicPontryaginDual p A) : PadicPontryaginDual p A where
  toFun a := φ (g⁻¹ • a)
  map_add' a b := by
    simp [smul_add, map_add]
  map_smul' r a := by
    change φ (g⁻¹ • (r • a)) = (RingHom.id ℤ_[p] r) • φ (g⁻¹ • a)
    rw [smul_comm g⁻¹ r a]
    simpa only [RingHom.id_apply] using φ.map_smul r (g⁻¹ • a)

/-- The contragredient distributive group action on the p-adic Pontryagin dual. -/
noncomputable instance instContragredientDistribMulAction (p : ℕ) [Fact p.Prime] (G A : Type*)
    [Group G] [AddCommGroup A] [Module ℤ_[p] A] [DistribMulAction G A] [SMulCommClass G ℤ_[p] A] :
    DistribMulAction G (PadicPontryaginDual p A) where
  smul g φ := contragredientSMul p G A g φ
  smul_zero g := by
    ext a
    change (0 : PadicPontryaginDual p A) (g⁻¹ • a) = 0
    rfl
  smul_add g φ ψ := by
    ext a
    change (φ + ψ) (g⁻¹ • a) = φ (g⁻¹ • a) + ψ (g⁻¹ • a)
    rfl
  one_smul φ := by
    ext a
    change φ ((1 : G)⁻¹ • a) = φ a
    simp
  mul_smul g h φ := by
    ext a
    change φ ((g * h)⁻¹ • a) = φ (h⁻¹ • g⁻¹ • a)
    rw [mul_inv_rev, mul_smul]

/-- **Evaluating the contragredient action.** Let $p$ be a prime, $G$ a group and $A$ a
$\mathbb{Z}_p$-module on which $G$ acts by additive maps commuting with the
$\mathbb{Z}_p$-action. For $g \in G$, $\varphi$ in the algebraic $p$-adic Pontryagin dual of $A$
and $a \in A$, the contragredient action satisfies $(g \cdot \varphi)(a) = \varphi(g^{-1} a)$. -/
@[simp]
theorem smul_apply (p : ℕ) [Fact p.Prime] (G A : Type*) [Group G]
    [AddCommGroup A] [Module ℤ_[p] A] [DistribMulAction G A] [SMulCommClass G ℤ_[p] A]
    (g : G) (φ : PadicPontryaginDual p A) (a : A) :
    (g • φ) a = φ (g⁻¹ • a) :=
  rfl

end MetaMathlibExt
