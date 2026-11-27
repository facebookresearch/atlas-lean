/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_MumfordPeriod.lean`
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

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Defs
public import MathlibExt.Combinatorics.SimpleGraph.SchottkyTreeAction
public import MathlibExt.NumberTheory.ModularCurve.RibbonKernel

@[expose] public section

noncomputable section

open MulAction CerednikDrinfeld CerednikDrinfeld.Mumford

namespace Mumford

section GraphAction

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W)
  [GraphAction G 𝒯]

variable (G) in
/-- The non-backtracking transition matrix of the quotient graph, indexed by
its oriented edges (the dart orbits). The entry at `(e, e')` is `1` when `e'`
starts where `e` ends and `e'` is not the reversal of `e`, and `0` otherwise
(`formalU_apply`); it is not symmetric in general. It takes finite dart
stabilizers only because it reads the endpoints from
`quotientDegeneracyData`. -/
public def formalU (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    [Fintype (QuotEdge G 𝒯)] [DecidableEq (QuotEdge G 𝒯)]
    [Fintype (QuotVert G W)] [DecidableEq (QuotVert G W)] :
    Matrix (QuotEdge G 𝒯) (QuotEdge G 𝒯) ℤ :=
  (degeneracyMatrix (quotientDegeneracyData G 𝒯 hfin).b).transpose *
      degeneracyMatrix (quotientDegeneracyData G 𝒯 hfin).a
    - Matrix.of fun e e' => if quotientReversal G 𝒯 e' = e then 1 else 0

/-- The entries of `formalU`: the entry at `(e, e')` is `1` when `e'` starts
where `e` ends and `e'` is not the reversal of `e`, and `0` otherwise. -/
public theorem formalU_apply (hfin : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    [Fintype (QuotEdge G 𝒯)] [DecidableEq (QuotEdge G 𝒯)]
    [Fintype (QuotVert G W)] [DecidableEq (QuotVert G W)]
    (e e' : QuotEdge G 𝒯) :
    formalU G 𝒯 hfin e e' =
      if (quotientDegeneracyData G 𝒯 hfin).b e =
          (quotientDegeneracyData G 𝒯 hfin).a e' ∧
        quotientReversal G 𝒯 e' ≠ e then 1 else 0 := by
  have hrev : ∀ e' : QuotEdge G 𝒯,
      (quotientDegeneracyData G 𝒯 hfin).b (quotientReversal G 𝒯 e') =
        (quotientDegeneracyData G 𝒯 hfin).a e' := by
    intro e'
    induction e' using Quotient.inductionOn' with
    | h d => rfl
  simp only [formalU, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply, degeneracyMatrix, Matrix.of_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hr : quotientReversal G 𝒯 e' = e
  · subst hr
    simp [hrev]
  · by_cases hb : (quotientDegeneracyData G 𝒯 hfin).b e =
        (quotientDegeneracyData G 𝒯 hfin).a e'
    · simp [hb, hr]
    · simp [hb, hr, Ne.symm hb]

end GraphAction

section PeriodDatum

/-- Mumford period data over a degeneracy datum: a symmetric bilinear
period pairing `Q` on the ribbon kernel with values in the units of `K`, such
that the given additive homomorphism `ord : Additive Kˣ →+ ℤ` sends `Q x y` to
the ribbon Gram pairing of `x` and `y` (`ord_Q`). Any group homomorphism from
the units of `K` to `ℤ` may serve as `ord`: a valuation is one choice, but no
valuation inequality is required (on `ℚ`, `ord = -v₂` with
`Q x y = (1/2) ^ ribbonGram D x y` is a period datum). -/
public structure PeriodDatum {E V : Type} [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (K L : Type) [Field K] [Field L] [Algebra K L]
    (ord : Additive Kˣ →+ ℤ) where
  Q : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D) →ₗ[ℤ] Additive Kˣ
  Q_symm : ∀ x y, Q x y = Q y x
  ord_Q : ∀ x y, ord (Q x y) = ribbonGram D x y

/-- Hecke adjointability of period data: for each prime `ℓ` and each `y` in
the ribbon kernel there is one `y'` in the ribbon kernel with
`Q y (heckeKernelMap H ℓ z) = Q y' z` for every `z` in the ribbon kernel. The
witness `y'` may depend on `ℓ` and `y`, and it need not be the Hecke translate
`heckeKernelMap H ℓ y`: the Hecke operators need not be self-adjoint for `Q`. -/
public def PeriodDatum.HeckeAdjointable {E V : Type} [Fintype E] [Fintype V]
    [DecidableEq V] {D : DegeneracyData E V} {K L : Type} [Field K] [Field L]
    [Algebra K L] {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord)
    (H : HeckeData D) : Prop :=
  ∀ (ℓ : Nat.Primes) (y : ↥(ribbonKernel D)),
    ∃ y' : ↥(ribbonKernel D),
      ∀ z : ↥(ribbonKernel D), P.Q y (heckeKernelMap H ℓ z) = P.Q y' z

/-- Base change of units along an algebra map, additively. -/
public def unitsBaseChange (K L : Type) [Field K] [Field L] [Algebra K L] :
    Additive Kˣ →ₗ[ℤ] Additive Lˣ :=
  (MonoidHom.toAdditive
    (Units.map (algebraMap K L).toMonoidHom)).toIntLinearMap

@[simp]
public theorem unitsBaseChange_apply (K L : Type) [Field K] [Field L]
    [Algebra K L] (u : Kˣ) :
    unitsBaseChange K L (Additive.ofMul u) =
      Additive.ofMul (Units.map (algebraMap K L).toMonoidHom u) :=
  rfl

namespace PeriodDatum

variable {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
  {K L : Type} [Field K] [Field L] [Algebra K L]
  {ord : Additive Kˣ →+ ℤ} (P : PeriodDatum D K L ord)

/-- Points of the period torus: homomorphisms from the ribbon kernel to
the units of `L`. -/
public abbrev TorusPoints (P : PeriodDatum D K L ord) : Type :=
  ↥(ribbonKernel D) →ₗ[ℤ] Additive Lˣ

/-- The period pairing after base change to `L`. -/
public def QL : ↥(ribbonKernel D) →ₗ[ℤ] P.TorusPoints :=
  P.Q.compr₂ (unitsBaseChange K L)

@[simp]
public theorem QL_apply (x y : ↥(ribbonKernel D)) :
    P.QL x y = unitsBaseChange K L (P.Q x y) :=
  rfl

/-- The period lattice: the image of the period pairing in the torus. -/
public def periodLattice : Submodule ℤ P.TorusPoints :=
  LinearMap.range P.QL

/-- Points of the period Jacobian: the torus modulo the period lattice. -/
public abbrev JacPoints : Type :=
  P.TorusPoints ⧸ P.periodLattice

/-- The preimage in the torus of the torsion subgroup of the Jacobian:
the points whose class modulo the period lattice is torsion. It contains the
period lattice. -/
public def U : Submodule ℤ P.TorusPoints :=
  (Submodule.torsion ℤ P.JacPoints).comap P.periodLattice.mkQ

/-- The projection from `U` to the Jacobian points. -/
public def π : ↥P.U →ₗ[ℤ] P.JacPoints :=
  P.periodLattice.mkQ ∘ₗ P.U.subtype

/-- `T` captures exactly the torsion of the Jacobian through `U`: there is an
additive homomorphism `e : U →+ T` whose values are exactly the finite-order
elements of `T` (every finite-order element of `T` is a value of `e`, and every
value of `e` has finite order), and whose kernel is the period lattice, viewed
inside `U`. `T` itself need not be a torsion group: adding a free summand `ℤ`
to `T` keeps the property. -/
public def IsTorsionOf (T : Type) [AddCommGroup T] : Prop :=
  ∃ e : ↥P.U →+ T,
    (∀ t : T, IsOfFinAddOrder t → t ∈ e.range) ∧
      (∀ u, IsOfFinAddOrder (e u)) ∧
        ∀ u : ↥P.U, e u = 0 ↔ (u : P.TorusPoints) ∈ P.periodLattice

end PeriodDatum

end PeriodDatum

end Mumford

end
