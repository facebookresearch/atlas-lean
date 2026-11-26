/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_ComponentGroup.lean`,
`Definitions/Def_CerednikDrinfeld_Ribbon.lean` and
`Definitions/Def_CerednikDrinfeld_MumfordPeriod.lean`
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

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Defs
public import MathlibExt.Combinatorics.SimpleGraph.SchottkyTreeAction

@[expose] public section

noncomputable section

open MulAction CerednikDrinfeld CerednikDrinfeld.Mumford

namespace Mumford

section Lattice

variable {ι : Type*} [Fintype ι]

/-- The degree (sum of coordinates) functional on a free abelian group. -/
public def degreeOn (ι : Type*) [Fintype ι] : (ι → ℤ) →ₗ[ℤ] ℤ :=
  ∑ x : ι, LinearMap.proj x

@[simp]
public theorem degreeOn_apply (D : ι → ℤ) : degreeOn ι D = ∑ x : ι, D x := by
  simp [degreeOn]

/-- The character lattice: degree-zero elements of a free abelian group. -/
public def characterLattice (ι : Type*) [Fintype ι] :
    Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (degreeOn ι)

public theorem mem_characterLattice {D : ι → ℤ} :
    D ∈ characterLattice ι ↔ ∑ x : ι, D x = 0 := by
  simp [characterLattice, LinearMap.mem_ker]

/-- The diagonal pairing weighted by `e`. -/
public def widthPairing (e : ι → ℕ) :
    (ι → ℤ) →ₗ[ℤ] (ι → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun D D' => ∑ x : ι, (e x : ℤ) * (D x * D' x))
    (fun D₁ D₂ D' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun D D'₁ D'₂ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp]
public theorem widthPairing_apply (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = ∑ x : ι, (e x : ℤ) * (D x * D' x) :=
  rfl

end Lattice

section Ribbon

variable {E V : Type*}

/-- The incidence matrix of a vertex map. -/
public def degeneracyMatrix [DecidableEq V] (f : E → V) : Matrix V E ℤ :=
  Matrix.of fun v e => if f e = v then 1 else 0

/-- Pushforward of chains along a vertex map. -/
public def pushforward [Fintype E] [DecidableEq V] (f : E → V) :
    (E → ℤ) →ₗ[ℤ] (V → ℤ) :=
  (degeneracyMatrix f).mulVecLin

/-- The two degeneracy maps, packaged as a `Fin 2` family. -/
public def jointDelta [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Fin 2 → ((E → ℤ) →ₗ[ℤ] (V → ℤ)) :=
  ![pushforward D.a, pushforward D.b]

/-- The ribbon kernel: chains killed by both degeneracy maps. -/
public def ribbonKernel [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Submodule ℤ (E → ℤ) :=
  ⨅ i, LinearMap.ker (jointDelta D i)

public theorem mem_ribbonKernel [Fintype E] [DecidableEq V]
    {D : DegeneracyData E V} {x : E → ℤ} :
    x ∈ ribbonKernel D ↔ ∀ i, jointDelta D i x = 0 := by
  simp [ribbonKernel, Submodule.mem_iInf, LinearMap.mem_ker]

public theorem degreeOn_pushforward [Fintype E] [Fintype V] [DecidableEq V]
    (f : E → V) (x : E → ℤ) :
    degreeOn V (pushforward f x) = degreeOn E x := by
  classical
  simp only [degreeOn_apply, pushforward, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp

public theorem ribbonKernel_le_characterLattice [Fintype E] [Fintype V]
    [DecidableEq V] (D : DegeneracyData E V) :
    ribbonKernel D ≤ characterLattice E := by
  intro x hx
  rw [mem_ribbonKernel] at hx
  have h0 : pushforward D.a x = 0 := by
    simpa [jointDelta] using hx 0
  have hdeg : degreeOn E x = 0 := by
    rw [← degreeOn_pushforward D.a x, h0, map_zero]
  simpa [characterLattice, LinearMap.mem_ker] using hdeg

/-- The Gram pairing of the ribbon kernel, given by the edge widths. -/
public def ribbonGram [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    ribbonKernel D →ₗ[ℤ] Module.Dual ℤ (ribbonKernel D) :=
  (widthPairing (fun e => (D.w e : ℕ))).domRestrict₁₂
    (ribbonKernel D) (ribbonKernel D)

@[simp]
public theorem ribbonGram_apply [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (x y : ribbonKernel D) :
    ribbonGram D x y = ∑ e : E, (D.w e : ℤ) * (x.1 e * y.1 e) :=
  rfl

/-- Hecke data on degeneracy data: commuting operators on edges and
vertices, equivariant away from a finite set of bad primes, and preserving
the ribbon kernel. -/
public structure HeckeData [Fintype E] [Fintype V] [DecidableEq V]
    (D : DegeneracyData E V) where
  T : Nat.Primes → Matrix E E ℤ
  Tv : Nat.Primes → Matrix V V ℤ
  comm : ∀ ℓ ℓ' : Nat.Primes, Commute (T ℓ) (T ℓ')
  commv : ∀ ℓ ℓ' : Nat.Primes, Commute (Tv ℓ) (Tv ℓ')
  S : Finset Nat.Primes
  good_equivariant : ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ i : Fin 2,
    ∀ x : E → ℤ,
      jointDelta D i ((T ℓ).mulVecLin x) =
        (Tv ℓ).mulVecLin (jointDelta D i x)
  kernel_stable : ∀ ℓ : Nat.Primes, ∀ x : E → ℤ,
    (∀ i, jointDelta D i x = 0) →
      ∀ i, jointDelta D i ((T ℓ).mulVecLin x) = 0

public theorem ribbonKernel_stable [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ∀ x ∈ ribbonKernel D, (H.T ℓ).mulVecLin x ∈ ribbonKernel D := by
  intro x hx
  rw [mem_ribbonKernel] at hx ⊢
  exact H.kernel_stable ℓ x hx

/-- The Hecke operator induced on the ribbon kernel. -/
public def heckeKernelMap [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ribbonKernel D →ₗ[ℤ] ribbonKernel D :=
  ((H.T ℓ).mulVecLin).restrict (ribbonKernel_stable H ℓ)

end Ribbon

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
period pairing on the ribbon kernel whose valuation recovers the ribbon
Gram pairing. -/
public structure PeriodDatum {E V : Type} [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (K L : Type) [Field K] [Field L] [Algebra K L]
    (ord : Additive Kˣ →+ ℤ) where
  Q : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D) →ₗ[ℤ] Additive Kˣ
  Q_symm : ∀ x y, Q x y = Q y x
  ord_Q : ∀ x y, ord (Q x y) = ribbonGram D x y

/-- Hecke adjointability of period data: every Hecke translate of the
second argument is represented, through `Q`, by a translate of the first. -/
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

/-- `T` captures exactly the torsion of the Jacobian through `U`. -/
public def IsTorsionOf (T : Type) [AddCommGroup T] : Prop :=
  ∃ e : ↥P.U →+ T,
    (∀ t : T, IsOfFinAddOrder t → t ∈ e.range) ∧
      (∀ u, IsOfFinAddOrder (e u)) ∧
        ∀ u : ↥P.U, e u = 0 ↔ (u : P.TorusPoints) ∈ P.periodLattice

end PeriodDatum

end PeriodDatum

end Mumford

end
