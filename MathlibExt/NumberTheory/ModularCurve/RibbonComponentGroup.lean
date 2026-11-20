/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_Ribbon.lean`
and
`Definitions/Def_ModularCurve_ComponentGroup.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.PNat.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import MathlibExt.NumberTheory.ModularCurve.ComponentGroup

@[expose] public section

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type*}

/-- Degeneracy data: two maps from edges to vertices, with a positive
width at each edge. -/
structure DegeneracyData (E V : Type*) where
  /-- The first vertex map. -/
  a : E → V
  /-- The second vertex map. -/
  b : E → V
  /-- The edge widths. -/
  w : E → ℕ+

/-- The incidence matrix of a vertex map `f`: entry `1` where `f e = v`,
and `0` elsewhere. -/
def degeneracyMatrix [DecidableEq V] (f : E → V) : Matrix V E ℤ :=
  Matrix.of fun v e => if f e = v then 1 else 0

/-- Pushforward of integer-valued functions along a vertex map. -/
def pushforward [Fintype E] [DecidableEq V] (f : E → V) :
    (E → ℤ) →ₗ[ℤ] (V → ℤ) :=
  (degeneracyMatrix f).mulVecLin

/-- The two degeneracy pushforwards, as a family indexed by `Fin 2`. -/
def jointDelta [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Fin 2 → ((E → ℤ) →ₗ[ℤ] (V → ℤ)) :=
  ![pushforward D.a, pushforward D.b]

/-- The ribbon kernel: functions on edges annihilated by both
degeneracy pushforwards. -/
def ribbonKernel [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Submodule ℤ (E → ℤ) :=
  ⨅ i, LinearMap.ker (jointDelta D i)

/-- Membership in the ribbon kernel. -/
theorem mem_ribbonKernel [Fintype E] [DecidableEq V]
    {D : DegeneracyData E V} {x : E → ℤ} :
    x ∈ ribbonKernel D ↔ ∀ i, jointDelta D i x = 0 := by
  simp [ribbonKernel, Submodule.mem_iInf, LinearMap.mem_ker]

/-- Pushforward preserves the degree. -/
theorem degreeOn_pushforward [Fintype E] [Fintype V] [DecidableEq V]
    (f : E → V) (x : E → ℤ) :
    degreeOn V (pushforward f x) = degreeOn E x := by
  classical
  simp only [degreeOn_apply, pushforward, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp

/-- The ribbon kernel is contained in the character lattice. -/
theorem ribbonKernel_le_characterLattice [Fintype E] [Finite V]
    [DecidableEq V] (D : DegeneracyData E V) :
    ribbonKernel D ≤ characterLattice E := by
  have : Fintype V := Fintype.ofFinite V
  intro x hx
  rw [mem_ribbonKernel] at hx
  have h0 : pushforward D.a x = 0 := by
    simpa [jointDelta] using hx 0
  have hdeg : degreeOn E x = 0 := by
    rw [← degreeOn_pushforward D.a x, h0, map_zero]
  simpa [characterLattice, LinearMap.mem_ker] using hdeg

/-- The Gram map of the width pairing on the ribbon kernel. -/
def ribbonGram [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    ribbonKernel D →ₗ[ℤ] Module.Dual ℤ (ribbonKernel D) :=
  (widthPairing (fun e => (D.w e : ℕ))).domRestrict₁₂
    (ribbonKernel D) (ribbonKernel D)

@[simp] theorem ribbonGram_apply [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (x y : ribbonKernel D) :
    ribbonGram D x y = ∑ e : E, (D.w e : ℤ) * (x.1 e * y.1 e) := by
  simp only [ribbonGram, LinearMap.domRestrict₁₂_apply, widthPairing_apply]

/-- The ribbon component group: the cokernel of the ribbon Gram map. -/
abbrev ribbonComponentGroup [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) :=
  Module.Dual ℤ ↥(ribbonKernel D) ⧸ LinearMap.range (ribbonGram D)

/-- The projection to the ribbon component group. -/
abbrev ribbonComponentGroupProj [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) :
    Module.Dual ℤ ↥(ribbonKernel D) →ₗ[ℤ] ribbonComponentGroup D :=
  (LinearMap.range (ribbonGram D)).mkQ

/-- An adjoint pair of endomorphisms of the ribbon kernel preserves
the range of the ribbon Gram map under the dual map. -/
theorem ribbonGram_range_map_dualMap_le [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V)
    (A B : ribbonKernel D →ₗ[ℤ] ribbonKernel D)
    (hadj : ∀ x y : ribbonKernel D,
      ribbonGram D (A x) y = ribbonGram D x (B y)) :
    (LinearMap.range (ribbonGram D)).map B.dualMap ≤
      LinearMap.range (ribbonGram D) := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hf
  refine LinearMap.mem_range.mpr ⟨A x, ?_⟩
  ext y
  rw [LinearMap.dualMap_apply]
  exact hadj x y

/-- The endomorphism of the ribbon component group induced by an
adjoint pair. -/
def ribbonComponentGroupMap [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V)
    (A B : ribbonKernel D →ₗ[ℤ] ribbonKernel D)
    (hadj : ∀ x y : ribbonKernel D,
      ribbonGram D (A x) y = ribbonGram D x (B y)) :
    ribbonComponentGroup D →ₗ[ℤ] ribbonComponentGroup D :=
  (LinearMap.range (ribbonGram D)).mapQ
    (LinearMap.range (ribbonGram D)) B.dualMap
    (fun _ hf => ribbonGram_range_map_dualMap_le D A B hadj
      (Submodule.mem_map_of_mem hf))

/-- Hecke data: commuting Hecke matrices on edges and vertices,
equivariant under the degeneracy maps away from a finite bad set. -/
structure HeckeData [Fintype E] [Fintype V] [DecidableEq V]
    (D : DegeneracyData E V) where
  /-- Hecke matrices on edges. -/
  T : Nat.Primes → Matrix E E ℤ
  /-- Hecke matrices on vertices. -/
  Tv : Nat.Primes → Matrix V V ℤ
  /-- The edge Hecke matrices commute. -/
  comm : ∀ ℓ ℓ' : Nat.Primes, Commute (T ℓ) (T ℓ')
  /-- The vertex Hecke matrices commute. -/
  commv : ∀ ℓ ℓ' : Nat.Primes, Commute (Tv ℓ) (Tv ℓ')
  /-- The finite set of bad primes. -/
  S : Finset Nat.Primes
  /-- Away from `S`, the Hecke action is degeneracy-equivariant. -/
  good_equivariant : ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ i : Fin 2,
    ∀ x : E → ℤ,
      jointDelta D i ((T ℓ).mulVecLin x) =
        (Tv ℓ).mulVecLin (jointDelta D i x)
  /-- The ribbon kernel is stable under the Hecke action. -/
  kernel_stable : ∀ ℓ : Nat.Primes, ∀ x : E → ℤ,
    (∀ i, jointDelta D i x = 0) →
      ∀ i, jointDelta D i ((T ℓ).mulVecLin x) = 0

/-- Hecke stability of the ribbon kernel, as a membership statement. -/
theorem ribbonKernel_stable [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ∀ x ∈ ribbonKernel D, (H.T ℓ).mulVecLin x ∈ ribbonKernel D := by
  intro x hx
  rw [mem_ribbonKernel] at hx ⊢
  exact H.kernel_stable ℓ x hx

/-- The Hecke endomorphism of the ribbon kernel. -/
def heckeKernelMap [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ribbonKernel D →ₗ[ℤ] ribbonKernel D :=
  ((H.T ℓ).mulVecLin).restrict (ribbonKernel_stable H ℓ)

variable {E₁ V₁ E₂ V₂ : Type*}

/-- A matching between two degeneracy/Hecke packages: equivalences of
edges and vertices intertwining the degeneracy data, and intertwining
the Hecke actions away from a finite bad set (and on the ribbon kernel
at bad primes). -/
structure Matching [Fintype E₁] [Fintype V₁] [DecidableEq V₁]
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂}
    (H₁ : HeckeData D₁) (H₂ : HeckeData D₂) where
  /-- The edge equivalence. -/
  eE : E₁ ≃ E₂
  /-- The vertex equivalence. -/
  eV : V₁ ≃ V₂
  /-- Compatibility with the first vertex map. -/
  map_a : ∀ e, D₂.a (eE e) = eV (D₁.a e)
  /-- Compatibility with the second vertex map. -/
  map_b : ∀ e, D₂.b (eE e) = eV (D₁.b e)
  /-- Compatibility with the widths. -/
  map_w : ∀ e, D₂.w (eE e) = D₁.w e
  /-- The finite set of bad primes. -/
  bad : Finset Nat.Primes
  /-- Hecke intertwining away from the bad primes. -/
  away_intertwine : ∀ ℓ : Nat.Primes, ℓ ∉ bad → ∀ x : E₁ → ℤ,
    (H₂.T ℓ).mulVecLin (x ∘ eE.symm) =
      ((H₁.T ℓ).mulVecLin x) ∘ eE.symm
  /-- Hecke intertwining on the ribbon kernel at bad primes. -/
  bad_kernel_intertwine : ∀ ℓ : Nat.Primes, ℓ ∈ bad →
    ∀ x ∈ ribbonKernel D₁,
      (H₂.T ℓ).mulVecLin (x ∘ eE.symm) =
        ((H₁.T ℓ).mulVecLin x) ∘ eE.symm

end CerednikDrinfeld
