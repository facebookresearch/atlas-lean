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
`Definitions/Def_CerednikDrinfeld_Ribbon.lean` (the degeneracy pushforwards, the
ribbon kernel, its Gram map and the Hecke data on it).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import MathlibExt.Combinatorics.SimpleGraph.SchottkyTreeAction
public import MathlibExt.NumberTheory.ModularCurve.CharacterLattice

/-!
# The ribbon kernel of degeneracy data

For degeneracy data `D` on finite edges (two vertex maps and positive widths), the two
degeneracy pushforwards of integer-valued functions on edges, the ribbon kernel (the functions
both pushforwards kill), the Gram map of the width pairing on it, and Hecke data: commuting
edge and vertex matrices that act on the ribbon kernel. Both the ribbon component group (the
cokernel of the Gram map) and the Mumford period data of a quotient graph
(`MathlibExt.Combinatorics.SimpleGraph.MumfordPeriod`) are built on this layer.
-/

@[expose] public section

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type*}

/-- **Incidence matrix.** The incidence matrix of a vertex map `f`: entry `1` where `f e = v`, and
`0` elsewhere. -/
def degeneracyMatrix [DecidableEq V] (f : E → V) : Matrix V E ℤ :=
  Matrix.of fun v e => if f e = v then 1 else 0

/-- **Pushforward.** Pushforward of integer-valued functions along a vertex map: the value at a
vertex is the sum of the values on the edges over it. -/
def pushforward [Fintype E] [DecidableEq V] (f : E → V) :
    (E → ℤ) →ₗ[ℤ] (V → ℤ) :=
  (degeneracyMatrix f).mulVecLin

/-- **Degeneracy pushforwards.** The two degeneracy pushforwards, along `D.a` and `D.b`, as a family
indexed by `Fin 2`. -/
def jointDelta [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Fin 2 → ((E → ℤ) →ₗ[ℤ] (V → ℤ)) :=
  ![pushforward D.a, pushforward D.b]

/-- **Ribbon kernel.** The functions on edges annihilated by both degeneracy pushforwards. -/
def ribbonKernel [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Submodule ℤ (E → ℤ) :=
  ⨅ i, LinearMap.ker (jointDelta D i)

/-- **Membership in the ribbon kernel.** A function lies in the ribbon kernel exactly when both
degeneracy pushforwards vanish on it. -/
theorem mem_ribbonKernel [Fintype E] [DecidableEq V]
    {D : DegeneracyData E V} {x : E → ℤ} :
    x ∈ ribbonKernel D ↔ ∀ i, jointDelta D i x = 0 := by
  simp [ribbonKernel, Submodule.mem_iInf, LinearMap.mem_ker]

/-- **Degree of a pushforward.** Pushforward preserves the degree. -/
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

/-- **Ribbon kernel and character lattice.** The ribbon kernel is contained in the character
lattice. -/
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

/-- **Ribbon Gram map.** The Gram map of the width pairing on the ribbon kernel. -/
def ribbonGram [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    ribbonKernel D →ₗ[ℤ] Module.Dual ℤ (ribbonKernel D) :=
  (widthPairing (fun e => (D.w e : ℕ))).domRestrict₁₂
    (ribbonKernel D) (ribbonKernel D)

@[simp] theorem ribbonGram_apply [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (x y : ribbonKernel D) :
    ribbonGram D x y = ∑ e : E, (D.w e : ℤ) * (x.1 e * y.1 e) := by
  simp only [ribbonGram, LinearMap.domRestrict₁₂_apply, widthPairing_apply]

/-- **Hecke data.** Commuting Hecke matrices on edges and vertices, equivariant under the degeneracy
maps away from a finite bad set. The fields give an action on the ribbon kernel only
(`heckeKernelMap`): they do not make the edge matrices adjoint for the ribbon Gram pairing, so the
action need not descend to the cokernel of the ribbon Gram map; descent takes an adjoint as an
extra hypothesis. -/
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
  /-- Away from `S`, both degeneracy pushforwards intertwine the edge and vertex Hecke
  matrices. -/
  good_equivariant : ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ i : Fin 2,
    ∀ x : E → ℤ,
      jointDelta D i ((T ℓ).mulVecLin x) =
        (Tv ℓ).mulVecLin (jointDelta D i x)
  /-- The edge Hecke matrices preserve the ribbon kernel, at every prime. -/
  kernel_stable : ∀ ℓ : Nat.Primes, ∀ x : E → ℤ,
    (∀ i, jointDelta D i x = 0) →
      ∀ i, jointDelta D i ((T ℓ).mulVecLin x) = 0

/-- **Hecke stability of the ribbon kernel.** Each edge Hecke matrix `H.T ℓ` maps the ribbon kernel
into itself. -/
theorem ribbonKernel_stable [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ∀ x ∈ ribbonKernel D, (H.T ℓ).mulVecLin x ∈ ribbonKernel D := by
  intro x hx
  rw [mem_ribbonKernel] at hx ⊢
  exact H.kernel_stable ℓ x hx

/-- **Hecke endomorphism of the ribbon kernel.** The restriction of the edge Hecke matrix `H.T ℓ` to
the ribbon kernel. It descends to the cokernel of the ribbon Gram map only together with an adjoint
for the ribbon Gram pairing, which `HeckeData` does not provide. -/
def heckeKernelMap [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ribbonKernel D →ₗ[ℤ] ribbonKernel D :=
  ((H.T ℓ).mulVecLin).restrict (ribbonKernel_stable H ℓ)

end CerednikDrinfeld
