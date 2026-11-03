/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Regular.SMul
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Coordinatization toolkit for the Bézout bridge

This module provides the coordinate-level toolkit that translates the
idempotent-submodule problem into a system of homogeneous quadratic equations:
finite bases indexed by `Fin n`, structure constants, the coordinate
parametrization `coordVec`, the coordinate quadrics `sqCoords`, and the
homogenized system `homogQuadric`, together with their basic properties
(membership, the bilinear expansion of the square, faithfulness of coordinates,
homogeneity, smoothness at the distinguished point, and the elementwise form
of the `N(V) = {0}` hypothesis).

The statements mirror the reference formulations in
`Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout` with identical short
names. The one
signature difference is that `sq_expand` takes the scalar-tower and
scalar-commutativity hypotheses explicitly (re-installed locally), rather
than through instance binders.

## Assumptions

`K` is a field and `E` a (not necessarily unital or associative) `K`-module.
Finiteness of `E` over `K` and the `IsScalarTower` / `SMulCommClass`
hypotheses are threaded as explicit `Prop` hypotheses rather than instance
binders, so callers control exactly which facts are in scope. No
algebraic-closedness hypothesis appears here: none of these lemmas needs it,
so downstream consumers add it at their own use sites.

Results live in the `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CoordinatizationToolkit`
namespace. This
module depends only on `EvolutionAlgebras.Section_2_Preliminaries.A_Preliminaries` and Mathlib.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CoordinatizationToolkit

open scoped BigOperators

variable (K E : Type*) [Field K] [NonUnitalNonAssocRing E] [Module K E]

/-- Existence of a positive-dimensional finite basis: over a field, a finite
nonzero submodule admits a basis indexed by `Fin n` for some `n ≥ 1`
(via `finrank > 0`, since a nonzero submodule is nontrivial). -/
theorem exists_pos_fin_basis (V : Submodule K E)
    (hfin : Module.Finite K E) (hneV : V ≠ ⊥) :
    ∃ (n : ℕ) (_ : 0 < n), Nonempty (Module.Basis (Fin n) K V) := by
  have hfinV : Module.Finite K V :=
    @FiniteDimensional.finiteDimensional_submodule K E _ _ _ hfin V
  have hnt : Nontrivial V := (Submodule.nontrivial_iff_ne_bot).mpr hneV
  have hpos : 0 < Module.finrank K V :=
    ((@Module.finrank_pos_iff_of_free K V _ _ _ _ _ hfinV).mpr hnt)
  exact ⟨Module.finrank K V, hpos,
    ⟨@Module.finBasisOfFinrankEq K V _ _ _ _ _ hfinV _ rfl⟩⟩

/-- Structure constants: since `V` is idempotent (`V² = V`), each basis
product proves back in `V` and hence expands in the basis. -/
theorem exists_structure_constants {V : Submodule K E} {n : ℕ}
    (b : Module.Basis (Fin n) K V) (hV : IsIdempotentSubmodule K E V) :
    ∃ c : Fin n → Fin n → Fin n → K,
      ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E) := by
  have hsq : square K E V = V := hV
  have hmem : ∀ i j : Fin n, (b i : E) * (b j : E) ∈ V := by
    intro i j
    have hgen : (b i : E) * (b j : E) ∈ square K E V := by
      apply Submodule.subset_span
      exact ⟨(b i : E), (b i).property, (b j : E), (b j).property, rfl⟩
    rwa [hsq] at hgen
  refine ⟨fun i j k => b.repr ⟨(b i : E) * (b j : E), hmem i j⟩ k, fun i j => ?_⟩
  have hrep := b.sum_repr ⟨(b i : E) * (b j : E), hmem i j⟩
  have hcon := congrArg (⇑V.subtype) hrep
  rw [map_sum] at hcon
  simp only [map_smul, Submodule.subtype_apply] at hcon
  exact hcon.symm

/-- Coordinate vector: the element of `E` with coordinates `X` in the basis `b`,
that is, `v(X) = ∑ i, X i • b i`. -/
noncomputable def coordVec {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (X : Fin n → K) : E :=
  ∑ i, X i • (b i : E)

/-- Quadrics of the squaring map: `Fₖ(X)` is the `k`-th coordinate of `v(X)²`
in the basis `b`, computed from the structure constants `c`. -/
def sqCoords {n : ℕ} (c : Fin n → Fin n → Fin n → K) (k : Fin n)
    (X : Fin n → K) : K :=
  ∑ i, ∑ j, c i j k * X i * X j

/-- Homogenized system `Gₖ(X, z) = Fₖ(X) - z * Xₖ`, whose cone solutions
with `X ≠ 0` are the weak second points sought downstream. -/
def homogQuadric {n : ℕ} (c : Fin n → Fin n → Fin n → K) (k : Fin n)
    (X : Fin n → K) (z : K) : K :=
  sqCoords K c k X - z * X k

/-- Coordinate vectors lie in `V`, as sums of scalar multiples of basis vectors. -/
theorem coordVec_mem {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (X : Fin n → K) : coordVec K E b X ∈ V := by
  unfold coordVec
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact (b i).property

/-- The distinguished point is always a solution: `F(0) = 0` since every
monomial of a quadric vanishes at `0`, so `Gₖ(0, 1) = 0 - 1 * 0 = 0`. -/
theorem distinguished_isSolution {n : ℕ} (c : Fin n → Fin n → Fin n → K)
    (k : Fin n) : homogQuadric K c k 0 1 = 0 := by
  simp [homogQuadric, sqCoords]

/-- Bilinear expansion of the square in coordinates:
`(∑ᵢ Xᵢbᵢ)² = ∑ₖ Fₖ(X) bₖ`, by distributivity of `*` over `+` and scalar
interchange through the product (via the explicit tower/commutativity
hypotheses). -/
theorem sq_expand {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (c : Fin n → Fin n → Fin n → K)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (X : Fin n → K) (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    coordVec K E b X * coordVec K E b X =
      ∑ k, sqCoords K c k X • (b k : E) := by
  have := htower
  have := hcomm
  have hsm : ∀ (a b : K) (u v : E), (a • u) * (b • v) = (a * b) • (u * v) := by
    intro a b u v
    rw [smul_mul_assoc, mul_smul_comm, ← smul_smul]
  have hscalar : ∀ i j k : Fin n,
      (X i * X j) * c i j k = c i j k * X i * X j := by
    intro i j k
    rw [mul_comm (X i * X j) (c i j k), ← mul_assoc]
  have hper : ∀ i j : Fin n,
      (X i • (b i : E)) * (X j • (b j : E)) =
        ∑ k, (c i j k * X i * X j) • (b k : E) := by
    intro i j
    have h1 : (X i • (b i : E)) * (X j • (b j : E))
        = (X i * X j) • ((b i : E) * (b j : E)) :=
      hsm (X i) (X j) _ _
    rw [h1, hexp i j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, hscalar i j k]
  have hswap : ∀ f : Fin n → Fin n → Fin n → E,
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
    intro f
    calc ∑ i, ∑ j, ∑ k, f i j k
        = ∑ i, ∑ k, ∑ j, f i j k := by
          congr 1
          ext i
          exact Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, f i j k := Finset.sum_comm
  have hR : (∑ k, sqCoords K c k X • (b k : E))
      = ∑ k, ∑ i, ∑ j, (c i j k * X i * X j) • (b k : E) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold sqCoords
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
  unfold coordVec
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, hper]
  rw [hswap, ← hR]

/-- Coordinates are faithful: the basis images `(bₖ : E)` are linearly
independent in `E`, so `v(X) = 0` forces `X = 0`. -/
theorem coordVec_eq_zero {V : Submodule K E} {n : ℕ}
    (b : Module.Basis (Fin n) K V) (X : Fin n → K)
    (h : coordVec K E b X = 0) : X = 0 := by
  have hindep : LinearIndependent K (V.subtype ∘ b) :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hsum : ∑ i, X i • (V.subtype ∘ b) i = 0 := h
  have hX : ∀ i, X i = 0 := Fintype.linearIndependent_iff.mp hindep X hsum
  funext i
  exact hX i

/-- Smoothness at the distinguished point: the linear parts of `G` at
`(0, 1)` are the coordinate forms `-xₖ` (the Jacobian there is `[-I | 0]`,
of rank `n`), which are linearly independent — so `[0:1]` is a smooth
`K`-point of multiplicity one. -/
theorem distinguished_smooth (n : ℕ) :
    LinearIndependent K (fun k : Fin n => fun dx : Fin n → K => -dx k) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h0 := congrFun hg (Pi.single (M := fun _ => K) i (1 : K))
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
  have hsum : ∑ j ∈ s, g j * (-(Pi.single (M := fun _ => K) i (1 : K) j)) = -(g i) := by
    calc ∑ j ∈ s, g j * (-(Pi.single (M := fun _ => K) i (1 : K) j))
        = g i * (-(Pi.single (M := fun _ => K) i (1 : K) i)) :=
          Finset.sum_eq_single_of_mem i hi (fun j _ hji => by
            have hzero : Pi.single (M := fun _ => K) i (1 : K) j = 0 := by
              simp [hji]
            simp [hzero])
      _ = -(g i) := by simp
  rw [hsum] at h0
  exact neg_eq_zero.mp h0

/-- Quadratic homogeneity of the coordinate quadrics: each monomial of `Fₖ`
has total degree 2, so `Fₖ(a • X) = a² * Fₖ(X)`. -/
theorem sqCoords_hom {n : ℕ} (c : Fin n → Fin n → Fin n → K)
    (k : Fin n) (a : K) (X : Fin n → K) :
    sqCoords K c k (a • X) = a ^ 2 * sqCoords K c k X := by
  simp only [sqCoords, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The `N(V) = {0}` hypothesis as an elementwise rule: a vector of `V`
squaring to zero is zero. -/
theorem eq_zero_of_mem_sq_eq_zero (V : Submodule K E)
    (hN : absNilpotent K E V = {0}) {x : E} (hx : x ∈ V) (hxx : x * x = 0) :
    x = 0 := by
  have hmem : x ∈ absNilpotent K E V := ⟨hx, hxx⟩
  rw [hN] at hmem
  exact Set.mem_singleton_iff.mp hmem

end CoordinatizationToolkit
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
