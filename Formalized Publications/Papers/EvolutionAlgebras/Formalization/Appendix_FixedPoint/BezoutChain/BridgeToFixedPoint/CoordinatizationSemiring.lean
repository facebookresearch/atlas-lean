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
# Coordinatization lemmas on the Semiring spine

Ports the 9 reuse lemmas (`exists_pos_fin_basis`, `exists_structure_constants`,
`coordVec_mem`, `distinguished_isSolution`, `sq_expand`, `coordVec_eq_zero`,
`distinguished_smooth`, `sqCoords_hom`, `eq_zero_of_mem_sq_eq_zero`) plus their
3 supporting definitions (`coordVec`, `sqCoords`, `homogQuadric`) from the Ring
spine (`Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.CoordinatizationToolkit`) onto the
Semiring spine shared by the principle
and both consumers, with identical short names.

Spine: `variable (K E: Type*) [Field K] [NonUnitalNonAssocSemiring E]
[Module K E]`, matching `A_FixedPoint.lean` exactly. `IsScalarTower K E E` /
`SMulCommClass K E E` ride as *instance* binders on `sq_expand` only (the
`FixedPointFromBezout` shape, not the Ring file's explicit-`Prop` shape):
both consumer contexts synthesize them (verified by probe), so no `Prop`-hyp fallback is needed.
They are local — not `variable`
— binders because `variable`-level placement trips `linter.unusedSectionVars`
on the 8 non-using lemmas (confirmed by probe).
`IsAlgClosed` is not threaded (same reason as the Ring file).

Consumer-instance recon (exact contexts recorded):
* Bundle (`B_Theorem_3_3_IdempotentElementsAndSubspaces.lean`): `[Field K]
  [NonUnitalNonAssocSemiring E]
  [NonUnitalNonAssocAlgebra K E]` — `Module`/`IsScalarTower`/`SMulCommClass`
  all synthesize via parent projections of the local bundle class
  (`A_EvolutionAlgebra.lean`).
* Ring (`SolvableCorollary` converse/iff): `[Field K] [NonUnitalNonAssocRing E]
  [Module K E] [IsScalarTower K E E] [SMulCommClass K E E] [IsAlgClosed K]
  [FiniteDimensional K E]` — `NonUnitalNonAssocSemiring E` synthesizes from
  the Ring root; tower/comm are already present.
* Principle (`A_FixedPoint.lean`): `[Field K] [NonUnitalNonAssocSemiring E]
  [Module K E]` — tower/comm do *not* synthesize here (no algebra
  structure); how the final proof absorbs them is the documented
  integration-time decision (`FixedPointFromBezout.lean`), not this file's.

Per-lemma port notes:
* 7 lemmas + 3 defs elaborate *verbatim*: `exists_structure_constants`,
  `coordVec_mem`, `distinguished_isSolution`, `sq_expand`, `distinguished_smooth`,
  `sqCoords_hom`, `eq_zero_of_mem_sq_eq_zero`.
* `coordVec_eq_zero` (P2c #6): the verbatim proof (via
  `LinearIndependent.map'` + `Fintype.linearIndependent_iff`) fails with a
  `whnf` timeout at default (200K) *and* raised (1M) heartbeats — an artifact
  of TC search for `AddCommGroup ↥V` through `map'` (whose section needs
  `[Ring R] [AddCommGroup M] [AddCommGroup M']`), not a fundamental need.
  Restructured onto semiring-native API (`Submodule.subtype_injective` +
  `Fintype.linearIndependent_iffₛ`), which ports cleanly at default heartbeats.
* `exists_pos_fin_basis`: the verbatim proof fails cleanly at step 1
  (`FiniteDimensional.finiteDimensional_submodule` needs `AddCommGroup E`).
  Since `K` is a field, additive inverses are *derivable* via Mathlib's own
  `Module.addCommMonoidToAddCommGroup`; but binding the derived groups with
  `haveI`/`have` re-triggers the §1 diamond (`failed to synthesize Module K E`,
  local hypotheses register for TC). Fix: pass the derived groups as *inline*
  terms inside fully explicit `@`-applications, keeping TC single-pathed
  (projection-defeq to the original `AddCommMonoid` verified by `rfl`).
  No `haveI`, no heartbeats bump, statement on the pure Semiring spine.

Namespace `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.CoordinatizationSemiring` keeps
short names
identical while avoiding collisions with the Ring file. Import-DAG-safe:
imports only clean `A_Preliminaries` + Mathlib (import block identical to the Ring
file — both new names resolve transitively (verified by probe));
never `BridgeToFixedPoint.FixedPointFromBezout`, `Statement.Statement`, or
`Geometry.Counting` (the exclusion is DAG hygiene).
No `ProjectiveToConeExtraction`/`MkSystemBridge`/`MkSystemSmoothness` piece
is needed by these 9.

Status: unconditional (9/9 ported, 0 errors 0 warnings).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CoordinatizationSemiring

open scoped BigOperators

variable (K E : Type*) [Field K] [NonUnitalNonAssocSemiring E] [Module K E]

/-- Coordinatization, existence (outline step 2, proved below):
over a field, a finite nonzero submodule has a finite basis indexed by
`Fin n` with `n ≥ 1` (via `finrank > 0` / a nonzero vector in `V`).

Semiring port: the finrank API needs `AddCommGroup`, which is derived from the
field scalars (`Module.addCommMonoidToAddCommGroup`) and passed as inline
terms inside explicit `@`-applications — never bound, since bound derived
groups re-trigger the §1 diamond. -/
theorem exists_pos_fin_basis (V : Submodule K E)
    (hfin : Module.Finite K E) (hneV : V ≠ ⊥) :
    ∃ (n : ℕ) (_ : 0 < n), Nonempty (Module.Basis (Fin n) K V) := by
  have myFreeV : Module.Free K V := @Module.Free.of_divisionRing K V _
    (Module.addCommMonoidToAddCommGroup K) _
  have hfinV : Module.Finite K V :=
    @FiniteDimensional.finiteDimensional_submodule K E _
      (Module.addCommMonoidToAddCommGroup K) _ hfin V
  have hnt : Nontrivial V := (Submodule.nontrivial_iff_ne_bot).mpr hneV
  have hpos : 0 < Module.finrank K V :=
    ((@Module.finrank_pos_iff_of_free K V _ _ _ _ myFreeV hfinV).mpr hnt)
  exact ⟨Module.finrank K V, hpos,
    ⟨@Module.finBasisOfFinrankEq K V _ _ _ myFreeV _ hfinV _ rfl⟩⟩

/-- Structure constants (outline step 2, proved below): basis products
land back in `V` by idempotence (`V² = V`), hence expand in the basis. -/
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

/-- Coordinate vector: the element of `E` with coordinates `X` in the basis `b`. -/
noncomputable def coordVec {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (X : Fin n → K) : E :=
  ∑ i, X i • (b i : E)

/-- Quadrics of the squaring map: `Fₖ(X)` is the `k`-th coordinate of `v(X)²`. -/
def sqCoords {n : ℕ} (c : Fin n → Fin n → Fin n → K) (k : Fin n)
    (X : Fin n → K) : K :=
  ∑ i, ∑ j, c i j k * X i * X j

/-- Homogenized system `Gₖ(X, z) = Fₖ(X) - z * Xₖ` (outline step 3). -/
def homogQuadric {n : ℕ} (c : Fin n → Fin n → Fin n → K) (k : Fin n)
    (X : Fin n → K) (z : K) : K :=
  sqCoords K c k X - z * X k

/-- Coordinate vectors lie in `V` (sums of scalar multiples of basis vectors). -/
theorem coordVec_mem {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (X : Fin n → K) : coordVec K E b X ∈ V := by
  unfold coordVec
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact (b i).property

/-- The distinguished point is always a solution (outline step 3, proved):
`F(0) = 0` since every monomial of a quadric vanishes at `0`, so
`Gₖ(0, 1) = 0 - 1 * 0 = 0`. -/
theorem distinguished_isSolution {n : ℕ} (c : Fin n → Fin n → Fin n → K)
    (k : Fin n) : homogQuadric K c k 0 1 = 0 := by
  simp [homogQuadric, sqCoords]

/-- Bilinear expansion of the square in coordinates (outline steps 4–5, proved
below): `(∑ᵢ Xᵢbᵢ)² = ∑ₖ Fₖ(X) bₖ`, by distributivity of `*` over `+`
and scalar interchange through the product.

Semiring port: scalar-compatibility rides as local *instance* binders (the
`FixedPointFromBezout` shape); both consumer probes synthesize them. -/
theorem sq_expand {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (c : Fin n → Fin n → Fin n → K)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (X : Fin n → K) [IsScalarTower K E E] [SMulCommClass K E E] :
    coordVec K E b X * coordVec K E b X =
      ∑ k, sqCoords K c k X • (b k : E) := by
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

/-- Coordinates are faithful (proved below): the basis images
`(bₖ : E)` are linearly independent in `E`, so `v(X) = 0` forces `X = 0`.

Semiring port (P2c #6): the Ring proof's `map'`-route whnf-times-out on this
spine (TC search for `AddCommGroup ↥V`, 200K and 1M heartbeats alike), so the
argument goes through `Submodule.subtype_injective` and the semiring-native
`Fintype.linearIndependent_iffₛ` instead. -/
theorem coordVec_eq_zero {V : Submodule K E} {n : ℕ}
    (b : Module.Basis (Fin n) K V) (X : Fin n → K)
    (h : coordVec K E b X = 0) : X = 0 := by
  have hmap : V.subtype (∑ i, X i • b i) = (0 : E) := by
    rw [map_sum]
    simp only [map_smul, Submodule.subtype_apply]
    exact h
  have hV : (∑ i, X i • b i : V) = 0 :=
    V.subtype_injective (by rw [hmap, map_zero])
  have heq : (∑ i, X i • b i : V) = ∑ i, (0 : Fin n → K) i • b i := by
    rw [hV]
    simp
  have hXi := Fintype.linearIndependent_iffₛ.mp b.linearIndependent X 0 heq
  funext i
  exact hXi i

/-- Smoothness at the distinguished point (outline step 3, proved below):
the linear parts of `G` at `(0, 1)` are the forms `-xₖ` (the Jacobian there is
`[-I | 0]`, rank `n`), which are linearly independent — so `[0:1]` is a smooth
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

/-- Quadratic homogeneity of the coordinate quadrics (proved): each monomial
of `Fₖ` has total degree 2, so `Fₖ(a • X) = a² * Fₖ(X)`. -/
theorem sqCoords_hom {n : ℕ} (c : Fin n → Fin n → Fin n → K)
    (k : Fin n) (a : K) (X : Fin n → K) :
    sqCoords K c k (a • X) = a ^ 2 * sqCoords K c k X := by
  simp only [sqCoords, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The `N(V) = {0}` hypothesis as an elementwise rule (proved): a vector of
`V` squaring to zero is zero. -/
theorem eq_zero_of_mem_sq_eq_zero (V : Submodule K E)
    (hN : absNilpotent K E V = {0}) {x : E} (hx : x ∈ V) (hxx : x * x = 0) :
    x = 0 := by
  have hmem : x ∈ absNilpotent K E V := ⟨hx, hxx⟩
  rw [hN] at hmem
  exact Set.mem_singleton_iff.mp hmem

end CoordinatizationSemiring
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
