/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KoszulComplex
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ExtComparison
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.QuasiIsomorphismBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ReducedMasters
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AugmentedConeStep
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Shrink
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Self-duality foundation for the Koszul complex (step A5, part 1)

Step A5 (part 1) of the scoped Koszul/AB plan (A1–A6): the dual complex
`Hom(K, R)` of the Koszul complex and the per-degree duality isomorphisms.
The full shift isomorphism `Hom(K, R) ≅ K[d]` (exterior-algebra duality
shifting the complex by `d`) needs the Hodge star `⋀^k ≅ ⋀^{d-k}`, which is
absent from Mathlib — that is the documented next milestone (remaining
below). What is proved here is the clean verified foundation on which it
rests: transpose differentials, both Hom-complex bundlings, rank-level
duality, and the canonical same-degree duality iso.

## Contents

* (§1) Transpose differentials: `koszulDualD` (dual of the contraction
  differential, cochain direction) and `koszulCoDualD` (dual of the wedge
  differential, chain direction), each squaring to zero
  (`koszulDualD_comp`, `koszulCoDualD_comp`) via
  `LinearMap.dualMap_comp_dualMap` + the primal `d² = 0`.
* (§2) Hom-complex bundlings: `koszulDualComplex φ` (cochain complex
  `Hom(K(φ), R)` of the chain form) and `koszulCoDualComplex ξ` (chain
  complex `Hom(K(ξ), R)` of the cochain form), following the `dite`
  bundling pattern of `KoszulComplex.lean`.
* (§3) Rank-level duality (the numerical shadow of the shift iso, over a
  field): `dualPiece_finrank`, the complementary-rank identity
  `exteriorPower_finrank_compl` (`k ↔ m - k` via `Nat.choose_symm`),
  `dualPiece_finrank_eq_compl`, the top-degree `koszulTop_finrank_one`,
  and the (non-canonical) degree-wise equiv `koszulDualPieceEquiv`.
* (§4) The canonical same-degree duality iso `koszulPairingEquiv`
  (`⋀^n (Dual M) ≃ₗ Dual (⋀^n M)`, from Mathlib's
  `exteriorPower.bijective_pairingDual`), with the determinant formula
  `koszulPairingEquiv_apply_ιMulti` and the basis form
  `koszulPairingEquiv_basis`.
* (§5) Complement indices + unsigned Hodge star (R-D1 unsigned part).
* (§6) Shift pieces `Dual ⋀^k ≃ ⋀^{m-k}` (R-D2 degree maps, unsigned).
* (§7) Shift target complex (R-D2 shape, unconditional part).
* (§8) Conditional shift iso (R-D2, assembled modulo signed star).
* (§9) Signed Hodge star (R-D1 signed part).
* (§10) Contraction Leibniz rule (R-D2 compat engine).
* (§11) Compatibility: signed star intertwines differentials.
* (§12) Shift compatibility + unconditional shift iso (R-D2).
* (§13) Ext-vanishing below sop length (R-D3 conditional assembly).
* (§14) CommRing generalization (R-D4): `koszulShiftIsoSigned_commRing`
  (`Hom(K, R) ≅ K[m]` over a `CommRing` with `M` finite-free) and the
  `K(sop)` sequence form `koszulShiftIsoSigned_commRing_ofSequence`,
  mirroring §§5–12 with `Field K → CommRing R`.

## Design notes

* `KoszulComplex.lean` is imported read-only; the only API consumed is
  `koszulD`, `koszulD_comp_koszulD`, `koszulContract`,
  `koszulContract_comp`, and the rank formula
  `exteriorPower_finrank_fin_fun`.
* Duals are `Module.Dual R ↥(⋀[R]^k M)` (linear functionals on the
  exterior-power submodules); transposes are `LinearMap.dualMap`.
* The `⋀[R]^n M` notation is global (the exterior-power submodule);
  Mathlib's `exteriorPower.pairingDual` API targets exactly its coercion,
  so no transport is needed.

## remaining (next milestones toward `Hom(K, R) ≅ K[d]`)

* (R-D1) done: the signed Hodge star `koszulHodgeSigned` (§9) and the
  signed shift piece `koszulShiftPieceSigned`, with the
  compatibility-forcing sign `hodgeSignWeight`.
* (R-D2) done: the unconditional shift iso `koszulShiftIsoSigned` (§12),
  via `koszulShiftCompat_signed` discharging the §8 residual.
* (R-D3) done-conditional (§13): A5 part 2 (Ext-vanishing) assembly
  `koszulExt_subsingleton_below_of_homExact` (+ sequence form): from the
  resolution data + explicit chain-level Hom-exactness below `d`, every
  `Ext^i(X, Y)` with `i < d` is a subsingleton — the exact shape
  `ModuleCat.exists_isRegular_tfae` (A6 Rees assembly → `DepthEqDimAt`)
  consumes. Residuals: (a) the R2 pair `(π, QuasiIso π)` in ExtComp shape
  (A4 series, not proved here); (b) the shift+R2 bridge discharging
  the Hom-exactness hyps (needs the shift iso over the base ring —
  §12 is field-only — plus homology transport; shift-iso half closed by
  §14, homology-transport half open).
* (R-D4) done (§14): the shift iso over a `CommRing` for finite-free `M`
  (`koszulShiftIsoSigned_commRing` + sequence form), so R2 exactness of
  `K(sop)` over `R_P` can transport once homology transport proves.

## References

Project (read-only): `Regularity/Koszul/KoszulComplex.lean` (A2 foundation:
`koszulD`, `koszulContract`, both `d² = 0`, rank formula),
(A4(i)
foundation, Hilbert-Samuel sub-plan).

Mathlib (`lean-toolchain` pins `v4.34.0`):
* `LinearAlgebra/Dual/Defs.lean`: `LinearMap.dualMap`, `dualMap_apply`,
  `dualMap_comp_dualMap`, `dualMap_id`.
* `LinearAlgebra/Dual/Lemmas.lean`: `Subspace.dual_finrank_eq`.
* `LinearAlgebra/ExteriorPower/Pairing.lean`: `exteriorPower.pairingDual`,
  `pairingDual_ιMulti_ιMulti` (determinant formula).
* `LinearAlgebra/ExteriorPower/Basis.lean`:
  `exteriorPower.bijective_pairingDual`,
  `pairingDual_apply_dualBasis_exteriorPower`,
  `Module.Basis.exteriorPower`.
* `LinearAlgebra/Dimension/Free.lean`: `LinearEquiv.ofFinrankEq`.
* `Algebra/Homology/HomologicalComplex.lean`: `HomologicalComplex`,
  `CochainComplex`, `ChainComplex`.
* `Data/Nat/Choose/Basic.lean`: `Nat.choose_symm`.

## Status

* §1 transpose differentials + `d² = 0`: unconditional.
* §2 Hom-complex bundlings: unconditional.
* §3 rank-level duality + non-canonical equivs: unconditional.
* §4 canonical same-degree duality iso: unconditional (needs exactly
  `[Module.Free R M] [Module.Finite R M]`).
* §13 R-D3 Ext-vanishing assembly: conditional-exact on `(π, QuasiIso π)`
  (R2 residual, ExtComp shape) + `koszulHomCocycleExactBelow` +
  `koszulHomZeroExact` (shift+R2 bridge content: shift-iso half closed by
  §14, homology-transport half open). The conclusion is
  the exact `exists_isRegular_tfae` shape A6 consumes.
* §14 R-D4 CommRing shift iso: unconditional (needs exactly `[CommRing R]`
  + a `Fin m` basis on `M`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SelfDuality

open CategoryTheory KoszulComplex

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ## §1. Transpose differentials -/

/-- The transpose of the zero map is zero (applied pointwise via
`LinearMap.dualMap_apply`). -/
theorem dualMap_zero (M₁ M₂ : Type*) [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] :
    (0 : M₁ →ₗ[R] M₂).dualMap = 0 := by
  apply LinearMap.ext
  intro g
  apply LinearMap.ext
  intro x
  simp [LinearMap.dualMap_apply]

/-- The dual (transpose) differential of the chain-form Koszul complex:
precomposition with the contraction `koszulContract φ k`. It goes up in
degree (cochain direction): `Dual K_k → Dual K_{k+1}`.
-/
def koszulDualD (φ : M →ₗ[R] R) (k : ℕ) :
    Module.Dual R ↥(⋀[R]^k M) →ₗ[R] Module.Dual R ↥(⋀[R]^(k + 1) M) :=
  (koszulContract φ k).dualMap

/-- The dual differential acts by precomposition with the contraction. -/
@[simp]
theorem koszulDualD_apply (φ : M →ₗ[R] R) (k : ℕ)
    (g : Module.Dual R ↥(⋀[R]^k M)) (z : ↥(⋀[R]^(k + 1) M)) :
    koszulDualD φ k g z = g (koszulContract φ k z) :=
  LinearMap.dualMap_apply _ g z

/-- The dual differential squares to zero: transposition reverses
composition (`dualMap_comp_dualMap`), turning the primal
`koszulContract_comp` into the dual `d² = 0`.
-/
theorem koszulDualD_comp (φ : M →ₗ[R] R) (k : ℕ) :
    (koszulDualD φ (k + 1)).comp (koszulDualD φ k) = 0 := by
  change (koszulContract φ (k + 1)).dualMap.comp (koszulContract φ k).dualMap
    = 0
  rw [LinearMap.dualMap_comp_dualMap, koszulContract_comp, dualMap_zero]

/-- The dual (transpose) differential of the cochain-form Koszul complex:
precomposition with the wedge differential `koszulD ξ k`. It goes down in
degree (chain direction): `Dual K^{k+1} → Dual K^k`.
-/
def koszulCoDualD (ξ : ↥(⋀[R]^1 M)) (k : ℕ) :
    Module.Dual R ↥(⋀[R]^(k + 1) M) →ₗ[R] Module.Dual R ↥(⋀[R]^k M) :=
  (koszulD ξ k).dualMap

/-- The co-dual differential acts by precomposition with the wedge
differential. -/
@[simp]
theorem koszulCoDualD_apply (ξ : ↥(⋀[R]^1 M)) (k : ℕ)
    (g : Module.Dual R ↥(⋀[R]^(k + 1) M)) (z : ↥(⋀[R]^k M)) :
    koszulCoDualD ξ k g z = g (koszulD ξ k z) :=
  LinearMap.dualMap_apply _ g z

/-- The co-dual differential squares to zero (transpose of
`koszulD_comp_koszulD`).
-/
theorem koszulCoDualD_comp (ξ : ↥(⋀[R]^1 M)) (k : ℕ) :
    (koszulCoDualD ξ k).comp (koszulCoDualD ξ (k + 1)) = 0 := by
  change (koszulD ξ k).dualMap.comp (koszulD ξ (k + 1)).dualMap = 0
  rw [LinearMap.dualMap_comp_dualMap, koszulD_comp_koszulD, dualMap_zero]

/-! ## §2. Hom-complex bundlings -/

/-- The dual differential transported along `i + 1 = j`, so it can serve as
the `d i j` morphism for arbitrary `j`. -/
def koszulDualAt (φ : M →ₗ[R] R) (i j : ℕ) (h : i + 1 = j) :
    Module.Dual R ↥(⋀[R]^i M) →ₗ[R] Module.Dual R ↥(⋀[R]^j M) :=
  h ▸ koszulDualD φ i

/-- Transport along `rfl` is the identity. -/
@[simp]
theorem koszulDualAt_rfl (φ : M →ₗ[R] R) (i : ℕ)
    (h : i + 1 = i + 1) : koszulDualAt φ i (i + 1) h = koszulDualD φ i := by
  cases h
  rfl

/-- The complex morphisms: the dual differential on consecutive degrees,
zero elsewhere. -/
def koszulDualMor (φ : M →ₗ[R] R) (i j : ℕ) :
    ModuleCat.of R (Module.Dual R ↥(⋀[R]^i M)) ⟶
      ModuleCat.of R (Module.Dual R ↥(⋀[R]^j M)) :=
  dite (i + 1 = j) (fun h => ModuleCat.ofHom (koszulDualAt φ i j h))
    (fun _ => 0)

/-- On consecutive degrees the morphism is the dual differential. -/
theorem koszulDualMor_succ (φ : M →ₗ[R] R) (i : ℕ) :
    koszulDualMor φ i (i + 1) = ModuleCat.ofHom (koszulDualD φ i) := by
  have hcond : i + 1 = i + 1 := rfl
  rw [koszulDualMor, dite_eq_left hcond]
  exact congrArg ModuleCat.ofHom (koszulDualAt_rfl φ i hcond)

/-- Consecutive morphisms compose to zero (§1 content at the `ModuleCat`
level). -/
theorem koszulDualMor_comp_zero (φ : M →ₗ[R] R) (i j k : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j)
    (hjk : (ComplexShape.up ℕ).Rel j k) :
    koszulDualMor φ i j ≫ koszulDualMor φ j k = 0 := by
  have hij' : i + 1 = j := hij
  have hjk' : j + 1 = k := hjk
  subst hij'
  subst hjk'
  rw [koszulDualMor_succ, koszulDualMor_succ, ← ModuleCat.ofHom_comp,
    koszulDualD_comp, ModuleCat.ofHom_zero]

/-- The dual cochain complex `Hom(K(φ), R)` of the chain-form Koszul
complex, as a `CochainComplex` with `ComplexShape.up ℕ`.
-/
def koszulDualComplex (φ : M →ₗ[R] R) :
    CochainComplex (ModuleCat R) ℕ where
  X k := ModuleCat.of R (Module.Dual R ↥(⋀[R]^k M))
  d := koszulDualMor φ
  shape := fun i j h => by
    have hne : ¬(i + 1 = j) := fun heq => h heq
    simp only [koszulDualMor, dite_eq_right hne]
  d_comp_d' := fun i j k hij hjk => koszulDualMor_comp_zero φ i j k hij hjk

/-- The degree-`k` object of the dual complex. -/
theorem koszulDualComplex_X (φ : M →ₗ[R] R) (k : ℕ) :
    (koszulDualComplex φ).X k =
      ModuleCat.of R (Module.Dual R ↥(⋀[R]^k M)) :=
  rfl

/-- The morphisms of the dual complex are `koszulDualMor`. -/
theorem koszulDualComplex_d (φ : M →ₗ[R] R) :
    (koszulDualComplex φ).d = koszulDualMor φ :=
  rfl

/-- The co-dual differential transported along `j + 1 = i`, so it can serve
as the `d i j` morphism for arbitrary `j`. -/
def koszulCoDualAt (ξ : ↥(⋀[R]^1 M)) (i j : ℕ) (h : j + 1 = i) :
    Module.Dual R ↥(⋀[R]^i M) →ₗ[R] Module.Dual R ↥(⋀[R]^j M) :=
  h ▸ koszulCoDualD ξ j

/-- Transport along `rfl` is the identity. -/
@[simp]
theorem koszulCoDualAt_rfl (ξ : ↥(⋀[R]^1 M)) (j : ℕ)
    (h : j + 1 = j + 1) :
    koszulCoDualAt ξ (j + 1) j h = koszulCoDualD ξ j := by
  cases h
  rfl

/-- The complex morphisms: the co-dual differential on consecutive degrees,
zero elsewhere. -/
def koszulCoDualMor (ξ : ↥(⋀[R]^1 M)) (i j : ℕ) :
    ModuleCat.of R (Module.Dual R ↥(⋀[R]^i M)) ⟶
      ModuleCat.of R (Module.Dual R ↥(⋀[R]^j M)) :=
  dite (j + 1 = i) (fun h => ModuleCat.ofHom (koszulCoDualAt ξ i j h))
    (fun _ => 0)

/-- On consecutive degrees the morphism is the co-dual differential. -/
theorem koszulCoDualMor_succ (ξ : ↥(⋀[R]^1 M)) (j : ℕ) :
    koszulCoDualMor ξ (j + 1) j = ModuleCat.ofHom (koszulCoDualD ξ j) := by
  have hcond : j + 1 = j + 1 := rfl
  rw [koszulCoDualMor, dite_eq_left hcond]
  exact congrArg ModuleCat.ofHom (koszulCoDualAt_rfl ξ j hcond)

/-- Consecutive morphisms compose to zero. -/
theorem koszulCoDualMor_comp_zero (ξ : ↥(⋀[R]^1 M)) (i j k : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j)
    (hjk : (ComplexShape.down ℕ).Rel j k) :
    koszulCoDualMor ξ i j ≫ koszulCoDualMor ξ j k = 0 := by
  have hij' : j + 1 = i := hij
  have hjk' : k + 1 = j := hjk
  subst hij'
  subst hjk'
  rw [koszulCoDualMor_succ, koszulCoDualMor_succ, ← ModuleCat.ofHom_comp,
    koszulCoDualD_comp, ModuleCat.ofHom_zero]

/-- The dual chain complex `Hom(K(ξ), R)` of the cochain-form Koszul
complex, as a `ChainComplex` with `ComplexShape.down ℕ`.
-/
def koszulCoDualComplex (ξ : ↥(⋀[R]^1 M)) :
    ChainComplex (ModuleCat R) ℕ where
  X k := ModuleCat.of R (Module.Dual R ↥(⋀[R]^k M))
  d := koszulCoDualMor ξ
  shape := fun i j h => by
    have hne : ¬(j + 1 = i) := fun heq => h heq
    simp only [koszulCoDualMor, dite_eq_right hne]
  d_comp_d' := fun i j k hij hjk => koszulCoDualMor_comp_zero ξ i j k hij hjk

/-! ## §3. Rank-level duality -/

/-- The dual piece has the same rank as the primal piece (dualizing
preserves `finrank` over a field).
-/
theorem dualPiece_finrank (K : Type*) [Field K] (m k : ℕ) :
    Module.finrank K (Module.Dual K ↥(⋀[K]^k (Fin m → K))) = m.choose k := by
  rw [Subspace.dual_finrank_eq, exteriorPower_finrank_fin_fun]

/-- Complementary-rank identity: degrees `k` and `m - k` have equal rank
(`Nat.choose_symm`). This is the numerical shadow of the shift iso.
-/
theorem exteriorPower_finrank_compl (K : Type*) [Field K] (m k : ℕ)
    (h : k ≤ m) :
    Module.finrank K ↥(⋀[K]^k (Fin m → K)) =
      Module.finrank K ↥(⋀[K]^(m - k) (Fin m → K)) := by
  rw [exteriorPower_finrank_fin_fun, exteriorPower_finrank_fin_fun,
    Nat.choose_symm h]

/-- The dual degree-`k` piece and the primal degree-`(m - k)` piece have
equal rank — the rank-level form of `Hom(K, R) ≅ K[m]`.
-/
theorem dualPiece_finrank_eq_compl (K : Type*) [Field K] (m k : ℕ)
    (h : k ≤ m) :
    Module.finrank K (Module.Dual K ↥(⋀[K]^k (Fin m → K))) =
      Module.finrank K ↥(⋀[K]^(m - k) (Fin m → K)) := by
  rw [dualPiece_finrank, exteriorPower_finrank_fin_fun, Nat.choose_symm h]

/-- The top exterior power has rank one (the dualizing module is free of
rank one).
-/
theorem koszulTop_finrank_one (K : Type*) [Field K] (m : ℕ) :
    Module.finrank K ↥(⋀[K]^m (Fin m → K)) = 1 := by
  rw [exteriorPower_finrank_fin_fun, Nat.choose_self]

/-- Degree-wise (non-canonical) duality equiv from the rank identity: the
dual degree-`k` piece is isomorphic to the primal degree-`(m - k)` piece.
The canonical signed version (Hodge star) is R-D1 in remaining.
-/
noncomputable def koszulDualPieceEquiv (K : Type*) [Field K] (m k : ℕ)
    (h : k ≤ m) :
    Module.Dual K ↥(⋀[K]^k (Fin m → K)) ≃ₗ[K] ↥(⋀[K]^(m - k) (Fin m → K)) :=
  LinearEquiv.ofFinrankEq _ _ (dualPiece_finrank_eq_compl K m k h)

/-! ## §4. The canonical same-degree duality iso -/

/-- The canonical duality iso: the `n`-th exterior power of the dual is
the dual of the `n`-th exterior power (Mathlib's
`exteriorPower.bijective_pairingDual`, bundled as a `LinearEquiv`).
-/
noncomputable def koszulPairingEquiv (n : ℕ) [Module.Free R M]
    [Module.Finite R M] :
    ↥(⋀[R]^n (Module.Dual R M)) ≃ₗ[R] Module.Dual R ↥(⋀[R]^n M) :=
  LinearEquiv.ofBijective _ (exteriorPower.bijective_pairingDual R M n)

/-- The duality iso acts by the determinant pairing on decomposable wedges.
-/
theorem koszulPairingEquiv_apply_ιMulti (n : ℕ) [Module.Free R M]
    [Module.Finite R M] (f : Fin n → Module.Dual R M) (v : Fin n → M) :
    koszulPairingEquiv (R := R) (M := M) n (exteriorPower.ιMulti R n f)
        (exteriorPower.ιMulti R n v) =
      (Matrix.of fun i j => f j (v i)).det := by
  simp only [koszulPairingEquiv, LinearEquiv.ofBijective_apply]
  exact exteriorPower.pairingDual_ιMulti_ιMulti f v

/-- The duality iso sends dual-basis wedges to dual bases: on the
exterior-power basis of a dual basis, it is exactly the dual basis of the
exterior-power basis.
-/
theorem koszulPairingEquiv_basis (n : ℕ) [Module.Free R M] [Module.Finite R M]
    {I : Type*} [LinearOrder I] [Finite I] (b : Module.Basis I R M)
    (s : ↥(Set.powersetCard I n)) :
    koszulPairingEquiv (R := R) (M := M) n
        ((b.dualBasis.exteriorPower n) s) =
      ((b.exteriorPower n).dualBasis s) := by
  simp only [koszulPairingEquiv, LinearEquiv.ofBijective_apply]
  exact exteriorPower.pairingDual_apply_dualBasis_exteriorPower n b s

end SelfDuality
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SelfDuality

open CategoryTheory KoszulComplex

/-! ## §5. Complement indices and the unsigned Hodge star (R-D1, unsigned part) -/

/-- Decidable equality on `k`-subsets of `Fin m` (from `Finset` decidability
plus proof irrelevance on the card constraint).
-/
instance powersetCardFinDecEq (m k : ℕ) :
    DecidableEq ↥(Set.powersetCard (Fin m) k) :=
  fun a b => if h : a.1 = b.1 then isTrue (Subtype.ext h)
    else isFalse (fun e => h (congrArg Subtype.val e))

/-- Finiteness of the exterior-power index set over `Fin m` (for `dualBasis`
in §6).
-/
instance powersetCardFinFinite (m k : ℕ) :
    Finite ↥(Set.powersetCard (Fin m) k) :=
  haveI := (Set.toFinite (Set.powersetCard (Fin m) k)).fintype
  Finite.of_fintype _

/-- Complement on `k`-subsets of `Fin m`: the index-level Hodge star. For
`s` of card `k`, `sᶜ` has card `m - k` (`Finset.card_compl`); the inverse
is complement again (`compl_compl`), with `m - (m - k) = k` from `h`.
-/
def powersetCardComplEquiv (m k : ℕ) (h : k ≤ m) :
    ↥(Set.powersetCard (Fin m) k) ≃ ↥(Set.powersetCard (Fin m) (m - k)) where
  toFun s := ⟨s.1ᶜ, by
    have hs : s.1.card = k := s.2
    change (s.1ᶜ).card = m - k
    rw [Finset.card_compl, Fintype.card_fin, hs]⟩
  invFun t := ⟨t.1ᶜ, by
    have ht : t.1.card = m - k := t.2
    change (t.1ᶜ).card = k
    rw [Finset.card_compl, Fintype.card_fin, ht]
    omega⟩
  left_inv s := Subtype.ext (compl_compl s.1)
  right_inv t := Subtype.ext (compl_compl t.1)

/-- The complement equiv acts by `Finset.compl` on the underlying finsets. -/
@[simp]
theorem powersetCardComplEquiv_val (m k : ℕ) (h : k ≤ m)
    (s : ↥(Set.powersetCard (Fin m) k)) :
    (powersetCardComplEquiv m k h s).1 = s.1ᶜ :=
  rfl

/-- The unsigned Hodge star: `⋀^k ≃ₗ ⋀^{m-k}` over the standard basis,
sending each exterior-power basis wedge to the complementary basis wedge.
Built by reindexing `repr` along `powersetCardComplEquiv`
(`Finsupp.domLCongr`). Canonical given the ordered standard basis, but
unsigned: the signed version (with shuffle signs) is the open R-D1
remainder, forced by R-D2 compatibility (see remaining in the module doc).
-/
noncomputable def koszulHodge (K : Type*) [Field K] (m k : ℕ) (h : k ≤ m) :
    ↥(⋀[K]^k (Fin m → K)) ≃ₗ[K] ↥(⋀[K]^(m - k) (Fin m → K)) :=
  (((Pi.basisFun K (Fin m)).exteriorPower k).repr.trans
    (Finsupp.domLCongr (powersetCardComplEquiv m k h))).trans
    (((Pi.basisFun K (Fin m)).exteriorPower (m - k)).repr.symm)

/-- The unsigned Hodge star sends basis wedges to complementary basis
wedges.
-/
@[simp]
theorem koszulHodge_apply_basis (K : Type*) [Field K] (m k : ℕ) (h : k ≤ m)
    (s : ↥(Set.powersetCard (Fin m) k)) :
    koszulHodge K m k h (((Pi.basisFun K (Fin m)).exteriorPower k) s) =
      (((Pi.basisFun K (Fin m)).exteriorPower (m - k))
        (powersetCardComplEquiv m k h s)) := by
  simp only [koszulHodge, LinearEquiv.trans_apply, Module.Basis.repr_self,
    Finsupp.domLCongr_single]
  rw [← Module.Basis.repr_self (((Pi.basisFun K (Fin m)).exteriorPower (m - k)))
    (powersetCardComplEquiv m k h s)]
  exact LinearEquiv.symm_apply_apply _ _

/-! ## §6. Shift pieces `Dual ⋀^k ≃ ⋀^{m-k}` (R-D2 degree maps, unsigned) -/

/-- The unsigned shift piece: the dual basis of the exterior-power basis,
reindexed by complement, identified with the complementary exterior-power
basis. These are the degree maps of the R-D2 shift iso; the unsigned
versions do not commute with the differentials (see remaining), so the
signed upgrade is the open remainder.
-/
noncomputable def koszulShiftPiece (K : Type*) [Field K] (m k : ℕ)
    (h : k ≤ m) :
    Module.Dual K ↥(⋀[K]^k (Fin m → K)) ≃ₗ[K] ↥(⋀[K]^(m - k) (Fin m → K)) :=
  ((((Pi.basisFun K (Fin m)).exteriorPower k).dualBasis).repr.trans
    (Finsupp.domLCongr (powersetCardComplEquiv m k h))).trans
    (((Pi.basisFun K (Fin m)).exteriorPower (m - k)).repr.symm)

/-- The unsigned shift piece sends dual-basis elements to complementary
basis wedges.
-/
@[simp]
theorem koszulShiftPiece_apply_dualBasis (K : Type*) [Field K] (m k : ℕ)
    (h : k ≤ m) (s : ↥(Set.powersetCard (Fin m) k)) :
    koszulShiftPiece K m k h
        ((((Pi.basisFun K (Fin m)).exteriorPower k).dualBasis) s) =
      (((Pi.basisFun K (Fin m)).exteriorPower (m - k))
        (powersetCardComplEquiv m k h s)) := by
  simp only [koszulShiftPiece, LinearEquiv.trans_apply, Module.Basis.repr_self,
    Finsupp.domLCongr_single]
  rw [← Module.Basis.repr_self (((Pi.basisFun K (Fin m)).exteriorPower (m - k)))
    (powersetCardComplEquiv m k h s)]
  exact LinearEquiv.symm_apply_apply _ _

/-! ## §7. The shift target complex (R-D2 shape, unconditional part) -/

/-- The objects of the shift target complex: `⋀^{m-i}` in degrees `i ≤ m`,
the zero module `Fin 0 → K` beyond. The case split is forced: for `i > m`
the source dual complex is zero (`⋀^i` has rank `m.choose i = 0`), while
`⋀^{m-i} = ⋀^0` has rank one, so no degree-wise iso could target it.
-/
def koszulShiftObj (K : Type*) [Field K] (m i : ℕ) : ModuleCat K :=
  if i ≤ m then ModuleCat.of K ↥(⋀[K]^(m - i) (Fin m → K))
  else ModuleCat.of K (Fin 0 → K)

/-- The in-range objects are the exterior powers (stated with folded
`koszulShiftObj` so `eqToHom` transports stay type-correct).
-/
theorem koszulShiftObj_eq_of_le (K : Type*) [Field K] (m i : ℕ)
    (hi : i ≤ m) :
    koszulShiftObj K m i =
      ModuleCat.of K ↥(⋀[K]^(m - i) (Fin m → K)) := by
  rw [koszulShiftObj, ite_eq_left hi]

/-- Countdown index identity for the shift differential (named so the
transport proof can be generalized in `koszulShiftMor_comp_zero`).
-/
theorem koszulShiftD_index_eq (m k : ℕ) (h : k + 1 ≤ m) :
    m - (k + 1) + 1 = m - k := by
  omega

/-- The shift-target differential at degree `k`: the Koszul contraction,
transported from countdown index `m - (k+1)` to `m - k`.
-/
def koszulShiftD (K : Type*) [Field K] (m k : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (h : k + 1 ≤ m) :
    ↥(⋀[K]^(m - k) (Fin m → K)) →ₗ[K] ↥(⋀[K]^(m - (k + 1)) (Fin m → K)) :=
  (koszulShiftD_index_eq m k h) ▸ koszulContract φ (m - (k + 1))

/-- The shift differential transported along the shape equation `i + 1 = j`
and the object case splits (via `eqToHom`, avoiding dependent
transport hell), so it can serve as the `d i j` morphism.
-/
def koszulShiftAt (K : Type*) [Field K] (m : ℕ) (φ : (Fin m → K) →ₗ[K] K)
    (i j : ℕ) (h : i + 1 = j) (hle : i + 1 ≤ m) :
    koszulShiftObj K m i ⟶ koszulShiftObj K m j :=
  eqToHom (koszulShiftObj_eq_of_le K m i (show i ≤ m from by omega)) ≫
    (h ▸ ModuleCat.ofHom (koszulShiftD K m i φ hle)) ≫
      eqToHom (koszulShiftObj_eq_of_le K m j (h ▸ hle)).symm

/-- The complex morphisms: the shift differential on consecutive degrees
within range, zero elsewhere. -/
def koszulShiftMor (K : Type*) [Field K] (m : ℕ) (φ : (Fin m → K) →ₗ[K] K)
    (i j : ℕ) : koszulShiftObj K m i ⟶ koszulShiftObj K m j :=
  dite (i + 1 = j) (fun h => dite (i + 1 ≤ m)
    (fun hle => koszulShiftAt K m φ i j h hle) (fun _ => 0))
    (fun _ => 0)

/-- On consecutive in-range degrees the morphism is the shift differential. -/
theorem koszulShiftMor_succ_of_le (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (i : ℕ) (hle : i + 1 ≤ m) :
    koszulShiftMor K m φ i (i + 1) =
      koszulShiftAt K m φ i (i + 1) rfl hle := by
  rw [koszulShiftMor, dite_eq_left rfl, dite_eq_left hle]

/-- On consecutive out-of-range degrees the morphism is zero. -/
theorem koszulShiftMor_succ_off (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (i : ℕ) (hle : ¬ i + 1 ≤ m) :
    koszulShiftMor K m φ i (i + 1) = 0 := by
  rw [koszulShiftMor, dite_eq_left rfl, dite_eq_right hle]

/-- Reassociation junction for `eqToHom` pairs in right-nested form: lets
the middle junction cancel via `eqToHom_trans` after `Category.assoc`
normalization (the pair is never a direct subterm otherwise).
-/
theorem eqToHom_middle_junction (R : Type*) [Ring R] {A B D E : ModuleCat R}
    (e2 : A = B) (e3 : B = D) (f : D ⟶ E) :
    eqToHom e2 ≫ (eqToHom e3 ≫ f) = eqToHom (e2.trans e3) ≫ f := by
  rw [← Category.assoc, eqToHom_trans]

/-- Transported contractions compose to zero: the generic form of the
in-range `d² = 0`, with the index equations as hypotheses over variables
(`cases` substitutes them, turning all transports into `rfl`).
-/
theorem koszulShiftD_comp_aux (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (a b c : ℕ) (e1 : b + 1 = a)
    (e2 : c + 1 = b) :
    ((e2 ▸ koszulContract φ c).comp (e1 ▸ koszulContract φ b)) = 0 := by
  cases e1
  cases e2
  change (koszulContract φ c).comp (koszulContract φ (c + 1)) = 0
  exact koszulContract_comp φ c

universe uShiftObj

/-- Reassociation junction for `ofHom` pairs in right-nested form: fuses an
adjacent pair into one `ofHom` of the composite linear map.
-/
theorem ofHom_comp_middle (K : Type*) [Field K]
    {M N O : Type uShiftObj} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup O] [Module K O]
    (l1 : M →ₗ[K] N) (l2 : N →ₗ[K] O) {E : ModuleCat K}
    (g : ModuleCat.of K O ⟶ E) :
    ModuleCat.ofHom l1 ≫ (ModuleCat.ofHom l2 ≫ g) =
      ModuleCat.ofHom (l2.comp l1) ≫ g := by
  rw [← Category.assoc, ModuleCat.ofHom_comp]

/-- Consecutive morphisms compose to zero. The in-range case cancels the
middle `eqToHom` junction (`eqToHom_middle_junction` + `eqToHom_refl`),
strips the `rfl` shape transports by definitional unfolding, and reduces
the linear part to `koszulContract_comp` by generalizing the named index
equations (`set` + `subst` + `cases` turn the transports into `rfl`).
-/
theorem koszulShiftMor_comp_zero (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (i j k : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j)
    (hjk : (ComplexShape.up ℕ).Rel j k) :
    koszulShiftMor K m φ i j ≫ koszulShiftMor K m φ j k = 0 := by
  have hij' : i + 1 = j := hij
  have hjk' : j + 1 = k := hjk
  subst hij'
  subst hjk'
  by_cases hle : i + 1 + 1 ≤ m
  · have hle1 : i + 1 ≤ m := by omega
    have hD : (koszulShiftD K m (i + 1) φ hle).comp
        (koszulShiftD K m i φ hle1) = 0 :=
      koszulShiftD_comp_aux K m φ _ _ _
        (koszulShiftD_index_eq m i hle1)
        (koszulShiftD_index_eq m (i + 1) hle)
    rw [koszulShiftMor_succ_of_le K m φ i hle1,
      koszulShiftMor_succ_of_le K m φ (i + 1) hle]
    simp only [koszulShiftAt, Category.assoc]
    rw [eqToHom_middle_junction, eqToHom_refl, Category.id_comp]
    change eqToHom (koszulShiftObj_eq_of_le K m i
        (show i ≤ m from by omega)) ≫
        ModuleCat.ofHom (koszulShiftD K m i φ hle1) ≫
          ModuleCat.ofHom (koszulShiftD K m (i + 1) φ hle) ≫
            eqToHom (koszulShiftObj_eq_of_le K m (i + 1 + 1)
              (show i + 1 + 1 ≤ m from hle)).symm = 0
    rw [ofHom_comp_middle, hD, ModuleCat.ofHom_zero, Limits.zero_comp,
      Limits.comp_zero]
  · have hle' : ¬ i + 1 + 1 ≤ m := hle
    rw [koszulShiftMor_succ_off K m φ (i + 1) hle']
    exact Limits.comp_zero

/-- The shift target cochain complex: `X k = ⋀^{m-k}` with contraction
differentials (zero beyond `m`). This is the target of the R-D2 shift iso.
-/
def koszulShiftComplex (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) : CochainComplex (ModuleCat K) ℕ where
  X := koszulShiftObj K m
  d := koszulShiftMor K m φ
  shape := fun i j h => by
    have hne : ¬(i + 1 = j) := fun heq => h heq
    simp only [koszulShiftMor, dite_eq_right hne]
  d_comp_d' := fun i j k hij hjk => koszulShiftMor_comp_zero K m φ i j k hij hjk

/-- The degree-`k` object of the shift target complex. -/
theorem koszulShiftComplex_X (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (k : ℕ) :
    (koszulShiftComplex K m φ).X k = koszulShiftObj K m k :=
  rfl

/-- The morphisms of the shift target complex are `koszulShiftMor`. -/
theorem koszulShiftComplex_d (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) :
    (koszulShiftComplex K m φ).d = koszulShiftMor K m φ :=
  rfl

/-! ## §8. The conditional shift iso (R-D2, assembled modulo signed star) -/

/-- Shift compatibility: the R-D2 residual as an explicit hypothesis
(repo-conventional conditional pattern, cf. `KoszulConeSESResidual`): the
degree maps `ψ` commute with the dual differential `δ` and the shift
differential `d`. Satisfied by the signed Hodge star (the open R-D1
remainder); false for the unsigned `koszulShiftPiece` when `m ≥ 2` (see
remaining in the module doc).

Conditional hypothesis (explicit residual for the signed-star development). -/
def koszulShiftCompat (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K))) : Prop :=
  ∀ k : ℕ, ∀ h : k + 1 ≤ m,
    (koszulShiftD K m k φ h).comp (ψ k) =
      (ψ (k + 1)).comp (koszulDualD φ k)

/-- Forward degree maps of the shift Hom: `ψ` on in-range degrees, zero
beyond.
-/
def koszulShiftHomF (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K))) (k : ℕ) :
    (koszulDualComplex φ).X k ⟶ koszulShiftObj K m k :=
  dite (k ≤ m) (fun hk => ModuleCat.ofHom (ψ k) ≫
    eqToHom (koszulShiftObj_eq_of_le K m k hk).symm) (fun _ => 0)

/-- On in-range degrees the forward map is `ψ` transported to the target. -/
theorem koszulShiftHomF_of_le (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K))) (k : ℕ) (hk : k ≤ m) :
    koszulShiftHomF K m φ ψ k = ModuleCat.ofHom (ψ k) ≫
      eqToHom (koszulShiftObj_eq_of_le K m k hk).symm := by
  rw [koszulShiftHomF]
  exact dite_eq_left hk

/-- On out-of-range degrees the forward map is zero. -/
theorem koszulShiftHomF_off (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K))) (k : ℕ) (hk : ¬ k ≤ m) :
    koszulShiftHomF K m φ ψ k = 0 := by
  rw [koszulShiftHomF, dite_eq_right hk]

/-- Forward commutation: the `ψ` squares commute, by `koszulShiftCompat`
after cancelling the object junction.

Conditional on exactly [`koszulShiftCompat`]. -/
theorem koszulShiftHom_comm (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K)))
    (hcompat : koszulShiftCompat K m φ ψ) (i j : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j) :
    koszulShiftHomF K m φ ψ i ≫ koszulShiftMor K m φ i j =
      koszulDualMor φ i j ≫ koszulShiftHomF K m φ ψ j := by
  have hij' : i + 1 = j := hij
  subst hij'
  by_cases hle : i + 1 ≤ m
  · have hle1 : i ≤ m := by omega
    rw [koszulShiftHomF_of_le K m φ ψ i hle1,
      koszulShiftHomF_of_le K m φ ψ (i + 1) hle,
      koszulShiftMor_succ_of_le K m φ i hle, koszulDualMor_succ]
    simp only [koszulShiftAt]
    change (ModuleCat.ofHom (ψ i) ≫
              eqToHom (koszulShiftObj_eq_of_le K m i hle1).symm) ≫
            (eqToHom (koszulShiftObj_eq_of_le K m i hle1) ≫
              (ModuleCat.ofHom (koszulShiftD K m i φ hle) ≫
                eqToHom (koszulShiftObj_eq_of_le K m (i + 1) hle).symm)) =
        ModuleCat.ofHom (koszulDualD φ i) ≫
          (ModuleCat.ofHom (ψ (i + 1)) ≫
            eqToHom (koszulShiftObj_eq_of_le K m (i + 1) hle).symm)
    simp only [Category.assoc]
    rw [eqToHom_middle_junction, eqToHom_refl, Category.id_comp,
      ofHom_comp_middle, ofHom_comp_middle, hcompat i hle]
  · have hmi : m < i + 1 := by omega
    have hdual0 : koszulDualD φ i = 0 := by
      have hfr : Module.finrank K ↥(⋀[K]^(i + 1) (Fin m → K)) = 0 := by
        rw [exteriorPower_finrank_fin_fun, Nat.choose_eq_zero_of_lt hmi]
      rw [Module.finrank_eq_zero_iff] at hfr
      have hsub : Subsingleton ↥(⋀[K]^(i + 1) (Fin m → K)) := by
        constructor
        intro x y
        obtain ⟨a, ha, hax⟩ := hfr x
        obtain ⟨b, hb, hby⟩ := hfr y
        have hx : x = 0 := by
          have h1 : a⁻¹ • (a • x) =
              a⁻¹ • (0 : ↥(⋀[K]^(i + 1) (Fin m → K))) := by
            rw [hax]
          rw [← mul_smul, inv_mul_cancel₀ ha, one_smul, smul_zero] at h1
          exact h1
        have hy : y = 0 := by
          have h1 : b⁻¹ • (b • y) =
              b⁻¹ • (0 : ↥(⋀[K]^(i + 1) (Fin m → K))) := by
            rw [hby]
          rw [← mul_smul, inv_mul_cancel₀ hb, one_smul, smul_zero] at h1
          exact h1
        exact hx.trans hy.symm
      have hC : koszulContract φ i = 0 := by
        apply LinearMap.ext
        intro z
        have hz : z = 0 := hsub.elim z 0
        rw [hz]
        simp
      calc koszulDualD φ i = (koszulContract φ i).dualMap := rfl
        _ = (0 : ↥(⋀[K]^(i + 1) (Fin m → K)) →ₗ[K]
            ↥(⋀[K]^i (Fin m → K))).dualMap := by
            rw [hC]
        _ = 0 := dualMap_zero _ _
    rw [koszulShiftHomF_off K m φ ψ (i + 1) hle,
      koszulShiftMor_succ_off K m φ i hle, koszulDualMor_succ,
      hdual0, ModuleCat.ofHom_zero]
    exact (Limits.comp_zero).trans (Limits.comp_zero).symm

/-- The forward shift Hom `Hom(K, R) → K[m]`, conditional on shift
compatibility (the exact shape A5.2 consumes: a `HomologicalComplex.Hom`
out of `koszulDualComplex`).

Conditional on exactly [`koszulShiftCompat`]. -/
def koszulShiftHom (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K)))
    (hcompat : koszulShiftCompat K m φ ψ) :
    (koszulDualComplex φ) ⟶ (koszulShiftComplex K m φ) where
  f := koszulShiftHomF K m φ ψ
  comm' := fun i j hij => by
    rw [koszulShiftComplex_d, koszulDualComplex_d]
    exact koszulShiftHom_comm K m φ ψ hcompat i j hij

/-- The forward Hom acts degree-wise by `koszulShiftHomF`. -/
theorem koszulShiftHom_f (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K)))
    (hcompat : koszulShiftCompat K m φ ψ) :
    (koszulShiftHom K m φ ψ hcompat).f = koszulShiftHomF K m φ ψ :=
  rfl

/-- Inverse compatibility, derived from forward compatibility plus the
two-sided inverse hypotheses (cancel `ψ` on the right via `hψr`).

Conditional on exactly [`koszulShiftCompat`, `hψl`, `hψr`]. -/
theorem koszulShiftCompat_inv (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K)))
    (ψinv : ∀ k : ℕ, ↥(⋀[K]^(m - k) (Fin m → K)) →ₗ[K]
      Module.Dual K ↥(⋀[K]^k (Fin m → K)))
    (hcompat : koszulShiftCompat K m φ ψ)
    (hψl : ∀ k : ℕ, ∀ _ : k ≤ m, (ψinv k).comp (ψ k) = LinearMap.id)
    (hψr : ∀ k : ℕ, ∀ _ : k ≤ m, (ψ k).comp (ψinv k) = LinearMap.id)
    (k : ℕ) (h : k + 1 ≤ m) :
    (koszulDualD φ k).comp (ψinv k) =
      (ψinv (k + 1)).comp (koszulShiftD K m k φ h) := by
  have hk : k ≤ m := by omega
  have eA : ((koszulDualD φ k).comp (ψinv k)).comp (ψ k) =
      koszulDualD φ k := by
    rw [LinearMap.comp_assoc, hψl k hk, LinearMap.comp_id]
  have eB : ((ψinv (k + 1)).comp (koszulShiftD K m k φ h)).comp (ψ k) =
      koszulDualD φ k := by
    rw [LinearMap.comp_assoc, hcompat k h, ← LinearMap.comp_assoc,
      hψl (k + 1) h, LinearMap.id_comp]
  have hEq := eA.trans eB.symm
  have hcancel := congrArg (fun X => X.comp (ψinv k)) hEq
  simp only [LinearMap.comp_assoc, hψr k hk, LinearMap.comp_id] at hcancel
  exact hcancel

/-- Backward degree maps of the shift Hom: `ψinv` on in-range degrees,
zero beyond.
-/
def koszulShiftHomInvF (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψinv : ∀ k : ℕ, ↥(⋀[K]^(m - k) (Fin m → K)) →ₗ[K]
      Module.Dual K ↥(⋀[K]^k (Fin m → K))) (k : ℕ) :
    koszulShiftObj K m k ⟶ (koszulDualComplex φ).X k :=
  dite (k ≤ m) (fun hk => eqToHom (koszulShiftObj_eq_of_le K m k hk) ≫
    ModuleCat.ofHom (ψinv k)) (fun _ => 0)

/-- On in-range degrees the backward map is `ψinv` transported from the
target. -/
theorem koszulShiftHomInvF_of_le (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψinv : ∀ k : ℕ, ↥(⋀[K]^(m - k) (Fin m → K)) →ₗ[K]
      Module.Dual K ↥(⋀[K]^k (Fin m → K))) (k : ℕ) (hk : k ≤ m) :
    koszulShiftHomInvF K m φ ψinv k =
      eqToHom (koszulShiftObj_eq_of_le K m k hk) ≫
        ModuleCat.ofHom (ψinv k) := by
  rw [koszulShiftHomInvF]
  exact dite_eq_left hk

/-- On out-of-range degrees the backward map is zero. -/
theorem koszulShiftHomInvF_off (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψinv : ∀ k : ℕ, ↥(⋀[K]^(m - k) (Fin m → K)) →ₗ[K]
      Module.Dual K ↥(⋀[K]^k (Fin m → K))) (k : ℕ) (hk : ¬ k ≤ m) :
    koszulShiftHomInvF K m φ ψinv k = 0 := by
  rw [koszulShiftHomInvF, dite_eq_right hk]

/-- Beyond `m`, exterior powers are subsingletons (rank `m.choose k = 0`).
-/
theorem exteriorPower_subsingleton_of_gt (K : Type*) [Field K] (m k : ℕ)
    (h : m < k) : Subsingleton ↥(⋀[K]^k (Fin m → K)) := by
  have hfr : Module.finrank K ↥(⋀[K]^k (Fin m → K)) = 0 := by
    rw [exteriorPower_finrank_fin_fun, Nat.choose_eq_zero_of_lt h]
  rw [Module.finrank_eq_zero_iff] at hfr
  constructor
  intro x y
  obtain ⟨a, ha, hax⟩ := hfr x
  obtain ⟨b, hb, hby⟩ := hfr y
  have hx : x = 0 := by
    have h1 : a⁻¹ • (a • x) = a⁻¹ • (0 : ↥(⋀[K]^k (Fin m → K))) := by
      rw [hax]
    rw [← mul_smul, inv_mul_cancel₀ ha, one_smul, smul_zero] at h1
    exact h1
  have hy : y = 0 := by
    have h1 : b⁻¹ • (b • y) = b⁻¹ • (0 : ↥(⋀[K]^k (Fin m → K))) := by
      rw [hby]
    rw [← mul_smul, inv_mul_cancel₀ hb, one_smul, smul_zero] at h1
    exact h1
  exact hx.trans hy.symm

/-- Duals of subsingleton modules are subsingletons (explicit hypothesis
form, since the `haveI` linter forbids propositional instances locally).
-/
theorem dual_subsingleton_of_subsingleton (K V : Type*) [Field K]
    [AddCommGroup V] [Module K V] (h : Subsingleton V) :
    Subsingleton (Module.Dual K V) :=
  ⟨fun f g => LinearMap.ext fun x => by
    have hx : x = 0 := h.elim x 0
    rw [hx, map_zero, map_zero]⟩

/-- The zero module `Fin 0 → K` is a subsingleton.
-/
theorem piFinZero_subsingleton (K : Type*) [Field K] :
    Subsingleton (Fin 0 → K) :=
  ⟨fun _ _ => funext fun i => Fin.elim0 i⟩

/-- Beyond `m`, the dual differential vanishes (it transposes contraction
out of a zero module).
-/
theorem koszulDualD_eq_zero_of_gt (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (i : ℕ) (h : m < i + 1) :
    koszulDualD φ i = 0 := by
  have hsub := exteriorPower_subsingleton_of_gt K m (i + 1) h
  have hC : koszulContract φ i = 0 := by
    apply LinearMap.ext
    intro z
    have hz : z = 0 := hsub.elim z 0
    rw [hz]
    simp
  calc koszulDualD φ i = (koszulContract φ i).dualMap := rfl
    _ = (0 : ↥(⋀[K]^(i + 1) (Fin m → K)) →ₗ[K] ↥(⋀[K]^i (Fin m → K))).dualMap := by
        rw [hC]
    _ = 0 := dualMap_zero _ _

/-- Backward commutation, from derived inverse compatibility.

Conditional on exactly [`koszulShiftCompat`, `hψl`, `hψr`]. -/
theorem koszulShiftHomInv_comm (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K)))
    (ψinv : ∀ k : ℕ, ↥(⋀[K]^(m - k) (Fin m → K)) →ₗ[K]
      Module.Dual K ↥(⋀[K]^k (Fin m → K)))
    (hcompat : koszulShiftCompat K m φ ψ)
    (hψl : ∀ k : ℕ, ∀ _ : k ≤ m, (ψinv k).comp (ψ k) = LinearMap.id)
    (hψr : ∀ k : ℕ, ∀ _ : k ≤ m, (ψ k).comp (ψinv k) = LinearMap.id)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    koszulShiftHomInvF K m φ ψinv i ≫ koszulDualMor φ i j =
      koszulShiftMor K m φ i j ≫ koszulShiftHomInvF K m φ ψinv j := by
  have hij' : i + 1 = j := hij
  subst hij'
  by_cases hle : i + 1 ≤ m
  · have hle1 : i ≤ m := by omega
    have hinv := koszulShiftCompat_inv K m φ ψ ψinv hcompat hψl hψr i hle
    rw [koszulShiftHomInvF_of_le K m φ ψinv i hle1,
      koszulShiftHomInvF_of_le K m φ ψinv (i + 1) hle,
      koszulShiftMor_succ_of_le K m φ i hle, koszulDualMor_succ]
    simp only [koszulShiftAt]
    change (eqToHom (koszulShiftObj_eq_of_le K m i hle1) ≫
              ModuleCat.ofHom (ψinv i)) ≫
            ModuleCat.ofHom (koszulDualD φ i) =
        (eqToHom (koszulShiftObj_eq_of_le K m i hle1) ≫
          ModuleCat.ofHom (koszulShiftD K m i φ hle) ≫
            eqToHom (koszulShiftObj_eq_of_le K m (i + 1) hle).symm) ≫
          (eqToHom (koszulShiftObj_eq_of_le K m (i + 1) hle) ≫
            ModuleCat.ofHom (ψinv (i + 1)))
    simp only [Category.assoc]
    rw [eqToHom_middle_junction, eqToHom_refl, Category.id_comp,
      ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, hinv]
  · have hmi : m < i + 1 := by omega
    rw [koszulShiftHomInvF_off K m φ ψinv (i + 1) hle,
      koszulShiftMor_succ_off K m φ i hle, koszulDualMor_succ,
      koszulDualD_eq_zero_of_gt K m φ i hmi, ModuleCat.ofHom_zero]
    exact (Limits.comp_zero).trans (Limits.comp_zero).symm

/-- The backward shift Hom `K[m] → Hom(K, R)`.

Conditional on exactly [`koszulShiftCompat`, `hψl`, `hψr`]. -/
def koszulShiftHomInv (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K)))
    (ψinv : ∀ k : ℕ, ↥(⋀[K]^(m - k) (Fin m → K)) →ₗ[K]
      Module.Dual K ↥(⋀[K]^k (Fin m → K)))
    (hcompat : koszulShiftCompat K m φ ψ)
    (hψl : ∀ k : ℕ, ∀ _ : k ≤ m, (ψinv k).comp (ψ k) = LinearMap.id)
    (hψr : ∀ k : ℕ, ∀ _ : k ≤ m, (ψ k).comp (ψinv k) = LinearMap.id) :
    (koszulShiftComplex K m φ) ⟶ (koszulDualComplex φ) where
  f := koszulShiftHomInvF K m φ ψinv
  comm' := fun i j hij => by
    rw [koszulShiftComplex_d, koszulDualComplex_d]
    exact koszulShiftHomInv_comm K m φ ψ ψinv hcompat hψl hψr i j hij

/-- The backward Hom acts degree-wise by `koszulShiftHomInvF`. -/
theorem koszulShiftHomInv_f (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K)))
    (ψinv : ∀ k : ℕ, ↥(⋀[K]^(m - k) (Fin m → K)) →ₗ[K]
      Module.Dual K ↥(⋀[K]^k (Fin m → K)))
    (hcompat : koszulShiftCompat K m φ ψ)
    (hψl : ∀ k : ℕ, ∀ _ : k ≤ m, (ψinv k).comp (ψ k) = LinearMap.id)
    (hψr : ∀ k : ℕ, ∀ _ : k ≤ m, (ψ k).comp (ψinv k) = LinearMap.id) :
    (koszulShiftHomInv K m φ ψ ψinv hcompat hψl hψr).f =
      koszulShiftHomInvF K m φ ψinv :=
  rfl

/-- The R-D2 shift iso `Hom(K, R) ≅ K[m]` as complexes, conditional on the
signed-star data (`ψ` bijective degree-wise + compatibility). This is the
exact shape A5.2 Ext-vanishing consumes: applying
`HomologicalComplex.homology` maps it to `H^i(Hom(K,R)) ≅ H^i(K[m])`, and
A4 exactness kills the right side for `m - i > 0`.

Conditional on exactly [`koszulShiftCompat`, `hψl`, `hψr`]. -/
noncomputable def koszulShiftIso (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K)
    (ψ : ∀ k : ℕ, Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K)))
    (ψinv : ∀ k : ℕ, ↥(⋀[K]^(m - k) (Fin m → K)) →ₗ[K]
      Module.Dual K ↥(⋀[K]^k (Fin m → K)))
    (hcompat : koszulShiftCompat K m φ ψ)
    (hψl : ∀ k : ℕ, ∀ _ : k ≤ m, (ψinv k).comp (ψ k) = LinearMap.id)
    (hψr : ∀ k : ℕ, ∀ _ : k ≤ m, (ψ k).comp (ψinv k) = LinearMap.id) :
    (koszulDualComplex φ) ≅ (koszulShiftComplex K m φ) :=
  Iso.mk (koszulShiftHom K m φ ψ hcompat)
    (koszulShiftHomInv K m φ ψ ψinv hcompat hψl hψr)
    (HomologicalComplex.hom_ext _ _ fun k => by
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        koszulShiftHom_f, koszulShiftHomInv_f]
      by_cases hk : k ≤ m
      · rw [koszulShiftHomF_of_le K m φ ψ k hk,
          koszulShiftHomInvF_of_le K m φ ψinv k hk]
        change (ModuleCat.ofHom (ψ k) ≫
                  eqToHom (koszulShiftObj_eq_of_le K m k hk).symm) ≫
                (eqToHom (koszulShiftObj_eq_of_le K m k hk) ≫
                  ModuleCat.ofHom (ψinv k)) =
              𝟙 ((koszulDualComplex φ).X k)
        simp only [Category.assoc]
        rw [eqToHom_middle_junction, eqToHom_refl, Category.id_comp,
          ← ModuleCat.ofHom_comp, hψl k hk, ModuleCat.ofHom_id]
        simp only [koszulDualComplex_X]
      · have hmk : m < k := by omega
        have hsub := exteriorPower_subsingleton_of_gt K m k hmk
        have hdual :=
          dual_subsingleton_of_subsingleton K ↥(⋀[K]^k (Fin m → K)) hsub
        have hid : (LinearMap.id :
            Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
              Module.Dual K ↥(⋀[K]^k (Fin m → K))) = 0 :=
          LinearMap.ext fun x => hdual.elim x 0
        rw [koszulShiftHomF_off K m φ ψ k hk,
          koszulShiftHomInvF_off K m φ ψinv k hk]
        change (0 : (koszulDualComplex φ).X k ⟶ koszulShiftObj K m k) ≫
                (0 : koszulShiftObj K m k ⟶ (koszulDualComplex φ).X k) =
              𝟙 ((koszulDualComplex φ).X k)
        rw [Limits.comp_zero, koszulDualComplex_X, ← ModuleCat.ofHom_id, hid,
          ModuleCat.ofHom_zero])
    (HomologicalComplex.hom_ext _ _ fun k => by
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        koszulShiftHom_f, koszulShiftHomInv_f]
      by_cases hk : k ≤ m
      · rw [koszulShiftHomF_of_le K m φ ψ k hk,
          koszulShiftHomInvF_of_le K m φ ψinv k hk]
        change (eqToHom (koszulShiftObj_eq_of_le K m k hk) ≫
                  ModuleCat.ofHom (ψinv k)) ≫
                (ModuleCat.ofHom (ψ k) ≫
                  eqToHom (koszulShiftObj_eq_of_le K m k hk).symm) =
              𝟙 ((koszulShiftComplex K m φ).X k)
        simp only [Category.assoc]
        rw [ofHom_comp_middle, hψr k hk, ModuleCat.ofHom_id,
          Category.id_comp, eqToHom_trans, eqToHom_refl]
        simp only [koszulShiftComplex_X]
      · have hsub := piFinZero_subsingleton K
        have hid : (LinearMap.id : (Fin 0 → K) →ₗ[K] (Fin 0 → K)) = 0 :=
          LinearMap.ext fun x => hsub.elim x 0
        rw [koszulShiftHomF_off K m φ ψ k hk,
          koszulShiftHomInvF_off K m φ ψinv k hk]
        change (0 : (koszulShiftComplex K m φ).X k ⟶
                  (koszulDualComplex φ).X k) ≫
                (0 : (koszulDualComplex φ).X k ⟶
                  (koszulShiftComplex K m φ).X k) =
              𝟙 ((koszulShiftComplex K m φ).X k)
        rw [Limits.comp_zero, koszulShiftComplex_X, koszulShiftObj,
          ite_eq_right hk, ← ModuleCat.ofHom_id, hid, ModuleCat.ofHom_zero])

/-! ## §9. The signed Hodge star (R-D1 signed part) -/

/-- The Hodge sign weight: `(-1)` to the sum of the index values. This is
the sign forced by R-D2 compatibility (`koszulShiftCompat`): for `i ∉ S`
the identity `σ(S ∪ {i}) / σ(S) = (-1)^i` must cancel the
contraction-position signs, which determines `σ` up to a global sign
(`neg_one_pow_sum_insert`, `neg_one_pow_sub_add`). It differs from the
classical shuffle-sign Hodge star by degree-dependent factors; any
unit-valued sign gives a valid star, and this is the one making compat
exact.
-/
noncomputable def hodgeSignWeight (K : Type*) [Field K] (m k : ℕ)
    (s : ↥(Set.powersetCard (Fin m) k)) : Kˣ :=
  (-1 : Kˣ)^(s.1.sum fun i => i.val)

/-- The sign is multiplicative over insertion (the compat-forcing identity
at the level of exponents).
-/
theorem neg_one_pow_sum_insert (K : Type*) [Field K] (m : ℕ)
    (S : Finset (Fin m)) (i : Fin m) (hi : i ∉ S) :
    (-1 : K)^((insert i S).sum (fun j => j.val)) =
      (-1 : K)^(S.sum (fun j => j.val)) * (-1 : K)^(i.val) := by
  rw [Finset.sum_insert hi, pow_add]
  exact mul_comm _ _

/-- Parity key for compat: `(-1)^{i-p} = (-1)^{i+p}` since the exponents
differ by the even number `2p`.
-/
theorem neg_one_pow_sub_add (K : Type*) [Field K] (i p : ℕ) (h : p ≤ i) :
    (-1 : K)^(i - p) = (-1 : K)^(i + p) := by
  have h2p : (-1 : K)^(2 * p) = 1 := by
    rw [pow_mul]
    have hsq : (-1 : K)^2 = 1 := by ring
    rw [hsq, one_pow]
  have hexp : i + p = (i - p) + 2 * p := by omega
  rw [hexp, pow_add, h2p, mul_one]

/-- Diagonal scaling of finitely-supported functions by unit weights, as a
linear equiv (the inverse scales by the inverse weights).
-/
noncomputable def diagLinearEquiv (K : Type*) [Field K]
    {ι : Type*} (w : ι → Kˣ) : (ι →₀ K) ≃ₗ[K] (ι →₀ K) where
  toLinearMap :=
    { toFun := fun f =>
        ⟨f.support, fun i => (w i : K) * f i, fun i =>
          ⟨fun hi => mul_ne_zero (Units.ne_zero _)
            (Finsupp.mem_support_iff.mp hi),
           fun hi => Finsupp.mem_support_iff.mpr fun h =>
            hi (by rw [h, mul_zero])⟩⟩
      map_add' := fun f g => by
        ext i
        change (w i : K) * ((f + g) i) = (w i : K) * f i + (w i : K) * g i
        rw [Finsupp.add_apply, mul_add]
      map_smul' := fun r f => by
        ext i
        change (w i : K) * ((r • f) i) = r • ((w i : K) * f i)
        exact Algebra.mul_smul_comm _ _ _ }
  invFun := fun g =>
    ⟨g.support, fun i => (((w i)⁻¹ : Kˣ) : K) * g i, fun i =>
      ⟨fun hi => mul_ne_zero (Units.ne_zero _)
        (Finsupp.mem_support_iff.mp hi),
       fun hi => Finsupp.mem_support_iff.mpr fun h =>
        hi (by rw [h, mul_zero])⟩⟩
  left_inv := fun f => by
    ext i
    change (((w i)⁻¹ : Kˣ) : K) * ((w i : K) * f i) = f i
    exact Units.inv_mul_cancel_left _ _
  right_inv := fun g => by
    ext i
    change (w i : K) * ((((w i)⁻¹ : Kˣ) : K) * g i) = g i
    exact Units.mul_inv_cancel_left _ _

/-- Diagonal scaling acts pointwise. -/
@[simp]
theorem diagLinearEquiv_apply (K : Type*) [Field K] {ι : Type*}
    (w : ι → Kˣ) (f : ι →₀ K) (i : ι) :
    diagLinearEquiv K w f i = (w i : K) * f i :=
  rfl

/-- Diagonal scaling sends `single a 1` to `single a (w a)`. -/
theorem diagLinearEquiv_single_one (K : Type*) [Field K] {ι : Type*}
    (w : ι → Kˣ) (a : ι) :
    diagLinearEquiv K w (Finsupp.single a 1)
      = Finsupp.single a (w a : K) := by
  classical
  ext i
  simp only [diagLinearEquiv_apply]
  by_cases h : i = a
  · subst h
    simp
  · rw [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h, mul_zero]

/-- A singleton with value `c` is `c` times the unit singleton. -/
theorem single_eq_smul_single_one (K : Type*) [Field K] {ι : Type*}
    (j : ι) (c : K) :
    Finsupp.single j c = c • Finsupp.single j 1 := by
  classical
  ext t
  by_cases h : t = j
  · subst h
    rw [Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  · rw [Finsupp.single_eq_of_ne h, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne h]
    simp

/-- The signed shift piece: dual basis element `ε_S` maps to the signed
complementary basis wedge `σ(S) • e_{Sᶜ}`. These are the degree maps of
the R-D2 shift iso.
-/
noncomputable def koszulShiftPieceSigned (K : Type*) [Field K] (m k : ℕ)
    (h : k ≤ m) :
    Module.Dual K ↥(⋀[K]^k (Fin m → K)) ≃ₗ[K] ↥(⋀[K]^(m - k) (Fin m → K)) :=
  ((((Pi.basisFun K (Fin m)).exteriorPower k).dualBasis).repr.trans
    (diagLinearEquiv K (hodgeSignWeight K m k))).trans
    ((Finsupp.domLCongr (powersetCardComplEquiv m k h)).trans
      (((Pi.basisFun K (Fin m)).exteriorPower (m - k)).repr.symm))

/-- The signed shift piece sends dual-basis elements to signed
complementary basis wedges.
-/
@[simp]
theorem koszulShiftPieceSigned_apply_dualBasis (K : Type*) [Field K]
    (m k : ℕ) (h : k ≤ m) (s : ↥(Set.powersetCard (Fin m) k)) :
    koszulShiftPieceSigned K m k h
        ((((Pi.basisFun K (Fin m)).exteriorPower k).dualBasis) s) =
      (hodgeSignWeight K m k s : K) •
        (((Pi.basisFun K (Fin m)).exteriorPower (m - k))
          (powersetCardComplEquiv m k h s)) := by
  simp only [koszulShiftPieceSigned, LinearEquiv.trans_apply,
    Module.Basis.repr_self, diagLinearEquiv_single_one,
    Finsupp.domLCongr_single]
  rw [single_eq_smul_single_one, map_smul]
  rw [← Module.Basis.repr_self
    (((Pi.basisFun K (Fin m)).exteriorPower (m - k)))
    (powersetCardComplEquiv m k h s)]
  rw [LinearEquiv.symm_apply_apply]

/-- The signed Hodge star: `⋀^k ≃ₗ ⋀^{m-k}` sending each exterior-power
basis wedge to the signed complementary basis wedge. This is R-D1 with
the compatibility-forcing sign.
-/
noncomputable def koszulHodgeSigned (K : Type*) [Field K] (m k : ℕ)
    (h : k ≤ m) :
    ↥(⋀[K]^k (Fin m → K)) ≃ₗ[K] ↥(⋀[K]^(m - k) (Fin m → K)) :=
  (((Pi.basisFun K (Fin m)).exteriorPower k).repr.trans
    (diagLinearEquiv K (hodgeSignWeight K m k))).trans
    ((Finsupp.domLCongr (powersetCardComplEquiv m k h)).trans
      (((Pi.basisFun K (Fin m)).exteriorPower (m - k)).repr.symm))

/-- The signed Hodge star sends basis wedges to signed complementary
basis wedges.
-/
@[simp]
theorem koszulHodgeSigned_apply_basis (K : Type*) [Field K]
    (m k : ℕ) (h : k ≤ m) (s : ↥(Set.powersetCard (Fin m) k)) :
    koszulHodgeSigned K m k h
        (((Pi.basisFun K (Fin m)).exteriorPower k) s) =
      (hodgeSignWeight K m k s : K) •
        (((Pi.basisFun K (Fin m)).exteriorPower (m - k))
          (powersetCardComplEquiv m k h s)) := by
  simp only [koszulHodgeSigned, LinearEquiv.trans_apply,
    Module.Basis.repr_self, diagLinearEquiv_single_one,
    Finsupp.domLCongr_single]
  rw [single_eq_smul_single_one, map_smul]
  rw [← Module.Basis.repr_self
    (((Pi.basisFun K (Fin m)).exteriorPower (m - k)))
    (powersetCardComplEquiv m k h s)]
  rw [LinearEquiv.symm_apply_apply]

/-- The signed degree maps on all degrees (zero beyond `m`), in the shape
`koszulShiftIso` consumes.
-/
noncomputable def koszulShiftPieceSignedMap (K : Type*) [Field K] (m k : ℕ) :
    Module.Dual K ↥(⋀[K]^k (Fin m → K)) →ₗ[K]
      ↥(⋀[K]^(m - k) (Fin m → K)) :=
  dite (k ≤ m) (fun hk => (koszulShiftPieceSigned K m k hk).toLinearMap)
    (fun _ => 0)

/-- The signed inverse degree maps on all degrees. -/
noncomputable def koszulShiftPieceSignedInvMap (K : Type*) [Field K]
    (m k : ℕ) :
    ↥(⋀[K]^(m - k) (Fin m → K)) →ₗ[K]
      Module.Dual K ↥(⋀[K]^k (Fin m → K)) :=
  dite (k ≤ m) (fun hk => (koszulShiftPieceSigned K m k hk).symm.toLinearMap)
    (fun _ => 0)

/-- On in-range degrees the signed map is the signed equiv. -/
theorem koszulShiftPieceSignedMap_of_le (K : Type*) [Field K] (m k : ℕ)
    (hk : k ≤ m) :
    koszulShiftPieceSignedMap K m k =
      (koszulShiftPieceSigned K m k hk).toLinearMap := by
  rw [koszulShiftPieceSignedMap, dite_eq_left hk]

/-- On in-range degrees the signed inverse map is the signed equiv inverse. -/
theorem koszulShiftPieceSignedInvMap_of_le (K : Type*) [Field K] (m k : ℕ)
    (hk : k ≤ m) :
    koszulShiftPieceSignedInvMap K m k =
      (koszulShiftPieceSigned K m k hk).symm.toLinearMap := by
  rw [koszulShiftPieceSignedInvMap, dite_eq_left hk]

/-- Left inverse law for the signed degree maps (feeds `koszulShiftIso`). -/
theorem koszulShiftPieceSigned_left (K : Type*) [Field K] (m k : ℕ)
    (hk : k ≤ m) :
    (koszulShiftPieceSignedInvMap K m k).comp
        (koszulShiftPieceSignedMap K m k) = LinearMap.id := by
  rw [koszulShiftPieceSignedMap_of_le K m k hk,
    koszulShiftPieceSignedInvMap_of_le K m k hk]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.id_apply]
  exact LinearEquiv.symm_apply_apply _ _

/-- Right inverse law for the signed degree maps (feeds `koszulShiftIso`). -/
theorem koszulShiftPieceSigned_right (K : Type*) [Field K] (m k : ℕ)
    (hk : k ≤ m) :
    (koszulShiftPieceSignedMap K m k).comp
        (koszulShiftPieceSignedInvMap K m k) = LinearMap.id := by
  rw [koszulShiftPieceSignedMap_of_le K m k hk,
    koszulShiftPieceSignedInvMap_of_le K m k hk]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.id_apply]
  exact LinearEquiv.apply_symm_apply _ _

/-! ## §10. The contraction Leibniz rule (engine of R-D2 compat) -/

/-- Tails commute with skipping a successor: deleting position `j'.succ`
then taking the tail is taking the tail then deleting position `j'`.
By cases on `i < j'`, via the `succAbove` unfolding lemmas.
-/
theorem vecTail_comp_succAbove_succ (M : Type*) [AddCommGroup M]
    {N : ℕ} (v : Fin (N + 1 + 1) → M) (j' : Fin (N + 1)) :
    Matrix.vecTail (v ∘ Fin.succAbove (j'.succ)) =
      (Matrix.vecTail v) ∘ Fin.succAbove j' := by
  funext i
  change v (Fin.succAbove (j'.succ) (i.succ)) = v ((Fin.succAbove j' i).succ)
  congr 1
  by_cases h : Fin.castSucc i < j'
  · have hiv : i.val < j'.val := h
    have hL : Fin.castSucc (i.succ) < j'.succ := by
      change (Fin.castSucc (i.succ)).val < (j'.succ).val
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    rw [Fin.succAbove_of_castSucc_lt _ _ hL,
      Fin.succAbove_of_castSucc_lt _ _ h, Fin.ext_iff]
    simp only [Fin.val_castSucc, Fin.val_succ]
  · have hle : j' ≤ Fin.castSucc i := le_of_not_gt h
    have hiv : j'.val ≤ i.val := hle
    have hL : j'.succ ≤ Fin.castSucc (i.succ) := by
      change (j'.succ).val ≤ (Fin.castSucc (i.succ)).val
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hL,
      Fin.succAbove_of_le_castSucc _ _ hle]

/-- Leibniz rule for `contractLeft` on decomposable wedges: contracting
`ιMulti v` sums over deleting each factor, with alternating signs from
the peel position. HilbertFunctionCount on `n`, peeling `v 0` via
`contractLeft_ι_mul`; the `j = 0` term has no sign, deeper terms pick up
one minus per peel.
-/
theorem contractLeft_ιMulti (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] R) (n : ℕ) (v : Fin n.succ → M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) φ
        (ExteriorAlgebra.ιMulti R n.succ v) =
      ∑ j : Fin n.succ, ((-1 : R)^(j.val) * φ (v j)) •
        ExteriorAlgebra.ιMulti R n (v ∘ Fin.succAbove j) := by
  induction n with
  | zero =>
    have hsplit := ExteriorAlgebra.ιMulti_succ_apply (R := R) v
    rw [hsplit, CliffordAlgebra.contractLeft_ι_mul,
      ExteriorAlgebra.ιMulti_zero_apply, CliffordAlgebra.contractLeft_one,
      mul_zero, sub_zero, Fin.sum_univ_one]
    simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ n ih =>
    have hsplit := ExteriorAlgebra.ιMulti_succ_apply (R := R) v
    rw [hsplit, CliffordAlgebra.contractLeft_ι_mul, ih (Matrix.vecTail v),
      Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    conv_rhs => rw [Fin.sum_univ_succ]
    have htail : Matrix.vecTail v = v ∘ Fin.succAbove 0 := by
      rw [Fin.succAbove_zero]
      rfl
    have hT0 : φ (v 0) • ExteriorAlgebra.ιMulti R (n.succ) (Matrix.vecTail v) =
        (((-1 : R)^((0 : Fin (n.succ).succ).val) * φ (v 0)) •
          ExteriorAlgebra.ιMulti R (n.succ) (v ∘ Fin.succAbove 0)) := by
      rw [htail]
      simp
    rw [hT0]
    congr 1
    apply Finset.sum_congr rfl
    intro j' _
    have hA : Fin.succAbove (j'.succ) 0 = 0 :=
      Fin.succAbove_ne_zero_zero (by simp)
    have hB := vecTail_comp_succAbove_succ M v j'
    have hX := ExteriorAlgebra.ιMulti_succ_apply (R := R)
      (v ∘ Fin.succAbove (j'.succ))
    rw [Function.comp_apply, hA, hB] at hX
    rw [hX, Algebra.mul_smul_comm, ← neg_smul]
    congr 1
    have hval : (j'.succ).val = j'.val + 1 := Fin.val_succ j'
    have hφ : φ ((Matrix.vecTail v) j') = φ (v (j'.succ)) := rfl
    rw [hval, hφ, pow_succ]
    ring

/-! ## §11. Compatibility: the signed star intertwines the differentials -/

/-- Card equation of a `powersetCard` element, with syntactic card type
(`s.2` has membership type, which poisons rewrites at implicit
transparency). -/
theorem powersetCard_card {m k : ℕ} (s : ↥(Set.powersetCard (Fin m) k)) :
    s.1.card = k :=
  s.2

/-- Membership from a card equation, with syntactic membership type (for
subtype constructors, dual to `powersetCard_card`). -/
theorem powersetCard_mem {m n : ℕ} {S : Finset (Fin m)}
    (h : S.card = n) : S ∈ Set.powersetCard (Fin m) n :=
  h

/-- Coe pushes through sums of exterior-power elements. -/
theorem exteriorPower_coe_sum (K : Type*) [Field K] (m n : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → ↥(⋀[K]^n (Fin m → K))) :
    ((∑ i ∈ s, f i : ↥(⋀[K]^n (Fin m → K))) :
      ExteriorAlgebra K (Fin m → K)) =
      ∑ i ∈ s, ((f i : ↥(⋀[K]^n (Fin m → K))) :
        ExteriorAlgebra K (Fin m → K)) :=
  map_sum (Submodule.subtype _) _ _

/-- Coe pushes through scalar multiples of exterior-power elements. -/
@[simp]
theorem exteriorPower_coe_smul (K : Type*) [Field K] (m n : ℕ)
    (c : K) (x : ↥(⋀[K]^n (Fin m → K))) :
    ((c • x : ↥(⋀[K]^n (Fin m → K))) : ExteriorAlgebra K (Fin m → K)) =
      c • ((x : ↥(⋀[K]^n (Fin m → K))) : ExteriorAlgebra K (Fin m → K)) :=
  map_smul (Submodule.subtype _) _ _

/-- Basis wedges are decomposable wedges of the ordered basis vectors. -/
theorem exteriorPower_basis_coe (K : Type*) [Field K] (m k : ℕ)
    (s : ↥(Set.powersetCard (Fin m) k)) :
    ((((Pi.basisFun K (Fin m)).exteriorPower k) s :
      ↥(⋀[K]^k (Fin m → K))) : ExteriorAlgebra K (Fin m → K)) =
      ExteriorAlgebra.ιMulti K k
        (⇑(Pi.basisFun K (Fin m)) ∘ s.1.orderEmbOfFin (powersetCard_card s)) := by
  rw [exteriorPower.basis_apply]
  rfl

/-- Erasing the `j`-th ordered element leaves `n` elements. -/
theorem erase_emb_card (m : ℕ) (S : Finset (Fin m)) {n : ℕ}
    (hS : S.card = n.succ) (j : Fin n.succ) :
    (S.erase (S.orderEmbOfFin hS j)).card = n := by
  have hmem : S.orderEmbOfFin hS j ∈ S := by
    rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin S hS]
    exact ⟨j, rfl⟩
  have h2 := Finset.card_erase_of_mem hmem
  omega

/-- Skipping position `j` in the ordered enumeration is the ordered
enumeration of the erased set (uniqueness of `orderEmbOfFin`). -/
theorem orderEmbOfFin_comp_succAbove (m : ℕ) (S : Finset (Fin m)) {n : ℕ}
    (hS : S.card = n.succ) (j : Fin n.succ) :
    S.orderEmbOfFin hS ∘ Fin.succAbove j =
      (S.erase (S.orderEmbOfFin hS j)).orderEmbOfFin
        (erase_emb_card m S hS j) := by
  refine Finset.orderEmbOfFin_unique (erase_emb_card m S hS j) ?_ ?_
  · intro x
    rw [Function.comp_apply]
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      have hinj := (S.orderEmbOfFin hS).strictMono.injective
      have hxx : Fin.succAbove j x = j := hinj heq
      exact Fin.succAbove_ne j x hxx
    · rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin S hS]
      exact ⟨_, rfl⟩
  · exact (S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove j)

/-- Contraction on basis wedges: delete each ordered factor in turn, with
alternating signs. Specializes the Leibniz rule via ordered-erasure
uniqueness.
-/
theorem koszulContract_basis (K : Type*) [Field K] (m n : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (s : ↥(Set.powersetCard (Fin m) (n.succ))) :
    koszulContract φ n (((Pi.basisFun K (Fin m)).exteriorPower (n.succ)) s) =
      ∑ j : Fin n.succ,
        ((-1 : K)^(j.val) *
            φ ((Pi.basisFun K (Fin m)) (s.1.orderEmbOfFin (powersetCard_card s) j))) •
          (((Pi.basisFun K (Fin m)).exteriorPower n)
            ⟨s.1.erase (s.1.orderEmbOfFin (powersetCard_card s) j),
              powersetCard_mem (erase_emb_card m s.1 (powersetCard_card s) j)⟩) := by
  apply Subtype.ext
  rw [koszulContract_apply, exteriorPower_basis_coe, contractLeft_ιMulti,
    exteriorPower_coe_sum]
  simp only [exteriorPower_coe_smul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply]
  have herase := orderEmbOfFin_comp_succAbove m s.1 (powersetCard_card s) j
  have hbridge : ExteriorAlgebra.ιMulti K n
      (⇑(Pi.basisFun K (Fin m)) ∘
        (s.1.erase (s.1.orderEmbOfFin (powersetCard_card s) j)).orderEmbOfFin
          (erase_emb_card m s.1 (powersetCard_card s) j)) =
      ↑((((Pi.basisFun K (Fin m)).exteriorPower n)
        ⟨s.1.erase (s.1.orderEmbOfFin (powersetCard_card s) j),
          powersetCard_mem (erase_emb_card m s.1 (powersetCard_card s) j)⟩) :
        ExteriorAlgebra K (Fin m → K)) :=
    (exteriorPower_basis_coe K m n
      ⟨s.1.erase (s.1.orderEmbOfFin (powersetCard_card s) j),
        powersetCard_mem (erase_emb_card m s.1 (powersetCard_card s) j)⟩).symm
  rw [Function.comp_assoc, herase, hbridge]

/-- Elements below `i` in `Fin m` number `i.val`. -/
theorem filter_lt_card (m : ℕ) (i : Fin m) :
    (Finset.univ.filter (· < i)).card = i.val := by
  have himg : Finset.image Fin.val (Finset.univ.filter (· < i)) =
      Finset.range i.val := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hx
      have hi := i.isLt
      refine ⟨⟨x, by omega⟩, ?_, rfl⟩
      exact hx
  have hcard := congrArg Finset.card himg
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  rw [Finset.card_range] at hcard
  exact hcard

/-- Position count: elements of `S` below the `j`-th ordered element
number `j.val`. -/
theorem orderEmbOfFin_filter_card (m : ℕ) (S : Finset (Fin m)) {n : ℕ}
    (hS : S.card = n.succ) (j : Fin n.succ) :
    (S.filter (· < S.orderEmbOfFin hS j)).card = j.val := by
  have himg : S.filter (· < S.orderEmbOfFin hS j) =
      Finset.image (S.orderEmbOfFin hS) (Finset.univ.filter (· < j)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have hxS : x ∈ S := hx.1
      rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin S hS] at hxS
      obtain ⟨j', hj'⟩ := hxS
      refine ⟨j', ?_, hj'⟩
      have hlt : S.orderEmbOfFin hS j' < S.orderEmbOfFin hS j := by
        rw [hj']
        exact hx.2
      exact (S.orderEmbOfFin hS).strictMono.lt_iff_lt.mp hlt
    · rintro ⟨j', hj', rfl⟩
      constructor
      · rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin S hS]
        exact ⟨_, rfl⟩
      · exact (S.orderEmbOfFin hS).strictMono.lt_iff_lt.mpr hj'
  rw [himg, Finset.card_image_of_injective _
    (S.orderEmbOfFin hS).strictMono.injective, filter_lt_card]

/-- Complementary position count. -/
theorem filter_compl_card (m : ℕ) (S : Finset (Fin m)) (i : Fin m) :
    ((Sᶜ).filter (· < i)).card = i.val - (S.filter (· < i)).card := by
  have hpart : Finset.univ.filter (· < i) =
      S.filter (· < i) ∪ (Sᶜ).filter (· < i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_compl]
    constructor
    · intro hx
      by_cases hxs : x ∈ S
      · exact Or.inl ⟨hxs, hx⟩
      · exact Or.inr ⟨hxs, hx⟩
    · rintro (⟨_, hx⟩ | ⟨_, hx⟩) <;> exact hx
  have hdisj : Disjoint (S.filter (· < i)) ((Sᶜ).filter (· < i)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_filter, Finset.mem_compl] at hx hx2
    exact hx2.1 hx.1
  have hcard := congrArg Finset.card hpart
  rw [filter_lt_card, Finset.card_union_of_disjoint hdisj] at hcard
  omega

/-- Position counts are bounded by the value. -/
theorem filter_card_le (m : ℕ) (S : Finset (Fin m)) (i : Fin m) :
    (S.filter (· < i)).card ≤ i.val := by
  have hsub : S.filter (· < i) ⊆ Finset.univ.filter (· < i) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.2
  have hle := Finset.card_le_card hsub
  rw [filter_lt_card] at hle
  exact hle

/-- Complement of insertion is erasure of complement. -/
theorem compl_insert_erase (m : ℕ) (S : Finset (Fin m)) (i : Fin m) :
    (insert i S)ᶜ = (Sᶜ).erase i := by
  ext x
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_erase, not_or]

/-- Inserting a missing element raises the card by one. -/
theorem insert_mem_card (m : ℕ) (S : Finset (Fin m)) {k : ℕ}
    (hS : S.card = k) (i : Fin m) (hi : i ∉ S) :
    (insert i S).card = k + 1 := by
  rw [Finset.card_insert_of_notMem hi, hS]

/-- The dual differential on dual-basis elements: transpose of contraction
sums over inserting each missing element, with position signs. By checking
on basis wedges: both sides select the unique insertion consistent with
the target (or vanish jointly when `S ⊄ T`).
-/
theorem koszulDualD_basis (K : Type*) [Field K] (m k : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (s : ↥(Set.powersetCard (Fin m) k)) :
    koszulDualD φ k ((((Pi.basisFun K (Fin m)).exteriorPower k).dualBasis) s) =
      ∑ i : ↥(s.1ᶜ), ((-1 : K)^((s.1.filter (· < i.1)).card) *
            φ ((Pi.basisFun K (Fin m)) i.1)) •
        ((((Pi.basisFun K (Fin m)).exteriorPower (k+1)).dualBasis)
          ⟨insert i.1 s.1, powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) i.1
            (Finset.mem_compl.mp i.2))⟩) := by
  refine Module.Basis.ext
    (((Pi.basisFun K (Fin m)).exteriorPower (k+1))) (fun T => ?_)
  rw [koszulDualD, LinearMap.dualMap_apply, koszulContract_basis]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.dualBasis_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  by_cases hsub : s.1 ⊆ T.1
  · have hne : s.1 ≠ T.1 := by
      intro heq
      have hcard := congrArg Finset.card heq
      have hs := powersetCard_card s
      have hTcard := powersetCard_card T
      omega
    have hssub : s.1 ⊂ T.1 := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    obtain ⟨e₀, he₀T, he₀S⟩ := Finset.exists_of_ssubset hssub
    have hT : T.1 = insert e₀ s.1 :=
      (Finset.eq_of_subset_of_card_le (s := insert e₀ s.1) (t := T.1)
        (by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxs
          · exact he₀T
          · exact hsub hxs)
        (by
          rw [insert_mem_card m s.1 (powersetCard_card s) e₀ he₀S]
          have hTcard := powersetCard_card T
          omega)).symm
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, T.1.orderEmbOfFin (powersetCard_card T) j₀ = e₀ := by
      have hmem : e₀ ∈ T.1 := he₀T
      rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin T.1 (powersetCard_card T)] at hmem
      obtain ⟨j₀, hj₀⟩ := hmem
      exact ⟨j₀, hj₀⟩
    have hLHS : (∑ j : Fin (k+1), ((-1 : K)^(j.val) *
            φ ((Pi.basisFun K (Fin m)) (T.1.orderEmbOfFin (powersetCard_card T) j))) •
          (if (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j),
              powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) j)⟩ :
              ↥(Set.powersetCard (Fin m) k)) = s then (1 : K) else 0)) =
        (-1 : K)^(j₀.val) *
          φ ((Pi.basisFun K (Fin m)) (T.1.orderEmbOfFin (powersetCard_card T) j₀)) := by
      have h0 : ∀ b ∈ (Finset.univ : Finset (Fin (k+1))), b ≠ j₀ →
          (((-1 : K)^(b.val) *
            φ ((Pi.basisFun K (Fin m)) (T.1.orderEmbOfFin (powersetCard_card T) b))) •
          (if (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) b),
              powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) b)⟩ :
              ↥(Set.powersetCard (Fin m) k)) = s then (1 : K) else 0)) = 0 := by
        intro b _ hbne
        have hne : (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) b),
            powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) b)⟩ :
            ↥(Set.powersetCard (Fin m) k)) ≠ s := by
          intro heq
          have hfin : T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) b) = s.1 :=
            congrArg Subtype.val heq
          by_cases hbe : T.1.orderEmbOfFin (powersetCard_card T) b = e₀
          · have hb0 : b = j₀ :=
              (T.1.orderEmbOfFin (powersetCard_card T)).strictMono.injective
                (by rw [hbe, hj₀])
            exact hbne hb0
          · exfalso
            have hmemT : e₀ ∈ T.1 := by
              rw [hT]
              exact Finset.mem_insert_self e₀ s.1
            have hmem : e₀ ∈ T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) b) := by
              rw [Finset.mem_erase]
              exact ⟨Ne.symm hbe, hmemT⟩
            rw [hfin] at hmem
            exact he₀S hmem
        rw [ite_eq_right hne]
        exact smul_zero _
      rw [Finset.sum_eq_single j₀ h0
        (fun h => absurd (Finset.mem_univ j₀) h)]
      have herase0 : (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j₀),
          powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) j₀)⟩ :
          ↥(Set.powersetCard (Fin m) k)) = s := by
        apply Subtype.ext
        change T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j₀) = s.1
        rw [hj₀, hT]
        exact Finset.erase_insert he₀S
      rw [ite_eq_left herase0, smul_eq_mul, mul_one]
    have hRHS : (∑ i : ↥(s.1ᶜ), ((-1 : K)^((s.1.filter (· < i.1)).card) *
            φ ((Pi.basisFun K (Fin m)) i.1)) •
          (if T = (⟨insert i.1 s.1,
            powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) i.1
              (Finset.mem_compl.mp i.2))⟩ :
              ↥(Set.powersetCard (Fin m) (k+1))) then (1 : K) else 0)) =
        (-1 : K)^((s.1.filter (· < e₀)).card) *
          φ ((Pi.basisFun K (Fin m)) e₀) := by
      have hi₀ : e₀ ∈ s.1ᶜ := Finset.mem_compl.mpr he₀S
      have h0 : ∀ b ∈ (Finset.univ : Finset ↥(s.1ᶜ)), b ≠ ⟨e₀, hi₀⟩ →
          (((-1 : K)^((s.1.filter (· < b.1)).card) *
            φ ((Pi.basisFun K (Fin m)) b.1)) •
          (if T = (⟨insert b.1 s.1,
            powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) b.1
              (Finset.mem_compl.mp b.2))⟩ :
              ↥(Set.powersetCard (Fin m) (k+1))) then (1 : K) else 0)) = 0 := by
        intro b _ hbne
        have hne : T ≠ (⟨insert b.1 s.1,
          powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) b.1
            (Finset.mem_compl.mp b.2))⟩ :
            ↥(Set.powersetCard (Fin m) (k+1))) := by
          intro heq
          have hfin : T.1 = insert b.1 s.1 := congrArg Subtype.val heq
          have hb1 : b.1 = e₀ := by
            have hmem : b.1 ∈ insert e₀ s.1 := by
              rw [← hT, hfin]
              exact Finset.mem_insert_self b.1 s.1
            simp only [Finset.mem_insert] at hmem
            rcases hmem with h | hmemS
            · exact h
            · exact absurd hmemS (Finset.mem_compl.mp b.2)
          have hbeq : b = (⟨e₀, hi₀⟩ : ↥(s.1ᶜ)) := Subtype.ext hb1
          exact hbne hbeq
        rw [ite_eq_right hne]
        exact smul_zero _
      rw [Finset.sum_eq_single (⟨e₀, hi₀⟩ : ↥(s.1ᶜ)) h0
        (fun h => absurd (Finset.mem_univ (⟨e₀, hi₀⟩ : ↥(s.1ᶜ))) h)]
      have hins0 : T = (⟨insert e₀ s.1,
        powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) e₀
          (Finset.mem_compl.mp hi₀))⟩ :
          ↥(Set.powersetCard (Fin m) (k+1))) := by
        apply Subtype.ext
        change T.1 = insert e₀ s.1
        exact hT
      rw [ite_eq_left hins0, smul_eq_mul, mul_one]
    rw [hLHS, hRHS]
    have hpos : j₀.val = (s.1.filter (· < e₀)).card := by
      have hTpos := orderEmbOfFin_filter_card m T.1 (powersetCard_card T) j₀
      rw [hj₀] at hTpos
      have hfil : T.1.filter (· < e₀) = s.1.filter (· < e₀) := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · intro hx
          have hxT : x ∈ insert e₀ s.1 := by rw [← hT]; exact hx.1
          simp only [Finset.mem_insert] at hxT
          rcases hxT with rfl | hxs
          · exact (ne_of_lt hx.2 rfl).elim
          · exact ⟨hxs, hx.2⟩
        · intro hx
          exact ⟨hsub hx.1, hx.2⟩
      rw [hfil] at hTpos
      exact hTpos.symm
    rw [hj₀, hpos]
  · have hL0 : (∑ j : Fin (k+1), ((-1 : K)^(j.val) *
          φ ((Pi.basisFun K (Fin m)) (T.1.orderEmbOfFin (powersetCard_card T) j))) •
        (if (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j),
            powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) j)⟩ :
            ↥(Set.powersetCard (Fin m) k)) = s then (1 : K) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hne : (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j),
          powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) j)⟩ :
          ↥(Set.powersetCard (Fin m) k)) ≠ s := by
        intro heq
        have hfin : T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j) = s.1 :=
          congrArg Subtype.val heq
        have hsub' : s.1 ⊆ T.1 := by
          rw [← hfin]
          exact Finset.erase_subset _ _
        exact hsub hsub'
      rw [ite_eq_right hne]
      exact smul_zero _
    have hR0 : (∑ i : ↥(s.1ᶜ), ((-1 : K)^((s.1.filter (· < i.1)).card) *
          φ ((Pi.basisFun K (Fin m)) i.1)) •
        (if T = (⟨insert i.1 s.1, powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) i.1
            (Finset.mem_compl.mp i.2))⟩ :
            ↥(Set.powersetCard (Fin m) (k+1))) then (1 : K) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hne : T ≠ (⟨insert i.1 s.1,
        powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) i.1
          (Finset.mem_compl.mp i.2))⟩ :
          ↥(Set.powersetCard (Fin m) (k+1))) := by
        intro heq
        have hfin : T.1 = insert i.1 s.1 := congrArg Subtype.val heq
        have hsub' : s.1 ⊆ T.1 := by
          rw [hfin]
          exact Finset.subset_insert _ _
        exact hsub hsub'
      rw [ite_eq_right hne]
      exact smul_zero _
    rw [hL0, hR0]

/-! ## §12. Shift compatibility and the unconditional shift iso (R-D2)

The signed shift piece satisfies `koszulShiftCompat`: on dual-basis
elements both sides expand (§11) into sums matched by complement
reindexing, with `neg_one_pow_sub_add` absorbing the
contraction-position signs into the Hodge weights. Instantiating the
conditional
`koszulShiftIso` (§8) gives the unconditional `Hom(K, R) ≅ K[m]`.

References: `LinearAlgebra/Dual/Basis.lean` (`Module.Basis.dualBasis`,
`Module.Basis.ext`), `Algebra/BigOperators/Group/Finset/Defs.lean`
(`Fintype.sum_bijective`), `Algebra/BigOperators/GroupWithZero/Action.lean`
(`Finset.smul_sum`), `Data/Finset/Sort.lean` (`orderIsoOfFin`),
`Algebra/Ring/Units.lean` (`Units.coe_neg_one`).
-/

/-- Transport of a graded linear map along a countdown index equation,
applied to a vector: the cast moves to the argument. Generalizes the
named equation (cf. `koszulShiftD_comp_aux`) so `cases` clears it.
-/
theorem koszulShiftD_apply_aux (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (a b : ℕ) (e : a + 1 = b)
    (x : ↥(⋀[K]^b (Fin m → K))) :
    (e ▸ koszulContract φ a) x = koszulContract φ a (e.symm ▸ x) := by
  cases e
  rfl

/-- The shift differential applied to a vector is the contraction applied
to the cast vector.
-/
theorem koszulShiftD_apply (K : Type*) [Field K] (m k : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) (h : k + 1 ≤ m)
    (x : ↥(⋀[K]^(m - k) (Fin m → K))) :
    koszulShiftD K m k φ h x =
      koszulContract φ (m - (k + 1))
        ((koszulShiftD_index_eq m k h).symm ▸ x) := by
  unfold koszulShiftD
  exact koszulShiftD_apply_aux K m φ _ _ (koszulShiftD_index_eq m k h) x

/-- Casts commute with scalar multiplication (for transporting the signed
basis expansion across `koszulShiftD_index_eq`).
-/
theorem cast_smul_exteriorPower (K : Type*) [Field K] {m a b : ℕ}
    (e : a = b) (c : K) (v : ↥(⋀[K]^a (Fin m → K))) :
    (e ▸ (c • v)) = c • (e ▸ v) := by
  cases e
  rfl

/-- Casts commute with exterior-power basis elements (index cast alongside).
-/
theorem cast_exteriorPower_basis (K : Type*) [Field K] {m a b : ℕ}
    (e : a = b) (s : ↥(Set.powersetCard (Fin m) a)) :
    (e ▸ ((Pi.basisFun K (Fin m)).exteriorPower a) s) =
      ((Pi.basisFun K (Fin m)).exteriorPower b) ⟨s.1, e ▸ s.2⟩ := by
  cases e
  rfl

/-- The Hodge sign weight coerced to `K` is `(-1)` to the index sum.
-/
theorem hodgeSignWeight_coe (K : Type*) [Field K] (m k : ℕ)
    (s : ↥(Set.powersetCard (Fin m) k)) :
    ((hodgeSignWeight K m k s : Kˣ) : K) =
      (-1 : K)^(s.1.sum fun i => i.val) := by
  simp [hodgeSignWeight]

/-- The coerced sign weight of an inserted set splits off the new factor.
-/
theorem hodgeSignWeight_coe_insert (K : Type*) [Field K] (m k : ℕ)
    (S : Finset (Fin m)) (a : Fin m) (hi : a ∉ S)
    (hmem : insert a S ∈ Set.powersetCard (Fin m) (k + 1)) :
    ((hodgeSignWeight K m (k + 1) ⟨insert a S, hmem⟩ : Kˣ) : K) =
      (-1 : K)^(S.sum fun j => j.val) * (-1 : K)^(a.val) := by
  simp only [hodgeSignWeight, Units.val_pow_eq_pow_val, Units.coe_neg_one]
  change (-1 : K)^((insert a S).sum fun j => j.val) =
    (-1 : K)^(S.sum fun j => j.val) * (-1 : K)^(a.val)
  exact neg_one_pow_sum_insert K m S a hi

/-- The signed shift piece satisfies shift compatibility
(`koszulShiftCompat`): transpose-of-contraction equals
contraction-up-to-star. Both sides are expanded on dual-basis elements
(`koszulDualD_basis`, `koszulContract_basis`), the contraction sum is
reindexed over the complement (`Fintype.sum_bijective` along
`orderIsoOfFin`), and each pair of terms agrees by
`neg_one_pow_sub_add` (`ring`) on scalars and
`compl_insert_erase` on basis vectors. This discharges the R-D2 residual.
-/
theorem koszulShiftCompat_signed (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) :
    koszulShiftCompat K m φ (koszulShiftPieceSignedMap K m) := by
  intro k h
  have hk : k ≤ m := by omega
  refine Module.Basis.ext
    (((Pi.basisFun K (Fin m)).exteriorPower k).dualBasis) (fun s => ?_)
  simp only [LinearMap.comp_apply]
  rw [koszulShiftPieceSignedMap_of_le K m k hk]
  simp only [LinearEquiv.coe_coe, koszulShiftPieceSigned_apply_dualBasis]
  rw [koszulShiftD_apply, cast_smul_exteriorPower, cast_exteriorPower_basis,
    map_smul]
  change ↑(hodgeSignWeight K m k s) •
        koszulContract φ (m - (k + 1))
          (((Pi.basisFun K (Fin m)).exteriorPower ((m - (k + 1)).succ))
            (⟨(powersetCardComplEquiv m k hk s).1,
              (koszulShiftD_index_eq m k h).symm ▸
                (powersetCardComplEquiv m k hk s).2⟩ :
              ↥(Set.powersetCard (Fin m) (m - (k + 1) + 1)))) =
      (koszulShiftPieceSignedMap K m (k + 1))
        (koszulDualD φ k
          ((((Pi.basisFun K (Fin m)).exteriorPower k).dualBasis) s))
  rw [koszulContract_basis]
  rw [koszulDualD_basis, koszulShiftPieceSignedMap_of_le K m (k + 1) h]
  simp only [map_sum, map_smul, LinearEquiv.coe_coe,
    koszulShiftPieceSigned_apply_dualBasis]
  have hcard : s.1ᶜ.card = (m - (k + 1)).succ := by
    rw [Finset.card_compl, Fintype.card_fin, powersetCard_card s]
    omega
  rw [Finset.smul_sum]
  refine Fintype.sum_bijective ⇑((s.1ᶜ.orderIsoOfFin hcard).toEquiv)
    ((s.1ᶜ.orderIsoOfFin hcard).toEquiv.bijective) _ _ (fun j => ?_)
  have hunit : ∀ (u : Kˣ) (x : ↥(⋀[K]^(m - (k + 1)) (Fin m → K))),
      u • x = (u : K) • x := fun u x => rfl
  simp only [hunit, smul_smul]
  have hi : (((s.1ᶜ.orderIsoOfFin hcard).toEquiv j).1) ∉ s.1 :=
    Finset.mem_compl.mp (((s.1ᶜ.orderIsoOfFin hcard).toEquiv j).2)
  have hsign := hodgeSignWeight_coe_insert K m k s.1
    (((s.1ᶜ.orderIsoOfFin hcard).toEquiv j).1) hi
    (powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s)
      (((s.1ᶜ.orderIsoOfFin hcard).toEquiv j).1)
      (Finset.mem_compl.mp (((s.1ᶜ.orderIsoOfFin hcard).toEquiv j).2))))
  have hcount :
      j.val + (s.1.filter (· < s.1ᶜ.orderEmbOfFin hcard j)).card =
        (s.1ᶜ.orderEmbOfFin hcard j).val := by
    have h1 := orderEmbOfFin_filter_card m s.1ᶜ hcard j
    have h2 := filter_compl_card m s.1 (s.1ᶜ.orderEmbOfFin hcard j)
    have hle := filter_card_le m s.1 (s.1ᶜ.orderEmbOfFin hcard j)
    omega
  have hkey :
      (-1 : K)^(s.1.sum fun i => i.val) *
          ((-1 : K)^(j.val) *
            φ ((Pi.basisFun K (Fin m)) (s.1ᶜ.orderEmbOfFin hcard j))) =
        (((-1 : K)^((s.1.filter (· < s.1ᶜ.orderEmbOfFin hcard j)).card) *
          φ ((Pi.basisFun K (Fin m)) (s.1ᶜ.orderEmbOfFin hcard j))) *
          ((-1 : K)^(s.1.sum fun i => i.val) *
            (-1 : K)^((s.1ᶜ.orderEmbOfFin hcard j).val))) := by
    have hj' : j.val = (s.1ᶜ.orderEmbOfFin hcard j).val -
        (s.1.filter (· < s.1ᶜ.orderEmbOfFin hcard j)).card := by omega
    have hle : (s.1.filter (· < s.1ᶜ.orderEmbOfFin hcard j)).card ≤
        (s.1ᶜ.orderEmbOfFin hcard j).val := by omega
    rw [hj', neg_one_pow_sub_add K _ _ hle, pow_add]
    ring
  rw [hsign, hodgeSignWeight_coe]
  refine congrArg₂ _ hkey ?_
  refine congrArg _ (Subtype.ext ?_)
  change (s.1ᶜ).erase (s.1ᶜ.orderEmbOfFin hcard j) =
    (insert (s.1ᶜ.orderEmbOfFin hcard j) s.1)ᶜ
  rw [compl_insert_erase]

/-- The R-D2 shift iso `Hom(K, R) ≅ K[m]` as complexes, unconditional:
`koszulShiftIso` (§8) instantiated with the signed degree maps, whose
compatibility (`koszulShiftCompat_signed`) and inverse laws
(`koszulShiftPieceSigned_left/right`) discharge the residual. This is the
exact shape A5.2 Ext-vanishing consumes.
-/
noncomputable def koszulShiftIsoSigned (K : Type*) [Field K] (m : ℕ)
    (φ : (Fin m → K) →ₗ[K] K) :
    (koszulDualComplex φ) ≅ (koszulShiftComplex K m φ) :=
  koszulShiftIso K m φ (koszulShiftPieceSignedMap K m)
    (koszulShiftPieceSignedInvMap K m) (koszulShiftCompat_signed K m φ)
    (fun k hk => koszulShiftPieceSigned_left K m k hk)
    (fun k hk => koszulShiftPieceSigned_right K m k hk)

end SelfDuality
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

-- Note: Lean 4 `universe` commands *replace* (not accumulate) the in-scope
-- universe variables, so this must re-list `uShiftObj` (declared §7, still
-- used by the §14 commring mirror) alongside the new `uRD3`.
universe uShiftObj uRD3

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SelfDuality

open CategoryTheory KoszulComplex ExtComparison

/-! ## §13. Ext-vanishing below the sop length (R-D3, conditional assembly)

Step A5 part 2 of the scoped Koszul/AB plan: from the Koszul projective
resolution (ExtComp) plus chain-level Hom-exactness below `d`, every
`Ext^i(X, Y)` with `i < d` is a subsingleton. A6 (Rees assembly →
`DepthEqDimAt`) instantiates `X := ↧(Shrink (R_P ⧸ m))` (residue field),
`Y := R_P`, `n := d` and feeds the conclusion into
`ModuleCat.exists_isRegular_tfae` condition (2).

Proof idea: every class is a `koszulExtMk` (surjectivity); at positive
degree a class is zero iff its cocycle is a coboundary
(`koszulExtMk_eq_zero_iff`), which is exactly the
`koszulHomCocycleExactBelow` hypothesis; at degree 0 the cocycle is zero
by `koszulHomZeroExact`, and `extMk` of zero is zero (`extMk_zero`).

Residual ledger (all explicit hypotheses, nothing assumed):
(a) the R2 pair `(π, QuasiIso π)` in the exact `ExtComparison` shape —
being built in the A4 series, not proved here;
(b) the shift+R2 bridge: `koszulHomCocycleExactBelow` +
`koszulHomZeroExact` are the chain-level content of "`Hom(K, R) ≅ K[d]`
transports R2 exactness", discharged once the shift iso exists over the
base ring plus homology transport. (The shift-iso half is closed by §14
`koszulShiftIsoSigned_commRing`; §12's iso alone is field-only.)
Stating them at chain level (about `K`, `f`, `g` — never about `Ext`)
makes the assembly a genuine reduction, not a restatement.

References: `Regularity/Koszul/ExtComparison.lean` (`koszulProjectiveResolution`,
`koszulExtMk`, `koszulExtMk_eq_zero_iff`, `koszulExtMk_surjective`),
Mathlib `CategoryTheory/Abelian/Projective/Ext.lean` (`extMk_zero`),
(`extMk_eq_zero_iff`) (`extMk_surjective`),
`RingTheory/Depth/Rees.lean` (`ModuleCat.exists_isRegular_tfae`).
-/

/-- Chain-level Hom-exactness below degree `d` at positive degrees (the
shift+R2 bridge content as an explicit residual, in the
`koszulShiftCompat` pattern): every Koszul cocycle of positive degree
`i < d` is a coboundary.

Conditional hypothesis (explicit residual for the shift+R2 bridge). -/
def koszulHomCocycleExactBelow {R M : Type uRD3} [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] R) {Y : ModuleCat.{uRD3} R} (d : ℕ) : Prop :=
  ∀ (i : ℕ) (_hi1 : 1 ≤ i) (_hid : i < d) (f : (koszulChainComplex φ).X i ⟶ Y)
    (m : ℕ) (_hm : i + 1 = m), (koszulChainComplex φ).d m i ≫ f = 0 →
    ∀ (p : ℕ) (_hp : p + 1 = i),
      ∃ g : (koszulChainComplex φ).X p ⟶ Y,
        (koszulChainComplex φ).d i p ≫ g = f

/-- Degree-0 base case (chain-level Hom-vanishing): every 0-cocycle is zero.
Discharged by the same bridge at top degree (`H^0(Hom) ≅ H_d(K) = 0` for
`d ≥ 1` once the shift iso exists over the base ring).

Conditional hypothesis (explicit residual for the shift+R2 bridge). -/
def koszulHomZeroExact {R M : Type uRD3} [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] R) {Y : ModuleCat.{uRD3} R} : Prop :=
  ∀ (f : (koszulChainComplex φ).X 0 ⟶ Y),
    (koszulChainComplex φ).d 1 0 ≫ f = 0 → f = 0

/-- Every positive-degree Ext class below `d` is zero: surjectivity exhibits
the class as a `koszulExtMk`, and `koszulExtMk_eq_zero_iff` turns the
chain-level coboundary witness from `koszulHomCocycleExactBelow` into
vanishing.

Conditional on exactly `(π, QuasiIso π)` (R2) + `koszulHomCocycleExactBelow`. -/
theorem koszulExt_eq_zero_of_homExact {R M : Type uRD3} [CommRing R]
    [AddCommGroup M] [Module R M] {I : Type uRD3} [LinearOrder I]
    (b : Module.Basis I R M) (φ : M →ₗ[R] R) {X Y : ModuleCat.{uRD3} R}
    (π : koszulChainComplex φ ⟶ (ChainComplex.single₀ _).obj X)
    (hπ : QuasiIso π) {d i : ℕ} (hi1 : 1 ≤ i) (hid : i < d)
    (hHom : koszulHomCocycleExactBelow φ (Y := Y) d)
    (α : Abelian.Ext X Y i) : α = 0 := by
  obtain ⟨f, hf, rfl⟩ :=
    koszulExtMk_surjective b φ π hπ α (i + 1) rfl
  exact (koszulExtMk_eq_zero_iff b φ π hπ f (i + 1) rfl hf (i - 1)
    (by omega)).mpr (hHom i hi1 hid f (i + 1) rfl hf (i - 1) (by omega))

/-- Every degree-0 Ext class is zero once 0-cocycles vanish: the class is a
`koszulExtMk` whose cocycle is zero by `koszulHomZeroExact`, and `extMk`
of the zero cocycle is zero.

Conditional on exactly `(π, QuasiIso π)` (R2) + `koszulHomZeroExact`. -/
theorem koszulExtZero_eq_zero_of_homZeroExact {R M : Type uRD3} [CommRing R]
    [AddCommGroup M] [Module R M] {I : Type uRD3} [LinearOrder I]
    (b : Module.Basis I R M) (φ : M →ₗ[R] R) {X Y : ModuleCat.{uRD3} R}
    (π : koszulChainComplex φ ⟶ (ChainComplex.single₀ _).obj X)
    (hπ : QuasiIso π) (h0 : koszulHomZeroExact φ (Y := Y))
    (α : Abelian.Ext X Y 0) : α = 0 := by
  obtain ⟨f, hf, rfl⟩ := koszulExtMk_surjective b φ π hπ α 1 rfl
  have hf0 : f = 0 := h0 f hf
  subst hf0
  exact ProjectiveResolution.extMk_zero
    (R := koszulProjectiveResolution b φ X π hπ) 1 rfl

/-- R-D3 master (A5.2 Ext-vanishing) in the exact shape A6 Rees assembly
consumes (`ModuleCat.exists_isRegular_tfae` condition (2)):
`Ext^i(X, Y)` is a subsingleton for all `i < d`. A6 instantiates
`X := ↧(Shrink (R_P ⧸ m))`, `Y := R_P`, `n := d`.

Conditional on exactly `(π, QuasiIso π)` (R2, ExtComp shape) +
`koszulHomCocycleExactBelow` + `koszulHomZeroExact` (shift+R2 bridge). -/
theorem koszulExt_subsingleton_below_of_homExact {R M : Type uRD3} [CommRing R]
    [AddCommGroup M] [Module R M] {I : Type uRD3} [LinearOrder I]
    (b : Module.Basis I R M) (φ : M →ₗ[R] R) {X Y : ModuleCat.{uRD3} R}
    (π : koszulChainComplex φ ⟶ (ChainComplex.single₀ _).obj X)
    (hπ : QuasiIso π) {d : ℕ}
    (hHom : koszulHomCocycleExactBelow φ (Y := Y) d)
    (h0 : koszulHomZeroExact φ (Y := Y)) :
    ∀ (i : ℕ) (_ : i < d), Subsingleton (Abelian.Ext X Y i) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact ⟨fun α β => (koszulExtZero_eq_zero_of_homZeroExact b φ π hπ h0 α).trans
      (koszulExtZero_eq_zero_of_homZeroExact b φ π hπ h0 β).symm⟩
  · exact ⟨fun α β => (koszulExt_eq_zero_of_homExact b φ π hπ hpos hi hHom α).trans
      (koszulExt_eq_zero_of_homExact b φ π hπ hpos hi hHom β).symm⟩

/-- Sequence form of the R-D3 master: `K(x)` for `x : Fin d → R` (the
`K(sop)` shape with sop length `d`), otherwise identical to
`koszulExt_subsingleton_below_of_homExact`.

Conditional on exactly `(π, QuasiIso π)` (R2, sequence shape) +
`koszulHomCocycleExactBelow` + `koszulHomZeroExact` (shift+R2 bridge). -/
theorem koszulExt_subsingleton_below_ofSequence {R : Type uRD3} [CommRing R]
    {I : Type uRD3} [LinearOrder I] {d : ℕ}
    (b : Module.Basis I R (Fin d → R)) (x : Fin d → R)
    {X Y : ModuleCat.{uRD3} R}
    (π : koszulChainComplexOfSequence x ⟶ (ChainComplex.single₀ _).obj X)
    (hπ : QuasiIso π)
    (hHom : koszulHomCocycleExactBelow (koszulContractOfSequence x) (Y := Y) d)
    (h0 : koszulHomZeroExact (koszulContractOfSequence x) (Y := Y)) :
    ∀ (i : ℕ) (_ : i < d), Subsingleton (Abelian.Ext X Y i) :=
  koszulExt_subsingleton_below_of_homExact b (koszulContractOfSequence x)
    π hπ hHom h0

end SelfDuality
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SelfDuality

open CategoryTheory KoszulComplex

/-! ## §14. CommRing shift iso for finite-free modules (R-D4)

Field-only upgrade of §§5–12: over a commutative ring `R` with `M` free of
rank `m` (explicit basis `b : Module.Basis (Fin m) R M` — the sop Koszul
complex is over the free module `Fin d → R`, so dual bases exist with no
field needed), the signed shift iso `Hom(K, R) ≅ K[m]` holds in the exact
shape §13 consumes. The target application is `R := R_P` (a local ring,
still a `CommRing`) with `M := Fin d → R`.

Proof strategy: mirror §§5–12 with `K → R`, `Field K → CommRing R`,
`Pi.basisFun → b`. Every Mathlib lemma consumed there is already
ring-general except two spots, fixed here:
* diagonal scaling (`diagLinearEquiv_commRing`): the support argument used
  `mul_ne_zero` (needs `NoZeroDivisors`); over a general `CommRing` it uses
  `Units.mul_right_eq_zero` (unit multiplication reflects zero, no
  hypotheses beyond `MonoidWithZero`).
* out-of-range vanishing (`exteriorPower_subsingleton_of_gt_commRing`):
  the field proof used `finrank` + inverses; over a `CommRing` the
  `k > m` exterior power is a subsingleton because its basis index type
  `↥(Set.powersetCard (Fin m) k)` is empty, transported along
  `(b.exteriorPower k).repr`.
All ring-independent combinatorics (`powersetCardComplEquiv`,
`koszulShiftD_index_eq`, `eqToHom_middle_junction`, the §10 Leibniz rule,
the §11 position-count/ordered-erasure lemmas) are reused as-is.

Deliverables: `koszulShiftIsoSigned_commRing` (general finite-free form)
and `koszulShiftIsoSigned_commRing_ofSequence` (`K(sop)` sequence form over
`Fin m → R`, the exact vehicle for transporting R2 exactness over `R_P`).
The remaining bridge half is homology transport (open, assigned to the
`HomologyTransport.lean` follow-up): applying `HomologicalComplex.homology`
to this iso maps `H^i(Hom(K,R)) ≅ H^i(K[m])`, and A4 exactness kills the
right side below the sop length.

References (new Mathlib pointers beyond §§5–12):
* `Algebra/GroupWithZero/Units/Basic.lean`: `Units.mul_right_eq_zero`.
* `Data/Fintype/Card.lean`: `Finset.card_le_univ`.
-/

/-! ### §14a. The shift target complex over a `CommRing` (mirror of §7) -/

/-- The objects of the shift target complex over a `CommRing`: `⋀^{m-i}` in
degrees `i ≤ m`, the zero module `PUnit` beyond (mirror of
`koszulShiftObj`; the case split is forced for the same rank reason, and
universe-polymorphic `PUnit` — Mathlib's canonical `ModuleCat` zero
object — keeps both branches in one universe).
-/
def koszulShiftObj_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m i : ℕ) : ModuleCat R :=
  if i ≤ m then ModuleCat.of R ↥(⋀[R]^(m - i) M)
  else ModuleCat.of R PUnit

/-- The in-range objects are the exterior powers (stated with folded
`koszulShiftObj_commRing` so `eqToHom` transports stay type-correct).
-/
theorem koszulShiftObj_commRing_eq_of_le (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m i : ℕ)
    (hi : i ≤ m) :
    koszulShiftObj_commRing R M m i =
      ModuleCat.of R ↥(⋀[R]^(m - i) M) := by
  rw [koszulShiftObj_commRing, ite_eq_left hi]

/-- The shift-target differential at degree `k`: the Koszul contraction,
transported from countdown index `m - (k+1)` to `m - k` (mirror of
`koszulShiftD`).
-/
def koszulShiftD_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (φ : M →ₗ[R] R) (h : k + 1 ≤ m) :
    ↥(⋀[R]^(m - k) M) →ₗ[R] ↥(⋀[R]^(m - (k + 1)) M) :=
  (koszulShiftD_index_eq m k h) ▸ koszulContract φ (m - (k + 1))

/-- The shift differential transported along the shape equation `i + 1 = j`
and the object case splits (via `eqToHom`), so it can serve as the `d i j`
morphism (mirror of `koszulShiftAt`).
-/
def koszulShiftAt_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ) (φ : M →ₗ[R] R)
    (i j : ℕ) (h : i + 1 = j) (hle : i + 1 ≤ m) :
    koszulShiftObj_commRing R M m i ⟶ koszulShiftObj_commRing R M m j :=
  eqToHom (koszulShiftObj_commRing_eq_of_le R M m i (show i ≤ m from by omega)) ≫
    (h ▸ ModuleCat.ofHom (koszulShiftD_commRing R M m i φ hle)) ≫
      eqToHom (koszulShiftObj_commRing_eq_of_le R M m j (h ▸ hle)).symm

/-- The complex morphisms: the shift differential on consecutive degrees
within range, zero elsewhere. -/
def koszulShiftMor_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ) (φ : M →ₗ[R] R)
    (i j : ℕ) : koszulShiftObj_commRing R M m i ⟶ koszulShiftObj_commRing R M m j :=
  dite (i + 1 = j) (fun h => dite (i + 1 ≤ m)
    (fun hle => koszulShiftAt_commRing R M m φ i j h hle) (fun _ => 0))
    (fun _ => 0)

/-- On consecutive in-range degrees the morphism is the shift differential. -/
theorem koszulShiftMor_commRing_succ_of_le (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ) (φ : M →ₗ[R] R)
    (i : ℕ) (hle : i + 1 ≤ m) :
    koszulShiftMor_commRing R M m φ i (i + 1) =
      koszulShiftAt_commRing R M m φ i (i + 1) rfl hle := by
  rw [koszulShiftMor_commRing, dite_eq_left rfl, dite_eq_left hle]

/-- On consecutive out-of-range degrees the morphism is zero. -/
theorem koszulShiftMor_commRing_succ_off (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ) (φ : M →ₗ[R] R)
    (i : ℕ) (hle : ¬ i + 1 ≤ m) :
    koszulShiftMor_commRing R M m φ i (i + 1) = 0 := by
  rw [koszulShiftMor_commRing, dite_eq_left rfl, dite_eq_right hle]

/-- Transported contractions compose to zero: the generic form of the
in-range `d² = 0`, with the index equations as hypotheses over variables
(mirror of `koszulShiftD_comp_aux`).
-/
theorem koszulShiftD_comp_aux_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] R) (a b c : ℕ) (e1 : b + 1 = a)
    (e2 : c + 1 = b) :
    ((e2 ▸ koszulContract φ c).comp (e1 ▸ koszulContract φ b)) = 0 := by
  cases e1
  cases e2
  change (koszulContract φ c).comp (koszulContract φ (c + 1)) = 0
  exact koszulContract_comp φ c

/-- Reassociation junction for `ofHom` pairs in right-nested form over a
`CommRing` (mirror of `ofHom_comp_middle`).
-/
theorem ofHom_comp_middle_commRing (R : Type*) [CommRing R]
    {M N O : Type uShiftObj} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup O] [Module R O]
    (l1 : M →ₗ[R] N) (l2 : N →ₗ[R] O) {E : ModuleCat R}
    (g : ModuleCat.of R O ⟶ E) :
    ModuleCat.ofHom l1 ≫ (ModuleCat.ofHom l2 ≫ g) =
      ModuleCat.ofHom (l2.comp l1) ≫ g := by
  rw [← Category.assoc, ModuleCat.ofHom_comp]

/-- Consecutive morphisms compose to zero (mirror of
`koszulShiftMor_comp_zero`: middle-`eqToHom` cancellation, `rfl` shape
transports, then `koszulContract_comp` via the named index equations).
-/
theorem koszulShiftMor_comp_zero_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R) (i j k : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j)
    (hjk : (ComplexShape.up ℕ).Rel j k) :
    koszulShiftMor_commRing R M m φ i j ≫ koszulShiftMor_commRing R M m φ j k = 0 := by
  have hij' : i + 1 = j := hij
  have hjk' : j + 1 = k := hjk
  subst hij'
  subst hjk'
  by_cases hle : i + 1 + 1 ≤ m
  · have hle1 : i + 1 ≤ m := by omega
    have hD : (koszulShiftD_commRing R M m (i + 1) φ hle).comp
        (koszulShiftD_commRing R M m i φ hle1) = 0 :=
      koszulShiftD_comp_aux_commRing R M φ _ _ _
        (koszulShiftD_index_eq m i hle1)
        (koszulShiftD_index_eq m (i + 1) hle)
    rw [koszulShiftMor_commRing_succ_of_le R M m φ i hle1,
      koszulShiftMor_commRing_succ_of_le R M m φ (i + 1) hle]
    simp only [koszulShiftAt_commRing, Category.assoc]
    rw [eqToHom_middle_junction, eqToHom_refl, Category.id_comp]
    change eqToHom (koszulShiftObj_commRing_eq_of_le R M m i
        (show i ≤ m from by omega)) ≫
        ModuleCat.ofHom (koszulShiftD_commRing R M m i φ hle1) ≫
          ModuleCat.ofHom (koszulShiftD_commRing R M m (i + 1) φ hle) ≫
            eqToHom (koszulShiftObj_commRing_eq_of_le R M m (i + 1 + 1)
              (show i + 1 + 1 ≤ m from hle)).symm = 0
    rw [ofHom_comp_middle_commRing, hD, ModuleCat.ofHom_zero, Limits.zero_comp,
      Limits.comp_zero]
  · have hle' : ¬ i + 1 + 1 ≤ m := hle
    rw [koszulShiftMor_commRing_succ_off R M m φ (i + 1) hle']
    exact Limits.comp_zero

/-- The shift target cochain complex over a `CommRing`: `X k = ⋀^{m-k}`
with contraction differentials (zero beyond `m`). Target of the R-D4 shift
iso (mirror of `koszulShiftComplex`).
-/
def koszulShiftComplex_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R) : CochainComplex (ModuleCat R) ℕ where
  X := koszulShiftObj_commRing R M m
  d := koszulShiftMor_commRing R M m φ
  shape := fun i j h => by
    have hne : ¬(i + 1 = j) := fun heq => h heq
    simp only [koszulShiftMor_commRing, dite_eq_right hne]
  d_comp_d' := fun i j k hij hjk =>
    koszulShiftMor_comp_zero_commRing R M m φ i j k hij hjk

/-- The degree-`k` object of the shift target complex. -/
theorem koszulShiftComplex_commRing_X (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R) (k : ℕ) :
    (koszulShiftComplex_commRing R M m φ).X k =
      koszulShiftObj_commRing R M m k :=
  rfl

/-- The morphisms of the shift target complex are `koszulShiftMor_commRing`. -/
theorem koszulShiftComplex_commRing_d (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R) :
    (koszulShiftComplex_commRing R M m φ).d = koszulShiftMor_commRing R M m φ :=
  rfl

/-! ### §14b. The conditional shift iso over a `CommRing` (mirror of §8) -/

/-- Shift compatibility over a `CommRing` (mirror of `koszulShiftCompat`):
the degree maps `ψ` commute with the dual differential `δ` and the shift
differential `d`. Satisfied by the signed star (§14e).

Conditional hypothesis (explicit residual for the signed-star development). -/
def koszulShiftCompat_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M)) : Prop :=
  ∀ k : ℕ, ∀ h : k + 1 ≤ m,
    (koszulShiftD_commRing R M m k φ h).comp (ψ k) =
      (ψ (k + 1)).comp (koszulDualD φ k)

/-- Forward degree maps of the shift Hom: `ψ` on in-range degrees, zero
beyond (mirror of `koszulShiftHomF`).
-/
def koszulShiftHomF_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M)) (k : ℕ) :
    (koszulDualComplex φ).X k ⟶ koszulShiftObj_commRing R M m k :=
  dite (k ≤ m) (fun hk => ModuleCat.ofHom (ψ k) ≫
    eqToHom (koszulShiftObj_commRing_eq_of_le R M m k hk).symm) (fun _ => 0)

/-- On in-range degrees the forward map is `ψ` transported to the target. -/
theorem koszulShiftHomF_commRing_of_le (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M)) (k : ℕ) (hk : k ≤ m) :
    koszulShiftHomF_commRing R M m φ ψ k = ModuleCat.ofHom (ψ k) ≫
      eqToHom (koszulShiftObj_commRing_eq_of_le R M m k hk).symm := by
  rw [koszulShiftHomF_commRing]
  exact dite_eq_left hk

/-- On out-of-range degrees the forward map is zero. -/
theorem koszulShiftHomF_commRing_off (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M)) (k : ℕ) (hk : ¬ k ≤ m) :
    koszulShiftHomF_commRing R M m φ ψ k = 0 := by
  rw [koszulShiftHomF_commRing, dite_eq_right hk]

/-- Beyond `m`, exterior powers are subsingletons — over a `CommRing`, via
the empty basis index: no `k`-subset of `Fin m` exists for `k > m`
(`Finset.card_le_univ`), so `(b.exteriorPower k).repr` lies in a
subsingleton `Finsupp` type. This replaces the field-only `finrank` +
inverse argument of `exteriorPower_subsingleton_of_gt`.
-/
theorem exteriorPower_subsingleton_of_gt_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) (h : m < k) :
    Subsingleton ↥(⋀[R]^k M) := by
  have hempty : ∀ s : ↥(Set.powersetCard (Fin m) k), False := fun s => by
    have hc : s.1.card = k := powersetCard_card s
    have hle : s.1.card ≤ m := by
      calc s.1.card ≤ Fintype.card (Fin m) := Finset.card_le_univ s.1
        _ = m := Fintype.card_fin m
    omega
  have hsub : Subsingleton (↥(Set.powersetCard (Fin m) k) →₀ R) :=
    ⟨fun f g => by ext i; exact (hempty i).elim⟩
  exact ⟨fun x y => (b.exteriorPower k).repr.injective
    (hsub.elim ((b.exteriorPower k).repr x) ((b.exteriorPower k).repr y))⟩

/-- Duals of subsingleton modules are subsingletons (mirror of
`dual_subsingleton_of_subsingleton`; proof is ring-general).
-/
theorem dual_subsingleton_of_subsingleton_commRing (R V : Type*) [CommRing R]
    [AddCommGroup V] [Module R V] (h : Subsingleton V) :
    Subsingleton (Module.Dual R V) :=
  ⟨fun f g => LinearMap.ext fun x => by
    have hx : x = 0 := h.elim x 0
    rw [hx, map_zero, map_zero]⟩

/-- Beyond `m`, the dual differential vanishes: it transposes contraction
out of a zero module (mirror of `koszulDualD_eq_zero_of_gt`, via the
empty-index subsingleton).
-/
theorem koszulDualD_eq_zero_of_gt_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R) (i : ℕ) (h : m < i + 1) :
    koszulDualD φ i = 0 := by
  have hsub := exteriorPower_subsingleton_of_gt_commRing R M m (i + 1) b h
  have hC : koszulContract φ i = 0 := by
    apply LinearMap.ext
    intro z
    have hz : z = 0 := hsub.elim z 0
    rw [hz]
    simp
  calc koszulDualD φ i = (koszulContract φ i).dualMap := rfl
    _ = (0 : ↥(⋀[R]^(i + 1) M) →ₗ[R] ↥(⋀[R]^i M)).dualMap := by
        rw [hC]
    _ = 0 := dualMap_zero _ _

/-- Forward commutation (mirror of `koszulShiftHom_comm`): the `ψ` squares
commute, by `koszulShiftCompat_commRing` in range and by vanishing of the
dual differential out of range.

Conditional on exactly [`koszulShiftCompat_commRing`]. -/
theorem koszulShiftHom_comm_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M))
    (hcompat : koszulShiftCompat_commRing R M m φ ψ) (i j : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j) :
    koszulShiftHomF_commRing R M m φ ψ i ≫ koszulShiftMor_commRing R M m φ i j =
      koszulDualMor φ i j ≫ koszulShiftHomF_commRing R M m φ ψ j := by
  have hij' : i + 1 = j := hij
  subst hij'
  by_cases hle : i + 1 ≤ m
  · have hle1 : i ≤ m := by omega
    rw [koszulShiftHomF_commRing_of_le R M m φ ψ i hle1,
      koszulShiftHomF_commRing_of_le R M m φ ψ (i + 1) hle,
      koszulShiftMor_commRing_succ_of_le R M m φ i hle,
      koszulDualMor_succ]
    simp only [koszulShiftAt_commRing]
    change (ModuleCat.ofHom (ψ i) ≫
              eqToHom (koszulShiftObj_commRing_eq_of_le R M m i hle1).symm) ≫
            (eqToHom (koszulShiftObj_commRing_eq_of_le R M m i hle1) ≫
              (ModuleCat.ofHom (koszulShiftD_commRing R M m i φ hle) ≫
                eqToHom (koszulShiftObj_commRing_eq_of_le R M m (i + 1) hle).symm)) =
        ModuleCat.ofHom (koszulDualD φ i) ≫
          (ModuleCat.ofHom (ψ (i + 1)) ≫
            eqToHom (koszulShiftObj_commRing_eq_of_le R M m (i + 1) hle).symm)
    simp only [Category.assoc]
    rw [eqToHom_middle_junction, eqToHom_refl, Category.id_comp,
      ofHom_comp_middle_commRing, ofHom_comp_middle_commRing, hcompat i hle]
  · have hmi : m < i + 1 := by omega
    have hdual0 : koszulDualD φ i = 0 :=
      koszulDualD_eq_zero_of_gt_commRing R M m b φ i hmi
    rw [koszulShiftHomF_commRing_off R M m φ ψ (i + 1) hle,
      koszulShiftMor_commRing_succ_off R M m φ i hle, koszulDualMor_succ,
      hdual0, ModuleCat.ofHom_zero]
    exact (Limits.comp_zero).trans (Limits.comp_zero).symm

/-- The forward shift Hom `Hom(K, R) → K[m]` over a `CommRing` (mirror of
`koszulShiftHom`).

Conditional on exactly [`koszulShiftCompat_commRing`]. -/
def koszulShiftHom_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M))
    (hcompat : koszulShiftCompat_commRing R M m φ ψ) :
    (koszulDualComplex φ) ⟶ (koszulShiftComplex_commRing R M m φ) where
  f := koszulShiftHomF_commRing R M m φ ψ
  comm' := fun i j hij => by
    rw [koszulShiftComplex_commRing_d, koszulDualComplex_d]
    exact koszulShiftHom_comm_commRing R M m b φ ψ hcompat i j hij

/-- The forward Hom acts degree-wise by `koszulShiftHomF_commRing`. -/
theorem koszulShiftHom_commRing_f (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M))
    (hcompat : koszulShiftCompat_commRing R M m φ ψ) :
    (koszulShiftHom_commRing R M m b φ ψ hcompat).f =
      koszulShiftHomF_commRing R M m φ ψ :=
  rfl

/-- Inverse compatibility over a `CommRing` (mirror of
`koszulShiftCompat_inv`): derived from forward compatibility plus the
two-sided inverse hypotheses.

Conditional on exactly [`koszulShiftCompat_commRing`, `hψl`, `hψr`]. -/
theorem koszulShiftCompat_inv_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M))
    (ψinv : ∀ k : ℕ, ↥(⋀[R]^(m - k) M) →ₗ[R]
      Module.Dual R ↥(⋀[R]^k M))
    (hcompat : koszulShiftCompat_commRing R M m φ ψ)
    (hψl : ∀ k : ℕ, ∀ _ : k ≤ m, (ψinv k).comp (ψ k) = LinearMap.id)
    (hψr : ∀ k : ℕ, ∀ _ : k ≤ m, (ψ k).comp (ψinv k) = LinearMap.id)
    (k : ℕ) (h : k + 1 ≤ m) :
    (koszulDualD φ k).comp (ψinv k) =
      (ψinv (k + 1)).comp (koszulShiftD_commRing R M m k φ h) := by
  have hk : k ≤ m := by omega
  have eA : ((koszulDualD φ k).comp (ψinv k)).comp (ψ k) =
      koszulDualD φ k := by
    rw [LinearMap.comp_assoc, hψl k hk, LinearMap.comp_id]
  have eB : ((ψinv (k + 1)).comp (koszulShiftD_commRing R M m k φ h)).comp
      (ψ k) = koszulDualD φ k := by
    rw [LinearMap.comp_assoc, hcompat k h, ← LinearMap.comp_assoc,
      hψl (k + 1) h, LinearMap.id_comp]
  have hEq := eA.trans eB.symm
  have hcancel := congrArg (fun X => X.comp (ψinv k)) hEq
  simp only [LinearMap.comp_assoc, hψr k hk, LinearMap.comp_id] at hcancel
  exact hcancel

/-- Backward degree maps of the shift Hom: `ψinv` on in-range degrees,
zero beyond (mirror of `koszulShiftHomInvF`).
-/
def koszulShiftHomInvF_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R)
    (ψinv : ∀ k : ℕ, ↥(⋀[R]^(m - k) M) →ₗ[R]
      Module.Dual R ↥(⋀[R]^k M)) (k : ℕ) :
    koszulShiftObj_commRing R M m k ⟶ (koszulDualComplex φ).X k :=
  dite (k ≤ m) (fun hk => eqToHom (koszulShiftObj_commRing_eq_of_le R M m k hk) ≫
    ModuleCat.ofHom (ψinv k)) (fun _ => 0)

/-- On in-range degrees the backward map is `ψinv` transported from the
target. -/
theorem koszulShiftHomInvF_commRing_of_le (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R)
    (ψinv : ∀ k : ℕ, ↥(⋀[R]^(m - k) M) →ₗ[R]
      Module.Dual R ↥(⋀[R]^k M)) (k : ℕ) (hk : k ≤ m) :
    koszulShiftHomInvF_commRing R M m φ ψinv k =
      eqToHom (koszulShiftObj_commRing_eq_of_le R M m k hk) ≫
        ModuleCat.ofHom (ψinv k) := by
  rw [koszulShiftHomInvF_commRing]
  exact dite_eq_left hk

/-- On out-of-range degrees the backward map is zero. -/
theorem koszulShiftHomInvF_commRing_off (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (φ : M →ₗ[R] R)
    (ψinv : ∀ k : ℕ, ↥(⋀[R]^(m - k) M) →ₗ[R]
      Module.Dual R ↥(⋀[R]^k M)) (k : ℕ) (hk : ¬ k ≤ m) :
    koszulShiftHomInvF_commRing R M m φ ψinv k = 0 := by
  rw [koszulShiftHomInvF_commRing, dite_eq_right hk]

/-- Backward commutation over a `CommRing` (mirror of
`koszulShiftHomInv_comm`), from derived inverse compatibility.

Conditional on exactly [`koszulShiftCompat_commRing`, `hψl`, `hψr`]. -/
theorem koszulShiftHomInv_comm_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M))
    (ψinv : ∀ k : ℕ, ↥(⋀[R]^(m - k) M) →ₗ[R]
      Module.Dual R ↥(⋀[R]^k M))
    (hcompat : koszulShiftCompat_commRing R M m φ ψ)
    (hψl : ∀ k : ℕ, ∀ _ : k ≤ m, (ψinv k).comp (ψ k) = LinearMap.id)
    (hψr : ∀ k : ℕ, ∀ _ : k ≤ m, (ψ k).comp (ψinv k) = LinearMap.id)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    koszulShiftHomInvF_commRing R M m φ ψinv i ≫ koszulDualMor φ i j =
      koszulShiftMor_commRing R M m φ i j ≫
        koszulShiftHomInvF_commRing R M m φ ψinv j := by
  have hij' : i + 1 = j := hij
  subst hij'
  by_cases hle : i + 1 ≤ m
  · have hle1 : i ≤ m := by omega
    have hinv :=
      koszulShiftCompat_inv_commRing R M m φ ψ ψinv hcompat hψl hψr i hle
    rw [koszulShiftHomInvF_commRing_of_le R M m φ ψinv i hle1,
      koszulShiftHomInvF_commRing_of_le R M m φ ψinv (i + 1) hle,
      koszulShiftMor_commRing_succ_of_le R M m φ i hle, koszulDualMor_succ]
    simp only [koszulShiftAt_commRing]
    change (eqToHom (koszulShiftObj_commRing_eq_of_le R M m i hle1) ≫
              ModuleCat.ofHom (ψinv i)) ≫
            ModuleCat.ofHom (koszulDualD φ i) =
        (eqToHom (koszulShiftObj_commRing_eq_of_le R M m i hle1) ≫
          ModuleCat.ofHom (koszulShiftD_commRing R M m i φ hle) ≫
            eqToHom (koszulShiftObj_commRing_eq_of_le R M m (i + 1) hle).symm) ≫
          (eqToHom (koszulShiftObj_commRing_eq_of_le R M m (i + 1) hle) ≫
            ModuleCat.ofHom (ψinv (i + 1)))
    simp only [Category.assoc]
    rw [eqToHom_middle_junction, eqToHom_refl, Category.id_comp,
      ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, hinv]
  · have hmi : m < i + 1 := by omega
    rw [koszulShiftHomInvF_commRing_off R M m φ ψinv (i + 1) hle,
      koszulShiftMor_commRing_succ_off R M m φ i hle, koszulDualMor_succ,
      koszulDualD_eq_zero_of_gt_commRing R M m b φ i hmi, ModuleCat.ofHom_zero]
    exact (Limits.comp_zero).trans (Limits.comp_zero).symm

/-- The backward shift Hom `K[m] → Hom(K, R)` over a `CommRing` (mirror of
`koszulShiftHomInv`).

Conditional on exactly [`koszulShiftCompat_commRing`, `hψl`, `hψr`]. -/
def koszulShiftHomInv_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M))
    (ψinv : ∀ k : ℕ, ↥(⋀[R]^(m - k) M) →ₗ[R]
      Module.Dual R ↥(⋀[R]^k M))
    (hcompat : koszulShiftCompat_commRing R M m φ ψ)
    (hψl : ∀ k : ℕ, ∀ _ : k ≤ m, (ψinv k).comp (ψ k) = LinearMap.id)
    (hψr : ∀ k : ℕ, ∀ _ : k ≤ m, (ψ k).comp (ψinv k) = LinearMap.id) :
    (koszulShiftComplex_commRing R M m φ) ⟶ (koszulDualComplex φ) where
  f := koszulShiftHomInvF_commRing R M m φ ψinv
  comm' := fun i j hij => by
    rw [koszulShiftComplex_commRing_d, koszulDualComplex_d]
    exact koszulShiftHomInv_comm_commRing R M m b φ ψ ψinv hcompat hψl hψr i j hij

/-- The backward Hom acts degree-wise by `koszulShiftHomInvF_commRing`. -/
theorem koszulShiftHomInv_commRing_f (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M))
    (ψinv : ∀ k : ℕ, ↥(⋀[R]^(m - k) M) →ₗ[R]
      Module.Dual R ↥(⋀[R]^k M))
    (hcompat : koszulShiftCompat_commRing R M m φ ψ)
    (hψl : ∀ k : ℕ, ∀ _ : k ≤ m, (ψinv k).comp (ψ k) = LinearMap.id)
    (hψr : ∀ k : ℕ, ∀ _ : k ≤ m, (ψ k).comp (ψinv k) = LinearMap.id) :
    (koszulShiftHomInv_commRing R M m b φ ψ ψinv hcompat hψl hψr).f =
      koszulShiftHomInvF_commRing R M m φ ψinv :=
  rfl

/-- The R-D4 shift iso `Hom(K, R) ≅ K[m]` over a `CommRing` as complexes,
conditional on the signed-star data (mirror of `koszulShiftIso`).

Conditional on exactly [`koszulShiftCompat_commRing`, `hψl`, `hψr`]. -/
noncomputable def koszulShiftIso_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R)
    (ψ : ∀ k : ℕ, Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M))
    (ψinv : ∀ k : ℕ, ↥(⋀[R]^(m - k) M) →ₗ[R]
      Module.Dual R ↥(⋀[R]^k M))
    (hcompat : koszulShiftCompat_commRing R M m φ ψ)
    (hψl : ∀ k : ℕ, ∀ _ : k ≤ m, (ψinv k).comp (ψ k) = LinearMap.id)
    (hψr : ∀ k : ℕ, ∀ _ : k ≤ m, (ψ k).comp (ψinv k) = LinearMap.id) :
    (koszulDualComplex φ) ≅ (koszulShiftComplex_commRing R M m φ) :=
  Iso.mk (koszulShiftHom_commRing R M m b φ ψ hcompat)
    (koszulShiftHomInv_commRing R M m b φ ψ ψinv hcompat hψl hψr)
    (HomologicalComplex.hom_ext _ _ fun k => by
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        koszulShiftHom_commRing_f, koszulShiftHomInv_commRing_f]
      by_cases hk : k ≤ m
      · rw [koszulShiftHomF_commRing_of_le R M m φ ψ k hk,
          koszulShiftHomInvF_commRing_of_le R M m φ ψinv k hk]
        change (ModuleCat.ofHom (ψ k) ≫
                  eqToHom (koszulShiftObj_commRing_eq_of_le R M m k hk).symm) ≫
                (eqToHom (koszulShiftObj_commRing_eq_of_le R M m k hk) ≫
                  ModuleCat.ofHom (ψinv k)) =
              𝟙 ((koszulDualComplex φ).X k)
        simp only [Category.assoc]
        rw [eqToHom_middle_junction, eqToHom_refl, Category.id_comp,
          ← ModuleCat.ofHom_comp, hψl k hk, ModuleCat.ofHom_id]
        simp only [koszulDualComplex_X]
      · have hmk : m < k := by omega
        have hsub := exteriorPower_subsingleton_of_gt_commRing R M m k b hmk
        have hdual :=
          dual_subsingleton_of_subsingleton_commRing R ↥(⋀[R]^k M) hsub
        have hid : (LinearMap.id :
            Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
              Module.Dual R ↥(⋀[R]^k M)) = 0 :=
          LinearMap.ext fun x => hdual.elim x 0
        rw [koszulShiftHomF_commRing_off R M m φ ψ k hk,
          koszulShiftHomInvF_commRing_off R M m φ ψinv k hk]
        change (0 : (koszulDualComplex φ).X k ⟶
                  koszulShiftObj_commRing R M m k) ≫
                (0 : koszulShiftObj_commRing R M m k ⟶
                  (koszulDualComplex φ).X k) =
              𝟙 ((koszulDualComplex φ).X k)
        rw [Limits.comp_zero, koszulDualComplex_X, ← ModuleCat.ofHom_id, hid,
          ModuleCat.ofHom_zero])
    (HomologicalComplex.hom_ext _ _ fun k => by
      simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        koszulShiftHom_commRing_f, koszulShiftHomInv_commRing_f]
      by_cases hk : k ≤ m
      · rw [koszulShiftHomF_commRing_of_le R M m φ ψ k hk,
          koszulShiftHomInvF_commRing_of_le R M m φ ψinv k hk]
        change (eqToHom (koszulShiftObj_commRing_eq_of_le R M m k hk) ≫
                  ModuleCat.ofHom (ψinv k)) ≫
                (ModuleCat.ofHom (ψ k) ≫
                  eqToHom (koszulShiftObj_commRing_eq_of_le R M m k hk).symm) =
              𝟙 ((koszulShiftComplex_commRing R M m φ).X k)
        simp only [Category.assoc]
        rw [ofHom_comp_middle_commRing, hψr k hk, ModuleCat.ofHom_id,
          Category.id_comp, eqToHom_trans, eqToHom_refl]
        simp only [koszulShiftComplex_commRing_X]
      · have hsub : Subsingleton PUnit := inferInstance
        have hid : (LinearMap.id : PUnit →ₗ[R] PUnit) = 0 :=
          LinearMap.ext fun x => hsub.elim x 0
        rw [koszulShiftHomF_commRing_off R M m φ ψ k hk,
          koszulShiftHomInvF_commRing_off R M m φ ψinv k hk]
        change (0 : (koszulShiftComplex_commRing R M m φ).X k ⟶
                  (koszulDualComplex φ).X k) ≫
                (0 : (koszulDualComplex φ).X k ⟶
                  (koszulShiftComplex_commRing R M m φ).X k) =
              𝟙 ((koszulShiftComplex_commRing R M m φ).X k)
        rw [Limits.comp_zero, koszulShiftComplex_commRing_X,
          koszulShiftObj_commRing, ite_eq_right hk, ← ModuleCat.ofHom_id, hid,
          ModuleCat.ofHom_zero])

/-! ### §14c. The signed Hodge star over a `CommRing` (mirror of §9) -/

/-- The Hodge sign weight over a `CommRing` (mirror of `hodgeSignWeight`):
`(-1)` to the sum of the index values — the sign forced by R-D2
compatibility.
-/
noncomputable def hodgeSignWeight_commRing (R : Type*) [CommRing R] (m k : ℕ)
    (s : ↥(Set.powersetCard (Fin m) k)) : Rˣ :=
  (-1 : Rˣ)^(s.1.sum fun i => i.val)

/-- The sign is multiplicative over insertion (mirror of
`neg_one_pow_sum_insert`).
-/
theorem neg_one_pow_sum_insert_commRing (R : Type*) [CommRing R] (m : ℕ)
    (S : Finset (Fin m)) (i : Fin m) (hi : i ∉ S) :
    (-1 : R)^((insert i S).sum (fun j => j.val)) =
      (-1 : R)^(S.sum (fun j => j.val)) * (-1 : R)^(i.val) := by
  rw [Finset.sum_insert hi, pow_add]
  exact mul_comm _ _

/-- Parity key for compat (mirror of `neg_one_pow_sub_add`):
`(-1)^{i-p} = (-1)^{i+p}` since the exponents differ by `2p`.
-/
theorem neg_one_pow_sub_add_commRing (R : Type*) [CommRing R] (i p : ℕ)
    (h : p ≤ i) :
    (-1 : R)^(i - p) = (-1 : R)^(i + p) := by
  have h2p : (-1 : R)^(2 * p) = 1 := by
    rw [pow_mul]
    have hsq : (-1 : R)^2 = 1 := by ring
    rw [hsq, one_pow]
  have hexp : i + p = (i - p) + 2 * p := by omega
  rw [hexp, pow_add, h2p, mul_one]

/-- Diagonal scaling of finitely-supported functions by unit weights over a
`CommRing`, as a linear equiv. The support argument uses
`Units.mul_right_eq_zero` (unit multiplication reflects zero) instead of
`mul_ne_zero`, so no `NoZeroDivisors` hypothesis is needed — this is the
fix that lets the signed star leave the field setting.
-/
noncomputable def diagLinearEquiv_commRing (R : Type*) [CommRing R]
    {ι : Type*} (w : ι → Rˣ) : (ι →₀ R) ≃ₗ[R] (ι →₀ R) where
  toLinearMap :=
    { toFun := fun f =>
        ⟨f.support, fun i => (w i : R) * f i, fun i =>
          ⟨fun hi hcon => Finsupp.mem_support_iff.mp hi
            ((Units.mul_right_eq_zero (w i)).mp hcon),
           fun hi => Finsupp.mem_support_iff.mpr fun h =>
            hi (by rw [h, mul_zero])⟩⟩
      map_add' := fun f g => by
        ext i
        change (w i : R) * ((f + g) i) = (w i : R) * f i + (w i : R) * g i
        rw [Finsupp.add_apply, mul_add]
      map_smul' := fun r f => by
        ext i
        change (w i : R) * ((r • f) i) = r • ((w i : R) * f i)
        exact Algebra.mul_smul_comm _ _ _ }
  invFun := fun g =>
    ⟨g.support, fun i => (((w i)⁻¹ : Rˣ) : R) * g i, fun i =>
      ⟨fun hi hcon => Finsupp.mem_support_iff.mp hi
        ((Units.mul_right_eq_zero (w i)⁻¹).mp hcon),
       fun hi => Finsupp.mem_support_iff.mpr fun h =>
        hi (by rw [h, mul_zero])⟩⟩
  left_inv := fun f => by
    ext i
    change (((w i)⁻¹ : Rˣ) : R) * ((w i : R) * f i) = f i
    exact Units.inv_mul_cancel_left _ _
  right_inv := fun g => by
    ext i
    change (w i : R) * ((((w i)⁻¹ : Rˣ) : R) * g i) = g i
    exact Units.mul_inv_cancel_left _ _

/-- Diagonal scaling acts pointwise. -/
@[simp]
theorem diagLinearEquiv_commRing_apply (R : Type*) [CommRing R] {ι : Type*}
    (w : ι → Rˣ) (f : ι →₀ R) (i : ι) :
    diagLinearEquiv_commRing R w f i = (w i : R) * f i :=
  rfl

/-- Diagonal scaling sends `single a 1` to `single a (w a)`. -/
theorem diagLinearEquiv_commRing_single_one (R : Type*) [CommRing R]
    {ι : Type*} (w : ι → Rˣ) (a : ι) :
    diagLinearEquiv_commRing R w (Finsupp.single a 1)
      = Finsupp.single a (w a : R) := by
  classical
  ext i
  simp only [diagLinearEquiv_commRing_apply]
  by_cases h : i = a
  · subst h
    simp
  · rw [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h, mul_zero]

/-- A singleton with value `c` is `c` times the unit singleton. -/
theorem single_eq_smul_single_one_commRing (R : Type*) [CommRing R]
    {ι : Type*} (j : ι) (c : R) :
    Finsupp.single j c = c • Finsupp.single j 1 := by
  classical
  ext t
  by_cases h : t = j
  · subst h
    rw [Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  · rw [Finsupp.single_eq_of_ne h, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne h]
    simp

/-- The signed shift piece over a `CommRing` (mirror of
`koszulShiftPieceSigned`): dual basis element `ε_S` maps to the signed
complementary basis wedge `σ(S) • e_{Sᶜ}`, along the free basis `b`. These
are the degree maps of the R-D4 shift iso.
-/
noncomputable def koszulShiftPieceSigned_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) (h : k ≤ m) :
    Module.Dual R ↥(⋀[R]^k M) ≃ₗ[R] ↥(⋀[R]^(m - k) M) :=
  (((b.exteriorPower k).dualBasis).repr.trans
    (diagLinearEquiv_commRing R (hodgeSignWeight_commRing R m k))).trans
    ((Finsupp.domLCongr (powersetCardComplEquiv m k h)).trans
      (((b.exteriorPower (m - k)).repr.symm)))

/-- The signed shift piece sends dual-basis elements to signed
complementary basis wedges.
-/
@[simp]
theorem koszulShiftPieceSigned_commRing_apply_dualBasis (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) (h : k ≤ m)
    (s : ↥(Set.powersetCard (Fin m) k)) :
    koszulShiftPieceSigned_commRing R M m k b h
        (((b.exteriorPower k).dualBasis) s) =
      (hodgeSignWeight_commRing R m k s : R) •
        ((b.exteriorPower (m - k))
          (powersetCardComplEquiv m k h s)) := by
  simp only [koszulShiftPieceSigned_commRing, LinearEquiv.trans_apply,
    Module.Basis.repr_self, diagLinearEquiv_commRing_single_one,
    Finsupp.domLCongr_single]
  rw [single_eq_smul_single_one_commRing, map_smul]
  rw [← Module.Basis.repr_self
    ((b.exteriorPower (m - k)))
    (powersetCardComplEquiv m k h s)]
  rw [LinearEquiv.symm_apply_apply]

/-- The signed Hodge star over a `CommRing` (mirror of `koszulHodgeSigned`):
`⋀^k ≃ₗ ⋀^{m-k}` sending each exterior-power basis wedge to the signed
complementary basis wedge.
-/
noncomputable def koszulHodgeSigned_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) (h : k ≤ m) :
    ↥(⋀[R]^k M) ≃ₗ[R] ↥(⋀[R]^(m - k) M) :=
  ((b.exteriorPower k).repr.trans
    (diagLinearEquiv_commRing R (hodgeSignWeight_commRing R m k))).trans
    ((Finsupp.domLCongr (powersetCardComplEquiv m k h)).trans
      (((b.exteriorPower (m - k)).repr.symm)))

/-- The signed Hodge star sends basis wedges to signed complementary
basis wedges.
-/
@[simp]
theorem koszulHodgeSigned_commRing_apply_basis (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) (h : k ≤ m)
    (s : ↥(Set.powersetCard (Fin m) k)) :
    koszulHodgeSigned_commRing R M m k b h
        ((b.exteriorPower k) s) =
      (hodgeSignWeight_commRing R m k s : R) •
        ((b.exteriorPower (m - k))
          (powersetCardComplEquiv m k h s)) := by
  simp only [koszulHodgeSigned_commRing, LinearEquiv.trans_apply,
    Module.Basis.repr_self, diagLinearEquiv_commRing_single_one,
    Finsupp.domLCongr_single]
  rw [single_eq_smul_single_one_commRing, map_smul]
  rw [← Module.Basis.repr_self
    ((b.exteriorPower (m - k)))
    (powersetCardComplEquiv m k h s)]
  rw [LinearEquiv.symm_apply_apply]

/-- The signed degree maps on all degrees (zero beyond `m`), in the shape
`koszulShiftIso_commRing` consumes.
-/
noncomputable def koszulShiftPieceSignedMap_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) :
    Module.Dual R ↥(⋀[R]^k M) →ₗ[R]
      ↥(⋀[R]^(m - k) M) :=
  dite (k ≤ m) (fun hk => (koszulShiftPieceSigned_commRing R M m k b hk).toLinearMap)
    (fun _ => 0)

/-- The signed inverse degree maps on all degrees. -/
noncomputable def koszulShiftPieceSignedInvMap_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) :
    ↥(⋀[R]^(m - k) M) →ₗ[R]
      Module.Dual R ↥(⋀[R]^k M) :=
  dite (k ≤ m)
    (fun hk => (koszulShiftPieceSigned_commRing R M m k b hk).symm.toLinearMap)
    (fun _ => 0)

/-- On in-range degrees the signed map is the signed equiv. -/
theorem koszulShiftPieceSignedMap_commRing_of_le (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) (hk : k ≤ m) :
    koszulShiftPieceSignedMap_commRing R M m k b =
      (koszulShiftPieceSigned_commRing R M m k b hk).toLinearMap := by
  rw [koszulShiftPieceSignedMap_commRing, dite_eq_left hk]

/-- On in-range degrees the signed inverse map is the signed equiv inverse. -/
theorem koszulShiftPieceSignedInvMap_commRing_of_le (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) (hk : k ≤ m) :
    koszulShiftPieceSignedInvMap_commRing R M m k b =
      (koszulShiftPieceSigned_commRing R M m k b hk).symm.toLinearMap := by
  rw [koszulShiftPieceSignedInvMap_commRing, dite_eq_left hk]

/-- Left inverse law for the signed degree maps (feeds
`koszulShiftIso_commRing`). -/
theorem koszulShiftPieceSigned_commRing_left (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) (hk : k ≤ m) :
    (koszulShiftPieceSignedInvMap_commRing R M m k b).comp
        (koszulShiftPieceSignedMap_commRing R M m k b) = LinearMap.id := by
  rw [koszulShiftPieceSignedMap_commRing_of_le R M m k b hk,
    koszulShiftPieceSignedInvMap_commRing_of_le R M m k b hk]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.id_apply]
  exact LinearEquiv.symm_apply_apply _ _

/-- Right inverse law for the signed degree maps (feeds
`koszulShiftIso_commRing`). -/
theorem koszulShiftPieceSigned_commRing_right (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) (hk : k ≤ m) :
    (koszulShiftPieceSignedMap_commRing R M m k b).comp
        (koszulShiftPieceSignedInvMap_commRing R M m k b) = LinearMap.id := by
  rw [koszulShiftPieceSignedMap_commRing_of_le R M m k b hk,
    koszulShiftPieceSignedInvMap_commRing_of_le R M m k b hk]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.id_apply]
  exact LinearEquiv.apply_symm_apply _ _

/-! ### §14d. Contraction and dual-differential formulas over a `CommRing`
(mirror of the §11 engine; the §10 Leibniz rule and all §11
position-count/ordered-erasure lemmas are ring-independent and reused) -/

/-- Coe pushes through sums of exterior-power elements. -/
theorem exteriorPower_coe_sum_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → ↥(⋀[R]^n M)) :
    ((∑ i ∈ s, f i : ↥(⋀[R]^n M)) :
      ExteriorAlgebra R M) =
      ∑ i ∈ s, ((f i : ↥(⋀[R]^n M)) :
        ExteriorAlgebra R M) :=
  map_sum (Submodule.subtype _) _ _

/-- Coe pushes through scalar multiples of exterior-power elements. -/
@[simp]
theorem exteriorPower_coe_smul_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ)
    (c : R) (x : ↥(⋀[R]^n M)) :
    ((c • x : ↥(⋀[R]^n M)) : ExteriorAlgebra R M) =
      c • ((x : ↥(⋀[R]^n M)) : ExteriorAlgebra R M) :=
  map_smul (Submodule.subtype _) _ _

/-- Basis wedges are decomposable wedges of the ordered basis vectors. -/
theorem exteriorPower_basis_coe_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M)
    (s : ↥(Set.powersetCard (Fin m) k)) :
    (((b.exteriorPower k) s :
      ↥(⋀[R]^k M)) : ExteriorAlgebra R M) =
      ExteriorAlgebra.ιMulti R k
        (⇑b ∘ s.1.orderEmbOfFin (powersetCard_card s)) := by
  rw [exteriorPower.basis_apply]
  rfl

/-- Contraction on basis wedges over a `CommRing` (mirror of
`koszulContract_basis`): delete each ordered factor in turn, with
alternating signs. Specializes the (§10) Leibniz rule via ordered-erasure
uniqueness.
-/
theorem koszulContract_basis_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m n : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R)
    (s : ↥(Set.powersetCard (Fin m) (n.succ))) :
    koszulContract φ n ((b.exteriorPower (n.succ)) s) =
      ∑ j : Fin n.succ,
        ((-1 : R)^(j.val) *
            φ (b (s.1.orderEmbOfFin (powersetCard_card s) j))) •
          ((b.exteriorPower n)
            ⟨s.1.erase (s.1.orderEmbOfFin (powersetCard_card s) j),
              powersetCard_mem (erase_emb_card m s.1 (powersetCard_card s) j)⟩) := by
  apply Subtype.ext
  rw [koszulContract_apply, exteriorPower_basis_coe_commRing,
    contractLeft_ιMulti, exteriorPower_coe_sum_commRing]
  simp only [exteriorPower_coe_smul_commRing]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp_apply]
  have herase := orderEmbOfFin_comp_succAbove m s.1 (powersetCard_card s) j
  have hbridge : ExteriorAlgebra.ιMulti R n
      (⇑b ∘
        (s.1.erase (s.1.orderEmbOfFin (powersetCard_card s) j)).orderEmbOfFin
          (erase_emb_card m s.1 (powersetCard_card s) j)) =
      ↑(((b.exteriorPower n)
        ⟨s.1.erase (s.1.orderEmbOfFin (powersetCard_card s) j),
          powersetCard_mem (erase_emb_card m s.1 (powersetCard_card s) j)⟩) :
        ExteriorAlgebra R M) :=
    (exteriorPower_basis_coe_commRing R M m n b
      ⟨s.1.erase (s.1.orderEmbOfFin (powersetCard_card s) j),
        powersetCard_mem (erase_emb_card m s.1 (powersetCard_card s) j)⟩).symm
  rw [Function.comp_assoc, herase, hbridge]

/-- The dual differential on dual-basis elements over a `CommRing` (mirror
of `koszulDualD_basis`): transpose of contraction sums over inserting each
missing element, with position signs. By checking on basis wedges: both
sides select the unique insertion consistent with the target (or vanish
jointly when `S ⊄ T`).
-/
theorem koszulDualD_basis_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R)
    (s : ↥(Set.powersetCard (Fin m) k)) :
    koszulDualD φ k (((b.exteriorPower k).dualBasis) s) =
      ∑ i : ↥(s.1ᶜ), ((-1 : R)^((s.1.filter (· < i.1)).card) *
            φ (b i.1)) •
        (((b.exteriorPower (k+1)).dualBasis)
          ⟨insert i.1 s.1, powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) i.1
            (Finset.mem_compl.mp i.2))⟩) := by
  refine Module.Basis.ext
    ((b.exteriorPower (k+1))) (fun T => ?_)
  rw [koszulDualD, LinearMap.dualMap_apply, koszulContract_basis_commRing]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.dualBasis_apply, Module.Basis.repr_self,
    Finsupp.single_apply]
  by_cases hsub : s.1 ⊆ T.1
  · have hne : s.1 ≠ T.1 := by
      intro heq
      have hcard := congrArg Finset.card heq
      have hs := powersetCard_card s
      have hTcard := powersetCard_card T
      omega
    have hssub : s.1 ⊂ T.1 := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    obtain ⟨e₀, he₀T, he₀S⟩ := Finset.exists_of_ssubset hssub
    have hT : T.1 = insert e₀ s.1 :=
      (Finset.eq_of_subset_of_card_le (s := insert e₀ s.1) (t := T.1)
        (by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxs
          · exact he₀T
          · exact hsub hxs)
        (by
          rw [insert_mem_card m s.1 (powersetCard_card s) e₀ he₀S]
          have hTcard := powersetCard_card T
          omega)).symm
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, T.1.orderEmbOfFin (powersetCard_card T) j₀ = e₀ := by
      have hmem : e₀ ∈ T.1 := he₀T
      rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin T.1 (powersetCard_card T)] at hmem
      obtain ⟨j₀, hj₀⟩ := hmem
      exact ⟨j₀, hj₀⟩
    have hLHS : (∑ j : Fin (k+1), ((-1 : R)^(j.val) *
            φ (b (T.1.orderEmbOfFin (powersetCard_card T) j))) •
          (if (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j),
              powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) j)⟩ :
              ↥(Set.powersetCard (Fin m) k)) = s then (1 : R) else 0)) =
        (-1 : R)^(j₀.val) *
          φ (b (T.1.orderEmbOfFin (powersetCard_card T) j₀)) := by
      have h0 : ∀ t ∈ (Finset.univ : Finset (Fin (k+1))), t ≠ j₀ →
          (((-1 : R)^(t.val) *
            φ (b (T.1.orderEmbOfFin (powersetCard_card T) t))) •
          (if (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) t),
              powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) t)⟩ :
              ↥(Set.powersetCard (Fin m) k)) = s then (1 : R) else 0)) = 0 := by
        intro t _ htne
        have hne : (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) t),
            powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) t)⟩ :
            ↥(Set.powersetCard (Fin m) k)) ≠ s := by
          intro heq
          have hfin : T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) t) = s.1 :=
            congrArg Subtype.val heq
          by_cases hbe : T.1.orderEmbOfFin (powersetCard_card T) t = e₀
          · have hb0 : t = j₀ :=
              (T.1.orderEmbOfFin (powersetCard_card T)).strictMono.injective
                (by rw [hbe, hj₀])
            exact htne hb0
          · exfalso
            have hmemT : e₀ ∈ T.1 := by
              rw [hT]
              exact Finset.mem_insert_self e₀ s.1
            have hmem : e₀ ∈ T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) t) := by
              rw [Finset.mem_erase]
              exact ⟨Ne.symm hbe, hmemT⟩
            rw [hfin] at hmem
            exact he₀S hmem
        rw [ite_eq_right hne]
        exact smul_zero _
      rw [Finset.sum_eq_single j₀ h0
        (fun h => absurd (Finset.mem_univ j₀) h)]
      have herase0 : (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j₀),
          powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) j₀)⟩ :
          ↥(Set.powersetCard (Fin m) k)) = s := by
        apply Subtype.ext
        change T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j₀) = s.1
        rw [hj₀, hT]
        exact Finset.erase_insert he₀S
      rw [ite_eq_left herase0, smul_eq_mul, mul_one]
    have hRHS : (∑ i : ↥(s.1ᶜ), ((-1 : R)^((s.1.filter (· < i.1)).card) *
            φ (b i.1)) •
          (if T = (⟨insert i.1 s.1,
            powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) i.1
              (Finset.mem_compl.mp i.2))⟩ :
              ↥(Set.powersetCard (Fin m) (k+1))) then (1 : R) else 0)) =
        (-1 : R)^((s.1.filter (· < e₀)).card) *
          φ (b e₀) := by
      have hi₀ : e₀ ∈ s.1ᶜ := Finset.mem_compl.mpr he₀S
      have h0 : ∀ t ∈ (Finset.univ : Finset ↥(s.1ᶜ)), t ≠ ⟨e₀, hi₀⟩ →
          (((-1 : R)^((s.1.filter (· < t.1)).card) *
            φ (b t.1)) •
          (if T = (⟨insert t.1 s.1,
            powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) t.1
              (Finset.mem_compl.mp t.2))⟩ :
              ↥(Set.powersetCard (Fin m) (k+1))) then (1 : R) else 0)) = 0 := by
        intro t _ htne
        have hne : T ≠ (⟨insert t.1 s.1,
          powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) t.1
            (Finset.mem_compl.mp t.2))⟩ :
            ↥(Set.powersetCard (Fin m) (k+1))) := by
          intro heq
          have hfin : T.1 = insert t.1 s.1 := congrArg Subtype.val heq
          have hb1 : t.1 = e₀ := by
            have hmem : t.1 ∈ insert e₀ s.1 := by
              rw [← hT, hfin]
              exact Finset.mem_insert_self t.1 s.1
            simp only [Finset.mem_insert] at hmem
            rcases hmem with h | hmemS
            · exact h
            · exact absurd hmemS (Finset.mem_compl.mp t.2)
          have hbeq : t = (⟨e₀, hi₀⟩ : ↥(s.1ᶜ)) := Subtype.ext hb1
          exact htne hbeq
        rw [ite_eq_right hne]
        exact smul_zero _
      rw [Finset.sum_eq_single (⟨e₀, hi₀⟩ : ↥(s.1ᶜ)) h0
        (fun h => absurd (Finset.mem_univ (⟨e₀, hi₀⟩ : ↥(s.1ᶜ))) h)]
      have hins0 : T = (⟨insert e₀ s.1,
        powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) e₀
          (Finset.mem_compl.mp hi₀))⟩ :
          ↥(Set.powersetCard (Fin m) (k+1))) := by
        apply Subtype.ext
        change T.1 = insert e₀ s.1
        exact hT
      rw [ite_eq_left hins0, smul_eq_mul, mul_one]
    rw [hLHS, hRHS]
    have hpos : j₀.val = (s.1.filter (· < e₀)).card := by
      have hTpos := orderEmbOfFin_filter_card m T.1 (powersetCard_card T) j₀
      rw [hj₀] at hTpos
      have hfil : T.1.filter (· < e₀) = s.1.filter (· < e₀) := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · intro hx
          have hxT : x ∈ insert e₀ s.1 := by rw [← hT]; exact hx.1
          simp only [Finset.mem_insert] at hxT
          rcases hxT with rfl | hxs
          · exact (ne_of_lt hx.2 rfl).elim
          · exact ⟨hxs, hx.2⟩
        · intro hx
          exact ⟨hsub hx.1, hx.2⟩
      rw [hfil] at hTpos
      exact hTpos.symm
    rw [hj₀, hpos]
  · have hL0 : (∑ j : Fin (k+1), ((-1 : R)^(j.val) *
          φ (b (T.1.orderEmbOfFin (powersetCard_card T) j))) •
        (if (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j),
            powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) j)⟩ :
            ↥(Set.powersetCard (Fin m) k)) = s then (1 : R) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hne : (⟨T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j),
          powersetCard_mem (erase_emb_card m T.1 (powersetCard_card T) j)⟩ :
          ↥(Set.powersetCard (Fin m) k)) ≠ s := by
        intro heq
        have hfin : T.1.erase (T.1.orderEmbOfFin (powersetCard_card T) j) = s.1 :=
          congrArg Subtype.val heq
        have hsub' : s.1 ⊆ T.1 := by
          rw [← hfin]
          exact Finset.erase_subset _ _
        exact hsub hsub'
      rw [ite_eq_right hne]
      exact smul_zero _
    have hR0 : (∑ i : ↥(s.1ᶜ), ((-1 : R)^((s.1.filter (· < i.1)).card) *
          φ (b i.1)) •
        (if T = (⟨insert i.1 s.1, powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) i.1
            (Finset.mem_compl.mp i.2))⟩ :
            ↥(Set.powersetCard (Fin m) (k+1))) then (1 : R) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hne : T ≠ (⟨insert i.1 s.1,
        powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s) i.1
          (Finset.mem_compl.mp i.2))⟩ :
          ↥(Set.powersetCard (Fin m) (k+1))) := by
        intro heq
        have hfin : T.1 = insert i.1 s.1 := congrArg Subtype.val heq
        have hsub' : s.1 ⊆ T.1 := by
          rw [hfin]
          exact Finset.subset_insert _ _
        exact hsub hsub'
      rw [ite_eq_right hne]
      exact smul_zero _
    rw [hL0, hR0]

/-! ### §14e. Shift compatibility and the unconditional shift iso over a
`CommRing` (mirror of §12, R-D4 result)

The signed shift piece satisfies `koszulShiftCompat_commRing`: on
dual-basis elements both sides expand (§14d) into sums matched by complement
reindexing, with `neg_one_pow_sub_add_commRing` absorbing the
contraction-position signs into the Hodge weights. Instantiating the
conditional `koszulShiftIso_commRing` (§14b) gives the unconditional
`Hom(K, R) ≅ K[m]` over a `CommRing` — the exact shape §13's bridge
residuals consume once homology transport proves.
-/

/-- Transport of a graded linear map along a countdown index equation,
applied to a vector (mirror of `koszulShiftD_apply_aux`).
-/
theorem koszulShiftD_apply_aux_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] R) (a b : ℕ) (e : a + 1 = b)
    (x : ↥(⋀[R]^b M)) :
    (e ▸ koszulContract φ a) x = koszulContract φ a (e.symm ▸ x) := by
  cases e
  rfl

/-- The shift differential applied to a vector is the contraction applied
to the cast vector (mirror of `koszulShiftD_apply`).
-/
theorem koszulShiftD_apply_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m k : ℕ)
    (φ : M →ₗ[R] R) (h : k + 1 ≤ m)
    (x : ↥(⋀[R]^(m - k) M)) :
    koszulShiftD_commRing R M m k φ h x =
      koszulContract φ (m - (k + 1))
        ((koszulShiftD_index_eq m k h).symm ▸ x) := by
  unfold koszulShiftD_commRing
  exact koszulShiftD_apply_aux_commRing R M φ _ _ (koszulShiftD_index_eq m k h) x

/-- Casts commute with scalar multiplication (mirror of
`cast_smul_exteriorPower`).
-/
theorem cast_smul_exteriorPower_commRing (R : Type*) [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {a c : ℕ}
    (e : a = c) (t : R) (v : ↥(⋀[R]^a M)) :
    (e ▸ (t • v)) = t • (e ▸ v) := by
  cases e
  rfl

/-- Casts commute with exterior-power basis elements (mirror of
`cast_exteriorPower_basis`).
-/
theorem cast_exteriorPower_basis_commRing (R : Type*) [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {m a c : ℕ}
    (b : Module.Basis (Fin m) R M) (e : a = c)
    (s : ↥(Set.powersetCard (Fin m) a)) :
    (e ▸ (b.exteriorPower a) s) =
      (b.exteriorPower c) ⟨s.1, e ▸ s.2⟩ := by
  cases e
  rfl

/-- The Hodge sign weight coerced to `R` is `(-1)` to the index sum
(mirror of `hodgeSignWeight_coe`).
-/
theorem hodgeSignWeight_coe_commRing (R : Type*) [CommRing R] (m k : ℕ)
    (s : ↥(Set.powersetCard (Fin m) k)) :
    ((hodgeSignWeight_commRing R m k s : Rˣ) : R) =
      (-1 : R)^(s.1.sum fun i => i.val) := by
  simp [hodgeSignWeight_commRing]

/-- The coerced sign weight of an inserted set splits off the new factor
(mirror of `hodgeSignWeight_coe_insert`).
-/
theorem hodgeSignWeight_coe_insert_commRing (R : Type*) [CommRing R] (m k : ℕ)
    (S : Finset (Fin m)) (a : Fin m) (hi : a ∉ S)
    (hmem : insert a S ∈ Set.powersetCard (Fin m) (k + 1)) :
    ((hodgeSignWeight_commRing R m (k + 1) ⟨insert a S, hmem⟩ : Rˣ) : R) =
      (-1 : R)^(S.sum fun j => j.val) * (-1 : R)^(a.val) := by
  simp only [hodgeSignWeight_commRing, Units.val_pow_eq_pow_val,
    Units.coe_neg_one]
  change (-1 : R)^((insert a S).sum fun j => j.val) =
    (-1 : R)^(S.sum fun j => j.val) * (-1 : R)^(a.val)
  exact neg_one_pow_sum_insert_commRing R m S a hi

/-- The signed shift piece satisfies shift compatibility over a `CommRing`
(mirror of `koszulShiftCompat_signed`). Both sides are expanded on
dual-basis elements (`koszulDualD_basis_commRing`,
`koszulContract_basis_commRing`), the contraction sum is reindexed over the
complement (`Fintype.sum_bijective` along `orderIsoOfFin`), and each pair
of terms agrees by `neg_one_pow_sub_add_commRing` (`ring`) on scalars and
`compl_insert_erase` on basis vectors. This discharges the R-D4 residual.
-/
theorem koszulShiftCompat_signed_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R) :
    koszulShiftCompat_commRing R M m φ
      (koszulShiftPieceSignedMap_commRing R M m · b) := by
  intro k h
  have hk : k ≤ m := by omega
  refine Module.Basis.ext
    (((b.exteriorPower k).dualBasis)) (fun s => ?_)
  simp only [LinearMap.comp_apply]
  rw [koszulShiftPieceSignedMap_commRing_of_le R M m k b hk]
  simp only [LinearEquiv.coe_coe,
    koszulShiftPieceSigned_commRing_apply_dualBasis]
  rw [koszulShiftD_apply_commRing, cast_smul_exteriorPower_commRing,
    cast_exteriorPower_basis_commRing, map_smul]
  change ↑(hodgeSignWeight_commRing R m k s) •
        koszulContract φ (m - (k + 1))
          ((b.exteriorPower ((m - (k + 1)).succ))
            (⟨(powersetCardComplEquiv m k hk s).1,
              (koszulShiftD_index_eq m k h).symm ▸
                (powersetCardComplEquiv m k hk s).2⟩ :
              ↥(Set.powersetCard (Fin m) (m - (k + 1) + 1)))) =
      (koszulShiftPieceSignedMap_commRing R M m (k + 1) b)
        (koszulDualD φ k
          (((b.exteriorPower k).dualBasis) s))
  rw [koszulContract_basis_commRing]
  rw [koszulDualD_basis_commRing,
    koszulShiftPieceSignedMap_commRing_of_le R M m (k + 1) b h]
  simp only [map_sum, map_smul, LinearEquiv.coe_coe,
    koszulShiftPieceSigned_commRing_apply_dualBasis]
  have hcard : s.1ᶜ.card = (m - (k + 1)).succ := by
    rw [Finset.card_compl, Fintype.card_fin, powersetCard_card s]
    omega
  rw [Finset.smul_sum]
  refine Fintype.sum_bijective ⇑((s.1ᶜ.orderIsoOfFin hcard).toEquiv)
    ((s.1ᶜ.orderIsoOfFin hcard).toEquiv.bijective) _ _ (fun j => ?_)
  have hunit : ∀ (u : Rˣ) (x : ↥(⋀[R]^(m - (k + 1)) M)),
      u • x = (u : R) • x := fun u x => rfl
  simp only [hunit, smul_smul]
  have hi : (((s.1ᶜ.orderIsoOfFin hcard).toEquiv j).1) ∉ s.1 :=
    Finset.mem_compl.mp (((s.1ᶜ.orderIsoOfFin hcard).toEquiv j).2)
  have hsign := hodgeSignWeight_coe_insert_commRing R m k s.1
    (((s.1ᶜ.orderIsoOfFin hcard).toEquiv j).1) hi
    (powersetCard_mem (insert_mem_card m s.1 (powersetCard_card s)
      (((s.1ᶜ.orderIsoOfFin hcard).toEquiv j).1)
      (Finset.mem_compl.mp (((s.1ᶜ.orderIsoOfFin hcard).toEquiv j).2))))
  have hcount :
      j.val + (s.1.filter (· < s.1ᶜ.orderEmbOfFin hcard j)).card =
        (s.1ᶜ.orderEmbOfFin hcard j).val := by
    have h1 := orderEmbOfFin_filter_card m s.1ᶜ hcard j
    have h2 := filter_compl_card m s.1 (s.1ᶜ.orderEmbOfFin hcard j)
    have hle := filter_card_le m s.1 (s.1ᶜ.orderEmbOfFin hcard j)
    omega
  have hkey :
      (-1 : R)^(s.1.sum fun i => i.val) *
          ((-1 : R)^(j.val) *
            φ (b (s.1ᶜ.orderEmbOfFin hcard j))) =
        (((-1 : R)^((s.1.filter (· < s.1ᶜ.orderEmbOfFin hcard j)).card) *
          φ (b (s.1ᶜ.orderEmbOfFin hcard j))) *
          ((-1 : R)^(s.1.sum fun i => i.val) *
            (-1 : R)^((s.1ᶜ.orderEmbOfFin hcard j).val))) := by
    have hj' : j.val = (s.1ᶜ.orderEmbOfFin hcard j).val -
        (s.1.filter (· < s.1ᶜ.orderEmbOfFin hcard j)).card := by omega
    have hle : (s.1.filter (· < s.1ᶜ.orderEmbOfFin hcard j)).card ≤
        (s.1ᶜ.orderEmbOfFin hcard j).val := by omega
    rw [hj', neg_one_pow_sub_add_commRing R _ _ hle, pow_add]
    ring
  rw [hsign, hodgeSignWeight_coe_commRing]
  refine congrArg₂ _ hkey ?_
  refine congrArg _ (Subtype.ext ?_)
  change (s.1ᶜ).erase (s.1ᶜ.orderEmbOfFin hcard j) =
    (insert (s.1ᶜ.orderEmbOfFin hcard j) s.1)ᶜ
  rw [compl_insert_erase]

/-- The R-D4 shift iso `Hom(K, R) ≅ K[m]` over a `CommRing` as complexes,
unconditional: `koszulShiftIso_commRing` (§14b) instantiated with the
signed degree maps, whose compatibility
(`koszulShiftCompat_signed_commRing`) and inverse laws
(`koszulShiftPieceSigned_commRing_left/right`) discharge the residual.
This is the exact shape §13's bridge residuals consume once homology
transport proves (the `HomologyTransport.lean` follow-up): R2 exactness of
`K(sop)` over `R_P` then transports through this iso to
`koszulHomCocycleExactBelow` + `koszulHomZeroExact`.
-/
noncomputable def koszulShiftIsoSigned_commRing (R : Type*) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (m : ℕ)
    (b : Module.Basis (Fin m) R M) (φ : M →ₗ[R] R) :
    (koszulDualComplex φ) ≅ (koszulShiftComplex_commRing R M m φ) :=
  koszulShiftIso_commRing R M m b φ
    (koszulShiftPieceSignedMap_commRing R M m · b)
    (koszulShiftPieceSignedInvMap_commRing R M m · b)
    (koszulShiftCompat_signed_commRing R M m b φ)
    (fun k hk => koszulShiftPieceSigned_commRing_left R M m k b hk)
    (fun k hk => koszulShiftPieceSigned_commRing_right R M m k b hk)

/-- Sequence form of the R-D4 shift iso: `K(x)` for `x : Fin m → R` (the
`K(sop)` shape over `R_P` with sop length `m`), otherwise identical to
`koszulShiftIsoSigned_commRing`.
-/
noncomputable def koszulShiftIsoSigned_commRing_ofSequence (R : Type*) [CommRing R]
    (m : ℕ) (x : Fin m → R) :
    (koszulDualComplex (koszulContractOfSequence x)) ≅
      (koszulShiftComplex_commRing R (Fin m → R) m
        (koszulContractOfSequence x)) :=
  koszulShiftIsoSigned_commRing R (Fin m → R) m (Pi.basisFun R (Fin m))
    (koszulContractOfSequence x)

end SelfDuality
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

-- Note: only new variables are declared here: the §13 `uShiftObj`/`uRD3`
-- are still in scope at top level (re-listing them errors as
-- already-declared), and §15 never names them. All §15 variables are on
-- one line since `universe` commands replace the in-scope list.
universe uC2 vCC uCC uII

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace SelfDuality

open CategoryTheory HomologicalComplex KoszulComplex AugmentedConeStep ReducedMasters
  QuasiIsomorphismBridge GradedSurjection

/-! ## §15. C2 master: Ext-subsingletons below `d` on `[hker]` (R-D3 discharge)

Step A5 (part 2, C2 close) of the scoped Koszul/AB plan: the §13 master
(`koszulExt_subsingleton_below_ofSequence`) instantiated at the A6 shape
(`X := ↧(Shrink (R_P ⧸ m))`, `Y := R_P`, `n := d`) with both residuals
discharged from R2 exactness on `[hker]` (+ `1 ≤ d`):

* (π) S2's residue augmentation `koszulResiduePi` (QuasiBridge, sequence
  form up to the definitional `koszulChainComplexOfSequence` unfolding)
  pushed along the `Shrink.linearEquiv` ModuleCat iso to the A6
  `residueCat`-shaped target; `QuasiIso` survives via `quasiIso_comp`
  with the iso leg (`quasiIso_of_isIso` + `Functor.map_isIso`).
* (Hom) S4's Hom-pair `koszulHomBridge_of_r2Reduced` (HomTransport §7):
  re-proved here (§15a–§15d) since `HomologyTransport` imports this
  file — importing it back would be circular. The proofs are the same
  Mathlib-first chases, with `c2`-prefixed names to avoid any ambiguity
  in files opening both namespaces.

Smallness side-conditions: `Shrink.linearEquiv` needs
`Small.{uC2} (R_P ⧸ m)` and `HasExt (ModuleCat.{uC2} R_P)` needs
`Small.{uC2} R_P`; both fire via `small_self`
(`Mathlib/Logic/Small/Defs.lean`) since everything lives in
`Type uC2` — no extra hypotheses.

References: `Regularity/Koszul/QuasiIsomorphismBridge.lean` (`koszulResiduePi`,
`koszulResiduePi_quasiIso`), `Regularity/Multiplicity/ReducedMasters.lean`
(`grlift_r2_exact_reduced`), `Regularity/Koszul/HomologyTransport.lean` (§§2–7,
proof source for §15a–§15d), Mathlib
`Algebra/Module/Shrink.lean` (`Shrink.linearEquiv`),
`Algebra/Category/ModuleCat/Basic.lean` (`toModuleIso`),
`Algebra/Homology/QuasiIso.lean,159` (`quasiIso_of_isIso`,
`quasiIso_comp`).

Conditional on exactly `[hker]` (+ `1 ≤ d`); `hgen` is ambient sop
data. This closes C2 (R-D3) modulo the `hwit`-chain `hker`.
-/

/-! ### §15a. Transport core (HomTransport §§2–4, `c2` copies) -/

/-- An isomorphism of homological complexes transports exactness at every
degree, in both directions (each direction is `ExactAt.of_iso`).
-/
theorem c2_iso_exactAt_iff {C : Type uCC} [Category.{vCC} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type uII}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (e : K ≅ L)
    (i : ι) : K.ExactAt i ↔ L.ExactAt i :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- `prev` of a successor for the cohomology shape.
-/
theorem c2_up_prev_succ (j : ℕ) : (ComplexShape.up ℕ).prev (j + 1) = j :=
  ComplexShape.prev_eq' _ (ComplexShape.up_mk j (j + 1) rfl)

/-- `next` of a successor for the cohomology shape.
-/
theorem c2_up_next_succ (j : ℕ) :
    (ComplexShape.up ℕ).next (j + 1) = (j + 1) + 1 :=
  ComplexShape.next_eq' _ (ComplexShape.up_mk (j + 1) ((j + 1) + 1) rfl)

/-- `next` of `0` for the cohomology shape (stated as `0 + 1` so the
`koszulDualMor_succ` rewrite matches syntactically).
-/
theorem c2_up_next_zero : (ComplexShape.up ℕ).next 0 = 0 + 1 :=
  ComplexShape.next_eq' _ (ComplexShape.up_mk 0 (0 + 1) rfl)

/-- `prev` of `0` is `0`: no degree maps into degree `0`.
-/
theorem c2_up_prev_zero : (ComplexShape.up ℕ).prev 0 = 0 := by
  apply ComplexShape.prev_eq_self _ 0
  intro hRel
  have hEq : (ComplexShape.up ℕ).prev 0 + 1 = 0 := hRel
  omega

/-- The dual differential is post-composition with the contraction.
-/
theorem c2_koszulDualD_eq_comp {R M : Type uC2} [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] R) (k : ℕ)
    (g : Module.Dual R ↥(⋀[R]^k M)) :
    koszulDualD φ k g = g.comp (koszulContract φ k) :=
  LinearMap.dualMap_apply' _ _

/-- Positive-degree bridge: `ExactAt` of `koszulDualComplex φ` at `j + 1`
implies every Koszul `(j+1)`-cocycle with `R` coefficients is a
coboundary.
-/
theorem c2_dualExactAt_cocycle_succ {R M : Type uC2} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (j : ℕ)
    (h : (koszulDualComplex φ).ExactAt (j + 1))
    (f : (koszulChainComplex φ).X (j + 1) ⟶ ModuleCat.of R R)
    (m : ℕ) (hm : j + 1 + 1 = m)
    (hf : (koszulChainComplex φ).d m (j + 1) ≫ f = 0) :
    ∃ g : (koszulChainComplex φ).X j ⟶ ModuleCat.of R R,
      (koszulChainComplex φ).d (j + 1) j ≫ g = f := by
  have hprev := c2_up_prev_succ j
  have hnext := c2_up_next_succ j
  rw [HomologicalComplex.exactAt_iff' _ _ _ _ hprev hnext] at h
  rw [ShortComplex.moduleCat_exact_iff _] at h
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g,
    koszulDualComplex_d, koszulDualMor_succ] at h
  have hclean : ∀ x₂ : Module.Dual R ↥(⋀[R]^(j + 1) M),
      koszulDualD φ (j + 1) x₂ = 0 →
      ∃ x₁ : Module.Dual R ↥(⋀[R]^j M), koszulDualD φ j x₁ = x₂ := h
  subst hm
  have hcomp : f.hom.comp (koszulContract φ (j + 1)) = 0 := by
    have h0 := congrArg ModuleCat.Hom.hom hf
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h0
    have hd_hom : ((koszulChainComplex φ).d (j + 1 + 1) (j + 1)).hom
        = koszulContract φ (j + 1) := by
      have e1 : (koszulChainComplex φ).d (j + 1 + 1) (j + 1)
          = ModuleCat.ofHom (koszulContract φ (j + 1)) := by
        rw [koszulChainComplex_d, koszulCMor_succ]
      rw [e1]
      rfl
    rw [hd_hom] at h0
    exact h0
  have hcoc : koszulDualD φ (j + 1) f.hom = 0 := by
    have e := c2_koszulDualD_eq_comp φ (j + 1) f.hom
    rw [e]
    exact hcomp
  obtain ⟨x₁, hx₁⟩ := hclean f.hom hcoc
  let hg : (koszulChainComplex φ).X j ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom x₁
  have hghom : hg.hom = x₁ := rfl
  refine ⟨hg, ?_⟩
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, hghom]
  have hd_hom : ((koszulChainComplex φ).d (j + 1) j).hom
      = koszulContract φ j := by
    have e1 : (koszulChainComplex φ).d (j + 1) j
        = ModuleCat.ofHom (koszulContract φ j) := by
      rw [koszulChainComplex_d, koszulCMor_succ]
    rw [e1]
    rfl
  rw [hd_hom]
  exact (c2_koszulDualD_eq_comp φ j x₁).symm.trans hx₁

/-- Degree-0 bridge: `ExactAt` of `koszulDualComplex φ` at `0` implies
every `0`-cocycle with `R` coefficients is zero.
-/
theorem c2_dualExactAt_zero {R M : Type uC2} [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] R)
    (h : (koszulDualComplex φ).ExactAt 0)
    (f : (koszulChainComplex φ).X 0 ⟶ ModuleCat.of R R)
    (hf : (koszulChainComplex φ).d 1 0 ≫ f = 0) : f = 0 := by
  have hprev := c2_up_prev_zero
  have hnext := c2_up_next_zero
  rw [HomologicalComplex.exactAt_iff' _ _ _ _ hprev hnext] at h
  rw [ShortComplex.moduleCat_exact_iff _] at h
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g,
    koszulDualComplex_d, koszulDualMor_succ] at h
  have hd00 : (koszulDualComplex φ).d 0 0 = 0 := by
    rw [koszulDualComplex_d]
    unfold koszulDualMor
    exact dite_eq_right (by omega)
  rw [← koszulDualComplex_d, hd00] at h
  have hclean : ∀ x₂ : Module.Dual R ↥(⋀[R]^0 M),
      koszulDualD φ 0 x₂ = 0 →
      ∃ x₁ : Module.Dual R ↥(⋀[R]^0 M),
        (0 : (koszulDualComplex φ).X 0 ⟶
          (koszulDualComplex φ).X 0) x₁ = x₂ := h
  have hf' : (koszulChainComplex φ).d (0 + 1) 0 ≫ f = 0 := hf
  have hcomp : f.hom.comp (koszulContract φ 0) = 0 := by
    have h0 := congrArg ModuleCat.Hom.hom hf'
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h0
    have hd_hom : ((koszulChainComplex φ).d (0 + 1) 0).hom
        = koszulContract φ 0 := by
      have e1 : (koszulChainComplex φ).d (0 + 1) 0
          = ModuleCat.ofHom (koszulContract φ 0) := by
        rw [koszulChainComplex_d, koszulCMor_succ]
      rw [e1]
      rfl
    rw [hd_hom] at h0
    exact h0
  have hcoc : koszulDualD φ 0 f.hom = 0 := by
    have e := c2_koszulDualD_eq_comp φ 0 f.hom
    rw [e]
    exact hcomp
  obtain ⟨x₁, hx₁⟩ := hclean f.hom hcoc
  have h0app : (0 : (koszulDualComplex φ).X 0 ⟶
      (koszulDualComplex φ).X 0) x₁ = 0 := rfl
  rw [h0app] at hx₁
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  exact hx₁.symm

/-- Positive-degree master: `koszulHomCocycleExactBelow` from the shift
iso plus shift-side exactness.

Conditional on exactly `(e, hS)`. -/
theorem c2_koszulHomCocycleExactBelow_of_iso {R M : Type uC2} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) {d : ℕ}
    {S : CochainComplex (ModuleCat.{uC2} R) ℕ}
    (e : koszulDualComplex φ ≅ S)
    (hS : ∀ i : ℕ, 1 ≤ i → i < d → S.ExactAt i) :
    koszulHomCocycleExactBelow φ (Y := ModuleCat.of R R) d := by
  intro i hi1 hid f m hm hf p hp
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hpj : j = p := by omega
  subst hpj
  have hdual : (koszulDualComplex φ).ExactAt (j + 1) :=
    (c2_iso_exactAt_iff e (j + 1)).mpr (hS (j + 1) (by omega) hid)
  exact c2_dualExactAt_cocycle_succ φ j hdual f m hm hf

/-- Degree-0 master: `koszulHomZeroExact` from the shift iso plus
exactness of `S` at `0`.

Conditional on exactly `(e, hS0)`. -/
theorem c2_koszulHomZeroExact_of_iso {R M : Type uC2} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)
    {S : CochainComplex (ModuleCat.{uC2} R) ℕ}
    (e : koszulDualComplex φ ≅ S) (hS0 : S.ExactAt 0) :
    koszulHomZeroExact φ (Y := ModuleCat.of R R) := by
  intro f hf
  have hdual : (koszulDualComplex φ).ExactAt 0 :=
    (c2_iso_exactAt_iff e 0).mpr hS0
  exact c2_dualExactAt_zero φ hdual f hf

/-- Sequence form of the combined bridge.

Conditional on exactly `(e, hS, hS0)`. -/
theorem c2_koszulHomBridge_ofSequence_of_iso {R : Type uC2}
    [CommRing R] {n d : ℕ} (x : Fin n → R)
    {S : CochainComplex (ModuleCat.{uC2} R) ℕ}
    (e : koszulDualComplex (koszulContractOfSequence x) ≅ S)
    (hS : ∀ i : ℕ, 1 ≤ i → i < d → S.ExactAt i)
    (hS0 : S.ExactAt 0) :
    koszulHomCocycleExactBelow (koszulContractOfSequence x)
        (Y := ModuleCat.of R R) d ∧
      koszulHomZeroExact (koszulContractOfSequence x)
        (Y := ModuleCat.of R R) :=
  ⟨c2_koszulHomCocycleExactBelow_of_iso _ e hS,
    c2_koszulHomZeroExact_of_iso _ e hS0⟩

/-! ### §15b. Shift-side chase toolkit (HomTransport §5, `c2` copies) -/

/-- Applying the shift differential: `eqToHom` conjugation unfolds to
nested application.
-/
theorem c2_shiftAt_apply {R : Type uC2} [CommRing R] {M : Type uC2}
    [AddCommGroup M] [Module R M] {m i : ℕ} {φ : M →ₗ[R] R}
    {hle : i + 1 ≤ m}
    (e1 : koszulShiftObj_commRing R M m i
      = ModuleCat.of R ↥(⋀[R]^(m - i) M))
    (e2 : koszulShiftObj_commRing R M m (i + 1)
      = ModuleCat.of R ↥(⋀[R]^(m - (i + 1)) M))
    (x : ↥(koszulShiftObj_commRing R M m i)) :
    koszulShiftAt_commRing R M m φ i (i + 1) rfl hle x =
      eqToHom e2.symm
        ((koszulShiftD_commRing R M m i φ hle) (eqToHom e1 x)) := rfl

/-- `eqToHom` round trip at application level.
-/
theorem c2_eqToHom_inv_hom_apply {R : Type uC2} [CommRing R]
    {A B : ModuleCat.{uC2} R} (e : A = B) (x : ↥A) :
    eqToHom e.symm (eqToHom e x) = x := by
  have h := ModuleCat.inv_hom_apply (eqToIso e) x
  simpa using h

/-- `eqToHom` round trip, other direction.
-/
theorem c2_eqToHom_hom_inv_apply {R : Type uC2} [CommRing R]
    {A B : ModuleCat.{uC2} R} (e : A = B) (x : ↥B) :
    eqToHom e (eqToHom e.symm x) = x := by
  have h := ModuleCat.hom_inv_apply (eqToIso e) x
  simpa using h

/-- Exterior-power cast round trip.
-/
theorem c2_exteriorCast_roundtrip {R : Type uC2} [CommRing R] {M : Type uC2}
    [AddCommGroup M] [Module R M] {a b : ℕ} (e1 : a = b) (e2 : b = a)
    (y : ↥(⋀[R]^b M)) :
    (e1 ▸ ((e2 ▸ y : ↥(⋀[R]^a M))) : ↥(⋀[R]^b M)) = y := by
  cases e1
  cases e2
  rfl

/-- A cast is zero only if the original is zero.
-/
theorem c2_exteriorCast_eq_zero {R : Type uC2} [CommRing R] {M : Type uC2}
    [AddCommGroup M] [Module R M] {a b : ℕ} (e : a = b) (y : ↥(⋀[R]^a M))
    (h : (e ▸ y : ↥(⋀[R]^b M)) = 0) : y = 0 := by
  cases e
  exact h

/-- Casts preserve the underlying exterior element.
-/
theorem c2_exteriorCast_val {R : Type uC2} [CommRing R] {M : Type uC2}
    [AddCommGroup M] [Module R M] {a b : ℕ} (e : a = b) (z : ↥(⋀[R]^a M)) :
    (((e ▸ z : ↥(⋀[R]^b M))) : ExteriorAlgebra R M)
      = (z : ExteriorAlgebra R M) := by
  cases e
  rfl

/-- Contraction commutes with index casts.
-/
theorem c2_koszulContract_cast {R : Type uC2} [CommRing R] {M : Type uC2}
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) {a b : ℕ} (e : a = b)
    (w : ↥(⋀[R]^(a + 1) M)) :
    koszulContract φ b ((congrArg (· + 1) e) ▸ w)
      = (e ▸ koszulContract φ a w) := by
  apply Subtype.ext
  show (((koszulContract φ b _) : ↥(⋀[R]^b M)) : ExteriorAlgebra R M) = _
  rw [koszulContract_apply]
  rw [c2_exteriorCast_val]
  rw [c2_exteriorCast_val]
  rw [koszulContract_apply]

/-! ### §15c. Shift exactness from `contractExactAt` (HomTransport §6) -/

/-- Positive-degree shift exactness from one `contractExactAt` instance
at the countdown index `m - (i+1)`.
-/
theorem c2_shiftExactAt_of_contractExact {R : Type uC2} [CommRing R]
    {M : Type uC2} [AddCommGroup M] [Module R M] {m : ℕ} (φ : M →ₗ[R] R)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i + 1 ≤ m)
    (hexact : AugmentedConeStep.contractExactAt φ (m - (i + 1))) :
    (koszulShiftComplex_commRing R M m φ).ExactAt i := by
  obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
  have hle1 : t + 1 ≤ m := by omega
  have hle2 : t + 1 + 1 ≤ m := him
  rw [HomologicalComplex.exactAt_iff' _ _ _ _
    (c2_up_prev_succ t) (c2_up_next_succ t)]
  rw [ShortComplex.moduleCat_exact_iff]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g,
    koszulShiftComplex_commRing_d]
  rw [koszulShiftMor_commRing_succ_of_le R M m φ t hle1,
    koszulShiftMor_commRing_succ_of_le R M m φ (t + 1) hle2]
  change ∀ x₂ : ↥(koszulShiftObj_commRing R M m (t + 1)),
    koszulShiftAt_commRing R M m φ (t + 1) (t + 1 + 1) rfl hle2 x₂ = 0 →
    ∃ x₁ : ↥(koszulShiftObj_commRing R M m t),
      koszulShiftAt_commRing R M m φ t (t + 1) rfl hle1 x₁ = x₂
  intro x₂ hx₂
  have eB : koszulShiftObj_commRing R M m (t + 1)
      = ModuleCat.of R ↥(⋀[R]^(m - (t + 1)) M) :=
    koszulShiftObj_commRing_eq_of_le R M m (t + 1) hle1
  have eC : koszulShiftObj_commRing R M m (t + 1 + 1)
      = ModuleCat.of R ↥(⋀[R]^(m - (t + 1 + 1)) M) :=
    koszulShiftObj_commRing_eq_of_le R M m (t + 1 + 1) hle2
  have eA : koszulShiftObj_commRing R M m t
      = ModuleCat.of R ↥(⋀[R]^(m - t) M) :=
    koszulShiftObj_commRing_eq_of_le R M m t (by omega)
  rw [c2_shiftAt_apply eB eC] at hx₂
  set y₂ : ↥(⋀[R]^(m - (t + 1)) M) := eqToHom eB x₂ with hy₂
  have hD : koszulShiftD_commRing R M m (t + 1) φ hle2 y₂ = 0 := by
    have h0 : eqToHom eC (eqToHom eC.symm
        (koszulShiftD_commRing R M m (t + 1) φ hle2 y₂)) = 0 := by
      rw [hx₂]
      simp
    rwa [c2_eqToHom_hom_inv_apply eC] at h0
  rw [koszulShiftD_apply_commRing] at hD
  obtain ⟨w, hw⟩ := hexact _ hD
  have e' : (m - (t + 1 + 1)) + 1 = m - (t + 1) := by omega
  have e_lo : m - (t + 1) + 1 = m - t :=
    koszulShiftD_index_eq m t hle1
  refine ⟨eqToHom eA.symm (e_lo ▸ ((congrArg (· + 1) e') ▸ w)), ?_⟩
  rw [c2_shiftAt_apply eA eB, c2_eqToHom_hom_inv_apply eA,
    koszulShiftD_apply_commRing]
  have hback : ((((koszulShiftD_index_eq m t hle1).symm ▸
      (e_lo ▸ ((congrArg (· + 1) e') ▸ w)))) : ↥(⋀[R]^(m - (t + 1) + 1) M))
      = ((((congrArg (· + 1) e') ▸ w)) : ↥(⋀[R]^(m - (t + 1) + 1) M)) :=
    c2_exteriorCast_roundtrip _ _ _
  rw [hback, c2_koszulContract_cast φ e' w, hw]
  have hfin : ((e' ▸
      (((koszulShiftD_index_eq m (t + 1) hle2).symm ▸ y₂))) :
      ↥(⋀[R]^(m - (t + 1)) M)) = y₂ :=
    c2_exteriorCast_roundtrip e' _ y₂
  rw [hfin, hy₂]
  exact c2_eqToHom_inv_hom_apply eB x₂

/-- Degree-0 shift exactness: the top contraction is injective. Needs
`1 ≤ m` (for `m = 0` the conclusion is false).
-/
theorem c2_shiftExactAt_zero_of_contractExact {R : Type uC2} [CommRing R]
    {M : Type uC2} [AddCommGroup M] [Module R M] {m : ℕ} (φ : M →ₗ[R] R)
    (hm1 : 1 ≤ m) (hexact : AugmentedConeStep.contractExactAt φ (m - 1))
    (hsub : Subsingleton ↥(⋀[R]^(m + 1) M)) :
    (koszulShiftComplex_commRing R M m φ).ExactAt 0 := by
  have hle : 0 + 1 ≤ m := hm1
  rw [HomologicalComplex.exactAt_iff' _ _ _ _ c2_up_prev_zero c2_up_next_zero]
  rw [ShortComplex.moduleCat_exact_iff]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g,
    koszulShiftComplex_commRing_d]
  have hd00 : koszulShiftMor_commRing R M m φ 0 0 = 0 := by
    unfold koszulShiftMor_commRing
    exact dite_eq_right (by omega)
  rw [hd00, koszulShiftMor_commRing_succ_of_le R M m φ 0 hle]
  change ∀ x₂ : ↥(koszulShiftObj_commRing R M m 0),
    koszulShiftAt_commRing R M m φ 0 (0 + 1) rfl hle x₂ = 0 →
    ∃ x₁ : ↥(koszulShiftObj_commRing R M m 0),
      (0 : koszulShiftObj_commRing R M m 0 ⟶
        koszulShiftObj_commRing R M m 0) x₁ = x₂
  intro x₂ hx₂
  have e0 : koszulShiftObj_commRing R M m 0
      = ModuleCat.of R ↥(⋀[R]^(m - 0) M) :=
    koszulShiftObj_commRing_eq_of_le R M m 0 (by omega)
  have e1 : koszulShiftObj_commRing R M m (0 + 1)
      = ModuleCat.of R ↥(⋀[R]^(m - (0 + 1)) M) :=
    koszulShiftObj_commRing_eq_of_le R M m (0 + 1) hle
  rw [c2_shiftAt_apply e0 e1] at hx₂
  set y₂ : ↥(⋀[R]^(m - 0) M) := eqToHom e0 x₂ with hy₂
  have hD : koszulShiftD_commRing R M m 0 φ hle y₂ = 0 := by
    have h0 : eqToHom e1 (eqToHom e1.symm
        (koszulShiftD_commRing R M m 0 φ hle y₂)) = 0 := by
      rw [hx₂]
      simp
    rwa [c2_eqToHom_hom_inv_apply e1] at h0
  rw [koszulShiftD_apply_commRing] at hD
  obtain ⟨w, hw⟩ := hexact _ hD
  have e_sub : ((m - 1) + 1) + 1 = m + 1 := by omega
  have hw0 : w = 0 := by
    have hcast : ((e_sub ▸ w : ↥(⋀[R]^(m + 1) M))) = 0 :=
      Subsingleton.elim _ _
    exact c2_exteriorCast_eq_zero e_sub w hcast
  rw [hw0, map_zero] at hw
  have hy₂0 : y₂ = 0 := by
    have hz : (((((koszulShiftD_index_eq m 0 hle).symm ▸ y₂))) :
        ↥(⋀[R]^(m - (0 + 1) + 1) M)) = 0 := hw.symm
    exact c2_exteriorCast_eq_zero _ _ hz
  have hx₂0 : x₂ = 0 := by
    have h : eqToHom e0.symm (eqToHom e0 x₂) = 0 := by
      rw [← hy₂, hy₂0]
      simp
    rwa [c2_eqToHom_inv_hom_apply e0] at h
  refine ⟨x₂, ?_⟩
  have h0app : (0 : koszulShiftObj_commRing R M m 0 ⟶
      koszulShiftObj_commRing R M m 0) x₂ = 0 := rfl
  rw [h0app, hx₂0]

/-! ### §15d. R2 discharge: the Hom-pair on `[hker]` (HomTransport §7) -/

/-- `hS` from R2: shift-side exactness below `d` over `R_P`.

Conditional on exactly `[hker]`. -/
theorem c2_shift_hS_of_r2Reduced {K : Type uC2} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    ∀ i : ℕ, 1 ≤ i → i < d →
      (koszulShiftComplex_commRing (Localization.AtPrime P)
        (Fin d → Localization.AtPrime P) d
        (koszulContractOfSequence g)).ExactAt i := by
  intro i hi1 hid
  exact c2_shiftExactAt_of_contractExact _ hi1 (by omega)
    ((grlift_r2_exact_reduced P d g hgen hker) _)

/-- `hS0` from R2: shift-side exactness at `0` over `R_P`. The `1 ≤ d`
side condition is necessary (`d = 0` makes the conclusion false).

Conditional on exactly `[hker, 1 ≤ d]`. -/
theorem c2_shift_hS0_of_r2Reduced {K : Type uC2} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥)
    (hd1 : 1 ≤ d) :
    (koszulShiftComplex_commRing (Localization.AtPrime P)
      (Fin d → Localization.AtPrime P) d
      (koszulContractOfSequence g)).ExactAt 0 :=
  c2_shiftExactAt_zero_of_contractExact _ hd1
    ((grlift_r2_exact_reduced P d g hgen hker) _)
    (exteriorPower_subsingleton_of_gt_commRing _ _ d (d + 1)
      (Pi.basisFun (Localization.AtPrime P) (Fin d)) (by omega))

/-- Combined §13 bridge from R2: both Hom-exactness residuals at
`Y = R_P` from the §14 shift iso plus R2 exactness.

Conditional on exactly `[hker, 1 ≤ d]`. -/
theorem c2_koszulHomBridge_of_r2Reduced {K : Type uC2} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥)
    (hd1 : 1 ≤ d) :
    koszulHomCocycleExactBelow (koszulContractOfSequence g)
        (Y := ModuleCat.of (Localization.AtPrime P)
          (Localization.AtPrime P)) d ∧
      koszulHomZeroExact (koszulContractOfSequence g)
        (Y := ModuleCat.of (Localization.AtPrime P)
          (Localization.AtPrime P)) :=
  c2_koszulHomBridge_ofSequence_of_iso g
    (koszulShiftIsoSigned_commRing_ofSequence _ d g)
    (c2_shift_hS_of_r2Reduced P d g hgen hker)
    (c2_shift_hS0_of_r2Reduced P d g hgen hker hd1)

/-! ### §15e. Shrink-wrapped residue augmentation (S2's pi, A6 shape) -/

/-- The Shrink-wrapped residue object is isomorphic (as a `ModuleCat`
object) to S2's `koszulResidueField`, via `Shrink.linearEquiv`. The
`Small.{uC2}` side-condition fires via `small_self`.
-/
noncomputable def koszulResidueShrinkIso {K : Type uC2} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] :
    ModuleCat.of (Localization.AtPrime P)
        (Shrink.{uC2} ((Localization.AtPrime P) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime P))) ≅
      koszulResidueField P :=
  (Shrink.linearEquiv (Localization.AtPrime P)
    ((Localization.AtPrime P) ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime P))).toModuleIso

/-- S2's residue augmentation, re-targeted to the A6 `residueCat`-shaped
object: `koszulResiduePi` (whose domain is definitionally
`koszulChainComplexOfSequence g`) pushed along the Shrink iso.
-/
noncomputable def koszulResiduePiShrink {K : Type uC2} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    koszulChainComplexOfSequence g ⟶
      (ChainComplex.single₀ _).obj (ModuleCat.of (Localization.AtPrime P)
        (Shrink.{uC2} ((Localization.AtPrime P) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime P)))) :=
  koszulResiduePi P d g hgen ≫
    (ChainComplex.single₀ _).map (koszulResidueShrinkIso P).symm.hom

/-- The Shrink-wrapped augmentation is a quasi-isomorphism: the S2
quasi-iso composed with the iso leg (`quasiIso_comp` with
`quasiIso_of_isIso` + `Functor.map_isIso`, all instances).

Conditional on exactly `[hker]`. -/
theorem koszulResiduePiShrink_quasiIso {K : Type uC2} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    QuasiIso (koszulResiduePiShrink P d g hgen) :=
  -- Explicit `quasiIso_comp`: the middle object is `single₀.obj` of
  -- `koszulResidueField P` on the S2 leg but of its unfolding on the
  -- `map` leg, so the instance is applied by hand (with `hπ` passed
  -- explicitly) rather than via `inferInstance` matching.
  @quasiIso_comp _ _ _ _ _ _ _ _
    (koszulResiduePi P d g hgen)
    ((ChainComplex.single₀ _).map (koszulResidueShrinkIso P).symm.hom)
    _ _ _ (koszulResiduePi_quasiIso P d g hgen hker)
    (quasiIso_of_isIso _)

/-! ### §15f. C2 master -/

/-- C2 master (R-D3 discharge): `Ext^i(X, Y)` is a subsingleton for all
`i < d` at the exact A6 shape (`X := ↧(Shrink (R_P ⧸ m))`,
`Y := R_P`), from the Shrink-wrapped S2 augmentation (§15e) plus the
R2-discharged Hom-pair (§15d) fed into the §13 sequence master.

Conditional on exactly `[hker]` (+ `1 ≤ d`); `hgen` is ambient sop
data. This closes C2 (R-D3) modulo the `hwit`-chain `hker`. -/
theorem koszulExt_subsingleton_below_of_hker {K : Type uC2} [Field K]
    {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] {d : ℕ}
    {Ix : Type uC2} [LinearOrder Ix]
    (b : Module.Basis Ix (Localization.AtPrime P)
      (Fin d → Localization.AtPrime P))
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥)
    (hd1 : 1 ≤ d) :
    ∀ (i : ℕ) (_ : i < d), Subsingleton (Abelian.Ext
      (ModuleCat.of (Localization.AtPrime P) (Shrink.{uC2}
        ((Localization.AtPrime P) ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime P))))
      (ModuleCat.of (Localization.AtPrime P)
        (Localization.AtPrime P)) i) := by
  obtain ⟨hHom, h0⟩ := c2_koszulHomBridge_of_r2Reduced P d g hgen hker hd1
  exact koszulExt_subsingleton_below_ofSequence b g
    (koszulResiduePiShrink P d g hgen)
    (koszulResiduePiShrink_quasiIso P d g hgen hker) hHom h0

#print axioms c2_koszulHomBridge_of_r2Reduced
#print axioms koszulResiduePiShrink_quasiIso
#print axioms koszulExt_subsingleton_below_of_hker

end SelfDuality
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
