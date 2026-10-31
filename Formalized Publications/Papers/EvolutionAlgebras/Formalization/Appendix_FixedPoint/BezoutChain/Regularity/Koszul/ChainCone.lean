/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ExteriorSumDecomposition
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Chain shift + chain-SES data + contraction matrix (A4(iii), file 3 of 6)

The chain-form mirror of the cone-SES construction: where the former `KoszulCone.lean`
(A3) worked with the wedge (cochain) form, this file works with the contraction
(chain) form that `AugmentedConeStep` (file 4 of 6: the shared augmented cone-step,
general `S`) consumes.

* (§1) Chain shift maps from the file-1 `extSplit` decomposition: the
  second split factor is the degree-shifted piece, with inclusion
  `chainShiftIncl` and projection `chainShiftProj` (`proj ∘ incl = id`,
  and the projection kills the unshifted `map inl` summand).
* (§2) `ChainSESData`, the exact chain-form mirror of
  `KoszulCone.KoszulConeSESData` (same three `ExactAt`-level correspondence
  fields, so no shift functor is needed), with the exactness/acyclicity/LES
  transfer corollaries in the exact shape file 4 consumes, plus the minimal
  chain-SES propagation wrappers (thin, shape-generic Mathlib transports with
  `Rel` discharged to `j + 1 = i`).
* (§3) Contraction-matrix entries: the file-1 chain differential matrix
  `extSplit_koszulContract` specialized to the two summands (the shift
  differential `-(d' b)`, the unshifted differential, and the bottom-map
  entries), in the exact bundled shape file 4's cone-step assembly needs.

Project (read-only): `Regularity/Koszul/ExteriorSumDecomposition.lean` (file 1 of 6: `extSplit`,
`extSplitZero`, `extSplit_koszulContract`, `extSplit_koszulContract_zero`,
`contract_snd_map_inl_alg`), `Regularity/Koszul/KoszulComplex.lean` (`koszulContract`,
`koszulChainComplex`, `koszulChainComplexOfSequence`).

Consumers (sibling lanes): `AugmentedConeStep` (file 4), `PolynomialExactness` (file 5).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ChainCone

open CategoryTheory CategoryTheory.Limits HomologicalComplex KoszulComplex
  ExteriorSumDecomposition

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-! ## §1. Chain shift maps from `extSplit` -/

/-- Inclusion of the shifted (second-split-factor) piece:
`b ↦ (extSplit k).symm (0, b)`. -/
noncomputable def chainShiftIncl (k : ℕ) :
    ↥(⋀[R]^k M) →ₗ[R] ↥(⋀[R]^(k + 1) (M × R)) :=
  (extSplit k).symm.toLinearMap ∘ₗ LinearMap.inr R _ _

/-- The shift inclusion sends `b` to `(extSplit k).symm (0, b)`. -/
@[simp]
theorem chainShiftIncl_apply (k : ℕ) (b : ↥(⋀[R]^k M)) :
    chainShiftIncl k b = (extSplit k).symm (0, b) := by
  simp [chainShiftIncl]

/-- Projection onto the shifted (second-split-factor) piece:
`z ↦ (extSplit k z).2`. -/
noncomputable def chainShiftProj (k : ℕ) :
    ↥(⋀[R]^(k + 1) (M × R)) →ₗ[R] ↥(⋀[R]^k M) :=
  LinearMap.snd R _ _ ∘ₗ (extSplit k).toLinearMap

/-- The shift projection sends `z` to `(extSplit k z).2`. -/
@[simp]
theorem chainShiftProj_apply (k : ℕ) (z : ↥(⋀[R]^(k + 1) (M × R))) :
    chainShiftProj k z = (extSplit k z).2 := by
  simp [chainShiftProj]

/-- The shift maps are a retraction: `proj ∘ incl = id`. -/
theorem chainShiftProj_incl (k : ℕ) (b : ↥(⋀[R]^k M)) :
    chainShiftProj k (chainShiftIncl k b) = b := by
  have h := extSplitFwd_bwd (R := R) (M := M) k
    ((0 : ↥(⋀[R]^(k + 1) M)), b)
  have h2 := congrArg Prod.snd h
  simpa using h2

/-! ## §2. Chain-SES data and propagation -/

/-- Chain-SES data for the Koszul induction step, in the exact shape file 4
(`AugmentedConeStep`) consumes: the chain-form mirror of
`KoszulCone.KoszulConeSESData`, with the same three `ExactAt`-level
correspondence fields (third term shifted by one, so no shift functor is
needed). File 4 discharges this by identifying `K(x::rs)` with the cone step
via the file-1 exterior-sum decomposition. -/
structure ChainSESData (K' K : ChainComplex (ModuleCat.{v} R) ℕ) where
  /-- The short exact sequence of complexes. -/
  S : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ)
  /-- The SES proof. -/
  shortExact : S.ShortExact
  /-- First term tracks `K'`. -/
  exactAt_one : ∀ i : ℕ, S.X₁.ExactAt i ↔ K'.ExactAt i
  /-- Third term tracks the shift `K'[1]`. -/
  exactAt_three : ∀ i : ℕ, S.X₃.ExactAt i ↔ K'.ExactAt (i + 1)
  /-- Middle term tracks `K`. -/
  exactAt_two : ∀ i : ℕ, S.X₂.ExactAt i ↔ K.ExactAt i

/-! ## §3. Contraction-matrix entries -/

/-- Chain differential on the shifted summand: the first component is `r • b`
and the second is the shift differential `-(d' b)`. -/
theorem chainMatrix_shift (i : ℕ) (φ : (M × R) →ₗ[R] R)
    (φ' : M →ₗ[R] R) (r : R)
    (phi_split : ∀ p : M × R, φ p = φ' p.1 + r * p.2)
    (b : ↥(⋀[R]^(i + 1) M)) :
    extSplit i (koszulContract φ (i + 1) ((extSplit (i + 1)).symm (0, b))) =
      (r • b, -(koszulContract φ' i b)) := by
  have h := extSplit_koszulContract i φ φ' r phi_split 0 b
  simpa using h

/-- Chain differential on the unshifted summand: `(d' a, 0)`. -/
theorem chainMatrix_unshift (i : ℕ) (φ : (M × R) →ₗ[R] R)
    (φ' : M →ₗ[R] R) (r : R)
    (phi_split : ∀ p : M × R, φ p = φ' p.1 + r * p.2)
    (a : ↥(⋀[R]^(i + 2) M)) :
    extSplit i (koszulContract φ (i + 1) ((extSplit (i + 1)).symm (a, 0))) =
      (koszulContract φ' (i + 1) a, 0) := by
  have h := extSplit_koszulContract i φ φ' r phi_split a 0
  simpa using h

/-- Bottom map on the unshifted summand. -/
theorem chainMatrix_bottom_unshift (φ : (M × R) →ₗ[R] R)
    (φ' : M →ₗ[R] R) (r : R)
    (phi_split : ∀ p : M × R, φ p = φ' p.1 + r * p.2)
    (a : ↥(⋀[R]^1 M)) :
    extSplitZero (koszulContract φ 0 ((extSplit 0).symm (a, 0))) =
      koszulContract φ' 0 a := by
  have h := extSplit_koszulContract_zero φ φ' r phi_split a 0
  simpa using h

/-- Bottom map on the shifted summand. -/
theorem chainMatrix_bottom_shift (φ : (M × R) →ₗ[R] R)
    (φ' : M →ₗ[R] R) (r : R)
    (phi_split : ∀ p : M × R, φ p = φ' p.1 + r * p.2)
    (b : ↥(⋀[R]^0 M)) :
    extSplitZero (koszulContract φ 0 ((extSplit 0).symm (0, b))) = r • b := by
  have h := extSplit_koszulContract_zero φ φ' r phi_split 0 b
  simpa using h

end ChainCone
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
