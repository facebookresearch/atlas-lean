/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.PolynomialExactness
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.ExteriorSumDecomposition
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# Tower identification for the Koszul exactness route (A4(iii), toward file 6)

The file-5 tower module `towerMod κ d d` is a right-nested product of `d`
copies of `S = MvPolynomial (Fin d) κ`; file 6 (`GradedLift`) instead works
with `Fin d → S` and, across the gr-equivalence, with `Fin d → grRegular P`.
This file proves the two identifications that bridge the shapes, as a step
toward the `E k` data of `GrLiftIntertwining`:

* (§1) `towerModEquivTop`: `towerMod κ d d ≃ₗ[S] (Fin d → S)` by induction,
  via the snoc step `snocLinearEquiv` and `LinearEquiv.prodCongr`; plus
  `towerExtEquiv`, the exterior-power transport reusing
  `exteriorPower.mapEquiv`.
* (§2) `piFinSemilinear`: coordinate-wise `(Fin n → R) ≃ₛₗ[σ] (Fin n → S)`
  over a ring equivalence `σ : R ≃+* S` (explicit matrix-unit build: there is
  no semilinear `Basis.constr` variant in Mathlib), with
  `piFinSemilinear_single` recording that matrix units go to matrix units;
  plus the composite `towerPiSemilinear`.

Design: the tower grows on the right (`towerMod (n+1) = towerMod n × S`), so
the head-split `Fin.consLinearEquiv` does not fit; the step equivalence is
built directly from `Fin.snoc` / `Fin.init` instead.

## References

Project (all read-only):
* `Regularity/Koszul/PolynomialExactness.lean`: `towerMod` (:440),
  `towerModAddCommGroup` / `towerModModule` (:444-454).
* `Regularity/Koszul/ExteriorSumDecomposition.lean`: `exteriorPower.mapEquiv` (:53-55).
* `Regularity/Koszul/GradedLift.lean`: `GrLiftIntertwining` (:310), the consumer.

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Data/Fin/Tuple/Basic.lean`: `Fin.init` (:508), `Fin.snoc` (:516),
  `Fin.init_snoc` (:521), `Fin.snoc_castSucc` (:527), `Fin.snoc_last` (:540),
  `Fin.snoc_init_self` (:603).
* `LinearAlgebra/Pi.lean`: `Fin.consLinearEquiv` (:662, head-split, not used).
* `LinearAlgebra/Prod.lean`: `LinearEquiv.prodCongr` (:771).
* `LinearAlgebra/Basis/Defs.lean`: `Basis.constr` (:508); no semilinear
  variant exists anywhere under `Mathlib/LinearAlgebra` (verified by grep),
  hence the explicit matrix-unit build in §2.
* `Algebra/Ring/CompTypeclasses.lean`: `RingHomInvPair.of_ringEquiv` (:124)
  (local instances only), `RingHomCompTriple.ids` (:148).

## Status

* §1 (snoc step + tower identification + exterior transport): unconditional.
* §2 (semilinear coordinate transport + composite): unconditional.
* Residual (explicit, unproved): the full `GrLiftIntertwining` family
  `E k` (exterior powers across the ring change), which needs an exterior
  power of a semilinear map — absent from Mathlib.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace TowerIdentification

open ExteriorAlgebra
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.PolynomialExactness

variable (κ : Type*) [Field κ] (d : ℕ)

/-! ## §1. The snoc step and the tower identification -/

section Snoc

variable {R : Type*} [CommRing R]

/-- Append-at-end as a linear equivalence: a tail product is a longer
`Fin`-family. This is the induction step for `towerModEquiv`. -/
noncomputable def snocLinearEquiv (n : ℕ) :
    ((Fin n → R) × R) ≃ₗ[R] (Fin (n + 1) → R) where
  toFun p := Fin.snoc p.1 p.2
  map_add' p q := by
    funext i
    refine i.lastCases ?_ ?_
    · change Fin.snoc (α := fun _ => R) (p + q).1 (p + q).2 (Fin.last n) =
        (Fin.snoc (α := fun _ => R) p.1 p.2 +
          Fin.snoc (α := fun _ => R) q.1 q.2) (Fin.last n)
      simp only [Fin.snoc_last, Pi.add_apply, Prod.snd_add]
    · intro j
      change Fin.snoc (α := fun _ => R) (p + q).1 (p + q).2 j.castSucc =
        (Fin.snoc (α := fun _ => R) p.1 p.2 +
          Fin.snoc (α := fun _ => R) q.1 q.2) j.castSucc
      simp only [Fin.snoc_castSucc, Pi.add_apply, Prod.fst_add]
  map_smul' c p := by
    funext i
    refine i.lastCases ?_ ?_
    · change Fin.snoc (α := fun _ => R) (c • p).1 (c • p).2 (Fin.last n) =
        (c • Fin.snoc (α := fun _ => R) p.1 p.2) (Fin.last n)
      simp only [Fin.snoc_last, Pi.smul_apply]
      rfl
    · intro j
      change Fin.snoc (α := fun _ => R) (c • p).1 (c • p).2 j.castSucc =
        (c • Fin.snoc (α := fun _ => R) p.1 p.2) j.castSucc
      simp only [Fin.snoc_castSucc, Pi.smul_apply]
      rfl
  invFun f := (Fin.init f, f (Fin.last n))
  left_inv p := by
    obtain ⟨a, x⟩ := p
    change (Fin.init (α := fun _ => R)
      (Fin.snoc (α := fun _ => R) a x),
      Fin.snoc (α := fun _ => R) a x (Fin.last n)) = (a, x)
    simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv f := by
    change Fin.snoc (α := fun _ => R)
      (Fin.init (α := fun _ => R) f) (f (Fin.last n)) = f
    exact Fin.snoc_init_self f

/-- `snocLinearEquiv` acts by `Fin.snoc`. -/
@[simp]
theorem snocLinearEquiv_apply (n : ℕ) (p : (Fin n → R) × R) :
    snocLinearEquiv (R := R) n p = Fin.snoc p.1 p.2 :=
  rfl

/-- The inverse of `snocLinearEquiv` splits off the last coordinate. -/
@[simp]
theorem snocLinearEquiv_symm_apply (n : ℕ) (f : Fin (n + 1) → R) :
    (snocLinearEquiv (R := R) n).symm f = (Fin.init f, f (Fin.last n)) :=
  rfl

end Snoc

/-- The tower identification: the right-nested product tower is the `Fin`-family
module. HilbertFunctionCount via `LinearEquiv.prodCongr` and `snocLinearEquiv`. -/
noncomputable def towerModEquiv : ∀ n : ℕ,
    towerMod κ d n ≃ₗ[MvPolynomial (Fin d) κ]
      (Fin n → MvPolynomial (Fin d) κ)
  | 0 => LinearEquiv.refl _ _
  | n + 1 =>
      ((towerModEquiv n).prodCongr
        (LinearEquiv.refl _ _)).trans (snocLinearEquiv n)

/-- The top identification, in the shape file 6 consumes. -/
noncomputable def towerModEquivTop :
    towerMod κ d d ≃ₗ[MvPolynomial (Fin d) κ]
      (Fin d → MvPolynomial (Fin d) κ) :=
  towerModEquiv κ d d

/-- Exterior-power transport along the tower identification, reusing
`exteriorPower.mapEquiv` (the file-1 precedent). -/
noncomputable def towerExtEquiv (k : ℕ) :
    ↥(⋀[MvPolynomial (Fin d) κ]^k (towerMod κ d d)) ≃ₗ[MvPolynomial (Fin d) κ]
      ↥(⋀[MvPolynomial (Fin d) κ]^k (Fin d → MvPolynomial (Fin d) κ)) :=
  exteriorPower.mapEquiv (towerModEquivTop κ d) k

/-! ## §2. Semilinear basis transport (matrix-unit build) -/

section PiSemilinear

attribute [local instance] RingHomInvPair.of_ringEquiv
  RingHomInvPair.of_ringEquiv_symm

variable {R S : Type*} [CommRing R] [CommRing S] (σ : R ≃+* S)

/-- Coordinate-wise transport along a ring equivalence. This is the fallback
explicit matrix-unit build: Mathlib has no semilinear `Basis.constr`. -/
noncomputable def piFinSemilinear (n : ℕ) :
    (Fin n → R) ≃ₛₗ[(σ : R →+* S)] (Fin n → S) where
  toFun f i := σ (f i)
  map_add' f g := by
    funext i
    change σ ((f + g) i) = σ (f i) + σ (g i)
    rw [Pi.add_apply, map_add]
  map_smul' c f := by
    funext i
    change (σ : R →+* S) ((c • f) i) =
      (σ : R →+* S) c • (σ : R →+* S) (f i)
    rw [Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  invFun g i := σ.symm (g i)
  left_inv f := by
    funext i
    change σ.symm (σ (f i)) = f i
    simp
  right_inv g := by
    funext i
    change σ (σ.symm (g i)) = g i
    simp

/-- `piFinSemilinear` acts pointwise by `σ`. -/
@[simp]
theorem piFinSemilinear_apply (n : ℕ) (f : Fin n → R) (i : Fin n) :
    piFinSemilinear σ n f i = σ (f i) :=
  rfl

/-- The inverse of `piFinSemilinear` acts pointwise by `σ.symm`. -/
@[simp]
theorem piFinSemilinear_symm_apply (n : ℕ) (g : Fin n → S) (i : Fin n) :
    (piFinSemilinear σ n).symm g i = σ.symm (g i) :=
  rfl

/-- Matrix units go to matrix units: the basis-transport character of
`piFinSemilinear`. -/
theorem piFinSemilinear_single (n : ℕ) (i : Fin n) :
    piFinSemilinear σ n (Pi.single i 1) = Pi.single i 1 := by
  funext j
  by_cases h : j = i <;> simp [h]

end PiSemilinear

section TowerSemilinear

attribute [local instance] RingHomInvPair.of_ringEquiv
  RingHomInvPair.of_ringEquiv_symm

variable (S : Type*) [CommRing S]
  (σ : MvPolynomial (Fin d) κ ≃+* S)

/-- Tower-to-pi semilinear transport over a ring equivalence: the composite of
`towerModEquivTop` and `piFinSemilinear`. Step toward the `E k` data of
`GrLiftIntertwining` (instantiate `σ` with the M4c gr-equivalence). -/
noncomputable def towerPiSemilinear :
    towerMod κ d d ≃ₛₗ[(σ : MvPolynomial (Fin d) κ →+* S)] (Fin d → S) :=
  (towerModEquivTop κ d).trans (piFinSemilinear σ d)

end TowerSemilinear

#print axioms towerModEquivTop
#print axioms towerExtEquiv
#print axioms piFinSemilinear
#print axioms towerPiSemilinear

end TowerIdentification
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
