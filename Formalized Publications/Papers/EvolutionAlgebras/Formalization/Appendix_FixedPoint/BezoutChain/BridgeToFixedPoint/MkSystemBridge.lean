/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.ProjectiveToConeExtraction
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Appendix_FixedPoint.BezoutChain.Statement.Statement
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Bridge: placeholder functions → `mkSystem` polynomials (D1 T1+T2, catenary-independent)

Reconciliation of the `bezout_quadrics` placeholder
(`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.bezout_quadrics`) with the
`Statement` polynomial theorems, covering the catenary-independent part
(T1+T2).

* T1: index shift `n_Statement = n_placeholder − 1` (needs `hn : 0 < n`;
  the extra factor `2` is purely this shift) and
  the embedding of structure-constant functions (`sqCoords`/`homogQuadric`
  pattern) into `MvPolynomial`s via `mkSystem`.
* T2: scaling behaviour ⟹ each component homogeneous of degree `2`, in the
  exact shape `mkSystem_homogeneous` consumes
  (`hF : ∀ i, (F i).IsHomogeneous 2`).

Needs nothing from unmixedness / catenary / avoidance: no
`Regularity/*` or `Dimension/*` imports.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.bezout_quadrics`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.sqCoords`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.homogQuadric`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.zRep`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.zRep_ne_zero`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.distinguishedPoint`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.vanishingLocus`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.coneQuotient`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.sectionQuotient`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.chartRing`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.bezout_quadratic`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.exists_another_point_of_smooth_point`
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MkSystemBridge

open scoped BigOperators

/-! ## T1a: the index shift. -/

/-- Statement-level index: `n_Statement = n_placeholder − 1`.
Under this shift equation counts agree (`n_S + 1 = n_P`) and variable
counts agree (`n_S + 2 = n_P + 1`); the Bézout count `2 ^ (m + 1)`
equals the placeholder `2 ^ n_P`. Instantiating `Statement` at `n`
instead of `n − 1` overcounts by exactly one factor of `2`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.bezout_quadrics`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.bezout_quadratic`
-/
def statementIndex (n : ℕ) : ℕ := n - 1

/-- The shift cancels: `statementIndex n + 1 = n` for `0 < n`.
-/
theorem shift_add_one (n : ℕ) (hn : 0 < n) : statementIndex n + 1 = n :=
  Nat.sub_add_cancel hn

/-- Equation-index equivalence `Fin (m + 1) ≃ Fin n` transported along
the shift cancellation. The downstream D1 bridge calls `Statement` at
`m = n − 1` and transports `Fin n ≃ Fin ((n − 1) + 1)` explicitly.
-/
def shiftEquiv (n : ℕ) (hn : 0 < n) : Fin (statementIndex n + 1) ≃ Fin n :=
  finCongr (shift_add_one n hn)

/-! ## T1b: functions → polynomials (the `sqCoords` pattern as `MvPolynomial`s). -/

/-- Quadratic form polynomials from structure constants: the polynomial
analogue of `sqCoords`, with `eval X (Fᵢ) = sqCoords …`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.sqCoords`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem`
-/
noncomputable def mkQuadForm (N : ℕ) (K : Type*) [Field K]
    (c : Fin N → Fin N → Fin N → K) (k : Fin N) : MvPolynomial (Fin N) K :=
  ∑ i, ∑ j, MvPolynomial.C (c i j k) * (MvPolynomial.X i * MvPolynomial.X j)

/-- Evaluation recovers the coordinate functions: `eval X (mkQuadForm …) =
sqCoords …` (feeds the step-2 eval-bridge).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.sqCoords`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem`
-/
theorem eval_mkQuadForm (N : ℕ) (K : Type*) [Field K]
    (c : Fin N → Fin N → Fin N → K) (k : Fin N) (X : Fin N → K) :
    MvPolynomial.eval X (mkQuadForm N K c k)
      = sqCoords K c k X := by
  unfold mkQuadForm sqCoords
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc]

/-- Reindex structure constants along the shift equivalence, so
placeholder data `c : Fin n → Fin n → Fin n → K` becomes
Statement-level data at `m + 1 = n − 1 + 1`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.sqCoords`
-/
noncomputable def shiftConsts (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    Fin (statementIndex n + 1) → Fin (statementIndex n + 1)
      → Fin (statementIndex n + 1) → K :=
  fun i j k => c (shiftEquiv n hn i) (shiftEquiv n hn j) (shiftEquiv n hn k)

/-- Statement-level quadratic forms built from (shifted) placeholder
structure constants.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.sqCoords`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem`
-/
noncomputable def bridgeForms (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    Fin (statementIndex n + 1) → MvPolynomial (Fin (statementIndex n + 1)) K :=
  fun k => mkQuadForm (statementIndex n + 1) K (shiftConsts n K c hn) k

/-- The instantiated `mkSystem` for the placeholder data: `G:= mkSystem
(n − 1) K F` (`Statement/Definitions.lean` line 437 shape). This is the exact object the
downstream D1 steps consume: T4 builds the section `ℓ` + `hreg` over
`coneQuotient (n−1) K G`, and T6 builds chart/local data over
`chartRing (n−1) K G ℓ`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.coneQuotient`
-/
noncomputable def bridgeSystem (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    Fin (statementIndex n + 1)
      → MvPolynomial (Fin (statementIndex n + 2)) K :=
  mkSystem (statementIndex n) K (bridgeForms n K c hn)

/-! ## T2: homogeneity (scaling behaviour ⟹ `IsHomogeneous 2`). -/

/-- Each quadratic-form polynomial is homogeneous of degree `2`
(char-2 safe: monomial argument only, no division).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous`
-/
theorem mkQuadForm_isHomogeneous (N : ℕ) (K : Type*) [Field K]
    (c : Fin N → Fin N → Fin N → K) (k : Fin N) :
    (mkQuadForm N K c k).IsHomogeneous 2 := by
  unfold mkQuadForm
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  simpa using (MvPolynomial.isHomogeneous_C _ _).mul
    ((MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))

/-- Homogeneity of the bridge forms without the scaling wrapper
(direct feed for `mkSystem_homogeneous`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous`
-/
theorem bridgeForms_homogeneous (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    ∀ i, ((bridgeForms n K c hn) i).IsHomogeneous 2 := by
  intro i
  change (mkQuadForm (statementIndex n + 1) K (shiftConsts n K c hn) i).IsHomogeneous 2
  exact mkQuadForm_isHomogeneous _ K _ _

/-! ## Consumer shapes for T4/T6 (exact `Statement` hypothesis shapes at `m = n − 1`). -/

/-- The instantiated system is homogeneous of degree `2` in every
component: the exact `hG` shape both `Statement` theorems consume
(`bezout_quadratic`, `Statement/Statement.lean` line 106;
`exists_another_point_of_smooth_point`, line 176). T4 consumes
`(bridgeSystem n K c hn, bridgeSystem_homogeneous n K c hn)` to supply
`G`/`hG` when producing `ℓ` + `hreg` via
`exists_regular_chartForm` / `regular_chartForm_of_zeroDim`; T6 consumes
the same pair (plus T4's `ℓ`) for `chartRing`/`sectionQuotient` inputs
(`hloc`, `hlocal`, `hadd`, `hpos`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.bezout_quadratic`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.exists_another_point_of_smooth_point`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.coneQuotient`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.sectionQuotient`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.chartRing`
-/
theorem bridgeSystem_homogeneous (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    ∀ i, ((bridgeSystem n K c hn) i).IsHomogeneous 2 :=
  mkSystem_homogeneous (statementIndex n) K _ (bridgeForms_homogeneous n K c hn)

/-- Statement-level `mkSystem` evaluation splits as `Fᵢ(x) − z·xᵢ`:
for `v : Fin (m + 2) → K`, writing `x j = v (castSucc j)` and
`z = v last`, `eval v (Gᵢ) = eval x (Fᵢ) − z * x i`.
This is step 1 of the `eval (X, z) (Gᵢ) = homogQuadric …`
bridge; step 2 is `eval_mkQuadForm`, which identifies
`eval x (Fᵢ)` with `sqCoords` for the `bridgeForms` family. The two steps are
combined manually at each use site (no combined `bridgeSystem = homogQuadric`
corollary is stated here).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.mkSystem`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.homogQuadric`
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.FixedPointFromBezout.sqCoords`
-/
theorem bridgeSystem_eval (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (i : Fin (m + 1)) (v : Fin (m + 2) → K) :
    MvPolynomial.eval v (mkSystem m K F i)
      = MvPolynomial.eval (fun j => v (Fin.castSucc j)) (F i)
        - v (Fin.last (m + 1)) * v (Fin.castSucc i) := by
  unfold mkSystem
  rw [map_sub, MvPolynomial.eval_rename, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_X]
  rfl

/-- The `z`-part of `zRep` is `1`: `zRep m K last = 1`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.zRep`
-/
theorem zRep_last (m : ℕ) (K : Type*) [Field K] :
    zRep m K (Fin.last (m + 1)) = 1 := by
  unfold zRep
  rw [Pi.single_eq_same]

end MkSystemBridge
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
