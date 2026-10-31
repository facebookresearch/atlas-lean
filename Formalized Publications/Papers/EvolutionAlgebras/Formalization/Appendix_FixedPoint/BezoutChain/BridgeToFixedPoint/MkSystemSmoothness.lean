/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Statement
import Appendix_FixedPoint.BezoutChain.Geometry.Counting
import Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# G-dependent smoothness for the `mkSystem` system (D1 reconciliation, T3)

Catenary-independent part: task T3 (Jacobian `[-I | 0]`
computation at `zRep` for the `mkSystem` system), feeding step 5. The
section data `ℓ` of `§2` step 3 is taken as a *parameter* here and its
locality input as an explicit hypothesis — that work (R1/T4–T6) is out of
scope; nothing below needs unmixedness, catenary, or avoidance.

## Replacement statement (audit issue #2)

*Assumed before (placeholder, G-independent):* `bezout_quadrics` took
`hsmooth : LinearIndependent K (fun k => fun dx => -dx k)` — an abstract
linear-algebra fact mentioning no `G` — discharged by `distinguished_smooth`
of the same function-level shape. Neither can feed
`exists_another_point_of_smooth_point`, whose `hsmooth` is the Jacobian rank
of the *actual* `G` (`Counting.lean` § `FixedPointFromBezout` non-import
says the shapes do not match, so no direct reuse is possible).

*Proved now (G-dependent, by Jacobian recomputation, never threading):* for
`G := mkSystem n K F` with `hFhom : ∀ i, (F i).IsHomogeneous 2`, the partials
at `zRep` are computed from the actual polynomials
(`hjac_mkSystem` — the `-z·xᵢ` piece evaluates to `-δ` directly, the renamed
`Fᵢ` piece vanishes by homogeneity), giving the exact `hjac` shape consumed by
`Counting.smooth_of_negId_linear_parts` (reused, not re-proved). From it:
`IsSmoothPoint` (`isSmoothPoint_mkSystem` — the corollary's `hsmooth`
shape), multiplicity `1` given `hloc` (`mult_one_mkSystem` — the corollary's
`hmult` shape, via `Counting.smooth_implies_mult_one`, reused), and locus
membership (`mem_vanishingLocus_mkSystem` — the corollary's `hmem` shape, via
homogeneity scaling). `distinguished_inputs_mkSystem` packages all three.

*Remains open:* `hloc : localMultiplicity … (distinguishedPoint _).rep … = 1`
(T6/LocalMultiplicity: regular-local ring ⇒ length `1`, via `hlocLocal`/`hlocBundle`);
the section `ℓ` + `hreg` + `hc` choice (T4/R1, `§2` step 3); the `hZd` case
split (T5). The only input assumption here is `hFhom` (quadratic input forms),
discharged upstream by the T1 construction.

## Catenary-independence

No direct or needed dependence on `Regularity/*` or `Dimension/*`: the only
`Counting` items used are the proved shells `smooth_of_negId_linear_parts`
(needs only `hmem` + `hjac`) and `smooth_implies_mult_one` (needs only `hs`
+ `hloc`). (`Counting` itself transitively imports `Regularity` for its
other lemmas; nothing used here takes such a hypothesis.)
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
variable (n : ℕ) (K : Type*) [Field K]

/-! ## `zRep` coordinate facts -/

/-- `zRep` vanishes on the `x` (`Fin.castSucc`) coordinates.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.zRep`.
* `Mathlib/Data/Fin/SuccPred.lean`, `Fin.castSucc_ne_last`. -/
theorem zRep_castSucc_eq_zero (i : Fin (n + 1)) :
    zRep n K (Fin.castSucc i) = 0 :=
  Pi.single_eq_of_ne (Fin.castSucc_ne_last i) _

/-- `zRep` is `1` in the last (`z`) coordinate.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.zRep`. -/
theorem zRep_last_eq_one : zRep n K (Fin.last (n + 1)) = 1 :=
  Pi.single_eq_same _ _

/-- The `x`-part of `zRep` is the zero vector (used to kill the renamed-`F`
contribution via `eval_rename`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.zRep`. -/
theorem zRep_comp_castSucc_eq_zero :
    (zRep n K) ∘ Fin.castSucc = (0 : Fin (n + 1) → K) := by
  funext x
  simp only [Function.comp_apply, zRep_castSucc_eq_zero, Pi.zero_apply]

/-! ## Positive-degree homogeneous forms vanish at the origin -/

/-- A positive-degree homogeneous polynomial vanishes at the origin (scaling
with `a = 0`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.eval_smul_of_isHomogeneous`. -/
theorem eval_zero_of_isHomogeneous_of_pos {σ : Type*} {φ : MvPolynomial σ K}
    {d : ℕ} (hφ : φ.IsHomogeneous d) (hd : 1 ≤ d) :
    MvPolynomial.eval (0 : σ → K) φ = 0 := by
  have h := eval_smul_of_isHomogeneous hφ (0 : K) (0 : σ → K)
  rw [smul_zero] at h
  have hd0 : d ≠ 0 := by omega
  rw [h, zero_pow hd0, zero_mul]

/-! ## Jacobian pieces at `zRep` -/

/-- The renamed-`Fᵢ` piece of the `mkSystem` Jacobian vanishes at `zRep`:
on `castSucc` columns by `pderiv_rename` + homogeneity (partials of a
quadratic are homogeneous of degree `1`, hence `0` at the origin); on the
`z` column because `rename Fin.castSucc` never mentions it.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`,
  `Appendix_FixedPoint.BezoutChain.zRep`.
* `Mathlib/Algebra/MvPolynomial/PDeriv.lean`, `MvPolynomial.pderiv_rename`,
  `MvPolynomial.pderiv_eq_zero_of_notMem_vars`.
* `Mathlib/Algebra/MvPolynomial/Rename.lean`, `MvPolynomial.eval_rename`.
* `Mathlib/Algebra/MvPolynomial/Variables.lean`,
  `MvPolynomial.mem_vars_rename`.
* `Mathlib/RingTheory/MvPolynomial/EulerIdentity.lean`,
  `MvPolynomial.IsHomogeneous.pderiv`. -/
theorem eval_pderiv_rename_eq_zero
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hFhom : ∀ i, (F i).IsHomogeneous 2)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    MvPolynomial.eval (zRep n K) (MvPolynomial.pderiv j
      (MvPolynomial.rename Fin.castSucc (F i))) = 0 := by
  by_cases hj : ∃ x, Fin.castSucc x = j
  · obtain ⟨x, rfl⟩ := hj
    rw [MvPolynomial.pderiv_rename (Fin.castSucc_injective _),
      MvPolynomial.eval_rename, zRep_comp_castSucc_eq_zero]
    exact eval_zero_of_isHomogeneous_of_pos K ((hFhom i).pderiv) (by omega)
  · have hnotmem : j ∉ (MvPolynomial.rename Fin.castSucc (F i)).vars := by
      intro hmem
      obtain ⟨x, _, hx⟩ := MvPolynomial.mem_vars_rename Fin.castSucc (F i) hmem
      exact hj ⟨x, hx⟩
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hnotmem]
    exact map_zero _

/-- The `-z·xᵢ` piece of the `mkSystem` Jacobian evaluates at `zRep` to the
Kronecker `δ` (Leibniz + `zRep = (0, …, 0, 1)`).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`,
  `Appendix_FixedPoint.BezoutChain.zRep`.
* `Mathlib/Algebra/MvPolynomial/PDeriv.lean`, `MvPolynomial.pderiv_mul`,
  `MvPolynomial.pderiv_X_self`, `MvPolynomial.pderiv_X_of_ne`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`. -/
theorem eval_pderiv_dualPart
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    MvPolynomial.eval (zRep n K) (MvPolynomial.pderiv j
      (MvPolynomial.X (Fin.last (n + 1)) * MvPolynomial.X (Fin.castSucc i)))
    = (if j = Fin.castSucc i then (1 : K) else 0) := by
  rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_X,
    zRep_last_eq_one, zRep_castSucc_eq_zero,
    mul_zero, zero_add, one_mul]
  by_cases h : j = Fin.castSucc i
  · subst h
    simp
  · rw [MvPolynomial.pderiv_X_of_ne (fun hcon => h hcon.symm), map_zero]
    simp [h]

/-! ## The `[-I | 0]` Jacobian and locus membership at `zRep` -/

/-- The `[-I | 0]` Jacobian shape at `zRep` for `mkSystem` polynomials —
the exact `hjac` input of `Counting.smooth_of_negId_linear_parts`. This is
the G-dependent recomputation replacing the placeholder's G-independent
`hsmooth` (audit issue #2).

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`,
  `Appendix_FixedPoint.BezoutChain.zRep`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.smooth_of_negId_linear_parts` (whose `hjac` this discharges).
* `Mathlib/RingTheory/Derivation/Basic.lean`, `Derivation.map_sub`. -/
theorem hjac_mkSystem
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hFhom : ∀ i, (F i).IsHomogeneous 2)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    MvPolynomial.eval (zRep n K)
        (MvPolynomial.pderiv j ((mkSystem n K F) i))
      = -(if j = Fin.castSucc i then (1 : K) else 0) := by
  have hdecomp : ((mkSystem n K F) i)
      = MvPolynomial.rename Fin.castSucc (F i)
        - MvPolynomial.X (Fin.last (n + 1)) * MvPolynomial.X (Fin.castSucc i) :=
    rfl
  rw [hdecomp, Derivation.map_sub, map_sub,
    eval_pderiv_rename_eq_zero _ _ _ hFhom, eval_pderiv_dualPart, zero_sub]

/-- The `mkSystem` equations vanish at `zRep` (both the renamed-`Fᵢ` piece,
by homogeneity, and the `-z·xᵢ` piece, since `x = 0` there) — the exact
`hmem` input of `Counting.smooth_of_negId_linear_parts`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`,
  `Appendix_FixedPoint.BezoutChain.zRep`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.smooth_of_negId_linear_parts` (whose `hmem` this discharges).
* `Mathlib/Algebra/MvPolynomial/Rename.lean`, `MvPolynomial.eval_rename`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_X`. -/
theorem hmem_eval_mkSystem
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hFhom : ∀ i, (F i).IsHomogeneous 2)
    (i : Fin (n + 1)) :
    MvPolynomial.eval (zRep n K) ((mkSystem n K F) i) = 0 := by
  have hdecomp : ((mkSystem n K F) i)
      = MvPolynomial.rename Fin.castSucc (F i)
        - MvPolynomial.X (Fin.last (n + 1)) * MvPolynomial.X (Fin.castSucc i) :=
    rfl
  have h1 : MvPolynomial.eval (zRep n K)
      (MvPolynomial.rename Fin.castSucc (F i)) = 0 := by
    rw [MvPolynomial.eval_rename, zRep_comp_castSucc_eq_zero]
    exact eval_zero_of_isHomogeneous_of_pos K (hFhom i) (by omega)
  have h2 : MvPolynomial.eval (zRep n K)
      (MvPolynomial.X (Fin.last (n + 1)) * MvPolynomial.X (Fin.castSucc i))
      = 0 := by
    rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X,
      zRep_last_eq_one, zRep_castSucc_eq_zero, mul_zero]
  rw [hdecomp, map_sub, h1, h2, sub_zero]

/-- Locus-level membership of the distinguished point for `mkSystem` —
the corollary's `hmem` shape (`exists_another_point_of_smooth_point`'s
`hmem` hypothesis, cited by name). Lifts the `zRep` evaluation via
homogeneity scaling along the projective fibre.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.vanishingLocus`,
  `Appendix_FixedPoint.BezoutChain.distinguishedPoint`, `Appendix_FixedPoint.BezoutChain.zRep`,
  `Appendix_FixedPoint.BezoutChain.zRep_ne_zero`,
  `Appendix_FixedPoint.BezoutChain.mkSystem`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.exists_another_point_of_smooth_point` (whose `hmem` this is),
  `Appendix_FixedPoint.BezoutChain.mkSystem_homogeneous` (reused, proved).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.ProjectiveLocus`,
  `Appendix_FixedPoint.BezoutChain.eval_smul_of_isHomogeneous`.
* `Mathlib/LinearAlgebra/Projectivization/Basic.lean`,
  `Projectivization.mk_eq_mk_iff'`. -/
theorem mem_vanishingLocus_mkSystem
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hFhom : ∀ i, (F i).IsHomogeneous 2) :
    distinguishedPoint n K ∈ vanishingLocus n K (mkSystem n K F) := by
  have hGhom : ∀ i, ((mkSystem n K F) i).IsHomogeneous 2 :=
    mkSystem_homogeneous n K F hFhom
  have h0 := hmem_eval_mkSystem n K F hFhom
  intro v hv hmk i
  have hrep : Projectivization.mk K (zRep n K) (zRep_ne_zero n K)
      = distinguishedPoint n K := rfl
  rw [← hrep] at hmk
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' K v (zRep n K) hv (zRep_ne_zero n K)).mp hmk
  have hscale := eval_smul_of_isHomogeneous (hGhom i) a (zRep n K)
  rw [ha] at hscale
  rw [hscale, h0 i, mul_zero]

/-! ## Corollary inputs: `hsmooth`, `hmult`, and packaging -/

/-- `IsSmoothPoint` for `mkSystem` at the distinguished point — the
corollary's `hsmooth` shape (`exists_another_point_of_smooth_point`'s
`hsmooth` hypothesis, cited by name). Reuses (not re-proves)
`Counting.smooth_of_negId_linear_parts` on the recomputed Jacobian.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.IsSmoothPoint`,
  `Appendix_FixedPoint.BezoutChain.distinguishedPoint`, `Appendix_FixedPoint.BezoutChain.mkSystem`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.exists_another_point_of_smooth_point` (whose `hsmooth` this is).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.smooth_of_negId_linear_parts` (reused). -/
theorem isSmoothPoint_mkSystem
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hFhom : ∀ i, (F i).IsHomogeneous 2) :
    IsSmoothPoint n K (mkSystem n K F) (distinguishedPoint n K) :=
  smooth_of_negId_linear_parts n K (mkSystem n K F)
    (hmem_eval_mkSystem n K F hFhom) (hjac_mkSystem n K F hFhom)

/-- Multiplicity `1` at the distinguished point for `mkSystem` — the
corollary's `hmult` shape (`exists_another_point_of_smooth_point`'s
`hmult` hypothesis, cited by name), now in local form. Reuses (not
re-proves) `Counting.smooth_implies_mult_one`; the local `hloc` is T6's
input and `hc` the R1-nonvanishing, both taken as hypotheses
(section data lives downstream). Locus
membership is supplied in-file by `mem_vanishingLocus_mkSystem`.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Definitions`,
  `Appendix_FixedPoint.BezoutChain.localPointMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.localMultiplicity`,
  `Appendix_FixedPoint.BezoutChain.distinguishedPoint`, `Appendix_FixedPoint.BezoutChain.mkSystem`.
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.exists_another_point_of_smooth_point` (whose `hmult` this is).
* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Geometry.Counting`,
  `Appendix_FixedPoint.BezoutChain.smooth_implies_mult_one` (reused). -/
theorem mult_one_mkSystem
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (ℓ : Fin (n + 2) → K)
    (hFhom : ∀ i, (F i).IsHomogeneous 2)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K (mkSystem n K F))
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hloc : localMultiplicity n K (mkSystem n K F) ℓ
      (distinguishedPoint n K).rep
      (fun i => mem_vanishingLocus_mkSystem n K F hFhom
        (distinguishedPoint n K).rep (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K)) i)
      (hc (distinguishedPoint n K) (mem_vanishingLocus_mkSystem n K F hFhom)
        (distinguishedPoint n K).rep (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K))) = 1) :
    localPointMultiplicity n K (mkSystem n K F) ℓ hc
      (distinguishedPoint n K) = 1 :=
  smooth_implies_mult_one n K (mkSystem n K F) ℓ hc (distinguishedPoint n K)
    (mem_vanishingLocus_mkSystem n K F hFhom)
    (isSmoothPoint_mkSystem n K F hFhom) hloc

/-- Packaged corollary inputs for `mkSystem`: `hmem` ∧ `hsmooth` ∧ `hmult`
in the exact shapes `exists_another_point_of_smooth_point` consumes.

## References

* `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Statement.Statement`,
  `Appendix_FixedPoint.BezoutChain.exists_another_point_of_smooth_point` (the consumer). -/
theorem distinguished_inputs_mkSystem
    (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (ℓ : Fin (n + 2) → K)
    (hFhom : ∀ i, (F i).IsHomogeneous 2)
    (hc : ∀ (p : Projectivization K (Fin (n + 2) → K))
      (_ : p ∈ vanishingLocus n K (mkSystem n K F))
      (v : Fin (n + 2) → K) (hv : v ≠ 0),
      Projectivization.mk K v hv = p → MvPolynomial.eval v (mkLin n K ℓ) ≠ 0)
    (hloc : localMultiplicity n K (mkSystem n K F) ℓ
      (distinguishedPoint n K).rep
      (fun i => mem_vanishingLocus_mkSystem n K F hFhom
        (distinguishedPoint n K).rep (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K)) i)
      (hc (distinguishedPoint n K) (mem_vanishingLocus_mkSystem n K F hFhom)
        (distinguishedPoint n K).rep (distinguishedPoint n K).rep_nonzero
        (Projectivization.mk_rep (distinguishedPoint n K))) = 1) :
    distinguishedPoint n K ∈ vanishingLocus n K (mkSystem n K F)
      ∧ IsSmoothPoint n K (mkSystem n K F) (distinguishedPoint n K)
      ∧ localPointMultiplicity n K (mkSystem n K F) ℓ hc
        (distinguishedPoint n K) = 1 :=
  ⟨mem_vanishingLocus_mkSystem n K F hFhom,
    isSmoothPoint_mkSystem n K F hFhom,
    mult_one_mkSystem n K F ℓ hFhom hc hloc⟩

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
