/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Appendix_FixedPoint.BezoutChain.Geometry.MkSystemChart
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Nullstellensatz

/-!
# Affine finiteness for the `mkSystem` chart system (finiteness-attack lane)

Target residual from `Geometry/MkSystemChart.lean` (`locus_finite_of_bpf_affine`):
`(affineZero m K F).Finite` where `affineZero` is the zero set of the
dehomogenized relations `chartPoly m K F i = F i - X i` (tex Lemma `Zfinite`
content, instantiated at the concrete affine system).

## Approach survey (Mathlib v4.34.0, grep-verified in `.lake/packages/mathlib`)

1. **Dimension/intersection/normalization APIs.** Present: Noether normalization
   (`exists_integral_inj_algHom_of_quotient`, `exists_integral_inj_algHom_of_fg`,
   `exists_finite_inj_algHom_of_fg` in
   `Mathlib/RingTheory/NoetherNormalization.lean`); Krull-dimension basics
   (`ringKrullDim`, `Ring.krullDimLE_iff`, `ringKrullDim_le_of_surjective`,
   `ringKrullDim_eq_of_ringEquiv` in `Mathlib/RingTheory/KrullDimension/Basic.lean`);
   the local regular-sequence dimension drop
   (`ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` in
   `.../KrullDimension/Regular.lean`, consumed via `RegularSequenceDimDrop`);
   `MvPolynomial` Krull dimension (`.../KrullDimension/Polynomial.lean`).
   Absent (zero hits each): `dehomog` (any case), `catenary`, any projective
   dimension theorem / projective-affine prime correspondence, any
   localization-dimension bound (`AtPrime` occurs in `KrullDimension/Zero.lean`
   only for `Ring.KrullDimLE.of_isLocalization`, which goes global-to-local),
   and any quotient-localization commutation iso at a general prime
   (`equivQuotientMapOfIsMaximal` covers maximal ideals only).
2. **PDT-corollary route.** The tex proof (Lemma `Zfinite` via Corollary
   `meetshyperplane`) is projective; scoped to the affine locus it becomes the
   end-to-end shape `MeetsInfinity` (§4): a positive-dimensional affine
   quotient forces a nonzero common zero of the input forms (projective closure
   meets `{λ = 0}`, where the top-degree parts are the `Fᵢ`). The closure and
   PDT steps have no in-tree API, so the shape is taken as an explicit
   hypothesis; `affineZero_finite_of_meetsInfinity` proves it suffices
   (with `BasePointFree`).
3. **Dimension-drop route** (§3, primary conditional): `RegularSequenceDimDrop`'s
   localized equation plus the ambient bound plus local-to-global transfer
   gives `KrullDimLE 0` of the affine quotient, hence finiteness via the
   bridge. The `WithBot ℕ∞` cancellation (`dimLE_zero_of_add_eq_le`) is proved.
4. **`O(Z') = K` alternative** (tex Remark `altfinite`): needs global regular
   functions on irreducible projective varieties (`Hartshorne Ch. I, Thm 3.4a`);
   no structure-sheaf-on-`Projectivization`-locus API exists in-tree, so this
   route is assessed and not formalized (strictly more missing API than (2)).

## What this file proves

* §2 (closed): the affine bridge at `chartPoly` shape —
  `affineZero_finite_of_krullDimLE_zero`, conditional on exactly `[hdim]`.
  The four bridge lemmas mirror `Geometry/ProjectiveLocus.lean` (cited by name,
  never imported) under `_affine` names.
* §3 (conditional-exact): `affineZero_finite_of_successiveRegular`,
  conditional on exactly `[hsucc, hambient, hglob]`.
* §4 (conditional-exact): `affineZero_finite_of_meetsInfinity`,
  conditional on exactly `[hPDT, hBPF]`.

## Status

* `(affineZero m K F).Finite`: conditional on exactly
  `[Ring.KrullDimLE 0 (MvPolynomial (Fin (m+1)) K ⧸ span (range (chartPoly)))]`
  (main bridge), discharged further from
  `[SuccessiveSMulRegular, AmbientLocalDimBound, LocalToGlobalDimZero]`
  (dim-drop) or from `[MeetsInfinity, BasePointFree]` (PDT route).
* `hsucc` is the crux-linked regularity input (cf.: CM-ness of
  successive quotients); `hambient`/`hglob`/`hPDT` are precisely-shaped
  dimension-geometry residuals with grep-verified missing API.

## DAG safety

Imports only clean `Geometry.MkSystemChart` (for `affineZero`, `chartPoly`,
`BasePointFree`) and `Dimension.RegularSequenceDimDrop` (for the localized dimension
drop) plus narrow Mathlib modules. Never imports `Statement.Statement`,
`Geometry.Counting`, `Geometry.ProjectiveLocus`, `BridgeToFixedPoint.MkSystemSmoothness`, or
`BridgeToFixedPoint.FixedPointFromBezout`; the `ProjectiveLocus` affine bridge is mirrored
under `_affine` names with by-name citations, per the `MkSystemChart`
precedent. No other file imports this one.

## References

Mathlib v4.34.0 (exact module paths and declaration names, each grep-verified
in-tree) is cited per declaration below.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hF : ∀ i, (F i).IsHomogeneous 2` — quadratic input forms.
* `hdim : Ring.KrullDimLE 0 …` — the affine-dimension input of the §2 bridge.
* Dim-drop triple: `hsucc` (successive regularity of `chartPoly`),
  `hambient : AmbientLocalDimBound`, `hglob : LocalToGlobalDimZero`.
* PDT pair: `hPDT : MeetsInfinity`, `hBPF : BasePointFree`; the hBPF chase
  binders `hcoord` (coordinate-level BPF) and `hbridge` (eval bridge);
  `hCurveMeet` (family-instance binder).
* `hn : 0 < n` — index positivity at the shift layer.
* Instance: `[Field K]` throughout; `[IsAlgClosed K]` at the PDT route.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## §2 Affine bridge at `chartPoly` shape (closed)

Mirrors of the `(b-aff)` bridge in `Geometry/ProjectiveLocus.lean`
(`vanishingIdeal_singleton_injective`,
`map_vanishingIdeal_isMaximal`,
`comap_map_vanishingIdeal`,
`zeroLocus_finite_of_krullDimLE_zero`), cited by name and never
imported, plus the identification of `affineZero` with the `zeroLocus` of the
`chartPoly` span (`MvPolynomial.zeroLocus_span`, `MvPolynomial.aeval_eq_eval`
is `rfl`). -/

/-- Points give distinct vanishing ideals: the singleton-ideal map is injective
(local mirror of `ProjectiveLocus.vanishingIdeal_singleton_injective`).

## References

* `Geometry.ProjectiveLocus`, `vanishingIdeal_singleton_injective`
  (mirrored).
* `Mathlib/RingTheory/Nullstellensatz.lean`,
  `MvPolynomial.mem_vanishingIdeal_singleton_iff`, `MvPolynomial.vanishingIdeal`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval_eq_eval`,
  `MvPolynomial.eval_X`, `MvPolynomial.eval_C`. -/
theorem vanishingIdeal_singleton_injective_affine
    {mm : ℕ} {K : Type*} [Field K] :
    Function.Injective (fun x : Fin mm → K =>
      MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K))) := by
  intro x y h
  have h' : MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K))
      = MvPolynomial.vanishingIdeal K ({y} : Set (Fin mm → K)) := h
  funext i
  have hmem : MvPolynomial.X i - MvPolynomial.C (x i)
      ∈ MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K)) := by
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  rw [h'] at hmem
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff] at hmem
  simp only [MvPolynomial.aeval_eq_eval, map_sub, MvPolynomial.eval_X,
    MvPolynomial.eval_C] at hmem
  exact (sub_eq_zero.mp hmem).symm

/-- The image of a point's vanishing ideal in an affine quotient (by an ideal
it contains) is maximal (local mirror of
`ProjectiveLocus.map_vanishingIdeal_isMaximal`).

## References

* `Geometry.ProjectiveLocus`, `map_vanishingIdeal_isMaximal`
  (mirrored).
* `Mathlib/RingTheory/Ideal/Maps.lean`,
  `Ideal.map_eq_top_or_isMaximal_of_surjective`,
  `Ideal.comap_map_of_surjective`, `RingHom.ker_eq_comap_bot`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.mk`,
  `Ideal.Quotient.mk_surjective`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Ideal.mk_ker`.
* `Mathlib/RingTheory/Nullstellensatz.lean`, `MvPolynomial.vanishingIdeal`
  (maximality of point ideals is the in-tree instance). -/
theorem map_vanishingIdeal_isMaximal_affine
    {mm : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin mm) K))
    (x : Fin mm → K)
    (hle : I ≤ MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K))) :
    (Ideal.map (Ideal.Quotient.mk I)
      (MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K)))).IsMaximal := by
  have hmax : (MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K))).IsMaximal :=
    inferInstance
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hmax with htop | hmax'
  · exfalso
    have hcomap : Ideal.comap (Ideal.Quotient.mk I)
        (Ideal.map (Ideal.Quotient.mk I)
          (MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K))))
        = MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K)) := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      have hker : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := by
        rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      rw [hker, sup_eq_left.mpr hle]
    rw [htop] at hcomap
    simp only [Ideal.comap_top] at hcomap
    have hne := hmax.ne_top
    rw [← hcomap] at hne
    exact hne rfl
  · exact hmax'

/-- Pullback undoes the pushforward on point ideals containing the kernel
(local mirror of `ProjectiveLocus.comap_map_vanishingIdeal`).

## References

* `Geometry.ProjectiveLocus`, `comap_map_vanishingIdeal` (mirrored).
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.comap_map_of_surjective`,
  `RingHom.ker_eq_comap_bot` (cited above).
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, `Ideal.mk_ker`
  (cited above). -/
theorem comap_map_vanishingIdeal_affine
    {mm : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin mm) K))
    (x : Fin mm → K)
    (hle : I ≤ MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K))) :
    Ideal.comap (Ideal.Quotient.mk I)
      (Ideal.map (Ideal.Quotient.mk I)
        (MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K))))
      = MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K)) := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  have hker : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rw [hker, sup_eq_left.mpr hle]

/-- Affine bridge (local mirror of
`ProjectiveLocus.zeroLocus_finite_of_krullDimLE_zero`): the zero locus of an
ideal with zero-dimensional quotient is finite (Noetherian + `KrullDimLE 0`
⟹ Artinian, finitely many maximal ideals, points inject into them).

## References

* `Geometry.ProjectiveLocus`, `zeroLocus_finite_of_krullDimLE_zero`
  (mirrored).
* `Mathlib/RingTheory/HopkinsLevitzki.lean`,
  `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`.
* `Mathlib/RingTheory/Artinian/Module.lean`,
  `IsArtinianRing.setOfPred_isMaximal_finite`.
* `Mathlib/Data/Set/Finite/Basic.lean`, `Set.Finite.of_injOn`.
* `Mathlib/RingTheory/Nullstellensatz.lean`, `MvPolynomial.zeroLocus`,
  `MvPolynomial.vanishingIdeal`,
  `MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal`.
* `Mathlib/Data/Set/Insert.lean`, `Set.singleton_subset_iff`.
* This module, `vanishingIdeal_singleton_injective_affine`,
  `map_vanishingIdeal_isMaximal_affine`,
  `comap_map_vanishingIdeal_affine` (mirrored above). -/
theorem zeroLocus_finite_of_krullDimLE_zero_affine
    {mm : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin mm) K))
    (hdim : Ring.KrullDimLE 0 (MvPolynomial (Fin mm) K ⧸ I)) :
    (MvPolynomial.zeroLocus K I).Finite := by
  have hArt : IsArtinianRing (MvPolynomial (Fin mm) K ⧸ I) :=
    @IsNoetherianRing.isArtinianRing_of_krullDimLE_zero _ _ _ hdim
  have hfinMax :=
    @IsArtinianRing.setOfPred_isMaximal_finite _ _ hArt
  refine Set.Finite.of_injOn (f := fun x : Fin mm → K =>
      Ideal.map (Ideal.Quotient.mk I)
        (MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K))))
    (t := {J : Ideal (MvPolynomial (Fin mm) K ⧸ I) | J.IsMaximal}) ?_ ?_ hfinMax
  · intro x hx
    change (Ideal.map (Ideal.Quotient.mk I)
      (MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K)))).IsMaximal
    have hle : I ≤ MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K)) :=
      (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal).mp
        (Set.singleton_subset_iff.mpr hx)
    exact map_vanishingIdeal_isMaximal_affine I x hle
  · intro x hx y hy hxy
    have hxle : I ≤ MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K)) :=
      (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal).mp
        (Set.singleton_subset_iff.mpr hx)
    have hyle : I ≤ MvPolynomial.vanishingIdeal K ({y} : Set (Fin mm → K)) :=
      (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal).mp
        (Set.singleton_subset_iff.mpr hy)
    have hxy' : Ideal.map (Ideal.Quotient.mk I)
          (MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K)))
        = Ideal.map (Ideal.Quotient.mk I)
          (MvPolynomial.vanishingIdeal K ({y} : Set (Fin mm → K))) := hxy
    have hJ : MvPolynomial.vanishingIdeal K ({x} : Set (Fin mm → K))
        = MvPolynomial.vanishingIdeal K ({y} : Set (Fin mm → K)) := by
      have h1 := comap_map_vanishingIdeal_affine I x hxle
      have h2 := comap_map_vanishingIdeal_affine I y hyle
      have hc := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hxy'
      rw [h1, h2] at hc
      exact hc
    exact vanishingIdeal_singleton_injective_affine hJ

/-- The `mkSystem` affine zero set is the `zeroLocus` of the `chartPoly` span
(`MvPolynomial.zeroLocus_span`; `aeval = eval` is `rfl`).

## References

* `Geometry.MkSystemChart`, `affineZero`,
  `chartPoly`.
* `Mathlib/RingTheory/Nullstellensatz.lean`, `MvPolynomial.zeroLocus_span`.
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval_eq_eval`. -/
theorem affineZero_eq_zeroLocus (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) :
    affineZero m K F
      = MvPolynomial.zeroLocus K
        (Ideal.span (Set.range (chartPoly m K F))) := by
  rw [MvPolynomial.zeroLocus_span]
  ext x
  simp only [affineZero, Set.mem_ofPred_eq]
  constructor
  · intro hx p hp
    obtain ⟨i, rfl⟩ := hp
    rw [MvPolynomial.aeval_eq_eval]
    exact hx i
  · intro hx i
    have h := hx _ ⟨i, rfl⟩
    rwa [MvPolynomial.aeval_eq_eval] at h

/-- Main affine bridge (closed): the `mkSystem` affine zero set is finite as
soon as its affine quotient is zero-dimensional. This discharges the
`(affineZero m K F).Finite` residual of
`MkSystemChart.locus_finite_of_bpf_affine` modulo the dimension hypothesis.

Conditional on exactly `[hdim]`.

## References

* This module, `affineZero_eq_zeroLocus`,
  `zeroLocus_finite_of_krullDimLE_zero_affine` (proved above).
* `Geometry.MkSystemChart`, `locus_finite_of_bpf_affine`
  (consumer). -/
theorem affineZero_finite_of_krullDimLE_zero (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hdim : Ring.KrullDimLE 0
      (MvPolynomial (Fin (m + 1)) K ⧸
        Ideal.span (Set.range (chartPoly m K F)))) :
    (affineZero m K F).Finite := by
  rw [affineZero_eq_zeroLocus]
  exact zeroLocus_finite_of_krullDimLE_zero_affine _ hdim

/-! ## §3 Dimension-drop route (conditional-exact)

From `RegularityBridge.SuccessiveSMulRegular` of the `m + 1` chart equations,
`RegularSequenceDimDrop.ringKrullDim_atPrime_quotient_span_add_of_successive` gives the
localized dimension equation; the `WithBot ℕ∞` cancellation below plus the two
explicit residuals (`AmbientLocalDimBound`, `LocalToGlobalDimZero`) assemble
`KrullDimLE 0` of the affine quotient, hence finiteness via §2. -/

/-- Pure `WithBot ℕ∞` cancellation: if `D + k = E` and `E ≤ k` then `D ≤ 0`.
Cancels the finite `k` via `ENat.add_le_add_iff_right` (needs `k ≠ ⊤`,
which holds for a naturals cast); the `⊥` case is `bot_le`.

## References

* `Mathlib/Algebra/Order/Monoid/Unbundled/WithTop.lean`, `WithBot.coe_add`,
  `WithBot.coe_natCast`.
* `Mathlib/Order/WithBot.lean`, `WithBot.coe_le_coe`.
* `Mathlib/Data/ENat/Basic.lean`, `ENat.add_le_add_iff_right`,
  `ENat.natCast_ne_top`, `ENat.natCast_zero`. -/
theorem dimLE_zero_of_add_eq_le {D E : WithBot ℕ∞} {k : ℕ}
    (heq : D + ((k : ℕ) : WithBot ℕ∞) = E)
    (hle : E ≤ ((k : ℕ) : WithBot ℕ∞)) :
    D ≤ (((0 : ℕ)) : WithBot ℕ∞) := by
  subst heq
  cases D with
  | bot => exact bot_le
  | coe d =>
    simp only [← WithBot.coe_natCast] at hle ⊢
    rw [← WithBot.coe_add] at hle
    rw [WithBot.coe_le_coe] at hle ⊢
    have hle2 : d + ((k : ℕ) : ℕ∞) ≤ (0 : ℕ∞) + ((k : ℕ) : ℕ∞) := by
      rw [zero_add]
      exact hle
    have hd0 : d ≤ (0 : ℕ∞) :=
      (ENat.add_le_add_iff_right (ENat.natCast_ne_top k)).mp hle2
    rw [ENat.natCast_zero]
    exact hd0

/-- Explicit residual R-amb: every localization of the polynomial ring at a
prime containing the `chartPoly` span has Krull dimension at most `m + 1`.
Closable in principle from `mvPolynomial_ringKrullDim` (in
`Dimension.PolynomialCatenary`) plus prime-correspondence monotonicity of
localization; no in-tree localization-dimension API exists (grep-verified:
`AtPrime` occurs in `Mathlib/RingTheory/KrullDimension/` only for the
global-to-local `Ring.KrullDimLE.of_isLocalization`).

## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `ringKrullDim`.
* `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`,
  `Localization.AtPrime`.
* `EvolutionAlgebras.Dimension.PolynomialCatenary`,
  `mvPolynomial_ringKrullDim` (cited by name, not imported). -/
def AmbientLocalDimBound (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) : Prop :=
  ∀ (P : Ideal (MvPolynomial (Fin (m + 1)) K)) [P.IsPrime],
    Ideal.span (Set.range (chartPoly m K F)) ≤ P →
      ringKrullDim (Localization.AtPrime P) ≤ (((m + 1 : ℕ)) : WithBot ℕ∞)

/-- Explicit residual R-glob: local dimension-zero at every prime containing
the `chartPoly` span (in exactly the `RegularSequenceDimDrop` quotient shape) implies
global dimension-zero of the affine quotient. Bundles the prime
correspondence, the quotient-localization commutation (in-tree only at maximal
ideals: `IsLocalization.AtPrime.equivQuotientMapOfIsMaximal`), and the
local-to-global `KrullDimLE 0` transfer — none available in-tree at a general
prime (grep-verified).

## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.KrullDimLE`.
* `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`,
  `Localization.AtPrime`.
* `Mathlib/RingTheory/Localization/AtPrime/Extension.lean`,
  `IsLocalization.AtPrime.equivQuotientMapOfIsMaximal` (maximal-only precedent).
* `EvolutionAlgebras.Dimension.RegularSequenceDimDrop`,
  `RegularSequenceDimDrop.ringKrullDim_atPrime_quotient_span_add_of_successive`
  (supplier of the antecedent). -/
def LocalToGlobalDimZero (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) : Prop :=
  (∀ (P : Ideal (MvPolynomial (Fin (m + 1)) K)) [P.IsPrime],
    Ideal.span (Set.range (chartPoly m K F)) ≤ P →
      Ring.KrullDimLE 0 (Localization.AtPrime P ⧸
        Ideal.span (Set.range (algebraMap (MvPolynomial (Fin (m + 1)) K)
          (Localization.AtPrime P) ∘ chartPoly m K F))))
  → Ring.KrullDimLE 0
      (MvPolynomial (Fin (m + 1)) K ⧸
        Ideal.span (Set.range (chartPoly m K F)))

/-- Dimension drop from successive regularity (proved modulo the two explicit
residuals): the localized `RegularSequenceDimDrop` equation plus the ambient bound
gives `KrullDimLE 0` at every prime, and `hglob` transfers globally.

Conditional on exactly `[hsucc, hambient, hglob]`. The `hsucc` input
(successive SMul-regularity of the `chartPoly` family) is the crux-linked
regularity hypothesis (cf.: CM-ness of successive quotients).

## References

* `EvolutionAlgebras.Dimension.RegularSequenceDimDrop`,
  `RegularSequenceDimDrop.ringKrullDim_atPrime_quotient_span_add_of_successive`.
* `EvolutionAlgebras.Regularity.Avoid.RegularityBridge`,
  `RegularityBridge.SuccessiveSMulRegular` (the `hsucc` shape).
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.krullDimLE_iff`.
* This module, `dimLE_zero_of_add_eq_le`,
  `AmbientLocalDimBound`,
  `LocalToGlobalDimZero` (proved/defined above). -/
theorem affineQuotient_dimZero_of_successiveRegular (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (chartPoly m K F))
    (hambient : AmbientLocalDimBound m K F)
    (hglob : LocalToGlobalDimZero m K F) :
    Ring.KrullDimLE 0
      (MvPolynomial (Fin (m + 1)) K ⧸
        Ideal.span (Set.range (chartPoly m K F))) := by
  apply hglob
  intro P _ hJP
  rw [Ring.krullDimLE_iff]
  have heq :=
    RegularSequenceDimDrop.ringKrullDim_atPrime_quotient_span_add_of_successive
      (P := P) (chartPoly m K F) hsucc hJP
  exact dimLE_zero_of_add_eq_le heq (hambient P hJP)

/-- Affine finiteness from successive regularity (dim-drop assembly).

Conditional on exactly `[hsucc, hambient, hglob]` (see
`affineQuotient_dimZero_of_successiveRegular` for the residual audit).

## References

* This module, `affineQuotient_dimZero_of_successiveRegular`,
  `affineZero_finite_of_krullDimLE_zero` (proved above). -/
theorem affineZero_finite_of_successiveRegular (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (chartPoly m K F))
    (hambient : AmbientLocalDimBound m K F)
    (hglob : LocalToGlobalDimZero m K F) :
    (affineZero m K F).Finite :=
  affineZero_finite_of_krullDimLE_zero m K F
    (affineQuotient_dimZero_of_successiveRegular m K F hsucc hambient hglob)

/-! ## §4 PDT route, scoped to this locus (conditional-exact)

The tex proof of Lemma `Zfinite` (via Corollary `meetshyperplane`) is
projective; at the affine locus it scopes to the end-to-end shape below: a
positive-dimensional affine quotient forces a nonzero common zero of the
input forms (the projective closure meets `{λ = 0}`, where the equations cut
out the top-degree parts — the homogeneous quadrics `Fᵢ`). Closure, PDT, and
the projective-affine prime correspondence have no in-tree API
(grep-verified), so the shape is taken as the explicit hypothesis
`MeetsInfinity`; the theorem proves it suffices together with
`BasePointFree`. The `O(Z') = K` alternative (tex Remark `altfinite`) needs
global regular functions on irreducible projective varieties (no
structure-sheaf-on-`Projectivization`-locus API in-tree) and is assessed but
not formalized. -/

/-- Explicit residual R-pdt (scoped PDT corollary for this locus): if the
affine `chartPoly` quotient is positive-dimensional, the input forms have a
nonzero common zero. End-to-end shape of "projective closure meets
`{λ = 0}`", statable without closure API.

## References

* `Geometry.MkSystemChart`, `chartPoly`,
  `BasePointFree`.
* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `Ring.KrullDimLE`. -/
def MeetsInfinity (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) : Prop :=
  ¬ Ring.KrullDimLE 0
      (MvPolynomial (Fin (m + 1)) K ⧸
        Ideal.span (Set.range (chartPoly m K F))) →
    ∃ v : Fin (m + 1) → K, v ≠ 0 ∧ ∀ i, MvPolynomial.eval v (F i) = 0

/-- Affine finiteness from the scoped PDT corollary plus base-point-freeness:
if the locus were infinite, the bridge's contrapositive gives
positive-dimensionality, `hPDT` gives a nonzero common `F`-zero,
contradicting `hBPF`.

Conditional on exactly `[hPDT, hBPF]`.

## References

* This module, `MeetsInfinity`,
  `affineZero_finite_of_krullDimLE_zero` (proved above).
* `Geometry.MkSystemChart`, `BasePointFree` (the tex `(bpf)`
  input). -/
theorem affineZero_finite_of_meetsInfinity (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hPDT : MeetsInfinity m K F)
    (hBPF : BasePointFree m K F) :
    (affineZero m K F).Finite := by
  by_contra hnf
  have hpos : ¬ Ring.KrullDimLE 0
      (MvPolynomial (Fin (m + 1)) K ⧸
        Ideal.span (Set.range (chartPoly m K F))) :=
    fun hdim => hnf (affineZero_finite_of_krullDimLE_zero m K F hdim)
  obtain ⟨v, hv, hFv⟩ := hPDT hpos
  obtain ⟨i, hi⟩ := hBPF v hv
  exact hi (hFv i)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## §5 hdim chase: exact residual is `[hsucc]` modulo proved by-name inputs

Feasibility note (`hdim`): `hdim` already follows from `[hsucc, hambient, hglob]`
via `affineQuotient_dimZero_of_successiveRegular` (§3); the chase below shows
`hambient` and `hglob` are by-name instances of proved results —
`AmbientLocalDimBound` from `LocalizationDimension.ringKrullDim_atPrime_le` plus the
`PolynomialCatenary.mvPolynomial_ringKrullDim` equation, `LocalToGlobalDimZero` from
`LocalizationDimension.krullDimLE_zero_quotient_span_of_localized` — taken as verbatim-shape
binders (cited by name, never imported, per the frozen-import-block DAG
precedent). The sole genuine residual is therefore `hsucc`, successive
SMul-regularity of the `m + 1` chart equations at length `≥ 2`, which is exactly
the central crux (`MkSystemRegular` grade: rung 0 proved, rung 1 triangular,
rungs `≥ 2` = `hunmixed_ge2`; cf. `RegularSequenceDimDrop` note and).
Closing `hsucc` closes `hdim` via `hdim_of_hsucc_of_dimAPI`, hence affine
finiteness via `affineZero_finite_of_hsucc_of_dimAPI`.

Status: `hdim` is conditional on exactly `[hsucc]` modulo the three proved
by-name shapes (`hAtPrime`, `hpoly`, `htrans`). -/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- `AmbientLocalDimBound` from the two proved by-name inputs: localization
monotonicity of `ringKrullDim` plus the polynomial-ring dimension equation.

## References

* `Dimension.LocalizationDimension`,
  `LocalizationDimension.ringKrullDim_atPrime_le`
  (verbatim `hAtPrime` shape, cited by name).
* `Dimension.PolynomialCatenary`, `mvPolynomial_ringKrullDim`
  (verbatim `hpoly` shape, cited by name).
* This module, `AmbientLocalDimBound` (consumer shape). -/
theorem ambientLocalDimBound_of_dimAPI (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hAtPrime : ∀ (P : Ideal (MvPolynomial (Fin (m + 1)) K)) [P.IsPrime],
      ringKrullDim (Localization.AtPrime P)
        ≤ ringKrullDim (MvPolynomial (Fin (m + 1)) K))
    (hpoly : ringKrullDim (MvPolynomial (Fin (m + 1)) K)
      = ((((m + 1 : ℕ))) : WithBot ℕ∞)) :
    AmbientLocalDimBound m K F := by
  intro P _ _
  calc ringKrullDim (Localization.AtPrime P)
      ≤ ringKrullDim (MvPolynomial (Fin (m + 1)) K) := hAtPrime P
    _ = ((((m + 1 : ℕ))) : WithBot ℕ∞) := hpoly

/-- `LocalToGlobalDimZero` is the verbatim `LocalizationDimension` transfer instance at
`q := chartPoly m K F` (definitional match, proved by application).

## References

* `Dimension.LocalizationDimension`,
  `LocalizationDimension.krullDimLE_zero_quotient_span_of_localized`
  (verbatim `htrans` shape, cited by name).
* This module, `LocalToGlobalDimZero` (consumer shape). -/
theorem localToGlobalDimZero_of_dimAPI (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (htrans : (∀ (P : Ideal (MvPolynomial (Fin (m + 1)) K)) [P.IsPrime],
      Ideal.span (Set.range (chartPoly m K F)) ≤ P →
        Ring.KrullDimLE 0 (Localization.AtPrime P ⧸
          Ideal.span (Set.range (algebraMap (MvPolynomial (Fin (m + 1)) K)
            (Localization.AtPrime P) ∘ chartPoly m K F))))
      → Ring.KrullDimLE 0
        (MvPolynomial (Fin (m + 1)) K ⧸
          Ideal.span (Set.range (chartPoly m K F)))) :
    LocalToGlobalDimZero m K F :=
  fun h => htrans h

/-- `hdim` chase assembly: the affine-quotient dimension hypothesis from
`hsucc` plus the three proved by-name dimension shapes.

Conditional on exactly `[hsucc]` modulo `[hAtPrime, hpoly, htrans]`.

## References

* This module, `affineQuotient_dimZero_of_successiveRegular`,
  `ambientLocalDimBound_of_dimAPI`,
  `localToGlobalDimZero_of_dimAPI` (proved above).
* `Regularity.Avoid.MkSystemRegular` (grade: `hsucc` at rungs `≥ 2` is the
  `hunmixed_ge2` crux, cited by name). -/
theorem hdim_of_hsucc_of_dimAPI (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (chartPoly m K F))
    (hAtPrime : ∀ (P : Ideal (MvPolynomial (Fin (m + 1)) K)) [P.IsPrime],
      ringKrullDim (Localization.AtPrime P)
        ≤ ringKrullDim (MvPolynomial (Fin (m + 1)) K))
    (hpoly : ringKrullDim (MvPolynomial (Fin (m + 1)) K)
      = ((((m + 1 : ℕ))) : WithBot ℕ∞))
    (htrans : (∀ (P : Ideal (MvPolynomial (Fin (m + 1)) K)) [P.IsPrime],
      Ideal.span (Set.range (chartPoly m K F)) ≤ P →
        Ring.KrullDimLE 0 (Localization.AtPrime P ⧸
          Ideal.span (Set.range (algebraMap (MvPolynomial (Fin (m + 1)) K)
            (Localization.AtPrime P) ∘ chartPoly m K F))))
      → Ring.KrullDimLE 0
        (MvPolynomial (Fin (m + 1)) K ⧸
          Ideal.span (Set.range (chartPoly m K F)))) :
    Ring.KrullDimLE 0
      (MvPolynomial (Fin (m + 1)) K ⧸
        Ideal.span (Set.range (chartPoly m K F))) :=
  affineQuotient_dimZero_of_successiveRegular m K F hsucc
    (ambientLocalDimBound_of_dimAPI m K F hAtPrime hpoly)
    (localToGlobalDimZero_of_dimAPI m K F htrans)

/-- Affine finiteness from `hsucc` plus the proved by-name dimension shapes
(dim-drop chase end-to-end).

Conditional on exactly `[hsucc]` modulo `[hAtPrime, hpoly, htrans]`.

## References

* This module, `hdim_of_hsucc_of_dimAPI`,
  `affineZero_finite_of_krullDimLE_zero` (proved above). -/
theorem affineZero_finite_of_hsucc_of_dimAPI (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular (chartPoly m K F))
    (hAtPrime : ∀ (P : Ideal (MvPolynomial (Fin (m + 1)) K)) [P.IsPrime],
      ringKrullDim (Localization.AtPrime P)
        ≤ ringKrullDim (MvPolynomial (Fin (m + 1)) K))
    (hpoly : ringKrullDim (MvPolynomial (Fin (m + 1)) K)
      = ((((m + 1 : ℕ))) : WithBot ℕ∞))
    (htrans : (∀ (P : Ideal (MvPolynomial (Fin (m + 1)) K)) [P.IsPrime],
      Ideal.span (Set.range (chartPoly m K F)) ≤ P →
        Ring.KrullDimLE 0 (Localization.AtPrime P ⧸
          Ideal.span (Set.range (algebraMap (MvPolynomial (Fin (m + 1)) K)
            (Localization.AtPrime P) ∘ chartPoly m K F))))
      → Ring.KrullDimLE 0
        (MvPolynomial (Fin (m + 1)) K ⧸
          Ideal.span (Set.range (chartPoly m K F)))) :
    (affineZero m K F).Finite :=
  affineZero_finite_of_krullDimLE_zero m K F
    (hdim_of_hsucc_of_dimAPI m K F hsucc hAtPrime hpoly htrans)

/-! ## §6 hBPF chase: exact residual is `[hcoord, hbridge]` with by-name suppliers

Feasibility note (`hBPF`): `BasePointFree m K F` is a theorem input at geometry
level, but its upstream discharge chain is fully proved: `hN : N(V) = {0}` gives
coordinate-level base-point-freeness on `sqCoords` via `MkSecondPoint.bpf_of_hN`
(which needs the `E`-algebra spine — basis, structure-constant expansion,
`IsScalarTower`/`SMulCommClass` — plus 4 reuse lemmas), and
`MkSystemBridge.eval_mkQuadForm` turns coordinate zeros into `MvPolynomial.eval`
zeros at the `mkQuadForm` family (with quadratic homogeneity from
`mkQuadForm_isHomogeneous`). Neither source is importable here (`MkSystemBridge`
transitively imports `FixedPointFromBezout` and `Statement`, both
outside this file's frozen import block), so both links are
taken as verbatim-shape
binders (`hcoord`, `hbridge`) and `basePointFree_of_coordBPF_of_evalBridge`
proves they suffice; instantiating `G` at the `sqCoords` pattern and `F` at
`bridgeForms` at the fixed-point consumer closes `hBPF`.

Status: `hBPF` is conditional on exactly `[hcoord, hbridge]` with by-name
suppliers (`bpf_of_hN`, `eval_mkQuadForm`). -/

/-- `BasePointFree` from coordinate-level BPF plus the eval bridge: a common
polynomial zero is a common coordinate zero via `hbridge`, hence `0` via
`hcoord`, contradicting `a ≠ 0`.

## References

* `BridgeToFixedPoint.SecondPointExistence`,
  `MkSecondPoint.bpf_of_hN`
  (verbatim `hcoord`-shape supplier at `G := sqCoords`-pattern, cited by name).
* `BridgeToFixedPoint.MkSystemBridge`,
  `MkSystemBridge.eval_mkQuadForm`
  (verbatim `hbridge`-shape supplier at `F := bridgeForms`, cited by name).
* `Geometry.MkSystemChart`, `BasePointFree` (conclusion shape). -/
theorem basePointFree_of_coordBPF_of_evalBridge (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (G : Fin (m + 1) → (Fin (m + 1) → K) → K)
    (hcoord : ∀ X : Fin (m + 1) → K, (∀ k, G k X = 0) → X = 0)
    (hbridge : ∀ k X, MvPolynomial.eval X (F k) = G k X) :
    BasePointFree m K F := by
  intro a ha
  by_contra hcon
  apply ha
  apply hcoord
  intro k
  have h0 : MvPolynomial.eval a (F k) = 0 := by
    by_contra hk
    exact hcon ⟨k, hk⟩
  rw [← hbridge]
  exact h0

/-- Affine finiteness from the PDT route with chased `hBPF`
(PDT chase end-to-end).

Conditional on exactly `[hPDT, hcoord, hbridge]`.

## References

* This module, `affineZero_finite_of_meetsInfinity`,
  `basePointFree_of_coordBPF_of_evalBridge` (proved above). -/
theorem affineZero_finite_of_meetsInfinity_of_coordBPF (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (hPDT : MeetsInfinity m K F)
    (G : Fin (m + 1) → (Fin (m + 1) → K) → K)
    (hcoord : ∀ X : Fin (m + 1) → K, (∀ k, G k X = 0) → X = 0)
    (hbridge : ∀ k X, MvPolynomial.eval X (F k) = G k X) :
    (affineZero m K F).Finite :=
  affineZero_finite_of_meetsInfinity m K F hPDT
    (basePointFree_of_coordBPF_of_evalBridge m K F G hcoord hbridge)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## §7 hcoord/hbridge instantiation for the mkSystem family (conditional-exact)

Supplier locations (found; all proved):
* `bpf_of_hN`: `BridgeToFixedPoint/SecondPointExistence.lean` (`MkSecondPoint.bpf_of_hN`,
  clean file importing only `Statement.Definitions` + `A_Preliminaries` + Mathlib).
* `eval_mkQuadForm`: `BridgeToFixedPoint/MkSystemBridge.lean` (duplicate at
  `BridgeToFixedPoint/FixedPointFromBezout.lean`); `mkQuadForm` bodies at
  `MkSystemBridge.lean` / `FixedPointFromBezout.lean`;
  `mkQuadForm_isHomogeneous` /.
* `bridgeSystem_eval` (mkSystem-level split): `MkSystemBridge.lean`
  (duplicate at `FixedPointFromBezout.lean`); already proved in-scope here
  as the imported `MkSystemChart.eval_mkSystem_eq`, so not mirrored (§6
  `hbridge` needs only the F-level `eval_mkQuadForm`).
* Reindex invariance `sqCoords_shift`: `FixedPointFromBezout.lean`
  (consumer-side).

Why mirrors, not imports: (1) `MkSystemBridge` transitively imports
`FixedPointFromBezout` and `Statement.Statement` (still
unimportable here under the import-DAG rule); (2) this file's imports are frozen
with a frozen import
block (Lean forbids `import` after any command), so even the clean
`SecondPointExistence` is unimportable; (3) three divergent `sqCoords` copies
already exist (`FixedPointFromBezout`, `CoordinatizationToolkit`, `MkSecondPoint`
namespaces, same bodies) — importing any one still needs cross-namespace
defeq identification, which a single local mirror sidesteps. The shift layer
(`statementIndex`/`shiftEquiv`/`shiftConsts`/`bridgeForms`) is likewise not
mirrored: the family below is stated at level `m + 1` with arbitrary `c`, and
the fixed-point consumer instantiates `c := shiftConsts …` (reindex invariance
is the proved `sqCoords_shift`, applied consumer-side).

`hPDT` status: `MeetsInfinity` as stated is false in general
(`CurveMeet.meetsInfinity_ofLinear_false`, witness `F i = X i`, linear input)
but the corrected shape `(hF: ∀ i, (F i).IsHomogeneous 2) → [IsAlgClosed K] →
MeetsInfinity` is proved unconditionally
(`CurveMeet.meetsInfinity_of_isHomogeneous` via the Nullstellensatz). The
family below is quadratic, so the refutation does not apply; `hPDT` is kept as
a family-instance binder (per the §5 instance-binder precedent) and
`familyForms_affine_homogeneous` closes the `hF` input needed
to discharge it via `CurveMeet` by-name (defeq transfer of the mirrored
`MeetsInfinity`/`chartPoly`, per the `CurveMeet` precedent).

Status: `(affineZero m K (familyForms_affine m K c)).Finite` is conditional on
exactly `[hPDT, h_mem, h_expand, h_zero_smul, h_nil, h_inj]`. `hcoord`
(`bpf_of_hN_affine`), `hbridge` (`eval_mkQuadForm_affine`), and family
quadraticity (`familyForms_affine_homogeneous`) are closed (proved in-file).
`hPDT` is by-name-dischargeable (`CurveMeet.meetsInfinity_of_isHomogeneous` +
`familyForms_affine_homogeneous`); the reuse binders are by-name-dischargeable
(`CoordinatizationToolkit.coordVec_mem` / `sq_expand` / `coordVec_eq_zero` /
`eq_zero_of_mem_sq_eq_zero` + consumer `hexp`/`hN`, `exact`-up-to-defeq since
the `sqCoords` bodies are identical).

DAG safety: no new imports; mirrors under `_affine` names with
by-name citations, per the `MkSystemChart`/`CurveMeet` precedent. -/

/-- Coordinate quadrics: `Fₖ(X)` is the `k`-th coordinate of `v(X)²`. Body
verbatim from `CoordinatizationToolkit.sqCoords` / `FixedPointFromBezout.sqCoords` /
`MkSecondPoint.sqCoords` (same body, three namespaces — this single local copy
sidesteps cross-namespace identification; see the §7 header).

## References

* `BridgeToFixedPoint.CoordinatizationToolkit`,
  `CoordinatizationToolkit.sqCoords`
  (`CoordinatizationToolkit.lean`).
* `BridgeToFixedPoint.FixedPointFromBezout`, `sqCoords`
  (`FixedPointFromBezout.lean`).
* `BridgeToFixedPoint.SecondPointExistence`,
  `MkSecondPoint.sqCoords`
  (`SecondPointExistence.lean`). -/
def sqCoords_affine {n : ℕ} (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (k : Fin n) (X : Fin n → K) : K :=
  ∑ i, ∑ j, c i j k * X i * X j

/-- Coordinate-level base-point-freeness (the `hN`-analogue): the only common
zero of the quadrics is `X = 0`. Verbatim shape of `MkSecondPoint.BPF`.

## References

* `BridgeToFixedPoint.SecondPointExistence`, `MkSecondPoint.BPF`
  (`SecondPointExistence.lean`).
* This module, `sqCoords_affine` (proved above). -/
def coordBPF_affine (K : Type*) [Field K] (n : ℕ)
    (c : Fin n → Fin n → Fin n → K) : Prop :=
  ∀ X : Fin n → K, (∀ k, sqCoords_affine K c k X = 0) → X = 0

/-- `coordBPF` from `hN`-style data (spine-abstracted mirror of
`MkSecondPoint.bpf_of_hN`): a common zero `X` gives `v(X)² = 0` (via
`h_expand`), hence `v(X) = 0` (via `h_nil`), hence `X = 0` (via `h_inj`).
The `E`-algebra spine is abstracted (`v`/`w`/`P` replace `coordVec`/`b`/`∈ V`,
`h_nil` replaces `eq_zero_of_mem_sq_eq_zero V hN`, `h_zero_smul` replaces the
`zero_smul` instance fact) so no algebra imports beyond the frozen block are
needed; the consumer feeds `CoordinatizationToolkit.coordVec_mem` / `sq_expand` /
`coordVec_eq_zero` / `eq_zero_of_mem_sq_eq_zero` + `hexp`/`hN`
(`exact`-up-to-defeq, identical `sqCoords` bodies).

## References

* `BridgeToFixedPoint.SecondPointExistence`,
  `MkSecondPoint.bpf_of_hN`
  (`SecondPointExistence.lean`, proof).
* `BridgeToFixedPoint.CoordinatizationToolkit`,
  `CoordinatizationToolkit.coordVec_mem` , `sq_expand`
  , `coordVec_eq_zero` , `eq_zero_of_mem_sq_eq_zero`
  (by-name discharge shapes).
* `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`,
  `Finset.prod_const_one` (`to_additive` → `Finset.sum_const_zero`, simp).
* `Mathlib/Algebra/Group/Monoid.lean`, `AddCommMonoid`. -/
theorem bpf_of_hN_affine {n : ℕ} {K E : Type*} [Field K]
    [AddCommMonoid E] [Mul E] [SMul K E]
    (c : Fin n → Fin n → Fin n → K)
    (v : (Fin n → K) → E) (w : Fin n → E) (P : E → Prop)
    (h_mem : ∀ X, P (v X))
    (h_expand : ∀ X, v X * v X = ∑ k, (sqCoords_affine K c k X) • w k)
    (h_zero_smul : ∀ e : E, (0 : K) • e = 0)
    (h_nil : ∀ {x : E}, P x → x * x = 0 → x = 0)
    (h_inj : ∀ X, v X = 0 → X = 0) :
    coordBPF_affine K n c := by
  intro X hX
  have hsq0 : v X * v X = 0 := by
    rw [h_expand X]
    simp only [hX, h_zero_smul, Finset.sum_const_zero]
  exact h_inj X (h_nil (h_mem X) hsq0)

/-- Quadratic-form polynomials from structure constants. Body verbatim from
`MkSystemBridge.mkQuadForm` / `FixedPointFromBezout.mkQuadForm`.

## References

* `BridgeToFixedPoint.MkSystemBridge`, `MkSystemBridge.mkQuadForm`
  (`MkSystemBridge.lean`).
* `BridgeToFixedPoint.FixedPointFromBezout`, `mkQuadForm`
  (`FixedPointFromBezout.lean`). -/
noncomputable def mkQuadForm_affine (N : ℕ) (K : Type*) [Field K]
    (c : Fin N → Fin N → Fin N → K) (k : Fin N) : MvPolynomial (Fin N) K :=
  ∑ i, ∑ j, MvPolynomial.C (c i j k) * (MvPolynomial.X i * MvPolynomial.X j)

/-- Evaluation recovers the coordinate functions: the §6 `hbridge` link.
Proof verbatim from `MkSystemBridge.eval_mkQuadForm` /
`FixedPointFromBezout.eval_mkQuadForm`.

## References

* `BridgeToFixedPoint.MkSystemBridge`,
  `MkSystemBridge.eval_mkQuadForm`
  (`MkSystemBridge.lean`).
* `BridgeToFixedPoint.FixedPointFromBezout`, `eval_mkQuadForm`
  (`FixedPointFromBezout.lean`).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.eval_sum` ,
  `MvPolynomial.eval_mul` , `MvPolynomial.eval_C` ,
  `MvPolynomial.eval_X`.
* `Finset.sum_congr` (standard Finset API; usage-verified in
  `CoordinatizationToolkit.sqCoords_hom`, `FixedPointFromBezout.eval_mkQuadForm`). -/
theorem eval_mkQuadForm_affine (N : ℕ) (K : Type*) [Field K]
    (c : Fin N → Fin N → Fin N → K) (k : Fin N) (X : Fin N → K) :
    MvPolynomial.eval X (mkQuadForm_affine N K c k)
      = sqCoords_affine K c k X := by
  unfold mkQuadForm_affine sqCoords_affine
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc]

/-- Each quadratic-form polynomial is homogeneous of degree `2` (char-2 safe:
monomial argument only). Proof verbatim from
`MkSystemBridge.mkQuadForm_isHomogeneous`. Feeds the `hF` input of the
corrected hPDT (`CurveMeet.meetsInfinity_of_isHomogeneous`).

## References

* `BridgeToFixedPoint.MkSystemBridge`,
  `MkSystemBridge.mkQuadForm_isHomogeneous`
  (`MkSystemBridge.lean`).
* `BridgeToFixedPoint.FixedPointFromBezout`,
  `mkQuadForm_isHomogeneous`
  (`FixedPointFromBezout.lean`).
* `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean`,
  `MvPolynomial.IsHomogeneous.sum` , `MvPolynomial.IsHomogeneous.mul`
  , `MvPolynomial.isHomogeneous_C` ,
  `MvPolynomial.isHomogeneous_X`. -/
theorem mkQuadForm_affine_isHomogeneous (N : ℕ) (K : Type*) [Field K]
    (c : Fin N → Fin N → Fin N → K) (k : Fin N) :
    (mkQuadForm_affine N K c k).IsHomogeneous 2 := by
  unfold mkQuadForm_affine
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  simpa using (MvPolynomial.isHomogeneous_C _ _).mul
    ((MvPolynomial.isHomogeneous_X _ _).mul (MvPolynomial.isHomogeneous_X _ _))

/-- The mkSystem-family input forms at level `m`: `F k` is the quadratic form
for constants `c` (the unshifted `bridgeForms` shape; the consumer
instantiates `c := shiftConsts …`, with reindex invariance from the proved
`FixedPointFromBezout.sqCoords_shift`).

## References

* `BridgeToFixedPoint.MkSystemBridge`, `MkSystemBridge.bridgeForms`
  (`MkSystemBridge.lean`), `shiftConsts`.
* `BridgeToFixedPoint.FixedPointFromBezout`, `sqCoords_shift`
  (`FixedPointFromBezout.lean`) (consumer-side reindex step).
* This module, `mkQuadForm_affine` (proved above). -/
noncomputable def familyForms_affine (m : ℕ) (K : Type*) [Field K]
    (c : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → K) :
    Fin (m + 1) → MvPolynomial (Fin (m + 1)) K :=
  fun k => mkQuadForm_affine (m + 1) K c k

/-- The family forms are quadratic (the `hF` input discharging corrected-hPDT
via `CurveMeet.meetsInfinity_of_isHomogeneous`).

## References

* This module, `mkQuadForm_affine_isHomogeneous` (proved above).
* `Geometry.CurveMeetsHyperplane`,
  `CurveMeet.meetsInfinity_of_isHomogeneous`  (consumer). -/
theorem familyForms_affine_homogeneous (m : ℕ) (K : Type*) [Field K]
    (c : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → K) :
    ∀ i, ((familyForms_affine m K c) i).IsHomogeneous 2 := by
  intro i
  change (mkQuadForm_affine (m + 1) K c i).IsHomogeneous 2
  exact mkQuadForm_affine_isHomogeneous _ K _ _

/-- `BasePointFree` for the mkSystem family from `hN`-style data (§6
instantiated at `G := sqCoords_affine`-pattern, `F := familyForms_affine`).

Conditional on exactly `[h_mem, h_expand, h_zero_smul, h_nil, h_inj]`
(by-name-dischargeable via `CoordinatizationToolkit` + consumer `hexp`/`hN`; see
`bpf_of_hN_affine`).

## References

* This module, `basePointFree_of_coordBPF_of_evalBridge`,
  `bpf_of_hN_affine`,
  `eval_mkQuadForm_affine` (proved above).
* `Geometry.MkSystemChart`, `BasePointFree` (conclusion shape). -/
theorem basePointFree_familyForms_affine (m : ℕ) (K : Type*) [Field K]
    (c : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → K)
    (E : Type*) [AddCommMonoid E] [Mul E] [SMul K E]
    (v : (Fin (m + 1) → K) → E) (w : Fin (m + 1) → E) (P : E → Prop)
    (h_mem : ∀ X, P (v X))
    (h_expand : ∀ X, v X * v X = ∑ k, (sqCoords_affine K c k X) • w k)
    (h_zero_smul : ∀ e : E, (0 : K) • e = 0)
    (h_nil : ∀ {x : E}, P x → x * x = 0 → x = 0)
    (h_inj : ∀ X, v X = 0 → X = 0) :
    BasePointFree m K (familyForms_affine m K c) :=
  basePointFree_of_coordBPF_of_evalBridge m K _
    (fun k X => sqCoords_affine K c k X)
    (bpf_of_hN_affine c v w P h_mem h_expand h_zero_smul h_nil h_inj)
    (fun k X => eval_mkQuadForm_affine (m + 1) K c k X)

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-! ## §8 hfin bind: hPDT + reuse + shift + hF end-to-end

Closes the §7 residual `[hPDT, h_mem, h_expand, h_zero_smul, h_nil, h_inj]`
at the shifted family `c := shiftConsts n K c0 hn` (the exact fixed-point
consumer shape):

* (i) `hPDT`: `meetsInfinity_familyForms_affine_of_curveMeet` derives the
  family `hPDT` from the verbatim `CurveMeet.meetsInfinity_of_isHomogeneous`
  conclusion shape (`hCurveMeet` binder) + `familyForms_affine_homogeneous`
  + defeq transfer (`meetsInfinity_curve_transfer`, `Iff.rfl`, both
  `chartPoly` bodies `F i - X i`). The proved supplier needs the
  global `[IsAlgClosed K]` at its site (carried as an instance
  binder here, cf. `Statement.Statement.bezout_quadratic`).
* (ii) reuse: `coordVec_mem_affine` / `sq_expand_affine` /
  `coordVec_eq_zero_affine` mirror the proved `CoordinatizationToolkit` proofs verbatim
  (RHS at `sqCoords_affine`, defeq to `CoordinatizationToolkit.sqCoords` by
  `rfl`); `eq_zero_of_mem_sq_eq_zero_affine`
  mirrors the `hN` rule over the local `absNilpotent_affine` mirror
  (`A_Preliminaries` is outside the transitive import closure, so the
  two-line `N(V)` def is mirrored); `h_zero_smul_affine` closes
  `h_zero_smul` via `zero_smul`. `basePointFree_familyForms_of_algebraData`
  assembles `BasePointFree` from algebra data `(V, b, hexp, hN)` + the
  tower/comm Prop binders.
* (iii) shift: `statementIndex_affine` / `shiftEquiv_affine` /
  `shiftConsts_affine` mirror the `FixedPointFromBezout` T1 data (same
  bodies, plain defs); `sqCoords_shift_affine` mirrors the proved
  `sqCoords_shift` proof verbatim; `h_expand_shift_affine` /
  `h_inj_shift_affine` transport the abstract reuse binders across the
  shift (`h_mem`/`h_nil`/`h_zero_smul` transport by `exact`, done inline).
* hF: `shiftedFamily_homogeneous` closes homogeneity at the shifted family
  (verbatim shape of `MkSystemBridge.bridgeForms_homogeneous` /
  `FixedPointFromBezout.bridgeForms_homogeneous`, both proved).
* End-to-end: `affineZero_finite_shiftedFamily_of_algebraData`.

Why mirrors, not imports (DAG check): `FixedPointFromBezout`
transitively imports `Statement.Statement` + `Geometry.Counting`
(via `BridgeToFixedPoint.MkSystemSmoothness`), so an import
would still violate the import-DAG rule; `CurveMeet` (leaf over `PolynomialCatenary`) and
`CoordinatizationToolkit` (leaf over `A_Preliminaries`) would be acyclic but this file's
import block is frozen. All mirrors carry by-name citations.

Status: `(affineZero (statementIndex n) K (familyForms_affine … shifted)).Finite`
is conditional on exactly `[hCurveMeet]` given consumer algebra data
`(V, b, hexp, hN, htower, hcomm)` + `[IsAlgClosed K]`. `hCurveMeet` is the
verbatim conclusion shape of proved-unconditional
`CurveMeet.meetsInfinity_of_isHomogeneous`; everything else is proved
in-file. No new imports; all Mathlib names used below are
transitively available (probed via `#check` under the §7 import closure)
and pinned to Mathlib v4.34.0 declaration sites in the per-declaration
references. -/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ### §8a Defeq-transfer mirrors for (i) (`CurveMeet` shapes) -/

/-- Mirror of `CurveMeet.chartPoly` (`qᵢ = Fᵢ − Xᵢ`), cited by name and never
imported (see the §8 header's DAG note).

## References

* `Geometry.CurveMeetsHyperplane`, `CurveMeet.chartPoly`.
* `Geometry.MkSystemChart`, `chartPoly` (imported original). -/
noncomputable def chartPoly_curve_affine (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1)) K :=
  F i - MvPolynomial.X i

/-- The mirror body is the imported `chartPoly` body (`rfl`).

## References

* This module, `chartPoly_curve_affine` (proved above).
* `Geometry.MkSystemChart`, `chartPoly` (imported original). -/
theorem chartPoly_curve_affine_eq (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K)
    (i : Fin (m + 1)) :
    chartPoly_curve_affine m K F i = chartPoly m K F i := rfl

/-- Mirror of `CurveMeet.MeetsInfinity` (the corrected-hPDT conclusion shape),
cited by name and never imported.

## References

* `Geometry.CurveMeetsHyperplane`, `CurveMeet.MeetsInfinity`.
* This module, `MeetsInfinity` (imported-shape original, §4). -/
def MeetsInfinity_curve_affine (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) : Prop :=
  ¬ Ring.KrullDimLE 0
      (MvPolynomial (Fin (m + 1)) K ⧸
        Ideal.span (Set.range (chartPoly_curve_affine m K F))) →
    ∃ v : Fin (m + 1) → K, v ≠ 0 ∧ ∀ i, MvPolynomial.eval v (F i) = 0

/-- Defeq transfer: the mirrored `MeetsInfinity` is the §4 `MeetsInfinity`
(`Iff.rfl` — both `chartPoly` bodies unfold to `F i - X i`).

## References

* This module, `MeetsInfinity_curve_affine`,
  `chartPoly_curve_affine_eq` (proved above). -/
theorem meetsInfinity_curve_transfer (m : ℕ) (K : Type*) [Field K]
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K) :
    MeetsInfinity_curve_affine m K F ↔ MeetsInfinity m K F := Iff.rfl

/-! ### §8b (i) hPDT discharge at the mkSystem family -/

/-- Family `hPDT` from the verbatim corrected-`MeetsInfinity` shape: the
`hCurveMeet` binder is the conclusion shape of proved-unconditional
`CurveMeet.meetsInfinity_of_isHomogeneous` (which needs `[IsAlgClosed K]`
at its site, carried here); `familyForms_affine_homogeneous` supplies its
`hF` input and `meetsInfinity_curve_transfer` moves the conclusion to the
§4 shape.

Conditional on exactly `[hCurveMeet]` (verbatim proved shape).

## References

* `Geometry.CurveMeetsHyperplane`,
  `CurveMeet.meetsInfinity_of_isHomogeneous` (proved
  unconditional modulo `[IsAlgClosed K]`).
* This module, `familyForms_affine_homogeneous`,
  `meetsInfinity_curve_transfer` (proved above). -/
theorem meetsInfinity_familyForms_affine_of_curveMeet (m : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (c : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → K)
    (hCurveMeet : ∀ (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) K),
      (∀ i, (F i).IsHomogeneous 2) → MeetsInfinity_curve_affine m K F) :
    MeetsInfinity m K (familyForms_affine m K c) :=
  (meetsInfinity_curve_transfer m K _).mp
    (hCurveMeet _ (familyForms_affine_homogeneous m K c))

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ### §8c (ii) reuse mirrors (`CoordinatizationToolkit` proofs, verbatim) -/

/-- Mirror of `CoordinatizationToolkit.coordVec`, cited by name and never imported.

## References

* `BridgeToFixedPoint.CoordinatizationToolkit`,
  `CoordinatizationToolkit.coordVec`
  (`CoordinatizationToolkit.lean`). -/
noncomputable def coordVec_affine (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [Module K E] {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (X : Fin n → K) : E :=
  ∑ i, X i • (b i : E)

/-- Mirror of `CoordinatizationToolkit.coordVec_mem` (proof verbatim): coordinate vectors
lie in `V`. Feeds the §7 `h_mem` binder at `v := coordVec_affine`,
`P := (· ∈ V)`.

## References

* `BridgeToFixedPoint.CoordinatizationToolkit`,
  `CoordinatizationToolkit.coordVec_mem`
  (`CoordinatizationToolkit.lean`).
* `Mathlib/Algebra/Module/Submodule/Basic.lean`, `Submodule.sum_mem`,
  `Submodule.smul_mem` (transitively imported; usage-verified in
  `CoordinatizationToolkit.coordVec_mem`). -/
theorem coordVec_mem_affine (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [Module K E] {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (X : Fin n → K) : coordVec_affine K E b X ∈ V := by
  unfold coordVec_affine
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact (b i).property

/-- Mirror of `CoordinatizationToolkit.sq_expand` (proof verbatim; RHS at `sqCoords_affine`,
defeq to the original by `rfl`). Feeds the §7 `h_expand`
binder. The tower/comm hypotheses are explicit `Prop` binders
(re-installed locally via `have`), matching the `CoordinatizationToolkit` signature.

## References

* `BridgeToFixedPoint.CoordinatizationToolkit`,
  `CoordinatizationToolkit.sq_expand`
  (`CoordinatizationToolkit.lean`).
* `Mathlib/Algebra/Group/Action/Defs.lean`, `smul_mul_assoc`,
  `mul_smul_comm` (transitively imported; usage-verified in
  `CoordinatizationToolkit.sq_expand`).
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_mul`, `Finset.mul_sum`, `Finset.sum_comm`, `Finset.smul_sum`,
  `Finset.sum_smul` (transitively imported; usage-verified in
  `CoordinatizationToolkit.sq_expand`). -/
theorem sq_expand_affine (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [Module K E] {V : Submodule K E} {n : ℕ} (b : Module.Basis (Fin n) K V)
    (c : Fin n → Fin n → Fin n → K)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (X : Fin n → K) (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    coordVec_affine K E b X * coordVec_affine K E b X =
      ∑ k, sqCoords_affine K c k X • (b k : E) := by
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
  have hR : (∑ k, sqCoords_affine K c k X • (b k : E))
      = ∑ k, ∑ i, ∑ j, (c i j k * X i * X j) • (b k : E) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold sqCoords_affine
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_smul]
  unfold coordVec_affine
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, hper]
  rw [hswap, ← hR]

/-- Mirror of `CoordinatizationToolkit.coordVec_eq_zero` (proof verbatim): coordinates are
faithful. Feeds the §7 `h_inj` binder.

## References

* `BridgeToFixedPoint.CoordinatizationToolkit`,
  `CoordinatizationToolkit.coordVec_eq_zero`
  (`CoordinatizationToolkit.lean`).
* `Mathlib/LinearAlgebra/LinearIndependent/Defs.lean`,
  `Fintype.linearIndependent_iff` (transitively imported; usage-verified in
  `CoordinatizationToolkit.coordVec_eq_zero`).
* `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`,
  `LinearIndependent.map'` (transitively imported).
* `Mathlib/Algebra/Module/Submodule/Ker.lean`, `Submodule.ker_subtype`
  (transitively imported). -/
theorem coordVec_eq_zero_affine (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [Module K E] {V : Submodule K E} {n : ℕ}
    (b : Module.Basis (Fin n) K V) (X : Fin n → K)
    (h : coordVec_affine K E b X = 0) : X = 0 := by
  have hindep : LinearIndependent K (V.subtype ∘ b) :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hsum : ∑ i, X i • (V.subtype ∘ b) i = 0 := h
  have hX : ∀ i, X i = 0 := Fintype.linearIndependent_iff.mp hindep X hsum
  funext i
  exact hX i

/-- Local mirror of `absNilpotent` (`N(V) = {y ∈ V | y² = 0}`,
`IsAbsNilpotent` unfolded inline), cited by name and never imported:
`Preliminaries` is outside the transitive import closure, so the two-line def
is mirrored (transfer to the original is by definitional unfolding).

## References

* `EvolutionAlgebras.Section_2_Preliminaries.A_Preliminaries`, `EvolutionAlgebras.absNilpotent`
  (`A_Preliminaries.lean`), `EvolutionAlgebras.IsAbsNilpotent`
  (`A_Preliminaries.lean`). -/
def absNilpotent_affine (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [Module K E] (V : Submodule K E) : Set E :=
  {x | x ∈ V ∧ x * x = 0}

/-- Mirror of `CoordinatizationToolkit.eq_zero_of_mem_sq_eq_zero` (proof verbatim) over the
local `N(V)` mirror. Feeds the §7 `h_nil` binder at `P := (· ∈ V)`.

## References

* `BridgeToFixedPoint.CoordinatizationToolkit`,
  `CoordinatizationToolkit.eq_zero_of_mem_sq_eq_zero`
  (`CoordinatizationToolkit.lean`).
* This module, `absNilpotent_affine` (proved above). -/
theorem eq_zero_of_mem_sq_eq_zero_affine (K E : Type*) [Field K]
    [NonUnitalNonAssocRing E] [Module K E] (V : Submodule K E)
    (hN : absNilpotent_affine K E V = {0}) {x : E} (hx : x ∈ V) (hxx : x * x = 0) :
    x = 0 := by
  have hmem : x ∈ absNilpotent_affine K E V := ⟨hx, hxx⟩
  rw [hN] at hmem
  exact Set.mem_singleton_iff.mp hmem

/-- The §7 `h_zero_smul` binder, closed at the reuse spine (`zero_smul` by
instance).

## References

* `Mathlib/Algebra/GroupWithZero/Action/Defs.lean`, `zero_smul` (transitively imported;
  `#check`-probed under the §7 import closure). -/
theorem h_zero_smul_affine (K E : Type*) [Field K] [NonUnitalNonAssocRing E]
    [Module K E] (e : E) : (0 : K) • e = 0 :=
  zero_smul K e

/-- `BasePointFree` for the mkSystem family from algebra data (unshifted):
(ii) closed — the §7 reuse binders are exactly the mirrored `CoordinatizationToolkit`
conclusions at `v := coordVec_affine`, `w := coe ∘ b`, `P := (· ∈ V)`.

`(V, b, hexp, hN, htower, hcomm)`.

## References

* This module, `basePointFree_familyForms_affine`,
  `coordVec_mem_affine`,
  `sq_expand_affine`,
  `h_zero_smul_affine`,
  `eq_zero_of_mem_sq_eq_zero_affine`,
  `coordVec_eq_zero_affine` (proved above). -/
theorem basePointFree_familyForms_of_algebraData (m : ℕ) (K : Type*) [Field K]
    (c : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) → K)
    (E : Type*) [NonUnitalNonAssocRing E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin (m + 1)) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent_affine K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    BasePointFree m K (familyForms_affine m K c) := by
  refine basePointFree_familyForms_affine m K c E (coordVec_affine K E b)
    (fun k => (b k : E)) (fun x => x ∈ V) ?_ ?_ ?_ ?_ ?_
  · intro X; exact coordVec_mem_affine K E b X
  · intro X; exact sq_expand_affine K E b c hexp X htower hcomm
  · intro e; exact h_zero_smul_affine K E e
  · intro x hx hxx; exact eq_zero_of_mem_sq_eq_zero_affine K E V hN hx hxx
  · intro X h; exact coordVec_eq_zero_affine K E b X h

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ### §8d (iii) shift mirrors + binder transport, and hF -/

/-- Mirror of `FixedPointFromBezout.statementIndex` (`n − 1`), cited by name
and never imported (see the §8 header's DAG note).

## References

* `BridgeToFixedPoint.FixedPointFromBezout`, `statementIndex`
  (`FixedPointFromBezout.lean`).
* `BridgeToFixedPoint.MkSystemBridge`,
  `MkSystemBridge.statementIndex`
  (`MkSystemBridge.lean`) (same body). -/
def statementIndex_affine (n : ℕ) : ℕ := n - 1

/-- The shift cancels for `0 < n` (mirror body, same proof).

## References

* `BridgeToFixedPoint.FixedPointFromBezout`, `shift_add_one`
  (`FixedPointFromBezout.lean`). -/
theorem shift_add_one_affine (n : ℕ) (hn : 0 < n) :
    statementIndex_affine n + 1 = n :=
  Nat.sub_add_cancel hn

/-- Mirror of `FixedPointFromBezout.shiftEquiv`, cited by name and never
imported.

## References

* `BridgeToFixedPoint.FixedPointFromBezout`, `shiftEquiv`
  (`FixedPointFromBezout.lean`). -/
def shiftEquiv_affine (n : ℕ) (hn : 0 < n) :
    Fin (statementIndex_affine n + 1) ≃ Fin n :=
  finCongr (shift_add_one_affine n hn)

/-- Mirror of `FixedPointFromBezout.shiftConsts`, cited by name and never
imported.

## References

* `BridgeToFixedPoint.FixedPointFromBezout`, `shiftConsts`
  (`FixedPointFromBezout.lean`).
* `BridgeToFixedPoint.MkSystemBridge`, `MkSystemBridge.shiftConsts`
  (`MkSystemBridge.lean`) (same body). -/
noncomputable def shiftConsts_affine (n : ℕ) (K : Type*) [Field K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    Fin (statementIndex_affine n + 1) → Fin (statementIndex_affine n + 1)
      → Fin (statementIndex_affine n + 1) → K :=
  fun i j k => c0 (shiftEquiv_affine n hn i) (shiftEquiv_affine n hn j)
    (shiftEquiv_affine n hn k)

/-- Mirror of `FixedPointFromBezout.sqCoords_shift` (proof verbatim):
`sqCoords` is invariant under reindexing structure constants along an
equivalence.

## References

* `BridgeToFixedPoint.FixedPointFromBezout`, `sqCoords_shift`
  (`FixedPointFromBezout.lean`).
* `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`,
  `Equiv.sum_comp` (`to_additive` of `Equiv.prod_comp`; transitively
  imported; usage-verified in `FixedPointFromBezout.sqCoords_shift`). -/
theorem sqCoords_shift_affine (M n : ℕ) (K : Type*) [Field K] (e : Fin M ≃ Fin n)
    (c : Fin n → Fin n → Fin n → K)
    (X' : Fin M → K) (X : Fin n → K) (i : Fin M)
    (hX : ∀ j, X' j = X (e j)) :
    sqCoords_affine K (fun p q r => c (e p) (e q) (e r)) i X'
      = sqCoords_affine K c (e i) X := by
  unfold sqCoords_affine
  change (∑ p, ∑ q, c (e p) (e q) (e i) * X' p * X' q)
      = ∑ p', ∑ q', c p' q' (e i) * X p' * X q'
  have inner : ∀ p : Fin M,
      (∑ q, c (e p) (e q) (e i) * X (e p) * X (e q))
        = ∑ q', c (e p) q' (e i) * X (e p) * X q' :=
    fun p => Equiv.sum_comp e
      (fun q' : Fin n => c (e p) q' (e i) * X (e p) * X q')
  simp_rw [hX, inner]
  exact Equiv.sum_comp e
    (fun p' : Fin n => ∑ q', c p' q' (e i) * X p' * X q')

/-- Reindexing of coordinate vectors along an equiv (the shift-transport
input at the abstract-reuse level): `X'` on `Fin M` becomes `X' ∘ e.symm`
on `Fin n`. Spec: `reindexVec_apply_affine`.

## References

* This module, `reindexVec_apply_affine` (proved below). -/
def reindexVec_affine (K : Type*) [Field K] {n M : ℕ} (e : Fin M ≃ Fin n)
    (X' : Fin M → K) : Fin n → K :=
  fun j => X' (e.symm j)

/-- Reindexed vectors agree on equiv images.

## References

* `Mathlib/Logic/Equiv/Defs.lean`, `Equiv.symm_apply_apply` (`@[simp]`; transitively
  imported). -/
theorem reindexVec_apply_affine (K : Type*) [Field K] {n M : ℕ}
    (e : Fin M ≃ Fin n) (X' : Fin M → K) (i : Fin M) :
    reindexVec_affine K e X' (e i) = X' i := by
  simp [reindexVec_affine, Equiv.symm_apply_apply]

/-- The §7 `h_expand` binder transports across the shift at the abstract
`(v, w)` level (via `sqCoords_shift_affine` + `Equiv.sum_comp`).

## References

* This module, `sqCoords_shift_affine`,
  `reindexVec_apply_affine` (proved above).
* `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`,
  `Equiv.sum_comp` (transitively imported; see `sqCoords_shift_affine`). -/
theorem h_expand_shift_affine {n M : ℕ} {K E : Type*} [Field K]
    [AddCommMonoid E] [Mul E] [SMul K E]
    (e : Fin M ≃ Fin n) (c0 : Fin n → Fin n → Fin n → K)
    (v : (Fin n → K) → E) (w : Fin n → E)
    (h_expand : ∀ X : Fin n → K,
      v X * v X = ∑ k, (sqCoords_affine K c0 k X) • w k)
    (X' : Fin M → K) :
    v (reindexVec_affine K e X') * v (reindexVec_affine K e X')
      = ∑ k, (sqCoords_affine K (fun p q r => c0 (e p) (e q) (e r)) k X')
        • w (e k) := by
  rw [h_expand (reindexVec_affine K e X')]
  have hX : ∀ j, X' j = reindexVec_affine K e X' (e j) :=
    fun j => (reindexVec_apply_affine K e X' j).symm
  have hterm : ∀ k : Fin M,
      sqCoords_affine K (fun p q r => c0 (e p) (e q) (e r)) k X'
        = sqCoords_affine K c0 (e k) (reindexVec_affine K e X') :=
    fun k => sqCoords_shift_affine M n K e c0 X' _ k hX
  simp_rw [hterm]
  exact (Equiv.sum_comp e
    (fun j => (sqCoords_affine K c0 j (reindexVec_affine K e X')) • w j)).symm

/-- The §7 `h_inj` binder transports across the shift at the abstract `v`
level: from `v (reindex X') = 0`, `h_inj` gives `reindex X' = 0`, and
`reindexVec_apply_affine` at each `e i` forces every coordinate of `X'`
to `0` (`funext`).

## References

* This module, `reindexVec_affine`,
  `reindexVec_apply_affine` (proved above). -/
theorem h_inj_shift_affine {n M : ℕ} {K E : Type*} [Field K]
    [AddCommMonoid E] [Mul E] [SMul K E]
    (e : Fin M ≃ Fin n) (v : (Fin n → K) → E)
    (h_inj : ∀ X : Fin n → K, v X = 0 → X = 0)
    (X' : Fin M → K) (h : v (reindexVec_affine K e X') = 0) :
    X' = 0 := by
  have hX0 : reindexVec_affine K e X' = 0 := h_inj _ h
  funext i
  have hi := congrFun hX0 (e i)
  have hrw : reindexVec_affine K e X' (e i) = X' i :=
    reindexVec_apply_affine K e X' i
  rw [hrw] at hi
  simpa using hi

/-- hF at the shifted family, closed (instances
`familyForms_affine_homogeneous`): the verbatim shape of
`MkSystemBridge.bridgeForms_homogeneous` /
`FixedPointFromBezout.bridgeForms_homogeneous` at the mirror level, so no
`FixedPointFromBezout.lean` append is needed for hF (that file already
proves `bridgeForms_homogeneous`).

## References

* This module, `familyForms_affine_homogeneous` (proved above, §7).
* `BridgeToFixedPoint.MkSystemBridge`,
  `MkSystemBridge.bridgeForms_homogeneous`
  (`MkSystemBridge.lean`, proved).
* `BridgeToFixedPoint.FixedPointFromBezout`,
  `bridgeForms_homogeneous`
  (`FixedPointFromBezout.lean`, proved). -/
theorem shiftedFamily_homogeneous (n : ℕ) (K : Type*) [Field K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n) :
    ∀ i, ((familyForms_affine (statementIndex_affine n) K
      (shiftConsts_affine n K c0 hn)) i).IsHomogeneous 2 :=
  familyForms_affine_homogeneous _ _ _

/-! ### §8e hfin end-to-end at the shifted family -/

/-- Affine finiteness at the shifted mkSystem family from algebra data:
the §7 hPDT binder is discharged via §8b, the §7 reuse binders via the
§8c mirrors transported across the shift (§8d), and hF via
`shiftedFamily_homogeneous` (used inside the §8b step).

Conditional on exactly `[hCurveMeet]` given consumer algebra data
`(V, b, hexp, hN, htower, hcomm)` + `[IsAlgClosed K]`. `hCurveMeet` is the
verbatim conclusion shape of proved-unconditional
`CurveMeet.meetsInfinity_of_isHomogeneous` (needs `[IsAlgClosed K]` at
its site); everything else is proved in-file. The remaining projective
step (`MkSystemChart.locus_finite_of_bpf_affine`, proved) and the
`FixedPointFromBezout` hfin-hypothesis wiring (import-capable site) are
out of scope for this file.

## References

* This module, `meetsInfinity_familyForms_affine_of_curveMeet`,
  `bpf_of_hN_affine`,
  `coordVec_mem_affine`,
  `sq_expand_affine`,
  `h_zero_smul_affine`,
  `eq_zero_of_mem_sq_eq_zero_affine`,
  `coordVec_eq_zero_affine`,
  `h_expand_shift_affine`,
  `h_inj_shift_affine`,
  `eval_mkQuadForm_affine`,
  `affineZero_finite_of_meetsInfinity_of_coordBPF` (proved above).
* `Geometry.MkSystemChart`, `locus_finite_of_bpf_affine`
  (proved projective→affine consumer). -/
theorem affineZero_finite_shiftedFamily_of_algebraData
    (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (c0 : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (E : Type*) [NonUnitalNonAssocRing E] [Module K E]
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c0 i j k • (b k : E))
    (hN : absNilpotent_affine K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hCurveMeet : ∀ (F : Fin (statementIndex_affine n + 1) →
        MvPolynomial (Fin (statementIndex_affine n + 1)) K),
      (∀ i, (F i).IsHomogeneous 2)
        → MeetsInfinity_curve_affine (statementIndex_affine n) K F) :
    (affineZero (statementIndex_affine n) K
      (familyForms_affine (statementIndex_affine n) K
        (shiftConsts_affine n K c0 hn))).Finite := by
  have hPDT : MeetsInfinity (statementIndex_affine n) K
      (familyForms_affine (statementIndex_affine n) K
        (shiftConsts_affine n K c0 hn)) :=
    meetsInfinity_familyForms_affine_of_curveMeet _ K _ hCurveMeet
  have h_expand : ∀ X : Fin n → K,
      coordVec_affine K E b X * coordVec_affine K E b X
        = ∑ k, (sqCoords_affine K c0 k X) • (b k : E) :=
    fun X => sq_expand_affine K E b c0 hexp X htower hcomm
  have h_inj : ∀ X : Fin n → K, coordVec_affine K E b X = 0 → X = 0 :=
    fun X h => coordVec_eq_zero_affine K E b X h
  have hcoord : ∀ X' : Fin (statementIndex_affine n + 1) → K,
      (∀ k, sqCoords_affine K (shiftConsts_affine n K c0 hn) k X' = 0)
        → X' = 0 := by
    have hcore := bpf_of_hN_affine (shiftConsts_affine n K c0 hn)
      (fun X' => coordVec_affine K E b
        (reindexVec_affine K (shiftEquiv_affine n hn) X'))
      (fun k => ((b (shiftEquiv_affine n hn k)) : E)) (fun x => x ∈ V)
      (fun X' => coordVec_mem_affine K E b _)
      (fun X' => h_expand_shift_affine (shiftEquiv_affine n hn) c0
        (coordVec_affine K E b) (fun k => (b k : E)) h_expand X')
      (fun e => h_zero_smul_affine K E e)
      (fun hx hxx => eq_zero_of_mem_sq_eq_zero_affine K E V hN hx hxx)
      (fun X' h0 => h_inj_shift_affine (shiftEquiv_affine n hn)
        (coordVec_affine K E b) h_inj X' h0)
    exact hcore
  have hbridge : ∀ (k : Fin (statementIndex_affine n + 1))
      (X' : Fin (statementIndex_affine n + 1) → K),
      MvPolynomial.eval X'
          ((familyForms_affine (statementIndex_affine n) K
            (shiftConsts_affine n K c0 hn)) k)
        = sqCoords_affine K (shiftConsts_affine n K c0 hn) k X' :=
    fun k X' => eval_mkQuadForm_affine _ K _ k X'
  exact affineZero_finite_of_meetsInfinity_of_coordBPF (statementIndex_affine n) K
    (familyForms_affine (statementIndex_affine n) K
      (shiftConsts_affine n K c0 hn)) hPDT
    (fun k X' => sqCoords_affine K (shiftConsts_affine n K c0 hn) k X')
    hcoord hbridge

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
