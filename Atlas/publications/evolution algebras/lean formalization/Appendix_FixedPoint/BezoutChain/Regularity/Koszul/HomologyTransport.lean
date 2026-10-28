/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SelfDuality
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AugmentedConeStep
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.ReducedMasters
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Homology transport for the Koszul shift iso (R-D3 bridge, part 2)

Step A5 (part 2, bridge half) of the scoped Koszul/AB plan (A1–A6): turn an isomorphism
of cochain complexes `Hom(K, R) ≅ S` plus exactness of the shift side `S`
into the chain-level Hom-exactness that §13 of `SelfDuality.lean`
(`koszulHomCocycleExactBelow`, `koszulHomZeroExact`) consumes. §13's master
`koszulExt_subsingleton_below_of_homExact` then yields `Ext^i(X, Y)`
subsingletons for `i < d` — the exact shape A6 Rees assembly
(`ModuleCat.exists_isRegular_tfae` condition (2)) consumes.

## Probe result: yes, the transport core exists in Mathlib (no gap)

Mathlib `v4.34.0` already contains iso-induced exactness transport:

* `HomologicalComplex.ExactAt.of_iso` (`ShortComplex/HomologicalComplex.lean`):
  `K.ExactAt i → (K ≅ L) → L.ExactAt i` — needs no homology instances.
* `HomologicalComplex.homologyMapIso` : `(K ≅ L) → (i) →
  K.homology i ≅ L.homology i` — the homology-level transport.
* `exactAt_iff_of_quasiIsoAt` (`QuasiIso.lean`): `[QuasiIsoAt f i] →
  (K.ExactAt i ↔ L.ExactAt i)`, with `quasiIsoAt_of_isIso`  and
  `QuasiIso.quasiIsoAt` (instance) feeding it from iso/quasi-iso inputs
  (surveyed alternative; the `of_iso` route above was chosen since it
  needs no homology instances).
* `ShortComplex.moduleCat_exact_iff` (`ShortComplex/ModuleCat.lean`):
  `S.Exact ↔ ∀ x₂, S.g x₂ = 0 → ∃ x₁, S.f x₁ = x₂` — elementwise
  exactness over `ModuleCat R` (via the `PreservesHomology` instance and `exact_iff_of_hasForget` in
  `ConcreteCategory.lean`).
* `HomologicalComplex.exactAt_iff'` : `K.ExactAt j ↔
  (K.sc' i j k).Exact` given `prev`/`next` equations — avoids unfolding
  the choice-based `ComplexShape.next`/`prev` (`ComplexShape.lean`).

So this file is a verified assembly in the exact §13 shape, not new
homological algebra: generic transport (§2), the `ExactAt`-to-`∀∃` bridge
for `koszulDualComplex` (§3), and the §13-shaped masters (§4).

## Contents

* (§1) Probe ledger (this docstring + `References` below): names with
  file:line for every Mathlib lemma consumed.
* (§2) `iso_exactAt_iff`, `iso_isZero_homology_iff`: iso of complexes
  transports exactness / homology-vanishing, both directions.
* (§3) `dualExactAt_cocycle_succ`, `dualExactAt_zero`: `ExactAt` of
  `koszulDualComplex φ` implies the chain-level cocycle/coboundary
  statements (for `Y = ModuleCat.of R R`), via `exactAt_iff'` at
  `sc'` + `moduleCat_exact_iff` + `ofHom`/`dualMap` unfolding.
* (§4) `koszulHomCocycleExactBelow_of_iso`,
  `koszulHomZeroExact_of_iso`, `koszulHomBridge_of_iso` (+ sequence
  forms): the §13 residuals from `(e, hS, hS0)`.

## Residual ledger (explicit hypotheses, nothing assumed)

(a) `e : koszulDualComplex φ ≅ S` — the shift iso over the base ring.
Per lane protocol this file builds only on the §1–13 API and takes `e`
over an abstract `S` (never naming §14+ declarations). Compatibility
the sibling CommRing iso
`koszulShiftIsoSigned_commRing` (`SelfDuality.lean`, sequence
form) has exactly this shape with
`S := koszulShiftComplex_commRing R M m φ` (a
`CochainComplex (ModuleCat R) ℕ`), so it instantiates `e` directly.
(b) `hS` / `hS0` — exactness of `S` below `d` / at `0`: the R2 content
(`H^i(S) = H_{m-i}(K) = 0` for `m - i ≥ 1`), discharged in A4
series once R2 exactness of `K(sop)` over `R_P` proves. Not proved here.
(c) `Y`-scope: `Y = ModuleCat.of R R` (the A6 instantiation `Y := R_P`
over `R := R_P`). General-`Y` Hom-exactness would need flatness and is
out of scope; §13's master is consumed at `Y = R_P` only.

## References

Project (read-only): `Regularity/Koszul/SelfDuality.lean` (§2 `koszulDualComplex`
`koszulDualComplex_d`, `koszulDualMor_succ`;
§13 `koszulHomCocycleExactBelow`, `koszulHomZeroExact`),
`Regularity/Koszul/KoszulComplex.lean` (`koszulContract`,
`koszulCMor_succ`, `koszulChainComplex`,
`koszulChainComplex_d`, `koszulContractOfSequence`).

Mathlib (`lean-toolchain` pins `v4.34.0`):
* `Algebra/Homology/ShortComplex/HomologicalComplex.lean`
  (`shortComplexFunctor'` + `obj` simp lemmas)
  (`homologyMapIso`) (`ExactAt.of_iso`)
  (`exactAt_iff'`).
* `Algebra/Homology/ShortComplex/ModuleCat.lean`
  (`PreservesHomology` instance) (`moduleCat_exact_iff`).
* `Algebra/Homology/QuasiIso.lean` (`quasiIsoAt_of_isIso`)
  (`exactAt_iff_of_quasiIsoAt`): surveyed alternative route (iso →
  quasi-iso → exactness transfer), not consumed — the `of_iso` route
  needs no homology instances.
* `Algebra/Homology/ComplexShape.lean` (`next_eq'`, `prev_eq'` via
  `to_dual`) (`prev_eq_self` via `to_dual`) (`up_mk`).
* `CategoryTheory/Limits/Shapes/ZeroObjects.lean`
  (`Iso.isZero_iff`).
* `Algebra/Category/ModuleCat/Basic.lean` (`Hom.hom`)
  (`hom_comp`) (`hom_ext`) (`hom_zero`); the
  `ofHom`/`hom` round-trip is closed by `rfl` (`hom_ofHom`
  is defeq).
* `LinearAlgebra/Dual/Defs.lean` (`LinearMap.dualMap_apply'`).

## Status

* §2 generic transport: unconditional.
* §3 `ExactAt`-to-`∀∃` bridge: unconditional.
* §4 masters: conditional-exact on `(e, hS)` / `(e, hS0)` (residuals
  (a)+(b) above). R-D3 overall: partial — this file proves the homology
  transport; full discharge needs the sibling iso instantiation + R2.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace HomologyTransport

open CategoryTheory HomologicalComplex KoszulComplex SelfDuality

universe vC uC uI uHT

/-! ## §2. Generic transport: iso of complexes preserves exactness -/

/-- An isomorphism of homological complexes transports exactness at every
degree, in both directions (each direction is `ExactAt.of_iso`, which
needs no homology instances).
-/
theorem iso_exactAt_iff {C : Type uC} [Category.{vC} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type uI}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (e : K ≅ L)
    (i : ι) : K.ExactAt i ↔ L.ExactAt i :=
  ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

/-- An isomorphism of complexes transports homology-vanishing, in both
directions (`homologyMapIso` + `Iso.isZero_iff`). §4 consumes the
exactness form; this records the homology-level transport for A6 use.
-/
theorem iso_isZero_homology_iff {C : Type uC} [Category.{vC} C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {ι : Type uI}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (e : K ≅ L)
    (i : ι) [K.HasHomology i] [L.HasHomology i] :
    CategoryTheory.Limits.IsZero (K.homology i) ↔
      CategoryTheory.Limits.IsZero (L.homology i) :=
  Iso.isZero_iff (homologyMapIso e i)

/-! ## §3. Bridge: `ExactAt` of the dual complex implies §13 cocycle-exactness -/

/-- `prev` of a successor for the cohomology shape (`prev_eq'` with the
witness `Rel j (j + 1)`).
-/
theorem up_prev_succ (j : ℕ) : (ComplexShape.up ℕ).prev (j + 1) = j :=
  ComplexShape.prev_eq' _ (ComplexShape.up_mk j (j + 1) rfl)

/-- `next` of a successor for the cohomology shape.
-/
theorem up_next_succ (j : ℕ) :
    (ComplexShape.up ℕ).next (j + 1) = (j + 1) + 1 :=
  ComplexShape.next_eq' _ (ComplexShape.up_mk (j + 1) ((j + 1) + 1) rfl)

/-- `next` of `0` for the cohomology shape (stated as `0 + 1` so the
`koszulDualMor_succ` rewrite matches syntactically).
-/
theorem up_next_zero : (ComplexShape.up ℕ).next 0 = 0 + 1 :=
  ComplexShape.next_eq' _ (ComplexShape.up_mk 0 (0 + 1) rfl)

/-- `prev` of `0` is `0`: no degree maps into degree `0` (`Rel i 0` would
mean `i + 1 = 0`).
-/
theorem up_prev_zero : (ComplexShape.up ℕ).prev 0 = 0 := by
  apply ComplexShape.prev_eq_self _ 0
  intro hRel
  have hEq : (ComplexShape.up ℕ).prev 0 + 1 = 0 := hRel
  omega

/-- The dual differential is post-composition with the contraction
(`LinearMap.dualMap_apply'` unfolded through `koszulDualD`).
-/
theorem koszulDualD_eq_comp {R M : Type uHT} [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] R) (k : ℕ)
    (g : Module.Dual R ↥(⋀[R]^k M)) :
    koszulDualD φ k g = g.comp (koszulContract φ k) :=
  LinearMap.dualMap_apply' _ _

/-- Positive-degree bridge: `ExactAt` of `koszulDualComplex φ` at `j + 1`
implies every Koszul `(j+1)`-cocycle with `R` coefficients is a
coboundary — the `i = j + 1` clause of `koszulHomCocycleExactBelow`.
Unfolds `ExactAt` at `sc'` (`exactAt_iff'`), applies elementwise
exactness (`moduleCat_exact_iff`), and converts between `ModuleCat`
morphisms and linear maps (`ofHom`/`dualMap`).
-/
theorem dualExactAt_cocycle_succ {R M : Type uHT} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) (j : ℕ)
    (h : (koszulDualComplex φ).ExactAt (j + 1))
    (f : (koszulChainComplex φ).X (j + 1) ⟶ ModuleCat.of R R)
    (m : ℕ) (hm : j + 1 + 1 = m)
    (hf : (koszulChainComplex φ).d m (j + 1) ≫ f = 0) :
    ∃ g : (koszulChainComplex φ).X j ⟶ ModuleCat.of R R,
      (koszulChainComplex φ).d (j + 1) j ≫ g = f := by
  have hprev := up_prev_succ j
  have hnext := up_next_succ j
  rw [HomologicalComplex.exactAt_iff' _ _ _ _ hprev hnext] at h
  rw [ShortComplex.moduleCat_exact_iff _] at h
  -- Only `_f`/`_g` fire here (the `X` projections are bridged by the
  -- `hclean` ascription below, which unfolds them definitionally).
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g,
    koszulDualComplex_d, koszulDualMor_succ] at h
  have hclean : ∀ x₂ : Module.Dual R ↥(⋀[R]^(j + 1) M),
      koszulDualD φ (j + 1) x₂ = 0 →
      ∃ x₁ : Module.Dual R ↥(⋀[R]^j M), koszulDualD φ j x₁ = x₂ := h
  subst hm
  -- Read the cocycle condition at `.hom` level: `congrArg` on the pristine
  -- `≫` (whose implicits are homogeneous), then `.hom` of `d` via `succ`.
  have hcomp : f.hom.comp (koszulContract φ (j + 1)) = 0 := by
    have h0 := congrArg ModuleCat.Hom.hom hf
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h0
    -- `.hom` of `d`: rewrite `d` to `ofHom` form, then `rfl` (the
    -- `ofHom`/`hom` round-trip is definitional; `rw [hom_ofHom]` cannot
    -- fire here since the rewritten subterm keeps stale `X` implicits).
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
    have e := koszulDualD_eq_comp φ (j + 1) f.hom
    rw [e]
    exact hcomp
  obtain ⟨x₁, hx₁⟩ := hclean f.hom hcoc
  -- The witness as a let-bound morphism keeps the `≫` implicits
  -- homogeneous (an inline `ofHom x₁` would poison them for `rw`).
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
  exact (koszulDualD_eq_comp φ j x₁).symm.trans hx₁

/-- Degree-0 bridge: `ExactAt` of `koszulDualComplex φ` at `0` implies
every `0`-cocycle with `R` coefficients is zero — `koszulHomZeroExact`.
At degree `0` the incoming differential of `sc'` is `d 0 0 = 0`, so the
coboundary witness forces the cocycle to vanish.
-/
theorem dualExactAt_zero {R M : Type uHT} [CommRing R] [AddCommGroup M]
    [Module R M] (φ : M →ₗ[R] R)
    (h : (koszulDualComplex φ).ExactAt 0)
    (f : (koszulChainComplex φ).X 0 ⟶ ModuleCat.of R R)
    (hf : (koszulChainComplex φ).d 1 0 ≫ f = 0) : f = 0 := by
  have hprev := up_prev_zero
  have hnext := up_next_zero
  rw [HomologicalComplex.exactAt_iff' _ _ _ _ hprev hnext] at h
  rw [ShortComplex.moduleCat_exact_iff _] at h
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g,
    koszulDualComplex_d, koszulDualMor_succ] at h
  have hd00 : (koszulDualComplex φ).d 0 0 = 0 := by
    rw [koszulDualComplex_d]
    unfold koszulDualMor
    exact dite_eq_right (by omega)
  -- Fold back to `.d` form first: after the `simp only`, the `f`-side is
  -- in `koszulDualMor` form, which `hd00` (stated via `.d`) cannot match.
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
    have e := koszulDualD_eq_comp φ 0 f.hom
    rw [e]
    exact hcomp
  obtain ⟨x₁, hx₁⟩ := hclean f.hom hcoc
  have h0app : (0 : (koszulDualComplex φ).X 0 ⟶
      (koszulDualComplex φ).X 0) x₁ = 0 := rfl
  rw [h0app] at hx₁
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  exact hx₁.symm

/-! ## §4. Masters: the §13 residuals from `(shift iso, shift-side exactness)` -/

/-- Positive-degree master: the shift iso `e` transports shift-side
exactness `hS` to `ExactAt` of the dual (§2), and §3 turns that into
`koszulHomCocycleExactBelow` — in the exact shape §13 consumes, at
`Y = ModuleCat.of R R` (the A6 instantiation).

Conditional on exactly `(e, hS)` (residuals (a)+(b)). -/
theorem koszulHomCocycleExactBelow_of_iso {R M : Type uHT} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) {d : ℕ}
    {S : CochainComplex (ModuleCat.{uHT} R) ℕ}
    (e : koszulDualComplex φ ≅ S)
    (hS : ∀ i : ℕ, 1 ≤ i → i < d → S.ExactAt i) :
    koszulHomCocycleExactBelow φ (Y := ModuleCat.of R R) d := by
  intro i hi1 hid f m hm hf p hp
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  -- Orient so `subst` eliminates `p` (RHS var), keeping `j`.
  have hpj : j = p := by omega
  subst hpj
  have hdual : (koszulDualComplex φ).ExactAt (j + 1) :=
    (iso_exactAt_iff e (j + 1)).mpr (hS (j + 1) (by omega) hid)
  exact dualExactAt_cocycle_succ φ j hdual f m hm hf

/-- Degree-0 master: `koszulHomZeroExact` from the shift iso plus
exactness of `S` at `0` (the `H_d(K) = 0` top-degree content).

Conditional on exactly `(e, hS0)` (residuals (a)+(b)). -/
theorem koszulHomZeroExact_of_iso {R M : Type uHT} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)
    {S : CochainComplex (ModuleCat.{uHT} R) ℕ}
    (e : koszulDualComplex φ ≅ S) (hS0 : S.ExactAt 0) :
    koszulHomZeroExact φ (Y := ModuleCat.of R R) := by
  intro f hf
  have hdual : (koszulDualComplex φ).ExactAt 0 :=
    (iso_exactAt_iff e 0).mpr hS0
  exact dualExactAt_zero φ hdual f hf

/-- Combined bridge: both §13 residuals from one iso plus shift-side
exactness below `d` and at `0`.

Conditional on exactly `(e, hS, hS0)` (residuals (a)+(b)). -/
theorem koszulHomBridge_of_iso {R M : Type uHT} [CommRing R]
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) {d : ℕ}
    {S : CochainComplex (ModuleCat.{uHT} R) ℕ}
    (e : koszulDualComplex φ ≅ S)
    (hS : ∀ i : ℕ, 1 ≤ i → i < d → S.ExactAt i)
    (hS0 : S.ExactAt 0) :
    koszulHomCocycleExactBelow φ (Y := ModuleCat.of R R) d ∧
      koszulHomZeroExact φ (Y := ModuleCat.of R R) :=
  ⟨koszulHomCocycleExactBelow_of_iso φ e hS,
    koszulHomZeroExact_of_iso φ e hS0⟩

/-- Sequence form of the positive-degree master: `K(x)` for `x : Fin n → R`
(the `K(sop)` shape), otherwise identical to
`koszulHomCocycleExactBelow_of_iso`.

Conditional on exactly `(e, hS)` (residuals (a)+(b)). -/
theorem koszulHomCocycleExactBelow_ofSequence_of_iso {R : Type uHT}
    [CommRing R] {n d : ℕ} (x : Fin n → R)
    {S : CochainComplex (ModuleCat.{uHT} R) ℕ}
    (e : koszulDualComplex (koszulContractOfSequence x) ≅ S)
    (hS : ∀ i : ℕ, 1 ≤ i → i < d → S.ExactAt i) :
    koszulHomCocycleExactBelow (koszulContractOfSequence x)
      (Y := ModuleCat.of R R) d :=
  koszulHomCocycleExactBelow_of_iso (koszulContractOfSequence x) e hS

/-- Sequence form of the degree-0 master.

Conditional on exactly `(e, hS0)` (residuals (a)+(b)). -/
theorem koszulHomZeroExact_ofSequence_of_iso {R : Type uHT} [CommRing R]
    {n : ℕ} (x : Fin n → R)
    {S : CochainComplex (ModuleCat.{uHT} R) ℕ}
    (e : koszulDualComplex (koszulContractOfSequence x) ≅ S)
    (hS0 : S.ExactAt 0) :
    koszulHomZeroExact (koszulContractOfSequence x)
      (Y := ModuleCat.of R R) :=
  koszulHomZeroExact_of_iso (koszulContractOfSequence x) e hS0

/-- Sequence form of the combined bridge.

Conditional on exactly `(e, hS, hS0)` (residuals (a)+(b)). -/
theorem koszulHomBridge_ofSequence_of_iso {R : Type uHT} [CommRing R]
    {n d : ℕ} (x : Fin n → R)
    {S : CochainComplex (ModuleCat.{uHT} R) ℕ}
    (e : koszulDualComplex (koszulContractOfSequence x) ≅ S)
    (hS : ∀ i : ℕ, 1 ≤ i → i < d → S.ExactAt i)
    (hS0 : S.ExactAt 0) :
    koszulHomCocycleExactBelow (koszulContractOfSequence x)
        (Y := ModuleCat.of R R) d ∧
      koszulHomZeroExact (koszulContractOfSequence x)
        (Y := ModuleCat.of R R) :=
  koszulHomBridge_of_iso (koszulContractOfSequence x) e hS hS0

/-! ## §5. Shift-side chase toolkit: `eqToHom`/cast computation lemmas

The shift complex `koszulShiftComplex_commRing` (§14b of `SelfDuality.lean`)
has `if`-split objects, so its differentials are `eqToHom`-conjugated
transported contractions (`koszulShiftAt_commRing`). §6's exactness chase
needs these applied to elements; each lemma below pins one computation.
All are `rfl`/`cases`-level facts (no homology).
-/

/-- Applying the shift differential: `eqToHom` conjugation unfolds to nested
application (`rfl`: `≫`/`ofHom` application plus the `rfl`-transport).
-/
theorem shiftAt_apply {R : Type uHT} [CommRing R] {M : Type uHT}
    [AddCommGroup M] [Module R M] {m i : ℕ} {φ : M →ₗ[R] R} {hle : i + 1 ≤ m}
    (e1 : koszulShiftObj_commRing R M m i = ModuleCat.of R ↥(⋀[R]^(m - i) M))
    (e2 : koszulShiftObj_commRing R M m (i + 1)
      = ModuleCat.of R ↥(⋀[R]^(m - (i + 1)) M))
    (x : ↥(koszulShiftObj_commRing R M m i)) :
    koszulShiftAt_commRing R M m φ i (i + 1) rfl hle x =
      eqToHom e2.symm
        ((koszulShiftD_commRing R M m i φ hle) (eqToHom e1 x)) := rfl

/-- `eqToHom` round trip at application level (`inv_hom_apply` at `eqToIso`,
Mathlib `ModuleCat/Basic.lean` + `EqToHom.lean`).
-/
theorem eqToHom_inv_hom_apply {R : Type uHT} [CommRing R]
    {A B : ModuleCat.{uHT} R} (e : A = B) (x : ↥A) :
    eqToHom e.symm (eqToHom e x) = x := by
  have h := ModuleCat.inv_hom_apply (eqToIso e) x
  simpa using h

/-- `eqToHom` round trip, other direction (`hom_inv_apply`).
-/
theorem eqToHom_hom_inv_apply {R : Type uHT} [CommRing R]
    {A B : ModuleCat.{uHT} R} (e : A = B) (x : ↥B) :
    eqToHom e (eqToHom e.symm x) = x := by
  have h := ModuleCat.hom_inv_apply (eqToIso e) x
  simpa using h

/-- Exterior-power cast round trip (`cases`-level, mirrors the
`koszulShiftD_apply_aux_commRing` proof pattern).
-/
theorem exteriorCast_roundtrip {R : Type uHT} [CommRing R] {M : Type uHT}
    [AddCommGroup M] [Module R M] {a b : ℕ} (e1 : a = b) (e2 : b = a)
    (y : ↥(⋀[R]^b M)) :
    (e1 ▸ ((e2 ▸ y : ↥(⋀[R]^a M))) : ↥(⋀[R]^b M)) = y := by
  cases e1
  cases e2
  rfl

/-- A cast is zero only if the original is zero.
-/
theorem exteriorCast_eq_zero {R : Type uHT} [CommRing R] {M : Type uHT}
    [AddCommGroup M] [Module R M] {a b : ℕ} (e : a = b) (y : ↥(⋀[R]^a M))
    (h : (e ▸ y : ↥(⋀[R]^b M)) = 0) : y = 0 := by
  cases e
  exact h

/-- Casts preserve the underlying exterior element.
-/
theorem exteriorCast_val {R : Type uHT} [CommRing R] {M : Type uHT}
    [AddCommGroup M] [Module R M] {a b : ℕ} (e : a = b) (z : ↥(⋀[R]^a M)) :
    (((e ▸ z : ↥(⋀[R]^b M))) : ExteriorAlgebra R M)
      = (z : ExteriorAlgebra R M) := by
  cases e
  rfl

/-- Contraction commutes with index casts: both sides are `contractLeft` of
the same exterior element (`koszulContract_apply`,
`KoszulComplex.lean`, + `exteriorCast_val`).
-/
theorem koszulContract_cast {R : Type uHT} [CommRing R] {M : Type uHT}
    [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R) {a b : ℕ} (e : a = b)
    (w : ↥(⋀[R]^(a + 1) M)) :
    koszulContract φ b ((congrArg (· + 1) e) ▸ w)
      = (e ▸ koszulContract φ a w) := by
  apply Subtype.ext
  show (((koszulContract φ b _) : ↥(⋀[R]^b M)) : ExteriorAlgebra R M) = _
  rw [koszulContract_apply]
  rw [exteriorCast_val]
  rw [exteriorCast_val]
  rw [koszulContract_apply]

/-! ## §6. Shift exactness from `contractExactAt` (generic R2-consumption)

`H^i(S) = H_{m-i}(K)`: at degree `i = t+1` (in range) the shift short
complex is `⋀^{j+2} → ⋀^{j+1} → ⋀^j` with `j = m-(i+1)`, so
`contractExactAt φ j` (`AugmentedConeStep.lean`) is exactly its elementwise
exactness (`moduleCat_exact_iff`), modulo the §5 computations. At degree
`0` the incoming map is `0`, so exactness is injectivity of the top
contraction — from `contractExactAt φ (m-1)` plus vanishing of `⋀^{m+1}`.
-/

/-- Positive-degree shift exactness from one `contractExactAt` instance at
the countdown index `m - (i+1)`.
-/
theorem shiftExactAt_of_contractExact {R : Type uHT} [CommRing R]
    {M : Type uHT} [AddCommGroup M] [Module R M] {m : ℕ} (φ : M →ₗ[R] R)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i + 1 ≤ m)
    (hexact : AugmentedConeStep.contractExactAt φ (m - (i + 1))) :
    (koszulShiftComplex_commRing R M m φ).ExactAt i := by
  obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
  have hle1 : t + 1 ≤ m := by omega
  have hle2 : t + 1 + 1 ≤ m := him
  rw [HomologicalComplex.exactAt_iff' _ _ _ _ (up_prev_succ t) (up_next_succ t)]
  rw [ShortComplex.moduleCat_exact_iff]
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f,
    HomologicalComplex.shortComplexFunctor'_obj_g,
    koszulShiftComplex_commRing_d]
  rw [koszulShiftMor_commRing_succ_of_le R M m φ t hle1,
    koszulShiftMor_commRing_succ_of_le R M m φ (t + 1) hle2]
  -- Restate with shift-object types (the `hclean` pattern of §3: `simp`
  -- leaves `sc'`-typed applications that `rw` cannot match).
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
  rw [shiftAt_apply eB eC] at hx₂
  set y₂ : ↥(⋀[R]^(m - (t + 1)) M) := eqToHom eB x₂ with hy₂
  have hD : koszulShiftD_commRing R M m (t + 1) φ hle2 y₂ = 0 := by
    have h0 : eqToHom eC (eqToHom eC.symm
        (koszulShiftD_commRing R M m (t + 1) φ hle2 y₂)) = 0 := by
      rw [hx₂]
      simp
    rwa [eqToHom_hom_inv_apply eC] at h0
  rw [koszulShiftD_apply_commRing] at hD
  obtain ⟨w, hw⟩ := hexact _ hD
  have e' : (m - (t + 1 + 1)) + 1 = m - (t + 1) := by omega
  have e_lo : m - (t + 1) + 1 = m - t :=
    koszulShiftD_index_eq m t hle1
  refine ⟨eqToHom eA.symm (e_lo ▸ ((congrArg (· + 1) e') ▸ w)), ?_⟩
  rw [shiftAt_apply eA eB, eqToHom_hom_inv_apply eA,
    koszulShiftD_apply_commRing]
  have hback : ((((koszulShiftD_index_eq m t hle1).symm ▸
      (e_lo ▸ ((congrArg (· + 1) e') ▸ w)))) : ↥(⋀[R]^(m - (t + 1) + 1) M))
      = ((((congrArg (· + 1) e') ▸ w)) : ↥(⋀[R]^(m - (t + 1) + 1) M)) :=
    exteriorCast_roundtrip _ _ _
  rw [hback, koszulContract_cast φ e' w, hw]
  have hfin : ((e' ▸
      (((koszulShiftD_index_eq m (t + 1) hle2).symm ▸ y₂))) :
      ↥(⋀[R]^(m - (t + 1)) M)) = y₂ :=
    exteriorCast_roundtrip e' _ y₂
  rw [hfin, hy₂]
  exact eqToHom_inv_hom_apply eB x₂

/-- Degree-0 shift exactness: the top contraction is injective, since
`contractExactAt φ (m-1)` exhibits every kernel element as a boundary from
`⋀^{m+1}`, which vanishes (`hsub`). Needs `1 ≤ m` (for `m = 0` the
conclusion is false: all shift differentials vanish while `⋀^0 ≠ 0`).
-/
theorem shiftExactAt_zero_of_contractExact {R : Type uHT} [CommRing R]
    {M : Type uHT} [AddCommGroup M] [Module R M] {m : ℕ} (φ : M →ₗ[R] R)
    (hm1 : 1 ≤ m) (hexact : AugmentedConeStep.contractExactAt φ (m - 1))
    (hsub : Subsingleton ↥(⋀[R]^(m + 1) M)) :
    (koszulShiftComplex_commRing R M m φ).ExactAt 0 := by
  have hle : 0 + 1 ≤ m := hm1
  rw [HomologicalComplex.exactAt_iff' _ _ _ _ up_prev_zero up_next_zero]
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
  rw [shiftAt_apply e0 e1] at hx₂
  set y₂ : ↥(⋀[R]^(m - 0) M) := eqToHom e0 x₂ with hy₂
  have hD : koszulShiftD_commRing R M m 0 φ hle y₂ = 0 := by
    have h0 : eqToHom e1 (eqToHom e1.symm
        (koszulShiftD_commRing R M m 0 φ hle y₂)) = 0 := by
      rw [hx₂]
      simp
    rwa [eqToHom_hom_inv_apply e1] at h0
  rw [koszulShiftD_apply_commRing] at hD
  obtain ⟨w, hw⟩ := hexact _ hD
  have e_sub : ((m - 1) + 1) + 1 = m + 1 := by omega
  have hw0 : w = 0 := by
    have hcast : ((e_sub ▸ w : ↥(⋀[R]^(m + 1) M))) = 0 :=
      Subsingleton.elim _ _
    exact exteriorCast_eq_zero e_sub w hcast
  rw [hw0, map_zero] at hw
  have hy₂0 : y₂ = 0 := by
    have hz : (((((koszulShiftD_index_eq m 0 hle).symm ▸ y₂))) :
        ↥(⋀[R]^(m - (0 + 1) + 1) M)) = 0 := hw.symm
    exact exteriorCast_eq_zero _ _ hz
  have hx₂0 : x₂ = 0 := by
    have h : eqToHom e0.symm (eqToHom e0 x₂) = 0 := by
      rw [← hy₂, hy₂0]
      simp
    rwa [eqToHom_inv_hom_apply e0] at h
  refine ⟨x₂, ?_⟩
  have h0app : (0 : koszulShiftObj_commRing R M m 0 ⟶
      koszulShiftObj_commRing R M m 0) x₂ = 0 := rfl
  rw [h0app, hx₂0]

/-! ## §7. R2 discharge: `hS`/`hS0` from `grlift_r2_exact_reduced`

Instantiates §6 with R2 exactness of `K(sop)` over `R_P`
(`grlift_r2_exact_reduced`, `ReducedMasters.lean`) at `Y = R_P` (the A6
instantiation), producing the `hS`/`hS0` Props in the exact
`koszulHomBridge_of_iso` hypothesis shape. The `⋀^{d+1}`-vanishing for `hS0`
is `exteriorPower_subsingleton_of_gt_commRing` (`SelfDuality.lean`)
at `Pi.basisFun`; the combined bridge uses
`koszulShiftIsoSigned_commRing_ofSequence`  for `e`.
-/

/-- `hS` from R2: shift-side exactness below `d` over `R_P`.

Conditional on exactly `[hker]`. -/
theorem shift_hS_of_r2Reduced {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (GradedSurjection.polySurjResidue P d g hgen) = ⊥) :
    ∀ i : ℕ, 1 ≤ i → i < d →
      (koszulShiftComplex_commRing (Localization.AtPrime P)
        (Fin d → Localization.AtPrime P) d
        (koszulContractOfSequence g)).ExactAt i := by
  intro i hi1 hid
  exact shiftExactAt_of_contractExact _ hi1 (by omega)
    ((ReducedMasters.grlift_r2_exact_reduced P d g hgen hker) _)

/-- `hS0` from R2: shift-side exactness at `0` over `R_P`. The `1 ≤ d`
side condition is necessary (`d = 0` makes the conclusion false, §6).

Conditional on exactly `[hker, 1 ≤ d]`. -/
theorem shift_hS0_of_r2Reduced {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (GradedSurjection.polySurjResidue P d g hgen) = ⊥)
    (hd1 : 1 ≤ d) :
    (koszulShiftComplex_commRing (Localization.AtPrime P)
      (Fin d → Localization.AtPrime P) d
      (koszulContractOfSequence g)).ExactAt 0 :=
  shiftExactAt_zero_of_contractExact _ hd1
    ((ReducedMasters.grlift_r2_exact_reduced P d g hgen hker) _)
    (exteriorPower_subsingleton_of_gt_commRing _ _ d (d + 1)
      (Pi.basisFun (Localization.AtPrime P) (Fin d)) (by omega))

/-- Combined §13 bridge from R2: both Hom-exactness residuals at `Y = R_P`
from the shift iso plus R2 exactness.

Conditional on exactly `[hker, 1 ≤ d]`. -/
theorem koszulHomBridge_of_r2Reduced {K : Type*} [Field K] {m : ℕ}
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (GradedSurjection.polySurjResidue P d g hgen) = ⊥)
    (hd1 : 1 ≤ d) :
    koszulHomCocycleExactBelow (koszulContractOfSequence g)
        (Y := ModuleCat.of (Localization.AtPrime P)
          (Localization.AtPrime P)) d ∧
      koszulHomZeroExact (koszulContractOfSequence g)
        (Y := ModuleCat.of (Localization.AtPrime P)
          (Localization.AtPrime P)) :=
  koszulHomBridge_ofSequence_of_iso g
    (koszulShiftIsoSigned_commRing_ofSequence _ d g)
    (shift_hS_of_r2Reduced P d g hgen hker)
    (shift_hS0_of_r2Reduced P d g hgen hker hd1)

#print axioms shift_hS_of_r2Reduced
#print axioms shift_hS0_of_r2Reduced
#print axioms koszulHomBridge_of_r2Reduced

end HomologyTransport
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
