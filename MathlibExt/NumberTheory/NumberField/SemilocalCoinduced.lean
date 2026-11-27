/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_NumberField_PlaceAbove.lean`,
`Definitions/Def_NumberField_PlaceTransport.lean`,
`Definitions/Def_NumberField_PlaceDecompositionAction.lean`,
`Definitions/Def_NumberField_FiniteSIdeleModule.lean`,
`Definitions/Def_NumberField_ArchimedeanIdeleModule.lean`,
`Definitions/Def_NumberField_InfinitePlaceTransport.lean`,
`Theorems/Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits.lean`,
`Theorems/Thm_NumberField_ArchIdele_exists_addEquiv_coind_localUnits.lean`,
`Theorems/Thm_NumberField_PlaceTransport_transport_one.lean`,
`Theorems/Thm_NumberField_PlaceTransport_transport_trans_transport.lean`,
`Theorems/Thm_NumberField_PlaceTransport_transport_eq_actRingEquiv.lean`,
`Theorems/Thm_NumberField_PlaceTransport_stabilizer_eq_decomp.lean`,
`Theorems/Thm_NumberField_PlaceTransport_under_smul.lean`,
`Theorems/Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq.lean`,
`Theorems/Thm_NumberField_InfinitePlaceTransport_transport_one.lean`,
`Theorems/Thm_NumberField_InfinitePlaceTransport_transport_trans_transport.lean`,
`Theorems/Thm_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv.lean`,
`P2M/Sol/S_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits.lean`,
`P2M/Sol/S_NumberField_ArchIdele_exists_addEquiv_coind_localUnits.lean`,
`P2M/Sol/S_NumberField_PlaceTransport_transport_one.lean`,
`P2M/Sol/S_NumberField_PlaceTransport_transport_trans_transport.lean`,
`P2M/Sol/S_NumberField_PlaceTransport_transport_eq_actRingEquiv.lean`,
`P2M/Sol/S_NumberField_PlaceTransport_stabilizer_eq_decomp.lean`,
`P2M/Sol/S_NumberField_PlaceTransport_under_smul.lean`,
`P2M/Sol/S_NumberField_PlaceTransport_orbit_eq_setOf_under_eq.lean`,
`P2M/Sol/S_NumberField_InfinitePlaceTransport_transport_one.lean`,
`P2M/Sol/S_NumberField_InfinitePlaceTransport_transport_trans_transport.lean`
and
`P2M/Sol/S_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
The source states its results for number fields in `Type`; here they hold for
number fields in any universe `Type u`.
-/

module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Invariant.Basic
import MathlibExt.NumberTheory.Padics.DecompositionSubgroup

/-!
# Semilocal coinduced modules of local units

Let `K / E` be a Galois extension of number fields and `v` a place of `E`. The Galois group
`K ≃ₐ[E] K` permutes the places of `K` above `v`, and an automorphism `σ` with `σ • w = w'`
extends to a ring isomorphism between the completions at `w` and at `w'`. This file constructs
these actions and transports and proves that the representation of the Galois group coinduced
from the decomposition group of a chosen place `w₀` above `v`, acting on the units of the
completion at `w₀`, is additively isomorphic to the product of the units of the completions at
all places above `v`, compatibly with the Galois action. This is the module-level input of
Shapiro's lemma for semilocal units, for finite and for infinite places.

## Main definitions

Finite places (nonzero primes of `𝓞 K`):

* `NumberField.PlaceAbove.above E K v`: a chosen finite place of `K` above `v`.
* `NumberField.PlaceTransport.instMulActionHeightOneSpectrum`: the action of `K ≃ₐ[E] K` on
  finite places, `(σ • w).asIdeal = σ(w.asIdeal)`; equivalently `x ∈ σ • w ↔ σ⁻¹ • x ∈ w`.
* `NumberField.PlaceDecomp.decomp E K w`: the decomposition group of `w`, and
  `NumberField.PlaceDecomp.actRingEquiv`, its action on the completion `w.adicCompletion K`.
* `NumberField.PlaceTransport.transport σ h`: for `h : σ • w = w'`, the ring isomorphism
  `w.adicCompletion K ≃+* w'.adicCompletion K` extending `σ`, with its restrictions
  `transportIntegers`, `transportUnits` and `transportIntegerUnits`.
* `NumberField.FiniteSIdele.D`, `localUnits`, `localIntegerUnits`: the decomposition group of
  the chosen place above `v` and its `ℤ`-representations on the local units and integer units.

Infinite places:

* `NumberField.ArchIdele.above E K v`: a chosen infinite place of `K` above `v`.
* `NumberField.InfPlaceDecomp.decomp E K w`: the stabilizer of `w`, with its action
  `NumberField.InfPlaceDecomp.actRingEquiv` on `w.Completion` and the representation
  `NumberField.InfPlaceDecomp.localUnits` on the local units.
* `NumberField.InfinitePlaceTransport.transport σ h` and `transportUnits`.

## Main results

* `NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits`
* `NumberField.ArchIdele.exists_addEquiv_coind_localUnits`

Each gives an additive equivalence `e` from `Rep.coind` of the local units to
`Additive (Π w, (local units at w))`, the product over the places `w` above `v`, such that the
`w`-component of `e (g • f)` is the transport along `g` of the `w'`-component of `e f`
whenever `g • w' = w`.

## Conventions and scopes

Automorphisms act on places on the left through their inverses: `σ • w` is the prime `σ(w)` for
finite places (scope `NumberField.PlaceTransport`), and Mathlib's `σ • w = w ∘ σ⁻¹` for
infinite places. Every transport is `σ` on the image of `K` (`transport_coe`); at finite places
it preserves valuations (`valued_transport`) and integers (`transportIntegers`). When `σ` fixes
`w`, the transport is the decomposition group action. The actions of decomposition groups on
completions, their integers and unit groups are scoped instances: open
`NumberField.PlaceDecomp` for finite places and `NumberField.InfPlaceDecomp` for infinite places.
The coinduced representation is Mathlib's `Rep.coind`: functions `f` on the Galois group with
`f (d * x) = d • f x` for `d` in the decomposition group, on which `g` acts by
`(g • f) x = f (x * g)`.
-/

@[expose] public section

universe u

open IsDedekindDomain NumberField

namespace NumberField.PlaceAbove

variable (E K : Type*) [Field E] [NumberField E] [Field K] [Algebra E K]

/-- **A finite place above a finite place.** For a field extension `K / E` with `E` a number
field, every finite place `v` of `E` (a nonzero prime of `𝓞 E`) has a nonzero prime `w` of
`𝓞 K` above it: the preimage of `w` in `𝓞 E` is `v`. -/
theorem exists_above (v : HeightOneSpectrum (𝓞 E)) :
    ∃ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 E) (𝓞 K)) := fun x y hxy => by
    apply IsIntegralClosure.algebraMap_injective (𝓞 E) ℤ E
    apply (algebraMap E K).injective
    have := congrArg (algebraMap (𝓞 K) K) hxy
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 E) E K, IsScalarTower.algebraMap_apply (𝓞 E) E K] at this
  have := v.isMaximal
  obtain ⟨W, hWmax, hWv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) v.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  have hW0 : W ≠ ⊥ := by
    rintro rfl
    exact v.ne_bot (by rw [← hWv, Ideal.under_bot])
  exact ⟨⟨W, hWmax.isPrime, hW0⟩, hWv⟩

/-- **Chosen finite place above a finite place.** A choice, made with `Classical.choose`, of a
nonzero prime `w` of `𝓞 K` lying over the finite place `v` of `E` (see `comap_above`). -/
noncomputable def above (v : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 K) := (exists_above E K
  v).choose

/-- **The chosen finite place lies over the given place.** The chosen place `above E K v` lies over
`v`: its prime ideal contracts to `v` in `𝓞 E`. -/
theorem comap_above (v : HeightOneSpectrum (𝓞 E)) :
    (above E K v).asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := (exists_above E K
      v).choose_spec

end NumberField.PlaceAbove

open IsDedekindDomain NumberField
open scoped Pointwise

namespace NumberField.PlaceDecomp

section general
variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Valuation-preserving automorphisms are uniformly continuous.** Let `K` be a field. A ring
automorphism `f` of `K` that preserves a valuation `v`, `v (f x) = v x` for all `x`, is uniformly
continuous as a map `WithVal v → WithVal v`. -/
theorem uniformContinuous_congr_of_forall_eq (v : Valuation K Γ₀) (f : K ≃+* K) (h : ∀ x,
  v (f x) = v x) :
    UniformContinuous (WithVal.congr v v f) := by
  apply uniformContinuous_addMonoidHom_of_continuous
  apply continuous_of_continuousAt_zero (WithVal.congr v v f).toAddMonoidHom
  rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero _ _).tendsto_iff (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  refine ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have key : Valued.v ((WithVal.congr v v f).toAddMonoidHom x) = Valued.v x := by
    change Valued.v (WithVal.congr _ _ _ x) = _
    rw [WithVal.congr_apply, WithVal.valued_toVal, ← WithVal.apply_ofVal]
    exact h _
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rwa [key]

end general

variable (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞
  K))

/-- **Decomposition group of a finite place.** The decomposition group of the finite place `w` of
`K` in `K ≃ₐ[E] K`: the automorphisms that map the valuation subring of `w` onto itself
(`ValuationSubring.decompositionSubgroup`). -/
noncomputable abbrev decomp : Subgroup (K ≃ₐ[E] K) := ((w.valuation
  K).valuationSubring).decompositionSubgroup E

variable {E K w}

-- `K` is algebraic over any subfield `E`, as it is algebraic over `ℚ`.
private theorem isAlgebraic_of_numberField : Algebra.IsAlgebraic E K := by
  have : CharZero E := RingHom.charZero (algebraMap E K)
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) (L := E) (A := K)

/-- **Decomposition group elements are uniformly continuous at a finite place.** An element of the
decomposition group of `w` is uniformly continuous for the `w`-adic uniformity on `K`. -/
theorem uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    UniformContinuous (WithVal.congr (w.valuation K) (w.valuation K) (σ : K ≃+* K)) :=
  have := isAlgebraic_of_numberField (E := E) (K := K)
  uniformContinuous_congr_of_forall_eq (w.valuation K) (σ : K ≃+* K) fun x =>
    (Valuation.isEquiv_valuation_valuationSubring _).eq_iff.mpr
      (ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup _ hσ x)

/-- **Decomposition group action on the completion at a finite place.** An element `σ` of the
decomposition group of `w` extends by continuity to a ring automorphism of the completion
`w.adicCompletion K`; on the image of `K` it is `σ` (`actRingEquiv_coe`). -/
noncomputable def actRingEquiv (σ : decomp E K w) : w.adicCompletion K ≃+* w.adicCompletion K :=
  ((HeightOneSpectrum.adicCompletion.equiv K w).trans
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K
      ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2).continuous
      (by
        rw [WithVal.congr_symm]
        exact (uniformContinuous_congr_of_mem ((σ⁻¹ : decomp E K w) : K ≃ₐ[E]
          K) (σ⁻¹).2).continuous))).trans
    (HeightOneSpectrum.adicCompletion.equiv K w).symm

/-- **Decomposition action at a finite place on the underlying completion.** On the underlying
uniform-space completion, `actRingEquiv σ` is the completion map of `σ`. -/
theorem actRingEquiv_apply (σ : decomp E K w) (x : w.adicCompletion K) :
    (actRingEquiv σ x).toCompletion
      = UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K)
        : K ≃+* K)) x.toCompletion :=
  rfl

/-- **Decomposition action at a finite place on elements of the field.** On the image of `K`,
`actRingEquiv σ` is `σ`: it sends the image of `x` to the image of `σ x`. -/
theorem actRingEquiv_coe (σ : decomp E K w) (x : WithVal (w.valuation K)) :
    actRingEquiv σ (x : w.adicCompletion K)
      = ((WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K) x
        : WithVal (w.valuation K)) : w.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  rw [actRingEquiv_apply, HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]

/-- **Continuity of the decomposition action at a finite place.** The automorphism `actRingEquiv σ`
of `w.adicCompletion K` is continuous. -/
theorem continuous_actRingEquiv (σ : decomp E K w) : Continuous (actRingEquiv σ) := by
  have : (actRingEquiv σ : w.adicCompletion K → w.adicCompletion K)
      = HeightOneSpectrum.adicCompletion.ofCompletion ∘
        UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K)
          : K ≃+* K)) ∘
        HeightOneSpectrum.adicCompletion.toCompletion :=
    funext fun x => HeightOneSpectrum.adicCompletion.ext (h := actRingEquiv_apply σ x)
  rw [this]
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w))

/-- **The identity acts trivially on the completion at a finite place.** The identity of the
decomposition group acts on `w.adicCompletion K` as the identity. -/
theorem actRingEquiv_one : actRingEquiv (1 : decomp E K w) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  apply HeightOneSpectrum.adicCompletion.ext
  rw [actRingEquiv_apply]
  change _ = id x.toCompletion
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map continuous_id
    fun a => ?_) _
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem
        ((1 : decomp E K w) : K ≃ₐ[E] K) (1 : decomp E K w).2)]
  rfl

/-- **The decomposition action at a finite place respects products.** The action on
`w.adicCompletion K` respects products: `σ * τ` acts as `τ` followed by `σ`. -/
theorem actRingEquiv_mul (σ τ : decomp E K w) : actRingEquiv (σ * τ) = (actRingEquiv
  τ).trans (actRingEquiv σ) := by
  apply RingEquiv.ext
  intro x
  apply HeightOneSpectrum.adicCompletion.ext
  change (actRingEquiv (σ * τ) x).toCompletion = (actRingEquiv σ (actRingEquiv τ x)).toCompletion
  rw [actRingEquiv_apply, actRingEquiv_apply, actRingEquiv_apply]
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map
    (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map) fun a =>
      ?_) _
  change _ = UniformSpace.Completion.map _ (UniformSpace.Completion.map _ _)
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem
        ((σ * τ : decomp E K w) : K ≃ₐ[E] K) (σ * τ).2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (τ : K ≃ₐ[E] K) τ.2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]
  rfl

/-- **Decomposition group to automorphisms of the completion at a finite place.** The action of the
decomposition group of `w` on `w.adicCompletion K`, as a group homomorphism into the ring
automorphisms of the completion. -/
noncomputable def actHom : decomp E K w →* (w.adicCompletion K ≃+* w.adicCompletion K) where
  toFun := actRingEquiv
  map_one' := actRingEquiv_one
  map_mul' σ τ := actRingEquiv_mul σ τ

/-- The decomposition group of `w` acts on `WithVal (w.valuation K)` through its action on `K`
(scoped in `NumberField.PlaceDecomp`). -/
noncomputable scoped instance instMulActionWithVal : MulAction (decomp E K w) (WithVal (w.valuation
  K)) where
  one_smul y := by rw [WithVal.smul_right_def]; rfl
  mul_smul σ τ y := by
    rw [WithVal.smul_right_def, WithVal.smul_right_def, WithVal.smul_right_def]; rfl

/-- The action of the decomposition group on `WithVal (w.valuation K)` is additive (scoped in
`NumberField.PlaceDecomp`). -/
noncomputable scoped instance instDistribMulActionWithVal : DistribMulAction (decomp E K
  w) (WithVal (w.valuation K)) where
  smul_zero σ := by rw [WithVal.smul_right_def]; simp
  smul_add σ x y := by
    rw [WithVal.smul_right_def, WithVal.smul_right_def, WithVal.smul_right_def]
    change WithVal.toVal _ ((σ : K ≃ₐ[E] K) (x.ofVal + y.ofVal)) = _
    rw [map_add]; rfl

/-- Each element of the decomposition group acts uniformly continuously on
`WithVal (w.valuation K)` (scoped in `NumberField.PlaceDecomp`). -/
noncomputable scoped instance instUniformContinuousConstSMul :
    UniformContinuousConstSMul (decomp E K w) (WithVal (w.valuation K)) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

/-- **Decomposition group acts on the completion at a finite place.** The decomposition group of
`w` acts on `w.adicCompletion K` by ring automorphisms, through `actRingEquiv` (scoped in
`NumberField.PlaceDecomp`). -/
noncomputable scoped instance instMulSemiringAction : MulSemiringAction (decomp E K
  w) (w.adicCompletion K) where
  smul σ x := actRingEquiv σ x
  one_smul x := by change actRingEquiv 1 x = x; rw [actRingEquiv_one]; rfl
  mul_smul σ τ x := by
    change actRingEquiv (σ * τ) x = actRingEquiv σ (actRingEquiv τ x)
    rw [actRingEquiv_mul]
    rfl
  smul_zero σ := by change actRingEquiv σ 0 = 0; rw [map_zero]
  smul_add σ x y := by
    change actRingEquiv σ (x + y) = actRingEquiv σ x + actRingEquiv σ y
    rw [map_add]
  smul_one σ := by change actRingEquiv σ 1 = 1; rw [map_one]
  smul_mul σ x y := by
    change actRingEquiv σ (x * y) = actRingEquiv σ x * actRingEquiv σ y
    rw [map_mul]

/-- **The scoped action at a finite place is the decomposition action.** The scoped action of the
decomposition group on `w.adicCompletion K` is `actRingEquiv`. -/
theorem smul_def (σ : decomp E K w) (x : w.adicCompletion K) : σ • x = actRingEquiv σ x := rfl

/-- The decomposition group of `w` acts on the units of `w.adicCompletion K` through its action on
the completion (scoped in `NumberField.PlaceDecomp`). -/
noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K
  w) (w.adicCompletion K)ˣ :=
  Units.mulDistribMulActionRight

section integers

open WithZeroTopology in
/-- The decomposition group action preserves the valuation of the completion:
`Valued.v (actRingEquiv σ x) = Valued.v x`. -/
theorem valued_actRingEquiv (σ : decomp E K w) (x : w.adicCompletion K) : Valued.v (actRingEquiv σ
  x) = Valued.v x := by
  have hclosed : IsClosed {y : w.adicCompletion K | Valued.v (actRingEquiv σ y) = Valued.v y} := by
    have : {y : w.adicCompletion K | Valued.v (actRingEquiv σ y) = Valued.v y}
        = {y | Valued.v.restrict (actRingEquiv σ y) = Valued.v.restrict y} :=
      Set.ext fun y => (Valuation.restrict_inj _).symm
    rw [this]
    exact isClosed_eq (Valued.continuous_valuation.comp (continuous_actRingEquiv σ))
      Valued.continuous_valuation
  obtain ⟨x, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w x
  refine UniformSpace.Completion.induction_on
    (p := fun y => Valued.v (actRingEquiv σ (HeightOneSpectrum.adicCompletion.ofCompletion y)) =
      Valued.v (HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K)) x
    (by simpa only [Set.preimage_ofPred_eq] using
      hclosed.preimage (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)) fun a => ?_
  show Valued.v (actRingEquiv σ (a : w.adicCompletion K)) = Valued.v (a : w.adicCompletion K)
  rw [actRingEquiv_coe, HeightOneSpectrum.adicCompletion.valued_ofCompletion_apply,
    HeightOneSpectrum.adicCompletion.valued_ofCompletion_apply,
    Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, ← WithVal.apply_ofVal,
      ← WithVal.apply_ofVal,
    WithVal.congr_apply]
  have := isAlgebraic_of_numberField (E := E) (K := K)
  exact (Valuation.isEquiv_valuation_valuationSubring _).eq_iff.mpr
    (ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup _ σ.2 a.ofVal)

/-- The decomposition group action preserves the integers of the completion:
`σ • x ∈ w.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K`. -/
theorem smul_mem_adicCompletionIntegers_iff (σ : decomp E K w) (x : w.adicCompletion K) :
    σ • x ∈ w.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    smul_def, valued_actRingEquiv]

/-- The decomposition group of `w` acts on the integers `w.adicCompletionIntegers K` by restricting
its action on the completion (scoped in `NumberField.PlaceDecomp`). -/
noncomputable scoped instance instSMulIntegers : SMul (decomp E K w) (w.adicCompletionIntegers K) :=
  ⟨fun σ x => ⟨σ • (x : w.adicCompletion K), (smul_mem_adicCompletionIntegers_iff σ _).2 x.2⟩⟩

/-- The action on the integers of the completion is the action on the underlying element. -/
theorem coe_smul_integers (σ : decomp E K w) (x : w.adicCompletionIntegers K) :
    ((σ • x : w.adicCompletionIntegers K) : w.adicCompletion K) = σ • (x : w.adicCompletion K)
      := rfl

/-- The decomposition group of `w` acts on the integers of `w.adicCompletion K` by ring
automorphisms (scoped in `NumberField.PlaceDecomp`). -/
noncomputable scoped instance instMulSemiringActionIntegers : MulSemiringAction (decomp E K
  w) (w.adicCompletionIntegers K) :=
  { instSMulIntegers (E := E) (K := K) (w := w) with
    one_smul := fun x => Subtype.ext (by rw [coe_smul_integers, one_smul])
    mul_smul := fun σ τ x => Subtype.ext (by rw [coe_smul_integers, coe_smul_integers,
      coe_smul_integers, mul_smul])
    smul_zero := fun σ => Subtype.ext (by rw [coe_smul_integers]; exact smul_zero σ)
    smul_add := fun σ x y => Subtype.ext (by
      rw [coe_smul_integers]; exact smul_add σ (x : w.adicCompletion K) y)
    smul_one := fun σ => Subtype.ext (by rw [coe_smul_integers]; exact smul_one σ)
    smul_mul := fun σ x y => Subtype.ext (by
      rw [coe_smul_integers]
      exact MulSemiringAction.smul_mul σ (x : w.adicCompletion K) y) }

/-- The decomposition group of `w` acts on the units of the integers of `w.adicCompletion K`
(scoped in `NumberField.PlaceDecomp`). -/
noncomputable scoped instance instMulDistribMulActionIntegerUnits : MulDistribMulAction (decomp E K
  w) (w.adicCompletionIntegers K)ˣ :=
  Units.mulDistribMulActionRight

/-- The multiplicative action underlying `instMulSemiringActionIntegers`, as a direct instance
(scoped in `NumberField.PlaceDecomp`). -/
noncomputable scoped instance instMulActionIntegers : MulAction (decomp E K
  w) (w.adicCompletionIntegers K) :=
  (instMulSemiringActionIntegers (E := E) (K := K) (w := w)).toMulAction

/-- The scalar action underlying `instMulDistribMulActionUnits`, as a direct instance (scoped in
`NumberField.PlaceDecomp`). -/
noncomputable scoped instance instSMulUnits : SMul (decomp E K w) (w.adicCompletion K)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction.toSMul

/-- The scalar action underlying `instMulDistribMulActionIntegerUnits`, as a direct instance
(scoped in `NumberField.PlaceDecomp`). -/
noncomputable scoped instance instSMulIntegerUnits : SMul (decomp E K w) (w.adicCompletionIntegers
  K)ˣ :=
  (instMulDistribMulActionIntegerUnits (E := E) (K := K) (w := w)).toMulAction.toSMul

/-- The multiplicative action underlying `instMulDistribMulActionUnits`, as a direct instance
(scoped in `NumberField.PlaceDecomp`). -/
noncomputable scoped instance instMulActionUnits : MulAction (decomp E K w) (w.adicCompletion K)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction

/-- The multiplicative action underlying `instMulDistribMulActionIntegerUnits`, as a direct
instance (scoped in `NumberField.PlaceDecomp`). -/
noncomputable scoped instance instMulActionIntegerUnits : MulAction (decomp E K
  w) (w.adicCompletionIntegers K)ˣ :=
  (instMulDistribMulActionIntegerUnits (E := E) (K := K) (w := w)).toMulAction

end integers

end NumberField.PlaceDecomp

open IsDedekindDomain NumberField

namespace NumberField.PlaceTransport

section general
variable {R S : Type*} [Field R] [Field S] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Valuation-matching ring isomorphisms are uniformly continuous.** Let `R` and `S` be fields.
A ring isomorphism `f : R ≃+* S` that carries a surjective valuation `v` on `R` to the valuation
`v'` on `S`, `v' (f x) = v x`, is uniformly continuous as a map `WithVal v → WithVal v'`. -/
theorem uniformContinuous_congr_of_forall_eq (v : Valuation R Γ₀) (v' : Valuation S Γ₀) (hv
  : Function.Surjective v)
    (f : R ≃+* S) (h : ∀ x, v' (f x) = v x) : UniformContinuous (WithVal.congr v v' f) := by
  apply uniformContinuous_addMonoidHom_of_continuous
  apply continuous_of_continuousAt_zero (WithVal.congr v v' f).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨x₀, hx₀⟩ := hv (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hx₀' : Valued.v.restrict (WithVal.toVal v x₀) ≠ 0 := fun h0 => by
    have h1 := (Valuation.restrict_eq_zero_iff Valued.v).1 h0
    rw [WithVal.valued_toVal, hx₀] at h1
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
      (h1.trans (map_zero _).symm))
  refine Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hx₀', fun x hx => hγ ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff, WithVal.valued_toVal,
    hx₀] at hx
  change Valued.v.restrict (WithVal.congr v v' f x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, WithVal.congr_apply, WithVal.valued_toVal, h,
    WithVal.apply_ofVal]
  exact hx

end general

variable (E K : Type*) [Field E] [Field K] [Algebra E K]

/-- **Galois action on finite places.** The automorphisms `K ≃ₐ[E] K` act on the left on the
nonzero primes of `𝓞 K`: `σ • w` is the preimage of `w` under `σ⁻¹`, that is the prime `σ(w)`,
so `x ∈ σ • w ↔ σ⁻¹ • x ∈ w` (scoped in `NumberField.PlaceTransport`). -/
noncomputable scoped instance instMulActionHeightOneSpectrum : MulAction (K ≃ₐ[E]
  K) (HeightOneSpectrum (𝓞 K)) where
  smul σ w := HeightOneSpectrum.comap (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹ : 𝓞 K →+*
    𝓞 K)
    (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹).surjective w
  one_smul w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    change (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) 1⁻¹) x ∈ w.asIdeal ↔ x ∈ w.asIdeal
    rw [MulSemiringAction.toRingEquiv_apply_apply, inv_one, one_smul])
  mul_smul σ τ w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    change (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) (σ * τ)⁻¹) x ∈ w.asIdeal ↔
      (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) τ⁻¹) ((MulSemiringAction.toRingEquiv (K ≃ₐ[E]
        K) (𝓞 K) σ⁻¹) x) ∈ w.asIdeal
    rw [MulSemiringAction.toRingEquiv_apply_apply, MulSemiringAction.toRingEquiv_apply_apply,
      MulSemiringAction.toRingEquiv_apply_apply,
      mul_inv_rev, mul_smul])

variable {E K}

/-- The prime ideal of `σ • w` is the preimage of the prime ideal of `w` under `σ⁻¹`. -/
theorem smul_asIdeal (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    (σ • w).asIdeal = w.asIdeal.comap (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹ : 𝓞 K →+*
      𝓞 K) := rfl

/-- `x` lies in the prime of `σ • w` if and only if `σ⁻¹ • x` lies in the prime of `w`. -/
theorem mem_smul_asIdeal_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ (σ • w).asIdeal ↔ σ⁻¹ • x ∈ w.asIdeal := Iff.rfl

/-- `σ • x` lies in the prime of `σ • w` if and only if `x` lies in the prime of `w`. -/
theorem smul_mem_smul_asIdeal_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    σ • x ∈ (σ • w).asIdeal ↔ x ∈ w.asIdeal := by
  rw [mem_smul_asIdeal_iff, inv_smul_smul]

/-- The prime ideal of `σ • w` is the image of the prime ideal of `w` under `σ`. -/
theorem smul_asIdeal_eq_map (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    (σ • w).asIdeal = Ideal.map ((MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ : 𝓞 K ≃+* 𝓞 K)
      : 𝓞 K →+* 𝓞 K) w.asIdeal := by
  rw [Ideal.map_comap_of_equiv]
  ext x
  rw [mem_smul_asIdeal_iff, Ideal.mem_comap, MulSemiringAction.toRingEquiv_apply_symm_apply]

/-- `σ • x` lies in the `n`-th power of the prime of `σ • w` if and only if `x` lies in the `n`-th
power of the prime of `w`. -/
theorem smul_mem_smul_asIdeal_pow_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (n
  : ℕ) :
    σ • x ∈ (σ • w).asIdeal ^ n ↔ x ∈ w.asIdeal ^ n := by
  rw [smul_asIdeal_eq_map, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap,
    MulSemiringAction.toRingEquiv_apply_symm_apply,
    inv_smul_smul]

variable [NumberField K]

/-- The Galois action carries valuations along: for `r ∈ 𝓞 K`, the `σ • w`-adic valuation of
`σ • r` equals the `w`-adic valuation of `r`. -/
theorem intValuation_smul_apply (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    (σ • w).intValuation (σ • r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [smul_zero, Valuation.map_zero, Valuation.map_zero]
  · have hσr : σ • r ≠ 0 := fun h0 => hr (by rw [← inv_smul_smul σ r, h0, smul_zero])
    apply le_antisymm
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, w.intValuation r = WithZero.exp (-(n : ℤ)) := ⟨_,
      w.intValuation_if_neg hr⟩
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem, smul_mem_smul_asIdeal_pow_iff,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (σ • w).intValuation (σ • r) = WithZero.exp (-(n : ℤ)) := ⟨_,
      (σ • w).intValuation_if_neg hσr⟩
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem, ← smul_mem_smul_asIdeal_pow_iff σ,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]

/-- If `σ • w = w'`, then `w'.valuation K (σ x) = w.valuation K x` for every `x ∈ K`. -/
theorem valuation_apply_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w =
  w') (x : K) :
    w'.valuation K (σ x) = w.valuation K x := by
  subst h
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h1 : ∀ c : 𝓞 K, σ (algebraMap (𝓞 K) K c) = algebraMap (𝓞 K) K (σ • c) := fun c => rfl
  rw [map_div₀, map_div₀, map_div₀, h1, h1, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      intValuation_smul_apply,
    intValuation_smul_apply]

/-- **Galois automorphisms are uniformly continuous between finite places.** If `σ • w = w'`, then
`σ` is uniformly continuous from the `w`-adic to the `w'`-adic uniformity on `K`. -/
theorem uniformContinuous_congr_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ •
  w = w') :
    UniformContinuous (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K))
      :=
  uniformContinuous_congr_of_forall_eq (w.valuation K) (w'.valuation K) (w.valuation_surjective K)
    _ (valuation_apply_of_smul_eq h)

/-- **Transport between completions at finite places.** For `σ : K ≃ₐ[E] K` with `σ • w = w'`,
the ring isomorphism `w.adicCompletion K ≃+* w'.adicCompletion K` extending `σ` by continuity:
on the image of `K` it is `σ` (`transport_coe`), and it preserves valuations
(`valued_transport`). -/
noncomputable def transport (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    w.adicCompletion K ≃+* w'.adicCompletion K :=
  ((HeightOneSpectrum.adicCompletion.equiv K w).trans
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K
      ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_smul_eq h).continuous
      ((uniformContinuous_congr_of_smul_eq (inv_smul_eq_iff.2 h.symm)).continuous.congr fun _ =>
        rfl))).trans
    (HeightOneSpectrum.adicCompletion.equiv K w').symm

/-- **Transport between finite places on the underlying completions.** On the underlying
uniform-space completions, `transport σ h` is the completion map of `σ`. -/
theorem transport_apply (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x
  : w.adicCompletion K) :
    (transport σ h x).toCompletion
      = UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K)
        : K ≃+* K)) x.toCompletion :=
  rfl

/-- **Transport between finite places on elements of the field.** On the image of `K`,
`transport σ h` is `σ`: it sends the image of `x` in `w.adicCompletion K` to the image of `σ x` in
`w'.adicCompletion K`. -/
theorem transport_coe (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x
  : WithVal (w.valuation K)) :
    transport σ h (x : w.adicCompletion K)
      = ((WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K) x
        : WithVal (w'.valuation K)) : w'.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  rw [transport_apply, HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_smul_eq h)]

/-- **Continuity of the transport between finite places.** The transport `transport σ h` between
completions at finite places is continuous. -/
theorem continuous_transport (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w')
  : Continuous (transport σ h) := by
  have : (transport σ h : w.adicCompletion K → w'.adicCompletion K)
      = HeightOneSpectrum.adicCompletion.ofCompletion ∘
        UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K)
          : K ≃+* K)) ∘
        HeightOneSpectrum.adicCompletion.toCompletion :=
    funext fun x => HeightOneSpectrum.adicCompletion.ext (h := transport_apply σ h x)
  rw [this]
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w').comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w))

/-- Let `K` be a number field and `w` a finite place of `K`. For `c ≠ 0`, the set of `y` in
`w.adicCompletion K` with `Valued.v y ≤ c` is clopen. -/
theorem isClopen_setOf_valued_le (w : HeightOneSpectrum (𝓞 K)) {c : WithZero (Multiplicative ℤ)} (hc
  : c ≠ 0) :
    IsClopen {y : w.adicCompletion K | Valued.v y ≤ c} := by
  obtain ⟨y₁, rfl⟩ := w.valuedAdicCompletion_surjective K c
  have hr : Valued.v.restrict y₁ ≠ 0 := fun h0 => hc ((Valuation.restrict_eq_zero_iff Valued.v).1
    h0)
  have : {y : w.adicCompletion K | Valued.v y ≤ Valued.v y₁} = {y | Valued.v.restrict y ≤
    Valued.v.restrict y₁} :=
    Set.ext fun y => (Valuation.restrict_le_iff Valued.v (x := y) (y := y₁)).symm
  rw [this]
  exact Valued.isClopen_closedBall (w.adicCompletion K) hr

/-- The transport preserves valuations: `Valued.v (transport σ h x) = Valued.v x`. -/
theorem valued_transport (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x
  : w.adicCompletion K) :
    Valued.v (transport σ h x) = Valued.v x := by
  have key : ∀ c : WithZero (Multiplicative ℤ), c ≠ 0 → ∀ y : w.adicCompletion K,
    (Valued.v (transport σ h y) ≤ c ↔ Valued.v y ≤ c) := by
    intro c hc y
    have hclosed : IsClosed {y : w.adicCompletion K | Valued.v (transport σ h y) ≤ c ↔ Valued.v y ≤
      c} := by
      have h1 : IsClopen {y : w.adicCompletion K | Valued.v (transport σ h y) ≤ c} :=
        (isClopen_setOf_valued_le w' hc).preimage (continuous_transport σ h)
      have h2 : IsClopen {y : w.adicCompletion K | Valued.v y ≤ c} := isClopen_setOf_valued_le w hc
      have : {y : w.adicCompletion K | Valued.v (transport σ h y) ≤ c ↔ Valued.v y ≤ c}
          = ({y | Valued.v (transport σ h y) ≤ c} ∩ {y | Valued.v y ≤ c}) ∪ ({y
            | Valued.v (transport σ h y) ≤ c}ᶜ ∩ {y | Valued.v y ≤ c}ᶜ) := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      rw [this]
      exact ((h1.inter h2).union (h1.compl.inter h2.compl)).isClosed
    obtain ⟨y, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w y
    refine UniformSpace.Completion.induction_on
      (p := fun y => Valued.v (transport σ h (HeightOneSpectrum.adicCompletion.ofCompletion y)) ≤ c
        ↔
        Valued.v (HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K) ≤ c) y
      (by simpa only [Set.preimage_ofPred_eq] using
        hclosed.preimage (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)) fun a => ?_
    show Valued.v (transport σ h (a : w.adicCompletion K)) ≤ c ↔ Valued.v (a : w.adicCompletion K) ≤
      c
    rw [transport_coe, HeightOneSpectrum.adicCompletion.valued_ofCompletion_apply,
      HeightOneSpectrum.adicCompletion.valued_ofCompletion_apply, Valued.valuedCompletion_apply,
        Valued.valuedCompletion_apply, ← WithVal.apply_ofVal, ← WithVal.apply_ofVal,
      WithVal.congr_apply, WithVal.ofVal_toVal, AlgEquiv.coe_toRingEquiv,
        valuation_apply_of_smul_eq h]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, Valuation.map_zero, Valuation.map_zero]
  · have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have h0' : Valued.v (transport σ h x) ≠ 0 := (Valuation.ne_zero_iff
      _).2 ((map_ne_zero (transport σ h)).2 hx)
    exact le_antisymm ((key _ h0 x).2 le_rfl) ((key _ h0' x).1 le_rfl)

/-- The transport matches the integers of the two completions:
`transport σ h x ∈ w'.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K`. -/
theorem transport_mem_adicCompletionIntegers_iff (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h
  : σ • w = w')
    (x : w.adicCompletion K) : transport σ h x ∈ w'.adicCompletionIntegers K ↔ x ∈
      w.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    valued_transport]

/-- **Transport between integers of completions.** The restriction of `transport σ h` to a ring
isomorphism `w.adicCompletionIntegers K ≃+* w'.adicCompletionIntegers K`. -/
noncomputable def transportIntegers (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w =
  w') :
    w.adicCompletionIntegers K ≃+* w'.adicCompletionIntegers K where
  toFun x := ⟨transport σ h x, (transport_mem_adicCompletionIntegers_iff σ h _).2 x.2⟩
  invFun y := ⟨(transport σ h).symm y,
    (transport_mem_adicCompletionIntegers_iff σ h _).1
      (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((transport σ h).symm_apply_apply x)
  right_inv y := Subtype.ext ((transport σ h).apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul (transport σ h) (x : w.adicCompletion K) (y
    : w.adicCompletion K))
  map_add' x y := Subtype.ext (map_add (transport σ h) (x : w.adicCompletion K) (y
    : w.adicCompletion K))

/-- `transportIntegers σ h` agrees with `transport σ h` on underlying elements. -/
theorem coe_transportIntegers (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x
  : w.adicCompletionIntegers K) :
    ((transportIntegers σ h x : w'.adicCompletionIntegers K) : w'.adicCompletion K) = transport σ
      h (x : w.adicCompletion K) := rfl

/-- **Transport between local units at finite places.** The group isomorphism
`(w.adicCompletion K)ˣ ≃* (w'.adicCompletion K)ˣ` induced by `transport σ h`. -/
noncomputable abbrev transportUnits (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w =
  w') :
    (w.adicCompletion K)ˣ ≃* (w'.adicCompletion K)ˣ :=
  Units.mapEquiv (transport σ h).toMulEquiv

/-- The group isomorphism between the units of `w.adicCompletionIntegers K` and of
`w'.adicCompletionIntegers K` induced by `transportIntegers σ h`. -/
noncomputable abbrev transportIntegerUnits (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ •
  w = w') :
    (w.adicCompletionIntegers K)ˣ ≃* (w'.adicCompletionIntegers K)ˣ :=
  Units.mapEquiv (transportIntegers σ h).toMulEquiv

end NumberField.PlaceTransport

open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

private theorem NumberField.PlaceTransport.transport_one (E K : Type*) [Field E] [Field
  K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (h : (1 : K ≃ₐ[E] K) • w
      = w) :
    NumberField.PlaceTransport.transport (1 : K ≃ₐ[E] K) h = RingEquiv.refl (w.adicCompletion K)
      := by
  apply RingEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w x
  have := UniformSpace.Completion.ext
    (f := fun y => (NumberField.PlaceTransport.transport (1 : K ≃ₐ[E] K) h
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y) : w.adicCompletion K))
    (g := fun y => (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y
      : w.adicCompletion K))
    ((NumberField.PlaceTransport.continuous_transport (1 : K ≃ₐ[E] K) h).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w) fun a => by
      show NumberField.PlaceTransport.transport (1 : K ≃ₐ[E] K) h (a : w.adicCompletion K) = (a
        : w.adicCompletion K)
      rw [NumberField.PlaceTransport.transport_coe]; rfl
  exact congrFun this y

private theorem NumberField.PlaceTransport.transport_trans_transport (E K : Type*) [Field E] [Field
  K] [NumberField K] [Algebra E K]
    (σ τ : K ≃ₐ[E] K) {w w' w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') :
    (NumberField.PlaceTransport.transport τ h₁).trans (NumberField.PlaceTransport.transport σ h₂)
      = NumberField.PlaceTransport.transport (σ * τ) h₃ := by
  apply RingEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w x
  have := UniformSpace.Completion.ext
    (f := fun y => NumberField.PlaceTransport.transport σ h₂ (NumberField.PlaceTransport.transport τ
      h₁
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K)))
    (g := fun y => NumberField.PlaceTransport.transport (σ * τ) h₃
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K))
    ((NumberField.PlaceTransport.continuous_transport σ h₂).comp
      ((NumberField.PlaceTransport.continuous_transport τ h₁).comp
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)))
    ((NumberField.PlaceTransport.continuous_transport (σ * τ) h₃).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)) fun a => by
      show NumberField.PlaceTransport.transport σ h₂ (NumberField.PlaceTransport.transport τ h₁ (a
        : w.adicCompletion K))
        = NumberField.PlaceTransport.transport (σ * τ) h₃ (a : w.adicCompletion K)
      rw [NumberField.PlaceTransport.transport_coe, NumberField.PlaceTransport.transport_coe,
        NumberField.PlaceTransport.transport_coe]
      rfl
  exact congrFun this x

private theorem NumberField.PlaceTransport.transport_eq_actRingEquiv (E K : Type*) [Field E] [Field
  K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (σ
      : NumberField.PlaceDecomp.decomp E K w)
    (h : (σ : K ≃ₐ[E] K) • w = w) :
    NumberField.PlaceTransport.transport (σ : K ≃ₐ[E] K) h = NumberField.PlaceDecomp.actRingEquiv σ
      :=
  rfl

private theorem NumberField.PlaceTransport.stabilizer_eq_decomp (E K : Type*) [Field E] [Field
  K] [NumberField K] [Algebra E K]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.stabilizer (K ≃ₐ[E] K) w = NumberField.PlaceDecomp.decomp E K w := by
  ext σ
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Valuation.mem_valuationSubring_iff,
      Valuation.mem_valuationSubring_iff, show σ⁻¹ • x = σ⁻¹ x from rfl,
      NumberField.PlaceTransport.valuation_apply_of_smul_eq
        (inv_smul_eq_iff.2 h.symm)]
  · intro hσ
    have hσ' : σ⁻¹ ∈ NumberField.PlaceDecomp.decomp E K w := inv_mem hσ
    apply IsDedekindDomain.HeightOneSpectrum.ext
    ext x
    rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff,
      ← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem,
      ← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
    have key : w.intValuation (σ⁻¹ • x) = w.intValuation x := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K),
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K)]
      have := NumberField.PlaceDecomp.isAlgebraic_of_numberField (E := E) (K := K)
      exact (Valuation.isEquiv_valuation_valuationSubring _).eq_iff.mpr
        (ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup _ hσ' (algebraMap _ K x))
    exact Iff.of_eq (congrArg (· < (1 : WithZero (Multiplicative ℤ))) key)

private theorem NumberField.PlaceTransport.under_smul (E K : Type*) [Field E] [Field K] [Algebra E
  K]
    (σ : K ≃ₐ[E] K) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (σ • w).under (NumberField.RingOfIntegers E) = w.under (NumberField.RingOfIntegers E) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal,
    IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have : σ⁻¹ • (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) x)
      = algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) x :=
    Subtype.ext ((σ⁻¹).commutes _)
  rw [this]

namespace NumberField.PlaceTransport.OrbitAux

open IsDedekindDomain NumberField

private theorem numberField_of_algebra (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E
  K] : NumberField E := by
  have : CharZero E := RingHom.charZero (algebraMap E K)
  exact { to_charZero := inferInstance,
          to_finiteDimensional :=
            FiniteDimensional.of_injective (algebraMap E K).toRatAlgHom.toLinearMap (algebraMap E
              K).injective }

private theorem smul_asIdeal_eq (E K : Type*) [Field E] [Field K] [Algebra E K] (σ : K ≃ₐ[E] K) (w
  : HeightOneSpectrum (𝓞 K)) :
    (σ • w).asIdeal = σ • w.asIdeal := by
  ext x
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem]

end NumberField.PlaceTransport.OrbitAux



private theorem NumberField.PlaceTransport.orbit_eq_setOf_under_eq (E K : Type*) [Field E] [Field
  K] [NumberField K]
    [Algebra E K] [IsGalois E K] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers
      K)) :
    MulAction.orbit (K ≃ₐ[E] K) w =
      {w' | w'.under (NumberField.RingOfIntegers E) = w.under (NumberField.RingOfIntegers E)} := by
  classical
  have : NumberField E := NumberField.PlaceTransport.OrbitAux.numberField_of_algebra E K
  have : w.asIdeal.IsPrime := w.isPrime
  have : w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal := ⟨rfl⟩
  have horb := Algebra.IsInvariant.orbit_eq_primesOver (𝓞 E) (𝓞 K) (K ≃ₐ[E] K) (w.under (𝓞
    E)).asIdeal w.asIdeal
  ext w'
  constructor
  · rintro ⟨σ, rfl⟩
    apply HeightOneSpectrum.ext
    change Ideal.under (𝓞 E) (σ • w).asIdeal = Ideal.under (𝓞 E) w.asIdeal
    rw [NumberField.PlaceTransport.OrbitAux.smul_asIdeal_eq, Ideal.under_smul]
  · intro hw'
    have hmem : w'.asIdeal ∈ (w.under (𝓞 E)).asIdeal.primesOver (𝓞 K) :=
      ⟨w'.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw').symm⟩⟩
    rw [← horb] at hmem
    obtain ⟨σ, hσ⟩ := hmem
    refine ⟨σ, HeightOneSpectrum.ext ?_⟩
    change (σ • w).asIdeal = w'.asIdeal
    rw [NumberField.PlaceTransport.OrbitAux.smul_asIdeal_eq]
    exact hσ


open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

namespace NumberField.FiniteSIdele

variable (E K : Type u) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

/-- **Decomposition group at the chosen place above a finite place.** The decomposition group in
`K ≃ₐ[E] K` of the chosen place `PlaceAbove.above E K v` above the finite place `v` of `E`. -/
noncomputable abbrev D (v : HeightOneSpectrum (𝓞 E)) : Subgroup (K ≃ₐ[E] K) :=
  NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)

section local_modules

/-- **Local units at the chosen place above a finite place.** The units of the completion
`w.adicCompletion K` at `w = PlaceAbove.above E K v`, written additively, as a `ℤ`-linear
representation of the decomposition group `D E K v` acting on the completion. -/
noncomputable abbrev localUnits (v : HeightOneSpectrum (𝓞 E)) : Rep ℤ (D E K v) :=
  Rep.ofMulDistribMulAction (D E K v) ((NumberField.PlaceAbove.above E K v).adicCompletion K)ˣ

/-- **Local integer units at the chosen place above a finite place.** The units of the integers
`w.adicCompletionIntegers K` at `w = PlaceAbove.above E K v`, written additively, as a
`ℤ`-linear representation of `D E K v`. -/
noncomputable abbrev localIntegerUnits (v : HeightOneSpectrum (𝓞 E)) : Rep ℤ (D E K v) :=
  Rep.ofMulDistribMulAction (D E K v) ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers
    K)ˣ

/-- The inclusion of the integer units into the units of the completion at the chosen place above
`v`, as a morphism of representations of `D E K v`. -/
noncomputable def integerUnitsToUnits (v : HeightOneSpectrum (𝓞 E)) : localIntegerUnits E K v ⟶
  localUnits E K v :=
  Rep.ofHom ⟨(Units.map ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers
    K).subtype.toMonoidHom).toAdditive.toIntLinearMap,
    fun _ => rfl⟩

/-- `integerUnitsToUnits` sends an integer unit to the same element, viewed as a unit of the
completion. -/
theorem integerUnitsToUnits_hom_apply (v : HeightOneSpectrum (𝓞 E)) (u
  : ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K)ˣ) :
    Additive.toMul ((integerUnitsToUnits E K v).hom (Additive.ofMul u))
      = Units.map ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers
        K).subtype.toMonoidHom u := rfl

end local_modules



end NumberField.FiniteSIdele

open NumberField

namespace NumberField.InfinitePlaceTransport

section general
variable {R S : Type*} [Field R] [Field S]

/-- **Absolute-value-matching ring isomorphisms are uniformly continuous.** Let `R` and `S` be
fields. A ring isomorphism `f : R ≃+* S` with `v' (f x) = v x` for real absolute values `v` and
`v'` is an isometry `WithAbs v → WithAbs v'`, hence uniformly continuous. -/
theorem uniformContinuous_congr_of_forall_eq (v : AbsoluteValue R ℝ) (v' : AbsoluteValue S ℝ) (f : R
  ≃+* S)
    (h : ∀ x, v' (f x) = v x) : UniformContinuous (WithAbs.congr v v' f) :=
  (AddMonoidHomClass.isometry_of_norm (WithAbs.congr v v' f) fun x => by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
    exact h _).uniformContinuous

end general

end NumberField.InfinitePlaceTransport

namespace NumberField.InfPlaceDecomp

variable (E K : Type*) [Field E] [Field K] [Algebra E K] (w : InfinitePlace K)

/-- **Decomposition group of an infinite place.** The stabilizer of the infinite place `w` of `K`
in `K ≃ₐ[E] K`, for Mathlib's action `σ • w = w ∘ σ⁻¹`. -/
abbrev decomp : Subgroup (K ≃ₐ[E] K) := MulAction.stabilizer (K ≃ₐ[E] K) w

variable {E K w}

/-- An element `σ` of the decomposition group of the infinite place `w` preserves `w`:
`w (σ x) = w x`. -/
theorem apply_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) (x : K) : w (σ x) = w x := by
  rw [MulAction.mem_stabilizer_iff] at hσ
  conv_lhs => rw [← hσ]
  rw [InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]

/-- **Decomposition group elements are uniformly continuous at an infinite place.** An element of
the decomposition group of the infinite place `w` is uniformly continuous for the absolute value of
`w`. -/
theorem uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    UniformContinuous (WithAbs.congr w.1 w.1 (σ : K ≃+* K)) :=
  InfinitePlaceTransport.uniformContinuous_congr_of_forall_eq w.1 w.1 (σ : K ≃+* K)
    (apply_of_mem σ hσ)

/-- **Decomposition group action on the completion at an infinite place.** An element `σ` of the
decomposition group of the infinite place `w` extends by continuity to a ring automorphism of
the completion `w.Completion`; on the image of `K` it is `σ` (`actRingEquiv_coe`). -/
noncomputable def actRingEquiv (σ : decomp E K w) : w.Completion ≃+* w.Completion :=
  ((AbsoluteValue.Completion.equiv w.1).trans
    (UniformSpace.Completion.mapRingEquiv (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2).continuous
      (by
        rw [WithAbs.congr_symm]
        exact (uniformContinuous_congr_of_mem ((σ⁻¹ : decomp E K w) : K ≃ₐ[E]
          K) (σ⁻¹).2).continuous))).trans
    (AbsoluteValue.Completion.equiv w.1).symm

/-- **Decomposition action at an infinite place on the underlying completion.** On the underlying
uniform-space completion, `actRingEquiv σ` is the completion map of `σ`. -/
theorem actRingEquiv_apply (σ : decomp E K w) (x : w.Completion) :
    AbsoluteValue.Completion.toCompletion (actRingEquiv σ x) =
      UniformSpace.Completion.map (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
        (AbsoluteValue.Completion.toCompletion x) := by
  rw [actRingEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    AbsoluteValue.Completion.equiv_symm_apply, AbsoluteValue.Completion.toCompletion_ofCompletion,
    AbsoluteValue.Completion.equiv_apply]
  rfl

/-- **Decomposition action at an infinite place on elements of the field.** On the image of `K`,
`actRingEquiv σ` is `σ`: it sends the image of `x` to the image of `σ x`. -/
theorem actRingEquiv_coe (σ : decomp E K w) (x : WithAbs w.1) :
    actRingEquiv σ (x : w.Completion) = ((WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K) x
      : WithAbs w.1) : w.Completion) := by
  apply AbsoluteValue.Completion.toCompletion_injective w.1
  rw [actRingEquiv_apply, AbsoluteValue.Completion.toCompletion_coe,
    AbsoluteValue.Completion.toCompletion_coe,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]

/-- **Continuity of the decomposition action at an infinite place.** The automorphism
`actRingEquiv σ` of `w.Completion` is continuous. -/
theorem continuous_actRingEquiv (σ : decomp E K w) : Continuous (actRingEquiv σ) := by
  have : (actRingEquiv σ : w.Completion → w.Completion) =
      AbsoluteValue.Completion.ofCompletion ∘
        UniformSpace.Completion.map (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) ∘
        AbsoluteValue.Completion.toCompletion :=
    funext fun x => AbsoluteValue.Completion.toCompletion_injective w.1 (by
      rw [Function.comp_apply, Function.comp_apply,
        AbsoluteValue.Completion.toCompletion_ofCompletion, actRingEquiv_apply])
  rw [this]
  exact (AbsoluteValue.Completion.continuous_ofCompletion w.1).comp
    (UniformSpace.Completion.continuous_map.comp
      (AbsoluteValue.Completion.continuous_toCompletion w.1))

/-- **The identity acts trivially on the completion at an infinite place.** The identity of the
decomposition group acts on `w.Completion` as the identity. -/
theorem actRingEquiv_one : actRingEquiv (1 : decomp E K w) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  apply AbsoluteValue.Completion.toCompletion_injective w.1
  rw [actRingEquiv_apply]
  change _ = id (AbsoluteValue.Completion.toCompletion x)
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map continuous_id
    fun a => ?_) _
  rw [UniformSpace.Completion.map_coe
    (uniformContinuous_congr_of_mem ((1 : decomp E K w) : K ≃ₐ[E] K) (1 : decomp E K w).2)]
  rfl

/-- **The decomposition action at an infinite place respects products.** The action on
`w.Completion` respects products: `σ * τ` acts as `τ` followed by `σ`. -/
theorem actRingEquiv_mul (σ τ : decomp E K w) : actRingEquiv (σ * τ) = (actRingEquiv
  τ).trans (actRingEquiv σ) := by
  apply RingEquiv.ext
  intro x
  apply AbsoluteValue.Completion.toCompletion_injective w.1
  change AbsoluteValue.Completion.toCompletion (actRingEquiv (σ * τ) x) =
    AbsoluteValue.Completion.toCompletion (actRingEquiv σ (actRingEquiv τ x))
  rw [actRingEquiv_apply, actRingEquiv_apply, actRingEquiv_apply]
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map
    (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map) fun a =>
      ?_) _
  change _ = UniformSpace.Completion.map _ (UniformSpace.Completion.map _ _)
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem
        ((σ * τ : decomp E K w) : K ≃ₐ[E] K) (σ * τ).2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (τ : K ≃ₐ[E] K) τ.2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]
  rfl

/-- **Decomposition group to automorphisms of the completion at an infinite place.** The action of
the decomposition group of the infinite place `w` on `w.Completion`, as a group homomorphism into
the ring automorphisms of the completion. -/
noncomputable def actHom : decomp E K w →* (w.Completion ≃+* w.Completion) where
  toFun := actRingEquiv
  map_one' := actRingEquiv_one
  map_mul' σ τ := actRingEquiv_mul σ τ

/-- The decomposition group of the infinite place `w` acts on `WithAbs w.1` through its action on
`K` (scoped in `NumberField.InfPlaceDecomp`). -/
noncomputable scoped instance instMulActionWithAbs : MulAction (decomp E K w) (WithAbs w.1) where
  one_smul y := by rw [WithAbs.smul_right_def]; rfl
  mul_smul σ τ y := by
    rw [WithAbs.smul_right_def, WithAbs.smul_right_def, WithAbs.smul_right_def]; rfl

/-- The action of the decomposition group on `WithAbs w.1` is additive (scoped in
`NumberField.InfPlaceDecomp`). -/
noncomputable scoped instance instDistribMulActionWithAbs : DistribMulAction (decomp E K w) (WithAbs
  w.1) where
  smul_zero σ := by rw [WithAbs.smul_right_def]; simp
  smul_add σ x y := by
    rw [WithAbs.smul_right_def, WithAbs.smul_right_def, WithAbs.smul_right_def]
    change WithAbs.toAbs _ ((σ : K ≃ₐ[E] K) (x.ofAbs + y.ofAbs)) = _
    rw [map_add]; rfl

/-- Each element of the decomposition group acts uniformly continuously on `WithAbs w.1` (scoped
in `NumberField.InfPlaceDecomp`). -/
noncomputable scoped instance instUniformContinuousConstSMul : UniformContinuousConstSMul (decomp E
  K w) (WithAbs w.1) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

/-- **Decomposition group acts on the completion at an infinite place.** The decomposition group
of the infinite place `w` acts on `w.Completion` by ring automorphisms, through `actRingEquiv`
(scoped in `NumberField.InfPlaceDecomp`). -/
noncomputable scoped instance instMulSemiringAction : MulSemiringAction (decomp E K w) w.Completion
  where
  smul σ x := actRingEquiv σ x
  one_smul x := by change actRingEquiv 1 x = x; rw [actRingEquiv_one]; rfl
  mul_smul σ τ x := by
    change actRingEquiv (σ * τ) x = actRingEquiv σ (actRingEquiv τ x); rw [actRingEquiv_mul]; rfl
  smul_zero σ := by change actRingEquiv σ 0 = 0; rw [map_zero]
  smul_add σ x y := by
    change actRingEquiv σ (x + y) = actRingEquiv σ x + actRingEquiv σ y
    rw [map_add]
  smul_one σ := by change actRingEquiv σ 1 = 1; rw [map_one]
  smul_mul σ x y := by
    change actRingEquiv σ (x * y) = actRingEquiv σ x * actRingEquiv σ y
    rw [map_mul]

/-- **The scoped action at an infinite place is the decomposition action.** The scoped action of the
decomposition group on `w.Completion` is `actRingEquiv`. -/
theorem smul_def (σ : decomp E K w) (x : w.Completion) : σ • x = actRingEquiv σ x := rfl

/-- Each element of the decomposition group acts continuously on `w.Completion` (scoped in
`NumberField.InfPlaceDecomp`). -/
scoped instance instContinuousConstSMul : ContinuousConstSMul (decomp E K w) w.Completion :=
  ⟨fun σ => continuous_actRingEquiv σ⟩

/-- The decomposition group of the infinite place `w` acts on the units of `w.Completion` through
its action on the completion (scoped in `NumberField.InfPlaceDecomp`). -/
noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K
  w) (w.Completion)ˣ :=
  Units.mulDistribMulActionRight

/-- The multiplicative action underlying `instMulDistribMulActionUnits`, as a direct instance
(scoped in `NumberField.InfPlaceDecomp`). -/
noncomputable scoped instance instMulActionUnits : MulAction (decomp E K w) (w.Completion)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction

/-- The scalar action underlying `instMulActionUnits`, as a direct instance (scoped in
`NumberField.InfPlaceDecomp`). -/
noncomputable scoped instance instSMulUnits : SMul (decomp E K w) (w.Completion)ˣ :=
  (instMulActionUnits (E := E) (K := K) (w := w)).toSMul

variable (E K w) in
/-- **Local units at an infinite place.** The units of the completion `w.Completion` at the
infinite place `w`, written additively, as a `ℤ`-linear representation of the decomposition
group of `w` acting on the completion. -/
noncomputable abbrev localUnits : Rep ℤ (decomp E K w) := Rep.ofMulDistribMulAction (decomp E K
  w) (w.Completion)ˣ

end NumberField.InfPlaceDecomp

namespace NumberField.ArchIdele

open scoped NumberField.InfPlaceDecomp

variable (E K : Type u) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

/-- **Chosen infinite place above an infinite place.** A choice, made with `Classical.choose`, of
an infinite place of `K` restricting to the infinite place `v` of `E` (see `comap_above`). -/
noncomputable def above (v : InfinitePlace E) : InfinitePlace K :=
  (InfinitePlace.comap_surjective (k := E) (K := K) v).choose

/-- **The chosen infinite place restricts to the given place.** The chosen infinite place
`above E K v` restricts to `v` on `E`. -/
theorem comap_above (v : InfinitePlace E) : (above E K v).comap (algebraMap E K) = v
  := (InfinitePlace.comap_surjective (k := E) (K := K) v).choose_spec

end NumberField.ArchIdele

open NumberField

namespace NumberField.InfinitePlaceTransport

variable {E K : Type*} [Field E] [Field K] [Algebra E K]

/-- If `σ • w = w'` for infinite places of `K`, then `w' (σ x) = w x` for every `x ∈ K`. -/
theorem apply_apply_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w') (x : K)
  : w' (σ x) = w x := by
  rw [← h, InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]

/-- **Galois automorphisms are uniformly continuous between infinite places.** If `σ • w = w'` for
infinite places, then `σ` is uniformly continuous from `WithAbs w.1` to `WithAbs w'.1`. -/
theorem uniformContinuous_congr_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w')
  :
    UniformContinuous (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq w.1 w'.1 _ (apply_apply_of_smul_eq h)

/-- **Transport between completions at infinite places.** For `σ : K ≃ₐ[E] K` with `σ • w = w'`,
the ring isomorphism `w.Completion ≃+* w'.Completion` extending `σ` by continuity: on the image
of `K` it is `σ` (`transport_coe`). -/
noncomputable def transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') : w.Completion
  ≃+* w'.Completion :=
  (AbsoluteValue.Completion.equiv w.1).trans
    ((UniformSpace.Completion.mapRingEquiv (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_smul_eq h).continuous
      ((uniformContinuous_congr_of_smul_eq (inv_smul_eq_iff.2 h.symm)).continuous.congr fun _ =>
        rfl)).trans
    (AbsoluteValue.Completion.equiv w'.1).symm)

/-- **Transport between infinite places through the underlying completions.** `transport σ h` is the
completion map of `σ` between the underlying uniform-space completions, wrapped back into
`w'.Completion`. -/
theorem transport_apply (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : w.Completion)
  :
    transport σ h x = AbsoluteValue.Completion.ofCompletion
      (UniformSpace.Completion.map (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
        (AbsoluteValue.Completion.toCompletion x)) := by
  rw [transport, RingEquiv.trans_apply, RingEquiv.trans_apply,
    AbsoluteValue.Completion.equiv_symm_apply, AbsoluteValue.Completion.equiv_apply]
  rfl

/-- **Transport between infinite places on elements of the field.** On the image of `K`,
`transport σ h` is `σ`: it sends the image of `x` in `w.Completion` to the image of `σ x` in
`w'.Completion`. -/
theorem transport_coe (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : WithAbs w.1) :
    transport σ h (x : w.Completion) = ((WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K) x
      : WithAbs w'.1) : w'.Completion) := by
  rw [transport_apply, AbsoluteValue.Completion.toCompletion_coe,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_smul_eq h),
    AbsoluteValue.Completion.ofCompletion_coe]

/-- **Continuity of the transport between infinite places.** The transport `transport σ h` between
completions at infinite places is continuous. -/
theorem continuous_transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w')
  : Continuous (transport σ h) := by
  rw [show (transport σ h : w.Completion → w'.Completion) = AbsoluteValue.Completion.ofCompletion ∘
      UniformSpace.Completion.map (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) ∘
        AbsoluteValue.Completion.toCompletion from funext (transport_apply σ h)]
  exact (AbsoluteValue.Completion.continuous_ofCompletion w'.1).comp
    (UniformSpace.Completion.continuous_map.comp
      (AbsoluteValue.Completion.continuous_toCompletion w.1))

/-- **Transport between local units at infinite places.** The group isomorphism
`(w.Completion)ˣ ≃* (w'.Completion)ˣ` induced by `transport σ h`. -/
noncomputable abbrev transportUnits (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') :
    (w.Completion)ˣ ≃* (w'.Completion)ˣ :=
  Units.mapEquiv (transport σ h).toMulEquiv

end NumberField.InfinitePlaceTransport

private theorem NumberField.InfinitePlaceTransport.transport_one (E K : Type*) [Field E] [Field
  K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (h : (1 : K ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (1 : K ≃ₐ[E] K) h = RingEquiv.refl w.Completion
      := by
  apply RingEquiv.ext
  intro x
  rw [RingEquiv.refl_apply]
  refine AbsoluteValue.Completion.induction_on x
    (isClosed_eq (NumberField.InfinitePlaceTransport.continuous_transport (1 : K ≃ₐ[E] K) h)
      continuous_id)
    fun a => ?_
  rw [NumberField.InfinitePlaceTransport.transport_coe]
  rfl

private theorem NumberField.InfinitePlaceTransport.transport_trans_transport (E K : Type*) [Field
  E] [Field K] [Algebra E K]
    (σ τ : K ≃ₐ[E] K) {w w' w'' : NumberField.InfinitePlace K}
    (h₁ : τ • w = w') (h₂ : σ • w' = w'') (h₃ : (σ * τ) • w = w'') :
    (NumberField.InfinitePlaceTransport.transport τ
      h₁).trans (NumberField.InfinitePlaceTransport.transport σ h₂)
      = NumberField.InfinitePlaceTransport.transport (σ * τ) h₃ := by
  apply RingEquiv.ext
  intro x
  change NumberField.InfinitePlaceTransport.transport σ
    h₂ (NumberField.InfinitePlaceTransport.transport τ h₁ x)
    = NumberField.InfinitePlaceTransport.transport (σ * τ) h₃ x
  refine AbsoluteValue.Completion.induction_on x
    (isClosed_eq
      ((NumberField.InfinitePlaceTransport.continuous_transport σ h₂).comp
        (NumberField.InfinitePlaceTransport.continuous_transport τ h₁))
      (NumberField.InfinitePlaceTransport.continuous_transport (σ * τ) h₃))
    fun a => ?_
  rw [NumberField.InfinitePlaceTransport.transport_coe,
    NumberField.InfinitePlaceTransport.transport_coe,
    NumberField.InfinitePlaceTransport.transport_coe]
  rfl

private theorem NumberField.InfinitePlaceTransport.transport_eq_actRingEquiv (E K : Type*) [Field
  E] [Field K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (σ : NumberField.InfPlaceDecomp.decomp E K w) (h : (σ : K
      ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (σ : K ≃ₐ[E] K) h =
      NumberField.InfPlaceDecomp.actRingEquiv σ :=
  rfl

/-! ### The stabilizer-to-orbit equivalence

Both main theorems are instances of one coinduction argument. It uses only the identity and
composition laws for transport between fibres and the transitivity of the action on the places
above `v`, never how a completion is built. A group `G` acts on a type `X`, `M` is a family of
commutative groups over `X`, and `T g h : M x ≃* M y` transports along `h : g • x = y`. When the
stabilizer `H` of a point `x₀` acts on `M x₀` by transport and `P` cuts out the orbit of `x₀`,
the module coinduced from `M x₀` is additively the product of the fibres over the orbit, and `g`
moves the component at `y'` to the component at `g • y'` by `T g`. -/

namespace StabilizerOrbitAux

variable {G : Type u} [Group G] {X : Type*} {M : X → Type u}
  [∀ x, CommGroup (M x)] {x₀ : X} {H : Subgroup G} [MulDistribMulAction H (M x₀)] {P : X → Prop}

-- The module coinduced from the action of `H` on `M x₀`.
variable (M x₀ H) in
private noncomputable abbrev Coind : Rep ℤ G :=
  Rep.coind H.subtype (Rep.ofMulDistribMulAction H (M x₀))

-- Evaluation of an element of the coinduced module.
private noncomputable def eval (f : Coind M x₀ H) (x : G) : M x₀ := Additive.toMul (f.1 x)

private theorem eval_add (f₁ f₂ : Coind M x₀ H) (x : G) :
    eval (f₁ + f₂) x = eval f₁ x * eval f₂ x := rfl

private theorem eval_mul_left (f : Coind M x₀ H) (d : H) (x : G) :
    eval f ((d : G) * x) = d • eval f x :=
  congrArg Additive.toMul ((Representation.mem_coindV _ _ _).1 f.2 d x)

variable [MulAction G X] (T : ∀ (g : G) {x y : X}, g • x = y → M x ≃* M y)
  (hone : ∀ {x : X} (h : (1 : G) • x = x) (u : M x), T 1 h u = u)
  (hmul : ∀ (σ τ : G) {x y z : X} (h₁ : τ • x = y) (h₂ : σ • y = z) (h₃ : (σ * τ) • x = z)
    (u : M x), T σ h₂ (T τ h₁ u) = T (σ * τ) h₃ u)
  (hact : ∀ (d : H) (h : (d : G) • x₀ = x₀) (u : M x₀), T d h u = d • u)
  (hstab : MulAction.stabilizer G x₀ = H)
  (horbit : ∀ y, P y ↔ y ∈ MulAction.orbit G x₀)

private theorem transport_congr {σ τ : G} (e : σ = τ) {x y : X} (h₁ : σ • x = y)
    (h₂ : τ • x = y) (u : M x) : T σ h₁ u = T τ h₂ u := by
  subst e; rfl

private theorem transport_congr_idx (u : Π y : {y // P y}, M y.1) {i₁ i₂ : {y // P y}}
    (e : i₁ = i₂) (σ : G) {t : X} (h₁ : σ • i₁.1 = t) (h₂ : σ • i₂.1 = t) :
    T σ h₁ (u i₁) = T σ h₂ (u i₂) := by
  subst e; rfl

include hone in
private theorem transport_one_idx (u : Π y : {y // P y}, M y.1) {i₁ i₂ : {y // P y}}
    (e : i₁ = i₂) (h : (1 : G) • i₁.1 = i₂.1) : T 1 h (u i₁) = u i₂ := by
  subst e
  exact hone h (u i₁)

include hstab in
private theorem smul_eq_of_mem (d : H) : (d : G) • x₀ = x₀ := by
  have hd : (d : G) ∈ MulAction.stabilizer G x₀ := by rw [hstab]; exact d.2
  exact hd

include hstab in
private theorem mem_of_smul_eq {g : G} (h : g • x₀ = x₀) : g ∈ H := by
  rw [← hstab]; exact h

include horbit in
private theorem mem_of_orbit (g : G) : P (g • x₀) := (horbit _).2 (MulAction.mem_orbit x₀ g)

include horbit in
private theorem exists_smul_eq_base (y : {y // P y}) : ∃ g : G, g • y.1 = x₀ := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 ((horbit y.1).1 y.2)
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

include hmul hact hstab in
private theorem indep (f : Coind M x₀ H) (x y : G) (w : X) (hx : x⁻¹ • x₀ = w)
    (hy : y⁻¹ • x₀ = w) : T y⁻¹ hy (eval f y) = T x⁻¹ hx (eval f x) := by
  have hd : y * x⁻¹ ∈ H := mem_of_smul_eq hstab (by rw [mul_smul, hx, ← hy, smul_inv_smul])
  obtain ⟨d, rfl⟩ : ∃ d : H, (d : G) * x = y := ⟨⟨y * x⁻¹, hd⟩, inv_mul_cancel_right y x⟩
  have hd1 : ((d⁻¹ : H) : G) • x₀ = x₀ := smul_eq_of_mem hstab d⁻¹
  rw [eval_mul_left, transport_congr T (show ((d : G) * x)⁻¹ = x⁻¹ * ((d⁻¹ : H) : G) by
        rw [mul_inv_rev]; rfl) hy (by rw [mul_smul]; exact (congrArg (x⁻¹ • ·) hd1).trans hx),
    ← hmul x⁻¹ ((d⁻¹ : H) : G) hd1 hx, hact, inv_smul_smul]

-- The inverse map: the value at `x` is the fibre at `x⁻¹ • x₀` transported back to `x₀`.
private noncomputable def bwdFun (u : Π y : {y // P y}, M y.1) : G → Additive (M x₀) :=
  fun x => Additive.ofMul (T x (smul_inv_smul x x₀) (u ⟨x⁻¹ • x₀, mem_of_orbit horbit x⁻¹⟩))

private theorem bwdFun_apply (u : Π y : {y // P y}, M y.1) (x : G) :
    Additive.toMul (bwdFun T horbit u x)
      = T x (smul_inv_smul x x₀) (u ⟨x⁻¹ • x₀, mem_of_orbit horbit x⁻¹⟩) := rfl

include hmul hact hstab in
private theorem bwdFun_mem (u : Π y : {y // P y}, M y.1) :
    bwdFun T horbit u ∈
      Representation.coindV H.subtype (Rep.ofMulDistribMulAction H (M x₀)).ρ := by
  refine (Representation.mem_coindV _ _ _).2 fun d x => ?_
  apply Additive.toMul.injective
  change Additive.toMul (bwdFun T horbit u ((d : G) * x)) = d • Additive.toMul (bwdFun T horbit u x)
  have hidx : (⟨((d : G) * x)⁻¹ • x₀, mem_of_orbit horbit ((d : G) * x)⁻¹⟩ : {y // P y}) =
      ⟨x⁻¹ • x₀, mem_of_orbit horbit x⁻¹⟩ := by
    apply Subtype.ext
    change ((d : G) * x)⁻¹ • x₀ = x⁻¹ • x₀
    rw [mul_inv_rev, mul_smul]
    exact congrArg (x⁻¹ • ·) (smul_eq_of_mem hstab d⁻¹)
  rw [bwdFun_apply, bwdFun_apply, transport_congr_idx T u hidx ((d : G) * x) _
      (by rw [mul_smul, smul_inv_smul]; exact smul_eq_of_mem hstab d),
    ← hmul (d : G) x (smul_inv_smul x _) (smul_eq_of_mem hstab d), hact]

private noncomputable def bwd (u : Π y : {y // P y}, M y.1) : Coind M x₀ H :=
  ⟨bwdFun (M := M) (x₀ := x₀) T horbit u, bwdFun_mem T hmul hact hstab horbit u⟩

-- A chosen transporter from each point of the orbit to `x₀`.
private noncomputable def sel (y : {y // P y}) : G := (exists_smul_eq_base horbit y).choose

private theorem sel_smul (y : {y // P y}) : sel horbit y • y.1 = x₀ :=
  (exists_smul_eq_base horbit y).choose_spec

private theorem inv_sel_smul (y : {y // P y}) : (sel horbit y)⁻¹ • x₀ = y.1 :=
  inv_smul_eq_iff.2 (sel_smul horbit y).symm

-- The forward map: the component at `y` is the value at the chosen transporter, moved to `y`.
private noncomputable def fwd (f : Coind M x₀ H) : Π y : {y // P y}, M y.1 :=
  fun y => T (sel horbit y)⁻¹ (inv_sel_smul horbit y) (eval f (sel horbit y))

include hmul hact hstab in
private theorem fwd_eq (f : Coind M x₀ H) (y : {y // P y}) (g : G) (hg : g • y.1 = x₀) :
    fwd T horbit f y = T g⁻¹ (inv_smul_eq_iff.2 hg.symm) (eval f g) :=
  indep T hmul hact hstab f g (sel horbit y) y.1 _ (inv_sel_smul horbit y)

private theorem fwd_add (f₁ f₂ : Coind M x₀ H) (y : {y // P y}) :
    fwd T horbit (f₁ + f₂) y = fwd T horbit f₁ y * fwd T horbit f₂ y := by
  change T _ _ (eval (f₁ + f₂) (sel horbit y)) = _
  rw [eval_add, map_mul]
  rfl

include hmul hact hstab in
private theorem fwd_ρ (g : G) (f : Coind M x₀ H) (y y' : {y // P y}) (h : g • y'.1 = y.1) :
    fwd T horbit ((Coind M x₀ H).ρ g f) y = T g h (fwd T horbit f y') := by
  have hy : (sel horbit y * g) • y'.1 = x₀ := by rw [mul_smul, h, sel_smul]
  rw [fwd_eq T hmul hact hstab horbit f y' (sel horbit y * g) hy,
    hmul g (sel horbit y * g)⁻¹ (inv_smul_eq_iff.2 hy.symm) h
      (by rw [mul_inv_rev, mul_inv_cancel_left]; exact inv_sel_smul horbit y),
    transport_congr T (show g * (sel horbit y * g)⁻¹ = (sel horbit y)⁻¹ by
      rw [mul_inv_rev, mul_inv_cancel_left]) _ (inv_sel_smul horbit y)]
  rfl

include hone hmul hact hstab in
private theorem fwd_bwd (u : Π y : {y // P y}, M y.1) (y : {y // P y}) :
    fwd T horbit (bwd T hmul hact hstab horbit u) y = u y := by
  have hidx : (⟨(sel horbit y)⁻¹ • x₀, mem_of_orbit horbit (sel horbit y)⁻¹⟩ : {y // P y}) = y :=
    Subtype.ext (inv_sel_smul horbit y)
  change T (sel horbit y)⁻¹ (inv_sel_smul horbit y)
    (Additive.toMul (bwdFun T horbit u (sel horbit y))) = u y
  rw [bwdFun_apply, hmul (sel horbit y)⁻¹ (sel horbit y) (smul_inv_smul (sel horbit y) _)
      (inv_sel_smul horbit y) (by rw [inv_mul_cancel, one_smul]; exact inv_sel_smul horbit y),
    transport_congr T (inv_mul_cancel (sel horbit y)) _
      (by rw [one_smul]; exact inv_sel_smul horbit y)]
  exact transport_one_idx T hone u hidx _

include hone hmul hact hstab in
private theorem bwd_fwd (f : Coind M x₀ H) : bwd T hmul hact hstab horbit (fwd T horbit f) = f := by
  apply Subtype.ext
  funext x
  apply Additive.toMul.injective
  change Additive.toMul (bwdFun T horbit (fwd T horbit f) x) = eval f x
  rw [bwdFun_apply, fwd_eq T hmul hact hstab horbit f ⟨x⁻¹ • x₀, mem_of_orbit horbit x⁻¹⟩ x
      (smul_inv_smul x _),
    hmul x x⁻¹ _ (smul_inv_smul x _) (by rw [mul_inv_cancel, one_smul]),
    transport_congr T (mul_inv_cancel x) _ (one_smul _ _), hone]

-- The stabilizer-to-orbit equivalence.
private noncomputable def coindEquiv : Coind M x₀ H ≃+ Additive (Π y : {y // P y}, M y.1) where
  toFun f := Additive.ofMul (fwd T horbit f)
  invFun a := bwd T hmul hact hstab horbit (Additive.toMul a)
  left_inv f := bwd_fwd T hone hmul hact hstab horbit f
  right_inv a := congrArg Additive.ofMul
    (funext (fwd_bwd T hone hmul hact hstab horbit (Additive.toMul a)))
  map_add' f₁ f₂ := congrArg Additive.ofMul (funext (fwd_add T horbit f₁ f₂))

include hone hmul hact hstab in
-- The equivalence moves the component at `y'` to the component at `g • y'` by `T g`.
private theorem coindEquiv_ρ (g : G) (f : Coind M x₀ H) (y y' : {y // P y})
    (h : g • y'.1 = y.1) :
    Additive.toMul (coindEquiv T hone hmul hact hstab horbit ((Coind M x₀ H).ρ g f)) y =
      T g h (Additive.toMul (coindEquiv T hone hmul hact hstab horbit f) y') :=
  fwd_ρ T hmul hact hstab horbit g f y y' h

include hone hmul hact hstab horbit in
-- The two main theorems in abstract form.
private theorem exists_coindEquiv :
    ∃ e : Coind M x₀ H ≃+ Additive (Π y : {y // P y}, M y.1),
      ∀ (g : G) (f : Coind M x₀ H) (y y' : {y // P y}) (h : g • y'.1 = y.1),
        Additive.toMul (e ((Coind M x₀ H).ρ g f)) y = T g h (Additive.toMul (e f) y') :=
  ⟨coindEquiv T hone hmul hact hstab horbit, coindEquiv_ρ T hone hmul hact hstab horbit⟩

end StabilizerOrbitAux

namespace FiniteCoindAux

open NumberField NumberField.PlaceTransport IsDedekindDomain
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

section general

variable {E K : Type u} [Field E] [Field K] [NumberField K] [Algebra E K]

private theorem transportUnits_trans (σ τ : K ≃ₐ[E] K) {w w' w'' : HeightOneSpectrum (𝓞 K)} (h₁ : τ
  • w = w') (h₂ : σ • w' = w'')
    (h₃ : (σ * τ) • w = w'') (u : (w.adicCompletion K)ˣ) :
    transportUnits σ h₂ (transportUnits τ h₁ u) = transportUnits (σ * τ) h₃ u := by
  ext : 1
  change transport σ h₂ (transport τ h₁ (u : w.adicCompletion K)) = transport (σ * τ) h₃ (u
    : w.adicCompletion K)
  rw [← NumberField.PlaceTransport.transport_trans_transport E K σ τ h₁ h₂ h₃]
  rfl

private theorem transportUnits_one {w : HeightOneSpectrum (𝓞 K)} (h : (1 : K ≃ₐ[E] K) • w = w) (u
  : (w.adicCompletion K)ˣ) :
    transportUnits (1 : K ≃ₐ[E] K) h u = u := by
  ext : 1
  change transport (1 : K ≃ₐ[E] K) h (u : w.adicCompletion K) = u
  rw [NumberField.PlaceTransport.transport_one E K w h]
  rfl

private theorem transportUnits_eq_smul {w : HeightOneSpectrum (𝓞 K)} (d : PlaceDecomp.decomp E K
  w) (h : (d : K ≃ₐ[E] K) • w = w)
    (u : (w.adicCompletion K)ˣ) : transportUnits (d : K ≃ₐ[E] K) h u = d • u := by
  ext : 1
  change transport (d : K ≃ₐ[E] K) h (u : w.adicCompletion K) = ((d • u : (w.adicCompletion K)ˣ)
    : w.adicCompletion K)
  rw [NumberField.PlaceTransport.transport_eq_actRingEquiv E K w d h, Units.coe_smul,
    PlaceDecomp.smul_def]

end general

variable (E K : Type u) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

omit [NumberField K] in
private theorem under_above (v : HeightOneSpectrum (𝓞 E)) : (PlaceAbove.above E K v).under (𝓞 E) = v
  :=
  HeightOneSpectrum.ext
    (by rw [HeightOneSpectrum.under_asIdeal]; exact PlaceAbove.comap_above E K v)

-- The finite places above `v` form the orbit of the chosen place.
private theorem mem_orbit_iff [IsGalois E K] (v : HeightOneSpectrum (𝓞 E))
    (w : HeightOneSpectrum (𝓞 K)) :
    w.under (𝓞 E) = v ↔ w ∈ MulAction.orbit (K ≃ₐ[E] K) (PlaceAbove.above E K v) := by
  rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq E K, Set.mem_ofPred_eq, under_above]

end FiniteCoindAux

open scoped NumberField.PlaceDecomp NumberField.PlaceTransport


/-- **Semilocal coinduced local units at a finite place.** Let `K / E` be a Galois extension of
number fields, `v` a finite place of `E`, `w₀ = PlaceAbove.above E K v` and `D = D E K v` its
decomposition group. The representation of `K ≃ₐ[E] K` coinduced from the `D`-representation
`localUnits E K v` on the units of `w₀.adicCompletion K` is additively isomorphic to the product
of the units of `w.adicCompletion K` over all finite places `w` of `K` above `v`, compatibly
with the Galois action: for `g : K ≃ₐ[E] K` and places `w`, `w'` above `v` with `g • w' = w`,
the `w`-component of the image of `g • f` is the transport along `g` of the `w'`-component of
the image of `f`. -/
theorem NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits (E K : Type u) [Field
  E] [NumberField E] [Field K]
    [NumberField K] [Algebra E K] [IsGalois E K] (v
      : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    ∃ e : (Rep.coind (NumberField.FiniteSIdele.D E K v).subtype (NumberField.FiniteSIdele.localUnits
      E K v))
          ≃+ Additive (Π w : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)
            //
                            w.under (NumberField.RingOfIntegers E) = v}, (w.1.adicCompletion K)ˣ),
      ∀ (g : K ≃ₐ[E] K) (f : Rep.coind (NumberField.FiniteSIdele.D E K
        v).subtype (NumberField.FiniteSIdele.localUnits E K v))
        (w w' : {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
                  w.under (NumberField.RingOfIntegers E) = v})
        (h : g • w'.1 = w.1),
        Additive.toMul (e ((Rep.coind (NumberField.FiniteSIdele.D E K v).subtype
          (NumberField.FiniteSIdele.localUnits E K v)).ρ g f)) w
          = NumberField.PlaceTransport.transportUnits g h (Additive.toMul (e f) w') :=
  by
  have h := StabilizerOrbitAux.exists_coindEquiv (M := fun w => (w.adicCompletion K)ˣ)
    (x₀ := NumberField.PlaceAbove.above E K v) (H := NumberField.FiniteSIdele.D E K v)
    (P := fun w => w.under (NumberField.RingOfIntegers E) = v)
    NumberField.PlaceTransport.transportUnits FiniteCoindAux.transportUnits_one
    FiniteCoindAux.transportUnits_trans FiniteCoindAux.transportUnits_eq_smul
    (NumberField.PlaceTransport.stabilizer_eq_decomp E K _) (FiniteCoindAux.mem_orbit_iff E K v)
  exact h


namespace ArchCoindAux

open NumberField NumberField.InfinitePlaceTransport
open scoped NumberField.InfPlaceDecomp

section general

variable {E K : Type u} [Field E] [Field K] [Algebra E K]

private theorem comap_smul_algebraMap (σ : K ≃ₐ[E] K) (w : InfinitePlace K) :
    (σ • w).comap (algebraMap E K) = w.comap (algebraMap E K) := by
  rw [InfinitePlace.smul_eq_comap, ← InfinitePlace.comap_comp]
  congr 1
  exact RingHom.ext fun x => σ.symm.commutes x

private theorem transportUnits_trans (σ τ : K ≃ₐ[E] K) {w w' w'' : InfinitePlace K} (h₁ : τ • w =
  w') (h₂ : σ • w' = w'')
    (h₃ : (σ * τ) • w = w'') (u : (w.Completion)ˣ) :
    transportUnits σ h₂ (transportUnits τ h₁ u) = transportUnits (σ * τ) h₃ u := by
  ext : 1
  change transport σ h₂ (transport τ h₁ (u : w.Completion)) = transport (σ * τ) h₃ (u
    : w.Completion)
  rw [← NumberField.InfinitePlaceTransport.transport_trans_transport E K σ τ h₁ h₂ h₃]
  rfl

private theorem transportUnits_one {w : InfinitePlace K} (h : (1 : K ≃ₐ[E] K) • w = w) (u
  : (w.Completion)ˣ) :
    transportUnits (1 : K ≃ₐ[E] K) h u = u := by
  ext : 1
  change transport (1 : K ≃ₐ[E] K) h (u : w.Completion) = u
  rw [NumberField.InfinitePlaceTransport.transport_one E K w h]
  rfl

private theorem transportUnits_eq_smul {w : InfinitePlace K} (d : InfPlaceDecomp.decomp E K w) (h
  : (d : K ≃ₐ[E] K) • w = w)
    (u : (w.Completion)ˣ) : transportUnits (d : K ≃ₐ[E] K) h u = d • u := by
  ext : 1
  change transport (d : K ≃ₐ[E] K) h (u : w.Completion) = ((d • u : (w.Completion)ˣ) : w.Completion)
  rw [NumberField.InfinitePlaceTransport.transport_eq_actRingEquiv E K w d h,
    Units.coe_smul,
    InfPlaceDecomp.smul_def]

end general

variable (E K : Type u) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

-- The infinite places above `v` form the orbit of the chosen place.
private theorem mem_orbit_iff [IsGalois E K] (v : InfinitePlace E) (w : InfinitePlace K) :
    w.comap (algebraMap E K) = v ↔ w ∈ MulAction.orbit (K ≃ₐ[E] K) (ArchIdele.above E K v) := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq
      (h.trans (ArchIdele.comap_above E K v).symm)
    exact MulAction.mem_orbit_iff.2 ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩
  · intro h
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 h
    exact (comap_smul_algebraMap g _).trans (ArchIdele.comap_above E K v)

end ArchCoindAux


/-- **Semilocal coinduced local units at an infinite place.** Let `K / E` be a Galois extension of
number fields, `v` an infinite place of `E`, and `w₀ = ArchIdele.above E K v` with
decomposition group `D`. The representation of `K ≃ₐ[E] K` coinduced from the
`D`-representation on the units of `w₀.Completion` is additively isomorphic to the product of
the units of `w.Completion` over all infinite places `w` of `K` above `v`, compatibly with the
Galois action: for `g : K ≃ₐ[E] K` and places `w`, `w'` above `v` with `g • w' = w`, the
`w`-component of the image of `g • f` is the transport along `g` of the `w'`-component of the
image of `f`. -/
theorem NumberField.ArchIdele.exists_addEquiv_coind_localUnits (E K : Type u) [Field E]
    [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : NumberField.InfinitePlace E) :
    ∃ e : (Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K
      v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v))) ≃+
        Additive (Π w : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v},
          (w.1.Completion)ˣ),
      ∀ (g : K ≃ₐ[E] K)
        (f : Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K
          v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)))
        (w w' : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v}) (h : g • w'.1 =
          w.1),
        Additive.toMul (e ((Rep.coind (NumberField.InfPlaceDecomp.decomp E
          K (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v))).ρ g f)) w
            =
          NumberField.InfinitePlaceTransport.transportUnits g h (Additive.toMul (e f) w') :=
  by
  open scoped NumberField.InfPlaceDecomp in
  have h := StabilizerOrbitAux.exists_coindEquiv (M := fun w => (w.Completion)ˣ)
    (x₀ := NumberField.ArchIdele.above E K v)
    (H := NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v))
    (P := fun w => w.comap (algebraMap E K) = v)
    NumberField.InfinitePlaceTransport.transportUnits ArchCoindAux.transportUnits_one
    ArchCoindAux.transportUnits_trans ArchCoindAux.transportUnits_eq_smul rfl
    (ArchCoindAux.mem_orbit_iff E K v)
  exact h
