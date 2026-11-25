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
`Theorems/Thm_NumberField_FiniteSIdele_exists_addEquiv_coind_localUnits.lean`,
`Theorems/Thm_NumberField_ArchIdele_exists_addEquiv_coind_localUnits.lean`
and the corresponding files in `P2M/Sol/`
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
-/

module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Invariant.Basic

@[expose] public section



open IsDedekindDomain NumberField

namespace NumberField.PlaceAbove

variable (E K : Type*) [Field E] [NumberField E] [Field K] [Algebra E K]

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

noncomputable def above (v : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 K) := (exists_above E K
  v).choose

theorem comap_above (v : HeightOneSpectrum (𝓞 E)) :
    (above E K v).asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := (exists_above E K
      v).choose_spec

end NumberField.PlaceAbove

open IsDedekindDomain NumberField
open scoped Pointwise

namespace NumberField.PlaceDecomp

section general
variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

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

theorem le_exp_neg_one_of_lt_one {t : WithZero (Multiplicative ℤ)} (ht : t < 1) : t ≤
  WithZero.exp (-1) := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at ht ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ht
    rw [WithZero.exp_le_exp]
    omega

theorem apply_eq_of_isEquiv_comap (v : Valuation K (WithZero (Multiplicative ℤ))) (f : K ≃+* K)
    (hf : v.IsEquiv (v.comap (f : K →+* K))) (hπ : ∃ π : K,
      v π = WithZero.exp (-1)) (x : K) : v (f x) = v x := by
  have hle : ∀ a b : K, v a ≤ v b ↔ v (f a) ≤ v (f b) := fun a b => hf a b
  have step1 : ∀ (g : K ≃+* K), (∀ a b : K, v a ≤ v b ↔ v (g a) ≤ v (g b)) → ∀ π : K,
    v π = WithZero.exp (-1) →
      v (g π) = WithZero.exp (-1) := by
    intro g hg π hπ
    have hπ1 : v π < 1 := by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    apply le_antisymm
    · apply le_exp_neg_one_of_lt_one
      have : ¬ v (g 1) ≤ v (g π) := fun h => (not_le.2 hπ1) (by simpa using (hg 1 π).2 h)
      simpa using not_le.1 this
    · have hy : v (g (g.symm π)) = WithZero.exp (-1) := by rw [g.apply_symm_apply, hπ]
      have hy1 : v (g.symm π) < 1 := by
        have : ¬ v (g 1) ≤ v (g (g.symm π)) := by
          rw [map_one, map_one, hy, not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
        have : ¬ v 1 ≤ v (g.symm π) := fun h => this ((hg _ _).1 h)
        simpa using not_le.1 this
      have := (hg (g.symm π) π).1 ((le_exp_neg_one_of_lt_one hy1).trans hπ.ge)
      rwa [hy] at this
  obtain ⟨π, hvπ⟩ := hπ
  have hfπ : v (f π) = WithZero.exp (-1) := step1 f hle π hvπ
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · set m : ℤ := WithZero.log (v x) with hm
    have hvx : v x = WithZero.exp m := (WithZero.exp_log ((map_ne_zero v).2 hx)).symm
    have hz : v (π ^ (-m)) = WithZero.exp m := by
      rw [map_zpow₀, hvπ, ← WithZero.exp_zsmul]
      congr 1
      simp
    have hfz : v (f (π ^ (-m))) = WithZero.exp m := by
      rw [map_zpow₀, map_zpow₀, hfπ, ← WithZero.exp_zsmul]
      congr 1
      simp
    have h1 : v (f x) ≤ v (f (π ^ (-m))) := (hle _ _).1 (by rw [hvx, hz])
    have h2 : v (f (π ^ (-m))) ≤ v (f x) := (hle _ _).1 (by rw [hvx, hz])
    rw [hvx]
    exact le_antisymm (h1.trans hfz.le) (hfz.ge.trans h2)

end general

variable (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞
  K))

noncomputable abbrev decomp : Subgroup (K ≃ₐ[E] K) := ((w.valuation
  K).valuationSubring).decompositionSubgroup E

variable {E K w}

theorem isEquiv_comap_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    (w.valuation K).IsEquiv ((w.valuation K).comap (σ : K →+* K)) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [MulAction.mem_stabilizer_iff] at hσ
  have : σ • x ∈ σ • (w.valuation K).valuationSubring ↔ x ∈ (w.valuation K).valuationSubring :=
    ValuationSubring.smul_mem_pointwise_smul_iff
  rw [hσ, Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff] at this
  rw [Valuation.comap_apply]
  exact this.symm

theorem valuation_apply_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) (x : K) :
    w.valuation K (σ x) = w.valuation K x :=
  apply_eq_of_isEquiv_comap (w.valuation K) (σ : K ≃+* K) (isEquiv_comap_of_mem σ
    hσ) (w.valuation_exists_uniformizer K) x

theorem uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    UniformContinuous (WithVal.congr (w.valuation K) (w.valuation K) (σ : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq (w.valuation K) (σ : K ≃+* K) (valuation_apply_of_mem σ hσ)

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

theorem actRingEquiv_apply (σ : decomp E K w) (x : w.adicCompletion K) :
    (actRingEquiv σ x).toCompletion
      = UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K)
        : K ≃+* K)) x.toCompletion :=
  rfl

theorem actRingEquiv_coe (σ : decomp E K w) (x : WithVal (w.valuation K)) :
    actRingEquiv σ (x : w.adicCompletion K)
      = ((WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K) x
        : WithVal (w.valuation K)) : w.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  rw [actRingEquiv_apply, HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]

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

noncomputable def actHom : decomp E K w →* (w.adicCompletion K ≃+* w.adicCompletion K) where
  toFun := actRingEquiv
  map_one' := actRingEquiv_one
  map_mul' σ τ := actRingEquiv_mul σ τ

theorem smul_withVal_def (σ : decomp E K w) (y : WithVal (w.valuation K)) :
    σ • y = WithVal.toVal (w.valuation K) ((σ : K ≃ₐ[E] K) y.ofVal) := rfl

noncomputable scoped instance instMulActionWithVal : MulAction (decomp E K w) (WithVal (w.valuation
  K)) where
  one_smul y := by rw [smul_withVal_def]; rfl
  mul_smul σ τ y := by rw [smul_withVal_def, smul_withVal_def, smul_withVal_def]; rfl

noncomputable scoped instance instDistribMulActionWithVal : DistribMulAction (decomp E K
  w) (WithVal (w.valuation K)) where
  smul_zero σ := by rw [smul_withVal_def]; simp
  smul_add σ x y := by
    rw [smul_withVal_def, smul_withVal_def, smul_withVal_def]
    change WithVal.toVal _ ((σ : K ≃ₐ[E] K) (x.ofVal + y.ofVal)) = _
    rw [map_add]; rfl

noncomputable scoped instance instUniformContinuousConstSMul :
    UniformContinuousConstSMul (decomp E K w) (WithVal (w.valuation K)) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

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

theorem smul_def (σ : decomp E K w) (x : w.adicCompletion K) : σ • x = actRingEquiv σ x := rfl

noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K
  w) (w.adicCompletion K)ˣ :=
  Units.mulDistribMulActionRight

theorem coe_smul_units (σ : decomp E K w) (u : (w.adicCompletion K)ˣ) : ((σ • u : (w.adicCompletion
  K)ˣ) : w.adicCompletion K) = σ • (u : w.adicCompletion K) := rfl

section integers

open WithZeroTopology in
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
  exact valuation_apply_of_mem (σ : K ≃ₐ[E] K) σ.2 a.ofVal

theorem valued_smul (σ : decomp E K w) (x : w.adicCompletion K) : Valued.v (σ • x) = Valued.v x :=
  valued_actRingEquiv σ x

theorem smul_mem_adicCompletionIntegers_iff (σ : decomp E K w) (x : w.adicCompletion K) :
    σ • x ∈ w.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    valued_smul]

noncomputable scoped instance instSMulIntegers : SMul (decomp E K w) (w.adicCompletionIntegers K) :=
  ⟨fun σ x => ⟨σ • (x : w.adicCompletion K), (smul_mem_adicCompletionIntegers_iff σ _).2 x.2⟩⟩

theorem coe_smul_integers (σ : decomp E K w) (x : w.adicCompletionIntegers K) :
    ((σ • x : w.adicCompletionIntegers K) : w.adicCompletion K) = σ • (x : w.adicCompletion K)
      := rfl

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

noncomputable scoped instance instMulDistribMulActionIntegerUnits : MulDistribMulAction (decomp E K
  w) (w.adicCompletionIntegers K)ˣ :=
  Units.mulDistribMulActionRight

noncomputable scoped instance instMulActionIntegers : MulAction (decomp E K
  w) (w.adicCompletionIntegers K) :=
  (instMulSemiringActionIntegers (E := E) (K := K) (w := w)).toMulAction

noncomputable scoped instance instSMulUnits : SMul (decomp E K w) (w.adicCompletion K)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction.toSMul

noncomputable scoped instance instSMulIntegerUnits : SMul (decomp E K w) (w.adicCompletionIntegers
  K)ˣ :=
  (instMulDistribMulActionIntegerUnits (E := E) (K := K) (w := w)).toMulAction.toSMul

noncomputable scoped instance instMulActionUnits : MulAction (decomp E K w) (w.adicCompletion K)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction

noncomputable scoped instance instMulActionIntegerUnits : MulAction (decomp E K
  w) (w.adicCompletionIntegers K)ˣ :=
  (instMulDistribMulActionIntegerUnits (E := E) (K := K) (w := w)).toMulAction

end integers

end NumberField.PlaceDecomp

open IsDedekindDomain NumberField

namespace NumberField.PlaceTransport

section general
variable {R S : Type*} [Field R] [Field S] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

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

theorem smul_asIdeal (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    (σ • w).asIdeal = w.asIdeal.comap (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹ : 𝓞 K →+*
      𝓞 K) := rfl

theorem mem_smul_asIdeal_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ (σ • w).asIdeal ↔ σ⁻¹ • x ∈ w.asIdeal := Iff.rfl

theorem smul_mem_smul_asIdeal_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    σ • x ∈ (σ • w).asIdeal ↔ x ∈ w.asIdeal := by
  rw [mem_smul_asIdeal_iff, inv_smul_smul]

theorem smul_asIdeal_eq_map (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    (σ • w).asIdeal = Ideal.map ((MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ : 𝓞 K ≃+* 𝓞 K)
      : 𝓞 K →+* 𝓞 K) w.asIdeal := by
  rw [Ideal.map_comap_of_equiv]
  ext x
  rw [mem_smul_asIdeal_iff, Ideal.mem_comap, MulSemiringAction.toRingEquiv_apply_symm_apply]

theorem smul_mem_smul_asIdeal_pow_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (n
  : ℕ) :
    σ • x ∈ (σ • w).asIdeal ^ n ↔ x ∈ w.asIdeal ^ n := by
  rw [smul_asIdeal_eq_map, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap,
    MulSemiringAction.toRingEquiv_apply_symm_apply,
    inv_smul_smul]

theorem inv_smul_eq_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w')
  : σ⁻¹ • w' = w := by
  rw [← h, inv_smul_smul]

variable [NumberField K]

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

theorem valuation_smul_apply (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    (σ • w).valuation K (σ x) = w.valuation K x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h1 : ∀ c : 𝓞 K, σ (algebraMap (𝓞 K) K c) = algebraMap (𝓞 K) K (σ • c) := fun c => rfl
  rw [map_div₀, map_div₀, map_div₀, h1, h1, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      intValuation_smul_apply,
    intValuation_smul_apply]

theorem valuation_apply_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w =
  w') (x : K) :
    w'.valuation K (σ x) = w.valuation K x := by
  subst h
  exact valuation_smul_apply σ w x

theorem uniformContinuous_congr_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ •
  w = w') :
    UniformContinuous (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K))
      :=
  uniformContinuous_congr_of_forall_eq (w.valuation K) (w'.valuation K) (w.valuation_surjective K)
    _ (valuation_apply_of_smul_eq h)

noncomputable def transport (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    w.adicCompletion K ≃+* w'.adicCompletion K :=
  ((HeightOneSpectrum.adicCompletion.equiv K w).trans
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K
      ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_smul_eq h).continuous
      ((uniformContinuous_congr_of_smul_eq (inv_smul_eq_of_smul_eq h)).continuous.congr fun _ =>
        rfl))).trans
    (HeightOneSpectrum.adicCompletion.equiv K w').symm

theorem transport_apply (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x
  : w.adicCompletion K) :
    (transport σ h x).toCompletion
      = UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K)
        : K ≃+* K)) x.toCompletion :=
  rfl

theorem transport_coe (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x
  : WithVal (w.valuation K)) :
    transport σ h (x : w.adicCompletion K)
      = ((WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K) x
        : WithVal (w'.valuation K)) : w'.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  rw [transport_apply, HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_smul_eq h)]

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

theorem transport_mem_adicCompletionIntegers_iff (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h
  : σ • w = w')
    (x : w.adicCompletion K) : transport σ h x ∈ w'.adicCompletionIntegers K ↔ x ∈
      w.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    valued_transport]

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

theorem coe_transportIntegers (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x
  : w.adicCompletionIntegers K) :
    ((transportIntegers σ h x : w'.adicCompletionIntegers K) : w'.adicCompletion K) = transport σ
      h (x : w.adicCompletion K) := rfl

noncomputable abbrev transportUnits (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w =
  w') :
    (w.adicCompletion K)ˣ ≃* (w'.adicCompletion K)ˣ :=
  Units.mapEquiv (transport σ h).toMulEquiv

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
        (NumberField.PlaceTransport.inv_smul_eq_of_smul_eq h)]
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
      exact NumberField.PlaceDecomp.valuation_apply_of_mem σ⁻¹ hσ' (algebraMap _ K x)
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

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

noncomputable abbrev D (v : HeightOneSpectrum (𝓞 E)) : Subgroup (K ≃ₐ[E] K) :=
  NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)

section local_modules

noncomputable abbrev localUnits (v : HeightOneSpectrum (𝓞 E)) : Rep ℤ (D E K v) :=
  Rep.ofMulDistribMulAction (D E K v) ((NumberField.PlaceAbove.above E K v).adicCompletion K)ˣ

noncomputable abbrev localIntegerUnits (v : HeightOneSpectrum (𝓞 E)) : Rep ℤ (D E K v) :=
  Rep.ofMulDistribMulAction (D E K v) ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers
    K)ˣ

noncomputable def integerUnitsToUnits (v : HeightOneSpectrum (𝓞 E)) : localIntegerUnits E K v ⟶
  localUnits E K v :=
  Rep.ofHom ⟨(Units.map ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers
    K).subtype.toMonoidHom).toAdditive.toIntLinearMap,
    fun _ => rfl⟩

theorem integerUnitsToUnits_hom_apply (v : HeightOneSpectrum (𝓞 E)) (u
  : ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K)ˣ) :
    Additive.toMul ((integerUnitsToUnits E K v).hom (Additive.ofMul u))
      = Units.map ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers
        K).subtype.toMonoidHom u := rfl

end local_modules



end NumberField.FiniteSIdele

open NumberField

namespace NumberField.InfPlaceDecomp

section general
variable {K : Type*} [Field K]

theorem uniformContinuous_congr_of_forall_eq (v : AbsoluteValue K ℝ) (f : K ≃+* K) (h : ∀ x,
  v (f x) = v x) :
    UniformContinuous (WithAbs.congr v v f) :=
  (AddMonoidHomClass.isometry_of_norm (WithAbs.congr v v f) fun x => by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
    exact h _).uniformContinuous

end general

variable (E K : Type*) [Field E] [Field K] [Algebra E K] (w : InfinitePlace K)

abbrev decomp : Subgroup (K ≃ₐ[E] K) := MulAction.stabilizer (K ≃ₐ[E] K) w

variable {E K w}

theorem apply_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) (x : K) : w (σ x) = w x := by
  rw [MulAction.mem_stabilizer_iff] at hσ
  conv_lhs => rw [← hσ]
  rw [InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]

theorem uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    UniformContinuous (WithAbs.congr w.1 w.1 (σ : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq w.1 (σ : K ≃+* K) (apply_of_mem σ hσ)

noncomputable def actRingEquiv (σ : decomp E K w) : w.Completion ≃+* w.Completion :=
  ((AbsoluteValue.Completion.equiv w.1).trans
    (UniformSpace.Completion.mapRingEquiv (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2).continuous
      (by
        rw [WithAbs.congr_symm]
        exact (uniformContinuous_congr_of_mem ((σ⁻¹ : decomp E K w) : K ≃ₐ[E]
          K) (σ⁻¹).2).continuous))).trans
    (AbsoluteValue.Completion.equiv w.1).symm

theorem actRingEquiv_apply (σ : decomp E K w) (x : w.Completion) :
    AbsoluteValue.Completion.toCompletion (actRingEquiv σ x) =
      UniformSpace.Completion.map (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
        (AbsoluteValue.Completion.toCompletion x) := by
  rw [actRingEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    AbsoluteValue.Completion.equiv_symm_apply, AbsoluteValue.Completion.toCompletion_ofCompletion,
    AbsoluteValue.Completion.equiv_apply]
  rfl

theorem actRingEquiv_coe (σ : decomp E K w) (x : WithAbs w.1) :
    actRingEquiv σ (x : w.Completion) = ((WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K) x
      : WithAbs w.1) : w.Completion) := by
  apply AbsoluteValue.Completion.toCompletion_injective w.1
  rw [actRingEquiv_apply, AbsoluteValue.Completion.toCompletion_coe,
    AbsoluteValue.Completion.toCompletion_coe,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]

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

noncomputable def actHom : decomp E K w →* (w.Completion ≃+* w.Completion) where
  toFun := actRingEquiv
  map_one' := actRingEquiv_one
  map_mul' σ τ := actRingEquiv_mul σ τ

theorem smul_withAbs_def (σ : decomp E K w) (y : WithAbs w.1) : σ • y = WithAbs.toAbs w.1 ((σ : K
  ≃ₐ[E] K) y.ofAbs) := rfl

noncomputable scoped instance instMulActionWithAbs : MulAction (decomp E K w) (WithAbs w.1) where
  one_smul y := by rw [smul_withAbs_def]; rfl
  mul_smul σ τ y := by rw [smul_withAbs_def, smul_withAbs_def, smul_withAbs_def]; rfl

noncomputable scoped instance instDistribMulActionWithAbs : DistribMulAction (decomp E K w) (WithAbs
  w.1) where
  smul_zero σ := by rw [smul_withAbs_def]; simp
  smul_add σ x y := by
    rw [smul_withAbs_def, smul_withAbs_def, smul_withAbs_def]
    change WithAbs.toAbs _ ((σ : K ≃ₐ[E] K) (x.ofAbs + y.ofAbs)) = _
    rw [map_add]; rfl

noncomputable scoped instance instUniformContinuousConstSMul : UniformContinuousConstSMul (decomp E
  K w) (WithAbs w.1) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

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

theorem smul_def (σ : decomp E K w) (x : w.Completion) : σ • x = actRingEquiv σ x := rfl

scoped instance instContinuousConstSMul : ContinuousConstSMul (decomp E K w) w.Completion :=
  ⟨fun σ => continuous_actRingEquiv σ⟩

noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K
  w) (w.Completion)ˣ :=
  Units.mulDistribMulActionRight

noncomputable scoped instance instMulActionUnits : MulAction (decomp E K w) (w.Completion)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction

noncomputable scoped instance instSMulUnits : SMul (decomp E K w) (w.Completion)ˣ :=
  (instMulActionUnits (E := E) (K := K) (w := w)).toSMul

theorem coe_smul_units (σ : decomp E K w) (u : (w.Completion)ˣ) : ((σ • u : (w.Completion)ˣ)
  : w.Completion) = σ • (u : w.Completion) := rfl

variable (E K w) in
noncomputable abbrev localUnits : Rep ℤ (decomp E K w) := Rep.ofMulDistribMulAction (decomp E K
  w) (w.Completion)ˣ

end NumberField.InfPlaceDecomp

namespace NumberField.ArchIdele

open scoped NumberField.InfPlaceDecomp

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem exists_above (v : InfinitePlace E) : ∃ w : InfinitePlace K, w.comap (algebraMap E K) = v :=
  InfinitePlace.comap_surjective v

noncomputable def above (v : InfinitePlace E) : InfinitePlace K := (exists_above E K v).choose

theorem comap_above (v : InfinitePlace E) : (above E K v).comap (algebraMap E K) = v
  := (exists_above E K v).choose_spec

end NumberField.ArchIdele

open NumberField

namespace NumberField.InfinitePlaceTransport

section general
variable {R S : Type*} [Field R] [Field S]

theorem uniformContinuous_congr_of_forall_eq (v : AbsoluteValue R ℝ) (v' : AbsoluteValue S ℝ) (f : R
  ≃+* S)
    (h : ∀ x, v' (f x) = v x) : UniformContinuous (WithAbs.congr v v' f) :=
  (AddMonoidHomClass.isometry_of_norm (WithAbs.congr v v' f) fun x => by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
    exact h _).uniformContinuous

end general

variable {E K : Type*} [Field E] [Field K] [Algebra E K]

theorem apply_apply_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w') (x : K)
  : w' (σ x) = w x := by
  rw [← h, InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]

theorem inv_smul_eq_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w') : σ⁻¹ • w'
  = w := by
  rw [← h, inv_smul_smul]

theorem uniformContinuous_congr_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : InfinitePlace K} (h : σ • w = w')
  :
    UniformContinuous (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq w.1 w'.1 _ (apply_apply_of_smul_eq h)

noncomputable def transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') : w.Completion
  ≃+* w'.Completion :=
  (AbsoluteValue.Completion.equiv w.1).trans
    ((UniformSpace.Completion.mapRingEquiv (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_smul_eq h).continuous
      ((uniformContinuous_congr_of_smul_eq (inv_smul_eq_of_smul_eq h)).continuous.congr fun _ =>
        rfl)).trans
    (AbsoluteValue.Completion.equiv w'.1).symm)

theorem transport_apply (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : w.Completion)
  :
    transport σ h x = AbsoluteValue.Completion.ofCompletion
      (UniformSpace.Completion.map (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
        (AbsoluteValue.Completion.toCompletion x)) := by
  rw [transport, RingEquiv.trans_apply, RingEquiv.trans_apply,
    AbsoluteValue.Completion.equiv_symm_apply, AbsoluteValue.Completion.equiv_apply]
  rfl

theorem toCompletion_transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x
  : w.Completion) :
    AbsoluteValue.Completion.toCompletion (transport σ h x)
      = UniformSpace.Completion.map (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
        (AbsoluteValue.Completion.toCompletion x) := by
  rw [transport_apply, AbsoluteValue.Completion.toCompletion_ofCompletion]

theorem transport_coe (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : WithAbs w.1) :
    transport σ h (x : w.Completion) = ((WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K) x
      : WithAbs w'.1) : w'.Completion) := by
  rw [transport_apply, AbsoluteValue.Completion.toCompletion_coe,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_smul_eq h),
    AbsoluteValue.Completion.ofCompletion_coe]

theorem continuous_transport (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w')
  : Continuous (transport σ h) := by
  rw [show (transport σ h : w.Completion → w'.Completion) = AbsoluteValue.Completion.ofCompletion ∘
      UniformSpace.Completion.map (WithAbs.congr w.1 w'.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) ∘
        AbsoluteValue.Completion.toCompletion from funext (transport_apply σ h)]
  exact (AbsoluteValue.Completion.continuous_ofCompletion w'.1).comp
    (UniformSpace.Completion.continuous_map.comp
      (AbsoluteValue.Completion.continuous_toCompletion w.1))

noncomputable abbrev transportUnits (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') :
    (w.Completion)ˣ ≃* (w'.Completion)ˣ :=
  Units.mapEquiv (transport σ h).toMulEquiv

theorem coe_transportUnits (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (u
  : (w.Completion)ˣ) :
    ((transportUnits σ h u : (w'.Completion)ˣ) : w'.Completion) = transport σ h (u : w.Completion)
      := rfl

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

namespace FiniteCoindAux

open NumberField NumberField.PlaceTransport IsDedekindDomain
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

section general

variable {E K : Type} [Field E] [Field K] [NumberField K] [Algebra E K]

private theorem transportUnits_congr {σ τ : K ≃ₐ[E] K} (e : σ = τ) {w w' : HeightOneSpectrum (𝓞
  K)} (h₁ : σ • w = w') (h₂ : τ • w = w')
    (u : (w.adicCompletion K)ˣ) : transportUnits σ h₁ u = transportUnits τ h₂ u := by
  subst e; rfl

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
  rw [NumberField.PlaceTransport.transport_eq_actRingEquiv E K w d h, PlaceDecomp.coe_smul_units,
    PlaceDecomp.smul_def]

private theorem decomp_smul {w : HeightOneSpectrum (𝓞 K)} (d : PlaceDecomp.decomp E K w) : (d
  : K ≃ₐ[E] K) • w = w := by
  have hd : (d : K ≃ₐ[E] K) ∈ MulAction.stabilizer (K ≃ₐ[E] K) w := by
    rw [NumberField.PlaceTransport.stabilizer_eq_decomp E K w]; exact d.2
  exact hd

private theorem mem_decomp_of_smul_eq {w : HeightOneSpectrum (𝓞 K)} {σ : K ≃ₐ[E] K} (h : σ • w = w)
  : σ ∈ PlaceDecomp.decomp E K w := by
  rw [← NumberField.PlaceTransport.stabilizer_eq_decomp E K w]; exact h

end general

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

private abbrev Idx (v : HeightOneSpectrum (𝓞 E)) : Type := {w : HeightOneSpectrum (𝓞 K) //
  w.under (𝓞 E) = v}

private noncomputable abbrev Cv (v : HeightOneSpectrum (𝓞 E)) : Rep ℤ (K ≃ₐ[E] K) :=
  Rep.coind (FiniteSIdele.D E K v).subtype (FiniteSIdele.localUnits E K v)

omit [NumberField K] in
private theorem under_above (v : HeightOneSpectrum (𝓞 E)) : (PlaceAbove.above E K v).under (𝓞 E) = v
  :=
  HeightOneSpectrum.ext
    (by rw [HeightOneSpectrum.under_asIdeal]; exact PlaceAbove.comap_above E K v)

variable {E K}
variable (v : HeightOneSpectrum (𝓞 E))

private noncomputable def fval (f : Cv E K v) (x : K ≃ₐ[E] K) : ((PlaceAbove.above E K
  v).adicCompletion K)ˣ := Additive.toMul (f.1 x)

private theorem fval_ρ (g : K ≃ₐ[E] K) (f : Cv E K v) (x : K ≃ₐ[E] K) : fval v ((Cv E K v).ρ g f) x
  = fval v f (x * g) := rfl

private theorem fval_add (f₁ f₂ : Cv E K v) (x : K ≃ₐ[E] K) : fval v (f₁ + f₂) x = fval v f₁ x *
  fval v f₂ x := rfl

private theorem coind_mem (f : Cv E K v) (d : FiniteSIdele.D E K v) (x : K ≃ₐ[E] K) :
    fval v f ((d : K ≃ₐ[E] K) * x) = d • fval v f x :=
  congrArg Additive.toMul ((Representation.mem_coindV _ _ _).1 f.2 d x)

omit [NumberField E] in
private theorem transportUnits_congr_idx (u : Π w : Idx E K v,
  (w.1.adicCompletion K)ˣ) {i₁ i₂ : Idx E K v} (e : i₁ = i₂)
    (σ : K ≃ₐ[E] K) {t : HeightOneSpectrum (𝓞 K)} (h₁ : σ • i₁.1 = t) (h₂ : σ • i₂.1 = t) :
    transportUnits σ h₁ (u i₁) = transportUnits σ h₂ (u i₂) := by
  subst e; rfl

omit [NumberField E] in
private theorem transportUnits_one_idx (u : Π w : Idx E K v,
  (w.1.adicCompletion K)ˣ) {i₁ i₂ : Idx E K v} (e : i₁ = i₂)
    (h : (1 : K ≃ₐ[E] K) • i₁.1 = i₂.1) : transportUnits (1 : K ≃ₐ[E] K) h (u i₁) = u i₂ := by
  subst e
  exact transportUnits_one h (u i₁)

private theorem indep (f : Cv E K v) (x y : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K))
    (hx : x⁻¹ • PlaceAbove.above E K v = w) (hy : y⁻¹ • PlaceAbove.above E K v = w) :
    transportUnits y⁻¹ hy (fval v f y) = transportUnits x⁻¹ hx (fval v f x) := by
  have hd : y * x⁻¹ ∈ FiniteSIdele.D E K v :=
    mem_decomp_of_smul_eq (by rw [mul_smul, hx, ← hy, smul_inv_smul])
  obtain ⟨d, rfl⟩ : ∃ d : FiniteSIdele.D E K v, (d : K ≃ₐ[E] K) * x = y :=
    ⟨⟨y * x⁻¹, hd⟩, inv_mul_cancel_right y x⟩
  have hd1 : ((d⁻¹ : FiniteSIdele.D E K v) : K ≃ₐ[E] K) • PlaceAbove.above E K v = PlaceAbove.above
    E K v :=
    decomp_smul d⁻¹
  rw [coind_mem, transportUnits_congr (show ((d : K ≃ₐ[E] K) * x)⁻¹ =
        x⁻¹ * ((d⁻¹ : FiniteSIdele.D E K v) : K ≃ₐ[E] K) by rw [mul_inv_rev]; rfl) hy
      (by rw [mul_smul]; exact (congrArg (x⁻¹ • ·) hd1).trans hx),
    ← transportUnits_trans x⁻¹ ((d⁻¹ : FiniteSIdele.D E K v) : K ≃ₐ[E] K) hd1 hx,
    transportUnits_eq_smul, inv_smul_smul]

omit [NumberField K] in
private theorem mem_idx (x : K ≃ₐ[E] K) : (x⁻¹ • PlaceAbove.above E K v).under (𝓞 E) = v :=
  (NumberField.PlaceTransport.under_smul E K x⁻¹ _).trans (under_above E K v)

private noncomputable def bwdFun (u : Π w : Idx E K v, (w.1.adicCompletion K)ˣ) :
    (K ≃ₐ[E] K) → Additive ((PlaceAbove.above E K v).adicCompletion K)ˣ :=
  fun x => Additive.ofMul (transportUnits x (smul_inv_smul x (PlaceAbove.above E K v)) (u ⟨x⁻¹ •
    PlaceAbove.above E K v, mem_idx v x⟩))

private theorem bwdFun_apply (u : Π w : Idx E K v, (w.1.adicCompletion K)ˣ) (x : K ≃ₐ[E] K) :
    Additive.toMul (bwdFun v u x)
      = transportUnits x (smul_inv_smul x (PlaceAbove.above E K v)) (u ⟨x⁻¹ • PlaceAbove.above E K
        v, mem_idx v x⟩) := rfl

private theorem bwdFun_mem (u : Π w : Idx E K v, (w.1.adicCompletion K)ˣ) :
    bwdFun v u ∈ Representation.coindV (FiniteSIdele.D E K v).subtype (FiniteSIdele.localUnits E K
      v).ρ := by
  refine (Representation.mem_coindV _ _ _).2 fun d x => ?_
  apply Additive.toMul.injective
  change Additive.toMul (bwdFun v u ((d : K ≃ₐ[E] K) * x)) = d • Additive.toMul (bwdFun v u x)
  have hidx : (⟨((d : K ≃ₐ[E] K) * x)⁻¹ • PlaceAbove.above E K v,
    mem_idx v ((d : K ≃ₐ[E] K) * x)⟩ : Idx E K v) =
      ⟨x⁻¹ • PlaceAbove.above E K v, mem_idx v x⟩ := by
    apply Subtype.ext
    change ((d : K ≃ₐ[E] K) * x)⁻¹ • PlaceAbove.above E K v = x⁻¹ • PlaceAbove.above E K v
    rw [mul_inv_rev, mul_smul]
    exact congrArg (x⁻¹ • ·) (decomp_smul d⁻¹)
  rw [bwdFun_apply, bwdFun_apply, transportUnits_congr_idx v u hidx ((d : K ≃ₐ[E] K) * x) _
      (by rw [mul_smul, smul_inv_smul]; exact decomp_smul d),
    ← transportUnits_trans (d : K ≃ₐ[E] K) x (smul_inv_smul x _) (decomp_smul d),
      transportUnits_eq_smul]

private noncomputable def bwd (u : Π w : Idx E K v,
  (w.1.adicCompletion K)ˣ) : Cv E K v := ⟨bwdFun v u, bwdFun_mem v u⟩

section
variable [IsGalois E K]

private theorem exists_smul_eq (w : Idx E K v) : ∃ x : K ≃ₐ[E] K,
  x • w.1 = PlaceAbove.above E K v := by
  have hmem : PlaceAbove.above E K v ∈ MulAction.orbit (K ≃ₐ[E] K) w.1 := by
    rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq E K w.1]
    exact (under_above E K v).trans w.2.symm
  exact MulAction.mem_orbit_iff.1 hmem

private noncomputable def sel (w : Idx E K v) : K ≃ₐ[E] K := (exists_smul_eq v w).choose

private theorem sel_smul (w : Idx E K v) : sel v w • w.1 = PlaceAbove.above E K v := (exists_smul_eq
  v w).choose_spec

private theorem inv_sel_smul (w : Idx E K v) : (sel v w)⁻¹ • PlaceAbove.above E K v = w.1
  := inv_smul_eq_of_smul_eq (sel_smul v w)

private noncomputable def fwd (f : Cv E K v) : Π w : Idx E K v, (w.1.adicCompletion K)ˣ :=
  fun w => transportUnits (sel v w)⁻¹ (inv_sel_smul v w) (fval v f (sel v w))

private theorem fwd_eq (f : Cv E K v) (w : Idx E K v) (y : K ≃ₐ[E] K) (hy : y • w.1 =
  PlaceAbove.above E K v) :
    fwd v f w = transportUnits y⁻¹ (inv_smul_eq_of_smul_eq hy) (fval v f y) :=
  (indep v f y (sel v w) w.1 (inv_smul_eq_of_smul_eq hy) (inv_sel_smul v w))

private theorem fwd_add (f₁ f₂ : Cv E K v) (w : Idx E K v) : fwd v (f₁ + f₂) w = fwd v f₁ w * fwd v
  f₂ w := by
  change transportUnits _ _ (fval v (f₁ + f₂) (sel v w)) = _
  rw [fval_add, map_mul]
  rfl

private theorem fwd_ρ (g : K ≃ₐ[E] K) (f : Cv E K v) (w w' : Idx E K v) (h : g • w'.1 = w.1) :
    fwd v ((Cv E K v).ρ g f) w = transportUnits g h (fwd v f w') := by
  have hy : (sel v w * g) • w'.1 = PlaceAbove.above E K v := by rw [mul_smul, h, sel_smul]
  rw [fwd_eq v f w' (sel v w * g) hy,
    transportUnits_trans g (sel v w * g)⁻¹ (inv_smul_eq_of_smul_eq hy) h
      (by rw [mul_inv_rev, mul_inv_cancel_left]; exact inv_sel_smul v w),
    transportUnits_congr (show g * (sel v w * g)⁻¹ = (sel v w)⁻¹ by rw [mul_inv_rev,
      mul_inv_cancel_left]) _ (inv_sel_smul v w)]
  rfl

private theorem fwd_bwd (u : Π w : Idx E K v,
  (w.1.adicCompletion K)ˣ) (w : Idx E K v) : fwd v (bwd v u) w = u w := by
  have hidx : (⟨(sel v w)⁻¹ • PlaceAbove.above E K v,
    mem_idx v (sel v w)⟩ : Idx E K v) = w := Subtype.ext (inv_sel_smul v w)
  change transportUnits (sel v w)⁻¹ (inv_sel_smul v w) (Additive.toMul (bwdFun v u (sel v w))) = u w
  rw [bwdFun_apply,
    transportUnits_trans (sel v w)⁻¹ (sel v w) (smul_inv_smul (sel v w) _) (inv_sel_smul v w)
      (by rw [inv_mul_cancel, one_smul]; exact inv_sel_smul v w),
    transportUnits_congr (inv_mul_cancel (sel v w)) _ (by rw [one_smul]; exact inv_sel_smul v w)]
  exact transportUnits_one_idx v u hidx _

private theorem bwd_fwd (f : Cv E K v) : bwd v (fwd v f) = f := by
  apply Subtype.ext
  funext x
  apply Additive.toMul.injective
  change Additive.toMul (bwdFun v (fwd v f) x) = fval v f x
  rw [bwdFun_apply, fwd_eq v f ⟨x⁻¹ • PlaceAbove.above E K v, mem_idx v x⟩ x (smul_inv_smul x _),
    transportUnits_trans x x⁻¹ _ (smul_inv_smul x _) (by rw [mul_inv_cancel, one_smul]),
    transportUnits_congr (mul_inv_cancel x) _ (one_smul _ _), transportUnits_one]

private noncomputable def equiv : Cv E K v ≃+ Additive (Π w : Idx E K v,
  (w.1.adicCompletion K)ˣ) where
  toFun f := Additive.ofMul (fwd v f)
  invFun a := bwd v (Additive.toMul a)
  left_inv f := bwd_fwd v f
  right_inv a := congrArg Additive.ofMul (funext (fwd_bwd v (Additive.toMul a)))
  map_add' f₁ f₂ := congrArg Additive.ofMul (funext (fwd_add v f₁ f₂))

end

end FiniteCoindAux

open scoped NumberField.PlaceDecomp NumberField.PlaceTransport


theorem NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits (E K : Type) [Field
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
  ⟨FiniteCoindAux.equiv v, fun g f w w' h => FiniteCoindAux.fwd_ρ v g f w w' h⟩


namespace ArchCoindAux

open NumberField NumberField.InfinitePlaceTransport
open scoped NumberField.InfPlaceDecomp

section general

variable {E K : Type} [Field E] [Field K] [Algebra E K]

private theorem comap_smul_algebraMap (σ : K ≃ₐ[E] K) (w : InfinitePlace K) :
    (σ • w).comap (algebraMap E K) = w.comap (algebraMap E K) := by
  rw [InfinitePlace.smul_eq_comap, ← InfinitePlace.comap_comp]
  congr 1
  exact RingHom.ext fun x => σ.symm.commutes x

private theorem transportUnits_congr {σ τ : K ≃ₐ[E] K} (e : σ = τ) {w w' : InfinitePlace K} (h₁ : σ
  • w = w') (h₂ : τ • w = w')
    (u : (w.Completion)ˣ) : transportUnits σ h₁ u = transportUnits τ h₂ u := by
  subst e; rfl

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
    InfPlaceDecomp.coe_smul_units,
    InfPlaceDecomp.smul_def]

end general

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

private abbrev Idx (v : InfinitePlace E) : Type := {w : InfinitePlace K // w.comap (algebraMap E K)
  = v}

private noncomputable abbrev Cv (v : InfinitePlace E) : Rep ℤ (K ≃ₐ[E] K) :=
  Rep.coind (InfPlaceDecomp.decomp E K (ArchIdele.above E K v)).subtype (InfPlaceDecomp.localUnits E
    K (ArchIdele.above E K v))

variable {E K}
variable (v : InfinitePlace E)

private noncomputable def fval (f : Cv E K v) (x : K ≃ₐ[E] K) : ((ArchIdele.above E K
  v).Completion)ˣ := Additive.toMul (f.1 x)

private theorem fval_ρ (g : K ≃ₐ[E] K) (f : Cv E K v) (x : K ≃ₐ[E] K) : fval v ((Cv E K v).ρ g f) x
  = fval v f (x * g) := rfl

private theorem fval_add (f₁ f₂ : Cv E K v) (x : K ≃ₐ[E] K) : fval v (f₁ + f₂) x = fval v f₁ x *
  fval v f₂ x := rfl

private theorem coind_mem (f : Cv E K v) (d : InfPlaceDecomp.decomp E K (ArchIdele.above E K v)) (x
  : K ≃ₐ[E] K) :
    fval v f ((d : K ≃ₐ[E] K) * x) = d • fval v f x :=
  congrArg Additive.toMul ((Representation.mem_coindV _ _ _).1 f.2 d x)

omit [NumberField E] [NumberField K] in
private theorem transportUnits_congr_idx (u : Π w : Idx E K v,
  (w.1.Completion)ˣ) {i₁ i₂ : Idx E K v} (e : i₁ = i₂)
    (σ : K ≃ₐ[E] K) {t : InfinitePlace K} (h₁ : σ • i₁.1 = t) (h₂ : σ • i₂.1 = t) :
    transportUnits σ h₁ (u i₁) = transportUnits σ h₂ (u i₂) := by
  subst e; rfl

omit [NumberField E] [NumberField K] in
private theorem transportUnits_one_idx (u : Π w : Idx E K v,
  (w.1.Completion)ˣ) {i₁ i₂ : Idx E K v} (e : i₁ = i₂)
    (h : (1 : K ≃ₐ[E] K) • i₁.1 = i₂.1) : transportUnits (1 : K ≃ₐ[E] K) h (u i₁) = u i₂ := by
  subst e
  exact transportUnits_one h (u i₁)

private theorem indep (f : Cv E K v) (x y : K ≃ₐ[E] K) (w : InfinitePlace K)
    (hx : x⁻¹ • ArchIdele.above E K v = w) (hy : y⁻¹ • ArchIdele.above E K v = w) :
    transportUnits y⁻¹ hy (fval v f y) = transportUnits x⁻¹ hx (fval v f x) := by
  have hd : y * x⁻¹ ∈ InfPlaceDecomp.decomp E K (ArchIdele.above E K v) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hx, ← hy, smul_inv_smul]
  obtain ⟨d, rfl⟩ : ∃ d : InfPlaceDecomp.decomp E K (ArchIdele.above E K v),
    (d : K ≃ₐ[E] K) * x = y :=
    ⟨⟨y * x⁻¹, hd⟩, inv_mul_cancel_right y x⟩
  have hd1 : ((d⁻¹ : InfPlaceDecomp.decomp E K (ArchIdele.above E K v)) : K ≃ₐ[E] K) •
    ArchIdele.above E K v =
      ArchIdele.above E K v := (d⁻¹).2
  rw [coind_mem, transportUnits_congr (show ((d : K ≃ₐ[E] K) * x)⁻¹ =
        x⁻¹ * ((d⁻¹ : InfPlaceDecomp.decomp E K (ArchIdele.above E K v)) : K ≃ₐ[E] K) by
          rw [mul_inv_rev]; rfl) hy
      (by rw [mul_smul]; exact (congrArg (x⁻¹ • ·) hd1).trans hx),
    ← transportUnits_trans x⁻¹ ((d⁻¹ : InfPlaceDecomp.decomp E K (ArchIdele.above E K v)) : K ≃ₐ[E]
      K) hd1 hx,
    transportUnits_eq_smul, inv_smul_smul]

private theorem mem_idx (x : K ≃ₐ[E] K) : (x⁻¹ • ArchIdele.above E K v).comap (algebraMap E K) = v
  :=
  (comap_smul_algebraMap x⁻¹ _).trans (ArchIdele.comap_above E K v)

private noncomputable def bwdFun (u : Π w : Idx E K v,
  (w.1.Completion)ˣ) : (K ≃ₐ[E] K) → Additive ((ArchIdele.above E K v).Completion)ˣ :=
  fun x => Additive.ofMul (transportUnits x (smul_inv_smul x (ArchIdele.above E K v)) (u ⟨x⁻¹ •
    ArchIdele.above E K v, mem_idx v x⟩))

private theorem bwdFun_apply (u : Π w : Idx E K v, (w.1.Completion)ˣ) (x : K ≃ₐ[E] K) :
    Additive.toMul (bwdFun v u x) = transportUnits x (smul_inv_smul x (ArchIdele.above E K v)) (u
      ⟨x⁻¹ • ArchIdele.above E K v, mem_idx v x⟩) := rfl

private theorem bwdFun_mem (u : Π w : Idx E K v, (w.1.Completion)ˣ) :
    bwdFun v u ∈ Representation.coindV (InfPlaceDecomp.decomp E K (ArchIdele.above E K v)).subtype
      (InfPlaceDecomp.localUnits E K (ArchIdele.above E K v)).ρ := by
  refine (Representation.mem_coindV _ _ _).2 fun d x => ?_
  apply Additive.toMul.injective
  change Additive.toMul (bwdFun v u ((d : K ≃ₐ[E] K) * x)) = d • Additive.toMul (bwdFun v u x)
  have hidx : (⟨((d : K ≃ₐ[E] K) * x)⁻¹ • ArchIdele.above E K v,
    mem_idx v ((d : K ≃ₐ[E] K) * x)⟩ : Idx E K v) =
      ⟨x⁻¹ • ArchIdele.above E K v, mem_idx v x⟩ := by
    apply Subtype.ext
    change ((d : K ≃ₐ[E] K) * x)⁻¹ • ArchIdele.above E K v = x⁻¹ • ArchIdele.above E K v
    rw [mul_inv_rev, mul_smul]
    exact congrArg (x⁻¹ • ·) (d⁻¹).2
  rw [bwdFun_apply, bwdFun_apply, transportUnits_congr_idx v u hidx ((d : K ≃ₐ[E] K) * x) _
      (by rw [mul_smul, smul_inv_smul]; exact d.2),
    ← transportUnits_trans (d : K ≃ₐ[E] K) x (smul_inv_smul x _) (MulAction.mem_stabilizer_iff.mp
      d.2), transportUnits_eq_smul]

private noncomputable def bwd (u : Π w : Idx E K v, (w.1.Completion)ˣ) : Cv E K v := ⟨bwdFun v u,
  bwdFun_mem v u⟩

section
variable [IsGalois E K]

private theorem exists_smul_eq (w : Idx E K v) : ∃ x : K ≃ₐ[E] K, x • w.1 = ArchIdele.above E K v :=
  InfinitePlace.exists_smul_eq_of_comap_eq (w.2.trans (ArchIdele.comap_above E K v).symm)

private noncomputable def sel (w : Idx E K v) : K ≃ₐ[E] K := (exists_smul_eq v w).choose

private theorem sel_smul (w : Idx E K v) : sel v w • w.1 = ArchIdele.above E K v := (exists_smul_eq
  v w).choose_spec

private theorem inv_sel_smul (w : Idx E K v) : (sel v w)⁻¹ • ArchIdele.above E K v = w.1
  := inv_smul_eq_of_smul_eq (sel_smul v w)

private noncomputable def fwd (f : Cv E K v) : Π w : Idx E K v, (w.1.Completion)ˣ :=
  fun w => transportUnits (sel v w)⁻¹ (inv_sel_smul v w) (fval v f (sel v w))

private theorem fwd_eq (f : Cv E K v) (w : Idx E K v) (y : K ≃ₐ[E] K) (hy : y • w.1 =
  ArchIdele.above E K v) :
    fwd v f w = transportUnits y⁻¹ (inv_smul_eq_of_smul_eq hy) (fval v f y) :=
  (indep v f y (sel v w) w.1 (inv_smul_eq_of_smul_eq hy) (inv_sel_smul v w))

private theorem fwd_add (f₁ f₂ : Cv E K v) (w : Idx E K v) : fwd v (f₁ + f₂) w = fwd v f₁ w * fwd v
  f₂ w := by
  change transportUnits _ _ (fval v (f₁ + f₂) (sel v w)) = _
  rw [fval_add, map_mul]
  rfl

private theorem fwd_ρ (g : K ≃ₐ[E] K) (f : Cv E K v) (w w' : Idx E K v) (h : g • w'.1 = w.1) :
    fwd v ((Cv E K v).ρ g f) w = transportUnits g h (fwd v f w') := by
  have hy : (sel v w * g) • w'.1 = ArchIdele.above E K v := by rw [mul_smul, h, sel_smul]
  rw [fwd_eq v f w' (sel v w * g) hy,
    transportUnits_trans g (sel v w * g)⁻¹ (inv_smul_eq_of_smul_eq hy) h
      (by rw [mul_inv_rev, mul_inv_cancel_left]; exact inv_sel_smul v w),
    transportUnits_congr (show g * (sel v w * g)⁻¹ = (sel v w)⁻¹ by rw [mul_inv_rev,
      mul_inv_cancel_left]) _ (inv_sel_smul v w)]
  rfl

private theorem fwd_bwd (u : Π w : Idx E K v,
  (w.1.Completion)ˣ) (w : Idx E K v) : fwd v (bwd v u) w = u w := by
  have hidx : (⟨(sel v w)⁻¹ • ArchIdele.above E K v,
    mem_idx v (sel v w)⟩ : Idx E K v) = w := Subtype.ext (inv_sel_smul v w)
  change transportUnits (sel v w)⁻¹ (inv_sel_smul v w) (Additive.toMul (bwdFun v u (sel v w))) = u w
  rw [bwdFun_apply,
    transportUnits_trans (sel v w)⁻¹ (sel v w) (smul_inv_smul (sel v w) _) (inv_sel_smul v w)
      (by rw [inv_mul_cancel, one_smul]; exact inv_sel_smul v w),
    transportUnits_congr (inv_mul_cancel (sel v w)) _ (by rw [one_smul]; exact inv_sel_smul v w)]
  exact transportUnits_one_idx v u hidx _

private theorem bwd_fwd (f : Cv E K v) : bwd v (fwd v f) = f := by
  apply Subtype.ext
  funext x
  apply Additive.toMul.injective
  change Additive.toMul (bwdFun v (fwd v f) x) = fval v f x
  rw [bwdFun_apply, fwd_eq v f ⟨x⁻¹ • ArchIdele.above E K v, mem_idx v x⟩ x (smul_inv_smul x _),
    transportUnits_trans x x⁻¹ _ (smul_inv_smul x _) (by rw [mul_inv_cancel, one_smul]),
    transportUnits_congr (mul_inv_cancel x) _ (one_smul _ _), transportUnits_one]

private noncomputable def equiv : Cv E K v ≃+ Additive (Π w : Idx E K v, (w.1.Completion)ˣ) where
  toFun f := Additive.ofMul (fwd v f)
  invFun a := bwd v (Additive.toMul a)
  left_inv f := bwd_fwd v f
  right_inv a := congrArg Additive.ofMul (funext (fwd_bwd v (Additive.toMul a)))
  map_add' f₁ f₂ := congrArg Additive.ofMul (funext (fwd_add v f₁ f₂))

end

end ArchCoindAux


theorem NumberField.ArchIdele.exists_addEquiv_coind_localUnits (E K : Type) [Field E] [NumberField
  E] [Field K] [NumberField K]
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
  ⟨ArchCoindAux.equiv v, fun g f w w' h => ArchCoindAux.fwd_ρ v g f w w' h⟩

