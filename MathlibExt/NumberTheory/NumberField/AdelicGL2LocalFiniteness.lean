/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_AdelicKernel.lean`,
`Definitions/Def_AutomorphicForm_AdelicLsXi.lean`,
`Definitions/Def_NumberField_AdelicBox.lean`,
`Theorems/Thm_AutomorphicForm_adelicKernelLocalFiniteness.lean`
and
`P2M/Sol/S_AutomorphicForm_adelicKernelLocalFiniteness.lean`
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

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

noncomputable section

open scoped Pointwise

namespace NumberField

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The group of `2 × 2` invertible matrices over the adele ring of `K`. -/
abbrev AdelicGL2 : Type _ :=
  Matrix.GeneralLinearGroup (Fin 2) (AdeleRing R K)

/-- The diagonal homomorphism from rational `GL(2)` points to adelic `GL(2)`; it need not be
injective for an arbitrary Dedekind domain (for `R = K = 𝔽₃` the target is trivial). -/
def globalPoints : Matrix.GeneralLinearGroup (Fin 2) K →* AdelicGL2 R K :=
  Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing R K))

variable {R K}

@[simp]
theorem globalPoints_apply (γ : Matrix.GeneralLinearGroup (Fin 2) K) (i j : Fin 2) :
    ((globalPoints R K γ : AdelicGL2 R K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j =
    algebraMap K (AdeleRing R K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) :=
  rfl

/-- Local finiteness of the adelic kernel: for a compact set `C` of adelic
`GL(2)` and fixed adelic `x, y`, only finitely many rational points `γ`
satisfy `x⁻¹ * γ * y ∈ C`. -/
def AdelicKernelLocalFiniteness (F : Type*) [Field F] [NumberField F] : Prop :=
  ∀ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C → ∀ x y : AdelicGL2 (𝓞 F) F,
    {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      x⁻¹ * globalPoints (𝓞 F) F γ * y ∈ C}.Finite

theorem adelicKernelLocalFiniteness_iff (F : Type*) [Field F] [NumberField F] :
    AdelicKernelLocalFiniteness F ↔
      ∀ C : Set (AdelicGL2 (𝓞 F) F), IsCompact C → ∀ x y : AdelicGL2 (𝓞 F) F,
        {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          x⁻¹ * globalPoints (𝓞 F) F γ * y ∈ C}.Finite :=
  Iff.rfl

section Proof

variable (F : Type*) [Field F] [NumberField F]

private def integralFiniteAdeles : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

private theorem zero_mem_integralFiniteAdeles :
    (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles F :=
  fun _ => zero_mem _

private theorem isOpen_integralFiniteAdeles : IsOpen (integralFiniteAdeles F) := by
  haveI : Fact (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ => Valued.isOpen_valuationSubring _⟩
  exact RestrictedProduct.isOpen_forall_mem
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      Valued.isOpen_valuationSubring _)

private theorem fst_algebraMap (ξ : F) :
    (algebraMap F (AdeleRing (𝓞 F) F) ξ).1 = algebraMap F (InfiniteAdeleRing F) ξ :=
  rfl

private theorem finite_setOf_algebraMap_mem {C : Set (AdeleRing (𝓞 F) F)}
    (hC : IsCompact C) :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C}.Finite := by
  classical
  have hO : IsOpen (integralFiniteAdeles F) := isOpen_integralFiniteAdeles F
  have hCf : IsCompact (Prod.snd '' C) := hC.image continuous_snd
  obtain ⟨t, -, hcover⟩ := hCf.elim_nhds_subcover
    (fun y => (fun z => z - y) ⁻¹' integralFiniteAdeles F) fun y _ =>
      (hO.preimage (continuous_id.sub continuous_const)).mem_nhds
        (by simpa only [Set.mem_preimage, Pi.sub_apply, id_eq, sub_self] using
          zero_mem_integralFiniteAdeles F)
  have hcont : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous fun x : InfiniteAdeleRing F =>
      InfiniteAdeleRing.ringEquiv_mixedSpace F x
    simp only [NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun ⟨v, hv⟩ =>
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).continuous.comp
          (continuous_apply v)
    · exact continuous_pi fun ⟨v, hv⟩ =>
        (InfinitePlace.Completion.isometry_extensionEmbedding (v := v)).continuous.comp
          (continuous_apply v)
  have hCinf : IsCompact (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) :=
    (hC.image continuous_fst).image hcont
  have hD : IsCompact ((fun p : mixedEmbedding.mixedSpace F ×
      mixedEmbedding.mixedSpace F => p.1 - p.2) ''
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) ×ˢ
          (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)))) :=
    (hCinf.prod hCinf).image (continuous_fst.sub continuous_snd)
  haveI : DiscreteTopology (mixedEmbedding.integerLattice F).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (mixedEmbedding.integerLattice F))
  have hL : ((fun p : mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F =>
      p.1 - p.2) ''
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C)) ×ˢ
        (InfiniteAdeleRing.ringEquiv_mixedSpace F '' (Prod.fst '' C))) ∩
      (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F))).Finite := by
    refine Metric.finite_isBounded_inter_isClosed
      (isDiscrete_iff_discreteTopology.mpr inferInstance) hD.isBounded ?_
    rw [← Submodule.coe_toAddSubgroup]
    exact AddSubgroup.isClosed_of_isDiscrete _
      (isDiscrete_iff_discreteTopology.mpr inferInstance)
  have hT : ∀ y : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F,
      {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C ∧
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - y ∈ integralFiniteAdeles F}.Finite := by
    intro y
    rcases Set.eq_empty_or_nonempty {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C ∧
        (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 - y ∈ integralFiniteAdeles F} with
      h0 | ⟨ξ₀, hξ₀C, hξ₀y⟩
    · rw [h0]; exact Set.finite_empty
    refine (hL.preimage (f := fun ξ : F => mixedEmbedding F (ξ - ξ₀)) fun a _ b _ h =>
      sub_left_inj.1 (mixedEmbedding_injective F h)).subset ?_
    rintro ξ ⟨hξC, hξy⟩
    refine ⟨?_, ?_⟩
    · refine ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace F
          (algebraMap F (AdeleRing (𝓞 F) F) ξ).1,
          InfiniteAdeleRing.ringEquiv_mixedSpace F
          (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1),
        ⟨⟨(algebraMap F (AdeleRing (𝓞 F) F) ξ).1, ⟨_, hξC, rfl⟩, rfl⟩,
          ⟨(algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1, ⟨_, hξ₀C, rfl⟩, rfl⟩⟩, ?_⟩
      change InfiniteAdeleRing.ringEquiv_mixedSpace F
          (algebraMap F (AdeleRing (𝓞 F) F) ξ).1
          - InfiniteAdeleRing.ringEquiv_mixedSpace F
            (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).1
        = mixedEmbedding F (ξ - ξ₀)
      rw [map_sub, fst_algebraMap, fst_algebraMap,
        ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
        ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    · have h2 : (algebraMap F (AdeleRing (𝓞 F) F) (ξ - ξ₀)).2
          = (algebraMap F (AdeleRing (𝓞 F) F) ξ).2
            - (algebraMap F (AdeleRing (𝓞 F) F) ξ₀).2 := by
        rw [map_sub]; rfl
      have hdiff : (algebraMap F (AdeleRing (𝓞 F) F) (ξ - ξ₀)).2
          ∈ integralFiniteAdeles F := by
        rw [h2, ← sub_sub_sub_cancel_right _ _ y]
        exact fun v => sub_mem (hξy v) (hξ₀y v)
      have hval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
          v.valuation F (ξ - ξ₀) ≤ 1 := fun v => by
        have h := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          (𝓞 F) F v).1 (hdiff v)
        rwa [NumberField.AdeleRing.algebraMap_snd_apply,
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
      obtain ⟨o, ho⟩ :=
        IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F (ξ - ξ₀) hval
      change mixedEmbedding F (ξ - ξ₀) ∈
        (mixedEmbedding.integerLattice F : Set (mixedEmbedding.mixedSpace F))
      rw [← ho]
      exact ⟨o, rfl⟩
  refine (t.finite_toSet.biUnion fun y _ => hT y).subset fun ξ hξ => ?_
  have h2 : (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 ∈ Prod.snd '' C := ⟨_, hξ, rfl⟩
  obtain ⟨y, hy, hyO⟩ := Set.mem_iUnion₂.1 (hcover h2)
  exact Set.mem_iUnion₂.2 ⟨y, hy, hξ, hyO⟩

/-- For a compact set of adelic matrices and fixed adelic `x, y`, only
finitely many rational `GL(2)` points `γ` satisfy `x⁻¹ * γ * y` in the set. -/
theorem adelicKernelLocalFiniteness : AdelicKernelLocalFiniteness F := by
  intro C hC x y
  have hC' : IsCompact ((fun g : AdelicGL2 (𝓞 F) F => x * g * y⁻¹) '' C) :=
    hC.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hE : ∀ i j : Fin 2, IsCompact ((fun g : AdelicGL2 (𝓞 F) F =>
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) ''
        ((fun g : AdelicGL2 (𝓞 F) F => x * g * y⁻¹) '' C)) :=
    fun i j => hC'.image (Units.continuous_val.matrix_elem i j)
  have hA : ∀ i j : Fin 2, {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈
      (fun g : AdelicGL2 (𝓞 F) F =>
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) ''
        ((fun g : AdelicGL2 (𝓞 F) F => x * g * y⁻¹) '' C)}.Finite :=
    fun i j => finite_setOf_algebraMap_mem F (hE i j)
  have hfin : {m : Fin 2 → Fin 2 → F | ∀ i, m i ∈ {r : Fin 2 → F | ∀ j, r j ∈
      {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈
        (fun g : AdelicGL2 (𝓞 F) F =>
          (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) ''
          ((fun g : AdelicGL2 (𝓞 F) F => x * g * y⁻¹) '' C)}}}.Finite :=
    Set.Finite.pi' fun i => Set.Finite.pi' fun j => hA i j
  refine (hfin.preimage (f := (Units.val :
    Matrix.GeneralLinearGroup (Fin 2) F → Matrix (Fin 2) (Fin 2) F))
    Units.val_injective.injOn).subset fun γ hγ => ?_
  simp only [Set.mem_ofPred_eq]
  intro i j
  exact ⟨globalPoints (𝓞 F) F γ,
    ⟨x⁻¹ * globalPoints (𝓞 F) F γ * y, hγ, by simp [mul_assoc]⟩, rfl⟩

end Proof

end NumberField

end
