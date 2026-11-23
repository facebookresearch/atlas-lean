/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The Banach–Nečas–Babuška theorem with Banach trial and Hilbert test spaces

Let `E` be a real Banach trial space and `F` a real Hilbert test space,
and let `B : E →L[ℝ] F →L[ℝ] ℝ` be a bounded
bilinear form, written `B x y` for the value at `(x, y)`. The
**Banach–Nečas–Babuška theorem** says that `B` induces an isomorphism
`E ≃L[ℝ] (F →L[ℝ] ℝ)` as soon as it satisfies two conditions:

* the **inf–sup condition**: there is `β > 0` with
  `β * ‖x‖ ≤ sup_{‖y‖ ≤ 1} |B x y|` for every `x`. Since the dual norm is that
  supremum (`norm_apply_eq_iSup`), this is stated here as
  `β * ‖x‖ ≤ ‖B x‖`, i.e. `IsInfSup B`;
* **nondegeneracy in the second variable**: if `B x y = 0` for every `x`, then `y = 0`,
  i.e. `IsNondegenerate B`.

The theorem is the two-space, non-coercive counterpart of the Lax–Milgram theorem
(`IsCoercive.continuousLinearEquivOfBilin` in Mathlib), which is the special case
`E = F` with the stronger coercivity hypothesis `C * ‖v‖ * ‖v‖ ≤ B v v`. In
particular, no symmetry or coercivity is assumed here: the result applies to the
mixed (saddle-point) variational problems of finite-element theory, e.g. the
Stokes problem, where coercivity fails.

This formalization allows any real Banach trial space `E` and keeps the test
space `F` Hilbert. In the general Banach formulation the reflexivity condition
concerns `F`, not `E`: nondegeneracy only kills the annihilator of the range
inside the image of the canonical embedding `F → F''`, and a closed proper
subspace of `F'` can be weak-* dense (e.g. `c₀ ⊂ ℓ∞`) without being all of `F'`.
The Hilbert structure on `F` lets the orthogonal-complement argument close this
gap. The initial dual-norm and hypothesis APIs need only real normed spaces.

The proof follows the Lax–Milgram pattern. Writing `T : E →L[ℝ] F` for the
operator `bilinearFormSharp B` with `⟪T x, y⟫ = B x y` (the two-space analogue of
Mathlib's `continuousLinearMapOfBilin`), the inf–sup condition says `T` is bounded
below, hence injective with closed range; nondegeneracy says the orthogonal
complement of the range is trivial, hence the range is everything; and a
bijective bounded operator from a Banach space to a Hilbert space is a continuous equivalence.

Main results:

* `bilinearFormSharp`: the operator `T` associated to a bilinear form, with
  `bilinearFormSharp_apply` and `norm_bilinearFormSharp_apply`.
* `IsInfSup`, `IsNondegenerate`: the two hypotheses, with `norm_apply_eq_iSup`
  identifying the dual norm with the supremum over the unit ball, and
  `isInfSup_iff` restating the inf–sup condition in supremum form.
* `sharpEquiv`: the isomorphism `E ≃L[ℝ] F` induced by `B`, with the inverse
  norm bound `norm_sharpEquiv_symm_le`.
* `continuousLinearEquivOfBilinearForm`: the isomorphism
  `E ≃L[ℝ] (F →L[ℝ] ℝ)` given by `B` itself.
* `exists_unique_apply_eq` and `exists_apply_eq_and_norm_le`: the variational
  problem `B x y = φ y` for all `y` has a unique solution, with the stability
  bound `‖x‖ ≤ β⁻¹ * ‖φ‖`.

This is a companion to the Hilbert-space and bounded-operator material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`BoundedOperators.lean`. It is not a numbered v1 target and ports no v1 proof
hole. The references identify the mathematical context; this development does
not claim a literal textbook transcription or a full saddle-point block or
Galerkin error theorem.

References: I. Babuška, "Error bounds for finite element method",
*Numerische Mathematik* 16 (1971), 322–333; J. Nečas, "Sur une méthode pour
résoudre les équations aux dérivées partielles du type elliptique, voisine de
la variationnelle", *Annali della Scuola Normale Superiore di Pisa* (3) 16
(1962), 305–326; A. Ern and J.-L. Guermond, *Theory and Practice of Finite
Elements*, Springer, 2004, §2.2.
-/

@[expose] public section

open scoped InnerProductSpace NNReal

namespace MathlibExt.Analysis.InnerProductSpace.BanachNecasBabuska

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

section Normed

variable [NormedSpace ℝ F]

/-- The **inf–sup condition**: there is `β > 0` such that
`β * ‖x‖ ≤ ‖B x‖` for every `x`. The right-hand side is the dual norm of the
functional `B x`, i.e. `sup_{‖y‖ ≤ 1} |B x y|` (see `norm_apply_eq_iSup`). -/
abbrev IsInfSup (B : E →L[ℝ] F →L[ℝ] ℝ) : Prop :=
  ∃ β : ℝ, 0 < β ∧ ∀ x : E, β * ‖x‖ ≤ ‖B x‖

/-- **Nondegeneracy in the second variable**: the only `y` annihilated by every
`B x` is `y = 0`. -/
abbrev IsNondegenerate (B : E →L[ℝ] F →L[ℝ] ℝ) : Prop :=
  ∀ y : F, (∀ x : E, B x y = 0) → y = 0

/-- The dual norm is the supremum over the closed unit ball. -/
theorem norm_apply_eq_iSup (B : E →L[ℝ] F →L[ℝ] ℝ) (x : E) :
    ‖B x‖ = ⨆ y : {y : F // ‖y‖ ≤ 1}, ‖B x y‖ := by
  have hball : BddAbove (Set.range fun y : {y : F // ‖y‖ ≤ 1} => ‖B x (y : F)‖) := by
    refine ⟨‖B x‖, ?_⟩
    rintro _ ⟨y, rfl⟩
    calc ‖B x (y : F)‖ ≤ ‖B x‖ * ‖(y : F)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖B x‖ * 1 := by
          apply mul_le_mul_of_nonneg_left y.2 (norm_nonneg _)
      _ = ‖B x‖ := mul_one _
  have : Nonempty {y : F // ‖y‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  have hnonneg : 0 ≤ ⨆ y : {y : F // ‖y‖ ≤ 1}, ‖B x (y : F)‖ := by
    have h0 := le_ciSup hball (⟨0, by simp⟩ : {y : F // ‖y‖ ≤ 1})
    simpa using h0
  apply le_antisymm
  · rw [ContinuousLinearMap.opNorm_le_iff hnonneg]
    intro y
    by_cases hy : y = 0
    · simp [hy]
    have hnorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hyball : ‖(‖y‖⁻¹ : ℝ) • y‖ ≤ 1 := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg y),
        inv_mul_cancel₀ (ne_of_gt hnorm)]
    have hle : ‖B x ((‖y‖⁻¹ : ℝ) • y)‖ ≤ ⨆ y : {y : F // ‖y‖ ≤ 1}, ‖B x (y : F)‖ :=
      le_ciSup hball ⟨(‖y‖⁻¹ : ℝ) • y, hyball⟩
    have hsmul : B x y = ‖y‖ • B x ((‖y‖⁻¹ : ℝ) • y) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hnorm), one_smul]
    calc ‖B x y‖ = ‖‖y‖ • B x ((‖y‖⁻¹ : ℝ) • y)‖ := by rw [hsmul]
      _ = ‖y‖ * ‖B x ((‖y‖⁻¹ : ℝ) • y)‖ := by
          rw [norm_smul, Real.norm_of_nonneg (norm_nonneg y)]
      _ ≤ ‖y‖ * (⨆ y : {y : F // ‖y‖ ≤ 1}, ‖B x (y : F)‖) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = (⨆ y : {y : F // ‖y‖ ≤ 1}, ‖B x (y : F)‖) * ‖y‖ := mul_comm _ _
  · apply ciSup_le
    intro y
    calc ‖B x (y : F)‖ ≤ ‖B x‖ * ‖(y : F)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖B x‖ * 1 := by
          apply mul_le_mul_of_nonneg_left y.2 (norm_nonneg _)
      _ = ‖B x‖ := mul_one _

/-- The inf–sup condition in classical supremum form. -/
theorem isInfSup_iff (B : E →L[ℝ] F →L[ℝ] ℝ) :
    IsInfSup B ↔ ∃ β : ℝ, 0 < β ∧
      ∀ x : E, β * ‖x‖ ≤ ⨆ y : {y : F // ‖y‖ ≤ 1}, ‖B x y‖ := by
  constructor
  · rintro ⟨β, hβ, hB⟩
    exact ⟨β, hβ, fun x => by rw [← norm_apply_eq_iSup B x]; exact hB x⟩
  · rintro ⟨β, hβ, hB⟩
    exact ⟨β, hβ, fun x => by rw [norm_apply_eq_iSup B x]; exact hB x⟩

end Normed

variable [InnerProductSpace ℝ F]

variable [CompleteSpace E] [CompleteSpace F]

/-- The operator `E →L[ℝ] F` associated to a bounded bilinear form
`B : E →L[ℝ] F →L[ℝ] ℝ`, characterized by `⟪bilinearFormSharp B x, y⟫ = B x y`.
This is the two-space analogue of Mathlib's `continuousLinearMapOfBilin`
(which is stated for `E = F`). -/
noncomputable def bilinearFormSharp (B : E →L[ℝ] F →L[ℝ] ℝ) : E →L[ℝ] F :=
  (InnerProductSpace.toDual ℝ F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

-- The defining property of `bilinearFormSharp`.
omit [CompleteSpace E] in
theorem bilinearFormSharp_apply (B : E →L[ℝ] F →L[ℝ] ℝ) (x : E) (y : F) :
    ⟪bilinearFormSharp B x, y⟫_ℝ = B x y := by
  simp [bilinearFormSharp, InnerProductSpace.toDual_symm_apply]

-- The Riesz map is an isometry, so the norm of `bilinearFormSharp B x` is the
-- dual norm of `B x`.
omit [CompleteSpace E] in
theorem norm_bilinearFormSharp_apply (B : E →L[ℝ] F →L[ℝ] ℝ) (x : E) :
    ‖bilinearFormSharp B x‖ = ‖B x‖ := by
  simp [bilinearFormSharp]

-- Applying the Riesz map to `bilinearFormSharp B x` recovers `B x`.
omit [CompleteSpace E] in
theorem toDual_bilinearFormSharp (B : E →L[ℝ] F →L[ℝ] ℝ) (x : E) :
    InnerProductSpace.toDual ℝ F (bilinearFormSharp B x) = B x := by
  simp [bilinearFormSharp]

omit [CompleteSpace E] in
/-- The inf–sup condition makes `bilinearFormSharp B` antilipschitz. -/
theorem sharp_antilipschitz {B : E →L[ℝ] F →L[ℝ] ℝ} (hB : IsInfSup B) :
    ∃ C : ℝ≥0, 0 < C ∧ AntilipschitzWith C (bilinearFormSharp B) := by
  obtain ⟨β, hβ, hβx⟩ := hB
  refine ⟨⟨β⁻¹, inv_nonneg.mpr hβ.le⟩, inv_pos.mpr hβ, ?_⟩
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro x
  have hbound : β * ‖x‖ ≤ ‖bilinearFormSharp B x‖ := by
    rw [norm_bilinearFormSharp_apply]; exact hβx x
  exact (le_inv_mul_iff₀ hβ).mpr hbound

omit [CompleteSpace E] in
/-- The inf–sup condition makes `bilinearFormSharp B` injective. -/
theorem sharp_ker_eq_bot {B : E →L[ℝ] F →L[ℝ] ℝ} (hB : IsInfSup B) :
    (bilinearFormSharp B).ker = ⊥ := by
  obtain ⟨_, _, hAnti⟩ := sharp_antilipschitz hB
  rw [LinearMap.ker_eq_bot]
  exact hAnti.injective

/-- The inf–sup condition makes the range of `bilinearFormSharp B` closed. -/
theorem sharp_isClosed_range {B : E →L[ℝ] F →L[ℝ] ℝ} (hB : IsInfSup B) :
    IsClosed ((bilinearFormSharp B).range : Set F) := by
  obtain ⟨_, _, hAnti⟩ := sharp_antilipschitz hB
  exact hAnti.isClosed_range (bilinearFormSharp B).uniformContinuous

/-- The inf–sup condition plus nondegeneracy make `bilinearFormSharp B`
surjective: the orthogonal complement of its range is trivial, and a closed
subspace of a Hilbert space with trivial orthogonal complement is everything. -/
theorem sharp_range_eq_top {B : E →L[ℝ] F →L[ℝ] ℝ} (hInf : IsInfSup B)
    (hNondeg : IsNondegenerate B) : (bilinearFormSharp B).range = ⊤ := by
  have hclosed := sharp_isClosed_range hInf
  have _ : CompleteSpace (bilinearFormSharp B).range := hclosed.completeSpace_coe
  have horth : (bilinearFormSharp B).rangeᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_bot]
    refine hNondeg y fun x => ?_
    have hmem : bilinearFormSharp B x ∈ (bilinearFormSharp B).range := ⟨x, rfl⟩
    have h0 : ⟪bilinearFormSharp B x, y⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal _ _).mp hy _ hmem
    rwa [bilinearFormSharp_apply] at h0
  calc (bilinearFormSharp B).range = (bilinearFormSharp B).rangeᗮᗮ :=
        (Submodule.orthogonal_orthogonal _).symm
    _ = (⊥ : Submodule ℝ F)ᗮ := by rw [horth]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- The **Banach–Nečas–Babuška isomorphism**: the operator associated to a
bilinear form satisfying the inf–sup condition and nondegeneracy is a
continuous linear equivalence. -/
noncomputable def sharpEquiv {B : E →L[ℝ] F →L[ℝ] ℝ} (hInf : IsInfSup B)
    (hNondeg : IsNondegenerate B) : E ≃L[ℝ] F :=
  ContinuousLinearEquiv.ofBijective (bilinearFormSharp B)
    (sharp_ker_eq_bot hInf) (sharp_range_eq_top hInf hNondeg)

/-- The equivalence `sharpEquiv` is characterized by the bilinear form. -/
@[simp]
theorem sharpEquiv_apply {B : E →L[ℝ] F →L[ℝ] ℝ} (hInf : IsInfSup B)
    (hNondeg : IsNondegenerate B) (x : E) (y : F) :
    ⟪sharpEquiv hInf hNondeg x, y⟫_ℝ = B x y := by
  simp only [sharpEquiv, ContinuousLinearEquiv.coeFn_ofBijective]
  exact bilinearFormSharp_apply B x y

/-- The norm of `sharpEquiv` applied to `x` is the dual norm of `B x`. -/
theorem norm_sharpEquiv_apply {B : E →L[ℝ] F →L[ℝ] ℝ} (hInf : IsInfSup B)
    (hNondeg : IsNondegenerate B) (x : E) :
    ‖sharpEquiv hInf hNondeg x‖ = ‖B x‖ := by
  simp only [sharpEquiv, ContinuousLinearEquiv.coeFn_ofBijective]
  exact norm_bilinearFormSharp_apply B x

/-- Pointwise inverse bound for `sharpEquiv`: the inverse operator is bounded
by `β⁻¹` when `β` is an inf–sup constant. -/
theorem norm_sharpEquiv_symm_apply_le {B : E →L[ℝ] F →L[ℝ] ℝ} {β : ℝ} (hβ : 0 < β)
    (hB : ∀ x : E, β * ‖x‖ ≤ ‖B x‖) (hNondeg : IsNondegenerate B) (y : F) :
    ‖(sharpEquiv ⟨β, hβ, hB⟩ hNondeg).symm y‖ ≤ β⁻¹ * ‖y‖ := by
  set x := (sharpEquiv ⟨β, hβ, hB⟩ hNondeg).symm y with hx
  have hxy : sharpEquiv ⟨β, hβ, hB⟩ hNondeg x = y :=
    ContinuousLinearEquiv.apply_symm_apply _ _
  have hbound : β * ‖x‖ ≤ ‖sharpEquiv ⟨β, hβ, hB⟩ hNondeg x‖ := by
    rw [norm_sharpEquiv_apply]; exact hB x
  calc ‖x‖ ≤ β⁻¹ * ‖sharpEquiv ⟨β, hβ, hB⟩ hNondeg x‖ :=
        (le_inv_mul_iff₀ hβ).mpr hbound
    _ = β⁻¹ * ‖y‖ := by rw [hxy]

/-- Operator-norm bound for the inverse: `‖(sharpEquiv)⁻¹‖ ≤ β⁻¹`. -/
theorem norm_sharpEquiv_symm_le {B : E →L[ℝ] F →L[ℝ] ℝ} {β : ℝ} (hβ : 0 < β)
    (hB : ∀ x : E, β * ‖x‖ ≤ ‖B x‖) (hNondeg : IsNondegenerate B) :
    ‖((sharpEquiv ⟨β, hβ, hB⟩ hNondeg).symm : F →L[ℝ] E)‖ ≤ β⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hβ.le)
    (norm_sharpEquiv_symm_apply_le hβ hB hNondeg)

/-- The **Banach–Nečas–Babuška theorem**: a bilinear form satisfying the
inf–sup condition and nondegeneracy is itself a continuous linear equivalence
`E ≃L[ℝ] (F →L[ℝ] ℝ)`. -/
noncomputable def continuousLinearEquivOfBilinearForm {B : E →L[ℝ] F →L[ℝ] ℝ}
    (hInf : IsInfSup B) (hNondeg : IsNondegenerate B) : E ≃L[ℝ] (F →L[ℝ] ℝ) :=
  (sharpEquiv hInf hNondeg).trans (InnerProductSpace.toDual ℝ F).toContinuousLinearEquiv

/-- The equivalence `continuousLinearEquivOfBilinearForm` acts as `B`. -/
@[simp]
theorem continuousLinearEquivOfBilinearForm_apply {B : E →L[ℝ] F →L[ℝ] ℝ}
    (hInf : IsInfSup B) (hNondeg : IsNondegenerate B) (x : E) :
    continuousLinearEquivOfBilinearForm hInf hNondeg x = B x := by
  simp [continuousLinearEquivOfBilinearForm, sharpEquiv, bilinearFormSharp]

/-- The variational problem `B x y = φ y` for all `y` has a unique solution. -/
theorem exists_unique_apply_eq {B : E →L[ℝ] F →L[ℝ] ℝ} (hInf : IsInfSup B)
    (hNondeg : IsNondegenerate B) (φ : F →L[ℝ] ℝ) :
    ∃! x : E, ∀ y : F, B x y = φ y := by
  refine ⟨(continuousLinearEquivOfBilinearForm hInf hNondeg).symm φ, ?_, ?_⟩
  · intro y
    have h : continuousLinearEquivOfBilinearForm hInf hNondeg
        ((continuousLinearEquivOfBilinearForm hInf hNondeg).symm φ) = φ :=
      ContinuousLinearEquiv.apply_symm_apply _ _
    rw [continuousLinearEquivOfBilinearForm_apply] at h
    rw [h]
  · intro x hx
    have hBx : B x = φ := by ext y; exact hx y
    have heq : (continuousLinearEquivOfBilinearForm hInf hNondeg) x = φ := by
      rwa [continuousLinearEquivOfBilinearForm_apply]
    rw [← heq]
    exact (ContinuousLinearEquiv.symm_apply_apply _ _).symm

/-- The variational problem has a solution with the stability bound
`‖x‖ ≤ β⁻¹ * ‖φ‖`. -/
theorem exists_apply_eq_and_norm_le {B : E →L[ℝ] F →L[ℝ] ℝ} {β : ℝ} (hβ : 0 < β)
    (hB : ∀ x : E, β * ‖x‖ ≤ ‖B x‖) (hNondeg : IsNondegenerate B)
    (φ : F →L[ℝ] ℝ) :
    ∃ x : E, (∀ y : F, B x y = φ y) ∧ ‖x‖ ≤ β⁻¹ * ‖φ‖ := by
  refine ⟨(sharpEquiv ⟨β, hβ, hB⟩ hNondeg).symm
      ((InnerProductSpace.toDual ℝ F).symm φ), ?_, ?_⟩
  · intro y
    have hBx : B ((sharpEquiv ⟨β, hβ, hB⟩ hNondeg).symm
        ((InnerProductSpace.toDual ℝ F).symm φ)) = φ := by
      have h2 : bilinearFormSharp B ((sharpEquiv ⟨β, hβ, hB⟩ hNondeg).symm
          ((InnerProductSpace.toDual ℝ F).symm φ)) =
          (InnerProductSpace.toDual ℝ F).symm φ := by
        have h3 := ContinuousLinearEquiv.apply_symm_apply
          (sharpEquiv ⟨β, hβ, hB⟩ hNondeg) ((InnerProductSpace.toDual ℝ F).symm φ)
        simpa only [sharpEquiv, ContinuousLinearEquiv.coeFn_ofBijective] using h3
      have h1 : InnerProductSpace.toDual ℝ F
          (bilinearFormSharp B ((sharpEquiv ⟨β, hβ, hB⟩ hNondeg).symm
            ((InnerProductSpace.toDual ℝ F).symm φ))) = φ := by
        rw [h2]
        exact LinearIsometryEquiv.apply_symm_apply _ _
      rwa [toDual_bilinearFormSharp] at h1
    rw [hBx]
  · calc ‖(sharpEquiv ⟨β, hβ, hB⟩ hNondeg).symm
          ((InnerProductSpace.toDual ℝ F).symm φ)‖
        ≤ β⁻¹ * ‖(InnerProductSpace.toDual ℝ F).symm φ‖ :=
          norm_sharpEquiv_symm_apply_le hβ hB hNondeg _
      _ = β⁻¹ * ‖φ‖ := by
          rw [LinearIsometryEquiv.norm_map]

end MathlibExt.Analysis.InnerProductSpace.BanachNecasBabuska
