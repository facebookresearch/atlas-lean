/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The actual weighted Griess form realized as a Euclidean inner product.
This module supplies the proper normed space and the continuous multiplication
needed for the analytic finiteness criterion.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxialVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneralAxialVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessCommutativity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The full 196884-dimensional real Euclidean realization of the Griess space. -/
abbrev GriessEuclidean := EuclideanSpace ℝ (Fin 196884)

/-- Multiply each dictionary coordinate by the square root of its actual form weight. -/
noncomputable def griessWeightEquiv : GriessSpace ≃ₗ[ℝ] GriessSpace :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero ℝ ℝ
    (Real.sqrt (griessBasisWeight i))
    (ne_of_gt (Real.sqrt_pos.mpr (griessBasisWeight_pos i)))

/-- A genuine linear identification with Euclidean space, rather than its sup norm. -/
noncomputable def griessEuclideanEquiv : GriessSpace ≃ₗ[ℝ] GriessEuclidean :=
  griessWeightEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin 196884 → ℝ)).symm

/-- The weighted Euclidean coordinates. -/
theorem griessEuclideanEquiv_apply (x : GriessSpace) (i : Fin 196884) :
    griessEuclideanEquiv x i = Real.sqrt (griessBasisWeight i) * x i := rfl

/-- The Euclidean inner product is exactly the actual source-weighted Griess form. -/
theorem griessEuclidean_inner (x y : GriessSpace) :
    inner ℝ (griessEuclideanEquiv x) (griessEuclideanEquiv y) = griessForm x y := by
  rw [griessForm_apply, PiLp.inner_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i hi
  simp only [RCLike.inner_apply, conj_trivial]
  change (Real.sqrt (griessBasisWeight i) * y i) *
    (Real.sqrt (griessBasisWeight i) * x i) = griessBasisWeight i * x i * y i
  have hs := Real.mul_self_sqrt (griessBasisWeight_pos i).le
  calc
    _ = (Real.sqrt (griessBasisWeight i) * Real.sqrt (griessBasisWeight i)) *
      (x i * y i) := by ring
    _ = _ := by rw [hs]; ring

/-- The actual Griess squared length is the squared Euclidean norm. -/
theorem griessEuclidean_norm_sq (x : GriessSpace) :
    ‖griessEuclideanEquiv x‖ ^ 2 = griessForm x x := by
  rw [← real_inner_self_eq_norm_sq, griessEuclidean_inner]

/-- The Euclidean realization has the full stated dimension. -/
theorem griessEuclidean_finrank : Module.finrank ℝ GriessEuclidean = 196884 := by
  simp [GriessEuclidean]

/-- Closed bounded balls in the Euclidean realization are compact. -/
theorem griessEuclidean_proper : ProperSpace GriessEuclidean := inferInstance

/-- Conjugation of an ambient Griess operator into the Euclidean coordinates. -/
noncomputable def griessEuclideanTransport :
    (GriessSpace ≃ₗ[ℝ] GriessSpace) →* (GriessEuclidean ≃ₗ[ℝ] GriessEuclidean) :=
  coordinateGLTransport griessEuclideanEquiv

theorem griessEuclideanTransport_apply (e : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (x : GriessEuclidean) :
    griessEuclideanTransport e x =
      griessEuclideanEquiv (e (griessEuclideanEquiv.symm x)) := rfl

/-- An operator preserving the actual Griess form acts isometrically on Euclidean coordinates. -/
theorem griessEuclideanTransport_inner
    (e : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (he : ∀ x y, griessForm (e x) (e y) = griessForm x y)
    (x y : GriessEuclidean) :
    inner ℝ (griessEuclideanTransport e x) (griessEuclideanTransport e y) = inner ℝ x y := by
  rw [griessEuclideanTransport_apply, griessEuclideanTransport_apply, griessEuclidean_inner, he]
  rw [← griessEuclidean_inner, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Triality is an actual Euclidean isometry. -/
noncomputable def sExtraEuclideanIsometry : GriessEuclidean ≃ₗᵢ[ℝ] GriessEuclidean :=
  (griessEuclideanTransport sExtra).isometryOfInner
    (griessEuclideanTransport_inner sExtra sExtra_preserves_griessForm)

/-- Every actual local operator is a Euclidean isometry, using its proved form law. -/
noncomputable def rhoLocalEuclideanIsometry (h : H) :
    GriessEuclidean ≃ₗᵢ[ℝ] GriessEuclidean :=
  (griessEuclideanTransport (rhoLocal h)).isometryOfInner
    (griessEuclideanTransport_inner (rhoLocal h) (rhoLocal_form h))

/-- Every element of the actual generated group is a Euclidean isometry. -/
noncomputable def generatedEuclideanIsometry (g : G) :
    GriessEuclidean ≃ₗᵢ[ℝ] GriessEuclidean :=
  (griessEuclideanTransport g.val).isometryOfInner
    (griessEuclideanTransport_inner g.val (generated_group_preserves_griessForm g))

/-- The actual Griess multiplication transported to the Euclidean realization. -/
noncomputable def griessEuclideanProductLinear :
    GriessEuclidean →ₗ[ℝ] GriessEuclidean →ₗ[ℝ] GriessEuclidean :=
  (griessProd.compl₁₂ griessEuclideanEquiv.symm.toLinearMap
    griessEuclideanEquiv.symm.toLinearMap).compr₂ griessEuclideanEquiv.toLinearMap

/-- Finite dimensionality upgrades the concrete bilinear multiplication to a
continuous bilinear operator with a genuine finite operator norm. -/
noncomputable def griessEuclideanProduct :
    GriessEuclidean →L[ℝ] GriessEuclidean →L[ℝ] GriessEuclidean :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp griessEuclideanProductLinear)

set_option maxRecDepth 10000 in
-- Removing the bundled-coordinate coercions traverses the full finite coordinate type.
/-- Continuous multiplication evaluates to the actual Griess multiplication. -/
theorem griessEuclideanProduct_apply (x y : GriessEuclidean) :
    griessEuclideanProduct x y = griessEuclideanEquiv
      (griessProd (griessEuclideanEquiv.symm x) (griessEuclideanEquiv.symm y)) := by
  simp only [griessEuclideanProduct, LinearMap.coe_toContinuousLinearMap',
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  simp only [griessEuclideanProductLinear, LinearMap.compr₂_apply,
    LinearMap.compl₁₂_apply]
  exact rfl

/-- The actual continuous Euclidean multiplication is commutative. -/
theorem griessEuclideanProduct_comm (x y : GriessEuclidean) :
    griessEuclideanProduct x y = griessEuclideanProduct y x := by
  rw [griessEuclideanProduct_apply, griessEuclideanProduct_apply, griessProd_comm]

/-- The generated group acts on the Euclidean realization by conjugation. -/
noncomputable def griessEuclideanGroupAction : G →*
    (GriessEuclidean ≃ₗ[ℝ] GriessEuclidean) :=
  griessEuclideanTransport.comp G.subtype

/-- Euclidean conjugation loses no information about the actual group. -/
theorem griessEuclideanGroupAction_injective : Function.Injective griessEuclideanGroupAction := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hx := congrArg (fun e : GriessEuclidean ≃ₗ[ℝ] GriessEuclidean =>
    e (griessEuclideanEquiv x)) he
  change griessEuclideanEquiv (g.val (griessEuclideanEquiv.symm (griessEuclideanEquiv x))) =
    griessEuclideanEquiv (h.val (griessEuclideanEquiv.symm (griessEuclideanEquiv x))) at hx
  rw [LinearEquiv.symm_apply_apply] at hx
  exact griessEuclideanEquiv.injective hx

/-- The same generated group, represented faithfully in Euclidean coordinates. -/
noncomputable def griessEuclideanGeneratedGroup : Subgroup
    (GriessEuclidean ≃ₗ[ℝ] GriessEuclidean) := griessEuclideanGroupAction.range

/-- Faithful Euclidean conjugation is an actual group isomorphism onto its image. -/
noncomputable def griessEuclideanGroupEquiv : G ≃* griessEuclideanGeneratedGroup :=
  MonoidHom.ofInjective griessEuclideanGroupAction_injective

/-- Every element of the Euclidean generated group preserves the Euclidean norm. -/
theorem griessEuclideanGeneratedGroup_norm (g : griessEuclideanGeneratedGroup)
    (x : GriessEuclidean) : ‖g.val x‖ = ‖x‖ := by
  obtain ⟨h, hh⟩ := g.property
  change griessEuclideanGroupAction h = g.val at hh
  rw [← hh]
  exact (generatedEuclideanIsometry h).norm_map x

/-- Product invariance transports faithfully into the Euclidean model. -/
theorem griessEuclideanTransport_product
    (e : GriessSpace ≃ₗ[ℝ] GriessSpace)
    (he : ∀ x y, e (griessProd x y) = griessProd (e x) (e y))
    (x y : GriessEuclidean) :
    griessEuclideanTransport e (griessEuclideanProduct x y) =
      griessEuclideanProduct (griessEuclideanTransport e x) (griessEuclideanTransport e y) := by
  rw [griessEuclideanProduct_apply, griessEuclideanTransport_apply,
    LinearEquiv.symm_apply_apply, he, griessEuclideanProduct_apply,
    griessEuclideanTransport_apply, griessEuclideanTransport_apply,
    LinearEquiv.symm_apply_apply]
  rw [LinearEquiv.symm_apply_apply]

/-- Conway's actual distinguished axis in the proper Euclidean realization. -/
noncomputable def griessEuclideanAxis (p : Fin 276) : GriessEuclidean :=
  griessEuclideanEquiv (conwayAxis p)

/-- The transported axis is the same scaled idempotent. -/
theorem griessEuclideanAxis_square (p : Fin 276) :
    griessEuclideanProduct (griessEuclideanAxis p) (griessEuclideanAxis p) =
      (64 : ℝ) • griessEuclideanAxis p := by
  simp only [griessEuclideanAxis, griessEuclideanProduct_apply,
    LinearEquiv.symm_apply_apply, conwayAxis_square, map_smul]

/-- The transported axis has exactly the source squared norm. -/
theorem griessEuclideanAxis_norm_sq (p : Fin 276) : ‖griessEuclideanAxis p‖ ^ 2 = 128 := by
  rw [griessEuclideanAxis, griessEuclidean_norm_sq, conwayAxis_square_length]

/-- The continuous linearized scaled-idempotent equation at the actual source axis. -/
noncomputable def griessAxisLinearization (p : Fin 276) :
    GriessEuclidean →L[ℝ] GriessEuclidean :=
  (64 : ℝ) • ContinuousLinearMap.id ℝ GriessEuclidean -
    (2 : ℝ) • griessEuclideanProduct (griessEuclideanAxis p)

/-- The linearized operator has exactly the coefficients used by the isolation criterion. -/
theorem griessAxisLinearization_apply (p : Fin 276) (x : GriessEuclidean) :
    griessAxisLinearization p x =
      (64 : ℝ) • x - (2 : ℝ) • griessEuclideanProduct (griessEuclideanAxis p) x := by
  simp only [griessAxisLinearization, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply]

/-- Every signed-short source axis in the genuine Euclidean realization. -/
noncomputable def griessEuclideanShortAxis (r : GriessShortIndex) (c : ZMod 2) :
    GriessEuclidean := griessEuclideanEquiv (conwayShortAxis r c)

/-- Every signed-short axis remains a scaled idempotent after transport. -/
theorem griessEuclideanShortAxis_square (r : GriessShortIndex) (c : ZMod 2) :
    griessEuclideanProduct (griessEuclideanShortAxis r c) (griessEuclideanShortAxis r c) =
      (64 : ℝ) • griessEuclideanShortAxis r c := by
  simp only [griessEuclideanShortAxis, griessEuclideanProduct_apply,
    LinearEquiv.symm_apply_apply, conwayShortAxis_square, map_smul]

/-- The entire source axis family has the exact squared norm 128. -/
theorem griessEuclideanShortAxis_norm_sq (r : GriessShortIndex) (c : ZMod 2) :
    ‖griessEuclideanShortAxis r c‖ ^ 2 = 128 := by
  rw [griessEuclideanShortAxis, griessEuclidean_norm_sq, conwayShortAxis_norm_sq]

/-- The continuous linearized equation for each signed-short source axis. -/
noncomputable def griessShortAxisLinearization (r : GriessShortIndex) (c : ZMod 2) :
    GriessEuclidean →L[ℝ] GriessEuclidean :=
  (64 : ℝ) • ContinuousLinearMap.id ℝ GriessEuclidean -
    (2 : ℝ) • griessEuclideanProduct (griessEuclideanShortAxis r c)

theorem griessShortAxisLinearization_apply (r : GriessShortIndex) (c : ZMod 2)
    (x : GriessEuclidean) :
    griessShortAxisLinearization r c x =
      (64 : ℝ) • x - (2 : ℝ) • griessEuclideanProduct (griessEuclideanShortAxis r c) x := by
  simp only [griessShortAxisLinearization, sub_apply, smul_apply, ContinuousLinearMap.id_apply]

/-- Finiteness proved in the Euclidean representation transfers back to the actual G. -/
theorem generated_group_finite_of_euclidean [Finite griessEuclideanGeneratedGroup] : Finite G :=
  Finite.of_injective griessEuclideanGroupEquiv griessEuclideanGroupEquiv.injective

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
