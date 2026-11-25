/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.ExactFilteredColimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-!
# A nonzero filtered module colimit with larger-world scalars

The scalar ring is the actual product of integers indexed by small types,
valued in world one. Evaluation at the natural-number type acts on the
world-zero coefficient Z/4 x Z. The sequence retains the torsion coordinate
and doubles the free coordinate, so its transition is not invertible. Projection
to Z/4 is a genuine cocone and detects a nonzero element in the native colimit.
No scalar-ring object, separator, alternative colimit or injectivity is supplied.
-/

@[expose] public section

noncomputable section

namespace MathlibExtTest.ExactFilteredModuleColimits

open CategoryTheory CategoryTheory.Limits

/-- The larger-world scalar ring, without a small-ring premise. -/
abbrev Scalar : Type 1 := Type → ℤ

/-- Actual evaluation gives the scalar action used on all coefficient modules. -/
def evaluation : Scalar →+* ℤ := Pi.evalRingHom (fun _ : Type => ℤ) ℕ

/-- The torsion coordinate has the actual restricted evaluation action. -/
instance scalarModuleTorsion : Module Scalar (ZMod 4) :=
  Module.compHom (ZMod 4) evaluation

/-- The free coordinate has the same restricted evaluation action. -/
instance scalarModuleInteger : Module Scalar ℤ := Module.compHom ℤ evaluation

/-- Original small coefficients retain both nonzero torsion and a free coordinate. -/
def M : ModuleCat.{0} Scalar := ModuleCat.of Scalar (ZMod 4 × ℤ)

/-- The actual torsion coordinate as a small module over the same large ring. -/
def T : ModuleCat.{0} Scalar := ModuleCat.of Scalar (ZMod 4)

/-- The transition preserves torsion and doubles the free coordinate. -/
def step : M ⟶ M :=
  ModuleCat.ofHom ((LinearMap.id : ZMod 4 →ₗ[Scalar] ZMod 4).prodMap
    ((2 : ℕ) • (LinearMap.id : ℤ →ₗ[Scalar] ℤ)))

/-- The transition's torsion coordinate is literally retained. -/
theorem step_torsion (x : M) : (step.hom x).1 = x.1 := rfl

/-- The free coordinate is multiplied by two. -/
theorem step_free (x : M) : (step.hom x).2 = 2 * x.2 := by
  change (2 : ℕ) • x.2 = 2 * x.2
  norm_num [nsmul_eq_mul]

/-- These transitions are genuinely noninvertible. -/
theorem step_not_isIso : ¬ IsIso step := by
  intro h
  let : IsIso step := h
  have hs : Function.Surjective step.hom := (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨x, hx⟩ := hs (0, 1)
  have hf := congrArg (fun y : M => y.2) hx
  rw [step_free] at hf
  omega

/-- The actual filtered diagram uses the native sequence constructor. -/
def diagram : ℕ ⥤ ModuleCat.{0} Scalar :=
  Functor.ofSequence (X := fun _ => M) (fun _ => step)

/-- Its adjacent morphism is the original transition, not a chosen comparison. -/
theorem diagram_succ (n : ℕ) :
    diagram.map (homOfLE (Nat.le_add_right n 1)) = step :=
  Functor.ofSequence_map_homOfLE_succ (fun _ => step) n

/-- Native module colimits of this filtered shape are exact across the unequal worlds. -/
theorem exact_filtered_shape : HasExactColimitsOfShape ℕ (ModuleCat.{0} Scalar) :=
  ModuleCat.hasExactFilteredColimitsOfShape Scalar ℕ

/-- The actual colimit functor retains finite-limit preservation from that capability. -/
theorem colim_preserves_finite_limits :
    PreservesFiniteLimits (colim (J := ℕ) (C := ModuleCat.{0} Scalar)) := by
  let := exact_filtered_shape
  infer_instance

/-- Projection onto the actual retained torsion coefficient. -/
def torsionProjection : M ⟶ T := ModuleCat.ofHom (LinearMap.fst Scalar (ZMod 4) ℤ)

/-- The original transition commutes with the detecting projection. -/
theorem step_projection : step ≫ torsionProjection = torsionProjection := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Native sequence naturality packages the detecting maps into a real cocone. -/
def detectingCocone : Cocone diagram where
  pt := T
  ι := NatTrans.ofSequence (fun _ => torsionProjection) (fun n => by
    rw [diagram_succ n]
    change step ≫ torsionProjection = torsionProjection ≫ 𝟙 T
    simpa only [Category.comp_id] using step_projection)

/-- The nonzero original torsion coefficient. -/
def one : M := (1, 0)

/-- The native colimit injection is detected by an actual module map to Z/4. -/
theorem detect_native_colimit_one :
    (colimit.desc diagram detectingCocone).hom ((colimit.ι diagram 0).hom one) = (1 : ZMod 4) := by
  have h := congrArg (fun f : M ⟶ T => f.hom one) (colimit.ι_desc detectingCocone 0)
  change (colimit.desc diagram detectingCocone).hom
    ((colimit.ι diagram 0).hom one) = (1 : ZMod 4) at h
  exact h

/-- The actually chosen native colimit has a nonzero element. -/
theorem native_colimit_one_nonzero : (colimit.ι diagram 0).hom one ≠ 0 := by
  intro h
  have hz : (colimit.desc diagram detectingCocone).hom ((colimit.ι diagram 0).hom one) = 0 := by
    rw [h, map_zero]
  exact (by decide : (1 : ZMod 4) ≠ 0) (detect_native_colimit_one.symm.trans hz)

end MathlibExtTest.ExactFilteredModuleColimits
