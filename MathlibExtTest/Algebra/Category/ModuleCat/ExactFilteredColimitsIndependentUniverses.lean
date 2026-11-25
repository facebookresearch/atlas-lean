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
# A nonzero filtered module colimit over larger-universe scalars

The scalar ring is a product of integers indexed by small types and lies in
universe one. Evaluation at the natural-number type acts on the universe-zero
module `ℤ/4 × ℤ`. Transition maps preserve the torsion coordinate and double
the free coordinate. Projection to `ℤ/4` defines a detecting cocone and proves
that the colimit contains a nonzero element.
-/

@[expose] public section

noncomputable section

namespace MathlibExtTest.ExactFilteredModuleColimits

open CategoryTheory CategoryTheory.Limits

/-- The scalar ring lies in universe one. -/
abbrev Scalar : Type 1 := Type → ℤ

/-- Evaluation at the natural-number type determines the scalar action. -/
def evaluation : Scalar →+* ℤ := Pi.evalRingHom (fun _ : Type => ℤ) ℕ

/-- The torsion coordinate carries the evaluation action. -/
instance scalarModuleTorsion : Module Scalar (ZMod 4) :=
  Module.compHom (ZMod 4) evaluation

/-- The integer coordinate carries the same evaluation action. -/
instance scalarModuleInteger : Module Scalar ℤ := Module.compHom ℤ evaluation

/-- The universe-zero module has a torsion coordinate and an integer coordinate. -/
def M : ModuleCat.{0} Scalar := ModuleCat.of Scalar (ZMod 4 × ℤ)

/-- The torsion module over the larger-universe scalar ring. -/
def T : ModuleCat.{0} Scalar := ModuleCat.of Scalar (ZMod 4)

/-- The transition preserves torsion and doubles the free coordinate. -/
def step : M ⟶ M :=
  ModuleCat.ofHom ((LinearMap.id : ZMod 4 →ₗ[Scalar] ZMod 4).prodMap
    ((2 : ℕ) • (LinearMap.id : ℤ →ₗ[Scalar] ℤ)))

/-- The transition fixes the torsion coordinate. -/
theorem step_torsion (x : M) : (step.hom x).1 = x.1 := rfl

/-- The free coordinate is multiplied by two. -/
theorem step_free (x : M) : (step.hom x).2 = 2 * x.2 := by
  change (2 : ℕ) • x.2 = 2 * x.2
  norm_num [nsmul_eq_mul]

/-- The transition is not invertible. -/
theorem step_not_isIso : ¬ IsIso step := by
  intro h
  let : IsIso step := h
  have hs : Function.Surjective step.hom := (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨x, hx⟩ := hs (0, 1)
  have hf := congrArg (fun y : M => y.2) hx
  rw [step_free] at hf
  omega

/-- The sequence diagram formed by the transition maps. -/
def diagram : ℕ ⥤ ModuleCat.{0} Scalar :=
  Functor.ofSequence (X := fun _ => M) (fun _ => step)

/-- Every adjacent map is the transition. -/
theorem diagram_succ (n : ℕ) :
    diagram.map (homOfLE (Nat.le_add_right n 1)) = step :=
  Functor.ofSequence_map_homOfLE_succ (fun _ => step) n

/-- Filtered colimits of these modules are exact across the two universes. -/
theorem exact_filtered_shape : HasExactColimitsOfShape ℕ (ModuleCat.{0} Scalar) :=
  ModuleCat.hasExactFilteredColimitsOfShape Scalar ℕ

/-- The colimit functor preserves finite limits. -/
theorem colim_preserves_finite_limits :
    PreservesFiniteLimits (colim (J := ℕ) (C := ModuleCat.{0} Scalar)) := by
  let := exact_filtered_shape
  infer_instance

/-- Projection onto the torsion coordinate. -/
def torsionProjection : M ⟶ T := ModuleCat.ofHom (LinearMap.fst Scalar (ZMod 4) ℤ)

/-- The transition commutes with the detecting projection. -/
theorem step_projection : step ≫ torsionProjection = torsionProjection := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- The detecting projections form a cocone over the sequence. -/
def detectingCocone : Cocone diagram where
  pt := T
  ι := NatTrans.ofSequence (fun _ => torsionProjection) (fun n => by
    rw [diagram_succ n]
    change step ≫ torsionProjection = torsionProjection ≫ 𝟙 T
    simpa only [Category.comp_id] using step_projection)

/-- A nonzero torsion element. -/
def one : M := (1, 0)

/-- The colimit injection is detected by a module map to `ℤ/4`. -/
theorem detect_native_colimit_one :
    (colimit.desc diagram detectingCocone).hom ((colimit.ι diagram 0).hom one) = (1 : ZMod 4) := by
  have h := congrArg (fun f : M ⟶ T => f.hom one) (colimit.ι_desc detectingCocone 0)
  change (colimit.desc diagram detectingCocone).hom
    ((colimit.ι diagram 0).hom one) = (1 : ZMod 4) at h
  exact h

/-- The colimit contains a nonzero element. -/
theorem native_colimit_one_nonzero : (colimit.ι diagram 0).hom one ≠ 0 := by
  intro h
  have hz : (colimit.desc diagram detectingCocone).hom ((colimit.ι diagram 0).hom one) = 0 := by
    rw [h, map_zero]
  exact (by decide : (1 : ZMod 4) ≠ 0) (detect_native_colimit_one.symm.trans hz)

end MathlibExtTest.ExactFilteredModuleColimits
