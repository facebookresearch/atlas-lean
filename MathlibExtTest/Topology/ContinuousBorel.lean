/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ContinuousBorel
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Topology.ContinuousBorel` -/

noncomputable section

open CategoryTheory
open MathlibExt.Topology.ContinuousBorel

private def two : ℂˣ := Units.mk0 2 (by norm_num)

/-- A nontrivial scalar orbit is normalized by division by its group coordinate. -/
example : levelZero ℂˣ (TopCat.of ℂ)
    (Quotient.mk'' ((fun _ : Fin 1 => two), (6 : ℂ))) = 3 := by
  change two⁻¹ • (6 : ℂ) = 3
  norm_num [two, Units.smul_def, smul_eq_mul]

/-- The inverse normalization puts the identity in the group coordinate. -/
example (x : ℂ) :
    (levelZero ℂˣ (TopCat.of ℂ)).symm x = Quotient.mk'' ((fun _ : Fin 1 => 1), x) :=
  rfl

section

variable (G : Type) [Group G] [TopologicalSpace G] (Z : TopCat.{0}) [MulAction G Z]

/-- Reindexing along the identity is the identity of a bar level. -/
example (n : ℕ) (p : BarLevel G Z n) : barMap G Z id p = p := by
  induction p using Quotient.inductionOn
  rfl

/-- Reindexing is contravariantly functorial. -/
example {l m n : ℕ} (f : Fin (l + 1) → Fin (m + 1)) (g : Fin (m + 1) → Fin (n + 1))
    (p : BarLevel G Z n) : barMap G Z f (barMap G Z g p) = barMap G Z (g ∘ f) p := by
  induction p using Quotient.inductionOn
  rfl

/-- A face map forgets a group coordinate and keeps the space coordinate. -/
example (p : Homogeneous G Z 1) :
    barMap G Z (fun _ : Fin 1 => (1 : Fin 2)) (Quotient.mk _ p) =
      Quotient.mk _ ((fun _ : Fin 1 => p.1 1), p.2) :=
  rfl

variable {G Z}

/-- The augmentation evaluates the invariant map on the space coordinate. -/
example {Q : TopCat.{0}} (q : Z ⟶ Q) (hq : ∀ (g : G) (x : Z), q (g • x) = q x) (n : ℕ)
    (p : Homogeneous G Z n) : quotientAugmentation q hq n (Quotient.mk _ p) = q p.2 :=
  rfl

/-- An equivariant map acts on the space coordinate of a bar level. -/
example {W : TopCat.{0}} [MulAction G W] (f : Z ⟶ W)
    (hf : ∀ (g : G) (x : Z), f (g • x) = g • f x) (n : ℕ) (p : Homogeneous G Z n) :
    levelEquivariantMap f hf n (Quotient.mk _ p) = Quotient.mk _ (p.1, f p.2) :=
  rfl

end

/-- The scaling action of `ℂˣ` on `ℂ` (with the two orbits `{0}` and `ℂˣ`) has a
Borel model, with the augmentation to a point induced by the constant invariant
map, and the Borel map of the identity. -/
example : borel ℂˣ (TopCat.of ℂ) ⟶ TopCat.of PUnit :=
  borelToQuotient (TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩) fun _ _ => rfl

example : borel ℂˣ (TopCat.of ℂ) ⟶ borel ℂˣ (TopCat.of ℂ) :=
  borelMap (𝟙 (TopCat.of ℂ)) fun _ _ => rfl

end
