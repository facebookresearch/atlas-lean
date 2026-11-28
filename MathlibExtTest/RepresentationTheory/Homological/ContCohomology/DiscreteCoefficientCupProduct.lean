/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import
  MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientCupAssociativity
import Mathlib.Tactic.NormNum

/-! # Public continuous tensor cup clients -/

noncomputable section
set_option autoImplicit false

open CategoryTheory ContinuousCohomology
open scoped TensorProduct
universe u v w

namespace ContinuousTensorCupTest

private abbrev integerCoefficient (G : ProfiniteGrp.{0}) : TopRep.{0, 0, 0} ℤ G :=
  TopRep.of (ContRepresentation.trivial ℤ G ℤ)

private def integerZeroCochain (G : ProfiniteGrp.{0}) (a : ℤ) :
    flatHomogeneousCochains (integerCoefficient G) 0 :=
  ⟨⟨fun _ => a, continuous_const⟩, fun _ _ => rfl⟩

example (G : ProfiniteGrp.{0}) :
    DiscreteTopology (discreteTensorCoefficient (integerCoefficient G) (integerCoefficient G)) :=
  inferInstance

example (G : ProfiniteGrp.{0}) :
    ContinuousSMul ℤ (discreteTensorCoefficient (integerCoefficient G) (integerCoefficient G)) :=
  inferInstance

-- A concrete action computation uses the public tensor coefficient, for every group element.
example (G : ProfiniteGrp.{0}) (h : G) :
    (discreteTensorCoefficient (integerCoefficient G) (integerCoefficient G)).ρ h
        ((2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ)) = (2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ) := by
  simpa only [integerCoefficient, ContRepresentation.trivial_apply] using
    discreteTensorCoefficient_action_tmul (integerCoefficient G) (integerCoefficient G) h 2 3

-- Both zero-degree factors use the same actual one-coordinate tuple.
example (G : ProfiniteGrp.{0}) (t : Fin 1 → G) :
    (TensorProduct.lid ℤ ℤ)
      ((flatHomogeneousCup (integerCoefficient G) (integerCoefficient G) 0 0
        (integerZeroCochain G 2) (integerZeroCochain G 3)).val t) = 6 := by
  rw [flatHomogeneousCup_apply]
  change (TensorProduct.lid ℤ ℤ) ((2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ)) = 6
  norm_num [TensorProduct.lid_tmul]

variable {R : Type u} [CommRing R] [TopologicalSpace R] {G : ProfiniteGrp.{v}}
variable (A B C : TopRep.{max v w, u, v} R G)
variable [DiscreteTopology A] [DiscreteTopology B] [DiscreteTopology C]

-- This client retains the independent ring, group and coefficient universes.
example (p q : ℕ) (x : cocycles A p) (y : cocycles B q) :
    discreteContinuousCup A B p q (π A p x) (π B q y) =
      π (discreteTensorCoefficient A B) (p + q) (discreteContinuousCupCocycles A B p q x y) :=
  discreteContinuousCup_pi A B p q x y

example (p q : ℕ) (x : continuousCohomology p A) (y : continuousCohomology q B) :
    discreteContinuousCupTensorMap A B p q (x ⊗ₜ[R] y) =
      discreteContinuousCup A B p q x y :=
  discreteContinuousCupTensorMap_tmul A B p q x y

example (A' B' : TopRep.{max v w, u, v} R G)
    [DiscreteTopology A'] [DiscreteTopology B'] (f : A ⟶ A') (g : B ⟶ B')
    (p q : ℕ) (x : continuousCohomology p A) (y : continuousCohomology q B) :
    ContinuousCohomology.map (ContinuousMonoidHom.id G) (discreteTensorCoefficientMap f g)
        (p + q) (discreteContinuousCup A B p q x y) =
      discreteContinuousCup A' B' p q
        (ContinuousCohomology.map (ContinuousMonoidHom.id G) f p x)
        (ContinuousCohomology.map (ContinuousMonoidHom.id G) g q y) :=
  discreteContinuousCup_naturality f g p q x y

example (p q r : ℕ) (x : continuousCohomology p A) (y : continuousCohomology q B)
    (z : continuousCohomology r C) :
    ((ContinuousCohomology.map (ContinuousMonoidHom.id G)
        (discreteTensorCoefficientAssociator A B C).hom ((p + q) + r)) ≫
      eqToHom (congrArg (fun n => continuousCohomology n
        (discreteTensorCoefficient A (discreteTensorCoefficient B C))) (Nat.add_assoc p q r))).hom
      (discreteContinuousCup (discreteTensorCoefficient A B) C (p + q) r
        (discreteContinuousCup A B p q x y) z) =
      discreteContinuousCup A (discreteTensorCoefficient B C) p (q + r) x
        (discreteContinuousCup B C q r y z) :=
  discreteContinuousCup_assoc A B C p q r x y z

end ContinuousTensorCupTest
