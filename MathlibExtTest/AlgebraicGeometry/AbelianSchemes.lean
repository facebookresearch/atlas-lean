/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AbelianSchemes

/-!
# General arithmetic interface probes

The actual trivial abelian scheme over Spec Z checks that the public group
and zero-section interfaces require no field base.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.AlgebraicGeometry.AbelianSchemes

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open scoped CategoryTheory.MonObj

def trivial (S : Scheme) : AbelianScheme S where
  model := 𝟙_ (Over S)
  group := inferInstance
  commutative := inferInstance
  smooth := by change Smooth (𝟙 S); infer_instance
  proper := by change IsProper (𝟙 S); infer_instance
  connected := by
    change GeometricallyConnected (𝟙 S)
    constructor
    intro K _ y Z fst snd h
    have : IsIso snd := h.isIso_snd_of_isIso
    exact snd.homeomorph.connectedSpace_iff.mpr inferInstance

example (T : Over (Spec (.of ℤ))) :
    zeroSectionAt (trivial (Spec (.of ℤ))) T ≫
      (prod.snd : prod (trivial (Spec (.of ℤ))).model T ⟶ T) = 𝟙 T := by
  exact prod.lift_snd _ _

section General

variable {S T : Scheme} (A : AbelianScheme S)

-- Base change is the pullback, with the pulled-back group law found by instance search.
example (f : T ⟶ S) : (A.baseChange f).model = (Over.pullback f).obj A.model := rfl

example (f : T ⟶ S) : GrpObj ((Over.pullback f).obj A.model) := inferInstance

-- The fibre at a point is the base change to its residue field.
example (s : S) : A.fibre s = A.baseChange (S.fromSpecResidueField s) := rfl

-- Multiplication by `n` is the `n`-th power in the commutative group of endomorphisms.
example : A.multiplication 1 = 𝟙 A.model := zpow_one _

example (m n : ℤ) : A.multiplication (m + n) = A.multiplication m * A.multiplication n :=
  zpow_add _ m n

example (m n : ℤ) : A.multiplication m * A.multiplication n =
    A.multiplication n * A.multiplication m :=
  mul_comm _ _

-- The zero section in a product is a section of the second projection.
example (T : Over S) : zeroSectionAt A T ≫ (prod.snd : prod A.model T ⟶ T) = 𝟙 T :=
  prod.lift_snd _ _

-- Pulling a family back along the identity of the parameter scheme gives the family back.
theorem familyPullback_id_iso (A D : Over S) (P : (prod A D).left.Modules) :
    Nonempty (familyPullback A D D P (𝟙 D) ≅ P) := by
  unfold familyPullback
  have h : (prod.map (𝟙 A) (𝟙 D)).left = 𝟙 (prod A D).left := by simp
  exact ⟨((Scheme.Modules.pullbackCongr h).app P) ≪≫ (Scheme.Modules.pullbackId _).app P⟩

-- The Poincaré family is classified by the identity of the dual.
example (D : DualAbelianScheme A) :
    D.classifyingMap D.dual.model D.poincare D.lineBundle D.normalized
      D.fibrewisePicardZero = 𝟙 D.dual.model :=
  (D.universal D.dual.model D.poincare D.lineBundle D.normalized
    D.fibrewisePicardZero).unique (D.classifyingMap_family ..) (familyPullback_id_iso ..)

-- `T`-valued points form a commutative group.
example (T : Over S) : CommGroup (A.Points T) := inferInstance

end General

end MathlibExtTest.AlgebraicGeometry.AbelianSchemes
