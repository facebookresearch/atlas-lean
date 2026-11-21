/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NeronModels

/-!
# General arithmetic interface probes

The residue comparison evaluates an actual global regular constant after
reducing the integral identity point on Spec R, for every local ring R.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.AlgebraicGeometry.NeronModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.NeronModels
open MathlibExt.AlgebraicGeometry.SemistableModels

variable (R : Type) [CommRing R] [IsLocalRing R]

def identityModel : Over (trait R) := Over.mk (𝟙 (trait R))

def reducedIdentity : SpecialPoint R (identityModel R) :=
  reducePoint R (identityModel R) ⟨𝟙 (trait R), by simp [identityModel]⟩

example (a : R) :
    (Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).hom.hom
      (((reducedIdentity R).1 ≫
        pullback.fst (identityModel R).hom (specialInclusion R)).appTop.hom
          ((Scheme.ΓSpecIso (.of R)).inv.hom a)) = IsLocalRing.residue R a := by
  have hp : (reducedIdentity R).1 ≫
      pullback.fst (identityModel R).hom (specialInclusion R) =
      specialInclusion R := by
    simp [reducedIdentity, reducePoint, identityModel]
  rw [hp]
  have h :
      (Scheme.ΓSpecIso (.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))).appTop ≫
          (Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField R))).hom =
      CommRingCat.ofHom (IsLocalRing.residue R) := by
    rw [Scheme.ΓSpecIso_naturality, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  exact congrArg (fun f : CommRingCat.of R ⟶
    CommRingCat.of (IsLocalRing.ResidueField R) ↦ f.hom a) h

end MathlibExtTest.AlgebraicGeometry.NeronModels
