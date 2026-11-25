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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOneNaturality

/-!
# Functoriality of the degree-one cup product

The inhomogeneous degree-`(1, 1)` cup representative is natural jointly in a
group homomorphism and two compatible coefficient morphisms.  This is the
representative-level statement needed to compare cup classes after restricting
the acting group and changing coefficients.

No injectivity, surjectivity, inflation, restriction, or comparison theorem is
asserted here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable {A B : Rep k H} {A' B' : Rep k G}

/-- Joint group-and-coefficient naturality of the degree-`(1, 1)` cup
representative. -/
theorem mapCocycles₂_cupCocycleOneOne_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ A') (psi : Rep.res f B ⟶ B')
    (x : cocycles₁ A) (y : cocycles₁ B) :
    mapCocycles₂ f (phi ⊗ₘ psi) (cupCocycleOneOne A B x y) =
      cupCocycleOneOne A' B'
        (mapCocycles₁ f phi x) (mapCocycles₁ f psi y) := by
  apply cocycles₂_ext
  intro p q
  change (phi ⊗ₘ psi).hom
      (x (f p) ⊗ₜ[k] B.ρ (f p) (y (f q))) =
    phi.hom (x (f p)) ⊗ₜ[k] B'.ρ p (psi.hom (y (f q)))
  rw [Rep.hom_tensorHom, Representation.IntertwiningMap.tensor_apply]
  congr 1
  simpa using Rep.hom_comm_apply psi p (y (f q))

end groupCohomology
