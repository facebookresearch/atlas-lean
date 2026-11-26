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
# Group and coefficient naturality of one-cocycle cups

Let `f : G →* H` be a homomorphism of groups, `k` a commutative ring, `A,B` representations of
`H`, and `A',B'` representations of `G`. For equivariant maps `φ : Rep.res f A → A'` and `ψ :
Rep.res f B → B'`, pulling back one-cocycles along `f` and applying `φ,ψ` commutes with their
degree-`(1,1)` cup. The pulled-back cochain is `g ↦ φ(x(f g))`, and the cup formula is `(x ∪
y)(g,h) = x(g) ⊗ g·y(h)`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable {A B : Rep k H} {A' B' : Rep k G}

/-- Let `k` be a commutative ring, `f : G →* H` a group homomorphism, `A,B : Rep k H`, and `A',B'
: Rep k G`. For morphisms `φ : Rep.res f A → A'`, `ψ : Rep.res f B → B'` and one-cocycles
`x,y` with values in `A,B`, respectively, `mapCocycles₂ f (φ ⊗ ψ) (x ∪ y) = (mapCocycles₁ f φ
x) ∪ (mapCocycles₁ f ψ y)` in `Z²(G,A' ⊗ B')`. The maps on one-cocycles have pointwise values
`φ(x(f g))` and `ψ(y(f g))`. -/
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
