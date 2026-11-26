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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOneFunctoriality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOneMap

/-!
# Pullback and coefficient naturality of degree-one cups

Let `f : G →* H` be a group homomorphism and `k` a commutative ring. Equivariant maps `φ :
Rep.res f A → A'` and `ψ : Rep.res f B → B'` induce maps on cohomology from `H` to `G`. For
degree-one classes, the tensor coefficient map carries `x ∪ y ∈ H²(H,A ⊗ B)` to the cup of the
two pulled-back classes in `H²(G,A' ⊗ B')`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
variable {A B : Rep k H} {A' B' : Rep k G}

set_option backward.isDefEq.respectTransparency false in
/-- Let `k` be a commutative ring, `f : G →* H` a group homomorphism, `A,B : Rep k H`, and `A',B'
: Rep k G`. For morphisms `φ : Rep.res f A → A'`, `ψ : Rep.res f B → B'`, and classes `x ∈
H¹(H,A)`, `y ∈ H¹(H,B)`, `map f (φ ⊗ ψ) 2 (cupOneOne A B x y) = cupOneOne A' B' (map f φ 1 x)
(map f ψ 1 y)`. -/
theorem map_cupOneOne_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ A') (psi : Rep.res f B ⟶ B')
    (x : H1 A) (y : H1 B) :
    map f (phi ⊗ₘ psi) 2 (cupOneOne A B x y) =
      cupOneOne A' B' (map f phi 1 x) (map f psi 1 y) := by
  induction x using H1_induction_on with
  | _ x =>
      induction y using H1_induction_on with
      | _ y =>
          rw [cupOneOne_H1π_H1π,
            ← ConcreteCategory.comp_apply, H2π_comp_map,
            ← ConcreteCategory.comp_apply, H1π_comp_map,
            ← ConcreteCategory.comp_apply, H1π_comp_map]
          simp only [ConcreteCategory.comp_apply]
          rw [cupOneOne_H1π_H1π,
            mapCocycles₂_cupCocycleOneOne_of_hom]

end groupCohomology
