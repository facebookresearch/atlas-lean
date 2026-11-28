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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneTwo
public import
  MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeFunctoriality

/-!
# Group and coefficient naturality of one-two cups

Let `f : G →* H` be a group homomorphism and `k` a commutative ring. For representations `A,B`
of `H`, representations `A',B'` of `G`, and morphisms `φ : Rep.res f A → A'`, `ψ : Rep.res f B
→ B'`, pullback and coefficient change preserve the formula `(x ∪ y)(g,h,j) = x(g) ⊗
g·y(h,j)`. The resulting equality holds for cocycles of degrees `1,2` and for their classes in
`H¹ × H² → H³`.
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
: Rep k G`. For `φ : Rep.res f A → A'`, `ψ : Rep.res f B → B'`, `x ∈ Z¹(H,A)`, and `y ∈
Z²(H,B)`, `mapCocycles₃ f (φ ⊗ ψ) (cupCocycleOneTwo A B x y) = cupCocycleOneTwo A' B'
(mapCocycles₁ f φ x) (mapCocycles₂ f ψ y)`. -/
theorem mapCocycles₃_cupCocycleOneTwo_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ A')
    (psi : Rep.res f B ⟶ B')
    (x : cocycles₁ A) (y : cocycles₂ B) :
    mapCocycles₃ f (phi ⊗ₘ psi) (cupCocycleOneTwo A B x y) =
      cupCocycleOneTwo A' B'
        (mapCocycles₁ f phi x) (mapCocycles₂ f psi y) := by
  apply cocycles₃_ext
  intro g h j
  change (phi ⊗ₘ psi).hom
      (x (f g) ⊗ₜ[k] B.ρ (f g) (y (f h, f j))) =
    phi.hom (x (f g)) ⊗ₜ[k]
      B'.ρ g (psi.hom (y (f h, f j)))
  rw [Rep.hom_tensorHom, Representation.IntertwiningMap.tensor_apply]
  congr 1
  exact Rep.hom_comm_apply psi g _

set_option backward.isDefEq.respectTransparency false in
/-- Let `k` be a commutative ring, `f : G →* H` a group homomorphism, `A,B : Rep k H`, and `A',B'
: Rep k G`. Given `φ : Rep.res f A → A'`, `ψ : Rep.res f B → B'`, and classes `x ∈ H¹(H,A)`,
`y ∈ H²(H,B)`, `map f (φ ⊗ ψ) 3 (cupOneTwo A B x y) = cupOneTwo A' B' (map f φ 1 x) (map f ψ 2
y)` in `H³(G,A' ⊗ B')`. -/
theorem map_cupOneTwo_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ A')
    (psi : Rep.res f B ⟶ B')
    (x : H1 A) (y : H2 B) :
    map f (phi ⊗ₘ psi) 3 (cupOneTwo A B x y) =
      cupOneTwo A' B' (map f phi 1 x) (map f psi 2 y) := by
  induction x using H1_induction_on with
  | _ x =>
    induction y using H2_induction_on with
    | _ y =>
      rw [cupOneTwo_H1π_H2π,
        ← ConcreteCategory.comp_apply, H3π_comp_map,
        ← ConcreteCategory.comp_apply, H1π_comp_map,
        ← ConcreteCategory.comp_apply, H2π_comp_map]
      simp only [ConcreteCategory.comp_apply]
      rw [cupOneTwo_H1π_H2π,
        mapCocycles₃_cupCocycleOneTwo_of_hom]

end groupCohomology
