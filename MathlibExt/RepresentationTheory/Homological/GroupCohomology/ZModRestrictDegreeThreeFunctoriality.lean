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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ZModRestrictDegreeThree
public import
  MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeFunctoriality

/-!
# Group and coefficient naturality of degree-three scalar restriction

For n∈ℕ, group homomorphism ψ:G→H and equivariant coefficient
map t:Res_ψ(A)→B of ZMod n-representations, restriction of scalars
to ℤ commutes with the induced maps on degree-three cochains,
cocycles and cohomology.
The maps precompose group coordinates by ψ and apply t to values.
The case n=0 is included.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

variable {G H : Type} [Group G] [Group H]
variable (n : ℕ) {A : Rep (ZMod n) H} {B : Rep (ZMod n) G}

set_option backward.isDefEq.respectTransparency false in
/-- Let n∈ℕ, G,H be groups, A a ZMod n-representation of H,
B one of G, ψ:G→H a group homomorphism and
t:Res_ψ(A)→B an equivariant coefficient map.
Scalar restriction to ℤ keeps the coefficient values and group actions.
The degree-three cochain comparisons satisfy
χ_B³(T_(ψ,t)(z))=T_(ψ,Res(t))(χ_A³(z))
for every function z:H³→A. -/
theorem cochains₃ZModRestrictIntEquiv_cochainsMap₃
    (f : G →* H) (phi : Rep.res f A ⟶ B)
    (z : H × H × H → A) :
    cochains₃ZModRestrictIntEquiv n B
        ((cochainsMap₃ f phi).hom z) =
      (cochainsMap₃ f (Rep.zmodRestrictIntMap phi)).hom
        (cochains₃ZModRestrictIntEquiv n A z) := by
  funext p
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let n∈ℕ, G,H be groups, A a ZMod n-representation of H,
B one of G, ψ:G→H a group homomorphism and
t:Res_ψ(A)→B an equivariant coefficient map.
Scalar restriction to ℤ keeps the coefficient values and group actions.
The degree-three cocycle comparisons commute with the map
induced by ψ and t:
χ_B³(Z³(ψ,t)(z))=Z³(ψ,Res(t))(χ_A³(z)). -/
theorem cocycles₃ZModRestrictIntEquiv_mapCocycles₃
    (f : G →* H) (phi : Rep.res f A ⟶ B) (z : cocycles₃ A) :
    cocycles₃ZModRestrictIntEquiv n B (mapCocycles₃ f phi z) =
      mapCocycles₃ f (Rep.zmodRestrictIntMap phi)
        (cocycles₃ZModRestrictIntEquiv n A z) := by
  apply cocycles₃_ext
  intro g h i
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let n∈ℕ, G,H be groups, A a ZMod n-representation of H,
B one of G, ψ:G→H a group homomorphism and
t:Res_ψ(A)→B an equivariant coefficient map.
Scalar restriction to ℤ keeps the coefficient values and group actions.
On cohomology, χ_B³∘H³(ψ,t)=H³(ψ,Res(t))∘χ_A³.
These χ are the additive integral scalar-restriction equivalences. -/
theorem H3ZModRestrictIntAddEquiv_map_of_hom
    (f : G →* H) (phi : Rep.res f A ⟶ B) (x : H3 A) :
    H3ZModRestrictIntAddEquiv n B (map f phi 3 x) =
      map f (Rep.zmodRestrictIntMap phi) 3
        (H3ZModRestrictIntAddEquiv n A x) := by
  induction x using H3_induction_on with
  | _ z =>
      rw [← ConcreteCategory.comp_apply, H3π_comp_map]
      rw [ConcreteCategory.comp_apply, H3ZModRestrictIntAddEquiv_H3π]
      rw [H3ZModRestrictIntAddEquiv_H3π]
      rw [← ConcreteCategory.comp_apply, H3π_comp_map]
      exact congrArg (H3π (Rep.zmodRestrictInt n B))
        (cocycles₃ZModRestrictIntEquiv_mapCocycles₃ n f phi z)

end groupCohomology
