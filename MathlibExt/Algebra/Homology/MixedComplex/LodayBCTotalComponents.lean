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

public import MathlibExt.Algebra.Homology.MixedComplex.LodayBCCoordinateLaws

/-!
# Horizontal and vertical total components in BC coordinates

For a mixed complex M in a preadditive category with zero object and finite coproducts, the
BC-to-Connes total isomorphism V intertwines horizontal and vertical total maps separately. The
BC columns store unsigned b, while totalization multiplies the column-p vertical component by
(-1)^p.

The total components D₁,D₂ therefore satisfy D₁≫D₂+D₂≫D₁=0. Their sum is the total differential,
and V identifies total homology in each degree where both homology objects exist.
-/

@[expose] public section
noncomputable section

open CategoryTheory HomologicalComplex HomologicalComplex₂

universe u v

namespace MixedComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.Limits.HasFiniteCoproducts C]
  (M : MixedComplex C)

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Let C_can be its
Connes bicomplex and C_BC its full column-sign coordinate model. Assume finite coproducts and
let V:Tot(C_BC)≅Tot(C_can). For i,j∈ℕ, V_i≫D₁^can(i,j)=D₁^BC(i,j)≫V_j, where D₁ is the
horizontal total component. -/
theorem lodayBCTotalIso_D₁ (i j : ℕ) :
    M.lodayBCTotalIso.hom.f i ≫ M.connesBicomplex.D₁ (ComplexShape.down ℕ) i j =
      M.lodayBCBicomplex.D₁ (ComplexShape.down ℕ) i j ≫ M.lodayBCTotalIso.hom.f j :=
  HomologicalComplex₂.total.mapAux.mapMap_D₁
    (K := M.lodayBCBicomplex) (L := M.connesBicomplex) (φ := M.lodayBCBicomplexIso.hom)
    (c₁₂ := ComplexShape.down ℕ) i j

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Let C_can be its
Connes bicomplex and C_BC its full column-sign coordinate model. With finite coproducts and
V:Tot(C_BC)≅Tot(C_can), V_i≫D₂^can(i,j)=D₂^BC(i,j)≫V_j for all i,j. The vertical total map on
column p includes (-1)^p. -/
theorem lodayBCTotalIso_D₂ (i j : ℕ) :
    M.lodayBCTotalIso.hom.f i ≫ M.connesBicomplex.D₂ (ComplexShape.down ℕ) i j =
      M.lodayBCBicomplex.D₂ (ComplexShape.down ℕ) i j ≫ M.lodayBCTotalIso.hom.f j :=
  HomologicalComplex₂.total.mapAux.mapMap_D₂
    (K := M.lodayBCBicomplex) (L := M.connesBicomplex) (φ := M.lodayBCBicomplexIso.hom)
    (c₁₂ := ComplexShape.down ℕ) i j

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Let C_can be its
Connes bicomplex and C_BC its full column-sign coordinate model. Assume finite coproducts. For
i,j,k∈ℕ, D₁^BC(i,j)≫D₂^BC(j,k)+D₂^BC(i,j)≫D₁^BC(j,k)=0. The vertical totalization sign converts
the commuting column square into this anticommutation law. -/
theorem lodayBCTotal_D₁_D₂ (i j k : ℕ) :
    M.lodayBCBicomplex.D₁ (ComplexShape.down ℕ) i j ≫ M.lodayBCBicomplex.D₂ (ComplexShape.down ℕ) j k +
      M.lodayBCBicomplex.D₂ (ComplexShape.down ℕ) i j ≫ M.lodayBCBicomplex.D₁ (ComplexShape.down ℕ) j k = 0 := by
  rw [M.lodayBCBicomplex.D₁_D₂]
  exact neg_add_cancel _

/-- Let C be preadditive with a zero object, in object/morphism universes u,v, and M a mixed complex
with underlying nonnegative chain differential b and degree-raising operator B. Let C_can be its
Connes bicomplex and C_BC its full column-sign coordinate model. Assume finite coproducts and
that Tot(C_BC),Tot(C_can) have homology at n∈ℕ. The chain isomorphism V induces
H_n(Tot(C_BC))≅H_n(Tot(C_can)). No homology in other degrees is required for this comparison. -/
def lodayBCTotalHomologyIso (n : ℕ)
    [(M.lodayBCBicomplex.total (ComplexShape.down ℕ)).HasHomology n]
    [(M.connesBicomplex.total (ComplexShape.down ℕ)).HasHomology n] :
    (M.lodayBCBicomplex.total (ComplexShape.down ℕ)).homology n ≅
      (M.connesBicomplex.total (ComplexShape.down ℕ)).homology n :=
  HomologicalComplex.homologyMapIso M.lodayBCTotalIso n

end MixedComplex
