/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoPreNatIso

/-!
# Homotopy to precomposition natural isomorphism (the supporting result): tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoPreNatIso`:
the external tensor of edges and its square
(`SSet.Edge.tensor_square`), the component edges and natural
transformation from a single homotopy
(`SSet.Homotopy.hoPreCompEdge`, `SSet.Homotopy.hoPreNatTrans`), the inverse
data and natural isomorphism from homotopies over a trivial Kan fibration
(`SSet.Homotopy.edgeIhom_invStruct_of_over`,
`SSet.hoPreNatIso_of_homotopy_over_of_rlp_I`), and the conclusion that
trivial Kan fibrations are categorical equivalences
(`SSet.categoricalEquivalences.of_rlp_I`,
`SSet.modelCategoryQuillen_I_rlp_le_categoricalEquivalences`), at an
arbitrary universe and at universe `0`.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace HoPreNatIsoTest

section TensorSquare

variable {A B : SSet.{u}} {x₀ x₁ : A _⦋0⦌} {y₀ y₁ : B _⦋0⦌}
  (ex : SSet.Edge x₀ x₁) (ey : SSet.Edge y₀ y₁)

example : SSet.Edge (X := A ⊗ B) (x₀, y₀) (x₁, y₁) := ex.tensor ey

example : (ex.tensor ey).edge = ((ex.edge, ey.edge) : (A ⊗ B) _⦋1⦌) :=
  SSet.Edge.tensor_edge ex ey

example :
    SSet.HomotopyCategory.homMk (ex.tensor (.id y₀)) ≫
        SSet.HomotopyCategory.homMk (SSet.Edge.tensor (.id x₁) ey) =
      SSet.HomotopyCategory.homMk (SSet.Edge.tensor (.id x₀) ey) ≫
        SSet.HomotopyCategory.homMk (ex.tensor (.id y₁)) :=
  SSet.Edge.tensor_square ex ey

end TensorSquare

section HomotopyAlgebra

variable {X Y Z : SSet.{u}} {f g : X ⟶ Y} (K : SSet.Homotopy f g) (q : Y ⟶ Z)
  (r : Z ⟶ X)

example : (K.postcomp q).h = K.h ≫ q := SSet.Homotopy.postcomp_h K q

example : ((K.postcomp q).precomp r).h =
    (r ▷ (Δ[1] : SSet.{u})) ≫ (K.h ≫ q) := by
  rw [SSet.Homotopy.precomp_h, SSet.Homotopy.postcomp_h]

example (m : X ⟶ Y) : (SSet.Homotopy.reflH m).h = fst X (Δ[1] : SSet.{u}) ≫ m :=
  SSet.Homotopy.reflH_h m

example {a b : X _⦋0⦌} (e : SSet.Edge a b) (θ : X ⟶ Z) :
    (e.map θ).edge = SSet.yonedaEquiv (SSet.yonedaEquiv.symm e.edge ≫ θ) :=
  SSet.Edge.map_edge_yoneda e θ

end HomotopyAlgebra

section NatTrans

variable {X C : SSet.{u}} {f g : X ⟶ X} (H : SSet.Homotopy f g)
  (x y : ((ihom X).obj C) _⦋0⦌) (e : ((ihom X).obj C).Edge x y)

example : ((ihom X).obj C).Edge (((pre f).app C).app _ x) (((pre g).app C).app _ x) :=
  H.hoPreCompEdge C x

-- The component edge has the underlying `1`-simplex classified by the
-- postcomposed homotopy, by `SSet.Homotopy.hoPreCompEdge_edge`,
-- `SSet.Homotopy.edgeIhom_edge`, and `SSet.Homotopy.postcomp_h`.
example : (H.hoPreCompEdge C x).edge =
    SSet.yonedaEquiv (MonoidalClosed.curry
      (H.h ≫ (SSet.ihomVertexEquiv X C).symm x)) := by
  rw [SSet.Homotopy.hoPreCompEdge_edge, SSet.Homotopy.edgeIhom_edge,
    SSet.Homotopy.postcomp_h]

example :
    SSet.HomotopyCategory.homMk (e.map ((pre f).app C)) ≫
        SSet.HomotopyCategory.homMk (H.hoPreCompEdge C y) =
      SSet.HomotopyCategory.homMk (H.hoPreCompEdge C x) ≫
        SSet.HomotopyCategory.homMk (e.map ((pre g).app C)) :=
  H.hoPre_square C e

example : (SSet.hoFunctor.map ((pre f).app C)).toFunctor ⟶
    (SSet.hoFunctor.map ((pre g).app C)).toFunctor :=
  H.hoPreNatTrans C

example : (H.hoPreNatTrans C).app (SSet.HomotopyCategory.mk x) =
    SSet.HomotopyCategory.homMk (H.hoPreCompEdge C x) :=
  SSet.Homotopy.hoPreNatTrans_app_mk H C x

-- Naturality of the transformation at the morphism represented by an edge
-- is exactly `SSet.Homotopy.hoPre_square`, through the object and morphism
-- formulas for precomposition functors.
example :
    (SSet.hoFunctor.map ((pre f).app C)).toFunctor.map
        (SSet.HomotopyCategory.homMk e) ≫ (H.hoPreNatTrans C).app
          (SSet.HomotopyCategory.mk y) =
      (H.hoPreNatTrans C).app (SSet.HomotopyCategory.mk x) ≫
        (SSet.hoFunctor.map ((pre g).app C)).toFunctor.map
          (SSet.HomotopyCategory.homMk e) :=
  (H.hoPreNatTrans C).naturality (SSet.HomotopyCategory.homMk e)

example : (SSet.Homotopy.reflH f).edgeIhom =
    SSet.Edge.id (SSet.ihomVertexEquiv X X f) :=
  SSet.Homotopy.edgeIhom_reflH f

end NatTrans

section NatIsoOver

variable {X Y C : SSet.{u}} {p : X ⟶ Y} {a b : X ⟶ X}
  (hp : SSet.modelCategoryQuillen.I.rlp p)
  (H : SSet.Homotopy a b) (Hrev : SSet.Homotopy b a)
  (hH : H.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p))
  (hHrev : Hrev.h ≫ p = fst X (Δ[1] : SSet.{u}) ≫ (a ≫ p))

example : H.edgeIhom.InvStruct :=
  H.edgeIhom_invStruct_of_over hp Hrev hH hHrev

-- The edge of `Fun(X, X)` classified by `H` represents an isomorphism in the
-- homotopy category, through the `InvStruct` composition structures.
example : IsIso (SSet.HomotopyCategory.homMk H.edgeIhom) := by
  let I := H.edgeIhom_invStruct_of_over hp Hrev hH hHrev
  exact ⟨⟨SSet.HomotopyCategory.homMk I.inv,
    by rw [SSet.HomotopyCategory.homMk_comp_homMk I.homInvId,
      SSet.HomotopyCategory.homMk_id],
    by rw [SSet.HomotopyCategory.homMk_comp_homMk I.invHomId,
      SSet.HomotopyCategory.homMk_id]⟩⟩

example : (SSet.hoFunctor.map ((pre a).app C)).toFunctor ≅
    (SSet.hoFunctor.map ((pre b).app C)).toFunctor :=
  SSet.hoPreNatIso_of_homotopy_over_of_rlp_I hp H Hrev hH hHrev C

example (x : ((ihom X).obj C) _⦋0⦌) :
    (SSet.hoPreNatIso_of_homotopy_over_of_rlp_I hp H Hrev hH hHrev C).hom.app
        (SSet.HomotopyCategory.mk x) =
      SSet.HomotopyCategory.homMk (H.hoPreCompEdge C x) :=
  SSet.hoPreNatIso_of_homotopy_over_of_rlp_I_hom_app_mk hp H Hrev hH hHrev C x

-- Every component of the natural isomorphism is an isomorphism: it is the
-- forward map of the component isomorphism `SSet.Homotopy.hoPreCompIso`.
example (x : ((ihom X).obj C) _⦋0⦌) :
    IsIso (SSet.HomotopyCategory.homMk (H.hoPreCompEdge C x)) :=
  Iso.isIso_hom (H.hoPreCompIso (H.edgeIhom_invStruct_of_over hp Hrev hH hHrev) C x)

example (x : ((ihom X).obj C) _⦋0⦌) :
    SSet.HomotopyCategory.mk (((pre a).app C).app _ x) ≅
      SSet.HomotopyCategory.mk (((pre b).app C).app _ x) :=
  H.hoPreCompIso (H.edgeIhom_invStruct_of_over hp Hrev hH hHrev) C x

end NatIsoOver

section CategoricalEquivalences

variable {X Y : SSet.{u}} {p : X ⟶ Y}

example (hp : SSet.modelCategoryQuillen.I.rlp p) :
    SSet.categoricalEquivalences p :=
  SSet.categoricalEquivalences.of_rlp_I hp

example : SSet.modelCategoryQuillen.I.rlp ≤ SSet.categoricalEquivalences.{u} :=
  SSet.modelCategoryQuillen_I_rlp_le_categoricalEquivalences

-- The inclusion in membership form, through the general `≤` on morphism
-- properties.
example (hp : SSet.modelCategoryQuillen.I.rlp p) :
    SSet.categoricalEquivalences p :=
  SSet.modelCategoryQuillen_I_rlp_le_categoricalEquivalences p hp

-- Tested against every quasicategory, precomposition with a trivial Kan
-- fibration is an equivalence of homotopy categories of functor objects.
example (hp : SSet.modelCategoryQuillen.I.rlp p) (C : SSet.{u})
    (hC : SSet.Quasicategory C) :
    (SSet.hoFunctor.map ((pre p).app C)).toFunctor.IsEquivalence :=
  SSet.categoricalEquivalences.of_rlp_I hp C hC

example : SSet.modelCategoryQuillen.I.rlp ≤ SSet.categoricalEquivalences.{0} :=
  SSet.modelCategoryQuillen_I_rlp_le_categoricalEquivalences.{0}

example {X₀ Y₀ : SSet.{0}} {p₀ : X₀ ⟶ Y₀}
    (hp : SSet.modelCategoryQuillen.I.rlp p₀) :
    SSet.categoricalEquivalences p₀ :=
  SSet.categoricalEquivalences.of_rlp_I hp

end CategoricalEquivalences

end HoPreNatIsoTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

end
