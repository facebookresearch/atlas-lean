/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Product coordinates of point adjunctions and their mates

Let J be a topology on C and A a coefficient category with w-sized products and colimits of
size (w,w). For a point Φ of fiber universe w, its skyscraper at M has value ∏_{x∈Φ(U)}M. The
local germ map followed by the stalk–skyscraper counit is projection at x.

For a point morphism j : Φ → Ψ, the mate on skyscrapers reindexes these products by j_U : Ψ(U)
→ Φ(U). Skyscraper restriction along a site morphism similarly reindexes by its fiber map;
this last formula needs only the product hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w u' v'

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let J be a topology on C, A have w-sized products and colimits of size (w,w), Φ : Point.{w} J,
M ∈ A, U ∈ C, and x ∈ Φ(U). The germ map ∏_{Φ(U)}M → Φ^*(Φ_*M), followed by the
stalk–skyscraper counit Φ^*(Φ_*M) → M, equals the product projection π_x. Category and fiber
universes may be independent. -/
@[reassoc (attr := simp)]
lemma toPresheafFiber_skyscraperSheafAdjunction_counit (Φ : Point.{w} J)
    (M : A) (U : C) (x : Φ.fiber.obj U) :
    Φ.toPresheafFiber U x ((Φ.skyscraperSheafFunctor.obj M).obj) ≫
        Φ.skyscraperSheafAdjunction.counit.app M = Pi.π (fun (_ : Φ.fiber.obj U) => M) x := by
  let Q : Sheaf J A := Φ.skyscraperSheafFunctor.obj M
  let g : Q.obj ⟶ Φ.skyscraperPresheaf M :=
    (sheafToPresheaf J A).map (𝟙 Q)
  have h := Φ.toPresheafFiber_skyscraperPresheafHomEquiv_symm g U x
  have hc := Φ.skyscraperSheafAdjunction_homEquiv_symm_apply (𝟙 Q)
  change (Φ.skyscraperSheafAdjunction.homEquiv Q M).symm (𝟙 Q) =
    Φ.skyscraperPresheafHomEquiv.symm g at hc
  have hg : g = 𝟙 Q.obj := (sheafToPresheaf J A).map_id Q
  rw [← hc, Adjunction.homEquiv_counit, Functor.map_id, Category.id_comp,
    hg, NatTrans.id_app, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let J be a topology on C and A have w-sized products and colimits of size (w,w). For points
Φ,Ψ and j : Φ → Ψ, write j_U : Ψ(U) → Φ(U) for its fiber map. The adjoint mate on skyscrapers
is a map Φ_*M → Ψ_*M whose U-component t satisfies t_U≫π_y=π_{j_U(y)} for every y ∈ Ψ(U). This
specifies its product reindexing coordinates. -/
lemma conjugateEquiv_sheafFiber_app_π {Φ Ψ : Point.{w} J} (j : Φ ⟶ Ψ)
    (M : A) (U : C) (y : Ψ.fiber.obj U) :
    ((conjugateEquiv Φ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
          (j.sheafFiber (A := A))).app M).hom.app (op U) ≫
        Pi.π (fun (_ : Ψ.fiber.obj U) => M) y =
      Pi.π (fun (_ : Φ.fiber.obj U) => M) (j.hom.app U y) := by
  have h := congrArg (fun k => Ψ.toPresheafFiber U y ((Φ.skyscraperSheafFunctor.obj M).obj) ≫ k)
    (conjugateEquiv_counit Φ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
      (j.sheafFiber (A := A)) M)
  change Ψ.toPresheafFiber U y ((Φ.skyscraperSheafFunctor.obj M).obj) ≫
      Ψ.presheafFiber.map
        (((conjugateEquiv Φ.skyscraperSheafAdjunction Ψ.skyscraperSheafAdjunction
          (j.sheafFiber (A := A))).app M).hom) ≫
      Ψ.skyscraperSheafAdjunction.counit.app M =
    Ψ.toPresheafFiber U y ((Φ.skyscraperSheafFunctor.obj M).obj) ≫
      j.presheafFiber.app ((Φ.skyscraperSheafFunctor.obj M).obj) ≫
      Φ.skyscraperSheafAdjunction.counit.app M at h
  rw [Ψ.toPresheafFiber_naturality_assoc,
    toPresheafFiber_skyscraperSheafAdjunction_counit] at h
  have hj : Ψ.toPresheafFiber U y ((Φ.skyscraperSheafFunctor.obj M).obj) ≫
      j.presheafFiber.app ((Φ.skyscraperSheafFunctor.obj M).obj) =
    Φ.toPresheafFiber U (j.hom.app U y) ((Φ.skyscraperSheafFunctor.obj M).obj) := by
    simpa only [Hom.presheafFiber] using
      (Ψ.toPresheafFiber_presheafFiberDesc
        (φ := fun X x => Φ.toPresheafFiber X (j.hom.app X x)
          ((Φ.skyscraperSheafFunctor.obj M).obj))
        (hφ := by
          intro X Y f x
          rw [Φ.toPresheafFiber_w]
          exact congrArg
            (fun z => Φ.toPresheafFiber Y z ((Φ.skyscraperSheafFunctor.obj M).obj))
            (j.hom.naturality_apply f x).symm) U y)
  rw [← Category.assoc, hj] at h
  rw [toPresheafFiber_skyscraperSheafAdjunction_counit] at h
  exact h

end CategoryTheory.GrothendieckTopology.Point

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {A : Type*} [Category* A] [HasProducts.{w} A]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Let J be a topology on C, A have w-sized products, Φ : Point.{w} J, and M ∈ A. For g : U → V
and z ∈ Φ(U), restriction Φ_*M(V) → Φ_*M(U) followed by π_z equals π_{Φ(g)(z)}. The
restriction map thus reindexes the product by Φ(g) : Φ(U) → Φ(V), without a colimit hypothesis
on A. -/
lemma skyscraperSheaf_restrict_π (Φ : Point.{w} J) (M : A)
    {U V : C} (g : U ⟶ V) (z : Φ.fiber.obj U) :
    (Φ.skyscraperSheafFunctor.obj M).obj.map g.op ≫ Pi.π (fun (_ : Φ.fiber.obj U) => M) z =
      Pi.π (fun (_ : Φ.fiber.obj V) => M) (Φ.fiber.map g z) := by
  simp [skyscraperSheafFunctor, skyscraperPresheafFunctor]

end CategoryTheory.GrothendieckTopology.Point
