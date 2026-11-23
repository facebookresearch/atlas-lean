/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCore
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractible
public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# The path-groupoid cover and its deck action

Describes the under category of a groupoid as a path cover, including its object
fibres and simplices. Inverse precomposition gives the deck action, while the
identity path supplies a contraction of the covering nerve.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial SSet.modelCategoryQuillen

universe u v

namespace CategoryTheory.Under

section Category

variable {C : Type u} [Category.{v} C] (y : C)

@[simp]
theorem objectFiberEquiv_apply (z : C) (U : {U : Under y // U.right = z}) :
    objectFiberEquiv y z U = U.val.hom ≫ eqToHom U.prop := rfl

/-- Precomposition retains the standard opposite-endomorphism action. -/
theorem objectFiberEquiv_precompose (z : C) (g : End y)
    (U : {U : Under y // U.right = z}) :
    objectFiberEquiv y z ⟨(Under.map g.asHom).obj U.val, U.prop⟩ =
      MulOpposite.op g • objectFiberEquiv y z U := by
  change (g.asHom ≫ U.val.hom) ≫ eqToHom U.prop =
    g.asHom ≫ (U.val.hom ≫ eqToHom U.prop)
  exact Category.assoc _ _ _

end Category

section Groupoid

variable {C : Type u} [Groupoid.{v} C] (y : C)

/-- Compatibility computes the unique original endpoint arrow. -/
theorem hom_right_eq_inv_comp {U V : Under y} (f : U ⟶ V) :
    f.right = inv U.hom ≫ V.hom := by
  calc
    f.right = inv U.hom ≫ (U.hom ≫ f.right) := by simp
    _ = inv U.hom ≫ V.hom := by rw [Under.w f]

instance hom_subsingleton (U V : Under y) : Subsingleton (U ⟶ V) where
  allEq f g := UnderMorphism.ext (by
    rw [hom_right_eq_inv_comp y f, hom_right_eq_inv_comp y g])

/-- The identity path is terminal as well as its existing initial structure. -/
def mkIdTerminal : IsTerminal (Under.mk (𝟙 y)) :=
  IsTerminal.ofUniqueHom
    (fun U => Under.homMk (inv U.hom) (by simp))
    (fun _ _ => Subsingleton.elim _ _)

/-- A left action of the original endomorphism group uses inverse precomposition. -/
def deckTransform (g : End y) : Under y ⥤ Under y :=
  Under.map (g⁻¹).asHom

/-- The functor order is the literal order for applying the left action. -/
theorem deckTransform_mul (g h : End y) :
    deckTransform y (g * h) = deckTransform y h ⋙ deckTransform y g := by
  change Under.map ((g * h)⁻¹).asHom =
    Under.map (h⁻¹).asHom ⋙ Under.map (g⁻¹).asHom
  rw [mul_inv_rev]
  exact Under.mapComp_eq (g⁻¹).asHom (h⁻¹).asHom

/-- Transfer the existing opposite-endomorphism action through standard inversion
and the proved identification of the original strict object fiber. -/
@[instance_reducible]
def objectFiberDeckAction (z : C) :
    MulAction (End y) {U : Under y // U.right = z} := by
  letI : MulAction (End y) (y ⟶ z) :=
    MulAction.compHom (y ⟶ z) (MulEquiv.inv' (End y)).toMonoidHom
  exact Equiv.mulAction (End y) (objectFiberEquiv y z)

/-- The transferred left action is the actual inverse-precomposition deck functor. -/
theorem objectFiberDeckAction_smul (z : C) (g : End y)
    (U : {U : Under y // U.right = z}) :
    letI := objectFiberDeckAction y z
    g • U = ⟨(deckTransform y g).obj U.val, U.prop⟩ := by
  let := objectFiberDeckAction y z
  apply (objectFiberEquiv y z).injective
  change objectFiberEquiv y z
    ((objectFiberEquiv y z).symm
      (MulOpposite.op g⁻¹ • objectFiberEquiv y z U)) =
    objectFiberEquiv y z ⟨(deckTransform y g).obj U.val, U.prop⟩
  rw [Equiv.apply_symm_apply]
  exact (objectFiberEquiv_precompose y z g⁻¹ U).symm

/-- A simplex of the original covering nerve is its projected original chain
and its original path to the first vertex. -/
def nerveSimplexEquiv (n : ℕ) :
    ComposableArrows (Under y) n ≃
      (Σ sigma : ComposableArrows C n, y ⟶ sigma.left) := by
  let liftChain (sigma : ComposableArrows C n) (gamma : y ⟶ sigma.left) :
      ComposableArrows (Under y) n :=
    sigma.toUnder y (fun i => gamma ≫ sigma.map' 0 i) (by
      intro i j f
      dsimp only [ComposableArrows.map']
      rw [Category.assoc, ← sigma.map_comp]
      exact congrArg (fun q => gamma ≫ sigma.map q) (Subsingleton.elim _ _))
  refine
    { toFun := fun L => ⟨L ⋙ Under.forget y, L.left.hom⟩
      invFun := fun s => liftChain s.1 s.2
      left_inv := ?_
      right_inv := ?_ }
  · intro L
    fapply ComposableArrows.ext
    · intro i
      change Under.mk (L.left.hom ≫ (L.map' 0 i).right) = L.obj i
      rw [Under.w (L.map' 0 i)]
      rfl
    · intro i hi
      exact Subsingleton.elim _ _
  · rintro ⟨sigma, gamma⟩
    have h : (liftChain sigma gamma).left.hom = gamma := by
      change gamma ≫ sigma.map' 0 0 = gamma
      rw [sigma.map'_self 0, Category.comp_id]
    change (⟨sigma, (liftChain sigma gamma).left.hom⟩ :
      Σ tau : ComposableArrows C n, y ⟶ tau.left) = ⟨sigma, gamma⟩
    rw [h]

@[simp]
theorem nerveSimplexEquiv_apply (n : ℕ) (L : ComposableArrows (Under y) n) :
    nerveSimplexEquiv y n L = ⟨L ⋙ Under.forget y, L.left.hom⟩ := rfl

/-- The inverse's path at each literal vertex follows the original projected chain. -/
@[simp]
theorem nerveSimplexEquiv_symm_obj (n : ℕ) (sigma : ComposableArrows C n)
    (gamma : y ⟶ sigma.left) (i : Fin (n + 1)) :
    (((nerveSimplexEquiv y n).symm ⟨sigma, gamma⟩).obj i).hom =
      gamma ≫ sigma.map' 0 i := rfl

/-- The identity endomorphism acts by the actual identity functor. -/
theorem deckTransform_one : deckTransform y (1 : End y) = 𝟭 (Under y) := by
  change Under.map ((1 : End y)⁻¹).asHom = 𝟭 (Under y)
  rw [inv_one]
  change Under.map (𝟙 y) = 𝟭 (Under y)
  exact Under.mapId_eq y

/-- The identity-path object gives an actual contraction of the original nerve. -/
def nerveIdentityContraction :
    SSet.Homotopy (𝟙 (CategoryTheory.nerve (Under y) : SSet.{max u v}))
      (NerveContractible.constNerveMap (C := Under y) (Under.mk (𝟙 y))) := by
  let hT : IsTerminal (Under.mk (𝟙 y)) := mkIdTerminal y
  let α : 𝟭 (Under y) ⟶ (Functor.const (Under y)).obj (Under.mk (𝟙 y)) :=
    { app := fun U => hT.from U
      naturality := by
        intro U V f
        dsimp
        exact IsTerminal.hom_ext hT _ _ }
  simpa only [NerveContractible.constNerveMap, CategoryTheory.nerveMap_id] using
    CategoryTheory.NatTrans.nerveHomotopy α

/-- All data use the literal original Under category and its given projection. -/
structure NativePathGroupoidCoverData (C : Type u) [Groupoid.{v} C] (y : C) where
  isGroupoid : IsGroupoid (Under y)
  /-- The chosen morphism between any two objects of `Under y`. -/
  hom : ∀ U V : Under y, U ⟶ V
  hom_right : ∀ U V, (hom U V).right = inv U.hom ≫ V.hom
  hom_unique : ∀ U V (f : U ⟶ V), f = hom U V
  hom_id : ∀ U, hom U U = 𝟙 U
  hom_comp : ∀ U V W, hom U V ≫ hom V W = hom U W
  composition_right : ∀ (U V W : Under y) (f : U ⟶ V) (g : V ⟶ W),
    (f ≫ g).right = f.right ≫ g.right
  projection_isIsofibration : (Under.forget y).IsIsofibration
  first_lift_unique : ∀ (U : Under y) (z : C) (g : U.right ⟶ z),
    ∃! s : ComposableArrows (Under y) 1,
      ((Under.forget y).mapComposableArrows 1).obj s = ComposableArrows.mk₁ g ∧ s.left = U
  /-- The object `Under.mk (𝟙 y)` is initial in `Under y`. -/
  identity_initial : IsInitial (Under.mk (𝟙 y))
  /-- The object `Under.mk (𝟙 y)` is terminal in `Under y`. -/
  identity_terminal : IsTerminal (Under.mk (𝟙 y))
  /-- For each `z`, the objects of `Under y` over `z` correspond to the morphisms `y ⟶ z`. -/
  object_fiber : ∀ z : C, {U : Under y // U.right = z} ≃ (y ⟶ z)
  object_fiber_apply : ∀ z U, object_fiber z U = U.val.hom ≫ eqToHom U.property
  object_fiber_hom_discrete : ∀ (z : C) (U V : {U : Under y // U.right = z})
    (f : U.val ⟶ V.val), f.right ≫ eqToHom V.property = eqToHom U.property → U = V
  /-- The composable `n`-strings in `Under y` correspond to a composable `n`-string `σ`
  in `C` together with a morphism from `y` to its first object. -/
  simplex_equiv : ∀ n : ℕ, ComposableArrows (Under y) n ≃
    (Σ σ : ComposableArrows C n, y ⟶ σ.left)
  simplex_equiv_apply : ∀ n L, simplex_equiv n L = ⟨L ⋙ Under.forget y, L.left.hom⟩
  simplex_right_at_vertex : ∀ n (σ : ComposableArrows C n) (γ : y ⟶ σ.left)
    (j : Fin (n + 1)), (((simplex_equiv n).symm ⟨σ, γ⟩).obj j).right = σ.obj j
  simplex_path_at_vertex : ∀ n (σ : ComposableArrows C n) (γ : y ⟶ σ.left)
    (j : Fin (n + 1)), (((simplex_equiv n).symm ⟨σ, γ⟩).obj j).hom ≫
      eqToHom (simplex_right_at_vertex n σ γ j) = γ ≫ σ.map' 0 j
  /-- The deck transformation of `Under y` attached to each endomorphism of `y`. -/
  deck : End y → Under y ⥤ Under y
  deck_one : deck 1 = 𝟭 (Under y)
  deck_mul : ∀ g h, deck (g * h) = deck h ⋙ deck g
  deck_projection : ∀ g, deck g ⋙ Under.forget y = Under.forget y
  deck_right : ∀ g U, ((deck g).obj U).right = U.right
  /-- For each `z`, the action of `End y` on the objects of `Under y` over `z`. -/
  fiber_action : ∀ z : C, MulAction (End y) {U : Under y // U.right = z}
  fiber_action_smul : ∀ z (g : End y) (U : {U : Under y // U.right = z}),
    letI := fiber_action z
    g • U = ⟨(deck g).obj U.val, (deck_right g U.val).trans U.property⟩
  /-- A homotopy from the identity of the nerve of `Under y` to the constant map at
  `Under.mk (𝟙 y)`. -/
  contraction : SSet.Homotopy (𝟙 (CategoryTheory.nerve (Under y) : SSet.{max u v}))
    (NerveContractible.constNerveMap (C := Under y) (Under.mk (𝟙 y)))
  nerve_to_terminal : SSet.realizationWeakEquivalences
    (terminal.from (CategoryTheory.nerve (Under y) : SSet.{max u v}))

attribute [nolint defsWithUnderscore] NativePathGroupoidCoverData.identity_initial
  NativePathGroupoidCoverData.identity_terminal NativePathGroupoidCoverData.object_fiber
  NativePathGroupoidCoverData.simplex_equiv NativePathGroupoidCoverData.fiber_action

private theorem nerveSimplexEquiv_path_transport
    (n : ℕ) (σ : ComposableArrows C n) (γ : y ⟶ σ.left) (j : Fin (n + 1))
    (h : (((nerveSimplexEquiv y n).symm ⟨σ, γ⟩).obj j).right = σ.obj j) :
    (((nerveSimplexEquiv y n).symm ⟨σ, γ⟩).obj j).hom ≫ eqToHom h =
      γ ≫ σ.map' 0 j := by
  have hc : eqToHom h = 𝟙 (σ.obj j) := CategoryTheory.eqToHom_refl (σ.obj j) h
  exact (congrArg (fun f : σ.obj j ⟶ σ.obj j =>
    (((nerveSimplexEquiv y n).symm ⟨σ, γ⟩).obj j).hom ≫ f) hc).trans
      ((Category.comp_id (((nerveSimplexEquiv y n).symm ⟨σ, γ⟩).obj j).hom).trans
        (nerveSimplexEquiv_symm_obj y n σ γ j))

/-- Construct the path-groupoid cover and every law from the original groupoid alone. -/
def nativePathGroupoidCover : NativePathGroupoidCoverData C y where
  isGroupoid := inferInstance
  hom U V := Under.homMk (inv U.hom ≫ V.hom) (by simp)
  hom_right _ _ := rfl
  hom_unique U V f := by
    apply (Under.forget y).map_injective
    exact hom_right_eq_inv_comp y f
  hom_id _ := Subsingleton.elim _ _
  hom_comp _ _ _ := Subsingleton.elim _ _
  composition_right U V W f g := Under.comp_right U V W f g
  projection_isIsofibration := inferInstance
  first_lift_unique U z g := existsUnique_oneSimplexLift_from y U g
  identity_initial := Under.mkIdInitial (X := y)
  identity_terminal := mkIdTerminal y
  object_fiber := objectFiberEquiv y
  object_fiber_apply z U := objectFiberEquiv_apply y z U
  object_fiber_hom_discrete z U V f hf := by
    apply (objectFiberEquiv y z).injective
    have he : U.val.hom ≫ eqToHom U.property = V.val.hom ≫ eqToHom V.property :=
      ((congrArg (fun g : U.val.right ⟶ z => U.val.hom ≫ g) hf).symm).trans
        ((Category.assoc U.val.hom f.right (eqToHom V.property)).symm.trans
          (congrArg (fun g : y ⟶ V.val.right => g ≫ eqToHom V.property) (Under.w f)))
    exact (objectFiberEquiv_apply y z U).trans (he.trans (objectFiberEquiv_apply y z V).symm)
  simplex_equiv := nerveSimplexEquiv y
  simplex_equiv_apply n L := nerveSimplexEquiv_apply y n L
  simplex_right_at_vertex _ _ _ _ := rfl
  simplex_path_at_vertex n σ γ j :=
    (by exact nerveSimplexEquiv_path_transport y n σ γ j rfl)
  deck := deckTransform y
  deck_one := deckTransform_one y
  deck_mul := deckTransform_mul y
  deck_projection g := Under.mapForget_eq (g⁻¹).asHom
  deck_right _ _ := rfl
  fiber_action := objectFiberDeckAction y
  fiber_action_smul z g U := objectFiberDeckAction_smul y z g U
  contraction := nerveIdentityContraction y
  nerve_to_terminal :=
    NerveContractible.nerve_to_terminal_mem_realizationWeakEquivalences_of_isInitial
      (Under.mkIdInitial (X := y))

end Groupoid

end CategoryTheory.Under

end
