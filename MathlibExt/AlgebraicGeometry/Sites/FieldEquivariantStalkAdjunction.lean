/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Formalization developed with automated proof assistants; original Git history retained.
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldInvariantSkyscraperInverseSheaf
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Equivariant geometric stalk and invariant inverse sheaf

Fix a field with separable closure and abelian coefficients in universe `max u w`. The
ordinary stalk-skyscraper transpose identifies diagonal-invariant sheaf maps with Galois-
equivariant stalk maps. Under the diagonal action of `g`, transposition uses the stalk action
of `g⁻¹` and the coefficient action of `g`.

The invariant cone gives a Hom correspondence between the geometric Galois stalk and the
invariant inverse-sheaf functor. This is an additive adjunction, natural in the sheaf and
discrete Galois coefficient.

The unit maps a section to its geometric-germ function. The counit evaluates an equivariant
section at the germ point. These values, the invariant projection maps, both triangle
identities, and coefficient-lift coordinates are retained.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Discrete field coefficient category is preadditive.

The discrete Galois coefficient category has the canonical additive Hom structure. -/
@[nolint defsWithUnderscore] -- preserve the original public compatibility name
abbrev fieldDiscreteAbelianAction_preadditive :
    Preadditive (DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :=
  DiscreteAbelianAction.instPreadditive.{u, max u w} (G := Gal(Ω/k))

/-- Invariant inverse sheaf functor is additive.

The inverse-sheaf construction preserves sums of coefficient morphisms. -/
instance fieldInvariantSkyscraperInverseSheaf_additive :
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro h
    apply MulActionHom.ext
    intro z
    rfl

/-- Ordinary field stalk maps transpose to skyscraper maps.

The point adjunction gives a bijection between additive stalk maps to the underlying
coefficient and sheaf maps to its skyscraper. -/
abbrev fieldStalkSkyscraperHomEquiv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    ((smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).obj Q ⟶
      (fieldModuleAbAction.{u, w} k Ω M).V) ≃
        (Q ⟶ fieldSkyscraper.{u, w} k Ω M) :=
  (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction.homEquiv
    Q ((fieldModuleAbAction.{u, w} k Ω M).V)

/-- Diagonal skyscraper action transposes with the inverse stalk action.

Postcomposition by the diagonal skyscraper map for `g` transposes to precomposition by the
stalk action of `g⁻¹`, followed by the coefficient action of `g`. -/
theorem fieldStalkSkyscraperHomEquiv_symm_diagonal
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (h : Q ⟶ fieldSkyscraper.{u, w} k Ω M) (g : Gal(Ω/k)) :
    (fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M).symm
        (h ≫ fieldSkyscraperDiagonalMap.{u, w} k Ω M g) =
      (fieldGaloisStalkMap.{u, w} k Ω g⁻¹).app Q ≫
        (fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M).symm h ≫
          ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom := by
  have hm
      (L : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ⥤
        AddCommGrpCat.{max u w})
      (R : AddCommGrpCat.{max u w} ⥤
        Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (adj : L ⊣ R) (α : L ⟶ L)
      (X : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (Y : AddCommGrpCat.{max u w}) (b : Y ⟶ Y) (a : X ⟶ R.obj Y) :
      (adj.homEquiv X Y).symm
          (a ≫ (conjugateEquiv adj adj α).app Y ≫ R.map b) =
        α.app X ≫ (adj.homEquiv X Y).symm a ≫ b := by
    let B := (conjugateEquiv adj adj α).app Y
    have hcore : (adj.homEquiv X Y).symm (a ≫ B) =
        α.app X ≫ (adj.homEquiv X Y).symm a := by
      change L.map (a ≫ B) ≫ adj.counit.app Y =
        α.app X ≫ (L.map a ≫ adj.counit.app Y)
      calc
        _ = (L.map a ≫ L.map B) ≫ adj.counit.app Y :=
          congrArg (fun t => t ≫ adj.counit.app Y) (L.map_comp a B)
        _ = L.map a ≫ (L.map B ≫ adj.counit.app Y) := Category.assoc _ _ _
        _ = L.map a ≫ (α.app (R.obj Y) ≫ adj.counit.app Y) :=
          congrArg (fun t => L.map a ≫ t) (conjugateEquiv_counit adj adj α Y)
        _ = (L.map a ≫ α.app (R.obj Y)) ≫ adj.counit.app Y :=
          (Category.assoc _ _ _).symm
        _ = (α.app X ≫ L.map a) ≫ adj.counit.app Y :=
          congrArg (fun t => t ≫ adj.counit.app Y) (α.naturality a)
        _ = _ := Category.assoc _ _ _
    exact (congrArg (adj.homEquiv X Y).symm (Category.assoc a B (R.map b)).symm).trans
      ((adj.homEquiv_naturality_right_symm (a ≫ B) b).trans
        ((congrArg (fun t => t ≫ b) hcore).trans (Category.assoc _ _ _)))
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  exact hm (Φ.sheafFiber (A := AddCommGrpCat.{max u w}))
    (Φ.skyscraperSheafFunctor (A := AddCommGrpCat.{max u w}))
    (Φ.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u w}))
    (fieldGaloisStalkMap.{u, w} k Ω g⁻¹) Q
    ((fieldModuleAbAction.{u, w} k Ω M).V)
    ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom h

/-- Equivariance condition on an additive field stalk map.

An additive map is equivariant when the stalk action of every `g` followed by the map equals
the map followed by the coefficient action of `g`. -/
def FieldEquivariantStalkAbHom
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (f : (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).obj Q ⟶
      (fieldModuleAbAction.{u, w} k Ω M).V) : Prop :=
  ∀ g : Gal(Ω/k), (fieldGaloisStalkMap.{u, w} k Ω g).app Q ≫ f =
    f ≫ ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom

/-- Invariance condition on a field skyscraper map.

A skyscraper-valued sheaf map is invariant when postcomposition with every diagonal Galois
action leaves it unchanged. -/
def FieldInvariantSkyscraperHom
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (h : Q ⟶ fieldSkyscraper.{u, w} k Ω M) : Prop :=
  ∀ g : Gal(Ω/k), h ≫ fieldSkyscraperDiagonalMap.{u, w} k Ω M g = h

/-- Invariant skyscraper maps transpose to equivariant stalk maps.

The ordinary point Hom correspondence identifies diagonal-invariant skyscraper maps with
equivariant additive stalk maps. -/
theorem fieldStalkSkyscraperHomEquiv_invariant_iff
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (h : Q ⟶ fieldSkyscraper.{u, w} k Ω M) :
    FieldInvariantSkyscraperHom.{u, w} k Ω Q M h ↔
      FieldEquivariantStalkAbHom.{u, w} k Ω Q M
        ((fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M).symm h) := by
  let e := fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M
  let f := e.symm h
  have hi (g : Gal(Ω/k)) :
      ((fieldModuleAbAction.{u, w} k Ω M).ρ g⁻¹).asHom ≫
        ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom = 𝟙 _ := by
    simp [← End.mul_asHom, ← map_mul]
  constructor
  · intro hh g
    let a := ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom
    let b := ((fieldModuleAbAction.{u, w} k Ω M).ρ g⁻¹).asHom
    let A := (fieldGaloisStalkMap.{u, w} k Ω g).app Q
    have hx : A ≫ f ≫ b = f := by
      have ht := (fieldStalkSkyscraperHomEquiv_symm_diagonal.{u, w} k Ω Q M h g⁻¹).symm.trans
        (congrArg e.symm (hh g⁻¹))
      simpa only [inv_inv] using ht
    have hc := hi g
    have he : (A ≫ f) ≫ (b ≫ a) = A ≫ f :=
      (congrArg (fun t => (A ≫ f) ≫ t) hc).trans (Category.comp_id _)
    have ha := congrArg (fun t => t ≫ a) hx
    exact he.symm.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ a) (Category.assoc A f b)).trans ha))
  · intro hf g
    apply e.symm.injective
    have ht := fieldStalkSkyscraperHomEquiv_symm_diagonal.{u, w} k Ω Q M h g
    have hc := hi g
    exact ht.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom)
        (hf g⁻¹)).trans ((Category.assoc _ _ _).trans
          ((congrArg (fun t => f ≫ t) hc).trans (Category.comp_id f)))))


/-- Underlying additive map of an equivariant stalk morphism.

Forget the Galois action on an equivariant stalk morphism to obtain its additive-group map. -/
abbrev fieldEquivariantStalkUnderlyingMap
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) :
    (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).obj Q ⟶
      (fieldModuleAbAction.{u, w} k Ω M).V :=
  (DiscreteAbelianAction.forget Gal(Ω/k)).map f

/-- Underlying stalk map retains Galois equivariance.

The underlying additive map commutes with each stalk action and the corresponding coefficient
action. -/
theorem fieldEquivariantStalkUnderlyingMap_comm
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) (g : Gal(Ω/k)) :
    (fieldGaloisStalkMap.{u, w} k Ω g).app Q ≫
        fieldEquivariantStalkUnderlyingMap.{u, w} k Ω f =
      fieldEquivariantStalkUnderlyingMap.{u, w} k Ω f ≫
        ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom := by
  have ha : ((fieldModuleAbAction.{u, w} k Ω
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)).ρ g).asHom =
    (fieldGaloisStalkMap.{u, w} k Ω g).app Q := by
    ext x
    exact fieldGeometricStalkGaloisObject_action.{u, w} k Ω Q g x
  have hc := (fieldModuleAbActionMap.{u, w} k Ω f).comm g
  exact (congrArg (fun a => a ≫ fieldEquivariantStalkUnderlyingMap.{u, w} k Ω f) ha.symm).trans hc

/-- Equivariant stalk transpose is diagonally invariant.

The ordinary skyscraper transpose of an equivariant stalk morphism is invariant under the
diagonal Galois action. -/
theorem fieldEquivariantStalkTranspose_invariant
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) :
    FieldInvariantSkyscraperHom.{u, w} k Ω Q M
      (fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M
        (fieldEquivariantStalkUnderlyingMap.{u, w} k Ω f)) := by
  apply (fieldStalkSkyscraperHomEquiv_invariant_iff.{u, w} k Ω Q M _).mpr
  intro g
  simpa only [Equiv.symm_apply_apply] using
    fieldEquivariantStalkUnderlyingMap_comm.{u, w} k Ω f g

/-- Invariant cone of an equivariant stalk morphism.

The diagonally invariant transpose defines a cone over the skyscraper invariant diagram, with
vertex the source sheaf. -/
def fieldEquivariantStalkHomCone
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) :
    Cone (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) where
  pt := Q
  π := {
    app := fun _ => fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M
      (fieldEquivariantStalkUnderlyingMap.{u, w} k Ω f)
    naturality := fun _ _ g => by
      change _ = _ ≫ fieldSkyscraperDiagonalMap.{u, w} k Ω M g
      exact (fieldEquivariantStalkTranspose_invariant.{u, w} k Ω f g).symm }

/-- Equivariant stalk map gives an inverse sheaf map.

Lift the invariant transpose cone through the skyscraper invariant limit to define a map to
the invariant inverse sheaf. -/
def fieldEquivariantStalkToInverse
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) :
    Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M :=
  (fieldInvariantSkyscraperSheafIsLimit.{u, w} k Ω M).lift
    (fieldEquivariantStalkHomCone.{u, w} k Ω f)

/-- Inverse sheaf map has its ordinary skyscraper transpose.

Composing the inverse-sheaf map with the invariant cone projection gives the ordinary stalk-
skyscraper transpose. -/
theorem fieldEquivariantStalkToInverse_fac
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) :
    fieldEquivariantStalkToInverse.{u, w} k Ω f ≫
        (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) =
      fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M
        (fieldEquivariantStalkUnderlyingMap.{u, w} k Ω f) :=
  (fieldInvariantSkyscraperSheafIsLimit.{u, w} k Ω M).fac _ _

/-- Underlying stalk map of an inverse sheaf map.

Compose the inverse-sheaf map with its skyscraper projection and apply the ordinary point Hom
correspondence in reverse. -/
abbrev fieldEquivariantStalkFromInversePlain
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) :
    (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).obj Q ⟶
      (fieldModuleAbAction.{u, w} k Ω M).V :=
  (fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M).symm
    (h ≫ (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)))

/-- Inverse sheaf transpose is equivariant.

The underlying stalk transpose commutes with each Galois stalk and coefficient action. -/
theorem fieldEquivariantStalkFromInversePlain_comm
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) (g : Gal(Ω/k)) :
    (fieldGaloisStalkMap.{u, w} k Ω g).app Q ≫
        fieldEquivariantStalkFromInversePlain.{u, w} k Ω h =
      fieldEquivariantStalkFromInversePlain.{u, w} k Ω h ≫
        ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom := by
  apply (fieldStalkSkyscraperHomEquiv_invariant_iff.{u, w} k Ω Q M _).mp
  intro a
  let i := (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k))
  have hi := (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).w
    (j := SingleObj.star Gal(Ω/k)) (j' := SingleObj.star Gal(Ω/k)) a
  change i ≫ fieldSkyscraperDiagonalMap.{u, w} k Ω M a = i at hi
  exact (Category.assoc h i _).trans (congrArg (fun t => h ≫ t) hi)

/-- Inverse sheaf map gives an equivariant stalk morphism.

Bundle the underlying equivariant transpose as a morphism of discrete Galois coefficients. -/
def fieldEquivariantStalkFromInverse
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M :=
  DiscreteAbelianAction.ofAddHom
    ⟨(fieldEquivariantStalkFromInversePlain.{u, w} k Ω h).hom, fun g x => by
      exact congrArg (fun f => f x) (fieldEquivariantStalkFromInversePlain_comm.{u, w} k Ω h g)⟩

/-- Equivariant transpose retains its additive map.

The underlying map of the bundled transpose is the ordinary inverse-sheaf transpose. -/
theorem fieldEquivariantStalkFromInverse_underlying
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) :
    fieldEquivariantStalkUnderlyingMap.{u, w} k Ω
        (fieldEquivariantStalkFromInverse.{u, w} k Ω h) =
      fieldEquivariantStalkFromInversePlain.{u, w} k Ω h := rfl

/-- Inverse transpose after forward transpose is the identity.

Starting from an equivariant stalk morphism, passing to the inverse sheaf and back returns the
same morphism. -/
theorem fieldEquivariantStalkFromInverse_toInverse
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) :
    fieldEquivariantStalkFromInverse.{u, w} k Ω
      (fieldEquivariantStalkToInverse.{u, w} k Ω f) = f := by
  apply (DiscreteAbelianAction.forget Gal(Ω/k)).map_injective
  exact (congrArg (fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M).symm
    (fieldEquivariantStalkToInverse_fac.{u, w} k Ω f)).trans
      ((fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M).symm_apply_apply _)

/-- Forward transpose after inverse transpose is the identity.

Starting from an inverse-sheaf map, passing to its stalk transpose and back returns the same
sheaf map. -/
theorem fieldEquivariantStalkToInverse_fromInverse
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) :
    fieldEquivariantStalkToInverse.{u, w} k Ω
      (fieldEquivariantStalkFromInverse.{u, w} k Ω h) = h := by
  apply (fieldInvariantSkyscraperSheafIsLimit.{u, w} k Ω M).hom_ext
  intro j
  cases j
  exact (fieldEquivariantStalkToInverse_fac.{u, w} k Ω
    (fieldEquivariantStalkFromInverse.{u, w} k Ω h)).trans
      ((fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M).apply_symm_apply _)

/-- Equivariant stalk and inverse sheaf Hom correspondence.

Equivariant maps from the geometric fiber to a coefficient are in bijection with maps from the
sheaf to the invariant inverse sheaf. -/
def fieldEquivariantStalkHomEquiv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) ≃
      (Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) where
  toFun := fieldEquivariantStalkToInverse.{u, w} k Ω
  invFun := fieldEquivariantStalkFromInverse.{u, w} k Ω
  left_inv := fieldEquivariantStalkFromInverse_toInverse.{u, w} k Ω
  right_inv := fieldEquivariantStalkToInverse_fromInverse.{u, w} k Ω


/-- Inverse transpose is natural in the source sheaf.

Precomposition by a sheaf morphism corresponds to precomposition by its geometric-stalk Galois
morphism. -/
theorem fieldEquivariantStalkFromInverse_naturality_left
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (τ : Q' ⟶ Q) (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) :
    fieldEquivariantStalkFromInverse.{u, w} k Ω (τ ≫ h) =
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map τ ≫
        fieldEquivariantStalkFromInverse.{u, w} k Ω h := by
  apply (DiscreteAbelianAction.forget Gal(Ω/k)).map_injective
  let i := (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k))
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  change (fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q' M).symm ((τ ≫ h) ≫ i) =
    Φ.sheafFiber.map τ ≫ (fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M).symm (h ≫ i)
  exact (congrArg (fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q' M).symm
    (Category.assoc τ h i)).trans
      (Φ.skyscraperSheafAdjunction.homEquiv_naturality_left_symm τ (h ≫ i))

/-- Forward transpose is natural in the coefficient.

Postcomposition by a coefficient map corresponds to postcomposition by its invariant inverse-
sheaf map. -/
theorem fieldEquivariantStalkToInverse_naturality_right
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) (t : M ⟶ N) :
    fieldEquivariantStalkToInverse.{u, w} k Ω (f ≫ t) =
      fieldEquivariantStalkToInverse.{u, w} k Ω f ≫
        (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t := by
  apply (fieldInvariantSkyscraperSheafIsLimit.{u, w} k Ω N).hom_ext
  intro j
  cases j
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let a := fieldEquivariantStalkToInverse.{u, w} k Ω f
  let iM := (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k))
  let iN := (fieldInvariantSkyscraperSheafCone.{u, w} k Ω N).π.app (SingleObj.star Gal(Ω/k))
  let b := (fieldModuleAbActionMap.{u, w} k Ω t).hom
  have hl := (fieldEquivariantStalkToInverse_fac.{u, w} k Ω (f ≫ t)).trans
    (Φ.skyscraperSheafAdjunction.homEquiv_naturality_right
      (fieldEquivariantStalkUnderlyingMap.{u, w} k Ω f) b)
  have hi := fieldInvariantSkyscraperInclusion_naturality.{u, w} k Ω t
  have hr := (Category.assoc a _ iN).trans
    ((congrArg (fun q => a ≫ q) hi).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q ≫ Φ.skyscraperSheafFunctor.map b)
        (fieldEquivariantStalkToInverse_fac.{u, w} k Ω f))))
  exact hl.trans hr.symm

/-- Natural Hom correspondence for the field stalk adjunction.

The equivariant Hom bijection with its source and coefficient naturality gives the adjunction
Hom data. -/
def fieldEquivariantStalkAdjunctionCore :
    Adjunction.CoreHomEquiv (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω) where
  homEquiv := fieldEquivariantStalkHomEquiv.{u, w} k Ω
  homEquiv_naturality_left_symm := fieldEquivariantStalkFromInverse_naturality_left.{u, w} k Ω
  homEquiv_naturality_right := fieldEquivariantStalkToInverse_naturality_right.{u, w} k Ω

/-- Geometric Galois stalk is left adjoint to the invariant inverse sheaf.

The natural equivariant Hom correspondence defines the field stalk/inverse-sheaf adjunction. -/
def fieldEquivariantStalkAdjunction :
    fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⊣
      fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω :=
  Adjunction.mkOfHomEquiv (fieldEquivariantStalkAdjunctionCore.{u, w} k Ω)

/-- Field stalk adjunction has the constructed transpose correspondence.

The adjunction Hom equivalence equals the invariant-cone transpose equivalence. -/
theorem fieldEquivariantStalkAdjunction_homEquiv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldEquivariantStalkAdjunction.{u, w} k Ω).homEquiv Q M =
      fieldEquivariantStalkHomEquiv.{u, w} k Ω Q M :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv
    (fieldEquivariantStalkAdjunctionCore.{u, w} k Ω)) Q) M

/-- Geometric Galois stalk functor is additive.

The field stalk left adjoint preserves sums of sheaf maps. -/
instance fieldGeometricStalkGaloisFunctor_additive :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).Additive :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).left_adjoint_additive

/-- Additive field stalk Hom correspondence.

The adjunction Hom correspondence is an additive equivalence of Hom groups. -/
abbrev fieldEquivariantStalkHomAddEquiv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) ≃+
      (Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).homAddEquiv Q M

/-- Additive stalk correspondence has the same underlying bijection.

Its underlying equivalence is the invariant-cone transpose correspondence. -/
theorem fieldEquivariantStalkHomAddEquiv_toEquiv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).toEquiv =
      fieldEquivariantStalkHomEquiv.{u, w} k Ω Q M :=
  fieldEquivariantStalkAdjunction_homEquiv.{u, w} k Ω Q M

/-- Unit of the equivariant field stalk adjunction.

The unit sends a sheaf to the invariant inverse sheaf of its geometric Galois stalk. -/
abbrev fieldEquivariantStalkUnit :
    𝟭 (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) ⟶
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⋙
        fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).unit

/-- Counit of the equivariant field stalk adjunction.

The counit maps the Galois stalk of an invariant inverse sheaf back to its coefficient. -/
abbrev fieldEquivariantStalkCounit :
    fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω ⋙
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ⟶
        𝟭 (DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).counit

/-- Field stalk unit has the identity stalk transpose.

The unit followed by the invariant skyscraper projection is the ordinary transpose of the
identity geometric-stalk map. -/
theorem fieldEquivariantStalkUnit_inclusion
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldEquivariantStalkUnit.{u, w} k Ω).app Q ≫
      (fieldInvariantSkyscraperSheafCone.{u, w} k Ω
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)).π.app
          (SingleObj.star Gal(Ω/k)) =
    fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) (𝟙 _) := by
  have hu : (fieldEquivariantStalkUnit.{u, w} k Ω).app Q =
      fieldEquivariantStalkToInverse.{u, w} k Ω
        (𝟙 ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) :=
    ((fieldEquivariantStalkAdjunction.{u, w} k Ω).homEquiv_id Q).symm.trans
      (congrArg (fun e => e (𝟙 _)) (fieldEquivariantStalkAdjunction_homEquiv.{u, w} k Ω Q _))
  exact (congrArg (fun h => h ≫
    (fieldInvariantSkyscraperSheafCone.{u, w} k Ω
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)).π.app
        (SingleObj.star Gal(Ω/k))) hu).trans (fieldEquivariantStalkToInverse_fac.{u, w} k Ω _)

/-- Field stalk counit is projected point evaluation.

Its underlying map is the stalk map of the invariant projection followed by the point-
skyscraper counit. -/
theorem fieldEquivariantStalkCounit_underlying
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (DiscreteAbelianAction.forget Gal(Ω/k)).map
        ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) =
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map
        ((fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k))) ≫
      (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).skyscraperSheafAdjunction.counit.app
        ((fieldModuleAbAction.{u, w} k Ω M).V) := by
  let R := fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω
  let i := (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k))
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  have hc : (fieldEquivariantStalkCounit.{u, w} k Ω).app M =
      fieldEquivariantStalkFromInverse.{u, w} k Ω (𝟙 (R.obj M)) :=
    ((fieldEquivariantStalkAdjunction.{u, w} k Ω).homEquiv_symm_id M).symm.trans
      (congrArg (fun e => e.symm (𝟙 _))
        (fieldEquivariantStalkAdjunction_homEquiv.{u, w} k Ω (R.obj M) M))
  have hmap := congrArg (DiscreteAbelianAction.forget Gal(Ω/k)).map hc
  have hid : (𝟙 (R.obj M)) ≫ i = i := Category.id_comp _
  exact hmap.trans ((congrArg (fieldStalkSkyscraperHomEquiv.{u, w} k Ω (R.obj M) M).symm hid).trans
    (Φ.skyscraperSheafAdjunction.homEquiv_symm_apply (R.obj M)
      ((fieldModuleAbAction.{u, w} k Ω M).V) i))


/-- Equivariant transpose evaluates by a geometric germ.

The inverse-sheaf section map followed by evaluation at a geometric point equals the germ map
followed by the underlying equivariant stalk map. -/
theorem fieldEquivariantStalkToInverse_germ_map
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M)
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (fieldEquivariantStalkToInverse.{u, w} k Ω f).hom.app (op U) ≫
        AddCommGrpCat.ofHom (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U z) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj ≫ fieldEquivariantStalkUnderlyingMap.{u, w} k Ω f := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let C := (fieldModuleAbAction.{u, w} k Ω M).V
  let a := (fieldEquivariantStalkToInverse.{u, w} k Ω f).hom.app (op U)
  let i := (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k))
  let b := fieldEquivariantStalkUnderlyingMap.{u, w} k Ω f
  let h := fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M b
  have hi := fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U (ULift.up z)
  have hc := congrArg (fun t => t.hom.app (op U) ≫
    Pi.π (fun _ : Φ.fiber.obj U => C) (ULift.up z))
      (fieldEquivariantStalkToInverse_fac.{u, w} k Ω f)
  have hl := (Category.assoc a (i.hom.app (op U)) _).trans (congrArg (fun t => a ≫ t) hi)
  have hs := Φ.skyscraperSheafAdjunction_homEquiv_apply_hom (F := Q) (M := C) b
  change h.hom = Φ.skyscraperPresheafHomEquiv b at hs
  have hp := (congrArg (fun t => t.app (op U) ≫
      Pi.π (fun _ : Φ.fiber.obj U => C) (ULift.up z)) hs).trans
    (Φ.skyscraperPresheafHomEquiv_app_π b U (ULift.up z))
  exact hl.symm.trans (hc.trans hp)

/-- Value of an equivariant transpose on a section.

At geometric fiber element `z`, the transposed section has value the equivariant map applied
to the germ of that section at `z`. -/
theorem fieldEquivariantStalkToInverse_germ_apply
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M)
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : Q.obj.obj (op U)) :
    (show FieldEquivariantFunctions.{u, w} k Ω U M from
      (fieldEquivariantStalkToInverse.{u, w} k Ω f).hom.app (op U) c) z =
    DiscreteAbelianAction.homToAdd f
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj c) :=
  congrArg (fun t => t c) (fieldEquivariantStalkToInverse_germ_map.{u, w} k Ω f U z)

/-- Field stalk unit is the transpose of the identity.

The adjunction unit equals the inverse-sheaf transpose of the identity stalk morphism. -/
theorem fieldEquivariantStalkUnit_toInverse_id
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldEquivariantStalkUnit.{u, w} k Ω).app Q =
      fieldEquivariantStalkToInverse.{u, w} k Ω
        (𝟙 ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) :=
  ((fieldEquivariantStalkAdjunction.{u, w} k Ω).homEquiv_id Q).symm.trans
    (congrArg (fun e => e (𝟙 _)) (fieldEquivariantStalkAdjunction_homEquiv.{u, w} k Ω Q _))

/-- Field stalk unit sends a section to its germ function.

The unit section evaluated at `z` is the geometric germ of the given section at `z`. -/
theorem fieldEquivariantStalkUnit_germ
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : Q.obj.obj (op U)) :
    (show FieldEquivariantFunctions.{u, w} k Ω U
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) from
        ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q).hom.app (op U) c) z =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj c := by
  have hu := congrArg (fun h =>
    fieldEquivariantFunctionEvaluation.{u, w} k Ω
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) U z (h.hom.app (op U) c))
      (fieldEquivariantStalkUnit_toInverse_id.{u, w} k Ω Q)
  exact hu.trans (fieldEquivariantStalkToInverse_germ_apply.{u, w} k Ω (𝟙 _) U z c)

/-- Field stalk counit on germs is coefficient evaluation.

The germ map followed by the underlying counit equals evaluation of the equivariant section at
its fiber element. -/
theorem fieldEquivariantStalkCounit_germ_map
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
        (ULift.up z) ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj ≫
      (DiscreteAbelianAction.forget Gal(Ω/k)).map
        ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) =
    AddCommGrpCat.ofHom (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U z) := by
  let R := fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let C := (fieldModuleAbAction.{u, w} k Ω M).V
  let i := (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k))
  let p := Φ.toPresheafFiber U (ULift.up z) (R.obj M).obj
  let ε := Φ.skyscraperSheafAdjunction.counit.app C
  have hc := fieldEquivariantStalkCounit_underlying.{u, w} k Ω M
  have hn := Φ.toPresheafFiber_naturality i.hom U (ULift.up z)
  have hp := GrothendieckTopology.Point.toPresheafFiber_skyscraperSheafAdjunction_counit
    Φ C U (ULift.up z)
  have hi := fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U (ULift.up z)
  exact (congrArg (fun t => p ≫ t) hc).trans
    ((Category.assoc p _ ε).symm.trans
      ((congrArg (fun t => t ≫ ε) hn).trans ((Category.assoc _ _ _).trans
        ((congrArg (fun t => i.hom.app (op U) ≫ t) hp).trans hi))))

/-- Field stalk counit evaluates an equivariant section.

The counit sends the germ of a section `h` at `z` to `h z`. -/
theorem fieldEquivariantStalkCounit_germ
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M) :
    DiscreteAbelianAction.homToAdd ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
        (ULift.up z) ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj h) = h z :=
  congrArg (fun t => t h) (fieldEquivariantStalkCounit_germ_map.{u, w} k Ω M U z)

/-- Field stalk unit is sheaf natural.

The unit commutes with a sheaf morphism and the inverse-sheaf image of its stalk morphism. -/
theorem fieldEquivariantStalkUnit_naturality
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q') :
    τ ≫ (fieldEquivariantStalkUnit.{u, w} k Ω).app Q' =
      (fieldEquivariantStalkUnit.{u, w} k Ω).app Q ≫
        (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map τ) :=
  (fieldEquivariantStalkUnit.{u, w} k Ω).naturality τ

/-- Field stalk counit is coefficient natural.

The counit commutes with the stalk image of an inverse-sheaf coefficient map and the given
coefficient map. -/
theorem fieldEquivariantStalkCounit_naturality
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t) ≫
      (fieldEquivariantStalkCounit.{u, w} k Ω).app N =
    (fieldEquivariantStalkCounit.{u, w} k Ω).app M ≫ t :=
  (fieldEquivariantStalkCounit.{u, w} k Ω).naturality t

/-- Equivariant field stalk adjunction satisfies the left triangle.

Apply the stalk functor to the unit and then the counit at the stalk coefficient; the
composite is the identity. -/
theorem fieldEquivariantStalk_left_triangle
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q) ≫
      (fieldEquivariantStalkCounit.{u, w} k Ω).app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) = 𝟙 _ :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).left_triangle_components Q

/-- Equivariant field stalk adjunction satisfies the right triangle.

The unit at the inverse sheaf followed by its image of the coefficient counit is the identity. -/
theorem fieldEquivariantStalk_right_triangle
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldEquivariantStalkUnit.{u, w} k Ω).app
        ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) ≫
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map
        ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) = 𝟙 _ :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).right_triangle_components M


/-- Additive stalk correspondence is natural in the sheaf.

Precomposition by a sheaf map commutes with the additive Hom correspondence. -/
theorem fieldEquivariantStalkHomAddEquiv_naturality_left
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (τ : Q' ⟶ Q) (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) :
    fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q' M
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map τ ≫ f) =
      τ ≫ fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M f :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).homEquiv_naturality_left τ f

/-- Additive stalk correspondence is natural in coefficients.

Postcomposition by a coefficient map commutes with the additive Hom correspondence. -/
theorem fieldEquivariantStalkHomAddEquiv_naturality_right
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) (t : M ⟶ N) :
    fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q N (f ≫ t) =
      fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M f ≫
        (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).homEquiv_naturality_right f t

/-- Inverse additive stalk correspondence is sheaf natural.

The inverse correspondence commutes with sheaf precomposition and the induced stalk map. -/
theorem fieldEquivariantStalkHomAddEquiv_symm_naturality_left
    {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (τ : Q' ⟶ Q) (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) :
    (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q' M).symm (τ ≫ h) =
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map τ ≫
        (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).symm h :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).homEquiv_naturality_left_symm τ h

/-- Inverse additive stalk correspondence is coefficient natural.

The inverse correspondence commutes with the inverse-sheaf coefficient map and coefficient
postcomposition. -/
theorem fieldEquivariantStalkHomAddEquiv_symm_naturality_right
    {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
    (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) (t : M ⟶ N) :
    (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q N).symm
        (h ≫ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t) =
      (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).symm h ≫ t :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).homEquiv_naturality_right_symm h t

/-- Field stalk unit retains lifted coefficient germ values.

For a sheaf in coefficient universe `w`, the unit evaluated on a lifted section is its common
geometric germ. -/
theorem fieldEquivariantStalkUnit_original_germ
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : F.obj.obj (op U)) :
    (show FieldEquivariantFunctions.{u, w} k Ω U
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) from
      ((fieldEquivariantStalkUnit.{u, w} k Ω).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom.app (op U) (ULift.up c)) z =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
      (ULift.up z) ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c) :=
  fieldEquivariantStalkUnit_germ.{u, w} k Ω
    ((liftCoefficients.{u, w} (Spec (.of k))).obj F) U z (ULift.up c)

/-- Full additive and invariant field stalk Hom laws.

The correspondence has the specified underlying bijection, inverse and additive laws,
naturality in both directions, invariant-equivariant criterion, cone factorization, and
geometric-germ values. -/
def FieldEquivariantStalkHomLaws : Prop :=
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)),
    (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).toEquiv =
      fieldEquivariantStalkHomEquiv.{u, w} k Ω Q M) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M),
    (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).symm
      (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M f) = f) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M),
    fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M
      ((fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).symm h) = h) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      (f g : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M),
    fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M (f + g) =
      fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M f +
        fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M g) ∧
  (∀ {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
      (τ : Q' ⟶ Q) (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M),
    fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q' M
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map τ ≫ f) =
      τ ≫ fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M f) ∧
  (∀ {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
      (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M) (t : M ⟶ N),
    fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q N (f ≫ t) =
      fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M f ≫
        (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t) ∧
  (∀ {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
      (τ : Q' ⟶ Q) (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M),
    (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q' M).symm (τ ≫ h) =
      (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map τ ≫
        (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).symm h) ∧
  (∀ {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
      (h : Q ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) (t : M ⟶ N),
    (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q N).symm
        (h ≫ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t) =
      (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).symm h ≫ t) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      (h : Q ⟶ fieldSkyscraper.{u, w} k Ω M),
    FieldInvariantSkyscraperHom.{u, w} k Ω Q M h ↔
      FieldEquivariantStalkAbHom.{u, w} k Ω Q M
        ((fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M).symm h)) ∧
  (∀ {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
      (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M),
    fieldEquivariantStalkToInverse.{u, w} k Ω f ≫
        (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) =
      fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q M
        (fieldEquivariantStalkUnderlyingMap.{u, w} k Ω f)) ∧
  ∀ {Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
      {M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)}
      (f : (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q ⟶ M)
      (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
      (c : Q.obj.obj (op U)),
    (show FieldEquivariantFunctions.{u, w} k Ω U M from
      (fieldEquivariantStalkToInverse.{u, w} k Ω f).hom.app (op U) c) z =
    DiscreteAbelianAction.homToAdd f
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj c)

/-- Full field stalk unit and counit laws.

The unit and counit are the adjunction maps, satisfy naturality and both triangles, and have
the invariant projection, germ, evaluation, and lifted-section formulas. -/
def FieldEquivariantStalkUnitCounitLaws : Prop :=
  (fieldEquivariantStalkUnit.{u, w} k Ω = (fieldEquivariantStalkAdjunction.{u, w} k Ω).unit) ∧
  (fieldEquivariantStalkCounit.{u, w} k Ω = (fieldEquivariantStalkAdjunction.{u, w} k Ω).counit) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
      (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
      (c : Q.obj.obj (op U)),
    (show FieldEquivariantFunctions.{u, w} k Ω U
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) from
        ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q).hom.app (op U) c) z =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj c) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
      (h : FieldEquivariantFunctions.{u, w} k Ω U M),
    DiscreteAbelianAction.homToAdd ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
        (ULift.up z) ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj h) = h z) ∧
  (∀ {Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}} (τ : Q ⟶ Q'),
    τ ≫ (fieldEquivariantStalkUnit.{u, w} k Ω).app Q' =
      (fieldEquivariantStalkUnit.{u, w} k Ω).app Q ≫
        (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map τ)) ∧
  (∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N),
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t) ≫
      (fieldEquivariantStalkCounit.{u, w} k Ω).app N =
    (fieldEquivariantStalkCounit.{u, w} k Ω).app M ≫ t) ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q) ≫
      (fieldEquivariantStalkCounit.{u, w} k Ω).app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) = 𝟙 _) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    (fieldEquivariantStalkUnit.{u, w} k Ω).app
        ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M) ≫
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map
        ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) = 𝟙 _) ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    (fieldEquivariantStalkUnit.{u, w} k Ω).app Q ≫
      (fieldInvariantSkyscraperSheafCone.{u, w} k Ω
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)).π.app
          (SingleObj.star Gal(Ω/k)) =
    fieldStalkSkyscraperHomEquiv.{u, w} k Ω Q
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) (𝟙 _)) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    (DiscreteAbelianAction.forget Gal(Ω/k)).map
        ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) =
      (smallEtaleCommonGeometricStalk.{u, w} (Spec.algebraMap k Ω)).map
        ((fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k))) ≫
      (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).skyscraperSheafAdjunction.counit.app
          ((fieldModuleAbAction.{u, w} k Ω M).V)) ∧
  ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
      (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
      (c : F.obj.obj (op U)),
    (show FieldEquivariantFunctions.{u, w} k Ω U
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) from
      ((fieldEquivariantStalkUnit.{u, w} k Ω).app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom.app (op U) (ULift.up c)) z =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
      (ULift.up z) ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c)

/-- Equivariant field stalk correspondence satisfies all adjunction laws.

The constructed correspondence satisfies the complete additive Hom laws and unit/counit
normalization, naturality, and triangle laws. -/
theorem original_field_equivariant_stalk_adjunction :
    FieldEquivariantStalkHomLaws.{u, w} k Ω ∧
      FieldEquivariantStalkUnitCounitLaws.{u, w} k Ω := by
  constructor
  · refine ⟨fieldEquivariantStalkHomAddEquiv_toEquiv.{u, w} k Ω,
      fun Q M f => (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).symm_apply_apply f,
      fun Q M h => (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).apply_symm_apply h,
      fun Q M f g => (fieldEquivariantStalkHomAddEquiv.{u, w} k Ω Q M).map_add f g,
      fieldEquivariantStalkHomAddEquiv_naturality_left.{u, w} k Ω,
      fieldEquivariantStalkHomAddEquiv_naturality_right.{u, w} k Ω,
      fieldEquivariantStalkHomAddEquiv_symm_naturality_left.{u, w} k Ω,
      fieldEquivariantStalkHomAddEquiv_symm_naturality_right.{u, w} k Ω,
      fieldStalkSkyscraperHomEquiv_invariant_iff.{u, w} k Ω,
      fieldEquivariantStalkToInverse_fac.{u, w} k Ω,
      fieldEquivariantStalkToInverse_germ_apply.{u, w} k Ω⟩
  · exact ⟨rfl, rfl, fieldEquivariantStalkUnit_germ.{u, w} k Ω,
      fieldEquivariantStalkCounit_germ.{u, w} k Ω,
      fieldEquivariantStalkUnit_naturality.{u, w} k Ω,
      fieldEquivariantStalkCounit_naturality.{u, w} k Ω,
      fieldEquivariantStalk_left_triangle.{u, w} k Ω,
      fieldEquivariantStalk_right_triangle.{u, w} k Ω,
      fieldEquivariantStalkUnit_inclusion.{u, w} k Ω,
      fieldEquivariantStalkCounit_underlying.{u, w} k Ω,
      fieldEquivariantStalkUnit_original_germ.{u, w} k Ω⟩

end AlgebraicGeometry.Scheme.DerivedSections
