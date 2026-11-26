/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleTensorCoefficients

/-!
# Tensor pairings of the Godement monad and its coresolution

Let X be a scheme in universe u and c = max(u, w).
For AddCommGrpCat c-valued étale sheaves, the stalk-family functor L has
product-skyscraper right adjoint R and Godement monad T = R L.
The tensor stalk isomorphism is pointwise over X.

The adjoint transpose of the tensor of the family counits gives
R(M) ⊗_sheaf R(N) → R(M ⊗[ℤ] N).
It induces the lax tensor map m : T(F) ⊗_sheaf T(H) → T(F ⊗_sheaf H),
natural in coefficients and compatible with the monad unit and multiplication.
Its iterates m_n pair T^n(F) and T^n(H).
The cosimplicial Godement coresolution has degree n term T^(n+1)(F);
its pairing commutes with every coface and with coefficient maps.
The scheme and coefficient universes are independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For coefficient families M_x, N_x over x ∈ X, their tensor family
is x ↦ M_x ⊗[ℤ] N_x, with pointwise abelian-group structure. -/
def smallEtaleGodementFamilyTensor (X : Scheme.{u})
    (M N : X → AddCommGrpCat.{max u w}) : X → AddCommGrpCat.{max u w} :=
  fun x => AddCommGrpCat.of (M x ⊗[ℤ] N x)

/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For sheaves F, H, the stalk-family isomorphism
L(F ⊗_sheaf H) ≅ L(F) ⊗ L(H) has at x the canonical tensor-stalk
isomorphism at the geometric point over x. -/
def smallEtaleGodementStalkTensorIso (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleGodementStalks.{u, w} X).obj (smallEtaleTensorSheaf.{u, w} X F G) ≅
      smallEtaleGodementFamilyTensor.{u, w} X
        ((smallEtaleGodementStalks.{u, w} X).obj F)
        ((smallEtaleGodementStalks.{u, w} X).obj G) where
  hom x := (smallEtalePointTensorSheafStalkIso.{u, w} X
    (smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)) F G).hom
  inv x := (smallEtalePointTensorSheafStalkIso.{u, w} X
    (smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)) F G).inv
  hom_inv_id := by
    funext x
    exact (smallEtalePointTensorSheafStalkIso.{u, w} X
      (smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)) F
          G).hom_inv_id
  inv_hom_id := by
    funext x
    exact (smallEtalePointTensorSheafStalkIso.{u, w} X
      (smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)) F
          G).inv_hom_id

/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For pointwise coefficient-family maps f : M → M′ and g : N → N′,
their tensor-family map has component f_x ⊗[ℤ] g_x at each x ∈ X. -/
def smallEtaleGodementFamilyTensorMap (X : Scheme.{u})
    {M M' N N' : X → AddCommGrpCat.{max u w}} (f : M ⟶ M') (g : N ⟶ N') :
    smallEtaleGodementFamilyTensor.{u, w} X M N ⟶
      smallEtaleGodementFamilyTensor.{u, w} X M' N' :=
  fun x => AddCommGrpCat.ofHom
    (TensorProduct.map (f x).hom.toIntLinearMap (g x).hom.toIntLinearMap).toAddMonoidHom

/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
With L the stalk family, R its product-skyscraper right adjoint,
and ε the adjunction counit, this map
R(M) ⊗_sheaf R(N) → R(M ⊗ N) is adjoint to
(ε_M ⊗ ε_N) ∘ τ_(R(M),R(N)), where τ is the stalk-family tensor
isomorphism. -/
def smallEtaleGodementSkyscraperPairing (X : Scheme.{u})
    (M N : X → AddCommGrpCat.{max u w}) :
    smallEtaleTensorSheaf.{u, w} X
        ((smallEtaleGodementSkyscrapers.{u, w} X).obj M)
        ((smallEtaleGodementSkyscrapers.{u, w} X).obj N) ⟶
      (smallEtaleGodementSkyscrapers.{u, w} X).obj
        (smallEtaleGodementFamilyTensor.{u, w} X M N) :=
  (smallEtaleGodementAdjunction.{u, w} X).homEquiv _ _
    ((smallEtaleGodementStalkTensorIso.{u, w} X
      ((smallEtaleGodementSkyscrapers.{u, w} X).obj M)
      ((smallEtaleGodementSkyscrapers.{u, w} X).obj N)).hom ≫
      smallEtaleGodementFamilyTensorMap.{u, w} X
        ((smallEtaleGodementAdjunction.{u, w} X).counit.app M)
        ((smallEtaleGodementAdjunction.{u, w} X).counit.app N))

/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
The Godement tensor map m : T(F) ⊗_sheaf T(H) → T(F ⊗_sheaf H)
pairs the product skyscrapers of the two stalk families and uses
the inverse stalk-family tensor isomorphism in the target. -/
def smallEtaleGodementTensorPairing (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleTensorSheaf.{u, w} X
        ((smallEtaleGodement.{u, w} X).obj F)
        ((smallEtaleGodement.{u, w} X).obj G) ⟶
      (smallEtaleGodement.{u, w} X).obj (smallEtaleTensorSheaf.{u, w} X F G) :=
  smallEtaleGodementSkyscraperPairing.{u, w} X
      ((smallEtaleGodementStalks.{u, w} X).obj F)
      ((smallEtaleGodementStalks.{u, w} X).obj G) ≫
    (smallEtaleGodementSkyscrapers.{u, w} X).map
      (smallEtaleGodementStalkTensorIso.{u, w} X F G).inv

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For sheaf maps f : F → F′ and g : H → H′, the stalk-family
isomorphisms satisfy
τ_(F′,H′) ∘ L(f ⊗_sheaf g) = (L(f) ⊗ L(g)) ∘ τ_(F,H). -/
theorem smallEtaleGodementStalkTensorIso_naturality (X : Scheme.{u})
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    (smallEtaleGodementStalks.{u, w} X).map (smallEtaleTensorSheafMap.{u, w} X f g) ≫
        (smallEtaleGodementStalkTensorIso.{u, w} X F' G').hom =
      (smallEtaleGodementStalkTensorIso.{u, w} X F G).hom ≫
        smallEtaleGodementFamilyTensorMap.{u, w} X
          ((smallEtaleGodementStalks.{u, w} X).map f)
          ((smallEtaleGodementStalks.{u, w} X).map g) := by
  funext x
  exact smallEtalePointTensorSheafStalkIso_naturality.{u, w} X
    (smallEtaleGeometricPointCommon.{u, w} (smallEtaleCanonicalGeometricMorphism X x)) f g

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For family maps f : A → B, g : B → C, h : D → E and i : E → H,
their pointwise tensor maps satisfy
(g ⊗ i) ∘ (f ⊗ h) = (g ∘ f) ⊗ (i ∘ h). -/
theorem smallEtaleGodementFamilyTensorMap_comp (X : Scheme.{u})
    {A B C D E H : X → AddCommGrpCat.{max u w}}
    (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ E) (i : E ⟶ H) :
    smallEtaleGodementFamilyTensorMap.{u, w} X f h ≫
        smallEtaleGodementFamilyTensorMap.{u, w} X g i =
      smallEtaleGodementFamilyTensorMap.{u, w} X (f ≫ g) (h ≫ i) := by
  funext x
  exact congrArg (fun l => AddCommGrpCat.ofHom l.toAddMonoidHom)
    (TensorProduct.map_comp (g x).hom.toIntLinearMap (i x).hom.toIntLinearMap
      (f x).hom.toIntLinearMap (h x).hom.toIntLinearMap).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
The tensor pairing m and monad unit η satisfy
m_(F,H) ∘ (η_F ⊗_sheaf η_H) = η_(F⊗H). -/
theorem smallEtaleGodementTensorPairing_unit (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleTensorSheafMap.{u, w} X
        ((smallEtaleGodementUnit.{u, w} X).app F)
        ((smallEtaleGodementUnit.{u, w} X).app G) ≫
      smallEtaleGodementTensorPairing.{u, w} X F G =
        (smallEtaleGodementUnit.{u, w} X).app (smallEtaleTensorSheaf.{u, w} X F G) := by
  let L := smallEtaleGodementStalks.{u, w} X
  let R := smallEtaleGodementSkyscrapers.{u, w} X
  let adj := smallEtaleGodementAdjunction.{u, w} X
  let LF := L.obj F
  let LG := L.obj G
  let Q := smallEtaleTensorSheaf.{u, w} X F G
  let a := smallEtaleTensorSheafMap.{u, w} X (adj.unit.app F) (adj.unit.app G)
  let b := (smallEtaleGodementStalkTensorIso.{u, w} X (R.obj LF) (R.obj LG)).hom ≫
    smallEtaleGodementFamilyTensorMap.{u, w} X (adj.counit.app LF) (adj.counit.app LG)
  let e := smallEtaleGodementStalkTensorIso.{u, w} X F G
  have hn : L.map a ≫ (smallEtaleGodementStalkTensorIso.{u, w} X (R.obj LF) (R.obj LG)).hom =
      e.hom ≫ smallEtaleGodementFamilyTensorMap.{u, w} X
        (L.map (adj.unit.app F)) (L.map (adj.unit.app G)) :=
    smallEtaleGodementStalkTensorIso_naturality.{u, w} X (adj.unit.app F) (adj.unit.app G)
  have ht : smallEtaleGodementFamilyTensorMap.{u, w} X
      (L.map (adj.unit.app F)) (L.map (adj.unit.app G)) ≫
      smallEtaleGodementFamilyTensorMap.{u, w} X
        (adj.counit.app LF) (adj.counit.app LG) = 𝟙 _ := by
    have hF : L.map (adj.unit.app F) ≫ adj.counit.app LF = 𝟙 LF :=
      adj.left_triangle_components F
    have hG : L.map (adj.unit.app G) ≫ adj.counit.app LG = 𝟙 LG :=
      adj.left_triangle_components G
    rw [smallEtaleGodementFamilyTensorMap_comp, hF, hG]
    funext x
    have h : TensorProduct.map (LinearMap.id : LF x →ₗ[ℤ] LF x)
        (LinearMap.id : LG x →ₗ[ℤ] LG x) = LinearMap.id := TensorProduct.map_id
    exact congrArg (fun l : LF x ⊗[ℤ] LG x →ₗ[ℤ] LF x ⊗[ℤ] LG x =>
      AddCommGrpCat.ofHom l.toAddMonoidHom) h
  have hb : L.map a ≫ b = e.hom := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun l => l ≫ smallEtaleGodementFamilyTensorMap.{u, w} X
        (adj.counit.app LF) (adj.counit.app LG)) hn).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun l => e.hom ≫ l) ht).trans (Category.comp_id _))))
  change a ≫ (adj.homEquiv _ _ b ≫ R.map e.inv) = adj.unit.app Q
  rw [← Category.assoc, ← adj.homEquiv_naturality_left,
    ← adj.homEquiv_naturality_right, hb, e.hom_inv_id]
  exact adj.homEquiv_id Q

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For coefficient-family maps f : M → M′ and g : N → N′, the
product-skyscraper pairing m_R satisfies
m_R′ ∘ (R(f) ⊗_sheaf R(g)) = R(f ⊗ g) ∘ m_R. -/
theorem smallEtaleGodementSkyscraperPairing_naturality (X : Scheme.{u})
    {M M' N N' : X → AddCommGrpCat.{max u w}} (f : M ⟶ M') (g : N ⟶ N') :
    smallEtaleTensorSheafMap.{u, w} X
        ((smallEtaleGodementSkyscrapers.{u, w} X).map f)
        ((smallEtaleGodementSkyscrapers.{u, w} X).map g) ≫
      smallEtaleGodementSkyscraperPairing.{u, w} X M' N' =
      smallEtaleGodementSkyscraperPairing.{u, w} X M N ≫
        (smallEtaleGodementSkyscrapers.{u, w} X).map
          (smallEtaleGodementFamilyTensorMap.{u, w} X f g) := by
  let L := smallEtaleGodementStalks.{u, w} X
  let R := smallEtaleGodementSkyscrapers.{u, w} X
  let adj := smallEtaleGodementAdjunction.{u, w} X
  let e := smallEtaleGodementStalkTensorIso.{u, w} X (R.obj M) (R.obj N)
  let e' := smallEtaleGodementStalkTensorIso.{u, w} X (R.obj M') (R.obj N')
  let a := smallEtaleTensorSheafMap.{u, w} X (R.map f) (R.map g)
  let b := e.hom ≫ smallEtaleGodementFamilyTensorMap.{u, w} X
    (adj.counit.app M) (adj.counit.app N)
  let b' := e'.hom ≫ smallEtaleGodementFamilyTensorMap.{u, w} X
    (adj.counit.app M') (adj.counit.app N')
  have hn : L.map a ≫ e'.hom = e.hom ≫ smallEtaleGodementFamilyTensorMap.{u, w} X
      (L.map (R.map f)) (L.map (R.map g)) :=
    smallEtaleGodementStalkTensorIso_naturality.{u, w} X (R.map f) (R.map g)
  have hf : L.map (R.map f) ≫ adj.counit.app M' = adj.counit.app M ≫ f :=
    adj.counit.naturality f
  have hg : L.map (R.map g) ≫ adj.counit.app N' = adj.counit.app N ≫ g :=
    adj.counit.naturality g
  have ht : smallEtaleGodementFamilyTensorMap.{u, w} X (L.map (R.map f)) (L.map (R.map g)) ≫
      smallEtaleGodementFamilyTensorMap.{u, w} X (adj.counit.app M') (adj.counit.app N') =
      smallEtaleGodementFamilyTensorMap.{u, w} X (adj.counit.app M) (adj.counit.app N) ≫
        smallEtaleGodementFamilyTensorMap.{u, w} X f g := by
    rw [smallEtaleGodementFamilyTensorMap_comp, hf, hg, smallEtaleGodementFamilyTensorMap_comp]
  have hb : L.map a ≫ b' = b ≫ smallEtaleGodementFamilyTensorMap.{u, w} X f g := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun l => l ≫ smallEtaleGodementFamilyTensorMap.{u, w} X
        (adj.counit.app M') (adj.counit.app N')) hn).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun l => e.hom ≫ l) ht).trans (Category.assoc _ _ _).symm)))
  change a ≫ adj.homEquiv _ _ b' = adj.homEquiv _ _ b ≫ R.map _
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right, hb]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For sheaf maps f : F → F′ and g : H → H′, the Godement pairing
satisfies m′ ∘ (T(f) ⊗_sheaf T(g)) = T(f ⊗_sheaf g) ∘ m. -/
theorem smallEtaleGodementTensorPairing_naturality (X : Scheme.{u})
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    smallEtaleTensorSheafMap.{u, w} X
        ((smallEtaleGodement.{u, w} X).map f)
        ((smallEtaleGodement.{u, w} X).map g) ≫
      smallEtaleGodementTensorPairing.{u, w} X F' G' =
      smallEtaleGodementTensorPairing.{u, w} X F G ≫
        (smallEtaleGodement.{u, w} X).map (smallEtaleTensorSheafMap.{u, w} X f g) := by
  let L := smallEtaleGodementStalks.{u, w} X
  let R := smallEtaleGodementSkyscrapers.{u, w} X
  let e := smallEtaleGodementStalkTensorIso.{u, w} X F G
  let e' := smallEtaleGodementStalkTensorIso.{u, w} X F' G'
  let m := smallEtaleGodementFamilyTensorMap.{u, w} X (L.map f) (L.map g)
  let a := smallEtaleTensorSheafMap.{u, w} X ((smallEtaleGodement.{u, w} X).map f)
    ((smallEtaleGodement.{u, w} X).map g)
  let b := smallEtaleTensorSheafMap.{u, w} X f g
  have he : m ≫ e'.inv = e.inv ≫ L.map b := by
    have hn : L.map b ≫ e'.hom = e.hom ≫ m :=
      smallEtaleGodementStalkTensorIso_naturality.{u, w} X f g
    apply (cancel_mono e'.hom).1
    calc
      (m ≫ e'.inv) ≫ e'.hom = m := by rw [Category.assoc, e'.inv_hom_id, Category.comp_id]
      _ = e.inv ≫ (e.hom ≫ m) := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
      _ = e.inv ≫ (L.map b ≫ e'.hom) := congrArg (fun l => e.inv ≫ l) hn.symm
      _ = (e.inv ≫ L.map b) ≫ e'.hom := (Category.assoc _ _ _).symm
  have hR : R.map m ≫ R.map e'.inv = R.map e.inv ≫ R.map (L.map b) :=
    (R.map_comp m e'.inv).symm.trans ((congrArg R.map he).trans (R.map_comp e.inv (L.map b)))
  have hs := smallEtaleGodementSkyscraperPairing_naturality.{u, w} X (L.map f) (L.map g)
  change a ≫ (smallEtaleGodementSkyscraperPairing.{u, w} X (L.obj F') (L.obj G') ≫ R.map e'.inv) =
    (smallEtaleGodementSkyscraperPairing.{u, w} X (L.obj F) (L.obj G) ≫ R.map e.inv) ≫
        R.map (L.map b)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun l => l ≫ R.map e'.inv) hs).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun l => smallEtaleGodementSkyscraperPairing.{u, w} X (L.obj F) (L.obj G) ≫
            l) hR).trans
          (Category.assoc _ _ _).symm)))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For L ⊣ R with counit ε, the product-skyscraper pairing m_R satisfies
ε_(M⊗N) ∘ L(m_R) = (ε_M ⊗ ε_N) ∘ τ_(R(M),R(N)).
This identifies its adjoint transpose on the stalk family. -/
theorem smallEtaleGodementSkyscraperPairing_counit (X : Scheme.{u})
    (M N : X → AddCommGrpCat.{max u w}) :
    (smallEtaleGodementStalks.{u, w} X).map (smallEtaleGodementSkyscraperPairing.{u, w} X M N) ≫
        (smallEtaleGodementAdjunction.{u, w} X).counit.app
          (smallEtaleGodementFamilyTensor.{u, w} X M N) =
      (smallEtaleGodementStalkTensorIso.{u, w} X
        ((smallEtaleGodementSkyscrapers.{u, w} X).obj M)
        ((smallEtaleGodementSkyscrapers.{u, w} X).obj N)).hom ≫
        smallEtaleGodementFamilyTensorMap.{u, w} X
          ((smallEtaleGodementAdjunction.{u, w} X).counit.app M)
          ((smallEtaleGodementAdjunction.{u, w} X).counit.app N) := by
  let adj := smallEtaleGodementAdjunction.{u, w} X
  let b := (smallEtaleGodementStalkTensorIso.{u, w} X
      ((smallEtaleGodementSkyscrapers.{u, w} X).obj M)
      ((smallEtaleGodementSkyscrapers.{u, w} X).obj N)).hom ≫
      smallEtaleGodementFamilyTensorMap.{u, w} X (adj.counit.app M) (adj.counit.app N)
  have h := (adj.homEquiv _ _).symm_apply_apply b
  exact ((adj.homEquiv_counit _ _ (adj.homEquiv _ _ b)).symm).trans h

set_option backward.isDefEq.respectTransparency.types false in
private theorem godementTensorPairing_counit (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    (smallEtaleGodementStalkTensorIso.{u, w} X
        ((smallEtaleGodement.{u, w} X).obj F) ((smallEtaleGodement.{u, w} X).obj G)).inv ≫
      (smallEtaleGodementStalks.{u, w} X).map (smallEtaleGodementTensorPairing.{u, w} X F G) ≫
      (smallEtaleGodementAdjunction.{u, w} X).counit.app
        ((smallEtaleGodementStalks.{u, w} X).obj (smallEtaleTensorSheaf.{u, w} X F G)) =
      smallEtaleGodementFamilyTensorMap.{u, w} X
        ((smallEtaleGodementAdjunction.{u, w} X).counit.app
          ((smallEtaleGodementStalks.{u, w} X).obj F))
        ((smallEtaleGodementAdjunction.{u, w} X).counit.app
          ((smallEtaleGodementStalks.{u, w} X).obj G)) ≫
        (smallEtaleGodementStalkTensorIso.{u, w} X F G).inv := by
  let L := smallEtaleGodementStalks.{u, w} X
  let R := smallEtaleGodementSkyscrapers.{u, w} X
  let adj := smallEtaleGodementAdjunction.{u, w} X
  let LF := L.obj F
  let LG := L.obj G
  let e := smallEtaleGodementStalkTensorIso.{u, w} X F G
  let eT := smallEtaleGodementStalkTensorIso.{u, w} X (R.obj LF) (R.obj LG)
  let r := smallEtaleGodementSkyscraperPairing.{u, w} X LF LG
  let t := smallEtaleGodementFamilyTensorMap.{u, w} X (adj.counit.app LF) (adj.counit.app LG)
  have he : L.map (R.map e.inv) ≫ adj.counit.app (L.obj (smallEtaleTensorSheaf.{u, w} X F G)) =
      adj.counit.app (smallEtaleGodementFamilyTensor.{u, w} X LF LG) ≫ e.inv :=
    adj.counit.naturality e.inv
  have hr : L.map r ≫ adj.counit.app (smallEtaleGodementFamilyTensor.{u, w} X LF LG) =
      eT.hom ≫ t := smallEtaleGodementSkyscraperPairing_counit.{u, w} X LF LG
  change eT.inv ≫ L.map (r ≫ R.map e.inv) ≫ adj.counit.app _ = t ≫ e.inv
  rw [L.map_comp]
  have h : L.map r ≫ L.map (R.map e.inv) ≫ adj.counit.app _ = (eT.hom ≫ t) ≫ e.inv := by
    exact (congrArg (fun a => L.map r ≫ a) he).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ e.inv) hr))
  calc
    eT.inv ≫ L.map r ≫ L.map (R.map e.inv) ≫ adj.counit.app _ =
        eT.inv ≫ ((eT.hom ≫ t) ≫ e.inv) := congrArg (fun a => eT.inv ≫ a) h
    _ = t ≫ e.inv := by rw [← Category.assoc, ← Category.assoc, eT.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
The tensor pairing m and monad multiplication μ satisfy
m_(F,H) ∘ (μ_F ⊗ μ_H) =
μ_(F⊗H) ∘ T(m_(F,H)) ∘ m_(T(F),T(H)).
Both sides map T²(F) ⊗_sheaf T²(H) to T(F ⊗_sheaf H). -/
theorem smallEtaleGodementTensorPairing_mul (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleTensorSheafMap.{u, w} X
        ((smallEtaleGodementMonad.{u, w} X).μ.app F)
        ((smallEtaleGodementMonad.{u, w} X).μ.app G) ≫
      smallEtaleGodementTensorPairing.{u, w} X F G =
      smallEtaleGodementTensorPairing.{u, w} X
        ((smallEtaleGodement.{u, w} X).obj F) ((smallEtaleGodement.{u, w} X).obj G) ≫
        (smallEtaleGodement.{u, w} X).map (smallEtaleGodementTensorPairing.{u, w} X F G) ≫
        (smallEtaleGodementMonad.{u, w} X).μ.app (smallEtaleTensorSheaf.{u, w} X F G) := by
  let L := smallEtaleGodementStalks.{u, w} X
  let R := smallEtaleGodementSkyscrapers.{u, w} X
  let adj := smallEtaleGodementAdjunction.{u, w} X
  let LF := L.obj F
  let LG := L.obj G
  let Q := smallEtaleTensorSheaf.{u, w} X F G
  let e := smallEtaleGodementStalkTensorIso.{u, w} X F G
  let eT := smallEtaleGodementStalkTensorIso.{u, w} X (R.obj LF) (R.obj LG)
  let m := smallEtaleGodementTensorPairing.{u, w} X F G
  let t := smallEtaleGodementFamilyTensorMap.{u, w} X (adj.counit.app LF) (adj.counit.app LG)
  let r := smallEtaleGodementSkyscraperPairing.{u, w} X (L.obj (R.obj LF)) (L.obj (R.obj LG))
  have hn := smallEtaleGodementSkyscraperPairing_naturality.{u, w} X
    (adj.counit.app LF) (adj.counit.app LG)
  have hi : eT.inv ≫ L.map m ≫ adj.counit.app (L.obj Q) = t ≫ e.inv :=
    godementTensorPairing_counit.{u, w} X F G
  have hmap : (R.map eT.inv ≫ R.map (L.map m)) ≫ R.map (adj.counit.app (L.obj Q)) =
      R.map t ≫ R.map e.inv := by
    calc
      (R.map eT.inv ≫ R.map (L.map m)) ≫ R.map (adj.counit.app (L.obj Q)) =
          R.map (eT.inv ≫ L.map m) ≫ R.map (adj.counit.app (L.obj Q)) :=
        congrArg (fun a => a ≫ R.map (adj.counit.app (L.obj Q)))
          (R.map_comp eT.inv (L.map m)).symm
      _ = R.map ((eT.inv ≫ L.map m) ≫ adj.counit.app (L.obj Q)) :=
        (R.map_comp _ _).symm
      _ = R.map (eT.inv ≫ L.map m ≫ adj.counit.app (L.obj Q)) :=
        congrArg R.map (Category.assoc _ _ _)
      _ = R.map (t ≫ e.inv) := congrArg R.map hi
      _ = R.map t ≫ R.map e.inv := R.map_comp _ _
  change _ ≫ (smallEtaleGodementSkyscraperPairing.{u, w} X LF LG ≫ R.map e.inv) =
    (r ≫ R.map eT.inv) ≫ R.map (L.map m) ≫ R.map (adj.counit.app (L.obj Q))
  have hl : _ ≫ (smallEtaleGodementSkyscraperPairing.{u, w} X LF LG ≫ R.map e.inv) =
      (r ≫ R.map t) ≫ R.map e.inv :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ R.map e.inv) hn)
  exact hl.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => r ≫ a) hmap.symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun a => a ≫ R.map (adj.counit.app (L.obj Q)))
            (Category.assoc _ _ _).symm))))

/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For n ∈ ℕ, the iterated pairing is
m_n : T^n(F) ⊗_sheaf T^n(H) → T^n(F ⊗_sheaf H).
It starts with m₀ = id and obeys
m_(n+1)(F,H) = T^n(m₁(F,H)) ∘ m_n(T(F),T(H)). -/
def smallEtaleGodementPowerTensorPairing (X : Scheme.{u}) : (n : ℕ) →
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) →
    smallEtaleTensorSheaf.{u, w} X
        ((Monad.monadPow (smallEtaleGodementMonad.{u, w} X) n).obj F)
        ((Monad.monadPow (smallEtaleGodementMonad.{u, w} X) n).obj G) ⟶
      (Monad.monadPow (smallEtaleGodementMonad.{u, w} X) n).obj
        (smallEtaleTensorSheaf.{u, w} X F G)
  | 0, F, G => 𝟙 (smallEtaleTensorSheaf.{u, w} X F G)
  | n + 1, F, G =>
      smallEtaleGodementPowerTensorPairing X n
        ((smallEtaleGodement.{u, w} X).obj F) ((smallEtaleGodement.{u, w} X).obj G) ≫
        (Monad.monadPow (smallEtaleGodementMonad.{u, w} X) n).map
          (smallEtaleGodementTensorPairing.{u, w} X F G)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For sheaf maps f : F → F′, g : H → H′ and n ∈ ℕ,
m_n′ ∘ (T^n(f) ⊗ T^n(g)) = T^n(f ⊗ g) ∘ m_n. -/
theorem smallEtaleGodementPowerTensorPairing_naturality (X : Scheme.{u}) (n : ℕ)
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    smallEtaleTensorSheafMap.{u, w} X
        ((Monad.monadPow (smallEtaleGodementMonad.{u, w} X) n).map f)
        ((Monad.monadPow (smallEtaleGodementMonad.{u, w} X) n).map g) ≫
      smallEtaleGodementPowerTensorPairing.{u, w} X n F' G' =
      smallEtaleGodementPowerTensorPairing.{u, w} X n F G ≫
        (Monad.monadPow (smallEtaleGodementMonad.{u, w} X) n).map
          (smallEtaleTensorSheafMap.{u, w} X f g) := by
  induction n generalizing F F' G G' with
  | zero =>
      change smallEtaleTensorSheafMap.{u, w} X f g ≫ (𝟙 _) =
        (𝟙 _) ≫ smallEtaleTensorSheafMap.{u, w} X f g
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ n ih =>
      let T := smallEtaleGodementMonad.{u, w} X
      let P := Monad.monadPow T n
      let a := smallEtaleTensorSheafMap.{u, w} X (P.map (T.map f)) (P.map (T.map g))
      let e := smallEtaleGodementPowerTensorPairing.{u, w} X n (T.obj F) (T.obj G)
      let e' := smallEtaleGodementPowerTensorPairing.{u, w} X n (T.obj F') (T.obj G')
      let b := smallEtaleTensorSheafMap.{u, w} X (T.map f) (T.map g)
      let m := smallEtaleGodementTensorPairing.{u, w} X F G
      let m' := smallEtaleGodementTensorPairing.{u, w} X F' G'
      let c := smallEtaleTensorSheafMap.{u, w} X f g
      have hn : a ≫ e' = e ≫ P.map b := ih (T.map f) (T.map g)
      have hm : b ≫ m' = m ≫ T.map c :=
        smallEtaleGodementTensorPairing_naturality.{u, w} X f g
      change a ≫ (e' ≫ P.map m') = (e ≫ P.map m) ≫ P.map (T.map c)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun l => l ≫ P.map m') hn).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun l => e ≫ l)
              ((P.map_comp b m').symm.trans
                ((congrArg P.map hm).trans (P.map_comp m (T.map c))))).trans
                  (Category.assoc _ _ _).symm)))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For n ∈ ℕ and a unit insertion η_i : T^n → T^(n+1) at
position i ∈ Fin(n + 1), the power pairings satisfy
m_(n+1) ∘ (η_i(F) ⊗ η_i(H)) = η_i(F ⊗ H) ∘ m_n. -/
theorem smallEtaleGodementPowerTensorPairing_etaAtPos (X : Scheme.{u}) (n : ℕ)
    (i : Fin (n + 1)) (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleTensorSheafMap.{u, w} X
        (Monad.etaAtPos (smallEtaleGodementMonad.{u, w} X) n i F)
        (Monad.etaAtPos (smallEtaleGodementMonad.{u, w} X) n i G) ≫
      smallEtaleGodementPowerTensorPairing.{u, w} X (n + 1) F G =
      smallEtaleGodementPowerTensorPairing.{u, w} X n F G ≫
        Monad.etaAtPos (smallEtaleGodementMonad.{u, w} X) n i
          (smallEtaleTensorSheaf.{u, w} X F G) := by
  induction n generalizing F G with
  | zero =>
      have hi : i = 0 := by
        apply Fin.ext
        omega
      subst i
      exact smallEtaleGodementTensorPairing_unit.{u, w} X F G
  | succ n ih =>
      let T := smallEtaleGodementMonad.{u, w} X
      let P := Monad.monadPow T n
      cases i with
      | mk val hval =>
          cases val with
          | zero =>
              have hn := smallEtaleGodementPowerTensorPairing_naturality.{u, w} X (n + 1)
                (T.η.app F) (T.η.app G)
              have hu := smallEtaleGodementTensorPairing_unit.{u, w} X F G
              let P' := Monad.monadPow T (n + 1)
              let a := smallEtaleTensorSheafMap.{u, w} X (P'.map (T.η.app F)) (P'.map (T.η.app G))
              let e := smallEtaleGodementPowerTensorPairing.{u, w} X (n + 1) F G
              let e' := smallEtaleGodementPowerTensorPairing.{u, w} X (n + 1) (T.obj F) (T.obj G)
              let b := smallEtaleTensorSheafMap.{u, w} X (T.η.app F) (T.η.app G)
              let m := smallEtaleGodementTensorPairing.{u, w} X F G
              have h : a ≫ e' = e ≫ P'.map b := hn
              have hm : b ≫ m = T.η.app (smallEtaleTensorSheaf.{u, w} X F G) := hu
              change a ≫ (e' ≫ P'.map m) = e ≫ P'.map (T.η.app _)
              exact (Category.assoc _ _ _).symm.trans
                ((congrArg (fun l => l ≫ P'.map m) h).trans
                  ((Category.assoc _ _ _).trans
                    (congrArg (fun l => e ≫ l)
                      ((P'.map_comp b m).symm.trans (congrArg P'.map hm)))))
          | succ k =>
              let j : Fin (n + 1) := ⟨k, Nat.lt_of_succ_lt_succ hval⟩
              let P' := Monad.monadPow T (n + 1)
              let e := smallEtaleGodementPowerTensorPairing.{u, w} X n (T.obj F) (T.obj G)
              let e' := smallEtaleGodementPowerTensorPairing.{u, w} X (n + 1) (T.obj F) (T.obj G)
              let m := smallEtaleGodementTensorPairing.{u, w} X F G
              let a := smallEtaleTensorSheafMap.{u, w} X
                (Monad.etaAtPos T n j (T.obj F)) (Monad.etaAtPos T n j (T.obj G))
              let b := Monad.etaAtPos T n j (smallEtaleTensorSheaf.{u, w} X (T.obj F) (T.obj G))
              let c := Monad.etaAtPos T n j (T.obj (smallEtaleTensorSheaf.{u, w} X F G))
              have he : a ≫ e' = e ≫ b := ih j (T.obj F) (T.obj G)
              have hn : P.map m ≫ c = b ≫ P'.map m :=
                Monad.etaAtPos_naturality T n j m
              change a ≫ (e' ≫ P'.map m) = (e ≫ P.map m) ≫ c
              exact (Category.assoc _ _ _).symm.trans
                ((congrArg (fun l => l ≫ P'.map m) he).trans
                  ((Category.assoc _ _ _).trans
                    ((congrArg (fun l => e ≫ l) hn.symm).trans
                      (Category.assoc _ _ _).symm)))

/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
The degree n coresolution pairing
T^(n+1)(F) ⊗_sheaf T^(n+1)(H) → T^(n+1)(F ⊗_sheaf H)
is m_(n+1) under the canonical coresolution degree identifications. -/
def smallEtaleGodementCoresolutionTensorPairing (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    smallEtaleTensorSheaf.{u, w} X
        ((smallEtaleGodementCoresolution.{u, w} X F).obj (SimplexCategory.mk n))
        ((smallEtaleGodementCoresolution.{u, w} X G).obj (SimplexCategory.mk n)) ⟶
      (smallEtaleGodementCoresolution.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G)).obj
        (SimplexCategory.mk n) :=
  smallEtaleTensorSheafMap.{u, w} X
      (Monad.coresolutionObjIso (smallEtaleGodementMonad.{u, w} X) F n).hom
      (Monad.coresolutionObjIso (smallEtaleGodementMonad.{u, w} X) G n).hom ≫
    smallEtaleGodementPowerTensorPairing.{u, w} X (n + 1) F G ≫
      (Monad.coresolutionObjIso (smallEtaleGodementMonad.{u, w} X)
        (smallEtaleTensorSheaf.{u, w} X F G) n).inv

/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For the bar-oriented unit insertion b_i : T^n → T^(n+1),
with i ∈ Fin(n + 1), the power pairings satisfy
m_(n+1) ∘ (b_i(F) ⊗ b_i(H)) = b_i(F ⊗ H) ∘ m_n.
These are the insertions used by the monad coresolution. -/
theorem smallEtaleGodementPowerTensorPairing_barEtaAtPos (X : Scheme.{u}) (n : ℕ)
    (i : Fin (n + 1)) (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleTensorSheafMap.{u, w} X
        (Monad.barEtaAtPos (smallEtaleGodementMonad.{u, w} X) n i F)
        (Monad.barEtaAtPos (smallEtaleGodementMonad.{u, w} X) n i G) ≫
      smallEtaleGodementPowerTensorPairing.{u, w} X (n + 1) F G =
      smallEtaleGodementPowerTensorPairing.{u, w} X n F G ≫
        Monad.barEtaAtPos (smallEtaleGodementMonad.{u, w} X) n i
          (smallEtaleTensorSheaf.{u, w} X F G) :=
  smallEtaleGodementPowerTensorPairing_etaAtPos.{u, w} X n i.rev F G

set_option backward.isDefEq.respectTransparency.types false in
private theorem pairingCoordinatesSquare.{vC, uC} {C : Type uC} [Category.{vC} C]
    {A B P P' Q Q' : C} (a : A ⟶ B) (t : A ⟶ P) (t' : B ⟶ P')
    (b : P ⟶ P') (m : P ⟶ Q) (m' : P' ⟶ Q')
    {D D' : C} (e : D ≅ Q) (e' : D' ≅ Q') (c : D ⟶ D') (d : Q ⟶ Q')
    (ht : a ≫ t' = t ≫ b) (hm : b ≫ m' = m ≫ d)
    (hc : c ≫ e'.hom = e.hom ≫ d) :
    a ≫ (t' ≫ m' ≫ e'.inv) = (t ≫ m ≫ e.inv) ≫ c := by
  apply (cancel_mono e'.hom).1
  calc
    (a ≫ (t' ≫ m' ≫ e'.inv)) ≫ e'.hom = (a ≫ t') ≫ m' := by
      rw [Category.assoc, Category.assoc, Category.assoc, e'.inv_hom_id, Category.comp_id]
      exact (Category.assoc _ _ _).symm
    _ = (t ≫ b) ≫ m' := congrArg (fun l => l ≫ m') ht
    _ = t ≫ m ≫ d := (Category.assoc _ _ _).trans (congrArg (fun l => t ≫ l) hm)
    _ = ((t ≫ m ≫ e.inv) ≫ c) ≫ e'.hom := by
      symm
      rw [Category.assoc, hc]
      calc
        (t ≫ m ≫ e.inv) ≫ e.hom ≫ d =
            t ≫ m ≫ (e.inv ≫ e.hom) ≫ d := by simp only [Category.assoc]
        _ = t ≫ m ≫ d := by rw [e.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For the cosimplicial coresolution pairing m^C_n and coface δ^i,
i ∈ Fin(n + 2), one has
m^C_(n+1) ∘ (δ_F^i ⊗ δ_H^i) = δ_(F⊗H)^i ∘ m^C_n. -/
theorem smallEtaleGodementCoresolutionTensorPairing_coface (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) (i : Fin (n + 2)) :
    smallEtaleTensorSheafMap.{u, w} X
        ((smallEtaleGodementCoresolution.{u, w} X F).map (SimplexCategory.δ i))
        ((smallEtaleGodementCoresolution.{u, w} X G).map (SimplexCategory.δ i)) ≫
      smallEtaleGodementCoresolutionTensorPairing.{u, w} X F G (n + 1) =
      smallEtaleGodementCoresolutionTensorPairing.{u, w} X F G n ≫
        (smallEtaleGodementCoresolution.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G)).map
          (SimplexCategory.δ i) := by
  let T := smallEtaleGodementMonad.{u, w} X
  let Q := smallEtaleTensorSheaf.{u, w} X F G
  let eF := fun j => Monad.coresolutionObjIso T F j
  let eG := fun j => Monad.coresolutionObjIso T G j
  let eQ := fun j => Monad.coresolutionObjIso T Q j
  let cF := (smallEtaleGodementCoresolution.{u, w} X F).map (SimplexCategory.δ i)
  let cG := (smallEtaleGodementCoresolution.{u, w} X G).map (SimplexCategory.δ i)
  let cQ := (smallEtaleGodementCoresolution.{u, w} X Q).map (SimplexCategory.δ i)
  let bF := Monad.barEtaAtPos T (n + 1) i F
  let bG := Monad.barEtaAtPos T (n + 1) i G
  let bQ := Monad.barEtaAtPos T (n + 1) i Q
  let a := smallEtaleTensorSheafMap.{u, w} X cF cG
  let t j := smallEtaleTensorSheafMap.{u, w} X (eF j).hom (eG j).hom
  let m j := smallEtaleGodementPowerTensorPairing.{u, w} X (j + 1) F G
  have hF : cF ≫ (eF (n + 1)).hom = (eF n).hom ≫ bF :=
    Monad.coresolutionObjIso_coface T F i
  have hG : cG ≫ (eG (n + 1)).hom = (eG n).hom ≫ bG :=
    Monad.coresolutionObjIso_coface T G i
  have hQ : cQ ≫ (eQ (n + 1)).hom = (eQ n).hom ≫ bQ :=
    Monad.coresolutionObjIso_coface T Q i
  have ht : a ≫ t (n + 1) = t n ≫ smallEtaleTensorSheafMap.{u, w} X bF bG := by
    exact (smallEtaleTensorSheafMap_comp.{u, w} X cF (eF (n + 1)).hom cG (eG (n + 1)).hom).trans
      ((congrArg₂ (fun f g => smallEtaleTensorSheafMap.{u, w} X f g) hF hG).trans
        (smallEtaleTensorSheafMap_comp.{u, w} X (eF n).hom bF (eG n).hom bG).symm)
  have hm : smallEtaleTensorSheafMap.{u, w} X bF bG ≫ m (n + 1) = m n ≫ bQ :=
    smallEtaleGodementPowerTensorPairing_barEtaAtPos.{u, w} X (n + 1) i F G
  exact pairingCoordinatesSquare a (t n) (t (n + 1))
    (smallEtaleTensorSheafMap.{u, w} X bF bG) (m n) (m (n + 1))
    (eQ n) (eQ (n + 1)) cQ bQ ht hm hQ

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u and c = max(u, w).
Work with AddCommGrpCat c-valued sheaves on its small étale site.
Let T be the Godement monad and ⊗_sheaf the sheafified integer tensor.
For coefficient sheaf maps f : F → F′ and g : H → H′, the
degree n coresolution pairings satisfy
m_n′ ∘ (Cores(f)_n ⊗ Cores(g)_n) =
Cores(f ⊗_sheaf g)_n ∘ m_n. -/
theorem smallEtaleGodementCoresolutionTensorPairing_naturality (X : Scheme.{u})
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') (n : ℕ) :
    smallEtaleTensorSheafMap.{u, w} X
        (((Monad.coresolutionFunctor (smallEtaleGodementMonad.{u, w} X)).map f).app
            (SimplexCategory.mk n))
        (((Monad.coresolutionFunctor (smallEtaleGodementMonad.{u, w} X)).map g).app
            (SimplexCategory.mk n)) ≫
      smallEtaleGodementCoresolutionTensorPairing.{u, w} X F' G' n =
      smallEtaleGodementCoresolutionTensorPairing.{u, w} X F G n ≫
        ((Monad.coresolutionFunctor (smallEtaleGodementMonad.{u, w} X)).map
          (smallEtaleTensorSheafMap.{u, w} X f g)).app (SimplexCategory.mk n) := by
  let T := smallEtaleGodementMonad.{u, w} X
  let P := Monad.monadPow T (n + 1)
  let eA := Monad.coresolutionObjIso T F n
  let eA' := Monad.coresolutionObjIso T F' n
  let eB := Monad.coresolutionObjIso T G n
  let eB' := Monad.coresolutionObjIso T G' n
  let eD := Monad.coresolutionObjIso T (smallEtaleTensorSheaf.{u, w} X F G) n
  let eD' := Monad.coresolutionObjIso T (smallEtaleTensorSheaf.{u, w} X F' G') n
  let a := ((Monad.coresolutionFunctor T).map f).app (SimplexCategory.mk n)
  let b := ((Monad.coresolutionFunctor T).map g).app (SimplexCategory.mk n)
  let c := ((Monad.coresolutionFunctor T).map (smallEtaleTensorSheafMap.{u, w} X f g)).app
      (SimplexCategory.mk n)
  let s := smallEtaleTensorSheafMap.{u, w} X a b
  let t := smallEtaleTensorSheafMap.{u, w} X eA.hom eB.hom
  let t' := smallEtaleTensorSheafMap.{u, w} X eA'.hom eB'.hom
  let v := smallEtaleTensorSheafMap.{u, w} X (P.map f) (P.map g)
  let m := smallEtaleGodementPowerTensorPairing.{u, w} X (n + 1) F G
  let m' := smallEtaleGodementPowerTensorPairing.{u, w} X (n + 1) F' G'
  let d := P.map (smallEtaleTensorSheafMap.{u, w} X f g)
  have hA : a ≫ eA'.hom = eA.hom ≫ P.map f := Monad.coresolutionObjIso_naturality T f n
  have hB : b ≫ eB'.hom = eB.hom ≫ P.map g := Monad.coresolutionObjIso_naturality T g n
  have hD : c ≫ eD'.hom = eD.hom ≫ d :=
    Monad.coresolutionObjIso_naturality T (smallEtaleTensorSheafMap.{u, w} X f g) n
  have ht : s ≫ t' = t ≫ v :=
    (smallEtaleTensorSheafMap_comp.{u, w} X a eA'.hom b eB'.hom).trans
      ((congrArg₂ (fun f g => smallEtaleTensorSheafMap.{u, w} X f g) hA hB).trans
        (smallEtaleTensorSheafMap_comp.{u, w} X eA.hom (P.map f) eB.hom (P.map g)).symm)
  have hm : v ≫ m' = m ≫ d := smallEtaleGodementPowerTensorPairing_naturality.{u, w} X (n + 1) f g
  exact pairingCoordinatesSquare s t t' v m m' eD eD' c d ht hm hD

end AlgebraicGeometry.Scheme.DerivedSections
