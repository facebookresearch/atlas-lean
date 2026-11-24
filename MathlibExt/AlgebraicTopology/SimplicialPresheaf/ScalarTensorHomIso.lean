/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarTensorEndLifting
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Scalar tensor/end comparison on the original presheaf category -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalClosed

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D]

/-- The original pointwise associator, with no size premise on the site. -/
def scalarTensorAssociator (K : SSet.{u}) (A : SimplicialPresheaf.{u} D) :
    scalarTensor.obj ((scalarTensor.obj A).obj K) ≅ tensorLeft K ⋙ scalarTensor.obj A :=
  NatIso.ofComponents
    (fun R => Functor.isoWhiskerLeft A (tensorRightTensor K R).symm)
    (by
      intro R S f
      apply NatTrans.ext
      funext d
      change (A.obj d ⊗ K) ◁ f ≫ (α_ (A.obj d) K S).hom =
        (α_ (A.obj d) K R).hom ≫ (A.obj d ◁ (K ◁ f))
      exact associator_naturality_right (A.obj d) K f)

/-- The original site component is the forward associator in the given factor order. -/
theorem scalarTensorAssociator_hom_app (K R : SSet.{u})
    (A : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    ((scalarTensorAssociator K A).hom.app R).app d = (α_ (A.obj d) K R).hom := rfl

/-- The original inverse component is the same inverse associator. -/
theorem scalarTensorAssociator_inv_app (K R : SSet.{u})
    (A : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    ((scalarTensorAssociator K A).inv.app R).app d = (α_ (A.obj d) K R).inv := rfl

/-- Scalar maps retain the original associator hom, without a braid. -/
theorem scalarTensorAssociator_scalar {K L : SSet.{u}} (k : K ⟶ L)
    (A : SimplicialPresheaf.{u} D) (R : SSet.{u}) :
    (scalarTensor.map ((scalarTensor.obj A).map k)).app R ≫
        (scalarTensorAssociator L A).hom.app R =
      (scalarTensorAssociator K A).hom.app R ≫ (scalarTensor.obj A).map (k ▷ R) := by
  apply NatTrans.ext
  funext d
  change ((A.obj d ◁ k) ▷ R) ≫ (α_ (A.obj d) L R).hom =
    (α_ (A.obj d) K R).hom ≫ (A.obj d ◁ (k ▷ R))
  exact associator_naturality_middle (A.obj d) k R

/-- Scalar maps also retain the whole inverse associator square. -/
theorem scalarTensorAssociator_scalar_inv {K L : SSet.{u}} (k : K ⟶ L)
    (A : SimplicialPresheaf.{u} D) (R : SSet.{u}) :
    (scalarTensorAssociator K A).inv.app R ≫
        (scalarTensor.map ((scalarTensor.obj A).map k)).app R =
      (scalarTensor.obj A).map (k ▷ R) ≫ (scalarTensorAssociator L A).inv.app R := by
  apply NatTrans.ext
  funext d
  change (α_ (A.obj d) K R).inv ≫ ((A.obj d ◁ k) ▷ R) =
    (A.obj d ◁ (k ▷ R)) ≫ (α_ (A.obj d) L R).inv
  exact (associator_inv_naturality_middle (A.obj d) k R).symm

/-- Every original source map retains the forward pointwise associator. -/
theorem scalarTensorAssociator_source (K : SSet.{u})
    {A A' : SimplicialPresheaf.{u} D} (a : A' ⟶ A) (R : SSet.{u}) :
    (scalarTensor.map ((scalarTensor.map a).app K)).app R ≫
        (scalarTensorAssociator K A).hom.app R =
      (scalarTensorAssociator K A').hom.app R ≫ (scalarTensor.map a).app (K ⊗ R) := by
  apply NatTrans.ext
  funext d
  change ((a.app d ▷ K) ▷ R) ≫ (α_ (A.obj d) K R).hom =
    (α_ (A'.obj d) K R).hom ≫ (a.app d ▷ (K ⊗ R))
  exact associator_naturality_left (a.app d) K R

/-- Every original source map retains the inverse pointwise associator. -/
theorem scalarTensorAssociator_source_inv (K : SSet.{u})
    {A A' : SimplicialPresheaf.{u} D} (a : A' ⟶ A) (R : SSet.{u}) :
    (scalarTensorAssociator K A').inv.app R ≫
        (scalarTensor.map ((scalarTensor.map a).app K)).app R =
      (scalarTensor.map a).app (K ⊗ R) ≫ (scalarTensorAssociator K A).inv.app R := by
  apply NatTrans.ext
  funext d
  change (α_ (A'.obj d) K R).inv ≫ ((a.app d ▷ K) ▷ R) =
    (a.app d ▷ (K ⊗ R)) ≫ (α_ (A.obj d) K R).inv
  exact (associator_inv_naturality_left (a.app d) K R).symm

variable [Small.{u} D] [LocallySmall.{u} D]

-- The type annotations below unfold only the actual public functor descriptions.
-- This preserves their original objects/maps without changing provider attributes.

/-- Native uniqueness compares the two actual scalar tensor/end right adjoints. -/
def scalarTensorHomIso (K : SSet.{u}) (A : SimplicialPresheaf.{u} D) :
    dsimp% only [innerHomFunctor, CategoryTheory.eHomFunctor, scalarEnrichment,
        Enriched.FunctorCategory.enrichedOrdinaryCategory, Functor.comp]
      (innerHomFunctor.obj (op ((scalarTensor.obj A).obj K)) ≅
        innerHomFunctor.obj (op A) ⋙ ihom K) :=
  ((scalarTensorHomAdjunction₂ (D := D)).adj ((scalarTensor.obj A).obj K)).rightAdjointUniq
    (((ihom.adjunction K).comp ((scalarTensorHomAdjunction₂ (D := D)).adj A)).ofNatIsoLeft
      (scalarTensorAssociator K A).symm)

/-- The comparison is the whole original scalar transposition through the inverse associator. -/
theorem scalarTensorHomIso_characteristic (K : SSet.{u})
    (A Z : SimplicialPresheaf.{u} D) (R : SSet.{u})
    (b : R ⟶ innerHom ((scalarTensor.obj A).obj K) Z) :
    b ≫ (scalarTensorHomIso K A).hom.app Z =
      curry (scalarTensorHomEquiv A (K ⊗ R) Z
        ((scalarTensorAssociator K A).inv.app R ≫
          (scalarTensorHomEquiv ((scalarTensor.obj A).obj K) R Z).symm b)) := by
  let adj0 : dsimp% only [innerHomFunctor, CategoryTheory.eHomFunctor, scalarEnrichment,
      Enriched.FunctorCategory.enrichedOrdinaryCategory, Functor.comp]
      (scalarTensor.obj ((scalarTensor.obj A).obj K) ⊣
        innerHomFunctor.obj (op ((scalarTensor.obj A).obj K))) :=
    (scalarTensorHomAdjunction₂ (D := D)).adj ((scalarTensor.obj A).obj K)
  let adj1 : dsimp% only [innerHomFunctor, CategoryTheory.eHomFunctor, scalarEnrichment,
      Enriched.FunctorCategory.enrichedOrdinaryCategory, Functor.comp]
      (tensorLeft K ⋙ scalarTensor.obj A ⊣ innerHomFunctor.obj (op A) ⋙ ihom K) :=
    (ihom.adjunction K).comp ((scalarTensorHomAdjunction₂ (D := D)).adj A)
  let adj := adj1.ofNatIsoLeft (scalarTensorAssociator K A).symm
  have h : adj.homEquiv R Z ((adj0.homEquiv R Z).symm b) =
      b ≫ (adj0.rightAdjointUniq adj).hom.app Z := by
    apply (adj.homEquiv R Z).symm.injective
    rw [Equiv.symm_apply_apply, adj.homEquiv_naturality_left_symm]
    exact (adj0.homEquiv_counit R Z b).trans
      (congrArg (fun f => (scalarTensor.obj ((scalarTensor.obj A).obj K)).map b ≫ f)
        (Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adj0 adj Z)).symm
  have hh := h.symm
  change b ≫ (scalarTensorHomIso K A).hom.app Z =
    (adj1.ofNatIsoLeft (scalarTensorAssociator K A).symm).homEquiv R Z
      ((adj0.homEquiv R Z).symm b) at hh
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply] at hh
  have hc : adj1.homEquiv = fun X Y =>
      Equiv.trans (scalarTensorHomEquiv A ((tensorLeft K).obj X) Y)
        ((ihom.adjunction K).homEquiv X (innerHom A Y)) := by
    have hc0 := dsimp% only [innerHomFunctor, CategoryTheory.eHomFunctor, scalarEnrichment,
        Enriched.FunctorCategory.enrichedOrdinaryCategory, Functor.comp,
        scalarTensorHomAdjunction₂_adj]
      (Adjunction.comp_homEquiv (adj₁ := ihom.adjunction K)
        (adj₂ := (scalarTensorHomAdjunction₂ (D := D)).adj A))
    have he := dsimp% only [innerHomFunctor, CategoryTheory.eHomFunctor, scalarEnrichment,
        Enriched.FunctorCategory.enrichedOrdinaryCategory, Functor.comp]
      (scalarTensorHomAdjunction_homEquiv A)
    rw [scalarTensorHomAdjunction₂_adj, he] at hc0
    convert hc0 using 1 <;> rfl
  rw [hc] at hh
  have h0 : adj0.homEquiv = scalarTensorHomEquiv ((scalarTensor.obj A).obj K) := by
    exact dsimp% only [adj0, innerHomFunctor, CategoryTheory.eHomFunctor, scalarEnrichment,
        Enriched.FunctorCategory.enrichedOrdinaryCategory, Functor.comp,
        scalarTensorHomAdjunction₂_adj]
      (scalarTensorHomAdjunction_homEquiv ((scalarTensor.obj A).obj K))
  rw [h0] at hh
  exact hh

/-- The genuine inverse preserves the forward associator and both original transpositions. -/
theorem scalarTensorHomIso_inverse_characteristic (K : SSet.{u})
    (A Z : SimplicialPresheaf.{u} D) (R : SSet.{u})
    (c : R ⟶ (ihom K).obj (innerHom A Z)) :
    c ≫ (scalarTensorHomIso K A).inv.app Z =
      scalarTensorHomEquiv ((scalarTensor.obj A).obj K) R Z
        ((scalarTensorAssociator K A).hom.app R ≫
          (scalarTensorHomEquiv A (K ⊗ R) Z).symm (uncurry c)) := by
  let b := scalarTensorHomEquiv ((scalarTensor.obj A).obj K) R Z
    ((scalarTensorAssociator K A).hom.app R ≫
      (scalarTensorHomEquiv A (K ⊗ R) Z).symm (uncurry c))
  have hb := scalarTensorHomIso_characteristic K A Z R b
  simp only [b, Equiv.symm_apply_apply, Iso.inv_hom_id_app_assoc,
    Equiv.apply_symm_apply, curry_uncurry] at hb
  apply (cancel_mono ((scalarTensorHomIso K A).hom.app Z)).mp
  rw [Category.assoc]
  exact ((congrArg (fun f => c ≫ f) ((scalarTensorHomIso K A).app Z).inv_hom_id).trans
    (Category.comp_id c)).trans hb.symm

/-- The forward characteristic retains every actual original end projection. -/
theorem scalarTensorHomIso_end_π (K : SSet.{u})
    (A Z : SimplicialPresheaf.{u} D) (R : SSet.{u})
    (b : R ⟶ innerHom ((scalarTensor.obj A).obj K) Z) (d : Dᵒᵖ) :
    uncurry (b ≫ (scalarTensorHomIso K A).hom.app Z) ≫ innerHomπ A Z d =
      curry ((α_ (A.obj d) K R).inv ≫
        ((scalarTensorHomEquiv ((scalarTensor.obj A).obj K) R Z).symm b).app d) := by
  rw [scalarTensorHomIso_characteristic, uncurry_curry, scalarTensorHomEquiv_π]
  rfl

/-- The inverse characteristic also retains its original end projection and factor order. -/
theorem scalarTensorHomIso_inv_end_π (K : SSet.{u})
    (A Z : SimplicialPresheaf.{u} D) (R : SSet.{u})
    (c : R ⟶ (ihom K).obj (innerHom A Z)) (d : Dᵒᵖ) :
    uncurry (c ≫ (scalarTensorHomIso K A).inv.app Z ≫
        innerHomπ ((scalarTensor.obj A).obj K) Z d) =
      (α_ (A.obj d) K R).hom ≫
        ((scalarTensorHomEquiv A (K ⊗ R) Z).symm (uncurry c)).app d := by
  rw [← Category.assoc, scalarTensorHomIso_inverse_characteristic, scalarTensorHomEquiv_π]
  change uncurry (curry ((α_ (A.obj d) K R).hom ≫
    ((scalarTensorHomEquiv A (K ⊗ R) Z).symm (uncurry c)).app d)) = _
  exact uncurry_curry _

/-- Native isomorphism naturality keeps the original target transformation. -/
theorem scalarTensorHomIso_naturality_target (K : SSet.{u})
    (A : SimplicialPresheaf.{u} D) {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') :
    innerHomPost ((scalarTensor.obj A).obj K) g ≫ (scalarTensorHomIso K A).hom.app Z' =
      (scalarTensorHomIso K A).hom.app Z ≫ (ihom K).map (innerHomPost A g) :=
  (scalarTensorHomIso K A).hom.naturality g

/-- The whole inverse retains that same original target transformation. -/
theorem scalarTensorHomIso_inv_naturality_target (K : SSet.{u})
    (A : SimplicialPresheaf.{u} D) {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') :
    (ihom K).map (innerHomPost A g) ≫ (scalarTensorHomIso K A).inv.app Z' =
      (scalarTensorHomIso K A).inv.app Z ≫ innerHomPost ((scalarTensor.obj A).obj K) g :=
  (scalarTensorHomIso K A).inv.naturality g


/-- Scalar precomposition retains the whole original tensor/end comparison. -/
theorem scalarTensorHomIso_naturality_scalar {K L : SSet.{u}} (k : K ⟶ L)
    (A Z : SimplicialPresheaf.{u} D) :
    innerHomPre ((scalarTensor.obj A).map k) Z ≫ (scalarTensorHomIso K A).hom.app Z =
      (scalarTensorHomIso L A).hom.app Z ≫ (pre k).app (innerHom A Z) := by
  suffices h : ∀ (R : SSet.{u}) (b : R ⟶ innerHom ((scalarTensor.obj A).obj L) Z),
      b ≫ innerHomPre ((scalarTensor.obj A).map k) Z ≫
          (scalarTensorHomIso K A).hom.app Z =
        b ≫ (scalarTensorHomIso L A).hom.app Z ≫ (pre k).app (innerHom A Z) by
    simpa only [Category.id_comp] using h _ (𝟙 _)
  intro R b
  let f := (scalarTensorHomEquiv ((scalarTensor.obj A).obj L) R Z).symm b
  have hc := scalarTensorAssociator_scalar_inv k A R
  have hn : scalarTensorHomEquiv A (K ⊗ R) Z
      ((scalarTensor.obj A).map (k ▷ R) ≫ (scalarTensorAssociator L A).inv.app R ≫ f) =
      (k ▷ R) ≫ scalarTensorHomEquiv A (L ⊗ R) Z
        ((scalarTensorAssociator L A).inv.app R ≫ f) := by
    rw [← scalarTensorHomAdjunction_homEquiv]
    exact (scalarTensorHomAdjunction A).homEquiv_naturality_left (k ▷ R) _
  calc
    _ = curry (scalarTensorHomEquiv A (K ⊗ R) Z
        ((scalarTensorAssociator K A).inv.app R ≫
          (scalarTensor.map ((scalarTensor.obj A).map k)).app R ≫ f)) := by
      have hb := scalarTensorHomEquiv_source_symm ((scalarTensor.obj A).map k) R Z b
      have hh := scalarTensorHomIso_characteristic K A Z R
        (b ≫ innerHomPre ((scalarTensor.obj A).map k) Z)
      rw [hb] at hh
      simpa only [Category.assoc] using hh
    _ = curry (scalarTensorHomEquiv A (K ⊗ R) Z
        ((scalarTensor.obj A).map (k ▷ R) ≫ (scalarTensorAssociator L A).inv.app R ≫ f)) := by
      apply congrArg (fun q => curry (scalarTensorHomEquiv A (K ⊗ R) Z q))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ f) hc).trans (Category.assoc _ _ _))
    _ = curry ((k ▷ R) ≫ scalarTensorHomEquiv A (L ⊗ R) Z
        ((scalarTensorAssociator L A).inv.app R ≫ f)) := congrArg curry hn
    _ = curry (scalarTensorHomEquiv A (L ⊗ R) Z
        ((scalarTensorAssociator L A).inv.app R ≫ f)) ≫ (pre k).app (innerHom A Z) :=
      (curry_pre_app k _).symm
    _ = _ := congrArg (fun q => q ≫ (pre k).app (innerHom A Z))
      (scalarTensorHomIso_characteristic L A Z R b).symm

/-- Original source precomposition retains the whole original comparison. -/
theorem scalarTensorHomIso_naturality_source (K : SSet.{u})
    {A A' : SimplicialPresheaf.{u} D} (a : A' ⟶ A) (Z : SimplicialPresheaf.{u} D) :
    innerHomPre ((scalarTensor.map a).app K) Z ≫ (scalarTensorHomIso K A').hom.app Z =
      (scalarTensorHomIso K A).hom.app Z ≫ (ihom K).map (innerHomPre a Z) := by
  suffices h : ∀ (R : SSet.{u}) (b : R ⟶ innerHom ((scalarTensor.obj A).obj K) Z),
      b ≫ innerHomPre ((scalarTensor.map a).app K) Z ≫
          (scalarTensorHomIso K A').hom.app Z =
        b ≫ (scalarTensorHomIso K A).hom.app Z ≫ (ihom K).map (innerHomPre a Z) by
    simpa only [Category.id_comp] using h _ (𝟙 _)
  intro R b
  let f := (scalarTensorHomEquiv ((scalarTensor.obj A).obj K) R Z).symm b
  have hc := scalarTensorAssociator_source_inv K a R
  calc
    _ = curry (scalarTensorHomEquiv A' (K ⊗ R) Z
        ((scalarTensorAssociator K A').inv.app R ≫
          (scalarTensor.map ((scalarTensor.map a).app K)).app R ≫ f)) := by
      have hb := scalarTensorHomEquiv_source_symm ((scalarTensor.map a).app K) R Z b
      have hh := scalarTensorHomIso_characteristic K A' Z R
        (b ≫ innerHomPre ((scalarTensor.map a).app K) Z)
      rw [hb] at hh
      simpa only [Category.assoc] using hh
    _ = curry (scalarTensorHomEquiv A' (K ⊗ R) Z
        ((scalarTensor.map a).app (K ⊗ R) ≫ (scalarTensorAssociator K A).inv.app R ≫ f)) := by
      apply congrArg (fun q => curry (scalarTensorHomEquiv A' (K ⊗ R) Z q))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ f) hc).trans (Category.assoc _ _ _))
    _ = curry (scalarTensorHomEquiv A (K ⊗ R) Z
        ((scalarTensorAssociator K A).inv.app R ≫ f) ≫ innerHomPre a Z) :=
      congrArg curry (scalarTensorHomEquiv_source a (K ⊗ R) Z _)
    _ = curry (scalarTensorHomEquiv A (K ⊗ R) Z
        ((scalarTensorAssociator K A).inv.app R ≫ f)) ≫ (ihom K).map (innerHomPre a Z) :=
      curry_natural_right _ _
    _ = _ := congrArg (fun q => q ≫ (ihom K).map (innerHomPre a Z))
      (scalarTensorHomIso_characteristic K A Z R b).symm

private theorem inverseSquare {X X' Y Y' : SSet.{u}}
    (e : X ≅ Y) (e' : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  apply (cancel_mono e'.hom).mp
  rw [Category.assoc, e'.inv_hom_id, Category.comp_id,
    Category.assoc, h, e.inv_hom_id_assoc]

/-- The inverse scalar square preserves that same original precomposition. -/
theorem scalarTensorHomIso_inv_naturality_scalar {K L : SSet.{u}} (k : K ⟶ L)
    (A Z : SimplicialPresheaf.{u} D) :
    (pre k).app (innerHom A Z) ≫ (scalarTensorHomIso K A).inv.app Z =
      (scalarTensorHomIso L A).inv.app Z ≫ innerHomPre ((scalarTensor.obj A).map k) Z := by
  exact inverseSquare ((scalarTensorHomIso L A).app Z) ((scalarTensorHomIso K A).app Z)
    (innerHomPre ((scalarTensor.obj A).map k) Z) ((pre k).app (innerHom A Z))
    (scalarTensorHomIso_naturality_scalar k A Z)

/-- The inverse source square retains the same original source arrow. -/
theorem scalarTensorHomIso_inv_naturality_source (K : SSet.{u})
    {A A' : SimplicialPresheaf.{u} D} (a : A' ⟶ A) (Z : SimplicialPresheaf.{u} D) :
    (ihom K).map (innerHomPre a Z) ≫ (scalarTensorHomIso K A').inv.app Z =
      (scalarTensorHomIso K A).inv.app Z ≫ innerHomPre ((scalarTensor.map a).app K) Z := by
  exact inverseSquare ((scalarTensorHomIso K A).app Z) ((scalarTensorHomIso K A').app Z)
    (innerHomPre ((scalarTensor.map a).app K) Z) ((ihom K).map (innerHomPre a Z))
    (scalarTensorHomIso_naturality_source K a Z)

end SimplicialPresheaf
