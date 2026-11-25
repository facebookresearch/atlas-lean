/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightSphereNaturality
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorHom

/-!
# Actual operator action generators from a genuine right sphere transformation

A genuine continuous I-space and its genuine sphere transformation determine
coefficients and the entire original operator Hom generator family. The source
block braiding, all sphere objects and all continuous Hom actions are retained.
These are functions on existing enriched data, before the canonical RightModule
supplies the unit/associativity proofs and the full reverse operator functor.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator.Reconstruction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [BraidedCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S X : EnrichedFunctor V I V)

attribute [local instance] Enriched.prodCategory

variable (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
  (X.externalTensor S) (d.tensorEnrichedFunctor.comp V X))

/-- The actual ordinary component of the genuine supplied sphere transformation. -/
def sphereComponent (n a : I) : X.obj n ⊗ S.obj a ⟶ X.obj (n ⊗ a) :=
  (eHomEquiv V).symm (t.app (n, a))

/-- The left-oriented original coefficient uses the actual source block inverse. -/
def coefficient (n a : I) : X.obj n ⊗ S.obj a ⟶ X.obj (a ⊗ n) :=
  sphereComponent d S X t n a ≫ X.toOrdinaryFunctor.map (β_ a n).inv

/-- The entire original operator generator retains continuous Hom and sphere values. -/
def generator (n k a : I) : X.obj n ⊗ (((a ⊗ n) ⟶[V] k) ⊗ S.obj a) ⟶ X.obj k :=
  (X.obj n ◁ (β_ ((a ⊗ n) ⟶[V] k) (S.obj a)).hom) ≫
    (α_ (X.obj n) (S.obj a) ((a ⊗ n) ⟶[V] k)).inv ≫
    (coefficient d S X t n a ▷ ((a ⊗ n) ⟶[V] k)) ≫
    MonoidalClosed.uncurry (X.map (a ⊗ n) k)

omit [BraidedCategory I] in
/-- Both original input arrows act naturally on each entire sphere component. -/
theorem sphereComponent_twoInputs (n m a b : I) (f : n ⟶ m) (u : a ⟶ b) :
    (X.toOrdinaryFunctor.map f ⊗ₘ S.toOrdinaryFunctor.map u) ≫
        sphereComponent d S X t m b =
      sphereComponent d S X t n a ≫ X.toOrdinaryFunctor.map (f ⊗ₘ u) := by
  let E := X.externalTensor S
  let J := d.tensorEnrichedFunctor.comp V X
  let Y := E.obj (n, a)
  let Z := J.obj (n, a)
  let H : V := (n, a) ⟶[V] (m, b)
  let p := (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V u)
  let r := X.toOrdinaryFunctor.map f ⊗ₘ S.toOrdinaryFunctor.map u
  let s := X.toOrdinaryFunctor.map (f ⊗ₘ u)
  let c := sphereComponent d S X t n a
  let c' := sphereComponent d S X t m b
  let h := MonoidalClosed.uncurry (E.map (n, a) (m, b))
  let j := MonoidalClosed.uncurry (J.map (n, a) (m, b))
  let pre := (ρ_ Y).inv ≫ Y ◁ p
  have hNature : h ≫ c' = (c ⊗ₘ 𝟙 H) ≫ j :=
    GradedNatTrans.uncurriedNaturality t (n, a) (m, b)
  have hE : p ≫ E.map (n, a) (m, b) = eHomEquiv V r :=
    externalTensor_pairPoint X S f u
  have hJ : p ≫ J.map (n, a) (m, b) = eHomEquiv V s :=
    tensorComp_pairPoint d X f u
  have hPointE : (Y ◁ p) ≫ h = (ρ_ Y).hom ≫ r :=
    uncurry_unitPoint p (E.map (n, a) (m, b)) r hE
  have hPointJ : (Z ◁ p) ≫ j = (ρ_ Z).hom ≫ s :=
    uncurry_unitPoint p (J.map (n, a) (m, b)) s hJ
  have hTensor : (Y ◁ p) ≫ (c ⊗ₘ 𝟙 H) = c ⊗ₘ p :=
    (congrArg (fun q => (Y ◁ p) ≫ q) (tensorHom_id c H)).trans
      (tensorHom_def' c p).symm
  have hPre : pre ≫ (c ⊗ₘ 𝟙 H) = c ≫ (ρ_ Z).inv ≫ Z ◁ p :=
    (Category.assoc (ρ_ Y).inv (Y ◁ p) (c ⊗ₘ 𝟙 H)).trans
      ((congrArg (fun q => (ρ_ Y).inv ≫ q) hTensor).trans
        (rightUnitor_inv_comp_tensorHom c p))
  have hLeftPoint : pre ≫ h = r :=
    (Category.assoc (ρ_ Y).inv (Y ◁ p) h).trans
      ((congrArg (fun q => (ρ_ Y).inv ≫ q) hPointE).trans
        (Iso.inv_hom_id_assoc (ρ_ Y) r))
  have hRightPoint : ((ρ_ Z).inv ≫ Z ◁ p) ≫ j = s :=
    (Category.assoc (ρ_ Z).inv (Z ◁ p) j).trans
      ((congrArg (fun q => (ρ_ Z).inv ≫ q) hPointJ).trans
        (Iso.inv_hom_id_assoc (ρ_ Z) s))
  have hLeft : pre ≫ (h ≫ c') = r ≫ c' :=
    (Category.assoc pre h c').symm.trans (congrArg (fun q => q ≫ c') hLeftPoint)
  have hRight : pre ≫ ((c ⊗ₘ 𝟙 H) ≫ j) = c ≫ s :=
    (Category.assoc pre (c ⊗ₘ 𝟙 H) j).symm.trans
      ((congrArg (fun q => q ≫ j) hPre).trans
        ((Category.assoc c ((ρ_ Z).inv ≫ Z ◁ p) j).trans
          (congrArg (fun q => c ≫ q) hRightPoint)))
  exact hLeft.symm.trans ((congrArg (fun q => pre ≫ q) hNature).trans hRight)

/-- The whole left-oriented coefficient is natural on the entire original sphere object. -/
theorem coefficient_natural (n a b : I) (u : a ⟶ b) :
    (X.obj n ◁ S.toOrdinaryFunctor.map u) ≫ coefficient d S X t n b =
      coefficient d S X t n a ≫ X.toOrdinaryFunctor.map (u ⊗ₘ 𝟙 n) := by
  have hId : X.toOrdinaryFunctor.map (𝟙 n) = 𝟙 (X.obj n) := Functor.map_id _ n
  have hTensorId : X.toOrdinaryFunctor.map (𝟙 n) ⊗ₘ S.toOrdinaryFunctor.map u =
      X.obj n ◁ S.toOrdinaryFunctor.map u :=
    (congrArg (fun q => q ⊗ₘ S.toOrdinaryFunctor.map u) hId).trans
      (id_tensorHom (X.obj n) (S.toOrdinaryFunctor.map u))
  have hSphere : (X.obj n ◁ S.toOrdinaryFunctor.map u) ≫ sphereComponent d S X t n b =
      sphereComponent d S X t n a ≫ X.toOrdinaryFunctor.map (𝟙 n ⊗ₘ u) :=
    (congrArg (fun q => q ≫ sphereComponent d S X t n b) hTensorId).symm.trans
      (sphereComponent_twoInputs d S X t n n a b (𝟙 n) u)
  have hIndex : (𝟙 n ⊗ₘ u) ≫ (β_ b n).inv = (β_ a n).inv ≫ (u ⊗ₘ 𝟙 n) := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] using
      (congrArg (fun q => (β_ a n).inv ≫ q ≫ (β_ b n).inv)
        (braiding_naturality u (𝟙 n))).symm
  have hMap : X.toOrdinaryFunctor.map (𝟙 n ⊗ₘ u) ≫
      X.toOrdinaryFunctor.map (β_ b n).inv =
    X.toOrdinaryFunctor.map (β_ a n).inv ≫ X.toOrdinaryFunctor.map (u ⊗ₘ 𝟙 n) :=
    (X.toOrdinaryFunctor.map_comp (𝟙 n ⊗ₘ u) (β_ b n).inv).symm.trans
      ((congrArg X.toOrdinaryFunctor.map hIndex).trans
        (X.toOrdinaryFunctor.map_comp (β_ a n).inv (u ⊗ₘ 𝟙 n)))
  have hAction : (X.obj n ◁ S.toOrdinaryFunctor.map u) ≫ coefficient d S X t n b =
      (sphereComponent d S X t n a ≫ X.toOrdinaryFunctor.map (β_ a n).inv) ≫
        X.toOrdinaryFunctor.map (u ⊗ₘ 𝟙 n) :=
    (Category.assoc (X.obj n ◁ S.toOrdinaryFunctor.map u) (sphereComponent d S X t n b)
      (X.toOrdinaryFunctor.map (β_ b n).inv)).symm.trans
        ((congrArg (fun q => q ≫ X.toOrdinaryFunctor.map (β_ b n).inv) hSphere).trans
          ((Category.assoc (sphereComponent d S X t n a)
            (X.toOrdinaryFunctor.map (𝟙 n ⊗ₘ u))
            (X.toOrdinaryFunctor.map (β_ b n).inv)).trans
              ((congrArg (fun q => sphereComponent d S X t n a ≫ q) hMap).trans
                (Category.assoc (sphereComponent d S X t n a)
                  (X.toOrdinaryFunctor.map (β_ a n).inv)
                  (X.toOrdinaryFunctor.map (u ⊗ₘ 𝟙 n))).symm)))
  exact hAction

end CategoryTheory.Enriched.SphereOperator.Reconstruction
