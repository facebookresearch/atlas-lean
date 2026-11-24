/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated
public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncatedQuasicategory
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexCompat

/-! # Binary-product comparison for `SSet.mapFundamentalGroupoid`

For simplicial sets `X` and `A`, the canonical comparison functor

  `prodComparison X A : FundamentalGroupoid (X ⨯ A) ⥤ FundamentalGroupoid X × FundamentalGroupoid A`

is `(mapFundamentalGroupoid prod.fst).prod' (mapFundamentalGroupoid prod.snd)`.
For maps `f : X ⟶ Y` and `g : A ⟶ B` it is natural up to the isomorphism
`prodMapNatIso f g`, built purely from functor-level isos (interchange with
`Iso.refl` components, `mapFundamentalGroupoidComp`, and
`congrMapFundamentalGroupoidOfEq` applied to `Limits.prod.map_fst` /
`Limits.prod.map_snd`); no edge/`homMk` manipulation is needed. Stability of
functor equivalences under products (`Equivalence.prod`) plus cancellation
along the static comparison (`isEquivalence_of_comp_right`) then yields the
public consumer theorem `isEquivalence_mapFundamentalGroupoid_prodMap`, which
has exactly the signature of the `KanComplexWProduct.lean` groupoid seam.

Proved layers in this file:
- `essSurj_prodComparison`, via the Yoneda pairing `Δ[0] ⟶ X ⨯ A`.
- `hc₂ProdComparison`, the `Truncated.HomotopyCategory₂` binary-product
  comparison for quasicategories, built with pinned `desc`, proved functorial
  with pointwise `CompStruct.map` plus `homotopyCategory₂_fac`, compared with
  `functor_ext`, and described on `homMk` with `homMk_eq_iff_homotopicL`.
  It is the quotient-level precursor of the groupoid comparison.
- `full_prodComparison`, fullness of the static groupoid comparison for
  arbitrary simplicial sets, via Yoneda edge pairing (`pairedSimplex1`,
  `pairEdge`) and zigzag induction (`hom_rec`) factored through
  `(fX, 𝟙)` and `(𝟙, fA)`. No homotopy quotient input is needed.
- `faithful_prodComparison`, faithfulness of the static groupoid comparison,
  via the wall-free Option A paired inverse: `invObj`/`invMap`/`invProd`
  built from the commuting left/right inclusions (`leftFunctor`,
  `rightFunctor`, whose commutation is `interchange`), with the left-inverse
  law `hUnit : prodComparison X A ⋙ invProd X A = 𝟭 _` proved by
  `functor_ext` (objects by the vertex pairing `pairEta`, morphisms by
  pairing the projected `homMk`s and refolding with
  `pairEdge_comp_left_then_right` plus the edge `eta`). A functor with a
  left inverse is faithful, so the former `ax_faithful_prodComparison` seam
  is deleted with no replacement.

Assumption inventory: no axiom remains in this file. The comparison
equivalence is fully proved from the Yoneda pairing, the `desc`/`hom_rec`
interfaces, and the `CompStruct` pairing, with all naturality and transport
steps proved. No map-level or `W`-level assumption is introduced.

Explicit nonclaims: no `ModelCategory SSet` instance is used or constructed;
no public or private assumption is added. The product is
never treated as definitional, and the proof never routes through
realization/singular.
-/

@[expose] public section

universe u u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory Simplicial Limits SimplicialObject.Truncated

namespace SSet

/-- Canonical comparison functor from the fundamental groupoid of a binary
product to the product of the fundamental groupoids. -/
private noncomputable def prodComparison (X A : SSet.{u}) :
    FundamentalGroupoid (X ⨯ A) ⥤
      FundamentalGroupoid X × FundamentalGroupoid A :=
  (mapFundamentalGroupoid (Limits.prod.fst : X ⨯ A ⟶ X)).prod'
    (mapFundamentalGroupoid (Limits.prod.snd : X ⨯ A ⟶ A))

/-- The comparison sends `mk v` to the paired vertices. -/
private lemma prodComparison_obj_mk (X A : SSet.{u}) (v : (X ⨯ A) _⦋0⦌) :
    (prodComparison X A).obj (FundamentalGroupoid.mk v) =
      (FundamentalGroupoid.mk ((Limits.prod.fst : X ⨯ A ⟶ X).app _ v),
        FundamentalGroupoid.mk ((Limits.prod.snd : X ⨯ A ⟶ A).app _ v)) := by
  simp only [prodComparison, Functor.prod'_obj, mapFundamentalGroupoid_obj_mk]

/-- First-vertex computation for the Yoneda pairing. -/
private lemma prod_fst_app_yoneda_lift (X A : SSet.{u}) (x : X _⦋0⦌)
    (a : A _⦋0⦌) :
    (Limits.prod.fst : X ⨯ A ⟶ X).app _ (SSet.yonedaEquiv (Limits.prod.lift
      (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm a))) = x := by
  have h := SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv (Limits.prod.lift
    (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm a)))
    (Limits.prod.fst : X ⨯ A ⟶ X)
  rw [Equiv.symm_apply_apply, Limits.prod.lift_fst] at h
  exact (SSet.yonedaEquiv.symm.injective h).symm

/-- Second-vertex computation for the Yoneda pairing. -/
private lemma prod_snd_app_yoneda_lift (X A : SSet.{u}) (x : X _⦋0⦌)
    (a : A _⦋0⦌) :
    (Limits.prod.snd : X ⨯ A ⟶ A).app _ (SSet.yonedaEquiv (Limits.prod.lift
      (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm a))) = a := by
  have h := SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv (Limits.prod.lift
    (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm a)))
    (Limits.prod.snd : X ⨯ A ⟶ A)
  rw [Equiv.symm_apply_apply, Limits.prod.lift_snd] at h
  exact (SSet.yonedaEquiv.symm.injective h).symm

/-- The comparison is essentially surjective, via the Yoneda pairing
`Δ[0] ⟶ X ⨯ A`. -/
private theorem essSurj_prodComparison (X A : SSet.{u}) :
    (prodComparison X A).EssSurj := by
  apply Functor.essSurj_of_surj
  rintro ⟨Y₁, Y₂⟩
  obtain ⟨x, rfl⟩ := FundamentalGroupoid.mk_surjective (X := X) Y₁
  obtain ⟨a, rfl⟩ := FundamentalGroupoid.mk_surjective (X := A) Y₂
  refine ⟨FundamentalGroupoid.mk (SSet.yonedaEquiv (Limits.prod.lift
    (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm a))), ?_⟩
  rw [prodComparison_obj_mk, prod_fst_app_yoneda_lift,
    prod_snd_app_yoneda_lift]

/-- Yoneda pairing of `1`-simplices into the binary product. -/
private noncomputable def pairedSimplex1 {X A : SSet.{u}}
    (sX : X _⦋1⦌) (sA : A _⦋1⦌) : (X ⨯ A) _⦋1⦌ :=
  SSet.yonedaEquiv (Limits.prod.lift
    (SSet.yonedaEquiv.symm sX) (SSet.yonedaEquiv.symm sA))

/-- First projection of the paired `1`-simplex. -/
private lemma pairedSimplex1_fst {X A : SSet.{u}} (sX : X _⦋1⦌) (sA : A _⦋1⦌) :
    (Limits.prod.fst : X ⨯ A ⟶ X).app _ (pairedSimplex1 sX sA) = sX := by
  have h := SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv (Limits.prod.lift
    (SSet.yonedaEquiv.symm sX) (SSet.yonedaEquiv.symm sA)))
    (Limits.prod.fst : X ⨯ A ⟶ X)
  rw [Equiv.symm_apply_apply, Limits.prod.lift_fst] at h
  exact (SSet.yonedaEquiv.symm.injective h).symm

/-- Second projection of the paired `1`-simplex. -/
private lemma pairedSimplex1_snd {X A : SSet.{u}} (sX : X _⦋1⦌) (sA : A _⦋1⦌) :
    (Limits.prod.snd : X ⨯ A ⟶ A).app _ (pairedSimplex1 sX sA) = sA := by
  have h := SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv (Limits.prod.lift
    (SSet.yonedaEquiv.symm sX) (SSet.yonedaEquiv.symm sA)))
    (Limits.prod.snd : X ⨯ A ⟶ A)
  rw [Equiv.symm_apply_apply, Limits.prod.lift_snd] at h
  exact (SSet.yonedaEquiv.symm.injective h).symm

/-- Source face of the paired `1`-simplex is the paired source vertex. -/
private lemma pairEdge_src {X A : SSet.{u}} {x₀ x₁ : X _⦋0⦌} {a₀ a₁ : A _⦋0⦌}
    (eX : SSet.Edge x₀ x₁) (eA : SSet.Edge a₀ a₁) :
    (X ⨯ A).δ 1 (pairedSimplex1 eX.edge eA.edge) =
      SSet.yonedaEquiv (Limits.prod.lift
        (SSet.yonedaEquiv.symm x₀) (SSet.yonedaEquiv.symm a₀)) := by
  have hLift : SSet.yonedaEquiv.symm (pairedSimplex1 eX.edge eA.edge) =
      Limits.prod.lift (SSet.yonedaEquiv.symm eX.edge)
        (SSet.yonedaEquiv.symm eA.edge) :=
    Equiv.symm_apply_apply _ _
  have hVert : SSet.yonedaEquiv.symm (SSet.yonedaEquiv (Limits.prod.lift
      (SSet.yonedaEquiv.symm x₀) (SSet.yonedaEquiv.symm a₀))) =
      Limits.prod.lift (SSet.yonedaEquiv.symm x₀) (SSet.yonedaEquiv.symm a₀) :=
    Equiv.symm_apply_apply _ _
  have hMap : SSet.stdSimplex.δ 1 ≫
      SSet.yonedaEquiv.symm (pairedSimplex1 eX.edge eA.edge) =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (Limits.prod.lift
        (SSet.yonedaEquiv.symm x₀) (SSet.yonedaEquiv.symm a₀))) := by
    rw [hLift, hVert]
    apply Limits.prod.hom_ext
    · rw [Category.assoc, Limits.prod.lift_fst,
        SSet.Edge.δ_one_yonedaEquiv_symm, Limits.prod.lift_fst]
    · rw [Category.assoc, Limits.prod.lift_snd,
        SSet.Edge.δ_one_yonedaEquiv_symm, Limits.prod.lift_snd]
  exact SSet.yonedaEquiv.symm.injective (by
    rw [← SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact hMap)

/-- Target face of the paired `1`-simplex is the paired target vertex. -/
private lemma pairEdge_tgt {X A : SSet.{u}} {x₀ x₁ : X _⦋0⦌} {a₀ a₁ : A _⦋0⦌}
    (eX : SSet.Edge x₀ x₁) (eA : SSet.Edge a₀ a₁) :
    (X ⨯ A).δ 0 (pairedSimplex1 eX.edge eA.edge) =
      SSet.yonedaEquiv (Limits.prod.lift
        (SSet.yonedaEquiv.symm x₁) (SSet.yonedaEquiv.symm a₁)) := by
  have hLift : SSet.yonedaEquiv.symm (pairedSimplex1 eX.edge eA.edge) =
      Limits.prod.lift (SSet.yonedaEquiv.symm eX.edge)
        (SSet.yonedaEquiv.symm eA.edge) :=
    Equiv.symm_apply_apply _ _
  have hVert : SSet.yonedaEquiv.symm (SSet.yonedaEquiv (Limits.prod.lift
      (SSet.yonedaEquiv.symm x₁) (SSet.yonedaEquiv.symm a₁))) =
      Limits.prod.lift (SSet.yonedaEquiv.symm x₁) (SSet.yonedaEquiv.symm a₁) :=
    Equiv.symm_apply_apply _ _
  have hMap : SSet.stdSimplex.δ 0 ≫
      SSet.yonedaEquiv.symm (pairedSimplex1 eX.edge eA.edge) =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (Limits.prod.lift
        (SSet.yonedaEquiv.symm x₁) (SSet.yonedaEquiv.symm a₁))) := by
    rw [hLift, hVert]
    apply Limits.prod.hom_ext
    · rw [Category.assoc, Limits.prod.lift_fst,
        SSet.Edge.δ_zero_yonedaEquiv_symm, Limits.prod.lift_fst]
    · rw [Category.assoc, Limits.prod.lift_snd,
        SSet.Edge.δ_zero_yonedaEquiv_symm, Limits.prod.lift_snd]
  exact SSet.yonedaEquiv.symm.injective (by
    rw [← SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact hMap)

/-- Pointwise pairing of edges into the binary product. -/
private noncomputable def pairEdge {X A : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    {a₀ a₁ : A _⦋0⦌} (eX : SSet.Edge x₀ x₁) (eA : SSet.Edge a₀ a₁) :
    SSet.Edge
      (SSet.yonedaEquiv (Limits.prod.lift
        (SSet.yonedaEquiv.symm x₀) (SSet.yonedaEquiv.symm a₀)))
      (SSet.yonedaEquiv (Limits.prod.lift
        (SSet.yonedaEquiv.symm x₁) (SSet.yonedaEquiv.symm a₁))) :=
  SSet.Edge.mk (pairedSimplex1 eX.edge eA.edge) (pairEdge_src eX eA)
    (pairEdge_tgt eX eA)

/-- The paired edge projects to the first factor edge. -/
private lemma pairEdge_map_fst {X A : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    {a₀ a₁ : A _⦋0⦌} (eX : SSet.Edge x₀ x₁) (eA : SSet.Edge a₀ a₁) :
    ((pairEdge eX eA).map (Limits.prod.fst : X ⨯ A ⟶ X)).ofEq
      (prod_fst_app_yoneda_lift X A x₀ a₀)
      (prod_fst_app_yoneda_lift X A x₁ a₁) = eX := by
  apply SSet.Edge.ext
  change (Limits.prod.fst : X ⨯ A ⟶ X).app _ (pairEdge eX eA).edge = eX.edge
  have hEdge : (pairEdge eX eA).edge = pairedSimplex1 eX.edge eA.edge := rfl
  rw [hEdge, pairedSimplex1_fst]

/-- The paired edge projects to the second factor edge. -/
private lemma pairEdge_map_snd {X A : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    {a₀ a₁ : A _⦋0⦌} (eX : SSet.Edge x₀ x₁) (eA : SSet.Edge a₀ a₁) :
    ((pairEdge eX eA).map (Limits.prod.snd : X ⨯ A ⟶ A)).ofEq
      (prod_snd_app_yoneda_lift X A x₀ a₀)
      (prod_snd_app_yoneda_lift X A x₁ a₁) = eA := by
  apply SSet.Edge.ext
  change (Limits.prod.snd : X ⨯ A ⟶ A).app _ (pairEdge eX eA).edge = eA.edge
  have hEdge : (pairEdge eX eA).edge = pairedSimplex1 eX.edge eA.edge := rfl
  rw [hEdge, pairedSimplex1_snd]

/-- Every product vertex is the Yoneda pairing of its projections. -/
private lemma pairEta {X A : SSet.{u}} (v : (X ⨯ A) _⦋0⦌) :
    v = SSet.yonedaEquiv (Limits.prod.lift
      (SSet.yonedaEquiv.symm ((Limits.prod.fst : X ⨯ A ⟶ X).app _ v))
      (SSet.yonedaEquiv.symm ((Limits.prod.snd : X ⨯ A ⟶ A).app _ v))) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  apply Limits.prod.hom_ext
  · rw [Limits.prod.lift_fst]
    have h := SSet.yonedaEquiv_symm_comp v (Limits.prod.fst : X ⨯ A ⟶ X)
    exact h
  · rw [Limits.prod.lift_snd]
    have h := SSet.yonedaEquiv_symm_comp v (Limits.prod.snd : X ⨯ A ⟶ A)
    exact h

/-- Product `eqToHom` splits as the paired component `eqToHom`s.
Proved by `cases`, so no pinned transparency unfolding is needed. -/
private theorem prod_eqToHom_mkHom {C D : Type*} [Category C] [Category D]
    {p q : C × D} (h : p = q) :
    eqToHom h =
      Prod.mkHom (eqToHom (congrArg Prod.fst h)) (eqToHom (congrArg Prod.snd h)) := by
  cases h
  rfl

/-- Every fundamental-groupoid object is `mk` of its underlying vertex. -/
private lemma mk_pt_eq {X : SSet.{u}} (x : FundamentalGroupoid X) :
    FundamentalGroupoid.mk x.pt = x := rfl

/-- The comparison sends a Yoneda-paired vertex to the paired vertices. -/
private lemma prodComparison_obj_yoneda_pair (X A : SSet.{u}) (x : X _⦋0⦌)
    (a : A _⦋0⦌) :
    (prodComparison X A).obj (FundamentalGroupoid.mk (SSet.yonedaEquiv
      (Limits.prod.lift (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm a)))) =
      (FundamentalGroupoid.mk x, FundamentalGroupoid.mk a) := by
  rw [prodComparison_obj_mk, prod_fst_app_yoneda_lift, prod_snd_app_yoneda_lift]

/-- Paired-vertex computation with a general left object. -/
private lemma prodComparison_obj_yoneda_pair_pt_left (X A : SSet.{u})
    (x : FundamentalGroupoid X) (a : A _⦋0⦌) :
    (prodComparison X A).obj (FundamentalGroupoid.mk (SSet.yonedaEquiv
      (Limits.prod.lift (SSet.yonedaEquiv.symm x.pt) (SSet.yonedaEquiv.symm a)))) =
      (x, FundamentalGroupoid.mk a) :=
  (prodComparison_obj_yoneda_pair X A x.pt a).trans
    (congrArg (fun y => (y, FundamentalGroupoid.mk a)) (mk_pt_eq x))

/-- Paired-vertex computation with a general right object. -/
private lemma prodComparison_obj_yoneda_pair_pt_right (X A : SSet.{u})
    (x : X _⦋0⦌) (a : FundamentalGroupoid A) :
    (prodComparison X A).obj (FundamentalGroupoid.mk (SSet.yonedaEquiv
      (Limits.prod.lift (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm a.pt)))) =
      (FundamentalGroupoid.mk x, a) :=
  (prodComparison_obj_yoneda_pair X A x a.pt).trans
    (congrArg (fun y => (FundamentalGroupoid.mk x, y)) (mk_pt_eq a))

/-- The comparison sends a paired `homMk` to the paired homotopy classes,
up to the endpoint `eqToHom` transports from the Yoneda pairing. -/
private lemma pairHomMk {X A : SSet.{u}} {x₀ x₁ : X _⦋0⦌} {a₀ a₁ : A _⦋0⦌}
    (eX : SSet.Edge x₀ x₁) (eA : SSet.Edge a₀ a₁) :
    (prodComparison X A).map (FundamentalGroupoid.homMk (pairEdge eX eA)) =
      eqToHom (prodComparison_obj_yoneda_pair X A x₀ a₀) ≫
        ((FundamentalGroupoid.homMk eX : FundamentalGroupoid.mk x₀ ⟶
            FundamentalGroupoid.mk x₁),
          (FundamentalGroupoid.homMk eA : FundamentalGroupoid.mk a₀ ⟶
            FundamentalGroupoid.mk a₁)) ≫
        eqToHom (prodComparison_obj_yoneda_pair X A x₁ a₁).symm := by
  have homMk_ofEq : ∀ {X : SSet.{u}} {x₀ x₁ y₀ y₁ : X _⦋0⦌}
      (e : SSet.Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁),
      FundamentalGroupoid.homMk (e.ofEq h₀ h₁) =
        eqToHom (congrArg FundamentalGroupoid.mk h₀).symm ≫
          FundamentalGroupoid.homMk e ≫
          eqToHom (congrArg FundamentalGroupoid.mk h₁) := by
    intro X x₀ x₁ y₀ y₁ e h₀ h₁
    cases h₀
    cases h₁
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    congr 1
  simp only [prodComparison, Functor.prod'_map,
    SSet.mapFundamentalGroupoid_map_homMk]
  have hFst : FundamentalGroupoid.homMk
      ((pairEdge eX eA).map (Limits.prod.fst : X ⨯ A ⟶ X)) =
      eqToHom (congrArg FundamentalGroupoid.mk
        (prod_fst_app_yoneda_lift X A x₀ a₀)) ≫
        FundamentalGroupoid.homMk eX ≫
        eqToHom (congrArg FundamentalGroupoid.mk
          (prod_fst_app_yoneda_lift X A x₁ a₁)).symm := by
    have h := pairEdge_map_fst eX eA
    have hHom := homMk_ofEq ((pairEdge eX eA).map
      (Limits.prod.fst : X ⨯ A ⟶ X))
      (prod_fst_app_yoneda_lift X A x₀ a₀)
      (prod_fst_app_yoneda_lift X A x₁ a₁)
    rw [h] at hHom
    rw [hHom]
    simp
  have hSnd : FundamentalGroupoid.homMk
      ((pairEdge eX eA).map (Limits.prod.snd : X ⨯ A ⟶ A)) =
      eqToHom (congrArg FundamentalGroupoid.mk
        (prod_snd_app_yoneda_lift X A x₀ a₀)) ≫
        FundamentalGroupoid.homMk eA ≫
        eqToHom (congrArg FundamentalGroupoid.mk
          (prod_snd_app_yoneda_lift X A x₁ a₁)).symm := by
    have h := pairEdge_map_snd eX eA
    have hHom := homMk_ofEq ((pairEdge eX eA).map
      (Limits.prod.snd : X ⨯ A ⟶ A))
      (prod_snd_app_yoneda_lift X A x₀ a₀)
      (prod_snd_app_yoneda_lift X A x₁ a₁)
    rw [h] at hHom
    rw [hHom]
    simp
  rw [hFst, hSnd]
  have split0 : (eqToHom (prodComparison_obj_yoneda_pair X A x₀ a₀)).1 =
      eqToHom (congrArg FundamentalGroupoid.mk
        (prod_fst_app_yoneda_lift X A x₀ a₀)) :=
    congrArg Prod.fst (prod_eqToHom_mkHom _)
  have split0' : (eqToHom (prodComparison_obj_yoneda_pair X A x₀ a₀)).2 =
      eqToHom (congrArg FundamentalGroupoid.mk
        (prod_snd_app_yoneda_lift X A x₀ a₀)) :=
    congrArg Prod.snd (prod_eqToHom_mkHom _)
  have split1 : (eqToHom (prodComparison_obj_yoneda_pair X A x₁ a₁).symm).1 =
      eqToHom (congrArg FundamentalGroupoid.mk
        (prod_fst_app_yoneda_lift X A x₁ a₁)).symm :=
    congrArg Prod.fst (prod_eqToHom_mkHom _)
  have split1' : (eqToHom (prodComparison_obj_yoneda_pair X A x₁ a₁).symm).2 =
      eqToHom (congrArg FundamentalGroupoid.mk
        (prod_snd_app_yoneda_lift X A x₁ a₁)).symm :=
    congrArg Prod.snd (prod_eqToHom_mkHom _)
  ext
  · simp only [prod_comp]
    refine congrArg₂ (· ≫ ·) ?_ ?_
    · exact split0.symm
    · refine congrArg₂ (· ≫ ·) ?_ ?_
      · rfl
      · exact split1.symm
  · simp only [prod_comp]
    refine congrArg₂ (· ≫ ·) ?_ ?_
    · exact split0'.symm
    · refine congrArg₂ (· ≫ ·) ?_ ?_
      · rfl
      · exact split1'.symm

/-- Fullness for pairs of the form `(fX, 𝟙)`: zigzag induction on the left,
with the indexed `hom_rec` motive and endpoint `eqToHom` transports. -/
private theorem full_pair_left {X A : SSet.{u}} (a : A _⦋0⦌) :
    ∀ {x₀ x₁ : X _⦋0⦌}
      (fX : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₁),
      ∃ f : FundamentalGroupoid.mk
          (SSet.yonedaEquiv (Limits.prod.lift
            (SSet.yonedaEquiv.symm x₀) (SSet.yonedaEquiv.symm a))) ⟶
          FundamentalGroupoid.mk
          (SSet.yonedaEquiv (Limits.prod.lift
            (SSet.yonedaEquiv.symm x₁) (SSet.yonedaEquiv.symm a))),
        (prodComparison X A).map f =
          eqToHom (prodComparison_obj_yoneda_pair X A x₀ a) ≫
            (fX, 𝟙 (FundamentalGroupoid.mk a)) ≫
            eqToHom (prodComparison_obj_yoneda_pair X A x₁ a).symm := by
  intro x₀ x₁ fX
  have key : ∀ {x y : FundamentalGroupoid X} (f : x ⟶ y),
      ∃ g : FundamentalGroupoid.mk
          (SSet.yonedaEquiv (Limits.prod.lift
            (SSet.yonedaEquiv.symm x.pt) (SSet.yonedaEquiv.symm a))) ⟶
          FundamentalGroupoid.mk
          (SSet.yonedaEquiv (Limits.prod.lift
            (SSet.yonedaEquiv.symm y.pt) (SSet.yonedaEquiv.symm a))),
        (prodComparison X A).map g =
          eqToHom (prodComparison_obj_yoneda_pair_pt_left X A x a) ≫
            (f, 𝟙 (FundamentalGroupoid.mk a)) ≫
            eqToHom (prodComparison_obj_yoneda_pair_pt_left X A y a).symm := by
    intro x y f
    induction f using FundamentalGroupoid.hom_rec with
    | homMk eX =>
      refine ⟨FundamentalGroupoid.homMk (pairEdge eX (SSet.Edge.id a)), ?_⟩
      have hMk := pairHomMk eX (SSet.Edge.id a)
      simp only [FundamentalGroupoid.homMk_id] at hMk
      exact hMk
    | inv fX ih =>
      obtain ⟨f, hf⟩ := ih
      have pair_inv : CategoryTheory.inv
            (Prod.mkHom fX (𝟙 (FundamentalGroupoid.mk a))) =
          Prod.mkHom (CategoryTheory.inv fX)
            (CategoryTheory.inv (𝟙 (FundamentalGroupoid.mk a))) := by
        rw [← Groupoid.inv_eq_inv, ← Groupoid.inv_eq_inv, ← Groupoid.inv_eq_inv]
        rfl
      refine ⟨inv f, ?_⟩
      simp only [Functor.map_inv, hf, IsIso.inv_comp, inv_eqToHom, pair_inv,
        IsIso.inv_id, Category.assoc]
    | comp fX gX ihf ihg =>
      obtain ⟨f, hf⟩ := ihf
      obtain ⟨g, hg⟩ := ihg
      have midCancel : ∀ {P Q : FundamentalGroupoid X × FundamentalGroupoid A}
          (h : P = Q), eqToHom h.symm ≫ eqToHom h = 𝟙 _ := by
        intro P Q h
        subst h
        simp only [eqToHom_refl, Category.id_comp]
      have midCancelC : ∀ {P Q R : FundamentalGroupoid X × FundamentalGroupoid A}
          (h : P = Q) (k : Q ⟶ R),
          (eqToHom h.symm ≫ eqToHom h ≫ k) = k := by
        intro P Q R h k
        subst h
        simp
      refine ⟨f ≫ g, ?_⟩
      simp only [Functor.map_comp, hf, hg, Category.assoc, midCancelC]
      ext
      · simp only [prod_comp, Category.assoc]
      · refine congrArg₂ (· ≫ ·) rfl ?_
        exact Category.id_comp _
  exact key fX

/-- Fullness for pairs of the form `(𝟙, fA)`: zigzag induction on the right,
with the indexed `hom_rec` motive and endpoint `eqToHom` transports. -/
private theorem full_pair_right {X A : SSet.{u}} (x : X _⦋0⦌) :
    ∀ {a₀ a₁ : A _⦋0⦌}
      (fA : FundamentalGroupoid.mk a₀ ⟶ FundamentalGroupoid.mk a₁),
      ∃ f : FundamentalGroupoid.mk
          (SSet.yonedaEquiv (Limits.prod.lift
            (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm a₀))) ⟶
          FundamentalGroupoid.mk
          (SSet.yonedaEquiv (Limits.prod.lift
            (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm a₁))),
        (prodComparison X A).map f =
          eqToHom (prodComparison_obj_yoneda_pair X A x a₀) ≫
            (𝟙 (FundamentalGroupoid.mk x), fA) ≫
            eqToHom (prodComparison_obj_yoneda_pair X A x a₁).symm := by
  intro a₀ a₁ fA
  have key : ∀ {x' y' : FundamentalGroupoid A} (f : x' ⟶ y'),
      ∃ g : FundamentalGroupoid.mk
          (SSet.yonedaEquiv (Limits.prod.lift
            (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm x'.pt))) ⟶
          FundamentalGroupoid.mk
          (SSet.yonedaEquiv (Limits.prod.lift
            (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y'.pt))),
        (prodComparison X A).map g =
          eqToHom (prodComparison_obj_yoneda_pair_pt_right X A x x') ≫
            (𝟙 (FundamentalGroupoid.mk x), f) ≫
            eqToHom (prodComparison_obj_yoneda_pair_pt_right X A x y').symm := by
    intro x' y' f
    induction f using FundamentalGroupoid.hom_rec with
    | homMk eA =>
      refine ⟨FundamentalGroupoid.homMk (pairEdge (SSet.Edge.id x) eA), ?_⟩
      have hMk := pairHomMk (SSet.Edge.id x) eA
      simp only [FundamentalGroupoid.homMk_id] at hMk
      exact hMk
    | inv fA ih =>
      obtain ⟨f, hf⟩ := ih
      have pair_inv : CategoryTheory.inv
            (Prod.mkHom (𝟙 (FundamentalGroupoid.mk x)) fA) =
          Prod.mkHom (CategoryTheory.inv (𝟙 (FundamentalGroupoid.mk x)))
            (CategoryTheory.inv fA) := by
        rw [← Groupoid.inv_eq_inv, ← Groupoid.inv_eq_inv, ← Groupoid.inv_eq_inv]
        rfl
      refine ⟨inv f, ?_⟩
      simp only [Functor.map_inv, hf, IsIso.inv_comp, inv_eqToHom, pair_inv,
        IsIso.inv_id, Category.assoc]
    | comp fA gA ihf ihg =>
      obtain ⟨f, hf⟩ := ihf
      obtain ⟨g, hg⟩ := ihg
      have midCancel : ∀ {P Q : FundamentalGroupoid X × FundamentalGroupoid A}
          (h : P = Q), eqToHom h.symm ≫ eqToHom h = 𝟙 _ := by
        intro P Q h
        subst h
        simp only [eqToHom_refl, Category.id_comp]
      have midCancelC : ∀ {P Q R : FundamentalGroupoid X × FundamentalGroupoid A}
          (h : P = Q) (k : Q ⟶ R),
          (eqToHom h.symm ≫ eqToHom h ≫ k) = k := by
        intro P Q R h k
        subst h
        simp
      refine ⟨f ≫ g, ?_⟩
      simp only [Functor.map_comp, hf, hg, Category.assoc, midCancelC]
      ext
      · refine congrArg₂ (· ≫ ·) rfl ?_
        exact Category.id_comp _
      · simp only [prod_comp, Category.assoc]
  exact key fA

/-- The static comparison is full: factor `(fX, fA)` as `(fX, 𝟙) ≫ (𝟙, fA)`,
with endpoint `eqToHom` transports matching `full_pair_left/right`. -/
private theorem full_prodComparison (X A : SSet.{u}) :
    (prodComparison X A).Full := by
  constructor
  intro a b f
  induction a using FundamentalGroupoid.rec with
  | mk v₁ =>
    induction b using FundamentalGroupoid.rec with
    | mk v₂ =>
      set x₁ := (Limits.prod.fst : X ⨯ A ⟶ X).app _ v₁ with hx₁
      set a₁ := (Limits.prod.snd : X ⨯ A ⟶ A).app _ v₁ with ha₁
      set x₂ := (Limits.prod.fst : X ⨯ A ⟶ X).app _ v₂ with hx₂
      set a₂ := (Limits.prod.snd : X ⨯ A ⟶ A).app _ v₂ with ha₂
      have h₁ : v₁ = SSet.yonedaEquiv (Limits.prod.lift
          (SSet.yonedaEquiv.symm x₁) (SSet.yonedaEquiv.symm a₁)) := by
        have h := pairEta (X := X) (A := A) v₁
        rw [← hx₁, ← ha₁] at h
        exact h
      have h₂ : v₂ = SSet.yonedaEquiv (Limits.prod.lift
          (SSet.yonedaEquiv.symm x₂) (SSet.yonedaEquiv.symm a₂)) := by
        have h := pairEta (X := X) (A := A) v₂
        rw [← hx₂, ← ha₂] at h
        exact h
      clear_value x₁
      clear_value a₁
      clear_value x₂
      clear_value a₂
      subst h₁
      subst h₂
      have hSrc : (prodComparison X A).obj
          (FundamentalGroupoid.mk (SSet.yonedaEquiv (Limits.prod.lift
            (SSet.yonedaEquiv.symm x₁) (SSet.yonedaEquiv.symm a₁)))) =
          (FundamentalGroupoid.mk x₁, FundamentalGroupoid.mk a₁) := by
        simp only [prodComparison_obj_mk, prod_fst_app_yoneda_lift,
          prod_snd_app_yoneda_lift]
      have hTgt : (prodComparison X A).obj
          (FundamentalGroupoid.mk (SSet.yonedaEquiv (Limits.prod.lift
            (SSet.yonedaEquiv.symm x₂) (SSet.yonedaEquiv.symm a₂)))) =
          (FundamentalGroupoid.mk x₂, FundamentalGroupoid.mk a₂) := by
        simp only [prodComparison_obj_mk, prod_fst_app_yoneda_lift,
          prod_snd_app_yoneda_lift]
      set fX : FundamentalGroupoid.mk x₁ ⟶ FundamentalGroupoid.mk x₂ :=
        (eqToHom hSrc.symm ≫ f ≫ eqToHom hTgt).1 with hfXdef
      set fA : FundamentalGroupoid.mk a₁ ⟶ FundamentalGroupoid.mk a₂ :=
        (eqToHom hSrc.symm ≫ f ≫ eqToHom hTgt).2 with hfAdef
      obtain ⟨g₁, hg₁⟩ := full_pair_left a₁ fX
      obtain ⟨g₂, hg₂⟩ := full_pair_right x₂ fA
      have midCancel : ∀ {P Q : FundamentalGroupoid X × FundamentalGroupoid A}
          (h : P = Q), eqToHom h.symm ≫ eqToHom h = 𝟙 _ := by
        intro P Q h
        subst h
        simp only [eqToHom_refl, Category.id_comp]
      have midCancelC : ∀ {P Q R : FundamentalGroupoid X × FundamentalGroupoid A}
          (h : P = Q) (k : Q ⟶ R),
          (eqToHom h.symm ≫ eqToHom h ≫ k) = k := by
        intro P Q R h k
        subst h
        simp
      refine ⟨g₁ ≫ g₂, ?_⟩
      have cancelSrc : eqToHom hSrc ≫ eqToHom hSrc.symm = 𝟙 _ :=
        eqToHom_trans hSrc hSrc.symm |>.trans (eqToHom_refl _ _)
      have cancelTgt : eqToHom hTgt ≫ eqToHom hTgt.symm = 𝟙 _ :=
        eqToHom_trans hTgt hTgt.symm |>.trans (eqToHom_refl _ _)
      have e1 : (eqToHom hSrc.symm ≫ f ≫ eqToHom hTgt).1 = fX := hfXdef.symm
      have e2 : (eqToHom hSrc.symm ≫ f ≫ eqToHom hTgt).2 = fA := hfAdef.symm
      have e : (eqToHom hSrc.symm ≫ f ≫ eqToHom hTgt) = (fX, fA) :=
        Prod.hom_ext e1 e2
      have hf : f = eqToHom hSrc ≫ (fX, fA) ≫ eqToHom hTgt.symm := by
        calc f = 𝟙 _ ≫ f ≫ 𝟙 _ := by simp
          _ = (eqToHom hSrc ≫ eqToHom hSrc.symm) ≫ f ≫
              (eqToHom hTgt ≫ eqToHom hTgt.symm) := by
            rw [← cancelSrc, ← cancelTgt]
          _ = eqToHom hSrc ≫ (eqToHom hSrc.symm ≫ f ≫ eqToHom hTgt) ≫
              eqToHom hTgt.symm := by simp only [Category.assoc]
          _ = eqToHom hSrc ≫ (fX, fA) ≫ eqToHom hTgt.symm := by rw [e]
      simp only [hf, Functor.map_comp, hg₁, hg₂, Category.assoc, midCancelC]
      ext
      · refine congrArg₂ (· ≫ ·) rfl ?_
        refine congrArg₂ (· ≫ ·) rfl ?_
        exact Category.id_comp _
      · refine congrArg₂ (· ≫ ·) rfl ?_
        exact Category.id_comp _

/-- Yoneda pairing of `2`-simplices into the binary product. -/
private noncomputable def pairedSimplex2 {X A : SSet.{u}}
    (sX : X _⦋2⦌) (sA : A _⦋2⦌) : (X ⨯ A) _⦋2⦌ :=
  SSet.yonedaEquiv (Limits.prod.lift
    (SSet.yonedaEquiv.symm sX) (SSet.yonedaEquiv.symm sA))

/-- Second face of the paired `2`-simplex is the paired second face. -/
private lemma pairedSimplex2_δ2 {X A : SSet.{u}} (sX : X _⦋2⦌) (sA : A _⦋2⦌) :
    (X ⨯ A).δ 2 (pairedSimplex2 sX sA) =
      pairedSimplex1 (X.δ 2 sX) (A.δ 2 sA) := by
  have hLift : SSet.yonedaEquiv.symm (pairedSimplex2 sX sA) =
      Limits.prod.lift (SSet.yonedaEquiv.symm sX)
        (SSet.yonedaEquiv.symm sA) :=
    Equiv.symm_apply_apply _ _
  have hVert : SSet.yonedaEquiv.symm
      (pairedSimplex1 (X.δ 2 sX) (A.δ 2 sA)) =
      Limits.prod.lift (SSet.yonedaEquiv.symm (X.δ 2 sX))
        (SSet.yonedaEquiv.symm (A.δ 2 sA)) :=
    Equiv.symm_apply_apply _ _
  have hMap : SSet.stdSimplex.δ 2 ≫
      SSet.yonedaEquiv.symm (pairedSimplex2 sX sA) =
      SSet.yonedaEquiv.symm
        (pairedSimplex1 (X.δ 2 sX) (A.δ 2 sA)) := by
    rw [hLift, hVert]
    apply Limits.prod.hom_ext
    · rw [Category.assoc, Limits.prod.lift_fst,
        SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Limits.prod.lift_fst]
    · rw [Category.assoc, Limits.prod.lift_snd,
        SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Limits.prod.lift_snd]
  exact SSet.yonedaEquiv.symm.injective (by
    rw [← SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact hMap)

/-- Zeroth face of the paired `2`-simplex is the paired zeroth face. -/
private lemma pairedSimplex2_δ0 {X A : SSet.{u}} (sX : X _⦋2⦌) (sA : A _⦋2⦌) :
    (X ⨯ A).δ 0 (pairedSimplex2 sX sA) =
      pairedSimplex1 (X.δ 0 sX) (A.δ 0 sA) := by
  have hLift : SSet.yonedaEquiv.symm (pairedSimplex2 sX sA) =
      Limits.prod.lift (SSet.yonedaEquiv.symm sX)
        (SSet.yonedaEquiv.symm sA) :=
    Equiv.symm_apply_apply _ _
  have hVert : SSet.yonedaEquiv.symm
      (pairedSimplex1 (X.δ 0 sX) (A.δ 0 sA)) =
      Limits.prod.lift (SSet.yonedaEquiv.symm (X.δ 0 sX))
        (SSet.yonedaEquiv.symm (A.δ 0 sA)) :=
    Equiv.symm_apply_apply _ _
  have hMap : SSet.stdSimplex.δ 0 ≫
      SSet.yonedaEquiv.symm (pairedSimplex2 sX sA) =
      SSet.yonedaEquiv.symm
        (pairedSimplex1 (X.δ 0 sX) (A.δ 0 sA)) := by
    rw [hLift, hVert]
    apply Limits.prod.hom_ext
    · rw [Category.assoc, Limits.prod.lift_fst,
        SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Limits.prod.lift_fst]
    · rw [Category.assoc, Limits.prod.lift_snd,
        SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Limits.prod.lift_snd]
  exact SSet.yonedaEquiv.symm.injective (by
    rw [← SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact hMap)

/-- First face of the paired `2`-simplex is the paired first face. -/
private lemma pairedSimplex2_δ1 {X A : SSet.{u}} (sX : X _⦋2⦌) (sA : A _⦋2⦌) :
    (X ⨯ A).δ 1 (pairedSimplex2 sX sA) =
      pairedSimplex1 (X.δ 1 sX) (A.δ 1 sA) := by
  have hLift : SSet.yonedaEquiv.symm (pairedSimplex2 sX sA) =
      Limits.prod.lift (SSet.yonedaEquiv.symm sX)
        (SSet.yonedaEquiv.symm sA) :=
    Equiv.symm_apply_apply _ _
  have hVert : SSet.yonedaEquiv.symm
      (pairedSimplex1 (X.δ 1 sX) (A.δ 1 sA)) =
      Limits.prod.lift (SSet.yonedaEquiv.symm (X.δ 1 sX))
        (SSet.yonedaEquiv.symm (A.δ 1 sA)) :=
    Equiv.symm_apply_apply _ _
  have hMap : SSet.stdSimplex.δ 1 ≫
      SSet.yonedaEquiv.symm (pairedSimplex2 sX sA) =
      SSet.yonedaEquiv.symm
        (pairedSimplex1 (X.δ 1 sX) (A.δ 1 sA)) := by
    rw [hLift, hVert]
    apply Limits.prod.hom_ext
    · rw [Category.assoc, Limits.prod.lift_fst,
        SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Limits.prod.lift_fst]
    · rw [Category.assoc, Limits.prod.lift_snd,
        SSet.stdSimplex.δ_comp_yonedaEquiv_symm, Limits.prod.lift_snd]
  exact SSet.yonedaEquiv.symm.injective (by
    rw [← SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact hMap)

/-- Every product `1`-simplex is the Yoneda pairing of its projections. -/
private lemma pairedSimplex1_eta {X A : SSet.{u}} (s : (X ⨯ A) _⦋1⦌) :
    s = pairedSimplex1 ((Limits.prod.fst : X ⨯ A ⟶ X).app _ s)
      ((Limits.prod.snd : X ⨯ A ⟶ A).app _ s) := by
  have h : s = SSet.yonedaEquiv (Limits.prod.lift
      (SSet.yonedaEquiv.symm ((Limits.prod.fst : X ⨯ A ⟶ X).app _ s))
      (SSet.yonedaEquiv.symm ((Limits.prod.snd : X ⨯ A ⟶ A).app _ s))) := by
    apply SSet.yonedaEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    apply Limits.prod.hom_ext
    · rw [Limits.prod.lift_fst]
      have hh := SSet.yonedaEquiv_symm_comp s
        (Limits.prod.fst : X ⨯ A ⟶ X)
      exact hh
    · rw [Limits.prod.lift_snd]
      have hh := SSet.yonedaEquiv_symm_comp s
        (Limits.prod.snd : X ⨯ A ⟶ A)
      exact hh
  exact h

/-- Pairing of `CompStruct`s into the binary product. -/
private noncomputable def pairCompStruct {X A : SSet.{u}}
    {x₀ x₁ x₂ : X _⦋0⦌} {a₀ a₁ a₂ : A _⦋0⦌}
    {e₀₁ : SSet.Edge x₀ x₁} {e₁₂ : SSet.Edge x₁ x₂} {e₀₂ : SSet.Edge x₀ x₂}
    {f₀₁ : SSet.Edge a₀ a₁} {f₁₂ : SSet.Edge a₁ a₂} {f₀₂ : SSet.Edge a₀ a₂}
    (hX : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (hA : SSet.Edge.CompStruct f₀₁ f₁₂ f₀₂) :
    SSet.Edge.CompStruct (pairEdge e₀₁ f₀₁) (pairEdge e₁₂ f₁₂)
      (pairEdge e₀₂ f₀₂) :=
  SSet.Edge.CompStruct.mk (pairedSimplex2 hX.simplex hA.simplex)
    (by rw [pairedSimplex2_δ2, hX.d₂, hA.d₂]; rfl)
    (by rw [pairedSimplex2_δ0, hX.d₀, hA.d₀]; rfl)
    (by rw [pairedSimplex2_δ1, hX.d₁, hA.d₁]; rfl)

/-- Object part of the left inclusion for a fixed right groupoid object. -/
private noncomputable def leftObj (X A : SSet.{u}) (a : FundamentalGroupoid A)
    (x : X _⦋0⦌) : FundamentalGroupoid (X ⨯ A) :=
  FundamentalGroupoid.mk (SSet.yonedaEquiv (Limits.prod.lift
    (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm a.pt)))

/-- Morphism part of the left inclusion: pairs an `X`-edge with the
identity on `a.pt`. -/
private noncomputable def leftMap (X A : SSet.{u}) (a : FundamentalGroupoid A)
    {x₀ x₁ : X _⦋0⦌} (eX : SSet.Edge x₀ x₁) :
    leftObj X A a x₀ ⟶ leftObj X A a x₁ :=
  FundamentalGroupoid.homMk (pairEdge eX (SSet.Edge.id a.pt))

/-- Left morphism part respects `CompStruct`, by pairing with the
degenerate `idCompId` witness. -/
private lemma leftMap_comp {X A : SSet.{u}} (a : FundamentalGroupoid A)
    {x₀ x₁ x₂ : X _⦋0⦌} {e₀₁ : SSet.Edge x₀ x₁} {e₁₂ : SSet.Edge x₁ x₂}
    {e₀₂ : SSet.Edge x₀ x₂} (hX : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    leftMap X A a e₀₁ ≫ leftMap X A a e₁₂ = leftMap X A a e₀₂ :=
  SSet.Edge.CompStruct.homMk_comp
    (pairCompStruct hX (SSet.Edge.CompStruct.idCompId a.pt))

/-- Left inclusion for a fixed right groupoid object, via `desc`. -/
private noncomputable def leftFunctor (X A : SSet.{u})
    (a : FundamentalGroupoid A) :
    FundamentalGroupoid X ⥤ FundamentalGroupoid (X ⨯ A) :=
  FundamentalGroupoid.desc (leftObj X A a) (leftMap X A a) (leftMap_comp a)

/-- Object part of the right inclusion for a fixed left groupoid object. -/
private noncomputable def rightObj (X A : SSet.{u})
    (x : FundamentalGroupoid X)
    (a : A _⦋0⦌) : FundamentalGroupoid (X ⨯ A) :=
  FundamentalGroupoid.mk (SSet.yonedaEquiv (Limits.prod.lift
    (SSet.yonedaEquiv.symm x.pt) (SSet.yonedaEquiv.symm a)))

/-- Morphism part of the right inclusion: pairs the identity on `x.pt`
with an `A`-edge. -/
private noncomputable def rightMap (X A : SSet.{u})
    (x : FundamentalGroupoid X)
    {a₀ a₁ : A _⦋0⦌} (eA : SSet.Edge a₀ a₁) :
    rightObj X A x a₀ ⟶ rightObj X A x a₁ :=
  FundamentalGroupoid.homMk (pairEdge (SSet.Edge.id x.pt) eA)

/-- Right morphism part respects `CompStruct`, by pairing with the
degenerate `idCompId` witness. -/
private lemma rightMap_comp {X A : SSet.{u}} (x : FundamentalGroupoid X)
    {a₀ a₁ a₂ : A _⦋0⦌} {f₀₁ : SSet.Edge a₀ a₁} {f₁₂ : SSet.Edge a₁ a₂}
    {f₀₂ : SSet.Edge a₀ a₂} (hA : SSet.Edge.CompStruct f₀₁ f₁₂ f₀₂) :
    rightMap X A x f₀₁ ≫ rightMap X A x f₁₂ = rightMap X A x f₀₂ :=
  SSet.Edge.CompStruct.homMk_comp
    (pairCompStruct (SSet.Edge.CompStruct.idCompId x.pt) hA)

/-- Right inclusion for a fixed left groupoid object, via `desc`. -/
private noncomputable def rightFunctor (X A : SSet.{u})
    (x : FundamentalGroupoid X) :
    FundamentalGroupoid A ⥤ FundamentalGroupoid (X ⨯ A) :=
  FundamentalGroupoid.desc (rightObj X A x) (rightMap X A x) (rightMap_comp x)

/-- Left inclusion acts as the paired edge on `homMk`. -/
private lemma leftFunctor_map_homMk {X A : SSet.{u}}
    (a : FundamentalGroupoid A)
    {x₀ x₁ : X _⦋0⦌} (eX : SSet.Edge x₀ x₁) :
    (leftFunctor X A a).map (FundamentalGroupoid.homMk eX) =
      FundamentalGroupoid.homMk (pairEdge eX (SSet.Edge.id a.pt)) :=
  (FundamentalGroupoid.desc_map_homMk (leftObj X A a) (leftMap X A a)
    (leftMap_comp a) eX).trans rfl

/-- Right inclusion acts as the paired edge on `homMk`. -/
private lemma rightFunctor_map_homMk {X A : SSet.{u}}
    (x : FundamentalGroupoid X)
    {a₀ a₁ : A _⦋0⦌} (eA : SSet.Edge a₀ a₁) :
    (rightFunctor X A x).map (FundamentalGroupoid.homMk eA) =
      FundamentalGroupoid.homMk (pairEdge (SSet.Edge.id x.pt) eA) :=
  (FundamentalGroupoid.desc_map_homMk (rightObj X A x) (rightMap X A x)
    (rightMap_comp x) eA).trans rfl

/-- Factoring a paired edge as left-then-right: `(eX, id)` followed by
`(id, eA)` composes to `(eX, eA)` via `compId`/`idComp` pairing. -/
private lemma pairEdge_comp_left_then_right {X A : SSet.{u}}
    {x₀ x₁ : X _⦋0⦌} {a₀ a₁ : A _⦋0⦌}
    (eX : SSet.Edge x₀ x₁) (eA : SSet.Edge a₀ a₁) :
    FundamentalGroupoid.homMk (pairEdge eX (SSet.Edge.id a₀)) ≫
      FundamentalGroupoid.homMk (pairEdge (SSet.Edge.id x₁) eA) =
      FundamentalGroupoid.homMk (pairEdge eX eA) :=
  SSet.Edge.CompStruct.homMk_comp (pairCompStruct
    (SSet.Edge.CompStruct.compId eX) (SSet.Edge.CompStruct.idComp eA))

/-- Factoring a paired edge as right-then-left: `(id, eA)` followed by
`(eX, id)` composes to `(eX, eA)` via `idComp`/`compId` pairing. -/
private lemma pairEdge_comp_right_then_left {X A : SSet.{u}}
    {x₀ x₁ : X _⦋0⦌} {a₀ a₁ : A _⦋0⦌}
    (eX : SSet.Edge x₀ x₁) (eA : SSet.Edge a₀ a₁) :
    FundamentalGroupoid.homMk (pairEdge (SSet.Edge.id x₀) eA) ≫
      FundamentalGroupoid.homMk (pairEdge eX (SSet.Edge.id a₁)) =
      FundamentalGroupoid.homMk (pairEdge eX eA) :=
  SSet.Edge.CompStruct.homMk_comp (pairCompStruct
    (SSet.Edge.CompStruct.idComp eX) (SSet.Edge.CompStruct.compId eA))

/-- Projection of a Yoneda-paired vertex is the original vertex. -/
private lemma pt_mk {X : SSet.{u}} (x : X _⦋0⦌) :
    (FundamentalGroupoid.mk x).pt = x := rfl

/-- Groupoid cancellation: if `a ≫ b = c ≫ d` then `d ≫ b⁻¹ = c⁻¹ ≫ a`.
Stated for a concrete fundamental groupoid so the global `IsIso`
instances fire without local provision. -/
private theorem swap_inv {Z : SSet.{u}} {P Q R S : FundamentalGroupoid Z}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ S} {d : S ⟶ R}
    (h : a ≫ b = c ≫ d) : d ≫ inv b = inv c ≫ a := by
  calc d ≫ inv b
      = inv c ≫ ((c ≫ d) ≫ inv b) := by
        simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    _ = inv c ≫ ((a ≫ b) ≫ inv b) := by
        rw [← h]
    _ = inv c ≫ a := by
        simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Groupoid cancellation dual: if `a ≫ b = c ≫ d` then `a⁻¹ ≫ c = b ≫ d⁻¹`.
Stated for a concrete fundamental groupoid so the global `IsIso`
instances fire without local provision. -/
private theorem swap_inv' {Z : SSet.{u}} {P Q R S : FundamentalGroupoid Z}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ S} {d : S ⟶ R}
    (h : a ≫ b = c ≫ d) : inv a ≫ c = b ≫ inv d := by
  calc inv a ≫ c
      = inv a ≫ ((c ≫ d) ≫ inv d) := by
        simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    _ = inv a ≫ ((a ≫ b) ≫ inv d) := by
        rw [h]
    _ = b ≫ inv d := by
        simp only [Category.assoc, IsIso.inv_hom_id_assoc]

/-- Interchange square for the left/right inclusions: moving an `X`-morphism
past an `A`-morphism gives the same product morphism. Proved by double
`hom_rec`: the edge-edge case is the two factorizations of a paired edge,
and the inverse/composition cases follow from functoriality plus groupoid
cancellation. -/
private theorem interchange {X A : SSet.{u}}
    {x₂ x₃ : FundamentalGroupoid X} {a₁ a₂ : FundamentalGroupoid A}
    (fX : x₂ ⟶ x₃) (fA : a₁ ⟶ a₂) :
    (leftFunctor X A a₁).map fX ≫ (rightFunctor X A x₃).map fA =
      (rightFunctor X A x₂).map fA ≫ (leftFunctor X A a₂).map fX :=
  FundamentalGroupoid.hom_rec
    (motive := fun {x₂ x₃ : FundamentalGroupoid X} (fX : x₂ ⟶ x₃) =>
      ∀ {a₁ a₂ : FundamentalGroupoid A} (fA : a₁ ⟶ a₂),
      (leftFunctor X A a₁).map fX ≫ (rightFunctor X A x₃).map fA =
        (rightFunctor X A x₂).map fA ≫ (leftFunctor X A a₂).map fX)
    (homMk := fun {x₀ x₁ : X _⦋0⦌} (eX : SSet.Edge x₀ x₁) =>
      FundamentalGroupoid.hom_rec
        (motive := fun {a₁ a₂ : FundamentalGroupoid A} (fA : a₁ ⟶ a₂) =>
          (leftFunctor X A a₁).map (FundamentalGroupoid.homMk eX) ≫
            (rightFunctor X A (FundamentalGroupoid.mk x₁)).map fA =
            (rightFunctor X A (FundamentalGroupoid.mk x₀)).map fA ≫
              (leftFunctor X A a₂).map (FundamentalGroupoid.homMk eX))
        (homMk := fun {a₀ b₀ : A _⦋0⦌} (eA : SSet.Edge a₀ b₀) => by
          rw [leftFunctor_map_homMk, rightFunctor_map_homMk,
            rightFunctor_map_homMk, leftFunctor_map_homMk]
          simp only [pt_mk]
          have hL : FundamentalGroupoid.homMk (pairEdge eX (SSet.Edge.id _)) ≫
              FundamentalGroupoid.homMk (pairEdge (SSet.Edge.id _) eA) =
              FundamentalGroupoid.homMk (pairEdge eX eA) :=
            pairEdge_comp_left_then_right eX eA
          have hR : FundamentalGroupoid.homMk (pairEdge (SSet.Edge.id _) eA) ≫
              FundamentalGroupoid.homMk (pairEdge eX (SSet.Edge.id _)) =
              FundamentalGroupoid.homMk (pairEdge eX eA) :=
            pairEdge_comp_right_then_left eX eA
          exact hL.trans hR.symm)
        (inv := fun {a₁ a₂ : FundamentalGroupoid A} (f : a₁ ⟶ a₂) ih => by
          have hR1 : (rightFunctor X A (FundamentalGroupoid.mk x₁)).map (inv f) =
              inv ((rightFunctor X A (FundamentalGroupoid.mk x₁)).map f) := by
            rw [Functor.map_inv]
          have hR2 : (rightFunctor X A (FundamentalGroupoid.mk x₀)).map (inv f) =
              inv ((rightFunctor X A (FundamentalGroupoid.mk x₀)).map f) := by
            rw [Functor.map_inv]
          have hEq := ih
          rw [hR1, hR2]
          exact swap_inv hEq)
        (comp := fun {a₁ a₂ a₃ : FundamentalGroupoid A} (f : a₁ ⟶ a₂)
            (g : a₂ ⟶ a₃) ihf ihg => by
          have hRcomp1 : (rightFunctor X A
              (FundamentalGroupoid.mk x₁)).map (f ≫ g) =
              (rightFunctor X A (FundamentalGroupoid.mk x₁)).map f ≫
                (rightFunctor X A (FundamentalGroupoid.mk x₁)).map g := by
            rw [Functor.map_comp]
          have hRcomp2 : (rightFunctor X A
              (FundamentalGroupoid.mk x₀)).map (f ≫ g) =
              (rightFunctor X A (FundamentalGroupoid.mk x₀)).map f ≫
                (rightFunctor X A (FundamentalGroupoid.mk x₀)).map g := by
            rw [Functor.map_comp]
          rw [hRcomp1, hRcomp2]
          exact ((Category.assoc _ _ _).symm.trans
            ((congrArg
              (· ≫ (rightFunctor X A (FundamentalGroupoid.mk x₁)).map g)
              ihf).trans
              ((Category.assoc _ _ _).trans
                ((congrArg
                  ((rightFunctor X A (FundamentalGroupoid.mk x₀)).map f ≫ ·)
                  ihg).trans
                  (Category.assoc _ _ _).symm))))))
    (inv := fun {x₂ x₃ : FundamentalGroupoid X} (f : x₂ ⟶ x₃) ih =>
      fun {a₁ a₂} (fA : a₁ ⟶ a₂) => by
        have hL1 : (leftFunctor X A a₁).map (inv f) =
            inv ((leftFunctor X A a₁).map f) := by rw [Functor.map_inv]
        have hL2 : (leftFunctor X A a₂).map (inv f) =
            inv ((leftFunctor X A a₂).map f) := by rw [Functor.map_inv]
        rw [hL1, hL2]
        exact swap_inv' (ih fA))
    (comp := fun {x₂ x₃ x₄ : FundamentalGroupoid X} (f : x₂ ⟶ x₃)
        (g : x₃ ⟶ x₄) ihf ihg => fun {a₁ a₂} (fA : a₁ ⟶ a₂) => by
        have hLcomp1 : (leftFunctor X A a₁).map (f ≫ g) =
            (leftFunctor X A a₁).map f ≫
              (leftFunctor X A a₁).map g := by rw [Functor.map_comp]
        have hLcomp2 : (leftFunctor X A a₂).map (f ≫ g) =
            (leftFunctor X A a₂).map f ≫
              (leftFunctor X A a₂).map g := by rw [Functor.map_comp]
        rw [hLcomp1, hLcomp2]
        exact ((Category.assoc _ _ _).trans
          ((congrArg ((leftFunctor X A a₁).map f ≫ ·) (ihg fA)).trans
            (((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ (leftFunctor X A a₂).map g) (ihf fA))).trans
              (Category.assoc _ _ _)))))
    fX fA

/-- Object part of the paired inverse: Yoneda-pair the underlying vertices. -/
private noncomputable def invObj (X A : SSet.{u})
    (p : FundamentalGroupoid X × FundamentalGroupoid A) :
    FundamentalGroupoid (X ⨯ A) :=
  FundamentalGroupoid.mk (SSet.yonedaEquiv (Limits.prod.lift
    (SSet.yonedaEquiv.symm p.1.pt) (SSet.yonedaEquiv.symm p.2.pt)))

/-- Morphism part of the paired inverse: left inclusion of the `X`-component
(indexed by the source right object) followed by right inclusion of the
`A`-component (indexed by the target left object). The indexing makes the
middle objects agree definitionally and reduces `map_comp` to a single middle
interchange. -/
private noncomputable def invMap (X A : SSet.{u})
    {p q : FundamentalGroupoid X × FundamentalGroupoid A} (f : p ⟶ q) :
    invObj X A p ⟶ invObj X A q :=
  (leftFunctor X A p.2).map f.1 ≫ (rightFunctor X A q.1).map f.2

/-- The paired inverse functor, via the commuting left/right inclusions. -/
private noncomputable def invProd (X A : SSet.{u}) :
    FundamentalGroupoid X × FundamentalGroupoid A ⥤
      FundamentalGroupoid (X ⨯ A) where
  obj := invObj X A
  map := invMap X A
  map_id := by
    intro p
    change invMap X A (𝟙 p) = 𝟙 (invObj X A p)
    change (leftFunctor X A p.2).map ((𝟙 p : p ⟶ p)).1 ≫
      (rightFunctor X A p.1).map ((𝟙 p : p ⟶ p)).2 = 𝟙 (invObj X A p)
    rw [show ((𝟙 p : p ⟶ p)).1 = 𝟙 p.1 from rfl,
      show ((𝟙 p : p ⟶ p)).2 = 𝟙 p.2 from rfl]
    exact (congrArg₂ (fun (a b : invObj X A p ⟶ invObj X A p) => a ≫ b)
      (CategoryTheory.Functor.map_id _ _)
      (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _)
  map_comp := by
    intro p q r f g
    have hfst : (f ≫ g).1 = f.1 ≫ g.1 := rfl
    have hsnd : (f ≫ g).2 = f.2 ≫ g.2 := rfl
    have hLc : (leftFunctor X A p.2).map (f.1 ≫ g.1) =
        (leftFunctor X A p.2).map f.1 ≫ (leftFunctor X A p.2).map g.1 :=
      Functor.map_comp (leftFunctor X A p.2) f.1 g.1
    have hRc : (rightFunctor X A r.1).map (f.2 ≫ g.2) =
        (rightFunctor X A r.1).map f.2 ≫ (rightFunctor X A r.1).map g.2 :=
      Functor.map_comp (rightFunctor X A r.1) f.2 g.2
    have hSwap : (rightFunctor X A q.1).map f.2 ≫
        (leftFunctor X A q.2).map g.1 =
        (leftFunctor X A p.2).map g.1 ≫ (rightFunctor X A r.1).map f.2 :=
      (interchange g.1 f.2).symm
    change (leftFunctor X A p.2).map (f ≫ g).1 ≫
        (rightFunctor X A r.1).map (f ≫ g).2 =
        ((leftFunctor X A p.2).map f.1 ≫ (rightFunctor X A q.1).map f.2) ≫
          ((leftFunctor X A q.2).map g.1 ≫ (rightFunctor X A r.1).map g.2)
    rw [hfst, hsnd, hLc, hRc]
    exact ((Category.assoc _ _ _).trans
      ((congrArg ((leftFunctor X A p.2).map f.1 ≫ ·)
        (((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ (rightFunctor X A r.1).map g.2) hSwap)).trans
          (Category.assoc _ _ _))).trans
        (Category.assoc _ _ _).symm)).symm

/-- The paired inverse is a left inverse of the comparison, by `functor_ext`:
objects by the vertex pairing `pairEta`, morphisms by pairing the projected
`homMk`s and refolding with `pairEdge_comp_left_then_right` plus the edge
`eta`. This is the exact content replacing the faithfulness seam: a functor
with a left inverse is faithful. -/
private theorem hUnit (X A : SSet.{u}) :
    prodComparison X A ⋙ invProd X A = 𝟭 _ := by
  refine FundamentalGroupoid.functor_ext (fun v => ?_) (fun {x y} e => ?_)
  · change (invProd X A).obj ((prodComparison X A).obj
      (FundamentalGroupoid.mk v)) = FundamentalGroupoid.mk v
    rw [prodComparison_obj_mk]
    exact (congrArg FundamentalGroupoid.mk (pairEta v)).symm
  · have hmap : (prodComparison X A).map (FundamentalGroupoid.homMk e) =
        Prod.mkHom
          (FundamentalGroupoid.homMk
            (e.map (Limits.prod.fst : X ⨯ A ⟶ X)) :
            FundamentalGroupoid.mk
              ((Limits.prod.fst : X ⨯ A ⟶ X).app _ x) ⟶
              FundamentalGroupoid.mk
              ((Limits.prod.fst : X ⨯ A ⟶ X).app _ y))
          (FundamentalGroupoid.homMk
            (e.map (Limits.prod.snd : X ⨯ A ⟶ A)) :
            FundamentalGroupoid.mk
              ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x) ⟶
              FundamentalGroupoid.mk
              ((Limits.prod.snd : X ⨯ A ⟶ A).app _ y)) := by
      simp only [prodComparison, Functor.prod'_map,
        SSet.mapFundamentalGroupoid_map_homMk]
    have hInv : invMap X A ((prodComparison X A).map
          (FundamentalGroupoid.homMk e)) =
        FundamentalGroupoid.homMk (pairEdge
          (e.map (Limits.prod.fst : X ⨯ A ⟶ X))
          (e.map (Limits.prod.snd : X ⨯ A ⟶ A))) := by
      rw [hmap]
      change (leftFunctor X A (FundamentalGroupoid.mk
          ((Limits.prod.snd : X ⨯ A ⟶ A).app _ x))).map
          (FundamentalGroupoid.homMk
            (e.map (Limits.prod.fst : X ⨯ A ⟶ X))) ≫
        (rightFunctor X A (FundamentalGroupoid.mk
          ((Limits.prod.fst : X ⨯ A ⟶ X).app _ y))).map
          (FundamentalGroupoid.homMk
            (e.map (Limits.prod.snd : X ⨯ A ⟶ A))) = _
      rw [leftFunctor_map_homMk, rightFunctor_map_homMk]
      exact pairEdge_comp_left_then_right _ _
    have homMk_ofEq : ∀ {x₀ x₁ y₀ y₁ : (X ⨯ A) _⦋0⦌}
        (e' : SSet.Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁),
        FundamentalGroupoid.homMk (e'.ofEq h₀ h₁) =
          eqToHom (congrArg FundamentalGroupoid.mk h₀).symm ≫
            FundamentalGroupoid.homMk e' ≫
            eqToHom (congrArg FundamentalGroupoid.mk h₁) := by
      intro _ _ _ _ e' h₀ h₁
      cases h₀
      cases h₁
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      congr 1
    have hEdge : pairEdge (e.map (Limits.prod.fst : X ⨯ A ⟶ X))
          (e.map (Limits.prod.snd : X ⨯ A ⟶ A)) =
        e.ofEq (pairEta x) (pairEta y) := by
      apply SSet.Edge.ext
      change (pairEdge (e.map (Limits.prod.fst : X ⨯ A ⟶ X))
        (e.map (Limits.prod.snd : X ⨯ A ⟶ A))).edge = e.edge
      have hE : (pairEdge (e.map (Limits.prod.fst : X ⨯ A ⟶ X))
          (e.map (Limits.prod.snd : X ⨯ A ⟶ A))).edge =
          pairedSimplex1 (e.map (Limits.prod.fst : X ⨯ A ⟶ X)).edge
            (e.map (Limits.prod.snd : X ⨯ A ⟶ A)).edge := rfl
      rw [hE, SSet.Edge.map_edge, SSet.Edge.map_edge]
      exact (pairedSimplex1_eta e.edge).symm
    have hLHS : (prodComparison X A ⋙ invProd X A).map
          (FundamentalGroupoid.homMk e) =
        eqToHom (congrArg FundamentalGroupoid.mk (pairEta x)).symm ≫
          FundamentalGroupoid.homMk e ≫
          eqToHom (congrArg FundamentalGroupoid.mk (pairEta y)) := by
      rw [show (prodComparison X A ⋙ invProd X A).map
          (FundamentalGroupoid.homMk e) =
          invMap X A ((prodComparison X A).map
            (FundamentalGroupoid.homMk e)) from rfl,
        hInv, hEdge, homMk_ofEq]
    exact hLHS

/-- `HomotopyCategory₂` binary-product comparison for quasicategories, via
pinned `desc` with pointwise projections. The quotient-level precursor of
`prodComparison`, retained for its independent interface value now that the
groupoid comparison is proved directly. -/
private noncomputable def hc₂ProdComparison (X A : SSet.{u})
    [Quasicategory X] [Quasicategory A] [Quasicategory (X ⨯ A)] :
    Truncated.HomotopyCategory₂ ((truncation 2).obj (X ⨯ A)) ⥤
      Truncated.HomotopyCategory₂ ((truncation 2).obj X) ×
        Truncated.HomotopyCategory₂ ((truncation 2).obj A) :=
  Truncated.HomotopyCategory₂.desc
    (fun v =>
      (Truncated.HomotopyCategory₂.mk
        (((truncation 2).map (Limits.prod.fst : X ⨯ A ⟶ X)).app _ v),
        Truncated.HomotopyCategory₂.mk
        (((truncation 2).map (Limits.prod.snd : X ⨯ A ⟶ A)).app _ v)))
    (fun e =>
      (Truncated.HomotopyCategory₂.homMk
        (e.map ((truncation 2).map (Limits.prod.fst : X ⨯ A ⟶ X))),
        Truncated.HomotopyCategory₂.homMk
        (e.map ((truncation 2).map (Limits.prod.snd : X ⨯ A ⟶ A)))))
    (by intro x; ext <;> simp only [Truncated.Edge.map_id] <;>
      exact Truncated.HomotopyCategory₂.homMk_id _)
    (by
      intro x₀ x₁ x₂ e₀₁ e₁₂ e₀₂ h
      ext
      · simpa using
          (h.map ((truncation 2).map (Limits.prod.fst : X ⨯ A ⟶ X))).homotopyCategory₂_fac
      · simpa using
          (h.map ((truncation 2).map (Limits.prod.snd : X ⨯ A ⟶ A))).homotopyCategory₂_fac)

/-- The `HomotopyCategory₂` comparison sends `homMk` to the paired classes. -/
private lemma hc₂ProdComparison_map_homMk (X A : SSet.{u})
    [Quasicategory X] [Quasicategory A] [Quasicategory (X ⨯ A)]
    {x y : ((truncation 2).obj (X ⨯ A)) _⦋0⦌₂}
    (e : Truncated.Edge x y) :
    (hc₂ProdComparison X A).map (Truncated.HomotopyCategory₂.homMk e) =
      (Truncated.HomotopyCategory₂.homMk
        (e.map ((truncation 2).map (Limits.prod.fst : X ⨯ A ⟶ X))),
        Truncated.HomotopyCategory₂.homMk
        (e.map ((truncation 2).map (Limits.prod.snd : X ⨯ A ⟶ A)))) := by
  simp only [hc₂ProdComparison, Truncated.HomotopyCategory₂.desc,
    Truncated.HomotopyCategory₂.descMap_homMk]

/-- Naturality of the `HomotopyCategory₂` comparison via `functor_ext`. -/
private lemma hc₂ProdComparison_functor_ext (X A : SSet.{u})
    [Quasicategory X] [Quasicategory A] [Quasicategory (X ⨯ A)]
    {F G : Truncated.HomotopyCategory₂ ((truncation 2).obj (X ⨯ A)) ⥤
      Truncated.HomotopyCategory₂ ((truncation 2).obj X) ×
        Truncated.HomotopyCategory₂ ((truncation 2).obj A)}
    (hObj : ∀ v, F.obj (Truncated.HomotopyCategory₂.mk v) =
      G.obj (Truncated.HomotopyCategory₂.mk v))
    (hMap : ∀ {x y} (e : Truncated.Edge x y),
      F.map (Truncated.HomotopyCategory₂.homMk e) =
        eqToHom (hObj x) ≫ G.map (Truncated.HomotopyCategory₂.homMk e) ≫
          eqToHom (hObj y).symm) :
    F = G :=
  Truncated.HomotopyCategory₂.functor_ext hObj hMap

/-- Equality of paired `homMk`s reduces to pointwise `HomotopicL` via
`homMk_eq_iff_homotopicL`. The quotient interface for the `HomotopyCategory₂`
comparison. -/
private lemma hc₂ProdComparison_homMk_eq (X A : SSet.{u})
    [Quasicategory X] [Quasicategory A]
    {x y : ((truncation 2).obj (X ⨯ A)) _⦋0⦌₂}
    {e e' : Truncated.Edge x y} :
    (Truncated.HomotopyCategory₂.homMk
        (e.map ((truncation 2).map (Limits.prod.fst : X ⨯ A ⟶ X))) =
      Truncated.HomotopyCategory₂.homMk
        (e'.map ((truncation 2).map (Limits.prod.fst : X ⨯ A ⟶ X)))) ∧
    (Truncated.HomotopyCategory₂.homMk
        (e.map ((truncation 2).map (Limits.prod.snd : X ⨯ A ⟶ A))) =
      Truncated.HomotopyCategory₂.homMk
        (e'.map ((truncation 2).map (Limits.prod.snd : X ⨯ A ⟶ A)))) ↔
    (Truncated.HomotopicL
      (e.map ((truncation 2).map (Limits.prod.fst : X ⨯ A ⟶ X)))
      (e'.map ((truncation 2).map (Limits.prod.fst : X ⨯ A ⟶ X)))) ∧
    (Truncated.HomotopicL
      (e.map ((truncation 2).map (Limits.prod.snd : X ⨯ A ⟶ A)))
      (e'.map ((truncation 2).map (Limits.prod.snd : X ⨯ A ⟶ A)))) := by
  simp only [Truncated.HomotopyCategory₂.homMk_eq_iff_homotopicL]

/-- Congruence of `Functor.prod'` for natural isomorphisms. (The library only
provides `NatIso.prod` for `.prod`.) -/
private def natIsoProd' {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₂} B] {C : Type u₃} [Category.{v₃} C] {F G : A ⥤ B}
    {H K : A ⥤ C} (e₁ : F ≅ G) (e₂ : H ≅ K) : F.prod' H ≅ G.prod' K where
  hom := NatTrans.prod' e₁.hom e₂.hom
  inv := NatTrans.prod' e₁.inv e₂.inv

/-- Interchange, left side: pushing the product functor inside the `prod'`
is definitionally the same functor. -/
private noncomputable def isoF {X Y A B : SSet.{u}} (f : X ⟶ Y) (g : A ⟶ B) :
    prodComparison X A ⋙
        (mapFundamentalGroupoid f).prod (mapFundamentalGroupoid g) ≅
      (mapFundamentalGroupoid (Limits.prod.fst : X ⨯ A ⟶ X) ⋙
        mapFundamentalGroupoid f).prod'
        (mapFundamentalGroupoid (Limits.prod.snd : X ⨯ A ⟶ A) ⋙
          mapFundamentalGroupoid g) :=
  eqToIso rfl

/-- Interchange, right side: pulling the comparison out of the post-composed
`prod'` is definitionally the same functor. -/
private noncomputable def isoG {X Y A B : SSet.{u}} (f : X ⟶ Y) (g : A ⟶ B) :
    (mapFundamentalGroupoid (Limits.prod.map f g) ⋙
      mapFundamentalGroupoid (Limits.prod.fst : Y ⨯ B ⟶ Y)).prod'
      (mapFundamentalGroupoid (Limits.prod.map f g) ⋙
        mapFundamentalGroupoid (Limits.prod.snd : Y ⨯ B ⟶ B)) ≅
      mapFundamentalGroupoid (Limits.prod.map f g) ⋙ prodComparison Y B :=
  eqToIso rfl

/-- Naturality of the comparison for `Limits.prod.map f g`, as an isomorphism
of functors. Built entirely from functor-level isos, so no `homMk`/edge
coherence proof is needed. -/
private noncomputable def prodMapNatIso {X Y A B : SSet.{u}} (f : X ⟶ Y) (g : A ⟶ B) :
    prodComparison X A ⋙
        (mapFundamentalGroupoid f).prod (mapFundamentalGroupoid g) ≅
      mapFundamentalGroupoid (Limits.prod.map f g) ⋙ prodComparison Y B :=
  isoF f g ≪≫
    natIsoProd' (mapFundamentalGroupoidComp _ _) (mapFundamentalGroupoidComp _ _) ≪≫
    natIsoProd'
      (congrMapFundamentalGroupoidOfEq (Limits.prod.map_fst f g).symm)
      (congrMapFundamentalGroupoidOfEq (Limits.prod.map_snd f g).symm) ≪≫
    natIsoProd' (mapFundamentalGroupoidComp _ _).symm
      (mapFundamentalGroupoidComp _ _).symm ≪≫
    isoG f g

/-- Faithfulness of the comparison, from the left inverse `hUnit`: a functor
with a left inverse is faithful. This deletes the former
`ax_faithful_prodComparison` seam with no replacement. -/
private theorem faithful_prodComparison (X A : SSet.{u}) :
    (prodComparison X A).Faithful where
  map_injective := by
    intro p q f g h
    have h2 := congrArg (invProd X A).map h
    rw [← Functor.comp_map, ← Functor.comp_map] at h2
    have hF : (prodComparison X A ⋙ invProd X A).Faithful :=
      (Eq.symm (hUnit X A)) ▸ inferInstance
    exact hF.map_injective h2

/-- The proved fullness, faithfulness, and essential surjectivity give the
comparison equivalence consumed by the public theorem. No axiom remains. -/
private instance isEquivalence_prodComparison (X A : SSet.{u}) :
    (prodComparison X A).IsEquivalence :=
  { faithful := faithful_prodComparison X A
    full := full_prodComparison X A
    essSurj := essSurj_prodComparison X A }

/-- The mapped fundamental groupoid sends a product of maps to an equivalence
when both factors do. This is the minimum public statement deleting the
`KanComplexWProduct.lean` groupoid seam: its caller `W.prodMap` applies it to
the two factor equivalences. -/
theorem isEquivalence_mapFundamentalGroupoid_prodMap {X Y A B : SSet.{u}}
    {f : X ⟶ Y} {g : A ⟶ B}
    (hF : (mapFundamentalGroupoid f).IsEquivalence)
    (hG : (mapFundamentalGroupoid g).IsEquivalence) :
    (mapFundamentalGroupoid
      (CategoryTheory.Limits.prod.map f g)).IsEquivalence := by
  have := hF
  have := hG
  have hProd : ((mapFundamentalGroupoid f).prod
      (mapFundamentalGroupoid g)).IsEquivalence :=
    (Equivalence.prod (Functor.asEquivalence (mapFundamentalGroupoid f))
      (Functor.asEquivalence (mapFundamentalGroupoid g))).isEquivalence_functor
  have hComp : (prodComparison X A ⋙
      (mapFundamentalGroupoid f).prod (mapFundamentalGroupoid g)).IsEquivalence :=
    inferInstance
  have hComp' : (mapFundamentalGroupoid (CategoryTheory.Limits.prod.map f g) ⋙
      prodComparison Y B).IsEquivalence :=
    Functor.isEquivalence_of_iso (prodMapNatIso f g)
  exact Functor.isEquivalence_of_comp_right
    (mapFundamentalGroupoid (CategoryTheory.Limits.prod.map f g))
    (prodComparison Y B)

end SSet
