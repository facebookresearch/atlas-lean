/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Category.TopCat.ULift
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath

/-!
# Actual realization and a change of carrier universe

The two realization functors preserve colimits and agree on the actual
standard simplices. Density of the existing lifted Yoneda embedding gives
their natural Iso. Its point law follows from naturality of the original
constant simplex map and uniqueness of the realized zero simplex.
No space model, homology comparison, or inverse witness is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w z

namespace SSet

private def liftedStandardSimplexIso :
    stdSimplex.{u} ⋙ uliftFunctor.{v, u} ≅ stdSimplex.{max u v} :=
  NatIso.ofComponents (fun n =>
    NatIso.ofComponents (fun D =>
      Equiv.toIso
        { toFun := fun x => ULift.up x.down.down
          invFun := fun x => ULift.up (ULift.up x.down)
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl })
      (by intro D E f; ext x; rfl))
    (by intro n m f; ext D x; rfl)

private def liftedTopSimplexIso :
    SimplexCategory.toTop.{u} ⋙ TopCat.uliftFunctor.{v, u} ≅
      SimplexCategory.toTop.{max u v} :=
  NatIso.ofComponents (fun n =>
    TopCat.isoOfHomeo
      ((Homeomorph.ulift : ULift.{v} (ULift.{u}
          (Convexity.StdSimplex ℝ (Fin (n.len + 1)))) ≃ₜ _).trans
        (Homeomorph.ulift.trans Homeomorph.ulift.symm)))
    (by intro n m f; apply TopCat.hom_ext; apply ContinuousMap.ext; intro x; rfl)

private theorem preservingFunctor_isLeftKanExtension
    {E : Type w} [Category.{z} E] (L : SSet.{u} ⥤ E)
    [PreservesColimitsOfSize.{0, u} L] :
    L.IsLeftKanExtension (𝟙 (stdSimplex.{u} ⋙ L)) := by
  let Y := stdSimplex.{u}
  let : Y.IsDense := by
    change (CategoryTheory.uliftYoneda.{u} (C := SimplexCategory)).IsDense
    infer_instance
  let : (𝟭 SSet.{u}).IsLeftKanExtension (Functor.rightUnitor Y).inv :=
    inferInstance
  let : L.PreservesLeftKanExtension Y Y := inferInstance
  let α : Y ⋙ L ⟶ Y ⋙ (𝟭 SSet.{u} ⋙ L) :=
    Functor.whiskerRight (Functor.rightUnitor Y).inv L ≫
      (Functor.associator Y (𝟭 SSet.{u}) L).hom
  let : (𝟭 SSet.{u} ⋙ L).IsLeftKanExtension α :=
    Functor.PreservesLeftKanExtension.preserves
      (G := L) (F := Y) (L := Y) (𝟭 SSet.{u}) (Functor.rightUnitor Y).inv
  exact Functor.isLeftKanExtension_of_iso (Functor.leftUnitor L) α (𝟙 _)
    (by ext n; simp [α])

private theorem originalSSetULift_preservesColimits :
    PreservesColimitsOfSize.{0, u} uliftFunctor.{v, u} := by
  change PreservesColimitsOfSize.{0, u}
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (Type (max u v))).obj
      CategoryTheory.uliftFunctor.{v, u})
  infer_instance

/-- Realizing the ORIGINAL lifted simplices is naturally isomorphic to
lifting the ORIGINAL realization. Both directions are actual continuous
maps on the same carrier values, in independent universes. -/
public def toTopULiftIso :
    uliftFunctor.{v, u} ⋙ toTop.{max u v} ≅
      toTop.{u} ⋙ TopCat.uliftFunctor.{v, u} := by
  let F := uliftFunctor.{v, u} ⋙ toTop.{max u v}
  let G := toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}
  letI : PreservesColimitsOfSize.{0, u} uliftFunctor.{v, u} :=
    originalSSetULift_preservesColimits
  letI : PreservesColimitsOfSize.{0, u} F := by
    dsimp only [F]
    infer_instance
  letI : PreservesColimitsOfSize.{0, u} G := by
    dsimp only [G]
    infer_instance
  let eF : stdSimplex.{u} ⋙ F ≅ SimplexCategory.toTop.{max u v} :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight liftedStandardSimplexIso toTop.{max u v} ≪≫
      toTopSimplex.{max u v}
  let eG : stdSimplex.{u} ⋙ G ≅ SimplexCategory.toTop.{max u v} :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight toTopSimplex.{u} (TopCat.uliftFunctor.{v, u}) ≪≫
      liftedTopSimplexIso
  letI : F.IsLeftKanExtension (𝟙 (stdSimplex.{u} ⋙ F)) :=
    preservingFunctor_isLeftKanExtension F
  letI : G.IsLeftKanExtension (𝟙 (stdSimplex.{u} ⋙ G)) :=
    preservingFunctor_isLeftKanExtension G
  exact Functor.leftKanExtensionUniqueOfIso F (𝟙 _) (eF ≪≫ eG.symm) G (𝟙 _)

/-- The actual universe-change Iso sends EVERY original lifted vertex to
the same original realized vertex, with only `ULift.up` on its carrier. -/
public theorem toTopULiftIso_hom_realizedVertex (X : SSet.{u}) (x : X _⦋0⦌) :
    (toTopULiftIso.{u, v}.hom.app X)
        (realizedVertex (X := uliftFunctor.{v, u}.obj X) (ULift.up x)) =
      (ULift.up (realizedVertex (X := X) x) :
        TopCat.uliftFunctor.{v, u}.obj (toTop.obj X)) := by
  let Z : SSet.{u} := Δ[0]
  let z : Z _⦋0⦌ := stdSimplex.objEquiv.{u}.symm (𝟙 ⦋0⦌)
  let g : Z ⟶ X := SSet.const x
  have hPoint : g.app (op ⦋0⦌) z = x := by
    change X.map ((⦋0⦌.const ⦋0⦌ 0).op) x = x
    have hId : (⦋0⦌.const ⦋0⦌ 0).op = 𝟙 (op ⦋0⦌) := Subsingleton.elim _ _
    rw [hId, X.map_id]
    rfl
  let a := realizedVertex (X := uliftFunctor.{v, u}.obj Z) (ULift.up z)
  let b := toTopULiftIso.{u, v}.hom.app Z a
  have hNat := ConcreteCategory.congr_hom (toTopULiftIso.{u, v}.hom.naturality g) a
  have hFa : toTop.map (uliftFunctor.{v, u}.map g) a =
      realizedVertex (X := uliftFunctor.{v, u}.obj X) (ULift.up x) :=
    (realizedVertex_naturality (X := uliftFunctor.{v, u}.obj Z)
      (Y := uliftFunctor.{v, u}.obj X) (uliftFunctor.{v, u}.map g) (ULift.up z)).symm.trans
      (congrArg (fun q => realizedVertex (X := uliftFunctor.{v, u}.obj X) q)
        (congrArg ULift.up hPoint))
  let : Subsingleton (toTop.obj Z) :=
    (TopCat.homeoOfIso (toTopSimplex.{u}.app ⦋0⦌)).injective.subsingleton
  have hGb : TopCat.uliftFunctor.{v, u}.map (toTop.map g) b =
      (ULift.up (realizedVertex (X := X) x) :
        TopCat.uliftFunctor.{v, u}.obj (toTop.obj X)) := by
    change ULift.up (toTop.map g b.down) = _
    have hOriginal : toTop.map g (realizedVertex (X := Z) z) =
        realizedVertex (X := X) x :=
      (realizedVertex_naturality (X := Z) (Y := X) g z).symm.trans
        (congrArg (fun q => realizedVertex (X := X) q) hPoint)
    exact (congrArg (fun y => ULift.up (toTop.map g y))
      (Subsingleton.elim b.down (realizedVertex (X := Z) z))).trans
        (congrArg ULift.up hOriginal)
  change toTopULiftIso.{u, v}.hom.app X (toTop.map (uliftFunctor.{v, u}.map g) a) =
    TopCat.uliftFunctor.{v, u}.map (toTop.map g) b at hNat
  exact (congrArg (toTopULiftIso.{u, v}.hom.app X) hFa).symm.trans (hNat.trans hGb)

/-- The actual inverse retains EVERY original vertex as well. -/
public theorem toTopULiftIso_inv_realizedVertex (X : SSet.{u}) (x : X _⦋0⦌) :
    (toTopULiftIso.{u, v}.inv.app X)
        (ULift.up (realizedVertex (X := X) x) :
          TopCat.uliftFunctor.{v, u}.obj (toTop.obj X)) =
      realizedVertex (X := uliftFunctor.{v, u}.obj X) (ULift.up x) := by
  have h := congrArg (toTopULiftIso.{u, v}.inv.app X)
    (toTopULiftIso_hom_realizedVertex.{u, v} X x)
  exact h.symm.trans (ConcreteCategory.congr_hom (toTopULiftIso.{u, v}.app X).hom_inv_id
    (realizedVertex (X := uliftFunctor.{v, u}.obj X) (ULift.up x)))

end SSet

end


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace SSet

private theorem toTopULiftIsoHomSimplexValueComputed
    (n : SimplexCategory)
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    let J : stdSimplex.{max u v}.obj n ⟶
        uliftFunctor.{v, u}.obj (stdSimplex.{u}.obj n) :=
      { app Δ := ↾fun a => ULift.up (ULift.up a.down)
        naturality := by intro Δ Γ f; ext a; rfl }
    (toTopULiftIso.{u, v}.hom.app (stdSimplex.{u}.obj n))
        (toTop.map J ((toTopSimplex.{max u v}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{max u v}.obj n))) =
      (ULift.up ((toTopSimplex.{u}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{u}.obj n)) :
        TopCat.uliftFunctor.{v, u}.obj (toTop.obj (stdSimplex.{u}.obj n))) := by
  let J : stdSimplex.{max u v}.obj n ⟶
      uliftFunctor.{v, u}.obj (stdSimplex.{u}.obj n) :=
    (liftedStandardSimplexIso.{u, v}).inv.app n
  change (toTopULiftIso.{u, v}.hom.app (stdSimplex.{u}.obj n))
      (toTop.map J ((toTopSimplex.{max u v}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{max u v}.obj n))) =
    (ULift.up ((toTopSimplex.{u}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{u}.obj n)) :
      TopCat.uliftFunctor.{v, u}.obj (toTop.obj (stdSimplex.{u}.obj n)))
  let F := uliftFunctor.{v, u} ⋙ toTop.{max u v}
  let G := toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}
  let : PreservesColimitsOfSize.{0, u} uliftFunctor.{v, u} :=
    originalSSetULift_preservesColimits
  let : PreservesColimitsOfSize.{0, u} F := by
    dsimp only [F]
    infer_instance
  let : PreservesColimitsOfSize.{0, u} G := by
    dsimp only [G]
    infer_instance
  let eF : stdSimplex.{u} ⋙ F ≅ SimplexCategory.toTop.{max u v} :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight liftedStandardSimplexIso toTop.{max u v} ≪≫
      toTopSimplex.{max u v}
  let eG : stdSimplex.{u} ⋙ G ≅ SimplexCategory.toTop.{max u v} :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight toTopSimplex.{u} (TopCat.uliftFunctor.{v, u}) ≪≫
      liftedTopSimplexIso
  let : F.IsLeftKanExtension (𝟙 (stdSimplex.{u} ⋙ F)) :=
    preservingFunctor_isLeftKanExtension F
  let : G.IsLeftKanExtension (𝟙 (stdSimplex.{u} ⋙ G)) :=
    preservingFunctor_isLeftKanExtension G
  have hIso : toTopULiftIso.{u, v}.hom.app (stdSimplex.{u}.obj n) =
      eF.hom.app n ≫ eG.inv.app n := by
    change (F.descOfIsLeftKanExtension (𝟙 (stdSimplex.{u} ⋙ F)) G
      ((eF ≪≫ eG.symm).hom ≫ 𝟙 (stdSimplex.{u} ⋙ G))).app
        (stdSimplex.{u}.obj n) = eF.hom.app n ≫ eG.inv.app n
    have hFac := Functor.descOfIsLeftKanExtension_fac_app F
      (𝟙 (stdSimplex.{u} ⋙ F)) G
      ((eF ≪≫ eG.symm).hom ≫ 𝟙 (stdSimplex.{u} ⋙ G)) n
    simpa only [NatTrans.id_app, NatTrans.comp_app, Category.id_comp,
      Category.comp_id, Iso.trans_hom, Iso.symm_hom] using hFac
  let y : SimplexCategory.toTop.{max u v}.obj n := ULift.up t
  have hSource : eF.inv.app n y =
      toTop.map J ((toTopSimplex.{max u v}.inv.app n) y) := rfl
  have hTarget : eG.inv.app n y =
      (ULift.up ((toTopSimplex.{u}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{u}.obj n)) :
        TopCat.uliftFunctor.{v, u}.obj (toTop.obj (stdSimplex.{u}.obj n))) := rfl
  have hInverse : eF.hom.app n (eF.inv.app n y) = y :=
    (TopCat.comp_app (eF.inv.app n) (eF.hom.app n) y).symm.trans
      (ConcreteCategory.congr_hom (eF.app n).inv_hom_id y)
  have hPoint : toTopULiftIso.{u, v}.hom.app (stdSimplex.{u}.obj n)
      (eF.inv.app n y) = eG.inv.app n y :=
    (ConcreteCategory.congr_hom hIso (eF.inv.app n y)).trans
      ((TopCat.comp_app (eF.hom.app n) (eG.inv.app n) (eF.inv.app n y)).trans
        (congrArg (eG.inv.app n) hInverse))
  exact (congrArg (toTopULiftIso.{u, v}.hom.app (stdSimplex.{u}.obj n)) hSource).symm.trans
    (hPoint.trans hTarget)

/-- The SAME original universe-change Iso has its actual value on every
standard simplex and every barycentric point, in both independent universes. -/
public theorem toTopULiftIso_hom_simplexValue
    (n : SimplexCategory)
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    let J : stdSimplex.{max u v}.obj n ⟶
        uliftFunctor.{v, u}.obj (stdSimplex.{u}.obj n) :=
      { app Δ := ↾fun a => ULift.up (ULift.up a.down)
        naturality := by intro Δ Γ f; ext a; rfl }
    (toTopULiftIso.{u, v}.hom.app (stdSimplex.{u}.obj n))
        (toTop.map J ((toTopSimplex.{max u v}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{max u v}.obj n))) =
      (ULift.up ((toTopSimplex.{u}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{u}.obj n)) :
        TopCat.uliftFunctor.{v, u}.obj (toTop.obj (stdSimplex.{u}.obj n))) :=
  toTopULiftIsoHomSimplexValueComputed n t

end SSet

end
