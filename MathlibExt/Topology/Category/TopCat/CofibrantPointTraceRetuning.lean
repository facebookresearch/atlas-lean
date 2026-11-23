/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.SectionHomotopyExtension
public import MathlibExt.Topology.Category.TopCat.PathModelCategory
public import MathlibExt.Topology.Category.TopCat.RealizedPointCofibration
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Retuning an actual homotopy along a null point trace

The given path homotopy is used as a homotopy in the actual fiber of endpoint
evaluation. Model-category homotopy extension retunes the whole path family
while fixing BOTH original endpoint maps. The final family is constant at
the original source point at every time.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Topology
open scoped Simplicial TopCat.modelCategory ContinuousMap

universe u

namespace TopCat.PointTraceRetuning

private abbrev pointObject : TopCat.{u} := TopCat.of PUnit.{u + 1}

private theorem point_isCofibrant : IsCofibrant (pointObject.{u}) := by
  let K : SSet.{u} := Δ[0]
  let : IsCofibrant (SSet.toTop.obj K) :=
    SSet.RealizationCWUpgrade.realization_isCofibrant K
  let e : SSet.toTop.obj K ≅ pointObject.{u} :=
    TopCat.isoOfHomeo (Homeomorph.homeomorphOfUnique _ _)
  exact isCofibrant_of_cofibration e.hom

private theorem intervalProjection_weak :
    WeakEquivalence
      (prod.fst : pointObject.{u} ⨯ TopCat.I.{u} ⟶ pointObject.{u}) := by
  let : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let : ContractibleSpace TopCat.I.{u} :=
    TopCat.I.homeomorph.{u}.contractibleSpace
  let J : TopCat.{u} := pointObject.{u} ⨯ TopCat.I.{u}
  let : ContractibleSpace J :=
    (TopCat.homeoOfIso
      (TopCat.prodIsoProd (pointObject.{u}) TopCat.I.{u})).contractibleSpace
  obtain ⟨e⟩ := ContractibleSpace.hequiv J (pointObject.{u})
  have he : TopCat.ofHom e.toFun =
      (prod.fst : J ⟶ pointObject.{u}) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact Subsingleton.elim _ _
  apply (weakEquivalence_iff _).mpr
  change TopCat.weakHomotopyEquivalences
    (prod.fst : J ⟶ pointObject.{u})
  rw [← he]
  exact TopCat.homotopyEquiv_toFun_mem e

private def pointCylinder : Cylinder (pointObject.{u}) where
  I := pointObject.{u} ⨯ TopCat.I.{u}
  i₀ := prod.lift (𝟙 _) (TopCat.const (0 : TopCat.I.{u}))
  i₁ := prod.lift (𝟙 _) (TopCat.const (1 : TopCat.I.{u}))
  π := prod.fst
  i₀_π := prod.lift_fst _ _
  i₁_π := prod.lift_fst _ _
  weakEquivalence_π := intervalProjection_weak

/-- The actual categorical point cylinder is the tensor cylinder through
its canonical product Iso. -/
private def pointCylinderTensorIso :
    (pointCylinder.{u}).I ≅ pointObject.{u} ⊗ TopCat.I.{u} :=
  TopCat.prodIsoProd (pointObject.{u}) TopCat.I.{u}

private theorem pointCylinder_i₀_tensor :
    (pointCylinder.{u}).i₀ ≫ (pointCylinderTensorIso.{u}).hom =
      (TopCat.ι₀ : pointObject.{u} ⟶ pointObject.{u} ⊗ TopCat.I.{u}) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  dsimp only [pointCylinder, pointCylinderTensorIso]
  change ((prod.lift (𝟙 (pointObject.{u})) (TopCat.const (0 : TopCat.I.{u})) ≫
    (TopCat.prodIsoProd (pointObject.{u}) TopCat.I.{u}).hom) a) = TopCat.ι₀ a
  rw [TopCat.comp_app, TopCat.prodIsoProd_hom_apply, TopCat.ι₀_apply]
  apply Prod.ext
  · have hv := ConcreteCategory.congr_hom
      (prod.lift_fst (𝟙 (pointObject.{u})) (TopCat.const (0 : TopCat.I.{u}))) a
    change ((prod.lift (𝟙 (pointObject.{u})) (TopCat.const (0 : TopCat.I.{u})) ≫
      (prod.fst : pointObject.{u} ⨯ TopCat.I.{u} ⟶ pointObject.{u})) a) = a at hv
    rw [TopCat.comp_app] at hv
  · have hv := ConcreteCategory.congr_hom
      (prod.lift_snd (𝟙 (pointObject.{u})) (TopCat.const (0 : TopCat.I.{u}))) a
    change ((prod.lift (𝟙 (pointObject.{u})) (TopCat.const (0 : TopCat.I.{u})) ≫
      (prod.snd : pointObject.{u} ⨯ TopCat.I.{u} ⟶ TopCat.I.{u})) a) = 0 at hv
    rw [TopCat.comp_app] at hv
    exact hv

private theorem pointCylinder_i₁_tensor :
    (pointCylinder.{u}).i₁ ≫ (pointCylinderTensorIso.{u}).hom =
      (TopCat.ι₁ : pointObject.{u} ⟶ pointObject.{u} ⊗ TopCat.I.{u}) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  dsimp only [pointCylinder, pointCylinderTensorIso]
  change ((prod.lift (𝟙 (pointObject.{u})) (TopCat.const (1 : TopCat.I.{u})) ≫
    (TopCat.prodIsoProd (pointObject.{u}) TopCat.I.{u}).hom) a) = TopCat.ι₁ a
  rw [TopCat.comp_app, TopCat.prodIsoProd_hom_apply, TopCat.ι₁_apply]
  apply Prod.ext
  · have hv := ConcreteCategory.congr_hom
      (prod.lift_fst (𝟙 (pointObject.{u})) (TopCat.const (1 : TopCat.I.{u}))) a
    change ((prod.lift (𝟙 (pointObject.{u})) (TopCat.const (1 : TopCat.I.{u})) ≫
      (prod.fst : pointObject.{u} ⨯ TopCat.I.{u} ⟶ pointObject.{u})) a) = a at hv
    rw [TopCat.comp_app] at hv
  · have hv := ConcreteCategory.congr_hom
      (prod.lift_snd (𝟙 (pointObject.{u})) (TopCat.const (1 : TopCat.I.{u}))) a
    change ((prod.lift (𝟙 (pointObject.{u})) (TopCat.const (1 : TopCat.I.{u})) ≫
      (prod.snd : pointObject.{u} ⨯ TopCat.I.{u} ⟶ TopCat.I.{u})) a) = 1 at hv
    rw [TopCat.comp_app] at hv
    exact hv

/-- An actual homotopy whose original point trace is null admits a WHOLE
homotopy relative to that point. Both original endpoint maps are retained;
the null trace supplies the actual fiberwise homotopy, not a desired lift. -/
public theorem _root_.TopCat.exists_pointRelativeHomotopy_of_null_trace
    {X Y : TopCat.{u}} (f g : X ⟶ Y) (x : X) (y : Y)
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    (hfx : f x = y) (hgx : g x = y) (H : TopCat.Homotopy f g)
    (L : Path.Homotopy ((H.evalAt x).cast hfx.symm hgx.symm) (Path.refl y)) :
    Nonempty (ContinuousMap.HomotopyRel f.hom g.hom {x}) := by
  let A : TopCat.{u} := pointObject.{u}
  let i : A ⟶ X := TopCat.const x
  let p : TopCat.pathObject Y ⟶ Y ⨯ Y := TopCat.pathEndpoints Y
  let b : X ⟶ Y ⨯ Y := prod.lift f g
  let s : X ⟶ TopCat.pathObject Y := TopCat.ofHom H.h.hom.curry
  let k : A ⟶ TopCat.pathObject Y :=
    TopCat.const (ContinuousMap.const TopCat.I.{u} y)
  let : Fibration p := TopCat.modelCategory.pathEndpoints_fibration Y
  let : IsCofibrant A := point_isCofibrant.{u}
  have hp₀ : p ≫ (prod.fst : Y ⨯ Y ⟶ Y) = TopCat.pathEvalZero Y := by
    dsimp only [p, TopCat.pathEndpoints]
    exact prod.lift_fst _ _
  have hp₁ : p ≫ (prod.snd : Y ⨯ Y ⟶ Y) = TopCat.pathEvalOne Y := by
    dsimp only [p, TopCat.pathEndpoints]
    exact prod.lift_snd _ _
  have hb₀ : b ≫ (prod.fst : Y ⨯ Y ⟶ Y) = f := prod.lift_fst _ _
  have hb₁ : b ≫ (prod.snd : Y ⨯ Y ⟶ Y) = g := prod.lift_snd _ _
  have hs₀ : s ≫ TopCat.pathEvalZero Y = f := by
    apply TopCat.hom_ext
    rw [TopCat.hom_comp]
    dsimp only [s, TopCat.pathEvalZero, TopCat.hom_ofHom]
    apply ContinuousMap.ext
    intro z
    change H.h.hom (z, (0 : TopCat.I.{u})) = f.hom z
    exact (TopCat.Homotopy.h_hom_apply H (z, (0 : TopCat.I.{u}))).trans
      ((congrArg (fun t => H (t, z)) TopCat.I.homeomorph_zero.{u}).trans
        (H.map_zero_left z))
  have hs₁ : s ≫ TopCat.pathEvalOne Y = g := by
    apply TopCat.hom_ext
    rw [TopCat.hom_comp]
    dsimp only [s, TopCat.pathEvalOne, TopCat.hom_ofHom]
    apply ContinuousMap.ext
    intro z
    change H.h.hom (z, (1 : TopCat.I.{u})) = g.hom z
    exact (TopCat.Homotopy.h_hom_apply H (z, (1 : TopCat.I.{u}))).trans
      ((congrArg (fun t => H (t, z)) TopCat.I.homeomorph_one.{u}).trans
        (H.map_one_left z))
  have hs : s ≫ p = b := by
    apply prod.hom_ext
    · rw [Category.assoc, hp₀, hb₀]
      exact hs₀
    · rw [Category.assoc, hp₁, hb₁]
      exact hs₁
  have hk₀ : k ≫ TopCat.pathEvalZero Y = i ≫ f := by
    apply TopCat.hom_ext
    simp only [TopCat.hom_comp]
    dsimp only [k, i, TopCat.pathEvalZero, TopCat.const, TopCat.hom_ofHom]
    apply ContinuousMap.ext
    intro a
    change y = f.hom x
    exact hfx.symm
  have hk₁ : k ≫ TopCat.pathEvalOne Y = i ≫ g := by
    apply TopCat.hom_ext
    simp only [TopCat.hom_comp]
    dsimp only [k, i, TopCat.pathEvalOne, TopCat.const, TopCat.hom_ofHom]
    apply ContinuousMap.ext
    intro a
    change y = g.hom x
    exact hgx.symm
  have hk : k ≫ p = i ≫ b := by
    apply prod.hom_ext
    · calc
        (k ≫ p) ≫ prod.fst = k ≫ TopCat.pathEvalZero Y := by
          rw [Category.assoc, hp₀]
        _ = i ≫ f := hk₀
        _ = (i ≫ b) ≫ prod.fst := by rw [Category.assoc, hb₀]
    · calc
        (k ≫ p) ≫ prod.snd = k ≫ TopCat.pathEvalOne Y := by
          rw [Category.assoc, hp₁]
        _ = i ≫ g := hk₁
        _ = (i ≫ b) ≫ prod.snd := by rw [Category.assoc, hb₁]
  let clock : C(TopCat.I.{u}, unitInterval) :=
    ⟨TopCat.I.homeomorph.{u}, TopCat.I.homeomorph.{u}.continuous⟩
  let square : C(unitInterval × TopCat.I.{u}, Y) :=
    L.toHomotopy.toContinuousMap.comp ((ContinuousMap.id unitInterval).prodMap clock)
  let family : C(unitInterval, TopCat.pathObject Y) := square.curry
  let K : TopCat.Homotopy (i ≫ s) k :=
    { toFun := fun z => family z.1
      continuous_toFun := family.continuous.comp continuous_fst
      map_zero_left := fun a => by
        apply ContinuousMap.ext
        intro t
        change L ((0 : unitInterval), TopCat.I.homeomorph.{u} t) = H.h.hom (x, t)
        exact (L.map_zero_left (TopCat.I.homeomorph.{u} t)).trans
          (TopCat.Homotopy.h_hom_apply H (x, t)).symm
      map_one_left := fun a => by
        apply ContinuousMap.ext
        intro t
        exact L.map_one_left (TopCat.I.homeomorph.{u} t) }
  let P : Cylinder A := pointCylinder.{u}
  let eP : P.I ≅ A ⊗ TopCat.I.{u} := pointCylinderTensorIso.{u}
  let h : P.LeftHomotopy (i ≫ s) k :=
    { h := eP.hom ≫ K.h
      h₀ := by
        change (pointCylinder.{u}).i₀ ≫
          ((pointCylinderTensorIso.{u}).hom ≫ K.h) = i ≫ s
        rw [← Category.assoc, pointCylinder_i₀_tensor.{u}]
        exact TopCat.Homotopy.ι₀_h K
      h₁ := by
        change (pointCylinder.{u}).i₁ ≫
          ((pointCylinderTensorIso.{u}).hom ≫ K.h) = k
        rw [← Category.assoc, pointCylinder_i₁_tensor.{u}]
        exact TopCat.Homotopy.ι₁_h K }
  have eP_π : eP.inv ≫ P.π = (TopCat.prodFst : A ⊗ TopCat.I.{u} ⟶ A) := by
    change (TopCat.prodIsoProd A TopCat.I.{u}).inv ≫
      (prod.fst : A ⨯ TopCat.I.{u} ⟶ A) = TopCat.prodFst
    exact TopCat.prodIsoProd_inv_fst A TopCat.I.{u}
  have hKbase : K.h ≫ p = TopCat.prodFst ≫ i ≫ b := by
    apply prod.hom_ext
    · rw [Category.assoc, hp₀]
      let πT : A ⊗ TopCat.I.{u} ⟶ A := TopCat.prodFst
      have hr : (πT ≫ i ≫ b) ≫ (prod.fst : Y ⨯ Y ⟶ Y) = πT ≫ i ≫ f :=
        (Category.assoc πT (i ≫ b) prod.fst).trans
          (congrArg (fun q => πT ≫ q)
            ((Category.assoc i b prod.fst).trans
              (congrArg (fun q => i ≫ q) hb₀)))
      change K.h ≫ TopCat.pathEvalZero Y = (πT ≫ i ≫ b) ≫ prod.fst
      refine Eq.trans ?_ hr.symm
      apply TopCat.hom_ext
      simp only [TopCat.hom_comp]
      dsimp only [i, TopCat.pathEvalZero, TopCat.const, TopCat.hom_ofHom]
      apply ContinuousMap.ext
      intro z
      change (K.h z) (0 : TopCat.I.{u}) = f.hom x
      calc
        (K.h z) (0 : TopCat.I.{u}) =
            (K (TopCat.I.homeomorph.{u} z.2, z.1)) (0 : TopCat.I.{u}) :=
          congrArg (fun q : C(TopCat.I.{u}, Y) => q 0)
            (TopCat.Homotopy.h_hom_apply K z)
        _ = L (TopCat.I.homeomorph.{u} z.2,
            TopCat.I.homeomorph.{u} (0 : TopCat.I.{u})) := rfl
        _ = f.hom x := (congrArg (fun t => L (TopCat.I.homeomorph.{u} z.2, t))
          TopCat.I.homeomorph_zero.{u}).trans ((L.source _).trans hfx.symm)
    · rw [Category.assoc, hp₁]
      let πT : A ⊗ TopCat.I.{u} ⟶ A := TopCat.prodFst
      have hr : (πT ≫ i ≫ b) ≫ (prod.snd : Y ⨯ Y ⟶ Y) = πT ≫ i ≫ g :=
        (Category.assoc πT (i ≫ b) prod.snd).trans
          (congrArg (fun q => πT ≫ q)
            ((Category.assoc i b prod.snd).trans
              (congrArg (fun q => i ≫ q) hb₁)))
      change K.h ≫ TopCat.pathEvalOne Y = (πT ≫ i ≫ b) ≫ prod.snd
      refine Eq.trans ?_ hr.symm
      apply TopCat.hom_ext
      simp only [TopCat.hom_comp]
      dsimp only [i, TopCat.pathEvalOne, TopCat.const, TopCat.hom_ofHom]
      apply ContinuousMap.ext
      intro z
      change (K.h z) (1 : TopCat.I.{u}) = g.hom x
      calc
        (K.h z) (1 : TopCat.I.{u}) =
            (K (TopCat.I.homeomorph.{u} z.2, z.1)) (1 : TopCat.I.{u}) :=
          congrArg (fun q : C(TopCat.I.{u}, Y) => q 1)
            (TopCat.Homotopy.h_hom_apply K z)
        _ = L (TopCat.I.homeomorph.{u} z.2,
            TopCat.I.homeomorph.{u} (1 : TopCat.I.{u})) := rfl
        _ = g.hom x := (congrArg (fun t => L (TopCat.I.homeomorph.{u} z.2, t))
          TopCat.I.homeomorph_one.{u}).trans ((L.target _).trans hgx.symm)
  have hbase : h.h ≫ p = P.π ≫ i ≫ b := by
    apply (cancel_epi eP.inv).mp
    change eP.inv ≫ ((eP.hom ≫ K.h) ≫ p) = eP.inv ≫ (P.π ≫ i ≫ b)
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, eP_π]
    exact hKbase
  obtain ⟨s', hs', hi⟩ :=
    HomotopicalAlgebra.exists_fibration_map_extension_of_fiberwise_homotopy
      i p b s hs k hk P h hbase
  have h₀ : s' ≫ TopCat.pathEvalZero Y = f := by
    calc
      s' ≫ TopCat.pathEvalZero Y = (s' ≫ p) ≫ prod.fst := by
        rw [Category.assoc, hp₀]
      _ = b ≫ prod.fst := congrArg (fun q => q ≫ prod.fst) hs'
      _ = f := hb₀
  have h₁ : s' ≫ TopCat.pathEvalOne Y = g := by
    calc
      s' ≫ TopCat.pathEvalOne Y = (s' ≫ p) ≫ prod.snd := by
        rw [Category.assoc, hp₁]
      _ = b ≫ prod.snd := congrArg (fun q => q ≫ prod.snd) hs'
      _ = g := hb₁
  let unclock : C(unitInterval, TopCat.I.{u}) :=
    ⟨TopCat.I.homeomorph.{u}.symm, TopCat.I.homeomorph.{u}.symm.continuous⟩
  let joint : C(unitInterval × X, Y) :=
    s'.hom.uncurry.comp ((ContinuousMap.snd : C(unitInterval × X, X)).prodMk
      (unclock.comp (ContinuousMap.fst : C(unitInterval × X, unitInterval))))
  refine ⟨
    { toContinuousMap := joint
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
  · intro z
    have t0 : TopCat.I.homeomorph.{u}.symm (0 : unitInterval) =
        (0 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.{u}.injective
      exact (TopCat.I.homeomorph.{u}.apply_symm_apply _).trans
        TopCat.I.homeomorph_zero.{u}.symm
    have hv := ConcreteCategory.congr_hom h₀ z
    change ((s' ≫ TopCat.pathEvalZero Y) : X → Y) z = f z at hv
    rw [TopCat.comp_app] at hv
    dsimp only [TopCat.pathEvalZero, TopCat.hom_ofHom] at hv
    change s'.hom z (0 : TopCat.I.{u}) = f.hom z at hv
    exact (congrArg (fun t => s'.hom z t) t0).trans hv
  · intro z
    have t1 : TopCat.I.homeomorph.{u}.symm (1 : unitInterval) =
        (1 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.{u}.injective
      exact (TopCat.I.homeomorph.{u}.apply_symm_apply _).trans
        TopCat.I.homeomorph_one.{u}.symm
    have hv := ConcreteCategory.congr_hom h₁ z
    change ((s' ≫ TopCat.pathEvalOne Y) : X → Y) z = g z at hv
    rw [TopCat.comp_app] at hv
    dsimp only [TopCat.pathEvalOne, TopCat.hom_ofHom] at hv
    change s'.hom z (1 : TopCat.I.{u}) = g.hom z at hv
    exact (congrArg (fun t => s'.hom z t) t1).trans hv
  · intro t z hz
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    subst z
    have hv := ConcreteCategory.congr_hom hi PUnit.unit.{u + 1}
    change ((i ≫ s') : A → TopCat.pathObject Y) PUnit.unit.{u + 1} = k PUnit.unit.{u + 1} at hv
    rw [TopCat.comp_app] at hv
    dsimp only [i, k, TopCat.const, TopCat.hom_ofHom] at hv
    change s'.hom x = ContinuousMap.const TopCat.I.{u} y at hv
    change s'.hom x (TopCat.I.homeomorph.{u}.symm t) = f.hom x
    exact (congrArg (fun q : C(TopCat.I.{u}, Y) =>
      q (TopCat.I.homeomorph.{u}.symm t)) hv).trans hfx.symm

end TopCat.PointTraceRetuning

end
