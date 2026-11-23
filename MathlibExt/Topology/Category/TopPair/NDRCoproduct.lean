/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.ProdCoproduct
public import MathlibExt.Topology.Category.TopPair.CoproductColimits
public import MathlibExt.Topology.Category.TopPair.NDR

import MathlibExt.Topology.Category.TopCat.ProdMapPointwise

/-!
# Componentwise controlled NDR coordinates on pair coproducts

A family of controlled NDR pairs has componentwise control, endpoint, and
deformation maps on its explicit topological coproduct.  Continuity of the
joint deformation follows from the canonical comparison between a fixed
product and a coproduct.

The component formulas package into NDR data without any nonempty-index
hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe v u

namespace TopPair.NDRData

variable {ι : Type v} {P : ι → TopPair.{max v u}}
variable (d : (i : ι) → TopPair.NDRData (P i))

private theorem exists_eq_sigma_fst_ι
    (x : (TopPair.sigma P).fst) :
    ∃ (i : ι) (y : (P i).fst),
      x = TopPair.Hom.fst (TopPair.sigmaι P i) y := by
  let e : (TopPair.sigma P).fst ≅
      TopCat.of (Σ i, (P i).fst) := by
    change (∐ fun i => (P i).fst) ≅ _
    exact TopCat.sigmaIsoSigma (fun i => (P i).fst)
  rcases h : e.hom x with ⟨i, y⟩
  refine ⟨i, y, ?_⟩
  have h₁ : x = e.inv (⟨i, y⟩ : Σ i, (P i).fst) :=
    (TopCat.hom_inv_id_apply e x).symm.trans
      (congrArg (fun z : Σ i, (P i).fst => e.inv z) h)
  have h₂ : e.inv (⟨i, y⟩ : Σ i, (P i).fst) =
      Limits.Sigma.ι (fun j => (P j).fst) i y :=
    TopCat.sigmaIsoSigma_inv_apply (fun j => (P j).fst) i y
  have h₃ : Limits.Sigma.ι (fun j => (P j).fst) i y =
      TopPair.Hom.fst (TopPair.sigmaι P i) y :=
    (ConcreteCategory.congr_hom (sigmaι_fst P i) y).symm
  exact h₁.trans (h₂.trans h₃)

private theorem exists_eq_sigma_snd_ι
    (x : (TopPair.sigma P).snd) :
    ∃ (i : ι) (y : (P i).snd),
      x = TopPair.Hom.snd (TopPair.sigmaι P i) y := by
  let e : (TopPair.sigma P).snd ≅
      TopCat.of (Σ i, (P i).snd) := by
    change (∐ fun i => (P i).snd) ≅ _
    exact TopCat.sigmaIsoSigma (fun i => (P i).snd)
  rcases h : e.hom x with ⟨i, y⟩
  refine ⟨i, y, ?_⟩
  have h₁ : x = e.inv (⟨i, y⟩ : Σ i, (P i).snd) :=
    (TopCat.hom_inv_id_apply e x).symm.trans
      (congrArg (fun z : Σ i, (P i).snd => e.inv z) h)
  have h₂ : e.inv (⟨i, y⟩ : Σ i, (P i).snd) =
      Limits.Sigma.ι (fun j => (P j).snd) i y :=
    TopCat.sigmaIsoSigma_inv_apply (fun j => (P j).snd) i y
  have h₃ : Limits.Sigma.ι (fun j => (P j).snd) i y =
      TopPair.Hom.snd (TopPair.sigmaι P i) y :=
    (ConcreteCategory.congr_hom (sigmaι_snd P i) y).symm
  exact h₁.trans (h₂.trans h₃)

private theorem mem_range_sigma_map_iff
    (x : (TopPair.sigma P).fst) :
    x ∈ Set.range (TopPair.sigma P).map ↔
      ∃ (i : ι) (a : (P i).snd),
        x = TopPair.Hom.fst (TopPair.sigmaι P i) ((P i).map a) := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨i, y, hy⟩ := exists_eq_sigma_snd_ι (P := P) a
    refine ⟨i, y, ?_⟩
    rw [hy]
    exact ConcreteCategory.congr_hom (TopPair.Hom.w (sigmaι P i)) y
  · rintro ⟨i, a, rfl⟩
    refine ⟨TopPair.Hom.snd (TopPair.sigmaι P i) a, ?_⟩
    exact ConcreteCategory.congr_hom (TopPair.Hom.w (sigmaι P i)) a

/-- The componentwise control on an explicit coproduct of topological pairs. -/
noncomputable def sigmaControl :
    C((TopPair.sigma P).fst, unitInterval) := by
  let controlHom (i : ι) : (P i).fst ⟶ TopCat.I.{max v u} :=
    TopCat.ofHom
      ((TopCat.I.homeomorph.symm :
        C(unitInterval, TopCat.I.{max v u})).comp (d i).control)
  let lifted : (TopPair.sigma P).fst ⟶ TopCat.I.{max v u} := by
    change (∐ fun i => (P i).fst) ⟶ TopCat.I.{max v u}
    exact Limits.Sigma.desc controlHom
  exact (TopCat.I.homeomorph :
    C(TopCat.I.{max v u}, unitInterval)).comp lifted.hom

/-- The coproduct control restricts to the supplied control on every
component. -/
@[simp]
theorem sigmaControl_ι (i : ι) (x : (P i).fst) :
    sigmaControl (P := P) d
        (TopPair.Hom.fst (TopPair.sigmaι P i) x) =
      (d i).control x := by
  let controlHom (j : ι) : (P j).fst ⟶ TopCat.I.{max v u} :=
    TopCat.ofHom
      ((TopCat.I.homeomorph.symm :
        C(unitInterval, TopCat.I.{max v u})).comp (d j).control)
  let lifted : (TopPair.sigma P).fst ⟶ TopCat.I.{max v u} := by
    change (∐ fun j => (P j).fst) ⟶ TopCat.I.{max v u}
    exact Limits.Sigma.desc controlHom
  change TopCat.I.homeomorph.{max v u}
    (lifted (TopPair.Hom.fst (TopPair.sigmaι P i) x)) = _
  have hlifted : TopPair.Hom.fst (TopPair.sigmaι P i) ≫ lifted =
      controlHom i := by
    rw [sigmaι_fst P i]
    exact Limits.Sigma.ι_comp_desc controlHom i
  have hx := ConcreteCategory.congr_hom hlifted x
  change lifted (TopPair.Hom.fst (TopPair.sigmaι P i) x) =
    controlHom i x at hx
  rw [hx]
  change TopCat.I.homeomorph.{max v u}
    (TopCat.I.homeomorph.{max v u}.symm ((d i).control x)) = _
  exact TopCat.I.homeomorph.{max v u}.apply_symm_apply ((d i).control x)

/-- The componentwise endpoint on an explicit coproduct of topological
pairs. -/
noncomputable def sigmaEndpoint :
    C((TopPair.sigma P).fst, (TopPair.sigma P).fst) := by
  let endpointHom (i : ι) : (P i).fst ⟶ (P i).fst :=
    TopCat.ofHom (d i).endpoint
  let e : (TopPair.sigma P).fst ⟶ (TopPair.sigma P).fst := by
    change (∐ fun i => (P i).fst) ⟶ (TopPair.sigma P).fst
    exact Limits.Sigma.desc fun i =>
      endpointHom i ≫
        TopPair.Hom.fst (TopPair.sigmaι P i)
  exact e.hom

/-- The coproduct endpoint restricts to the supplied endpoint and remains in
the same component. -/
@[simp]
theorem sigmaEndpoint_ι (i : ι) (x : (P i).fst) :
    sigmaEndpoint (P := P) d
        (TopPair.Hom.fst (TopPair.sigmaι P i) x) =
      TopPair.Hom.fst (TopPair.sigmaι P i) ((d i).endpoint x) := by
  let endpointHom (j : ι) : (P j).fst ⟶ (P j).fst :=
    TopCat.ofHom (d j).endpoint
  change (Limits.Sigma.desc (fun j =>
    endpointHom j ≫
      TopPair.Hom.fst (TopPair.sigmaι P j)))
        (TopPair.Hom.fst (TopPair.sigmaι P i) x) = _
  have hendpoint : TopPair.Hom.fst (TopPair.sigmaι P i) ≫
      Limits.Sigma.desc (fun j =>
        endpointHom j ≫ TopPair.Hom.fst (TopPair.sigmaι P j)) =
      endpointHom i ≫ TopPair.Hom.fst (TopPair.sigmaι P i) := by
    rw [sigmaι_fst P i]
    exact Limits.Sigma.ι_comp_desc _ i
  have hx := ConcreteCategory.congr_hom hendpoint x
  change
    (Limits.Sigma.desc (fun j =>
      endpointHom j ≫ TopPair.Hom.fst (TopPair.sigmaι P j)))
        (TopPair.Hom.fst (TopPair.sigmaι P i) x) =
      TopPair.Hom.fst (TopPair.sigmaι P i) ((d i).endpoint x) at hx
  exact hx

/-- The jointly continuous componentwise deformation on an explicit
coproduct of controlled NDR pairs. -/
noncomputable def sigmaDeformation :
    C(unitInterval × (TopPair.sigma P).fst, (TopPair.sigma P).fst) := by
  let timeLift :
    TopCat.of (unitInterval × (TopPair.sigma P).fst) ⟶
        TopCat.of (TopCat.I.{max v u} × (TopPair.sigma P).fst) :=
    TopCat.ofHom
      ((TopCat.I.homeomorph.symm :
        C(unitInterval, TopCat.I.{max v u})).prodMap
        (ContinuousMap.id _))
  let indexEquiv : ULift.{u} ι ≃ ι := Equiv.ulift
  let family : ι → TopCat.{max v u} := fun i => (P i).fst
  let reindexFamily := Limits.Sigma.reindex indexEquiv family
  let reindexProduct := Limits.Sigma.reindex indexEquiv
    (fun i : ι => TopCat.I.{max v u} ⨯ family i)
  let liftedComparison := TopCat.prodCoproductComparisonIso.{max v u}
    (J := ULift.{u} ι) (TopCat.I.{max v u}) (family ∘ indexEquiv)
  let comparison :
      (∐ fun i : ι => TopCat.I.{max v u} ⨯ family i) ≅
        TopCat.I.{max v u} ⨯ (∐ family) :=
    reindexProduct.symm ≪≫ liftedComparison ≪≫
      Limits.prod.mapIso (Iso.refl _) reindexFamily
  let deformationHom (i : ι) :
      TopCat.I.{max v u} ⨯ (P i).fst ⟶ (P i).fst :=
    (TopCat.prodIsoProd TopCat.I (P i).fst).hom ≫
      TopCat.ofHom
        { toFun := fun p =>
            (d i).deformation (TopCat.I.homeomorph p.1, p.2)
          continuous_toFun :=
            (d i).deformation.continuous.comp
              ((TopCat.I.homeomorph.continuous.comp continuous_fst).prodMk
                continuous_snd) }
  let H : TopCat.of (unitInterval × (TopPair.sigma P).fst) ⟶
      (TopPair.sigma P).fst :=
    timeLift ≫
      (TopCat.prodIsoProd TopCat.I (TopPair.sigma P).fst).inv ≫
      comparison.inv ≫
      Limits.Sigma.desc (fun i =>
        deformationHom i ≫
          TopPair.Hom.fst (TopPair.sigmaι P i))
  exact H.hom

/-- The coproduct deformation restricts to the supplied deformation on every
component. -/
@[simp]
theorem sigmaDeformation_ι
    (i : ι) (t : unitInterval) (x : (P i).fst) :
    sigmaDeformation (P := P) d
        (t, TopPair.Hom.fst (TopPair.sigmaι P i) x) =
      TopPair.Hom.fst (TopPair.sigmaι P i)
        ((d i).deformation (t, x)) := by
  let timeLift :
    TopCat.of (unitInterval × (TopPair.sigma P).fst) ⟶
        TopCat.of (TopCat.I.{max v u} × (TopPair.sigma P).fst) :=
    TopCat.ofHom
      ((TopCat.I.homeomorph.symm :
        C(unitInterval, TopCat.I.{max v u})).prodMap
        (ContinuousMap.id _))
  let indexEquiv : ULift.{u} ι ≃ ι := Equiv.ulift
  let family : ι → TopCat.{max v u} := fun j => (P j).fst
  let reindexFamily := Limits.Sigma.reindex indexEquiv family
  let reindexProduct := Limits.Sigma.reindex indexEquiv
    (fun j : ι => TopCat.I.{max v u} ⨯ family j)
  let liftedComparison := TopCat.prodCoproductComparisonIso.{max v u}
    (J := ULift.{u} ι) (TopCat.I.{max v u}) (family ∘ indexEquiv)
  let comparison :
      (∐ fun j : ι => TopCat.I.{max v u} ⨯ family j) ≅
        TopCat.I.{max v u} ⨯ (∐ family) :=
    reindexProduct.symm ≪≫ liftedComparison ≪≫
      Limits.prod.mapIso (Iso.refl _) reindexFamily
  let deformationHom (j : ι) :
      TopCat.I.{max v u} ⨯ (P j).fst ⟶ (P j).fst :=
    (TopCat.prodIsoProd TopCat.I (P j).fst).hom ≫
      TopCat.ofHom
        { toFun := fun p =>
            (d j).deformation (TopCat.I.homeomorph p.1, p.2)
          continuous_toFun :=
            (d j).deformation.continuous.comp
              ((TopCat.I.homeomorph.continuous.comp continuous_fst).prodMk
                continuous_snd) }
  let componentPoint :=
    (TopCat.prodIsoProd TopCat.I (P i).fst).inv
      (TopCat.I.homeomorph.symm t, x)
  have hReindexProduct :
      Limits.Sigma.ι (fun j : ι => TopCat.I.{max v u} ⨯ family j) i ≫
          reindexProduct.inv =
        Limits.Sigma.ι
          ((fun j : ι => TopCat.I.{max v u} ⨯ family j) ∘ indexEquiv)
          (ULift.up i) := by
    exact Limits.Sigma.ι_reindex_inv indexEquiv _ (ULift.up i)
  have hReindexFamily :
      Limits.Sigma.ι (family ∘ indexEquiv) (ULift.up i) ≫
          reindexFamily.hom =
        Limits.Sigma.ι family i := by
    exact Limits.Sigma.ι_reindex_hom indexEquiv family (ULift.up i)
  have hLiftedComparison :
      Limits.Sigma.ι
          (fun j : ULift.{u} ι =>
            TopCat.I.{max v u} ⨯ (family ∘ indexEquiv) j)
          (ULift.up i) ≫ liftedComparison.hom =
        Limits.prod.map (𝟙 TopCat.I)
          (Limits.Sigma.ι (family ∘ indexEquiv) (ULift.up i)) := by
    exact TopCat.prodCoproductComparison_ι
      (TopCat.I.{max v u}) (family ∘ indexEquiv) (ULift.up i)
  have hcomparisonHom :
      Limits.Sigma.ι
          (fun j : ι => TopCat.I.{max v u} ⨯ family j) i ≫
          comparison.hom =
        Limits.prod.map (𝟙 TopCat.I) (Limits.Sigma.ι family i) := by
    have hExpand :
      Limits.Sigma.ι
            (fun j : ι => TopCat.I.{max v u} ⨯ family j) i ≫
          comparison.hom =
          ((Limits.Sigma.ι
              (fun j : ι => TopCat.I.{max v u} ⨯ family j) i ≫
                reindexProduct.inv) ≫ liftedComparison.hom) ≫
            (Limits.prod.mapIso (Iso.refl _) reindexFamily).hom := by
      dsimp only [comparison]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    have hReindexWhisk :
        ((Limits.Sigma.ι
              (fun j : ι => TopCat.I.{max v u} ⨯ family j) i ≫
                reindexProduct.inv) ≫ liftedComparison.hom) ≫
            (Limits.prod.mapIso (Iso.refl _) reindexFamily).hom =
          (Limits.Sigma.ι
              ((fun j : ι => TopCat.I.{max v u} ⨯ family j) ∘ indexEquiv)
              (ULift.up i) ≫ liftedComparison.hom) ≫
            (Limits.prod.mapIso (Iso.refl _) reindexFamily).hom :=
      congrArg
        (fun k => (k ≫ liftedComparison.hom) ≫
          (Limits.prod.mapIso (Iso.refl _) reindexFamily).hom)
        hReindexProduct
    have hLiftedWhisk :
        (Limits.Sigma.ι
              ((fun j : ι => TopCat.I.{max v u} ⨯ family j) ∘ indexEquiv)
              (ULift.up i) ≫ liftedComparison.hom) ≫
            (Limits.prod.mapIso (Iso.refl _) reindexFamily).hom =
          Limits.prod.map (𝟙 TopCat.I)
              (Limits.Sigma.ι (family ∘ indexEquiv) (ULift.up i)) ≫
            Limits.prod.map (𝟙 TopCat.I) reindexFamily.hom := by
      have hLiftedComparison' :
          Limits.Sigma.ι
              ((fun j : ι => TopCat.I.{max v u} ⨯ family j) ∘ indexEquiv)
              (ULift.up i) ≫ liftedComparison.hom =
            Limits.prod.map (𝟙 TopCat.I)
              (Limits.Sigma.ι (family ∘ indexEquiv) (ULift.up i)) :=
        hLiftedComparison
      exact congrArg
        (fun k => k ≫
          (Limits.prod.mapIso (Iso.refl _) reindexFamily).hom)
        hLiftedComparison'
    have hMap :
        Limits.prod.map (𝟙 TopCat.I)
              (Limits.Sigma.ι (family ∘ indexEquiv) (ULift.up i)) ≫
            Limits.prod.map (𝟙 TopCat.I) reindexFamily.hom =
          Limits.prod.map (𝟙 TopCat.I)
          (Limits.Sigma.ι family i) := by
      rw [Limits.prod.map_map, Category.id_comp, hReindexFamily]
      rfl
    exact hExpand.trans (hReindexWhisk.trans (hLiftedWhisk.trans hMap))
  have hfst : TopPair.Hom.fst (TopPair.sigmaι P i) =
      Limits.Sigma.ι family i := sigmaι_fst P i
  have hcomparison :
      Limits.prod.map (𝟙 TopCat.I)
            (Limits.Sigma.ι family i) ≫ comparison.inv =
        Limits.Sigma.ι
          (fun j : ι => TopCat.I.{max v u} ⨯ family j) i := by
    apply (cancel_mono comparison.hom).1
    rw [Category.assoc, comparison.inv_hom_id, Category.comp_id,
      hcomparisonHom]
  have hfstx := ConcreteCategory.congr_hom hfst x
  rw [hfstx]
  have hcomponentPoint :
      (Limits.prod.map (𝟙 TopCat.I)
        (Limits.Sigma.ι family i)) componentPoint =
      (TopCat.prodIsoProd TopCat.I (∐ family)).inv
        (TopCat.I.homeomorph.symm t,
          Limits.Sigma.ι family i x) := by
    exact TopCat.prodMap_prodIso_inv_apply
      (Limits.Sigma.ι family i)
        (TopCat.I.homeomorph.symm t) x
  have htimeLift :
      timeLift (t, Limits.Sigma.ι family i x) =
        (TopCat.I.homeomorph.symm t,
          Limits.Sigma.ι family i x) := rfl
  unfold sigmaDeformation
  change
    (Limits.Sigma.desc (fun j =>
      deformationHom j ≫ TopPair.Hom.fst (TopPair.sigmaι P j)))
        (comparison.inv
          ((TopCat.prodIsoProd TopCat.I (∐ family)).inv
            (timeLift (t, Limits.Sigma.ι family i x)))) = _
  rw [htimeLift]
  rw [← hcomponentPoint]
  have hc := ConcreteCategory.congr_hom hcomparison componentPoint
  change comparison.inv
      (Limits.prod.map (𝟙 TopCat.I)
        (Limits.Sigma.ι family i) componentPoint) =
    Limits.Sigma.ι
      (fun j : ι => TopCat.I.{max v u} ⨯ family j) i componentPoint at hc
  rw [hc]
  rw [← ConcreteCategory.comp_apply, Limits.Sigma.ι_comp_desc]
  simp only [TopCat.comp_app]
  apply congrArg (TopPair.Hom.fst (TopPair.sigmaι P i))
  have hpoint :
      (TopCat.prodIsoProd TopCat.I (P i).fst).hom componentPoint =
        (TopCat.I.homeomorph.{max v u}.symm t, x) := by
    dsimp only [componentPoint]
    exact TopCat.inv_hom_id_apply
      (TopCat.prodIsoProd TopCat.I (P i).fst)
        (TopCat.I.homeomorph.{max v u}.symm t, x)
  dsimp only [deformationHom]
  change (d i).deformation
      (TopCat.I.homeomorph.{max v u}
        ((TopCat.prodIsoProd TopCat.I (P i).fst).hom componentPoint).1,
        ((TopCat.prodIsoProd TopCat.I (P i).fst).hom componentPoint).2) =
    (d i).deformation (t, x)
  rw [hpoint, TopCat.I.homeomorph.{max v u}.apply_symm_apply]

/-- Componentwise controlled NDR data on an explicit coproduct of
topological pairs. No nonempty-index hypothesis is required. -/
noncomputable def sigma :
    TopPair.NDRData (TopPair.sigma P) where
  control := sigmaControl (P := P) d
  endpoint := sigmaEndpoint (P := P) d
  deformation :=
    { toFun := sigmaDeformation (P := P) d
      map_zero_left := fun x => by
        obtain ⟨i, y, rfl⟩ := exists_eq_sigma_fst_ι (P := P) x
        rw [sigmaDeformation_ι]
        exact congrArg (TopPair.Hom.fst (TopPair.sigmaι P i))
          ((d i).deformation.apply_zero y)
      map_one_left := fun x => by
        obtain ⟨i, y, rfl⟩ := exists_eq_sigma_fst_ι (P := P) x
        rw [sigmaDeformation_ι, (d i).deformation.apply_one,
          sigmaEndpoint_ι]
      prop' := fun t x hx => by
        obtain ⟨i, a, rfl⟩ :=
          (mem_range_sigma_map_iff (P := P) x).mp hx
        change sigmaDeformation (P := P) d
          (t, TopPair.Hom.fst (TopPair.sigmaι P i) ((P i).map a)) =
            TopPair.Hom.fst (TopPair.sigmaι P i) ((P i).map a)
        rw [sigmaDeformation_ι]
        exact congrArg (TopPair.Hom.fst (TopPair.sigmaι P i))
          ((d i).deformation.eq_fst t ⟨a, rfl⟩) }
  control_eq_zero_iff := fun x => by
    obtain ⟨i, y, rfl⟩ := exists_eq_sigma_fst_ι (P := P) x
    constructor
    · intro h
      have hy : (d i).control y = 0 := by
        simpa only [sigmaControl_ι] using h
      obtain ⟨a, ha⟩ := ((d i).control_eq_zero_iff y).mp hy
      exact (mem_range_sigma_map_iff (P := P) _).mpr
        ⟨i, a, congrArg (TopPair.Hom.fst (TopPair.sigmaι P i)) ha.symm⟩
    · intro h
      obtain ⟨j, a, ha⟩ := (mem_range_sigma_map_iff (P := P) _).mp h
      change sigmaControl (P := P) d
        (TopPair.Hom.fst (TopPair.sigmaι P i) y) = 0
      rw [ha, sigmaControl_ι]
      exact ((d j).control_eq_zero_iff ((P j).map a)).mpr ⟨a, rfl⟩
  control_deformation_le := fun t x => by
    obtain ⟨i, y, rfl⟩ := exists_eq_sigma_fst_ι (P := P) x
    change sigmaControl (P := P) d
        (sigmaDeformation (P := P) d
          (t, TopPair.Hom.fst (TopPair.sigmaι P i) y)) ≤
      sigmaControl (P := P) d
        (TopPair.Hom.fst (TopPair.sigmaι P i) y)
    rw [sigmaDeformation_ι, sigmaControl_ι, sigmaControl_ι]
    exact (d i).control_deformation_le t y
  endpoint_mem_range := fun x hx => by
    obtain ⟨i, y, rfl⟩ := exists_eq_sigma_fst_ι (P := P) x
    have hy : (d i).control y < 1 := by
      simpa only [sigmaControl_ι] using hx
    obtain ⟨a, ha⟩ := (d i).endpoint_mem_range y hy
    apply (mem_range_sigma_map_iff (P := P) _).mpr
    exact ⟨i, a, (sigmaEndpoint_ι (P := P) d i y).trans
      (congrArg (TopPair.Hom.fst (TopPair.sigmaι P i)) ha.symm)⟩

end TopPair.NDRData

end
