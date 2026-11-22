/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Smash
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# One-point compactifications as pointed CGWH spaces

This file coreflects the one-point compactification of a locally compact
Hausdorff space into CGWH.  Proper maps extend over infinity, compact spaces
recover free basepoint addition, and one-point compactification carries
products to smash products.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Topology
open Filter TopologicalSpace

namespace PointedCGWH

/-- The one-point compactification, pointed at infinity, as a CGWH space. -/
noncomputable def onePointOf
    (X : Type v) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] : PointedCGWH.{u, v} := by
  let K : CompactlyGenerated.{u, v} :=
    TopCat.toCompactlyGenerated.obj (TopCat.of (OnePoint X))
  have hWeak : UWeakHausdorffSpace.{u} K := by
    refine ⟨fun L f => ?_⟩
    let c := CompactlyGenerated.adj.{u, v}.counit.app
      (TopCat.of (OnePoint X))
    let g : C(L, OnePoint X) :=
      ⟨fun k => c (f k), (ConcreteCategory.hom c).continuous.comp f.continuous⟩
    have hg : IsClosed (Set.range g) :=
      (isCompact_range g.continuous).isClosed
    have hp := hg.preimage (ConcreteCategory.hom c).continuous
    have hrange : (ConcreteCategory.hom c) ⁻¹' Set.range g = Set.range f := by
      ext x
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hcX := CompactlyGenerated.adjCounit_apply.{v, u}
          (TopCat.of (OnePoint X)) x
        have hcF := CompactlyGenerated.adjCounit_apply.{v, u}
          (TopCat.of (OnePoint X)) (f k)
        exact hcF.symm.trans (hk.trans hcX)
      · rintro ⟨k, rfl⟩
        exact ⟨k, rfl⟩
    rwa [hrange] at hp
  let R : CGWH.{u, v} :=
    { toCompactlyGenerated := K
      is_weakHausdorff := hWeak }
  exact Under.mk (ConcreteCategory.ofHom
    (show C(CGWH.point.{u, v}, R) from
      ⟨fun _ => OnePoint.infty, continuous_const⟩))

/-- An arrow from a generated one-point compactification is continuous in its raw topology. -/
def onePointArrowRaw {X : PointedCGWH.{u, v}} {Y : Type v}
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [UCompactlyGeneratedSpace.{u} (OnePoint Y)]
    (f : PointedCGWH.onePointOf.{u, v} Y ⟶ X) : C(OnePoint Y, X.right) := by
  let c := CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint Y)
  exact ⟨fun z => f.right (c.1.symm z),
    (ConcreteCategory.hom f.right).continuous.comp c.1.symm.continuous⟩

/-- The continuous arrow agrees with the based map at every compactification point. -/
theorem onePointArrowRaw_apply {X : PointedCGWH.{u, v}} {Y : Type v}
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [UCompactlyGeneratedSpace.{u} (OnePoint Y)]
    (f : PointedCGWH.onePointOf.{u, v} Y ⟶ X) (z : OnePoint Y) :
    onePointArrowRaw f z = f.right z := by
  let c := CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint Y)
  change f.right (c.1.symm z) = f.right z
  apply congrArg f.right
  exact (c.2 (c.1.symm z)).symm.trans (c.1.apply_symm_apply z)

/-- Based maps from an actual one-point compactification preserve its original infinity. -/
theorem mapOnePoint_infty {X : PointedCGWH.{u, v}} {Y : Type v}
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (f : PointedCGWH.onePointOf.{u, v} Y ⟶ X) :
    f.right (OnePoint.infty : OnePoint Y) = X.hom PUnit.unit :=
  ConcreteCategory.congr_hom (Under.w f) PUnit.unit

/-- A proper continuous map extends over the point at infinity. -/
noncomputable def onePointMapOfProper
    {X Y : Type v}
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (f : ContinuousMap X Y)
    (hf : Tendsto f (coclosedCompact X) (coclosedCompact Y)) :
    onePointOf.{u, v} X ⟶ onePointOf.{u, v} Y := by
  let m : (onePointOf.{u, v} X).right ⟶
      (onePointOf.{u, v} Y).right :=
    CGWH.fullyFaithfulCgwhToCompactlyGenerated.preimage
      (TopCat.toCompactlyGenerated.map
        (TopCat.ofHom
          ⟨OnePoint.map f, OnePoint.continuous_map f.continuous hf⟩))
  exact Under.homMk m (by
    apply ConcreteCategory.hom_ext
    intro p
    change OnePoint.map f OnePoint.infty = OnePoint.infty
    exact OnePoint.map_infty f)

/-- A proper extension fixes infinity. -/
theorem onePointMapOfProper_infty
    {X Y : Type v}
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (f : ContinuousMap X Y)
    (hf : Tendsto f (coclosedCompact X) (coclosedCompact Y)) :
    (onePointMapOfProper.{u, v} f hf).right OnePoint.infty =
      OnePoint.infty := by
  rfl

/-- A proper extension agrees with the original map on finite points. -/
theorem onePointMapOfProper_coe
    {X Y : Type v}
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (f : ContinuousMap X Y)
    (hf : Tendsto f (coclosedCompact X) (coclosedCompact Y))
    (x : X) :
    (onePointMapOfProper.{u, v} f hf).right (x : OnePoint X) =
      (f x : OnePoint Y) := by
  rfl

/-- A homeomorphism extends to an isomorphism of pointed one-point
compactifications. -/
noncomputable def onePointHomeomorphOfHomeomorph
    {X Y : Type v}
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (e : X ≃ₜ Y) :
    onePointOf.{u, v} X ≅ onePointOf.{u, v} Y := by
  let f : C(X, Y) := ⟨e, e.continuous⟩
  let g : C(Y, X) := ⟨e.symm, e.symm.continuous⟩
  let hf : Tendsto f (coclosedCompact X) (coclosedCompact Y) :=
    e.map_coclosedCompact.le
  let hg : Tendsto g (coclosedCompact Y) (coclosedCompact X) :=
    e.symm.map_coclosedCompact.le
  exact
    { hom := onePointMapOfProper f hf
      inv := onePointMapOfProper g hg
      hom_inv_id := by
        apply Under.UnderMorphism.ext
        apply ConcreteCategory.hom_ext
        intro z
        simp only [Under.comp_right, ConcreteCategory.comp_apply,
          Under.id_right, ConcreteCategory.id_apply]
        induction z using OnePoint.rec with
        | infty =>
            rw [onePointMapOfProper_infty, onePointMapOfProper_infty]
        | coe x =>
            rw [onePointMapOfProper_coe, onePointMapOfProper_coe]
            exact congrArg ((↑) : X → OnePoint X) (e.symm_apply_apply x)
      inv_hom_id := by
        apply Under.UnderMorphism.ext
        apply ConcreteCategory.hom_ext
        intro z
        simp only [Under.comp_right, ConcreteCategory.comp_apply,
          Under.id_right, ConcreteCategory.id_apply]
        induction z using OnePoint.rec with
        | infty =>
            rw [onePointMapOfProper_infty, onePointMapOfProper_infty]
        | coe y =>
            rw [onePointMapOfProper_coe, onePointMapOfProper_coe]
            exact congrArg ((↑) : Y → OnePoint Y) (e.apply_symm_apply y) }


/-- Collapse either infinite product coordinate to infinity in the product compactification. -/
def rawCollapse (X Y : Type v) :
    OnePoint X × OnePoint Y → OnePoint (X × Y) :=
  fun p => p.1.elim OnePoint.infty
    (fun x => p.2.elim OnePoint.infty
      (fun y => ((x, y) : OnePoint (X × Y))))

/-- Joint continuity of the product collapse map. -/
theorem rawCollapse_continuous
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y] :
    Continuous (rawCollapse X Y) := by
  let e : X × Y → OnePoint X × OnePoint Y :=
    fun p => ((p.1 : OnePoint X), (p.2 : OnePoint Y))
  have he : IsOpenEmbedding e :=
    OnePoint.isOpenEmbedding_coe.prodMap OnePoint.isOpenEmbedding_coe
  rw [continuous_def]
  intro s hs
  by_cases hInf : OnePoint.infty ∈ s
  · have hs' := (OnePoint.isOpen_iff_of_mem hInf).mp hs
    let K : Set (X × Y) :=
      (((↑) : X × Y → OnePoint (X × Y)) ⁻¹' s)ᶜ
    have hK : IsCompact K := hs'.2
    have hpre : (rawCollapse X Y ⁻¹' s)ᶜ = e '' K := by
      ext p
      rcases p with ⟨a, b⟩
      induction a using OnePoint.rec with
      | infty => simp [rawCollapse, hInf, e]
      | coe x =>
          induction b using OnePoint.rec with
          | infty => simp [rawCollapse, hInf, e]
          | coe y =>
              simp [rawCollapse, e, K]
    rw [← isClosed_compl_iff, hpre]
    exact (hK.image he.continuous).isClosed
  · have hpre : rawCollapse X Y ⁻¹' s =
        e '' (((↑) : X × Y → OnePoint (X × Y)) ⁻¹' s) := by
      ext p
      rcases p with ⟨a, b⟩
      induction a using OnePoint.rec with
      | infty => simp [rawCollapse, hInf, e]
      | coe x =>
          induction b using OnePoint.rec with
          | infty => simp [rawCollapse, hInf, e]
          | coe y =>
              simp [rawCollapse, e]
    rw [hpre]
    exact he.isOpenMap _ (hs.preimage OnePoint.continuous_coe)

/-- Compact generation of the one-point compactification of the product. -/
theorem onePointProduct_generated
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y)) :
    UCompactlyGeneratedSpace.{u} (OnePoint (X × Y)) := by
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint X) := hX
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint Y) := hY
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint X × OnePoint Y) :=
    uCompactlyGeneratedSpace_prod_of_locallyCompact_left
  have hsurj : Function.Surjective (rawCollapse X Y) := by
    intro z
    induction z using OnePoint.rec with
    | infty => exact ⟨(OnePoint.infty, OnePoint.infty), rfl⟩
    | coe p =>
        exact ⟨((p.1 : OnePoint X), (p.2 : OnePoint Y)), rfl⟩
  have hquot : IsQuotientMap (rawCollapse X Y) :=
    IsQuotientMap.of_surjective_continuous hsurj
      (rawCollapse_continuous X Y)
  exact uCompactlyGeneratedSpace_of_coinduced
    (rawCollapse_continuous X Y) hquot.eq_coinduced

/-- The product compactification as the collapse quotient, with infinity and finite point
formulas. -/
noncomputable def rawProdSmashHomeomorphData
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y] :
    let R : Setoid (OnePoint X × OnePoint Y) :=
      Setoid.ker (rawCollapse X Y)
    { e : OnePoint (X × Y) ≃ₜ Quotient R //
      e OnePoint.infty = Quotient.mk R
          (OnePoint.infty, OnePoint.infty) ∧
        ∀ (x : X) (y : Y),
          e ((x, y) : OnePoint (X × Y)) =
            Quotient.mk R ((x : OnePoint X), (y : OnePoint Y)) } := by
  let R : Setoid (OnePoint X × OnePoint Y) :=
    Setoid.ker (rawCollapse X Y)
  let bar : Quotient R → OnePoint (X × Y) :=
    Quotient.lift (rawCollapse X Y) (fun _ _ h => h)
  have hbar : Continuous bar :=
    Continuous.quotient_lift (rawCollapse_continuous X Y)
      (fun _ _ h => h)
  have hsurj : Function.Surjective bar := by
    intro z
    induction z using OnePoint.rec with
    | infty =>
        exact ⟨Quotient.mk' (OnePoint.infty, OnePoint.infty), rfl⟩
    | coe p =>
        exact ⟨Quotient.mk'
          ((p.1 : OnePoint X), (p.2 : OnePoint Y)), rfl⟩
  have hinj : Function.Injective bar := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | _ p =>
        induction b using Quotient.inductionOn with
        | _ q =>
            exact Quotient.sound hab
  let e : Quotient R ≃ OnePoint (X × Y) :=
    Equiv.ofBijective bar ⟨hinj, hsurj⟩
  let h := (Continuous.homeoOfEquivCompactToT2 (f := e) hbar).symm
  refine ⟨h, ?_, ?_⟩
  · apply h.symm.injective
    rw [h.symm_apply_apply]
    rfl
  · intro x y
    apply h.symm.injective
    rw [h.symm_apply_apply]
    rfl

/-- The native CGWH product compared with the product of the underlying compactifications. -/
noncomputable def nativeOnePointProductHomeo
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y)) :
    ((onePointOf.{u, v} X).right ⊗
        (onePointOf.{u, v} Y).right : CGWH.{u, v}) ≃ₜ
      OnePoint X × OnePoint Y := by
  letI : UCompactlyGeneratedSpace.{u} (OnePoint X) := hX
  letI : UCompactlyGeneratedSpace.{u} (OnePoint Y) := hY
  letI : UCompactlyGeneratedSpace.{u} (OnePoint X × OnePoint Y) :=
    uCompactlyGeneratedSpace_prod_of_locallyCompact_left
  let cX := (CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint X)).1
  let cY := (CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint Y)).1
  letI : LocallyCompactSpace (onePointOf.{u, v} X).right :=
    (cX.locallyCompactSpace_iff).2 inferInstance
  letI : T2Space (onePointOf.{u, v} X).right :=
    cX.isEmbedding.t2Space
  let p := CGWH.prodComparisonToTop
    (onePointOf.{u, v} X).right (onePointOf.{u, v} Y).right
  let hp := CGWH.prodComparisonToTop_isHomeomorph_of_locallyCompact_left
    (onePointOf.{u, v} X).right (onePointOf.{u, v} Y).right
  exact (hp.homeomorph p).trans (cX.prodCongr cY)

/-- The native product comparison sends the left basepoint axis to an infinite second coordinate. -/
theorem nativeOnePointProductHomeo_leftAxis
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y))
    (x : (onePointOf.{u, v} X).right) :
    nativeOnePointProductHomeo.{u, v} X Y hX hY
        (CartesianMonoidalCategory.lift
          (𝟙 (onePointOf.{u, v} X).right)
          (CGWH.point_isTerminal.from (onePointOf.{u, v} X).right ≫
            (onePointOf.{u, v} Y).hom) x) =
      (x, OnePoint.infty) := by
  rw [show nativeOnePointProductHomeo.{u, v} X Y hX hY
      (CartesianMonoidalCategory.lift
        (𝟙 (onePointOf.{u, v} X).right)
        (CGWH.point_isTerminal.from (onePointOf.{u, v} X).right ≫
          (onePointOf.{u, v} Y).hom) x) =
      CGWH.prodComparisonToTop
        (onePointOf.{u, v} X).right (onePointOf.{u, v} Y).right
        (CartesianMonoidalCategory.lift
          (𝟙 (onePointOf.{u, v} X).right)
          (CGWH.point_isTerminal.from (onePointOf.{u, v} X).right ≫
            (onePointOf.{u, v} Y).hom) x) by
    apply Prod.ext
    · exact (CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint X)).2 _
    · exact (CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint Y)).2 _]
  apply Prod.ext
  · have hfst := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_fst
        (onePointOf.{u, v} X).right (onePointOf.{u, v} Y).right)
      (CartesianMonoidalCategory.lift
        (𝟙 (onePointOf.{u, v} X).right)
        (CGWH.point_isTerminal.from (onePointOf.{u, v} X).right ≫
          (onePointOf.{u, v} Y).hom) x)
    change (CGWH.prodComparisonToTop
        (onePointOf.{u, v} X).right
        (onePointOf.{u, v} Y).right _).1 =
      (Limits.prod.fst :
        (onePointOf.{u, v} X).right ⨯
          (onePointOf.{u, v} Y).right ⟶
        (onePointOf.{u, v} X).right) _ at hfst
    have hlift := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst
        (𝟙 (onePointOf.{u, v} X).right)
        (CGWH.point_isTerminal.from (onePointOf.{u, v} X).right ≫
          (onePointOf.{u, v} Y).hom)) x
    rw [ConcreteCategory.comp_apply] at hlift
    exact hfst.trans hlift
  · have hsnd := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_snd
        (onePointOf.{u, v} X).right (onePointOf.{u, v} Y).right)
      (CartesianMonoidalCategory.lift
        (𝟙 (onePointOf.{u, v} X).right)
        (CGWH.point_isTerminal.from (onePointOf.{u, v} X).right ≫
          (onePointOf.{u, v} Y).hom) x)
    change (CGWH.prodComparisonToTop
        (onePointOf.{u, v} X).right
        (onePointOf.{u, v} Y).right _).2 =
      (Limits.prod.snd :
        (onePointOf.{u, v} X).right ⨯
          (onePointOf.{u, v} Y).right ⟶
        (onePointOf.{u, v} Y).right) _ at hsnd
    have hlift := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd
        (𝟙 (onePointOf.{u, v} X).right)
        (CGWH.point_isTerminal.from (onePointOf.{u, v} X).right ≫
          (onePointOf.{u, v} Y).hom)) x
    rw [ConcreteCategory.comp_apply] at hlift
    exact hsnd.trans (hlift.trans rfl)

/-- The native product comparison sends the right basepoint axis to an infinite first coordinate. -/
theorem nativeOnePointProductHomeo_rightAxis
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y))
    (y : (onePointOf.{u, v} Y).right) :
    nativeOnePointProductHomeo.{u, v} X Y hX hY
        (CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from (onePointOf.{u, v} Y).right ≫
            (onePointOf.{u, v} X).hom)
          (𝟙 (onePointOf.{u, v} Y).right) y) =
      (OnePoint.infty, y) := by
  rw [show nativeOnePointProductHomeo.{u, v} X Y hX hY
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from (onePointOf.{u, v} Y).right ≫
          (onePointOf.{u, v} X).hom)
        (𝟙 (onePointOf.{u, v} Y).right) y) =
      CGWH.prodComparisonToTop
        (onePointOf.{u, v} X).right (onePointOf.{u, v} Y).right
        (CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from (onePointOf.{u, v} Y).right ≫
            (onePointOf.{u, v} X).hom)
          (𝟙 (onePointOf.{u, v} Y).right) y) by
    apply Prod.ext
    · exact (CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint X)).2 _
    · exact (CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint Y)).2 _]
  apply Prod.ext
  · have hfst := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_fst
        (onePointOf.{u, v} X).right (onePointOf.{u, v} Y).right)
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from (onePointOf.{u, v} Y).right ≫
          (onePointOf.{u, v} X).hom)
        (𝟙 (onePointOf.{u, v} Y).right) y)
    change (CGWH.prodComparisonToTop
        (onePointOf.{u, v} X).right
        (onePointOf.{u, v} Y).right _).1 =
      (Limits.prod.fst :
        (onePointOf.{u, v} X).right ⨯
          (onePointOf.{u, v} Y).right ⟶
        (onePointOf.{u, v} X).right) _ at hfst
    have hlift := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst
        (CGWH.point_isTerminal.from (onePointOf.{u, v} Y).right ≫
          (onePointOf.{u, v} X).hom)
        (𝟙 (onePointOf.{u, v} Y).right)) y
    rw [ConcreteCategory.comp_apply] at hlift
    exact hfst.trans (hlift.trans rfl)
  · have hsnd := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_snd
        (onePointOf.{u, v} X).right (onePointOf.{u, v} Y).right)
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from (onePointOf.{u, v} Y).right ≫
          (onePointOf.{u, v} X).hom)
        (𝟙 (onePointOf.{u, v} Y).right) y)
    change (CGWH.prodComparisonToTop
        (onePointOf.{u, v} X).right
        (onePointOf.{u, v} Y).right _).2 =
      (Limits.prod.snd :
        (onePointOf.{u, v} X).right ⨯
          (onePointOf.{u, v} Y).right ⟶
        (onePointOf.{u, v} Y).right) _ at hsnd
    have hlift := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd
        (CGWH.point_isTerminal.from (onePointOf.{u, v} Y).right ≫
          (onePointOf.{u, v} X).hom)
        (𝟙 (onePointOf.{u, v} Y).right)) y
    rw [ConcreteCategory.comp_apply] at hlift
    exact hsnd.trans hlift

/-- The collapse quotient as a compactly generated weak Hausdorff space. -/
noncomputable abbrev rawQuotientCGWH
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y)) : CGWH.{u, v} := by
  letI : UCompactlyGeneratedSpace.{u} (OnePoint X) := hX
  letI : UCompactlyGeneratedSpace.{u} (OnePoint Y) := hY
  letI : UCompactlyGeneratedSpace.{u} (OnePoint X × OnePoint Y) :=
    uCompactlyGeneratedSpace_prod_of_locallyCompact_left
  let R : Setoid (OnePoint X × OnePoint Y) :=
    Setoid.ker (rawCollapse X Y)
  let e := (rawProdSmashHomeomorphData X Y).1
  letI : T2Space (Quotient R) := e.symm.isEmbedding.t2Space
  exact CGWH.of (Quotient R)

/-- The underlying carrier equivalence of the native collapse quotient. -/
noncomputable def rawQuotientEquiv
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y)) :
    let R : Setoid (OnePoint X × OnePoint Y) :=
      Setoid.ker (rawCollapse X Y)
    (rawQuotientCGWH.{u, v} X Y hX hY : Type v) ≃ Quotient R := by
  unfold rawQuotientCGWH
  exact Equiv.refl _

/-- Map native smash to the collapse quotient, with generator and distinguished-point formulas. -/
noncomputable def smashToRawQuotientData
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y)) :
    let R : Setoid (OnePoint X × OnePoint Y) :=
      Setoid.ker (rawCollapse X Y)
    let p := CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal
      (onePointOf.{u, v} X) (onePointOf.{u, v} Y)
    { m : (onePointOf.{u, v} X ⊗ onePointOf.{u, v} Y).right ⟶
        rawQuotientCGWH.{u, v} X Y hX hY //
      (∀ z,
        rawQuotientEquiv.{u, v} X Y hX hY (m (p.2.1.inl z)) =
          Quotient.mk R (nativeOnePointProductHomeo X Y hX hY z)) ∧
      ∀ t, rawQuotientEquiv.{u, v} X Y hX hY (m (p.2.1.inr t)) =
        Quotient.mk R (OnePoint.infty, OnePoint.infty) } := by
  letI : UCompactlyGeneratedSpace.{u} (OnePoint X) := hX
  letI : UCompactlyGeneratedSpace.{u} (OnePoint Y) := hY
  letI : UCompactlyGeneratedSpace.{u} (OnePoint X × OnePoint Y) :=
    uCompactlyGeneratedSpace_prod_of_locallyCompact_left
  let R : Setoid (OnePoint X × OnePoint Y) :=
    Setoid.ker (rawCollapse X Y)
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal A B
  let n := nativeOnePointProductHomeo X Y hX hY
  let prodToQ : A.right ⊗ B.right ⟶
      rawQuotientCGWH.{u, v} X Y hX hY := by
    unfold rawQuotientCGWH
    exact ConcreteCategory.ofHom
      ⟨fun z => Quotient.mk R (n z),
        continuous_quotient_mk'.comp n.continuous⟩
  let pointToQ : CGWH.point.{u, v} ⟶
      rawQuotientCGWH.{u, v} X Y hX hY := by
    unfold rawQuotientCGWH
    exact ConcreteCategory.ofHom
      ⟨fun _ => Quotient.mk R (OnePoint.infty, OnePoint.infty),
        continuous_const⟩
  have hLeft : pushout.inl A.hom B.hom ≫ p.1.right =
      CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom) := by
    change pushout.inl A.hom B.hom ≫ pushout.desc
      (CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom))
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom) (𝟙 B.right)) _ = _
    exact pushout.inl_desc _ _ _
  have hRight : pushout.inr A.hom B.hom ≫ p.1.right =
      CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom) (𝟙 B.right) := by
    change pushout.inr A.hom B.hom ≫ pushout.desc
      (CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom))
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom) (𝟙 B.right)) _ = _
    exact pushout.inr_desc _ _ _
  have hTermLeft : pushout.inl A.hom B.hom ≫
      CGWH.point_isTerminal.from
        (((CategoryTheory.Pointed.wedge CGWH.point).obj A).obj B).right =
      CGWH.point_isTerminal.from A.right :=
    CGWH.point_isTerminal.hom_ext _ _
  have hTermRight : pushout.inr A.hom B.hom ≫
      CGWH.point_isTerminal.from
        (((CategoryTheory.Pointed.wedge CGWH.point).obj A).obj B).right =
      CGWH.point_isTerminal.from B.right :=
    CGWH.point_isTerminal.hom_ext _ _
  let wedgeObj : CGWH.{u, v} :=
    (((CategoryTheory.Pointed.wedge CGWH.point).obj A).obj B).right
  let wedgeMap : wedgeObj ⟶ A.right ⊗ B.right := p.1.right
  let wedgeTerminal : wedgeObj ⟶ CGWH.point.{u, v} :=
    CGWH.point_isTerminal.from wedgeObj
  let leftLeg : A.right ⟶ wedgeObj := pushout.inl A.hom B.hom
  let rightLeg : B.right ⟶ wedgeObj := pushout.inr A.hom B.hom
  have hLeftTyped : leftLeg ≫ wedgeMap =
      CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom) := hLeft
  have hRightTyped : rightLeg ≫ wedgeMap =
      CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom) (𝟙 B.right) := hRight
  have hTermLeftTyped : leftLeg ≫ wedgeTerminal =
      CGWH.point_isTerminal.from A.right := hTermLeft
  have hTermRightTyped : rightLeg ≫ wedgeTerminal =
      CGWH.point_isTerminal.from B.right := hTermRight
  have hWedge : p.1.right ≫ prodToQ =
      CGWH.point_isTerminal.from
        (((CategoryTheory.Pointed.wedge CGWH.point).obj A).obj B).right ≫
          pointToQ := by
    apply pushout.hom_ext
    · change leftLeg ≫ (wedgeMap ≫ prodToQ) =
        leftLeg ≫ (wedgeTerminal ≫ pointToQ)
      rw [← Category.assoc, hLeftTyped, ← Category.assoc, hTermLeftTyped]
      apply ConcreteCategory.hom_ext
      intro x
      dsimp only [prodToQ, pointToQ]
      unfold rawQuotientCGWH
      let z : ((onePointOf.{u, v} X).right ⊗
          (onePointOf.{u, v} Y).right : CGWH.{u, v}) :=
        CartesianMonoidalCategory.lift (𝟙 A.right)
          (CGWH.point_isTerminal.from A.right ≫ B.hom) x
      change Quotient.mk R (n z) =
        Quotient.mk R (OnePoint.infty, OnePoint.infty)
      apply Quotient.sound
      change rawCollapse X Y (n z) =
        OnePoint.infty
      rw [show n z = (x, OnePoint.infty) by
        exact nativeOnePointProductHomeo_leftAxis X Y hX hY x]
      induction x using OnePoint.rec <;> rfl
    · change rightLeg ≫ (wedgeMap ≫ prodToQ) =
        rightLeg ≫ (wedgeTerminal ≫ pointToQ)
      rw [← Category.assoc, hRightTyped, ← Category.assoc, hTermRightTyped]
      apply ConcreteCategory.hom_ext
      intro y
      dsimp only [prodToQ, pointToQ]
      unfold rawQuotientCGWH
      let z : ((onePointOf.{u, v} X).right ⊗
          (onePointOf.{u, v} Y).right : CGWH.{u, v}) :=
        CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from B.right ≫ A.hom)
          (𝟙 B.right) y
      change Quotient.mk R (n z) =
        Quotient.mk R (OnePoint.infty, OnePoint.infty)
      apply Quotient.sound
      change rawCollapse X Y (n z) =
        OnePoint.infty
      rw [show n z = (OnePoint.infty, y) by
        exact nativeOnePointProductHomeo_rightAxis X Y hX hY y]
      rfl
  let m := PushoutCocone.IsColimit.desc p.2.2 prodToQ pointToQ hWedge
  refine ⟨m, ?_, ?_⟩
  · intro z
    have hz := ConcreteCategory.congr_hom
      (PushoutCocone.IsColimit.inl_desc p.2.2 prodToQ pointToQ hWedge) z
    rw [ConcreteCategory.comp_apply] at hz
    change rawQuotientEquiv.{u, v} X Y hX hY (m (p.2.1.inl z)) = _
    rw [hz]
    dsimp only [prodToQ]
    unfold rawQuotientEquiv rawQuotientCGWH
    rfl
  · intro t
    have ht := ConcreteCategory.congr_hom
      (PushoutCocone.IsColimit.inr_desc p.2.2 prodToQ pointToQ hWedge) t
    rw [ConcreteCategory.comp_apply] at ht
    change rawQuotientEquiv.{u, v} X Y hX hY (m (p.2.1.inr t)) = _
    rw [ht]
    dsimp only [pointToQ]
    unfold rawQuotientEquiv rawQuotientCGWH
    rfl

/-- Map the collapse quotient to native smash, with its generator formula. -/
noncomputable def rawQuotientToSmashData
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y)) :
    let R : Setoid (OnePoint X × OnePoint Y) :=
      Setoid.ker (rawCollapse X Y)
    let q := (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal
      (onePointOf.{u, v} X) (onePointOf.{u, v} Y)).2.1.inl
    { m : rawQuotientCGWH.{u, v} X Y hX hY ⟶
        (onePointOf.{u, v} X ⊗ onePointOf.{u, v} Y).right //
      ∀ a, m ((rawQuotientEquiv.{u, v} X Y hX hY).symm
        (Quotient.mk R a)) =
          q ((nativeOnePointProductHomeo X Y hX hY).symm a) } := by
  letI : UCompactlyGeneratedSpace.{u} (OnePoint X) := hX
  letI : UCompactlyGeneratedSpace.{u} (OnePoint Y) := hY
  letI : UCompactlyGeneratedSpace.{u} (OnePoint X × OnePoint Y) :=
    uCompactlyGeneratedSpace_prod_of_locallyCompact_left
  let R : Setoid (OnePoint X × OnePoint Y) :=
    Setoid.ker (rawCollapse X Y)
  let rawHomeo := (rawProdSmashHomeomorphData X Y).1
  letI : T2Space (Quotient R) := rawHomeo.symm.isEmbedding.t2Space
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal A B
  let q : A.right ⊗ B.right ⟶ (A ⊗ B).right := p.2.1.inl
  let n := nativeOnePointProductHomeo X Y hX hY
  have hLeft : pushout.inl A.hom B.hom ≫ p.1.right =
      CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom) := by
    change pushout.inl A.hom B.hom ≫ pushout.desc
      (CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom))
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom) (𝟙 B.right)) _ = _
    exact pushout.inl_desc _ _ _
  have hRight : pushout.inr A.hom B.hom ≫ p.1.right =
      CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom) (𝟙 B.right) := by
    change pushout.inr A.hom B.hom ≫ pushout.desc
      (CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom))
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom) (𝟙 B.right)) _ = _
    exact pushout.inr_desc _ _ _
  have hkernel (a b : OnePoint X × OnePoint Y) :
      rawCollapse X Y a = rawCollapse X Y b ↔
        a = b ∨
          ((a.1 = OnePoint.infty ∨ a.2 = OnePoint.infty) ∧
            (b.1 = OnePoint.infty ∨ b.2 = OnePoint.infty)) := by
    rcases a with ⟨a₁, a₂⟩
    rcases b with ⟨b₁, b₂⟩
    induction a₁ using OnePoint.rec <;>
      induction a₂ using OnePoint.rec <;>
      induction b₁ using OnePoint.rec <;>
      induction b₂ using OnePoint.rec <;>
      simp [rawCollapse, Prod.ext_iff]
  have hmem (a : OnePoint X × OnePoint Y)
      (ha : a.1 = OnePoint.infty ∨ a.2 = OnePoint.infty) :
      n.symm a ∈ Set.range (ConcreteCategory.hom
        ((forget TopCat).map (CGWH.cgwhToTop.map p.1.right))) := by
    rcases a with ⟨a₁, a₂⟩
    rcases ha with ha | ha
    · change a₁ = OnePoint.infty at ha
      subst a₁
      refine ⟨pushout.inr A.hom B.hom a₂, ?_⟩
      change p.1.right (pushout.inr A.hom B.hom a₂) =
        n.symm (OnePoint.infty, a₂)
      apply n.injective
      rw [n.apply_symm_apply]
      rw [show p.1.right (pushout.inr A.hom B.hom a₂) =
          CartesianMonoidalCategory.lift
            (CGWH.point_isTerminal.from B.right ≫ A.hom)
            (𝟙 B.right) a₂ by
        exact ConcreteCategory.congr_hom hRight a₂]
      exact nativeOnePointProductHomeo_rightAxis X Y hX hY a₂
    · change a₂ = OnePoint.infty at ha
      subst a₂
      refine ⟨pushout.inl A.hom B.hom a₁, ?_⟩
      change p.1.right (pushout.inl A.hom B.hom a₁) =
        n.symm (a₁, OnePoint.infty)
      apply n.injective
      rw [n.apply_symm_apply]
      rw [show p.1.right (pushout.inl A.hom B.hom a₁) =
          CartesianMonoidalCategory.lift (𝟙 A.right)
            (CGWH.point_isTerminal.from A.right ≫ B.hom) a₁ by
        exact ConcreteCategory.congr_hom hLeft a₁]
      exact nativeOnePointProductHomeo_leftAxis X Y hX hY a₁
  let descend : Quotient R → (A ⊗ B).right :=
    Quotient.lift (fun a => q (n.symm a)) (by
      intro a b hab
      apply (smashQuotient_eq_iff A B (n.symm a) (n.symm b)).2
      rcases (hkernel a b).mp hab with hab | hab
      · exact Or.inl (congrArg n.symm hab)
      · exact Or.inr ⟨hmem a hab.1, hmem b hab.2⟩)
  have hdescend : Continuous descend :=
    Continuous.quotient_lift
      ((ConcreteCategory.hom q).continuous.comp n.symm.continuous) (by
        intro a b hab
        apply (smashQuotient_eq_iff A B (n.symm a) (n.symm b)).2
        rcases (hkernel a b).mp hab with hab | hab
        · exact Or.inl (congrArg n.symm hab)
        · exact Or.inr ⟨hmem a hab.1, hmem b hab.2⟩)
  let m : rawQuotientCGWH.{u, v} X Y hX hY ⟶ (A ⊗ B).right := by
    unfold rawQuotientCGWH
    exact ConcreteCategory.ofHom ⟨descend, hdescend⟩
  refine ⟨m, ?_⟩
  intro a
  unfold rawQuotientEquiv
  rfl

/-- The native CGWH smash quotient is isomorphic to the collapse quotient. -/
noncomputable def smashRawQuotientIso
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y)) :
    (onePointOf.{u, v} X ⊗ onePointOf.{u, v} Y).right ≅
      rawQuotientCGWH.{u, v} X Y hX hY := by
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal A B
  let q : A.right ⊗ B.right ⟶ (A ⊗ B).right := p.2.1.inl
  let n := nativeOnePointProductHomeo X Y hX hY
  let eQ := rawQuotientEquiv.{u, v} X Y hX hY
  let R : Setoid (OnePoint X × OnePoint Y) :=
    Setoid.ker (rawCollapse X Y)
  exact
    { hom := (smashToRawQuotientData X Y hX hY).1
      inv := (rawQuotientToSmashData X Y hX hY).1
      hom_inv_id := by
        change (show p.2.1.pt ⟶ p.2.1.pt from
          (smashToRawQuotientData X Y hX hY).1 ≫
            (rawQuotientToSmashData X Y hX hY).1) = 𝟙 p.2.1.pt
        apply PushoutCocone.IsColimit.hom_ext p.2.2
        · apply ConcreteCategory.hom_ext
          intro z
          change (rawQuotientToSmashData.{u, v} X Y hX hY).1
              ((smashToRawQuotientData.{u, v} X Y hX hY).1 (q z)) = q z
          have hto := (smashToRawQuotientData X Y hX hY).2.1 z
          have harg : (smashToRawQuotientData.{u, v} X Y hX hY).1 (q z) =
              eQ.symm (Quotient.mk R (n z)) := by
            apply eQ.injective
            rw [eQ.apply_symm_apply]
            exact hto
          rw [harg, (rawQuotientToSmashData X Y hX hY).2,
            n.symm_apply_apply]
          rfl
        · apply ConcreteCategory.hom_ext
          intro t
          change (rawQuotientToSmashData.{u, v} X Y hX hY).1
              ((smashToRawQuotientData.{u, v} X Y hX hY).1
                (p.2.1.inr t)) = p.2.1.inr t
          have hpt := (smashToRawQuotientData X Y hX hY).2.2 t
          have harg : (smashToRawQuotientData.{u, v} X Y hX hY).1
                (p.2.1.inr t) =
              eQ.symm (Quotient.mk R
                (OnePoint.infty, OnePoint.infty)) := by
            apply eQ.injective
            rw [eQ.apply_symm_apply]
            exact hpt
          rw [harg, (rawQuotientToSmashData X Y hX hY).2]
          have hn : n.symm (OnePoint.infty, OnePoint.infty) =
              CartesianMonoidalCategory.lift (𝟙 A.right)
                (CGWH.point_isTerminal.from A.right ≫ B.hom)
                OnePoint.infty := by
            apply n.injective
            rw [n.apply_symm_apply]
            exact (nativeOnePointProductHomeo_leftAxis
              X Y hX hY OnePoint.infty).symm
          rw [hn]
          have hLeft : pushout.inl A.hom B.hom ≫ p.1.right =
              CartesianMonoidalCategory.lift (𝟙 A.right)
                (CGWH.point_isTerminal.from A.right ≫ B.hom) := by
            change pushout.inl A.hom B.hom ≫ pushout.desc
              (CartesianMonoidalCategory.lift (𝟙 A.right)
                (CGWH.point_isTerminal.from A.right ≫ B.hom))
              (CartesianMonoidalCategory.lift
                (CGWH.point_isTerminal.from B.right ≫ A.hom)
                (𝟙 B.right)) _ = _
            exact pushout.inl_desc _ _ _
          let wedgeObj : CGWH.{u, v} :=
            (((CategoryTheory.Pointed.wedge CGWH.point).obj A).obj B).right
          let leg : A.right ⟶ wedgeObj := pushout.inl A.hom B.hom
          let wedgeMap : wedgeObj ⟶ A.right ⊗ B.right := p.1.right
          let wedgeTerminal : wedgeObj ⟶ CGWH.point.{u, v} :=
            CGWH.point_isTerminal.from wedgeObj
          have hc := ConcreteCategory.congr_hom p.2.1.condition (leg OnePoint.infty)
          change p.2.1.inl (wedgeMap (leg OnePoint.infty)) =
            p.2.1.inr (wedgeTerminal (leg OnePoint.infty)) at hc
          have hLegPoint : wedgeMap (leg OnePoint.infty) =
            CartesianMonoidalCategory.lift (𝟙 A.right)
              (CGWH.point_isTerminal.from A.right ≫ B.hom) OnePoint.infty :=
            ConcreteCategory.congr_hom hLeft OnePoint.infty
          rw [hLegPoint] at hc
          have hterminal :
              CGWH.point_isTerminal.from
                (((CategoryTheory.Pointed.wedge CGWH.point).obj A).obj B).right
                (pushout.inl A.hom B.hom OnePoint.infty) = t :=
            by
              change PUnit.unit = t
              cases t
              rfl
          change q (CartesianMonoidalCategory.lift (𝟙 A.right)
              (CGWH.point_isTerminal.from A.right ≫ B.hom)
              OnePoint.infty) = p.2.1.inr t
          exact hc.trans (congrArg p.2.1.inr hterminal)
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro a
        simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply]
        apply eQ.injective
        rw [show a = eQ.symm (eQ a) by
          exact (eQ.symm_apply_apply a).symm]
        generalize hqa : eQ a = qa
        induction qa using Quotient.inductionOn with
        | _ b =>
            rw [(rawQuotientToSmashData X Y hX hY).2,
              (smashToRawQuotientData X Y hX hY).2.1,
              n.apply_symm_apply, eQ.apply_symm_apply] }

/-- The underlying product-compactification to smash isomorphism, with its point formulas. -/
noncomputable def onePointProdSmashRightIsoData
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y)) :
    let q := (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal
      (onePointOf.{u, v} X) (onePointOf.{u, v} Y)).2.1.inl
    { e : (onePointOf.{u, v} (X × Y)).right ≅
        (onePointOf.{u, v} X ⊗ onePointOf.{u, v} Y).right //
      e.hom OnePoint.infty =
          q ((nativeOnePointProductHomeo X Y hX hY).symm
            (OnePoint.infty, OnePoint.infty)) ∧
        ∀ (x : X) (y : Y),
          e.hom ((x, y) : OnePoint (X × Y)) =
            q ((nativeOnePointProductHomeo X Y hX hY).symm
              ((x : OnePoint X), (y : OnePoint Y))) } := by
  letI : UCompactlyGeneratedSpace.{u} (OnePoint X) := hX
  letI : UCompactlyGeneratedSpace.{u} (OnePoint Y) := hY
  letI : UCompactlyGeneratedSpace.{u} (OnePoint X × OnePoint Y) :=
    uCompactlyGeneratedSpace_prod_of_locallyCompact_left
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint (X × Y)) :=
    onePointProduct_generated X Y hX hY
  let R : Setoid (OnePoint X × OnePoint Y) :=
    Setoid.ker (rawCollapse X Y)
  let rawHomeo := (rawProdSmashHomeomorphData X Y).1
  letI : T2Space (Quotient R) := rawHomeo.symm.isEmbedding.t2Space
  let coreIso : (onePointOf.{u, v} (X × Y)).right ≅
      CGWH.of (OnePoint (X × Y)) :=
    CGWH.isoOfHomeo (CompactlyGenerated.coreflectionCounitHomeoData (OnePoint (X × Y))).1
  let rawIso : CGWH.of (OnePoint (X × Y)) ≅
      rawQuotientCGWH.{u, v} X Y hX hY := by
    unfold rawQuotientCGWH
    exact CGWH.isoOfHomeo rawHomeo
  let E := coreIso ≪≫ rawIso ≪≫ (smashRawQuotientIso X Y hX hY).symm
  let eQ := rawQuotientEquiv.{u, v} X Y hX hY
  let q := (CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal
    (onePointOf.{u, v} X) (onePointOf.{u, v} Y)).2.1.inl
  refine ⟨E, ?_, ?_⟩
  · change (rawQuotientToSmashData.{u, v} X Y hX hY).1
        (eQ.symm (rawHomeo (coreIso.hom OnePoint.infty))) =
      q ((nativeOnePointProductHomeo X Y hX hY).symm
        (OnePoint.infty, OnePoint.infty))
    have hcore : coreIso.hom OnePoint.infty = OnePoint.infty :=
      (CompactlyGenerated.coreflectionCounitHomeoData.{u, v}
        (OnePoint (X × Y))).2 OnePoint.infty
    rw [hcore,
      (rawProdSmashHomeomorphData X Y).2.1,
      (rawQuotientToSmashData X Y hX hY).2]
  · intro x y
    change (rawQuotientToSmashData.{u, v} X Y hX hY).1
        (eQ.symm (rawHomeo
          (coreIso.hom ((x, y) : OnePoint (X × Y))))) =
      q ((nativeOnePointProductHomeo X Y hX hY).symm
        ((x : OnePoint X), (y : OnePoint Y)))
    have hcore : coreIso.hom ((x, y) : OnePoint (X × Y)) =
        ((x, y) : OnePoint (X × Y)) :=
      (CompactlyGenerated.coreflectionCounitHomeoData.{u, v}
        (OnePoint (X × Y))).2 ((x, y) : OnePoint (X × Y))
    rw [hcore,
      (rawProdSmashHomeomorphData X Y).2.2 x y,
      (rawQuotientToSmashData X Y hX hY).2]

/-- The inverse native product comparison is the canonical tensor carrier equivalence. -/
theorem nativeOnePointProductHomeo_symm_eq_tensorEquivProd
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y))
    (a : OnePoint X × OnePoint Y) :
    (nativeOnePointProductHomeo.{u, v} X Y hX hY).symm a =
      (CGWH.tensorEquivProd (onePointOf.{u, v} X).right
          (onePointOf.{u, v} Y).right).symm a := by
  let n := nativeOnePointProductHomeo.{u, v} X Y hX hY
  let c := (CGWH.tensorEquivProd (onePointOf.{u, v} X).right
      (onePointOf.{u, v} Y).right).symm a
  apply n.injective
  rw [n.apply_symm_apply]
  rw [show n c = CGWH.prodComparisonToTop
      (onePointOf.{u, v} X).right
      (onePointOf.{u, v} Y).right c by
    apply Prod.ext
    · exact (CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint X)).2 _
    · exact (CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint Y)).2 _]
  rw [← CGWH.tensorEquivProd_eq_prodComparisonToTop]
  exact ((CGWH.tensorEquivProd (onePointOf.{u, v} X).right
    (onePointOf.{u, v} Y).right).apply_symm_apply a).symm

/-- Native smash collapses the left basepoint axis to its distinguished point. -/
theorem smashQuotient_leftAxis_eq_point
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (x : (onePointOf.{u, v} X).right) (t : CGWH.point.{u, v}) :
    let A := onePointOf.{u, v} X
    let B := onePointOf.{u, v} Y
    let q := (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal A B).2.1.inl
    q (CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom) x) =
      (A ⊗ B).hom t := by
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal A B
  have hLeft : pushout.inl A.hom B.hom ≫ p.1.right =
      CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom) := by
    change pushout.inl A.hom B.hom ≫ pushout.desc
      (CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom))
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom)
        (𝟙 B.right)) _ = _
    exact pushout.inl_desc _ _ _
  let wedgeObj : CGWH.{u, v} :=
    (((CategoryTheory.Pointed.wedge CGWH.point).obj A).obj B).right
  let leg : A.right ⟶ wedgeObj := pushout.inl A.hom B.hom
  let wedgeMap : wedgeObj ⟶ A.right ⊗ B.right := p.1.right
  let wedgeTerminal : wedgeObj ⟶ CGWH.point.{u, v} :=
    CGWH.point_isTerminal.from wedgeObj
  have hc := ConcreteCategory.congr_hom p.2.1.condition (leg x)
  change p.2.1.inl (wedgeMap (leg x)) =
    p.2.1.inr (wedgeTerminal (leg x)) at hc
  have hLegPoint : wedgeMap (leg x) =
    CartesianMonoidalCategory.lift (𝟙 A.right)
      (CGWH.point_isTerminal.from A.right ≫ B.hom) x :=
    ConcreteCategory.congr_hom hLeft x
  rw [hLegPoint] at hc
  have hterminal :
      CGWH.point_isTerminal.from
        (((CategoryTheory.Pointed.wedge CGWH.point).obj A).obj B).right
        (pushout.inl A.hom B.hom x) = t := by
    change PUnit.unit = t
    cases t
    rfl
  exact hc.trans (congrArg p.2.1.inr hterminal)

/-- Native smash collapses the right basepoint axis to its distinguished point. -/
theorem smashQuotient_rightAxis_eq_point
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (y : (onePointOf.{u, v} Y).right) (t : CGWH.point.{u, v}) :
    let A := onePointOf.{u, v} X
    let B := onePointOf.{u, v} Y
    let q := (CategoryTheory.Pointed.smashPresentation
      CGWH.point CGWH.point_isTerminal A B).2.1.inl
    q (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom)
        (𝟙 B.right) y) = (A ⊗ B).hom t := by
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal A B
  have hRight : pushout.inr A.hom B.hom ≫ p.1.right =
      CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom) (𝟙 B.right) := by
    change pushout.inr A.hom B.hom ≫ pushout.desc
      (CartesianMonoidalCategory.lift (𝟙 A.right)
        (CGWH.point_isTerminal.from A.right ≫ B.hom))
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from B.right ≫ A.hom)
        (𝟙 B.right)) _ = _
    exact pushout.inr_desc _ _ _
  let wedgeObj : CGWH.{u, v} :=
    (((CategoryTheory.Pointed.wedge CGWH.point).obj A).obj B).right
  let leg : B.right ⟶ wedgeObj := pushout.inr A.hom B.hom
  let wedgeMap : wedgeObj ⟶ A.right ⊗ B.right := p.1.right
  let wedgeTerminal : wedgeObj ⟶ CGWH.point.{u, v} :=
    CGWH.point_isTerminal.from wedgeObj
  have hc := ConcreteCategory.congr_hom p.2.1.condition (leg y)
  change p.2.1.inl (wedgeMap (leg y)) =
    p.2.1.inr (wedgeTerminal (leg y)) at hc
  have hLegPoint : wedgeMap (leg y) =
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from B.right ≫ A.hom) (𝟙 B.right) y :=
    ConcreteCategory.congr_hom hRight y
  rw [hLegPoint] at hc
  have hterminal :
      CGWH.point_isTerminal.from
        (((CategoryTheory.Pointed.wedge CGWH.point).obj A).obj B).right
        (pushout.inr A.hom B.hom y) = t := by
    change PUnit.unit = t
    cases t
    rfl
  exact hc.trans (congrArg p.2.1.inr hterminal)

/-- One-point compactification carries products to the native smash product. -/
noncomputable def onePointProdSmashIso
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y)) :
    onePointOf.{u, v} (X × Y) ≅
      onePointOf.{u, v} X ⊗ onePointOf.{u, v} Y :=
  Under.isoMk (onePointProdSmashRightIsoData X Y hX hY).1 (by
    apply ConcreteCategory.hom_ext
    intro t
    let A := onePointOf.{u, v} X
    let B := onePointOf.{u, v} Y
    let q : A.right ⊗ B.right ⟶ (A ⊗ B).right :=
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal A B).2.1.inl
    let n := nativeOnePointProductHomeo X Y hX hY
    change (onePointProdSmashRightIsoData.{u, v} X Y hX hY).1.hom
        OnePoint.infty =
      (onePointOf.{u, v} X ⊗ onePointOf.{u, v} Y).hom t
    rw [(onePointProdSmashRightIsoData X Y hX hY).2.1]
    rw [show n.symm (OnePoint.infty, OnePoint.infty) =
        CartesianMonoidalCategory.lift (𝟙 A.right)
          (CGWH.point_isTerminal.from A.right ≫ B.hom)
          OnePoint.infty by
      apply n.injective
      rw [n.apply_symm_apply]
      exact (nativeOnePointProductHomeo_leftAxis
        X Y hX hY OnePoint.infty).symm]
    exact smashQuotient_leftAxis_eq_point X Y OnePoint.infty t)

/-- The product-to-smash comparison sends infinity to the left basepoint
face. -/
theorem onePointProdSmashIso_infty_left
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y))
    (y : OnePoint Y) :
    (onePointProdSmashIso.{u, v} X Y hX hY).hom.right
        OnePoint.infty =
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal
        (onePointOf.{u, v} X) (onePointOf.{u, v} Y)).2.1.inl
          ((CGWH.tensorEquivProd (onePointOf.{u, v} X).right
              (onePointOf.{u, v} Y).right).symm (OnePoint.infty, y)) := by
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal A B
  let q : A.right ⊗ B.right ⟶ (A ⊗ B).right := p.2.1.inl
  let n := nativeOnePointProductHomeo X Y hX hY
  let t : CGWH.point.{u, v} := by
    change PUnit
    exact PUnit.unit
  change (onePointProdSmashRightIsoData.{u, v} X Y hX hY).1.hom
      OnePoint.infty = q ((CGWH.tensorEquivProd A.right B.right).symm (OnePoint.infty, y))
  rw [(onePointProdSmashRightIsoData X Y hX hY).2.1]
  calc
    q (n.symm (OnePoint.infty, OnePoint.infty)) = (A ⊗ B).hom t := by
      rw [show n.symm (OnePoint.infty, OnePoint.infty) =
          CartesianMonoidalCategory.lift (𝟙 A.right)
            (CGWH.point_isTerminal.from A.right ≫ B.hom)
            OnePoint.infty by
        apply n.injective
        rw [n.apply_symm_apply]
        exact (nativeOnePointProductHomeo_leftAxis
          X Y hX hY OnePoint.infty).symm]
      exact smashQuotient_leftAxis_eq_point X Y OnePoint.infty t
    _ = q (n.symm (OnePoint.infty, y)) := by
      rw [show n.symm (OnePoint.infty, y) =
          CartesianMonoidalCategory.lift
            (CGWH.point_isTerminal.from B.right ≫ A.hom)
            (𝟙 B.right) y by
        apply n.injective
        rw [n.apply_symm_apply]
        exact (nativeOnePointProductHomeo_rightAxis X Y hX hY y).symm]
      exact (smashQuotient_rightAxis_eq_point X Y y t).symm
    _ = q ((CGWH.tensorEquivProd A.right B.right).symm (OnePoint.infty, y)) := congrArg q
      (nativeOnePointProductHomeo_symm_eq_tensorEquivProd X Y hX hY
        (OnePoint.infty, y))

/-- The product-to-smash comparison sends infinity to the right basepoint
face. -/
theorem onePointProdSmashIso_infty_right
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y))
    (x : OnePoint X) :
    (onePointProdSmashIso.{u, v} X Y hX hY).hom.right
        OnePoint.infty =
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal
        (onePointOf.{u, v} X) (onePointOf.{u, v} Y)).2.1.inl
          ((CGWH.tensorEquivProd (onePointOf.{u, v} X).right
              (onePointOf.{u, v} Y).right).symm (x, OnePoint.infty)) := by
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal A B
  let q : A.right ⊗ B.right ⟶ (A ⊗ B).right := p.2.1.inl
  let n := nativeOnePointProductHomeo X Y hX hY
  let t : CGWH.point.{u, v} := by
    change PUnit
    exact PUnit.unit
  change (onePointProdSmashRightIsoData.{u, v} X Y hX hY).1.hom
      OnePoint.infty = q ((CGWH.tensorEquivProd A.right B.right).symm (x, OnePoint.infty))
  rw [(onePointProdSmashRightIsoData X Y hX hY).2.1]
  calc
    q (n.symm (OnePoint.infty, OnePoint.infty)) = (A ⊗ B).hom t := by
      rw [show n.symm (OnePoint.infty, OnePoint.infty) =
          CartesianMonoidalCategory.lift (𝟙 A.right)
            (CGWH.point_isTerminal.from A.right ≫ B.hom)
            OnePoint.infty by
        apply n.injective
        rw [n.apply_symm_apply]
        exact (nativeOnePointProductHomeo_leftAxis
          X Y hX hY OnePoint.infty).symm]
      exact smashQuotient_leftAxis_eq_point X Y OnePoint.infty t
    _ = q (n.symm (x, OnePoint.infty)) := by
      rw [show n.symm (x, OnePoint.infty) =
          CartesianMonoidalCategory.lift (𝟙 A.right)
            (CGWH.point_isTerminal.from A.right ≫ B.hom) x by
        apply n.injective
        rw [n.apply_symm_apply]
        exact (nativeOnePointProductHomeo_leftAxis X Y hX hY x).symm]
      exact (smashQuotient_leftAxis_eq_point X Y x t).symm
    _ = q ((CGWH.tensorEquivProd A.right B.right).symm (x, OnePoint.infty)) := congrArg q
      (nativeOnePointProductHomeo_symm_eq_tensorEquivProd X Y hX hY
        (x, OnePoint.infty))

/-- The product-to-smash comparison sends a finite pair to its smash class. -/
theorem onePointProdSmashIso_coe
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y))
    (x : X) (y : Y) :
    (onePointProdSmashIso.{u, v} X Y hX hY).hom.right
        ((x, y) : OnePoint (X × Y)) =
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal
        (onePointOf.{u, v} X) (onePointOf.{u, v} Y)).2.1.inl
          ((CGWH.tensorEquivProd (onePointOf.{u, v} X).right
              (onePointOf.{u, v} Y).right).symm ((x : OnePoint X), (y : OnePoint Y))) := by
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal A B
  let q : A.right ⊗ B.right ⟶ (A ⊗ B).right := p.2.1.inl
  change (onePointProdSmashRightIsoData.{u, v} X Y hX hY).1.hom
      ((x, y) : OnePoint (X × Y)) =
    q ((CGWH.tensorEquivProd A.right B.right).symm ((x : OnePoint X), (y : OnePoint Y)))
  rw [(onePointProdSmashRightIsoData X Y hX hY).2.2 x y]
  exact congrArg q
    (nativeOnePointProductHomeo_symm_eq_tensorEquivProd X Y hX hY
      ((x : OnePoint X), (y : OnePoint Y)))


/-- The product-to-smash comparison is natural for proper maps, with the
product properness witness kept explicit. -/
theorem onePointProdSmashIso_naturality
    {X X' Y Y' : Type v}
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace X'] [LocallyCompactSpace X'] [T2Space X']
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [TopologicalSpace Y'] [LocallyCompactSpace Y'] [T2Space Y']
    (f : ContinuousMap X X') (g : ContinuousMap Y Y')
    (hf : Tendsto f (coclosedCompact X) (coclosedCompact X'))
    (hg : Tendsto g (coclosedCompact Y) (coclosedCompact Y'))
    (hfg : Tendsto (f.prodMap g) (coclosedCompact (X × Y))
      (coclosedCompact (X' × Y')))
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hX' : UCompactlyGeneratedSpace.{u} (OnePoint X'))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y))
    (hY' : UCompactlyGeneratedSpace.{u} (OnePoint Y')) :
    onePointMapOfProper.{u, v} (f.prodMap g) hfg ≫
        (onePointProdSmashIso.{u, v} X' Y' hX' hY').hom =
      (onePointProdSmashIso.{u, v} X Y hX hY).hom ≫
        (onePointMapOfProper.{u, v} f hf ⊗ₘ
          onePointMapOfProper.{u, v} g hg) := by
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let A := onePointOf.{u, v} X
  let A' := onePointOf.{u, v} X'
  let B := onePointOf.{u, v} Y
  let B' := onePointOf.{u, v} Y'
  let F := onePointMapOfProper.{u, v} f hf
  let G := onePointMapOfProper.{u, v} g hg
  let FG := onePointMapOfProper.{u, v} (f.prodMap g) hfg
  let μ := onePointProdSmashIso.{u, v} X Y hX hY
  let μ' := onePointProdSmashIso.{u, v} X' Y' hX' hY'
  let lhs : onePointOf.{u, v} (X × Y) ⟶ A' ⊗ B' := FG ≫ μ'.hom
  let rhs : onePointOf.{u, v} (X × Y) ⟶ A' ⊗ B' :=
    μ.hom ≫ (F ⊗ₘ G)
  change lhs = rhs
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  induction z using OnePoint.rec with
  | infty =>
      let t : CGWH.point.{u, v} := by
        change PUnit
        exact PUnit.unit
      have hl := ConcreteCategory.congr_hom (Under.w lhs) t
      have hr := ConcreteCategory.congr_hom (Under.w rhs) t
      rw [ConcreteCategory.comp_apply] at hl hr
      change lhs.right OnePoint.infty = (A' ⊗ B').hom t at hl
      change rhs.right OnePoint.infty = (A' ⊗ B').hom t at hr
      exact hl.trans hr.symm
  | coe pxy =>
      rcases pxy with ⟨x, y⟩
      change μ'.hom.right (FG.right ((x, y) : OnePoint (X × Y))) =
        (F ⊗ₘ G).right
          (μ.hom.right ((x, y) : OnePoint (X × Y)))
      rw [onePointMapOfProper_coe,
        onePointProdSmashIso_coe, onePointProdSmashIso_coe]
      let c := (CGWH.tensorEquivProd A.right B.right).symm ((x : OnePoint X), (y : OnePoint Y))
      let c' := (CGWH.tensorEquivProd A'.right B'.right).symm
        ((f x : OnePoint X'), (g y : OnePoint Y'))
      let q : A.right ⊗ B.right ⟶ (A ⊗ B).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal A B).2.1.inl
      let q' : A'.right ⊗ B'.right ⟶ (A' ⊗ B').right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal A' B').2.1.inl
      have hnat := ConcreteCategory.congr_hom
        (CategoryTheory.Pointed.smashQuotient_naturality
          CGWH.point CGWH.point_isTerminal F G) c
      change (F ⊗ₘ G).right (q c) =
        q' ((F.right ⊗ₘ G.right) c) at hnat
      have hc : (F.right ⊗ₘ G.right) c = c' :=
        by
          simpa only [c, c', F, G, A, A', B, B', onePointMapOfProper_coe] using
            CGWH.tensorEquivProd_symm_map F.right G.right
              (x : OnePoint X) (y : OnePoint Y)
      exact (congrArg q' hc.symm).trans hnat.symm

/-- For a compact Hausdorff space, adjoining a disjoint point realizes its compactification. -/
noncomputable def compactFreePointRawHomeo
    (X : Type v) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    PUnit.{v + 1} ⊕ X ≃ₜ OnePoint X := by
  let e : PUnit.{v + 1} ⊕ X ≃ OnePoint X :=
    { toFun := Sum.elim (fun _ => OnePoint.infty)
        (fun x => (x : OnePoint X))
      invFun := OnePoint.rec (Sum.inl PUnit.unit) Sum.inr
      left_inv := by
        intro z
        rcases z with p | x
        · cases p
          rfl
        · rfl
      right_inv := by
        intro z
        induction z using OnePoint.rec <;> rfl }
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (continuous_sum_dom.2 ⟨by simpa [e] using
        (continuous_const : Continuous
          (fun _ : PUnit.{v + 1} => (OnePoint.infty : OnePoint X))),
      by simpa [e] using (OnePoint.continuous_coe :
        Continuous ((↑) : X → OnePoint X))⟩)

/-- The native free-point carrier isomorphism for a compact space, preserving the added point. -/
noncomputable def compactFreePointRightIsoData
    (X : CGWH.{u, v}) [CompactSpace X] [T2Space X] :
    { e : ((Under.costar CGWH.point).obj X).right ≅
        (onePointOf.{u, v} (X : Type v)).right //
      ∀ t : CGWH.point.{u, v},
        e.hom (((Under.costar CGWH.point).obj X).hom t) =
          OnePoint.infty } := by
  let rawHomeo := compactFreePointRawHomeo (X : Type v)
  let _ : UCompactlyGeneratedSpace.{u} PUnit.{v + 1} := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} (X : Type v) :=
    X.toCompactlyGenerated.is_compactly_generated
  let _ : UCompactlyGeneratedSpace.{u} (PUnit.{v + 1} ⊕ X) :=
    inferInstance
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint X) :=
    uCompactlyGeneratedSpace_of_coinduced rawHomeo.continuous
      rawHomeo.isQuotientMap.eq_coinduced
  let W : CGWH.{u, v} := CGWH.of (PUnit.{v + 1} ⊕ X)
  let i0 : CGWH.point.{u, v} ⟶ W :=
    ConcreteCategory.ofHom ⟨Sum.inl, continuous_inl⟩
  let i1 : X ⟶ W :=
    ConcreteCategory.ofHom ⟨Sum.inr, continuous_inr⟩
  let c : BinaryCofan CGWH.point X := BinaryCofan.mk i0 i1
  have hc : IsColimit c := BinaryCofan.isColimitMk
      (fun s => ConcreteCategory.ofHom
        ⟨Sum.elim s.inl s.inr,
          continuous_sum_dom.2
            ⟨(ConcreteCategory.hom s.inl).continuous,
              (ConcreteCategory.hom s.inr).continuous⟩⟩)
      (by
        intro s
        apply ConcreteCategory.hom_ext
        intro p
        change PUnit.{v + 1} at p
        cases p
        rfl)
      (by
        intro s
        apply ConcreteCategory.hom_ext
        intro x
        rfl)
      (by
        intro s m h0 h1
        apply ConcreteCategory.hom_ext
        intro z
        rcases z with p | x
        · exact ConcreteCategory.congr_hom h0 p
        · exact ConcreteCategory.congr_hom h1 x)
  let e : CGWH.point.{u, v} ⨿ X ≅ W :=
    (coprodIsCoprod CGWH.point X).coconePointUniqueUpToIso hc
  let rawIso : W ≅ CGWH.of (OnePoint X) :=
    CGWH.isoOfHomeo rawHomeo
  let coreIso : (onePointOf.{u, v} (X : Type v)).right ≅
      CGWH.of (OnePoint X) :=
    CGWH.isoOfHomeo (CompactlyGenerated.coreflectionCounitHomeoData (OnePoint X)).1
  let E := e ≪≫ rawIso ≪≫ coreIso.symm
  refine ⟨E, ?_⟩
  intro t
  have hsource : ((Under.costar CGWH.point).obj X).hom =
      (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ X) :=
    (Under.costar_obj_hom CGWH.point X).trans (coprod.inl_desc _ _)
  have he : (coprod.inl : CGWH.point.{u, v} ⟶
      CGWH.point.{u, v} ⨿ X) ≫ e.hom = i0 :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod CGWH.point X) hc ⟨WalkingPair.left⟩
  have het := ConcreteCategory.congr_hom he t
  rw [show ((Under.costar CGWH.point).obj X).hom t =
      (ConcreteCategory.hom (coprod.inl :
        CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ X)) t by
    exact ConcreteCategory.congr_hom hsource t]
  change coreIso.inv (rawIso.hom (e.hom
      ((ConcreteCategory.hom (coprod.inl :
        CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ X)) t))) =
    OnePoint.infty
  rw [show e.hom ((ConcreteCategory.hom (coprod.inl :
      CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ X)) t) = i0 t by
    simpa only [ConcreteCategory.comp_apply] using het]
  change (CompactlyGenerated.coreflectionCounitHomeoData (OnePoint X)).1.symm
      (compactFreePointRawHomeo (X : Type v) (Sum.inl t)) =
    OnePoint.infty
  have ht : t = PUnit.unit := by
    change PUnit.{v + 1} at t
    cases t
    rfl
  rw [ht]
  apply (CompactlyGenerated.coreflectionCounitHomeoData (OnePoint X)).1.injective
  rw [(CompactlyGenerated.coreflectionCounitHomeoData (OnePoint X)).1.apply_symm_apply]
  exact ((CompactlyGenerated.coreflectionCounitHomeoData.{u, v}
    (OnePoint X)).2 OnePoint.infty).symm

/-- For compact Hausdorff CGWH spaces, adjoining a disjoint basepoint agrees
with one-point compactification. -/
noncomputable def addBasepointIsoOnePointOfCompact
    (X : CGWH.{u, v}) [CompactSpace X] [T2Space X] :
    (Under.costar CGWH.point).obj X ≅
      onePointOf.{u, v} (X : Type v) :=
  Under.isoMk (compactFreePointRightIsoData X).1 (by
    apply ConcreteCategory.hom_ext
    intro t
    exact (compactFreePointRightIsoData.{u, v} X).2 t)

/-- The compact free-point comparison sends the original finite coproduct
branch to its finite point. -/
theorem compactFreePointIso_coe (X : CGWH.{u, v}) [CompactSpace X] [T2Space X] (x : X) :
    (PointedCGWH.addBasepointIsoOnePointOfCompact X).hom.right
        ((coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) x) = (x : OnePoint X) := by
  let rawHomeo := PointedCGWH.compactFreePointRawHomeo (X : Type v)
  let _ : UCompactlyGeneratedSpace.{u} PUnit.{v + 1} := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} (X : Type v) := X.toCompactlyGenerated.is_compactly_generated
  let _ : UCompactlyGeneratedSpace.{u} (PUnit.{v + 1} ⊕ X) := inferInstance
  let _ : UCompactlyGeneratedSpace.{u} (OnePoint (X : Type v)) :=
    uCompactlyGeneratedSpace_of_coinduced rawHomeo.continuous rawHomeo.isQuotientMap.eq_coinduced
  let W : CGWH.{u, v} := CGWH.of (PUnit.{v + 1} ⊕ X)
  let i0 : CGWH.point.{u, v} ⟶ W :=
    ConcreteCategory.ofHom ⟨(Sum.inl : PUnit.{v + 1} → PUnit.{v + 1} ⊕ X), continuous_inl⟩
  let i1 : X ⟶ W := ConcreteCategory.ofHom
    ⟨(Sum.inr : X → PUnit.{v + 1} ⊕ X), continuous_inr⟩
  let c : BinaryCofan CGWH.point X := BinaryCofan.mk i0 i1
  have hc : IsColimit c := BinaryCofan.isColimitMk
      (fun s => ConcreteCategory.ofHom
        ⟨Sum.elim s.inl s.inr,
          continuous_sum_dom.2 ⟨(ConcreteCategory.hom s.inl).continuous,
            (ConcreteCategory.hom s.inr).continuous⟩⟩)
      (by intro s; apply ConcreteCategory.hom_ext; intro p; cases p; rfl)
      (by intro s; apply ConcreteCategory.hom_ext; intro p; rfl)
      (by
        intro s f h0 h1
        apply ConcreteCategory.hom_ext
        intro p
        rcases p with p | p
        · exact ConcreteCategory.congr_hom h0 p
        · exact ConcreteCategory.congr_hom h1 p)
  let e : CGWH.point.{u, v} ⨿ X ≅ W :=
    (coprodIsCoprod CGWH.point X).coconePointUniqueUpToIso hc
  let rawIso : W ≅ CGWH.of (OnePoint X) := CGWH.isoOfHomeo rawHomeo
  let core := CompactlyGenerated.coreflectionCounitHomeoData.{u, v} (OnePoint X)
  let coreIso : (PointedCGWH.onePointOf.{u, v} (X : Type v)).right ≅ CGWH.of (OnePoint X) :=
    CGWH.isoOfHomeo core.1
  change coreIso.inv (rawIso.hom (e.hom ((coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) x))) =
    (x : OnePoint X)
  have he : (coprod.inr : X ⟶ CGWH.point.{u, v} ⨿ X) ≫ e.hom = i1 :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod CGWH.point X) hc ⟨WalkingPair.right⟩
  have hex := ConcreteCategory.congr_hom he x
  rw [ConcreteCategory.comp_apply] at hex
  rw [hex]
  change core.1.symm (rawHomeo (Sum.inr x)) = (x : OnePoint X)
  change core.1.symm (x : OnePoint X) = (x : OnePoint X)
  exact (core.2 (core.1.symm (x : OnePoint X))).symm.trans (core.1.apply_symm_apply _)

/-- Native smash braiding swaps the coordinates of its product generators. -/
theorem smashQuotient_braiding_hom
    (X Y : PointedCGWH.{u, v}) :
    let P := CGWH.point.{u, v}
    let hP := CGWH.point_isTerminal.{u, v}
    (CategoryTheory.Pointed.smashPresentation P hP X Y).2.1.inl ≫
        (β_ X Y).hom.right =
      CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.snd X.right Y.right)
          (CartesianMonoidalCategory.fst X.right Y.right) ≫
        (CategoryTheory.Pointed.smashPresentation P hP Y X).2.1.inl := by
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let P := CGWH.point.{u, v}
  let hP := CGWH.point_isTerminal.{u, v}
  change (CategoryTheory.Pointed.smashPresentation P hP X Y).2.1.inl ≫
      (CategoryTheory.Pointed.smashBraiding P hP X Y).hom.right =
    CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.snd X.right Y.right)
        (CartesianMonoidalCategory.fst X.right Y.right) ≫
      (CategoryTheory.Pointed.smashPresentation P hP Y X).2.1.inl
  simpa only [CartesianMonoidalCategory.lift_snd_fst] using
    CategoryTheory.Pointed.smashBraiding_hom_quotient P hP X Y

/-- Swapping finite coordinates swaps their canonical tensor preimages. -/
theorem nativeProductSwap_tensorEquivProd_coe
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (x : X) (y : Y) :
    let A := onePointOf.{u, v} X
    let B := onePointOf.{u, v} Y
    CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.snd A.right B.right)
        (CartesianMonoidalCategory.fst A.right B.right)
        ((CGWH.tensorEquivProd A.right B.right).symm
          ((x : OnePoint X), (y : OnePoint Y))) =
      (CGWH.tensorEquivProd B.right A.right).symm
        ((y : OnePoint Y), (x : OnePoint X)) := by
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let c := (CGWH.tensorEquivProd A.right B.right).symm
    ((x : OnePoint X), (y : OnePoint Y))
  apply (CGWH.tensorEquivProd B.right A.right).injective
  rw [(CGWH.tensorEquivProd B.right A.right).apply_symm_apply]
  apply Prod.ext
  · have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst
        (CartesianMonoidalCategory.snd A.right B.right)
        (CartesianMonoidalCategory.fst A.right B.right)) c
    change CartesianMonoidalCategory.fst B.right A.right
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.snd A.right B.right)
          (CartesianMonoidalCategory.fst A.right B.right) c) =
      (y : OnePoint Y)
    exact h.trans (congrArg Prod.snd
      ((CGWH.tensorEquivProd A.right B.right).apply_symm_apply
        ((x : OnePoint X), (y : OnePoint Y))))
  · have h := ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd
        (CartesianMonoidalCategory.snd A.right B.right)
        (CartesianMonoidalCategory.fst A.right B.right)) c
    change CartesianMonoidalCategory.snd B.right A.right
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.snd A.right B.right)
          (CartesianMonoidalCategory.fst A.right B.right) c) =
      (x : OnePoint X)
    exact h.trans (congrArg Prod.fst
      ((CGWH.tensorEquivProd A.right B.right).apply_symm_apply
        ((x : OnePoint X), (y : OnePoint Y))))


/-- The product-to-smash comparison respects product and smash
associativity. -/
theorem onePointProdSmashIso_associativity
    (X Y Z : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y))
    (hZ : UCompactlyGeneratedSpace.{u} (OnePoint Z))
    (hXY : UCompactlyGeneratedSpace.{u} (OnePoint (X × Y)))
    (hYZ : UCompactlyGeneratedSpace.{u} (OnePoint (Y × Z))) :
    (onePointHomeomorphOfHomeomorph.{u, v}
        (Homeomorph.prodAssoc X Y Z)).hom ≫
        (onePointProdSmashIso.{u, v} X (Y × Z) hX hYZ).hom ≫
        (𝟙 (onePointOf.{u, v} X) ⊗ₘ
          (onePointProdSmashIso.{u, v} Y Z hY hZ).hom) =
      (onePointProdSmashIso.{u, v} (X × Y) Z hXY hZ).hom ≫
        ((onePointProdSmashIso.{u, v} X Y hX hY).hom ⊗ₘ
          𝟙 (onePointOf.{u, v} Z)) ≫
        (α_ (onePointOf.{u, v} X) (onePointOf.{u, v} Y)
          (onePointOf.{u, v} Z)).hom := by
  let _ : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let C := onePointOf.{u, v} Z
  let D := onePointOf.{u, v} (X × Y)
  let E := onePointOf.{u, v} (Y × Z)
  let H := onePointHomeomorphOfHomeomorph.{u, v}
    (Homeomorph.prodAssoc X Y Z)
  let μXY := onePointProdSmashIso.{u, v} X Y hX hY
  let μYZ := onePointProdSmashIso.{u, v} Y Z hY hZ
  let μDC := onePointProdSmashIso.{u, v} (X × Y) Z hXY hZ
  let μAE := onePointProdSmashIso.{u, v} X (Y × Z) hX hYZ
  let lhs : onePointOf.{u, v} ((X × Y) × Z) ⟶ A ⊗ (B ⊗ C) :=
    H.hom ≫ μAE.hom ≫ (𝟙 A ⊗ₘ μYZ.hom)
  let rhs : onePointOf.{u, v} ((X × Y) × Z) ⟶ A ⊗ (B ⊗ C) :=
    μDC.hom ≫ (μXY.hom ⊗ₘ 𝟙 C) ≫ (α_ A B C).hom
  change lhs = rhs
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro w
  induction w using OnePoint.rec with
  | infty =>
      let t0 : CGWH.point.{u, v} := by
        change PUnit
        exact PUnit.unit
      have hl := ConcreteCategory.congr_hom (Under.w lhs) t0
      have hr := ConcreteCategory.congr_hom (Under.w rhs) t0
      rw [ConcreteCategory.comp_apply] at hl hr
      change lhs.right OnePoint.infty = (A ⊗ (B ⊗ C)).hom t0 at hl
      change rhs.right OnePoint.infty = (A ⊗ (B ⊗ C)).hom t0 at hr
      exact hl.trans hr.symm
  | coe pxyz =>
      rcases pxyz with ⟨⟨x, y⟩, z⟩
      change (𝟙 A ⊗ₘ μYZ.hom).right
          (μAE.hom.right (H.hom.right
            (((x, y), z) : OnePoint ((X × Y) × Z)))) =
        (α_ A B C).hom.right
          ((μXY.hom ⊗ₘ 𝟙 C).right
            (μDC.hom.right
              (((x, y), z) : OnePoint ((X × Y) × Z))))
      have hH : H.hom.right
          (((x, y), z) : OnePoint ((X × Y) × Z)) =
          ((x, (y, z)) : OnePoint (X × (Y × Z))) := by
        unfold H onePointHomeomorphOfHomeomorph
        exact onePointMapOfProper_coe.{u, v}
          (⟨Homeomorph.prodAssoc X Y Z,
            (Homeomorph.prodAssoc X Y Z).continuous⟩ :
              C((X × Y) × Z, X × (Y × Z)))
          (Homeomorph.prodAssoc X Y Z).map_coclosedCompact.le
          ((x, y), z)
      rw [hH, onePointProdSmashIso_coe,
        onePointProdSmashIso_coe]
      let a : A.right := (x : OnePoint X)
      let b : B.right := (y : OnePoint Y)
      let c : C.right := (z : OnePoint Z)
      let d : D.right := ((x, y) : OnePoint (X × Y))
      let e : E.right := ((y, z) : OnePoint (Y × Z))
      let cXY := (CGWH.tensorEquivProd A.right B.right).symm (a, b)
      let cYZ := (CGWH.tensorEquivProd B.right C.right).symm (b, c)
      let cDC := (CGWH.tensorEquivProd D.right C.right).symm (d, c)
      let cAE := (CGWH.tensorEquivProd A.right E.right).symm (a, e)
      let t := (CGWH.tensorEquivProd (A.right ⊗ B.right) C.right).symm (cXY, c)
      let qXY : A.right ⊗ B.right ⟶ (A ⊗ B).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal A B).2.1.inl
      let qYZ : B.right ⊗ C.right ⟶ (B ⊗ C).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal B C).2.1.inl
      let qDC : D.right ⊗ C.right ⟶ (D ⊗ C).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal D C).2.1.inl
      let qAE : A.right ⊗ E.right ⟶ (A ⊗ E).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal A E).2.1.inl
      let qAB_C : (A ⊗ B).right ⊗ C.right ⟶ ((A ⊗ B) ⊗ C).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal (A ⊗ B) C).2.1.inl
      let qA_BC : A.right ⊗ (B ⊗ C).right ⟶ (A ⊗ (B ⊗ C)).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal A (B ⊗ C)).2.1.inl
      have hμXY : μXY.hom.right d = qXY cXY :=
        onePointProdSmashIso_coe X Y hX hY x y
      have hμYZ : μYZ.hom.right e = qYZ cYZ :=
        onePointProdSmashIso_coe Y Z hY hZ y z
      have hRarg : (μXY.hom.right ⊗ₘ 𝟙 C.right) cDC =
          (qXY ▷ C.right) t := by
        have h1 := CGWH.tensorEquivProd_symm_map μXY.hom.right (𝟙 C.right) d c
        have h2 := CGWH.tensorEquivProd_symm_map qXY (𝟙 C.right) cXY c
        rw [MonoidalCategory.tensorHom_id] at h2
        have hmid : (CGWH.tensorEquivProd (A ⊗ B).right C.right).symm (μXY.hom.right d, c) =
            (CGWH.tensorEquivProd (A ⊗ B).right C.right).symm (qXY cXY, c) := by
          exact congrArg
            (fun w => (CGWH.tensorEquivProd (A ⊗ B).right C.right).symm (w, c)) hμXY
        simpa only [ConcreteCategory.id_apply] using h1.trans (hmid.trans h2.symm)
      have hLarg : (𝟙 A.right ⊗ₘ μYZ.hom.right) cAE =
          (A.right ◁ qYZ) ((α_ A.right B.right C.right).hom t) := by
        have h1 := CGWH.tensorEquivProd_symm_map (𝟙 A.right) μYZ.hom.right a e
        have h2 := CGWH.tensorEquivProd_symm_map (𝟙 A.right) qYZ a cYZ
        rw [MonoidalCategory.id_tensorHom] at h2
        have hα := CGWH.tensorEquivProd_symm_associator
          A.right B.right C.right a b c
        have hmid : (CGWH.tensorEquivProd A.right (B ⊗ C).right).symm (a, μYZ.hom.right e) =
            (CGWH.tensorEquivProd A.right (B ⊗ C).right).symm (a, qYZ cYZ) := by
          exact congrArg
            (fun w => (CGWH.tensorEquivProd A.right (B ⊗ C).right).symm (a, w)) hμYZ
        simpa only [ConcreteCategory.id_apply] using
          h1.trans (hmid.trans (h2.symm.trans (congrArg _ hα.symm)))
      have hNatL := ConcreteCategory.congr_hom
        (CategoryTheory.Pointed.smashQuotient_naturality
          CGWH.point CGWH.point_isTerminal (𝟙 A) μYZ.hom) cAE
      change (𝟙 A ⊗ₘ μYZ.hom).right (qAE cAE) =
        qA_BC ((𝟙 A.right ⊗ₘ μYZ.hom.right) cAE) at hNatL
      have hNatR := ConcreteCategory.congr_hom
        (CategoryTheory.Pointed.smashQuotient_naturality
          CGWH.point CGWH.point_isTerminal μXY.hom (𝟙 C)) cDC
      change (μXY.hom ⊗ₘ 𝟙 C).right (qDC cDC) =
        qAB_C ((μXY.hom.right ⊗ₘ 𝟙 C.right) cDC) at hNatR
      have hAssoc := ConcreteCategory.congr_hom
        (CategoryTheory.Pointed.smashAssociator_hom_quotient
          CGWH.point CGWH.point_isTerminal A B C) t
      change (α_ A B C).hom.right
          (qAB_C ((qXY ▷ C.right) t)) =
        qA_BC ((A.right ◁ qYZ)
          ((α_ A.right B.right C.right).hom t)) at hAssoc
      change (𝟙 A ⊗ₘ μYZ.hom).right (qAE cAE) =
        (α_ A B C).hom.right
          ((μXY.hom ⊗ₘ 𝟙 C).right (qDC cDC))
      rw [hNatL, hNatR, hLarg, hRarg]
      exact hAssoc.symm

/-- The product-to-smash comparison intertwines product swap with the
native smash braiding. -/
theorem onePointProdSmashIso_braiding
    (X Y : Type v)
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    (hX : UCompactlyGeneratedSpace.{u} (OnePoint X))
    (hY : UCompactlyGeneratedSpace.{u} (OnePoint Y)) :
    (onePointHomeomorphOfHomeomorph.{u, v}
        (Homeomorph.prodComm X Y)).hom ≫
        (onePointProdSmashIso.{u, v} Y X hY hX).hom =
      (onePointProdSmashIso.{u, v} X Y hX hY).hom ≫
        (β_ (onePointOf.{u, v} X) (onePointOf.{u, v} Y)).hom := by
  let A := onePointOf.{u, v} X
  let B := onePointOf.{u, v} Y
  let H := onePointHomeomorphOfHomeomorph.{u, v}
    (Homeomorph.prodComm X Y)
  let μ := onePointProdSmashIso.{u, v} X Y hX hY
  let μ' := onePointProdSmashIso.{u, v} Y X hY hX
  let lhs : onePointOf.{u, v} (X × Y) ⟶ B ⊗ A := H.hom ≫ μ'.hom
  let rhs : onePointOf.{u, v} (X × Y) ⟶ B ⊗ A :=
    μ.hom ≫ (β_ A B).hom
  change lhs = rhs
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro z
  induction z using OnePoint.rec with
  | infty =>
      let t : CGWH.point.{u, v} := by
        change PUnit
        exact PUnit.unit
      have hl := ConcreteCategory.congr_hom (Under.w lhs) t
      have hr := ConcreteCategory.congr_hom (Under.w rhs) t
      rw [ConcreteCategory.comp_apply] at hl hr
      change lhs.right OnePoint.infty = (B ⊗ A).hom t at hl
      change rhs.right OnePoint.infty = (B ⊗ A).hom t at hr
      exact hl.trans hr.symm
  | coe pxy =>
      rcases pxy with ⟨x, y⟩
      change μ'.hom.right
          (H.hom.right ((x, y) : OnePoint (X × Y))) =
        (β_ A B).hom.right
          (μ.hom.right ((x, y) : OnePoint (X × Y)))
      have hH : H.hom.right ((x, y) : OnePoint (X × Y)) =
          ((y, x) : OnePoint (Y × X)) := by
        unfold H onePointHomeomorphOfHomeomorph
        exact onePointMapOfProper_coe.{u, v}
          (⟨Homeomorph.prodComm X Y,
            (Homeomorph.prodComm X Y).continuous⟩ : C(X × Y, Y × X))
          (Homeomorph.prodComm X Y).map_coclosedCompact.le (x, y)
      rw [hH, onePointProdSmashIso_coe,
        onePointProdSmashIso_coe]
      let c := (CGWH.tensorEquivProd A.right B.right).symm ((x : OnePoint X), (y : OnePoint Y))
      let c' := (CGWH.tensorEquivProd B.right A.right).symm ((y : OnePoint Y), (x : OnePoint X))
      let q : A.right ⊗ B.right ⟶ (A ⊗ B).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal A B).2.1.inl
      let q' : B.right ⊗ A.right ⟶ (B ⊗ A).right :=
        (CategoryTheory.Pointed.smashPresentation
          CGWH.point CGWH.point_isTerminal B A).2.1.inl
      let s : A.right ⊗ B.right ⟶ B.right ⊗ A.right :=
        CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.snd A.right B.right)
          (CartesianMonoidalCategory.fst A.right B.right)
      have hb := ConcreteCategory.congr_hom
        (smashQuotient_braiding_hom A B) c
      change (β_ A B).hom.right (q c) = q' (s c) at hb
      have hc : s c = c' := nativeProductSwap_tensorEquivProd_coe X Y x y
      exact (congrArg q' hc.symm).trans hb.symm

end PointedCGWH
