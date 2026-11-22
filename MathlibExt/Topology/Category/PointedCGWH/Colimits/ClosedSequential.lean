/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.CGWH.Colimits.ClosedSequential
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup
import MathlibExt.Topology.Homotopy.HomotopyGroupMap
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Pointed closed sequential colimits and compact cubes

The same chosen pointed colimit cocone remains colimiting after forgetting
the point. Compact pointed maps and cube representatives factor through
actual closed stages. A compact homotopy relative to the cube boundary
factors at a common later stage with both endpoints, every boundary value,
and the entire included continuous homotopy unchanged.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval Topology.Homotopy

namespace PointedCGWH.ClosedSequentialColimit

/-- The entire forgetful inclusion, including all actual maps. -/
def topFunctor : PointedCGWH.{u, v} ⥤ TopCat.{v} :=
  pointedToCGWH ⋙ CGWH.cgwhToTop

/-- The complete included pointed-map function is unchanged. -/
theorem topFunctor_map {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    topFunctor.map f = CGWH.cgwhToTop.map f.right := rfl

/-- The actual pointed Nat cocone is colimiting after forgetting only its selected point. -/
def isColimitCGWH {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F) (hc : IsColimit c) :
    IsColimit (pointedToCGWH.mapCocone c) := by
  let _ : IsConnected ℕ := IsFiltered.isConnected ℕ
  exact isColimitOfPreserves pointedToCGWH hc

/-- The same whole pointed cocone is colimiting in actual compactly generated spaces. -/
def isColimitCompactlyGenerated {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) :
    IsColimit ((pointedToCGWH ⋙ CGWH.cgwhToCompactlyGenerated).mapCocone c) := by
  have h := CGWH.ClosedSequentialColimit.isColimitCompactlyGenerated
    (pointedToCGWH.mapCocone c) (isColimitCGWH c hc) hF
  exact IsColimit.ofIsoColimit h (Cocone.ext (Iso.refl _))

/-- The same complete pointed Nat cocone is colimiting in actual TopCat. -/
def isColimitTop {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) :
    IsColimit (topFunctor.mapCocone c) := by
  have h := CGWH.ClosedSequentialColimit.isColimitTop
    (pointedToCGWH.mapCocone c) (isColimitCGWH c hc) hF
  exact IsColimit.ofIsoColimit h (Cocone.ext (Iso.refl _))

/-- Every included pointed transition is a closed-T1 embedding. -/
theorem map_closedT1 {F : ℕ ⥤ PointedCGWH.{u, v}}
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    {i j : ℕ} (f : i ⟶ j) : TopCat.closedT1Embeddings ((F ⋙ topFunctor).map f) :=
  CGWH.ClosedSequentialColimit.map_closedT1 (F := F ⋙ pointedToCGWH) hF f

/-- The actual pointed cocone leg is a closed embedding on underlying spaces. -/
theorem leg_isClosedEmbedding {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (n : ℕ) :
    IsClosedEmbedding (topFunctor.map (c.ι.app n)).hom :=
  CGWH.ClosedSequentialColimit.leg_isClosedEmbedding
    (pointedToCGWH.mapCocone c) (isColimitCGWH c hc) hF n

/-- A compact continuous map factors through an actual pointed cocone leg. -/
theorem exists_stage_of_compact {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    {K : Type w} [TopologicalSpace K] (hK : IsCompact (Set.univ : Set K))
    (f : C(K, topFunctor.obj c.pt)) :
    ∃ (n : ℕ) (g : C(K, topFunctor.obj (F.obj n))),
      (topFunctor.map (c.ι.app n)).hom.comp g = f :=
  CGWH.ClosedSequentialColimit.exists_stage_of_compact
    (pointedToCGWH.mapCocone c) (isColimitCGWH c hc) hF hK f

/-- An underlying compact map factors after any prescribed pointed stage. -/
theorem exists_later_stage_of_compact {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    {K : Type w} [TopologicalSpace K] (hK : IsCompact (Set.univ : Set K))
    (f : C(K, topFunctor.obj c.pt)) (n₀ : ℕ) :
    ∃ (n : ℕ), n₀ ≤ n ∧ ∃ (g : C(K, topFunctor.obj (F.obj n))),
      (topFunctor.map (c.ι.app n)).hom.comp g = f :=
  CGWH.ClosedSequentialColimit.exists_later_stage_of_compact
    (pointedToCGWH.mapCocone c) (isColimitCGWH c hc) hF hK f n₀

/-- Factoring an actual pointed compact map recovers its whole point square. -/
theorem exists_stage_of_pointed_compact {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    (K : PointedCGWH.{u, v})
    (hK : IsCompact (Set.univ : Set (topFunctor.obj K))) (f : K ⟶ c.pt) :
    ∃ (n : ℕ) (g : K ⟶ F.obj n), g ≫ c.ι.app n = f := by
  obtain ⟨n, g, hg⟩ := exists_stage_of_compact c hc hF hK (topFunctor.map f).hom
  let g₀ : K.right ⟶ (F.obj n).right :=
    CGWH.fullyFaithfulCgwhToTop.preimage (TopCat.ofHom g)
  have hg₀ : CGWH.cgwhToTop.map g₀ = TopCat.ofHom g :=
    CGWH.fullyFaithfulCgwhToTop.map_preimage _
  have hfac : g₀ ≫ (c.ι.app n).right = f.right := by
    apply CGWH.cgwhToTop.map_injective
    rw [Functor.map_comp, hg₀]
    apply TopCat.hom_ext
    exact hg
  have hpoint : K.hom ≫ g₀ = (F.obj n).hom := by
    have h : (K.hom ≫ g₀) ≫ (c.ι.app n).right =
        (F.obj n).hom ≫ (c.ι.app n).right := by
      have hf : K.hom ≫ f.right = c.pt.hom := Under.w f
      have hl : (F.obj n).hom ≫ (c.ι.app n).right = c.pt.hom := Under.w (c.ι.app n)
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun q => K.hom ≫ q) hfac).trans (hf.trans hl.symm))
    apply CGWH.cgwhToTop.map_injective
    apply ConcreteCategory.hom_ext
    intro p
    apply (leg_isClosedEmbedding c hc hF n).injective
    exact ConcreteCategory.congr_hom (CGWH.cgwhToTop.congr_map h) p
  refine ⟨n, Under.homMk g₀ hpoint, ?_⟩
  apply pointedToCGWH.map_injective
  exact hfac


/-- The pointed compact factor can be chosen after any prescribed stage. -/
theorem exists_later_stage_of_pointed_compact {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    (K : PointedCGWH.{u, v})
    (hK : IsCompact (Set.univ : Set (topFunctor.obj K))) (f : K ⟶ c.pt) (n₀ : ℕ) :
    ∃ (n : ℕ), n₀ ≤ n ∧ ∃ (g : K ⟶ F.obj n), g ≫ c.ι.app n = f := by
  obtain ⟨j, g, hg⟩ := exists_stage_of_pointed_compact c hc hF K hK f
  let φ : j ⟶ max n₀ j := homOfLE (le_max_right n₀ j)
  refine ⟨max n₀ j, le_max_left _ _, g ≫ F.map φ, ?_⟩
  rw [Category.assoc, c.w φ]
  exact hg


/-- The whole comparison to the same chosen pointed native colimit point. -/
def topComparisonIso {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) :
    colimit (F ⋙ topFunctor) ≅ topFunctor.obj c.pt :=
  CGWH.ClosedSequentialColimit.topComparisonIso
    (pointedToCGWH.mapCocone c) (isColimitCGWH c hc) hF

/-- The forward comparison retains every actual pointed cocone leg. -/
@[reassoc]
theorem topComparisonIso_hom_ι {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (j : ℕ) :
    colimit.ι (F ⋙ topFunctor) j ≫ (topComparisonIso c hc hF).hom =
      topFunctor.map (c.ι.app j) :=
  CGWH.ClosedSequentialColimit.topComparisonIso_hom_ι
    (pointedToCGWH.mapCocone c) (isColimitCGWH c hc) hF j

/-- The inverse comparison retains every actual pointed cocone leg. -/
@[reassoc]
theorem topComparisonIso_inv_ι {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right)) (j : ℕ) :
    topFunctor.map (c.ι.app j) ≫ (topComparisonIso c hc hF).inv =
      colimit.ι (F ⋙ topFunctor) j :=
  CGWH.ClosedSequentialColimit.topComparisonIso_inv_ι
    (pointedToCGWH.mapCocone c) (isColimitCGWH c hc) hF j

end PointedCGWH.ClosedSequentialColimit

namespace GenLoop

/-- Transporting only the selected point retains the entire cube function. -/
private theorem closedSequential_eq_mp_apply {N : Type w} {X : Type u}
    [TopologicalSpace X] {x y : X}
    (h : x = y) (p : GenLoop N X x) (t : N → unitInterval) :
    (Eq.mp (congrArg (fun z => ↥(GenLoop N X z)) h) p).1 t = p.1 t := by
  cases h
  rfl

/-- The two actual selected-point transports are inverse on the whole cube. -/
private theorem closedSequential_eq_mp_symm {N : Type w} {X : Type u} [TopologicalSpace X] {x y : X}
    (h : x = y) (p : GenLoop N X x) :
    Eq.mp (congrArg (fun z => ↥(GenLoop N X z)) h.symm)
      (Eq.mp (congrArg (fun z => ↥(GenLoop N X z)) h) p) = p := by
  cases h
  rfl

end GenLoop

namespace HomotopyGroup

/-- Literal selected-point transport commutes with the actual cube quotient constructor. -/
private theorem closedSequential_eq_mp_mk {N : Type w} {X : Type u} [TopologicalSpace X] {x y : X}
    (h : x = y) (p : GenLoop N X x) :
    Eq.mp (congrArg (fun z => HomotopyGroup N X z) h) (mk p) =
      mk (Eq.mp (congrArg (fun z => ↥(GenLoop N X z)) h) p) := by
  cases h
  rfl

end HomotopyGroup

namespace PointedCGWH.CubeColimitGeometry
open PointedCGWH.ClosedSequentialColimit

/--
The actual cube map postcomposes, then uses its same literal selected-point equality.
-/
def cubeMap (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (p : GenLoop (Fin n) (topFunctor.obj X) (underlyingBasepoint X)) :
    GenLoop (Fin n) (topFunctor.obj Y) (underlyingBasepoint Y) :=
  Eq.mp (congrArg (fun z => ↥(GenLoop (Fin n) (topFunctor.obj Y) z))
    (underlyingBasepoint_naturality f)) (GenLoop.map (topFunctor.map f).hom p)

/-- Every full cube-map function is the same underlying pointed-map function. -/
theorem cubeMap_apply (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (p : GenLoop (Fin n) (topFunctor.obj X) (underlyingBasepoint X)) (t : Fin n → unitInterval) :
    (cubeMap n f p).1 t = (topFunctor.map f).hom (p.1 t) :=
  GenLoop.closedSequential_eq_mp_apply (underlyingBasepoint_naturality f) _ t

/-- The entire identity cube map is unchanged. -/
theorem cubeMap_id (n : ℕ) (X : PointedCGWH.{u, v})
    (p : GenLoop (Fin n) (topFunctor.obj X) (underlyingBasepoint X)) :
    cubeMap n (𝟙 X) p = p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [cubeMap_apply]
  exact ConcreteCategory.congr_hom (topFunctor.map_id X) (p.1 t)

/-- The complete cube maps obey the same pointed-map composition. -/
theorem cubeMap_comp (n : ℕ) {X Y Z : PointedCGWH.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : GenLoop (Fin n) (topFunctor.obj X) (underlyingBasepoint X)) :
    cubeMap n (f ≫ g) p = cubeMap n g (cubeMap n f p) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [cubeMap_apply, cubeMap_apply, cubeMap_apply, Functor.map_comp]
  rfl

/-- The whole actual cube-representative functor retains every pointed map. -/
def cubeRepresentativeFunctor (n : ℕ) : PointedCGWH.{u, v} ⥤ Type v where
  obj X := GenLoop (Fin n) (topFunctor.obj X) (underlyingBasepoint X)
  map f := ↾(cubeMap n f)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro p
    exact cubeMap_id n X p
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact cubeMap_comp n f g p

/-- The entire actual representative-functor map function is owned. -/
theorem cubeRepresentativeFunctor_map (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (cubeRepresentativeFunctor n).map f = ↾(cubeMap n f) := rfl

/-- Genuine cube postcomposition preserves actual relative homotopies. -/
theorem cubeMap_homotopic (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    {p q : GenLoop (Fin n) (topFunctor.obj X) (underlyingBasepoint X)}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (cubeMap n f p) (cubeMap n f q) := by
  have hm := GenLoop.Homotopic.map h (topFunctor.map f).hom
  have hpoint := underlyingBasepoint_naturality f
  have transport {Z : Type v} [TopologicalSpace Z] {z z' : Z} (e : z = z')
      {a b : GenLoop (Fin n) Z z} (h : GenLoop.Homotopic a b) :
      GenLoop.Homotopic (Eq.mp (congrArg (fun x => ↥(GenLoop (Fin n) Z x)) e) a)
        (Eq.mp (congrArg (fun x => ↥(GenLoop (Fin n) Z x)) e) b) := by
    cases e
    exact h
  exact transport hpoint hm

/-- The piNMap uses the same entire cube-map function at every representative. -/
theorem piNMap_mk (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (p : GenLoop (Fin n) (topFunctor.obj X) (underlyingBasepoint X)) :
    piNMap n f (HomotopyGroup.mk p) = HomotopyGroup.mk (cubeMap n f p) := by
  let h := underlyingBasepoint_naturality f
  apply (Equiv.cast (congrArg (fun z => HomotopyGroup.Pi n (topFunctor.obj Y) z)
    h.symm)).injective
  have hraw : Eq.mp (congrArg (fun z => ↥(GenLoop (Fin n) (topFunctor.obj Y) z)) h.symm)
      (cubeMap n f p) = GenLoop.map (topFunctor.map f).hom p :=
    GenLoop.closedSequential_eq_mp_symm h _
  exact (piNMap_apply n f (HomotopyGroup.mk p)).trans
    ((HomotopyGroup.closedSequential_eq_mp_mk h.symm (cubeMap n f p)).trans
      (congrArg HomotopyGroup.mk hraw)).symm

/-- The whole piNMap function is literally the quotient of the actual cube map. -/
theorem piNMap_eq_quotientMap (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    piNMap n f = Quotient.map (cubeMap n f) (fun _ _ h => cubeMap_homotopic n f h) := by
  funext a
  induction a using Quotient.inductionOn with
  | _ p => exact piNMap_mk n f p

/-- Every actual cube representative factors beyond any prescribed closed Nat stage. -/
theorem cube_stage_factor (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    (p : GenLoop (Fin n) (topFunctor.obj c.pt) (underlyingBasepoint c.pt)) (n₀ : ℕ) :
    ∃ (j : ℕ), n₀ ≤ j ∧ ∃ (q : GenLoop (Fin n) (topFunctor.obj (F.obj j))
      (underlyingBasepoint (F.obj j))), cubeMap n (c.ι.app j) q = p := by
  obtain ⟨j, hj, g, hg⟩ := ClosedSequentialColimit.exists_later_stage_of_compact
    c hc hF isCompact_univ p.1 n₀
  have hinj := (ClosedSequentialColimit.leg_isClosedEmbedding c hc hF j).injective
  have hb : ∀ t ∈ Cube.boundary (Fin n), g t = underlyingBasepoint (F.obj j) := by
    intro t ht
    apply hinj
    exact (ContinuousMap.congr_fun hg t).trans
      ((p.property t ht).trans (underlyingBasepoint_naturality (c.ι.app j)).symm)
  refine ⟨j, hj, ⟨g, hb⟩, ?_⟩
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  rw [cubeMap_apply]
  exact ContinuousMap.congr_fun hg t

/--
An actual relative homotopy of two included cubes factors through a common later
stage, retaining BOTH full endpoints, the whole boundary and the actual included homotopy map.
-/
theorem relative_homotopy_stage_factor (n : ℕ) {F : ℕ ⥤ PointedCGWH.{u, v}} (c : Cocone F)
    (hc : IsColimit c)
    (hF : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j),
      IsClosedEmbedding (ConcreteCategory.hom (F.map f).right))
    (i j : ℕ)
    (p : GenLoop (Fin n) (topFunctor.obj (F.obj i)) (underlyingBasepoint (F.obj i)))
    (q : GenLoop (Fin n) (topFunctor.obj (F.obj j)) (underlyingBasepoint (F.obj j)))
    (H : (cubeMap n (c.ι.app i) p).1.HomotopyRel (cubeMap n (c.ι.app j) q).1
      (Cube.boundary (Fin n))) :
    ∃ (k : ℕ) (hik : i ≤ k) (hjk : j ≤ k),
      ∃ (Hk : (cubeMap n (F.map (homOfLE hik)) p).1.HomotopyRel
        (cubeMap n (F.map (homOfLE hjk)) q).1 (Cube.boundary (Fin n))),
        (topFunctor.map (c.ι.app k)).hom.comp Hk.toHomotopy.toContinuousMap =
          H.toHomotopy.toContinuousMap := by
  obtain ⟨k, hk, g, hg⟩ := ClosedSequentialColimit.exists_later_stage_of_compact
    c hc hF isCompact_univ H.toHomotopy.toContinuousMap (max i j)
  have hik : i ≤ k := (le_max_left i j).trans hk
  have hjk : j ≤ k := (le_max_right i j).trans hk
  let φ : i ⟶ k := homOfLE hik
  let ψ : j ⟶ k := homOfLE hjk
  let pk := cubeMap n (F.map φ) p
  let qk := cubeMap n (F.map ψ) q
  have hpi : cubeMap n (c.ι.app k) pk = cubeMap n (c.ι.app i) p :=
    (cubeMap_comp n (F.map φ) (c.ι.app k) p).symm.trans
      (congrArg (fun f => cubeMap n f p) (c.w φ))
  have hqj : cubeMap n (c.ι.app k) qk = cubeMap n (c.ι.app j) q :=
    (cubeMap_comp n (F.map ψ) (c.ι.app k) q).symm.trans
      (congrArg (fun f => cubeMap n f q) (c.w ψ))
  have hp (t : Fin n → unitInterval) :
      (topFunctor.map (c.ι.app k)).hom (pk.1 t) = (cubeMap n (c.ι.app i) p).1 t :=
    (cubeMap_apply n (c.ι.app k) pk t).symm.trans (congrArg (fun r => r.1 t) hpi)
  have hq (t : Fin n → unitInterval) :
      (topFunctor.map (c.ι.app k)).hom (qk.1 t) = (cubeMap n (c.ι.app j) q).1 t :=
    (cubeMap_apply n (c.ι.app k) qk t).symm.trans (congrArg (fun r => r.1 t) hqj)
  have hH (z : unitInterval × (Fin n → unitInterval)) :
      (topFunctor.map (c.ι.app k)).hom (g z) = H z := ContinuousMap.congr_fun hg z
  have hinj := (ClosedSequentialColimit.leg_isClosedEmbedding c hc hF k).injective
  let Hk : pk.1.HomotopyRel qk.1 (Cube.boundary (Fin n)) :=
    { toHomotopy :=
        { toContinuousMap := g
          map_zero_left := fun t => hinj ((hH (0, t)).trans
            ((H.toHomotopy.map_zero_left t).trans (hp t).symm))
          map_one_left := fun t => hinj ((hH (1, t)).trans
            ((H.toHomotopy.map_one_left t).trans (hq t).symm)) }
      prop' := fun t x hx => hinj ((hH (t, x)).trans ((H.eq_fst t hx).trans (hp x).symm)) }
  exact ⟨k, hik, hjk, Hk, hg⟩

end PointedCGWH.CubeColimitGeometry
