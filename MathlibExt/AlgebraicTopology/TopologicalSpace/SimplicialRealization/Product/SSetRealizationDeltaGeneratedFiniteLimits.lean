/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUnderlyingFiniteLimits
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationCompactSupport
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.Product.SSetRealizationFiniteProductComparisonArbitrary
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.Topology.Category.DeltaGenerated
public import Mathlib.Topology.ContinuousOn

/-!
# Finite limits of delta-generated geometric realization

Let D:TopCat→DeltaGenerated be the coreflection to delta-generated spaces. For arbitrary
simplicial sets X,Y, applying D to the geometric-realization product comparison |X×Y|→|X|×|Y|
gives an isomorphism.

Geometric realization followed by D preserves finite categorical limits, including terminal
objects and equalizers. These statements hold in every simplicial-set and space universe u.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Topology
open scoped Simplicial

namespace SSet

private theorem limitPost_toTop_bijective
    {J : Type v} [Category.{v} J] (K : J ⥤ SSet.{u})
    [HasLimit K] [HasLimit (K ⋙ SSet.toTop)]
    [PreservesLimit K (SSet.toTop ⋙ forget TopCat)] :
    Function.Bijective (limit.post K SSet.toTop) := by
  let cTop := limit.post K SSet.toTop
  let cForget := limit.post (K ⋙ SSet.toTop) (forget TopCat)
  let _ : IsIso cForget := inferInstance
  let _ : IsIso ((forget TopCat).map cTop ≫ cForget) := by
    rw [limit.post_post]
    infer_instance
  let _ : IsIso ((forget TopCat).map cTop) :=
    IsIso.of_isIso_comp_right _ cForget
  exact (CategoryTheory.isIso_iff_bijective
    ((forget TopCat).map cTop)).mp inferInstance

private theorem prodComparison_toTop_bijective (X Y : SSet.{u}) :
    Function.Bijective (prodComparison SSet.toTop X Y) := by
  let cTop := prodComparison SSet.toTop X Y
  let cForget := prodComparison (forget TopCat)
    (SSet.toTop.obj X) (SSet.toTop.obj Y)
  let _ : IsIso cForget := inferInstance
  let _ : IsIso ((forget TopCat).map cTop ≫ cForget) := by
    rw [← prodComparison_comp]
    infer_instance
  let _ : IsIso ((forget TopCat).map cTop) :=
    IsIso.of_isIso_comp_right _ cForget
  exact (CategoryTheory.isIso_iff_bijective
    ((forget TopCat).map cTop)).mp inferInstance

private theorem prodComparison_inv_natural_apply
    {X Y X' Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p : ↑(SSet.toTop.obj X ⨯ SSet.toTop.obj Y))
    [IsIso (prodComparison SSet.toTop X Y)] :
    (prodComparison SSet.toTop X' Y')
      ((SSet.toTop.map (prod.map f g))
        ((inv (prodComparison SSet.toTop X Y)) p)) =
      (prod.map (SSet.toTop.map f) (SSet.toTop.map g)) p := by
  have hInvPt :
      (prodComparison SSet.toTop X Y)
        ((inv (prodComparison SSet.toTop X Y)) p) = p := by
    simpa only [ConcreteCategory.comp_apply, CategoryTheory.id_apply] using
      ConcreteCategory.congr_hom
        (IsIso.inv_hom_id (prodComparison SSet.toTop X Y)) p
  have hNat := prodComparison_natural (F := SSet.toTop) f g
  have hPoint := ConcreteCategory.congr_hom hNat
    ((inv (prodComparison SSet.toTop X Y)) p)
  simpa only [ConcreteCategory.comp_apply, hInvPt] using hPoint

private theorem exists_finite_subcomplex_factor
    {K : Type v} [TopologicalSpace K] [CompactSpace K] {X : SSet.{u}}
    (g : K → SSet.toTop.obj X) (hg : Continuous g) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{u}))
      (gA : K → SSet.toTop.obj (A : SSet.{u})),
      Continuous gA ∧ ∀ x, SSet.toTop.map A.ι (gA x) = g x := by
  have hRange : IsCompact (Set.range g) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image hg
  obtain ⟨A, hA, hsub⟩ :=
    SSet.exists_finite_subcomplex_of_isCompact X (Set.range g) hRange
  choose gA hgA using fun x : K => hsub (Set.mem_range_self x)
  have hEmb : IsEmbedding (SSet.toTop.map A.ι).hom :=
    (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι A).isEmbedding
  have hcont : Continuous gA := hEmb.continuous_iff.mpr (by
    apply hg.congr
    intro x
    exact (hgA x).symm)
  exact ⟨A, hA, gA, hcont, hgA⟩

private theorem prodComparison_inverse_continuousGeneratedBy
    (X Y : SSet.{u})
    (hbij : Function.Bijective (prodComparison SSet.toTop X Y)) :
    ContinuousGeneratedBy (fun n : ℕ => Fin n → ℝ)
      (Equiv.ofBijective (prodComparison SSet.toTop X Y) hbij).symm := by
  rw [continuousGeneratedBy_def]
  intro n q
  rw [continuous_iff_continuousAt]
  intro z
  let e := Equiv.ofBijective (prodComparison SSet.toTop X Y) hbij
  obtain ⟨K, hK, hKz⟩ := exists_compact_mem_nhds z
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let qK := q.restrict K
  let qX : K → SSet.toTop.obj X := fun w =>
    (prod.fst : SSet.toTop.obj X ⨯ SSet.toTop.obj Y ⟶ SSet.toTop.obj X) (qK w)
  let qY : K → SSet.toTop.obj Y := fun w =>
    (prod.snd : SSet.toTop.obj X ⨯ SSet.toTop.obj Y ⟶ SSet.toTop.obj Y) (qK w)
  have hqX : Continuous qX :=
    (prod.fst : SSet.toTop.obj X ⨯ SSet.toTop.obj Y ⟶
      SSet.toTop.obj X).hom.continuous.comp qK.continuous
  have hqY : Continuous qY :=
    (prod.snd : SSet.toTop.obj X ⨯ SSet.toTop.obj Y ⟶
      SSet.toTop.obj Y).hom.continuous.comp qK.continuous
  obtain ⟨A, hA, qA, hqA, hqAeq⟩ :=
    exists_finite_subcomplex_factor qX hqX
  let _ : SSet.Finite (A : SSet.{u}) := hA
  let _ : IsIso (prodComparison SSet.toTop (A : SSet.{u}) Y) :=
    SSet.isIso_prodComparison_toTop_finite_arbitrary _ _
  let pairMap : K → ↑(SSet.toTop.obj A ⨯ SSet.toTop.obj Y) :=
    fun w => (TopCat.prodIsoProd (SSet.toTop.obj A) (SSet.toTop.obj Y)).inv
      (qA w, qY w)
  have hpairMap : Continuous pairMap :=
    (TopCat.homeoOfIso
      (TopCat.prodIsoProd (SSet.toTop.obj A) (SSet.toTop.obj Y))).symm.continuous.comp
        (hqA.prodMk hqY)
  let localMap : K → SSet.toTop.obj (X ⨯ Y) := fun w =>
    SSet.toTop.map (prod.map A.ι (𝟙 Y))
      (inv (prodComparison SSet.toTop (A : SSet.{u}) Y) (pairMap w))
  have hlocalMap : Continuous localMap :=
    (SSet.toTop.map (prod.map A.ι (𝟙 Y))).hom.continuous.comp
      ((inv (prodComparison SSet.toTop (A : SSet.{u}) Y)).hom.continuous.comp
        hpairMap)
  have hlocal (w : K) : localMap w = e.symm (q w) := by
    apply hbij.1
    have hn := prodComparison_inv_natural_apply A.ι (𝟙 Y)
      (pairMap w)
    have hrhs : (prodComparison SSet.toTop X Y) (e.symm (q w)) = q w :=
      e.apply_symm_apply (q w)
    rw [hrhs]
    have hright :
        (prod.map (SSet.toTop.map A.ι) (SSet.toTop.map (𝟙 Y)))
            (pairMap w) = q w := by
      have hqK_apply : qK w = q w := rfl
      apply TopCat.prod_point_ext
      · calc
          (prod.fst : SSet.toTop.obj X ⨯ SSet.toTop.obj Y ⟶
              SSet.toTop.obj X)
              ((prod.map (SSet.toTop.map A.ι) (SSet.toTop.map (𝟙 Y)))
                (pairMap w)) =
              SSet.toTop.map A.ι
                ((prod.fst : SSet.toTop.obj A ⨯ SSet.toTop.obj Y ⟶
                  SSet.toTop.obj A) (pairMap w)) :=
            ConcreteCategory.congr_hom
              (prod.map_fst (SSet.toTop.map A.ι) (SSet.toTop.map (𝟙 Y)))
              (pairMap w)
          _ = SSet.toTop.map A.ι (qA w) := by
            rw [TopCat.prodIsoProd_inv_fst_apply]
          _ = qX w := hqAeq w
          _ = (prod.fst : SSet.toTop.obj X ⨯ SSet.toTop.obj Y ⟶
              SSet.toTop.obj X) (q w) := by
            exact congrArg
              (fun v => (prod.fst : SSet.toTop.obj X ⨯ SSet.toTop.obj Y ⟶
                SSet.toTop.obj X) v) hqK_apply
      · calc
          (prod.snd : SSet.toTop.obj X ⨯ SSet.toTop.obj Y ⟶
              SSet.toTop.obj Y)
              ((prod.map (SSet.toTop.map A.ι) (SSet.toTop.map (𝟙 Y)))
                (pairMap w)) =
              SSet.toTop.map (𝟙 Y)
                ((prod.snd : SSet.toTop.obj A ⨯ SSet.toTop.obj Y ⟶
                  SSet.toTop.obj Y) (pairMap w)) :=
            ConcreteCategory.congr_hom
              (prod.map_snd (SSet.toTop.map A.ι) (SSet.toTop.map (𝟙 Y)))
              (pairMap w)
          _ = qY w := by
            rw [TopCat.prodIsoProd_inv_snd_apply]
            simp
          _ = (prod.snd : SSet.toTop.obj X ⨯ SSet.toTop.obj Y ⟶
              SSet.toTop.obj Y) (q w) := by
            exact congrArg
              (fun v => (prod.snd : SSet.toTop.obj X ⨯ SSet.toTop.obj Y ⟶
                SSet.toTop.obj Y) v) hqK_apply
    exact hn.trans hright
  have hcontK : Continuous (fun w : K => e.symm (q w)) := by
    apply hlocalMap.congr
    intro w
    exact hlocal w
  have hOn : ContinuousOn (e.symm ∘ q) K := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun w : K => e.symm (q w))
    exact hcontK
  have hz : z ∈ K := mem_of_mem_nhds hKz
  exact (hOn z hz).continuousAt hKz

private theorem map_toDeltaGenerated_isIso_of_bijective_of_continuousGeneratedBy_inverse
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Function.Bijective f)
    (hinv : ContinuousGeneratedBy (fun n : ℕ => Fin n → ℝ)
      (Equiv.ofBijective f hf).symm) :
    IsIso (TopCat.toDeltaGenerated.map f) := by
  let e : (X : Type u) ≃ (Y : Type u) := Equiv.ofBijective f hf
  let fC :=
    (TopCat.toContinuousGeneratedByCat (fun n : ℕ => Fin n → ℝ)).map f
  let invC :
      (TopCat.toContinuousGeneratedByCat (fun n : ℕ => Fin n → ℝ)).obj Y ⟶
        (TopCat.toContinuousGeneratedByCat (fun n : ℕ => Fin n → ℝ)).obj X :=
    ContinuousGeneratedByCat.homMk e.symm hinv
  let _ : IsIso fC := ⟨⟨invC, by
    apply ConcreteCategory.hom_ext
    intro x
    exact e.symm_apply_apply x, by
    apply ConcreteCategory.hom_ext
    intro y
    exact e.apply_symm_apply y⟩⟩
  change IsIso (ContinuousGeneratedByCat.toGeneratedByTopCat.map fC)
  infer_instance

/-- For arbitrary simplicial sets X,Y in universe u, delta-generated coreflection sends the
canonical product comparison |X×Y|→|X|×|Y| to an isomorphism. -/
theorem isIso_map_prodComparison_toDeltaGenerated (X Y : SSet.{u}) :
    IsIso (TopCat.toDeltaGenerated.map
      (prodComparison SSet.toTop X Y)) := by
  let cTop := prodComparison SSet.toTop X Y
  let hbij := prodComparison_toTop_bijective X Y
  have hcont := prodComparison_inverse_continuousGeneratedBy X Y hbij
  exact map_toDeltaGenerated_isIso_of_bijective_of_continuousGeneratedBy_inverse
    cTop hbij hcont

private theorem isIso_prodComparison_toDeltaGenerated (X Y : SSet.{u}) :
    IsIso (prodComparison
      (SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}) X Y) := by
  let cTop := prodComparison SSet.toTop X Y
  have hMap : IsIso (TopCat.toDeltaGenerated.map cTop) :=
    isIso_map_prodComparison_toDeltaGenerated X Y
  have hTarget : IsIso (prodComparison TopCat.toDeltaGenerated
      (SSet.toTop.obj X) (SSet.toTop.obj Y)) := inferInstance
  rw [prodComparison_comp]
  exact IsIso.comp_isIso' hMap hTarget

private theorem preservesTerminal_toTop :
    PreservesLimit (Functor.empty.{0} SSet.{u}) SSet.toTop.{u} := by
  have hType : IsTerminal
      ((SSet.toTop.{u} ⋙ forget TopCat.{u}).obj (⊤_ SSet.{u})) :=
    IsTerminal.isTerminalObj (SSet.toTop.{u} ⋙ forget TopCat.{u})
      (⊤_ SSet.{u}) terminalIsTerminal
  let _ : Unique (SSet.toTop.obj (⊤_ SSet.{u}) : Type u) :=
    Types.isTerminalEquivUnique _ hType
  let _ : ∀ Y : TopCat.{u}, Unique (Y ⟶ SSet.toTop.obj (⊤_ SSet.{u})) :=
    fun Y =>
      { default := TopCat.ofHom ⟨fun _ => default, continuous_const⟩
        uniq := by
          intro f
          apply TopCat.hom_ext
          ext y
          exact Subsingleton.elim _ _ }
  have hTop : IsTerminal (SSet.toTop.obj (⊤_ SSet.{u})) :=
    IsTerminal.ofUnique _
  exact preservesTerminal_of_iso SSet.toTop
    (hTop.uniqueUpToIso terminalIsTerminal)

private theorem equalizerComparison_toTop_bijective
    {X Y : SSet.{u}} (f g : X ⟶ Y) :
    Function.Bijective (equalizerComparison f g SSet.toTop) := by
  let G := SSet.toTop.{u} ⋙ forget TopCat.{u}
  let c := equalizerComparison f g SSet.toTop
  let i := G.map (equalizer.ι f g)
  let j := (forget TopCat).map
    (equalizer.ι (SSet.toTop.map f) (SSet.toTop.map g))
  have hc : (forget TopCat).map c ≫ j = i := by
    exact (forget TopCat).congr_map
      (equalizerComparison_comp_π f g SSet.toTop)
  have hs := isLimitOfHasEqualizerOfPreservesLimit G f g
  have wi : i ≫ G.map f = i ≫ G.map g := by
    calc
      i ≫ G.map f = G.map (equalizer.ι f g ≫ f) := by
        dsimp [i]
        rw [Functor.map_comp]
      _ = G.map (equalizer.ι f g ≫ g) := by rw [equalizer.condition]
      _ = i ≫ G.map g := by
        dsimp [i]
        rw [Functor.map_comp]
  have hi : Function.Injective i := CategoryTheory.injective_of_mono i
  have hj : Function.Injective j := CategoryTheory.injective_of_mono j
  constructor
  · intro a b hab
    change (forget TopCat).map c a = (forget TopCat).map c b at hab
    apply hi
    calc
      i a = j ((forget TopCat).map c a) :=
        (ConcreteCategory.congr_hom hc a).symm
      _ = j ((forget TopCat).map c b) := congrArg (fun z => j z) hab
      _ = i b := ConcreteCategory.congr_hom hc b
  · intro y
    have hy : G.map f (j y) = G.map g (j y) := by
      simpa [j, G] using ConcreteCategory.congr_hom
        (equalizer.condition (SSet.toTop.map f) (SSet.toTop.map g)) y
    obtain ⟨x, hx, _⟩ := Types.unique_of_type_equalizer i wi hs (j y) hy
    refine ⟨x, hj ?_⟩
    calc
      j ((forget TopCat).map c x) = i x :=
        ConcreteCategory.congr_hom hc x
      _ = j y := hx

private theorem isIso_equalizerComparison_toTop
    {X Y : SSet.{u}} (f g : X ⟶ Y) :
    IsIso (equalizerComparison f g SSet.toTop) := by
  let c := equalizerComparison f g SSet.toTop
  have hbij : Function.Bijective c := equalizerComparison_toTop_bijective f g
  have hComp : IsEmbedding
      (c ≫ equalizer.ι (SSet.toTop.map f) (SSet.toTop.map g)) := by
    rw [equalizerComparison_comp_π]
    exact (SSet.closedT1Embeddings_toTop_map_of_mono
      (equalizer.ι f g)).isEmbedding
  have hEmb : IsEmbedding c := IsEmbedding.of_comp
    c.hom.continuous
    (equalizer.ι (SSet.toTop.map f) (SSet.toTop.map g)).hom.continuous hComp
  let e := hEmb.toHomeomorphOfSurjective hbij.2
  exact (TopCat.isIso_iff_isHomeomorph c).2 e.isHomeomorph

private theorem preservesEqualizer_toTop
    {X Y : SSet.{u}} (f g : X ⟶ Y) :
    PreservesLimit (parallelPair f g) SSet.toTop := by
  let _ : IsIso (equalizerComparison f g SSet.toTop) :=
    isIso_equalizerComparison_toTop f g
  exact PreservesEqualizer.of_iso_comparison (f := f) (g := g) SSet.toTop

private theorem preservesEqualizers_toTop :
    PreservesLimitsOfShape WalkingParallelPair SSet.toTop.{u} where
  preservesLimit {K} := by
    let _ : PreservesLimit
        (parallelPair (K.map WalkingParallelPairHom.left)
          (K.map WalkingParallelPairHom.right)) SSet.toTop :=
      preservesEqualizer_toTop _ _
    apply preservesLimit_of_iso_diagram SSet.toTop
      (diagramIsoParallelPair K).symm

private theorem preservesBinaryProducts_toDeltaGenerated :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}) := by
  let _ : ∀ {X Y : SSet.{u}},
      IsIso (prodComparison
        (SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}) X Y) :=
    fun {X Y} => isIso_prodComparison_toDeltaGenerated X Y
  exact preservesBinaryProducts_of_isIso_prodComparison _

set_option backward.privateInPublic true in
/-- Geometric realization followed by delta-generated coreflection preserves every finite
categorical limit in an arbitrary universe u. -/
noncomputable instance preservesFiniteLimits_toDeltaGenerated :
    PreservesFiniteLimits
      (SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}) := by
  let F := SSet.toTop.{u} ⋙ TopCat.toDeltaGenerated.{u}
  let _ : PreservesLimit (Functor.empty.{0} SSet.{u}) SSet.toTop.{u} :=
    preservesTerminal_toTop
  let _ : PreservesLimitsOfShape (Discrete PEmpty.{1}) SSet.toTop.{u} :=
    preservesLimitsOfShape_pempty_of_preservesTerminal SSet.toTop
  let _ : PreservesLimitsOfShape WalkingParallelPair SSet.toTop.{u} :=
    preservesEqualizers_toTop
  let _ : PreservesLimitsOfShape (Discrete WalkingPair) F :=
    preservesBinaryProducts_toDeltaGenerated
  let _ : PreservesLimitsOfShape (Discrete PEmpty.{1}) F := inferInstance
  let _ : PreservesLimitsOfShape WalkingParallelPair F := inferInstance
  let _ : PreservesFiniteProducts F :=
    PreservesFiniteProducts.of_preserves_binary_and_terminal F
  exact preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts F

end SSet
