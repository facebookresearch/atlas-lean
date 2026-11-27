/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationCompactSupport
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.ContinuousMap.Sigma

/-!
# Finite connected factorization of maps into realizations

A continuous map from a compact path-connected space into the realization of a
simplicial set factors through the realization of a finite connected simplicial
set mapping monomorphically to the original one. The source space and both
simplicial sets remain in the specified universe.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

noncomputable section

universe u

/--
For a map from a compact path-connected space to `|X|`, there exist a finite
connected simplicial set `Y`, a monomorphism `Y → X`, and a continuous map
to `|Y|` whose composite with the realized monomorphism is the given map.
-/
theorem SSet.exists_factor_thru_finite_connected_of_topCatHom
    {X : SSet.{u}} {K : TopCat.{u}}
    [CompactSpace K] [PathConnectedSpace K]
    (f : K ⟶ SSet.toTop.obj X) :
    ∃ (Y : SSet.{u}) (_ : Y.Finite) (_ : Y.IsConnected)
      (i : Y ⟶ X) (_ : Mono i) (g : K ⟶ SSet.toTop.obj Y),
      f = g ≫ SSet.toTop.map i := by
  classical
  have hcompact : IsCompact (Set.range f) :=
    isCompact_range f.hom.continuous
  obtain ⟨A, hAfin, hsub⟩ :=
    SSet.exists_finite_subcomplex_of_isCompact X (Set.range f) hcompact
  let _ : SSet.Finite (A : SSet.{u}) := hAfin
  let e : SSet.toTop.obj (A : SSet.{u}) ⟶ SSet.toTop.obj X :=
    SSet.toTop.map A.ι
  have he : IsEmbedding e :=
    (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι (S := A)).isEmbedding
  let fr : C(K, Set.range e) :=
    ⟨fun z ↦ ⟨f z, hsub ⟨z, rfl⟩⟩,
      f.hom.continuous.subtype_mk _⟩
  let hInv : C(Set.range e, SSet.toTop.obj (A : SSet.{u})) :=
    ⟨he.toHomeomorph.symm, he.toHomeomorph.symm.continuous⟩
  let fA : K ⟶ SSet.toTop.obj (A : SSet.{u}) :=
    TopCat.ofHom (hInv.comp fr)
  have hfA : f = fA ≫ e := by
    ext z
    have hz := he.toHomeomorph.apply_symm_apply (fr z)
    change (fr z).val = e (he.toHomeomorph.symm (fr z))
    exact (congrArg Subtype.val hz).symm
  let F : SSet.π₀ (A : SSet.{u}) → TopCat.{u} := fun c ↦
    SSet.toTop.obj (SSet.π₀.component c : SSet.{u})
  let hc : IsColimit
      (SSet.toTop.mapCocone (SSet.π₀.cofan (A : SSet.{u}))) :=
    isColimitOfPreserves SSet.toTop (SSet.π₀.isColimitCofan (A : SSet.{u}))
  let hc' : IsColimit
      (Cofan.mk (SSet.toTop.obj (A : SSet.{u}))
        (fun c ↦ SSet.toTop.map (SSet.π₀.component c).ι) :
        Cofan fun c : SSet.π₀ (A : SSet.{u}) ↦
          SSet.toTop.obj (SSet.π₀.component c : SSet.{u})) :=
    (isColimitMapCoconeCofanMkEquiv
      (G := SSet.toTop)
      (f := fun c : SSet.π₀ (A : SSet.{u}) ↦
        (SSet.π₀.component c : SSet.{u}))
      (fun c ↦ (SSet.π₀.component c).ι)) hc
  let hsigma : IsColimit (TopCat.sigmaCofan F) :=
    TopCat.sigmaCofanIsColimit F
  let eComp : SSet.toTop.obj (A : SSet.{u}) ≅ TopCat.of (Σ c, F c) :=
    IsColimit.coconePointUniqueUpToIso
      (s := Cofan.mk (SSet.toTop.obj (A : SSet.{u}))
        (fun c ↦ SSet.toTop.map (SSet.π₀.component c).ι))
      (t := TopCat.sigmaCofan F) hc' hsigma
  have hleg (c : SSet.π₀ (A : SSet.{u})) :
      SSet.toTop.map (SSet.π₀.component c).ι ≫ eComp.hom =
        TopCat.sigmaι F c := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom hc' hsigma ⟨c⟩
  let H := ContinuousMap.sigmaCodHomeomorph K (fun c ↦ (F c : Type u))
  let q : C(K, Σ c, F c) := (fA ≫ eComp.hom).hom
  rcases hp : H q with ⟨c, gc⟩
  have hq : q = (ContinuousMap.sigmaMk c).comp gc := by
    calc
      q = H.symm (H q) := (H.symm_apply_apply q).symm
      _ = H.symm ⟨c, gc⟩ := congrArg H.symm hp
      _ = (ContinuousMap.sigmaMk c).comp gc := by simp [H]
  let g : K ⟶ F c := TopCat.ofHom gc
  have hqTop : fA ≫ eComp.hom = g ≫ TopCat.sigmaι F c := by
    apply ConcreteCategory.hom_ext
    intro z
    exact DFunLike.congr_fun hq z
  have hfAcomp :
      fA = g ≫ SSet.toTop.map (SSet.π₀.component c).ι := by
    apply (cancel_mono eComp.hom).mp
    simpa only [Category.assoc, hleg] using hqTop
  refine ⟨(SSet.π₀.component c : SSet.{u}), inferInstance, inferInstance,
    (SSet.π₀.component c).ι ≫ A.ι, inferInstance, g, ?_⟩
  calc
    f = fA ≫ SSet.toTop.map A.ι := hfA
    _ = (g ≫ SSet.toTop.map (SSet.π₀.component c).ι) ≫
        SSet.toTop.map A.ι := by rw [hfAcomp]
    _ = g ≫ SSet.toTop.map ((SSet.π₀.component c).ι ≫ A.ι) := by
      simp only [Functor.map_comp, Category.assoc]
