/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.Subspace
public import MathlibExt.AlgebraicTopology.SingularHomology.SmallChains

/-!
# Subspace chains - basic

`subspaceIncl`, mono instance, range equality `range (toSSet.map subspaceIncl) = subordinateSet`,
coefficient-generic chain iso via `Subcomplex.toRange`,
homology iso `smallChainHomologyIsoSubspace` and its naturality
`smallChainHomologyIsoSubspace_naturality_inclusion`.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

namespace AlgebraicTopology

universe w v u

section SubspaceGeneral

variable {X : TopCat.{w}} (S : Set X)

lemma toSSetObjEquiv_map_naturality {Y : TopCat.{w}} (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj Y).obj n) :
    (X.toSSetObjEquiv n) ((TopCat.toSSet.map f).app n σ)
      = (ConcreteCategory.hom f).comp ((Y.toSSetObjEquiv n) σ) := rfl

/-- The `TopCat.toSSet.map (subspaceIncl)` is mono. -/
instance mono_toSSet_map_subspaceIncl :
    Mono (TopCat.toSSet.map (subspaceIncl S)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro g1 g2 h_eq
  have h1 := toSSetObjEquiv_map_naturality (Y := TopCat.of S) (subspaceIncl S) n g1
  have h2 := toSSetObjEquiv_map_naturality (Y := TopCat.of S) (subspaceIncl S) n g2
  have h_comp :
      (ConcreteCategory.hom (subspaceIncl S)).comp ((TopCat.of S).toSSetObjEquiv n g1)
        = (ConcreteCategory.hom (subspaceIncl S)).comp ((TopCat.of S).toSSetObjEquiv n g2) := by
    calc (ConcreteCategory.hom (subspaceIncl S)).comp ((TopCat.of S).toSSetObjEquiv n g1)
        = (X.toSSetObjEquiv n) ((TopCat.toSSet.map (subspaceIncl S)).app n g1) := h1.symm
      _ = (X.toSSetObjEquiv n) ((TopCat.toSSet.map (subspaceIncl S)).app n g2) := by rw [h_eq]
      _ = (ConcreteCategory.hom (subspaceIncl S)).comp ((TopCat.of S).toSSetObjEquiv n g2) := h2
  have h_inj : Function.Injective (ConcreteCategory.hom (subspaceIncl S)) := by
    rw [← TopCat.mono_iff_injective]
    infer_instance
  have h_cont :
      (TopCat.of S).toSSetObjEquiv n g1 = (TopCat.of S).toSSetObjEquiv n g2 := by
    ext z : 1
    have h_at : (ConcreteCategory.hom (subspaceIncl S)) (((TopCat.of S).toSSetObjEquiv n g1) z)
        = (ConcreteCategory.hom (subspaceIncl S)) (((TopCat.of S).toSSetObjEquiv n g2) z) := by
      have := DFunLike.congr_fun h_comp z
      simpa only [ContinuousMap.comp_apply] using this
    exact h_inj h_at
  exact (TopCat.toSSetObjEquiv (X := TopCat.of S) n).injective h_cont

/-- The SSet range of the subspace inclusion is exactly the subordinate set. -/
lemma range_subspaceIncl_eq_subordinateSet :
    SSet.Subcomplex.range (TopCat.toSSet.map (subspaceIncl S)) = subordinateSet (X := X) S := by
  ext n σ
  simp only [SSet.Subcomplex.range, Subfunctor.range_obj]
  constructor
  · rintro ⟨g, rfl⟩
    simp only [subordinateSet, Set.mem_ofPred_eq]
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    have h_nat := toSSetObjEquiv_map_naturality (Y := TopCat.of S) (subspaceIncl S) n g
    have h_eq : (X.toSSetObjEquiv n) ((TopCat.toSSet.map (subspaceIncl S)).app n g) z
        = (ConcreteCategory.hom (subspaceIncl S)) (((TopCat.of S).toSSetObjEquiv n) g z) := by
      have := DFunLike.congr_fun h_nat z
      simpa only [ContinuousMap.comp_apply] using this
    rw [h_eq]
    exact (((TopCat.of S).toSSetObjEquiv n) g z).2
  · intro h_sub
    have hmem : ∀ z, (X.toSSetObjEquiv n σ) z ∈ S := by
      intro z
      have : σ ∈ (subordinateSet (X := X) S).obj n := h_sub
      simp only [subordinateSet, Set.mem_ofPred_eq] at this
      exact this ⟨z, rfl⟩
    let τ : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), X) := X.toSSetObjEquiv n σ
    have h_cont : Continuous (Set.codRestrict τ S hmem) :=
      Continuous.subtype_mk τ.continuous hmem
    let τS : C(Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)), TopCat.of S) :=
      ⟨Set.codRestrict τ S hmem, h_cont⟩
    refine ⟨(TopCat.of S).toSSetObjEquiv n |>.symm τS, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    rw [toSSetObjEquiv_map_naturality]
    ext z
    rfl

end SubspaceGeneral

section SubspaceChainIso

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable (S : Set X) (R : C)

/-- The canonical chain isomorphism between singular chains of the subspace `S`
and its one-member small-chain complex, via the `Subcomplex.toRange` equivalence.
This is the generic, coefficient-polymorphic comparison. -/
noncomputable def subspaceChainIsoSubcomplex :
    ((singularChainComplexFunctor C).obj R).obj (TopCat.of S) ≅
      smallChainComplex (C := C) R (fun _ : Unit => S) := by
  let f : (TopCat.toSSet.obj (TopCat.of S)) ⟶ (TopCat.toSSet.obj X) :=
    TopCat.toSSet.map (subspaceIncl S)
  have h_range : SSet.Subcomplex.range f = subordinateSet (X := X) S :=
    range_subspaceIncl_eq_subordinateSet S
  have h_cover : subordinateCover (fun _ : Unit => S) = subordinateSet (X := X) S :=
    subordinateCover_singleton S
  haveI : Mono f := mono_toSSet_map_subspaceIncl S
  haveI : IsIso (SSet.Subcomplex.toRange f) := inferInstance
  let iso1 : (TopCat.toSSet.obj (TopCat.of S)) ≅ (SSet.Subcomplex.range f : SSet) :=
    asIso (SSet.Subcomplex.toRange f)
  let iso2 : (SSet.Subcomplex.range f : SSet) ≅ (subordinateSet (X := X) S : SSet) :=
    SSet.Subcomplex.eqToIso h_range
  let iso3 : (subordinateSet (X := X) S : SSet) ≅ (subordinateCover (fun _ : Unit => S) : SSet) :=
    SSet.Subcomplex.eqToIso h_cover.symm
  let iso_SSet : (TopCat.toSSet.obj (TopCat.of S)) ≅
      (subordinateCover (fun _ : Unit => S) : SSet) :=
    iso1 ≪≫ iso2 ≪≫ iso3
  exact (SSet.chainComplexFunctor C).obj R |>.mapIso iso_SSet

@[reassoc]
lemma subspaceChainIsoSubcomplex_hom_comp_smallChainInclusion :
    (subspaceChainIsoSubcomplex (C := C) S R).hom ≫
        smallChainInclusion (C := C) R (fun _ : Unit ↦ S) =
      ((singularChainComplexFunctor C).obj R).map (subspaceIncl S) := by
  change ((SSet.chainComplexFunctor C).obj R).map _ ≫
      ((SSet.chainComplexFunctor C).obj R).map _ =
    ((SSet.chainComplexFunctor C).obj R).map _
  rw [← Functor.map_comp]
  congr 1

end SubspaceChainIso

section SubspaceChainIsoNaturality

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable {S T : Set X} (hST : S ⊆ T) (R : C)

/-- Naturality of the primary subspace-chain isomorphism with respect to
subset inclusion.

For `S ⊆ T`, the square formed by the singular-chain map of
`subspaceInclOfSubset`, the two subspace isomorphisms `subspaceChainIsoSubcomplex`,
and the primary refinement `smallChainMapOfLE` commutes.

The proof is purely categorical: both composites agree after post-composing
with the mono `smallChainInclusion T`, using the inclusion triangle
`subspaceChainIsoSubcomplex_hom_comp_smallChainInclusion`,
the refinement identity `smallChainMapOfLE_comp_inclusion`,
functoriality of singular chains, and the TopCat equality
`subspaceInclOfSubset_comp`. -/
theorem subspaceChainIsoSubcomplex_naturality_inclusion :
    (subspaceChainIsoSubcomplex (C := C) S R).hom ≫
      smallChainMapOfLE (C := C) R (fun _ : Unit => S) (fun _ : Unit => T)
        (by
          rw [subordinateCover_singleton, subordinateCover_singleton]
          exact subordinateSet_mono hST) =
    ((singularChainComplexFunctor C).obj R).map (subspaceInclOfSubset hST) ≫
      (subspaceChainIsoSubcomplex (C := C) T R).hom := by
  have h_le : subordinateCover (X := X) (fun _ : Unit => S) ≤
      subordinateCover (fun _ : Unit => T) := by
    rw [subordinateCover_singleton, subordinateCover_singleton]
    exact subordinateSet_mono hST
  have h_eq : smallChainMapOfLE (C := C) R (fun _ : Unit => S) (fun _ : Unit => T)
      (by
        rw [subordinateCover_singleton, subordinateCover_singleton]
        exact subordinateSet_mono hST) =
      smallChainMapOfLE R (fun _ : Unit => S) (fun _ : Unit => T) h_le := rfl
  rw [h_eq]
  apply (cancel_mono (smallChainInclusion (C := C) R (fun _ : Unit => T))).mp
  have left_eq : ((subspaceChainIsoSubcomplex (C := C) S R).hom ≫
        smallChainMapOfLE R (fun _ : Unit => S) (fun _ : Unit => T) h_le) ≫
          smallChainInclusion (C := C) R (fun _ : Unit => T) =
      ((singularChainComplexFunctor C).obj R).map (subspaceIncl S) := by
    rw [Category.assoc]
    rw [smallChainMapOfLE_comp_inclusion]
    rw [subspaceChainIsoSubcomplex_hom_comp_smallChainInclusion]
  have right_eq : (((singularChainComplexFunctor C).obj R).map (subspaceInclOfSubset hST) ≫
        (subspaceChainIsoSubcomplex (C := C) T R).hom) ≫
          smallChainInclusion (C := C) R (fun _ : Unit => T) =
      ((singularChainComplexFunctor C).obj R).map (subspaceIncl S) := by
    rw [Category.assoc]
    rw [subspaceChainIsoSubcomplex_hom_comp_smallChainInclusion]
    have h_map_comp :
        ((singularChainComplexFunctor C).obj R).map (subspaceInclOfSubset hST) ≫
            ((singularChainComplexFunctor C).obj R).map (subspaceIncl T) =
          ((singularChainComplexFunctor C).obj R).map
              (subspaceInclOfSubset hST ≫ subspaceIncl T) :=
      (((singularChainComplexFunctor C).obj R).map_comp
          (subspaceInclOfSubset hST) (subspaceIncl T)).symm
    have h_comp :
        ((singularChainComplexFunctor C).obj R).map
            (subspaceInclOfSubset hST ≫ subspaceIncl T) =
          ((singularChainComplexFunctor C).obj R).map (subspaceIncl S) := by
      rw [subspaceInclOfSubset_comp]
    exact h_map_comp.trans h_comp
  rw [left_eq, right_eq]

end SubspaceChainIsoNaturality

section SubspaceChainIsoNaturalityCross

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
variable {X Y : TopCat.{w}} {S : Set X} {T : Set Y}

theorem subspaceChainIsoSubcomplex_naturality
    (f : X ⟶ Y) (h : Set.MapsTo f S T) (R : C) :
    (subspaceChainIsoSubcomplex S R).hom ≫
        smallChainMapOfMapsTo R f (fun _ : Unit => S) (fun _ : Unit => T)
          (fun _ => ⟨(), h⟩) =
      ((singularChainComplexFunctor C).obj R).map (subspaceMap f h) ≫
        (subspaceChainIsoSubcomplex T R).hom := by
  let F := (SSet.chainComplexFunctor C).obj R
  let eS := subspaceChainIsoSubcomplex (C := C) S R
  let eT := subspaceChainIsoSubcomplex (C := C) T R
  let m := smallChainMapOfMapsTo R f (fun _ : Unit => S) (fun _ : Unit => T)
      (fun _ => ⟨(), h⟩)
  let iS := smallChainInclusion R (fun _ : Unit => S)
  let iT := smallChainInclusion R (fun _ : Unit => T)
  let sf := F.map (TopCat.toSSet.map (subspaceMap f h))
  let fRaw := F.map (TopCat.toSSet.map f)
  let eS_hom : F.obj (TopCat.toSSet.obj (TopCat.of S)) ⟶
      smallChainComplex R (fun _ : Unit => S) := by
    change F.obj (TopCat.toSSet.obj (TopCat.of S)) ⟶ smallChainComplex R (fun _ : Unit => S)
    exact eS.hom
  let eT_hom : F.obj (TopCat.toSSet.obj (TopCat.of T)) ⟶
      smallChainComplex R (fun _ : Unit => T) := by
    change F.obj (TopCat.toSSet.obj (TopCat.of T)) ⟶ smallChainComplex R (fun _ : Unit => T)
    exact eT.hom
  change eS_hom ≫ m = sf ≫ eT_hom
  have hMap : m ≫ iT = iS ≫ fRaw := by
    change m ≫ iT = iS ≫ F.map (TopCat.toSSet.map f)
    exact smallChainMapOfMapsTo_comp_inclusion R f _ _ _
  have hS : eS_hom ≫ iS = F.map (TopCat.toSSet.map (subspaceIncl S)) := by
    change eS.hom ≫ iS = ((singularChainComplexFunctor C).obj R).map (subspaceIncl S)
    exact subspaceChainIsoSubcomplex_hom_comp_smallChainInclusion (C := C) S R
  have hT : eT_hom ≫ iT = F.map (TopCat.toSSet.map (subspaceIncl T)) := by
    change eT.hom ≫ iT = ((singularChainComplexFunctor C).obj R).map (subspaceIncl T)
    exact subspaceChainIsoSubcomplex_hom_comp_smallChainInclusion (C := C) T R
  have hTop : TopCat.toSSet.map (subspaceMap f h) ≫ TopCat.toSSet.map (subspaceIncl T) =
      TopCat.toSSet.map (subspaceIncl S) ≫ TopCat.toSSet.map f := by
    rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp, subspaceMap_comp_subspaceIncl]
  have hLeftPath : (eS_hom ≫ m) ≫ iT =
      F.map (TopCat.toSSet.map (subspaceIncl S) ≫ TopCat.toSSet.map f) := by
    calc (eS_hom ≫ m) ≫ iT
        = eS_hom ≫ (m ≫ iT) := by rw [Category.assoc]
      _ = eS_hom ≫ (iS ≫ fRaw) := by rw [hMap]
      _ = (eS_hom ≫ iS) ≫ fRaw := by rw [← Category.assoc]
      _ = F.map (TopCat.toSSet.map (subspaceIncl S)) ≫ fRaw := by rw [hS]
      _ = F.map (TopCat.toSSet.map (subspaceIncl S) ≫ TopCat.toSSet.map f) := by
          rw [← Functor.map_comp]
  have hRightPath : (sf ≫ eT_hom) ≫ iT =
      F.map (TopCat.toSSet.map (subspaceIncl S) ≫ TopCat.toSSet.map f) := by
    calc (sf ≫ eT_hom) ≫ iT
        = sf ≫ (eT_hom ≫ iT) := by rw [Category.assoc]
      _ = sf ≫ F.map (TopCat.toSSet.map (subspaceIncl T)) := by rw [hT]
      _ = F.map (TopCat.toSSet.map (subspaceMap f h) ≫ TopCat.toSSet.map (subspaceIncl T)) := by
          rw [← Functor.map_comp]
      _ = F.map (TopCat.toSSet.map (subspaceIncl S) ≫ TopCat.toSSet.map f) := by rw [hTop]
  apply (cancel_mono iT).mp
  change (eS_hom ≫ m) ≫ iT = (sf ≫ eT_hom) ≫ iT
  rw [hLeftPath, hRightPath]

/-- After entering singular chains through the inverse subspace comparison,
the ambient path agrees with mapping through the target subspace and then
including it. -/
theorem subspaceChainIsoSubcomplex_inv_comp_ambient_naturality
    (f : X ⟶ Y) (h : Set.MapsTo f S T) (R : C) :
    ((subspaceChainIsoSubcomplex (C := C) S R).inv ≫
        singularChainMap R (subspaceIncl S)) ≫
      singularChainMap R f =
    ((subspaceChainIsoSubcomplex (C := C) S R).inv ≫
        singularChainMap R (subspaceMap f h)) ≫
      singularChainMap R (subspaceIncl T) := by
  let F := (SSet.chainComplexFunctor C).obj R
  let eS := subspaceChainIsoSubcomplex (C := C) S R
  let eS_inv : smallChainComplex R (fun _ : Unit => S) ⟶
      F.obj (TopCat.toSSet.obj (TopCat.of S)) := by
    change smallChainComplex R (fun _ : Unit => S) ⟶
      F.obj (TopCat.toSSet.obj (TopCat.of S))
    exact eS.inv
  change (eS_inv ≫ F.map (TopCat.toSSet.map (subspaceIncl S))) ≫
      F.map (TopCat.toSSet.map f) =
    (eS_inv ≫ F.map (TopCat.toSSet.map (subspaceMap f h))) ≫
      F.map (TopCat.toSSet.map (subspaceIncl T))
  calc
    (eS_inv ≫ F.map (TopCat.toSSet.map (subspaceIncl S))) ≫
          F.map (TopCat.toSSet.map f) =
        eS_inv ≫ F.map
          (TopCat.toSSet.map (subspaceIncl S) ≫ TopCat.toSSet.map f) := by
      rw [Category.assoc, ← F.map_comp]
    _ = eS_inv ≫ F.map
        (TopCat.toSSet.map (subspaceMap f h) ≫
          TopCat.toSSet.map (subspaceIncl T)) := by
      rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp,
        subspaceMap_comp_subspaceIncl]
    _ = (eS_inv ≫ F.map (TopCat.toSSet.map (subspaceMap f h))) ≫
        F.map (TopCat.toSSet.map (subspaceIncl T)) := by
      rw [F.map_comp, ← Category.assoc]

end SubspaceChainIsoNaturalityCross

section SubspaceHomologyIso

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable (S : Set X) (R : C) (n : ℕ)

/-- Homology iso between the one-member small-chain complex of `S` and
the singular homology of `TopCat.of S`. -/
noncomputable def smallChainHomologyIsoSubspace :
    (smallChainComplex (C := C) R (fun _ : Unit => S)).homology n ≅
      ((singularHomologyFunctor C n).obj R).obj (TopCat.of S) :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down Nat) n).mapIso
    (subspaceChainIsoSubcomplex (C := C) S R).symm

@[simp]
lemma smallChainHomologyIsoSubspace_hom :
    (smallChainHomologyIsoSubspace (C := C) S R n).hom =
      HomologicalComplex.homologyMap (subspaceChainIsoSubcomplex (C := C) S R).inv n := rfl

@[simp]
lemma smallChainHomologyIsoSubspace_inv :
    (smallChainHomologyIsoSubspace (C := C) S R n).inv =
      HomologicalComplex.homologyMap (subspaceChainIsoSubcomplex (C := C) S R).hom n := rfl

end SubspaceHomologyIso

section SubspaceHomologyIsoNaturality

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {S T : Set X} (hST : S ⊆ T) (R : C) (n : ℕ)

/-- Naturality of `smallChainHomologyIsoSubspace` with respect to subset inclusion. -/
theorem smallChainHomologyIsoSubspace_naturality_inclusion :
    HomologicalComplex.homologyMap
        (smallChainMapOfLE (C := C) R (fun _ : Unit => S) (fun _ : Unit => T)
          (by
            rw [subordinateCover_singleton, subordinateCover_singleton]
            exact subordinateSet_mono hST)) n ≫
      (smallChainHomologyIsoSubspace (C := C) T R n).hom =
    (smallChainHomologyIsoSubspace (C := C) S R n).hom ≫
      ((singularHomologyFunctor C n).obj R).map (subspaceInclOfSubset hST) := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  apply congrArg (fun f => HomologicalComplex.homologyMap f n)
  rw [← cancel_epi (subspaceChainIsoSubcomplex (C := C) S R).hom]
  simp only [← Category.assoc]
  rw [subspaceChainIsoSubcomplex_naturality_inclusion (C := C) hST R]
  simp

end SubspaceHomologyIsoNaturality

section SubspaceHomologyIsoNaturalityCross

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {X Y : TopCat.{w}} {S : Set X} {T : Set Y}

theorem smallChainHomologyIsoSubspace_naturality
    (f : X ⟶ Y) (h : Set.MapsTo f S T) (R : C) (n : ℕ) :
    HomologicalComplex.homologyMap
        (smallChainMapOfMapsTo R f (fun _ : Unit => S) (fun _ : Unit => T)
          (fun _ => ⟨(), h⟩)) n ≫
      (smallChainHomologyIsoSubspace T R n).hom =
    (smallChainHomologyIsoSubspace S R n).hom ≫
      ((singularHomologyFunctor C n).obj R).map (subspaceMap f h) := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  apply congrArg (fun f => HomologicalComplex.homologyMap f n)
  rw [← cancel_epi (subspaceChainIsoSubcomplex (C := C) S R).hom]
  simp only [← Category.assoc]
  rw [subspaceChainIsoSubcomplex_naturality (C := C) f h R]
  simp

end SubspaceHomologyIsoNaturalityCross

end AlgebraicTopology
