/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.Homotopy.VanKampen
public import MathlibExt.Topology.Homotopy.PathOpenCoverGrid
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Fullness of one leg in a fundamental-groupoid van Kampen square

For an open two-set cover, suppose that the overlap inclusion into the
second open set is full and essentially surjective on fundamental
groupoids.  Then every path class between points of the first open set can
be represented inside that first open set.

The proof uses an actual subordinate finite path grid.  Vertices outside
the first open set are moved to chosen overlap representatives.  A path
piece in the second open set is conjugated by those chosen connectors and
lifted through fullness of the overlap functor.  The connectors cancel in
the finite product, while the subpath classes telescope back to the
original path class.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u

namespace MathlibExt.Topology.Homotopy.VanKampenWanted

/-- The Bool-indexed open cover whose two values are the original open
subsets `U` and `V`. -/
public def twoSetOpenCover {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    Bool → TopologicalSpace.Opens X
  | false => ⟨U, hU⟩
  | true => ⟨V, hV⟩

private theorem twoSetOpenCover_isOpenCover {X : Type u} [TopologicalSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hCover : U ∪ V = Set.univ) :
    TopologicalSpace.IsOpenCover (twoSetOpenCover U V hU hV) := by
  apply TopologicalSpace.IsOpenCover.mk
  ext y
  simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion,
    TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  have hy : y ∈ U ∪ V := by rw [hCover]; exact Set.mem_univ y
  rcases hy with hyU | hyV
  · exact ⟨false, hyU⟩
  · exact ⟨true, hyV⟩

/-- View a path whose range lies in a set as a path in that subtype. -/
private def restrictPath {X : Type u} [TopologicalSpace X]
    (W : Set X) {a b : X} (p : Path a b) (hp : Set.range p ⊆ W) :
    Path (⟨a, hp ⟨0, p.source⟩⟩ : W) (⟨b, hp ⟨1, p.target⟩⟩ : W) where
  toFun t := ⟨p t, hp ⟨t, rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk (fun t => hp ⟨t, rfl⟩)
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

private theorem restrictPath_map_inclusion
    {X : Type u} [TopologicalSpace X] (W : Set X)
    {a b : X} (p : Path a b) (hp : Set.range p ⊆ W) :
    (Path.Homotopic.Quotient.mk (restrictPath W p hp)).map
        (inclusionSub W) = Path.Homotopic.Quotient.mk p := by
  change Path.Homotopic.Quotient.mk
      ((restrictPath W p hp).map (inclusionSub W).continuous) = _
  congr 1

private theorem mem_right_of_not_mem_left {X : Type u}
    {U V : Set X} (hCover : U ∪ V = Set.univ) {y : X} (hyU : y ∉ U) : y ∈ V := by
  have hy : y ∈ U ∪ V := by rw [hCover]; exact Set.mem_univ y
  exact hy.resolve_left hyU

private abbrev interRightFunctor
    {X : Type u} [TopologicalSpace X] (U V : Set X) :
    FundamentalGroupoid ↥(U ∩ V) ⥤ FundamentalGroupoid ↥V :=
  FundamentalGroupoid.map (inclusionInterRight U V)

private abbrev inclusionFunctor
    {X : Type u} [TopologicalSpace X] (W : Set X) :
    FundamentalGroupoid ↥W ⥤ FundamentalGroupoid X :=
  FundamentalGroupoid.map (inclusionSub W)

private theorem overlap_square
    {X : Type u} [TopologicalSpace X] (U V : Set X) :
    FundamentalGroupoid.map (inclusionInterLeft U V) ⋙ inclusionFunctor U =
      interRightFunctor U V ⋙ inclusionFunctor V := by
  rw [← FundamentalGroupoid.map_comp, ← FundamentalGroupoid.map_comp]
  rfl

private theorem eqToHom_eq {C : Type*} [Category C]
    {A B : C} (p q : A = B) : eqToHom p = eqToHom q := by
  subst p
  rfl

private theorem eqToHom_comp3 {C : Type*} [Category C]
    {A B D E : C} (p : A = B) (q : B = D) (r : D = E) :
    eqToHom p ≫ eqToHom q ≫ eqToHom r = eqToHom (p.trans (q.trans r)) := by
  subst p
  subst q
  subst r
  simp

private noncomputable def overlapRepresentative
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    [(interRightFunctor U V).EssSurj]
    (y : X) (hyV : y ∈ V) : ↥(U ∩ V) := by
  classical
  by_cases hyU : y ∈ U
  · exact ⟨y, hyU, hyV⟩
  · exact ((interRightFunctor U V).objPreimage
      (FundamentalGroupoid.mk ⟨y, hyV⟩)).as

private noncomputable def overlapRepresentativeIso
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    [(interRightFunctor U V).EssSurj]
    (y : X) (hyV : y ∈ V) :
    (interRightFunctor U V).obj
        (FundamentalGroupoid.mk (overlapRepresentative y hyV)) ≅
      FundamentalGroupoid.mk (⟨y, hyV⟩ : V) := by
  classical
  by_cases hyU : y ∈ U
  · refine eqToIso ?_
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    simp [interRightFunctor, overlapRepresentative, hyU, inclusionInterRight]
  · simpa [interRightFunctor, overlapRepresentative, hyU] using
      (interRightFunctor U V).objObjPreimageIso
        (FundamentalGroupoid.mk (⟨y, hyV⟩ : V))

private noncomputable def uRepresentative
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).EssSurj] (y : X) : U := by
  classical
  by_cases hyU : y ∈ U
  · exact ⟨y, hyU⟩
  · let hyV : y ∈ V := mem_right_of_not_mem_left hCover hyU
    let z := overlapRepresentative (U := U) (V := V) y hyV
    exact ⟨z.1, z.2.1⟩

private theorem uRepresentative_of_mem_left
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).EssSurj] (y : X) (hyU : y ∈ U) :
    uRepresentative hCover y = (⟨y, hyU⟩ : U) := by
  classical
  simp [uRepresentative, hyU]

private theorem uRepresentative_eq_overlap_left
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).EssSurj] (y : X) (hyV : y ∈ V) :
    uRepresentative hCover y =
      (⟨(overlapRepresentative (U := U) y hyV).1,
        (overlapRepresentative (U := U) y hyV).2.1⟩ : U) := by
  classical
  by_cases hyU : y ∈ U
  · apply Subtype.ext
    simp [uRepresentative, overlapRepresentative, hyU]
  · apply Subtype.ext
    simp only [uRepresentative, hyU, ↓reduceDIte]

private noncomputable def uPointIso
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).EssSurj] (y : X) (hyU : y ∈ U) :
    FundamentalGroupoid.mk (uRepresentative hCover y) ≅
      FundamentalGroupoid.mk (⟨y, hyU⟩ : U) :=
  eqToIso (congrArg FundamentalGroupoid.mk
    (uRepresentative_of_mem_left hCover y hyU))

private theorem uRepresentative_overlap_obj_eq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).EssSurj] (y : X) (hyV : y ∈ V) :
    FundamentalGroupoid.mk (uRepresentative hCover y) =
      (FundamentalGroupoid.map (inclusionInterLeft U V)).obj
        (FundamentalGroupoid.mk (overlapRepresentative (U := U) y hyV)) := by
  apply FundamentalGroupoid.ext
  change uRepresentative hCover y =
    (⟨(overlapRepresentative (U := U) y hyV).1,
      (overlapRepresentative (U := U) y hyV).2.1⟩ : U)
  exact uRepresentative_eq_overlap_left hCover y hyV

private noncomputable def uOverlapIso
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).EssSurj] (y : X) (hyV : y ∈ V) :
    FundamentalGroupoid.mk (uRepresentative hCover y) ≅
      (FundamentalGroupoid.map (inclusionInterLeft U V)).obj
        (FundamentalGroupoid.mk (overlapRepresentative (U := U) y hyV)) :=
  eqToIso (uRepresentative_overlap_obj_eq hCover y hyV)

/-- The selected first-open-set representative is connected to the original
vertex.  On vertices already in the first open set this is the identity;
otherwise it is the chosen overlap-to-second-set isomorphism mapped into
the ambient groupoid. -/
private noncomputable def vertexIso
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).EssSurj] (y : X) :
    (inclusionFunctor U).obj
        (FundamentalGroupoid.mk (uRepresentative hCover y)) ≅
      FundamentalGroupoid.mk y := by
  classical
  by_cases hyU : y ∈ U
  · exact (inclusionFunctor U).mapIso (uPointIso hCover y hyU)
  · let hyV : y ∈ V := mem_right_of_not_mem_left hCover hyU
    let eV := overlapRepresentativeIso (U := U) y hyV
    exact (inclusionFunctor U).mapIso (uOverlapIso hCover y hyV) ≪≫
      eqToIso (Functor.congr_obj (overlap_square U V)
        (FundamentalGroupoid.mk (overlapRepresentative (U := U) y hyV))) ≪≫
      (inclusionFunctor V).mapIso eV

private theorem vertexIso_hom_of_mem_right
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).EssSurj] (y : X) (hyV : y ∈ V) :
    (inclusionFunctor U).map (uOverlapIso hCover y hyV).hom ≫
        eqToHom (Functor.congr_obj (overlap_square U V)
          (FundamentalGroupoid.mk (overlapRepresentative (U := U) y hyV))) ≫
        (inclusionFunctor V).map (overlapRepresentativeIso (U := U) y hyV).hom =
      (vertexIso hCover y).hom := by
  classical
  by_cases hyU : y ∈ U
  · simp only [vertexIso, hyU, ↓reduceDIte, Functor.mapIso_hom]
    unfold uOverlapIso uPointIso
    simp only [overlapRepresentativeIso, hyU, ↓reduceDIte]
    dsimp only [eqToIso]
    rw [eqToHom_map, eqToHom_map, eqToHom_map]
    exact (eqToHom_comp3 _ _ _).trans (eqToHom_eq _ _)
  · simp only [vertexIso, hyU, ↓reduceDIte, Iso.trans_hom,
      Functor.mapIso_hom]
    rfl

private theorem vertexIso_inv_of_mem_right
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).EssSurj] (y : X) (hyV : y ∈ V) :
    (inclusionFunctor V).map (overlapRepresentativeIso (U := U) y hyV).inv ≫
        eqToHom (Functor.congr_obj (overlap_square U V)
          (FundamentalGroupoid.mk (overlapRepresentative (U := U) y hyV))).symm ≫
        (inclusionFunctor U).map (uOverlapIso hCover y hyV).inv =
      (vertexIso hCover y).inv := by
  let eTotal :=
    (inclusionFunctor U).mapIso (uOverlapIso hCover y hyV) ≪≫
      eqToIso (Functor.congr_obj (overlap_square U V)
        (FundamentalGroupoid.mk (overlapRepresentative (U := U) y hyV))) ≪≫
      (inclusionFunctor V).mapIso (overlapRepresentativeIso (U := U) y hyV)
  have hHom : eTotal.hom = (vertexIso hCover y).hom := by
    dsimp only [eTotal, Iso.trans_hom, Functor.mapIso_hom, eqToIso]
    simpa only [Category.assoc] using
      vertexIso_hom_of_mem_right hCover y hyV
  have hIso : eTotal = vertexIso hCover y := Iso.ext hHom
  have hInv := congrArg Iso.inv hIso
  dsimp only [eTotal, Iso.trans_inv, Functor.mapIso_inv, eqToIso] at hInv
  simpa only [Category.assoc] using hInv

/-- Replace one path piece subordinate to the two-set cover by an arrow in
the first open set, between the selected representatives of its endpoints. -/
private noncomputable def liftSmallPath
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).Full] [(interRightFunctor U V).EssSurj]
    {a b : X} (p : Path a b)
    (hp : Set.range p ⊆ U ∨ Set.range p ⊆ V) :
    FundamentalGroupoid.mk (uRepresentative hCover a) ⟶
      FundamentalGroupoid.mk (uRepresentative hCover b) := by
  classical
  exact dite (Set.range p ⊆ U) (fun hpU =>
    let aU : U := ⟨a, hpU ⟨0, p.source⟩⟩
    let bU : U := ⟨b, hpU ⟨1, p.target⟩⟩
    (uPointIso hCover a aU.2).hom ≫
      Path.Homotopic.Quotient.mk (restrictPath U p hpU) ≫
      (uPointIso hCover b bU.2).inv)
    (fun hnU =>
    let hpV : Set.range p ⊆ V := hp.resolve_left hnU
    let aV : V := ⟨a, hpV ⟨0, p.source⟩⟩
    let bV : V := ⟨b, hpV ⟨1, p.target⟩⟩
    let oA : ↥(U ∩ V) := overlapRepresentative (U := U) a aV.2
    let oB : ↥(U ∩ V) := overlapRepresentative (U := U) b bV.2
    let eA : (interRightFunctor U V).obj (FundamentalGroupoid.mk oA) ≅
        FundamentalGroupoid.mk aV := overlapRepresentativeIso (U := U) a aV.2
    let eB : (interRightFunctor U V).obj (FundamentalGroupoid.mk oB) ≅
        FundamentalGroupoid.mk bV := overlapRepresentativeIso (U := U) b bV.2
    let qV : FundamentalGroupoid.mk aV ⟶ FundamentalGroupoid.mk bV :=
      Path.Homotopic.Quotient.mk (restrictPath V p hpV)
    let qO : FundamentalGroupoid.mk oA ⟶ FundamentalGroupoid.mk oB :=
      (interRightFunctor U V).preimage (eA.hom ≫ qV ≫ eB.inv)
    let K := FundamentalGroupoid.map (inclusionInterLeft U V)
    (uOverlapIso hCover a aV.2).hom ≫
      K.map qO ≫ (uOverlapIso hCover b bV.2).inv
    )

private theorem inclusionFunctor_map_liftSmallPath_of_left
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).Full] [(interRightFunctor U V).EssSurj]
    {a b : X} (p : Path a b)
    (hp : Set.range p ⊆ U ∨ Set.range p ⊆ V)
    (hpU : Set.range p ⊆ U) :
    (inclusionFunctor U).map (liftSmallPath hCover p hp) =
      (vertexIso hCover a).hom ≫ Path.Homotopic.Quotient.mk p ≫
        (vertexIso hCover b).inv := by
  simp only [liftSmallPath, hpU, ↓reduceDIte]
  have hMiddle :
      (inclusionFunctor U).map
          (Path.Homotopic.Quotient.mk (restrictPath U p hpU)) =
        Path.Homotopic.Quotient.mk p := by
    change (Path.Homotopic.Quotient.mk (restrictPath U p hpU)).map
      (inclusionSub U) = _
    exact restrictPath_map_inclusion U p hpU
  rw [Functor.map_comp, Functor.map_comp, hMiddle]
  simp only [vertexIso, hpU ⟨0, p.source⟩, hpU ⟨1, p.target⟩,
    ↓reduceDIte, Functor.mapIso_hom, Functor.mapIso_inv]
  rfl

private theorem inclusionFunctor_map_liftSmallPath_of_right
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).Full] [(interRightFunctor U V).EssSurj]
    {a b : X} (p : Path a b)
    (hp : Set.range p ⊆ U ∨ Set.range p ⊆ V)
    (hnU : ¬ Set.range p ⊆ U) :
    (inclusionFunctor U).map (liftSmallPath hCover p hp) =
      (vertexIso hCover a).hom ≫ Path.Homotopic.Quotient.mk p ≫
        (vertexIso hCover b).inv := by
  let hpV : Set.range p ⊆ V := hp.resolve_left hnU
  let aV : V := ⟨a, hpV ⟨0, p.source⟩⟩
  let bV : V := ⟨b, hpV ⟨1, p.target⟩⟩
  let oA : ↥(U ∩ V) := overlapRepresentative (U := U) a aV.2
  let oB : ↥(U ∩ V) := overlapRepresentative (U := U) b bV.2
  let eA : (interRightFunctor U V).obj (FundamentalGroupoid.mk oA) ≅
      FundamentalGroupoid.mk aV := overlapRepresentativeIso (U := U) a aV.2
  let eB : (interRightFunctor U V).obj (FundamentalGroupoid.mk oB) ≅
      FundamentalGroupoid.mk bV := overlapRepresentativeIso (U := U) b bV.2
  let qV : FundamentalGroupoid.mk aV ⟶ FundamentalGroupoid.mk bV :=
    Path.Homotopic.Quotient.mk (restrictPath V p hpV)
  let qO : FundamentalGroupoid.mk oA ⟶ FundamentalGroupoid.mk oB :=
    (interRightFunctor U V).preimage (eA.hom ≫ qV ≫ eB.inv)
  let K := FundamentalGroupoid.map (inclusionInterLeft U V)
  let IU := inclusionFunctor U
  let IV := inclusionFunctor V
  have hMiddle : IV.map qV = Path.Homotopic.Quotient.mk p := by
    change (Path.Homotopic.Quotient.mk (restrictPath V p hpV)).map
      (inclusionSub V) = _
    exact restrictPath_map_inclusion V p hpV
  have hPreimage : (interRightFunctor U V).map qO = eA.hom ≫ qV ≫ eB.inv :=
    (interRightFunctor U V).map_preimage _
  have hSquare := Functor.congr_hom (overlap_square U V) qO
  change IU.map (K.map qO) =
    eqToHom _ ≫ IV.map ((interRightFunctor U V).map qO) ≫ eqToHom _ at hSquare
  simp only [liftSmallPath, hnU, ↓reduceDIte]
  rw [Functor.map_comp, Functor.map_comp]
  change IU.map (uOverlapIso hCover a aV.2).hom ≫
      IU.map (K.map qO) ≫ IU.map (uOverlapIso hCover b bV.2).inv = _
  rw [hSquare, hPreimage]
  simp only [Functor.map_comp, Category.assoc]
  rw [hMiddle]
  let cA := IU.map (uOverlapIso hCover a aV.2).hom ≫
    eqToHom (Functor.congr_obj (overlap_square U V)
      (FundamentalGroupoid.mk oA)) ≫ IV.map eA.hom
  let cB := IV.map eB.inv ≫
    eqToHom (Functor.congr_obj (overlap_square U V)
      (FundamentalGroupoid.mk oB)).symm ≫
      IU.map (uOverlapIso hCover b bV.2).inv
  have hcA : cA = (vertexIso hCover a).hom := by
    change (inclusionFunctor U).map (uOverlapIso hCover a aV.2).hom ≫
        eqToHom (Functor.congr_obj (overlap_square U V)
          (FundamentalGroupoid.mk
            (overlapRepresentative (U := U) a aV.2))) ≫
        (inclusionFunctor V).map
          (overlapRepresentativeIso (U := U) a aV.2).hom = _
    exact vertexIso_hom_of_mem_right hCover a aV.2
  have hcB : cB = (vertexIso hCover b).inv := by
    change (inclusionFunctor V).map
          (overlapRepresentativeIso (U := U) b bV.2).inv ≫
        eqToHom (Functor.congr_obj (overlap_square U V)
          (FundamentalGroupoid.mk
            (overlapRepresentative (U := U) b bV.2))).symm ≫
        (inclusionFunctor U).map (uOverlapIso hCover b bV.2).inv = _
    exact vertexIso_inv_of_mem_right hCover b bV.2
  calc
    _ = cA ≫ Path.Homotopic.Quotient.mk p ≫ cB := by
      simp only [cA, cB, Category.assoc]
      rfl
    _ = _ := by
      rw [hcA, hcB]
      rfl

private theorem inclusionFunctor_map_liftSmallPath
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).Full] [(interRightFunctor U V).EssSurj]
    {a b : X} (p : Path a b)
    (hp : Set.range p ⊆ U ∨ Set.range p ⊆ V) :
    (inclusionFunctor U).map (liftSmallPath hCover p hp) =
      (vertexIso hCover a).hom ≫ Path.Homotopic.Quotient.mk p ≫
        (vertexIso hCover b).inv := by
  by_cases hpU : Set.range p ⊆ U
  · exact inclusionFunctor_map_liftSmallPath_of_left hCover p hp hpU
  · exact inclusionFunctor_map_liftSmallPath_of_right hCover p hp hpU

private theorem gridCell_small
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) {a b : X} (p : Path a b)
    (G : SubordinatePathGrid (twoSetOpenCover U V hU hV) p)
    (k : Fin (G.extraCells + 1)) :
    Set.range (G.cell k) ⊆ U ∨ Set.range (G.cell k) ⊆ V := by
  have hk := G.cell_range_subset k
  cases hLabel : G.label k with
  | false =>
      left
      simpa [twoSetOpenCover, hLabel] using hk
  | true =>
      right
      simpa [twoSetOpenCover, hLabel] using hk

private def gridCellIndex
    {X : Type u} [TopologicalSpace X] {ι : Type*}
    {W : ι → TopologicalSpace.Opens X} {a b : X} {p : Path a b}
    (G : SubordinatePathGrid W p) (k : ℕ) (hk : k ≤ G.extraCells) :
    Fin (G.extraCells + 1) :=
  ⟨k, by omega⟩

private def gridVertexIndex
    {X : Type u} [TopologicalSpace X] {ι : Type*}
    {W : ι → TopologicalSpace.Opens X} {a b : X} {p : Path a b}
    (G : SubordinatePathGrid W p) (k : ℕ) (hk : k ≤ G.extraCells + 1) :
    Fin (G.extraCells + 2) :=
  ⟨k, by omega⟩

private noncomputable def gridPrefixLift
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).Full] [(interRightFunctor U V).EssSurj]
    {a b : X} (p : Path a b)
    (G : SubordinatePathGrid (twoSetOpenCover U V hU hV) p) :
    (k : ℕ) → (hk : k ≤ G.extraCells) →
      FundamentalGroupoid.mk
          (uRepresentative hCover (p (G.time (gridVertexIndex G 0 (Nat.zero_le _))))) ⟶
        FundamentalGroupoid.mk
          (uRepresentative hCover
            (p (G.time (gridVertexIndex G (k + 1) (by omega)))))
  | 0, hk =>
      liftSmallPath hCover (G.cell (gridCellIndex G 0 hk))
        (gridCell_small hU hV p G (gridCellIndex G 0 hk))
  | k + 1, hk =>
      gridPrefixLift hU hV hCover p G k (by omega) ≫
        liftSmallPath hCover (G.cell (gridCellIndex G (k + 1) hk))
          (gridCell_small hU hV p G (gridCellIndex G (k + 1) hk))

private theorem inclusionFunctor_map_gridPrefixLift
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    [(interRightFunctor U V).Full] [(interRightFunctor U V).EssSurj]
    {a b : X} (p : Path a b)
    (G : SubordinatePathGrid (twoSetOpenCover U V hU hV) p)
    (k : ℕ) (hk : k ≤ G.extraCells) :
    (inclusionFunctor U).map (gridPrefixLift hU hV hCover p G k hk) =
      (vertexIso hCover
          (p (G.time (gridVertexIndex G 0 (Nat.zero_le _))))).hom ≫
        Path.Homotopic.Quotient.mk
          (p.subpath (G.time (gridVertexIndex G 0 (Nat.zero_le _)))
            (G.time (gridVertexIndex G (k + 1) (by omega)))) ≫
        (vertexIso hCover
          (p (G.time (gridVertexIndex G (k + 1) (by omega))))).inv := by
  induction k with
  | zero =>
      simpa [gridPrefixLift, SubordinatePathGrid.cell, gridCellIndex,
        gridVertexIndex] using
        inclusionFunctor_map_liftSmallPath hCover
          (G.cell (gridCellIndex G 0 hk))
          (gridCell_small hU hV p G (gridCellIndex G 0 hk))
  | succ k ih =>
      have hk' : k ≤ G.extraCells := by omega
      have hCell :
          (inclusionFunctor U).map
              (liftSmallPath hCover
                (G.cell (gridCellIndex G (k + 1) hk))
                (gridCell_small hU hV p G (gridCellIndex G (k + 1) hk))) =
            (vertexIso hCover
              (p (G.time (gridVertexIndex G (k + 1) (by omega))))).hom ≫
              Path.Homotopic.Quotient.mk
                (p.subpath (G.time (gridVertexIndex G (k + 1) (by omega)))
                  (G.time (gridVertexIndex G (k + 2) (by omega)))) ≫
              (vertexIso hCover
                (p (G.time (gridVertexIndex G (k + 2) (by omega))))).inv := by
        simpa [SubordinatePathGrid.cell, gridCellIndex, gridVertexIndex] using
          inclusionFunctor_map_liftSmallPath hCover
            (G.cell (gridCellIndex G (k + 1) hk))
            (gridCell_small hU hV p G (gridCellIndex G (k + 1) hk))
      let stepImage :=
        (vertexIso hCover
            (p (G.time (gridVertexIndex G (k + 1) (by omega))))).hom ≫
          Path.Homotopic.Quotient.mk
            (p.subpath (G.time (gridVertexIndex G (k + 1) (by omega)))
              (G.time (gridVertexIndex G (k + 2) (by omega)))) ≫
          (vertexIso hCover
            (p (G.time (gridVertexIndex G (k + 2) (by omega))))).inv
      let q₁ : FundamentalGroupoid.mk
            (p (G.time (gridVertexIndex G 0 (Nat.zero_le _)))) ⟶
          FundamentalGroupoid.mk
            (p (G.time (gridVertexIndex G (k + 1) (by omega)))) :=
        Path.Homotopic.Quotient.mk
          (p.subpath (G.time (gridVertexIndex G 0 (Nat.zero_le _)))
            (G.time (gridVertexIndex G (k + 1) (by omega))))
      let q₂ : FundamentalGroupoid.mk
            (p (G.time (gridVertexIndex G (k + 1) (by omega)))) ⟶
          FundamentalGroupoid.mk
            (p (G.time (gridVertexIndex G (k + 2) (by omega)))) :=
        Path.Homotopic.Quotient.mk
          (p.subpath (G.time (gridVertexIndex G (k + 1) (by omega)))
            (G.time (gridVertexIndex G (k + 2) (by omega))))
      let qLong : FundamentalGroupoid.mk
            (p (G.time (gridVertexIndex G 0 (Nat.zero_le _)))) ⟶
          FundamentalGroupoid.mk
            (p (G.time (gridVertexIndex G (k + 2) (by omega)))) :=
        Path.Homotopic.Quotient.mk
          (p.subpath (G.time (gridVertexIndex G 0 (Nat.zero_le _)))
            (G.time (gridVertexIndex G (k + 2) (by omega))))
      have hSubpath : q₁ ≫ q₂ = qLong := by
        change (Path.Homotopic.Quotient.mk
            (p.subpath (G.time (gridVertexIndex G 0 (Nat.zero_le _)))
              (G.time (gridVertexIndex G (k + 1) (by omega))))).trans
            (Path.Homotopic.Quotient.mk
              (p.subpath (G.time (gridVertexIndex G (k + 1) (by omega)))
                (G.time (gridVertexIndex G (k + 2) (by omega))))) = _
        exact Path.Homotopic.mk_subpath_trans_mk_subpath _ _ _ _
      rw [gridPrefixLift, Functor.map_comp]
      calc
        _ = (inclusionFunctor U).map
              (gridPrefixLift hU hV hCover p G k hk') ≫ stepImage :=
          congrArg
            (fun q => (inclusionFunctor U).map
              (gridPrefixLift hU hV hCover p G k hk') ≫ q) hCell
        _ = ((vertexIso hCover
                (p (G.time (gridVertexIndex G 0 (Nat.zero_le _))))).hom ≫
              Path.Homotopic.Quotient.mk
                (p.subpath (G.time (gridVertexIndex G 0 (Nat.zero_le _)))
                  (G.time (gridVertexIndex G (k + 1) (by omega)))) ≫
              (vertexIso hCover
                (p (G.time (gridVertexIndex G (k + 1) (by omega))))).inv) ≫
            stepImage :=
          congrArg (fun q => q ≫ stepImage)
            (ih hk')
        _ = _ := by
          simp only [stepImage, Category.assoc, Iso.inv_hom_id_assoc]
          change (vertexIso hCover
                (p (G.time (gridVertexIndex G 0 (Nat.zero_le _))))).hom ≫
              q₁ ≫ q₂ ≫
              (vertexIso hCover
                (p (G.time (gridVertexIndex G (k + 2) (by omega))))).inv =
            (vertexIso hCover
                (p (G.time (gridVertexIndex G 0 (Nat.zero_le _))))).hom ≫
              qLong ≫
              (vertexIso hCover
                (p (G.time (gridVertexIndex G (k + 2) (by omega))))).inv
          have h := congrArg
            (fun q => (vertexIso hCover
                (p (G.time (gridVertexIndex G 0 (Nat.zero_le _))))).hom ≫
              q ≫ (vertexIso hCover
                (p (G.time (gridVertexIndex G (k + 2) (by omega))))).inv)
            hSubpath
          simpa only [Category.assoc] using h

/-- A subordinate grid supplies an arrow in the first open set whose image
is the original ambient path class. -/
public theorem openCoverGridLift_exists
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    [(FundamentalGroupoid.map (inclusionInterRight U V)).Full]
    [(FundamentalGroupoid.map (inclusionInterRight U V)).EssSurj]
    {a b : U} (p : Path a.1 b.1)
    (G : SubordinatePathGrid (twoSetOpenCover U V hU hV) p) :
    ∃ q : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b,
      (FundamentalGroupoid.map (inclusionSub U)).map q =
        Path.Homotopic.Quotient.mk p := by
  let t₀ := G.time (gridVertexIndex G 0 (Nat.zero_le _))
  let t₁ := G.time (gridVertexIndex G (G.extraCells + 1) le_rfl)
  let y₀ := p t₀
  let y₁ := p t₁
  have ht₀ : t₀ = 0 := by
    exact (congrArg G.time (Fin.ext rfl)).trans G.time_zero
  have ht₁ : t₁ = 1 := by
    exact (congrArg G.time (Fin.ext rfl)).trans G.time_last
  have hy₀ : y₀ = a.1 := (congrArg p ht₀).trans p.source
  have hy₁ : y₁ = b.1 := (congrArg p ht₁).trans p.target
  have hy₀U : y₀ ∈ U := hy₀.symm ▸ a.2
  have hy₁U : y₁ ∈ U := hy₁.symm ▸ b.2
  let eStart : FundamentalGroupoid.mk a ≅
      FundamentalGroupoid.mk (uRepresentative hCover y₀) :=
    eqToIso (congrArg FundamentalGroupoid.mk (Subtype.ext hy₀.symm)) ≪≫
      (uPointIso hCover y₀ hy₀U).symm
  let eFinish : FundamentalGroupoid.mk (uRepresentative hCover y₁) ≅
      FundamentalGroupoid.mk b :=
    uPointIso hCover y₁ hy₁U ≪≫
      eqToIso (congrArg FundamentalGroupoid.mk (Subtype.ext hy₁))
  let q : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b :=
    eStart.hom ≫ gridPrefixLift hU hV hCover p G G.extraCells le_rfl ≫ eFinish.hom
  refine ⟨q, ?_⟩
  dsimp only [q]
  rw [Functor.map_comp, Functor.map_comp,
    inclusionFunctor_map_gridPrefixLift hU hV hCover p G G.extraCells le_rfl]
  simp only [Category.assoc]
  change (FundamentalGroupoid.map (inclusionSub U)).map eStart.hom ≫
      (vertexIso hCover y₀).hom ≫
        Path.Homotopic.Quotient.mk (p.subpath t₀ t₁) ≫
          (vertexIso hCover y₁).inv ≫
            (FundamentalGroupoid.map (inclusionSub U)).map eFinish.hom =
    Path.Homotopic.Quotient.mk p
  simp only [eStart, eFinish, Iso.trans_hom, Functor.map_comp,
    vertexIso, hy₀U, hy₁U, ↓reduceDIte]
  let E₀ := (inclusionFunctor U).mapIso (uPointIso hCover y₀ hy₀U)
  let E₁ := (inclusionFunctor U).mapIso (uPointIso hCover y₁ hy₁U)
  let hStart : FundamentalGroupoid.mk a =
      FundamentalGroupoid.mk (⟨y₀, hy₀U⟩ : U) :=
    congrArg FundamentalGroupoid.mk (Subtype.ext hy₀.symm)
  let hFinish : FundamentalGroupoid.mk (⟨y₁, hy₁U⟩ : U) =
      FundamentalGroupoid.mk b :=
    congrArg FundamentalGroupoid.mk (Subtype.ext hy₁)
  simp only [Category.assoc]
  change (inclusionFunctor U).map (eqToIso hStart).hom ≫
      E₀.inv ≫ E₀.hom ≫
        Path.Homotopic.Quotient.mk (p.subpath t₀ t₁) ≫
          E₁.inv ≫ E₁.hom ≫
            (inclusionFunctor U).map (eqToIso hFinish).hom =
    Path.Homotopic.Quotient.mk p
  simp only [Iso.inv_hom_id_assoc]
  let rEnd := (inclusionFunctor U).map (eqToIso hFinish).hom
  have hCancel₁ : E₁.inv ≫ E₁.hom ≫ rEnd = rEnd := E₁.inv_hom_id_assoc rEnd
  have hStartMap : (inclusionFunctor U).map (eqToIso hStart).hom =
      eqToHom (congrArg FundamentalGroupoid.mk hy₀.symm) := by
    dsimp only [eqToIso]
    rw [eqToHom_map]
    apply eqToHom_eq
  have hFinishMap : rEnd = eqToHom (congrArg FundamentalGroupoid.mk hy₁) := by
    dsimp only [rEnd, eqToIso]
    rw [eqToHom_map]
    apply eqToHom_eq
  have hPath : (p.subpath t₀ t₁).cast hy₀.symm hy₁.symm = p := by
    apply Path.ext
    funext s
    rw [Path.cast_coe]
    rw [ht₀, ht₁, Path.subpath_zero_one, Path.cast_coe]
  have hClass :
      (Path.Homotopic.Quotient.mk (p.subpath t₀ t₁)).cast
          hy₀.symm hy₁.symm = Path.Homotopic.Quotient.mk p :=
    (Path.Homotopic.Quotient.mk_cast (p.subpath t₀ t₁)
      hy₀.symm hy₁.symm).symm.trans
        (congrArg Path.Homotopic.Quotient.mk hPath)
  have hCancelWhole :
      (inclusionFunctor U).map (eqToIso hStart).hom ≫
          Path.Homotopic.Quotient.mk (p.subpath t₀ t₁) ≫
            E₁.inv ≫ E₁.hom ≫ rEnd =
        (inclusionFunctor U).map (eqToIso hStart).hom ≫
          Path.Homotopic.Quotient.mk (p.subpath t₀ t₁) ≫ rEnd := by
    have h := congrArg
      (fun z => (inclusionFunctor U).map (eqToIso hStart).hom ≫
        Path.Homotopic.Quotient.mk (p.subpath t₀ t₁) ≫ z) hCancel₁
    convert h using 1
    rfl
  have hEndpoint :
      (inclusionFunctor U).map (eqToIso hStart).hom ≫
          Path.Homotopic.Quotient.mk (p.subpath t₀ t₁) ≫ rEnd =
        (Path.Homotopic.Quotient.mk p :
          FundamentalGroupoid.mk a.1 ⟶ FundamentalGroupoid.mk b.1) := by
    rw [hStartMap, hFinishMap]
    exact (FundamentalGroupoid.conj_eqToHom hy₀.symm hy₁.symm).trans hClass
  exact hCancelWhole.trans hEndpoint

/-- The complete lifted arrow in the first open set associated to one
subordinate path grid. -/
public noncomputable def openCoverGridLift
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    [(FundamentalGroupoid.map (inclusionInterRight U V)).Full]
    [(FundamentalGroupoid.map (inclusionInterRight U V)).EssSurj]
    {a b : U} (p : Path a.1 b.1)
    (G : SubordinatePathGrid (twoSetOpenCover U V hU hV) p) :
    FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b :=
  (openCoverGridLift_exists hU hV hCover p G).choose

/-- Mapping the complete lifted grid arrow recovers the original path class. -/
public theorem openCoverGridLift_map
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    [(FundamentalGroupoid.map (inclusionInterRight U V)).Full]
    [(FundamentalGroupoid.map (inclusionInterRight U V)).EssSurj]
    {a b : U} (p : Path a.1 b.1)
    (G : SubordinatePathGrid (twoSetOpenCover U V hU hV) p) :
    (FundamentalGroupoid.map (inclusionSub U)).map
        (openCoverGridLift hU hV hCover p G) =
      Path.Homotopic.Quotient.mk p :=
  (openCoverGridLift_exists hU hV hCover p G).choose_spec

/-- In a two-set fundamental-groupoid van Kampen square, fullness and
essential surjectivity of the overlap inclusion into the second open set
make the inclusion of the first open set full. -/
public theorem inclusionSub_full_of_interRight_full_essSurj
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hCover : U ∪ V = Set.univ)
    (hFull : (FundamentalGroupoid.map (inclusionInterRight U V)).Full)
    (hEssSurj : (FundamentalGroupoid.map (inclusionInterRight U V)).EssSurj) :
    (FundamentalGroupoid.map (inclusionSub (X := X) U)).Full := by
  let _ : (FundamentalGroupoid.map (inclusionInterRight U V)).Full := hFull
  let _ : (FundamentalGroupoid.map (inclusionInterRight U V)).EssSurj := hEssSurj
  refine
    { map_surjective := fun {a b : FundamentalGroupoid U} q => ?_ }
  change Path.Homotopic.Quotient a.as.1 b.as.1 at q
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
      let G : SubordinatePathGrid (twoSetOpenCover U V hU hV) p :=
        Classical.choice (exists_subordinatePathGrid
          (twoSetOpenCover U V hU hV)
          (twoSetOpenCover_isOpenCover hU hV hCover) p)
      exact ⟨openCoverGridLift hU hV hCover p G,
        openCoverGridLift_map hU hV hCover p G⟩

end MathlibExt.Topology.Homotopy.VanKampenWanted

end

end
