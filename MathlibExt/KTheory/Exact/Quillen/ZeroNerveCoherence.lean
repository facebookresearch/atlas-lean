/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.ZeroCoherence

/-!
# Zero nerve coherence triangle

For additive exact functors `F G : C ⥤ D` with `e : F ≅ G`, the categorical
naturality `QuillenQ.zeroComparisonIso_naturality` lifts to a simplicial
2-simplex in `NQ D`.

Orientation: `F`-mapped zero → `G`-mapped zero → target zero.
First edge is the nerve edge of `(QuillenQ.mapNatIso F G e).hom.app ⟨0⟩`,
second edge is `NQ.zeroComparisonEdge G`, composite edge is
`NQ.zeroComparisonEdge F`.

For additive exact `F : C ⥤ D` and `G : D ⥤ E`, the `G`-mapped `F`
zero-comparison edge `NQ.mapZeroComparisonEdge F G` followed by
`NQ.zeroComparisonEdge G` composes to `NQ.zeroComparisonEdge (F ⋙ G)`,
represented by `NQ.zeroCompTriangle`.

For additive exact `F : C ⥤ D` and `X : C`, the hom-level
`QuillenQ.zeroToVertex_naturality_hom` lifts to a simplicial 2-simplex in
`NQ D`, represented by `NQ.zeroVertexTriangle`.

Orientation: mapped zero → target zero → mapped `X` vertex. No strict pointed
functoriality; no realized homotopy or path coherence here.

Nonclaims: no strict pointed functoriality (mapped and selected basepoints are
only compared, never identified); no realized homotopy or path coherence here;
no second nerve representation or new homotopy foundation.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial ZeroObject
open CategoryTheory.ExactCategory

universe v u v₁ u₁ v₂ u₂ v₃ u₃

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type u} [Category.{v} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- Hom-level naturality for the zero comparison iso. -/
theorem QuillenQ.zeroComparisonIso_naturality_hom (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    ((QuillenQ.mapNatIso F G e).hom.app ⟨0⟩) ≫
      (QuillenQ.zeroComparisonIso G).hom =
      (QuillenQ.zeroComparisonIso F).hom := by
  have h := QuillenQ.zeroComparisonIso_naturality F G e
  have hhom := congrArg Iso.hom h
  simpa using hhom

/-- Nerve edge in `NQ D` induced by the natural-isomorphism transport at `⟨0⟩`. -/
noncomputable def NQ.mapNatIsoEdge (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQ D).Edge ((NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C))
      ((NQ.map G).app (op ⦋0⦌) (NQ.zeroVertex C)) :=
  SSet.Edge.ofEq
    (CategoryTheory.nerve.edgeMk ((QuillenQ.mapNatIso F G e).hom.app ⟨0⟩))
    (by simp [NQ.zeroVertex, NQ.map_app_mk₀]; rfl)
    (by simp [NQ.zeroVertex, NQ.map_app_mk₀]; rfl)

/-- Edge formula for the `⟨0⟩` natural-isomorphism transport edge. -/
@[simp]
theorem NQ.mapNatIsoEdge_edge (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQ.mapNatIsoEdge F G e).edge =
      ComposableArrows.mk₁ ((QuillenQ.mapNatIso F G e).hom.app ⟨0⟩) :=
  rfl

/-- Source face of the transport edge is the `F`-mapped zero vertex. -/
@[simp]
theorem NQ.mapNatIsoEdge_src (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQ D).δ 1 (NQ.mapNatIsoEdge F G e).edge =
      (NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C) :=
  SSet.Edge.src_eq _

/-- Target face of the transport edge is the `G`-mapped zero vertex. -/
@[simp]
theorem NQ.mapNatIsoEdge_tgt (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQ D).δ 0 (NQ.mapNatIsoEdge F G e).edge =
      (NQ.map G).app (op ⦋0⦌) (NQ.zeroVertex C) :=
  SSet.Edge.tgt_eq _

/-- Underlying 2-simplex witnessing the zero nerve triangle. -/
noncomputable def NQ.zeroNerveTriangleSimplex (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQ D).obj (op ⦋2⦌) :=
  ComposableArrows.mk₂ ((QuillenQ.mapNatIso F G e).hom.app ⟨0⟩)
    (QuillenQ.zeroComparisonIso G).hom

/-- Second face of the triangle is the natural-isomorphism transport edge. -/
theorem NQ.zeroNerveTriangle_d₂ (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQ D).δ 2 (NQ.zeroNerveTriangleSimplex F G e) =
      (NQ.mapNatIsoEdge F G e).edge := by
  unfold NQ.zeroNerveTriangleSimplex
  rw [CategoryTheory.nerve.δ₂_mk₂_eq, NQ.mapNatIsoEdge_edge]

/-- Zeroth face of the triangle is the `G` comparison edge. -/
theorem NQ.zeroNerveTriangle_d₀ (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQ D).δ 0 (NQ.zeroNerveTriangleSimplex F G e) =
      (NQ.zeroComparisonEdge G).edge := by
  unfold NQ.zeroNerveTriangleSimplex
  rw [CategoryTheory.nerve.δ₀_mk₂_eq, NQ.zeroComparisonEdge_edge]

/-- First face of the triangle is the `F` comparison edge. -/
theorem NQ.zeroNerveTriangle_d₁ (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQ D).δ 1 (NQ.zeroNerveTriangleSimplex F G e) =
      (NQ.zeroComparisonEdge F).edge := by
  have hcomp := QuillenQ.zeroComparisonIso_naturality_hom F G e
  simp only [NQ.zeroNerveTriangleSimplex,
    CategoryTheory.nerve.δ₁_mk₂_eq, NQ.zeroComparisonEdge_edge]
  rw [hcomp]

/-- Simplicial coherence triangle: natural-isomorphism edge followed by the
`G` comparison edge composes to the `F` comparison edge. -/
noncomputable def NQ.zeroNerveTriangle (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    SSet.Edge.CompStruct (NQ.mapNatIsoEdge F G e)
      (NQ.zeroComparisonEdge G) (NQ.zeroComparisonEdge F) :=
  SSet.Edge.CompStruct.mk (NQ.zeroNerveTriangleSimplex F G e)
    (NQ.zeroNerveTriangle_d₂ F G e)
    (NQ.zeroNerveTriangle_d₀ F G e)
    (NQ.zeroNerveTriangle_d₁ F G e)

/-- Underlying 2-simplex of the zero nerve coherence triangle. -/
@[simp]
theorem NQ.zeroNerveTriangle_simplex (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQ.zeroNerveTriangle F G e).simplex =
      NQ.zeroNerveTriangleSimplex F G e :=
  rfl

/-- Morphism-level composition law for the triangle. -/
theorem NQ.zeroNerveTriangle_homEquiv (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    CategoryTheory.nerve.homEquiv (NQ.mapNatIsoEdge F G e) ≫
      CategoryTheory.nerve.homEquiv (NQ.zeroComparisonEdge G) =
      CategoryTheory.nerve.homEquiv (NQ.zeroComparisonEdge F) :=
  CategoryTheory.nerve.homEquiv_comp (NQ.zeroNerveTriangle F G e)

/-- Hom-level composition law for the zero comparison iso. -/
theorem QuillenQ.zeroComparisonIso_comp_hom {C : Type u₁} [Category.{v₁} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type u₂} [Category.{v₂} D]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    {E : Type u₃} [Category.{v₃} E]
    [Preadditive E] [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    ((QuillenQ.map G).map (QuillenQ.zeroComparisonIso F).hom) ≫
      (QuillenQ.zeroComparisonIso G).hom =
      (QuillenQ.zeroComparisonIso (F ⋙ G)).hom := by
  have h := QuillenQ.zeroComparisonIso_comp F G
  have hhom := congrArg Iso.hom h
  have h_obj : (QuillenQ.map (F ⋙ G)).obj (⟨0⟩ : QuillenQ C) =
      (QuillenQ.map G).obj ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C)) := by
    rw [QuillenQ.map_comp F G]
    rfl
  cases h_obj
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hhom
  exact hhom.symm

/-- Mapped zero-comparison edge: `NQ.zeroComparisonEdge F` transported through
`NQ.map G`, with source aligned to the `F ⋙ G` mapped zero vertex. -/
noncomputable def NQ.mapZeroComparisonEdge (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQ E).Edge ((NQ.map (F ⋙ G)).app (op ⦋0⦌) (NQ.zeroVertex C))
      ((NQ.map G).app (op ⦋0⦌) (NQ.zeroVertex D)) :=
  SSet.Edge.ofEq ((NQ.zeroComparisonEdge F).map (NQ.map G))
    (by simp [← NQ.map_comp]; rfl)
    rfl

/-- Edge formula for the mapped zero-comparison edge. -/
@[simp]
theorem NQ.mapZeroComparisonEdge_edge (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQ.mapZeroComparisonEdge F G).edge =
      ComposableArrows.mk₁ ((QuillenQ.map G).map (QuillenQ.zeroComparisonIso F).hom) := by
  unfold NQ.mapZeroComparisonEdge
  change (NQ.map G).app (op ⦋1⦌) (NQ.zeroComparisonEdge F).edge = _
  rw [NQ.zeroComparisonEdge_edge, NQ.map_app_mk₁]

/-- Source face of the mapped edge is the `F ⋙ G` mapped zero vertex. -/
@[simp]
theorem NQ.mapZeroComparisonEdge_src (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQ E).δ 1 (NQ.mapZeroComparisonEdge F G).edge =
      (NQ.map (F ⋙ G)).app (op ⦋0⦌) (NQ.zeroVertex C) :=
  SSet.Edge.src_eq _

/-- Target face of the mapped edge is the `G`-mapped zero vertex. -/
@[simp]
theorem NQ.mapZeroComparisonEdge_tgt (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQ E).δ 0 (NQ.mapZeroComparisonEdge F G).edge =
      (NQ.map G).app (op ⦋0⦌) (NQ.zeroVertex D) :=
  SSet.Edge.tgt_eq _

/-- Underlying 2-simplex witnessing the composition triangle. -/
noncomputable def NQ.zeroCompTriangleSimplex (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQ E).obj (op ⦋2⦌) :=
  ComposableArrows.mk₂ ((QuillenQ.map G).map (QuillenQ.zeroComparisonIso F).hom)
    (QuillenQ.zeroComparisonIso G).hom

/-- Second face of the composition triangle is the mapped comparison edge. -/
theorem NQ.zeroCompTriangle_d₂ (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQ E).δ 2 (NQ.zeroCompTriangleSimplex F G) =
      (NQ.mapZeroComparisonEdge F G).edge := by
  unfold NQ.zeroCompTriangleSimplex
  rw [CategoryTheory.nerve.δ₂_mk₂_eq, NQ.mapZeroComparisonEdge_edge]

/-- Zeroth face of the composition triangle is the `G` comparison edge. -/
theorem NQ.zeroCompTriangle_d₀ (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQ E).δ 0 (NQ.zeroCompTriangleSimplex F G) =
      (NQ.zeroComparisonEdge G).edge := by
  unfold NQ.zeroCompTriangleSimplex
  rw [CategoryTheory.nerve.δ₀_mk₂_eq, NQ.zeroComparisonEdge_edge]

/-- First face of the composition triangle is the `F ⋙ G` comparison edge. -/
theorem NQ.zeroCompTriangle_d₁ (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQ E).δ 1 (NQ.zeroCompTriangleSimplex F G) =
      (NQ.zeroComparisonEdge (F ⋙ G)).edge := by
  have hcomp := QuillenQ.zeroComparisonIso_comp_hom F G
  simp only [NQ.zeroCompTriangleSimplex,
    CategoryTheory.nerve.δ₁_mk₂_eq, NQ.zeroComparisonEdge_edge]
  rw [hcomp]; rfl

/-- Simplicial coherence triangle: mapped comparison followed by the `G`
comparison composes to the `F ⋙ G` comparison. -/
noncomputable def NQ.zeroCompTriangle (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    SSet.Edge.CompStruct (NQ.mapZeroComparisonEdge F G)
      (NQ.zeroComparisonEdge G) (NQ.zeroComparisonEdge (F ⋙ G)) :=
  SSet.Edge.CompStruct.mk (NQ.zeroCompTriangleSimplex F G)
    (NQ.zeroCompTriangle_d₂ F G)
    (NQ.zeroCompTriangle_d₀ F G)
    (NQ.zeroCompTriangle_d₁ F G)

/-- Underlying 2-simplex of the composition triangle. -/
@[simp]
theorem NQ.zeroCompTriangle_simplex (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQ.zeroCompTriangle F G).simplex =
      NQ.zeroCompTriangleSimplex F G :=
  rfl

/-- Morphism-level composition law for the composition triangle. -/
theorem NQ.zeroCompTriangle_homEquiv (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    CategoryTheory.nerve.homEquiv (NQ.mapZeroComparisonEdge F G) ≫
      CategoryTheory.nerve.homEquiv (NQ.zeroComparisonEdge G) =
      CategoryTheory.nerve.homEquiv (NQ.zeroComparisonEdge (F ⋙ G)) :=
  CategoryTheory.nerve.homEquiv_comp (NQ.zeroCompTriangle F G)

/-- Hom-level naturality for the zero-to-vertex edge: the mapped source equals
the comparison followed by the target zero-to-vertex edge.

Orientation: mapped zero `mk₀ ⟨F.obj 0⟩` → target zero `mk₀ ⟨0⟩` → mapped
`X` vertex `mk₀ ⟨F.obj X⟩`. No strict pointed functoriality; no realized
homotopy or path coherence here. -/
theorem QuillenQ.zeroToVertex_naturality_hom {C : Type u₁} [Category.{v₁} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    {D : Type u₂} [Category.{v₂} D]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] (X : C) :
    (QuillenQ.map F).map (QuillenQ.zeroToObjectHom X) =
      (QuillenQ.zeroComparisonIso F).hom ≫ QuillenQ.zeroToObjectHom (F.obj X) := by
  have hPB_fwd : HasPullback (QuillenQ.zeroToObjectSpan (F.obj X)).l
      (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject).r :=
    hasPullback_ofHasPullbacksAgainst
      (P := admissibleEpisOf D IsAdmissibleExact)
      (P' := admissibleMonosOf D IsAdmissibleExact)
      (QuillenQ.zeroToObjectSpan (F.obj X)).wl
      (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject).wr
  have hPB : HasPullback (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject).r
      (QuillenQ.zeroToObjectSpan (F.obj X)).l :=
    hasPullback_symmetry _ _
  unfold QuillenQ.zeroComparisonIso QuillenQ.zeroToObjectHom
  rw [QuillenQ.underlyingIso_hom, QuillenQ.map_mk]
  change QuillenQ.mkHom (QuillenSpan.map F (QuillenQ.zeroToObjectSpan X)) =
    quillenComp (QuillenQ.mkHom (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject))
      (QuillenQ.mkHom (QuillenQ.zeroToObjectSpan (F.obj X)))
  rw [mkHom_comp]
  apply Eq.symm
  apply QuillenQ.mkHom_sound
  have hR : IsIso (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject).r := by
    change IsIso (F.mapZeroObject).hom
    infer_instance
  have hL : IsIso (QuillenQ.zeroToObjectSpan (F.obj X)).l := by
    change IsIso (𝟙 (0 : D))
    infer_instance
  have hFst_iso : IsIso (pullback.fst
      (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject).r
      (QuillenQ.zeroToObjectSpan (F.obj X)).l) := by
    infer_instance
  refine Span.mkIso (@asIso _ _ _ _ _ hFst_iso) ?_ ?_
  · change pullback.fst
        (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject).r
        (QuillenQ.zeroToObjectSpan (F.obj X)).l ≫ F.map (𝟙 (0 : C)) =
      pullback.fst
        (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject).r
        (QuillenQ.zeroToObjectSpan (F.obj X)).l ≫ 𝟙 (F.obj 0)
    simp only [F.map_id]
  · change pullback.fst
        (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject).r
        (QuillenQ.zeroToObjectSpan (F.obj X)).l ≫ F.map (0 : (0 : C) ⟶ X) =
      pullback.snd
        (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject).r
        (QuillenQ.zeroToObjectSpan (F.obj X)).l ≫ (0 : (0 : D) ⟶ F.obj X)
    simp only [F.map_zero, comp_zero]
    change (0 : _ ⟶ F.obj X) =
      pullback.snd
          (QuillenQ.underlyingIsoFwdSpan F.mapZeroObject).r
          (QuillenQ.zeroToObjectSpan (F.obj X)).l ≫
        (0 : (QuillenQ.zeroToObjectSpan (F.obj X)).apex ⟶ F.obj X)
    simp only [comp_zero]

/-- Mapped zero-to-vertex edge: `NQ.zeroToVertexEdge X` transported through
`NQ.map F`, with target aligned to `mk₀ ⟨F.obj X⟩`.

Orientation: mapped zero → mapped `X`. No strict pointed functoriality; no
realized homotopy here. -/
noncomputable def NQ.mapZeroToVertexEdge (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    (NQ D).Edge ((NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C))
      (ComposableArrows.mk₀ (⟨F.obj X⟩ : QuillenQ D)) :=
  SSet.Edge.ofEq
    (CategoryTheory.nerve.edgeMk ((QuillenQ.map F).map (QuillenQ.zeroToObjectHom X)))
    (by simp [NQ.zeroVertex, NQ.map_app_mk₀]; rfl)
    (by rfl)

/-- Edge formula for the mapped zero-to-vertex edge. -/
@[simp]
theorem NQ.mapZeroToVertexEdge_edge (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    (NQ.mapZeroToVertexEdge F X).edge =
      ComposableArrows.mk₁ ((QuillenQ.map F).map (QuillenQ.zeroToObjectHom X)) :=
  rfl

/-- Source face of the mapped edge is the mapped zero vertex. -/
@[simp]
theorem NQ.mapZeroToVertexEdge_src (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    (NQ D).δ 1 (NQ.mapZeroToVertexEdge F X).edge =
      (NQ.map F).app (op ⦋0⦌) (NQ.zeroVertex C) :=
  SSet.Edge.src_eq _

/-- Target face of the mapped edge is `mk₀ ⟨F.obj X⟩`. -/
@[simp]
theorem NQ.mapZeroToVertexEdge_tgt (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    (NQ D).δ 0 (NQ.mapZeroToVertexEdge F X).edge =
      ComposableArrows.mk₀ (⟨F.obj X⟩ : QuillenQ D) :=
  SSet.Edge.tgt_eq _

/-- Underlying 2-simplex witnessing the zero-vertex naturality triangle. -/
noncomputable def NQ.zeroVertexTriangleSimplex (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    (NQ D).obj (op ⦋2⦌) :=
  ComposableArrows.mk₂ (QuillenQ.zeroComparisonIso F).hom
    (QuillenQ.zeroToObjectHom (F.obj X))

/-- Second face of the vertex triangle is the comparison edge. -/
theorem NQ.zeroVertexTriangle_d₂ (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    (NQ D).δ 2 (NQ.zeroVertexTriangleSimplex F X) =
      (NQ.zeroComparisonEdge F).edge := by
  unfold NQ.zeroVertexTriangleSimplex
  rw [CategoryTheory.nerve.δ₂_mk₂_eq, NQ.zeroComparisonEdge_edge]

/-- Zeroth face of the vertex triangle is the target zero-to-vertex edge. -/
theorem NQ.zeroVertexTriangle_d₀ (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    (NQ D).δ 0 (NQ.zeroVertexTriangleSimplex F X) =
      (NQ.zeroToVertexEdge (F.obj X)).edge := by
  unfold NQ.zeroVertexTriangleSimplex
  rw [CategoryTheory.nerve.δ₀_mk₂_eq, NQ.zeroToVertexEdge_edge]

/-- First face of the vertex triangle is the mapped source edge. -/
theorem NQ.zeroVertexTriangle_d₁ (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    (NQ D).δ 1 (NQ.zeroVertexTriangleSimplex F X) =
      (NQ.mapZeroToVertexEdge F X).edge := by
  have hcomp := QuillenQ.zeroToVertex_naturality_hom F X
  simp only [NQ.zeroVertexTriangleSimplex,
    CategoryTheory.nerve.δ₁_mk₂_eq, NQ.mapZeroToVertexEdge_edge]
  rw [hcomp]
  rfl

/-- Simplicial naturality triangle: the mapped source edge is the composite of
the comparison edge and the target zero-to-vertex edge. -/
noncomputable def NQ.zeroVertexTriangle (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    SSet.Edge.CompStruct (NQ.zeroComparisonEdge F)
      (NQ.zeroToVertexEdge (F.obj X)) (NQ.mapZeroToVertexEdge F X) :=
  SSet.Edge.CompStruct.mk (NQ.zeroVertexTriangleSimplex F X)
    (NQ.zeroVertexTriangle_d₂ F X)
    (NQ.zeroVertexTriangle_d₀ F X)
    (NQ.zeroVertexTriangle_d₁ F X)

/-- Underlying 2-simplex of the zero-vertex naturality triangle. -/
@[simp]
theorem NQ.zeroVertexTriangle_simplex (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    (NQ.zeroVertexTriangle F X).simplex =
      NQ.zeroVertexTriangleSimplex F X :=
  rfl

/-- Morphism-level composition law for the vertex triangle. -/
theorem NQ.zeroVertexTriangle_homEquiv (F : C ⥤ D)
    [F.Additive] [F.IsExact] (X : C) :
    CategoryTheory.nerve.homEquiv (NQ.zeroComparisonEdge F) ≫
      CategoryTheory.nerve.homEquiv (NQ.zeroToVertexEdge (F.obj X)) =
      CategoryTheory.nerve.homEquiv (NQ.mapZeroToVertexEdge F X) :=
  CategoryTheory.nerve.homEquiv_comp (NQ.zeroVertexTriangle F X)

end AlgebraicKTheory
