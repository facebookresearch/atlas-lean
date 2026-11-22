/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.PrismSkeletal
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace
public import MathlibExt.AlgebraicTopology.SimplicialSet.ProdStdSimplexOneCompat
public import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat

/-!
# Pointwise equivalences of functors

For an arbitrary simplicial set `A` and a quasicategory `C`, an edge of the
internal hom `C^A` is an equivalence if and only if its evaluations at all
vertices of `A` are equivalences in `C`.

The converse uses the pure source-prescribed prism extension along
`(boundary 1).ι ▷ A`. The extended square has the given edge on its left
side and identity edges on its bottom and right sides. Its two standard
triangles provide a right inverse in the ordinary homotopy category, whose
vertex evaluations are again equivalences. Applying the construction to this
right inverse and using ordinary category algebra proves invertibility.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace SSet

private def boundarySquareDatum {A C : SSet.{u}}
    (E I : A ⊗ Δ[1] ⟶ C) :
    ((∂Δ[1] : SSet.{u}) ⊗ A) ⊗ Δ[1] ⟶ C :=
  (α_ (∂Δ[1] : SSet.{u}) A Δ[1]).hom ≫
    BinaryCofan.IsColimit.desc (boundaryOneTensorCofanIsColimit (A ⊗ Δ[1]))
      ((stdSimplex.leftUnitor (A ⊗ Δ[1] : SSet.{u})).hom ≫ E)
      ((stdSimplex.leftUnitor (A ⊗ Δ[1] : SSet.{u})).hom ≫ I)

private lemma boundarySquareDatum_zero {A C : SSet.{u}}
    (E I : A ⊗ Δ[1] ⟶ C) :
    ((boundary.ι (1 : Fin 2) ▷ A) ▷ Δ[1]) ≫
        boundarySquareDatum E I =
      ((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ E := by
  rw [boundarySquareDatum, ← Category.assoc,
    MonoidalCategory.associator_naturality_left]
  have hdesc := BinaryCofan.IsColimit.inl_desc
    (boundaryOneTensorCofanIsColimit (A ⊗ Δ[1]))
    ((stdSimplex.leftUnitor (A ⊗ Δ[1] : SSet.{u})).hom ≫ E)
    ((stdSimplex.leftUnitor (A ⊗ Δ[1] : SSet.{u})).hom ≫ I)
  rw [BinaryCofan.mk_inl] at hdesc
  rw [Category.assoc, hdesc]
  rfl

private lemma boundarySquareDatum_one {A C : SSet.{u}}
    (E I : A ⊗ Δ[1] ⟶ C) :
    ((boundary.ι (0 : Fin 2) ▷ A) ▷ Δ[1]) ≫
        boundarySquareDatum E I =
      ((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ I := by
  rw [boundarySquareDatum, ← Category.assoc,
    MonoidalCategory.associator_naturality_left]
  have hdesc := BinaryCofan.IsColimit.inr_desc
    (boundaryOneTensorCofanIsColimit (A ⊗ Δ[1]))
    ((stdSimplex.leftUnitor (A ⊗ Δ[1] : SSet.{u})).hom ≫ E)
    ((stdSimplex.leftUnitor (A ⊗ Δ[1] : SSet.{u})).hom ≫ I)
  rw [BinaryCofan.mk_inr] at hdesc
  rw [Category.assoc, hdesc]
  rfl

private lemma exists_boundaryTensor_vertex {A : SSet.{u}}
    (x : ((∂Δ[1] : SSet.{u}) ⊗ A).obj (op (SimplexCategory.mk 0))) :
    (∃ y : (Δ[0] ⊗ A : SSet.{u}).obj (op (SimplexCategory.mk 0)),
      (boundary.ι (1 : Fin 2) ▷ A).app _ y = x) ∨
    (∃ y : (Δ[0] ⊗ A : SSet.{u}).obj (op (SimplexCategory.mk 0)),
      (boundary.ι (0 : Fin 2) ▷ A).app _ y = x) := by
  rcases x with ⟨b, a⟩
  generalize hk : stdSimplex.obj₀Equiv b.val = k
  fin_cases k
  · left
    refine ⟨⟨stdSimplex.obj₀Equiv.symm 0, a⟩, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      apply stdSimplex.obj₀Equiv.injective
      rw [hk]
      rfl
    · rfl
  · right
    refine ⟨⟨stdSimplex.obj₀Equiv.symm 0, a⟩, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      apply stdSimplex.obj₀Equiv.injective
      rw [hk]
      rfl
    · rfl

/-- The condition that every vertex evaluation of the edge is an equivalence. -/
private def Edge.PointwiseIsEquivalence {A C : SSet.{u}}
    {F G : ((ihom A).obj C).obj (Opposite.op (SimplexCategory.mk 0))}
    (E : SSet.Edge F G) : Prop :=
  ∀ a : A.obj (Opposite.op (SimplexCategory.mk 0)),
    ((E.map ((pre (yonedaEquiv.symm a)).app C)).map
      (evalDeltaZeroIso C).hom).IsEquivalence

private lemma prismOneVerticalsEquivalences_of_pointwise
    {A C : SSet.{u}}
    {F G : ((ihom A).obj C).obj (Opposite.op (SimplexCategory.mk 0))}
    (E : SSet.Edge F G) (hE : E.PointwiseIsEquivalence) :
    PrismOneVerticalsEquivalences (ihomPrismOfSimplex E.edge) := by
  intro a
  refine (Edge.isEquivalence_iff_of_edge_eq (e :=
      Edge.mk' ((ihomPrismOfSimplex E.edge).app _ (verticalOneSimplex a)))
      (e' := (E.map ((pre (yonedaEquiv.symm a)).app C)).map
        (evalDeltaZeroIso C).hom) ?_).2 (hE a)
  exact ihomPrismOfSimplex_app_verticalOneSimplex E a

private lemma boundarySquareDatum_verticals {A C : SSet.{u}}
    (E I : A ⊗ Δ[1] ⟶ C)
    (hE : PrismOneVerticalsEquivalences E)
    (hI : PrismOneVerticalsEquivalences I) :
    PrismOneVerticalsEquivalences (boundarySquareDatum E I) := by
  have hE₀ : PrismOneVerticalsEquivalences
      (((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ E) :=
    prismOneVerticalsEquivalences_whiskerRight_comp
      (stdSimplex.leftUnitor A).hom E hE
  have hI₀ : PrismOneVerticalsEquivalences
      (((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ I) :=
    prismOneVerticalsEquivalences_whiskerRight_comp
      (stdSimplex.leftUnitor A).hom I hI
  intro x
  rcases exists_boundaryTensor_vertex x with ⟨y, hy⟩ | ⟨y, hy⟩
  · refine (Edge.isEquivalence_iff_of_edge_eq (e :=
        Edge.mk' ((boundarySquareDatum E I).app _ (verticalOneSimplex x)))
        (e' := Edge.mk' ((((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ E).app _
          (verticalOneSimplex y))) ?_).2 (hE₀ y)
    change (boundarySquareDatum E I).app _ (verticalOneSimplex x) =
      (((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ E).app _
        (verticalOneSimplex y)
    calc (boundarySquareDatum E I).app _ (verticalOneSimplex x)
        = ((((boundary.ι (1 : Fin 2) ▷ A) ▷ Δ[1]) ≫
            boundarySquareDatum E I).app _ (verticalOneSimplex y)) := by
          change (boundarySquareDatum E I).app _ (verticalOneSimplex x) =
            (boundarySquareDatum E I).app _
              ((((boundary.ι (1 : Fin 2) ▷ A) ▷ Δ[1]).app _
                (verticalOneSimplex y)))
          rw [whiskerRight_app_verticalOneSimplex, hy]
      _ = _ := congr($(boundarySquareDatum_zero E I).app _ (verticalOneSimplex y))
  · refine (Edge.isEquivalence_iff_of_edge_eq (e :=
        Edge.mk' ((boundarySquareDatum E I).app _ (verticalOneSimplex x)))
        (e' := Edge.mk' ((((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ I).app _
          (verticalOneSimplex y))) ?_).2 (hI₀ y)
    change (boundarySquareDatum E I).app _ (verticalOneSimplex x) =
      (((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ I).app _
        (verticalOneSimplex y)
    calc (boundarySquareDatum E I).app _ (verticalOneSimplex x)
        = ((((boundary.ι (0 : Fin 2) ▷ A) ▷ Δ[1]) ≫
            boundarySquareDatum E I).app _ (verticalOneSimplex y)) := by
          change (boundarySquareDatum E I).app _ (verticalOneSimplex x) =
            (boundarySquareDatum E I).app _
              ((((boundary.ι (0 : Fin 2) ▷ A) ▷ Δ[1]).app _
                (verticalOneSimplex y)))
          rw [whiskerRight_app_verticalOneSimplex, hy]
      _ = _ := congr($(boundarySquareDatum_one E I).app _ (verticalOneSimplex y))

private lemma prismSectionAt_zero_ihomPrismOfSimplex
    {A C : SSet.{u}}
    {F G : ((ihom A).obj C).obj (Opposite.op (SimplexCategory.mk 0))}
    (E : SSet.Edge F G) :
    prismSectionAt A 0 ≫ ihomPrismOfSimplex E.edge =
      (ihomVertexEquiv A C).symm F := by
  apply (ihomVertexEquiv A C).injective
  rw [ihomVertexEquiv_prismSectionAt_zero_comp,
    ihomSimplexOfPrism_ihomPrismOfSimplex, E.src_eq,
    Equiv.apply_symm_apply]

private lemma boundarySquareDatum_source {A C : SSet.{u}}
    (E I : A ⊗ Δ[1] ⟶ C) (F : A ⟶ C)
    (hE : prismSectionAt A 0 ≫ E = F)
    (hI : prismSectionAt A 0 ≫ I = F) :
    prismSectionAt ((∂Δ[1] : SSet.{u}) ⊗ A) 0 ≫
        boundarySquareDatum E I =
      ((boundary 1).ι ▷ A) ≫
        (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) A ≫ F) := by
  apply (boundaryOneTensorCofanIsColimit A).hom_ext
  rintro ⟨j⟩
  cases j
  · calc
      (boundary.ι (1 : Fin 2) ▷ A) ≫
          (prismSectionAt ((∂Δ[1] : SSet.{u}) ⊗ A) 0 ≫
            boundarySquareDatum E I)
          = prismSectionAt ((Δ[0] : SSet.{u}) ⊗ A) 0 ≫
              ((((boundary.ι (1 : Fin 2) ▷ A) ▷ Δ[1]) ≫
                boundarySquareDatum E I)) := by
              rw [← Category.assoc]
              exact congrArg (fun q ↦ q ≫ boundarySquareDatum E I)
                (prismSectionAt_comp_whiskerRight
                  (boundary.ι (1 : Fin 2) ▷ A) 0).symm
      _ = prismSectionAt ((Δ[0] : SSet.{u}) ⊗ A) 0 ≫
            (((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ E) := by
              rw [boundarySquareDatum_zero]
      _ = (stdSimplex.leftUnitor A).hom ≫ (prismSectionAt A 0 ≫ E) := by
              rw [← Category.assoc, prismSectionAt_comp_whiskerRight,
                Category.assoc]
      _ = (stdSimplex.leftUnitor A).hom ≫ F := by rw [hE]
      _ = (boundary.ι (1 : Fin 2) ▷ A) ≫
          (((boundary 1).ι ▷ A) ≫
            (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) A ≫ F)) := by
              rw [← Category.assoc, ← Category.assoc,
                ← MonoidalCategory.comp_whiskerRight, boundary.ι_ι]
              rw [CartesianMonoidalCategory.whiskerRight_snd]
              rfl
  · calc
      (boundary.ι (0 : Fin 2) ▷ A) ≫
          (prismSectionAt ((∂Δ[1] : SSet.{u}) ⊗ A) 0 ≫
            boundarySquareDatum E I)
          = prismSectionAt ((Δ[0] : SSet.{u}) ⊗ A) 0 ≫
              ((((boundary.ι (0 : Fin 2) ▷ A) ▷ Δ[1]) ≫
                boundarySquareDatum E I)) := by
              rw [← Category.assoc]
              exact congrArg (fun q ↦ q ≫ boundarySquareDatum E I)
                (prismSectionAt_comp_whiskerRight
                  (boundary.ι (0 : Fin 2) ▷ A) 0).symm
      _ = prismSectionAt ((Δ[0] : SSet.{u}) ⊗ A) 0 ≫
            (((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ I) := by
              rw [boundarySquareDatum_one]
      _ = (stdSimplex.leftUnitor A).hom ≫ (prismSectionAt A 0 ≫ I) := by
              rw [← Category.assoc, prismSectionAt_comp_whiskerRight,
                Category.assoc]
      _ = (stdSimplex.leftUnitor A).hom ≫ F := by rw [hI]
      _ = (boundary.ι (0 : Fin 2) ▷ A) ≫
          (((boundary 1).ι ▷ A) ≫
            (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) A ≫ F)) := by
              rw [← Category.assoc, ← Category.assoc,
                ← MonoidalCategory.comp_whiskerRight, boundary.ι_ι]
              rw [CartesianMonoidalCategory.whiskerRight_snd]
              rfl

private theorem exists_pointwiseRightInverse_square
    {A C : SSet.{u}} [Quasicategory C]
    {F G : ((ihom A).obj C).obj (Opposite.op (SimplexCategory.mk 0))}
    (E : SSet.Edge F G) (hE : E.PointwiseIsEquivalence) :
    ∃ H : (((Δ[1] : SSet.{u}) ⊗ A) ⊗ Δ[1] : SSet.{u}) ⟶ C,
      ((((boundary 1).ι ▷ A) ▷ Δ[1]) ≫ H =
        boundarySquareDatum (ihomPrismOfSimplex E.edge)
          (ihomPrismOfSimplex (Edge.id F).edge)) ∧
      prismSectionAt ((Δ[1] : SSet.{u}) ⊗ A) 0 ≫ H =
        CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) A ≫
          (ihomVertexEquiv A C).symm F ∧
      PrismOneVerticalsEquivalences H := by
  let i : ((∂Δ[1] : SSet.{u}) ⊗ A) ⟶ ((Δ[1] : SSet.{u}) ⊗ A) :=
    (boundary 1).ι ▷ A
  have hi : Mono i := by
    dsimp only [i]
    exact (tensorRight A).map_mono (boundary 1).ι
  let Eprism : A ⊗ Δ[1] ⟶ C := ihomPrismOfSimplex E.edge
  let Fmap : A ⟶ C := (ihomVertexEquiv A C).symm F
  let Iprism : A ⊗ Δ[1] ⟶ C :=
    ihomPrismOfSimplex (Edge.id F).edge
  let HA : (((∂Δ[1] : SSet.{u}) ⊗ A) ⊗ Δ[1] : SSet.{u}) ⟶ C :=
    boundarySquareDatum Eprism Iprism
  let c : ((Δ[1] : SSet.{u}) ⊗ A) ⟶ C :=
    CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) A ≫ Fmap
  have hEsrc : prismSectionAt A 0 ≫ Eprism = Fmap := by
    exact prismSectionAt_zero_ihomPrismOfSimplex E
  have hIsrc : prismSectionAt A 0 ≫ Iprism = Fmap := by
    exact prismSectionAt_zero_ihomPrismOfSimplex (Edge.id F)
  have hHAsrc : prismSectionAt (((∂Δ[1] : SSet.{u}) ⊗ A)) 0 ≫ HA =
      i ≫ c := by
    exact boundarySquareDatum_source Eprism Iprism Fmap hEsrc hIsrc
  have hEvert : PrismOneVerticalsEquivalences Eprism :=
    prismOneVerticalsEquivalences_of_pointwise E hE
  have hIvert : PrismOneVerticalsEquivalences Iprism := by
    exact prismOneVerticalsEquivalences_ihomPrismOfSimplex_of_isEquivalence
      (Edge.id F) (Edge.isEquivalence_id F)
  have hHAvert : PrismOneVerticalsEquivalences HA :=
    boundarySquareDatum_verticals Eprism Iprism hEvert hIvert
  obtain ⟨H, hHr, hHs, hHv⟩ :=
    (@prismSrcExtension_of_mono _ _ C i hi inferInstance)
      HA c hHAsrc hHAvert
  exact ⟨H, hHr, hHs, hHv⟩

private lemma rightInverseEquation_of_compStructs
    {X : SSet.{u}} {x y : X.obj (Opposite.op (SimplexCategory.mk 0))}
    (E : SSet.Edge x y) (V : SSet.Edge y x) (D : SSet.Edge x x)
    (hEV : Edge.CompStruct E V D)
    (hId : Edge.CompStruct (Edge.id x) (Edge.id x) D) :
    E.toHoHom ≫ V.toHoHom = 𝟙 (HomotopyCategory.mk x) := by
  rw [Edge.toHoHom_comp hEV]
  calc D.toHoHom
      = (Edge.id x).toHoHom ≫ (Edge.id x).toHoHom :=
        (Edge.toHoHom_comp hId).symm
    _ = 𝟙 (HomotopyCategory.mk x) := by rw [Edge.toHoHom_id, Category.id_comp]

private lemma isEquivalence_of_two_successive_rightInverses
    {X : SSet.{u}} {x y : X.obj (Opposite.op (SimplexCategory.mk 0))}
    (E : SSet.Edge x y) (V : SSet.Edge y x) (W : SSet.Edge x y)
    (hEV : E.toHoHom ≫ V.toHoHom = 𝟙 (HomotopyCategory.mk x))
    (hVW : V.toHoHom ≫ W.toHoHom = 𝟙 (HomotopyCategory.mk y)) :
    E.IsEquivalence := by
  have hWE : W.toHoHom = E.toHoHom := by
    calc W.toHoHom
        = (𝟙 (HomotopyCategory.mk x)) ≫ W.toHoHom :=
          (Category.id_comp _).symm
      _ = (E.toHoHom ≫ V.toHoHom) ≫ W.toHoHom := by rw [hEV]
      _ = E.toHoHom ≫ (V.toHoHom ≫ W.toHoHom) := Category.assoc _ _ _
      _ = E.toHoHom := by rw [hVW, Category.comp_id]
  have hVE : V.toHoHom ≫ E.toHoHom = 𝟙 (HomotopyCategory.mk y) := by
    rw [← hWE]
    exact hVW
  exact ⟨⟨V.toHoHom, hEV, hVE⟩⟩

private noncomputable def squareLeft : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫
    (stdSimplex.δ (1 : Fin 2) ▷ Δ[1])

private noncomputable def squareRight : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫
    (stdSimplex.δ (0 : Fin 2) ▷ Δ[1])

private lemma prismTauMap_zero_zero_eq_leftUnitor_inv :
    prismTauMap.{u} 0 0 =
      (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv := by
  apply CartesianMonoidalCategory.hom_ext
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  · have hleft : prismTauMap.{u} 0 0 ≫
        CartesianMonoidalCategory.snd _ _ = 𝟙 Δ[1] := by
      rw [prodStdSimplex₁.ι_snd]
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      apply stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext t
      fin_cases t <;> rfl
    have hright : (stdSimplex.leftUnitor (Δ[1] : SSet.{u})).inv ≫
        CartesianMonoidalCategory.snd _ _ = 𝟙 Δ[1] := rfl
    rw [hleft, hright]

private lemma prismTauMap_one_zero_face_two :
    stdSimplex.δ (2 : Fin 3) ≫ prismTauMap.{u} 1 0 = squareLeft := by
  rw [prodStdSimplex₁.δ_ι_of_gt (p := 0) (i := (2 : Fin 3)) (j := (0 : Fin 2))]
  change prismTauMap.{u} 0 0 ≫
    (stdSimplex.δ (1 : Fin 2) ▷ Δ[1]) = squareLeft
  rw [prismTauMap_zero_zero_eq_leftUnitor_inv]
  rfl

private lemma prismTauMap_one_zero_face_zero :
    stdSimplex.δ (0 : Fin 3) ≫ prismTauMap.{u} 1 0 =
      ι₁ (X := (Δ[1] : SSet.{u})) := by
  exact prodStdSimplex₁.δ_ι_zero (p := 1)

private lemma prismTauMap_one_one_face_two :
    stdSimplex.δ (2 : Fin 3) ≫ prismTauMap.{u} 1 1 =
      ι₀ (X := (Δ[1] : SSet.{u})) := by
  exact prodStdSimplex₁.δ_ι_last (p := 1)

private lemma prismTauMap_one_one_face_zero :
    stdSimplex.δ (0 : Fin 3) ≫ prismTauMap.{u} 1 1 = squareRight := by
  rw [prodStdSimplex₁.δ_ι_of_lt (p := 0) (i := (0 : Fin 3)) (j := (1 : Fin 2))]
  change prismTauMap.{u} 0 0 ≫
    (stdSimplex.δ (0 : Fin 2) ▷ Δ[1]) = squareRight
  rw [prismTauMap_zero_zero_eq_leftUnitor_inv]
  rfl

private lemma prismTauMap_one_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ prismTauMap.{u} 1 1 =
      stdSimplex.δ (1 : Fin 3) ≫ prismTauMap.{u} 1 0 := by
  exact prodStdSimplex₁.δ_succ_castSucc_ι_succ (p := 1) (i := (0 : Fin 1))

private lemma square_top_src :
    stdSimplex.δ (1 : Fin 2) ≫ ι₁ (X := (Δ[1] : SSet.{u})) =
      stdSimplex.δ (0 : Fin 2) ≫ squareLeft := by
  apply yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.obj₀Equiv.injective <;> rfl

private lemma square_top_tgt :
    stdSimplex.δ (0 : Fin 2) ≫ ι₁ (X := (Δ[1] : SSet.{u})) =
      stdSimplex.δ (0 : Fin 2) ≫ squareRight := by
  apply yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.obj₀Equiv.injective <;> rfl

private noncomputable def squareDiagonal : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  stdSimplex.δ (1 : Fin 3) ≫ prismTauMap.{u} 1 0

private lemma square_diagonal_src :
    stdSimplex.δ (1 : Fin 2) ≫ squareDiagonal =
      stdSimplex.δ (1 : Fin 2) ≫ ι₀ (X := (Δ[1] : SSet.{u})) := by
  apply yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.obj₀Equiv.injective <;> rfl

private lemma square_diagonal_tgt :
    stdSimplex.δ (0 : Fin 2) ≫ squareDiagonal =
      stdSimplex.δ (0 : Fin 2) ≫ ι₁ (X := (Δ[1] : SSet.{u})) := by
  apply yonedaEquiv.injective
  apply Prod.ext <;> apply stdSimplex.obj₀Equiv.injective <;> rfl

private theorem exists_rightInverse_of_square
    {X : SSet.{u}} {x y : X.obj (Opposite.op (SimplexCategory.mk 0))}
    (E : SSet.Edge x y) (S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hleft : squareLeft ≫ S = yonedaEquiv.symm E.edge)
    (hright : squareRight ≫ S = yonedaEquiv.symm (Edge.id x).edge)
    (hbottom : ι₀ (X := (Δ[1] : SSet.{u})) ≫ S =
      yonedaEquiv.symm (Edge.id x).edge) :
    ∃ (V : SSet.Edge y x) (D : SSet.Edge x x),
      Nonempty (Edge.CompStruct E V D ×
        Edge.CompStruct (Edge.id x) (Edge.id x) D) := by
  let topMap : (Δ[1] : SSet.{u}) ⟶ X :=
    ι₁ (X := (Δ[1] : SSet.{u})) ≫ S
  let Vraw := Edge.mk' (yonedaEquiv topMap)
  have hVsrc : X.δ 1 (yonedaEquiv topMap) = y := by
    calc X.δ 1 (yonedaEquiv topMap)
        = yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ topMap) :=
          (stdSimplex.yonedaEquiv_δ_comp _ _).symm
      _ = yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ squareLeft ≫ S) := by
          dsimp only [topMap]
          rw [← Category.assoc, square_top_src, Category.assoc]
      _ = X.δ 0 E.edge := by
          rw [hleft,
            stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      _ = y := E.tgt_eq
  have hVtgt : X.δ 0 (yonedaEquiv topMap) = x := by
    calc X.δ 0 (yonedaEquiv topMap)
        = yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ topMap) :=
          (stdSimplex.yonedaEquiv_δ_comp _ _).symm
      _ = yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ squareRight ≫ S) := by
          dsimp only [topMap]
          rw [← Category.assoc, square_top_tgt, Category.assoc]
      _ = X.δ 0 (Edge.id x).edge := by
          rw [hright,
            stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      _ = x := (Edge.id x).tgt_eq
  let V : SSet.Edge y x := Vraw.ofEq hVsrc hVtgt
  let diagMap : (Δ[1] : SSet.{u}) ⟶ X := squareDiagonal ≫ S
  let Draw := Edge.mk' (yonedaEquiv diagMap)
  have hDsrc : X.δ 1 (yonedaEquiv diagMap) = x := by
    calc X.δ 1 (yonedaEquiv diagMap)
        = yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ diagMap) :=
          (stdSimplex.yonedaEquiv_δ_comp _ _).symm
      _ = yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫
            ι₀ (X := (Δ[1] : SSet.{u})) ≫ S) := by
          dsimp only [diagMap]
          rw [← Category.assoc, square_diagonal_src, Category.assoc]
      _ = X.δ 1 (Edge.id x).edge := by
          rw [hbottom,
            stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      _ = x := (Edge.id x).src_eq
  have hDtgt : X.δ 0 (yonedaEquiv diagMap) = x := by
    calc X.δ 0 (yonedaEquiv diagMap)
        = yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ diagMap) :=
          (stdSimplex.yonedaEquiv_δ_comp _ _).symm
      _ = yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ topMap) := by
          dsimp only [diagMap, topMap]
          rw [← Category.assoc, square_diagonal_tgt, Category.assoc]
      _ = X.δ 0 (yonedaEquiv topMap) :=
          stdSimplex.yonedaEquiv_δ_comp _ _
      _ = x := hVtgt
  let D : SSet.Edge x x := Draw.ofEq hDsrc hDtgt
  let P₀ : (Δ[2] : SSet.{u}) ⟶ X := prismTauMap 1 0 ≫ S
  let P₁ : (Δ[2] : SSet.{u}) ⟶ X := prismTauMap 1 1 ≫ S
  have hP₀₂ : X.δ 2 (yonedaEquiv P₀) = E.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    dsimp only [P₀]
    rw [← Category.assoc, prismTauMap_one_zero_face_two,
      hleft, Equiv.apply_symm_apply]
  have hP₀₀ : X.δ 0 (yonedaEquiv P₀) = V.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    dsimp only [P₀, V, Vraw, topMap]
    rw [← Category.assoc, prismTauMap_one_zero_face_zero]
    rfl
  have hP₀₁ : X.δ 1 (yonedaEquiv P₀) = D.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    dsimp only [P₀, D, Draw, diagMap]
    rfl
  have hP₁₂ : X.δ 2 (yonedaEquiv P₁) = (Edge.id x).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    dsimp only [P₁]
    rw [← Category.assoc, prismTauMap_one_one_face_two,
      hbottom, Equiv.apply_symm_apply]
  have hP₁₀ : X.δ 0 (yonedaEquiv P₁) = (Edge.id x).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    dsimp only [P₁]
    rw [← Category.assoc, prismTauMap_one_one_face_zero,
      hright, Equiv.apply_symm_apply]
  have hP₁₁ : X.δ 1 (yonedaEquiv P₁) = D.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    dsimp only [P₁, D, Draw, diagMap]
    rw [← Category.assoc, prismTauMap_one_diagonal]
    rfl
  have hEV : Edge.CompStruct E V D :=
    Edge.CompStruct.mk (yonedaEquiv P₀) hP₀₂ hP₀₀ hP₀₁
  have hId : Edge.CompStruct (Edge.id x) (Edge.id x) D :=
    Edge.CompStruct.mk (yonedaEquiv P₁) hP₁₂ hP₁₀ hP₁₁
  exact ⟨V, D, ⟨hEV, hId⟩⟩

private noncomputable def functorSquareUncurry {A C : SSet.{u}}
    (H : (((Δ[1] : SSet.{u}) ⊗ A) ⊗ Δ[1] : SSet.{u}) ⟶ C) :
    A ⊗ (Δ[1] ⊗ Δ[1]) ⟶ C :=
  (α_ A Δ[1] Δ[1]).inv ≫
    (((β_ A Δ[1]).hom ▷ Δ[1]) ≫ H)

private lemma functorSquare_left_prefix (A : SSet.{u}) :
    (A ◁ squareLeft) ≫ (α_ A Δ[1] Δ[1]).inv ≫
        ((β_ A Δ[1]).hom ▷ Δ[1]) =
      ((stdSimplex.leftUnitor A).inv ▷ Δ[1]) ≫
        ((((boundary.ι (1 : Fin 2) ▷ A) ▷ Δ[1]) ≫
          ((((boundary 1).ι ▷ A) ▷ Δ[1])))) := by
  apply CartesianMonoidalCategory.hom_ext
  · apply CartesianMonoidalCategory.hom_ext
    · apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro z
      apply stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext k
      rfl
    · rfl
  · rfl

private lemma functorSquare_right_prefix (A : SSet.{u}) :
    (A ◁ squareRight) ≫ (α_ A Δ[1] Δ[1]).inv ≫
        ((β_ A Δ[1]).hom ▷ Δ[1]) =
      ((stdSimplex.leftUnitor A).inv ▷ Δ[1]) ≫
        ((((boundary.ι (0 : Fin 2) ▷ A) ▷ Δ[1]) ≫
          ((((boundary 1).ι ▷ A) ▷ Δ[1])))) := by
  apply CartesianMonoidalCategory.hom_ext
  · apply CartesianMonoidalCategory.hom_ext
    · apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro z
      apply stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext k
      rfl
    · rfl
  · rfl

private lemma functorSquare_bottom_prefix (A : SSet.{u}) :
    (A ◁ ι₀ (X := (Δ[1] : SSet.{u}))) ≫
        (α_ A Δ[1] Δ[1]).inv ≫
        ((β_ A Δ[1]).hom ▷ Δ[1]) =
      (β_ A Δ[1]).hom ≫
        prismSectionAt ((Δ[1] : SSet.{u}) ⊗ A) 0 := by
  apply CartesianMonoidalCategory.hom_ext
  · apply CartesianMonoidalCategory.hom_ext <;> rfl
  · apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    apply stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    rfl

private noncomputable def functorSquare {A C : SSet.{u}}
    (H : (((Δ[1] : SSet.{u}) ⊗ A) ⊗ Δ[1] : SSet.{u}) ⟶ C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom A).obj C :=
  MonoidalClosed.curry (functorSquareUncurry H)

private lemma functorSquare_left {A C : SSet.{u}}
    (E I : A ⊗ Δ[1] ⟶ C)
    (H : (((Δ[1] : SSet.{u}) ⊗ A) ⊗ Δ[1] : SSet.{u}) ⟶ C)
    (hH : ((((boundary 1).ι ▷ A) ▷ Δ[1]) ≫ H =
      boundarySquareDatum E I)) :
    squareLeft ≫ functorSquare H = MonoidalClosed.curry E := by
  rw [functorSquare, ← MonoidalClosed.curry_natural_left]
  congr 1
  calc (A ◁ squareLeft) ≫ functorSquareUncurry H
      = (((stdSimplex.leftUnitor A).inv ▷ Δ[1]) ≫
          ((((boundary.ι (1 : Fin 2) ▷ A) ▷ Δ[1]) ≫
            ((((boundary 1).ι ▷ A) ▷ Δ[1]))))) ≫ H := by
          dsimp only [functorSquareUncurry]
          simpa only [Category.assoc] using
            congrArg (fun q ↦ q ≫ H) (functorSquare_left_prefix A)
    _ = ((stdSimplex.leftUnitor A).inv ▷ Δ[1]) ≫
          ((((boundary.ι (1 : Fin 2) ▷ A) ▷ Δ[1]) ≫
            boundarySquareDatum E I)) := by
              simp only [Category.assoc, hH]
    _ = ((stdSimplex.leftUnitor A).inv ▷ Δ[1]) ≫
          (((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ E) := by
            rw [boundarySquareDatum_zero]
    _ = E := by
      rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
        Iso.inv_hom_id, MonoidalCategory.id_whiskerRight, Category.id_comp]

private lemma functorSquare_right {A C : SSet.{u}}
    (E I : A ⊗ Δ[1] ⟶ C)
    (H : (((Δ[1] : SSet.{u}) ⊗ A) ⊗ Δ[1] : SSet.{u}) ⟶ C)
    (hH : ((((boundary 1).ι ▷ A) ▷ Δ[1]) ≫ H =
      boundarySquareDatum E I)) :
    squareRight ≫ functorSquare H = MonoidalClosed.curry I := by
  rw [functorSquare, ← MonoidalClosed.curry_natural_left]
  congr 1
  calc (A ◁ squareRight) ≫ functorSquareUncurry H
      = (((stdSimplex.leftUnitor A).inv ▷ Δ[1]) ≫
          ((((boundary.ι (0 : Fin 2) ▷ A) ▷ Δ[1]) ≫
            ((((boundary 1).ι ▷ A) ▷ Δ[1]))))) ≫ H := by
          dsimp only [functorSquareUncurry]
          simpa only [Category.assoc] using
            congrArg (fun q ↦ q ≫ H) (functorSquare_right_prefix A)
    _ = ((stdSimplex.leftUnitor A).inv ▷ Δ[1]) ≫
          ((((boundary.ι (0 : Fin 2) ▷ A) ▷ Δ[1]) ≫
            boundarySquareDatum E I)) := by
              simp only [Category.assoc, hH]
    _ = ((stdSimplex.leftUnitor A).inv ▷ Δ[1]) ≫
          (((stdSimplex.leftUnitor A).hom ▷ Δ[1]) ≫ I) := by
            rw [boundarySquareDatum_one]
    _ = I := by
      rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
        Iso.inv_hom_id, MonoidalCategory.id_whiskerRight, Category.id_comp]

private lemma functorSquare_bottom {A C : SSet.{u}}
    (H : (((Δ[1] : SSet.{u}) ⊗ A) ⊗ Δ[1] : SSet.{u}) ⟶ C)
    (F : A ⟶ C)
    (hH : prismSectionAt ((Δ[1] : SSet.{u}) ⊗ A) 0 ≫ H =
      CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) A ≫ F) :
    ι₀ (X := (Δ[1] : SSet.{u})) ≫ functorSquare H =
      MonoidalClosed.curry (CartesianMonoidalCategory.fst A Δ[1] ≫ F) := by
  rw [functorSquare, ← MonoidalClosed.curry_natural_left]
  congr 1
  calc (A ◁ ι₀ (X := (Δ[1] : SSet.{u}))) ≫ functorSquareUncurry H
      = ((β_ A Δ[1]).hom ≫
          prismSectionAt ((Δ[1] : SSet.{u}) ⊗ A) 0) ≫ H := by
          dsimp only [functorSquareUncurry]
          simpa only [Category.assoc] using
            congrArg (fun q ↦ q ≫ H) (functorSquare_bottom_prefix A)
    _ = (β_ A Δ[1]).hom ≫
          (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) A ≫ F) := by
            rw [Category.assoc, hH]
    _ = CartesianMonoidalCategory.fst A Δ[1] ≫ F := by
      rw [← Category.assoc, CartesianMonoidalCategory.braiding_hom_snd]

private lemma fst_comp_eq_ihomPrism_id {A C : SSet.{u}}
    (F : ((ihom A).obj C).obj (Opposite.op (SimplexCategory.mk 0))) :
    CartesianMonoidalCategory.fst A Δ[1] ≫ (ihomVertexEquiv A C).symm F =
      ihomPrismOfSimplex (Edge.id F).edge := by
  apply (ihomSimplexEquiv A C 1).injective
  change ihomSimplexOfPrism
      (CartesianMonoidalCategory.fst A Δ[1] ≫ (ihomVertexEquiv A C).symm F) =
    ihomSimplexOfPrism (ihomPrismOfSimplex (Edge.id F).edge)
  rw [ihomSimplexOfPrism_fst,
    ihomSimplexOfPrism_ihomPrismOfSimplex, Edge.id_edge,
    Equiv.apply_symm_apply]

private lemma curry_fst_comp_eq_id {A C : SSet.{u}}
    (F : ((ihom A).obj C).obj (Opposite.op (SimplexCategory.mk 0))) :
    MonoidalClosed.curry
        (CartesianMonoidalCategory.fst A Δ[1] ≫ (ihomVertexEquiv A C).symm F) =
      yonedaEquiv.symm (Edge.id F).edge := by
  rw [fst_comp_eq_ihomPrism_id, curry_ihomPrismOfSimplex]

private theorem exists_pointwiseRightInverseData
    {A C : SSet.{u}} [Quasicategory C]
    {F G : ((ihom A).obj C).obj (Opposite.op (SimplexCategory.mk 0))}
    (E : SSet.Edge F G) (hE : E.PointwiseIsEquivalence) :
    ∃ (V : SSet.Edge G F) (D : SSet.Edge F F),
      Nonempty (Edge.CompStruct E V D ×
        Edge.CompStruct (Edge.id F) (Edge.id F) D) := by
  obtain ⟨H, hHr, hHs, hHv⟩ := exists_pointwiseRightInverse_square E hE
  let S : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom A).obj C := functorSquare H
  have hleft : squareLeft ≫ S = yonedaEquiv.symm E.edge := by
    dsimp only [S]
    calc squareLeft ≫ functorSquare H
        = MonoidalClosed.curry (ihomPrismOfSimplex E.edge) :=
          functorSquare_left _ _ H hHr
      _ = yonedaEquiv.symm E.edge := curry_ihomPrismOfSimplex E.edge
  have hright : squareRight ≫ S = yonedaEquiv.symm (Edge.id F).edge := by
    dsimp only [S]
    calc squareRight ≫ functorSquare H
        = MonoidalClosed.curry (ihomPrismOfSimplex (Edge.id F).edge) :=
          functorSquare_right _ _ H hHr
      _ = yonedaEquiv.symm (Edge.id F).edge :=
          curry_ihomPrismOfSimplex (Edge.id F).edge
  have hbottom : ι₀ (X := (Δ[1] : SSet.{u})) ≫ S =
      yonedaEquiv.symm (Edge.id F).edge := by
    dsimp only [S]
    calc ι₀ (X := (Δ[1] : SSet.{u})) ≫ functorSquare H
        = MonoidalClosed.curry
            (CartesianMonoidalCategory.fst A Δ[1] ≫
              (ihomVertexEquiv A C).symm F) :=
          functorSquare_bottom H _ hHs
      _ = yonedaEquiv.symm (Edge.id F).edge := curry_fst_comp_eq_id F
  exact exists_rightInverse_of_square E S hleft hright hbottom

private lemma isEquivalence_snd_of_compStruct
    {X : SSet.{u}}
    {x₀ x₁ x₂ : X.obj (Opposite.op (SimplexCategory.mk 0))}
    {e₀₁ : SSet.Edge x₀ x₁} {e₁₂ : SSet.Edge x₁ x₂}
    {e₀₂ : SSet.Edge x₀ x₂}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂)
    (h₀₁ : e₀₁.IsEquivalence) (h₀₂ : e₀₂.IsEquivalence) :
    e₁₂.IsEquivalence := by
  have hfirst : IsIso e₀₁.toHoHom := h₀₁
  have hcomp : IsIso (e₀₁.toHoHom ≫ e₁₂.toHoHom) := by
    rw [Edge.toHoHom_comp h]
    exact h₀₂
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    e₀₁.toHoHom e₁₂.toHoHom hfirst hcomp

private lemma pointwiseIsEquivalence_of_rightInverse
    {A C : SSet.{u}}
    {F G : ((ihom A).obj C).obj (Opposite.op (SimplexCategory.mk 0))}
    (E : SSet.Edge F G) (V : SSet.Edge G F) (D : SSet.Edge F F)
    (hE : E.PointwiseIsEquivalence)
    (hEV : Edge.CompStruct E V D)
    (hId : Edge.CompStruct (Edge.id F) (Edge.id F) D) :
    V.PointwiseIsEquivalence := by
  intro a
  let preA := (pre (yonedaEquiv.symm a)).app C
  let ev₀ := (evalDeltaZeroIso C).hom
  let ev := preA ≫ ev₀
  have hEVa : Edge.CompStruct (E.map ev) (V.map ev) (D.map ev) := hEV.map ev
  have hIda : Edge.CompStruct ((Edge.id F).map ev) ((Edge.id F).map ev)
      (D.map ev) := hId.map ev
  have hidEq : ((Edge.id F).map ev) = Edge.id (ev.app _ F) := Edge.map_id F ev
  have hDa : (D.map ev).IsEquivalence := by
    apply Edge.IsEquivalence.of_compStruct hIda
    · rw [hidEq]
      exact Edge.isEquivalence_id _
    · rw [hidEq]
      exact Edge.isEquivalence_id _
  have hEa : (E.map ev).IsEquivalence := by
    have hmap : E.map ev = (E.map preA).map ev₀ := Edge.ext rfl
    rw [hmap]
    exact hE a
  exact isEquivalence_snd_of_compStruct hEVa hEa hDa

/-- An edge in a functor quasicategory is an equivalence exactly when all of
its vertex evaluations are equivalences. The reverse implication uses only the
pure source-prism extension along a monomorphism. -/
public theorem Edge.isEquivalence_iff_forall_eval_vertex
    {A C : SSet.{u}} [Quasicategory C]
    {F G : ((ihom A).obj C).obj (Opposite.op (SimplexCategory.mk 0))}
    (E : SSet.Edge F G) :
    E.IsEquivalence ↔
      ∀ a : A.obj (Opposite.op (SimplexCategory.mk 0)),
        ((E.map ((pre (yonedaEquiv.symm a)).app C)).map
          (evalDeltaZeroIso C).hom).IsEquivalence := by
  constructor
  · intro hE a
    exact hE.eval_vertex (yonedaEquiv.symm a)
  · intro hE
    obtain ⟨V, D, ⟨hEV, hIdF⟩⟩ := exists_pointwiseRightInverseData E hE
    have hV : V.PointwiseIsEquivalence :=
      pointwiseIsEquivalence_of_rightInverse E V D hE hEV hIdF
    obtain ⟨W, D', ⟨hVW, hIdG⟩⟩ := exists_pointwiseRightInverseData V hV
    exact isEquivalence_of_two_successive_rightInverses E V W
      (rightInverseEquation_of_compStructs E V D hEV hIdF)
      (rightInverseEquation_of_compStructs V W D' hVW hIdG)

end SSet
