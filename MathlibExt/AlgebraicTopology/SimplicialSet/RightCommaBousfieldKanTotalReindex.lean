/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanTotalHomotopy
public import
  MathlibExt.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Equivalence

/-!
# Reindexing for the right-comma BK degree decoder

This file computes the right-comma BK degree decoder after each face and
degeneracy generator on a weighted summand.  A shared typed leaf proves the
formula from an explicit weighted-bar inclusion square; the four public
specializations use the landed `d₀`, last-face, interior-face, and degeneracy
inclusion formulas.  GenRel induction in the quotient simplex category then
assembles these generator formulas into the decoder theorem for an arbitrary
simplex-category morphism.

No global cylinder, realization, weak-equivalence, or Quillen-Theorem-A claim
is made here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Simplicial

namespace SSet

universe u v w hIndex

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- A weighted summand inclusion, retyped at the public diagonal BK carrier.
This wrapper prevents downstream proofs from depending on reducibility of the
diagonal and weighted-bar object spellings. -/
def rightCommaBKIncl (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n) :
    ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌) →
      (bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).obj (op ⦋n⦌) :=
  (StrictOrdinaryWeightedBar.wbarIncl
    (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app (op ⦋n⦌)

@[simp]
theorem rightCommaBKIncl_apply (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌)) :
    rightCommaBKIncl F n p X =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
          (op ⦋n⦌) X :=
  rfl

/-- Reindex a terminal-weighted outer chain.  The terminal weight is carried
unchanged. -/
def rightCommaWIdxReindex
    {D : Type u} [Category.{hIndex} D] {m n : ℕ}
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) m :=
  ⟨rightCommaReindexOuter p.1 Φ, p.2⟩

@[simp]
theorem rightCommaWIdxReindex_chain
    {D : Type u} [Category.{hIndex} D] {m n : ℕ}
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    (rightCommaWIdxReindex p Φ).1 = rightCommaReindexOuter p.1 Φ :=
  rfl

@[simp]
theorem rightCommaWIdxReindex_weight
    {D : Type u} [Category.{hIndex} D] {m n : ℕ}
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    (rightCommaWIdxReindex p Φ).2 = p.2 :=
  rfl

/-- Outer-chain reindexing by the identity is the identity. -/
theorem rightCommaReindexOuter_id
    {D : Type u} [Category.{hIndex} D] {n : ℕ} (s : ComposableArrows D n) :
    rightCommaReindexOuter s (𝟭 (Fin (n + 1))) = s :=
  Functor.id_comp s

/-- Outer-chain reindexing respects composition. -/
theorem rightCommaReindexOuter_comp
    {D : Type u} [Category.{hIndex} D] {l m n : ℕ}
    (s : ComposableArrows D n) (Φ : Fin (m + 1) ⥤ Fin (n + 1))
    (Ψ : Fin (l + 1) ⥤ Fin (m + 1)) :
    rightCommaReindexOuter (rightCommaReindexOuter s Φ) Ψ =
      rightCommaReindexOuter s (Ψ ⋙ Φ) :=
  (Functor.assoc Ψ Φ s).symm

/-- The base arrows selected by two reindexings compose to the base arrow of
the composite reindexing. -/
theorem rightCommaReindexBase_comp
    {D : Type u} [Category.{hIndex} D] {l m n : ℕ}
    (s : ComposableArrows D n) (Φ : Fin (m + 1) ⥤ Fin (n + 1))
    (Ψ : Fin (l + 1) ⥤ Fin (m + 1)) :
    rightCommaReindexBase s Φ ≫
        rightCommaReindexBase (rightCommaReindexOuter s Φ) Ψ =
      rightCommaReindexBase s (Ψ ⋙ Φ) := by
  change s.map _ ≫ s.map _ = s.map _
  rw [← s.map_comp]
  exact congrArg s.map (Subsingleton.elim _ _)

/-- The reindexing functor carried by a simplex-category morphism. -/
abbrev rightCommaSimplexReindexFunctorHom {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) : Fin (m + 1) ⥤ Fin (n + 1) :=
  (SimplexCategory.toCat.map f).toFunctor

/-- Simplex reindexing sends an identity to the identity finite-chain
functor. -/
theorem rightCommaSimplexReindexFunctorHom_id (n : ℕ) :
    rightCommaSimplexReindexFunctorHom (𝟙 ⦋n⦌) = 𝟭 (Fin (n + 1)) := by
  have h := congrArg Cat.Hom.toFunctor
    (SimplexCategory.toCat.map_id ⦋n⦌)
  change rightCommaSimplexReindexFunctorHom (𝟙 ⦋n⦌) =
    𝟭 (Fin (n + 1)) at h
  exact h

/-- Simplex reindexing preserves composition in its categorical
orientation. -/
theorem rightCommaSimplexReindexFunctorHom_comp {l m n : ℕ}
    (f : ⦋l⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n⦌) :
    rightCommaSimplexReindexFunctorHom (f ≫ g) =
      rightCommaSimplexReindexFunctorHom f ⋙
        rightCommaSimplexReindexFunctorHom g := by
  have h := congrArg Cat.Hom.toFunctor
    (SimplexCategory.toCat.map_comp f g)
  change rightCommaSimplexReindexFunctorHom (f ≫ g) =
    rightCommaSimplexReindexFunctorHom f ⋙
      rightCommaSimplexReindexFunctorHom g at h
  exact h

/-- On a face generator, simplex reindexing is the strict omission functor. -/
theorem rightCommaSimplexReindexFunctorHom_δ {n : ℕ} (i : Fin (n + 2)) :
    rightCommaSimplexReindexFunctorHom (SimplexCategory.δ i) =
      StrictOmitDup.omitFinFunctor n i := by
  apply CategoryTheory.Functor.hext
  · intro j
    rfl
  · intro j k f
    exact HEq.rfl

/-- On a degeneracy generator, simplex reindexing is the strict duplication
functor. -/
theorem rightCommaSimplexReindexFunctorHom_σ {n : ℕ} (i : Fin (n + 1)) :
    rightCommaSimplexReindexFunctorHom (SimplexCategory.σ i) =
      StrictOmitDup.dupFinFunctor n i := by
  apply CategoryTheory.Functor.hext
  · intro j
    rfl
  · intro j k f
    exact HEq.rfl

private theorem rightCommaOmitZeroChain
    {D : Type u} [Category.{hIndex} D] {n : ℕ}
    (s : ComposableArrows D (n + 1)) :
    SrepBridge.srepDropFirst s =
      (StrictOmitDup.omitAt (0 : Fin (n + 2))).obj s := by
  have hFin : Fin.succFunctor (n + 1) =
      StrictOmitDup.omitFinFunctor n 0 := by
    refine CategoryTheory.Functor.ext (fun k => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    change k.succ = (StrictOmitDup.omitFinFunctor n 0).obj k
    exact (StrictOmitDup.omitFin_zero_succ n k).symm
  have h := StrictOmitDup.whiskerLeft_obj_eq_of_idx_obj_eq
    (C := D) hFin s
  change (ComposableArrows.whiskerLeftFunctor
      (Fin.succFunctor (n + 1))).obj s =
    (ComposableArrows.whiskerLeftFunctor
      (StrictOmitDup.omitFinFunctor n 0)).obj s
  exact h

private theorem rightCommaOmitLastChain
    {D : Type u} [Category.{hIndex} D] {n : ℕ}
    (s : ComposableArrows D (n + 1)) :
    SrepBridge.srepDropLast s =
      (StrictOmitDup.omitAt (Fin.last (n + 1))).obj s := by
  have hFin : Fin.castSuccFunctor (n + 1) =
      StrictOmitDup.omitFinFunctor n (Fin.last (n + 1)) := by
    refine CategoryTheory.Functor.ext (fun k => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    change k.castSucc =
      (StrictOmitDup.omitFinFunctor n (Fin.last (n + 1))).obj k
    exact (StrictOmitDup.omitFin_last_castSucc n k).symm
  have h := StrictOmitDup.whiskerLeft_obj_eq_of_idx_obj_eq
    (C := D) hFin s
  change (ComposableArrows.whiskerLeftFunctor
      (Fin.castSuccFunctor (n + 1))).obj s =
    (ComposableArrows.whiskerLeftFunctor
      (StrictOmitDup.omitFinFunctor n (Fin.last (n + 1)))).obj s
  exact h

/-- Terminal-weight reindexing along the zeroth face is the weighted zeroth
face index. -/
theorem rightCommaWIdxReindex_δ_zero
    {D : Type u} [Category.{hIndex} D] (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) (n + 1)) :
    rightCommaWIdxReindex p
        (rightCommaSimplexReindexFunctorHom
          (SimplexCategory.δ (0 : Fin (n + 2)))) =
      StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit D) n p := by
  rw [rightCommaSimplexReindexFunctorHom_δ]
  obtain ⟨s, w⟩ := p
  change PUnit at w
  cases w
  exact Sigma.ext (rightCommaOmitZeroChain s).symm HEq.rfl

/-- Terminal-weight reindexing along the last face is the weighted last-face
index. -/
theorem rightCommaWIdxReindex_δ_last
    {D : Type u} [Category.{hIndex} D] (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) (n + 1)) :
    rightCommaWIdxReindex p
        (rightCommaSimplexReindexFunctorHom
          (SimplexCategory.δ (Fin.last (n + 1)))) =
      StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit D) n p := by
  rw [rightCommaSimplexReindexFunctorHom_δ]
  obtain ⟨s, w⟩ := p
  change PUnit at w
  cases w
  exact Sigma.ext (rightCommaOmitLastChain s).symm HEq.rfl

/-- Terminal-weight reindexing along a non-last face is the weighted interior
face index (the statement is also valid for the zeroth position). -/
theorem rightCommaWIdxReindex_δ_inner
    {D : Type u} [Category.{hIndex} D] (n : ℕ) (i : Fin (n + 2))
    (hiLast : i ≠ Fin.last (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) (n + 1)) :
    rightCommaWIdxReindex p
        (rightCommaSimplexReindexFunctorHom (SimplexCategory.δ i)) =
      StrictOrdinaryWeightedBar.wFaceInnerIdx
        (CategoryBar.replUnit D) n i hiLast p := by
  rw [rightCommaSimplexReindexFunctorHom_δ]
  obtain ⟨s, w⟩ := p
  change PUnit at w
  cases w
  exact Sigma.ext rfl HEq.rfl

/-- Terminal-weight reindexing along a degeneracy is the weighted interior
degeneracy index. -/
theorem rightCommaWIdxReindex_σ
    {D : Type u} [Category.{hIndex} D] (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) n) :
    rightCommaWIdxReindex p
        (rightCommaSimplexReindexFunctorHom (SimplexCategory.σ i)) =
      StrictOrdinaryWeightedBar.wDegInnerIdx
        (CategoryBar.replUnit D) n i p := by
  rw [rightCommaSimplexReindexFunctorHom_σ]
  obtain ⟨s, w⟩ := p
  change PUnit at w
  cases w
  exact Sigma.ext rfl HEq.rfl

/-- The base arrow selected by identity reindexing is the identity. -/
theorem rightCommaReindexBase_id
    {D : Type u} [Category.{hIndex} D] {n : ℕ} (s : ComposableArrows D n) :
    rightCommaReindexBase s (𝟭 (Fin (n + 1))) = 𝟙 s.left := by
  let f₀ : (0 : Fin (n + 1)) ⟶
      (𝟭 (Fin (n + 1))).obj 0 := homOfLE (Fin.zero_le _)
  have hf₀ : f₀ = 𝟙 (0 : Fin (n + 1)) := Subsingleton.elim _ _
  change s.map f₀ = 𝟙 s.left
  exact (congrArg s.map hf₀).trans (s.map_id 0)

/-- When a reindexing fixes the zeroth vertex, its selected base arrow is the
corresponding explicit object transport. -/
theorem rightCommaReindexBase_eq_eqToHom_of_obj_zero
    {D : Type u} [Category.{hIndex} D] {m n : ℕ}
    (s : ComposableArrows D n) (Φ : Fin (m + 1) ⥤ Fin (n + 1))
    (h₀ : Φ.obj 0 = 0) :
    rightCommaReindexBase s Φ =
      eqToHom (congrArg s.obj h₀.symm) := by
  let f₀ : (0 : Fin (n + 1)) ⟶ Φ.obj 0 :=
    homOfLE (Fin.zero_le _)
  have hf₀ : f₀ = eqToHom h₀.symm := Subsingleton.elim _ _
  change s.map f₀ = eqToHom (congrArg s.obj h₀.symm)
  exact (congrArg s.map hf₀).trans (eqToHom_map s h₀.symm)

/-- The zeroth-face finite reindexing sends zero to the old first vertex. -/
theorem rightCommaSimplexReindexFunctorHom_δ_zero_obj_zero (n : ℕ) :
    (rightCommaSimplexReindexFunctorHom
      (SimplexCategory.δ (0 : Fin (n + 2)))).obj 0 =
        (1 : Fin (n + 2)) := by
  have hΦ := congrArg (fun Φ => Φ.obj (0 : Fin (n + 1)))
    (rightCommaSimplexReindexFunctorHom_δ (0 : Fin (n + 2)))
  exact hΦ.trans (StrictOmitDup.omitFin_zero_succ n 0)

/-- The zeroth-face reindexing sends the new left endpoint to the old first
vertex. -/
theorem rightCommaReindexOuter_δ_zero_left
    {D : Type u} [Category.{hIndex} D] (n : ℕ)
    (s : ComposableArrows D (n + 1)) :
    (rightCommaReindexOuter s
      (rightCommaSimplexReindexFunctorHom
        (SimplexCategory.δ (0 : Fin (n + 2))))).left = s.obj' 1 :=
  congrArg s.obj (rightCommaSimplexReindexFunctorHom_δ_zero_obj_zero n)

/-- The first outer arrow, followed by the zeroth-face endpoint transport,
is the base arrow selected by reindexing. -/
theorem rightCommaReindexBase_δ_zero
    {D : Type u} [Category.{hIndex} D] (n : ℕ)
    (s : ComposableArrows D (n + 1)) :
    s.map' 0 1 ≫
        eqToHom (rightCommaReindexOuter_δ_zero_left n s).symm =
      rightCommaReindexBase s
        (rightCommaSimplexReindexFunctorHom
          (SimplexCategory.δ (0 : Fin (n + 2)))) := by
  let Φ := rightCommaSimplexReindexFunctorHom
    (SimplexCategory.δ (0 : Fin (n + 2)))
  have hIndex : Φ.obj 0 = (1 : Fin (n + 2)) := by
    exact rightCommaSimplexReindexFunctorHom_δ_zero_obj_zero n
  have hLeft : rightCommaReindexOuter_δ_zero_left n s =
      congrArg s.obj hIndex := Subsingleton.elim _ _
  rw [hLeft]
  rw [← eqToHom_map, ← s.map_comp]
  · exact congrArg s.map (Subsingleton.elim _ _)
  · exact Fin.ext (congrArg Fin.val hIndex.symm)

/-- Terminal-weight WIdx reindexing by the identity is the identity. -/
theorem rightCommaWIdxReindex_id
    {D : Type u} [Category.{hIndex} D] {n : ℕ}
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n) :
    rightCommaWIdxReindex p (𝟭 (Fin (n + 1))) = p := by
  obtain ⟨s, w⟩ := p
  change PUnit at w
  cases w
  exact Sigma.ext (rightCommaReindexOuter_id s) HEq.rfl

/-- Terminal-weight WIdx reindexing respects composition. -/
theorem rightCommaWIdxReindex_comp
    {D : Type u} [Category.{hIndex} D] {l m n : ℕ}
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1))
    (Ψ : Fin (l + 1) ⥤ Fin (m + 1)) :
    rightCommaWIdxReindex (rightCommaWIdxReindex p Φ) Ψ =
      rightCommaWIdxReindex p (Ψ ⋙ Φ) := by
  obtain ⟨s, w⟩ := p
  change PUnit at w
  cases w
  exact Sigma.ext (rightCommaReindexOuter_comp s Φ Ψ) HEq.rfl

/-- Reindexing of inner right-comma chains respects composition. -/
theorem rightCommaReindexInner_comp (F : C ⥤ D) {l m n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1))
    (Ψ : Fin (l + 1) ⥤ Fin (m + 1)) :
    rightCommaReindexInner F (rightCommaReindexOuter s Φ)
        (rightCommaReindexInner F s X Φ) Ψ =
      rightCommaReindexInner F s X (Ψ ⋙ Φ) := by
  change Fin (n + 1) ⥤ CostructuredArrow F s.left at X
  apply CategoryTheory.Functor.hext
  · intro i
    change
      (CostructuredArrow.map
          (rightCommaReindexBase (rightCommaReindexOuter s Φ) Ψ)).obj
          ((CostructuredArrow.map (rightCommaReindexBase s Φ)).obj
            (X.obj (Φ.obj (Ψ.obj i)))) =
        (CostructuredArrow.map
          (rightCommaReindexBase s (Ψ ⋙ Φ))).obj
            (X.obj (Φ.obj (Ψ.obj i)))
    refine CostructuredArrow.obj_ext _ _ (rfl : _ = _) ?_
    rw [eqToHom_refl, F.map_id, Category.id_comp]
    change (X.obj (Φ.obj (Ψ.obj i))).hom ≫
        rightCommaReindexBase s (Ψ ⋙ Φ) =
      ((X.obj (Φ.obj (Ψ.obj i))).hom ≫
          rightCommaReindexBase s Φ) ≫
        rightCommaReindexBase (rightCommaReindexOuter s Φ) Ψ
    rw [Category.assoc, rightCommaReindexBase_comp]
  · intro i j f
    change
      (CostructuredArrow.map
          (rightCommaReindexBase (rightCommaReindexOuter s Φ) Ψ)).map
          ((CostructuredArrow.map (rightCommaReindexBase s Φ)).map
            (X.map (Φ.map (Ψ.map f)))) ≍
        (CostructuredArrow.map
          (rightCommaReindexBase s (Ψ ⋙ Φ))).map
            (X.map (Φ.map (Ψ.map f)))
    rw [← rightCommaReindexBase_comp s Φ Ψ]
    have hMapComp := congrArg Cat.Hom.toFunctor
      ((CostructuredArrow.functor F).map_comp
        (rightCommaReindexBase s Φ)
        (rightCommaReindexBase (rightCommaReindexOuter s Φ) Ψ))
    change CostructuredArrow.map
        (rightCommaReindexBase s Φ ≫
          rightCommaReindexBase (rightCommaReindexOuter s Φ) Ψ) =
      CostructuredArrow.map (rightCommaReindexBase s Φ) ⋙
        CostructuredArrow.map
          (rightCommaReindexBase (rightCommaReindexOuter s Φ) Ψ) at hMapComp
    exact (CategoryTheory.Functor.hcongr_hom hMapComp
      (X.map (Φ.map (Ψ.map f)))).symm

/-- Reindexing an inner right-comma chain by the identity recovers the
original chain. -/
theorem rightCommaReindexInner_id (F : C ⥤ D) {n : ℕ}
    (s : ComposableArrows D n)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj s.left) n) :
    rightCommaReindexInner F s X (𝟭 (Fin (n + 1))) = X := by
  change Fin (n + 1) ⥤ CostructuredArrow F s.left at X
  change ((𝟭 (Fin (n + 1)) ⋙ X) ⋙
      CostructuredArrow.map
        (rightCommaReindexBase s (𝟭 (Fin (n + 1))))) = X
  rw [rightCommaReindexBase_id]
  have hMapId := congrArg Cat.Hom.toFunctor
    ((CostructuredArrow.functor F).map_id s.left)
  change CostructuredArrow.map (𝟙 s.left) =
    𝟭 (CostructuredArrow F s.left) at hMapId
  rw [CategoryTheory.Functor.id_comp, hMapId,
    CategoryTheory.Functor.comp_id]

/-- Package the reindexed weighted outer chain and inner comma simplex in the
dependent coordinates of the degree decoder. -/
def rightCommaTotalReindexPair (F : C ⥤ D) {m n : ℕ}
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌))
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    Σ q : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) m,
      ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj q.1.left).obj (op ⦋m⦌) :=
  ⟨rightCommaWIdxReindex p Φ, rightCommaReindexInner F p.1 X Φ⟩

/-- The packaged total reindexing preserves identities. -/
theorem rightCommaTotalReindexPair_id (F : C ⥤ D) {n : ℕ}
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌)) :
    rightCommaTotalReindexPair F p X (𝟭 (Fin (n + 1))) = ⟨p, X⟩ := by
  refine Sigma.ext (rightCommaWIdxReindex_id p) ?_
  exact heq_of_eq (rightCommaReindexInner_id F p.1 X)

/-- The packaged total reindexing preserves composition, with the first
reindexing on the right of the composite finite-index functor. -/
theorem rightCommaTotalReindexPair_comp (F : C ⥤ D) {l m n : ℕ}
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌))
    (Φ : Fin (m + 1) ⥤ Fin (n + 1))
    (Ψ : Fin (l + 1) ⥤ Fin (m + 1)) :
    rightCommaTotalReindexPair F (rightCommaWIdxReindex p Φ)
        (rightCommaReindexInner F p.1 X Φ) Ψ =
      rightCommaTotalReindexPair F p X (Ψ ⋙ Φ) := by
  refine Sigma.ext (rightCommaWIdxReindex_comp p Φ Ψ) ?_
  exact heq_of_eq (rightCommaReindexInner_comp F p.1 X Φ Ψ)

/-- Applying the right-comma diagram map after simplicial reindexing is the
explicitly reindexed inner comma chain. -/
theorem rightCommaNerveDiagram_map_reindex_apply (F : C ⥤ D)
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (s : ComposableArrows D n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj s.left).obj (op ⦋n⦌)) :
    ((rightCommaNerveDiagram.{max u w, max v w, u} F).map
      (rightCommaReindexBase s (rightCommaSimplexReindexFunctorHom f))).app
        (op ⦋m⦌)
          (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj s.left).map f.op X) =
      rightCommaReindexInner F s X
        (rightCommaSimplexReindexFunctorHom f) :=
  rfl

/-- The zeroth-face coefficient formula is the explicit right-comma inner
reindexing. -/
theorem rightCommaReindexInner_δ_zero (F : C ⥤ D) (n : ℕ)
    (s : ComposableArrows D (n + 1))
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj s.left).obj (op ⦋n + 1⦌)) :
    (SrepBridge.srepFaceZeroComponent
      (rightCommaNerveDiagram.{max u w, max v w, u} F) s).app (op ⦋n⦌)
        (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj s.left).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op X) =
      rightCommaReindexInner F s X
        (rightCommaSimplexReindexFunctorHom
          (SimplexCategory.δ (0 : Fin (n + 2)))) := by
  have hCoeff :
      SrepBridge.srepFaceZeroComponent
          (rightCommaNerveDiagram.{max u w, max v w, u} F) s =
        (rightCommaNerveDiagram.{max u w, max v w, u} F).map
          (rightCommaReindexBase s
            (rightCommaSimplexReindexFunctorHom
              (SimplexCategory.δ (0 : Fin (n + 2))))) := by
    unfold SrepBridge.srepFaceZeroComponent
    rw [eqToHom_refl, Category.id_comp]
    have hMap := congrArg (rightCommaNerveDiagram.{max u w, max v w, u} F).map
      (rightCommaReindexBase_δ_zero n s)
    rw [Functor.map_comp, eqToHom_map] at hMap
    exact hMap
  rw [hCoeff]
  exact rightCommaNerveDiagram_map_reindex_apply F
    (SimplexCategory.δ (0 : Fin (n + 2))) s X

/-- The interior-face coefficient formula is the explicit right-comma inner
reindexing. -/
theorem rightCommaReindexInner_δ_inner (F : C ⥤ D) (n : ℕ)
    (i : Fin (n + 2)) (hi₀ : i ≠ 0)
    (s : ComposableArrows D (n + 1))
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj s.left).obj (op ⦋n + 1⦌)) :
    (StrictOrdinaryWeightedBar.wFaceInnerComponent
      (rightCommaNerveDiagram.{max u w, max v w, u} F) i hi₀ s).app (op ⦋n⦌)
        (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj s.left).map
          (SimplexCategory.δ i).op X) =
      rightCommaReindexInner F s X
        (rightCommaSimplexReindexFunctorHom (SimplexCategory.δ i)) := by
  have hZero : (StrictOmitDup.omitFinFunctor n i).obj 0 = 0 :=
    Fin.succAbove_ne_zero_zero hi₀
  have hCoeff :
      StrictOrdinaryWeightedBar.wFaceInnerComponent
          (rightCommaNerveDiagram.{max u w, max v w, u} F) i hi₀ s =
        (rightCommaNerveDiagram.{max u w, max v w, u} F).map
          (eqToHom (congrArg s.obj hZero.symm)) := by
    unfold StrictOrdinaryWeightedBar.wFaceInnerComponent
    rw [eqToHom_map]
    exact congrArg eqToHom (Subsingleton.elim _ _)
  rw [hCoeff]
  have hReindex := rightCommaNerveDiagram_map_reindex_apply F
    (SimplexCategory.δ i) s X
  rw [rightCommaSimplexReindexFunctorHom_δ] at hReindex
  rw [rightCommaReindexBase_eq_eqToHom_of_obj_zero s
    (StrictOmitDup.omitFinFunctor n i) hZero] at hReindex
  exact hReindex

/-- The degeneracy coefficient formula is the explicit right-comma inner
reindexing. -/
theorem rightCommaReindexInner_σ (F : C ⥤ D) (n : ℕ)
    (i : Fin (n + 1)) (s : ComposableArrows D n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj s.left).obj (op ⦋n⦌)) :
    (StrictOrdinaryWeightedBar.wDegInnerComponent
      (rightCommaNerveDiagram.{max u w, max v w, u} F) i s).app (op ⦋n + 1⦌)
        (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj s.left).map
          (SimplexCategory.σ i).op X) =
      rightCommaReindexInner F s X
        (rightCommaSimplexReindexFunctorHom (SimplexCategory.σ i)) := by
  have hZero : (StrictOmitDup.dupFinFunctor n i).obj 0 = 0 := by
    change i.predAbove 0 = 0
    exact Fin.predAbove_right_zero
  have hCoeff :
      StrictOrdinaryWeightedBar.wDegInnerComponent
          (rightCommaNerveDiagram.{max u w, max v w, u} F) i s =
        (rightCommaNerveDiagram.{max u w, max v w, u} F).map
          (eqToHom (congrArg s.obj hZero.symm)) := by
    unfold StrictOrdinaryWeightedBar.wDegInnerComponent
    rw [eqToHom_map]
    exact congrArg eqToHom (Subsingleton.elim _ _)
  rw [hCoeff]
  have hReindex := rightCommaNerveDiagram_map_reindex_apply F
    (SimplexCategory.σ i) s X
  rw [rightCommaSimplexReindexFunctorHom_σ] at hReindex
  rw [rightCommaReindexBase_eq_eqToHom_of_obj_zero s
    (StrictOmitDup.dupFinFunctor n i) hZero] at hReindex
  exact hReindex

/-- Decode a reindexed weighted inclusion from its explicit outer
weighted-bar inclusion square.  The inner simplicial map is applied first,
then the outer coefficient map. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι_of
    (F : C ⥤ D) {m n : ℕ} (k : op ⦋n⦌ ⟶ op ⦋m⦌)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (p' : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) m)
    (c : (rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left ⟶
      (rightCommaNerveDiagram.{max u w, max v w, u} F).obj p'.1.left)
    (hOuter : StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p ≫
          (StrictOrdinaryWeightedBar.wbarSimplicial
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F)).map k =
      c ≫ StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) m p')
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌)) :
    (rightCommaTotalDegreeSigmaIso F m).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map k
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
              (op ⦋n⦌) X)) =
      ⟨p', c.app (op ⦋m⦌)
        (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map k X)⟩ := by
  have hInner := ConcreteCategory.congr_hom
    ((StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).naturality k) X
  have hOuterApp := congr_app hOuter (op ⦋m⦌)
  have hOuterValue := ConcreteCategory.congr_hom hOuterApp
    (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map k X)
  have hMap :
      (bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map k
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
              (op ⦋n⦌) X) =
        (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) m p').app
            (op ⦋m⦌)
              (c.app (op ⦋m⦌)
                (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map k X)) := by
    unfold bkHocolim
    rw [simplicialDiagonalFunctor_obj_map]
    change ((StrictOrdinaryWeightedBar.wbarSimplicial
        (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F)).map k).app
          (op ⦋m⦌)
        (((StrictOrdinaryWeightedBar.wbarObj
          (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n).map k)
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
                (op ⦋n⦌) X)) = _
    have hInner' :
        ((StrictOrdinaryWeightedBar.wbarObj
          (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n).map k)
            ((StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
                (op ⦋n⦌) X) =
          (StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
              (op ⦋m⦌)
                (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map k X) :=
      hInner.symm
    rw [hInner']
    exact hOuterValue
  rw [hMap]
  have hDecode := ConcreteCategory.congr_hom
    (rightCommaTotalDegreeSigmaIso_hom_ι F m p')
      (c.app (op ⦋m⦌)
        (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map k X))
  change (rightCommaTotalDegreeSigmaIso F m).hom
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) m p').app
          (op ⦋m⦌)
            (c.app (op ⦋m⦌)
              (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map k X))) =
      _ at hDecode
  exact hDecode

/-- Decoder formula for the zeroth face on a weighted summand. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι_d0
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) (n + 1))
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    (rightCommaTotalDegreeSigmaIso F n).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) (n + 1) p).app
              (op ⦋n + 1⦌) X)) =
      ⟨StrictOrdinaryWeightedBar.wFaceZeroIdx
          (CategoryBar.replUnit D) n p,
        (SrepBridge.srepFaceZeroComponent (rightCommaNerveDiagram.{max u w, max v w, u} F) p.1).app
          (op ⦋n⦌)
            (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map
              (SimplexCategory.δ (0 : Fin (n + 2))).op X)⟩ := by
  apply rightCommaTotalDegreeSigmaIso_map_ι_of F
  rw [StrictOrdinaryWeightedBar.wbarSimplicial_map_δ,
    StrictOrdinaryWeightedBar.wbarδ_zero]
  exact StrictOrdinaryWeightedBar.wbarFaceZero_ι
    (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p

/-- Decoder formula for the last face on a weighted summand. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι_dLast
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) (n + 1))
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    (rightCommaTotalDegreeSigmaIso F n).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map
          (SimplexCategory.δ (Fin.last (n + 1))).op
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) (n + 1) p).app
              (op ⦋n + 1⦌) X)) =
      ⟨StrictOrdinaryWeightedBar.wFaceLastIdx
          (CategoryBar.replUnit D) n p,
        (SrepBridge.srepFaceLastComponent (rightCommaNerveDiagram.{max u w, max v w, u} F) p.1).app
          (op ⦋n⦌)
            (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map
              (SimplexCategory.δ (Fin.last (n + 1))).op X)⟩ := by
  apply rightCommaTotalDegreeSigmaIso_map_ι_of F
  rw [StrictOrdinaryWeightedBar.wbarSimplicial_map_δ,
    StrictOrdinaryWeightedBar.wbarδ_last]
  exact StrictOrdinaryWeightedBar.wbarFaceLast_ι
    (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p

/-- Decoder formula for an interior face on a weighted summand. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι_dInterior
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 2))
    (hi0 : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) (n + 1))
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    (rightCommaTotalDegreeSigmaIso F n).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map
          (SimplexCategory.δ i).op
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) (n + 1) p).app
              (op ⦋n + 1⦌) X)) =
      ⟨StrictOrdinaryWeightedBar.wFaceInnerIdx
          (CategoryBar.replUnit D) n i hiLast p,
        (StrictOrdinaryWeightedBar.wFaceInnerComponent
          (rightCommaNerveDiagram.{max u w, max v w, u} F) i hi0 p.1).app (op ⦋n⦌)
            (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map
              (SimplexCategory.δ i).op X)⟩ := by
  apply rightCommaTotalDegreeSigmaIso_map_ι_of F
  rw [StrictOrdinaryWeightedBar.wbarSimplicial_map_δ,
    StrictOrdinaryWeightedBar.wbarδ_inner _ _ _ _ hi0 hiLast]
  exact StrictOrdinaryWeightedBar.wbarFaceInner_ι
    (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n i hi0 hiLast p

/-- Decoder formula for a degeneracy on a weighted summand. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι_s
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌)) :
    (rightCommaTotalDegreeSigmaIso F (n + 1)).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map
          (SimplexCategory.σ i).op
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
              (op ⦋n⦌) X)) =
      ⟨StrictOrdinaryWeightedBar.wDegInnerIdx
          (CategoryBar.replUnit D) n i p,
        (StrictOrdinaryWeightedBar.wDegInnerComponent
          (rightCommaNerveDiagram.{max u w, max v w, u} F) i p.1).app (op ⦋n + 1⦌)
            (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map
              (SimplexCategory.σ i).op X)⟩ := by
  apply rightCommaTotalDegreeSigmaIso_map_ι_of F
  rw [StrictOrdinaryWeightedBar.wbarSimplicial_map_σ]
  exact StrictOrdinaryWeightedBar.wbarσ_ι
    (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n i p

/-- Zeroth-face decoder formula in the uniform outer/inner reindexing
coordinates. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι_δ_zero_reindex
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) (n + 1))
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    (rightCommaTotalDegreeSigmaIso F n).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map
          (SimplexCategory.δ (0 : Fin (n + 2))).op
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) (n + 1) p).app
              (op ⦋n + 1⦌) X)) =
      ⟨rightCommaWIdxReindex p
          (rightCommaSimplexReindexFunctorHom
            (SimplexCategory.δ (0 : Fin (n + 2)))),
        rightCommaReindexInner F p.1 X
          (rightCommaSimplexReindexFunctorHom
            (SimplexCategory.δ (0 : Fin (n + 2))))⟩ := by
  rw [rightCommaTotalDegreeSigmaIso_map_ι_d0]
  refine Sigma.ext (rightCommaWIdxReindex_δ_zero n p).symm ?_
  exact heq_of_eq (rightCommaReindexInner_δ_zero F n p.1 X)

/-- Interior-face decoder formula in the uniform outer/inner reindexing
coordinates. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι_δ_inner_reindex
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 2))
    (hi₀ : i ≠ 0) (hiLast : i ≠ Fin.last (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) (n + 1))
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    (rightCommaTotalDegreeSigmaIso F n).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map
          (SimplexCategory.δ i).op
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) (n + 1) p).app
              (op ⦋n + 1⦌) X)) =
      ⟨rightCommaWIdxReindex p
          (rightCommaSimplexReindexFunctorHom (SimplexCategory.δ i)),
        rightCommaReindexInner F p.1 X
          (rightCommaSimplexReindexFunctorHom (SimplexCategory.δ i))⟩ := by
  rw [rightCommaTotalDegreeSigmaIso_map_ι_dInterior F n i hi₀ hiLast p X]
  refine Sigma.ext (rightCommaWIdxReindex_δ_inner n i hiLast p).symm ?_
  exact heq_of_eq (rightCommaReindexInner_δ_inner F n i hi₀ p.1 X)

/-- Last-face decoder formula in the uniform outer/inner reindexing
coordinates. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι_δ_last_reindex
    (F : C ⥤ D) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) (n + 1))
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    (rightCommaTotalDegreeSigmaIso F n).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map
          (SimplexCategory.δ (Fin.last (n + 1))).op
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) (n + 1) p).app
              (op ⦋n + 1⦌) X)) =
      ⟨rightCommaWIdxReindex p
          (rightCommaSimplexReindexFunctorHom
            (SimplexCategory.δ (Fin.last (n + 1)))),
        rightCommaReindexInner F p.1 X
          (rightCommaSimplexReindexFunctorHom
            (SimplexCategory.δ (Fin.last (n + 1))))⟩ := by
  rw [rightCommaTotalDegreeSigmaIso_map_ι_dLast F n p X]
  refine Sigma.ext (rightCommaWIdxReindex_δ_last n p).symm ?_
  have hi₀ : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 :=
    ne_of_gt (Fin.last_pos' (n := n + 1))
  have hBridge :
      (SrepBridge.srepFaceLastComponent
        (rightCommaNerveDiagram.{max u w, max v w, u} F) p.1).app (op ⦋n⦌)
          (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map
            (SimplexCategory.δ (Fin.last (n + 1))).op X) ≍
        (StrictOrdinaryWeightedBar.wFaceInnerComponent
          (rightCommaNerveDiagram.{max u w, max v w, u} F) (Fin.last (n + 1)) hi₀ p.1).app
            (op ⦋n⦌)
              (((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).map
                (SimplexCategory.δ (Fin.last (n + 1))).op X) := by
    unfold SrepBridge.srepFaceLastComponent
      StrictOrdinaryWeightedBar.wFaceInnerComponent
    apply heq_of_eq
    congr 1
  exact hBridge.trans (heq_of_eq
    (rightCommaReindexInner_δ_inner F n (Fin.last (n + 1)) hi₀ p.1 X))

/-- Every face generator has the uniform outer/inner reindexing decoder
formula. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι_δ_reindex
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 2))
    (p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) (n + 1))
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n + 1⦌)) :
    (rightCommaTotalDegreeSigmaIso F n).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map
          (SimplexCategory.δ i).op
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) (n + 1) p).app
              (op ⦋n + 1⦌) X)) =
      rightCommaTotalReindexPair F p X
        (rightCommaSimplexReindexFunctorHom (SimplexCategory.δ i)) := by
  by_cases hi₀ : i = 0
  · subst i
    exact rightCommaTotalDegreeSigmaIso_map_ι_δ_zero_reindex F n p X
  by_cases hiLast : i = Fin.last (n + 1)
  · subst i
    exact rightCommaTotalDegreeSigmaIso_map_ι_δ_last_reindex F n p X
  exact rightCommaTotalDegreeSigmaIso_map_ι_δ_inner_reindex
    F n i hi₀ hiLast p X

/-- Degeneracy decoder formula in the uniform outer/inner reindexing
coordinates. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι_σ_reindex
    (F : C ⥤ D) (n : ℕ) (i : Fin (n + 1))
    (p : StrictOrdinaryWeightedBar.WIdx D
      (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌)) :
    (rightCommaTotalDegreeSigmaIso F (n + 1)).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map
          (SimplexCategory.σ i).op
          ((StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit D) (rightCommaNerveDiagram.{max u w, max v w, u} F) n p).app
              (op ⦋n⦌) X)) =
      ⟨rightCommaWIdxReindex p
          (rightCommaSimplexReindexFunctorHom (SimplexCategory.σ i)),
        rightCommaReindexInner F p.1 X
          (rightCommaSimplexReindexFunctorHom (SimplexCategory.σ i))⟩ := by
  rw [rightCommaTotalDegreeSigmaIso_map_ι_s F n i p X]
  refine Sigma.ext (rightCommaWIdxReindex_σ n i p).symm ?_
  exact heq_of_eq (rightCommaReindexInner_σ F n i p.1 X)

/-- The decoder formula for a fixed ordinary simplex-category morphism. -/
private def rightCommaSimplexDecoderProp (F : C ⥤ D) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) : Prop :=
  ∀ (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌)),
    (rightCommaTotalDegreeSigmaIso F m).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map f.op
          (rightCommaBKIncl F n p X)) =
      rightCommaTotalReindexPair F p X
        (rightCommaSimplexReindexFunctorHom f)

/-- Equality after decoding can be reflected back to the underlying BK
carrier because the degree decoder is an isomorphism. -/
private theorem rightCommaCarrier_eq_of_decoder_eq (F : C ⥤ D)
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌))
    (q : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) m)
    (Y : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj q.1.left).obj (op ⦋m⦌))
    (h : (rightCommaTotalDegreeSigmaIso F m).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map f.op
          (rightCommaBKIncl F n p X)) = ⟨q, Y⟩) :
    (bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map f.op
        (rightCommaBKIncl F n p X) =
      rightCommaBKIncl F m q Y := by
  apply (rightCommaTotalDegreeSigmaIso F m).toEquiv.injective
  change (rightCommaTotalDegreeSigmaIso F m).hom
      ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map f.op
        (rightCommaBKIncl F n p X)) =
    (rightCommaTotalDegreeSigmaIso F m).hom
      (rightCommaBKIncl F m q Y)
  rw [h]
  have hIncl := ConcreteCategory.congr_hom
    (rightCommaTotalDegreeSigmaIso_hom_ι F m q) Y
  change (rightCommaTotalDegreeSigmaIso F m).hom
      (rightCommaBKIncl F m q Y) = ⟨q, Y⟩ at hIncl
  exact hIncl.symm

private theorem rightCommaSimplexDecoderProp_id (F : C ⥤ D) (n : ℕ) :
    rightCommaSimplexDecoderProp F (𝟙 ⦋n⦌) := by
  intro p X
  have hId : (𝟙 ⦋n⦌).op = 𝟙 (op ⦋n⦌) := rfl
  rw [hId, (bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map_id]
  change (rightCommaTotalDegreeSigmaIso F n).hom
      (rightCommaBKIncl F n p X) =
    rightCommaTotalReindexPair F p X
      (rightCommaSimplexReindexFunctorHom (𝟙 ⦋n⦌))
  have hDecode := ConcreteCategory.congr_hom
    (rightCommaTotalDegreeSigmaIso_hom_ι F n p) X
  change (rightCommaTotalDegreeSigmaIso F n).hom
      (rightCommaBKIncl F n p X) = ⟨p, X⟩ at hDecode
  calc
    _ = ⟨p, X⟩ := hDecode
    _ = rightCommaTotalReindexPair F p X
        (rightCommaSimplexReindexFunctorHom (𝟙 ⦋n⦌)) := by
      rw [rightCommaSimplexReindexFunctorHom_id]
      exact (rightCommaTotalReindexPair_id F p X).symm

/-- Decoder formulas compose in the opposite simplicial order: the right
factor acts on the simplex first. -/
private theorem rightCommaSimplexDecoderProp_comp (F : C ⥤ D)
    {l m n : ℕ} (f : ⦋l⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : rightCommaSimplexDecoderProp F f)
    (hg : rightCommaSimplexDecoderProp F g) :
    rightCommaSimplexDecoderProp F (f ≫ g) := by
  intro p X
  let Φg := rightCommaSimplexReindexFunctorHom g
  let Φf := rightCommaSimplexReindexFunctorHom f
  let pg := rightCommaWIdxReindex p Φg
  let Xg := rightCommaReindexInner F p.1 X Φg
  have hDecodeG := hg p X
  have hCarrierG :
      (bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map g.op
          (rightCommaBKIncl F n p X) =
        rightCommaBKIncl F m pg Xg :=
    rightCommaCarrier_eq_of_decoder_eq F g p X pg Xg hDecodeG
  rw [op_comp, (bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map_comp,
    ConcreteCategory.comp_apply, hCarrierG]
  calc
    _ = rightCommaTotalReindexPair F pg Xg Φf := hf pg Xg
    _ = rightCommaTotalReindexPair F p X (Φf ⋙ Φg) :=
      rightCommaTotalReindexPair_comp F p X Φg Φf
    _ = rightCommaTotalReindexPair F p X
        (rightCommaSimplexReindexFunctorHom (f ≫ g)) := by
      rw [rightCommaSimplexReindexFunctorHom_comp]

private theorem rightCommaSimplexDecoderProp_δ (F : C ⥤ D)
    (n : ℕ) (i : Fin (n + 2)) :
    rightCommaSimplexDecoderProp F (SimplexCategory.δ i) := by
  intro p X
  rw [rightCommaBKIncl_apply]
  exact rightCommaTotalDegreeSigmaIso_map_ι_δ_reindex F n i p X

private theorem rightCommaSimplexDecoderProp_σ (F : C ⥤ D)
    (n : ℕ) (i : Fin (n + 1)) :
    rightCommaSimplexDecoderProp F (SimplexCategory.σ i) := by
  intro p X
  rw [rightCommaBKIncl_apply]
  exact rightCommaTotalDegreeSigmaIso_map_ι_σ_reindex F n i p X

/-- GenRel form of the arbitrary decoder formula.  `hom_induction` operates
on the quotient category itself, so all six simplex relations are respected
by construction rather than reproved on free paths. -/
private def rightCommaGenRelDecoderProp (F : C ⥤ D) :
    CategoryTheory.MorphismProperty SimplexCategoryGenRel :=
  fun {_a _b} g => rightCommaSimplexDecoderProp F
    (SimplexCategoryGenRel.toSimplexCategory.map g)

private theorem rightCommaGenRelDecoder (F : C ⥤ D)
    {a b : SimplexCategoryGenRel} (g : a ⟶ b) :
    rightCommaGenRelDecoderProp F g := by
  refine SimplexCategoryGenRel.hom_induction
    (rightCommaGenRelDecoderProp F)
    (fun {n} => ?_) (fun u i ih => ?_) (fun u i ih => ?_) g
  · change rightCommaSimplexDecoderProp F
      (SimplexCategoryGenRel.toSimplexCategory.map
        (𝟙 (SimplexCategoryGenRel.mk n)))
    rw [SimplexCategoryGenRel.toSimplexCategory.map_id]
    exact rightCommaSimplexDecoderProp_id F n
  · change rightCommaSimplexDecoderProp F
      (SimplexCategoryGenRel.toSimplexCategory.map
        (u ≫ SimplexCategoryGenRel.δ i))
    rw [SimplexCategoryGenRel.toSimplexCategory.map_comp,
      SimplexCategoryGenRel.toSimplexCategory_map_δ]
    exact rightCommaSimplexDecoderProp_comp F _ _ ih
      (rightCommaSimplexDecoderProp_δ F _ i)
  · change rightCommaSimplexDecoderProp F
      (SimplexCategoryGenRel.toSimplexCategory.map
        (u ≫ SimplexCategoryGenRel.σ i))
    rw [SimplexCategoryGenRel.toSimplexCategory.map_comp,
      SimplexCategoryGenRel.toSimplexCategory_map_σ]
    exact rightCommaSimplexDecoderProp_comp F _ _ ih
      (rightCommaSimplexDecoderProp_σ F _ i)

/-- Arbitrary simplex-morphism decoder formula on a weighted summand. -/
theorem rightCommaTotalDegreeSigmaIso_map_ι
    (F : C ⥤ D) {m n : ℕ} (k : op ⦋n⦌ ⟶ op ⦋m⦌)
    (p : StrictOrdinaryWeightedBar.WIdx D (CategoryBar.replUnit D) n)
    (X : ((rightCommaNerveDiagram.{max u w, max v w, u} F).obj p.1.left).obj (op ⦋n⦌)) :
    (rightCommaTotalDegreeSigmaIso F m).hom
        ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map k
          (rightCommaBKIncl F n p X)) =
      ⟨rightCommaWIdxReindex p (rightCommaSimplexReindexFunctor k),
        rightCommaReindexInner F p.1 X
          (rightCommaSimplexReindexFunctor k)⟩ := by
  let g := SimplexCategoryGenRel.fromSimplexCategory.map k.unop
  have hGen := rightCommaGenRelDecoder F g
  change rightCommaSimplexDecoderProp F
    (SimplexCategoryGenRel.toSimplexCategory.map g) at hGen
  have hPre : SimplexCategoryGenRel.toSimplexCategory.map g = k.unop := by
    rw [SimplexCategoryGenRel.fromSimplexCategory_map_preimage]
  have hk : rightCommaSimplexDecoderProp F k.unop := hPre ▸ hGen
  have h := hk p X
  change (rightCommaTotalDegreeSigmaIso F m).hom
      ((bkHocolim (rightCommaNerveDiagram.{max u w, max v w, u} F)).map k
        (rightCommaBKIncl F n p X)) =
    rightCommaTotalReindexPair F p X
      (rightCommaSimplexReindexFunctor k)
  simpa only [Quiver.Hom.op_unop] using h

end SSet

end
