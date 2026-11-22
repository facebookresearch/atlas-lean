/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.SubdiagramChainColimits
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalCellReplacementAccessibility

/-!
# The final-rho comparison for the same original replacement

Actual original union colimits and preservation at the designated final
regular cardinal construct both strict comparison maps. Their two mixed
triangles give one whole Arrow isomorphism, with both original leg and
ambient equations. All original sites, coefficients and maps are retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits
open SimplicialPresheaf.KanWeakInterpolation

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]
  (S : I → Arrow (SimplicialPresheaf.{u} D))
  (ρ : Cardinal.{u}) [Fact ρ.IsRegular]
  (hκ : (originalLocalCellData S).κ ≤ ρ)
  [IsCardinalFiltered ρ.ord.ToType ρ]
  {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) (γ : Cardinal.{u})
  (a : ρ.ord.ToType → cardinalSubarrowIndex f γ) (ha : Monotone a)


/-- The SAME original R preserves the constructed A union at the actual final rho. -/
def originalLocalLadderRUnionIsColimit :
    IsColimit ((originalLocalCellReplacement S).mapArrow.mapCocone
      (cardinalSubarrowChainCocone f γ a ha)) :=
  originalLocalCellReplacementPreservesArrowCocone S ρ hκ (cardinalSubarrowChainCocone f γ a ha)
    (cardinalSubarrowChainIsColimit f γ a ha)

variable (b : ρ.ord.ToType → cardinalSubarrowIndex (((originalLocalCellReplacement S)).map f) γ)
    (hb : Monotone b)
  (p : (ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
      ((originalLocalCellReplacement S)).mapArrow ⟶ hb.functor ⋙
      cardinalSubarrowDiagram (((originalLocalCellReplacement S)).map f) γ)
  (q : hb.functor ⋙ cardinalSubarrowDiagram (((originalLocalCellReplacement S)).map f) γ ⟶
    ((Order.succ_mono : Monotone (fun α : ρ.ord.ToType => Order.succ α)).functor) ⋙
        (ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
        ((originalLocalCellReplacement S)).mapArrow)


private def forwardDestination :
    Cocone ((ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
      (originalLocalCellReplacement S).mapArrow) where
  pt := (cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb).pt
  ι :=
    { app α := p.app α ≫
        (cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb).ι.app α
      naturality := by
        intro α β h
        have hc :
            (hb.functor ⋙ cardinalSubarrowDiagram
              ((originalLocalCellReplacement S).map f) γ).map h ≫
            (cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb).ι.app β =
          (cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b
              hb).ι.app α ≫ 𝟙 _ :=
          (cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b
              hb).ι.naturality h
        calc
          _ = (((ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
                (originalLocalCellReplacement S).mapArrow).map h ≫ p.app β) ≫
                  (cardinalSubarrowChainCocone
                      ((originalLocalCellReplacement S).map f) γ b hb).ι.app β :=
            (CategoryTheory.Category.assoc _ _ _).symm
          _ = (p.app α ≫ (hb.functor ⋙ cardinalSubarrowDiagram
                ((originalLocalCellReplacement S).map f) γ).map h) ≫
                  (cardinalSubarrowChainCocone
                      ((originalLocalCellReplacement S).map f) γ b hb).ι.app β :=
            congrArg (fun m => m ≫
              (cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb).ι.app β)
                (p.naturality h)
          _ = p.app α ≫ ((hb.functor ⋙ cardinalSubarrowDiagram
                ((originalLocalCellReplacement S).map f) γ).map h ≫
                  (cardinalSubarrowChainCocone
                      ((originalLocalCellReplacement S).map f) γ b hb).ι.app β) :=
            CategoryTheory.Category.assoc _ _ _
          _ = p.app α ≫ ((cardinalSubarrowChainCocone
                ((originalLocalCellReplacement S).map f) γ b hb).ι.app α ≫ 𝟙 _) :=
            congrArg (fun m => p.app α ≫ m) hc
          _ = (p.app α ≫ (cardinalSubarrowChainCocone
                ((originalLocalCellReplacement S).map f) γ b hb).ι.app α) ≫ 𝟙 _ :=
            (CategoryTheory.Category.assoc _ _ _).symm }

private def inverseDestination :
    Cocone (hb.functor ⋙ cardinalSubarrowDiagram ((originalLocalCellReplacement S).map f) γ) where
  pt := ((originalLocalCellReplacement S).mapArrow.mapCocone
    (cardinalSubarrowChainCocone f γ a ha)).pt
  ι :=
    { app α := q.app α ≫ ((originalLocalCellReplacement S).mapArrow.mapCocone
        (cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ α)
      naturality := by
        intro α β h
        let σ : ρ.ord.ToType ⥤ ρ.ord.ToType :=
          (Order.succ_mono : Monotone (fun α : ρ.ord.ToType => Order.succ α)).functor
        have hc : ((ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
              (originalLocalCellReplacement S).mapArrow).map (σ.map h) ≫
                ((originalLocalCellReplacement S).mapArrow.mapCocone
                  (cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ β) =
            ((originalLocalCellReplacement S).mapArrow.mapCocone
              (cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ α) ≫ 𝟙 _ :=
          ((originalLocalCellReplacement S).mapArrow.mapCocone
            (cardinalSubarrowChainCocone f γ a ha)).ι.naturality (σ.map h)
        calc
          _ = ((hb.functor ⋙ cardinalSubarrowDiagram
                ((originalLocalCellReplacement S).map f) γ).map h ≫ q.app β) ≫
                  ((originalLocalCellReplacement S).mapArrow.mapCocone
                    (cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ β) :=
            (CategoryTheory.Category.assoc _ _ _).symm
          _ = (q.app α ≫ ((ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
                (originalLocalCellReplacement S).mapArrow).map (σ.map h)) ≫
                  ((originalLocalCellReplacement S).mapArrow.mapCocone
                    (cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ β) :=
            congrArg (fun m => m ≫ ((originalLocalCellReplacement S).mapArrow.mapCocone
              (cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ β)) (q.naturality h)
          _ = q.app α ≫ (((ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
                (originalLocalCellReplacement S).mapArrow).map (σ.map h) ≫
                  ((originalLocalCellReplacement S).mapArrow.mapCocone
                    (cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ β)) :=
            CategoryTheory.Category.assoc _ _ _
          _ = q.app α ≫ (((originalLocalCellReplacement S).mapArrow.mapCocone
                (cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ α) ≫ 𝟙 _) :=
            congrArg (fun m => q.app α ≫ m) hc
          _ = (q.app α ≫ ((originalLocalCellReplacement S).mapArrow.mapCocone
                (cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ α)) ≫ 𝟙 _ :=
            (CategoryTheory.Category.assoc _ _ _).symm }

private def forwardComparison :
    (((originalLocalCellReplacement S).mapArrow.mapCocone
      (cardinalSubarrowChainCocone f γ a ha))).pt ⟶
      ((cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb)).pt :=
  (originalLocalLadderRUnionIsColimit S ρ hκ f γ a ha).desc
    (forwardDestination S ρ f γ a ha b hb p)

private def inverseComparison :
    ((cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb)).pt ⟶
    (((originalLocalCellReplacement S).mapArrow.mapCocone
      (cardinalSubarrowChainCocone f γ a ha))).pt :=
  (cardinalSubarrowChainIsColimit (((originalLocalCellReplacement S)).map f) γ b hb).desc
    (inverseDestination S ρ f γ a ha b hb q)

private theorem forwardComparison_leg (α : ρ.ord.ToType) :
    (((originalLocalCellReplacement S).mapArrow.mapCocone
        (cardinalSubarrowChainCocone f γ a ha))).ι.app α ≫
        forwardComparison S ρ hκ f γ a ha b hb p =
      p.app α ≫
          ((cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b
            hb)).ι.app α :=
  (originalLocalLadderRUnionIsColimit S ρ hκ f γ a ha).fac
    (forwardDestination S ρ f γ a ha b hb p) α

omit [Fact ρ.IsRegular] [IsCardinalFiltered ρ.ord.ToType ρ] in
private theorem inverseComparison_leg (α : ρ.ord.ToType) :
    ((cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb)).ι.app α ≫
        inverseComparison S ρ f γ a ha b hb q =
      q.app α ≫
          (((originalLocalCellReplacement S).mapArrow.mapCocone
            (cardinalSubarrowChainCocone f γ a ha))).ι.app (Order.succ α) :=
  (cardinalSubarrowChainIsColimit (((originalLocalCellReplacement S)).map f) γ b hb).fac
    (inverseDestination S ρ f γ a ha b hb q) α

variable
  (hPQ : ∀ α : ρ.ord.ToType,
      p.app α ≫ q.app α =
      (((ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
        (originalLocalCellReplacement S).mapArrow)).map (homOfLE (Order.le_succ α)))
  (hQP : ∀ α : ρ.ord.ToType,
      q.app α ≫ p.app (Order.succ α) =
      ((hb.functor ⋙ cardinalSubarrowDiagram ((originalLocalCellReplacement S).map f) γ)).map
      (homOfLE (Order.le_succ α)))

include hPQ in
private theorem comparison_hom_inv :
    forwardComparison S ρ hκ f γ a ha b hb p ≫
        inverseComparison S ρ f γ a ha b hb q =
            𝟙
            (((originalLocalCellReplacement S).mapArrow.mapCocone
              (cardinalSubarrowChainCocone f γ a ha))).pt := by
  apply (originalLocalLadderRUnionIsColimit S ρ hκ f γ a ha).hom_ext
  intro α
  rw [← Category.assoc, forwardComparison_leg, Category.assoc,
    inverseComparison_leg, ← Category.assoc, hPQ, Category.comp_id]
  have hn : ((ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
        (originalLocalCellReplacement S).mapArrow).map (homOfLE (Order.le_succ α)) ≫
          ((originalLocalCellReplacement S).mapArrow.mapCocone
            (cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ α) =
      ((originalLocalCellReplacement S).mapArrow.mapCocone
        (cardinalSubarrowChainCocone f γ a ha)).ι.app α ≫ 𝟙 _ :=
    ((originalLocalCellReplacement S).mapArrow.mapCocone
      (cardinalSubarrowChainCocone f γ a ha)).ι.naturality (homOfLE (Order.le_succ α))
  exact hn.trans (CategoryTheory.Category.comp_id _)

include hQP in
private theorem comparison_inv_hom :
    inverseComparison S ρ f γ a ha b hb q ≫
        forwardComparison S ρ hκ f γ a ha b hb p =
            𝟙
            ((cardinalSubarrowChainCocone
              ((originalLocalCellReplacement S).map f) γ b hb)).pt := by
  apply (cardinalSubarrowChainIsColimit (((originalLocalCellReplacement S)).map f) γ b hb).hom_ext
  intro α
  rw [← Category.assoc, inverseComparison_leg, Category.assoc,
    forwardComparison_leg, ← Category.assoc, hQP, Category.comp_id]
  have hn : (hb.functor ⋙ cardinalSubarrowDiagram
        ((originalLocalCellReplacement S).map f) γ).map (homOfLE (Order.le_succ α)) ≫
          (cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb).ι.app
            (Order.succ α) =
      (cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb).ι.app α ≫ 𝟙 _ :=
    (cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb).ι.naturality
      (homOfLE (Order.le_succ α))
  exact hn.trans (CategoryTheory.Category.comp_id _)

private def comparisonIso :
    (((originalLocalCellReplacement S).mapArrow.mapCocone
      (cardinalSubarrowChainCocone f γ a ha))).pt ≅
      ((cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb)).pt where
  hom := forwardComparison S ρ hκ f γ a ha b hb p
  inv := inverseComparison S ρ f γ a ha b hb q
  hom_inv_id := comparison_hom_inv S ρ hκ f γ a ha b hb p q hPQ
  inv_hom_id := comparison_inv_hom S ρ hκ f γ a ha b hb p q hQP

/-- Both actual descendants and mixed triangles give one whole original Arrow Iso. -/
def originalLocalLadderColimitIso :
    ((originalLocalCellReplacement S)).mapArrow.obj
        (Subdiagram.arrow f (Subdiagram.indexedUnion f (fun α => (a α).val))) ≅
      Subdiagram.arrow (((originalLocalCellReplacement S)).map f)
          (Subdiagram.indexedUnion (((originalLocalCellReplacement S)).map f)
            (fun α => (b α).val)) :=
  comparisonIso S ρ hκ f γ a ha b hb p q hPQ hQP

/-- Every original A leg followed by the comparison is its supplied p leg into Binf. -/
theorem originalLocalLadderColimitIso_hom_leg (α : ρ.ord.ToType) :
    ((originalLocalCellReplacement S)).mapArrow.map
        (((cardinalSubarrowChainCocone f γ a ha)).ι.app α) ≫
        (originalLocalLadderColimitIso S ρ hκ f γ a ha b hb p q hPQ hQP).hom =
      p.app α ≫
          ((cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b
            hb)).ι.app α :=
  forwardComparison_leg S ρ hκ f γ a ha b hb p α

/-- Every original B leg followed by the inverse comparison is its q successor leg. -/
theorem originalLocalLadderColimitIso_inv_leg (α : ρ.ord.ToType) :
    ((cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb)).ι.app α ≫
        (originalLocalLadderColimitIso S ρ hκ f γ a ha b hb p q hPQ hQP).inv =
      q.app α ≫ ((originalLocalCellReplacement S)).mapArrow.map
          (((cardinalSubarrowChainCocone f γ a ha)).ι.app (Order.succ α)) :=
  inverseComparison_leg S ρ f γ a ha b hb q α

omit [Fact ρ.IsRegular] [IsCardinalFiltered ρ.ord.ToType ρ] in
private theorem mapped_union_inclusion (α : ρ.ord.ToType) :
    (((originalLocalCellReplacement S).mapArrow.mapCocone
        (cardinalSubarrowChainCocone f γ a ha))).ι.app α ≫
        ((originalLocalCellReplacement S)).mapArrow.map
        (Subdiagram.inclusion f (Subdiagram.indexedUnion f (fun β => (a β).val))) =
      ((originalLocalCellReplacement S)).mapArrow.map (Subdiagram.inclusion f (a α).val) := by
  change ((originalLocalCellReplacement S)).mapArrow.map (Subdiagram.map f
      (Subdiagram.le_indexedUnion f (fun β => (a β).val) α)) ≫
        ((originalLocalCellReplacement S)).mapArrow.map
            (Subdiagram.inclusion f (Subdiagram.indexedUnion f
          (fun β => (a β).val))) = _
  rw [← ((originalLocalCellReplacement S)).mapArrow.map_comp, Subdiagram.map_inclusion]

private theorem comparison_hom_ambient
    (hP : ∀ α : ρ.ord.ToType,
        p.app α ≫ Subdiagram.inclusion (((originalLocalCellReplacement S)).map f) (b α).val =
      ((originalLocalCellReplacement S)).mapArrow.map (Subdiagram.inclusion f (a α).val)) :
    (originalLocalLadderColimitIso S ρ hκ f γ a ha b hb p q hPQ hQP).hom ≫
        Subdiagram.inclusion (((originalLocalCellReplacement S)).map f)
            (Subdiagram.indexedUnion (((originalLocalCellReplacement S)).map f)
              (fun α => (b α).val)) =
      ((originalLocalCellReplacement S)).mapArrow.map
          (Subdiagram.inclusion f (Subdiagram.indexedUnion f (fun α => (a α).val))) := by
  let r := (originalLocalCellReplacement S).mapArrow.mapCocone
    (cardinalSubarrowChainCocone f γ a ha)
  let cB := cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb
  let Φ : r.pt ⟶ cB.pt :=
    (originalLocalLadderColimitIso S ρ hκ f γ a ha b hb p q hPQ hQP).hom
  let jA : r.pt ⟶ Arrow.mk ((originalLocalCellReplacement S).map f) :=
    (originalLocalCellReplacement S).mapArrow.map
      (Subdiagram.inclusion f (Subdiagram.indexedUnion f (fun α => (a α).val)))
  let jB : cB.pt ⟶ Arrow.mk ((originalLocalCellReplacement S).map f) :=
    Subdiagram.inclusion ((originalLocalCellReplacement S).map f)
      (Subdiagram.indexedUnion ((originalLocalCellReplacement S).map f) (fun α => (b α).val))
  change Φ ≫ jB = jA
  apply (originalLocalLadderRUnionIsColimit S ρ hκ f γ a ha).hom_ext
  intro α
  have hΦ : r.ι.app α ≫ Φ = p.app α ≫ cB.ι.app α :=
    originalLocalLadderColimitIso_hom_leg S ρ hκ f γ a ha b hb p q hPQ hQP α
  have hB : cB.ι.app α ≫ jB =
      Subdiagram.inclusion ((originalLocalCellReplacement S).map f) (b α).val :=
    Subdiagram.map_inclusion ((originalLocalCellReplacement S).map f)
      (Subdiagram.le_indexedUnion ((originalLocalCellReplacement S).map f) (fun β => (b β).val) α)
  have hA : r.ι.app α ≫ jA =
      (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f (a α).val) :=
    mapped_union_inclusion S ρ f γ a ha α
  let tA : ((ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
      (originalLocalCellReplacement S).mapArrow).obj α ⟶
        Arrow.mk ((originalLocalCellReplacement S).map f) :=
    (originalLocalCellReplacement S).mapArrow.map (Subdiagram.inclusion f (a α).val)
  have hp : p.app α ≫ Subdiagram.inclusion ((originalLocalCellReplacement S).map f)
      (b α).val = tA := hP α
  calc
    _ = (r.ι.app α ≫ Φ) ≫ jB := (CategoryTheory.Category.assoc _ _ _).symm
    _ = (p.app α ≫ cB.ι.app α) ≫ jB := congrArg (fun m => m ≫ jB) hΦ
    _ = p.app α ≫ (cB.ι.app α ≫ jB) := CategoryTheory.Category.assoc _ _ _
    _ = p.app α ≫ Subdiagram.inclusion ((originalLocalCellReplacement S).map f) (b α).val :=
      congrArg (fun m => p.app α ≫ m) hB
    _ = tA := hp
    _ = _ := hA.symm

/-- The forward comparison retains the whole original p ambient square. -/
theorem originalLocalLadderColimitIso_hom_ambient
    (hP : ∀ α : ρ.ord.ToType,
        p.app α ≫ Subdiagram.inclusion (((originalLocalCellReplacement S)).map f) (b α).val =
      ((originalLocalCellReplacement S)).mapArrow.map (Subdiagram.inclusion f (a α).val)) :
    (originalLocalLadderColimitIso S ρ hκ f γ a ha b hb p q hPQ hQP).hom ≫
        Subdiagram.inclusion (((originalLocalCellReplacement S)).map f)
            (Subdiagram.indexedUnion (((originalLocalCellReplacement S)).map f)
              (fun α => (b α).val)) =
      ((originalLocalCellReplacement S)).mapArrow.map
          (Subdiagram.inclusion f (Subdiagram.indexedUnion f (fun α => (a α).val))) :=
  comparison_hom_ambient S ρ hκ f γ a ha b hb p q hPQ hQP hP

private theorem comparison_inv_ambient
    (hQ : ∀ α : ρ.ord.ToType,
        q.app α ≫ ((originalLocalCellReplacement S)).mapArrow.map
        (Subdiagram.inclusion f (a (Order.succ α)).val) =
      Subdiagram.inclusion (((originalLocalCellReplacement S)).map f) (b α).val) :
    (originalLocalLadderColimitIso S ρ hκ f γ a ha b hb p q hPQ hQP).inv ≫
        ((originalLocalCellReplacement S)).mapArrow.map
            (Subdiagram.inclusion f (Subdiagram.indexedUnion f (fun α => (a α).val))) =
      Subdiagram.inclusion (((originalLocalCellReplacement S)).map f)
          (Subdiagram.indexedUnion (((originalLocalCellReplacement S)).map f)
            (fun α => (b α).val)) := by
  let r := (originalLocalCellReplacement S).mapArrow.mapCocone
    (cardinalSubarrowChainCocone f γ a ha)
  let cB := cardinalSubarrowChainCocone ((originalLocalCellReplacement S).map f) γ b hb
  let Ψ : cB.pt ⟶ r.pt :=
    (originalLocalLadderColimitIso S ρ hκ f γ a ha b hb p q hPQ hQP).inv
  let jA : r.pt ⟶ Arrow.mk ((originalLocalCellReplacement S).map f) :=
    (originalLocalCellReplacement S).mapArrow.map
      (Subdiagram.inclusion f (Subdiagram.indexedUnion f (fun α => (a α).val)))
  let jB : cB.pt ⟶ Arrow.mk ((originalLocalCellReplacement S).map f) :=
    Subdiagram.inclusion ((originalLocalCellReplacement S).map f)
      (Subdiagram.indexedUnion ((originalLocalCellReplacement S).map f) (fun α => (b α).val))
  change Ψ ≫ jA = jB
  apply (cardinalSubarrowChainIsColimit ((originalLocalCellReplacement S).map f) γ b hb).hom_ext
  intro α
  have hΨ : cB.ι.app α ≫ Ψ = q.app α ≫ r.ι.app (Order.succ α) :=
    originalLocalLadderColimitIso_inv_leg S ρ hκ f γ a ha b hb p q hPQ hQP α
  have hA : r.ι.app (Order.succ α) ≫ jA =
      (originalLocalCellReplacement S).mapArrow.map
          (Subdiagram.inclusion f (a (Order.succ α)).val) :=
    mapped_union_inclusion S ρ f γ a ha (Order.succ α)
  have hB : cB.ι.app α ≫ jB =
      Subdiagram.inclusion ((originalLocalCellReplacement S).map f) (b α).val :=
    Subdiagram.map_inclusion ((originalLocalCellReplacement S).map f)
      (Subdiagram.le_indexedUnion ((originalLocalCellReplacement S).map f) (fun β => (b β).val) α)
  let tB : (hb.functor ⋙ cardinalSubarrowDiagram ((originalLocalCellReplacement S).map f) γ).obj α ⟶
      Arrow.mk ((originalLocalCellReplacement S).map f) :=
    Subdiagram.inclusion ((originalLocalCellReplacement S).map f) (b α).val
  have hq : q.app α ≫ ((originalLocalCellReplacement S).mapArrow.map
      (Subdiagram.inclusion f (a (Order.succ α)).val) :
        ((ha.functor ⋙ cardinalSubarrowDiagram f γ) ⋙
          (originalLocalCellReplacement S).mapArrow).obj (Order.succ α) ⟶
            Arrow.mk ((originalLocalCellReplacement S).map f)) = tB := hQ α
  calc
    _ = (cB.ι.app α ≫ Ψ) ≫ jA := (CategoryTheory.Category.assoc _ _ _).symm
    _ = (q.app α ≫ r.ι.app (Order.succ α)) ≫ jA := congrArg (fun m => m ≫ jA) hΨ
    _ = q.app α ≫ (r.ι.app (Order.succ α) ≫ jA) := CategoryTheory.Category.assoc _ _ _
    _ = q.app α ≫ (originalLocalCellReplacement S).mapArrow.map
        (Subdiagram.inclusion f (a (Order.succ α)).val) := congrArg (fun m => q.app α ≫ m) hA
    _ = tB := hq
    _ = _ := hB.symm

/-- The inverse comparison retains the whole original q ambient square. -/
theorem originalLocalLadderColimitIso_inv_ambient
    (hQ : ∀ α : ρ.ord.ToType,
        q.app α ≫ ((originalLocalCellReplacement S)).mapArrow.map
        (Subdiagram.inclusion f (a (Order.succ α)).val) =
      Subdiagram.inclusion (((originalLocalCellReplacement S)).map f) (b α).val) :
    (originalLocalLadderColimitIso S ρ hκ f γ a ha b hb p q hPQ hQP).inv ≫
        ((originalLocalCellReplacement S)).mapArrow.map
            (Subdiagram.inclusion f (Subdiagram.indexedUnion f (fun α => (a α).val))) =
      Subdiagram.inclusion (((originalLocalCellReplacement S)).map f)
          (Subdiagram.indexedUnion (((originalLocalCellReplacement S)).map f)
            (fun α => (b α).val)) :=
  comparison_inv_ambient S ρ hκ f γ a ha b hb p q hPQ hQP hQ

end SimplicialPresheaf.InjectiveKan
