/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OrderedJFSRawFamilies
import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace SimplicialPresheaf.OrderedJFS

/-- The actual original Source1 evaluation and constant-tuple category equivalence. -/
def oneSiteEquivalence : FinitePowerSite.Source 1 ≌ SimplexCategory :=
  (piEquivalenceFunctorDiscrete (Fin 1) SimplexCategory).trans
    (((Discrete.equivalence finOneEquiv).congrLeft).trans
      (Functor.equiv (C := SimplexCategory)))

/-- Original one-coordinate presheaves are transported on the SAME opposite site and coefficient
universe. -/
def oneOriginalEquivalence : Original.{u} 1 ≌ SimplicialPresheaf.{u} SimplexCategory :=
  SimplicialPresheaf.transport oneSiteEquivalence
/-- Compose the original one-coordinate carrier transport with the actual scalar designation
equivalence. -/
def oneDesignatedEquivalence : Original.{u} 1 ≌ SimplicialSpace.{u} :=
  oneOriginalEquivalence.{u}.trans SimplicialSpace.equivalenceSimplicialObject.symm

private theorem oneSite_inverse_obj (a : SimplexCategory) :
    oneSiteEquivalence.inverse.obj a = fun _ => a := rfl

private theorem oneIndexBridgePoint (a : SimplexCategoryᵒᵖ) :
    (FinitePowerSite.sourceOpEquiv 1).functor.obj (oneSiteEquivalence.inverse.op.obj a) =
      FinitePowerSite.oneIndexEquiv.inverse.obj a := by
  change (fun i : Fin 1 => op ((oneSiteEquivalence.inverse.obj a.unop) i)) = _
  rw [oneSite_inverse_obj, FinitePowerSite.oneIndexEquiv_inverse_obj]

private def oneIndexBridge :
    (oneSiteEquivalence.inverse.op ⋙ (FinitePowerSite.sourceOpEquiv 1).functor) ≅
      FinitePowerSite.oneIndexEquiv.inverse :=
  NatIso.ofComponents (fun a => eqToIso (oneIndexBridgePoint a)) (by
    intro a b f
    ext i
    fin_cases i
    rfl)

-- Both paths are actual inverse-site precomposition. The iso is derived from that index map.
private def oneOriginalMultiIso (M : Multi.{u} 1) :
    oneOriginalEquivalence.{u}.functor.obj
      ((FinitePowerSite.diagramEquiv 1 SSet.{u}).inverse.obj M) ≅
        (FinitePowerSite.oneDiagramEquiv SSet.{u}).functor.obj M := by
  change (oneSiteEquivalence.inverse.op ⋙ (FinitePowerSite.sourceOpEquiv 1).functor) ⋙ M ≅
    FinitePowerSite.oneIndexEquiv.inverse ⋙ M
  exact
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ
        (FinitePowerSite.Index 1) SSet.{u}).obj M).mapIso
    oneIndexBridge

private theorem oneOriginalMultiIso_naturality {M N : Multi.{u} 1} (f : M ⟶ N) :
    oneOriginalEquivalence.{u}.functor.map
      ((FinitePowerSite.diagramEquiv 1 SSet.{u}).inverse.map f) ≫
        (oneOriginalMultiIso N).hom =
      (oneOriginalMultiIso M).hom ≫
        (FinitePowerSite.oneDiagramEquiv SSet.{u}).functor.map f := by
  apply NatTrans.ext
  funext a
  change f.app _ ≫ N.map (oneIndexBridge.hom.app a) =
    M.map (oneIndexBridge.hom.app a) ≫ f.app _
  exact (f.naturality (oneIndexBridge.hom.app a)).symm

private def oneOriginalMultiArrowIso (f : Arrow (Multi.{u} 1)) :
    oneOriginalEquivalence.{u}.functor.mapArrow.obj
      ((FinitePowerSite.diagramEquiv 1 SSet.{u}).inverse.mapArrow.obj f) ≅
        (FinitePowerSite.oneDiagramEquiv SSet.{u}).functor.mapArrow.obj f :=
  Arrow.isoMk (oneOriginalMultiIso f.left) (oneOriginalMultiIso f.right)
    (oneOriginalMultiIso_naturality f.hom).symm

private theorem noOtherCoord (j : OtherCoord 1 (0 : Fin 1)) : False :=
  j.property (Subsingleton.elim _ _)
/-- The exact original normalized Fin1 labels are equivalent to the original scalar spine and
completeness index. -/
def oneNormalizedIndexEquiv : Generator 1 ≃ SSet.Rezk.LocalizingIndex where
  toFun
    | .inl s => .inl ⟨s.arity, s.arity_ge⟩
    | .inr (.inl _) => .inr PUnit.unit
    | .inr (.inr c) => isEmptyElim c
  invFun
    | .inl n => .inl ⟨0, n.1, n.2, fun j => (j.property (Subsingleton.elim _ _)).elim⟩
    | .inr _ => .inr (.inl ⟨0, fun j => (j.property (Subsingleton.elim _ _)).elim⟩)
  left_inv g := by
    rcases g with s | c | c
    · cases s with
      | mk coord arity bound other =>
        have h : coord = 0 := Subsingleton.elim _ _
        subst coord
        change (Sum.inl (⟨0, arity, bound,
            fun j => (j.property (Subsingleton.elim _ _)).elim⟩ : SegalIndex 1) : Generator 1) =
          Sum.inl (⟨0, arity, bound, other⟩ : SegalIndex 1)
        have ho : (fun j : OtherCoord 1 0 =>
            (j.property (Subsingleton.elim _ _)).elim : OtherCoord 1 0 → ℕ) = other := by
          funext j
          exact (noOtherCoord j).elim
        rw [ho]
    · cases c with
      | mk coord other =>
        have h : coord = 0 := Subsingleton.elim _ _
        subst coord
        change
            (Sum.inr (Sum.inl (⟨0,
              fun j => (j.property (Subsingleton.elim _ _)).elim⟩ : CompletenessIndex
              1)) : Generator 1) =
          Sum.inr (Sum.inl (⟨0, other⟩ : CompletenessIndex 1))
        have ho : (fun j : OtherCoord 1 0 =>
            (j.property (Subsingleton.elim _ _)).elim : OtherCoord 1 0 → ℕ) = other := by
          funext j
          exact (noOtherCoord j).elim
        rw [ho]
    · exact isEmptyElim c
  right_inv i := by
    rcases i with n | x
    · rfl
    · cases x
      rfl

/-- The original finite coefficient family retains spines and kappa:K→F0 at the SAME labels. -/
def oneFiniteFamily : SSet.Rezk.LocalizingIndex → Arrow (SimplicialPresheaf.{u} SimplexCategory)
  | .inl n => Arrow.mk (SSet.Rezk.segalMap.{u} n.1)
  | .inr _ => Arrow.mk SSet.Rezk.FiniteCompleteness.kappa.{u}

/-- The genuine dependent singleton product is compared by original coordinate evaluation and its
inverse. -/
def oneProductIso (X : Fin 1 → SimplicialObject SSet.{u}) :
    (FinitePowerSite.oneDiagramEquiv SSet.{u}).functor.obj (productDiagram X) ≅ X 0 :=
  NatIso.ofComponents (fun a =>
    NatIso.ofComponents (fun n =>
      (Equiv.piUnique (fun i : Fin 1 => ((X i).obj a).obj n)).toIso)
      (by intro n m theta; ext x; rfl))
    (by intro a b theta; ext n x; rfl)

/-- The original singleton product Arrow retains both endpoint isos and its original coordinate
map. -/
def oneProductArrowIso (f : Fin 1 → Arrow (SimplicialObject SSet.{u})) :
    ((FinitePowerSite.oneDiagramEquiv SSet.{u}).functor.mapArrow.obj (productArrow f)) ≅ f 0 :=
  Arrow.isoMk (oneProductIso (fun i => (f i).left))
    (oneProductIso (fun i => (f i).right)) (by ext a n x; rfl)


-- Actual finite coefficient arrow of the full original one-coordinate label.
private def oneFullCoefficient (g : FullGenerator 1) :
    Arrow (SimplicialObject SSet.{u}) :=
  match g with
  | .inl s => Arrow.mk (SSet.Rezk.segalMap.{u} s.arity)
  | .inr (.inl _) => Arrow.mk SSet.Rezk.FiniteCompleteness.kappa.{u}
  | .inr (.inr _) => Arrow.mk (𝟙 (SSet.Rezk.representable.{u} 0))

private def oneFullArrowIso (g : FullGenerator 1) :
    oneOriginalEquivalence.{u}.functor.mapArrow.obj (fullOriginalFamily.{u} 1 g) ≅
      oneFullCoefficient.{u} g := by
  rcases g with s | k | k
  · let f := fullSegalComponents.{u} s
    have h : f 0 = Arrow.mk (SSet.Rezk.segalMap.{u} s.arity) := by
      have hc : (0 : Fin 1) = s.coord := Subsingleton.elim _ _
      rw [hc]
      exact fullSegal_selected s
    exact oneOriginalMultiArrowIso (productArrow f) ≪≫
      oneProductArrowIso f ≪≫ eqToIso h
  · let f := completenessComponents.{u} k
    have h : f 0 = Arrow.mk SSet.Rezk.FiniteCompleteness.kappa.{u} := by
      have hc : (0 : Fin 1) = k.coord := Subsingleton.elim _ _
      rw [hc]
      exact completeness_selected k
    exact oneOriginalMultiArrowIso (productArrow f) ≪≫
      oneProductArrowIso f ≪≫ eqToIso h
  · let f := fullConstancyComponents.{u} k
    have h : f 0 = Arrow.mk (𝟙 (SSet.Rezk.representable.{u} 0)) := by
      have hc : (0 : Fin 1) = k.coord := Subsingleton.elim _ _
      rw [hc]
      exact fullConstancy_selected k
    exact oneOriginalMultiArrowIso (productArrow f) ≪≫
      oneProductArrowIso f ≪≫ eqToIso h

/-- Original normalized generators have the same labels and actual whole finite coefficient maps. -/
def oneNormalizedArrowIso (g : Generator 1) :
    oneOriginalEquivalence.{u}.functor.mapArrow.obj (originalFamily.{u} 1 g) ≅
      oneFiniteFamily.{u} (oneNormalizedIndexEquiv g) := by
  rcases g with s | k | k
  · exact oneFullArrowIso.{u} (normalizedToFull (.inl s))
  · exact oneFullArrowIso.{u} (normalizedToFull (.inr (.inl k)))
  · exact isEmptyElim k

private theorem spineOne_top : SSet.Rezk.spineSubcomplex.{u} 1 = ⊤ := by
  have h : SimplexCategory.mkOfSucc (0 : Fin 1) = 𝟙 ⦋1⦌ := by
    ext i
    fin_cases i <;> rfl
  unfold SSet.Rezk.spineSubcomplex
  rw [iSup_unique]
  change SSet.Subcomplex.range (SSet.stdSimplex.{u}.map (SimplexCategory.mkOfSucc (0 : Fin 1))) = ⊤
  rw [h, CategoryTheory.Functor.map_id]
  exact SSet.Subcomplex.range_eq_top _

private theorem segalMapOne_isIso : IsIso (SSet.Rezk.segalMap.{u} 1) := by
  have h : IsIso (SSet.Rezk.spineSubcomplex.{u} 1).ι := by
    rw [spineOne_top]
    infer_instance
  exact inferInstanceAs (IsIso (SSet.simplicialSpaceDiscrete.map
    (SSet.Rezk.spineSubcomplex.{u} 1).ι))

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_from_fullCoefficient (g : FullGenerator 1)
    (h : IsIso (oneFullCoefficient.{u} g).hom) :
    IsIso (fullOriginalFamily.{u} 1 g).hom := by
  let e := oneFullArrowIso.{u} g
  let : IsIso (oneFullCoefficient.{u} g).hom := h
  have heq : oneOriginalEquivalence.{u}.functor.map (fullOriginalFamily.{u} 1 g).hom =
      e.hom.left ≫ (oneFullCoefficient.{u} g).hom ≫ e.inv.right := by
    have hw := congrArg (fun q => q ≫ e.inv.right) e.hom.w
    have hr : e.hom.right ≫ e.inv.right = 𝟙 _ :=
      congrArg (fun q => q.right) e.hom_inv_id
    simpa only [Functor.mapArrow_obj, Arrow.mk, Category.assoc, hr, Category.comp_id] using hw.symm
  let : IsIso (oneOriginalEquivalence.{u}.functor.map (fullOriginalFamily.{u} 1 g).hom) := by
    rw [heq]
    infer_instance
  exact isIso_of_reflects_iso (fullOriginalFamily.{u} 1 g).hom
    oneOriginalEquivalence.{u}.functor

/-- Full one-fold labels retain real normalized members and real redundant Iso arrows. -/
theorem oneFullRedundancy (g : FullGenerator 1) :
    (∃ n : Generator 1,
      Nonempty (oneOriginalEquivalence.{u}.functor.mapArrow.obj (fullOriginalFamily.{u} 1 g) ≅
        oneOriginalEquivalence.{u}.functor.mapArrow.obj (originalFamily.{u} 1 n))) ∨
      IsIso (fullOriginalFamily.{u} 1 g).hom := by
  rcases g with s | k | k
  · by_cases hn : 2 ≤ s.arity
    · let n : Generator 1 := .inl ⟨s.coord, s.arity, hn, s.otherIndex⟩
      left
      refine ⟨n, ⟨eqToIso ?_⟩⟩
      rfl
    · have ha : s.arity = 1 :=
        Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)) s.arity_pos
      right
      apply isIso_from_fullCoefficient (.inl s)
      change IsIso (SSet.Rezk.segalMap.{u} s.arity)
      rw [ha]
      exact segalMapOne_isIso
  · left
    exact ⟨.inr (.inl k), ⟨Iso.refl _⟩⟩
  · right
    apply isIso_from_fullCoefficient (.inr (.inr k))
    change IsIso (𝟙 (SSet.Rezk.representable.{u} 0))
    infer_instance

end SimplicialPresheaf.OrderedJFS
