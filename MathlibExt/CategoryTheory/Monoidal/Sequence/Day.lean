/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Sequence.Index
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor

/-!
# Day convolution of sequences

This file specializes Day convolution to sequences indexed by the additive
natural-number monoidal category.  It records evaluation and its ordinary
free adjoint, the finite graded tensor formula, and the degree-zero and
positive-degree formulas for the Day unit.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped ExternalProduct MonoidalCategory

namespace CategoryTheory

universe v u

@[expose] public section

/-- Sequences in `V`, equipped with their Day-convolution monoidal structure. -/
abbrev Sequence (V : Type u) [Category.{v} V] [MonoidalCategory V] :=
  DayFunctor Sequence.Index V

end

namespace Sequence

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

@[expose] public section

/-- Evaluation of a sequence at degree `n`. -/
def evaluation (V : Type u) [Category.{v} V] [MonoidalCategory V] (n : ℕ) :
    Sequence V ⥤ V :=
  (DayFunctor.equiv Sequence.Index V).functor ⋙
    (CategoryTheory.evaluation Sequence.Index V).obj (Sequence.index n)

/-- The ordinary diagram-theoretic free sequence concentrated at degree `n`. -/
def freeAt (V : Type u) [Category.{v} V] [MonoidalCategory V]
    [∀ i j : Sequence.Index, HasCoproductsOfShape (i ⟶ j) V] (n : ℕ) :
    V ⥤ Sequence V :=
  CategoryTheory.evaluationLeftAdjoint V (Sequence.index n) ⋙
    (DayFunctor.equiv Sequence.Index V).inverse

/-- The free-at-degree/evaluation adjunction for ordinary sequences. -/
def freeAtEvaluationAdjunction (V : Type u) [Category.{v} V]
    [MonoidalCategory V] [∀ i j : Sequence.Index,
      HasCoproductsOfShape (i ⟶ j) V] (n : ℕ) :
    freeAt V n ⊣ evaluation V n :=
  (CategoryTheory.evaluationAdjunctionRight V (Sequence.index n)).comp
    (DayFunctor.equiv Sequence.Index V).symm.toAdjunction

end

abbrev decompositionObject (n : ℕ) (p : Fin (n + 1)) :
    CostructuredArrow (tensor Sequence.Index) (Sequence.index n) :=
  CostructuredArrow.mk
    (Y := (Sequence.index (p : ℕ), Sequence.index (n - (p : ℕ))))
    (eqToHom ((Sequence.tensorObj_index (p : ℕ) (n - (p : ℕ))).trans
      (congrArg Sequence.index (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt)))))

abbrev decompositionFunctor (n : ℕ) :
    Discrete (Fin (n + 1)) ⥤
      CostructuredArrow (tensor Sequence.Index) (Sequence.index n) where
  obj p := decompositionObject n p.as
  map {p q} f := eqToHom (congrArg (decompositionObject n) f.eq)

def decompositionFullyFaithful (n : ℕ) :
    (decompositionFunctor n).FullyFaithful where
  preimage {p q} f := by
    apply Discrete.eqToHom
    apply Fin.ext
    simpa [decompositionFunctor, decompositionObject, Sequence.index] using
      congrArg (fun x : Multiplicative ℕ => x.toAdd)
        (Discrete.eq_of_hom f.left.fst)
  map_preimage _ := by
    apply CostructuredArrow.hom_ext
    ext <;> apply Discrete.hom_eq
  preimage_map _ := Discrete.hom_eq

noncomputable def decompositionIsEquivalence (n : ℕ) :
    PLift (decompositionFunctor n).IsEquivalence := by
  let F := decompositionFunctor n
  let hFF : F.FullyFaithful := decompositionFullyFaithful n
  let hEss : F.EssSurj :=
    ⟨fun j => by
      have hsum : Sequence.degree j.left.1 + Sequence.degree j.left.2 = n := by
        have h := Discrete.eq_of_hom j.hom
        change
          (j.left.1.as.toAdd + j.left.2.as.toAdd : ℕ) =
            (Sequence.index n).as.toAdd at h
        simpa [Sequence.degree, Sequence.index] using h
      let p : Fin (n + 1) :=
        ⟨Sequence.degree j.left.1, by omega⟩
      have hp : Sequence.index (p : ℕ) = j.left.1 :=
        Sequence.index_degree j.left.1
      have hq : Sequence.index (n - (p : ℕ)) = j.left.2 := by
        change Sequence.index (n - Sequence.degree j.left.1) = j.left.2
        rw [show n - Sequence.degree j.left.1 = Sequence.degree j.left.2 by omega]
        exact Sequence.index_degree j.left.2
      have hleft : (F.obj ⟨p⟩).left = j.left := by
        exact Prod.ext hp hq
      refine ⟨⟨p⟩, ⟨CostructuredArrow.isoMk (eqToIso hleft) ?_⟩⟩
      apply Discrete.hom_eq⟩
  exact ⟨
    { faithful := hFF.faithful
      full := hFF.full
      essSurj := hEss }⟩

noncomputable def decompositionDiagramIso (X Y : Sequence V) (n : ℕ) :
    decompositionFunctor n ⋙
        CostructuredArrow.proj (tensor Sequence.Index) (Sequence.index n) ⋙
          X.functor ⊠ Y.functor ≅
      Discrete.functor (fun p : Fin (n + 1) =>
        X.functor.obj (Sequence.index (p : ℕ)) ⊗
          Y.functor.obj (Sequence.index (n - (p : ℕ)))) :=
  NatIso.ofComponents (fun p => eqToIso (by
    rcases p with ⟨p⟩
    rfl)) (by
    intro p q f
    rcases p with ⟨p⟩
    rcases q with ⟨q⟩
    have hpq : p = q := Discrete.eq_of_hom f
    subst q
    rw [show f = 𝟙 _ from Discrete.hom_eq]
    simp)

variable
  [∀ (F G : Sequence.Index ⥤ V),
    (tensor Sequence.Index).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ Sequence.Index)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (W : V) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor Sequence.Index) d) (tensorLeft W)]
  [∀ (W : V) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow (tensor Sequence.Index) d) (tensorRight W)]
  [∀ (W : V) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorLeft W)]
  [∀ (W : V) (d : Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorRight W)]
  [∀ (W : V) (d : Sequence.Index × Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((𝟭 Sequence.Index).prod
          (Functor.fromPUnit.{0} (𝟙_ Sequence.Index))) d)
      (tensorRight W)]
  [∀ (W : V) (d : Sequence.Index × Sequence.Index),
    PreservesColimitsOfShape
      (CostructuredArrow
        ((tensor Sequence.Index).prod (𝟭 Sequence.Index)) d)
      (tensorRight W)]

public section

/-- The degree-`n` value of the Day tensor is the coproduct over all
decompositions `n = p + (n-p)`. -/
noncomputable def tensorObjIso
    [∀ n : ℕ, HasCoproductsOfShape (Fin (n + 1)) V]
    (X Y : Sequence V) (n : ℕ) :
    (X ⊗ Y).functor.obj (Sequence.index n) ≅
      ∐ fun p : Fin (n + 1) =>
        X.functor.obj (Sequence.index (p : ℕ)) ⊗
          Y.functor.obj (Sequence.index (n - (p : ℕ))) := by
  let D := CostructuredArrow.proj (tensor Sequence.Index) (Sequence.index n) ⋙
    X.functor ⊠ Y.functor
  let G := Discrete.functor (fun p : Fin (n + 1) =>
    X.functor.obj (Sequence.index (p : ℕ)) ⊗
      Y.functor.obj (Sequence.index (n - (p : ℕ))))
  let F := decompositionFunctor n
  let hEquiv := (decompositionIsEquivalence n).down
  let e₀ := @Functor.asEquivalence _ _ _ _ F hEquiv
  let hfun : e₀.functor = F := @Functor.asEquivalence_functor _ _ _ _ F hEquiv
  let e := e₀.changeFunctor (eqToIso hfun)
  let w : e.functor ⋙ D ≅ G := decompositionDiagramIso X Y n
  let hD : IsColimit ((colimit.cocone D).whisker e.functor) :=
    (colimit.isColimit D).whiskerEquivalence e
  let hG : IsColimit (Sigma.cocone G) := coproductIsCoproduct' G
  let hDay : (Functor.LeftExtension.mk (X ⊗ Y).functor
      (DayFunctor.η X Y)).IsPointwiseLeftKanExtensionAt (Sequence.index n) :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := Sequence.Index) (V := V) (D := Sequence V) X Y (Sequence.index n)
  let k := IsColimit.coconePointsIsoOfNatIso hD hG w
  exact hDay.isoColimit ≪≫ k

end

noncomputable def tensorObjIso_η_data
    [∀ n : ℕ, HasCoproductsOfShape (Fin (n + 1)) V]
    (X Y : Sequence V) (n : ℕ) (p : Fin (n + 1)) :
    PLift (
    (DayFunctor.η X Y).app
          (Sequence.index (p : ℕ),
            Sequence.index (n - (p : ℕ))) ≫
        (X ⊗ Y).functor.map
          (eqToHom
            ((Sequence.tensorObj_index (p : ℕ) (n - (p : ℕ))).trans
              (congrArg Sequence.index
                (Nat.add_sub_of_le
                  (Nat.le_of_lt_succ p.isLt))))) ≫
        (Sequence.tensorObjIso X Y n).hom =
      Sigma.ι
        (fun q : Fin (n + 1) =>
          X.functor.obj (Sequence.index (q : ℕ)) ⊗
            Y.functor.obj (Sequence.index (n - (q : ℕ)))) p) := by
  let D := CostructuredArrow.proj (tensor Sequence.Index) (Sequence.index n) ⋙
    X.functor ⊠ Y.functor
  let G := Discrete.functor (fun q : Fin (n + 1) =>
    X.functor.obj (Sequence.index (q : ℕ)) ⊗
      Y.functor.obj (Sequence.index (n - (q : ℕ))))
  let F := decompositionFunctor n
  let hEquiv := (decompositionIsEquivalence n).down
  let e₀ := @Functor.asEquivalence _ _ _ _ F hEquiv
  let hfun : e₀.functor = F := @Functor.asEquivalence_functor _ _ _ _ F hEquiv
  let e := e₀.changeFunctor (eqToIso hfun)
  let w : e.functor ⋙ D ≅ G := decompositionDiagramIso X Y n
  let hD : IsColimit ((colimit.cocone D).whisker e.functor) :=
    (colimit.isColimit D).whiskerEquivalence e
  let hG : IsColimit (Sigma.cocone G) := coproductIsCoproduct' G
  let hDay : (Functor.LeftExtension.mk (X ⊗ Y).functor
      (DayFunctor.η X Y)).IsPointwiseLeftKanExtensionAt (Sequence.index n) :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      (C := Sequence.Index) (V := V) (D := Sequence V) X Y (Sequence.index n)
  let k := IsColimit.coconePointsIsoOfNatIso hD hG w
  have hleft : (decompositionObject n p).left =
      (Sequence.index (p : ℕ), Sequence.index (n - (p : ℕ))) := rfl
  have hhom : (decompositionObject n p).hom =
      eqToHom
        ((Sequence.tensorObj_index (p : ℕ) (n - (p : ℕ))).trans
          (congrArg Sequence.index
            (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt)))) := rfl
  have hDayLeg :
      (DayFunctor.η X Y).app
            (Sequence.index (p : ℕ), Sequence.index (n - (p : ℕ))) ≫
          (X ⊗ Y).functor.map
            (eqToHom
              ((Sequence.tensorObj_index (p : ℕ) (n - (p : ℕ))).trans
                (congrArg Sequence.index
                  (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt))))) ≫
          hDay.isoColimit.hom =
        colimit.ι D (decompositionObject n p) := by
    have h := hDay.ι_isoColimit_hom (decompositionObject n p)
    cases hleft
    cases hhom
    simpa [D] using h
  have hk : colimit.ι D (decompositionObject n p) ≫ k.hom =
      Sigma.ι (fun q : Fin (n + 1) =>
        X.functor.obj (Sequence.index (q : ℕ)) ⊗
          Y.functor.obj (Sequence.index (n - (q : ℕ)))) p := by
    have h :=
      IsColimit.comp_coconePointsIsoOfNatIso_hom hD hG w (Discrete.mk p)
    simpa [D, G, F, e, w, k, Functor.asEquivalence_functor,
      decompositionDiagramIso, decompositionFunctor,
      decompositionObject, Sigma.cocone] using h
  have htensor : tensorObjIso X Y n = hDay.isoColimit ≪≫ k := by rfl
  refine ⟨?_⟩
  have hcomp := congrArg (fun f => f ≫ k.hom) hDayLeg
  have hfinal := hcomp.trans hk
  have hfinal' :
      (DayFunctor.η X Y).app
            (Sequence.index (p : ℕ), Sequence.index (n - (p : ℕ))) ≫
          (X ⊗ Y).functor.map
            (eqToHom
              ((Sequence.tensorObj_index (p : ℕ) (n - (p : ℕ))).trans
                (congrArg Sequence.index
                  (Nat.add_sub_of_le (Nat.le_of_lt_succ p.isLt))))) ≫
          hDay.isoColimit.hom ≫ k.hom =
        Sigma.ι (fun q : Fin (n + 1) =>
          X.functor.obj (Sequence.index (q : ℕ)) ⊗
            Y.functor.obj (Sequence.index (n - (q : ℕ)))) p := by
    simpa only [Category.assoc] using hfinal
  have hpt : (Sigma.cocone G).pt =
      ∐ fun q : Fin (n + 1) =>
        X.functor.obj (Sequence.index (q : ℕ)) ⊗
          Y.functor.obj (Sequence.index (n - (q : ℕ))) := by
    rfl
  have htransport := congrArg (fun f => f ≫ eqToHom hpt) hfinal'
  rw [Category.assoc] at htransport
  rw [htensor, Iso.trans_hom]
  apply (cancel_mono (eqToHom hpt)).mp
  convert htransport using 1
  exact Category.assoc _ _ _

@[expose] public section

/-- The Day generator for the `p`th decomposition is the corresponding
coproduct injection under `tensorObjIso`. -/
theorem tensorObjIso_η
    [∀ n : ℕ, HasCoproductsOfShape (Fin (n + 1)) V]
    (X Y : Sequence V) (n : ℕ) (p : Fin (n + 1)) :
    (DayFunctor.η X Y).app
          (Sequence.index (p : ℕ),
            Sequence.index (n - (p : ℕ))) ≫
        (X ⊗ Y).functor.map
          (eqToHom
            ((Sequence.tensorObj_index (p : ℕ) (n - (p : ℕ))).trans
              (congrArg Sequence.index
                (Nat.add_sub_of_le
                  (Nat.le_of_lt_succ p.isLt))))) ≫
        (Sequence.tensorObjIso X Y n).hom =
      Sigma.ι
        (fun q : Fin (n + 1) =>
          X.functor.obj (Sequence.index (q : ℕ)) ⊗
            Y.functor.obj (Sequence.index (n - (q : ℕ)))) p :=
  (tensorObjIso_η_data X Y n p).down

/-- The Day-convolution unit is the tensor unit of `V` in degree zero. -/
noncomputable def tensorUnitZeroIso (V : Type u) [Category.{v} V]
    [MonoidalCategory V]
    [∀ (F G : Sequence.Index ⥤ V),
      (tensor Sequence.Index).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} (𝟙_ Sequence.Index)).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} (𝟙_ V))]
    [∀ (W : V) (d : Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow (tensor Sequence.Index) d) (tensorLeft W)]
    [∀ (W : V) (d : Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow (tensor Sequence.Index) d) (tensorRight W)]
    [∀ (W : V) (d : Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow
          (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorLeft W)]
    [∀ (W : V) (d : Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow
          (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorRight W)]
    [∀ (W : V) (d : Sequence.Index × Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow
          ((𝟭 Sequence.Index).prod
            (Functor.fromPUnit.{0} (𝟙_ Sequence.Index))) d)
        (tensorRight W)]
    [∀ (W : V) (d : Sequence.Index × Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow
          ((tensor Sequence.Index).prod (𝟭 Sequence.Index)) d)
        (tensorRight W)] :
    (𝟙_ (Sequence V)).functor.obj (Sequence.index 0) ≅ 𝟙_ V := by
  let hUnit :
      (Functor.LeftExtension.mk (𝟙_ (Sequence V)).functor
        (DayFunctor.νNatTrans Sequence.Index V)).IsPointwiseLeftKanExtensionAt
          (Sequence.index 0) :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionUnitUnit
      Sequence.Index V (Sequence V) (Sequence.index 0)
  let L := Functor.fromPUnit.{0} (𝟙_ Sequence.Index)
  let hFF : L.FullyFaithful :=
    { preimage := fun {_ _} _ => eqToHom (Subsingleton.elim _ _)
      map_preimage := fun _ => Discrete.hom_eq
      preimage_map := fun _ => Discrete.hom_eq }
  let _ : L.Full := hFF.full
  let _ : L.Faithful := hFF.faithful
  letI : IsIso (DayFunctor.ν Sequence.Index V) :=
    hUnit.isIso_hom_app (X := ⟨PUnit.unit⟩)
  exact (asIso (DayFunctor.ν Sequence.Index V)).symm

/-- The Day-convolution unit is initial in every positive degree. -/
noncomputable def tensorUnitSuccIso (V : Type u) [Category.{v} V]
    [MonoidalCategory V]
    [∀ (F G : Sequence.Index ⥤ V),
      (tensor Sequence.Index).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} (𝟙_ Sequence.Index)).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} (𝟙_ V))]
    [∀ (W : V) (d : Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow (tensor Sequence.Index) d) (tensorLeft W)]
    [∀ (W : V) (d : Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow (tensor Sequence.Index) d) (tensorRight W)]
    [∀ (W : V) (d : Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow
          (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorLeft W)]
    [∀ (W : V) (d : Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow
          (Functor.fromPUnit.{0} (𝟙_ Sequence.Index)) d) (tensorRight W)]
    [∀ (W : V) (d : Sequence.Index × Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow
          ((𝟭 Sequence.Index).prod
            (Functor.fromPUnit.{0} (𝟙_ Sequence.Index))) d)
        (tensorRight W)]
    [∀ (W : V) (d : Sequence.Index × Sequence.Index),
      PreservesColimitsOfShape
        (CostructuredArrow
          ((tensor Sequence.Index).prod (𝟭 Sequence.Index)) d)
        (tensorRight W)] [HasInitial V] (n : ℕ) :
    (𝟙_ (Sequence V)).functor.obj (Sequence.index (n + 1)) ≅ ⊥_ V := by
  let L := Functor.fromPUnit.{0} (𝟙_ Sequence.Index)
  let J := CostructuredArrow L (Sequence.index (n + 1))
  letI : IsEmpty J :=
    ⟨fun j => by
      have h := Discrete.eq_of_hom j.hom
      change (0 : ℕ) = n + 1 at h
      omega⟩
  let hUnit :
      (Functor.LeftExtension.mk (𝟙_ (Sequence V)).functor
        (DayFunctor.νNatTrans Sequence.Index V)).IsPointwiseLeftKanExtensionAt
          (Sequence.index (n + 1)) :=
    LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionUnitUnit
      Sequence.Index V (Sequence V) (Sequence.index (n + 1))
  let hInitial : IsInitial
      ((𝟙_ (Sequence V)).functor.obj (Sequence.index (n + 1))) :=
    (isColimitEquivIsInitialOfIsEmpty V
      (Functor.LeftExtension.coconeAt
        (Functor.LeftExtension.mk (𝟙_ (Sequence V)).functor
          (DayFunctor.νNatTrans Sequence.Index V))
        (Sequence.index (n + 1)))).toFun hUnit
  exact hInitial.uniqueUpToIso initialIsInitial

end

end Sequence

end CategoryTheory
