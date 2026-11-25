/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHocolim
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToAugmented

/-!
# Canonical point inclusion with an independent simplicial coefficient universe

This is the single proof core extracted from BousfieldKanPointFiberComparison,
whose historical implementation was authored by @toskua. The same original
constant weighted index and all outer/scalar operators define the full inclusion
for arbitrary indexing object/Hom universes and an independent scalar universe.
The historical inferable APIs are specializations in their original module.
No weak-equivalence, Kan or homotopy-fibre conclusion is asserted here.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace SSet
universe u v w
variable {J : Type u} [Category.{v} J]

/-- Weighted-bar index represented by the constant outer chain at `j`. -/
def bkPointWeightedIndex (j : J) (n : ℕ) :
    StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n :=
  ⟨SrepBridge.constChain j n, PUnit.unit⟩

/-- Inclusion of a diagram value into one outer weighted-bar degree along
the constant chain. -/
noncomputable def bkPointOuterComponentOf (E : J ⥤ SSet.{max u v w})
    (j : J) (n : ℕ) :
    E.obj j ⟶
      StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit J) E n :=
  StrictOrdinaryWeightedBar.wbarIncl
    (CategoryBar.replUnit J) E n (bkPointWeightedIndex j n)

@[simp]
private theorem bkPointWeightedIndex_faceZero_general (j : J) (n : ℕ) :
    StrictOrdinaryWeightedBar.wFaceZeroIdx
        (CategoryBar.replUnit J) n (bkPointWeightedIndex j (n + 1)) =
      bkPointWeightedIndex j n := by
  rfl

@[simp]
private theorem bkPointWeightedIndex_faceLast_general (j : J) (n : ℕ) :
    StrictOrdinaryWeightedBar.wFaceLastIdx
        (CategoryBar.replUnit J) n (bkPointWeightedIndex j (n + 1)) =
      bkPointWeightedIndex j n := by
  rfl

@[simp]
private theorem bkPointWeightedIndex_degZero_general (j : J) (n : ℕ) :
    StrictOrdinaryWeightedBar.wDegZeroIdx
        (CategoryBar.replUnit J) n (bkPointWeightedIndex j n) =
      bkPointWeightedIndex j (n + 1) := by
  have hchain :
      SrepBridge.srepDupFirst (SrepBridge.constChain j n) =
        SrepBridge.constChain j (n + 1) := by
    apply Functor.hext
    · intro x
      rcases x with ⟨i, hi⟩
      obtain _ | i := i <;> rfl
    · intro x y f
      rcases x with ⟨i, hi⟩
      rcases y with ⟨k, hk⟩
      obtain _ | i := i
      · obtain _ | k := k
        · apply heq_of_eq
          change 𝟙 j = 𝟙 j
          rfl
        · obtain _ | k := k
          · apply heq_of_eq
            change 𝟙 j = 𝟙 j
            rfl
          · apply heq_of_eq
            change (𝟙 j) ≫ 𝟙 j = 𝟙 j
            simp
      · obtain _ | k := k
        · exfalso
          have hle : i + 1 ≤ 0 := leOfHom f
          omega
        · apply heq_of_eq
          dsimp only [SrepBridge.srepDupFirst, SrepBridge.constChain, ComposableArrows.Precomp.map]
          rfl
  refine Sigma.ext hchain ?_
  change HEq PUnit.unit PUnit.unit
  rfl

private theorem bkPoint_constChain_omit_general (j : J) (n : ℕ)
    (i : Fin (n + 2)) :
    (StrictOmitDup.omitAt i).obj (SrepBridge.constChain j (n + 1)) =
      SrepBridge.constChain j n := by
  apply Functor.hext
  · intro x
    rfl
  · intro x y f
    apply heq_of_eq
    change 𝟙 j = 𝟙 j
    rfl

private theorem bkPoint_constChain_dup_general (j : J) (n : ℕ)
    (i : Fin (n + 1)) :
    (StrictOmitDup.dupAt i).obj (SrepBridge.constChain j n) =
      SrepBridge.constChain j (n + 1) := by
  apply Functor.hext
  · intro x
    rfl
  · intro x y f
    apply heq_of_eq
    change 𝟙 j = 𝟙 j
    rfl

@[simp]
private theorem bkPointWeightedIndex_faceInner_general (j : J) (n : ℕ)
    (i : Fin (n + 2)) (hiLast : i ≠ Fin.last (n + 1)) :
    StrictOrdinaryWeightedBar.wFaceInnerIdx
        (CategoryBar.replUnit J) n i hiLast
        (bkPointWeightedIndex j (n + 1)) =
      bkPointWeightedIndex j n := by
  refine Sigma.ext (bkPoint_constChain_omit_general j n i) ?_
  change HEq PUnit.unit PUnit.unit
  rfl

@[simp]
private theorem bkPointWeightedIndex_degInner_general (j : J) (n : ℕ)
    (i : Fin (n + 1)) :
    StrictOrdinaryWeightedBar.wDegInnerIdx
        (CategoryBar.replUnit J) n i (bkPointWeightedIndex j n) =
      bkPointWeightedIndex j (n + 1) := by
  refine Sigma.ext (bkPoint_constChain_dup_general j n i) ?_
  change HEq PUnit.unit PUnit.unit
  rfl

private theorem bkPoint_faceZeroComponent_general (E : J ⥤ SSet.{max u v w})
    (j : J) (n : ℕ) :
    SrepBridge.srepFaceZeroComponent E
        (SrepBridge.constChain j (n + 1)) =
      𝟙 (E.obj j) := by
  let s := SrepBridge.constChain j (n + 1)
  let e₁ := congrArg E.obj (SrepBridge.srepLeftZero s)
  let e₂ := congrArg E.obj (SrepBridge.srepDropFirst_left s).symm
  change (eqToHom e₁ ≫ E.map (𝟙 j) ≫ eqToHom e₂) = 𝟙 (E.obj j)
  have h₁ : eqToHom e₁ = 𝟙 (E.obj j) := eqToHom_refl _ _
  simp only [h₁]
  exact E.map_id j

private theorem bkPoint_faceLastComponent_general (E : J ⥤ SSet.{max u v w})
    (j : J) (n : ℕ) :
    SrepBridge.srepFaceLastComponent E
        (SrepBridge.constChain j (n + 1)) =
      𝟙 (E.obj j) := by
  rfl

private theorem bkPoint_faceInnerComponent_general (E : J ⥤ SSet.{max u v w})
    (j : J) (n : ℕ) (i : Fin (n + 2)) (hi0 : i ≠ 0) :
    StrictOrdinaryWeightedBar.wFaceInnerComponent E i hi0
        (SrepBridge.constChain j (n + 1)) =
      𝟙 (E.obj j) := by
  change eqToHom _ = 𝟙 (E.obj j)
  exact eqToHom_refl _ _

private theorem bkPoint_degInnerComponent_general (E : J ⥤ SSet.{max u v w})
    (j : J) (n : ℕ) (i : Fin (n + 1)) :
    StrictOrdinaryWeightedBar.wDegInnerComponent E i
        (SrepBridge.constChain j n) =
      𝟙 (E.obj j) := by
  change eqToHom _ = 𝟙 (E.obj j)
  exact eqToHom_refl _ _

private theorem bkPoint_wbarIncl_transport_general
    (E : J ⥤ SSet.{max u v w}) (n : ℕ)
    {p q : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n}
    (h : p = q) :
    eqToHom (congrArg (fun r => E.obj r.1.left) h) ≫
        StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit J) E n q =
      StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n p := by
  subst q
  rw [eqToHom_refl, Category.id_comp]

/-- Outer simplicial-data map inserting a diagram value along the constant
bar chain. -/
noncomputable def bkPointOuterDataMapOf (E : J ⥤ SSet.{max u v w}) (j : J) :
    SimplicialObject.Data.constData (E.obj j) ⟶
      StrictOrdinaryWeightedBar.wbarData
        (CategoryBar.replUnit J) E where
  app n := bkPointOuterComponentOf E j n
  w_δ := by
    intro n i
    change bkPointOuterComponentOf E j (n + 1) ≫
        StrictOrdinaryWeightedBar.wbarδ
          (CategoryBar.replUnit J) E n i =
      𝟙 (E.obj j) ≫ bkPointOuterComponentOf E j n
    rw [Category.id_comp]
    by_cases h0 : i = 0
    · subst i
      rw [StrictOrdinaryWeightedBar.wbarδ_zero]
      unfold bkPointOuterComponentOf
      rw [StrictOrdinaryWeightedBar.wbarFaceZero_ι]
      have hidx := bkPointWeightedIndex_faceZero_general j n
      let carrier := fun r : StrictOrdinaryWeightedBar.WIdx J
          (CategoryBar.replUnit J) n => E.obj r.1.left
      have hcoeff : SrepBridge.srepFaceZeroComponent E
          (SrepBridge.constChain j (n + 1)) =
          eqToHom (congrArg carrier hidx.symm) := by
        cases hidx
        exact (bkPoint_faceZeroComponent_general E j n).trans
          (eqToHom_refl _ _).symm
      change SrepBridge.srepFaceZeroComponent E
          (SrepBridge.constChain j (n + 1)) ≫
            StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) E n
                (StrictOrdinaryWeightedBar.wFaceZeroIdx
                  (CategoryBar.replUnit J) n
                    (bkPointWeightedIndex j (n + 1))) =
          StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) E n (bkPointWeightedIndex j n)
      rw [hcoeff]
      exact bkPoint_wbarIncl_transport_general E n hidx.symm
    · by_cases hlast : i = Fin.last (n + 1)
      · subst i
        rw [StrictOrdinaryWeightedBar.wbarδ_last]
        unfold bkPointOuterComponentOf
        rw [StrictOrdinaryWeightedBar.wbarFaceLast_ι]
        have hidx := bkPointWeightedIndex_faceLast_general j n
        let carrier := fun r : StrictOrdinaryWeightedBar.WIdx J
            (CategoryBar.replUnit J) n => E.obj r.1.left
        have hcoeff : SrepBridge.srepFaceLastComponent E
            (SrepBridge.constChain j (n + 1)) =
            eqToHom (congrArg carrier hidx.symm) := by
          cases hidx
          exact (bkPoint_faceLastComponent_general E j n).trans
            (eqToHom_refl _ _).symm
        change SrepBridge.srepFaceLastComponent E
            (SrepBridge.constChain j (n + 1)) ≫
              StrictOrdinaryWeightedBar.wbarIncl
                (CategoryBar.replUnit J) E n
                  (StrictOrdinaryWeightedBar.wFaceLastIdx
                    (CategoryBar.replUnit J) n
                      (bkPointWeightedIndex j (n + 1))) =
            StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) E n (bkPointWeightedIndex j n)
        rw [hcoeff]
        exact bkPoint_wbarIncl_transport_general E n hidx.symm
      · rw [StrictOrdinaryWeightedBar.wbarδ_inner _ _ _ i h0 hlast]
        unfold bkPointOuterComponentOf
        rw [StrictOrdinaryWeightedBar.wbarFaceInner_ι]
        have hidx := bkPointWeightedIndex_faceInner_general j n i hlast
        let carrier := fun r : StrictOrdinaryWeightedBar.WIdx J
            (CategoryBar.replUnit J) n => E.obj r.1.left
        have hcoeff : StrictOrdinaryWeightedBar.wFaceInnerComponent E i h0
            (SrepBridge.constChain j (n + 1)) =
            eqToHom (congrArg carrier hidx.symm) := by
          cases hidx
          exact (bkPoint_faceInnerComponent_general E j n i h0).trans
            (eqToHom_refl _ _).symm
        change StrictOrdinaryWeightedBar.wFaceInnerComponent E i h0
            (SrepBridge.constChain j (n + 1)) ≫
              StrictOrdinaryWeightedBar.wbarIncl
                (CategoryBar.replUnit J) E n
                  (StrictOrdinaryWeightedBar.wFaceInnerIdx
                    (CategoryBar.replUnit J) n i hlast
                      (bkPointWeightedIndex j (n + 1))) =
            StrictOrdinaryWeightedBar.wbarIncl
              (CategoryBar.replUnit J) E n (bkPointWeightedIndex j n)
        rw [hcoeff]
        exact bkPoint_wbarIncl_transport_general E n hidx.symm
  w_σ := by
    intro n i
    change bkPointOuterComponentOf E j n ≫
        StrictOrdinaryWeightedBar.wbarσ
          (CategoryBar.replUnit J) E n i =
      𝟙 (E.obj j) ≫ bkPointOuterComponentOf E j (n + 1)
    rw [Category.id_comp]
    unfold bkPointOuterComponentOf
    rw [StrictOrdinaryWeightedBar.wbarσ_ι]
    have hidx := bkPointWeightedIndex_degInner_general j n i
    let carrier := fun r : StrictOrdinaryWeightedBar.WIdx J
        (CategoryBar.replUnit J) (n + 1) => E.obj r.1.left
    have hcoeff : StrictOrdinaryWeightedBar.wDegInnerComponent E i
        (SrepBridge.constChain j n) =
        eqToHom (congrArg carrier hidx.symm) := by
      cases hidx
      exact (bkPoint_degInnerComponent_general E j n i).trans
        (eqToHom_refl _ _).symm
    change StrictOrdinaryWeightedBar.wDegInnerComponent E i
        (SrepBridge.constChain j n) ≫
          StrictOrdinaryWeightedBar.wbarIncl
            (CategoryBar.replUnit J) E (n + 1)
              (StrictOrdinaryWeightedBar.wDegInnerIdx
                (CategoryBar.replUnit J) n i (bkPointWeightedIndex j n)) =
      StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E (n + 1)
          (bkPointWeightedIndex j (n + 1))
    rw [hcoeff]
    exact bkPoint_wbarIncl_transport_general E (n + 1) hidx.symm

/-- Outer simplicial map inserting a diagram value along constant bar
chains. -/
noncomputable def bkPointOuterMapOf (E : J ⥤ SSet.{max u v w}) (j : J) :
    (SimplicialObject.Data.constData (E.obj j)).toSimplicialObject ⟶
      StrictOrdinaryWeightedBar.wbarSimplicial
        (CategoryBar.replUnit J) E :=
  SimplicialObject.Data.toSimplicialFunctor.map
    (bkPointOuterDataMapOf E j)

@[simp]
theorem bkPointOuterMapOf_app_mk (E : J ⥤ SSet.{max u v w})
    (j : J) (n : ℕ) :
    (bkPointOuterMapOf E j).app (op ⦋n⦌) =
      bkPointOuterComponentOf E j n := by
  exact SimplicialObject.Data.toSimplicialFunctor_map_app_mk
    (bkPointOuterDataMapOf E j) n

/-- The diagonal of the constant outer data is canonically the original
diagram value. -/
noncomputable def bkPointSourceIsoOf (E : J ⥤ SSet.{max u v w}) (j : J) :
    simplicialDiagonalFunctor.obj
        (SimplicialObject.Data.constData (E.obj j)).toSimplicialObject ≅
      E.obj j :=
  simplicialDiagonalFunctor.mapIso
      (SimplicialObject.Data.constDataIso (E.obj j)) ≪≫
    diagonalConstIso (E.obj j)

/-- Canonical inclusion of a diagram value into its Bousfield--Kan carrier,
using the constant outer chain at the selected indexing object. -/
noncomputable def bkPointInclusionOf (E : J ⥤ SSet.{max u v w}) (j : J) :
    E.obj j ⟶ bkHocolimOf E :=
  (bkPointSourceIsoOf E j).inv ≫
    simplicialDiagonalFunctor.map (bkPointOuterMapOf E j)

@[simp]
theorem bkPointInclusionOf_app_mk (E : J ⥤ SSet.{max u v w})
    (j : J) (n : ℕ) :
    (bkPointInclusionOf E j).app (op ⦋n⦌) =
      (bkPointOuterComponentOf E j n).app (op ⦋n⦌) := by
  unfold bkPointInclusionOf bkPointSourceIsoOf
  dsimp only [diagonalConstIso]
  simp only [NatTrans.comp_app, Iso.trans_inv, Functor.mapIso_inv,
    simplicialDiagonalFunctor_map_app, bkPointOuterMapOf_app_mk,
    SimplicialObject.Data.constDataIso_inv_app,
    CategoryTheory.SimplicialObject.diagonalConstIso_inv_app]
  change (𝟙 _ ≫ 𝟙 _) ≫ _ = _
  simp


end SSet
