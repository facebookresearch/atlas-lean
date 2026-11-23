/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.ExUnit
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SubdivisionAnodyne
import
  MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.AnchoredNormalForm
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Connected

/-!
# The explicit infinite Kan Ex construction

This file forms the natural-number tower of one-step Ex units, defines its
pointwise colimit functor and natural unit, proves the colimit Kan, and proves
that its unit is a realization weak equivalence in every universe.

## Mathematical source

The sequential `Ex` construction and the theorem that `Ex∞ X` is Kan follow
Goerss--Jardine, *Simplicial Homotopy Theory*, Chapter III, Section 4,
Theorem 4.8.  The private theorem `hornDoubleSubdivisionRetraction` below
formalizes the double-subdivision horn-extension step in that proof: applying
double subdivision to the horn inclusion and then the constructed retraction
is exactly subdivision of the last-vertex map.  Transporting this strict
equation twice through the subdivision--`Ex` adjunction promotes a horn map
two stages up the tower with an exact boundary equation.

The realization-weak-equivalence theorem for the unit uses the separately
proved one-step weak unit and stability under sequential monomorphism
colimits; that part is not attributed to Theorem III.4.8.

The finite-stage readouts below retain the same finite iterates and colimit
legs. Finite-source factorization uses the original finitely presentable
factorization through the large-universe reindex of this tower.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open PartialOrder
open scoped Simplicial

universe u

namespace SSet

/-- The finite iterates of the one-step Ex functor. -/
private noncomputable abbrev exIter : ℕ → SSet.{u} ⥤ SSet.{u} := fun n =>
  Nat.rec (Functor.id _) (fun _ F => F ⋙ SSet.ex) n

/-- The sequence `X -> Ex X -> Ex² X -> ...`. -/
private noncomputable abbrev exTower (X : SSet.{u}) : ℕ ⥤ SSet.{u} :=
  Functor.ofSequence
    (fun n => SSet.exUnit.app ((exIter n).obj X))

private theorem exTower_map_succ (X : SSet.{u}) (n : ℕ) :
    (exTower X).map (homOfLE (n.le_add_right 1)) =
      SSet.exUnit.app ((exIter n).obj X) := by
  unfold exTower
  exact Functor.ofSequence_map_homOfLE_succ _ n

private theorem exIter_succ_map {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    (exIter (n + 1)).map f =
      SSet.ex.map ((exIter n).map f) := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of every finite Ex iterate packages the tower objectwise into
a functor to sequential diagrams. -/
private noncomputable abbrev exTowerFunctor :
    SSet.{u} ⥤ (ℕ ⥤ SSet.{u}) where
  obj X := exTower X
  map {X Y} f := NatTrans.ofSequence
    (fun n => (exIter n).map f)
    (fun n => by
      rw [exTower_map_succ, exTower_map_succ, exIter_succ_map]
      simpa only [Functor.id_map] using
        (SSet.exUnit.naturality ((exIter n).map f)).symm)
  map_id X := by
    apply NatTrans.ext
    funext n
    change (exIter n).map (𝟙 X) = 𝟙 ((exIter n).obj X)
    exact (exIter n).map_id X
  map_comp {X Y Z} f g := by
    apply NatTrans.ext
    funext n
    change (exIter n).map (f ≫ g) =
      (exIter n).map f ≫ (exIter n).map g
    exact (exIter n).map_comp f g

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit infinite Ex construction, as the colimit of its finite
iterate tower. -/
noncomputable def exInfinity : SSet.{u} ⥤ SSet.{u} := by
  let iter : ℕ → SSet.{u} ⥤ SSet.{u} := fun n =>
    Nat.rec (𝟭 _) (fun _ F => F ⋙ SSet.ex) n
  let tower : SSet.{u} → (ℕ ⥤ SSet.{u}) := fun X =>
    Functor.ofSequence
      (fun n => SSet.exUnit.app ((iter n).obj X))
  have iter_succ_map {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
      (iter (n + 1)).map f =
        SSet.ex.map ((iter n).map f) := by
    rfl
  have tower_map_succ (X : SSet.{u}) (n : ℕ) :
      (tower X).map (homOfLE (n.le_add_right 1)) =
        SSet.exUnit.app ((iter n).obj X) := by
    exact Functor.ofSequence_map_homOfLE_succ _ n
  let towerMap {X Y : SSet.{u}} (f : X ⟶ Y) :
      tower X ⟶ tower Y :=
    NatTrans.ofSequence
      (fun n => (iter n).map f)
      (fun n => by
        rw [tower_map_succ, tower_map_succ, iter_succ_map]
        simpa only [Functor.id_map] using
          (SSet.exUnit.naturality ((iter n).map f)).symm)
  let towerFunctor : SSet.{u} ⥤ (ℕ ⥤ SSet.{u}) :=
    { obj := tower
      map := towerMap
      map_id := fun X => by
        apply NatTrans.ext
        funext n
        change (iter n).map (𝟙 X) = 𝟙 ((iter n).obj X)
        exact (iter n).map_id X
      map_comp := fun {X Y Z} f g => by
        apply NatTrans.ext
        funext n
        change (iter n).map (f ≫ g) =
          (iter n).map f ≫ (iter n).map g
        exact (iter n).map_comp f g }
  exact towerFunctor ⋙ Limits.colim

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural inclusion of a simplicial set into its infinite Ex tower. -/
noncomputable def exInfinityUnit :
    𝟭 (SSet.{u}) ⟶ exInfinity := by
  let iter : ℕ → SSet.{u} ⥤ SSet.{u} := fun n =>
    Nat.rec (𝟭 _) (fun _ F => F ⋙ SSet.ex) n
  let tower : SSet.{u} → (ℕ ⥤ SSet.{u}) := fun X =>
    Functor.ofSequence
      (fun n => SSet.exUnit.app ((iter n).obj X))
  have iter_succ_map {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
      (iter (n + 1)).map f =
        SSet.ex.map ((iter n).map f) := by
    rfl
  have tower_map_succ (X : SSet.{u}) (n : ℕ) :
      (tower X).map (homOfLE (n.le_add_right 1)) =
        SSet.exUnit.app ((iter n).obj X) := by
    exact Functor.ofSequence_map_homOfLE_succ _ n
  let towerMap {X Y : SSet.{u}} (f : X ⟶ Y) :
      tower X ⟶ tower Y :=
    NatTrans.ofSequence
      (fun n => (iter n).map f)
      (fun n => by
        rw [tower_map_succ, tower_map_succ, iter_succ_map]
        simpa only [Functor.id_map] using
          (SSet.exUnit.naturality ((iter n).map f)).symm)
  let towerFunctor : SSet.{u} ⥤ (ℕ ⥤ SSet.{u}) :=
    { obj := tower
      map := towerMap
      map_id := fun X => by
        apply NatTrans.ext
        funext n
        change (iter n).map (𝟙 X) = 𝟙 ((iter n).obj X)
        exact (iter n).map_id X
      map_comp := fun {X Y Z} f g => by
        apply NatTrans.ext
        funext n
        change (iter n).map (f ≫ g) =
          (iter n).map f ≫ (iter n).map g
        exact (iter n).map_comp f g }
  let zeroHom (X : SSet.{u}) : X ⟶ (tower X).obj 0 :=
    eqToHom (by rfl)
  have zeroHom_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
      f ≫ zeroHom Y =
        zeroHom X ≫ (towerFunctor.map f).app 0 := by
    rfl
  change 𝟭 (SSet.{u}) ⟶ towerFunctor ⋙ Limits.colim
  refine
    { app := fun X => zeroHom X ≫ colimit.ι (tower X) 0
      naturality := fun {X Y} f => ?_ }
  let α := towerFunctor.map f
  calc
    (𝟭 (SSet.{u})).map f ≫
        (zeroHom Y ≫ colimit.ι (tower Y) 0) =
      (f ≫ zeroHom Y) ≫ colimit.ι (tower Y) 0 := by
        simp
    _ = (zeroHom X ≫ α.app 0) ≫
        colimit.ι (tower Y) 0 := by
      rw [zeroHom_naturality]
    _ = zeroHom X ≫
        (α.app 0 ≫ colimit.ι (tower Y) 0) := by
      rw [Category.assoc]
    _ = zeroHom X ≫
        (colimit.ι (tower X) 0 ≫ colimMap α) := by
      rw [Limits.ι_colimMap]
    _ = (zeroHom X ≫ colimit.ι (tower X) 0) ≫
        (towerFunctor ⋙ Limits.colim).map f := by
      dsimp only [Functor.comp_map]
      rw [Category.assoc]
      rfl

private theorem exInfinity_eq_towerFunctor :
    exInfinity.{u} = exTowerFunctor.{u} ⋙ Limits.colim := by
  unfold exInfinity exTowerFunctor exTower
  rfl

/-- The original finite Ex iterate at stage `n` of the infinite Ex tower. -/
@[no_expose]
noncomputable def exInfinityStageFunctor (n : ℕ) : SSet.{u} ⥤ SSet.{u} :=
  exIter n

/-- Stage zero of the original tower is the identity functor. -/
theorem exInfinityStageFunctor_zero :
    exInfinityStageFunctor.{u} 0 = 𝟭 _ := by
  unfold exInfinityStageFunctor exIter
  rfl

/-- The original successor stage applies one further Ex functor. -/
theorem exInfinityStageFunctor_succ (n : ℕ) :
    exInfinityStageFunctor.{u} (n + 1) = exInfinityStageFunctor n ⋙ ex := by
  unfold exInfinityStageFunctor exIter
  rfl

/-- The original stage-zero object is the original simplicial source. -/
theorem exInfinityStageFunctor_obj_zero (X : SSet.{u}) :
    (exInfinityStageFunctor 0).obj X = X :=
  congrArg (fun F : SSet.{u} ⥤ SSet.{u} => F.obj X) exInfinityStageFunctor_zero

/-- The successor object is the one-step Ex of the original previous stage. -/
theorem exInfinityStageFunctor_obj_succ (X : SSet.{u}) (n : ℕ) :
    (exInfinityStageFunctor (n + 1)).obj X =
      ex.obj ((exInfinityStageFunctor n).obj X) :=
  congrArg (fun F : SSet.{u} ⥤ SSet.{u} => F.obj X)
    (exInfinityStageFunctor_succ n)

/-- The original colimit leg from the finite Ex stage into `Ex∞ X`. -/
@[no_expose]
noncomputable def exInfinityStageι (X : SSet.{u}) (n : ℕ) :
    (exInfinityStageFunctor n).obj X ⟶ exInfinity.obj X := by
  unfold exInfinityStageFunctor
  change (exIter n).obj X ⟶ colimit (exTower X)
  exact colimit.ι (exTower X) n

/-- Consecutive original colimit legs commute with the one-step Ex unit. -/
theorem exInfinityStageι_succ (X : SSet.{u}) (n : ℕ) :
    exUnit.app ((exInfinityStageFunctor n).obj X) ≫
      eqToHom (exInfinityStageFunctor_obj_succ X n).symm ≫
      exInfinityStageι X (n + 1) = exInfinityStageι X n := by
  unfold exInfinityStageFunctor exInfinityStageι
  let iNext : (exIter (n + 1)).obj X ⟶ colimit (exTower X) :=
    colimit.ι (exTower X) (n + 1)
  let iOld : (exIter n).obj X ⟶ colimit (exTower X) := colimit.ι (exTower X) n
  have hStep : exUnit.app ((exIter n).obj X) ≫ iNext = iOld := by
    have h := colimit.w (exTower X) (homOfLE (n.le_add_right 1))
    rw [exTower_map_succ] at h
    exact h
  change exUnit.app ((exIter n).obj X) ≫ 𝟙 ((exIter (n + 1)).obj X) ≫ iNext = iOld
  exact (congrArg (fun k : (exIter (n + 1)).obj X ⟶ colimit (exTower X) =>
    exUnit.app ((exIter n).obj X) ≫ k) (Category.id_comp iNext)).trans hStep

private noncomputable abbrev exSmallTower (X : SSet.{u}) :
    CategoryTheory.AsSmall.{u} ℕ ⥤ SSet.{u} :=
  CategoryTheory.AsSmall.down ⋙ exTower X

private theorem exSmallDown_final :
    (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).Final := by
  let _ : (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).IsRightAdjoint :=
    (CategoryTheory.AsSmall.equiv.{0, 0, u}
      (C := ℕ)).isRightAdjoint_inverse
  infer_instance

private noncomputable def exTowerColimitIso (X : SSet.{u}) :
    colimit (exSmallTower X) ≅ colimit (exTower X) := by
  let _ : (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).Final := exSmallDown_final
  exact Functor.Final.colimitIso CategoryTheory.AsSmall.down (exTower X)

set_option backward.isDefEq.respectTransparency false in
private theorem exTowerColimitIso_hom_ι (X : SSet.{u})
    (j : CategoryTheory.AsSmall.{u} ℕ) :
    colimit.ι (exSmallTower X) j ≫ (exTowerColimitIso X).hom =
      colimit.ι (exTower X) (CategoryTheory.AsSmall.down.obj j) := by
  let _ : (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).Final := exSmallDown_final
  unfold exTowerColimitIso
  exact Functor.Final.ι_colimitIso_hom
    CategoryTheory.AsSmall.down (exTower X) j

private theorem exists_exTower_factor
    (X K : SSet.{u}) [K.Finite]
    (f : K ⟶ exInfinity.obj X) :
    ∃ (j : CategoryTheory.AsSmall.{u} ℕ)
      (p : K ⟶ (exTower X).obj
        (CategoryTheory.AsSmall.down.obj j)),
        p ≫ colimit.ι (exTower X)
          (CategoryTheory.AsSmall.down.obj j) = f := by
  change K ⟶ colimit (exTower X) at f
  let _ : (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).Final := exSmallDown_final
  let e := exTowerColimitIso X
  obtain ⟨j, p, hp⟩ :=
    IsFinitelyPresentable.exists_hom_of_isColimit
      (X := K) (colimit.isColimit (exSmallTower X)) (f ≫ e.inv)
  refine ⟨j, p, ?_⟩
  have hp' : p ≫ colimit.ι (exSmallTower X) j = f ≫ e.inv := hp
  calc
    p ≫ colimit.ι (exTower X)
        (CategoryTheory.AsSmall.down.obj j) =
        p ≫ colimit.ι (exSmallTower X) j ≫ e.hom := by
      rw [exTowerColimitIso_hom_ι]
    _ = (p ≫ colimit.ι (exSmallTower X) j) ≫ e.hom := by
      rw [Category.assoc]
    _ = (f ≫ e.inv) ≫ e.hom := by rw [hp']
    _ = f := by simp

/-- Every map from a finite simplicial set into `Ex∞ X` factors through an
original finite stage, with its original colimit leg as the comparison. -/
theorem exists_exInfinity_stage_factor (X K : SSet.{u}) [K.Finite]
    (f : K ⟶ exInfinity.obj X) :
    ∃ (n : ℕ) (p : K ⟶ (exInfinityStageFunctor n).obj X),
      p ≫ exInfinityStageι X n = f := by
  unfold exInfinityStageFunctor exInfinityStageι
  obtain ⟨j, p, hp⟩ := exists_exTower_factor X K f
  refine ⟨CategoryTheory.AsSmall.down.obj j, p, ?_⟩
  change p ≫ colimit.ι (exTower X) (CategoryTheory.AsSmall.down.obj j) = f
  exact hp

private theorem exists_exTower_later_eq
    (X K : SSet.{u}) [K.Finite]
    {i j : CategoryTheory.AsSmall.{u} ℕ}
    (f : K ⟶ (exTower X).obj
      (CategoryTheory.AsSmall.down.obj i))
    (g : K ⟶ (exTower X).obj
      (CategoryTheory.AsSmall.down.obj j))
    (h : f ≫ colimit.ι (exTower X)
        (CategoryTheory.AsSmall.down.obj i) =
      g ≫ colimit.ι (exTower X)
        (CategoryTheory.AsSmall.down.obj j)) :
    ∃ (k : CategoryTheory.AsSmall.{u} ℕ) (a : i ⟶ k) (b : j ⟶ k),
      f ≫ (exTower X).map (CategoryTheory.AsSmall.down.map a) =
        g ≫ (exTower X).map (CategoryTheory.AsSmall.down.map b) := by
  let _ : (CategoryTheory.AsSmall.down :
      CategoryTheory.AsSmall.{u} ℕ ⥤ ℕ).Final := exSmallDown_final
  let e := exTowerColimitIso X
  have hsmall :
      f ≫ colimit.ι (exSmallTower X) i =
        g ≫ colimit.ι (exSmallTower X) j := by
    apply (cancel_mono e.hom).mp
    calc
      (f ≫ colimit.ι (exSmallTower X) i) ≫ e.hom =
          f ≫ colimit.ι (exTower X)
            (CategoryTheory.AsSmall.down.obj i) := by
        rw [Category.assoc, exTowerColimitIso_hom_ι]
      _ = g ≫ colimit.ι (exTower X)
          (CategoryTheory.AsSmall.down.obj j) := h
      _ = (g ≫ colimit.ι (exSmallTower X) j) ≫ e.hom := by
        rw [Category.assoc, exTowerColimitIso_hom_ι]
  obtain ⟨k, a, b, hab⟩ :=
    IsFinitelyPresentable.exists_eq_of_isColimit
      (X := K) (colimit.isColimit (exSmallTower X)) f g hsmall
  exact ⟨k, a, b, hab⟩


attribute [local instance] Classical.propDecidable

private abbrev Vertex (n : ℕ) : Type u := ULift.{u} (Fin (n + 2))

private abbrev Face (n : ℕ) := NonemptyFiniteChains (Vertex.{u} n)

private def distinguished {n : ℕ} (i : Fin (n + 2)) : Vertex.{u} n :=
  ULift.up i

private def missingFace {n : ℕ} (i : Fin (n + 2)) :
    Finset (Vertex.{u} n) :=
  Finset.univ.erase (distinguished.{u} i)

private def Allowed {n : ℕ} (i : Fin (n + 2)) (S : Face.{u} n) : Prop :=
  ¬missingFace.{u} i ⊆ S.finset

private abbrev H {n : ℕ} (i : Fin (n + 2)) :=
  {S : Face.{u} n // Allowed.{u} i S}

private def jH {n : ℕ} (i : Fin (n + 2)) : H.{u} i ↪o Face.{u} n :=
  OrderEmbedding.subtype _

private def specialMax {n : ℕ} (i : Fin (n + 2))
    (S : Face.{u} n) : Vertex.{u} n :=
  if missingFace.{u} i ⊆ S.finset then distinguished.{u} i
  else S.finset.max' S.nonempty

private theorem missingFace_nonempty {n : ℕ} (i : Fin (n + 2)) :
    (missingFace.{u} i).Nonempty := by
  obtain ⟨j, hji⟩ : ∃ j : Fin (n + 2), j ≠ i := by
    by_cases hi : i = 0
    · refine ⟨1, ?_⟩
      simp [hi]
    · exact ⟨0, fun h ↦ hi h.symm⟩
  exact ⟨ULift.up j, by simp [missingFace, distinguished, hji]⟩

private def retractedFace {n : ℕ} (i : Fin (n + 2))
    (C : NonemptyFiniteChains (Face.{u} n)) : Face.{u} n where
  finset := C.finset.image (specialMax.{u} i)
  nonempty := C.nonempty.image _
  comparable _ _ := le_total _ _

private theorem retractedFace_allowed {n : ℕ} (i : Fin (n + 2))
    (C : NonemptyFiniteChains (Face.{u} n)) :
    Allowed.{u} i (retractedFace.{u} i C) := by
  intro hmissing
  let j : Vertex.{u} n :=
    (missingFace.{u} i).max' (missingFace_nonempty.{u} i)
  have hjmem : j ∈ missingFace.{u} i :=
    Finset.max'_mem _ (missingFace_nonempty.{u} i)
  have hjne : j ≠ distinguished.{u} i := by
    simpa [j, missingFace] using (Finset.mem_erase.mp hjmem).1
  have hjimage : j ∈ (retractedFace.{u} i C).finset := hmissing hjmem
  change j ∈ C.finset.image (specialMax.{u} i) at hjimage
  obtain ⟨S, hSC, hSj⟩ := Finset.mem_image.mp hjimage
  have hSnot : ¬ missingFace.{u} i ⊆ S.finset := by
    intro hS
    have : specialMax.{u} i S = distinguished.{u} i := by
      simp [specialMax, hS]
    exact hjne (hSj.symm.trans this)
  have hSmax : S.finset.max' S.nonempty = j := by
    simpa [specialMax, hSnot] using hSj
  apply hSnot
  intro k hk
  have hkimage : k ∈ (retractedFace.{u} i C).finset := hmissing hk
  change k ∈ C.finset.image (specialMax.{u} i) at hkimage
  obtain ⟨T, hTC, hTk⟩ := Finset.mem_image.mp hkimage
  have hkne : k ≠ distinguished.{u} i := by
    simpa [missingFace] using (Finset.mem_erase.mp hk).1
  have hTnot : ¬ missingFace.{u} i ⊆ T.finset := by
    intro hT
    have : specialMax.{u} i T = distinguished.{u} i := by
      simp [specialMax, hT]
    exact hkne (hTk.symm.trans this)
  have hTmax : T.finset.max' T.nonempty = k := by
    simpa [specialMax, hTnot] using hTk
  rcases C.comparable ⟨S, hSC⟩ ⟨T, hTC⟩ with hST | hTS
  · have hjk : j ≤ k := by
      rw [← hSmax, ← hTmax]
      exact Finset.max'_subset S.nonempty hST
    have hkj : k ≤ j := Finset.le_max' _ _ hk
    have hkjEq : k = j := le_antisymm hkj hjk
    rw [hkjEq, ← hSmax]
    exact Finset.max'_mem S.finset S.nonempty
  · have hkT : k ∈ T.finset := by
      rw [← hTmax]
      exact Finset.max'_mem T.finset T.nonempty
    exact hTS hkT

private def retractOrderHom {n : ℕ} (i : Fin (n + 2)) :
    NonemptyFiniteChains (Face.{u} n) →o H.{u} i where
  toFun C := ⟨retractedFace.{u} i C, retractedFace_allowed.{u} i C⟩
  monotone' C D h := by
    intro v hv
    change v ∈ C.finset.image (specialMax.{u} i) at hv
    change v ∈ D.finset.image (specialMax.{u} i)
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨S, h hS, rfl⟩

private def hornLastOrderHom {n : ℕ} (i : Fin (n + 2)) :
    H.{u} i →o Vertex.{u} n where
  toFun S := S.1.finset.max' S.1.nonempty
  monotone' S _T h := Finset.max'_subset S.1.nonempty h

private def faceLastOrderHom (n : ℕ) : Face.{u} n →o Vertex.{u} n where
  toFun S := S.finset.max' S.nonempty
  monotone' S _T h := Finset.max'_subset S.nonempty h

private theorem specialMax_allowed {n : ℕ} (i : Fin (n + 2))
    (S : H.{u} i) :
    specialMax.{u} i S.1 = hornLastOrderHom.{u} i S := by
  change specialMax.{u} i S.1 = S.1.finset.max' S.1.nonempty
  have hS : ¬ missingFace.{u} i ⊆ S.1.finset := S.2
  rw [specialMax, ite_eq_right hS]

private theorem retractedFace_map_jH {n : ℕ} (i : Fin (n + 2))
    (C : NonemptyFiniteChains (H.{u} i)) :
    retractedFace.{u} i (C.map (jH.{u} i).toOrderHom) =
      C.map (hornLastOrderHom.{u} i) := by
  apply NonemptyFiniteChains.ext
  ext v
  change v ∈ (C.map (jH.{u} i).toOrderHom).finset.image
      (specialMax.{u} i) ↔
    v ∈ (C.map (hornLastOrderHom.{u} i)).finset
  rw [Finset.mem_image, NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨S, hS, hSv⟩
    obtain ⟨T, hT, hTS⟩ :=
      (NonemptyFiniteChains.mem_map_iff C (jH.{u} i).toOrderHom S).1 hS
    subst S
    exact ⟨T, hT, (specialMax_allowed i T).symm.trans hSv⟩
  · rintro ⟨T, hT, hTv⟩
    refine ⟨T.1, ?_, (specialMax_allowed i T).trans hTv⟩
    exact (NonemptyFiniteChains.mem_map_iff
      C (jH.{u} i).toOrderHom T.1).2 ⟨T, hT, rfl⟩

private def hornLastFace {n : ℕ} (i : Fin (n + 2))
    (C : NonemptyFiniteChains (H.{u} i)) : H.{u} i :=
  ⟨C.map (hornLastOrderHom.{u} i), by
    rw [← retractedFace_map_jH i C]
    exact retractedFace_allowed.{u} i
      (C.map (jH.{u} i).toOrderHom)⟩

private theorem retract_map_jH {n : ℕ} (i : Fin (n + 2))
    (C : NonemptyFiniteChains (H.{u} i)) :
    (retractOrderHom.{u} i)
        (C.map (jH.{u} i).toOrderHom) = hornLastFace.{u} i C := by
  apply Subtype.ext
  exact retractedFace_map_jH i C

private theorem map_jH_last {n : ℕ} (i : Fin (n + 2))
    (C : NonemptyFiniteChains (H.{u} i)) :
    (C.map (jH.{u} i).toOrderHom).map
        (SimplexCategory.sdLastVertexOrderHom ⦋n + 1⦌) =
      C.map (hornLastOrderHom.{u} i) := by
  apply NonemptyFiniteChains.ext
  ext v
  simp only [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨S, ⟨T, hT, rfl⟩, rfl⟩
    exact ⟨T, hT, rfl⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T.1, ⟨T, hT, rfl⟩, rfl⟩

private theorem map_jH_faceLast {n : ℕ} (i : Fin (n + 2))
    (C : NonemptyFiniteChains (H.{u} i)) :
    (C.map (jH.{u} i).toOrderHom).map (faceLastOrderHom.{u} n) =
      C.map (hornLastOrderHom.{u} i) := by
  apply NonemptyFiniteChains.ext
  ext v
  simp only [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨S, ⟨T, hT, rfl⟩, rfl⟩
    exact ⟨T, hT, rfl⟩
  · rintro ⟨T, hT, rfl⟩
    exact ⟨T.1, ⟨T, hT, rfl⟩, rfl⟩

private def jHOrd {n : ℕ} (i : Fin (n + 2)) :
    PartOrd.of (H.{u} i) ⟶ PartOrd.of (Face.{u} n) :=
  PartOrd.ofHom (jH.{u} i).toOrderHom

private noncomputable def faceOrderIso (n : ℕ) :
    (Δ[n + 1] : SSet.{u}).N ≃o Face.{u} n :=
  (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} (n + 1))).trans
    (PartOrd.nerveNOrderIso (PartOrd.of (Vertex.{u} n)))

private theorem mem_faceOrderIso_finset {n : ℕ}
    (x : (Δ[n + 1] : SSet.{u}).N) (v : Vertex.{u} n) :
    v ∈ (faceOrderIso.{u} n x).finset ↔
      ∃ j, ULift.up (x.simplex j) = v := by
  rw [faceOrderIso, OrderIso.trans_apply,
    PartOrd.mem_nerveNOrderIso_finset]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    change ((SSet.stdSimplex.isoNerve.{u} (n + 1)).hom.app _
      x.simplex).obj j = v at hj
    exact (SSet.stdSimplex.isoNerve_hom_app_apply x.simplex j).symm.trans hj
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_⟩
    change ((SSet.stdSimplex.isoNerve.{u} (n + 1)).hom.app _
      x.simplex).obj j = ULift.up (x.simplex j)
    exact SSet.stdSimplex.isoNerve_hom_app_apply _ _

private noncomputable def faceFinset {n : ℕ}
    (x : (Δ[n + 1] : SSet.{u}).N) : Finset (Fin (n + 2)) :=
  (faceOrderIso.{u} n x).finset.image ULift.down

private theorem mem_faceFinset_iff {n : ℕ}
    (x : (Δ[n + 1] : SSet.{u}).N) (v : Fin (n + 2)) :
    v ∈ faceFinset.{u} x ↔ ∃ j, x.simplex j = v := by
  classical
  rw [faceFinset, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨j, hj⟩ := (mem_faceOrderIso_finset x w).1 hw
    exact ⟨j, ULift.up_injective hj⟩
  · rintro ⟨j, rfl⟩
    exact ⟨ULift.up (x.simplex j),
      (mem_faceOrderIso_finset x _).2 ⟨j, rfl⟩, rfl⟩

private theorem faceFinset_eq_nonDegenerateEquiv {n : ℕ}
    (x : (Δ[n + 1] : SSet.{u}).N) :
    faceFinset.{u} x =
      (SSet.stdSimplex.nonDegenerateEquiv'
        ⟨x.simplex, x.nonDegenerate⟩).val := by
  classical
  ext v
  rw [mem_faceFinset_iff,
    SSet.stdSimplex.nonDegenerateEquiv'_iff]

private theorem mem_down_image_iff {n : ℕ} (S : Face.{u} n)
    (v : Fin (n + 2)) :
    v ∈ S.finset.image ULift.down ↔ ULift.up v ∈ S.finset := by
  classical
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hwv⟩
    have : w = ULift.up v := by
      apply ULift.down_injective
      simpa using hwv
    simpa [this] using hw
  · intro hv
    exact ⟨ULift.up v, hv, rfl⟩

private theorem missing_subset_iff {n : ℕ} (i : Fin (n + 2))
    (S : Face.{u} n) :
    missingFace.{u} i ⊆ S.finset ↔
      Finset.univ.erase i ⊆ S.finset.image ULift.down := by
  classical
  constructor
  · intro h v hv
    rw [mem_down_image_iff]
    apply h
    simpa [missingFace, distinguished] using hv
  · intro h v hv
    have hv0 : v ≠ ULift.up i := by
      rw [missingFace, distinguished, Finset.mem_erase] at hv
      exact hv.1
    have hv' : v.down ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hvi
      apply hv0
      apply ULift.down_injective
      simpa using hvi
    have := h hv'
    rw [mem_down_image_iff] at this
    simpa using this

private theorem erase_subset_iff_eq {n : ℕ} (i : Fin (n + 2))
    (D : Finset (Fin (n + 2))) :
    Finset.univ.erase i ⊆ D ↔
      D = Finset.univ.erase i ∨ D = Finset.univ := by
  classical
  constructor
  · intro h
    by_cases hi : i ∈ D
    · right
      apply Finset.eq_univ_of_forall
      intro v
      by_cases hvi : v = i
      · simpa [hvi] using hi
      · exact h (by simp [hvi])
    · left
      apply Finset.Subset.antisymm
      · intro v hv
        have hvi : v ≠ i := by
          rintro rfl
          exact hi hv
        simp [hvi]
      · exact h
  · rintro (rfl | rfl)
    · exact fun _ h ↦ h
    · exact Finset.subset_univ _

private theorem allowed_iff {n : ℕ} (i : Fin (n + 2))
    (S : Face.{u} n) :
    Allowed.{u} i S ↔
      S.finset.image ULift.down ≠ Finset.univ ∧
        S.finset.image ULift.down ≠ {i}ᶜ := by
  classical
  have hcompl : ({i}ᶜ : Finset (Fin (n + 2))) =
      Finset.univ.erase i := by
    ext v
    simp
  rw [Allowed, missing_subset_iff, erase_subset_iff_eq, not_or]
  constructor
  · rintro ⟨hC, hU⟩
    exact ⟨hU, by simpa [hcompl] using hC⟩
  · rintro ⟨hU, hC⟩
    exact ⟨by simpa [hcompl] using hC, hU⟩

private theorem allowed_faceOrderIso_iff {n : ℕ} (i : Fin (n + 2))
    (x : (Δ[n + 1] : SSet.{u}).N) :
    Allowed.{u} i (faceOrderIso.{u} n x) ↔
      x.simplex ∈ (SSet.horn.{u} (n + 1) i).obj _ := by
  rw [allowed_iff]
  change faceFinset.{u} x ≠ Finset.univ ∧
      faceFinset.{u} x ≠ {i}ᶜ ↔ _
  rw [faceFinset_eq_nonDegenerateEquiv,
    ← SSet.face_le_horn_iff,
    SSet.stdSimplex.face_nonDegenerateEquiv',
    SSet.Subcomplex.ofSimplex_le_iff]

private theorem N_map_le_iff_of_mono {X Y : SSet.{u}}
    (f : X ⟶ Y) [Mono f] (x y : X.N) :
    SSet.N.map f x ≤ SSet.N.map f y ↔ x ≤ y := by
  rw [SSet.N.le_iff, SSet.N.le_iff,
    SSet.N.map_subcomplex, SSet.N.map_subcomplex,
    SSet.Subcomplex.image_le_image_iff]

private noncomputable def hornFaceOrderEmbedding {n : ℕ}
    (i : Fin (n + 2)) :
    (SSet.horn.{u} (n + 1) i : SSet.{u}).N ↪o H.{u} i where
  toFun x :=
    ⟨faceOrderIso.{u} n
      (SSet.N.map (SSet.horn.{u} (n + 1) i).ι x), by
      rw [allowed_faceOrderIso_iff]
      have hnon :
          (SSet.horn.{u} (n + 1) i).ι.app _ x.simplex ∈
            (Δ[n + 1] : SSet.{u}).nonDegenerate x.dim :=
        (SSet.nonDegenerate_iff_of_mono
          (SSet.horn.{u} (n + 1) i).ι x.simplex).2 x.nonDegenerate
      rw [SSet.N.map_eq_mk _ _ hnon]
      exact x.simplex.property⟩
  inj' x y hxy := by
    have hmap :
        SSet.N.map (SSet.horn.{u} (n + 1) i).ι x =
          SSet.N.map (SSet.horn.{u} (n + 1) i).ι y := by
      apply (faceOrderIso.{u} n).injective
      exact congrArg Subtype.val hxy
    apply le_antisymm
    · exact (N_map_le_iff_of_mono _ _ _).1 hmap.le
    · exact (N_map_le_iff_of_mono _ _ _).1 hmap.ge
  map_rel_iff' {x y} := by
    change faceOrderIso.{u} n
        (SSet.N.map (SSet.horn.{u} (n + 1) i).ι x) ≤
      faceOrderIso.{u} n
        (SSet.N.map (SSet.horn.{u} (n + 1) i).ι y) ↔ x ≤ y
    rw [(faceOrderIso.{u} n).le_iff_le,
      N_map_le_iff_of_mono]

private theorem hornFaceOrderEmbedding_surjective {n : ℕ}
    (i : Fin (n + 2)) :
    Function.Surjective (hornFaceOrderEmbedding.{u} i) := by
  intro S
  let y : (Δ[n + 1] : SSet.{u}).N :=
    (faceOrderIso.{u} n).symm S.1
  have hyMem : y.simplex ∈ (SSet.horn.{u} (n + 1) i).obj _ := by
    rw [← allowed_faceOrderIso_iff]
    simpa [y] using S.2
  let xs : (SSet.horn.{u} (n + 1) i).obj _ := ⟨y.simplex, hyMem⟩
  have hxnon : xs ∈
      (SSet.horn.{u} (n + 1) i : SSet.{u}).nonDegenerate y.dim :=
    (SSet.Subcomplex.mem_nonDegenerate_iff _ _).2 y.nonDegenerate
  let x : (SSet.horn.{u} (n + 1) i : SSet.{u}).N :=
    SSet.N.mk xs hxnon
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change faceOrderIso.{u} n
      (SSet.N.map (SSet.horn.{u} (n + 1) i).ι x) = S.1
  rw [show S.1 = faceOrderIso.{u} n y by simp [y]]
  congr 1
  have hnon :
      (SSet.horn.{u} (n + 1) i).ι.app _ x.simplex ∈
        (Δ[n + 1] : SSet.{u}).nonDegenerate x.dim :=
    (SSet.nonDegenerate_iff_of_mono
      (SSet.horn.{u} (n + 1) i).ι x.simplex).2 x.nonDegenerate
  rw [SSet.N.map_eq_mk _ _ hnon, SSet.N.ext_iff]
  rfl

private noncomputable def hornFaceOrderIso {n : ℕ}
    (i : Fin (n + 2)) :
    (SSet.horn.{u} (n + 1) i : SSet.{u}).N ≃o H.{u} i :=
  OrderIso.ofSurjective (hornFaceOrderEmbedding.{u} i)
    (hornFaceOrderEmbedding_surjective.{u} i)

private theorem hornFaceOrderIso_hom_comp_jHOrd {n : ℕ}
    (i : Fin (n + 2)) :
    (PartOrd.Iso.mk (hornFaceOrderIso.{u} i)).hom ≫ jHOrd.{u} i =
      SSet.N.functor.map (SSet.horn.{u} (n + 1) i).ι ≫
        (PartOrd.Iso.mk (faceOrderIso.{u} n)).hom := by
  apply PartOrd.ext
  intro x
  rfl

private noncomputable def hornFacePartOrdIso {n : ℕ}
    (i : Fin (n + 2)) :
    SSet.N.functor.obj (SSet.horn.{u} (n + 1) i) ≅ PartOrd.of (H.{u} i) :=
  PartOrd.Iso.mk (hornFaceOrderIso.{u} i)

private noncomputable def facePartOrdIso (n : ℕ) :
    SSet.N.functor.obj (Δ[n + 1] : SSet.{u}) ≅
      PartOrd.of (Face.{u} n) :=
  PartOrd.Iso.mk (faceOrderIso.{u} n)

private theorem hornFacePartOrdIso_hom_comp_jHOrd {n : ℕ}
    (i : Fin (n + 2)) :
    (hornFacePartOrdIso.{u} i).hom ≫ jHOrd.{u} i =
      SSet.N.functor.map (SSet.horn.{u} (n + 1) i).ι ≫
        (facePartOrdIso.{u} n).hom :=
  hornFaceOrderIso_hom_comp_jHOrd i

private noncomputable def hornSdIso {n : ℕ} (i : Fin (n + 2)) :
    SSet.sd.obj (SSet.horn.{u} (n + 1) i) ≅
      CategoryTheory.nerve (H.{u} i) :=
  SSet.sdIsoNondegenerateNerve (SSet.horn.{u} (n + 1) i) ≪≫
    PartOrd.nerveFunctor.mapIso (hornFacePartOrdIso.{u} i)

private noncomputable def simplexSdIso (n : ℕ) :
    SSet.sd.obj (Δ[n + 1] : SSet.{u}) ≅
      CategoryTheory.nerve (Face.{u} n) :=
  SSet.sdIsoNondegenerateNerve (Δ[n + 1] : SSet.{u}) ≪≫
    PartOrd.nerveFunctor.mapIso (facePartOrdIso.{u} n)

set_option backward.isDefEq.respectTransparency false in
private theorem hornSdIso_hom {n : ℕ} (i : Fin (n + 2)) :
    (hornSdIso.{u} i).hom =
      SSet.sdToNondegenerateNerve.app (SSet.horn.{u} (n + 1) i) ≫
        PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom := by
  rw [hornSdIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [SSet.sdIsoNondegenerateNerve_hom]

set_option backward.isDefEq.respectTransparency false in
private theorem simplexSdIso_hom (n : ℕ) :
    (simplexSdIso.{u} n).hom =
      SSet.sdToNondegenerateNerve.app (Δ[n + 1] : SSet.{u}) ≫
        PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom := by
  rw [simplexSdIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [SSet.sdIsoNondegenerateNerve_hom]

set_option backward.isDefEq.respectTransparency false in
private theorem hornSdIso_hom_comp {n : ℕ} (i : Fin (n + 2)) :
    (hornSdIso.{u} i).hom ≫
        PartOrd.nerveFunctor.map (jHOrd.{u} i) =
      SSet.sd.map (SSet.horn.{u} (n + 1) i).ι ≫
        (simplexSdIso.{u} n).hom := by
  rw [hornSdIso_hom, simplexSdIso_hom]
  change (SSet.sdToNondegenerateNerve.app
      (SSet.horn.{u} (n + 1) i) ≫
        PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom) ≫
      PartOrd.nerveFunctor.map (jHOrd.{u} i) = _
  rw [Category.assoc, ← Functor.map_comp,
    hornFacePartOrdIso_hom_comp_jHOrd, Functor.map_comp]
  have hnat := SSet.sdToNondegenerateNerve.naturality
    (SSet.horn.{u} (n + 1) i).ι
  change SSet.sd.map (SSet.horn.{u} (n + 1) i).ι ≫
      SSet.sdToNondegenerateNerve.app (Δ[n + 1] : SSet.{u}) =
    SSet.sdToNondegenerateNerve.app (SSet.horn.{u} (n + 1) i) ≫
      PartOrd.nerveFunctor.map
        (SSet.N.functor.map (SSet.horn.{u} (n + 1) i).ι) at hnat
  calc
    SSet.sdToNondegenerateNerve.app (SSet.horn.{u} (n + 1) i) ≫
        PartOrd.nerveFunctor.map
          (SSet.N.functor.map (SSet.horn.{u} (n + 1) i).ι) ≫
        PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom =
      (SSet.sdToNondegenerateNerve.app (SSet.horn.{u} (n + 1) i) ≫
        PartOrd.nerveFunctor.map
          (SSet.N.functor.map (SSet.horn.{u} (n + 1) i).ι)) ≫
        PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom :=
      (Category.assoc _ _ _).symm
    _ = (SSet.sd.map (SSet.horn.{u} (n + 1) i).ι ≫
          SSet.sdToNondegenerateNerve.app (Δ[n + 1] : SSet.{u})) ≫
        PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom := by
      rw [hnat]
    _ = SSet.sd.map (SSet.horn.{u} (n + 1) i).ι ≫
        SSet.sdToNondegenerateNerve.app (Δ[n + 1] : SSet.{u}) ≫
          PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom :=
      Category.assoc _ _ _

private noncomputable def nerveSdIso (P : PartOrd.{u}) :
    SSet.sd.obj (PartOrd.nerveFunctor.obj P) ≅
      PartOrd.nerveFunctor.obj
        (PartOrd.nonemptyFiniteChainsFunctor.obj P) := by
  let _ : (PartOrd.nerveFunctor.obj P).Nonsingular := by
    change (CategoryTheory.nerve P).Nonsingular
    infer_instance
  exact SSet.sdIsoNondegenerateNerve (PartOrd.nerveFunctor.obj P) ≪≫
    PartOrd.nerveFunctor.mapIso
      (PartOrd.Iso.mk (PartOrd.nerveNOrderIso P))

set_option backward.isDefEq.respectTransparency false in
private theorem nerveSdIso_hom (P : PartOrd.{u}) :
    (nerveSdIso P).hom =
      SSet.sdToNondegenerateNerve.app (PartOrd.nerveFunctor.obj P) ≫
        PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk (PartOrd.nerveNOrderIso P)).hom := by
  rw [nerveSdIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [SSet.sdIsoNondegenerateNerve_hom]

set_option backward.isDefEq.respectTransparency false in
private theorem nerveSdIso_naturality {P Q : PartOrd.{u}} (f : P ⟶ Q) :
    (nerveSdIso P).hom ≫
        PartOrd.nerveFunctor.map
          (PartOrd.nonemptyFiniteChainsFunctor.map f) =
      SSet.sd.map (PartOrd.nerveFunctor.map f) ≫
        (nerveSdIso Q).hom := by
  rw [nerveSdIso_hom, nerveSdIso_hom]
  have hC0 := PartOrd.nerveFunctorCompNFunctorIso.{u}.hom.naturality f
  have hC := congrArg PartOrd.nerveFunctor.map hC0
  simp only [Functor.map_comp] at hC
  change SSet.nondegenerateNerve.map
      (PartOrd.nerveFunctor.map f) ≫
        PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk (PartOrd.nerveNOrderIso Q)).hom =
    PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk (PartOrd.nerveNOrderIso P)).hom ≫
      PartOrd.nerveFunctor.map
        (PartOrd.nonemptyFiniteChainsFunctor.map f) at hC
  calc
    (SSet.sdToNondegenerateNerve.app (PartOrd.nerveFunctor.obj P) ≫
        PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk (PartOrd.nerveNOrderIso P)).hom) ≫
      PartOrd.nerveFunctor.map
        (PartOrd.nonemptyFiniteChainsFunctor.map f) =
      SSet.sdToNondegenerateNerve.app (PartOrd.nerveFunctor.obj P) ≫
        (PartOrd.nerveFunctor.map
            (PartOrd.Iso.mk (PartOrd.nerveNOrderIso P)).hom ≫
          PartOrd.nerveFunctor.map
            (PartOrd.nonemptyFiniteChainsFunctor.map f)) :=
      Category.assoc _ _ _
    _ = SSet.sdToNondegenerateNerve.app (PartOrd.nerveFunctor.obj P) ≫
        (SSet.nondegenerateNerve.map
            (PartOrd.nerveFunctor.map f) ≫
          PartOrd.nerveFunctor.map
            (PartOrd.Iso.mk (PartOrd.nerveNOrderIso Q)).hom) := by
      rw [hC]
    _ = (SSet.sdToNondegenerateNerve.app (PartOrd.nerveFunctor.obj P) ≫
          SSet.nondegenerateNerve.map
            (PartOrd.nerveFunctor.map f)) ≫
        PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk (PartOrd.nerveNOrderIso Q)).hom :=
      (Category.assoc _ _ _).symm
    _ = (SSet.sd.map (PartOrd.nerveFunctor.map f) ≫
          SSet.sdToNondegenerateNerve.app
            (PartOrd.nerveFunctor.obj Q)) ≫
        PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk (PartOrd.nerveNOrderIso Q)).hom := by
      rw [SSet.sdToNondegenerateNerve.naturality]
    _ = SSet.sd.map (PartOrd.nerveFunctor.map f) ≫
        (SSet.sdToNondegenerateNerve.app
            (PartOrd.nerveFunctor.obj Q) ≫
          PartOrd.nerveFunctor.map
            (PartOrd.Iso.mk (PartOrd.nerveNOrderIso Q)).hom) :=
      Category.assoc _ _ _

private noncomputable def doubleSimplexChart (n : ℕ) :
    SSet.sd.obj (SSet.sd.obj (Δ[n + 1] : SSet.{u})) ≅
      PartOrd.nerveFunctor.obj
        (PartOrd.of (NonemptyFiniteChains (Face.{u} n))) :=
  SSet.sd.mapIso (simplexSdIso.{u} n) ≪≫
    nerveSdIso (PartOrd.of (Face.{u} n))

private noncomputable def doubleHornChart {n : ℕ} (i : Fin (n + 2)) :
    SSet.sd.obj (SSet.sd.obj (SSet.horn.{u} (n + 1) i)) ≅
      PartOrd.nerveFunctor.obj
        (PartOrd.of (NonemptyFiniteChains (H.{u} i))) :=
  SSet.sd.mapIso (hornSdIso.{u} i) ≪≫
    nerveSdIso (PartOrd.of (H.{u} i))

private noncomputable def hornDoubleSubdivisionRetraction
    (n : ℕ) (i : Fin (n + 2)) :
    SSet.sd.obj (SSet.sd.obj (Δ[n + 1] : SSet.{u})) ⟶
      SSet.sd.obj (SSet.horn.{u} (n + 1) i) :=
  (doubleSimplexChart.{u} n).hom ≫
    PartOrd.nerveFunctor.map
      (PartOrd.ofHom (retractOrderHom.{u} i)) ≫
    (hornSdIso.{u} i).inv

set_option backward.isDefEq.respectTransparency false in
private theorem doubleHornChart_hom_comp {n : ℕ} (i : Fin (n + 2)) :
    (doubleHornChart.{u} i).hom ≫
        PartOrd.nerveFunctor.map
          (PartOrd.nonemptyFiniteChainsFunctor.map (jHOrd.{u} i)) =
      SSet.sd.map (SSet.sd.map (SSet.horn.{u} (n + 1) i).ι) ≫
        (doubleSimplexChart.{u} n).hom := by
  change (SSet.sd.map (hornSdIso.{u} i).hom ≫
      (nerveSdIso (PartOrd.of (H.{u} i))).hom) ≫
        PartOrd.nerveFunctor.map
          (PartOrd.nonemptyFiniteChainsFunctor.map (jHOrd.{u} i)) = _
  rw [Category.assoc, nerveSdIso_naturality]
  rw [← Category.assoc, ← SSet.sd.map_comp]
  rw [hornSdIso_hom_comp]
  rw [SSet.sd.map_comp]
  rfl

private def hornLastFaceOrderHom {n : ℕ} (i : Fin (n + 2)) :
    PartOrd.of (NonemptyFiniteChains (H.{u} i)) ⟶ PartOrd.of (H.{u} i) :=
  PartOrd.nonemptyFiniteChainsFunctor.map (jHOrd.{u} i) ≫
    PartOrd.ofHom (retractOrderHom.{u} i)

private theorem hornLastFaceOrderHom_apply {n : ℕ} (i : Fin (n + 2))
    (C : NonemptyFiniteChains (H.{u} i)) :
    (hornLastFaceOrderHom.{u} i).hom C = hornLastFace.{u} i C := by
  exact retract_map_jH i C

private noncomputable abbrev GenericFace (q : SimplexCategory) :=
  NonemptyFiniteChains (ULift.{u} (Fin (q.len + 1)))

private noncomputable def directFaceOrderIso (q : SimplexCategory) :
    (SSet.stdSimplex.{u}.obj q).N ≃o GenericFace.{u} q :=
  (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} q.len)).trans
    (PartOrd.nerveNOrderIso (SimplexCategory.toPartOrd.obj q))

private noncomputable def flagFaceToN (q : SimplexCategory)
    (T : GenericFace.{u} q) : (SSet.stdSimplex.{u}.obj q).N :=
  (SSet.sdFlagCarrierChain q (ComposableArrows.mk₀ T)).obj 0

private noncomputable def nToFlagFace (q : SimplexCategory)
    (x : (SSet.stdSimplex.{u}.obj q).N) : GenericFace.{u} q :=
  (SSet.sdFlagOfCarrierChain q (ComposableArrows.mk₀ x)).obj 0

private theorem nToFlagFace_flagFaceToN
    (q : SimplexCategory) (T : GenericFace.{u} q) :
    nToFlagFace q (flagFaceToN q T) = T := by
  let c := SSet.sdFlagCarrierChain q (ComposableArrows.mk₀ T)
  have hc : ComposableArrows.mk₀ (c.obj 0) = c := by
    apply ComposableArrows.ext (h := fun i ↦ by fin_cases i; rfl)
      (w := by intro i hi; omega)
  unfold nToFlagFace flagFaceToN
  change (SSet.sdFlagOfCarrierChain q
    (ComposableArrows.mk₀ (c.obj 0))).obj 0 = T
  rw [hc]
  have hcomp := SSet.sdFlagOfCarrierChain_flagCarrierChain q
    (ComposableArrows.mk₀ T)
  change SSet.sdFlagOfCarrierChain q c = ComposableArrows.mk₀ T at hcomp
  exact congrArg (fun F ↦ F.obj 0) hcomp

private theorem flagFaceToN_nToFlagFace
    (q : SimplexCategory) (x : (SSet.stdSimplex.{u}.obj q).N) :
    flagFaceToN q (nToFlagFace q x) = x := by
  let F := SSet.sdFlagOfCarrierChain q (ComposableArrows.mk₀ x)
  have hF : ComposableArrows.mk₀ (F.obj 0) = F := by
    apply ComposableArrows.ext (h := fun i ↦ by fin_cases i; rfl)
      (w := by intro i hi; simp at hi)
  unfold nToFlagFace flagFaceToN
  change (SSet.sdFlagCarrierChain q
    (ComposableArrows.mk₀ (F.obj 0))).obj 0 = x
  rw [hF]
  have hcomp := SSet.sdFlagCarrierChain_flagOfCarrierChain q
    (ComposableArrows.mk₀ x)
  change SSet.sdFlagCarrierChain q F = ComposableArrows.mk₀ x at hcomp
  exact congrArg (fun c ↦ c.obj 0) hcomp

private theorem sdFlagCarrierChain_obj_eq
    (q : SimplexCategory) {d : ℕ}
    (F : (SimplexCategory.sd.{u}.obj q) _⦋d⦌)
    (j : Fin (d + 1)) :
    (SSet.sdFlagCarrierChain q F).obj j = flagFaceToN q (F.obj j) := by
  let f := SimplexCategory.const ⦋0⦌ ⦋d⦌ j
  have h := SSet.sdFlagCarrierChain_obj_map q f F
  have hleft :
      (SimplexCategory.sd.{u}.obj q).map f.op F =
        ComposableArrows.mk₀ (F.obj j) := by
    apply ComposableArrows.ext (h := fun k ↦ by fin_cases k; rfl)
      (w := by intro k hk; simp at hk)
  have hright :
      (SSet.nondegenerateNerve.obj (SSet.stdSimplex.{u}.obj q)).map f.op
          (SSet.sdFlagCarrierChain q F) =
        ComposableArrows.mk₀ ((SSet.sdFlagCarrierChain q F).obj j) := by
    apply ComposableArrows.ext (h := fun k ↦ by fin_cases k; rfl)
      (w := by intro k hk; simp at hk)
  rw [hleft, hright] at h
  exact (congrArg (fun c ↦ c.obj 0) h).symm

private theorem flagFaceToN_injective (q : SimplexCategory) :
    Function.Injective (flagFaceToN.{u} q) := by
  intro T U h
  exact (nToFlagFace_flagFaceToN q T).symm.trans
    ((congrArg (nToFlagFace q) h).trans (nToFlagFace_flagFaceToN q U))

private theorem flagFaceToN_monotone (q : SimplexCategory) :
    Monotone (flagFaceToN.{u} q) := by
  intro T U hTU
  let c : (SimplexCategory.sd.{u}.obj q) _⦋1⦌ :=
    ComposableArrows.mk₁ (homOfLE hTU)
  have hmono := (SSet.sdFlagCarrierChain q c).monotone
    (show (0 : Fin 2) ≤ 1 by omega)
  rw [sdFlagCarrierChain_obj_eq q c 0,
    sdFlagCarrierChain_obj_eq q c 1] at hmono
  exact hmono

private theorem flagFaceToN_le_iff (q : SimplexCategory)
    (T U : GenericFace.{u} q) :
    flagFaceToN q T ≤ flagFaceToN q U ↔ T ≤ U := by
  constructor
  · intro hTU
    let c : (CategoryTheory.nerve
        (SSet.stdSimplex.{u}.obj q).N) _⦋1⦌ :=
      ComposableArrows.mk₁ (homOfLE hTU)
    let F := SSet.sdFlagOfCarrierChain q c
    have hchain : SSet.sdFlagCarrierChain q F = c :=
      SSet.sdFlagCarrierChain_flagOfCarrierChain q c
    have hzero : F.obj 0 = T := by
      apply flagFaceToN_injective q
      rw [← sdFlagCarrierChain_obj_eq q F 0, hchain]
      rfl
    have hone : F.obj 1 = U := by
      apply flagFaceToN_injective q
      rw [← sdFlagCarrierChain_obj_eq q F 1, hchain]
      rfl
    rw [← hzero, ← hone]
    exact F.monotone (Fin.zero_le (Fin.last 1))
  · intro hTU
    exact flagFaceToN_monotone q hTU

private noncomputable def flagFaceOrderIso (q : SimplexCategory) :
    GenericFace.{u} q ≃o (SSet.stdSimplex.{u}.obj q).N where
  toFun := flagFaceToN q
  invFun := nToFlagFace q
  left_inv := nToFlagFace_flagFaceToN q
  right_inv := flagFaceToN_nToFlagFace q
  map_rel_iff' := flagFaceToN_le_iff q _ _

private theorem flagFaceToN_map {q r : SimplexCategory}
    (f : q ⟶ r) (T : GenericFace.{u} q) :
    flagFaceToN r
        (T.map ((SimplexCategory.toPartOrd.map f).hom)) =
      SSet.N.map (SSet.stdSimplex.map f) (flagFaceToN q T) := by
  have h := SSet.sdFlagCarrierChain_map f (ComposableArrows.mk₀ T)
  have hleft :
      (SimplexCategory.sd.map f).app (op ⦋0⦌) (ComposableArrows.mk₀ T) =
        ComposableArrows.mk₀
          (T.map ((SimplexCategory.toPartOrd.map f).hom)) := by
    apply ComposableArrows.ext (h := fun j ↦ rfl)
      (w := by intro j hj; subsingleton)
  have hright :
      (SSet.nondegenerateNerve.map (SSet.stdSimplex.map f)).app (op ⦋0⦌)
          (SSet.sdFlagCarrierChain q (ComposableArrows.mk₀ T)) =
        ComposableArrows.mk₀
          (SSet.N.map (SSet.stdSimplex.map f) (flagFaceToN q T)) := by
    let c := SSet.sdFlagCarrierChain q (ComposableArrows.mk₀ T)
    have hc : ComposableArrows.mk₀ (c.obj 0) = c := by
      apply ComposableArrows.ext (h := fun j ↦ by fin_cases j; rfl)
        (w := by intro j hj; simp at hj)
    change (SSet.nondegenerateNerve.map
      (SSet.stdSimplex.map f)).app (op ⦋0⦌) c = _
    rw [← hc]
    rfl
  rw [hleft, hright] at h
  exact congrArg (fun c ↦ c.obj 0) h

private theorem N_map_iso_hom {X Y : SSet.{u}}
    (e : X ≅ Y) (x : X.N) :
    SSet.N.map e.hom x = SSet.N.orderIsoOfIso e x := by
  rw [SSet.N.map_eq_mk]
  rfl

private theorem directFaceOrderIso_map {q r : SimplexCategory}
    (f : q ⟶ r) (x : (SSet.stdSimplex.{u}.obj q).N) :
    directFaceOrderIso r
        (SSet.N.map (SSet.stdSimplex.map f) x) =
      (directFaceOrderIso q x).map
        ((SimplexCategory.toPartOrd.map f).hom) := by
  let nf : CategoryTheory.nerve
        (ULift.{u} (Fin (q.len + 1))) ⟶
      CategoryTheory.nerve
        (ULift.{u} (Fin (r.len + 1))) :=
    CategoryTheory.nerveMap
      ((SimplexCategory.toPartOrd.map f).hom.toFunctor)
  have hsquare :
      SSet.stdSimplex.map f ≫
          (SSet.stdSimplex.isoNerve.{u} r.len).hom =
        (SSet.stdSimplex.isoNerve.{u} q.len).hom ≫ nf := by
    ext d s j
    rfl
  have hN :
      SSet.N.map (SSet.stdSimplex.isoNerve.{u} r.len).hom
          (SSet.N.map (SSet.stdSimplex.map f) x) =
        SSet.N.map nf
          (SSet.N.map (SSet.stdSimplex.isoNerve.{u} q.len).hom x) := by
    calc
      _ = SSet.N.map
          (SSet.stdSimplex.map f ≫
            (SSet.stdSimplex.isoNerve.{u} r.len).hom) x :=
        SSet.N.map_comp_apply _ _ _
      _ = SSet.N.map
          ((SSet.stdSimplex.isoNerve.{u} q.len).hom ≫ nf) x := by
        rw [hsquare]
      _ = _ := (SSet.N.map_comp_apply _ _ _).symm
  change PartOrd.nerveNOrderIso (SimplexCategory.toPartOrd.obj r)
      (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} r.len)
        (SSet.N.map (SSet.stdSimplex.map f) x)) =
    (PartOrd.nerveNOrderIso (SimplexCategory.toPartOrd.obj q)
      (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} q.len) x)).map
        ((SimplexCategory.toPartOrd.map f).hom)
  rw [← N_map_iso_hom, ← N_map_iso_hom, hN]
  have hnat := PartOrd.nerveNOrderIso_naturality
    (SimplexCategory.toPartOrd.map f)
      (SSet.N.map (SSet.stdSimplex.isoNerve.{u} q.len).hom x)
  change PartOrd.nerveNOrderIso (SimplexCategory.toPartOrd.obj r)
      (SSet.N.map nf
        (SSet.N.map (SSet.stdSimplex.isoNerve.{u} q.len).hom x)) = _ at hnat
  exact hnat

private noncomputable def faceTwistOrderIso (q : SimplexCategory) :
    GenericFace.{u} q ≃o GenericFace.{u} q :=
  (flagFaceOrderIso q).trans (directFaceOrderIso q)

private theorem faceTwist_map {q r : SimplexCategory}
    (f : q ⟶ r) (T : GenericFace.{u} q) :
    faceTwistOrderIso r
        (T.map ((SimplexCategory.toPartOrd.map f).hom)) =
      (faceTwistOrderIso q T).map
        ((SimplexCategory.toPartOrd.map f).hom) := by
  change directFaceOrderIso r
      (flagFaceToN r
        (T.map ((SimplexCategory.toPartOrd.map f).hom))) = _
  rw [flagFaceToN_map, directFaceOrderIso_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem fullFace_map_vertex
    (q : SimplexCategory) (j : Fin (q.len + 1)) :
    (SSet.sdFullFace.{u} ⦋0⦌).map
        ((SimplexCategory.toPartOrd.map
          (SimplexCategory.const ⦋0⦌ q j)).hom) =
      SimplexCategory.sdSingletonChain.{u} q j := by
  classical
  apply NonemptyFiniteChains.ext
  ext y
  simp only [NonemptyFiniteChains.mem_map_iff,
    SSet.mem_sdFullFace, SimplexCategory.sdSingletonChain,
    Finset.mem_singleton, true_and]
  constructor
  · rintro ⟨x, hxy⟩
    change ULift.up j = y at hxy
    exact hxy.symm
  · rintro rfl
    exact ⟨ULift.up 0, rfl⟩

private theorem faceTwist_full_zero :
    faceTwistOrderIso ⦋0⦌ (SSet.sdFullFace.{u} ⦋0⦌) =
      SSet.sdFullFace.{u} ⦋0⦌ := by
  apply NonemptyFiniteChains.ext
  ext y
  constructor
  · intro _
    exact SSet.mem_sdFullFace _ _
  · intro _
    obtain ⟨z, hz⟩ :=
      (faceTwistOrderIso ⦋0⦌ (SSet.sdFullFace.{u} ⦋0⦌)).nonempty
    have hzy : z = y := by
      apply ULift.ext
      apply Fin.ext
      have hz := z.down.isLt
      have hy := y.down.isLt
      change z.down.val < 1 at hz
      change y.down.val < 1 at hy
      omega
    rwa [← hzy]

set_option backward.isDefEq.respectTransparency false in
private theorem faceTwist_singleton
    (q : SimplexCategory) (j : Fin (q.len + 1)) :
    faceTwistOrderIso.{u} q
        (SimplexCategory.sdSingletonChain.{u} q j) =
      SimplexCategory.sdSingletonChain.{u} q j := by
  let f := SimplexCategory.const ⦋0⦌ q j
  have h := faceTwist_map f (SSet.sdFullFace.{u} ⦋0⦌)
  dsimp only [f] at h
  have hfull := fullFace_map_vertex.{u} q j
  have hzero := faceTwist_full_zero.{u}
  calc
    _ = faceTwistOrderIso q
        ((SSet.sdFullFace.{u} ⦋0⦌).map
          ((SimplexCategory.toPartOrd.map
            (SimplexCategory.const ⦋0⦌ q j)).hom)) :=
      congrArg (faceTwistOrderIso q) hfull.symm
    _ = (faceTwistOrderIso ⦋0⦌
          (SSet.sdFullFace.{u} ⦋0⦌)).map
        ((SimplexCategory.toPartOrd.map
          (SimplexCategory.const ⦋0⦌ q j)).hom) := h
    _ = (SSet.sdFullFace.{u} ⦋0⦌).map
        ((SimplexCategory.toPartOrd.map
          (SimplexCategory.const ⦋0⦌ q j)).hom) :=
      congrArg (fun T ↦ T.map
        ((SimplexCategory.toPartOrd.map
          (SimplexCategory.const ⦋0⦌ q j)).hom)) hzero
    _ = _ := hfull

private theorem faceTwist_eq
    (q : SimplexCategory) (T : GenericFace.{u} q) :
    faceTwistOrderIso q T = T := by
  apply NonemptyFiniteChains.ext
  ext x
  let j : Fin (q.len + 1) := x.down
  have hmem : ULift.up j ∈
      (SimplexCategory.sdSingletonChain.{u} q j).finset := by
    simp [SimplexCategory.sdSingletonChain]
  constructor
  · intro hx
    have hsTw : SimplexCategory.sdSingletonChain.{u} q j ≤
        faceTwistOrderIso q T := by
      intro y hy
      have hyx : y = ULift.up j := by
        simpa [SimplexCategory.sdSingletonChain] using hy
      rw [hyx, ULift.up_down]
      exact hx
    have htw : faceTwistOrderIso q
          (SimplexCategory.sdSingletonChain.{u} q j) ≤
        faceTwistOrderIso q T := by
      rw [faceTwist_singleton]
      exact hsTw
    have hsT : SimplexCategory.sdSingletonChain.{u} q j ≤ T :=
      (faceTwistOrderIso q).map_rel_iff.mp htw
    simpa [j, ULift.up_down] using hsT hmem
  · intro hx
    have hsT : SimplexCategory.sdSingletonChain.{u} q j ≤ T := by
      intro y hy
      have hyx : y = ULift.up j := by
        simpa [SimplexCategory.sdSingletonChain] using hy
      rw [hyx, ULift.up_down]
      exact hx
    have htw : faceTwistOrderIso q
          (SimplexCategory.sdSingletonChain.{u} q j) ≤
        faceTwistOrderIso q T :=
      (faceTwistOrderIso q).map_rel_iff.mpr hsT
    rw [faceTwist_singleton] at htw
    simpa [j, ULift.up_down] using htw hmem

private theorem flagFaceToN_eq
    (q : SimplexCategory) (T : GenericFace.{u} q) :
    flagFaceToN q T = (directFaceOrderIso q).symm T := by
  apply (directFaceOrderIso q).injective
  change faceTwistOrderIso q T =
    directFaceOrderIso q ((directFaceOrderIso q).symm T)
  rw [OrderIso.apply_symm_apply]
  exact faceTwist_eq q T

private theorem sdFlagCarrierChain_obj
    (q : SimplexCategory) {d : ℕ}
    (F : (SimplexCategory.sd.{u}.obj q) _⦋d⦌)
    (j : Fin (d + 1)) :
    (SSet.sdFlagCarrierChain q F).obj j =
      (directFaceOrderIso q).symm (F.obj j) := by
  calc
    _ = flagFaceToN q (F.obj j) := sdFlagCarrierChain_obj_eq q F j
    _ = _ := flagFaceToN_eq q (F.obj j)

set_option backward.isDefEq.respectTransparency false in
private theorem simplexSdIso_hom_eq_sdIso (n : ℕ) :
    (simplexSdIso.{u} n).hom =
      SSet.stdSimplex.sdIso.hom.app ⦋n + 1⦌ := by
  rw [simplexSdIso_hom]
  ext d S
  let q : SimplexCategory := ⦋n + 1⦌
  let F := (SSet.stdSimplex.sdIso.hom.app q).app d S
  have hInv : (SSet.stdSimplex.sdIso.inv.app q).app d F = S := by
    exact ConcreteCategory.congr_hom
      (Iso.hom_inv_id_app (SSet.stdSimplex.sdIso.app q) d) S
  change (PartOrd.nerveFunctor.map (facePartOrdIso.{u} n).hom).app d
      ((SSet.sdToNondegenerateNerve.app
        (SSet.stdSimplex.obj q)).app d S) = F
  have hc : (SSet.sdToNondegenerateNerve.app
      (SSet.stdSimplex.obj q)).app d S =
      SSet.sdFlagCarrierChain q F := by
    unfold SSet.sdFlagCarrierChain
    rw [hInv]
  rw [hc]
  apply ComposableArrows.ext (h := fun j ↦ ?_) (w := by
    intro j hj
    subsingleton)
  change directFaceOrderIso q
      ((SSet.sdFlagCarrierChain q F).obj j) = F.obj j
  rw [sdFlagCarrierChain_obj q F j, OrderIso.apply_symm_apply]

private noncomputable abbrev lastNerveMap (q : SimplexCategory) :
    SimplexCategory.sd.{u}.obj q ⟶
      CategoryTheory.nerve (ULift.{u} (Fin (q.len + 1))) :=
  PartOrd.nerveFunctor.map
    (PartOrd.ofHom (SimplexCategory.sdLastVertexOrderHom q))

set_option backward.isDefEq.respectTransparency false in
private theorem lastVertex_chart (q : SimplexCategory) :
    SSet.lastVertex.app (SSet.stdSimplex.{u}.obj q) ≫
        (SSet.stdSimplex.isoNerve.{u} q.len).hom =
      SSet.stdSimplex.sdIso.hom.app q ≫ lastNerveMap.{u} q := by
  apply (cancel_epi (SSet.stdSimplex.sdIso.{u}.inv.app q)).mp
  calc
    _ = SimplexCategory.lastVertex.app q ≫
        (SSet.stdSimplex.isoNerve.{u} q.len).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ (SSet.stdSimplex.isoNerve.{u} q.len).hom)
        (SSet.lastVertex_fac.{u} q)
    _ = lastNerveMap.{u} q := by
      unfold SimplexCategory.lastVertex
      dsimp only [SimplexCategory.sdRepresentableLastVertexApp,
        lastNerveMap]
      change (lastNerveMap.{u} q ≫
          (SSet.stdSimplex.isoNerve.{u} q.len).inv) ≫
        (SSet.stdSimplex.isoNerve.{u} q.len).hom = lastNerveMap.{u} q
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = SSet.stdSimplex.sdIso.inv.app q ≫
        SSet.stdSimplex.sdIso.hom.app q ≫ lastNerveMap.{u} q := by
      exact (Iso.inv_hom_id_assoc (SSet.stdSimplex.sdIso.app q)
        (lastNerveMap.{u} q)).symm

private theorem standardLastCarrier (q : SimplexCategory)
    (x : (SSet.sd.obj (SSet.stdSimplex.obj q : SSet.{u})).N) :
    (PartOrd.nerveNOrderIso
        (PartOrd.nonemptyFiniteChainsFunctor.obj
          (SimplexCategory.toPartOrd.obj q))
        (SSet.N.map (SSet.stdSimplex.sdIso.hom.app q) x)).map
      (SimplexCategory.sdLastVertexOrderHom q) =
    directFaceOrderIso q
      (SSet.N.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj q)) x) := by
  let P := PartOrd.nonemptyFiniteChainsFunctor.obj
    (SimplexCategory.toPartOrd.obj q)
  let Q := SimplexCategory.toPartOrd.obj q
  let h : P ⟶ Q :=
    PartOrd.ofHom (SimplexCategory.sdLastVertexOrderHom q)
  let x' : (SimplexCategory.sd.{u}.obj q).N :=
    SSet.N.map (SSet.stdSimplex.sdIso.hom.app q) x
  let C : NonemptyFiniteChains P := PartOrd.nerveNOrderIso P x'
  change C.map h.hom = directFaceOrderIso q
    (SSet.N.map
      (SSet.lastVertex.app (SSet.stdSimplex.obj q)) x)
  change C.map h.hom = PartOrd.nerveNOrderIso Q
    (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} q.len)
      (SSet.N.map
        (SSet.lastVertex.app (SSet.stdSimplex.obj q)) x))
  rw [← N_map_iso_hom]
  have hN :
      SSet.N.map (SSet.stdSimplex.isoNerve.{u} q.len).hom
          (SSet.N.map
            (SSet.lastVertex.app (SSet.stdSimplex.obj q)) x) =
        SSet.N.map (lastNerveMap.{u} q) x' := by
    calc
      _ = SSet.N.map
          (SSet.lastVertex.app (SSet.stdSimplex.obj q) ≫
            (SSet.stdSimplex.isoNerve.{u} q.len).hom) x :=
        SSet.N.map_comp_apply _ _ _
      _ = SSet.N.map
          (SSet.stdSimplex.sdIso.hom.app q ≫ lastNerveMap.{u} q) x :=
        congrArg (fun k ↦ SSet.N.map k x) (lastVertex_chart.{u} q)
      _ = SSet.N.map (lastNerveMap.{u} q) x' :=
        (SSet.N.map_comp_apply _ _ _).symm
  rw [hN]
  have hnat := PartOrd.nerveNOrderIso_naturality h x'
  change PartOrd.nerveNOrderIso Q
      (SSet.N.map (lastNerveMap.{u} q) x') = C.map h.hom at hnat
  exact hnat.symm

private noncomputable abbrev faceLastNerveMap (n : ℕ) :
    CategoryTheory.nerve (Face.{u} n) ⟶
      CategoryTheory.nerve (Vertex.{u} n) :=
  PartOrd.nerveFunctor.map (PartOrd.ofHom (faceLastOrderHom.{u} n))

set_option backward.isDefEq.respectTransparency false in
private theorem lastVertex_face_chart (n : ℕ) :
    SSet.lastVertex.app (Δ[n + 1] : SSet.{u}) ≫
        (SSet.stdSimplex.isoNerve.{u} (n + 1)).hom =
      (simplexSdIso.{u} n).hom ≫ faceLastNerveMap.{u} n := by
  rw [simplexSdIso_hom_eq_sdIso]
  apply (cancel_epi (SSet.stdSimplex.sdIso.{u}.inv.app ⦋n + 1⦌)).mp
  calc
    _ = SimplexCategory.lastVertex.app ⦋n + 1⦌ ≫
        (SSet.stdSimplex.isoNerve.{u} (n + 1)).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ (SSet.stdSimplex.isoNerve.{u} (n + 1)).hom)
        (SSet.lastVertex_fac.{u} ⦋n + 1⦌)
    _ = faceLastNerveMap.{u} n := by
      unfold SimplexCategory.lastVertex
      dsimp only [SimplexCategory.sdRepresentableLastVertexApp,
        faceLastNerveMap]
      change (faceLastNerveMap.{u} n ≫
          (SSet.stdSimplex.isoNerve.{u} (n + 1)).inv) ≫
        (SSet.stdSimplex.isoNerve.{u} (n + 1)).hom =
          faceLastNerveMap.{u} n
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = SSet.stdSimplex.sdIso.inv.app ⦋n + 1⦌ ≫
        SSet.stdSimplex.sdIso.hom.app ⦋n + 1⦌ ≫
          faceLastNerveMap.{u} n := by
      exact (Iso.inv_hom_id_assoc (SSet.stdSimplex.sdIso.app ⦋n + 1⦌)
        (faceLastNerveMap.{u} n)).symm

private theorem standardLastCarrierN (n : ℕ)
    (x : (SSet.sd.obj (Δ[n + 1] : SSet.{u})).N) :
    (PartOrd.nerveNOrderIso (PartOrd.of (Face.{u} n))
        (SSet.N.map (simplexSdIso.{u} n).hom x)).map
      (faceLastOrderHom.{u} n) =
    faceOrderIso.{u} n
      (SSet.N.map (SSet.lastVertex.app (Δ[n + 1] : SSet.{u})) x) := by
  let P := PartOrd.of (Face.{u} n)
  let Q := PartOrd.of (Vertex.{u} n)
  let h : P ⟶ Q := PartOrd.ofHom (faceLastOrderHom.{u} n)
  let x' : (CategoryTheory.nerve (Face.{u} n)).N :=
    SSet.N.map (simplexSdIso.{u} n).hom x
  let C : NonemptyFiniteChains (Face.{u} n) :=
    PartOrd.nerveNOrderIso P x'
  change C.map h.hom = faceOrderIso.{u} n
    (SSet.N.map (SSet.lastVertex.app (Δ[n + 1] : SSet.{u})) x)
  change C.map h.hom = PartOrd.nerveNOrderIso Q
    (SSet.N.orderIsoOfIso (SSet.stdSimplex.isoNerve.{u} (n + 1))
      (SSet.N.map (SSet.lastVertex.app (Δ[n + 1] : SSet.{u})) x))
  rw [← N_map_iso_hom]
  have hN :
      SSet.N.map (SSet.stdSimplex.isoNerve.{u} (n + 1)).hom
          (SSet.N.map (SSet.lastVertex.app (Δ[n + 1] : SSet.{u})) x) =
        SSet.N.map (faceLastNerveMap.{u} n) x' := by
    calc
      _ = SSet.N.map
          (SSet.lastVertex.app (Δ[n + 1] : SSet.{u}) ≫
            (SSet.stdSimplex.isoNerve.{u} (n + 1)).hom) x :=
        SSet.N.map_comp_apply _ _ _
      _ = SSet.N.map
          ((simplexSdIso.{u} n).hom ≫ faceLastNerveMap.{u} n) x :=
        congrArg (fun k ↦ SSet.N.map k x) (lastVertex_face_chart.{u} n)
      _ = SSet.N.map (faceLastNerveMap.{u} n) x' :=
        (SSet.N.map_comp_apply _ _ _).symm
  rw [hN]
  have hnat := PartOrd.nerveNOrderIso_naturality h x'
  change PartOrd.nerveNOrderIso Q
      (SSet.N.map (faceLastNerveMap.{u} n) x') = C.map h.hom at hnat
  exact hnat.symm

private theorem hornLastCarrierSquare {n : ℕ} (i : Fin (n + 2)) :
    SSet.N.functor.map (hornSdIso.{u} i).hom ≫
        (PartOrd.Iso.mk
          (PartOrd.nerveNOrderIso (PartOrd.of (H.{u} i)))).hom ≫
        hornLastFaceOrderHom.{u} i =
      SSet.N.functor.map
          (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
        (hornFacePartOrdIso.{u} i).hom := by
  apply PartOrd.ext
  intro x
  let y : (CategoryTheory.nerve (H.{u} i)).N :=
    SSet.N.map (hornSdIso.{u} i).hom x
  let C : NonemptyFiniteChains (H.{u} i) :=
    PartOrd.nerveNOrderIso (PartOrd.of (H.{u} i)) y
  let z : (SSet.horn.{u} (n + 1) i : SSet.{u}).N :=
    SSet.N.map
      (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) x
  change (hornLastFaceOrderHom.{u} i).hom C =
    hornFaceOrderIso.{u} i z
  rw [hornLastFaceOrderHom_apply]
  apply Subtype.ext
  change C.map (hornLastOrderHom.{u} i) =
    (hornFaceOrderIso.{u} i z).1
  have hzVal : (hornFaceOrderIso.{u} i z).1 =
      faceOrderIso.{u} n
        (SSet.N.map (SSet.horn.{u} (n + 1) i).ι z) := by
    rfl
  rw [hzVal]
  let xD : (SSet.sd.obj (Δ[n + 1] : SSet.{u})).N :=
    SSet.N.map (SSet.sd.map (SSet.horn.{u} (n + 1) i).ι) x
  have hLastNat :
      SSet.N.map (SSet.horn.{u} (n + 1) i).ι z =
        SSet.N.map
          (SSet.lastVertex.app (Δ[n + 1] : SSet.{u})) xD := by
    dsimp only [z, xD]
    calc
      SSet.N.map (SSet.horn.{u} (n + 1) i).ι
          (SSet.N.map
            (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) x) =
        SSet.N.map
          (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i) ≫
            (SSet.horn.{u} (n + 1) i).ι) x :=
        SSet.N.map_comp_apply _ _ _
      _ = SSet.N.map
          (SSet.sd.map (SSet.horn.{u} (n + 1) i).ι ≫
            SSet.lastVertex.app (SSet.stdSimplex.obj ⦋n + 1⦌)) x := by
        rw [SSet.lastVertex.naturality]
        simp only [Functor.id_map]
      _ = SSet.N.map
          (SSet.lastVertex.app (SSet.stdSimplex.obj ⦋n + 1⦌))
            (SSet.N.map
              (SSet.sd.map (SSet.horn.{u} (n + 1) i).ι) x) :=
        (SSet.N.map_comp_apply _ _ _).symm
  rw [hLastNat]
  let Cstd : NonemptyFiniteChains (Face.{u} n) :=
    PartOrd.nerveNOrderIso (PartOrd.of (Face.{u} n))
      (SSet.N.map (simplexSdIso.{u} n).hom xD)
  have hChartN :
      SSet.N.map (PartOrd.nerveFunctor.map (jHOrd.{u} i)) y =
        SSet.N.map (simplexSdIso.{u} n).hom xD := by
    dsimp only [y, xD]
    exact (SSet.N.map_comp_apply _ _ _).trans
      ((congrArg (fun k ↦ SSet.N.map k x)
        (hornSdIso_hom_comp.{u} i)).trans
          (SSet.N.map_comp_apply _ _ _).symm)
  have hCstd : Cstd = C.map (jH.{u} i).toOrderHom := by
    have hnat := PartOrd.nerveNOrderIso_naturality (jHOrd.{u} i) y
    change PartOrd.nerveNOrderIso (PartOrd.of (Face.{u} n))
        (SSet.N.map (PartOrd.nerveFunctor.map (jHOrd.{u} i)) y) =
      C.map (jH.{u} i).toOrderHom at hnat
    rw [hChartN] at hnat
    exact hnat
  rw [← map_jH_faceLast i C, ← hCstd]
  exact standardLastCarrierN.{u} n xD

set_option backward.isDefEq.respectTransparency false in
private theorem lastVertex_chart_of_carrier_square
    {n : ℕ} (i : Fin (n + 2))
    (hCarrier :
      SSet.N.functor.map (hornSdIso.{u} i).hom ≫
          (PartOrd.Iso.mk
            (PartOrd.nerveNOrderIso (PartOrd.of (H.{u} i)))).hom ≫
          hornLastFaceOrderHom.{u} i =
        SSet.N.functor.map
            (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
          (hornFacePartOrdIso.{u} i).hom) :
    (doubleHornChart.{u} i).hom ≫
        PartOrd.nerveFunctor.map (hornLastFaceOrderHom.{u} i) =
      SSet.sd.map
          (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
        (hornSdIso.{u} i).hom := by
  have hCarrierN := congrArg PartOrd.nerveFunctor.map hCarrier
  simp only [Functor.map_comp] at hCarrierN
  change SSet.nondegenerateNerve.map (hornSdIso.{u} i).hom ≫
        PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk
            (PartOrd.nerveNOrderIso (PartOrd.of (H.{u} i)))).hom ≫
        PartOrd.nerveFunctor.map (hornLastFaceOrderHom.{u} i) =
      SSet.nondegenerateNerve.map
          (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
        PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom at hCarrierN
  change (SSet.sd.map (hornSdIso.{u} i).hom ≫
      (nerveSdIso (PartOrd.of (H.{u} i))).hom) ≫
        PartOrd.nerveFunctor.map (hornLastFaceOrderHom.{u} i) = _
  rw [nerveSdIso_hom]
  have hnatChart := SSet.sdToNondegenerateNerve.naturality
    (hornSdIso.{u} i).hom
  change SSet.sd.map (hornSdIso.{u} i).hom ≫
      SSet.sdToNondegenerateNerve.app
        (PartOrd.nerveFunctor.obj (PartOrd.of (H.{u} i))) =
    SSet.sdToNondegenerateNerve.app
        (SSet.sd.obj (SSet.horn.{u} (n + 1) i)) ≫
      SSet.nondegenerateNerve.map (hornSdIso.{u} i).hom at hnatChart
  have hnatLast := SSet.sdToNondegenerateNerve.naturality
    (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i))
  change SSet.sd.map
        (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
      SSet.sdToNondegenerateNerve.app (SSet.horn.{u} (n + 1) i) =
    SSet.sdToNondegenerateNerve.app
        (SSet.sd.obj (SSet.horn.{u} (n + 1) i)) ≫
      SSet.nondegenerateNerve.map
        (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) at hnatLast
  calc
    (SSet.sd.map (hornSdIso.{u} i).hom ≫
        (SSet.sdToNondegenerateNerve.app
            (PartOrd.nerveFunctor.obj (PartOrd.of (H.{u} i))) ≫
          PartOrd.nerveFunctor.map
            (PartOrd.Iso.mk
              (PartOrd.nerveNOrderIso (PartOrd.of (H.{u} i)))).hom)) ≫
      PartOrd.nerveFunctor.map (hornLastFaceOrderHom.{u} i) =
      (SSet.sd.map (hornSdIso.{u} i).hom ≫
        SSet.sdToNondegenerateNerve.app
          (PartOrd.nerveFunctor.obj (PartOrd.of (H.{u} i)))) ≫
        PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk
            (PartOrd.nerveNOrderIso (PartOrd.of (H.{u} i)))).hom ≫
        PartOrd.nerveFunctor.map (hornLastFaceOrderHom.{u} i) := by
      cat_disch
    _ = (SSet.sdToNondegenerateNerve.app
          (SSet.sd.obj (SSet.horn.{u} (n + 1) i)) ≫
        SSet.nondegenerateNerve.map (hornSdIso.{u} i).hom) ≫
        PartOrd.nerveFunctor.map
          (PartOrd.Iso.mk
            (PartOrd.nerveNOrderIso (PartOrd.of (H.{u} i)))).hom ≫
        PartOrd.nerveFunctor.map (hornLastFaceOrderHom.{u} i) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ PartOrd.nerveFunctor.map
            (PartOrd.Iso.mk
              (PartOrd.nerveNOrderIso (PartOrd.of (H.{u} i)))).hom ≫
          PartOrd.nerveFunctor.map (hornLastFaceOrderHom.{u} i)) hnatChart
    _ = SSet.sdToNondegenerateNerve.app
          (SSet.sd.obj (SSet.horn.{u} (n + 1) i)) ≫
        (SSet.nondegenerateNerve.map (hornSdIso.{u} i).hom ≫
          PartOrd.nerveFunctor.map
            (PartOrd.Iso.mk
              (PartOrd.nerveNOrderIso (PartOrd.of (H.{u} i)))).hom ≫
          PartOrd.nerveFunctor.map (hornLastFaceOrderHom.{u} i)) := by
      cat_disch
    _ = SSet.sdToNondegenerateNerve.app
          (SSet.sd.obj (SSet.horn.{u} (n + 1) i)) ≫
        (SSet.nondegenerateNerve.map
            (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
          PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom) := by
      rw [hCarrierN]
    _ = (SSet.sdToNondegenerateNerve.app
          (SSet.sd.obj (SSet.horn.{u} (n + 1) i)) ≫
        SSet.nondegenerateNerve.map
          (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i))) ≫
        PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom := by
      cat_disch
    _ = (SSet.sd.map
          (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
        SSet.sdToNondegenerateNerve.app (SSet.horn.{u} (n + 1) i)) ≫
        PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ PartOrd.nerveFunctor.map
          (hornFacePartOrdIso.{u} i).hom) hnatLast.symm
    _ = SSet.sd.map
          (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
        (SSet.sdToNondegenerateNerve.app (SSet.horn.{u} (n + 1) i) ≫
          PartOrd.nerveFunctor.map (hornFacePartOrdIso.{u} i).hom) := by
      cat_disch
    _ = SSet.sd.map
          (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
        (hornSdIso.{u} i).hom := by
      rw [hornSdIso_hom]

set_option backward.isDefEq.respectTransparency false in
private theorem hornDoubleSubdivisionRetraction_fac_of_chart
    (n : ℕ) (i : Fin (n + 2))
    (hLast : (doubleHornChart.{u} i).hom ≫
        PartOrd.nerveFunctor.map (hornLastFaceOrderHom.{u} i) =
      SSet.sd.map
          (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
        (hornSdIso.{u} i).hom) :
    SSet.sd.map (SSet.sd.map (SSet.horn.{u} (n + 1) i).ι) ≫
        hornDoubleSubdivisionRetraction.{u} n i =
      SSet.sd.map
        (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) := by
  apply (cancel_mono (hornSdIso.{u} i).hom).mp
  unfold hornDoubleSubdivisionRetraction
  calc
    (SSet.sd.map (SSet.sd.map (SSet.horn.{u} (n + 1) i).ι) ≫
        ((doubleSimplexChart.{u} n).hom ≫
          PartOrd.nerveFunctor.map
            (PartOrd.ofHom (retractOrderHom.{u} i)) ≫
          (hornSdIso.{u} i).inv)) ≫
        (hornSdIso.{u} i).hom =
      SSet.sd.map (SSet.sd.map (SSet.horn.{u} (n + 1) i).ι) ≫
        (doubleSimplexChart.{u} n).hom ≫
        PartOrd.nerveFunctor.map
          (PartOrd.ofHom (retractOrderHom.{u} i)) := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (doubleHornChart.{u} i).hom ≫
        PartOrd.nerveFunctor.map
          (PartOrd.nonemptyFiniteChainsFunctor.map (jHOrd.{u} i)) ≫
        PartOrd.nerveFunctor.map
          (PartOrd.ofHom (retractOrderHom.{u} i)) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ PartOrd.nerveFunctor.map
          (PartOrd.ofHom (retractOrderHom.{u} i)))
        (doubleHornChart_hom_comp.{u} i).symm
    _ = (doubleHornChart.{u} i).hom ≫
        PartOrd.nerveFunctor.map (hornLastFaceOrderHom.{u} i) := by
      rw [hornLastFaceOrderHom, Functor.map_comp]
    _ = SSet.sd.map
          (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) ≫
        (hornSdIso.{u} i).hom := hLast

private theorem hornDoubleSubdivisionRetraction_fac
    (n : ℕ) (i : Fin (n + 2)) :
    SSet.sd.map (SSet.sd.map (SSet.horn.{u} (n + 1) i).ι) ≫
        hornDoubleSubdivisionRetraction.{u} n i =
      SSet.sd.map
        (SSet.lastVertex.app (SSet.horn.{u} (n + 1) i)) := by
  exact hornDoubleSubdivisionRetraction_fac_of_chart n i
    (lastVertex_chart_of_carrier_square i (hornLastCarrierSquare i))


private theorem exists_exIter_horn_extension_of_retraction
    (X : SSet.{u}) (m n : ℕ) (i : Fin (n + 2))
    (R : SSet.sd.obj (SSet.sd.obj (Δ[n + 1] : SSet.{u})) ⟶
      SSet.sd.obj (SSet.horn (n := n + 1) i : SSet.{u}))
    (hR : SSet.sd.map
          (SSet.sd.map (SSet.horn (n := n + 1) i).ι) ≫ R =
        SSet.sd.map
          (SSet.lastVertex.app
            (SSet.horn (n := n + 1) i : SSet.{u})))
    (f : (SSet.horn (n := n + 1) i : SSet.{u}) ⟶
      (exIter (m + 1)).obj X) :
    ∃ g : (Δ[n + 1] : SSet.{u}) ⟶ (exIter (m + 2)).obj X,
      (SSet.horn (n := n + 1) i).ι ≫ g =
        f ≫ SSet.exUnit.app ((exIter (m + 1)).obj X) := by
  let Z : SSet.{u} := (exIter m).obj X
  let fInv : SSet.sd.obj (SSet.horn (n := n + 1) i : SSet.{u}) ⟶ Z :=
    (SSet.sdExAdjunction.homEquiv
      (SSet.horn (n := n + 1) i : SSet.{u}) Z).symm f
  let inner : SSet.sd.obj (Δ[n + 1] : SSet.{u}) ⟶ SSet.ex.obj Z :=
    (SSet.sdExAdjunction.homEquiv
      (SSet.sd.obj (Δ[n + 1] : SSet.{u})) Z) (R ≫ fInv)
  let g : (Δ[n + 1] : SSet.{u}) ⟶ SSet.ex.obj (SSet.ex.obj Z) :=
    (SSet.sdExAdjunction.homEquiv
      (Δ[n + 1] : SSet.{u}) (SSet.ex.obj Z)) inner
  refine ⟨g, ?_⟩
  change (SSet.horn (n := n + 1) i).ι ≫ g =
    f ≫ SSet.exUnit.app (SSet.ex.obj Z)
  have hfInv : (SSet.sdExAdjunction.homEquiv
      (SSet.horn (n := n + 1) i : SSet.{u}) Z) fInv = f := by
    exact (SSet.sdExAdjunction.homEquiv
      (SSet.horn (n := n + 1) i : SSet.{u}) Z).apply_symm_apply f
  have hInner :
      SSet.sd.map (SSet.horn (n := n + 1) i).ι ≫ inner =
        SSet.sd.map f ≫ SSet.lastVertex.app (SSet.ex.obj Z) := by
    unfold inner
    calc
      SSet.sd.map (SSet.horn (n := n + 1) i).ι ≫
          (SSet.sdExAdjunction.homEquiv
            (SSet.sd.obj (Δ[n + 1] : SSet.{u})) Z) (R ≫ fInv) =
        (SSet.sdExAdjunction.homEquiv
          (SSet.sd.obj (SSet.horn (n := n + 1) i : SSet.{u})) Z)
            (SSet.sd.map
              (SSet.sd.map (SSet.horn (n := n + 1) i).ι) ≫
                (R ≫ fInv)) :=
          (SSet.sdExAdjunction.homEquiv_naturality_left _ _).symm
      _ = (SSet.sdExAdjunction.homEquiv
          (SSet.sd.obj (SSet.horn (n := n + 1) i : SSet.{u})) Z)
            (SSet.sd.map
              (SSet.lastVertex.app
                (SSet.horn (n := n + 1) i : SSet.{u})) ≫ fInv) := by
          apply congrArg
          simpa only [Category.assoc] using congrArg
            (fun k ↦ k ≫ fInv) hR
      _ = SSet.lastVertex.app
            (SSet.horn (n := n + 1) i : SSet.{u}) ≫
          (SSet.sdExAdjunction.homEquiv
            (SSet.horn (n := n + 1) i : SSet.{u}) Z) fInv :=
          SSet.sdExAdjunction.homEquiv_naturality_left _ _
      _ = SSet.lastVertex.app
            (SSet.horn (n := n + 1) i : SSet.{u}) ≫ f := by rw [hfInv]
      _ = SSet.sd.map f ≫ SSet.lastVertex.app (SSet.ex.obj Z) :=
          (SSet.lastVertex.naturality f).symm
  unfold g
  calc
    (SSet.horn (n := n + 1) i).ι ≫
        (SSet.sdExAdjunction.homEquiv
          (Δ[n + 1] : SSet.{u}) (SSet.ex.obj Z)) inner =
      (SSet.sdExAdjunction.homEquiv
        (SSet.horn (n := n + 1) i : SSet.{u}) (SSet.ex.obj Z))
          (SSet.sd.map (SSet.horn (n := n + 1) i).ι ≫ inner) :=
        (SSet.sdExAdjunction.homEquiv_naturality_left _ _).symm
    _ = (SSet.sdExAdjunction.homEquiv
        (SSet.horn (n := n + 1) i : SSet.{u}) (SSet.ex.obj Z))
          (SSet.sd.map f ≫ SSet.lastVertex.app (SSet.ex.obj Z)) := by
        rw [hInner]
    _ = f ≫ (SSet.sdExAdjunction.homEquiv
        (SSet.ex.obj Z) (SSet.ex.obj Z))
          (SSet.lastVertex.app (SSet.ex.obj Z)) :=
        SSet.sdExAdjunction.homEquiv_naturality_left _ _
    _ = f ≫ SSet.exUnit.app (SSet.ex.obj Z) := by rfl

private theorem exists_exIter_horn_extension
    (X : SSet.{u}) (m n : ℕ) (i : Fin (n + 2))
    (f : (SSet.horn (n := n + 1) i : SSet.{u}) ⟶
      (exIter (m + 1)).obj X) :
    ∃ g : (Δ[n + 1] : SSet.{u}) ⟶ (exIter (m + 2)).obj X,
      (SSet.horn (n := n + 1) i).ι ≫ g =
        f ≫ SSet.exUnit.app ((exIter (m + 1)).obj X) :=
  exists_exIter_horn_extension_of_retraction X m n i
    (hornDoubleSubdivisionRetraction n i)
    (hornDoubleSubdivisionRetraction_fac n i) f
set_option backward.isDefEq.respectTransparency false in
private theorem exInfinity_kanComplex_of_horn_extension
    (X : SSet.{u})
    (hpromote : ∀ (m n : ℕ) (i : Fin (n + 2))
      (f : (SSet.horn (n := n + 1) i : SSet.{u}) ⟶
        (exIter (m + 1)).obj X),
      ∃ g : (Δ[n + 1] : SSet.{u}) ⟶ (exIter (m + 2)).obj X,
        (SSet.horn (n := n + 1) i).ι ≫ g =
          f ≫ SSet.exUnit.app ((exIter (m + 1)).obj X)) :
    KanComplex (exInfinity.obj X) := by
  rw [KanComplex.iff]
  intro n i f hf
  let a : (SSet.horn (n := n + 1) i : SSet.{u}) ⟶
      exInfinity.obj X := hf.desc
  obtain ⟨j, p, hp⟩ := exists_exTower_factor X
    (SSet.horn (n := n + 1) i : SSet.{u}) a
  let m : ℕ := CategoryTheory.AsSmall.down.obj j
  let s₀ : m ⟶ m + 1 := homOfLE (m.le_add_right 1)
  let s₁ : m + 1 ⟶ m + 2 := homOfLE ((m + 1).le_add_right 1)
  let s₂ : m ⟶ m + 2 := homOfLE (by omega)
  let p₁ : (SSet.horn (n := n + 1) i : SSet.{u}) ⟶
      (exIter (m + 1)).obj X :=
    p ≫ (exTower X).map s₀
  obtain ⟨g, hg⟩ := hpromote m n i p₁
  let φ : (Δ[n + 1] : SSet.{u}) ⟶ exInfinity.obj X :=
    g ≫ colimit.ι (exTower X) (m + 2)
  have hι : (SSet.horn (n := n + 1) i).ι ≫ φ = a := by
    have hs₁ : (exTower X).map s₁ =
        SSet.exUnit.app ((exIter (m + 1)).obj X) := by
      dsimp only [s₁]
      exact exTower_map_succ X (m + 1)
    have hmaps :
        (exTower X).map s₀ ≫ (exTower X).map s₁ =
          (exTower X).map s₂ := by
      calc
        _ = (exTower X).map (s₀ ≫ s₁) :=
          ((exTower X).map_comp s₀ s₁).symm
        _ = _ := congrArg
          (fun q : m ⟶ m + 2 => (exTower X).map q)
          (Subsingleton.elim (s₀ ≫ s₁) s₂)
    calc
      (SSet.horn (n := n + 1) i).ι ≫ φ =
          ((SSet.horn (n := n + 1) i).ι ≫ g) ≫
            colimit.ι (exTower X) (m + 2) := by
        rw [Category.assoc]
      _ = (p₁ ≫ SSet.exUnit.app ((exIter (m + 1)).obj X)) ≫
            colimit.ι (exTower X) (m + 2) := by rw [hg]
      _ = (p ≫ (exTower X).map s₀ ≫ (exTower X).map s₁) ≫
            colimit.ι (exTower X) (m + 2) := by
        dsimp only [p₁]
        rw [hs₁]
        simp only [Category.assoc]
      _ = (p ≫ (exTower X).map s₂) ≫
            colimit.ι (exTower X) (m + 2) := by rw [hmaps]
      _ = p ≫ colimit.ι (exTower X) m := by
        rw [Category.assoc, colimit.w (exTower X) s₂]
      _ = a := hp
  refine ⟨φ, fun j' hj' => ?_⟩
  calc
    SSet.stdSimplex.δ j' ≫ φ =
        (SSet.horn.ι i j' hj' ≫
          (SSet.horn (n := n + 1) i).ι) ≫ φ := by
      rw [SSet.horn.ι_ι]
    _ = SSet.horn.ι i j' hj' ≫
        ((SSet.horn (n := n + 1) i).ι ≫ φ) := by
      rw [Category.assoc]
    _ = SSet.horn.ι i j' hj' ≫ a := by rw [hι]
    _ = f j' hj' := hf.ι_desc j' hj'

/-- The infinite Ex construction is a Kan complex. This is theorem-valued;
it deliberately installs no global fibrancy instance. -/
theorem exInfinity_kanComplex (X : SSet.{u}) :
    KanComplex (exInfinity.obj X) :=
  exInfinity_kanComplex_of_horn_extension X
    (exists_exIter_horn_extension X)

private theorem exTower_map_mono (X : SSet.{u})
    {i j : ℕ} (f : i ⟶ j) : Mono ((exTower X).map f) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
  induction k with
  | zero =>
      have h : (exTower X).map f = 𝟙 _ := by
        rw [Subsingleton.elim f (𝟙 i)]
        exact (exTower X).map_id i
      rw [h]
      infer_instance
  | succ k ih =>
      let f₁ : i ⟶ i + k := homOfLE (Nat.le_add_right i k)
      let f₂ : i + k ⟶ i + k + 1 := homOfLE (Nat.le_add_right (i + k) 1)
      have hf₁ : Mono ((exTower X).map f₁) := ih f₁
      have hf₂ : Mono ((exTower X).map f₂) := by
        rw [show f₂ = homOfLE (Nat.le_add_right (i + k) 1) by rfl,
          exTower_map_succ]
        exact SSet.exUnit_app_mono _
      rw [show f = f₁ ≫ f₂ by subsingleton, Functor.map_comp]
      have _ : Mono ((exTower X).map f₁) := hf₁
      have _ : Mono ((exTower X).map f₂) := hf₂
      exact mono_comp _ _

private noncomputable def exTowerZeroHom (X : SSet.{u}) :
    X ⟶ (exTower X).obj 0 :=
  eqToHom (by rfl)

private theorem exTowerZeroHom_eq (X : SSet.{u}) :
    exTowerZeroHom X = 𝟙 X := by
  rfl

private noncomputable def exTowerFromZero (X : SSet.{u}) :
    (Functor.const ℕ).obj X ⟶ exTower X :=
  NatTrans.ofSequence
    (fun n => exTowerZeroHom X ≫
      (exTower X).map (homOfLE (Nat.zero_le n)))
    (fun n => by
      let a : 0 ⟶ n := homOfLE (Nat.zero_le n)
      let b : n ⟶ n + 1 := homOfLE (n.le_add_right 1)
      let c : 0 ⟶ n + 1 := homOfLE (Nat.zero_le (n + 1))
      have hmap : (exTower X).map (a ≫ b) = (exTower X).map c :=
        congrArg (fun q : 0 ⟶ n + 1 => (exTower X).map q)
          (Subsingleton.elim (a ≫ b) c)
      dsimp only [Functor.const_obj_map]
      calc
        𝟙 X ≫ (exTowerZeroHom X ≫ (exTower X).map c) =
            exTowerZeroHom X ≫ (exTower X).map c := by simp
        _ = exTowerZeroHom X ≫ (exTower X).map (a ≫ b) := by rw [hmap]
        _ = (exTowerZeroHom X ≫ (exTower X).map a) ≫
            (exTower X).map b := by
          rw [Functor.map_comp, Category.assoc])

private theorem exTowerFromZero_app_mem (X : SSet.{u}) (n : ℕ) :
    realizationWeakEquivalences ((exTowerFromZero X).app n) := by
  change realizationWeakEquivalences
    (exTowerZeroHom X ≫
      (exTower X).map (homOfLE (Nat.zero_le n)))
  apply MorphismProperty.comp_mem realizationWeakEquivalences
  · rw [exTowerZeroHom_eq]
    exact realizationWeakEquivalences.id_mem _
  · induction n with
    | zero =>
        have h : (exTower X).map (homOfLE (Nat.zero_le 0)) = 𝟙 _ := by
          rw [Subsingleton.elim (homOfLE (Nat.zero_le 0)) (𝟙 0)]
          exact (exTower X).map_id 0
        rw [h]
        exact realizationWeakEquivalences.id_mem _
    | succ n ih =>
        let a : 0 ⟶ n := homOfLE (Nat.zero_le n)
        let b : n ⟶ n + 1 := homOfLE (n.le_add_right 1)
        let c : 0 ⟶ n + 1 := homOfLE (Nat.zero_le (n + 1))
        have hcomp :
            (exTower X).map a ≫ (exTower X).map b =
              (exTower X).map c := by
          calc
            _ = (exTower X).map (a ≫ b) :=
              ((exTower X).map_comp a b).symm
            _ = _ := congrArg
              (fun q : 0 ⟶ n + 1 => (exTower X).map q)
              (Subsingleton.elim (a ≫ b) c)
        rw [← hcomp]
        exact MorphismProperty.comp_mem realizationWeakEquivalences _ _ ih
          (by
            rw [exTower_map_succ]
            exact SSet.exUnit_app_mem_realizationWeakEquivalences _)

private theorem exInfinityUnit_app_eq (X : SSet.{u}) :
    exInfinityUnit.app X =
      exTowerZeroHom X ≫ colimit.ι (exTower X) 0 := by
  unfold exInfinityUnit exTowerZeroHom exTower
  rfl

/-- The original stage-zero colimit leg is the specified infinite Ex unit. -/
theorem exInfinityStageι_zero (X : SSet.{u}) :
    eqToHom (exInfinityStageFunctor_obj_zero X).symm ≫
      exInfinityStageι X 0 = exInfinityUnit.app X := by
  have h : 𝟙 X ≫ colimit.ι (exTower X) 0 = exInfinityUnit.app X := by
    rw [exInfinityUnit_app_eq, exTowerZeroHom_eq]
    rfl
  unfold exInfinityStageι exInfinityStageFunctor
  exact h

/-- The natural unit into the infinite Ex construction is a realization weak
equivalence. -/
theorem exInfinityUnit_mem_realizationWeakEquivalences (X : SSet.{u}) :
    realizationWeakEquivalences (exInfinityUnit.app X) := by
  rw [exInfinityUnit_app_eq]
  apply SSet.realizationWeakEquivalences.of_isColimit_nat_mono
    (exTowerFromZero X) (Limits.isColimitConstCocone ℕ X)
      (colimit.isColimit (exTower X))
      (exTowerZeroHom X ≫ colimit.ι (exTower X) 0)
  · intro n
    change 𝟙 X ≫
        (exTowerZeroHom X ≫ colimit.ι (exTower X) 0) =
      (exTowerZeroHom X ≫
          (exTower X).map (homOfLE (Nat.zero_le n))) ≫
        colimit.ι (exTower X) n
    simp only [Category.id_comp, Category.assoc]
    rw [colimit.w (exTower X) (homOfLE (Nat.zero_le n))]
  · intro i j f
    change Mono (𝟙 X)
    infer_instance
  · intro i j f
    exact exTower_map_mono X f
  · exact exTowerFromZero_app_mem X

end SSet

end
