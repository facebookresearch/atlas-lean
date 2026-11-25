/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.IteratedCupRestriction

/-!
# Head-recursive positive iterated cups

The head-recursive iterated cup uses nonempty right-associated tensor-power
coefficients, so each successor is definitionally a target-normalized
`(1,q)` cup.  It is canonically equal to the existing left-associated
iterated cup after reassociating coefficients.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Head-recursive positive iterated cup with right-associated coefficient
tensor powers.  The parameter `n` represents weight and degree `n + 1`. -/
noncomputable def iteratedCupClassCons (A : Rep k G) :
    ∀ (n : ℕ) (_x : Fin (n + 1) → groupCohomology.H1 A),
      groupCohomology
        (TensorPower.tensorPowObjRightSucc A n) (n + 1)
  | 0, x => x 0
  | n + 1, x =>
      cupOneAny A (TensorPower.tensorPowObjRightSucc A n) (n + 1)
        (x 0 ⊗ₜ[k]
          iteratedCupClassCons A n (fun i => x i.succ))

@[simp]
theorem iteratedCupClassCons_zero
    (A : Rep k G) (x : Fin 1 → groupCohomology.H1 A) :
    iteratedCupClassCons A 0 x = x 0 :=
  rfl

@[simp]
theorem iteratedCupClassCons_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 2) → groupCohomology.H1 A) :
    iteratedCupClassCons A (n + 1) x =
      cupOneAny A (TensorPower.tensorPowObjRightSucc A n) (n + 1)
        (x 0 ⊗ₜ[k]
          iteratedCupClassCons A n (fun i => x i.succ)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Reassociating coefficients carries the left-associated positive
iterated cup to the head-recursive iterated cup. -/
theorem iteratedCupClassSucc_to_cons
    (A : Rep k G) :
    ∀ (n : ℕ) (x : Fin (n + 1) → groupCohomology.H1 A),
      (map (MonoidHom.id G)
        (TensorPower.tensorPowObjRightSuccIso A n).hom (n + 1)).hom
          (iteratedCupClassSucc A n x) =
        iteratedCupClassCons A n x
  | 0, x => by
      rw [iteratedCupClassSucc_zero]
      rw [TensorPower.tensorPowObjRightSuccIso_zero]
      rw [← ConcreteCategory.comp_apply, ← map_id_comp]
      rw [Iso.inv_hom_id]
      change (map (MonoidHom.id G) (𝟙 A) 1).hom (x 0) = x 0
      rw [map_id]
      rfl
  | n + 1, x => by
      rw [TensorPower.tensorPowObjRightSuccIso_succ]
      simp only [Iso.trans_hom]
      rw [map_id_comp]
      simp only [ConcreteCategory.comp_apply]
      rw [iteratedCupClassSucc_headTail]
      have hnat := ConcreteCategory.congr_hom
        (cupOneAny_naturality
          (𝟙 A) (TensorPower.tensorPowObjRightSuccIso A n).hom (n + 1))
        (x 0 ⊗ₜ[k]
          iteratedCupClassSucc A n (fun i => x i.succ))
      rw [map_id] at hnat
      have hnat_apply :
          (map (MonoidHom.id G)
            (𝟙 A ⊗ₘ (TensorPower.tensorPowObjRightSuccIso A n).hom)
            (n + 2)).hom
            (cupOneAny A (TensorPower.tensorPowObj A (n + 1)) (n + 1)
              (x 0 ⊗ₜ[k]
                iteratedCupClassSucc A n (fun i => x i.succ))) =
          cupOneAny A (TensorPower.tensorPowObjRightSucc A n) (n + 1)
            (x 0 ⊗ₜ[k]
              (map (MonoidHom.id G)
                (TensorPower.tensorPowObjRightSuccIso A n).hom
                (n + 1)).hom
                (iteratedCupClassSucc A n (fun i => x i.succ))) := by
        convert hnat using 1
        all_goals rfl
      change (map (MonoidHom.id G)
          (𝟙 A ⊗ₘ (TensorPower.tensorPowObjRightSuccIso A n).hom)
          (n + 2)).hom
          (cupOneAny A (TensorPower.tensorPowObj A (n + 1)) (n + 1)
            (x 0 ⊗ₜ[k]
              iteratedCupClassSucc A n (fun i => x i.succ))) = _
      rw [hnat_apply, iteratedCupClassSucc_to_cons]
      rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Inverse orientation of the comparison between head-recursive and
left-associated positive iterated cups. -/
theorem iteratedCupClassCons_to_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A) :
    (map (MonoidHom.id G)
      (TensorPower.tensorPowObjRightSuccIso A n).inv (n + 1)).hom
        (iteratedCupClassCons A n x) =
      iteratedCupClassSucc A n x := by
  rw [← iteratedCupClassSucc_to_cons]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Iso.hom_inv_id]
  change (map (MonoidHom.id G)
    (𝟙 (TensorPower.tensorPowObj A (n + 1))) (n + 1)).hom
      (iteratedCupClassSucc A n x) = _
  rw [map_id]
  rfl

/-- Head-recursive ambient iterated cup with a distinguished final
degree-one class. -/
noncomputable def iteratedCupClassConsLast (A : Rep k G) :
    ∀ (n : ℕ) (_x : Fin n → groupCohomology.H1 A)
      (_y : groupCohomology.H1 A),
      groupCohomology
        (TensorPower.tensorPowObjRightSucc A n) (n + 1)
  | 0, _, y => y
  | n + 1, x, y =>
      cupOneAny A (TensorPower.tensorPowObjRightSucc A n) (n + 1)
        (x 0 ⊗ₜ[k]
          iteratedCupClassConsLast A n (fun i => x i.succ) y)

/-- Head-recursive mixed iterated cup along an arbitrary group homomorphism.
Its coefficient is the restriction of the ambient right-associated positive
tensor power. -/
noncomputable def restrictedIteratedCupClassConsLastOfHom
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G) :
    ∀ (n : ℕ) (_x : Fin n → groupCohomology.H1 A)
      (_y : groupCohomology.H1 (Rep.res f A)),
      groupCohomology
        (Rep.res f (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
  | 0, _, y => y
  | n + 1, x, y =>
      groupCohomology.map (MonoidHom.id H)
        (Rep.resTensorIso f A
          (TensorPower.tensorPowObjRightSucc A n)).hom (n + 2)
        (cupOneAny (Rep.res f A)
          (Rep.res f (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
          (groupCohomology.map f
              (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
            restrictedIteratedCupClassConsLastOfHom f A n
              (fun i => x i.succ) y))

@[simp]
theorem iteratedCupClassConsLast_zero
    (A : Rep k G) (x : Fin 0 → groupCohomology.H1 A)
    (y : groupCohomology.H1 A) :
    iteratedCupClassConsLast A 0 x y = y :=
  rfl

@[simp]
theorem iteratedCupClassConsLast_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A)
    (y : groupCohomology.H1 A) :
    iteratedCupClassConsLast A (n + 1) x y =
      cupOneAny A (TensorPower.tensorPowObjRightSucc A n) (n + 1)
        (x 0 ⊗ₜ[k]
          iteratedCupClassConsLast A n (fun i => x i.succ) y) :=
  rfl

@[simp]
theorem restrictedIteratedCupClassConsLastOfHom_zero
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G)
    (x : Fin 0 → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    restrictedIteratedCupClassConsLastOfHom f A 0 x y = y :=
  rfl

@[simp]
theorem restrictedIteratedCupClassConsLastOfHom_succ
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    restrictedIteratedCupClassConsLastOfHom f A (n + 1) x y =
      groupCohomology.map (MonoidHom.id H)
        (Rep.resTensorIso f A
          (TensorPower.tensorPowObjRightSucc A n)).hom (n + 2)
        (cupOneAny (Rep.res f A)
          (Rep.res f (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
          (groupCohomology.map f
              (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
            restrictedIteratedCupClassConsLastOfHom f A n
              (fun i => x i.succ) y)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Mapping a normalized restricted head-recursive cup through the canonical
right-tensor restriction comparison recovers the native head-recursive cup
over the source group. -/
theorem restrictedIteratedCupClassConsLastOfHom_to_native
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G) :
    ∀ (n : ℕ) (x : Fin n → groupCohomology.H1 A)
      (y : groupCohomology.H1 (Rep.res f A)),
      (map (MonoidHom.id H)
        (Rep.resTensorPowRightSuccIso f
          (Iso.refl (Rep.res f A)) n).hom (n + 1)).hom
          (restrictedIteratedCupClassConsLastOfHom f A n x y) =
        iteratedCupClassConsLast (Rep.res f A) n
          (fun i => groupCohomology.map f
            (𝟙 (Rep.res f A)) 1 (x i)) y
  | 0, x, y => by
      rw [restrictedIteratedCupClassConsLastOfHom_zero,
        iteratedCupClassConsLast_zero,
        Rep.resTensorPowRightSuccIso_zero]
      change (map (MonoidHom.id H) (𝟙 (Rep.res f A)) 1).hom y = y
      rw [map_id]
      rfl
  | n + 1, x, y => by
      rw [restrictedIteratedCupClassConsLastOfHom_succ,
        iteratedCupClassConsLast_succ,
        Rep.resTensorPowRightSuccIso_succ]
      simp only [Iso.trans_hom, Iso.symm_hom]
      dsimp only [TensorPower.tensorPowObjRightSucc]
      rw [← ConcreteCategory.comp_apply, ← map_id_comp]
      have hcoeff :
          (Rep.resTensorIso f A
              (TensorPower.tensorPowObjRightSucc A n)).hom ≫
            ((Rep.resTensorIso f A
              (TensorPower.tensorPowObjRightSucc A n)).inv ≫
              (tensorIso (Iso.refl (Rep.res f A))
                (Rep.resTensorPowRightSuccIso f
                  (Iso.refl (Rep.res f A)) n)).hom) =
          (tensorIso (Iso.refl (Rep.res f A))
            (Rep.resTensorPowRightSuccIso f
              (Iso.refl (Rep.res f A)) n)).hom := by
        simp
      rw [hcoeff]
      have htensor :
          (tensorIso (Iso.refl (Rep.res f A))
            (Rep.resTensorPowRightSuccIso f
              (Iso.refl (Rep.res f A)) n)).hom =
            𝟙 (Rep.res f A) ⊗ₘ
              (Rep.resTensorPowRightSuccIso f
                (Iso.refl (Rep.res f A)) n).hom :=
        rfl
      rw [htensor]
      have hnat := ConcreteCategory.congr_hom
        (cupOneAny_naturality
          (𝟙 (Rep.res f A))
          (Rep.resTensorPowRightSuccIso f
            (Iso.refl (Rep.res f A)) n).hom (n + 1))
        (groupCohomology.map f
            (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
          restrictedIteratedCupClassConsLastOfHom f A n
            (fun i => x i.succ) y)
      rw [map_id] at hnat
      have hnat_apply :
          (map (MonoidHom.id H)
            (𝟙 (Rep.res f A) ⊗ₘ
              (Rep.resTensorPowRightSuccIso f
                (Iso.refl (Rep.res f A)) n).hom) (n + 2)).hom
            (cupOneAny (Rep.res f A)
              (Rep.res f (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
              (groupCohomology.map f
                  (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
                restrictedIteratedCupClassConsLastOfHom f A n
                  (fun i => x i.succ) y)) =
          cupOneAny (Rep.res f A)
              (TensorPower.tensorPowObjRightSucc (Rep.res f A) n) (n + 1)
            (groupCohomology.map f
                (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
              (map (MonoidHom.id H)
                (Rep.resTensorPowRightSuccIso f
                  (Iso.refl (Rep.res f A)) n).hom (n + 1)).hom
                (restrictedIteratedCupClassConsLastOfHom f A n
                  (fun i => x i.succ) y)) := by
        convert hnat using 1
        all_goals rfl
      refine hnat_apply.trans ?_
      rw [restrictedIteratedCupClassConsLastOfHom_to_native]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Inverse normalization formula for a native source-group head-recursive
cup. -/
theorem restrictedIteratedCupClassConsLastOfHom_from_native
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G)
    (n : ℕ) (x : Fin n → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    (map (MonoidHom.id H)
      (Rep.resTensorPowRightSuccIso f
        (Iso.refl (Rep.res f A)) n).inv (n + 1)).hom
        (iteratedCupClassConsLast (Rep.res f A) n
          (fun i => groupCohomology.map f
            (𝟙 (Rep.res f A)) 1 (x i)) y) =
      restrictedIteratedCupClassConsLastOfHom f A n x y := by
  rw [← restrictedIteratedCupClassConsLastOfHom_to_native]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Iso.hom_inv_id]
  change (map (MonoidHom.id H)
    (𝟙 (Rep.res f (TensorPower.tensorPowObjRightSucc A n)))
    (n + 1)).hom
      (restrictedIteratedCupClassConsLastOfHom f A n x y) = _
  rw [map_id]
  rfl

/-- The distinguished-final-entry recursion is the ordinary head-recursive
cup on the tuple obtained by appending the final class. -/
theorem iteratedCupClassConsLast_eq_snoc
    (A : Rep k G) :
    ∀ (n : ℕ) (x : Fin n → groupCohomology.H1 A)
      (y : groupCohomology.H1 A),
      iteratedCupClassConsLast A n x y =
        iteratedCupClassCons A n (Fin.snoc x y)
  | 0, x, y => by
      rw [iteratedCupClassConsLast_zero, iteratedCupClassCons_zero]
      change y = Fin.snoc (α := fun _ => groupCohomology.H1 A)
        x y (Fin.last 0)
      rw [Fin.snoc_last]
  | n + 1, x, y => by
      have hz0 : Fin.snoc (α := fun _ => groupCohomology.H1 A)
          x y 0 = x 0 := by
        change Fin.snoc (α := fun _ => groupCohomology.H1 A)
          x y (0 : Fin (n + 1)).castSucc = x 0
        rw [Fin.snoc_castSucc]
      have hztail : (fun i => Fin.snoc
          (α := fun _ => groupCohomology.H1 A) x y i.succ) =
          Fin.snoc (α := fun _ => groupCohomology.H1 A)
            (fun i => x i.succ) y := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · change Fin.snoc (α := fun _ => groupCohomology.H1 A)
            x y j.succ.castSucc = _
          rw [Fin.snoc_castSucc]
          rw [Fin.snoc_castSucc]
      rw [iteratedCupClassConsLast_succ, iteratedCupClassCons_succ,
        hz0, hztail, iteratedCupClassConsLast_eq_snoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Reassociating a distinguished-final-entry head-recursive cup back to
the canonical left tensor power gives the ordinary iterated cup on the
appended tuple. -/
theorem iteratedCupClassConsLast_to_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin n → groupCohomology.H1 A)
    (y : groupCohomology.H1 A) :
    (map (MonoidHom.id G)
      (TensorPower.tensorPowObjRightSuccIso A n).inv (n + 1)).hom
        (iteratedCupClassConsLast A n x y) =
      iteratedCupClassSucc A n (Fin.snoc x y) := by
  rw [iteratedCupClassConsLast_eq_snoc]
  exact iteratedCupClassCons_to_succ A n (Fin.snoc x y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Reassociating the normalized restricted head-recursive cup gives the
ordinary normalized restricted iterated cup. -/
theorem restrictedIteratedCupClassConsLastOfHom_reassociate
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G)
    (n : ℕ) (x : Fin n → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    (map (MonoidHom.id H)
      ((Rep.resFunctor f).map
        (TensorPower.tensorPowObjRightSuccIso A n).inv)
      (n + 1)).hom
        (restrictedIteratedCupClassConsLastOfHom f A n x y) =
      restrictedIteratedCupClassSuccLastOfHom f A n x y := by
  unfold restrictedIteratedCupClassSuccLastOfHom
    restrictedIteratedCupClassSucc
  rw [← restrictedIteratedCupClassConsLastOfHom_from_native]
  rw [iteratedCupClassConsLast_eq_snoc]
  rw [← iteratedCupClassSucc_to_cons]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Rep.resTensorPow_reassociation_coherence]

end groupCohomology
