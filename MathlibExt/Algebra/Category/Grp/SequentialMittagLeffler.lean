/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOne
public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialMittagLeffler
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Mittag--Leffler vanishing of sequential lim-one in abelian groups

For an inverse sequence of abelian groups satisfying Mittag--Leffler, every
tuple is a standard `1 - shift` difference.  The proof forms the affine tower
`x ↦ bₙ + tₙ x`, transfers range stabilization from the original linear
tower, and uses the existing nonempty-section theorem.  Surjectivity makes the
accepted sequential difference epi, so the existing generic cokernel theorem
gives zero concrete sequential `lim¹`.

The tuple-preimage theorem is stated literally on dependent functions so the
same proof can be reused after forgetting a module tower to abelian groups.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Set

namespace AddCommGrpCat

private def affineTransition
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (b : ∀ n : ℕ, A.obj (op n)) (n : ℕ) :
    (A.obj (op (n + 1)) : Type u) ⟶ (A.obj (op n) : Type u) :=
  ↾(fun x => b n + A.map (homOfLE (Nat.le_succ n)).op x)

private abbrev affineTower
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (b : ∀ n : ℕ, A.obj (op n)) : ℕᵒᵖ ⥤ Type u :=
  Functor.ofOpSequence (C := Type u)
    (X := fun n => A.obj (op n)) (affineTransition A b)

private def affineMap
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (b : ∀ n : ℕ, A.obj (op n)) {n m : ℕ} (h : n ≤ m)
    (x : A.obj (op m)) : A.obj (op n) :=
  (affineTower A b).map (homOfLE h).op x

private theorem affineMap_step
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (b : ∀ n : ℕ, A.obj (op n)) {n m : ℕ} (h : n ≤ m)
    (x : A.obj (op (m + 1))) :
    affineMap A b (Nat.le.step h) x =
      affineMap A b h
        (b m + A.map (homOfLE (Nat.le_succ m)).op x) := by
  change (affineTower A b).obj (op (m + 1)) at x
  unfold affineMap
  have heq : (homOfLE (Nat.le.step h)).op =
      (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op :=
    Subsingleton.elim _ _
  rw [heq, (affineTower A b).map_comp]
  rw [ConcreteCategory.comp_apply,
    Functor.ofOpSequence_map_homOfLE_succ]
  rfl

private theorem affineTower_map_eq
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (b : ∀ n : ℕ, A.obj (op n)) {n m : ℕ} (h : n ≤ m)
    (x : A.obj (op m)) :
    affineMap A b h x = affineMap A b h 0 +
        A.map (homOfLE h).op x := by
  induction m, h using Nat.le_induction with
  | base =>
      unfold affineMap
      have heq : (homOfLE (Nat.le_refl n)).op = 𝟙 (op n) :=
        Subsingleton.elim _ _
      rw [heq, (affineTower A b).map_id, A.map_id]
      change x = (0 : A.obj (op n)) + x
      exact (zero_add x).symm
  | succ m h ih =>
      rw [affineMap_step A b h x]
      calc
        affineMap A b h
            (b m + A.map (homOfLE (Nat.le_succ m)).op x) =
            affineMap A b h 0 + A.map (homOfLE h).op
                (b m + A.map (homOfLE (Nat.le_succ m)).op x) :=
          ih _
        _ = (affineMap A b h 0 + A.map (homOfLE h).op (b m)) +
              A.map (homOfLE h).op
                (A.map (homOfLE (Nat.le_succ m)).op x) := by
          rw [map_add, add_assoc]
        _ = affineMap A b h (b m) +
              A.map (homOfLE h).op
                (A.map (homOfLE (Nat.le_succ m)).op x) := by
          rw [← ih (b m)]
        _ = affineMap A b (Nat.le.step h) 0 +
              A.map (homOfLE (Nat.le.step h)).op x := by
          rw [affineMap_step A b h 0]
          simp only [map_zero, add_zero]
          have heq : (homOfLE (Nat.le.step h)).op =
              (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op :=
            Subsingleton.elim _ _
          rw [heq, A.map_comp]
          rfl

/-- Every tuple in a Mittag--Leffler inverse sequence of abelian groups is a
literal `1 - shift` difference.  This dependent-function form is the shared
low-level bridge for module towers. -/
theorem exists_oneSubShift_preimage_of_isMittagLeffler
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : A.IsSequentialMittagLeffler)
    (b : ∀ n : ℕ, A.obj (op n)) :
    ∃ a : ∀ n : ℕ, A.obj (op n), ∀ n : ℕ,
      a n - A.map (homOfLE (Nat.le_succ n)).op (a (n + 1)) = b n := by
  let F := affineTower A b
  have hstab :=
    (CategoryTheory.Functor.isSequentialMittagLeffler_iff_range_stabilizes A).1 hA
  have hF : F.IsMittagLeffler := by
    rw [F.isMittagLeffler_iff_subset_range_comp]
    rintro ⟨n⟩
    obtain ⟨m, hnm, hm⟩ := hstab n
    let f : op m ⟶ op n := (homOfLE hnm).op
    refine ⟨op m, f, ?_⟩
    rintro ⟨k⟩ g
    let hmk : m ≤ k := leOfHom g.unop
    have hg : g = (homOfLE hmk).op := Subsingleton.elim _ _
    rw [hg]
    rintro y ⟨x, rfl⟩
    change A.obj (op m) at x
    change ∃ z : A.obj (op k),
      affineMap A b (hnm.trans hmk) z = affineMap A b hnm x
    let c : A.obj (op m) := affineMap A b hmk 0
    have hdRange :
        affineMap A b hnm x - affineMap A b hnm c ∈
          range ((A ⋙ forget AddCommGrpCat).map f) := by
      refine ⟨x - c, ?_⟩
      change A.map f (x - c) =
        affineMap A b hnm x - affineMap A b hnm c
      rw [map_sub, affineTower_map_eq A b hnm x,
        affineTower_map_eq A b hnm c, add_sub_add_left_eq_sub]
    have hm' := hm k hmk
    change range ((A ⋙ forget AddCommGrpCat).map
        (homOfLE (hnm.trans hmk)).op) =
      range ((A ⋙ forget AddCommGrpCat).map f) at hm'
    rw [← hm'] at hdRange
    obtain ⟨d, hd⟩ := hdRange
    refine ⟨d, ?_⟩
    have hzero :
        affineMap A b (hnm.trans hmk) 0 = affineMap A b hnm c := by
      have hcomp : (homOfLE (hnm.trans hmk)).op =
          (homOfLE hmk).op ≫ f := Subsingleton.elim _ _
      unfold affineMap
      rw [hcomp, F.map_comp]
      rfl
    change A.map (homOfLE (hnm.trans hmk)).op d =
      affineMap A b hnm x - affineMap A b hnm c at hd
    calc
      affineMap A b (hnm.trans hmk) d =
          affineMap A b (hnm.trans hmk) 0 +
            A.map (homOfLE (hnm.trans hmk)).op d :=
        affineTower_map_eq A b (hnm.trans hmk) d
      _ = affineMap A b hnm c +
          (affineMap A b hnm x - affineMap A b hnm c) := by
        rw [hzero, hd]
      _ = affineMap A b hnm x := by
        rw [add_comm, sub_add_cancel]
  let _ (j : ℕᵒᵖ) : Nonempty (F.obj j) := by
    rcases j with ⟨n⟩
    change Nonempty (A.obj (op n))
    infer_instance
  obtain ⟨s⟩ :=
    CategoryTheory.Functor.nonempty_sections_of_isMittagLeffler F hF
  let a : ∀ n : ℕ, A.obj (op n) := fun n => s.val (op n)
  refine ⟨a, fun n => ?_⟩
  have hs := s.prop (homOfLE (Nat.le_succ n)).op
  change (affineTower A b).map (homOfLE (Nat.le_succ n)).op
    (a (n + 1)) = a n at hs
  rw [Functor.ofOpSequence_map_homOfLE_succ] at hs
  change a n - A.map (homOfLE (Nat.le_succ n)).op (a (n + 1)) = b n
  rw [← hs]
  change (b n + A.map (homOfLE (Nat.le_succ n)).op (a (n + 1))) -
      A.map (homOfLE (Nat.le_succ n)).op (a (n + 1)) = b n
  exact add_sub_cancel_right _ _

/-- The standard sequential difference of a Mittag--Leffler inverse sequence
of abelian groups is an epimorphism. -/
theorem epi_sequentialDifference_of_isMittagLeffler
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : A.IsSequentialMittagLeffler) :
    Epi (sequentialDifference A) := by
  apply (AddCommGrpCat.epi_iff_surjective _).2
  intro b
  let Z : ℕ → AddCommGrpCat.{u} := fun n => A.obj (op n)
  let e := Limits.Concrete.productEquiv Z
  obtain ⟨a, ha⟩ :=
    exists_oneSubShift_preimage_of_isMittagLeffler A hA (e b)
  refine ⟨e.symm a, ?_⟩
  apply e.injective
  funext n
  have h := ConcreteCategory.congr_hom
    (sequentialDifference_π A n) (e.symm a)
  have hcoord :
      e (sequentialDifference A (e.symm a)) n =
        a n - A.map (homOfLE (Nat.le_succ n)).op (a (n + 1)) := by
    change
      Pi.π (fun j : ℕ => A.obj (op j)) n
          (sequentialDifference A (e.symm a)) =
        Pi.π (fun j : ℕ => A.obj (op j)) n (e.symm a) -
          A.map (homOfLE (Nat.le_succ n)).op
            (Pi.π (fun j : ℕ => A.obj (op j)) (n + 1) (e.symm a)) at h
    simpa only [e, Z, Limits.Concrete.productEquiv_apply_apply,
      Limits.Concrete.productEquiv_symm_apply_π] using h
  rw [hcoord, ha n]

/-- A Mittag--Leffler inverse sequence of abelian groups has zero concrete
sequential `lim¹`. -/
theorem isZero_sequentialLimOne_of_isMittagLeffler
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : A.IsSequentialMittagLeffler) :
    IsZero (sequentialLimOne A) :=
  @CategoryTheory.Limits.isZero_sequentialLimOne_of_epi
    AddCommGrpCat.{u} _ _ _ _ A
      (epi_sequentialDifference_of_isMittagLeffler A hA)

/-- Eventually epimorphic successor transitions imply the
Mittag--Leffler condition for an inverse sequence of abelian groups. -/
theorem isMittagLeffler_of_eventually_transition_epi
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Epi (A.map (homOfLE (Nat.le_succ n)).op)) :
    A.IsSequentialMittagLeffler := by
  apply CategoryTheory.Functor.isMittagLeffler_of_eventually_surjective_transition
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  let _ : Epi (A.map (homOfLE (Nat.le_succ n)).op) := hN n hn
  exact (AddCommGrpCat.epi_iff_surjective _).1 inferInstance

/-- Epimorphic successor transitions imply the Mittag--Leffler condition for
an inverse sequence of abelian groups. -/
theorem isMittagLeffler_of_transition_epi
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    [∀ n : ℕ, Epi (A.map (homOfLE (Nat.le_succ n)).op)] :
    A.IsSequentialMittagLeffler :=
  isMittagLeffler_of_eventually_transition_epi A
    ⟨0, fun _ _ => inferInstance⟩

/-- Eventually epimorphic successor transitions give zero concrete
sequential `lim¹` for an inverse sequence of abelian groups. -/
theorem isZero_sequentialLimOne_of_eventually_transition_epi
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Epi (A.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero (sequentialLimOne A) :=
  isZero_sequentialLimOne_of_isMittagLeffler A
    (isMittagLeffler_of_eventually_transition_epi A h)

/-- Epimorphic successor transitions give zero concrete sequential `lim¹`
for an inverse sequence of abelian groups. -/
theorem isZero_sequentialLimOne_of_transition_epi
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    [∀ n : ℕ, Epi (A.map (homOfLE (Nat.le_succ n)).op)] :
    IsZero (sequentialLimOne A) :=
  isZero_sequentialLimOne_of_isMittagLeffler A
    (isMittagLeffler_of_transition_epi A)

end AddCommGrpCat

end
