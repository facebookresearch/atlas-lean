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
# Mittag–Leffler vanishing of sequential lim-one

Let A:ℕᵒᵖ→Ab_u be an inverse sequence, with transition maps t_n:A_{n+1}→A_n. Its difference map
on the full product is D(a)_n=a_n-t_n(a_{n+1}), and sequential lim-one is coker(D).

If the images of A_m→A_n stabilize for each n as m increases, then every product tuple b has a
preimage under D. The affine transition x↦b_n+t_n(x) has the same image-stabilization property
and a compatible section, which solves a_n-t_n(a_{n+1})=b_n for all n. Thus D is epi and its
cokernel is zero.

Surjectivity of all sufficiently late successor transitions implies the Mittag–Leffler
condition. In particular, both an eventually epi tower and an everywhere epi tower have zero
sequential lim-one.
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

/-- Let A:ℕᵒᵖ→AddCommGrpCat_u be an inverse sequence, A_n=A(n), and t_n:A_{n+1}→A_n its successor
transition. Assume the sequence is Mittag–Leffler: for each n, the images of A_m→A_n stabilize
for all sufficiently large m≥n. For every b∈∏_n A_n there exists a∈∏_n A_n with
a_n-t_n(a_{n+1})=b_n for every n≥0. The construction uses the entire dependent tuple of group
coefficients. -/
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

/-- Let A:ℕᵒᵖ→AddCommGrpCat_u be an inverse sequence, A_n=A(n), and t_n:A_{n+1}→A_n its successor
transition. Assume the sequence is Mittag–Leffler: for each n, the images of A_m→A_n stabilize
for all sufficiently large m≥n. The difference map D:∏_n A_n→∏_n A_n is D(a)_n=a_n-t_n(a_{n+1}),
and its cokernel is the sequential lim-one object. The map D is an epimorphism of abelian
groups, equivalently every tuple b has a tuple a with D(a)=b. -/
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

/-- Let A:ℕᵒᵖ→AddCommGrpCat_u be an inverse sequence, A_n=A(n), and t_n:A_{n+1}→A_n its successor
transition. Assume the sequence is Mittag–Leffler: for each n, the images of A_m→A_n stabilize
for all sufficiently large m≥n. The difference map D:∏_n A_n→∏_n A_n is D(a)_n=a_n-t_n(a_{n+1}),
and its cokernel is the sequential lim-one object. The sequential lim-one object coker(D) is a
zero abelian group because D is epi. -/
theorem isZero_sequentialLimOne_of_isMittagLeffler
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : A.IsSequentialMittagLeffler) :
    IsZero (sequentialLimOne A) :=
  @CategoryTheory.Limits.isZero_sequentialLimOne_of_epi
    AddCommGrpCat.{u} _ _ _ _ A
      (epi_sequentialDifference_of_isMittagLeffler A hA)

/-- Let A:ℕᵒᵖ→AddCommGrpCat_u be an inverse sequence, A_n=A(n), and t_n:A_{n+1}→A_n its successor
transition. If there exists N∈ℕ such that t_n is epi for every n≥N, the sequence is
Mittag–Leffler. For each fixed target A_r, the images of A_m→A_r stabilize once the surjective
tail begins. -/
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

/-- Let A:ℕᵒᵖ→AddCommGrpCat_u be an inverse sequence, A_n=A(n), and t_n:A_{n+1}→A_n its successor
transition. If every successor map t_n is epi, then the sequence is Mittag–Leffler. Every
composite A_m→A_n for m≥n is surjective, so its image is all of A_n. -/
theorem isMittagLeffler_of_transition_epi
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    [∀ n : ℕ, Epi (A.map (homOfLE (Nat.le_succ n)).op)] :
    A.IsSequentialMittagLeffler :=
  isMittagLeffler_of_eventually_transition_epi A
    ⟨0, fun _ _ => inferInstance⟩

/-- Let A:ℕᵒᵖ→AddCommGrpCat_u be an inverse sequence, A_n=A(n), and t_n:A_{n+1}→A_n its successor
transition. The difference map D:∏_n A_n→∏_n A_n is D(a)_n=a_n-t_n(a_{n+1}), and its cokernel is
the sequential lim-one object. If some N satisfies that t_n is epi for every n≥N, then coker(D)
is a zero object of abelian groups. Eventual surjectivity gives image stabilization and
surjectivity of the full difference map. -/
theorem isZero_sequentialLimOne_of_eventually_transition_epi
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Epi (A.map (homOfLE (Nat.le_succ n)).op)) :
    IsZero (sequentialLimOne A) :=
  isZero_sequentialLimOne_of_isMittagLeffler A
    (isMittagLeffler_of_eventually_transition_epi A h)

/-- Let A:ℕᵒᵖ→AddCommGrpCat_u be an inverse sequence, A_n=A(n), and t_n:A_{n+1}→A_n its successor
transition. The difference map D:∏_n A_n→∏_n A_n is D(a)_n=a_n-t_n(a_{n+1}), and its cokernel is
the sequential lim-one object. If t_n is epi for all n≥0, the sequential lim-one object coker(D)
is zero. Each product tuple b is of the form a_n-t_n(a_{n+1}) for a compatible difference
preimage a. -/
theorem isZero_sequentialLimOne_of_transition_epi
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    [∀ n : ℕ, Epi (A.map (homOfLE (Nat.le_succ n)).op)] :
    IsZero (sequentialLimOne A) :=
  isZero_sequentialLimOne_of_isMittagLeffler A
    (isMittagLeffler_of_transition_epi A)

end AddCommGrpCat

end
