/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.SocialChoice.Black
import MathlibExt.GameTheory.SocialChoice.ArrowImpossibility
public import MathlibExt.GameTheory.Matching.StableMechanism
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Tests for the social-choice audit module

- T1: the dictator social welfare function is Pareto and IIA, hence
  dictatorial by C1, with witness dictator `0`.
- T2: a single-peaked profile with peaks `0, 1, 2`; its pairwise majorities,
  one of them also derived via C4.
- T3: the cyclic profile is not single-peaked; an even-electorate tie has no
  majority either way.
- T4: recomputed Borda values and agreement for the two C6 profiles.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExtTest.GameTheory.SocialChoice.Black

open MathlibExt.Order
open MathlibExt.GameTheory.SocialChoice
open MathlibExt.GameTheory.SocialChoice.ArrowWanted
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle
open MathlibExt.GameTheory.Matching.StableMechanism

/- C1 audit: strict Arrow statement derived from the relation form
`MetaMathlibExt.arrowImpossibility` only; the canonical strict theorem
remains `ArrowWanted.arrow_impossibility`. -/
private def sEncode {Alt : Type*} (T : ArrowWanted.StrictTotalOrder Alt) :
    Alt → Alt → Prop :=
  fun a b => ¬ T.lt b a

private theorem isPreorder_sEncode {Alt : Type*}
    (T : ArrowWanted.StrictTotalOrder Alt) : IsPreorder Alt (sEncode T) := by
  have hR : Std.Refl (sEncode T) := ⟨fun a => T.irrefl a⟩
  have hT : IsTrans Alt (sEncode T) := by
    refine ⟨?_⟩
    intro a b c hab hbc hca
    by_cases hba : b = a
    · subst hba; exact hbc hca
    · rcases T.total hba with h | h
      · exact hab h
      · by_cases hcb : c = b
        · subst hcb; exact hab hca
        · rcases T.total hcb with h2 | h2
          · exact hbc h2
          · exact hab (T.trans h2 hca)
  exact @IsPreorder.mk _ _ hR hT

private theorem total_sEncode {Alt : Type*}
    (T : ArrowWanted.StrictTotalOrder Alt) :
    ∀ x y, sEncode T x y ∨ sEncode T y x := by
  intro x y
  show (¬ T.lt y x) ∨ (¬ T.lt x y)
  by_cases h : x = y
  · subst h
    exact Or.inl (T.irrefl _)
  · rcases T.total h with h1 | h1
    · exact Or.inl (fun h2 => T.irrefl _ (T.trans h2 h1))
    · exact Or.inr (fun h2 => T.irrefl _ (T.trans h1 h2))

private theorem strict_sEncode {Alt : Type*}
    (T : ArrowWanted.StrictTotalOrder Alt) (a b : Alt) :
    (sEncode T a b ∧ ¬ sEncode T b a) ↔ T.lt a b := by
  change ((¬ T.lt b a) ∧ ¬ ¬ T.lt a b) ↔ T.lt a b
  constructor
  · rintro ⟨-, h⟩
    exact Classical.byContradiction h
  · intro h
    exact ⟨fun h2 => T.irrefl _ (T.trans h h2), fun h2 => h2 h⟩

private noncomputable def tieBreak (Alt : Type*) [Fintype Alt] [DecidableEq Alt] :
    ArrowWanted.StrictTotalOrder Alt where
  lt := fun a b => Fintype.equivFin Alt a < Fintype.equivFin Alt b
  irrefl := fun _ h => Nat.lt_irrefl _ h
  trans := fun {_ _ _} h1 h2 => Nat.lt_trans h1 h2
  total := fun {_ _} hab => lt_or_gt_of_ne (fun h => hab ((Fintype.equivFin Alt).injective h))

private noncomputable def sStrict {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (R : Alt → Alt → Prop) (hPre : IsPreorder Alt R)
    (hTot : ∀ x y, R x y ∨ R y x) : ArrowWanted.StrictTotalOrder Alt where
  lt := fun a b => R a b ∧ (¬ R b a ∨ (tieBreak Alt).lt a b)
  irrefl := fun a h => by
    have h' : R a a ∧ (¬ R a a ∨ (tieBreak Alt).lt a a) := h
    obtain ⟨hraa, hOr⟩ := h'
    rcases hOr with h | ht
    · exact h hraa
    · exact (tieBreak Alt).irrefl a ht
  trans := fun {a b c} h1 h2 => by
    have g1 : R a b ∧ (¬ R b a ∨ (tieBreak Alt).lt a b) := h1
    have g2 : R b c ∧ (¬ R c b ∨ (tieBreak Alt).lt b c) := h2
    obtain ⟨hab, h1'⟩ := g1
    obtain ⟨hbc, h2'⟩ := g2
    change R a c ∧ (¬ R c a ∨ (tieBreak Alt).lt a c)
    refine ⟨@IsTrans.trans _ _ hPre.toIsTrans _ _ _ hab hbc, ?_⟩
    by_cases hca : R c a
    · refine Or.inr ?_
      have hba : R b a := @IsTrans.trans _ _ hPre.toIsTrans _ _ _ hbc hca
      have hcb : R c b := @IsTrans.trans _ _ hPre.toIsTrans _ _ _ hca hab
      have ht1 : (tieBreak Alt).lt a b := h1'.resolve_left (fun h => h hba)
      have ht2 : (tieBreak Alt).lt b c := h2'.resolve_left (fun h => h hcb)
      exact (tieBreak Alt).trans ht1 ht2
    · exact Or.inl hca
  total := fun {a b} hab => by
    show (R a b ∧ (¬ R b a ∨ (tieBreak Alt).lt a b)) ∨
      (R b a ∧ (¬ R a b ∨ (tieBreak Alt).lt b a))
    rcases hTot a b with h | h
    · by_cases hnba : R b a
      · rcases (tieBreak Alt).total hab with ht | ht
        · exact Or.inl ⟨h, Or.inr ht⟩
        · exact Or.inr ⟨hnba, Or.inr ht⟩
      · exact Or.inl ⟨h, Or.inl hnba⟩
    · by_cases hnab : R a b
      · rcases (tieBreak Alt).total hab with ht | ht
        · exact Or.inl ⟨hnab, Or.inr ht⟩
        · exact Or.inr ⟨h, Or.inr ht⟩
      · exact Or.inr ⟨h, Or.inl hnab⟩

private noncomputable def sProfile {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    (P : Voter → Alt → Alt → Prop)
    (hP : ∀ v, IsPreorder Alt (P v) ∧ ∀ x y, P v x y ∨ P v y x) : Profile Alt Voter :=
  fun v => sStrict (P v) (hP v).1 (hP v).2

open Classical in
private noncomputable def sSocial {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] (F : SocialWelfareFunction Alt Voter)
    (P : Voter → Alt → Alt → Prop) : Alt → Alt → Prop :=
  if h : ∀ v ∈ Finset.univ, IsPreorder Alt (P v) ∧ ∀ x y, P v x y ∨ P v y x
  then sEncode (F (sProfile P (fun v => h v (Finset.mem_univ v))))
  else fun _ _ => True

private theorem sSocial_eq {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt] [Fintype Voter]
    (F : SocialWelfareFunction Alt Voter) (P : Voter → Alt → Alt → Prop)
    (hP : ∀ v ∈ Finset.univ, IsPreorder Alt (P v) ∧ ∀ x y, P v x y ∨ P v y x) :
    sSocial F P = sEncode (F (sProfile P (fun v => hP v (Finset.mem_univ v)))) :=
  dite_eq_left hP

private def sFwd {Alt : Type*} {Blt : Type*} (e : Alt ≃ Blt)
    (T : ArrowWanted.StrictTotalOrder Alt) : ArrowWanted.StrictTotalOrder Blt where
  lt := fun a b => T.lt (e.symm a) (e.symm b)
  irrefl := fun _ h => T.irrefl _ h
  trans := fun {_ _ _} h1 h2 => T.trans h1 h2
  total := fun {_ _} hab => T.total (fun h => hab (e.symm.injective h))

private def sBwd {Alt : Type*} {Blt : Type*} (e : Alt ≃ Blt)
    (S : ArrowWanted.StrictTotalOrder Blt) : ArrowWanted.StrictTotalOrder Alt where
  lt := fun a b => S.lt (e a) (e b)
  irrefl := fun _ h => S.irrefl _ h
  trans := fun {_ _ _} h1 h2 => S.trans h1 h2
  total := fun {_ _} hab => S.total (fun h => hab (e.injective h))

private theorem arrow_bridge_aux {A V : Type} [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (hA : ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (G : SocialWelfareFunction A V) (hPG : IsPareto G) (hIG : IsIIA G) : IsDictatorial G := by
  by_contra hCon
  refine MetaMathlibExt.arrowImpossibility Finset.univ (sSocial G) hA ?_ ?_ ?_ ?_ ?_
  · obtain ⟨d0⟩ := (inferInstance : Nonempty V); exact ⟨d0, Finset.mem_univ d0⟩
  · intro P hP; rw [sSocial_eq G P hP]; exact ⟨isPreorder_sEncode _, total_sEncode _⟩
  · intro P a b hP hall; rw [sSocial_eq G P hP]
    have hFab : (G (sProfile P (fun v => hP v (Finset.mem_univ v)))).lt a b :=
      hPG (sProfile P (fun v => hP v (Finset.mem_univ v))) a b (fun v => by
        change P v a b ∧ (¬ P v b a ∨ (tieBreak A).lt a b)
        exact ⟨(hall v (Finset.mem_univ v)).1, Or.inl (hall v (Finset.mem_univ v)).2⟩)
    exact (strict_sEncode _ _ _).mpr hFab
  · intro P Q a b hP hQ hAgree; rw [sSocial_eq G P hP, sSocial_eq G Q hQ]
    have ag1 : ∀ i, ((sProfile P (fun v => hP v (Finset.mem_univ v))) i).lt a b ↔
        ((sProfile Q (fun v => hQ v (Finset.mem_univ v))) i).lt a b := by
      intro i; change (P i a b ∧ (¬ P i b a ∨ (tieBreak A).lt a b)) ↔
        (Q i a b ∧ (¬ Q i b a ∨ (tieBreak A).lt a b))
      rw [(hAgree i (Finset.mem_univ i)).1, (hAgree i (Finset.mem_univ i)).2]
    have ag2 : ∀ i, ((sProfile P (fun v => hP v (Finset.mem_univ v))) i).lt b a ↔
        ((sProfile Q (fun v => hQ v (Finset.mem_univ v))) i).lt b a := by
      intro i; change (P i b a ∧ (¬ P i a b ∨ (tieBreak A).lt b a)) ↔
        (Q i b a ∧ (¬ Q i a b ∨ (tieBreak A).lt b a))
      rw [(hAgree i (Finset.mem_univ i)).2, (hAgree i (Finset.mem_univ i)).1]
    exact ⟨not_congr (hIG _ _ _ _ ag2), not_congr (hIG _ _ _ _ ag1)⟩
  · intro d hd
    have hNd : ¬ IsDictator G d := fun hh => hCon (show ∃ d, IsDictator G d from ⟨d, hh⟩)
    obtain ⟨p, a, b, hpd, hFp⟩ : ∃ p a b, (p d).lt a b ∧ ¬ (G p).lt a b := by
      by_contra hw; exact hNd (fun p a b h => by_contra (fun hc => hw ⟨p, a, b, h, hc⟩))
    have hTotP : ∀ v ∈ Finset.univ,
        IsPreorder A (sEncode (p v)) ∧ ∀ x y, sEncode (p v) x y ∨ sEncode (p v) y x :=
      fun v _ => ⟨isPreorder_sEncode _, total_sEncode _⟩
    refine ⟨fun (v : V) (x y : A) => sEncode (p v) x y, a, b, hTotP, ?_, ?_⟩
    · exact (strict_sEncode _ _ _).mpr hpd
    · have hEq := sSocial_eq G (fun (v : V) (x y : A) => sEncode (p v) x y) hTotP
      rw [hEq, strict_sEncode]
      have h2 : (G (sProfile (fun (v : V) (x y : A) => sEncode (p v) x y)
          (fun v => hTotP v (Finset.mem_univ v)))).lt a b ↔ (G p).lt a b :=
        hIG _ _ _ _ (fun i => by
          change ((¬ (p i).lt b a) ∧ (¬ ¬ (p i).lt a b ∨ (tieBreak A).lt a b)) ↔ (p i).lt a b
          constructor
          · rintro ⟨hnba, h⟩
            by_cases heq : a = b
            · subst heq
              rcases h with h | ht
              · exact Classical.byContradiction h
              · exact absurd ht ((tieBreak A).irrefl _)
            · rcases (p i).total heq with hside | hside
              · exact hside
              · exact absurd hside hnba
          · intro h
            exact ⟨fun hneg => (p i).irrefl _ ((p i).trans h hneg), Or.inl (fun hneg => hneg h)⟩)
      rw [h2]; exact hFp

/-- Arrow bridge from the relation form to the strict form (C1): the strict
Arrow statement, to be proved from `MetaMathlibExt.arrowImpossibility` as its
only Arrow input. -/
theorem arrow_impossibility_of_arrowImpossibility
    {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (F : SocialWelfareFunction Alt Voter)
    (hPareto : IsPareto F) (hIIA : IsIIA F) :
    IsDictatorial F := by
  set eA := Fintype.equivFin Alt; set eV := Fintype.equivFin Voter
  obtain ⟨a0, b0, c0, hab0, hac0, hbc0⟩ := hAlt
  obtain ⟨v0⟩ := (inferInstance : Nonempty Voter)
  have hAltF : ∃ a b c : Fin (Fintype.card Alt), a ≠ b ∧ a ≠ c ∧ b ≠ c :=
    ⟨eA a0, eA b0, eA c0, fun h => hab0 (eA.injective h),
      fun h => hac0 (eA.injective h), fun h => hbc0 (eA.injective h)⟩
  have hNeF : Nonempty (Fin (Fintype.card Voter)) := ⟨eV v0⟩
  set F' : SocialWelfareFunction (Fin (Fintype.card Alt)) (Fin (Fintype.card Voter)) :=
    fun p' => sFwd eA (F (fun v => sBwd eA (p' (eV v))))
  have hPF' : IsPareto F' := by
    intro p' a b hall; show (F (fun v => sBwd eA (p' (eV v)))).lt (eA.symm a) (eA.symm b)
    refine hPareto _ _ _ (fun v => ?_)
    show (p' (eV v)).lt (eA (eA.symm a)) (eA (eA.symm b))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hall (eV v)
  have hIF' : IsIIA F' := by
    intro p1' p2' a b hAg
    show (F (fun v => sBwd eA (p1' (eV v)))).lt (eA.symm a) (eA.symm b) ↔
      (F (fun v => sBwd eA (p2' (eV v)))).lt (eA.symm a) (eA.symm b)
    refine hIIA _ _ _ _ (fun v => ?_)
    show (p1' (eV v)).lt (eA (eA.symm a)) (eA (eA.symm b)) ↔
      (p2' (eV v)).lt (eA (eA.symm a)) (eA (eA.symm b))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hAg (eV v)
  obtain ⟨d', hd'⟩ := @arrow_bridge_aux _ _ _ _ _ _ hNeF hAltF F' hPF' hIF'
  show ∃ d, IsDictator F d
  refine ⟨eV.symm d', fun p a b h => ?_⟩
  have hPd : ((fun i => sFwd eA (p (eV.symm i))) d').lt (eA a) (eA b) := by
    change (p (eV.symm d')).lt (eA.symm (eA a)) (eA.symm (eA b))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact h
  have hFIff : (F (fun v => sBwd eA ((fun i => sFwd eA (p (eV.symm i))) (eV v)))).lt a b ↔
      (F p).lt a b := by
    refine hIIA _ _ _ _ (fun v => ?_)
    change (p (eV.symm (eV v))).lt (eA.symm (eA a)) (eA.symm (eA b)) ↔ (p v).lt a b
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hFold : (F' (fun i => sFwd eA (p (eV.symm i)))).lt (eA a) (eA b) :=
    hd' (fun i => sFwd eA (p (eV.symm i))) (eA a) (eA b) hPd
  have hFd' : (F (fun v => sBwd eA ((fun i => sFwd eA (p (eV.symm i))) (eV v)))).lt
      (eA.symm (eA a)) (eA.symm (eA b)) := hFold
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hFd'; exact hFIff.mp hFd'

/-- The dictator social welfare function `F p = p 0` (T1). -/
def dictSWF : SocialWelfareFunction (Fin 3) (Fin 2) := fun p => p 0

/-- `dictSWF` is Pareto (T1). -/
theorem dictSWF_pareto : IsPareto dictSWF := fun p a b h => h 0

/-- `dictSWF` is IIA (T1). -/
theorem dictSWF_iia : IsIIA dictSWF := fun p1 p2 a b h => h 0

/-- `dictSWF` is dictatorial by C1 (T1). -/
theorem dictSWF_dictatorial : IsDictatorial dictSWF :=
  arrow_impossibility_of_arrowImpossibility ⟨0, 1, 2, by decide, by decide,
    by decide⟩ dictSWF dictSWF_pareto dictSWF_iia

/-- The witness dictator can be taken to be voter `0` (T1). -/
theorem dictSWF_dictator_zero : IsDictator dictSWF 0 := fun p a b h => h

/-- Ballot ranking `2 > 1 > 0`, best first (helper for T2). -/
def ballot210 : ArrowWanted.StrictTotalOrder (Fin 3) := rankOrder ![2, 1, 0] (by decide)

/-- Unfolding for `ballot210` (helper for T2). -/
theorem ballot210_lt (a b : Fin 3) :
    ballot210.lt a b ↔ ![2, 1, 0] a < ![2, 1, 0] b :=
  Iff.rfl

/-- Ballot ranking `0 > 1 > 2`, best first (helper for T2/T3/T4). -/
def ballot012 : ArrowWanted.StrictTotalOrder (Fin 3) := rankOrder ![0, 1, 2] (by decide)

/-- Unfolding for `ballot012` (helper for T2/T3/T4). -/
theorem ballot012_lt (a b : Fin 3) :
    ballot012.lt a b ↔ ![0, 1, 2] a < ![0, 1, 2] b :=
  Iff.rfl

/-- Ballot ranking `1 > 0 > 2`, best first (helper for T2/T4). -/
def ballot102 : ArrowWanted.StrictTotalOrder (Fin 3) := rankOrder ![1, 0, 2] (by decide)

/-- Unfolding for `ballot102` (helper for T2/T4). -/
theorem ballot102_lt (a b : Fin 3) :
    ballot102.lt a b ↔ ![1, 0, 2] a < ![1, 0, 2] b :=
  Iff.rfl

/-- Ballot ranking `1 > 2 > 0`, best first (helper for T3/T4). -/
def ballot120 : ArrowWanted.StrictTotalOrder (Fin 3) := rankOrder ![2, 0, 1] (by decide)

/-- Unfolding for `ballot120` (helper for T3/T4). -/
theorem ballot120_lt (a b : Fin 3) :
    ballot120.lt a b ↔ ![2, 0, 1] a < ![2, 0, 1] b :=
  Iff.rfl

/-- Single-peaked profile with peaks `0, 1, 2` (T2). -/
def peaksProfile : Profile (Fin 3) (Fin 3) := ![ballot012, ballot102, ballot210]

/-- Application fact for `peaksProfile` (helper for T2). -/
theorem peaksProfile_zero : peaksProfile 0 = ballot012 := rfl

/-- Application fact for `peaksProfile` (helper for T2). -/
theorem peaksProfile_one : peaksProfile 1 = ballot102 := rfl

/-- Application fact for `peaksProfile` (helper for T2). -/
theorem peaksProfile_two : peaksProfile 2 = ballot210 := rfl

/-- `peaksProfile` is single-peaked (T2). -/
theorem peaksProfile_singlePeaked : IsSinglePeaked peaksProfile := by
  intro i
  fin_cases i
  · show ∃ p : Fin 3, (∀ a b : Fin 3, a < b → b ≤ p → ballot012.lt b a) ∧
        ∀ a b : Fin 3, p ≤ a → a < b → ballot012.lt a b
    refine ⟨0, ?_, ?_⟩
    · intro a b hab hb
      revert hab hb
      fin_cases a <;> fin_cases b <;> rw [ballot012_lt] <;> decide
    · intro a b ha hab
      revert ha hab
      fin_cases a <;> fin_cases b <;> rw [ballot012_lt] <;> decide
  · show ∃ p : Fin 3, (∀ a b : Fin 3, a < b → b ≤ p → ballot102.lt b a) ∧
        ∀ a b : Fin 3, p ≤ a → a < b → ballot102.lt a b
    refine ⟨1, ?_, ?_⟩
    · intro a b hab hb
      revert hab hb
      fin_cases a <;> fin_cases b <;> rw [ballot102_lt] <;> decide
    · intro a b ha hab
      revert ha hab
      fin_cases a <;> fin_cases b <;> rw [ballot102_lt] <;> decide
  · show ∃ p : Fin 3, (∀ a b : Fin 3, a < b → b ≤ p → ballot210.lt b a) ∧
        ∀ a b : Fin 3, p ≤ a → a < b → ballot210.lt a b
    refine ⟨2, ?_, ?_⟩
    · intro a b hab hb
      revert hab hb
      fin_cases a <;> fin_cases b <;> rw [ballot210_lt] <;> decide
    · intro a b ha hab
      revert ha hab
      fin_cases a <;> fin_cases b <;> rw [ballot210_lt] <;> decide

/-- Supporter count (helper for T2). -/
theorem peaksCard_10 : (supporters peaksProfile 1 0).card = 2 := by
  rw [supporters_eq_filter, Finset.card_filter, Fin.sum_univ_three]
  have c0 : ¬ (peaksProfile 0).lt 1 0 := by
    rw [peaksProfile_zero, ballot012_lt]; decide
  have c1 : (peaksProfile 1).lt 1 0 := by
    rw [peaksProfile_one, ballot102_lt]; decide
  have c2 : (peaksProfile 2).lt 1 0 := by
    rw [peaksProfile_two, ballot210_lt]; decide
  rw [ite_eq_right c0, ite_eq_left c1, ite_eq_left c2]

/-- Supporter count (helper for T2). -/
theorem peaksCard_12 : (supporters peaksProfile 1 2).card = 2 := by
  rw [supporters_eq_filter, Finset.card_filter, Fin.sum_univ_three]
  have c0 : (peaksProfile 0).lt 1 2 := by
    rw [peaksProfile_zero, ballot012_lt]; decide
  have c1 : (peaksProfile 1).lt 1 2 := by
    rw [peaksProfile_one, ballot102_lt]; decide
  have c2 : ¬ (peaksProfile 2).lt 1 2 := by
    rw [peaksProfile_two, ballot210_lt]; decide
  rw [ite_eq_left c0, ite_eq_left c1, ite_eq_right c2]

/-- Supporter count (helper for T2). -/
theorem peaksCard_02 : (supporters peaksProfile 0 2).card = 2 := by
  rw [supporters_eq_filter, Finset.card_filter, Fin.sum_univ_three]
  have c0 : (peaksProfile 0).lt 0 2 := by
    rw [peaksProfile_zero, ballot012_lt]; decide
  have c1 : (peaksProfile 1).lt 0 2 := by
    rw [peaksProfile_one, ballot102_lt]; decide
  have c2 : ¬ (peaksProfile 2).lt 0 2 := by
    rw [peaksProfile_two, ballot210_lt]; decide
  rw [ite_eq_left c0, ite_eq_left c1, ite_eq_right c2]

/-- Majority of `1` over `0` (T2). -/
theorem peaksMaj_10 : MajorityPrefers peaksProfile 1 0 := by
  rw [majorityPrefers_iff, peaksCard_10, Fintype.card_fin]
  decide

/-- Majority of `1` over `2` (T2). -/
theorem peaksMaj_12 : MajorityPrefers peaksProfile 1 2 := by
  rw [majorityPrefers_iff, peaksCard_12, Fintype.card_fin]
  decide

/-- Majority of `0` over `2` (T2). -/
theorem peaksMaj_02 : MajorityPrefers peaksProfile 0 2 := by
  rw [majorityPrefers_iff, peaksCard_02, Fintype.card_fin]
  decide

/-- Majority of `1` over `2`, also derived via C4 (T2). -/
theorem peaksMaj_12_viaC4 : MajorityPrefers peaksProfile 1 2 :=
  majorityPrefers_trans_of_singlePeaked peaksProfile peaksProfile_singlePeaked
    (by rw [Fintype.card_fin]; exact ⟨1, rfl⟩) peaksMaj_10 peaksMaj_02

/-- Ballot ranking `2 > 0 > 1`, best first (helper for T3). -/
def ballot201 : ArrowWanted.StrictTotalOrder (Fin 3) := rankOrder ![1, 2, 0] (by decide)

/-- Unfolding for `ballot201` (helper for T3). -/
theorem ballot201_lt (a b : Fin 3) :
    ballot201.lt a b ↔ ![1, 2, 0] a < ![1, 2, 0] b :=
  Iff.rfl

/-- Cyclic profile with ballots `0 > 1 > 2`, `1 > 2 > 0`, `2 > 0 > 1` (T3). -/
def cycleProfile : Profile (Fin 3) (Fin 3) := ![ballot012, ballot120, ballot201]

/-- Application fact for `cycleProfile` (helper for T3). -/
theorem cycleProfile_zero : cycleProfile 0 = ballot012 := rfl

/-- Application fact for `cycleProfile` (helper for T3). -/
theorem cycleProfile_one : cycleProfile 1 = ballot120 := rfl

/-- Application fact for `cycleProfile` (helper for T3). -/
theorem cycleProfile_two : cycleProfile 2 = ballot201 := rfl

/-- The cyclic profile is not single-peaked (T3). -/
theorem cycleProfile_not_singlePeaked : ¬ IsSinglePeaked cycleProfile := by
  intro hSP
  have h2 := hSP 2
  rw [cycleProfile_two] at h2
  obtain ⟨p, hleft, hright⟩ := h2
  fin_cases p
  · have h := hright 0 2 le_rfl (by decide : (0 : Fin 3) < 2)
    rw [ballot201_lt] at h
    exact absurd h (by decide)
  · have h := hleft 0 1 (by decide : (0 : Fin 3) < 1) (by decide : (1 : Fin 3) ≤ 1)
    rw [ballot201_lt] at h
    exact absurd h (by decide)
  · have h := hleft 0 1 (by decide : (0 : Fin 3) < 1) (by decide : (1 : Fin 3) ≤ 2)
    rw [ballot201_lt] at h
    exact absurd h (by decide)

/-- Ballot ranking `0 > 1` on two alternatives (helper for T3). -/
def tie01 : ArrowWanted.StrictTotalOrder (Fin 2) := rankOrder ![0, 1] (by decide)

/-- Ballot ranking `1 > 0` on two alternatives (helper for T3). -/
def tie10 : ArrowWanted.StrictTotalOrder (Fin 2) := rankOrder ![1, 0] (by decide)

/-- Unfolding for `tie01` (helper for T3). -/
theorem tie01_lt (a b : Fin 2) : tie01.lt a b ↔ ![0, 1] a < ![0, 1] b :=
  Iff.rfl

/-- Unfolding for `tie10` (helper for T3). -/
theorem tie10_lt (a b : Fin 2) : tie10.lt a b ↔ ![1, 0] a < ![1, 0] b :=
  Iff.rfl

/-- Even-electorate tie profile (T3). -/
def tieProfile : Profile (Fin 2) (Fin 2) := ![tie01, tie10]

/-- Application fact for `tieProfile` (helper for T3). -/
theorem tieProfile_zero : tieProfile 0 = tie01 := rfl

/-- Application fact for `tieProfile` (helper for T3). -/
theorem tieProfile_one : tieProfile 1 = tie10 := rfl

/-- Supporter count (helper for T3). -/
theorem tieCard_01 : (supporters tieProfile 0 1).card = 1 := by
  rw [supporters_eq_filter, Finset.card_filter, Fin.sum_univ_two]
  have c0 : (tieProfile 0).lt 0 1 := by rw [tieProfile_zero, tie01_lt]; decide
  have c1 : ¬ (tieProfile 1).lt 0 1 := by rw [tieProfile_one, tie10_lt]; decide
  rw [ite_eq_left c0, ite_eq_right c1]

/-- Supporter count (helper for T3). -/
theorem tieCard_10 : (supporters tieProfile 1 0).card = 1 := by
  rw [supporters_eq_filter, Finset.card_filter, Fin.sum_univ_two]
  have c0 : ¬ (tieProfile 0).lt 1 0 := by rw [tieProfile_zero, tie01_lt]; decide
  have c1 : (tieProfile 1).lt 1 0 := by rw [tieProfile_one, tie10_lt]; decide
  rw [ite_eq_right c0, ite_eq_left c1]

/-- Even-electorate tie: no majority either way (T3). -/
theorem tie_neither :
    ¬ MajorityPrefers tieProfile 0 1 ∧ ¬ MajorityPrefers tieProfile 1 0 := by
  rw [majorityPrefers_iff, majorityPrefers_iff, tieCard_01, tieCard_10,
    Fintype.card_fin]
  decide

/-- Five-voter Borda profile `P` for C6 (T4). -/
def bordaP : Profile (Fin 3) (Fin 5) := ![ballot012, ballot012, ballot012, ballot102, ballot102]

/-- Five-voter Borda profile `Q` for C6 (T4). -/
def bordaQ : Profile (Fin 3) (Fin 5) := ![ballot012, ballot012, ballot012, ballot120, ballot120]

/-- Application fact for `bordaP` (helper for T4). -/
theorem bordaP_zero : bordaP 0 = ballot012 := rfl

/-- Application fact for `bordaP` (helper for T4). -/
theorem bordaP_one : bordaP 1 = ballot012 := rfl

/-- Application fact for `bordaP` (helper for T4). -/
theorem bordaP_two : bordaP 2 = ballot012 := rfl

/-- Application fact for `bordaP` (helper for T4). -/
theorem bordaP_three : bordaP 3 = ballot102 := rfl

/-- Application fact for `bordaP` (helper for T4). -/
theorem bordaP_four : bordaP 4 = ballot102 := rfl

/-- Application fact for `bordaQ` (helper for T4). -/
theorem bordaQ_zero : bordaQ 0 = ballot012 := rfl

/-- Application fact for `bordaQ` (helper for T4). -/
theorem bordaQ_one : bordaQ 1 = ballot012 := rfl

/-- Application fact for `bordaQ` (helper for T4). -/
theorem bordaQ_two : bordaQ 2 = ballot012 := rfl

/-- Application fact for `bordaQ` (helper for T4). -/
theorem bordaQ_three : bordaQ 3 = ballot120 := rfl

/-- Application fact for `bordaQ` (helper for T4). -/
theorem bordaQ_four : bordaQ 4 = ballot120 := rfl

/-- Recomputed Borda values for `bordaP` (T4). -/
theorem t4_bordaP :
    bordaScore bordaP 0 = 8 ∧ bordaScore bordaP 1 = 7 ∧ bordaScore bordaP 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bordaScore_unfold, Fin.sum_univ_five,
      bordaP_zero, bordaP_one, bordaP_two, bordaP_three, bordaP_four]
    simp [Finset.card_filter, Fin.sum_univ_three, ballot012_lt, ballot102_lt,
      ballot120_lt, -Finset.sum_boole]
  · rw [bordaScore_unfold, Fin.sum_univ_five,
      bordaP_zero, bordaP_one, bordaP_two, bordaP_three, bordaP_four]
    simp [Finset.card_filter, Fin.sum_univ_three, ballot012_lt, ballot102_lt,
      ballot120_lt, -Finset.sum_boole]
  · rw [bordaScore_unfold, Fin.sum_univ_five,
      bordaP_zero, bordaP_one, bordaP_two, bordaP_three, bordaP_four]
    simp [Finset.card_filter, Fin.sum_univ_three, ballot012_lt, ballot102_lt,
      ballot120_lt, -Finset.sum_boole]

/-- Recomputed Borda values for `bordaQ` (T4). -/
theorem t4_bordaQ :
    bordaScore bordaQ 0 = 6 ∧ bordaScore bordaQ 1 = 7 ∧ bordaScore bordaQ 2 = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bordaScore_unfold, Fin.sum_univ_five,
      bordaQ_zero, bordaQ_one, bordaQ_two, bordaQ_three, bordaQ_four]
    simp [Finset.card_filter, Fin.sum_univ_three, ballot012_lt, ballot102_lt,
      ballot120_lt, -Finset.sum_boole]
  · rw [bordaScore_unfold, Fin.sum_univ_five,
      bordaQ_zero, bordaQ_one, bordaQ_two, bordaQ_three, bordaQ_four]
    simp [Finset.card_filter, Fin.sum_univ_three, ballot012_lt, ballot102_lt,
      ballot120_lt, -Finset.sum_boole]
  · rw [bordaScore_unfold, Fin.sum_univ_five,
      bordaQ_zero, bordaQ_one, bordaQ_two, bordaQ_three, bordaQ_four]
    simp [Finset.card_filter, Fin.sum_univ_three, ballot012_lt, ballot102_lt,
      ballot120_lt, -Finset.sum_boole]

/-- Voterwise agreement, rechecked (T4). -/
theorem t4_agreement : ∀ i : Fin 5, (bordaP i).lt 0 1 ↔ (bordaQ i).lt 0 1 := by
  intro i
  fin_cases i <;> simp [bordaP, bordaQ, ballot012_lt, ballot102_lt, ballot120_lt]

/-- C6 reassembled in the test module (T4). -/
theorem t4_borda_score_reversal :
    ∃ P Q : Profile (Fin 3) (Fin 5),
      (∀ i : Fin 5, (P i).lt 0 1 ↔ (Q i).lt 0 1) ∧
        bordaScore P 1 < bordaScore P 0 ∧ bordaScore Q 0 < bordaScore Q 1 :=
  borda_score_reversal

end MathlibExtTest.GameTheory.SocialChoice.Black

end
