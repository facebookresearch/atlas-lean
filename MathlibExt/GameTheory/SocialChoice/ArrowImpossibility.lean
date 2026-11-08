/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Finset.Basic

public import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Push

@[expose] public section

namespace MetaMathlibExt

section

private theorem preRefl {Alt : Type} (R : Alt → Alt → Prop)
    (h : IsPreorder Alt R) (x : Alt) : R x x := by
  have := IsPreorder.toRefl (self := h)
  exact Std.Refl.refl x

private theorem preTrans {Alt : Type} (R : Alt → Alt → Prop)
    (h : IsPreorder Alt R) {x y z : Alt} (h1 : R x y) (h2 : R y z) : R x z := by
  have := IsPreorder.toIsTrans (self := h)
  exact IsTrans.trans x y z h1 h2

private theorem ballotDom {Alt Voter : Type} (electorate : Finset Voter)
    (f : Voter → Alt → Nat) :
    ∀ v ∈ electorate, IsPreorder Alt (fun x y => f v x ≤ f v y) ∧
      ∀ x y : Alt, (fun x y => f v x ≤ f v y) x y ∨
        (fun x y => f v x ≤ f v y) y x := by
  intro v _
  refine ⟨?_, fun x y => le_total _ _⟩
  have : Std.Refl (fun x y => f v x ≤ f v y) := ⟨fun _ => le_refl _⟩
  have : IsTrans Alt (fun x y => f v x ≤ f v y) := ⟨fun _ _ _ a b => le_trans a b⟩
  exact IsPreorder.mk

private theorem ballotStrict {Alt Voter : Type} (f : Voter → Alt → Nat) (v : Voter)
    (a b : Alt) :
    ((fun x y => f v x ≤ f v y) a b ∧ ¬ (fun x y => f v x ≤ f v y) b a) ↔
      f v a < f v b := by
  change (f v a ≤ f v b ∧ ¬ f v b ≤ f v a) ↔ f v a < f v b
  constructor <;> intro h <;> omega

private def Dom {Alt Voter : Type} (electorate : Finset Voter)
    (P : Voter → Alt → Alt → Prop) : Prop :=
  ∀ v ∈ electorate, IsPreorder Alt (P v) ∧ ∀ x y : Alt, P v x y ∨ P v y x

private def StrongDec {Alt Voter : Type} (electorate : Finset Voter)
    (F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop))
    (G : Finset Voter) (p q : Alt) : Prop :=
  ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
    (∀ v ∈ G, P v p q ∧ ¬ P v q p) → F P p q ∧ ¬ F P q p

private def WeakDec {Alt Voter : Type} (electorate : Finset Voter)
    (F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop))
    (G : Finset Voter) (p q : Alt) : Prop :=
  ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
    (∀ v ∈ G, P v p q ∧ ¬ P v q p) →
    (∀ v ∈ electorate, v ∉ G → P v q p ∧ ¬ P v p q) →
    F P p q ∧ ¬ F P q p

private theorem d1_to_d2 {Alt Voter : Type} {electorate : Finset Voter}
    {F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop)}
    {G : Finset Voter} {p q : Alt}
    (h : StrongDec electorate F G p q) : WeakDec electorate F G p q := by
  intro P hDom hG _
  exact h P hDom hG

private theorem spreadA {Alt Voter : Type} {electorate : Finset Voter}
    {F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop)}
    {G : Finset Voter} (hG : G ⊆ electorate)
    (hUniv : ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
      IsPreorder Alt (F P) ∧ ∀ x y : Alt, F P x y ∨ F P y x)
    (hPareto : ∀ (P : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P →
      (∀ v ∈ electorate, P v a b ∧ ¬ P v b a) → F P a b ∧ ¬ F P b a)
    (hIIA : ∀ (P Q : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P → Dom electorate Q →
      (∀ v ∈ electorate, (P v a b ↔ Q v a b) ∧ (P v b a ↔ Q v b a)) →
      (F P a b ↔ F Q a b) ∧ (F P b a ↔ F Q b a))
    {u v : Alt} {w : Alt} (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (hD : WeakDec electorate F G u v) :
    StrongDec electorate F G u w := by
  classical
  intro P hDom hGuw
  set f : Voter → Alt → Nat := fun t x =>
    if t ∈ G then (if x = u then 0 else if x = v then 1 else if x = w then 2 else 3)
    else if x = v then 0
      else if P t u w ∧ ¬ P t w u then (if x = u then 1 else if x = w then 2 else 3)
      else if P t w u ∧ ¬ P t u w then (if x = u then 2 else if x = w then 1 else 3)
      else (if x = u then 1 else if x = w then 1 else 3) with hf
  have hDomQ : Dom electorate (fun v x y => f v x ≤ f v y) :=
    ballotDom electorate f
  have eGu : ∀ t ∈ G, f t u = 0 := by
    intro t ht
    simp only [hf, ht, ite_true]
  have eGv : ∀ t ∈ G, f t v = 1 := by
    intro t ht
    simp only [hf, ht, (Ne.symm huv), ite_true, ite_false]
  have eGw : ∀ t ∈ G, f t w = 2 := by
    intro t ht
    simp only [hf, ht, hwu, hwv, ite_true, ite_false]
  have eOv : ∀ t ∈ electorate, t ∉ G → f t v = 0 := by
    intro t _ htG
    simp only [hf, htG, ite_true, ite_false]
  have hGQ : ∀ t ∈ G, (fun x y => f t x ≤ f t y) u v ∧
      ¬ (fun x y => f t x ≤ f t y) v u := by
    intro t ht
    have eu := eGu t ht
    have ev := eGv t ht
    exact (ballotStrict f t u v).mpr (by omega)
  have hGQw : ∀ t ∈ G, (fun x y => f t x ≤ f t y) v w ∧
      ¬ (fun x y => f t x ≤ f t y) w v := by
    intro t ht
    have ev := eGv t ht
    have ew := eGw t ht
    exact (ballotStrict f t v w).mpr (by omega)
  have hOQ : ∀ t ∈ electorate, t ∉ G → (fun x y => f t x ≤ f t y) v u ∧
      ¬ (fun x y => f t x ≤ f t y) u v := by
    intro t ht htG
    have ev := eOv t ht htG
    by_cases h1 : P t u w ∧ ¬ P t w u
    · have eu : f t u = 1 := by
        simp only [hf, htG, huv, h1, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
      exact (ballotStrict f t v u).mpr (by omega)
    · by_cases h2 : P t w u ∧ ¬ P t u w
      · have eu : f t u = 2 := by
          simp only [hf, htG, huv, h2, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
        exact (ballotStrict f t v u).mpr (by omega)
      · have eu : f t u = 1 := by
          simp only [hf, htG, huv, h1, h2, ite_true, ite_false]
        exact (ballotStrict f t v u).mpr (by omega)
  have hOQw : ∀ t ∈ electorate, t ∉ G → (fun x y => f t x ≤ f t y) v w ∧
      ¬ (fun x y => f t x ≤ f t y) w v := by
    intro t ht htG
    have ev := eOv t ht htG
    by_cases h1 : P t u w ∧ ¬ P t w u
    · have ew : f t w = 2 := by
        simp only [hf, htG, hwv, h1, hwu, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
      exact (ballotStrict f t v w).mpr (by omega)
    · by_cases h2 : P t w u ∧ ¬ P t u w
      · have ew : f t w = 1 := by
          simp only [hf, htG, hwv, h2, hwu, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
        exact (ballotStrict f t v w).mpr (by omega)
      · have ew : f t w = 1 := by
          simp only [hf, htG, hwv, h1, h2, hwu, ite_true, ite_false]
        exact (ballotStrict f t v w).mpr (by omega)
  have hSocUV := hD _ hDomQ hGQ hOQ
  have hSocVW := hPareto _ _ _ hDomQ (fun t ht => by
    by_cases htG : t ∈ G
    · exact hGQw t htG
    · exact hOQw t ht htG)
  have hPreQ := (hUniv _ hDomQ).1
  have hFUW : F (fun v x y => f v x ≤ f v y) u w :=
    preTrans _ hPreQ hSocUV.1 hSocVW.1
  have hnWU : ¬ F (fun v x y => f v x ≤ f v y) w u := by
    intro hc
    exact hSocVW.2 (preTrans _ hPreQ hc hSocUV.1)
  have hagree : ∀ t ∈ electorate,
      ((fun v x y => f v x ≤ f v y) t u w ↔ P t u w) ∧
      ((fun v x y => f v x ≤ f v y) t w u ↔ P t w u) := by
    intro t ht
    by_cases htG : t ∈ G
    · have eu := eGu t htG
      have ew := eGw t htG
      have hP := hGuw t htG
      have q1 : (fun v x y => f v x ≤ f v y) t u w := by
        change f t u ≤ f t w
        omega
      have q2 : ¬ (fun v x y => f v x ≤ f v y) t w u := by
        change ¬ f t w ≤ f t u
        omega
      exact ⟨iff_of_true q1 hP.1, iff_of_false q2 hP.2⟩
    · by_cases h1 : P t u w ∧ ¬ P t w u
      · have eu : f t u = 1 := by
          simp only [hf, htG, huv, h1, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
        have ew : f t w = 2 := by
          simp only [hf, htG, hwv, h1, hwu, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
        have q1 : (fun v x y => f v x ≤ f v y) t u w := by
          change f t u ≤ f t w
          omega
        have q2 : ¬ (fun v x y => f v x ≤ f v y) t w u := by
          change ¬ f t w ≤ f t u
          omega
        exact ⟨iff_of_true q1 h1.1, iff_of_false q2 h1.2⟩
      · by_cases h2 : P t w u ∧ ¬ P t u w
        · have eu : f t u = 2 := by
            simp only [hf, htG, huv, h2, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
          have ew : f t w = 1 := by
            simp only [hf, htG, hwv, h2, hwu, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
          have q1 : ¬ (fun v x y => f v x ≤ f v y) t u w := by
            change ¬ f t u ≤ f t w
            omega
          have q2 : (fun v x y => f v x ≤ f v y) t w u := by
            change f t w ≤ f t u
            omega
          exact ⟨iff_of_false q1 h2.2, iff_of_true q2 h2.1⟩
        · have hPuw : P t u w := by
            by_contra hc
            rcases (hDom t ht).2 u w with h | h
            · exact hc h
            · exact h2 ⟨h, hc⟩
          have hPwu : P t w u := by
            by_contra hc
            rcases (hDom t ht).2 u w with h | h
            · exact h1 ⟨h, hc⟩
            · exact hc h
          have eu : f t u = 1 := by
            simp only [hf, htG, huv, h1, h2, ite_true, ite_false]
          have ew : f t w = 1 := by
            simp only [hf, htG, hwv, h1, h2, hwu, ite_true, ite_false]
          have q1 : (fun v x y => f v x ≤ f v y) t u w := by
            change f t u ≤ f t w
            omega
          have q2 : (fun v x y => f v x ≤ f v y) t w u := by
            change f t w ≤ f t u
            omega
          exact ⟨iff_of_true q1 hPuw, iff_of_true q2 hPwu⟩
  have htrans := hIIA _ P u w hDomQ hDom hagree
  exact ⟨htrans.1.mp hFUW, fun h => hnWU (htrans.2.mpr h)⟩

private theorem spreadB {Alt Voter : Type} {electorate : Finset Voter}
    {F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop)}
    {G : Finset Voter} (hG : G ⊆ electorate)
    (hUniv : ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
      IsPreorder Alt (F P) ∧ ∀ x y : Alt, F P x y ∨ F P y x)
    (hPareto : ∀ (P : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P →
      (∀ v ∈ electorate, P v a b ∧ ¬ P v b a) → F P a b ∧ ¬ F P b a)
    (hIIA : ∀ (P Q : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P → Dom electorate Q →
      (∀ v ∈ electorate, (P v a b ↔ Q v a b) ∧ (P v b a ↔ Q v b a)) →
      (F P a b ↔ F Q a b) ∧ (F P b a ↔ F Q b a))
    {u v : Alt} {w : Alt} (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (hD : WeakDec electorate F G u v) :
    StrongDec electorate F G w v := by
  classical
  intro P hDom hGwv
  set f : Voter → Alt → Nat := fun t x =>
    if t ∈ G then (if x = w then 0 else if x = u then 1 else if x = v then 2 else 3)
    else if x = u then 2
      else if P t w v ∧ ¬ P t v w then (if x = w then 0 else if x = v then 1 else 2)
      else if P t v w ∧ ¬ P t w v then (if x = w then 1 else if x = v then 0 else 2)
      else (if x = w then 0 else if x = v then 0 else 2) with hf
  have hDomQ : Dom electorate (fun v x y => f v x ≤ f v y) :=
    ballotDom electorate f
  have eGw : ∀ t ∈ G, f t w = 0 := by
    intro t ht
    simp only [hf, ht, ite_true]
  have eGu : ∀ t ∈ G, f t u = 1 := by
    intro t ht
    simp only [hf, ht, (Ne.symm hwu), ite_true, ite_false]
  have eGv : ∀ t ∈ G, f t v = 2 := by
    intro t ht
    simp only [hf, ht, (Ne.symm hwv), (Ne.symm huv), ite_true, ite_false]
  have eOu : ∀ t ∈ electorate, t ∉ G → f t u = 2 := by
    intro t _ htG
    simp only [hf, htG, (Ne.symm hwu), ite_true, ite_false]
  have hGQ : ∀ t ∈ G, (fun x y => f t x ≤ f t y) u v ∧
      ¬ (fun x y => f t x ≤ f t y) v u := by
    intro t ht
    have eu := eGu t ht
    have ev := eGv t ht
    exact (ballotStrict f t u v).mpr (by omega)
  have hGwU : ∀ t ∈ G, (fun x y => f t x ≤ f t y) w u ∧
      ¬ (fun x y => f t x ≤ f t y) u w := by
    intro t ht
    have ew := eGw t ht
    have eu := eGu t ht
    exact (ballotStrict f t w u).mpr (by omega)
  have hOQ : ∀ t ∈ electorate, t ∉ G → (fun x y => f t x ≤ f t y) v u ∧
      ¬ (fun x y => f t x ≤ f t y) u v := by
    intro t ht htG
    have eu := eOu t ht htG
    by_cases h1 : P t w v ∧ ¬ P t v w
    · have ev : f t v = 1 := by
        simp only [hf, htG, (Ne.symm huv), h1,
          (Ne.symm hwv), ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
      exact (ballotStrict f t v u).mpr (by omega)
    · by_cases h2 : P t v w ∧ ¬ P t w v
      · have ev : f t v = 0 := by
          simp only [hf, htG, (Ne.symm huv), h2, (Ne.symm hwv), ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
        exact (ballotStrict f t v u).mpr (by omega)
      · have ev : f t v = 0 := by
          simp only [hf, htG, (Ne.symm huv), h1, h2, (Ne.symm hwv), ite_true, ite_false]
        exact (ballotStrict f t v u).mpr (by omega)
  have hOwU : ∀ t ∈ electorate, t ∉ G → (fun x y => f t x ≤ f t y) w u ∧
      ¬ (fun x y => f t x ≤ f t y) u w := by
    intro t ht htG
    have eu := eOu t ht htG
    by_cases h1 : P t w v ∧ ¬ P t v w
    · have ew : f t w = 0 := by
        simp only [hf, htG, hwu, h1, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
      exact (ballotStrict f t w u).mpr (by omega)
    · by_cases h2 : P t v w ∧ ¬ P t w v
      · have ew : f t w = 1 := by
          simp only [hf, htG, hwu, h2, hwv, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
        exact (ballotStrict f t w u).mpr (by omega)
      · have ew : f t w = 0 := by
          simp only [hf, htG, hwu, h1, h2, ite_true, ite_false]
        exact (ballotStrict f t w u).mpr (by omega)
  have hSocUV := hD _ hDomQ hGQ hOQ
  have hSocWU := hPareto _ _ _ hDomQ (fun t ht => by
    by_cases htG : t ∈ G
    · exact hGwU t htG
    · exact hOwU t ht htG)
  have hPreQ := (hUniv _ hDomQ).1
  have hFWV : F (fun v x y => f v x ≤ f v y) w v :=
    preTrans _ hPreQ hSocWU.1 hSocUV.1
  have hnVW : ¬ F (fun v x y => f v x ≤ f v y) v w := by
    intro hc
    exact hSocUV.2 (preTrans _ hPreQ hc hSocWU.1)
  have hagree : ∀ t ∈ electorate,
      ((fun v x y => f v x ≤ f v y) t w v ↔ P t w v) ∧
      ((fun v x y => f v x ≤ f v y) t v w ↔ P t v w) := by
    intro t ht
    by_cases htG : t ∈ G
    · have ew := eGw t htG
      have ev := eGv t htG
      have hP := hGwv t htG
      have q1 : (fun v x y => f v x ≤ f v y) t w v := by
        change f t w ≤ f t v
        omega
      have q2 : ¬ (fun v x y => f v x ≤ f v y) t v w := by
        change ¬ f t v ≤ f t w
        omega
      exact ⟨iff_of_true q1 hP.1, iff_of_false q2 hP.2⟩
    · by_cases h1 : P t w v ∧ ¬ P t v w
      · have ew : f t w = 0 := by
          simp only [hf, htG, hwu, h1, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
        have ev : f t v = 1 := by
          simp only [hf, htG, (Ne.symm huv), h1,
            (Ne.symm hwv), ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
        have q1 : (fun v x y => f v x ≤ f v y) t w v := by
          change f t w ≤ f t v
          omega
        have q2 : ¬ (fun v x y => f v x ≤ f v y) t v w := by
          change ¬ f t v ≤ f t w
          omega
        exact ⟨iff_of_true q1 h1.1, iff_of_false q2 h1.2⟩
      · by_cases h2 : P t v w ∧ ¬ P t w v
        · have ew : f t w = 1 := by
            simp only [hf, htG, hwu, h2, hwv, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
          have ev : f t v = 0 := by
            simp only [hf, htG, (Ne.symm huv), h2, (Ne.symm hwv), ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
          have q1 : ¬ (fun v x y => f v x ≤ f v y) t w v := by
            change ¬ f t w ≤ f t v
            omega
          have q2 : (fun v x y => f v x ≤ f v y) t v w := by
            change f t v ≤ f t w
            omega
          exact ⟨iff_of_false q1 h2.2, iff_of_true q2 h2.1⟩
        · have hPwv : P t w v := by
            by_contra hc
            rcases (hDom t ht).2 w v with h | h
            · exact hc h
            · exact h2 ⟨h, hc⟩
          have hPvw : P t v w := by
            by_contra hc
            rcases (hDom t ht).2 w v with h | h
            · exact h1 ⟨h, hc⟩
            · exact hc h
          have ew : f t w = 0 := by
            simp only [hf, htG, hwu, h1, h2, ite_true, ite_false]
          have ev : f t v = 0 := by
            simp only [hf, htG, (Ne.symm huv), h1, h2, (Ne.symm hwv), ite_true, ite_false]
          have q1 : (fun v x y => f v x ≤ f v y) t w v := by
            change f t w ≤ f t v
            omega
          have q2 : (fun v x y => f v x ≤ f v y) t v w := by
            change f t v ≤ f t w
            omega
          exact ⟨iff_of_true q1 hPwv, iff_of_true q2 hPvw⟩
  have htrans := hIIA _ P w v hDomQ hDom hagree
  exact ⟨htrans.1.mp hFWV, fun h => hnVW (htrans.2.mpr h)⟩

private theorem transferA {Alt Voter : Type} {electorate : Finset Voter}
    {F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop)}
    {G : Finset Voter} (hG : G ⊆ electorate)
    (hUniv : ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
      IsPreorder Alt (F P) ∧ ∀ x y : Alt, F P x y ∨ F P y x)
    (hPareto : ∀ (P : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P →
      (∀ v ∈ electorate, P v a b ∧ ¬ P v b a) → F P a b ∧ ¬ F P b a)
    (hIIA : ∀ (P Q : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P → Dom electorate Q →
      (∀ v ∈ electorate, (P v a b ↔ Q v a b) ∧ (P v b a ↔ Q v b a)) →
      (F P a b ↔ F Q a b) ∧ (F P b a ↔ F Q b a))
    {u v w : Alt} (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (hD : StrongDec electorate F G u v) :
    StrongDec electorate F G u w :=
  spreadA hG hUniv hPareto hIIA huv hwu hwv (d1_to_d2 hD)

private theorem transferB {Alt Voter : Type} {electorate : Finset Voter}
    {F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop)}
    {G : Finset Voter} (hG : G ⊆ electorate)
    (hUniv : ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
      IsPreorder Alt (F P) ∧ ∀ x y : Alt, F P x y ∨ F P y x)
    (hPareto : ∀ (P : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P →
      (∀ v ∈ electorate, P v a b ∧ ¬ P v b a) → F P a b ∧ ¬ F P b a)
    (hIIA : ∀ (P Q : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P → Dom electorate Q →
      (∀ v ∈ electorate, (P v a b ↔ Q v a b) ∧ (P v b a ↔ Q v b a)) →
      (F P a b ↔ F Q a b) ∧ (F P b a ↔ F Q b a))
    {u v w : Alt} (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v)
    (hD : StrongDec electorate F G u v) :
    StrongDec electorate F G w v :=
  spreadB hG hUniv hPareto hIIA huv hwu hwv (d1_to_d2 hD)

private theorem composeD1 {Alt Voter : Type} {electorate : Finset Voter}
    {F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop)}
    {G : Finset Voter}
    (hUniv : ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
      IsPreorder Alt (F P) ∧ ∀ x y : Alt, F P x y ∨ F P y x)
    (hIIA : ∀ (P Q : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P → Dom electorate Q →
      (∀ v ∈ electorate, (P v a b ↔ Q v a b) ∧ (P v b a ↔ Q v b a)) →
      (F P a b ↔ F Q a b) ∧ (F P b a ↔ F Q b a))
    {u z v : Alt} (huz : u ≠ z) (hzv : z ≠ v) (huv : u ≠ v)
    (h1 : StrongDec electorate F G u z) (h2 : StrongDec electorate F G z v) :
    StrongDec electorate F G u v := by
  classical
  intro P hDom hGuv
  set f : Voter → Alt → Nat := fun t x =>
    if t ∈ G then (if x = u then 0 else if x = z then 1 else if x = v then 2 else 3)
    else if P t u v ∧ ¬ P t v u then (if x = u then 0 else if x = v then 1 else 2)
    else if P t v u ∧ ¬ P t u v then (if x = u then 1 else if x = v then 0 else 2)
    else (if x = u then 0 else if x = v then 0 else 2) with hf
  have hDomQ : Dom electorate (fun v x y => f v x ≤ f v y) :=
    ballotDom electorate f
  have eGu : ∀ t ∈ G, f t u = 0 := by
    intro t ht
    simp only [hf, ht, ite_true]
  have eGz : ∀ t ∈ G, f t z = 1 := by
    intro t ht
    simp only [hf, ht, (Ne.symm huz), ite_true, ite_false]
  have eGv : ∀ t ∈ G, f t v = 2 := by
    intro t ht
    simp only [hf, ht, (Ne.symm huv), (Ne.symm hzv), ite_true, ite_false]
  have hGQ1 : ∀ t ∈ G, (fun x y => f t x ≤ f t y) u z ∧
      ¬ (fun x y => f t x ≤ f t y) z u := by
    intro t ht
    have eu := eGu t ht
    have ez := eGz t ht
    exact (ballotStrict f t u z).mpr (by omega)
  have hGQ2 : ∀ t ∈ G, (fun x y => f t x ≤ f t y) z v ∧
      ¬ (fun x y => f t x ≤ f t y) v z := by
    intro t ht
    have ez := eGz t ht
    have ev := eGv t ht
    exact (ballotStrict f t z v).mpr (by omega)
  have hSocUZ := h1 _ hDomQ hGQ1
  have hSocZV := h2 _ hDomQ hGQ2
  have hPreQ := (hUniv _ hDomQ).1
  have hFUV : F (fun v x y => f v x ≤ f v y) u v :=
    preTrans _ hPreQ hSocUZ.1 hSocZV.1
  have hnVU : ¬ F (fun v x y => f v x ≤ f v y) v u := by
    intro hc
    exact hSocZV.2 (preTrans _ hPreQ hc hSocUZ.1)
  have hagree : ∀ t ∈ electorate,
      ((fun v x y => f v x ≤ f v y) t u v ↔ P t u v) ∧
      ((fun v x y => f v x ≤ f v y) t v u ↔ P t v u) := by
    intro t ht
    by_cases htG : t ∈ G
    · have eu := eGu t htG
      have ev := eGv t htG
      have hP := hGuv t htG
      have q1 : (fun v x y => f v x ≤ f v y) t u v := by
        change f t u ≤ f t v
        omega
      have q2 : ¬ (fun v x y => f v x ≤ f v y) t v u := by
        change ¬ f t v ≤ f t u
        omega
      exact ⟨iff_of_true q1 hP.1, iff_of_false q2 hP.2⟩
    · by_cases h1 : P t u v ∧ ¬ P t v u
      · have eu : f t u = 0 := by
          simp only [hf, htG, h1, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
        have ev : f t v = 1 := by
          simp only [hf, htG, h1, (Ne.symm huv), ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
        have q1 : (fun v x y => f v x ≤ f v y) t u v := by
          change f t u ≤ f t v
          omega
        have q2 : ¬ (fun v x y => f v x ≤ f v y) t v u := by
          change ¬ f t v ≤ f t u
          omega
        exact ⟨iff_of_true q1 h1.1, iff_of_false q2 h1.2⟩
      · by_cases h2 : P t v u ∧ ¬ P t u v
        · have eu : f t u = 1 := by
            simp only [hf, htG, h2, ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
          have ev : f t v = 0 := by
            simp only [hf, htG, h2, (Ne.symm huv), ite_true, ite_false, true_and, false_and, not_false_eq_true, not_true_eq_false]
          have q1 : ¬ (fun v x y => f v x ≤ f v y) t u v := by
            change ¬ f t u ≤ f t v
            omega
          have q2 : (fun v x y => f v x ≤ f v y) t v u := by
            change f t v ≤ f t u
            omega
          exact ⟨iff_of_false q1 h2.2, iff_of_true q2 h2.1⟩
        · have hPuv : P t u v := by
            by_contra hc
            rcases (hDom t ht).2 u v with h | h
            · exact hc h
            · exact h2 ⟨h, hc⟩
          have hPvu : P t v u := by
            by_contra hc
            rcases (hDom t ht).2 u v with h | h
            · exact h1 ⟨h, hc⟩
            · exact hc h
          have eu : f t u = 0 := by
            simp only [hf, htG, h1, h2, ite_true, ite_false]
          have ev : f t v = 0 := by
            simp only [hf, htG, h1, h2, (Ne.symm huv), ite_true, ite_false]
          have q1 : (fun v x y => f v x ≤ f v y) t u v := by
            change f t u ≤ f t v
            omega
          have q2 : (fun v x y => f v x ≤ f v y) t v u := by
            change f t v ≤ f t u
            omega
          exact ⟨iff_of_true q1 hPuv, iff_of_true q2 hPvu⟩
  have htrans := hIIA _ P u v hDomQ hDom hagree
  exact ⟨htrans.1.mp hFUV, fun h => hnVU (htrans.2.mpr h)⟩

private theorem pivotEx {Alt : Type} {a0 b0 c0 p q : Alt}
    (hab : a0 ≠ b0) (hac : a0 ≠ c0) (hbc : b0 ≠ c0) :
    ∃ z, z ≠ p ∧ z ≠ q := by
  by_cases h1 : a0 ≠ p ∧ a0 ≠ q
  · exact ⟨a0, h1⟩
  · by_cases h2 : b0 ≠ p ∧ b0 ≠ q
    · exact ⟨b0, h2⟩
    · by_cases h3 : c0 ≠ p ∧ c0 ≠ q
      · exact ⟨c0, h3⟩
      · have e1 : a0 = p ∨ a0 = q := by
          by_contra hc
          push_neg at hc
          exact h1 hc
        have e2 : b0 = p ∨ b0 = q := by
          by_contra hc
          push_neg at hc
          exact h2 hc
        have e3 : c0 = p ∨ c0 = q := by
          by_contra hc
          push_neg at hc
          exact h3 hc
        rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl <;>
          rcases e3 with rfl | rfl <;>
          first | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl hbc

private theorem expand {Alt Voter : Type} {electorate : Finset Voter}
    {F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop)}
    {G : Finset Voter} (hG : G ⊆ electorate) (hGne : G.Nonempty)
    (hUniv : ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
      IsPreorder Alt (F P) ∧ ∀ x y : Alt, F P x y ∨ F P y x)
    (hPareto : ∀ (P : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P →
      (∀ v ∈ electorate, P v a b ∧ ¬ P v b a) → F P a b ∧ ¬ F P b a)
    (hIIA : ∀ (P Q : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P → Dom electorate Q →
      (∀ v ∈ electorate, (P v a b ↔ Q v a b) ∧ (P v b a ↔ Q v b a)) →
      (F P a b ↔ F Q a b) ∧ (F P b a ↔ F Q b a))
    {a0 b0 c0 : Alt} (hab : a0 ≠ b0) (hac : a0 ≠ c0) (hbc : b0 ≠ c0)
    {p q : Alt} (hpq : p ≠ q) (hD : WeakDec electorate F G p q) :
    ∀ x y, StrongDec electorate F G x y := by
  classical
  obtain ⟨z, hzp, hzq⟩ := pivotEx hab hac hbc (p := p) (q := q)
  have hDpz : StrongDec electorate F G p z :=
    spreadA hG hUniv hPareto hIIA hpq hzp hzq hD
  have hDzq : StrongDec electorate F G z q :=
    spreadB hG hUniv hPareto hIIA hpq hzp hzq hD
  have hDpq : StrongDec electorate F G p q :=
    composeD1 hUniv hIIA (Ne.symm hzp) hzq hpq hDpz hDzq
  have hDqz : StrongDec electorate F G q z :=
    transferB hG hUniv hPareto hIIA (Ne.symm hzp) (Ne.symm hpq) (Ne.symm hzq) hDpz
  have hDzp : StrongDec electorate F G z p :=
    transferA hG hUniv hPareto hIIA hzq (Ne.symm hzp) hpq hDzq
  have row : ∀ s, s ≠ z → StrongDec electorate F G s z := by
    intro s hs
    by_cases hsp : s = p
    · subst hsp
      exact hDpz
    · by_cases hsq : s = q
      · subst hsq
        exact hDqz
      · exact transferA hG hUniv hPareto hIIA hsq (Ne.symm hs) hzq
          (transferB hG hUniv hPareto hIIA hpq hsp hsq hDpq)
  have col : ∀ t, t ≠ z → StrongDec electorate F G z t := by
    intro t ht
    by_cases htp : t = p
    · subst htp
      exact hDzp
    · by_cases htq : t = q
      · subst htq
        exact hDzq
      · exact transferB hG hUniv hPareto hIIA (Ne.symm htp) hzp (Ne.symm ht)
          (transferA hG hUniv hPareto hIIA hpq htp htq hDpq)
  intro x y
  by_cases hxy : x = y
  · subst hxy
    intro P hDom hGxx
    obtain ⟨d, hd⟩ := hGne
    have hc := hGxx d hd
    have hr := preRefl (P d) (hDom d (hG hd)).1 x
    exact absurd hr hc.2
  · by_cases hxz : x = z
    · subst hxz
      exact col y (Ne.symm hxy)
    · by_cases hyz : y = z
      · subst hyz
        exact row x hxz
      · exact composeD1 hUniv hIIA hxz (Ne.symm hyz) hxy (row x hxz) (col y hyz)

private theorem contract {Alt Voter : Type} {electorate : Finset Voter}
    {F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop)}
    {G : Finset Voter} (hG : G ⊆ electorate)
    (hD : ∀ x y, StrongDec electorate F G x y)
    {a b c : Alt} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hUniv : ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
      IsPreorder Alt (F P) ∧ ∀ x y : Alt, F P x y ∨ F P y x)
    (hPareto : ∀ (P : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P →
      (∀ v ∈ electorate, P v a b ∧ ¬ P v b a) → F P a b ∧ ¬ F P b a)
    (hIIA : ∀ (P Q : Voter → Alt → Alt → Prop) (a b : Alt),
      Dom electorate P → Dom electorate Q →
      (∀ v ∈ electorate, (P v a b ↔ Q v a b) ∧ (P v b a ↔ Q v b a)) →
      (F P a b ↔ F Q a b) ∧ (F P b a ↔ F Q b a))
    (v1 : Voter) (hv1 : v1 ∈ G) (v2 : Voter) (hv2 : v2 ∈ G) (h12 : v1 ≠ v2) :
    ∃ G', G' ⊂ G ∧ G' ⊆ electorate ∧ (∀ x y, StrongDec electorate F G' x y) ∧
      G'.Nonempty := by
  classical
  have hde : DecidableEq Voter := fun x y => Classical.propDecidable (x = y)
  set f : Voter → Alt → Nat := fun t x =>
    if t = v1 then (if x = a then 0 else if x = b then 1 else if x = c then 2 else 3)
    else if t ∈ G then (if x = b then 0 else if x = c then 1 else if x = a then 2 else 3)
    else (if x = c then 0 else if x = a then 1 else if x = b then 2 else 3) with hf
  have hDomQ : Dom electorate (fun v x y => f v x ≤ f v y) :=
    ballotDom electorate f
  have hGbc : ∀ t ∈ G, (fun x y => f t x ≤ f t y) b c ∧
      ¬ (fun x y => f t x ≤ f t y) c b := by
    intro t ht
    by_cases heq : t = v1
    · have eb : f t b = 1 := by
        simp only [hf, heq, (Ne.symm hab), ite_true, ite_false]
      have ec : f t c = 2 := by
        simp only [hf, heq, (Ne.symm hac), (Ne.symm hbc), ite_true, ite_false]
      exact (ballotStrict f t b c).mpr (by omega)
    · have eb : f t b = 0 := by
        simp only [hf, heq, ht, ite_true, ite_false]
      have ec : f t c = 1 := by
        simp only [hf, heq, ht, (Ne.symm hbc), ite_true, ite_false]
      exact (ballotStrict f t b c).mpr (by omega)
  have hSoc := hD b c _ hDomQ hGbc
  have hPreQ := (hUniv _ hDomQ).1
  have hTot := (hUniv _ hDomQ).2 a b
  by_cases hFab : F (fun v x y => f v x ≤ f v y) a b
  · have hFac : F (fun v x y => f v x ≤ f v y) a c :=
      preTrans _ hPreQ hFab hSoc.1
    have hnca : ¬ F (fun v x y => f v x ≤ f v y) c a := by
      intro hc
      exact hSoc.2 (preTrans _ hPreQ hc hFab)
    have hD2 : WeakDec electorate F {v1} a c := by
      intro P' hDom' hE hOut
      have hagree : ∀ t ∈ electorate,
          ((fun v x y => f v x ≤ f v y) t a c ↔ P' t a c) ∧
          ((fun v x y => f v x ≤ f v y) t c a ↔ P' t c a) := by
        intro t ht
        by_cases heq : t = v1
        · have ea : f t a = 0 := by
            simp only [hf, heq, ite_true]
          have ec : f t c = 2 := by
            simp only [hf, heq, (Ne.symm hac), (Ne.symm hbc), ite_true, ite_false]
          have hP := hE t (Finset.mem_singleton.mpr heq)
          have q1 : (fun v x y => f v x ≤ f v y) t a c := by
            change f t a ≤ f t c
            omega
          have q2 : ¬ (fun v x y => f v x ≤ f v y) t c a := by
            change ¬ f t c ≤ f t a
            omega
          exact ⟨iff_of_true q1 hP.1, iff_of_false q2 hP.2⟩
        · have hP := hOut t ht (by rw [Finset.mem_singleton]; exact heq)
          by_cases htG : t ∈ G
          · have ec : f t c = 1 := by
              simp only [hf, heq, htG, (Ne.symm hbc), ite_true, ite_false]
            have ea : f t a = 2 := by
              simp only [hf, heq, htG, hab, hac, ite_true, ite_false]
            have q1 : ¬ (fun v x y => f v x ≤ f v y) t a c := by
              change ¬ f t a ≤ f t c
              omega
            have q2 : (fun v x y => f v x ≤ f v y) t c a := by
              change f t c ≤ f t a
              omega
            exact ⟨iff_of_false q1 hP.2, iff_of_true q2 hP.1⟩
          · have ec : f t c = 0 := by
              simp only [hf, heq, htG, ite_true, ite_false]
            have ea : f t a = 1 := by
              simp only [hf, heq, htG, hac, ite_true, ite_false]
            have q1 : ¬ (fun v x y => f v x ≤ f v y) t a c := by
              change ¬ f t a ≤ f t c
              omega
            have q2 : (fun v x y => f v x ≤ f v y) t c a := by
              change f t c ≤ f t a
              omega
            exact ⟨iff_of_false q1 hP.2, iff_of_true q2 hP.1⟩
      have htrans := hIIA _ P' a c hDomQ hDom' hagree
      exact ⟨htrans.1.mp hFac, fun h => hnca (htrans.2.mpr h)⟩
    have hEsub : ({v1} : Finset Voter) ⊆ electorate :=
      Finset.singleton_subset_iff.mpr (hG hv1)
    have hEss : ({v1} : Finset Voter) ⊂ G :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hv1, by
        intro hEq
        have hmem : v2 ∈ ({v1} : Finset Voter) := by rw [hEq]; exact hv2
        rw [Finset.mem_singleton] at hmem
        exact h12 hmem.symm⟩
    refine ⟨{v1}, hEss, hEsub, ?_, Finset.singleton_nonempty v1⟩
    exact expand hEsub (Finset.singleton_nonempty v1) hUniv hPareto hIIA hab hac
      hbc hac hD2
  · have hFba : F (fun v x y => f v x ≤ f v y) b a := hTot.resolve_left hFab
    have hstrict : F (fun v x y => f v x ≤ f v y) b a ∧
        ¬ F (fun v x y => f v x ≤ f v y) a b := ⟨hFba, hFab⟩
    have hD2 : WeakDec electorate F (G.erase v1) b a := by
      intro P' hDom' hF hOut
      have hagree : ∀ t ∈ electorate,
          ((fun v x y => f v x ≤ f v y) t b a ↔ P' t b a) ∧
          ((fun v x y => f v x ≤ f v y) t a b ↔ P' t a b) := by
        intro t ht
        by_cases heq : t = v1
        · have hP := hOut t ht (by
            intro h
            rw [Finset.mem_erase] at h
            exact h.1 heq)
          have eb : f t b = 1 := by
            simp only [hf, heq, (Ne.symm hab), ite_true, ite_false]
          have ea : f t a = 0 := by
            simp only [hf, heq, ite_true]
          have q1 : ¬ (fun v x y => f v x ≤ f v y) t b a := by
            change ¬ f t b ≤ f t a
            omega
          have q2 : (fun v x y => f v x ≤ f v y) t a b := by
            change f t a ≤ f t b
            omega
          exact ⟨iff_of_false q1 hP.2, iff_of_true q2 hP.1⟩
        · by_cases htG : t ∈ G
          · have hPm := hF t (Finset.mem_erase.mpr ⟨heq, htG⟩)
            have eb : f t b = 0 := by
              simp only [hf, heq, htG, ite_true, ite_false]
            have ea : f t a = 2 := by
              simp only [hf, heq, htG, hab, hac, ite_true, ite_false]
            have q1 : (fun v x y => f t x ≤ f t y) t b a := by
              change f t b ≤ f t a
              omega
            have q2 : ¬ (fun v x y => f v x ≤ f v y) t a b := by
              change ¬ f t a ≤ f t b
              omega
            exact ⟨iff_of_true q1 hPm.1, iff_of_false q2 hPm.2⟩
          · have hP := hOut t ht (by
              intro h
              rw [Finset.mem_erase] at h
              exact htG h.2)
            have eb : f t b = 2 := by
              simp only [hf, heq, htG, hbc,
                (Ne.symm hab), ite_true, ite_false]
            have ea : f t a = 1 := by
              simp only [hf, heq, htG, hac, ite_true, ite_false]
            have q1 : ¬ (fun v x y => f v x ≤ f v y) t b a := by
              change ¬ f t b ≤ f t a
              omega
            have q2 : (fun v x y => f v x ≤ f v y) t a b := by
              change f t a ≤ f t b
              omega
            exact ⟨iff_of_false q1 hP.2, iff_of_true q2 hP.1⟩
      have htrans := hIIA _ P' b a hDomQ hDom' hagree
      exact ⟨htrans.1.mp hstrict.1, fun h => hstrict.2 (htrans.2.mpr h)⟩
    have hFsub : G.erase v1 ⊆ electorate := (Finset.erase_subset v1 G).trans hG
    have hFss : G.erase v1 ⊂ G := Finset.erase_ssubset hv1
    have hFne : (G.erase v1).Nonempty :=
      ⟨v2, Finset.mem_erase.mpr ⟨Ne.symm h12, hv2⟩⟩
    refine ⟨G.erase v1, hFss, hFsub, ?_, hFne⟩
    exact expand hFsub hFne hUniv hPareto hIIA hab hac hbc (Ne.symm hab) hD2
/-- Arrow's impossibility theorem (statement `arrow-impossibility-s1`):
    with at least three alternatives, no ranked voting rule with unrestricted
    domain satisfies unanimity (Pareto), independence of irrelevant alternatives
    (IIA), and non-dictatorship.
    Stable source: https://en.wikipedia.org/wiki/Arrow%27s_impossibility_theorem.

Proves `Wanted` entry `arrowImpossibility`.
-/
theorem arrowImpossibility : ∀ {Alt Voter : Type}
    (electorate : Finset Voter)
    (F : (Voter → Alt → Alt → Prop) → (Alt → Alt → Prop))
    (hexists : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hNonempty : ∃ d, d ∈ electorate)
    (hUniv : ∀ P : Voter → Alt → Alt → Prop,
      (∀ v ∈ electorate, IsPreorder Alt (P v) ∧ ∀ x y : Alt, P v x y ∨ P v y x) →
      IsPreorder Alt (F P) ∧ ∀ x y : Alt, F P x y ∨ F P y x)
    (hPareto : ∀ (P : Voter → Alt → Alt → Prop) (a b : Alt),
      (∀ v ∈ electorate, IsPreorder Alt (P v) ∧ ∀ x y : Alt, P v x y ∨ P v y x) →
      (∀ v ∈ electorate, P v a b ∧ ¬ P v b a) → F P a b ∧ ¬ F P b a)
    (hIIA : ∀ (P Q : Voter → Alt → Alt → Prop) (a b : Alt),
      (∀ v ∈ electorate, IsPreorder Alt (P v) ∧ ∀ x y : Alt, P v x y ∨ P v y x) →
      (∀ v ∈ electorate, IsPreorder Alt (Q v) ∧ ∀ x y : Alt, Q v x y ∨ Q v y x) →
      (∀ v ∈ electorate, (P v a b ↔ Q v a b) ∧ (P v b a ↔ Q v b a)) →
      (F P a b ↔ F Q a b) ∧ (F P b a ↔ F Q b a))
    (hNoDict : ∀ d ∈ electorate, ∃ (P : Voter → Alt → Alt → Prop) (a b : Alt),
      (∀ v ∈ electorate, IsPreorder Alt (P v) ∧ ∀ x y : Alt, P v x y ∨ P v y x) ∧
      (P d a b ∧ ¬ P d b a) ∧ ¬ (F P a b ∧ ¬ F P b a)),
    False := by
  intro Alt Voter electorate F hexists hNonempty hUniv hPareto hIIA hNoDict
  classical
  obtain ⟨a0, b0, c0, hab, hac, hbc⟩ := hexists
  have hUniv' : ∀ P : Voter → Alt → Alt → Prop, Dom electorate P →
      IsPreorder Alt (F P) ∧ ∀ x y : Alt, F P x y ∨ F P y x :=
    fun P h => hUniv P h
  have hPareto' : ∀ (P : Voter → Alt → Alt → Prop) (a b : Alt), Dom electorate P →
      (∀ v ∈ electorate, P v a b ∧ ¬ P v b a) → F P a b ∧ ¬ F P b a :=
    fun P a b h => hPareto P a b h
  have hIIA' : ∀ (P Q : Voter → Alt → Alt → Prop) (a b : Alt), Dom electorate P →
      Dom electorate Q →
      (∀ v ∈ electorate, (P v a b ↔ Q v a b) ∧ (P v b a ↔ Q v b a)) →
      (F P a b ↔ F Q a b) ∧ (F P b a ↔ F Q b a) :=
    fun P Q a b h1 h2 h3 => hIIA P Q a b h1 h2 h3
  have hAll : ∀ x y, StrongDec electorate F electorate x y := by
    intro x y P hDom h
    exact hPareto' P x y hDom h
  have hdict : ∀ (n : Nat) (G : Finset Voter), G ⊆ electorate →
      (∀ x y, StrongDec electorate F G x y) → G.Nonempty →
      G.card ≤ n → ∃ d, d ∈ electorate ∧ ∀ x y, StrongDec electorate F {d} x y := by
    intro n
    induction n with
    | zero =>
      intro G hG hD hne hle
      have h0 : G.card = 0 := Nat.le_zero.mp hle
      rw [Finset.card_eq_zero] at h0
      obtain ⟨d, hd⟩ := hne
      rw [h0] at hd
      exact absurd hd (Finset.notMem_empty d)
    | succ n ih =>
      intro G hG hD hne hle
      by_cases hcard : G.card ≤ 1
      · obtain ⟨d, hd⟩ := hne
        have huniq : ∀ x ∈ G, x = d :=
          fun x hx => Finset.card_le_one.mp hcard x hx d hd
        have hGeq : G = {d} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hd, huniq⟩
        subst hGeq
        exact ⟨d, hG hd, hD⟩
      · push_neg at hcard
        obtain ⟨v1, hv1, v2, hv2, h12⟩ := Finset.one_lt_card.mp hcard
        obtain ⟨G', hss, hsub, hD', hne'⟩ :=
          contract hG hD hab hac hbc hUniv' hPareto' hIIA' v1 hv1 v2 hv2 h12
        have hlt : G'.card < G.card := Finset.card_lt_card hss
        have hle' : G'.card ≤ n := by omega
        exact ih G' hsub hD' hne' hle'
  obtain ⟨d, hd⟩ := hNonempty
  obtain ⟨w, hw, hDw⟩ := hdict electorate.card electorate (Finset.Subset.refl _)
    hAll ⟨d, hd⟩ (le_refl _)
  obtain ⟨P, a, b, hDomP, hPd, hnF⟩ := hNoDict w hw
  have hsing : ∀ v ∈ ({w} : Finset Voter), P v a b ∧ ¬ P v b a := by
    intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv
    exact hPd
  exact hnF (hDw a b P hDomP hsing)

end

end MetaMathlibExt
