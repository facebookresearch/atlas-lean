/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Basic
public import MathlibExt.Order.StrictTotalOrder
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.SuccPred

@[expose] public section

section
namespace MathlibExt.GameTheory.SocialChoice.ArrowWanted

/-! # Arrow's impossibility theorem

Records Pareto and IIA for social welfare functions over strict total orders.
-/

/-- **Strict preference orders for Arrow's theorem.** A strict total order on a type $\alpha$
consists of a relation $<$ on $\alpha$ that is irreflexive ($a < a$ holds for no $a$),
transitive ($a < b$ and $b < c$ imply $a < c$) and total on distinct elements ($a \ne b$
implies $a < b$ or $b < a$). Here it models a strict preference over alternatives. -/
abbrev StrictTotalOrder := MathlibExt.Order.StrictTotalOrder

namespace StrictTotalOrder

/-- **Strict total order from a relation (Arrow's theorem).** A relation $<$ on a type $\alpha$
that is irreflexive ($a < a$ holds for no $a$), transitive ($a < b$ and $b < c$ imply $a < c$)
and total on distinct elements ($a \ne b$ implies $a < b$ or $b < a$) defines a strict total
order on $\alpha$. -/
abbrev mk {α : Type*} (lt : α → α → Prop)
    (irrefl : ∀ a, ¬lt a a)
    (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (total : ∀ {a b}, a ≠ b → lt a b ∨ lt b a) :
    StrictTotalOrder α :=
  MathlibExt.Order.StrictTotalOrder.mk lt irrefl trans total

/-- **Preference relation of a strict total order (Arrow's theorem).** For a strict total order
$T$ on a type $\alpha$, this is its underlying binary relation $<_T$ on $\alpha$. -/
abbrev lt {α : Type*} (self : StrictTotalOrder α) : α → α → Prop :=
  MathlibExt.Order.StrictTotalOrder.lt self

/-- **Irreflexivity of strict preference (Arrow's theorem).** Let $T$ be a strict total order on a
type $\alpha$, and write $a <_T b$ for its relation. Then for every $a \in \alpha$, $a <_T a$ does
not hold. -/
abbrev irrefl {α : Type*} (self : StrictTotalOrder α) (a : α) : ¬self.lt a a :=
  MathlibExt.Order.StrictTotalOrder.irrefl self a

/-- **Strict preference orders for Arrow's theorem are transitive.** If $<$ is a strict total order
on a type $\alpha$ and $a, b, c \in \alpha$ satisfy $a < b$ and $b < c$, then $a < c$. -/
abbrev trans {α : Type*} (self : StrictTotalOrder α) {a b c : α}
    (h1 : self.lt a b) (h2 : self.lt b c) : self.lt a c :=
  MathlibExt.Order.StrictTotalOrder.trans self h1 h2

/-- **Strict preference orders for Arrow's theorem are total.** If $<$ is a strict total order on
a type $\alpha$ and $a, b \in \alpha$ are distinct, then $a < b$ or $b < a$. -/
abbrev total {α : Type*} (self : StrictTotalOrder α) {a b : α} (h : a ≠ b) :
    self.lt a b ∨ self.lt b a :=
  MathlibExt.Order.StrictTotalOrder.total self h

end StrictTotalOrder

/-- **Preference profile (Arrow's theorem).** A profile assigns to each voter a strict total
order on the alternatives. -/
abbrev Profile (Alt Voter : Type*) := Voter → StrictTotalOrder Alt

/-- A social welfare function maps each unrestricted profile to a social strict total order. -/
abbrev SocialWelfareFunction (Alt Voter : Type*) := Profile Alt Voter → StrictTotalOrder Alt

/-- **Pareto condition.** A social welfare function $F$ satisfies the Pareto condition if for
every profile $p$ and all alternatives $a, b$, whenever every voter strictly prefers $a$ to $b$ in
$p$, the social order $F(p)$ also strictly prefers $a$ to $b$. -/
def IsPareto {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) : Prop :=
  ∀ (p : Profile Alt Voter) (a b : Alt), (∀ i, (p i).lt a b) → (F p).lt a b

/-- **Independence of irrelevant alternatives.** A social welfare function $F$ satisfies
independence of irrelevant alternatives if for all profiles $p_1, p_2$ and all alternatives
$a, b$ the following holds: if every voter strictly prefers $a$ to $b$ in $p_1$ exactly when that
voter strictly prefers $a$ to $b$ in $p_2$, then $F(p_1)$ strictly prefers $a$ to $b$ exactly
when $F(p_2)$ does. -/
def IsIIA {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) : Prop :=
  ∀ (p₁ p₂ : Profile Alt Voter) (a b : Alt),
    (∀ i, (p₁ i).lt a b ↔ (p₂ i).lt a b) → ((F p₁).lt a b ↔ (F p₂).lt a b)

/-- **Dictator of a social welfare function.** A voter $d$ is a dictator for a social welfare
function $F$ if for every profile $p$ and all alternatives $a, b$, whenever $d$ strictly prefers
$a$ to $b$ in $p$, the social order $F(p)$ also strictly prefers $a$ to $b$. -/
def IsDictator {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) (d : Voter) : Prop :=
  ∀ (p : Profile Alt Voter) (a b : Alt), (p d).lt a b → (F p).lt a b

/-- **Dictatorial social welfare function.** A social welfare function $F$ is dictatorial if some
voter $d$ is a dictator for $F$: for every profile $p$ and all alternatives $a, b$, whenever $d$
strictly prefers $a$ to $b$ in $p$, the social order $F(p)$ also strictly prefers $a$ to $b$. -/
def IsDictatorial {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter) : Prop :=
  ∃ d : Voter, IsDictator F d

/-- An arbitrary injection from alternatives into naturals. -/
private noncomputable def baseRank {Alt : Type*} [Fintype Alt] : Alt → ℕ :=
  fun w => (Fintype.equivFin Alt w).val

private lemma baseRank_injective {Alt : Type*} [Fintype Alt] :
    Function.Injective (baseRank (Alt := Alt)) := by
  intro a b h
  unfold baseRank at h
  have h2 : Fintype.equivFin Alt a = Fintype.equivFin Alt b := Fin.val_injective h
  exact (Fintype.equivFin Alt).injective h2

/-- Rank function putting `x` first, then `y`, then `z`, then everything else. -/
private noncomputable def rank3 {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (x y z w : Alt) : ℕ :=
  if w = x then 0 else if w = y then 1 else if w = z then 2 else 3 + baseRank (Alt := Alt) w

private lemma rank3_injective {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (x y z : Alt) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) :
    Function.Injective (rank3 (Alt := Alt) x y z) := by
  intro a b h
  have e1 : a = x ∨ a = y ∨ a = z ∨ (a ≠ x ∧ a ≠ y ∧ a ≠ z) := by
    by_cases ha1 : a = x
    · exact Or.inl ha1
    · by_cases ha2 : a = y
      · exact Or.inr (Or.inl ha2)
      · by_cases ha3 : a = z
        · exact Or.inr (Or.inr (Or.inl ha3))
        · exact Or.inr (Or.inr (Or.inr ⟨ha1, ha2, ha3⟩))
  have e2 : b = x ∨ b = y ∨ b = z ∨ (b ≠ x ∧ b ≠ y ∧ b ≠ z) := by
    by_cases hb1 : b = x
    · exact Or.inl hb1
    · by_cases hb2 : b = y
      · exact Or.inr (Or.inl hb2)
      · by_cases hb3 : b = z
        · exact Or.inr (Or.inr (Or.inl hb3))
        · exact Or.inr (Or.inr (Or.inr ⟨hb1, hb2, hb3⟩))
  unfold rank3 at h
  rcases e1 with rfl | rfl | rfl | ⟨ha1, ha2, ha3⟩ <;>
    rcases e2 with rfl | rfl | rfl | ⟨hb1, hb2, hb3⟩ <;>
    simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3]
  all_goals try omega
  exact baseRank_injective (by omega)

/-- Strict total order ranking `x` above `y` above `z` above everything else. -/
private noncomputable def mkOrder3 {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (x y z : Alt) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) : StrictTotalOrder Alt where
  lt := fun u v => rank3 (Alt := Alt) x y z u < rank3 (Alt := Alt) x y z v
  irrefl := fun a h => (lt_irrefl _) h
  trans := fun h1 h2 => Nat.lt_trans h1 h2
  total := by
    intro a b hab
    have hne : rank3 (Alt := Alt) x y z a ≠ rank3 (Alt := Alt) x y z b :=
      fun he => hab (rank3_injective x y z h1 h2 h3 he)
    exact lt_or_gt_of_ne hne

private lemma mk3_lt_xy {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    {x y z : Alt} {h1 : x ≠ y} {h2 : x ≠ z} {h3 : y ≠ z} :
    (mkOrder3 (Alt := Alt) x y z h1 h2 h3).lt x y := by
  change rank3 (Alt := Alt) x y z x < rank3 (Alt := Alt) x y z y
  unfold rank3
  simp [Ne.symm h1]

private lemma mk3_lt_yz {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    {x y z : Alt} {h1 : x ≠ y} {h2 : x ≠ z} {h3 : y ≠ z} :
    (mkOrder3 (Alt := Alt) x y z h1 h2 h3).lt y z := by
  change rank3 (Alt := Alt) x y z y < rank3 (Alt := Alt) x y z z
  unfold rank3
  simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]

private lemma mk3_lt_xz {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    {x y z : Alt} {h1 : x ≠ y} {h2 : x ≠ z} {h3 : y ≠ z} :
    (mkOrder3 (Alt := Alt) x y z h1 h2 h3).lt x z := by
  change rank3 (Alt := Alt) x y z x < rank3 (Alt := Alt) x y z z
  unfold rank3
  simp [Ne.symm h2, Ne.symm h3]

private lemma mk3_not_yx {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    {x y z : Alt} {h1 : x ≠ y} {h2 : x ≠ z} {h3 : y ≠ z} :
    ¬ (mkOrder3 (Alt := Alt) x y z h1 h2 h3).lt y x := by
  change ¬ rank3 (Alt := Alt) x y z y < rank3 (Alt := Alt) x y z x
  unfold rank3
  simp [Ne.symm h1]

private lemma mk3_not_zy {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    {x y z : Alt} {h1 : x ≠ y} {h2 : x ≠ z} {h3 : y ≠ z} :
    ¬ (mkOrder3 (Alt := Alt) x y z h1 h2 h3).lt z y := by
  change ¬ rank3 (Alt := Alt) x y z z < rank3 (Alt := Alt) x y z y
  unfold rank3
  simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]

private lemma mk3_not_zx {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    {x y z : Alt} {h1 : x ≠ y} {h2 : x ≠ z} {h3 : y ≠ z} :
    ¬ (mkOrder3 (Alt := Alt) x y z h1 h2 h3).lt z x := by
  change ¬ rank3 (Alt := Alt) x y z z < rank3 (Alt := Alt) x y z x
  unfold rank3
  simp [Ne.symm h2, Ne.symm h3]

private lemma sto_asymm {Alt : Type*} {o : StrictTotalOrder Alt} {a b : Alt}
    (h : o.lt a b) : ¬ o.lt b a :=
  fun h2 => o.irrefl a (o.trans h h2)

private lemma sto_of_not {Alt : Type*} {o : StrictTotalOrder Alt} {a b : Alt}
    (hne : a ≠ b) (hn : ¬ o.lt a b) : o.lt b a :=
  (o.total hne).resolve_left hn

private lemma sto_ne {Alt : Type*} {o : StrictTotalOrder Alt} {a b : Alt}
    (h : o.lt a b) : a ≠ b := by
  intro he
  subst he
  exact o.irrefl _ h

/-- `C` is decisive for the ordered pair `(a, b)`: whenever every member of `C`
ranks `a` above `b`, so does society. -/
private def decFor {Alt Voter : Type*} (F : SocialWelfareFunction Alt Voter)
    (C : Finset Voter) (a b : Alt) : Prop :=
  ∀ p : Profile Alt Voter, (∀ i ∈ C, (p i).lt a b) → (F p).lt a b

/-- Field expansion, first coordinate: decisiveness for `(a, b)` extends to `(a, c)`. -/
private lemma field_fst {Alt Voter : Type*} [Finite Alt]
    (F : SocialWelfareFunction Alt Voter)
    (hPareto : IsPareto F) (hIIA : IsIIA F)
    (C : Finset Voter) (a b : Alt)
    (hdec : decFor F C a b) (c : Alt) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) :
    decFor F C a c := by
  classical
  have := Fintype.ofFinite Alt
  intro p hCp
  classical
  set q : Profile Alt Voter := fun i =>
    if _ : i ∈ C then mkOrder3 (Alt := Alt) a b c hab (Ne.symm hca) (Ne.symm hcb)
    else if _ : (p i).lt a c then mkOrder3 (Alt := Alt) a b c hab (Ne.symm hca) (Ne.symm hcb)
    else mkOrder3 (Alt := Alt) b c a (Ne.symm hcb) (Ne.symm hab) hca with hqdef
  have hqC : ∀ i ∈ C, q i =
      mkOrder3 (Alt := Alt) a b c hab (Ne.symm hca) (Ne.symm hcb) := by
    intro i hi
    simp only [hqdef]
    exact dite_eq_left hi
  have hqO1 : ∀ i : Voter, i ∉ C → (p i).lt a c → q i =
      mkOrder3 (Alt := Alt) a b c hab (Ne.symm hca) (Ne.symm hcb) := by
    intro i hn hpc
    simp only [hqdef]
    rw [dite_eq_right hn]
    exact dite_eq_left hpc
  have hqO2 : ∀ i : Voter, i ∉ C → ¬ (p i).lt a c → q i =
      mkOrder3 (Alt := Alt) b c a (Ne.symm hcb) (Ne.symm hab) hca := by
    intro i hn hnpc
    simp only [hqdef]
    rw [dite_eq_right hn, dite_eq_right hnpc]
  have soc_ab : (F q).lt a b := by
    apply hdec
    intro i hi
    rw [hqC i hi]
    exact mk3_lt_xy
  have soc_bc : (F q).lt b c := by
    apply hPareto
    intro i
    by_cases hi : i ∈ C
    · rw [hqC i hi]
      exact mk3_lt_yz
    · by_cases hpc : (p i).lt a c
      · rw [hqO1 i hi hpc]
        exact mk3_lt_yz
      · rw [hqO2 i hi hpc]
        exact mk3_lt_xy
  have soc_ac : (F q).lt a c := (F q).trans soc_ab soc_bc
  have agree : ∀ i, (q i).lt a c ↔ (p i).lt a c := by
    intro i
    by_cases hi : i ∈ C
    · have hqc : (q i).lt a c := by
        rw [hqC i hi]
        exact mk3_lt_xz
      exact iff_of_true hqc (hCp i hi)
    · by_cases hpc : (p i).lt a c
      · rw [hqO1 i hi hpc]
        exact iff_of_true mk3_lt_xz hpc
      · rw [hqO2 i hi hpc]
        exact iff_of_false mk3_not_zy hpc
  exact (hIIA q p a c agree).mp soc_ac

/-- Field expansion, second coordinate: decisiveness for `(a, b)` extends to `(c, b)`. -/
private lemma field_snd {Alt Voter : Type*} [Finite Alt]
    (F : SocialWelfareFunction Alt Voter)
    (hPareto : IsPareto F) (hIIA : IsIIA F)
    (C : Finset Voter) (a b : Alt)
    (hdec : decFor F C a b) (c : Alt) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) :
    decFor F C c b := by
  classical
  have := Fintype.ofFinite Alt
  intro p hCp
  classical
  set q : Profile Alt Voter := fun i =>
    if _ : i ∈ C then mkOrder3 (Alt := Alt) c a b hca hcb hab
    else if _ : (p i).lt c b then mkOrder3 (Alt := Alt) c a b hca hcb hab
    else mkOrder3 (Alt := Alt) b c a (Ne.symm hcb) (Ne.symm hab) hca with hqdef
  have hqC : ∀ i ∈ C, q i =
      mkOrder3 (Alt := Alt) c a b hca hcb hab := by
    intro i hi
    simp only [hqdef]
    exact dite_eq_left hi
  have hqO1 : ∀ i : Voter, i ∉ C → (p i).lt c b → q i =
      mkOrder3 (Alt := Alt) c a b hca hcb hab := by
    intro i hn hpc
    simp only [hqdef]
    rw [dite_eq_right hn]
    exact dite_eq_left hpc
  have hqO2 : ∀ i : Voter, i ∉ C → ¬ (p i).lt c b → q i =
      mkOrder3 (Alt := Alt) b c a (Ne.symm hcb) (Ne.symm hab) hca := by
    intro i hn hnpc
    simp only [hqdef]
    rw [dite_eq_right hn, dite_eq_right hnpc]
  have soc_ab : (F q).lt a b := by
    apply hdec
    intro i hi
    rw [hqC i hi]
    exact mk3_lt_yz
  have soc_ca : (F q).lt c a := by
    apply hPareto
    intro i
    by_cases hi : i ∈ C
    · rw [hqC i hi]
      exact mk3_lt_xy
    · by_cases hpc : (p i).lt c b
      · rw [hqO1 i hi hpc]
        exact mk3_lt_xy
      · rw [hqO2 i hi hpc]
        exact mk3_lt_yz
  have soc_cb : (F q).lt c b := (F q).trans soc_ca soc_ab
  have agree : ∀ i, (q i).lt c b ↔ (p i).lt c b := by
    intro i
    by_cases hi : i ∈ C
    · have hqc : (q i).lt c b := by
        rw [hqC i hi]
        exact mk3_lt_xz
      exact iff_of_true hqc (hCp i hi)
    · by_cases hpc : (p i).lt c b
      · rw [hqO1 i hi hpc]
        exact iff_of_true mk3_lt_xz hpc
      · rw [hqO2 i hi hpc]
        exact iff_of_false mk3_not_yx hpc
  exact (hIIA q p c b agree).mp soc_cb

/-- From three pairwise-distinct alternatives, find one avoiding two given elements. -/
private lemma exists_third {Alt : Type*} {a b c : Alt}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x y : Alt) :
    ∃ d, d ≠ x ∧ d ≠ y := by
  by_cases hxa : x = a
  · subst hxa
    by_cases hyb : y = b
    · subst hyb
      exact ⟨c, Ne.symm hac, Ne.symm hbc⟩
    · exact ⟨b, Ne.symm hab, fun he => hyb he.symm⟩
  · by_cases hya : y = a
    · subst hya
      by_cases hxb : x = b
      · subst hxb
        exact ⟨c, fun he => hbc he.symm, Ne.symm hac⟩
      · exact ⟨b, fun he => hxb he.symm, Ne.symm hab⟩
    · exact ⟨a, Ne.symm hxa, Ne.symm hya⟩

/-- Full neutrality: decisiveness for one pair spreads to every pair. -/
private lemma chain {Alt Voter : Type*} [Finite Alt]
    (F : SocialWelfareFunction Alt Voter)
    (hPareto : IsPareto F) (hIIA : IsIIA F)
    (C : Finset Voter) (a0 b0 : Alt) (hab0 : a0 ≠ b0)
    (hdec : decFor F C a0 b0)
    (a b c : Alt) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x y : Alt) (hxy : x ≠ y) :
    decFor F C x y := by
  classical
  by_cases hx0 : x = a0
  · rw [hx0] at hxy ⊢
    by_cases hy0 : y = b0
    · rw [hy0]
      exact hdec
    · exact field_fst F hPareto hIIA C a0 b0 hdec y (Ne.symm hxy) hy0 hab0
  · by_cases hx1 : x = b0
    · rw [hx1] at hxy ⊢
      obtain ⟨e, hea, heb⟩ := exists_third hab hac hbc a0 b0
      have h1 : decFor F C a0 e :=
        field_fst F hPareto hIIA C a0 b0 hdec e hea heb hab0
      have h2 : decFor F C b0 e :=
        field_snd F hPareto hIIA C a0 e h1 b0 (Ne.symm hab0) (Ne.symm heb) (Ne.symm hea)
      by_cases hye : y = e
      · rw [hye]
        exact h2
      · exact field_fst F hPareto hIIA C b0 e h2 y (Ne.symm hxy) hye (Ne.symm heb)
    · have h1 : decFor F C x b0 :=
        field_snd F hPareto hIIA C a0 b0 hdec x hx0 hx1 hab0
      by_cases hy0 : y = b0
      · rw [hy0]
        exact h1
      · exact field_fst F hPareto hIIA C x b0 h1 y (Ne.symm hxy) hy0 hx1

/-- Intersection of fully decisive coalitions is fully decisive. -/
private lemma inter_dec {Alt Voter : Type*} [Finite Alt] [DecidableEq Voter]
    (F : SocialWelfareFunction Alt Voter)
    (hIIA : IsIIA F)
    (C1 C2 : Finset Voter)
    (h1 : ∀ x y : Alt, x ≠ y → decFor F C1 x y)
    (h2 : ∀ x y : Alt, x ≠ y → decFor F C2 x y)
    (a b c : Alt) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x y : Alt) (hxy : x ≠ y) :
    decFor F (C1 ∩ C2) x y := by
  classical
  have := Fintype.ofFinite Alt
  intro p hCp
  classical
  obtain ⟨e, hex, hey⟩ := exists_third hab hac hbc x y
  set q : Profile Alt Voter := fun i =>
    if _ : i ∈ C1 then
      (if _ : i ∈ C2 then mkOrder3 (Alt := Alt) x e y (Ne.symm hex) hxy hey
       else if _ : (p i).lt x y then mkOrder3 (Alt := Alt) x y e hxy (Ne.symm hex) (Ne.symm hey)
       else mkOrder3 (Alt := Alt) y x e (Ne.symm hxy) (Ne.symm hey) (Ne.symm hex))
    else
      (if _ : i ∈ C2 then
        (if _ : (p i).lt x y then mkOrder3 (Alt := Alt) x e y (Ne.symm hex) hxy hey
         else mkOrder3 (Alt := Alt) e y x hey hex (Ne.symm hxy))
       else if _ : (p i).lt x y then mkOrder3 (Alt := Alt) x y e hxy (Ne.symm hex) (Ne.symm hey)
       else mkOrder3 (Alt := Alt) y x e (Ne.symm hxy) (Ne.symm hey) (Ne.symm hex)) with hqdef
  have hqII : ∀ i : Voter, i ∈ C1 → i ∈ C2 → q i =
      mkOrder3 (Alt := Alt) x e y (Ne.symm hex) hxy hey := by
    intro i hi1 hi2
    simp only [hqdef]
    rw [dite_eq_left hi1, dite_eq_left hi2]
  have hqI1 : ∀ i : Voter, i ∈ C1 → i ∉ C2 → (p i).lt x y → q i =
      mkOrder3 (Alt := Alt) x y e hxy (Ne.symm hex) (Ne.symm hey) := by
    intro i hi1 hi2 hpxy
    simp only [hqdef]
    rw [dite_eq_left hi1, dite_eq_right hi2, dite_eq_left hpxy]
  have hqI2 : ∀ i : Voter, i ∈ C1 → i ∉ C2 → ¬ (p i).lt x y → q i =
      mkOrder3 (Alt := Alt) y x e (Ne.symm hxy) (Ne.symm hey) (Ne.symm hex) := by
    intro i hi1 hi2 hpxy
    simp only [hqdef]
    rw [dite_eq_left hi1, dite_eq_right hi2, dite_eq_right hpxy]
  have hqJ1 : ∀ i : Voter, i ∉ C1 → i ∈ C2 → (p i).lt x y → q i =
      mkOrder3 (Alt := Alt) x e y (Ne.symm hex) hxy hey := by
    intro i hn1 hi2 hpxy
    simp only [hqdef]
    rw [dite_eq_right hn1, dite_eq_left hi2, dite_eq_left hpxy]
  have hqJ2 : ∀ i : Voter, i ∉ C1 → i ∈ C2 → ¬ (p i).lt x y → q i =
      mkOrder3 (Alt := Alt) e y x hey hex (Ne.symm hxy) := by
    intro i hn1 hi2 hpxy
    simp only [hqdef]
    rw [dite_eq_right hn1, dite_eq_left hi2, dite_eq_right hpxy]
  have hqO1 : ∀ i : Voter, i ∉ C1 → i ∉ C2 → (p i).lt x y → q i =
      mkOrder3 (Alt := Alt) x y e hxy (Ne.symm hex) (Ne.symm hey) := by
    intro i hn1 hn2 hpxy
    simp only [hqdef]
    rw [dite_eq_right hn1, dite_eq_right hn2, dite_eq_left hpxy]
  have hqO2 : ∀ i : Voter, i ∉ C1 → i ∉ C2 → ¬ (p i).lt x y → q i =
      mkOrder3 (Alt := Alt) y x e (Ne.symm hxy) (Ne.symm hey) (Ne.symm hex) := by
    intro i hn1 hn2 hpxy
    simp only [hqdef]
    rw [dite_eq_right hn1, dite_eq_right hn2, dite_eq_right hpxy]
  have soc_xe : (F q).lt x e := by
    apply h1 x e (Ne.symm hex)
    intro i hi
    by_cases hi2 : i ∈ C2
    · rw [hqII i hi hi2]
      exact mk3_lt_xy
    · by_cases hpxy : (p i).lt x y
      · rw [hqI1 i hi hi2 hpxy]
        exact mk3_lt_xz
      · rw [hqI2 i hi hi2 hpxy]
        exact mk3_lt_yz
  have soc_ey : (F q).lt e y := by
    apply h2 e y hey
    intro i hi
    by_cases hi1 : i ∈ C1
    · rw [hqII i hi1 hi]
      exact mk3_lt_yz
    · by_cases hpxy : (p i).lt x y
      · rw [hqJ1 i hi1 hi hpxy]
        exact mk3_lt_yz
      · rw [hqJ2 i hi1 hi hpxy]
        exact mk3_lt_xy
  have soc_xy : (F q).lt x y := (F q).trans soc_xe soc_ey
  have agree : ∀ i, (q i).lt x y ↔ (p i).lt x y := by
    intro i
    by_cases hi1 : i ∈ C1
    · by_cases hi2 : i ∈ C2
      · have hqc : (q i).lt x y := by
          rw [hqII i hi1 hi2]
          exact mk3_lt_xz
        exact iff_of_true hqc (hCp i (Finset.mem_inter.mpr ⟨hi1, hi2⟩))
      · by_cases hpxy : (p i).lt x y
        · rw [hqI1 i hi1 hi2 hpxy]
          exact iff_of_true mk3_lt_xy hpxy
        · rw [hqI2 i hi1 hi2 hpxy]
          exact iff_of_false mk3_not_yx hpxy
    · by_cases hi2 : i ∈ C2
      · by_cases hpxy : (p i).lt x y
        · rw [hqJ1 i hi1 hi2 hpxy]
          exact iff_of_true mk3_lt_xz hpxy
        · rw [hqJ2 i hi1 hi2 hpxy]
          exact iff_of_false mk3_not_zy hpxy
      · by_cases hpxy : (p i).lt x y
        · rw [hqO1 i hi1 hi2 hpxy]
          exact iff_of_true mk3_lt_xy hpxy
        · rw [hqO2 i hi1 hi2 hpxy]
          exact iff_of_false mk3_not_yx hpxy
  exact (hIIA q p x y agree).mp soc_xy

/-- Left sandwich: if society ranks `a` above `b` in a profile where `V1` ranks
`a > b > c` and everyone else ranks `c > b > a`, then `V1` is decisive for `(a, c)`. -/
private lemma sandwichA {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    (F : SocialWelfareFunction Alt Voter)
    (hPareto : IsPareto F) (hIIA : IsIIA F)
    (V1 : Finset Voter)
    (a b c : Alt) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Profile Alt Voter)
    (hpV1 : ∀ i ∈ V1, p i =
      mkOrder3 (Alt := Alt) a b c hab hac hbc)
    (hpOut : ∀ i : Voter, i ∉ V1 → p i =
      mkOrder3 (Alt := Alt) c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab))
    (hsoc : (F p).lt a b) :
    decFor F V1 a c := by
  classical
  intro q hCq
  classical
  set r : Profile Alt Voter := fun i =>
    if _ : i ∈ V1 then mkOrder3 (Alt := Alt) a b c hab hac hbc
    else if _ : (q i).lt a c then mkOrder3 (Alt := Alt) b a c (Ne.symm hab) hbc hac
    else mkOrder3 (Alt := Alt) b c a hbc (Ne.symm hab) (Ne.symm hac) with hrdef
  have hrV1 : ∀ i ∈ V1, r i =
      mkOrder3 (Alt := Alt) a b c hab hac hbc := by
    intro i hi
    simp only [hrdef]
    exact dite_eq_left hi
  have hrO1 : ∀ i : Voter, i ∉ V1 → (q i).lt a c → r i =
      mkOrder3 (Alt := Alt) b a c (Ne.symm hab) hbc hac := by
    intro i hn hqc
    simp only [hrdef]
    rw [dite_eq_right hn, dite_eq_left hqc]
  have hrO2 : ∀ i : Voter, i ∉ V1 → ¬ (q i).lt a c → r i =
      mkOrder3 (Alt := Alt) b c a hbc (Ne.symm hab) (Ne.symm hac) := by
    intro i hn hqc
    simp only [hrdef]
    rw [dite_eq_right hn, dite_eq_right hqc]
  have agreeAB : ∀ i, (r i).lt a b ↔ (p i).lt a b := by
    intro i
    by_cases hi : i ∈ V1
    · rw [hrV1 i hi, hpV1 i hi]
    · by_cases hqc : (q i).lt a c
      · rw [hrO1 i hi hqc, hpOut i hi]
        exact iff_of_false mk3_not_yx mk3_not_zy
      · rw [hrO2 i hi hqc, hpOut i hi]
        exact iff_of_false mk3_not_zx mk3_not_zy
  have soc_ab : (F r).lt a b := (hIIA r p a b agreeAB).mpr hsoc
  have soc_bc : (F r).lt b c := by
    apply hPareto
    intro i
    by_cases hi : i ∈ V1
    · rw [hrV1 i hi]
      exact mk3_lt_yz
    · by_cases hqc : (q i).lt a c
      · rw [hrO1 i hi hqc]
        exact mk3_lt_xz
      · rw [hrO2 i hi hqc]
        exact mk3_lt_xy
  have soc_ac : (F r).lt a c := (F r).trans soc_ab soc_bc
  have agreeAC : ∀ i, (r i).lt a c ↔ (q i).lt a c := by
    intro i
    by_cases hi : i ∈ V1
    · rw [hrV1 i hi]
      exact iff_of_true mk3_lt_xz (hCq i hi)
    · by_cases hqc : (q i).lt a c
      · rw [hrO1 i hi hqc]
        exact iff_of_true mk3_lt_yz hqc
      · rw [hrO2 i hi hqc]
        exact iff_of_false mk3_not_zy hqc
  exact (hIIA r q a c agreeAC).mp soc_ac

/-- Right sandwich: if society ranks `b` above `a` in a profile where `V1` ranks
`a > b > c` and `V2` ranks `c > b > a` (covering all voters), then `V2` is
decisive for `(c, a)`. -/
private lemma sandwichB {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    (F : SocialWelfareFunction Alt Voter)
    (hPareto : IsPareto F) (hIIA : IsIIA F)
    (V1 V2 : Finset Voter) (hdisj : Disjoint V1 V2)
    (a b c : Alt) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (p : Profile Alt Voter)
    (hpV1 : ∀ i ∈ V1, p i =
      mkOrder3 (Alt := Alt) a b c hab hac hbc)
    (hpV2 : ∀ i ∈ V2, p i =
      mkOrder3 (Alt := Alt) c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab))
    (hcover : ∀ i : Voter, i ∈ V1 ∨ i ∈ V2)
    (hsoc : (F p).lt b a) :
    decFor F V2 c a := by
  classical
  intro q hCq
  classical
  set r : Profile Alt Voter := fun i =>
    if _ : i ∈ V2 then mkOrder3 (Alt := Alt) c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab)
    else if _ : i ∈ V1 then
      (if _ : (q i).lt c a then mkOrder3 (Alt := Alt) c a b (Ne.symm hac) (Ne.symm hbc) hab
       else mkOrder3 (Alt := Alt) a c b hac hab (Ne.symm hbc))
    else mkOrder3 (Alt := Alt) c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) with hrdef
  have hrV2 : ∀ i ∈ V2, r i =
      mkOrder3 (Alt := Alt) c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) := by
    intro i hi
    simp only [hrdef]
    exact dite_eq_left hi
  have hrV1a : ∀ i : Voter, i ∉ V2 → i ∈ V1 → (q i).lt c a → r i =
      mkOrder3 (Alt := Alt) c a b (Ne.symm hac) (Ne.symm hbc) hab := by
    intro i hn2 hi1 hqc
    simp only [hrdef]
    rw [dite_eq_right hn2, dite_eq_left hi1, dite_eq_left hqc]
  have hrV1b : ∀ i : Voter, i ∉ V2 → i ∈ V1 → ¬ (q i).lt c a → r i =
      mkOrder3 (Alt := Alt) a c b hac hab (Ne.symm hbc) := by
    intro i hn2 hi1 hqc
    simp only [hrdef]
    rw [dite_eq_right hn2, dite_eq_left hi1, dite_eq_right hqc]
  have hrO : ∀ i : Voter, i ∉ V2 → i ∉ V1 → r i =
      mkOrder3 (Alt := Alt) c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) := by
    intro i hn2 hn1
    simp only [hrdef]
    rw [dite_eq_right hn2, dite_eq_right hn1]
  have agreeBA : ∀ i, (r i).lt b a ↔ (p i).lt b a := by
    intro i
    by_cases hi2 : i ∈ V2
    · rw [hrV2 i hi2, hpV2 i hi2]
    · by_cases hi1 : i ∈ V1
      · have hn2 : i ∉ V2 := Finset.disjoint_left.mp hdisj hi1
        by_cases hqc : (q i).lt c a
        · rw [hrV1a i hn2 hi1 hqc, hpV1 i hi1]
          exact iff_of_false mk3_not_zy mk3_not_yx
        · rw [hrV1b i hn2 hi1 hqc, hpV1 i hi1]
          exact iff_of_false mk3_not_zx mk3_not_yx
      · rw [hrO i hi2 hi1]
        rcases hcover i with h | h
        · exact absurd h hi1
        · exact absurd h hi2
  have soc_ba : (F r).lt b a := (hIIA r p b a agreeBA).mpr hsoc
  have soc_cb : (F r).lt c b := by
    apply hPareto
    intro i
    by_cases hi2 : i ∈ V2
    · rw [hrV2 i hi2]
      exact mk3_lt_xy
    · by_cases hi1 : i ∈ V1
      · have hn2 : i ∉ V2 := Finset.disjoint_left.mp hdisj hi1
        by_cases hqc : (q i).lt c a
        · rw [hrV1a i hn2 hi1 hqc]
          exact mk3_lt_xz
        · rw [hrV1b i hn2 hi1 hqc]
          exact mk3_lt_yz
      · rw [hrO i hi2 hi1]
        exact mk3_lt_xy
  have soc_ca : (F r).lt c a := (F r).trans soc_cb soc_ba
  have agreeCA : ∀ i, (r i).lt c a ↔ (q i).lt c a := by
    intro i
    by_cases hi2 : i ∈ V2
    · rw [hrV2 i hi2]
      exact iff_of_true mk3_lt_xz (hCq i hi2)
    · by_cases hi1 : i ∈ V1
      · have hn2 : i ∉ V2 := Finset.disjoint_left.mp hdisj hi1
        by_cases hqc : (q i).lt c a
        · rw [hrV1a i hn2 hi1 hqc]
          exact iff_of_true mk3_lt_xy hqc
        · rw [hrV1b i hn2 hi1 hqc]
          exact iff_of_false mk3_not_yx hqc
      · rw [hrO i hi2 hi1]
        rcases hcover i with h | h
        · exact absurd h hi1
        · exact absurd h hi2
  exact (hIIA r q c a agreeCA).mp soc_ca

/-- Contraction for full partitions: one side is decisive for a single pair. -/
private lemma prime {Alt Voter : Type*} [Finite Alt] [DecidableEq Voter]
    [Fintype Voter]
    (F : SocialWelfareFunction Alt Voter)
    (hPareto : IsPareto F) (hIIA : IsIIA F)
    (V1 V2 : Finset Voter) (hdisj : Disjoint V1 V2) (hunion : V1 ∪ V2 = Finset.univ)
    (a b c : Alt) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    decFor F V1 a c ∨ decFor F V2 c a := by
  classical
  have := Fintype.ofFinite Alt
  set p : Profile Alt Voter := fun i =>
    if _ : i ∈ V1 then mkOrder3 (Alt := Alt) a b c hab hac hbc
    else mkOrder3 (Alt := Alt) c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) with hpdef
  have hpV1 : ∀ i ∈ V1, p i =
      mkOrder3 (Alt := Alt) a b c hab hac hbc := by
    intro i hi
    simp only [hpdef]
    exact dite_eq_left hi
  have hpOut : ∀ i : Voter, i ∉ V1 → p i =
      mkOrder3 (Alt := Alt) c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) := by
    intro i hn
    simp only [hpdef]
    exact dite_eq_right hn
  have hpV2 : ∀ i ∈ V2, p i =
      mkOrder3 (Alt := Alt) c b a (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) := by
    intro i hi
    have hn : i ∉ V1 := fun hi1 => (Finset.disjoint_left.mp hdisj hi1) hi
    exact hpOut i hn
  have hcover : ∀ i : Voter, i ∈ V1 ∨ i ∈ V2 := by
    intro i
    have hmem : i ∈ V1 ∪ V2 := by
      rw [hunion]
      exact Finset.mem_univ i
    exact Finset.mem_union.mp hmem
  rcases (F p).total hab with hsoc | hsoc
  · exact Or.inl (sandwichA F hPareto hIIA V1 a b c hab hac hbc p hpV1 hpOut hsoc)
  · exact Or.inr (sandwichB F hPareto hIIA V1 V2 hdisj a b c hab hac hbc p hpV1 hpV2 hcover hsoc)

/-- Finite descent: some singleton is fully decisive. -/
private lemma descent {Alt Voter : Type*} [Finite Alt]
    [Finite Voter]
    (F : SocialWelfareFunction Alt Voter)
    (hPareto : IsPareto F) (hIIA : IsIIA F)
    (a b c : Alt) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ d : Voter, ∀ x y : Alt, x ≠ y → decFor F {d} x y := by
  classical
  have := Fintype.ofFinite Alt
  have := Fintype.ofFinite Voter
  suffices h : ∀ n : ℕ, ∀ C : Finset Voter, C.card ≤ n →
      (∀ x y : Alt, x ≠ y → decFor F C x y) →
      ∃ d ∈ C, ∀ x y : Alt, x ≠ y → decFor F {d} x y by
    have huniv : ∀ x y : Alt, x ≠ y → decFor F Finset.univ x y := by
      intro x y hxy p hp
      exact hPareto p x y (fun i => hp i (Finset.mem_univ i))
    obtain ⟨d, -, hd⟩ := h Finset.univ.card Finset.univ le_rfl huniv
    exact ⟨d, hd⟩
  intro n
  induction n with
  | zero =>
    intro C hcard hC
    have hempty : C = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hempty
    exfalso
    have hdec : decFor F ∅ a b := hC a b hab
    set p0 : Profile Alt Voter :=
      fun _ => mkOrder3 (Alt := Alt) b a c (Ne.symm hab) hbc hac with hpdef
    have hall : ∀ i ∈ (∅ : Finset Voter), (p0 i).lt a b := by
      intro i hi
      exact absurd hi (Finset.notMem_empty i)
    have hsoc : (F p0).lt a b := hdec p0 hall
    have hp0 : ∀ i : Voter, p0 i =
        mkOrder3 (Alt := Alt) b a c (Ne.symm hab) hbc hac := by
      intro i
      rfl
    have hsoc2 : (F p0).lt b a := by
      apply hPareto
      intro i
      rw [hp0 i]
      exact mk3_lt_xy
    exact sto_asymm hsoc hsoc2
  | succ n ih =>
    intro C hcard hC
    by_cases hle : C.card ≤ n
    · exact ih C hle hC
    · have hcard' : C.card = n + 1 := by omega
      have hpos : 0 < C.card := by omega
      obtain ⟨x, hxC⟩ := Finset.card_pos.mp hpos
      have hdisj : Disjoint ({x} : Finset Voter) (Finset.univ \ {x}) := by
        rw [Finset.disjoint_left]
        intro i hi hcon
        obtain ⟨-, hnx⟩ := Finset.mem_sdiff.mp hcon
        exact hnx (Finset.mem_singleton.mpr (Finset.mem_singleton.mp hi))
      have hunion : ({x} : Finset Voter) ∪ (Finset.univ \ {x}) = Finset.univ := by
        rw [Finset.union_comm]
        exact Finset.sdiff_union_of_subset (Finset.subset_univ {x})
      rcases prime F hPareto hIIA {x} (Finset.univ \ {x}) hdisj hunion
          a b c hab hac hbc with hleft | hright
      · have hfull : ∀ x' y' : Alt, x' ≠ y' → decFor F {x} x' y' := by
          intro x' y' hxy'
          exact chain F hPareto hIIA {x} a c hac hleft a b c hab hac hbc x' y' hxy'
        exact ⟨x, hxC, hfull⟩
      · have hfull2 : ∀ x' y' : Alt, x' ≠ y' → decFor F (Finset.univ \ {x}) x' y' := by
          intro x' y' hxy'
          exact chain F hPareto hIIA (Finset.univ \ {x}) c a (Ne.symm hac)
            hright a b c hab hac hbc x' y' hxy'
        have hinter : ∀ x' y' : Alt, x' ≠ y' → decFor F (C \ {x}) x' y' := by
          intro x' y' hxy'
          have hsub : C ∩ (Finset.univ \ {x}) = C \ {x} := by
            ext i
            simp [Finset.mem_inter, Finset.mem_sdiff]
          rw [← hsub]
          exact inter_dec F hIIA C (Finset.univ \ {x}) hC hfull2 a b c hab hac hbc x' y' hxy'
        have hcard2 : (C \ {x}).card ≤ n := by
          rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hxC]
          omega
        obtain ⟨d, hdC, hdfull⟩ := ih (C \ {x}) hcard2 hinter
        refine ⟨d, ?_, hdfull⟩
        exact (Finset.mem_sdiff.mp hdC).1

/--
**Arrow's impossibility theorem for strict preferences, general form.** Suppose there are
finitely many alternatives, at least three of them, and finitely many voters, at least one. Then
every social welfare function, which assigns a strict total order of the alternatives to each
profile of strict total orders (one per voter), that satisfies the Pareto condition and
independence of irrelevant alternatives is dictatorial.

Here finiteness is assumed only as a property. The companion statement of Arrow's impossibility
theorem also fixes an explicit enumeration of the alternatives and of the voters and a decision
procedure for equality on each; this extra data does not change the mathematical content.
-/
theorem arrow_impossibility_general
    {Alt Voter : Type*} [Finite Alt] [Finite Voter] [Nonempty Voter]
    (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (F : SocialWelfareFunction Alt Voter)
    (hPareto : IsPareto F) (hIIA : IsIIA F) :
    IsDictatorial F := by
  obtain ⟨a, b, c, hab, hac, hbc⟩ := hAlt
  obtain ⟨d, hd⟩ := descent F hPareto hIIA a b c hab hac hbc
  refine ⟨d, fun p x y hxy => ?_⟩
  by_cases hxx : x = y
  · rw [hxx] at hxy ⊢
    exact False.elim ((p d).irrefl y hxy)
  · exact hd x y hxx p (fun i hi => by
      obtain rfl := Finset.mem_singleton.mp hi
      exact hxy)

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/--
**Arrow's impossibility theorem for strict preferences.** Suppose there are finitely many
alternatives, at least three of them, and finitely many voters, at least one. Then every social
welfare function, which assigns a strict total order of the alternatives to each profile of strict
total orders (one per voter), that satisfies the Pareto condition and independence of irrelevant
alternatives is dictatorial.

Source: K. J. Arrow, Social Choice and Individual Values, Wiley (1951; 2nd ed. 1963).

Proves `Wanted` entry `arrow_impossibility`.
-/
theorem arrow_impossibility
    {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (F : SocialWelfareFunction Alt Voter)
    (hPareto : IsPareto F) (hIIA : IsIIA F) :
    IsDictatorial F :=
  arrow_impossibility_general hAlt F hPareto hIIA

end MathlibExt.GameTheory.SocialChoice.ArrowWanted
end
