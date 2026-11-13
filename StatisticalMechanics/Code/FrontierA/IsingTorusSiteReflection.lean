/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusSpinReflection

open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

private theorem isingTorus_side_eq_two_half :
    2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring



def isingTorusSiteReflect (i : Fin d) (x : IsingDyadicTorus d k) :
    IsingDyadicTorus d k :=
  Function.update x i (-x i)

@[simp] theorem isingTorusSiteReflect_apply_same
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusSiteReflect i x i = -x i := by
  simp [isingTorusSiteReflect]

theorem isingTorusSiteReflect_apply_of_ne
    (i j : Fin d) (hji : j ≠ i) (x : IsingDyadicTorus d k) :
    isingTorusSiteReflect i x j = x j := by
  simp [isingTorusSiteReflect, hji]

@[simp] theorem isingTorusSiteReflect_involutive
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusSiteReflect i (isingTorusSiteReflect i x) = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [isingTorusSiteReflect_apply_of_ne i j hji]


def isingTorusOnSitePlane (i : Fin d) (x : IsingDyadicTorus d k) : Prop :=
  (x i).val = 0 ∨ (x i).val = 2 ^ (k + 1)


def isingTorusInStrictLower (i : Fin d) (x : IsingDyadicTorus d k) : Prop :=
  0 < (x i).val ∧ (x i).val < 2 ^ (k + 1)

instance (i : Fin d) (x : IsingDyadicTorus d k) :
    Decidable (isingTorusOnSitePlane i x) :=
  instDecidableOr

instance (i : Fin d) (x : IsingDyadicTorus d k) :
    Decidable (isingTorusInStrictLower i x) :=
  instDecidableAnd

theorem isingTorusSiteReflect_fixed
    (i : Fin d) {x : IsingDyadicTorus d k}
    (hx : isingTorusOnSitePlane i x) :
    isingTorusSiteReflect i x = x := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [isingTorusSiteReflect_apply_same]
    apply (ZMod.neg_eq_self_iff (x i)).2
    rcases hx with hx | hx
    · left
      exact (ZMod.val_eq_zero (x i)).mp hx
    · right
      rw [hx, isingTorus_side_eq_two_half]
  · exact isingTorusSiteReflect_apply_of_ne i j hji x

theorem isingTorusSiteReflect_strictLower_of_upper
    (i : Fin d) {x : IsingDyadicTorus d k}
    (hplane : ¬ isingTorusOnSitePlane i x)
    (hlower : ¬ isingTorusInStrictLower i x) :
    isingTorusInStrictLower i (isingTorusSiteReflect i x) := by
  have hx0 : (x i).val ≠ 0 := fun h => hplane (Or.inl h)
  have hxhalf : (x i).val ≠ 2 ^ (k + 1) :=
    fun h => hplane (Or.inr h)
  have hxge : 2 ^ (k + 1) < (x i).val := by
    unfold isingTorusInStrictLower at hlower
    push Not at hlower
    have hpos : 0 < (x i).val := Nat.pos_of_ne_zero hx0
    have hge := hlower hpos
    omega
  have hxi0 : x i ≠ 0 := (ZMod.val_ne_zero (x i)).mp hx0
  unfold isingTorusInStrictLower
  rw [isingTorusSiteReflect_apply_same, ZMod.neg_val,
    if_neg hxi0]
  have hxlt := (x i).val_lt
  have hside := isingTorus_side_eq_two_half (k := k)
  omega

theorem isingTorusSiteReflect_not_plane
    (i : Fin d) {x : IsingDyadicTorus d k}
    (hx : ¬ isingTorusOnSitePlane i x) :
    ¬ isingTorusOnSitePlane i (isingTorusSiteReflect i x) := by
  intro hr
  have heq : x = isingTorusSiteReflect i x := by
    simpa using isingTorusSiteReflect_fixed i hr
  apply hx
  rw [heq]
  exact hr

abbrev IsingTorusSitePlane (i : Fin d) :=
  {x : IsingDyadicTorus d k // isingTorusOnSitePlane i x}

abbrev IsingTorusStrictLower (i : Fin d) :=
  {x : IsingDyadicTorus d k // isingTorusInStrictLower i x}


def isingTorusSiteGlue (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    ConfigSpace (IsingDyadicTorus d k) :=
  fun x => if hp : isingTorusOnSitePlane i x then boundary ⟨x, hp⟩
    else if hl : isingTorusInStrictLower i x then lower ⟨x, hl⟩
    else upper ⟨isingTorusSiteReflect i x,
      isingTorusSiteReflect_strictLower_of_upper i hp hl⟩


def isingTorusSiteSplit (i : Fin d)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    ConfigSpace (IsingTorusSitePlane (k := k) i) ×
      (ConfigSpace (IsingTorusStrictLower (k := k) i) ×
        ConfigSpace (IsingTorusStrictLower (k := k) i)) :=
  (fun x => sigma x.1,
    (fun x => sigma x.1, fun x => sigma (isingTorusSiteReflect i x.1)))

@[simp] theorem isingTorusSiteSplit_glue
    (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusSiteSplit i (isingTorusSiteGlue i boundary lower upper) =
      (boundary, (lower, upper)) := by
  apply Prod.ext
  · funext x
    simp [isingTorusSiteSplit, isingTorusSiteGlue, x.2]
  · apply Prod.ext
    · funext x
      have hnp : ¬ isingTorusOnSitePlane i x.1 := by
        intro hp
        rcases x.2 with ⟨hx0, hxhalf⟩
        rcases hp with hp | hp <;> omega
      simp [isingTorusSiteSplit, isingTorusSiteGlue, hnp, x.2]
    · funext x
      have hnp : ¬ isingTorusOnSitePlane i x.1 := by
        intro hp
        rcases x.2 with ⟨hx0, hxhalf⟩
        rcases hp with hp | hp <;> omega
      have hnpR : ¬ isingTorusOnSitePlane i
          (isingTorusSiteReflect i x.1) :=
        isingTorusSiteReflect_not_plane i hnp
      have hlR : ¬ isingTorusInStrictLower i
          (isingTorusSiteReflect i x.1) := by
        intro hl
        have hval := hl.2
        have hxi0 : x.1 i ≠ 0 :=
          (ZMod.val_ne_zero (x.1 i)).mp (ne_of_gt x.2.1)
        rw [isingTorusSiteReflect_apply_same, ZMod.neg_val,
          if_neg hxi0] at hval
        have hxlt := (x.1 i).val_lt
        have hxhalf := x.2.2
        have hside := isingTorus_side_eq_two_half (k := k)
        omega
      simp [isingTorusSiteSplit, isingTorusSiteGlue, hnpR, hlR]

@[simp] theorem isingTorusSiteGlue_split
    (i : Fin d) (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    isingTorusSiteGlue i (isingTorusSiteSplit i sigma).1
      (isingTorusSiteSplit i sigma).2.1
      (isingTorusSiteSplit i sigma).2.2 = sigma := by
  funext x
  by_cases hp : isingTorusOnSitePlane i x
  · simp [isingTorusSiteGlue, isingTorusSiteSplit, hp]
  · by_cases hl : isingTorusInStrictLower i x
    · simp [isingTorusSiteGlue, isingTorusSiteSplit, hp, hl]
    · simp [isingTorusSiteGlue, isingTorusSiteSplit, hp, hl]


def isingTorusSiteSplitEquiv (i : Fin d) :
    (ConfigSpace (IsingTorusSitePlane (k := k) i) ×
      (ConfigSpace (IsingTorusStrictLower (k := k) i) ×
        ConfigSpace (IsingTorusStrictLower (k := k) i))) ≃
      ConfigSpace (IsingDyadicTorus d k) where
  toFun p := isingTorusSiteGlue i p.1 p.2.1 p.2.2
  invFun := isingTorusSiteSplit i
  left_inv p := by rcases p with ⟨boundary, lower, upper⟩; simp
  right_inv := isingTorusSiteGlue_split i



theorem isingTorusSiteReflect_add_step_same
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusSiteReflect i (x + isingTorusStep i) =
      isingTorusSiteReflect i x - isingTorusStep i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [isingTorusSiteReflect_apply_same,
      isingTorusStep_apply_same]
    ring
  · simp [isingTorusSiteReflect_apply_of_ne i j hji,
      isingTorusStep_apply_of_ne i j hji]

theorem isingTorusSiteReflect_add_step_of_ne
    (i j : Fin d) (hji : j ≠ i) (x : IsingDyadicTorus d k) :
    isingTorusSiteReflect i (x + isingTorusStep j) =
      isingTorusSiteReflect i x + isingTorusStep j := by
  funext l
  by_cases hli : l = i
  · subst l
    have hij : i ≠ j := Ne.symm hji
    simp [isingTorusSiteReflect_apply_same,
      isingTorusStep_apply_of_ne j i hij]
  · simp [isingTorusSiteReflect_apply_of_ne i l hli]

def isingTorusSiteReflectField (i : Fin d)
    (u : IsingDyadicTorus d k → Real) : IsingDyadicTorus d k → Real :=
  fun x => u (isingTorusSiteReflect i x)

theorem isingTorusDirichlet_siteReflectField
    (i : Fin d) (u : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet (isingTorusSiteReflectField i u) =
      isingTorusDirichlet u := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  calc
    (∑ x : IsingDyadicTorus d k, ∑ j : Fin d,
        (isingTorusSiteReflectField i u x -
          isingTorusSiteReflectField i u (x + isingTorusStep j)) *
        (isingTorusSiteReflectField i u x -
          isingTorusSiteReflectField i u (x + isingTorusStep j))) =
      ∑ j : Fin d, ∑ x : IsingDyadicTorus d k,
        (isingTorusSiteReflectField i u x -
          isingTorusSiteReflectField i u (x + isingTorusStep j)) *
        (isingTorusSiteReflectField i u x -
          isingTorusSiteReflectField i u (x + isingTorusStep j)) :=
        Finset.sum_comm
    _ = ∑ j : Fin d, ∑ x : IsingDyadicTorus d k,
        (u x - u (x + isingTorusStep j)) *
          (u x - u (x + isingTorusStep j)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        let e : IsingDyadicTorus d k → IsingDyadicTorus d k := fun x =>
          isingTorusSiteReflect i x - isingTorusStep i
        have hinv : Function.Involutive
            (isingTorusSiteReflect (k := k) i) :=
          fun x => isingTorusSiteReflect_involutive i x
        have hreflect : Function.Bijective
            (isingTorusSiteReflect (k := k) i) := hinv.bijective
        have he : Function.Bijective e :=
          (Equiv.subRight (isingTorusStep (k := k) i)).bijective.comp
            hreflect
        calc
          (∑ x,
              (isingTorusSiteReflectField i u x -
                isingTorusSiteReflectField i u (x + isingTorusStep i)) *
              (isingTorusSiteReflectField i u x -
                isingTorusSiteReflectField i u (x + isingTorusStep i))) =
            ∑ x, (u (e x + isingTorusStep i) - u (e x)) *
              (u (e x + isingTorusStep i) - u (e x)) := by
                apply Finset.sum_congr rfl
                intro x _
                dsimp only [e, isingTorusSiteReflectField]
                rw [isingTorusSiteReflect_add_step_same]
                ring
          _ = ∑ x, (u (x + isingTorusStep i) - u x) *
              (u (x + isingTorusStep i) - u x) :=
            he.sum_comp (fun y : IsingDyadicTorus d k =>
              (u (y + isingTorusStep i) - u y) *
                (u (y + isingTorusStep i) - u y))
          _ = ∑ x, (u x - u (x + isingTorusStep i)) *
              (u x - u (x + isingTorusStep i)) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
      · have hinv : Function.Involutive
            (isingTorusSiteReflect (k := k) i) :=
          fun x => isingTorusSiteReflect_involutive i x
        have hreflect : Function.Bijective
            (isingTorusSiteReflect (k := k) i) := hinv.bijective
        calc
          (∑ x,
              (isingTorusSiteReflectField i u x -
                isingTorusSiteReflectField i u (x + isingTorusStep j)) *
              (isingTorusSiteReflectField i u x -
                isingTorusSiteReflectField i u (x + isingTorusStep j))) =
            ∑ x, (u (isingTorusSiteReflect i x) -
              u (isingTorusSiteReflect i x + isingTorusStep j)) *
              (u (isingTorusSiteReflect i x) -
                u (isingTorusSiteReflect i x + isingTorusStep j)) := by
                apply Finset.sum_congr rfl
                intro x _
                dsimp only [isingTorusSiteReflectField]
                rw [isingTorusSiteReflect_add_step_of_ne i j hji]
          _ = ∑ x, (u x - u (x + isingTorusStep j)) *
              (u x - u (x + isingTorusStep j)) :=
            hreflect.sum_comp (fun y : IsingDyadicTorus d k =>
              (u y - u (y + isingTorusStep j)) *
                (u y - u (y + isingTorusStep j)))
    _ = ∑ x : IsingDyadicTorus d k, ∑ j : Fin d,
        (u x - u (x + isingTorusStep j)) *
          (u x - u (x + isingTorusStep j)) := Finset.sum_comm

theorem isingTorusDirichletBilinear_siteReflectField
    (i : Fin d) (u v : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear
        (isingTorusSiteReflectField i u)
        (isingTorusSiteReflectField i v) =
      isingTorusDirichletBilinear u v := by
  have hadd := isingTorusDirichlet_add u v
  have haddR := isingTorusDirichlet_add
    (isingTorusSiteReflectField i u) (isingTorusSiteReflectField i v)
  have hrefAdd : isingTorusSiteReflectField i (u + v) =
      isingTorusSiteReflectField i u +
        isingTorusSiteReflectField i v := rfl
  rw [← hrefAdd,
    isingTorusDirichlet_siteReflectField,
    isingTorusDirichlet_siteReflectField,
    isingTorusDirichlet_siteReflectField] at haddR
  linarith



theorem isingTorusSiteReflect_strictLower_iff_upper
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusInStrictLower i (isingTorusSiteReflect i x) ↔
      2 ^ (k + 1) < (x i).val := by
  unfold isingTorusInStrictLower
  rw [isingTorusSiteReflect_apply_same]
  by_cases hx0 : x i = 0
  · simp [hx0]
  · rw [ZMod.neg_val, if_neg hx0]
    have hxlt := (x i).val_lt
    have hside := isingTorus_side_eq_two_half (k := k)
    constructor <;> intro h <;> omega

private theorem isingTorus_no_edge_meets_both_strict_halves
    (i j : Fin d) (x : IsingDyadicTorus d k) :
    ¬ ((isingTorusInStrictLower i x ∨
          isingTorusInStrictLower i (x + isingTorusStep j)) ∧
        (isingTorusInStrictLower i (isingTorusSiteReflect i x) ∨
          isingTorusInStrictLower i
            (isingTorusSiteReflect i (x + isingTorusStep j)))) := by
  rw [isingTorusSiteReflect_strictLower_iff_upper,
    isingTorusSiteReflect_strictLower_iff_upper]
  simp only [isingTorusInStrictLower]
  by_cases hji : j = i
  · subst j
    have hone : (1 : ZMod (2 ^ (k + 2))).val = 1 := by
      have hlt : 1 < 2 ^ (k + 2) := by
        have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside := isingTorus_side_eq_two_half (k := k)
        omega
      letI : Fact (1 < 2 ^ (k + 2)) := ⟨hlt⟩
      exact ZMod.val_one (2 ^ (k + 2))
    have hycoord : (x + isingTorusStep (k := k) i) i = x i + 1 := by
      simp [Pi.add_apply, isingTorusStep_apply_same]
    rw [hycoord]
    by_cases hsum : (x i).val + (1 : ZMod (2 ^ (k + 2))).val <
        2 ^ (k + 2)
    · rw [ZMod.val_add_of_lt hsum, hone]
      rintro ⟨hl, hu⟩
      rcases hl with hl | hl <;> rcases hu with hu | hu <;>
        omega
    · have hle : 2 ^ (k + 2) ≤
          (x i).val + (1 : ZMod (2 ^ (k + 2))).val := by omega
      rw [ZMod.val_add_of_le hle, hone]
      have hxlt := (x i).val_lt
      rintro ⟨hl, hu⟩
      rcases hl with hl | hl <;> rcases hu with hu | hu <;>
        omega
  · have hcoord : (x + isingTorusStep (k := k) j) i = x i := by
      rw [Pi.add_apply, isingTorusStep_apply_of_ne j i (Ne.symm hji),
        add_zero]
    rw [hcoord]
    rintro ⟨hl, hu⟩
    rcases hl with hl | hl <;> omega

def isingTorusSitePlaneField (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i)) :
    IsingDyadicTorus d k → Real :=
  fun x => if hp : isingTorusOnSitePlane i x
    then spin boundary ⟨x, hp⟩ else 0

def isingTorusStrictLowerField (i : Fin d)
    (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    IsingDyadicTorus d k → Real :=
  fun x => if hl : isingTorusInStrictLower i x
    then spin lower ⟨x, hl⟩ else 0

def isingTorusStrictUpperField (i : Fin d)
    (upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    IsingDyadicTorus d k → Real :=
  isingTorusSiteReflectField i (isingTorusStrictLowerField i upper)

theorem isingTorusStrictLowerField_reflect
    (i : Fin d)
    (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusSiteReflectField i (isingTorusStrictLowerField i lower) =
      isingTorusStrictUpperField i lower := rfl

theorem isingTorusSitePlaneField_reflect
    (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i)) :
    isingTorusSiteReflectField i (isingTorusSitePlaneField i boundary) =
      isingTorusSitePlaneField i boundary := by
  funext x
  unfold isingTorusSiteReflectField isingTorusSitePlaneField
  by_cases hp : isingTorusOnSitePlane i x
  · have href := isingTorusSiteReflect_fixed i hp
    simp [href, hp]
  · have hpR := isingTorusSiteReflect_not_plane i hp
    simp [hp, hpR]

theorem isingTorusStrictLower_upper_cross_zero
    (i : Fin d)
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusDirichletBilinear
        (isingTorusStrictLowerField i lower)
        (isingTorusStrictUpperField i upper) = 0 := by
  unfold isingTorusDirichletBilinear
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro j _
  have hsep := isingTorus_no_edge_meets_both_strict_halves i j x
  push Not at hsep
  by_cases hL : isingTorusInStrictLower i x ∨
      isingTorusInStrictLower i (x + isingTorusStep j)
  · have hU := hsep hL
    rcases hU with ⟨hxU, hyU⟩
    simp [isingTorusStrictUpperField, isingTorusSiteReflectField,
      isingTorusStrictLowerField, hxU, hyU]
  · push Not at hL
    rcases hL with ⟨hxL, hyL⟩
    simp [isingTorusStrictLowerField, hxL, hyL]

theorem isingTorusSpinSiteGlue_eq_fields
    (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusSpinField (isingTorusSiteGlue i boundary lower upper) =
      isingTorusSitePlaneField i boundary +
        isingTorusStrictLowerField i lower +
          isingTorusStrictUpperField i upper := by
  funext x
  change spin (isingTorusSiteGlue i boundary lower upper) x = _
  by_cases hp : isingTorusOnSitePlane i x
  · have href := isingTorusSiteReflect_fixed i hp
    have hnl : ¬ isingTorusInStrictLower i x := by
      unfold isingTorusOnSitePlane at hp
      unfold isingTorusInStrictLower
      rcases hp with hp | hp <;> omega
    have hspin : spin (isingTorusSiteGlue i boundary lower upper) x =
        spin boundary ⟨x, hp⟩ := by
      unfold spin
      simp [isingTorusSiteGlue, hp]
    rw [hspin]
    simp [isingTorusSpinField, isingTorusSiteGlue,
      isingTorusSitePlaneField, isingTorusStrictLowerField,
      isingTorusStrictUpperField, isingTorusSiteReflectField,
      hp, hnl, href]
  · by_cases hl : isingTorusInStrictLower i x
    · have hrl : ¬ isingTorusInStrictLower i
          (isingTorusSiteReflect i x) := by
        rw [isingTorusSiteReflect_strictLower_iff_upper]
        exact (not_lt_of_ge hl.2.le)
      have hspin : spin (isingTorusSiteGlue i boundary lower upper) x =
          spin lower ⟨x, hl⟩ := by
        unfold spin
        simp [isingTorusSiteGlue, hp, hl]
      rw [hspin]
      simp [isingTorusSpinField, isingTorusSiteGlue,
        isingTorusSitePlaneField, isingTorusStrictLowerField,
        isingTorusStrictUpperField, isingTorusSiteReflectField,
        hp, hl, hrl]
    · have hrl := isingTorusSiteReflect_strictLower_of_upper i hp hl
      have hspin : spin (isingTorusSiteGlue i boundary lower upper) x =
          spin upper ⟨isingTorusSiteReflect i x, hrl⟩ := by
        unfold spin
        simp [isingTorusSiteGlue, hp, hl]
      rw [hspin]
      simp [isingTorusSpinField, isingTorusSiteGlue,
        isingTorusSitePlaneField, isingTorusStrictLowerField,
        isingTorusStrictUpperField, isingTorusSiteReflectField,
        hp, hl, hrl]

theorem isingTorusStrictUpper_dirichlet
    (i : Fin d)
    (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusDirichlet (isingTorusStrictUpperField i lower) =
      isingTorusDirichlet (isingTorusStrictLowerField i lower) := by
  rw [← isingTorusStrictLowerField_reflect,
    isingTorusDirichlet_siteReflectField]

theorem isingTorusSitePlane_upper_bilinear
    (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusDirichletBilinear
        (isingTorusSitePlaneField i boundary)
        (isingTorusStrictUpperField i lower) =
      isingTorusDirichletBilinear
        (isingTorusSitePlaneField i boundary)
        (isingTorusStrictLowerField i lower) := by
  have h := isingTorusDirichletBilinear_siteReflectField i
    (isingTorusSitePlaneField i boundary)
    (isingTorusStrictLowerField i lower)
  rw [isingTorusSitePlaneField_reflect,
    isingTorusStrictLowerField_reflect] at h
  exact h

theorem isingTorusSiteGlue_dirichlet_midpoint
    (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    2 * isingTorusDirichlet
        (isingTorusSpinField (isingTorusSiteGlue i boundary lower upper)) =
      isingTorusDirichlet
          (isingTorusSpinField (isingTorusSiteGlue i boundary lower lower)) +
        isingTorusDirichlet
          (isingTorusSpinField (isingTorusSiteGlue i boundary upper upper)) := by
  let B := isingTorusSitePlaneField i boundary
  let L := fun sigma : ConfigSpace (IsingTorusStrictLower (k := k) i) =>
    isingTorusStrictLowerField i sigma
  let U := fun sigma : ConfigSpace (IsingTorusStrictLower (k := k) i) =>
    isingTorusStrictUpperField i sigma
  rw [isingTorusSpinSiteGlue_eq_fields,
    isingTorusSpinSiteGlue_eq_fields,
    isingTorusSpinSiteGlue_eq_fields]
  change 2 * isingTorusDirichlet (B + L lower + U upper) =
    isingTorusDirichlet (B + L lower + U lower) +
      isingTorusDirichlet (B + L upper + U upper)
  rw [isingTorusDirichlet_add (B + L lower) (U upper),
    isingTorusDirichlet_add B (L lower),
    isingTorusDirichlet_add (B + L lower) (U lower),
    isingTorusDirichlet_add B (L lower),
    isingTorusDirichlet_add (B + L upper) (U upper),
    isingTorusDirichlet_add B (L upper)]
  rw [isingTorusDirichletBilinear_add_left B (L lower) (U upper),
    isingTorusDirichletBilinear_add_left B (L lower) (U lower),
    isingTorusDirichletBilinear_add_left B (L upper) (U upper)]
  have hcrossLU := isingTorusStrictLower_upper_cross_zero i lower upper
  have hcrossLL := isingTorusStrictLower_upper_cross_zero i lower lower
  have hcrossUU := isingTorusStrictLower_upper_cross_zero i upper upper
  have hDUl := isingTorusStrictUpper_dirichlet i lower
  have hDUu := isingTorusStrictUpper_dirichlet i upper
  have hBUl := isingTorusSitePlane_upper_bilinear i boundary lower
  have hBUu := isingTorusSitePlane_upper_bilinear i boundary upper
  change isingTorusDirichletBilinear (L lower) (U upper) = 0 at hcrossLU
  change isingTorusDirichletBilinear (L lower) (U lower) = 0 at hcrossLL
  change isingTorusDirichletBilinear (L upper) (U upper) = 0 at hcrossUU
  change isingTorusDirichlet (U lower) = isingTorusDirichlet (L lower) at hDUl
  change isingTorusDirichlet (U upper) = isingTorusDirichlet (L upper) at hDUu
  change isingTorusDirichletBilinear B (U lower) =
    isingTorusDirichletBilinear B (L lower) at hBUl
  change isingTorusDirichletBilinear B (U upper) =
    isingTorusDirichletBilinear B (L upper) at hBUu
  rw [hcrossLU, hcrossLL, hcrossUU, hDUl, hDUu, hBUl, hBUu]
  ring

noncomputable def isingTorusSiteHalfWeight
    (i : Fin d) (beta : Real)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) : Real :=
  Real.exp (-(beta / 4) * isingTorusDirichlet
    (isingTorusSpinField (isingTorusSiteGlue i boundary lower lower)))

theorem isingTorusSiteWeight_factor
    (i : Fin d) (beta : Real)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    Real.exp (-(beta / 2) * isingTorusDirichlet
        (isingTorusSpinField (isingTorusSiteGlue i boundary lower upper))) =
      isingTorusSiteHalfWeight i beta boundary lower *
        isingTorusSiteHalfWeight i beta boundary upper := by
  unfold isingTorusSiteHalfWeight
  rw [← Real.exp_add]
  congr 1
  have h := isingTorusSiteGlue_dirichlet_midpoint
    i boundary lower upper
  calc
    -(beta / 2) * isingTorusDirichlet
        (isingTorusSpinField
          (isingTorusSiteGlue i boundary lower upper)) =
      -(beta / 4) * (2 * isingTorusDirichlet
        (isingTorusSpinField
          (isingTorusSiteGlue i boundary lower upper))) := by ring
    _ = -(beta / 4) *
        (isingTorusDirichlet
            (isingTorusSpinField
              (isingTorusSiteGlue i boundary lower lower)) +
          isingTorusDirichlet
            (isingTorusSpinField
              (isingTorusSiteGlue i boundary upper upper))) := by rw [h]
    _ = -(beta / 4) * isingTorusDirichlet
          (isingTorusSpinField
            (isingTorusSiteGlue i boundary lower lower)) +
        -(beta / 4) * isingTorusDirichlet
          (isingTorusSpinField
            (isingTorusSiteGlue i boundary upper upper)) := by ring



noncomputable def isingTorusSiteBoundaryAmplitude
    (i : Fin d) (beta : Real)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (F : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) : Real :=
  ∑ lower : ConfigSpace (IsingTorusStrictLower (k := k) i),
    isingTorusSiteHalfWeight i beta boundary lower * F lower

noncomputable def isingTorusSiteReflectionForm
    (i : Fin d) (beta : Real)
    (F G : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) : Real :=
  ∑ boundary : ConfigSpace (IsingTorusSitePlane (k := k) i),
    ∑ lower : ConfigSpace (IsingTorusStrictLower (k := k) i),
      ∑ upper : ConfigSpace (IsingTorusStrictLower (k := k) i),
        (isingTorusSiteHalfWeight i beta boundary lower * F lower) *
          (isingTorusSiteHalfWeight i beta boundary upper * G upper)

theorem isingTorusSiteReflectionForm_eq_amplitudes
    (i : Fin d) (beta : Real)
    (F G : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) :
    isingTorusSiteReflectionForm i beta F G =
      ∑ boundary : ConfigSpace (IsingTorusSitePlane (k := k) i),
        isingTorusSiteBoundaryAmplitude i beta boundary F *
          isingTorusSiteBoundaryAmplitude i beta boundary G := by
  unfold isingTorusSiteReflectionForm isingTorusSiteBoundaryAmplitude
  apply Finset.sum_congr rfl
  intro boundary _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro lower _
  rw [Finset.mul_sum]

theorem isingTorusSiteReflectionForm_nonneg
    (i : Fin d) (beta : Real)
    (F : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) :
    0 ≤ isingTorusSiteReflectionForm i beta F F := by
  rw [isingTorusSiteReflectionForm_eq_amplitudes]
  exact Finset.sum_nonneg fun boundary _ =>
    mul_self_nonneg (isingTorusSiteBoundaryAmplitude i beta boundary F)

theorem isingTorusSiteReflectionForm_cauchy
    (i : Fin d) (beta : Real)
    (F G : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) :
    isingTorusSiteReflectionForm i beta F G ^ 2 ≤
      isingTorusSiteReflectionForm i beta F F *
        isingTorusSiteReflectionForm i beta G G := by
  simp_rw [isingTorusSiteReflectionForm_eq_amplitudes]
  simpa only [pow_two] using sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun boundary : ConfigSpace (IsingTorusSitePlane (k := k) i) =>
      isingTorusSiteBoundaryAmplitude i beta boundary F)
    (fun boundary : ConfigSpace (IsingTorusSitePlane (k := k) i) =>
      isingTorusSiteBoundaryAmplitude i beta boundary G)

def isingTorusStrictHalfSpin (x : IsingTorusStrictLower (k := k) i)
    (sigma : ConfigSpace (IsingTorusStrictLower (k := k) i)) : Real :=
  spin sigma x

theorem isingTorusSiteReflectionForm_spin_eq
    (i : Fin d) (beta : Real)
    (x y : IsingTorusStrictLower (k := k) i) :
    isingTorusSiteReflectionForm i beta
        (isingTorusStrictHalfSpin x) (isingTorusStrictHalfSpin y) =
      ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
        Real.exp (-(beta / 2) *
          isingTorusDirichlet (isingTorusSpinField sigma)) *
          isingTorusSpinField sigma x.1 *
          isingTorusSpinField sigma (isingTorusSiteReflect i y.1) := by
  rw [← (isingTorusSiteSplitEquiv (k := k) i).bijective.sum_comp
    (fun sigma : ConfigSpace (IsingDyadicTorus d k) =>
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma)) *
        isingTorusSpinField sigma x.1 *
        isingTorusSpinField sigma (isingTorusSiteReflect i y.1))]
  simp only [Fintype.sum_prod_type]
  unfold isingTorusSiteReflectionForm
  apply Finset.sum_congr rfl
  intro boundary _
  apply Finset.sum_congr rfl
  intro lower _
  apply Finset.sum_congr rfl
  intro upper _
  have hequiv : (isingTorusSiteSplitEquiv (k := k) i)
      (boundary, (lower, upper)) =
        isingTorusSiteGlue i boundary lower upper := rfl
  rw [hequiv, isingTorusSiteWeight_factor]
  have hnp : ¬ isingTorusOnSitePlane i x.1 := by
    intro hp
    unfold isingTorusOnSitePlane at hp
    have hx := x.2
    unfold isingTorusInStrictLower at hx
    rcases hp with hp | hp <;> omega
  have hnpY : ¬ isingTorusOnSitePlane i y.1 := by
    intro hp
    unfold isingTorusOnSitePlane at hp
    have hy := y.2
    unfold isingTorusInStrictLower at hy
    rcases hp with hp | hp <;> omega
  have hnpRY := isingTorusSiteReflect_not_plane i hnpY
  have hnotRY : ¬ isingTorusInStrictLower i
      (isingTorusSiteReflect i y.1) := by
    rw [isingTorusSiteReflect_strictLower_iff_upper]
    exact not_lt_of_ge y.2.2.le
  have hgluex : isingTorusSiteGlue i boundary lower upper x.1 =
      lower x := by
    simp [isingTorusSiteGlue, hnp, x.2]
  have hgluey : isingTorusSiteGlue i boundary lower upper
      (isingTorusSiteReflect i y.1) = upper y := by
    simp [isingTorusSiteGlue, hnpRY, hnotRY]
  have hspinx : spin (isingTorusSiteGlue i boundary lower upper) x.1 =
      spin lower x := by
    unfold spin
    rw [hgluex]
  have hspiny : spin (isingTorusSiteGlue i boundary lower upper)
      (isingTorusSiteReflect i y.1) = spin upper y := by
    unfold spin
    rw [hgluey]
  simp only [isingTorusSpinField, isingTorusStrictHalfSpin]
  rw [hspinx, hspiny]
  ring

theorem isingTorusTwoPoint_siteReflection_cauchy
    (i : Fin d) (beta : Real)
    (x y : IsingTorusStrictLower (k := k) i) :
    isingTorusTwoPoint beta x.1 (isingTorusSiteReflect i y.1) ^ 2 ≤
      isingTorusTwoPoint beta x.1 (isingTorusSiteReflect i x.1) *
        isingTorusTwoPoint beta y.1 (isingTorusSiteReflect i y.1) := by
  have h := isingTorusSiteReflectionForm_cauchy i beta
    (isingTorusStrictHalfSpin x) (isingTorusStrictHalfSpin y)
  rw [isingTorusSiteReflectionForm_spin_eq,
    isingTorusSiteReflectionForm_spin_eq,
    isingTorusSiteReflectionForm_spin_eq] at h
  unfold isingTorusTwoPoint
  rw [div_pow, div_mul_div_comm]
  simpa only [pow_two] using div_le_div_of_nonneg_right h
    (sq_nonneg (isingTorusShiftedPartition (d := d) (k := k) beta 0))

theorem isingTorusSiteReflect_coordinateShift
    (i : Fin d) (n : Nat) :
    isingTorusSiteReflect i (isingTorusCoordinateShift (k := k) i n) =
      -isingTorusCoordinateShift i n := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [isingTorusSiteReflect_apply_same,
      isingTorusCoordinateShift_apply_same]
  · simp [isingTorusSiteReflect_apply_of_ne i j hji,
      isingTorusCoordinateShift_apply_of_ne i j hji]



theorem isingTorusTwoPoint_axis_site_midpoint_sq_le
    (i : Fin d) (beta : Real)
    (a b : Nat) (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a < 2 ^ (k + 1)) (hb : b < 2 ^ (k + 1)) :
    isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i (a + b)) ^ 2 ≤
      isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * a)) *
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * b)) := by
  let x : IsingTorusStrictLower (k := k) i :=
    ⟨isingTorusCoordinateShift i a, by
      unfold isingTorusInStrictLower
      rw [isingTorusCoordinateShift_apply_same,
        ZMod.val_natCast_of_lt]
      · exact ⟨ha0, ha⟩
      · have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside := isingTorus_side_eq_two_half (k := k)
        omega⟩
  let y : IsingTorusStrictLower (k := k) i :=
    ⟨isingTorusCoordinateShift i b, by
      unfold isingTorusInStrictLower
      rw [isingTorusCoordinateShift_apply_same,
        ZMod.val_natCast_of_lt]
      · exact ⟨hb0, hb⟩
      · have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside := isingTorus_side_eq_two_half (k := k)
        omega⟩
  have h := isingTorusTwoPoint_siteReflection_cauchy i beta x y
  have hxy : isingTorusSiteReflect i y.1 - x.1 =
      -isingTorusCoordinateShift i (a + b) := by
    dsimp only [x, y]
    rw [isingTorusSiteReflect_coordinateShift,
      isingTorusCoordinateShift_add]
    abel
  have hxx : isingTorusSiteReflect i x.1 - x.1 =
      -isingTorusCoordinateShift i (2 * a) := by
    dsimp only [x]
    rw [isingTorusSiteReflect_coordinateShift]
    have hs := isingTorusCoordinateShift_add (k := k) i a a
    rw [show a + a = 2 * a by omega] at hs
    rw [hs]
    abel
  have hyy : isingTorusSiteReflect i y.1 - y.1 =
      -isingTorusCoordinateShift i (2 * b) := by
    dsimp only [y]
    rw [isingTorusSiteReflect_coordinateShift]
    have hs := isingTorusCoordinateShift_add (k := k) i b b
    rw [show b + b = 2 * b by omega] at hs
    rw [hs]
    abel
  have hcxy : isingTorusTwoPoint beta x.1
      (isingTorusSiteReflect i y.1) =
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (a + b)) := by
    rw [isingTorusTwoPoint_eq_origin_displacement, hxy,
      isingTorusTwoPoint_origin_neg]
  have hcxx : isingTorusTwoPoint beta x.1
      (isingTorusSiteReflect i x.1) =
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * a)) := by
    rw [isingTorusTwoPoint_eq_origin_displacement, hxx,
      isingTorusTwoPoint_origin_neg]
  have hcyy : isingTorusTwoPoint beta y.1
      (isingTorusSiteReflect i y.1) =
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i (2 * b)) := by
    rw [isingTorusTwoPoint_eq_origin_displacement, hyy,
      isingTorusTwoPoint_origin_neg]
  calc
    isingTorusTwoPoint beta 0
          (isingTorusCoordinateShift i (a + b)) ^ 2 =
        isingTorusTwoPoint beta x.1
          (isingTorusSiteReflect i y.1) ^ 2 := by rw [hcxy]
    _ ≤ isingTorusTwoPoint beta x.1
          (isingTorusSiteReflect i x.1) *
        isingTorusTwoPoint beta y.1
          (isingTorusSiteReflect i y.1) := h
    _ = isingTorusTwoPoint beta 0
          (isingTorusCoordinateShift i (2 * a)) *
        isingTorusTwoPoint beta 0
          (isingTorusCoordinateShift i (2 * b)) := by
      rw [hcxx, hcyy]

end StatMech.FrontierA
