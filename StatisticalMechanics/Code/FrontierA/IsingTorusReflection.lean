/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusGaussianDomination

open Finset
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

private theorem isingTorus_side_eq_two_mul_half :
    2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring



def isingTorusReflectCoord (z : ZMod (2 ^ (k + 2))) :
    ZMod (2 ^ (k + 2)) :=
  ((2 ^ (k + 2) - 1 - z.val : Nat) : ZMod (2 ^ (k + 2)))

@[simp] theorem isingTorusReflectCoord_val
    (z : ZMod (2 ^ (k + 2))) :
    (isingTorusReflectCoord z).val = 2 ^ (k + 2) - 1 - z.val := by
  unfold isingTorusReflectCoord
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hz := z.val_lt
  have hpos : 0 < 2 ^ (k + 2) := pow_pos (by omega) _
  omega

@[simp] theorem isingTorusReflectCoord_involutive
    (z : ZMod (2 ^ (k + 2))) :
    isingTorusReflectCoord (isingTorusReflectCoord z) = z := by
  apply ZMod.val_injective
  rw [isingTorusReflectCoord_val, isingTorusReflectCoord_val]
  have hz := z.val_lt
  have hpos : 0 < 2 ^ (k + 2) := pow_pos (by omega) _
  omega

theorem isingTorusReflectCoord_eq_neg_sub_one
    (z : ZMod (2 ^ (k + 2))) :
    isingTorusReflectCoord z = -z - 1 := by
  have hpos : 0 < 2 ^ (k + 2) := pow_pos (by omega) _
  have hz := z.val_lt
  have hnat : 2 ^ (k + 2) - 1 - z.val + z.val + 1 =
      2 ^ (k + 2) := by omega
  have hsum : isingTorusReflectCoord z + z + 1 = 0 := by
    rw [show isingTorusReflectCoord z + z + 1 =
      ((2 ^ (k + 2) - 1 - z.val : Nat) : ZMod (2 ^ (k + 2))) +
        (z.val : ZMod (2 ^ (k + 2))) + 1 by
      rw [ZMod.natCast_zmod_val]
      rfl]
    rw [← Nat.cast_add]
    have hone : (1 : ZMod (2 ^ (k + 2))) =
        ((1 : Nat) : ZMod (2 ^ (k + 2))) := by norm_num
    rw [hone, ← Nat.cast_add, hnat, ZMod.natCast_self]
  calc
    isingTorusReflectCoord z =
        (isingTorusReflectCoord z + z + 1) - z - 1 := by ring
    _ = 0 - z - 1 := by rw [hsum]
    _ = -z - 1 := by ring

theorem isingTorusReflectCoord_add_one
    (z : ZMod (2 ^ (k + 2))) :
    isingTorusReflectCoord (z + 1) = isingTorusReflectCoord z - 1 := by
  rw [isingTorusReflectCoord_eq_neg_sub_one,
    isingTorusReflectCoord_eq_neg_sub_one]
  ring

theorem isingTorusReflectCoord_sub_one
    (z : ZMod (2 ^ (k + 2))) :
    isingTorusReflectCoord (z - 1) = isingTorusReflectCoord z + 1 := by
  rw [isingTorusReflectCoord_eq_neg_sub_one,
    isingTorusReflectCoord_eq_neg_sub_one]
  ring


def isingTorusReflectSite (i : Fin d) (x : IsingDyadicTorus d k) :
    IsingDyadicTorus d k :=
  Function.update x i (isingTorusReflectCoord (x i))

@[simp] theorem isingTorusReflectSite_apply_same
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusReflectSite i x i = isingTorusReflectCoord (x i) := by
  simp [isingTorusReflectSite]

theorem isingTorusReflectSite_apply_of_ne
    (i j : Fin d) (hji : j ≠ i) (x : IsingDyadicTorus d k) :
    isingTorusReflectSite i x j = x j := by
  simp [isingTorusReflectSite, hji]


def isingTorusInLowerHalf (i : Fin d) (x : IsingDyadicTorus d k) : Prop :=
  (x i).val < 2 ^ (k + 1)

instance (i : Fin d) (x : IsingDyadicTorus d k) :
    Decidable (isingTorusInLowerHalf i x) :=
  Nat.decLt _ _

theorem isingTorusStep_apply_same (i : Fin d) :
    isingTorusStep (k := k) i i = 1 := by
  simp [isingTorusStep]

theorem isingTorusStep_apply_of_ne (i j : Fin d) (hji : j ≠ i) :
    isingTorusStep (k := k) i j = 0 := by
  simp [isingTorusStep, hji]

theorem isingTorusReflectSite_add_step_same
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusReflectSite i (x + isingTorusStep i) =
      isingTorusReflectSite i x - isingTorusStep i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [isingTorusReflectSite_apply_same, isingTorusStep_apply_same,
      isingTorusReflectCoord_add_one]
  · simp [isingTorusReflectSite_apply_of_ne i j hji,
      isingTorusStep_apply_of_ne i j hji]

theorem isingTorusReflectSite_add_step_of_ne
    (i j : Fin d) (hji : j ≠ i) (x : IsingDyadicTorus d k) :
    isingTorusReflectSite i (x + isingTorusStep j) =
      isingTorusReflectSite i x + isingTorusStep j := by
  funext l
  by_cases hli : l = i
  · subst l
    have hij : i ≠ j := Ne.symm hji
    simp [isingTorusReflectSite_apply_same,
      isingTorusStep_apply_of_ne j i hij]
  · simp [isingTorusReflectSite_apply_of_ne i l hli]

theorem isingTorusReflectCoord_add_one_eq_of_lower_cross
    (z : ZMod (2 ^ (k + 2)))
    (hz : z.val < 2 ^ (k + 1))
    (hcross : ¬(z + 1).val < 2 ^ (k + 1)) :
    isingTorusReflectCoord (z + 1) = z := by
  apply ZMod.val_injective
  rw [isingTorusReflectCoord_val]
  have hzlt := z.val_lt
  have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
    isingTorus_side_eq_two_mul_half
  have hone : (1 : ZMod (2 ^ (k + 2))).val = 1 := by
    have hlt : 1 < 2 ^ (k + 2) := by
      rw [hside]
      have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
      omega
    letI : Fact (1 < 2 ^ (k + 2)) := ⟨hlt⟩
    exact ZMod.val_one (2 ^ (k + 2))
  have hsumlt : z.val + (1 : ZMod (2 ^ (k + 2))).val <
      2 ^ (k + 2) := by rw [hone]; omega
  rw [ZMod.val_add_of_lt hsumlt] at hcross ⊢
  rw [hone] at hcross ⊢
  omega

theorem isingTorusReflectCoord_eq_add_one_of_upper_cross
    (z : ZMod (2 ^ (k + 2)))
    (hz : ¬z.val < 2 ^ (k + 1))
    (hcross : (z + 1).val < 2 ^ (k + 1)) :
    isingTorusReflectCoord z = z + 1 := by
  apply ZMod.val_injective
  rw [isingTorusReflectCoord_val]
  have hzlt := z.val_lt
  have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
    isingTorus_side_eq_two_mul_half
  have hone : (1 : ZMod (2 ^ (k + 2))).val = 1 := by
    have hlt : 1 < 2 ^ (k + 2) := by
      rw [hside]
      have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
      omega
    letI : Fact (1 < 2 ^ (k + 2)) := ⟨hlt⟩
    exact ZMod.val_one (2 ^ (k + 2))
  by_cases hsumlt : z.val + (1 : ZMod (2 ^ (k + 2))).val <
      2 ^ (k + 2)
  · rw [ZMod.val_add_of_lt hsumlt] at hcross ⊢
    rw [hone] at hcross ⊢
    omega
  · have hle : 2 ^ (k + 2) ≤
        z.val + (1 : ZMod (2 ^ (k + 2))).val := by omega
    rw [ZMod.val_add_of_le hle]
    rw [hone] at hle ⊢
    omega

theorem isingTorus_crossing_reflects_endpoints
    (i j : Fin d) (x : IsingDyadicTorus d k) :
    (isingTorusInLowerHalf i x ∧
        ¬ isingTorusInLowerHalf i (x + isingTorusStep j) →
      isingTorusReflectSite i (x + isingTorusStep j) = x) ∧
    (¬ isingTorusInLowerHalf i x ∧
        isingTorusInLowerHalf i (x + isingTorusStep j) →
      isingTorusReflectSite i x = x + isingTorusStep j) := by
  constructor
  · rintro ⟨hx, hy⟩
    have hji : j = i := by
      by_contra hne
      apply hy
      unfold isingTorusInLowerHalf at hx ⊢
      rw [Pi.add_apply, isingTorusStep_apply_of_ne j i (Ne.symm hne)]
      simpa using hx
    subst j
    have hy' : ¬(x i + 1).val < 2 ^ (k + 1) := by
      unfold isingTorusInLowerHalf at hy
      simpa [Pi.add_apply, isingTorusStep_apply_same] using hy
    funext l
    by_cases hli : l = i
    · subst l
      rw [isingTorusReflectSite_apply_same, Pi.add_apply,
        isingTorusStep_apply_same]
      exact congrArg id
        (isingTorusReflectCoord_add_one_eq_of_lower_cross
          (x i) hx hy')
    · simp [isingTorusReflectSite_apply_of_ne i l hli,
        isingTorusStep_apply_of_ne i l hli]
  · rintro ⟨hx, hy⟩
    have hji : j = i := by
      by_contra hne
      apply hx
      unfold isingTorusInLowerHalf at hy ⊢
      rw [Pi.add_apply,
        isingTorusStep_apply_of_ne j i (Ne.symm hne)] at hy
      simpa using hy
    subst j
    have hy' : (x i + 1).val < 2 ^ (k + 1) := by
      unfold isingTorusInLowerHalf at hy
      simpa [Pi.add_apply, isingTorusStep_apply_same] using hy
    funext l
    by_cases hli : l = i
    · subst l
      rw [isingTorusReflectSite_apply_same, Pi.add_apply,
        isingTorusStep_apply_same]
      exact congrArg id
        (isingTorusReflectCoord_eq_add_one_of_upper_cross
          (x i) hx hy')
    · simp [isingTorusReflectSite_apply_of_ne i l hli,
        isingTorusStep_apply_of_ne i l hli]

@[simp] theorem isingTorusReflectSite_involutive
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusReflectSite i (isingTorusReflectSite i x) = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [isingTorusReflectSite_apply_of_ne i j hji]

theorem isingTorusReflectSite_not_lower_iff
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusInLowerHalf i (isingTorusReflectSite i x) ↔
      ¬ isingTorusInLowerHalf i x := by
  unfold isingTorusInLowerHalf
  rw [isingTorusReflectSite_apply_same, isingTorusReflectCoord_val]
  have hx := (x i).val_lt
  have hhpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
  have hside : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) :=
    isingTorus_side_eq_two_mul_half
  omega


def isingTorusPolarizeLower (i : Fin d)
    (h : IsingDyadicTorus d k → Real) : IsingDyadicTorus d k → Real :=
  fun x => if isingTorusInLowerHalf i x then h x
    else h (isingTorusReflectSite i x)


def isingTorusPolarizeUpper (i : Fin d)
    (h : IsingDyadicTorus d k → Real) : IsingDyadicTorus d k → Real :=
  fun x => if isingTorusInLowerHalf i x
    then h (isingTorusReflectSite i x) else h x

theorem isingTorusPolarizeLower_reflection_invariant
    (i : Fin d) (h : IsingDyadicTorus d k → Real) (x : IsingDyadicTorus d k) :
    isingTorusPolarizeLower i h (isingTorusReflectSite i x) =
      isingTorusPolarizeLower i h x := by
  unfold isingTorusPolarizeLower
  by_cases hx : isingTorusInLowerHalf i x
  · have hr : ¬ isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      fun hr => (isingTorusReflectSite_not_lower_iff i x).mp hr hx
    simp [hx, hr]
  · have hr : isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      (isingTorusReflectSite_not_lower_iff i x).mpr hx
    simp [hx, hr]

theorem isingTorusPolarizeUpper_reflection_invariant
    (i : Fin d) (h : IsingDyadicTorus d k → Real) (x : IsingDyadicTorus d k) :
    isingTorusPolarizeUpper i h (isingTorusReflectSite i x) =
      isingTorusPolarizeUpper i h x := by
  unfold isingTorusPolarizeUpper
  by_cases hx : isingTorusInLowerHalf i x
  · have hr : ¬ isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      fun hr => (isingTorusReflectSite_not_lower_iff i x).mp hr hx
    simp [hx, hr]
  · have hr : isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      (isingTorusReflectSite_not_lower_iff i x).mpr hx
    simp [hx, hr]



abbrev IsingTorusLowerSite (i : Fin d) :=
  {x : IsingDyadicTorus d k // isingTorusInLowerHalf i x}



def isingTorusGlueHalves (i : Fin d)
    (lower upper : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    ConfigSpace (IsingDyadicTorus d k) :=
  fun x => if hx : isingTorusInLowerHalf i x then lower ⟨x, hx⟩
    else upper ⟨isingTorusReflectSite i x,
      (isingTorusReflectSite_not_lower_iff i x).mpr hx⟩



def isingTorusSplitHalves (i : Fin d)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    ConfigSpace (IsingTorusLowerSite (k := k) i) ×
      ConfigSpace (IsingTorusLowerSite (k := k) i) :=
  (fun x => sigma x.1, fun x => sigma (isingTorusReflectSite i x.1))

@[simp] theorem isingTorusSplitHalves_glueHalves
    (i : Fin d)
    (lower upper : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusSplitHalves i (isingTorusGlueHalves i lower upper) =
      (lower, upper) := by
  apply Prod.ext
  · funext x
    simp [isingTorusSplitHalves, isingTorusGlueHalves, x.2]
  · funext x
    have hr : ¬ isingTorusInLowerHalf i
        (isingTorusReflectSite i x.1) :=
      fun h => (isingTorusReflectSite_not_lower_iff i x.1).mp h x.2
    simp [isingTorusSplitHalves, isingTorusGlueHalves, hr]

@[simp] theorem isingTorusGlueHalves_splitHalves
    (i : Fin d) (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    isingTorusGlueHalves i (isingTorusSplitHalves i sigma).1
      (isingTorusSplitHalves i sigma).2 = sigma := by
  funext x
  by_cases hx : isingTorusInLowerHalf i x
  · simp [isingTorusGlueHalves, isingTorusSplitHalves, hx]
  · simp [isingTorusGlueHalves, isingTorusSplitHalves, hx]


def isingTorusHalvesEquiv (i : Fin d) :
    (ConfigSpace (IsingTorusLowerSite (k := k) i) ×
      ConfigSpace (IsingTorusLowerSite (k := k) i)) ≃
        ConfigSpace (IsingDyadicTorus d k) where
  toFun p := isingTorusGlueHalves i p.1 p.2
  invFun := isingTorusSplitHalves i
  left_inv p := by rcases p with ⟨lower, upper⟩; simp
  right_inv sigma := isingTorusGlueHalves_splitHalves i sigma



def isingTorusEmbedLower (i : Fin d)
    (u : IsingTorusLowerSite (k := k) i → Real) :
    IsingDyadicTorus d k → Real :=
  fun x => if hx : isingTorusInLowerHalf i x then u ⟨x, hx⟩ else 0

def isingTorusEmbedUpper (i : Fin d)
    (u : IsingTorusLowerSite (k := k) i → Real) :
    IsingDyadicTorus d k → Real :=
  fun x => if hx : isingTorusInLowerHalf i x then 0
    else u ⟨isingTorusReflectSite i x,
      (isingTorusReflectSite_not_lower_iff i x).mpr hx⟩

def isingTorusLowerValues (i : Fin d)
    (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    IsingTorusLowerSite (k := k) i → Real :=
  fun x => spin sigma x + h x.1

def isingTorusUpperValues (i : Fin d)
    (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    IsingTorusLowerSite (k := k) i → Real :=
  fun x => spin sigma x + h (isingTorusReflectSite i x.1)

theorem isingTorusSpinGlue_add_field_eq_embeds
    (i : Fin d) (h : IsingDyadicTorus d k → Real)
    (lower upper : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusSpinField (isingTorusGlueHalves i lower upper) + h =
      isingTorusEmbedLower i (isingTorusLowerValues i h lower) +
        isingTorusEmbedUpper i (isingTorusUpperValues i h upper) := by
  funext x
  by_cases hx : isingTorusInLowerHalf i x
  · have hs : isingTorusGlueHalves i lower upper x = lower ⟨x, hx⟩ := by
      simp [isingTorusGlueHalves, hx]
    have hspin : spin (isingTorusGlueHalves i lower upper) x =
        spin lower ⟨x, hx⟩ := by
      unfold spin
      rw [hs]
    change spin (isingTorusGlueHalves i lower upper) x + h x = _
    rw [hspin]
    simp [isingTorusEmbedLower, isingTorusEmbedUpper,
      isingTorusLowerValues, hx]
  · have hs : isingTorusGlueHalves i lower upper x =
        upper ⟨isingTorusReflectSite i x,
          (isingTorusReflectSite_not_lower_iff i x).mpr hx⟩ := by
      simp [isingTorusGlueHalves, hx]
    have hspin : spin (isingTorusGlueHalves i lower upper) x =
        spin upper ⟨isingTorusReflectSite i x,
          (isingTorusReflectSite_not_lower_iff i x).mpr hx⟩ := by
      unfold spin
      rw [hs]
    change spin (isingTorusGlueHalves i lower upper) x + h x = _
    rw [hspin]
    simp [isingTorusEmbedLower, isingTorusEmbedUpper,
      isingTorusUpperValues, hx]

abbrev IsingTorusDirectedEdge (d k : Nat) :=
  IsingDyadicTorus d k × Fin d

def isingTorusLowerGradientFeature (i : Fin d)
    (u : IsingTorusLowerSite (k := k) i → Real)
    (e : IsingTorusDirectedEdge d k) : Real :=
  isingTorusEmbedLower i u e.1 -
    isingTorusEmbedLower i u (e.1 + isingTorusStep e.2)

def isingTorusUpperGradientFeature (i : Fin d)
    (u : IsingTorusLowerSite (k := k) i → Real)
    (e : IsingTorusDirectedEdge d k) : Real :=
  -(isingTorusEmbedUpper i u e.1 -
    isingTorusEmbedUpper i u (e.1 + isingTorusStep e.2))



def isingTorusBoundaryFeature (i : Fin d)
    (u : IsingTorusLowerSite (k := k) i → Real)
    (e : IsingTorusDirectedEdge d k) : Real :=
  if isingTorusInLowerHalf i e.1 ↔
      isingTorusInLowerHalf i (e.1 + isingTorusStep e.2)
    then 0 else isingTorusLowerGradientFeature i u e

theorem isingTorus_lowerFeature_mul_upperFeature_eq_boundary
    (i : Fin d) (u v : IsingTorusLowerSite (k := k) i → Real)
    (e : IsingTorusDirectedEdge d k) :
    isingTorusLowerGradientFeature i u e *
        isingTorusUpperGradientFeature i v e =
      isingTorusBoundaryFeature i u e *
        isingTorusBoundaryFeature i v e := by
  rcases e with ⟨x, j⟩
  let y := x + isingTorusStep j
  by_cases hx : isingTorusInLowerHalf i x <;>
    by_cases hy : isingTorusInLowerHalf i y
  · simp [isingTorusBoundaryFeature, isingTorusLowerGradientFeature,
      isingTorusUpperGradientFeature, isingTorusEmbedLower,
      isingTorusEmbedUpper, y, hx, hy]
  · have href : isingTorusReflectSite i y = x :=
      (isingTorus_crossing_reflects_endpoints i j x).1 ⟨hx, hy⟩
    simp [isingTorusBoundaryFeature, isingTorusLowerGradientFeature,
      isingTorusUpperGradientFeature, isingTorusEmbedLower,
      isingTorusEmbedUpper, y, hx, hy, href]
  · have href : isingTorusReflectSite i x = y :=
      (isingTorus_crossing_reflects_endpoints i j x).2 ⟨hx, hy⟩
    simp [isingTorusBoundaryFeature, isingTorusLowerGradientFeature,
      isingTorusUpperGradientFeature, isingTorusEmbedLower,
      isingTorusEmbedUpper, y, hx, hy, href]
  · simp [isingTorusBoundaryFeature, isingTorusLowerGradientFeature,
      isingTorusUpperGradientFeature, isingTorusEmbedLower,
      isingTorusEmbedUpper, y, hx, hy]

theorem isingTorus_crossBilinear_eq_neg_boundaryFeatureDot
    (i : Fin d)
    (u v : IsingTorusLowerSite (k := k) i → Real) :
    isingTorusDirichletBilinear
        (isingTorusEmbedLower i u) (isingTorusEmbedUpper i v) =
      -(∑ e : IsingTorusDirectedEdge d k,
        isingTorusBoundaryFeature i u e *
          isingTorusBoundaryFeature i v e) := by
  unfold isingTorusDirichletBilinear
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← isingTorus_lowerFeature_mul_upperFeature_eq_boundary
    i u v (x, j)]
  unfold isingTorusLowerGradientFeature isingTorusUpperGradientFeature
  ring

theorem isingTorus_crossBilinear_eq_neg_featureDot
    (i : Fin d)
    (u v : IsingTorusLowerSite (k := k) i → Real) :
    isingTorusDirichletBilinear
        (isingTorusEmbedLower i u) (isingTorusEmbedUpper i v) =
      -(∑ e : IsingTorusDirectedEdge d k,
        isingTorusLowerGradientFeature i u e *
          isingTorusUpperGradientFeature i v e) := by
  unfold isingTorusDirichletBilinear
    isingTorusLowerGradientFeature isingTorusUpperGradientFeature
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def isingTorusLowerHalfWeight (i : Fin d) (beta : Real)
    (u : IsingTorusLowerSite (k := k) i → Real) : Real :=
  Real.exp (-(beta / 2) * isingTorusDirichlet
    (isingTorusEmbedLower i u))

noncomputable def isingTorusUpperHalfWeight (i : Fin d) (beta : Real)
    (u : IsingTorusLowerSite (k := k) i → Real) : Real :=
  Real.exp (-(beta / 2) * isingTorusDirichlet
    (isingTorusEmbedUpper i u))

theorem isingTorus_shiftedWeight_factor_halves
    (i : Fin d) (beta : Real)
    (u v : IsingTorusLowerSite (k := k) i → Real) :
    Real.exp (-(beta / 2) * isingTorusDirichlet
      (isingTorusEmbedLower i u + isingTorusEmbedUpper i v)) =
      isingTorusLowerHalfWeight i beta u *
        isingTorusUpperHalfWeight i beta v *
        Real.exp (beta *
          ∑ e : IsingTorusDirectedEdge d k,
            isingTorusLowerGradientFeature i u e *
              isingTorusUpperGradientFeature i v e) := by
  rw [isingTorusDirichlet_add,
    isingTorus_crossBilinear_eq_neg_featureDot]
  unfold isingTorusLowerHalfWeight isingTorusUpperHalfWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem isingTorus_shiftedWeight_factor_boundary
    (i : Fin d) (beta : Real)
    (u v : IsingTorusLowerSite (k := k) i → Real) :
    Real.exp (-(beta / 2) * isingTorusDirichlet
      (isingTorusEmbedLower i u + isingTorusEmbedUpper i v)) =
      isingTorusLowerHalfWeight i beta u *
        isingTorusUpperHalfWeight i beta v *
        Real.exp (beta *
          ∑ e : IsingTorusDirectedEdge d k,
            isingTorusBoundaryFeature i u e *
              isingTorusBoundaryFeature i v e) := by
  rw [isingTorusDirichlet_add,
    isingTorus_crossBilinear_eq_neg_boundaryFeatureDot]
  unfold isingTorusLowerHalfWeight isingTorusUpperHalfWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring



def isingTorusReflectField (i : Fin d)
    (u : IsingDyadicTorus d k → Real) : IsingDyadicTorus d k → Real :=
  fun x => u (isingTorusReflectSite i x)

theorem isingTorusDirichlet_reflectField
    (i : Fin d) (u : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet (isingTorusReflectField i u) =
      isingTorusDirichlet u := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  calc
    (∑ x : IsingDyadicTorus d k, ∑ j : Fin d,
        (isingTorusReflectField i u x -
          isingTorusReflectField i u (x + isingTorusStep j)) *
        (isingTorusReflectField i u x -
          isingTorusReflectField i u (x + isingTorusStep j))) =
      ∑ j : Fin d, ∑ x : IsingDyadicTorus d k,
        (isingTorusReflectField i u x -
          isingTorusReflectField i u (x + isingTorusStep j)) *
        (isingTorusReflectField i u x -
          isingTorusReflectField i u (x + isingTorusStep j)) :=
        Finset.sum_comm
    _ = ∑ j : Fin d, ∑ x : IsingDyadicTorus d k,
        (u x - u (x + isingTorusStep j)) *
          (u x - u (x + isingTorusStep j)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        let e : IsingDyadicTorus d k → IsingDyadicTorus d k := fun x =>
          isingTorusReflectSite i x - isingTorusStep i
        have hinv : Function.Involutive
            (isingTorusReflectSite (k := k) i) :=
          fun x => isingTorusReflectSite_involutive i x
        have hrefl : Function.Bijective
            (isingTorusReflectSite (k := k) i) :=
          hinv.bijective
        have he : Function.Bijective e :=
          (Equiv.subRight (isingTorusStep (k := k) i)).bijective.comp hrefl
        calc
          (∑ x,
              (isingTorusReflectField i u x -
                isingTorusReflectField i u (x + isingTorusStep i)) *
              (isingTorusReflectField i u x -
                isingTorusReflectField i u (x + isingTorusStep i))) =
            ∑ x, (u (e x + isingTorusStep i) - u (e x)) *
              (u (e x + isingTorusStep i) - u (e x)) := by
                apply Finset.sum_congr rfl
                intro x _
                dsimp only [e, isingTorusReflectField]
                rw [isingTorusReflectSite_add_step_same]
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
            (isingTorusReflectSite (k := k) i) :=
          fun x => isingTorusReflectSite_involutive i x
        have hrefl : Function.Bijective
            (isingTorusReflectSite (k := k) i) :=
          hinv.bijective
        calc
          (∑ x,
              (isingTorusReflectField i u x -
                isingTorusReflectField i u (x + isingTorusStep j)) *
              (isingTorusReflectField i u x -
                isingTorusReflectField i u (x + isingTorusStep j))) =
            ∑ x, (u (isingTorusReflectSite i x) -
              u (isingTorusReflectSite i x + isingTorusStep j)) *
              (u (isingTorusReflectSite i x) -
              u (isingTorusReflectSite i x + isingTorusStep j)) := by
                apply Finset.sum_congr rfl
                intro x _
                dsimp only [isingTorusReflectField]
                rw [isingTorusReflectSite_add_step_of_ne i j hji]
          _ = ∑ x, (u x - u (x + isingTorusStep j)) *
              (u x - u (x + isingTorusStep j)) :=
            hrefl.sum_comp (fun y : IsingDyadicTorus d k =>
              (u y - u (y + isingTorusStep j)) *
                (u y - u (y + isingTorusStep j)))
    _ = ∑ x : IsingDyadicTorus d k, ∑ j : Fin d,
        (u x - u (x + isingTorusStep j)) *
          (u x - u (x + isingTorusStep j)) := Finset.sum_comm

theorem isingTorusReflectField_add
    (i : Fin d) (u v : IsingDyadicTorus d k → Real) :
    isingTorusReflectField i (u + v) =
      isingTorusReflectField i u + isingTorusReflectField i v := by
  rfl

theorem isingTorusDirichletBilinear_reflectField
    (i : Fin d) (u v : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear
        (isingTorusReflectField i u) (isingTorusReflectField i v) =
      isingTorusDirichletBilinear u v := by
  have hadd := isingTorusDirichlet_add u v
  have haddR := isingTorusDirichlet_add
    (isingTorusReflectField i u) (isingTorusReflectField i v)
  rw [← isingTorusReflectField_add,
    isingTorusDirichlet_reflectField,
    isingTorusDirichlet_reflectField,
    isingTorusDirichlet_reflectField] at haddR
  linarith

theorem isingTorusEmbedUpper_eq_reflect_embedLower
    (i : Fin d) (u : IsingTorusLowerSite (k := k) i → Real) :
    isingTorusEmbedUpper i u =
      isingTorusReflectField i (isingTorusEmbedLower i u) := by
  funext x
  by_cases hx : isingTorusInLowerHalf i x
  · have hr : ¬ isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      fun hr => (isingTorusReflectSite_not_lower_iff i x).mp hr hx
    simp [isingTorusEmbedUpper, isingTorusReflectField,
      isingTorusEmbedLower, hx, hr]
  · have hr : isingTorusInLowerHalf i (isingTorusReflectSite i x) :=
      (isingTorusReflectSite_not_lower_iff i x).mpr hx
    simp [isingTorusEmbedUpper, isingTorusReflectField,
      isingTorusEmbedLower, hx, hr]

theorem isingTorusUpperHalfWeight_eq_lowerHalfWeight
    (i : Fin d) (beta : Real)
    (u : IsingTorusLowerSite (k := k) i → Real) :
    isingTorusUpperHalfWeight i beta u =
      isingTorusLowerHalfWeight i beta u := by
  unfold isingTorusUpperHalfWeight isingTorusLowerHalfWeight
  rw [isingTorusEmbedUpper_eq_reflect_embedLower,
    isingTorusDirichlet_reflectField]

theorem isingTorus_upperFeatureDot_eq_lowerFeatureDot
    (i : Fin d)
    (u v : IsingTorusLowerSite (k := k) i → Real) :
    (∑ e : IsingTorusDirectedEdge d k,
        isingTorusUpperGradientFeature i u e *
          isingTorusUpperGradientFeature i v e) =
      ∑ e : IsingTorusDirectedEdge d k,
        isingTorusLowerGradientFeature i u e *
          isingTorusLowerGradientFeature i v e := by
  have href := isingTorusDirichletBilinear_reflectField i
    (isingTorusEmbedLower i u) (isingTorusEmbedLower i v)
  rw [← isingTorusEmbedUpper_eq_reflect_embedLower,
    ← isingTorusEmbedUpper_eq_reflect_embedLower] at href
  unfold isingTorusUpperGradientFeature isingTorusLowerGradientFeature
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [neg_mul_neg]
  exact href



theorem isingTorusShiftedPartition_eq_halves
    (i : Fin d) (beta : Real) (h : IsingDyadicTorus d k → Real) :
    isingTorusShiftedPartition beta h =
      ∑ lower : ConfigSpace (IsingTorusLowerSite (k := k) i),
        ∑ upper : ConfigSpace (IsingTorusLowerSite (k := k) i),
          isingTorusLowerHalfWeight i beta
              (isingTorusLowerValues i h lower) *
            isingTorusUpperHalfWeight i beta
              (isingTorusUpperValues i h upper) *
            Real.exp (beta *
              ∑ e : IsingTorusDirectedEdge d k,
                isingTorusBoundaryFeature i
                    (isingTorusLowerValues i h lower) e *
                  isingTorusBoundaryFeature i
                    (isingTorusUpperValues i h upper) e) := by
  unfold isingTorusShiftedPartition
  rw [← (isingTorusHalvesEquiv (k := k) i).bijective.sum_comp
    (fun sigma : ConfigSpace (IsingDyadicTorus d k) =>
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma + h))),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro lower _
  apply Finset.sum_congr rfl
  intro upper _
  change Real.exp (-(beta / 2) * isingTorusDirichlet
      (isingTorusSpinField (isingTorusGlueHalves i lower upper) + h)) = _
  rw [isingTorusSpinGlue_add_field_eq_embeds,
    isingTorus_shiftedWeight_factor_boundary]

theorem isingTorusLowerValues_polarizeLower
    (i : Fin d) (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusLowerValues i (isingTorusPolarizeLower i h) sigma =
      isingTorusLowerValues i h sigma := by
  funext x
  simp [isingTorusLowerValues, isingTorusPolarizeLower, x.2]

theorem isingTorusUpperValues_polarizeLower
    (i : Fin d) (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusUpperValues i (isingTorusPolarizeLower i h) sigma =
      isingTorusLowerValues i h sigma := by
  funext x
  have hr : ¬ isingTorusInLowerHalf i (isingTorusReflectSite i x.1) :=
    fun hr => (isingTorusReflectSite_not_lower_iff i x.1).mp hr x.2
  simp [isingTorusUpperValues, isingTorusLowerValues,
    isingTorusPolarizeLower, hr]

theorem isingTorusLowerValues_polarizeUpper
    (i : Fin d) (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusLowerValues i (isingTorusPolarizeUpper i h) sigma =
      isingTorusUpperValues i h sigma := by
  funext x
  simp [isingTorusLowerValues, isingTorusUpperValues,
    isingTorusPolarizeUpper, x.2]

theorem isingTorusUpperValues_polarizeUpper
    (i : Fin d) (h : IsingDyadicTorus d k → Real)
    (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusUpperValues i (isingTorusPolarizeUpper i h) sigma =
      isingTorusUpperValues i h sigma := by
  funext x
  have hr : ¬ isingTorusInLowerHalf i (isingTorusReflectSite i x.1) :=
    fun hr => (isingTorusReflectSite_not_lower_iff i x.1).mp hr x.2
  simp [isingTorusUpperValues, isingTorusPolarizeUpper, hr]


theorem isingTorusShiftedPartition_polarization
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (h : IsingDyadicTorus d k → Real) :
    2 * isingTorusShiftedPartition beta h ≤
      isingTorusShiftedPartition beta (isingTorusPolarizeLower i h) +
        isingTorusShiftedPartition beta (isingTorusPolarizeUpper i h) := by
  rw [isingTorusShiftedPartition_eq_halves i beta h,
    isingTorusShiftedPartition_eq_halves i beta
      (isingTorusPolarizeLower i h),
    isingTorusShiftedPartition_eq_halves i beta
      (isingTorusPolarizeUpper i h)]
  simp_rw [isingTorusLowerValues_polarizeLower,
    isingTorusUpperValues_polarizeLower,
    isingTorusLowerValues_polarizeUpper,
    isingTorusUpperValues_polarizeUpper,
    isingTorusUpperHalfWeight_eq_lowerHalfWeight]
  exact exp_dotProduct_two_family_reflection_inequality beta hbeta
    (fun sigma e => isingTorusBoundaryFeature i
      (isingTorusLowerValues i h sigma) e)
    (fun sigma e => isingTorusBoundaryFeature i
      (isingTorusUpperValues i h sigma) e)
    (fun sigma => isingTorusLowerHalfWeight i beta
      (isingTorusLowerValues i h sigma))
    (fun sigma => isingTorusLowerHalfWeight i beta
      (isingTorusUpperValues i h sigma))

end StatMech.FrontierA
