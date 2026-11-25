/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.RayGroup
import Mathlib.Data.ZMod.Basic

/-!
# Infinite-place signs for ray class groups (N406 stage 1a)

The first coordinate of the later residue-sign map: the sign of a ray element
at each real place selected by a modulus, valued in `Multiplicative (ZMod 2)`.

ATLAS source map: NumberTheoryI item N406, Theorem 21.8, Section 21.3, source
`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, declaration
`RayClassField.theorem_21_8_quotient_iso`:
https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647

* `signAtRealPlace` corresponds to ATLAS `signAtPlace` with
  `signAtPlace_eq_zero_iff` (lines 1497--1531): trivial sign is strict
  positivity at the selected real embedding.
* `infiniteSignMap` corresponds to ATLAS `signMapHom` (lines 1533--1551):
  it collects the sign coordinates over the modulus's infinite support.
* `positiveRayElements := (infiniteSignMap m).ker` packages the
  infinite-positivity conjunct of ATLAS `UnitsCongruent_subgroup'`
  (lines 827--839), and `mem_positiveRayElements_iff` is the native
  kernel/positivity bridge used by the final product-map kernel calculation
  (lines 2612--2643).

Scope: this module provides only the infinite-sign coordinate toward the
residue-sign product and quotient equivalence. It does not complete all of
N406, including the finite coordinate, surjectivity, quotient equivalence,
or exact sequence.
-/

@[expose] public noncomputable section

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Sign bit of a real number: `0` when positive and `1` otherwise. -/
private def signBit (r : ℝ) : ZMod 2 := if 0 < r then 0 else 1

/-- The sign bit of a positive real number is `0`. -/
private theorem signBit_of_pos {r : ℝ} (h : 0 < r) : signBit r = 0 := ite_eq_left h

/-- The sign bit of a non-positive real number is `1`. -/
private theorem signBit_of_not_pos {r : ℝ} (h : ¬ 0 < r) : signBit r = 1 :=
  ite_eq_right h

/-- The sign bit is multiplicative on nonzero reals. -/
private theorem signBit_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    signBit (a * b) = signBit a + signBit b := by
  rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
  · rcases lt_or_gt_of_ne hb with hb_neg | hb_pos
    · have hpos : 0 < a * b := mul_pos_of_neg_of_neg ha_neg hb_neg
      rw [signBit_of_pos hpos, signBit_of_not_pos (not_lt_of_gt ha_neg),
        signBit_of_not_pos (not_lt_of_gt hb_neg)]
      decide
    · have hneg : a * b < 0 := mul_neg_of_neg_of_pos ha_neg hb_pos
      rw [signBit_of_not_pos (not_lt_of_gt hneg),
        signBit_of_not_pos (not_lt_of_gt ha_neg), signBit_of_pos hb_pos]
      decide
  · rcases lt_or_gt_of_ne hb with hb_neg | hb_pos
    · have hneg : a * b < 0 := mul_neg_of_pos_of_neg ha_pos hb_neg
      rw [signBit_of_not_pos (not_lt_of_gt hneg), signBit_of_pos ha_pos,
        signBit_of_not_pos (not_lt_of_gt hb_neg)]
      decide
    · have hpos : 0 < a * b := mul_pos ha_pos hb_pos
      rw [signBit_of_pos hpos, signBit_of_pos ha_pos, signBit_of_pos hb_pos]
      decide

/-- `ofAdd 0` is the identity of `Multiplicative (ZMod 2)`. -/
private theorem ofAdd_zero_eq_one : Multiplicative.ofAdd (0 : ZMod 2) = 1 := rfl

/-- **Sign of a unit at a real place.** For a real place $w$ of a number field $K$, let
$\sigma_w \colon K \to \mathbb{R}$ be the corresponding real embedding. The sign at $w$ is the
group homomorphism from $K^\times$ to $\mathbb{Z}/2\mathbb{Z}$, written multiplicatively, that
sends $x$ to the class of $0$ (the identity) if $\sigma_w(x) > 0$ and to the class of $1$
otherwise. -/
noncomputable def signAtRealPlace (w : RealPlace K) :
    Kˣ →* Multiplicative (ZMod 2) where
  toFun x :=
    Multiplicative.ofAdd
      (signBit (InfinitePlace.embedding_of_isReal w.property (x : K)))
  map_one' := by
    change Multiplicative.ofAdd
        (signBit (InfinitePlace.embedding_of_isReal w.property ((1 : Kˣ) : K))) =
        1
    rw [Units.val_one, map_one, signBit_of_pos one_pos, ofAdd_zero_eq_one]
  map_mul' := fun x y => by
    have hx : InfinitePlace.embedding_of_isReal w.property (x : K) ≠ 0 :=
      (map_ne_zero_iff _
        (RingHom.injective (InfinitePlace.embedding_of_isReal w.property))).mpr
        (Units.ne_zero x)
    have hy : InfinitePlace.embedding_of_isReal w.property (y : K) ≠ 0 :=
      (map_ne_zero_iff _
        (RingHom.injective (InfinitePlace.embedding_of_isReal w.property))).mpr
        (Units.ne_zero y)
    change Multiplicative.ofAdd
        (signBit
          (InfinitePlace.embedding_of_isReal w.property ((x * y : Kˣ) : K))) =
        Multiplicative.ofAdd
          (signBit (InfinitePlace.embedding_of_isReal w.property (x : K))) *
          Multiplicative.ofAdd
            (signBit (InfinitePlace.embedding_of_isReal w.property (y : K)))
    rw [Units.val_mul, map_mul, signBit_mul hx hy, ofAdd_add]

/-- **Trivial sign at a real place means positivity.** Let $w$ be a real place of a number field
$K$ with real embedding $\sigma_w \colon K \to \mathbb{R}$. For every $x \in K^\times$, the sign of
$x$ at $w$, an element of $\mathbb{Z}/2\mathbb{Z}$ written multiplicatively, is the identity if
and only if $\sigma_w(x) > 0$. -/
@[simp] theorem signAtRealPlace_apply_eq_one_iff (w : RealPlace K) (x : Kˣ) :
    signAtRealPlace w x = 1 ↔
      0 < InfinitePlace.embedding_of_isReal w.property (x : K) := by
  unfold signAtRealPlace
  constructor
  · intro hcon
    change Multiplicative.ofAdd
        (signBit (InfinitePlace.embedding_of_isReal w.property (x : K))) = 1 at hcon
    by_cases hpos : 0 < InfinitePlace.embedding_of_isReal w.property (x : K)
    · exact hpos
    · rw [signBit_of_not_pos hpos] at hcon
      have h2 : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd hcon
      exact False.elim (one_ne_zero h2)
  · intro hpos
    change Multiplicative.ofAdd
        (signBit (InfinitePlace.embedding_of_isReal w.property (x : K))) = 1
    rw [signBit_of_pos hpos, ofAdd_zero_eq_one]

/-- **Infinite sign map of a modulus.** Let $m$ be a modulus of a number field $K$ and let
$m_\infty$ be its finite set of real places. The infinite sign map of $m$ is the group
homomorphism from the ray elements of $m$ to the group of functions
$m_\infty \to \mathbb{Z}/2\mathbb{Z}$, with $\mathbb{Z}/2\mathbb{Z}$ written multiplicatively and
the pointwise product, that sends $x$ to the function whose value at $w \in m_\infty$ is the
sign of $x$ at the real place $w$. -/
noncomputable def infiniteSignMap (m : Modulus K) :
    rayElements m →* (m.infinitePart → Multiplicative (ZMod 2)) where
  toFun x := fun w => signAtRealPlace (w : RealPlace K) (x : Kˣ)
  map_one' := by
    funext w
    change signAtRealPlace (w : RealPlace K) ((1 : rayElements m) : Kˣ) = 1
    rw [show ((1 : rayElements m) : Kˣ) = (1 : Kˣ) from rfl, map_one]
  map_mul' := fun x y => by
    funext w
    change signAtRealPlace (w : RealPlace K) ((x * y : rayElements m) : Kˣ) =
      signAtRealPlace (w : RealPlace K) (x : Kˣ) *
        signAtRealPlace (w : RealPlace K) (y : Kˣ)
    rw [show ((x * y : rayElements m) : Kˣ) = (x : Kˣ) * (y : Kˣ) from rfl,
      map_mul]

/-- **Coordinates of the infinite sign map.** Let $m$ be a modulus of a number field $K$ with
finite set of real places $m_\infty$. For every ray element $x$ of $m$ and every $w \in m_\infty$,
the value at $w$ of the infinite sign map of $m$ applied to $x$ is the sign of $x$ at the real
place $w$. -/
@[simp] theorem infiniteSignMap_apply (m : Modulus K) (x : rayElements m)
    (w : m.infinitePart) :
    infiniteSignMap m x w = signAtRealPlace (w : RealPlace K) (x : Kˣ) :=
  rfl

/-- **Trivial infinite sign means positivity at the modulus.** Let $m$ be a modulus of a number
field $K$ with finite set of real places $m_\infty$, and for a real place $w$ let $\sigma_w$ be
the corresponding real embedding of $K$. For every ray element $x$ of $m$, the infinite sign map
of $m$ sends $x$ to the identity if and only if $x$ is positive at the infinite part of $m$,
that is, $\sigma_w(x) > 0$ for every $w \in m_\infty$. -/
@[simp] theorem infiniteSignMap_eq_one_iff (m : Modulus K) (x : rayElements m) :
    infiniteSignMap m x = 1 ↔ PositiveAtInfinitePart m (x : Kˣ) := by
  constructor
  · intro h w hw
    have hmem := congrFun h (⟨w, hw⟩ : m.infinitePart)
    rw [Pi.one_apply, infiniteSignMap_apply] at hmem
    exact (signAtRealPlace_apply_eq_one_iff _ _).mp hmem
  · intro h
    funext w
    rw [Pi.one_apply, infiniteSignMap_apply]
    exact (signAtRealPlace_apply_eq_one_iff _ _).mpr (h (w : RealPlace K) w.property)

/-- **Ray elements positive at the infinite part.** Let $m$ be a modulus of a number field $K$
with finite set of real places $m_\infty$, and for a real place $w$ let $\sigma_w$ be the real
embedding of $K$ at $w$. The positive ray elements of $m$ form the subgroup of the ray elements
of $m$ defined as the kernel of the infinite sign map of $m$; equivalently, they are the ray
elements $x$ with $\sigma_w(x) > 0$ for every $w \in m_\infty$. -/
def positiveRayElements (m : Modulus K) : Subgroup (rayElements m) :=
  (infiniteSignMap m).ker

/-- **Membership in the positive ray elements.** Let $m$ be a modulus of a number field $K$ with
finite set of real places $m_\infty$, and for a real place $w$ let $\sigma_w$ be the real embedding
of $K$ at $w$. A ray element $x$ of $m$ is a positive ray element of $m$ if and only if $x$ is
positive at the infinite part of $m$, that is, $\sigma_w(x) > 0$ for every $w \in m_\infty$. -/
@[simp] theorem mem_positiveRayElements_iff (m : Modulus K) (x : rayElements m) :
    x ∈ positiveRayElements m ↔ PositiveAtInfinitePart m (x : Kˣ) := by
  unfold positiveRayElements
  rw [MonoidHom.mem_ker, infiniteSignMap_eq_one_iff]

end Modulus
end NumberField
