/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.AddAut
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Tactic.Ring

/-!
# Inner twisted classes in centreless groups (Kourovka Notebook Problem 18.15)

Kourovka Notebook, Archive of Solved Problems, Problem 18.15 (V. G. Bardakov, M. V. Neshchadim, T.
R. Nasybullov): for `φ ∈ Aut G` let `[e]_φ = {g⁻¹ g^φ | g ∈ G}`. Is it true that if a group `G` has
trivial centre, then there is an inner automorphism `φ` such that `[e]_φ` is not a subgroup?

Bludov's affine group gives a negative answer to this question. It consists of affine
maps over the rational function field with multipliers regular at 1 and equal to 1 there.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.15 (V. G.
Bardakov, M. V. Neshchadim, T. R. Nasybullov). UnsolvedMath record UM-00701444 (`KOU-18.15`),
dataset ulamai/UnsolvedMath v1.8.0.

`G` is required to be nontrivial: the trivial group has trivial centre and `[e]_φ = {1}`, so without
this hypothesis the claim fails for a degenerate reason. Inner automorphisms are `MulAut.conj a`;
the set of inner automorphisms does not depend on the conjugation convention. Adding the hypothesis
makes the refuted claim weaker, so its refutation is the stronger statement.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.TrivialCentreTwistedClassKourovka18Problem15Wanted

/-- **Twisted conjugacy class of the identity (Kourovka 18.15).** For a group $G$ and an
automorphism $\varphi$ of $G$, the $\varphi$-twisted conjugacy class of the identity is the set
$[e]_\varphi = \{g^{-1}\varphi(g) : g \in G\} \subseteq G$. -/
def twistedUnitClass {G : Type} [Group G] (φ : G ≃* G) : Set G :=
  Set.range fun g : G => g⁻¹ * φ g

/-- **Kourovka Problem 18.15: an inner twisted class that is not a subgroup.** Every nontrivial
group $G$ with trivial centre has an element $a \in G$ such that, for the inner automorphism
$\varphi(g) = aga^{-1}$, the twisted conjugacy class of the identity
$[e]_\varphi = \{g^{-1}\varphi(g) : g \in G\}$ is not a subgroup of $G$.

The conjecture is due to V. G. Bardakov, M. V. Neshchadim and T. R. Nasybullov. -/
def trivialCentreHasInnerTwistedClassNotSubgroup : Prop :=
  ∀ (G : Type) [Group G], Nontrivial G → Subgroup.center G = ⊥ →
    ∃ a : G, ¬ ∃ H : Subgroup G, (H : Set G) = twistedUnitClass (MulAut.conj a)

namespace Counterexample

open IsLocalRing Multiplicative SemidirectProduct

private noncomputable abbrev evalIdeal := RingHom.ker (Polynomial.evalRingHom (1 : ℚ))

private instance evalIdealPrime : evalIdeal.IsPrime := RingHom.ker_isPrime _

-- Rational functions regular at 1 and the field of all rational functions.
private abbrev R := Localization.AtPrime evalIdeal
private abbrev K := FractionRing (Polynomial ℚ)

private noncomputable abbrev principalUnits : Subgroup Rˣ :=
  (Units.map (residue R).toMonoidHom).ker

private noncomputable abbrev maximalIdealAddSubgroup : AddSubgroup R :=
  (maximalIdeal R).toAddSubgroup

private noncomputable def slopeUnit : principalUnits →* Kˣ :=
  (Units.map (algebraMap R K).toMonoidHom).comp principalUnits.subtype

private noncomputable def slope : principalUnits →* K :=
  (Units.coeHom K).comp slopeUnit

private theorem slope_injective : Function.Injective slope := by
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  exact IsFractionRing.injective R K huv

private noncomputable def scale : principalUnits →* MulAut (Multiplicative K) where
  toFun u := AddEquiv.toMultiplicative (AddAut.mulLeft (slopeUnit u)).toAdd
  map_one' := MulEquiv.ext fun x ↦ by
    change ofAdd (slope 1 * x.toAdd) = x
    rw [map_one, one_mul]
    rfl
  map_mul' u v := MulEquiv.ext fun x ↦ by
    change ofAdd (slope (u * v) * x.toAdd) = ofAdd (slope u * (slope v * x.toAdd))
    rw [map_mul slope, mul_assoc]

private abbrev G := Multiplicative K ⋊[scale] ↥principalUnits

private noncomputable def translation (x : K) : G := inl (ofAdd x)

private theorem translation_left (x : K) : (translation x).left.toAdd = x := rfl

private theorem translation_right (x : K) : (translation x).right = 1 := rfl

private theorem left_mul (a b : G) :
    (a * b).left.toAdd = a.left.toAdd + slope a.right * b.left.toAdd := rfl

private theorem twisted_eq_translation_iff (a g : G) (c : K) :
    g⁻¹ * MulAut.conj a g = translation c ↔
      a.left.toAdd + slope a.right * g.left.toAdd =
        g.left.toAdd + slope g.right * (c + a.left.toAdd) := by
  rw [MulAut.conj_apply, inv_mul_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  have hleft : (g * translation c * a).left.toAdd =
      g.left.toAdd + slope g.right * (c + a.left.toAdd) := by
    simp only [left_mul, mul_right, translation_left, translation_right, mul_one, mul_add,
      add_assoc]
  constructor
  · intro h
    rw [← left_mul, ← hleft, h]
  · intro h
    apply SemidirectProduct.ext
    · exact toAdd.injective (by rwa [left_mul, hleft])
    · simp only [mul_right, translation_right, mul_one, mul_comm]

private theorem twisted_eq_translation (a g : G) :
    g⁻¹ * MulAut.conj a g =
      translation (slope g.right⁻¹ *
        (a.left.toAdd + (slope a.right - 1) * g.left.toAdd) - a.left.toAdd) := by
  rw [twisted_eq_translation_iff, sub_add_cancel, ← mul_assoc (slope g.right), ← map_mul,
    mul_inv_cancel, map_one, one_mul]
  ring

private theorem sub_one_mem_maximalIdeal (u : principalUnits) :
    ((u.val : R) - 1) ∈ maximalIdeal R := by
  rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  exact congrArg Units.val u.property

private theorem exists_unit_add (d : maximalIdeal R) :
    ∃ u : principalUnits, (u.val : R) = 1 + (d : R) := by
  have hd : residue R (1 + (d : R)) = 1 := by
    rw [map_add, map_one, (residue_eq_zero_iff _).2 d.property, add_zero]
  have hu : IsUnit (1 + (d : R)) := (residue_ne_zero_iff_isUnit _).1 (hd ▸ one_ne_zero)
  refine ⟨⟨hu.unit, ?_⟩, hu.unit_spec⟩
  change Units.map (residue R).toMonoidHom hu.unit = 1
  apply Units.ext
  change residue R (hu.unit : R) = 1
  rw [hu.unit_spec, hd]

private noncomputable def idealTranslations (x : K) :
    Multiplicative ↥maximalIdealAddSubgroup →* G :=
  inl.comp (show ↥maximalIdealAddSubgroup →+ K from
    { toFun := fun d ↦ algebraMap R K (d : R) * x
      map_zero' := by simp
      map_add' := fun d e ↦ by simp [add_mul] }).toMultiplicative

private theorem idealTranslations_apply (x : K) (d : Multiplicative ↥maximalIdealAddSubgroup) :
    idealTranslations x d = translation (algebraMap R K (d.toAdd : R) * x) := rfl

private theorem twisted_eq_translation_of_right_eq_one (a g : G) (ha : a.right = 1) :
    g⁻¹ * MulAut.conj a g = translation ((slope g.right⁻¹ - 1) * a.left.toAdd) := by
  rw [twisted_eq_translation, ha, map_one, sub_self, zero_mul, add_zero, sub_mul, one_mul]

private theorem slope_sub_one (u : principalUnits) :
    slope u - 1 = algebraMap R K ((u.val : R) - 1) := by
  rw [map_sub, map_one]
  rfl

private theorem class_subgroup (a : G) :
    ∃ H : Subgroup G, (H : Set G) = twistedUnitClass (MulAut.conj a) := by
  classical
  by_cases ha : a.right = 1
  · -- For a pure translation by x, the class consists of translations by x times the ideal.
    refine ⟨(idealTranslations a.left.toAdd).range, ?_⟩
    ext z
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨u, hu⟩ := exists_unit_add d.toAdd
      refine ⟨inr u⁻¹, ?_⟩
      change (inr u⁻¹ : G)⁻¹ * MulAut.conj a (inr u⁻¹) = _
      rw [twisted_eq_translation_of_right_eq_one _ _ ha, right_inr, inv_inv,
        idealTranslations_apply, slope_sub_one, hu, add_sub_cancel_left]
    · rintro ⟨g, rfl⟩
      let d : maximalIdealAddSubgroup :=
        ⟨(g.right⁻¹.val : R) - 1, sub_one_mem_maximalIdeal g.right⁻¹⟩
      exact ⟨ofAdd d, by
        change _ = g⁻¹ * MulAut.conj a g
        rw [idealTranslations_apply, twisted_eq_translation_of_right_eq_one _ _ ha, slope_sub_one]
        rfl⟩
  · -- A multiplier different from 1 gives the whole translation subgroup.
    refine ⟨inl.range, ?_⟩
    have hne : slope a.right - 1 ≠ 0 := by
      rw [sub_ne_zero, ← map_one slope]
      exact fun h ↦ ha (slope_injective h)
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      let g := translation (c.toAdd / (slope a.right - 1))
      refine ⟨g, ?_⟩
      change g⁻¹ * MulAut.conj a g = translation c.toAdd
      dsimp only [g]
      rw [twisted_eq_translation, translation_left, translation_right, inv_one, map_one, one_mul,
        mul_div_cancel₀ _ hne, add_sub_cancel_left]
    · rintro ⟨g, rfl⟩
      change g⁻¹ * MulAut.conj a g ∈ _
      rw [twisted_eq_translation]
      exact ⟨_, rfl⟩

private theorem exists_slope_ne_one : ∃ u : principalUnits, slope u ≠ 1 := by
  let p : Polynomial ℚ := Polynomial.X - 1
  let x : R := algebraMap (Polynomial ℚ) R p
  have hp : p ≠ 0 := sub_ne_zero.mpr (by simpa using Polynomial.X_ne_C (1 : ℚ))
  have hx : x ≠ 0 := by
    intro h
    exact hp (IsLocalization.injective R evalIdeal.primeCompl_le_nonZeroDivisors
      (h.trans (map_zero _).symm))
  have hxmem : x ∈ maximalIdeal R := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff R evalIdeal]
    simp [evalIdeal, p, RingHom.mem_ker]
  obtain ⟨u, hu⟩ := exists_unit_add ⟨x, hxmem⟩
  refine ⟨u, ?_⟩
  rw [← sub_ne_zero, slope_sub_one, hu, add_sub_cancel_left]
  intro h
  exact hx (IsFractionRing.injective R K (h.trans (map_zero _).symm))

private theorem center_eq_bot : Subgroup.center G = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  rw [Subgroup.mem_center_iff] at ha
  have hs : slope a.right = 1 := by
    have h := congrArg (fun g : G ↦ g.left.toAdd) (ha (translation 1))
    simp only [left_mul, translation_left, translation_right, map_one, one_mul, mul_one,
      add_comm (1 : K) a.left.toAdd] at h
    exact (add_left_cancel h).symm
  obtain ⟨u, hu⟩ := exists_slope_ne_one
  have h := congrArg (fun g : G ↦ g.left.toAdd) (ha (inr u))
  have hx : slope u * a.left.toAdd = a.left.toAdd := by
    simpa only [left_mul, left_inr, right_inr, toAdd_one, zero_add, mul_zero, add_zero] using h
  have hzero : a.left.toAdd = 0 := by
    have hm : (slope u - 1) * a.left.toAdd = 0 := by rw [sub_mul, one_mul, hx, sub_self]
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hu)
  rw [Subgroup.mem_bot]
  exact SemidirectProduct.ext (toAdd.injective hzero)
    (slope_injective (hs.trans (map_one slope).symm))

private theorem group_nontrivial : Nontrivial G :=
  ⟨⟨translation 1, translation 0, fun h ↦ (one_ne_zero : (1 : K) ≠ 0)
    (congrArg (fun g ↦ g.left.toAdd) h)⟩⟩

end Counterexample

/--
**Negative answer to Kourovka Problem 18.15.** The conjecture of Kourovka Problem 18.15 is
false: there is a nontrivial group $G$ with trivial centre such that for every $a \in G$, with
$\varphi$ the inner automorphism $\varphi(g) = aga^{-1}$, the twisted conjugacy class of the
identity $[e]_\varphi = \{g^{-1}\varphi(g) : g \in G\}$ is a subgroup of $G$.

The Kourovka Archive answers 18.15 "No, not always", citing V. V. Bludov's Example 2 in
Gonçalves–Nasybullov (2019), a group with trivial centre in which $[e]_\varphi$ is a subgroup for
every inner automorphism $\varphi$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 18.15 (V. G. Bardakov, M. V. Neshchadim, T. R. Nasybullov); resolution: V. V. Bludov,
Example 2 in D. Gonçalves and T. Nasybullov, On groups where the twisted conjugacy class of the unit
element is a subgroup, Comm. Algebra 47 (2019), no. 3, 930-944, Kourovka Archive, Problem 18.15: No,
not always; see Bludov's Example 2, https://arxiv.org/abs/1401.0300v49.
-/
theorem trivialCentreHasInnerTwistedClassNotSubgroup_refuted :
    ¬ trivialCentreHasInnerTwistedClassNotSubgroup := by
  intro h
  obtain ⟨a, ha⟩ := h Counterexample.G Counterexample.group_nontrivial Counterexample.center_eq_bot
  exact ha (Counterexample.class_subgroup a)

end MathlibExt.GroupTheory.TrivialCentreTwistedClassKourovka18Problem15Wanted
