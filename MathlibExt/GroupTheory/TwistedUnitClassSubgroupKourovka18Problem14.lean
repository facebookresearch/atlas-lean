/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.SemidirectProduct

/-!
# The abelian assertion of Kourovka Problem 18.14

We refute the assertion using the class-two case of Nicotera's construction at the prime three.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.TwistedUnitClassSubgroupKourovka18Problem14Wanted

/-- **Twisted conjugacy class of the identity (Kourovka 18.14).** For a group $G$ and an
automorphism $\varphi$ of $G$, the $\varphi$-twisted conjugacy class of the identity is the set
$[e]_\varphi = \{g^{-1}\varphi(g) : g \in G\} \subseteq G$. -/
def twistedUnitClass {G : Type} [Group G] (φ : G ≃* G) : Set G :=
  Set.range fun g : G => g⁻¹ * φ g

/-- **Groups whose twisted classes of the identity are all subgroups.** A group $G$ has this
property when, for every automorphism $\varphi$ of $G$, the twisted conjugacy class of the
identity $[e]_\varphi = \{g^{-1}\varphi(g) : g \in G\}$ is a subgroup of $G$. -/
def AllTwistedUnitClassesSubgroups (G : Type) [Group G] : Prop :=
  ∀ φ : G ≃* G, ∃ H : Subgroup G, (H : Set G) = twistedUnitClass φ

/-- **Kourovka Problem 18.14, nilpotency assertion.** Every group $G$ in which, for every
automorphism $\varphi$ of $G$, the twisted conjugacy class of the identity
$[e]_\varphi = \{g^{-1}\varphi(g) : g \in G\}$ is a subgroup of $G$, is nilpotent.

This is the first assertion of the conjecture of V. G. Bardakov, M. V. Neshchadim and
T. R. Nasybullov. -/
def twistedUnitClassesSubgroupsImpliesNilpotent : Prop :=
  ∀ (G : Type) [Group G], AllTwistedUnitClassesSubgroups G → Group.IsNilpotent G

/-- **Kourovka Problem 18.14, abelian assertion for finitely generated groups.** Every finitely
generated group $G$ in which, for every automorphism $\varphi$ of $G$, the twisted conjugacy class
of the identity $[e]_\varphi = \{g^{-1}\varphi(g) : g \in G\}$ is a subgroup of $G$, is abelian.

This is the second assertion of the conjecture of Kourovka Problem 18.14. -/
def twistedUnitClassesSubgroupsFGImpliesAbelian : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → AllTwistedUnitClassesSubgroups G →
    ∀ x y : G, x * y = y * x

namespace Counterexample

open SemidirectProduct
open Multiplicative (ofAdd toAdd)

private abbrev R := ZMod 9
private abbrev V := R × R
private abbrev A := Multiplicative V
private abbrev C := Multiplicative (ZMod 3)

-- The generator acts by the scalar four, whose cube is one modulo nine.
private def scale (t : C) : R := 1 + 3 * (t.toAdd.val : R)

private theorem scale_one : scale 1 = 1 := by decide

private theorem scale_mul : ∀ t s : C, scale (t * s) = scale t * scale s := by decide

private def action : C →* MulAut A where
  toFun t :=
    { toFun := fun a ↦ ofAdd (scale t • a.toAdd)
      invFun := fun a ↦ ofAdd (scale t⁻¹ • a.toAdd)
      left_inv := fun a ↦ by
        change ofAdd (scale t⁻¹ • (scale t • a.toAdd)) = a
        rw [smul_smul, ← scale_mul, inv_mul_cancel, scale_one, one_smul]
        rfl
      right_inv := fun a ↦ by
        change ofAdd (scale t • (scale t⁻¹ • a.toAdd)) = a
        rw [smul_smul, ← scale_mul, mul_inv_cancel, scale_one, one_smul]
        rfl
      map_mul' := fun a b ↦ congrArg ofAdd (smul_add (scale t) a.toAdd b.toAdd) }
  map_one' := by
    apply MulEquiv.ext
    intro a
    change ofAdd (scale 1 • a.toAdd) = a
    rw [scale_one, one_smul]
    rfl
  map_mul' t s := by
    apply MulEquiv.ext
    intro a
    change ofAdd (scale (t * s) • a.toAdd) = ofAdd (scale t • (scale s • a.toAdd))
    rw [smul_smul, scale_mul]

private theorem action_apply (t : C) (a : A) :
    action t a = ofAdd (scale t • a.toAdd) := rfl

private abbrev G := A ⋊[action] C

private def a : G := inl (ofAdd (1, 0))
private def b : G := inl (ofAdd (0, 1))
private def x : G := inr (ofAdd 1)

private theorem a_x_noncommute : a * x ≠ x * a := by
  intro h
  have h₁ := congrArg (fun g : G ↦ g.left.toAdd.1) h
  simp only [a, x, mul_left, action_apply, right_inl, right_inr, left_inl, left_inr] at h₁
  exact (by decide : (1 : R) ≠ 4) h₁

private theorem cube_right : ∀ t : C, t ^ 3 = 1 := by decide

private theorem scale_sum : ∀ t : C, scale t + scale (t * t) = 2 := by decide

private theorem cube (g : G) : g ^ 3 = inl (ofAdd ((3 : R) • g.left.toAdd)) := by
  apply SemidirectProduct.ext
  · simp only [pow_succ, pow_zero, one_mul, mul_left, mul_right, left_inl, action_apply]
    change ofAdd
      (g.left.toAdd + scale g.right • g.left.toAdd + scale (g.right * g.right) • g.left.toAdd) = _
    rw [add_assoc, ← add_smul, scale_sum]
    apply congrArg ofAdd
    rw [show (3 : R) = 1 + 2 from by decide, add_smul, one_smul]
  · simp only [pow_succ, pow_zero, one_mul, mul_right, right_inl]
    simpa only [pow_succ, pow_zero, one_mul] using cube_right g.right

private theorem inl_cube (g : G) : (inl g.left : G) ^ 3 = g ^ 3 := by
  rw [cube, cube, left_inl]

private theorem commute_of_right_eq_one {g h : G} (hg : g.right = 1) (hh : h.right = 1) :
    Commute g h := by
  change g * h = h * g
  apply SemidirectProduct.ext
  · simp [hg, hh, mul_comm]
  · simp [hg, hh]

private theorem scale_smul (t : C) (v : V) :
    scale t • v = v + (t.toAdd.val : R) • ((3 : R) • v) := by
  rw [scale, add_smul, one_smul, smul_smul, mul_comm (3 : R)]

private theorem cube_left (g : G) : (g ^ 3).left.toAdd = (3 : R) • g.left.toAdd := by
  rw [cube]
  rfl

private theorem commute_cube_coeff {g h : G} (hc : Commute g h) :
    (g.right.toAdd.val : R) • (h ^ 3).left.toAdd =
      (h.right.toAdd.val : R) • (g ^ 3).left.toAdd := by
  have e := congrArg (fun z : G ↦ z.left.toAdd) hc.eq
  simp only [mul_left, action_apply, toAdd_mul] at e
  change g.left.toAdd + scale g.right • h.left.toAdd =
    h.left.toAdd + scale h.right • g.left.toAdd at e
  rw [scale_smul, scale_smul, ← add_assoc, ← add_assoc, add_comm h.left.toAdd] at e
  simpa only [cube_left] using add_left_cancel e

private theorem times_three_eq_zero :
    ∀ t : C, (t.toAdd.val : R) * 3 = 0 ↔ t = 1 := by decide

private theorem coeff_mul_eq_zero :
    ∀ (t : C) (z : R), t ≠ 1 → (t.toAdd.val : R) * z = 0 → z = 0 := by decide

-- Independent cubes of commuting elements force their common centralizer into the abelian factor.
private theorem right_eq_one_of_commute_cubes {g u v : G}
    (hu : u ^ 3 = a ^ 3) (hv : v ^ 3 = b ^ 3)
    (hgu : Commute g u) (hgv : Commute g v) : g.right = 1 := by
  have e₁ := congrArg Prod.fst (commute_cube_coeff hgu)
  have e₂ := congrArg Prod.fst (commute_cube_coeff hgv)
  have e₃ := congrArg Prod.snd (commute_cube_coeff hgv)
  rw [hu, cube_left] at e₁
  rw [hv, cube_left] at e₂ e₃
  change (g.right.toAdd.val : R) * (3 * 1) = _ at e₁
  change (g.right.toAdd.val : R) * (3 * 0) =
    (v.right.toAdd.val : R) * (g ^ 3).left.toAdd.1 at e₂
  change (g.right.toAdd.val : R) * (3 * 1) =
    (v.right.toAdd.val : R) * (g ^ 3).left.toAdd.2 at e₃
  simp only [mul_one, mul_zero] at e₁ e₂ e₃
  apply (times_three_eq_zero _).mp
  by_cases hv₁ : v.right = 1
  · rw [e₃, hv₁]
    change 0 * _ = 0
    exact zero_mul _
  · rw [e₁]
    change (u.right.toAdd.val : R) * (g ^ 3).left.toAdd.1 = 0
    rw [coeff_mul_eq_zero _ _ hv₁ e₂.symm, mul_zero]

private theorem map_inl_right (φ : G ≃* G) (c : A) : (φ (inl c)).right = 1 := by
  have exists_cube (g : G) : ∃ w : A, φ (inl w) ^ 3 = g ^ 3 := by
    obtain ⟨y, rfl⟩ := φ.surjective g
    exact ⟨y.left, by rw [← map_pow, inl_cube, map_pow]⟩
  obtain ⟨u, hu⟩ := exists_cube a
  obtain ⟨v, hv⟩ := exists_cube b
  exact right_eq_one_of_commute_cubes hu hv
    ((commute_of_right_eq_one (right_inl c) (right_inl u)).map φ)
    ((commute_of_right_eq_one (right_inl c) (right_inl v)).map φ)

private theorem x_mul_a : x * a = a ^ 3 * (a * x) := by
  apply SemidirectProduct.ext
  · simp only [cube, x, a, mul_left, left_inl, left_inr, right_inl, right_inr, action_apply]
    rfl
  · simp [x, a, pow_succ]

private theorem a_cube_ne_one : a ^ 3 ≠ 1 := by
  intro h
  have h₁ := congrArg (fun g : G ↦ g.left.toAdd.1) h
  rw [cube] at h₁
  exact (by decide : (3 : R) ≠ 0) h₁

private theorem eq_generator_or_zero :
    ∀ (t : C) (z : R), (t.toAdd.val : R) * (3 * z) = 3 * z →
      t = ofAdd 1 ∨ 3 * z = 0 := by decide

private theorem right_eq_generator_of_relation {g h : G} (hh : h.right = 1)
    (hc : h ^ 3 ≠ 1) (hr : g * h = h ^ 3 * (h * g)) : g.right = ofAdd 1 := by
  have hc₁ : (h ^ 3).right = 1 := by rw [cube, right_inl]
  have e := congrArg (fun z : G ↦ z.left.toAdd) hr
  simp only [mul_left, action_apply, hh, hc₁, scale_one, one_smul,
    toAdd_mul] at e
  change g.left.toAdd + scale g.right • h.left.toAdd =
    (h ^ 3).left.toAdd + (h.left.toAdd + g.left.toAdd) at e
  rw [scale_smul, cube_left, ← add_assoc, add_comm g.left.toAdd,
    add_comm ((3 : R) • h.left.toAdd)] at e
  have ev := add_left_cancel e
  have e₁ : (g.right.toAdd.val : R) * (3 * h.left.toAdd.1) = 3 * h.left.toAdd.1 :=
    congrArg Prod.fst ev
  have e₂ : (g.right.toAdd.val : R) * (3 * h.left.toAdd.2) = 3 * h.left.toAdd.2 :=
    congrArg Prod.snd ev
  rcases eq_generator_or_zero _ _ e₁ with h₁ | h₁
  · exact h₁
  rcases eq_generator_or_zero _ _ e₂ with h₂ | h₂
  · exact h₂
  exfalso
  apply hc
  have hz : (3 : R) • h.left.toAdd = 0 := Prod.ext h₁ h₂
  rw [cube, hz]
  exact map_one inl

private theorem generator_pow : ∀ t : C, (ofAdd (1 : ZMod 3)) ^ t.toAdd.val = t := by
  decide

private theorem map_inr_right (φ : G ≃* G) (t : C) : (φ (inr t)).right = t := by
  have hx : (φ x).right = ofAdd 1 := by
    apply right_eq_generator_of_relation (show (φ a).right = 1 from map_inl_right φ _)
    · rw [← map_pow, ← map_one φ, ne_eq, EmbeddingLike.apply_eq_iff_eq]
      exact a_cube_ne_one
    · simpa only [map_mul, map_pow] using congrArg φ x_mul_a
  have ht : inr t = x ^ t.toAdd.val := by rw [x, ← map_pow, generator_pow]
  change rightHom (φ (inr t)) = t
  rw [ht, map_pow, map_pow, rightHom_eq_right, hx, generator_pow]

private theorem three_smul_scale (t : C) (v : V) :
    (3 : R) • (scale t • v) = (3 : R) • v := by
  calc
    (3 : R) • (scale t • v) = scale t • ((3 : R) • v) := by
      rw [smul_smul, smul_smul, mul_comm (3 : R)]
    _ = (3 : R) • v := by
      rw [scale_smul, smul_smul (3 : R), show (3 : R) * 3 = 0 from by decide,
        zero_smul, smul_zero, add_zero]

private theorem cube_mul (g h : G) : (g * h) ^ 3 = g ^ 3 * h ^ 3 := by
  rw [cube (g * h), cube g, cube h, ← map_mul]
  apply congrArg inl
  change ofAdd ((3 : R) • (g * h).left.toAdd) =
    ofAdd ((3 : R) • g.left.toAdd + (3 : R) • h.left.toAdd)
  apply congrArg ofAdd
  rw [mul_left, toAdd_mul, action_apply]
  change (3 : R) • (g.left.toAdd + scale g.right • h.left.toAdd) = _
  rw [smul_add, three_smul_scale]

private theorem commute_of_right_eq_one_of_cube_eq_one {g : G} (hg : g.right = 1)
    (hc : g ^ 3 = 1) (h : G) : Commute g h := by
  have hz : (3 : R) • g.left.toAdd = 0 := by
    simpa only [cube_left, one_left, toAdd_one] using congrArg (fun z : G ↦ z.left.toAdd) hc
  change g * h = h * g
  apply SemidirectProduct.ext
  · simp only [mul_left, action_apply, hg, scale_one, one_smul]
    rw [scale_smul, hz, smul_zero, add_zero]
    exact mul_comm _ _
  · simp [hg]

private def displacement (φ : G ≃* G) (g : G) : G := g⁻¹ * φ g

private theorem displacement_mul (φ : G ≃* G) (g h : G)
    (hc : Commute (displacement φ g) h) :
    displacement φ (g * h) = displacement φ g * displacement φ h := by
  calc
    displacement φ (g * h) = h⁻¹ * (displacement φ g * h) * displacement φ h := by
      simp [displacement, mul_assoc]
    _ = _ := by rw [hc.eq, inv_mul_cancel_left]

private theorem displacement_inl_right (φ : G ≃* G) (c : A) :
    (displacement φ (inl c)).right = 1 := by
  simp [displacement, map_inl_right]

private theorem commute_displacement_inr (φ : G ≃* G) (t : C) (g : G) :
    Commute (displacement φ (inr t)) g := by
  apply commute_of_right_eq_one_of_cube_eq_one
  · simp [displacement, map_inr_right]
  · simp only [displacement, cube_mul, inv_pow, ← map_pow, cube_right, map_one,
      inv_one, one_mul]

private def displacementHom {K : Type} [Group K] (φ : G ≃* G) (i : K →* G)
    (hi : ∀ u v, Commute (displacement φ (i u)) (i v)) : K →* G where
  toFun u := displacement φ (i u)
  map_one' := by simp [displacement]
  map_mul' u v := by rw [map_mul, displacement_mul φ _ _ (hi u v)]

private theorem all_twisted_unit_classes_subgroups : AllTwistedUnitClassesSubgroups G := by
  intro φ
  let cyclicTwist := displacementHom φ inr (fun t s ↦ commute_displacement_inr φ t (inr s))
  let abelianTwist := displacementHom φ inl (fun c d ↦
    commute_of_right_eq_one (displacement_inl_right φ c) (right_inl d))
  let twist := cyclicTwist.noncommCoprod abelianTwist (fun t c ↦
    commute_displacement_inr φ t (abelianTwist c))
  refine ⟨twist.range, Set.ext fun g ↦ ?_⟩
  change (∃ p : C × A, twist p = g) ↔ ∃ y : G, displacement φ y = g
  have hTwist (t : C) (c : A) : twist (t, c) = displacement φ (inr t * inl c) :=
    (displacement_mul φ _ _ (commute_displacement_inr φ t (inl c))).symm
  constructor
  · rintro ⟨⟨t, c⟩, hp⟩
    exact ⟨inr t * inl c, (hTwist t c).symm.trans hp⟩
  · rintro ⟨y, rfl⟩
    let c := (action y.right)⁻¹ y.left
    have hy : inr y.right * inl c = y := by
      rw [inl_aut_inv, map_inv, mul_assoc (inr y.right)⁻¹, mul_inv_cancel_left,
        inl_left_mul_inr_right]
    exact ⟨(y.right, c), (hTwist _ _).trans (congrArg (displacement φ) hy)⟩

private theorem refuted : ¬ twistedUnitClassesSubgroupsFGImpliesAbelian := by
  intro h
  let _ : Finite G := Finite.of_equiv (A × C) equivProd.symm
  exact a_x_noncommute (h G inferInstance all_twisted_unit_classes_subgroups a x)

end Counterexample

/--
**Negative answer to the abelian assertion of Kourovka Problem 18.14.** There is a finitely
generated group $G$ that is not abelian although, for every automorphism $\varphi$ of $G$, the
twisted conjugacy class of the identity $[e]_\varphi = \{g^{-1}\varphi(g) : g \in G\}$ is a
subgroup of $G$.

Nicotera's Theorem 1.2 gives, for every $n$ and every odd prime $p$, a finite $p$-group of
nilpotency class $n$ with this property; for $n \ge 2$ it is not abelian.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Problem 18.14 (V. G. Bardakov, M. V. Neshchadim, T. R.
Nasybullov); resolution: C. Nicotera, On finite groups in which the twisted conjugacy classes of the
unit element are subgroups, Arch. Math. 123 (2024), no. 3, 225-232, Theorem 1.2 (for every n and
every odd prime p, a finite p-group of class n in which [G, φ] is a subgroup for every φ ∈ Aut G)
and Corollary 3.1 (an infinite non-nilpotent group with this property); the Kourovka Notebook (21st
issue) marks 18.14 solved, https://doi.org/10.1007/s00013-024-02025-6.
-/
theorem twistedUnitClassesSubgroupsFGImpliesAbelian_refuted :
    ¬ twistedUnitClassesSubgroupsFGImpliesAbelian :=
  Counterexample.refuted

end MathlibExt.GroupTheory.TwistedUnitClassSubgroupKourovka18Problem14Wanted
