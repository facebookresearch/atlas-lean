/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# LERF solvable groups and Baumslag-Solitar subgroups (Kourovka Notebook Problem 16.2)

Kourovka Notebook, Archive of Solved Problems, Problem 16.2 (R. C. Alperin): a group `G` is
subgroup-separable if for any subgroup `H` and `x ∉ H` there is a homomorphism `f` to a finite group
with `f(x) ∉ f(H)`. Is it true that a finitely generated solvable group is locally
subgroup-separable if and only if it does not contain a solvable Baumslag-Solitar group `BS(1, n) =
⟨a, b | b a b⁻¹ = aⁿ⟩`, `n > 1`?

We prove the negative answer using Button’s action on a rank-two lattice.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.2 (R. C.
Alperin). UnsolvedMath record UM-00701194 (`KOU-16.2`), dataset ulamai/UnsolvedMath v1.8.0.

Locally subgroup-separable is the problem's separability condition for finitely generated subgroups
(LERF), as in the resolving paper: Button states Problem 16.2 as asking whether a finitely generated
solvable group is LERF if and only if it does not contain `BS(1, m)` for `m > 1`. For all subgroups
the condition characterizes the polycyclic groups among finitely generated solvable groups (the
problem's background, Alperin). Containing `BS(1, n)` means having a subgroup isomorphic to it,
stated as an injective homomorphism from the presented group.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SolvableLERFBaumslagSolitarKourovka16Problem2Wanted

/-- **The Baumslag–Solitar group BS(1, n).** For a natural number $n$, $\mathrm{BS}(1, n)$ is the
group with presentation $\langle a, b \mid b a b^{-1} = a^n \rangle$. -/
abbrev BS1 (n : ℕ) : Type :=
  PresentedGroup ({FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0 ^ n)⁻¹} :
    Set (FreeGroup (Fin 2)))

/-- **Separable subgroup.** A subgroup $H$ of a group $G$ is separable when for every element
$x \in G$ with $x \notin H$ there are a finite group $F$ and a group homomorphism
$f \colon G \to F$ with $f(x) \notin f(H)$. -/
def IsSeparableSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ x : G, x ∉ H → ∃ (F : Type) (_ : Group F) (_ : Finite F) (f : G →* F), f x ∉ H.map f

/-- **Locally subgroup-separable (LERF) group.** A group $G$ is locally subgroup-separable, or
LERF, when every finitely generated subgroup of $G$ is separable. -/
def IsLocallySubgroupSeparable (G : Type) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → IsSeparableSubgroup H

/-- **Kourovka Problem 16.2 (R. C. Alperin).** A finitely generated solvable group $G$ is locally
subgroup-separable if and only if there is no $n > 1$ such that $G$ has a subgroup isomorphic to
the Baumslag–Solitar group $\mathrm{BS}(1, n)$. -/
def solvableLERFIffNoBaumslagSolitar : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → Group.IsSolvable G →
    (IsLocallySubgroupSeparable G ↔ ¬ ∃ n : ℕ, 1 < n ∧ ∃ f : BS1 n →* G, Function.Injective f)

open Multiplicative SemidirectProduct

private abbrev K := QuadraticAlgebra ℚ 17 0

private instance nonsquare : Fact (¬ IsSquare (17 : ℚ)) :=
  ⟨by norm_num⟩

private def root : K := ⟨5 / 2, 1 / 2⟩

private theorem root_ne_zero : root ≠ 0 := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  norm_num [root] at him

private def dilation {k : Type} [Field k] (r : kˣ) :
    Multiplicative ℤ →* MulAut (Multiplicative k) :=
  ((MulAutMultiplicative k).symm.toMonoidHom.comp (DistribMulAction.toAddAut kˣ k)).comp
    (zpowersHom _ r)

private abbrev Aff {k : Type} [Field k] (r : kˣ) :=
  Multiplicative k ⋊[dilation r] Multiplicative ℤ

private theorem dilation_apply {k : Type} [Field k] (r : kˣ) (j : Multiplicative ℤ)
    (x : Multiplicative k) : ((dilation r j) x).toAdd = (r : k) ^ j.toAdd * x.toAdd := by
  change (↑(r ^ j.toAdd) : k) * x.toAdd = _
  rw [Units.val_zpow_eq_zpow_val]

private abbrev translation {k : Type} [Field k] {r : kˣ} (x : k) : Aff r := inl (ofAdd x)

private theorem translation_pow {k : Type} [Field k] {r : kˣ} (x : k) (n : ℕ) :
    (translation x : Aff r) ^ n = translation (n * x) := by
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul]

private theorem move_translation {k : Type} [Field k] {r : kˣ} (b : Aff r) (x : k) :
    b * translation x = translation ((r : k) ^ b.right.toAdd * x) * b := by
  apply SemidirectProduct.ext
  · apply toAdd.injective
    change b.left.toAdd + ((dilation r b.right) (ofAdd x)).toAdd = _ + _
    rw [dilation_apply]
    simp [translation, add_comm]
  · simp [translation]

private abbrev scale : Kˣ := Units.mk0 root root_ne_zero

-- In Button's basis, u = 1 and v = (5 - √17)/2. Multiplication by the root
-- sends u to 5u - v and v to 2u.
private def lattice : ℤ × ℤ →+ K where
  toFun p := ⟨p.1 + 5 / 2 * p.2, -(p.2 : ℚ) / 2⟩
  map_zero' := by ext <;> norm_num
  map_add' p q := by ext <;> simp <;> ring

private theorem lattice_injective : Function.Injective lattice := by
  rintro ⟨p, q⟩ ⟨x, y⟩ h
  have him := congrArg QuadraticAlgebra.im h
  have hre := congrArg QuadraticAlgebra.re h
  simp [lattice] at him hre
  subst y
  simpa using hre

private def step : ℤ × ℤ →+ ℤ × ℤ where
  toFun p := (5 * p.1 + 2 * p.2, -p.1)
  map_zero' := by simp
  map_add' p q := by ext <;> simp <;> ring

private theorem root_mul_lattice (p : ℤ × ℤ) : root * lattice p = lattice (step p) := by
  ext <;> simp [lattice, root, step] <;> ring

private abbrev translations : Multiplicative (ℤ × ℤ) →* Aff scale :=
  inl.comp (AddMonoidHom.toMultiplicative lattice)

private abbrev stable : Aff scale := inr (ofAdd 1)

private abbrev witness : Subgroup (Aff scale) := translations.range ⊔ Subgroup.zpowers stable

private abbrev baseMap : Multiplicative (ℤ × ℤ) →* witness :=
  translations.codRestrict witness fun p ↦ (le_sup_left : translations.range ≤ witness) ⟨p, rfl⟩

private abbrev t : witness :=
  ⟨stable, (le_sup_right : Subgroup.zpowers stable ≤ witness) (Subgroup.mem_zpowers _)⟩

private theorem shift (p : Multiplicative (ℤ × ℤ)) :
    t * baseMap p = baseMap (ofAdd (step p.toAdd)) * t := by
  apply Subtype.ext
  change stable * translation (lattice p.toAdd) = translation (lattice (step p.toAdd)) * stable
  rw [move_translation]
  change translation (root ^ (1 : ℤ) * _) * stable = _
  rw [zpow_one, root_mul_lattice]

private theorem witness_fg : Group.FG witness := by
  have : Group.FG (Multiplicative (ℤ × ℤ)) := AddGroup.fg_iff_mul_fg.mp inferInstance
  exact (Group.fg_iff_subgroup_fg _).mpr (Subgroup.FG.sup inferInstance inferInstance)

private theorem witness_solvable : Group.IsSolvable witness := by
  have : Group.IsSolvable (Aff scale) := Group.isSolvable_of_ker_le_range inl rightHom
    range_inl_eq_ker_rightHom.ge
  infer_instance

-- The image of the lattice under conjugation misses u, since (1,0) is not in
-- the image of step. In a finite quotient, conjugation maps the lattice onto itself.
private theorem witness_not_lerf : ¬ IsLocallySubgroupSeparable witness := by
  intro h
  let shifted := baseMap.comp (AddMonoidHom.toMultiplicative step)
  let u := baseMap (ofAdd (1, 0))
  have hu : u ∉ shifted.range := by
    rintro ⟨p, hp⟩
    have he := lattice_injective (congrArg (fun x : witness ↦ x.val.left.toAdd) hp)
    change (5 * p.toAdd.1 + 2 * p.toAdd.2, -p.toAdd.1) = (1, 0) at he
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    dsimp at hfst hsnd
    omega
  have : Group.FG (Multiplicative (ℤ × ℤ)) := AddGroup.fg_iff_mul_fg.mp inferInstance
  obtain ⟨F, _, _, f, hf⟩ := h shifted.range (by infer_instance) u hu
  let B := (f.comp baseMap).range
  have hconj (p : Multiplicative (ℤ × ℤ)) :
      MulAut.conj (f t) (f (baseMap p)) = f (shifted p) := by
    rw [MulAut.conj_apply, ← map_mul, shift, map_mul, mul_inv_cancel_right]
    rfl
  let c : B → B := fun x ↦ ⟨MulAut.conj (f t) x, by
    obtain ⟨p, hp⟩ := x.property
    exact ⟨ofAdd (step p.toAdd), hp ▸ (hconj p).symm⟩⟩
  have hc : Function.Injective c := fun _ _ he ↦ Subtype.ext <|
    (MulAut.conj (f t)).injective (congrArg Subtype.val he)
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hc ⟨f u, ofAdd (1, 0), rfl⟩
  obtain ⟨p, hp⟩ := x.property
  apply hf
  refine ⟨shifted p, ⟨p, rfl⟩, ?_⟩
  exact (hconj p).symm.trans ((congrArg (MulAut.conj (f t)) hp).trans (congrArg Subtype.val hx))

-- Every positive power has positive √17 coefficient, so cannot be rational.
private theorem root_pow_pos (m : ℕ) : 0 < (root ^ (m + 1)).re ∧ 0 < (root ^ (m + 1)).im := by
  induction m with
  | zero => norm_num [root]
  | succ m ih =>
    rw [pow_succ]
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, add_zero]
    change 0 < _ * (5 / 2 : ℚ) + 17 * _ * (1 / 2 : ℚ) ∧
      0 < _ * (1 / 2 : ℚ) + _ * (5 / 2 : ℚ)
    obtain ⟨hre, him⟩ := ih
    constructor <;> positivity

private theorem root_zpow_ne_nat (j : ℤ) {n : ℕ} (hn : 1 < n) : root ^ j ≠ (n : K) := by
  intro h
  cases j with
  | ofNat m =>
    change root ^ m = (n : K) at h
    cases m with
    | zero =>
      have he := congrArg QuadraticAlgebra.re h
      change (root ^ 0).re = (n : ℚ) at he
      rw [pow_zero, QuadraticAlgebra.re_one] at he
      exact (show (1 : ℚ) < n by exact_mod_cast hn).ne he
    | succ m =>
      have him := (root_pow_pos m).2
      rw [h] at him
      exact lt_irrefl _ him
  | negSucc m =>
    rw [zpow_negSucc] at h
    have he := inv_mul_cancel₀ (pow_ne_zero (m + 1) root_ne_zero)
    rw [h] at he
    have him := congrArg QuadraticAlgebra.im he
    simp [QuadraticAlgebra.im_one, QuadraticAlgebra.im_natCast, QuadraticAlgebra.re_natCast] at him
    exact (root_pow_pos m).2.ne' (him.resolve_left (by omega))

private theorem relation_forces_one {a b : Aff scale} {n : ℕ} (hn : 1 < n)
    (h : b * a = a ^ n * b) : a = 1 := by
  have he := congrArg (fun g : Aff scale ↦ (rightHom g).toAdd) h
  simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul] at he
  have hj : (rightHom a).toAdd = 0 := by
    have hz : ((n : ℤ) - 1) * (rightHom a).toAdd = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left (by omega)
  have ha : a = translation a.left.toAdd := SemidirectProduct.ext rfl (congrArg ofAdd hj)
  rw [ha, move_translation, translation_pow, mul_right_cancel_iff] at h
  have heq := congrArg (fun g : Aff scale ↦ g.left.toAdd) h
  change root ^ b.right.toAdd * a.left.toAdd = (n : K) * a.left.toAdd at heq
  have hz := (mul_eq_mul_right_iff.mp heq).resolve_left (root_zpow_ne_nat _ hn)
  rw [ha, hz]
  rfl

private theorem bs_relation (n : ℕ) :
    (PresentedGroup.of 1 : BS1 n) * PresentedGroup.of 0 =
      (PresentedGroup.of 0) ^ n * PresentedGroup.of 1 := by
  apply eq_mul_of_mul_inv_eq
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem
    (x := FreeGroup.of (1 : Fin 2) * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹)
    (y := FreeGroup.of 0 ^ n) (Set.mem_singleton _)
  simpa only [map_mul, map_inv, map_pow, PresentedGroup.of] using h

-- The base generator of the presented group acts as a nonidentity translation on ℚ.
private theorem bs_generator_ne_one {n : ℕ} (hn : 1 < n) : (PresentedGroup.of 0 : BS1 n) ≠ 1 := by
  let r : ℚˣ := Units.mk0 n (by exact_mod_cast (show n ≠ 0 by omega))
  let gen : Fin 2 → Aff r := fun i ↦ if i = 0 then translation 1 else inr (ofAdd 1)
  have hrel : inr (ofAdd 1) * translation 1 = (translation 1 : Aff r) ^ n * inr (ofAdd 1) := by
    rw [move_translation, translation_pow]
    change translation ((n : ℚ) ^ (1 : ℤ) * 1) * _ = _
    simp
  let rep : BS1 n →* Aff r := PresentedGroup.toGroup (f := gen) (by
    rintro _ rfl
    simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of]
    simp [gen, hrel, mul_assoc])
  intro he
  have he' := congrArg (fun x ↦ (rep x).left.toAdd) he
  simp [rep, gen, translation] at he'

private theorem witness_no_bs {n : ℕ} (hn : 1 < n) (f : BS1 n →* witness) :
    ¬ Function.Injective f := by
  intro hi
  let g := witness.subtype.comp f
  have h := congrArg g (bs_relation n)
  simp only [map_mul, map_pow] at h
  apply bs_generator_ne_one hn
  apply hi
  apply witness.subtype_injective
  simpa [g] using relation_forces_one hn h

/--
**Kourovka Problem 16.2 has a negative answer.** There is a finitely generated solvable group $G$
for which the following two conditions are not equivalent: $G$ is locally subgroup-separable;
there is no $n > 1$ such that $G$ has a subgroup isomorphic to the Baumslag–Solitar group
$\mathrm{BS}(1, n)$.

Button's counterexample is the solvable ascending HNN extension of
$\mathbb{Z} \times \mathbb{Z} = \langle u, v \rangle$ by the injective endomorphism
$u \mapsto u^5 v^{-1}$, $v \mapsto u^2$: it is not locally subgroup-separable but contains no
$\mathrm{BS}(1, m)$ with $m \ne 0, \pm 1$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.2 (R. C.
Alperin); resolution: J. O. Button, Strictly ascending HNN extensions in soluble groups, Ricerche
di Matematica 61 (2012), no. 1, 139-145, arXiv:1004.0197, Theorem 2.1 and the remark after it
(the soluble ascending HNN extension G = ⟨t, ℤ × ℤ⟩ with θ(u) = u⁵v⁻¹, θ(v) = u² is not LERF and
contains no BS(1, m), m ≠ 0, ±1, so the answer to Problem 16.2 is no); Kourovka Archive, Problem
16.2 (No, it is not), https://arxiv.org/abs/1004.0197.
-/
theorem solvableLERFIffNoBaumslagSolitar_refuted : ¬ solvableLERFIffNoBaumslagSolitar := by
  intro h
  apply witness_not_lerf ((h witness witness_fg witness_solvable).2 ?_)
  rintro ⟨n, hn, f, hf⟩
  exact witness_no_bs hn f hf

end MathlibExt.GroupTheory.SolvableLERFBaumslagSolitarKourovka16Problem2Wanted
