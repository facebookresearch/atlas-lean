/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Finite.Perm
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement

/-!
# Surjections that are injective on no nontrivial subgroup (Kourovka Notebook Problem 17.50)

Kourovka Notebook, Archive of Solved Problems, Problem 17.50 (E. G. Zelenyuk): is it true that for
every finite group `G`, there is a finite group `F` and a surjective homomorphism `f : F → G` such
that for each nontrivial subgroup `H` of `F`, the restriction `f|_H` is not injective?

We lift left multiplication on the cosets of each cyclic subgroup of order `d` to permutations
with an additional coordinate modulo `d²`. A generator fixes the identity coset and translates
its coordinate by an integer congruent to one modulo `d`. For `d > 1`, this forces every lift
of that generator to have order greater than `d`.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.50 (E. G.
Zelenyuk). UnsolvedMath record UM-00701352 (`KOU-17.50`), dataset ulamai/UnsolvedMath v1.8.0.

The restriction of `f` to `H` is `f.comp H.subtype`; groups are taken in `Type`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SurjectionNoninjectiveOnSubgroupsKourovka17Problem50Wanted

/-- **Kourovka Problem 17.50: surjections injective on no nontrivial subgroup.** The statement
that for every finite group $G$ there are a finite group $F$ and a surjective homomorphism
$f \colon F \to G$ such that for every nontrivial subgroup $H$ of $F$ the restriction of $f$ to
$H$ is not injective. -/
def surjectionNoninjectiveOnSubgroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ∃ (F : Type) (_ : Group F) (_ : Finite F) (f : F →* G),
    Function.Surjective f ∧ ∀ H : Subgroup F, H ≠ ⊥ → ¬ Function.Injective (f.comp H.subtype)

open Subgroup

variable {G : Type} [Group G]

/-- Over each coset of the cyclic group of order `d`, use a cyclic coordinate of order `d²`. -/
private abbrev Sheets (a : G) := (G ⧸ zpowers a) × ZMod (orderOf a ^ 2)

/-- A lift permutes cosets by left multiplication. Its translation on each sheet records
the power of `a` relating the chosen representatives before and after multiplication. -/
private def IsLift (a g : G) (σ : Equiv.Perm (Sheets a)) : Prop :=
  ∀ q : G ⧸ zpowers a, ∃ k : ℤ, g * q.out = (g • q).out * a ^ k ∧
    ∀ z, σ (q, z) = (g • q, z + k)

private lemma exists_lift (a g : G) : ∃ σ, IsLift a g σ := by
  have hex (q : G ⧸ zpowers a) : ∃ k : ℤ, g * q.out = (g • q).out * a ^ k := by
    have hmem : (g • q).out⁻¹ * (g * q.out) ∈ zpowers a := by
      apply QuotientGroup.eq.mp
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, (eq_inv_mul_iff_mul_eq.mp hk).symm⟩
  choose k hk using hex
  refine ⟨Equiv.prodShear (MulAction.toPerm g) (fun q ↦ Equiv.addRight (k q : ZMod _)), ?_⟩
  exact fun q ↦ ⟨k q, hk q, fun _ ↦ rfl⟩

private lemma isLift_mul {a g h : G} {σ τ : Equiv.Perm (Sheets a)}
    (hσ : IsLift a g σ) (hτ : IsLift a h τ) : IsLift a (g * h) (σ * τ) := by
  intro q
  obtain ⟨i, hi, hτi⟩ := hτ q
  obtain ⟨j, hj, hσj⟩ := hσ (h • q)
  refine ⟨j + i, ?_, ?_⟩
  · rw [mul_smul, mul_assoc, hi, ← mul_assoc, hj, mul_assoc, ← zpow_add]
  · intro z
    rw [Equiv.Perm.mul_apply, hτi, hσj, mul_smul, Int.cast_add]
    congr 1
    ac_rfl

private lemma isLift_inv {a g : G} {σ : Equiv.Perm (Sheets a)}
    (hσ : IsLift a g σ) : IsLift a g⁻¹ σ⁻¹ := by
  intro q
  obtain ⟨k, hk, hσk⟩ := hσ (g⁻¹ • q)
  rw [smul_inv_smul] at hk hσk
  refine ⟨-k, ?_, ?_⟩
  · rw [zpow_neg, eq_mul_inv_iff_mul_eq, mul_assoc, ← hk, inv_mul_cancel_left]
  · intro z
    apply σ.injective
    simp [hσk]

/-- Combine the lifts for every cyclic subgroup generator into a single group over `G`. -/
private def cover (G : Type) [Group G] : Subgroup (G × ((a : G) → Equiv.Perm (Sheets a))) where
  carrier := {w | ∀ a, IsLift a w.1 (w.2 a)}
  one_mem' a q := ⟨0, by simp, by simp⟩
  mul_mem' hx hy a := isLift_mul (hx a) (hy a)
  inv_mem' hx a := isLift_inv (hx a)

private def projection : cover G →* G := (MonoidHom.fst _ _).comp (cover G).subtype

private lemma projection_surjective : Function.Surjective (projection (G := G)) := by
  intro g
  choose σ hσ using fun a : G ↦ exists_lift a g
  exact ⟨⟨(g, σ), hσ⟩, rfl⟩

/-- On a fixed coset, taking powers of a lift iterates a single translation. -/
private lemma pow_on_coset {a : G} {σ : Equiv.Perm (Sheets a)} {q : G ⧸ zpowers a}
    {t : ZMod (orderOf a ^ 2)} (h : ∀ z, σ (q, z) = (q, z + t)) (n : ℕ) (z) :
    (σ ^ n) (q, z) = (q, z + (n : ZMod _) * t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, h, Nat.cast_succ, add_mul, one_mul, add_assoc]

/-- If the order of the image kills a lift, the image is the identity. -/
private lemma image_eq_one_of_pow_eq_one [Finite G] (w : cover G)
    (hw : w ^ orderOf (projection w) = 1) : projection w = 1 := by
  let g := projection w
  let q : G ⧸ zpowers g := QuotientGroup.mk 1
  have hq : g • q = q := by
    apply QuotientGroup.eq.mpr
    simp [smul_eq_mul, mem_zpowers]
  have hm : q.out ∈ zpowers g := by
    simpa using (QuotientGroup.eq.mp (QuotientGroup.out_eq' q).symm :
      (1 : G)⁻¹ * q.out ∈ zpowers g)
  let ρ : cover G →* Equiv.Perm (Sheets g) :=
    (Pi.evalMonoidHom _ g).comp ((MonoidHom.snd _ _).comp (cover G).subtype)
  have hlift : IsLift g g (ρ w) := w.property g
  obtain ⟨k, hk, hσ⟩ := hlift q
  rw [hq] at hk hσ
  have hg : g = g ^ k := by
    have hcomm : Commute g q.out := by
      obtain ⟨i, hi⟩ := hm
      exact hi ▸ (Commute.refl g).zpow_right i
    exact mul_left_cancel (hcomm.eq.symm.trans hk)
  have hpow : ρ w ^ orderOf g = 1 := by rw [← map_pow, hw, map_one]
  -- Writing `d = orderOf g`, the lift translates by `k`, so its `d`th power translates by `d*k`.
  have hzero : (((orderOf g : ℤ) * k : ℤ) : ZMod (orderOf g ^ 2)) = 0 := by
    simpa [hpow] using (congrArg Prod.snd (pow_on_coset hσ (orderOf g) 0)).symm
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  rw [Nat.cast_pow, sq, Int.mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr (orderOf_pos g).ne')]
    at hdvd
  exact hg.trans (orderOf_dvd_iff_zpow_eq_one.mp hdvd)

/--
**Burichenko's theorem on surjections injective on no nontrivial subgroup.** For every finite
group $G$ there are a finite group $F$ and a surjective homomorphism $f \colon F \to G$ such that
for every nontrivial subgroup $H$ of $F$ the restriction of $f$ to $H$ is not injective.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 17.50 (E. G. Zelenyuk); resolution: V. P. Burichenko, Math.
Notes 92 (2012), 327-332, Kourovka Archive, Problem 17.50 (Yes, it is).
-/
theorem surjectionNoninjectiveOnSubgroups_holds : surjectionNoninjectiveOnSubgroups := by
  intro G _ _
  let (a : G) : NeZero (orderOf a) := ⟨(orderOf_pos a).ne'⟩
  refine ⟨cover G, inferInstance, inferInstance, projection, projection_surjective, ?_⟩
  intro H hH hinj
  obtain ⟨h, hne⟩ := ne_bot_iff_exists_ne_one.mp hH
  let f := projection.comp H.subtype
  have hpow : h ^ orderOf (f h) = 1 := by rw [orderOf_injective f hinj, pow_orderOf_eq_one]
  have hg := image_eq_one_of_pow_eq_one (h : cover G) (congrArg H.subtype hpow)
  exact hne (hinj (hg.trans (map_one f).symm))

end MathlibExt.GroupTheory.SurjectionNoninjectiveOnSubgroupsKourovka17Problem50Wanted
