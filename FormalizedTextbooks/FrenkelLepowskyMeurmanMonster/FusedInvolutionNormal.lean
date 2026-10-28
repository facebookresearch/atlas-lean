/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The fused Klein four in the actual generated group detects nontrivial normal
subgroups through the centralizer of its distinguished involution. This is a
normal-subgroup prerequisite for Conway's centralizer recognition argument;
it does not assume the recognition theorem or assert simplicity.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralInvolution
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFiniteness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityFullProduct
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.GroupAction.ConjAct

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

section FusedInvolutions
variable {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]

private theorem conjNormal_fixedPointFree_of_inf_centralizer
    (x : Γ) (h : N ⊓ Subgroup.centralizer {x} = ⊥) :
    MonoidHom.FixedPointFree (MulAut.conjNormal (H := N) x) := by
  intro n hn
  have he := congrArg Subtype.val hn
  rw [MulAut.conjNormal_apply] at he
  have hm : n.val ∈ N ⊓ Subgroup.centralizer {x} :=
    ⟨n.property, Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm⟩
  rw [h] at hm
  exact Subtype.ext (Subgroup.mem_bot.mp hm)

private theorem conjNormal_fixedPointFree_conjugate
    (x g : Γ) (hx : MonoidHom.FixedPointFree (MulAut.conjNormal (H := N) x)) :
    MonoidHom.FixedPointFree (MulAut.conjNormal (H := N) (g * x * g⁻¹)) := by
  let a := MulAut.conjNormal (H := N) x
  let b := MulAut.conjNormal (H := N) g
  intro n hn
  have he : b (a (b.symm n)) = n := by
    simpa only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply] using hn
  have hf : a (b.symm n) = b.symm n := by
    apply b.injective
    simpa only [MulEquiv.apply_symm_apply] using he
  have hz := hx (b.symm n) hf
  have hz' := congrArg b hz
  simpa only [MulEquiv.apply_symm_apply, map_one] using hz'

/-- The three nonidentity elements of a fused Klein four force a finite normal
subgroup with trivial intersection with one centralizer to be trivial. -/
theorem normal_eq_bot_of_fused_involutions
    [Finite Γ]
    (x : Fin 3 → Γ) (hsquare : ∀ k, x k * x k = 1)
    (hproduct : x 0 * x 1 = x 2)
    (hfused : ∀ k, ∃ g, g * x 0 * g⁻¹ = x k)
    (hcentral : N ⊓ Subgroup.centralizer {x 0} = ⊥) : N = ⊥ := by
  have hfree (k : Fin 3) :
      MonoidHom.FixedPointFree (MulAut.conjNormal (H := N) (x k)) := by
    obtain ⟨g, hg⟩ := hfused k
    rw [← hg]
    exact conjNormal_fixedPointFree_conjugate N (x 0) g
      (conjNormal_fixedPointFree_of_inf_centralizer N (x 0) hcentral)
  have hinverse (k : Fin 3) (n : N) : MulAut.conjNormal (H := N) (x k) n = n⁻¹ := by
    have hs : MulAut.conjNormal (H := N) (x k) *
        MulAut.conjNormal (H := N) (x k) = 1 := by
      rw [← map_mul, hsquare, map_one]
    have hi : Function.Involutive (MulAut.conjNormal (H := N) (x k)) := by
      intro n
      change (MulAut.conjNormal (H := N) (x k) *
        MulAut.conjNormal (H := N) (x k)) n = n
      rw [hs]
      rfl
    exact congrFun ((hfree k).coe_eq_inv_of_involutive hi) n
  apply bot_unique
  intro n hn
  let u : N := ⟨n, hn⟩
  have hu : MulAut.conjNormal (H := N) (x 2) u = u := by
    rw [← hproduct, map_mul, MulAut.mul_apply, hinverse, hinverse, inv_inv]
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hfree 2 u hu))

end FusedInvolutions

/-- The three actual dictionary sign involutions, as elements of G. -/
noncomputable def generatedTrialityCentralSign (k : Fin 3) : G :=
  ⟨trialityCentralSign k, trialityCentralSign_mem_G k⟩

theorem generatedTrialityCentralSign_zero :
    generatedTrialityCentralSign 0 = qIntoGenerated qCentralInvolution := by
  apply Subtype.ext
  exact localCentralGriess_eq_trialityCentralSign.symm

/-- Every nontrivial normal subgroup of the actual finite generated group has
a nontrivial intersection with the actual central involution centralizer. -/
theorem generated_normal_eq_bot_of_inf_centralizer_eq_bot
    (N : Subgroup G) [N.Normal]
    (h : N ⊓ Subgroup.centralizer {qIntoGenerated qCentralInvolution} = ⊥) : N = ⊥ := by
  let : Finite G := generated_group_finite_of_triality_product sExtra_preserves_griessProd
  apply normal_eq_bot_of_fused_involutions N generatedTrialityCentralSign
  · intro k
    exact Subtype.ext (trialityCentralSign_square k)
  · exact Subtype.ext trialityCentralSign_zero_mul_one
  · intro k
    let t : G := ⟨sExtra, sExtra_mem_generated_G⟩
    fin_cases k
    · refine ⟨1, ?_⟩
      simp
    · refine ⟨t, ?_⟩
      apply Subtype.ext
      change sExtra * trialityCentralSign 0 * sExtra⁻¹ = trialityCentralSign 1
      rw [← localCentralGriess_eq_trialityCentralSign]
      exact localCentralGriess_conjugate
    · refine ⟨t ^ 2, ?_⟩
      apply Subtype.ext
      change sExtra ^ 2 * trialityCentralSign 0 * (sExtra ^ 2)⁻¹ = trialityCentralSign 2
      rw [← localCentralGriess_eq_trialityCentralSign]
      exact localCentralGriess_conjugate_square
  · simpa only [generatedTrialityCentralSign_zero] using h

/-- A nontrivial normal subgroup meets the distinguished involution centralizer
nontrivially, before any identification of that centralizer with H. -/
theorem generated_normal_inf_centralizer_ne_bot
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    N ⊓ Subgroup.centralizer {qIntoGenerated qCentralInvolution} ≠ ⊥ := by
  intro h
  exact hN (generated_normal_eq_bot_of_inf_centralizer_eq_bot N h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
