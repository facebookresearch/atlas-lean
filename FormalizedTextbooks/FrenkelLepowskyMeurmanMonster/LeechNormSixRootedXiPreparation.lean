/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixOutsideCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2XiTransport

/-! Genuine monomial preparation of norm-six vectors at the Xi-fixed positive root. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem integral_sign_of_magnitude (x y : ℤ) (h : x.natAbs = y.natAbs) :
    (if (if x = y then (0 : ZMod 2) else 1) = 0 then x else -x) = y := by
  by_cases he : x = y
  · simp [he]
  · have hn : x = -y := (Int.natAbs_eq_natAbs_iff.mp h).resolve_left he
    simp [hn]

/-- Four genuine coordinate and sign choices normalize the root and the two outside entries
at once, retaining the original two root entries with their required signs. -/
theorem leechNormSix_rooted_xi_preparation (u : leechIntegral) (i j : Fin 24)
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hij : i ≠ j)
    (a z : ℤ) (hia : (u.val i).natAbs = a.natAbs) (hjz : (u.val j).natAbs = z.natAbs) :
    ∃ b : leechIsomSubgroup, b ∈ golayMonomialSubgroup ∧
      leechIntegralAction b leechRootedA2Root = leechRootedA2XiRoot ∧
      (leechIntegralAction b u).val 0 = a ∧
      (leechIntegralAction b u).val 1 = u.val 0 ∧
      (leechIntegralAction b u).val 2 = -u.val 1 ∧
      (leechIntegralAction b u).val 3 = z := by
  obtain ⟨p, hp⟩ := golayAutomorphism_four_transitive ![0, 1, i, j] ![1, 2, 0, 3]
    (by intro x y h; fin_cases x <;> fin_cases y <;> simp_all)
    (by decide +kernel)
  have hp0 : p.val 0 = 1 := by simpa using hp 0
  have hp1 : p.val 1 = 2 := by simpa using hp 1
  have hpi : p.val i = 0 := by simpa using hp 2
  have hpj : p.val j = 3 := by simpa using hp 3
  let bits : Fin 4 → ZMod 2 :=
    ![if u.val i = a then 0 else 1, 0, 1, if u.val j = z then 0 else 1]
  obtain ⟨d, hd⟩ := golayCode_four_coordinate_surjective
    (fun k : Fin 4 => Fin.castAdd 20 k)
    (by intro x y h; exact Fin.ext (congrArg (fun k : Fin 24 => k.val) h)) bits
  have hd0 : d.val 0 = if u.val i = a then 0 else 1 := by simpa [bits] using congrFun hd 0
  have hd1 : d.val 1 = 0 := by simpa [bits] using congrFun hd 1
  have hd2 : d.val 2 = 1 := by simpa [bits] using congrFun hd 2
  have hd3 : d.val 3 = if u.val j = z then 0 else 1 := by simpa [bits] using congrFun hd 3
  let b := golaySignIsometry d * golayPermutationIsometry p
  have hroot : leechIntegralAction b leechRootedA2Root = leechRootedA2XiRoot := by
    apply Subtype.ext
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation]
    funext k
    have h0 : p.val.symm k = 0 ↔ k = 1 := by rw [p.val.symm_apply_eq, hp0]
    have h1 : p.val.symm k = 1 ↔ k = 2 := by rw [p.val.symm_apply_eq, hp1]
    simp only [golayIntegerSign, golayIntegerPermute, leechRootedA2Root,
      leechRootedA2RootIntegral, h0, h1, leechRootedA2XiRoot]
    by_cases hk1 : k = 1
    · subst k
      simp [hd1]
    · by_cases hk2 : k = 2
      · subst k
        simp [hd2]
      · simp [hk1, hk2]
  have hval (k : Fin 24) : (leechIntegralAction b u).val k =
      if d.val k = 0 then u.val (p.val.symm k) else -u.val (p.val.symm k) := by
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation]
    rfl
  refine ⟨b, ⟨d, p, rfl⟩, hroot, ?_, ?_, ?_, ?_⟩
  · have hs : p.val.symm 0 = i := p.val.symm_apply_eq.mpr hpi.symm
    rw [hval, hs, hd0]
    exact integral_sign_of_magnitude _ _ hia
  · have hs : p.val.symm 1 = 0 := p.val.symm_apply_eq.mpr hp0.symm
    rw [hval, hs, hd1]
    simp
  · have hs : p.val.symm 2 = 1 := p.val.symm_apply_eq.mpr hp1.symm
    rw [hval, hs, hd2]
    simp
  · have hs : p.val.symm 3 = j := p.val.symm_apply_eq.mpr hpj.symm
    rw [hval, hs, hd3]
    exact integral_sign_of_magnitude _ _ hjz

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
