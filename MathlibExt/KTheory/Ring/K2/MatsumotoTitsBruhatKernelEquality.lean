/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatExtensionCommutation
public import MathlibExt.KTheory.Ring.K2.MatsumotoTitsBruhatRightTransitivity

/-! # Finite-rank Bruhat extension kernel equality

For `2 ≤ n` the kernel of the paired left-extension projection coincides with
the range of the central pair homomorphism.  A kernel element has trivial `SL`
component, preserves `X.fst` fibres, agrees with a central permutation at the
base point `X_one`, and then agrees everywhere by transporting an arbitrary
`x = (centralPerm c' * g) X_one` through the commuting left-extension,
central, and right-action permutations.
-/

@[expose] public section

universe u

namespace MatsumotoTitsBruhatFiber

section KernelEquality

variable (F : Type u) [Field F] (n : ℕ)

private theorem ker_fst_eq_one
    {p : leftExtensionSubgroup F n}
    (hp : p ∈ (leftExtensionProjHom F n).ker) :
    p.val.1 = 1 := by
  have h : leftExtensionProjHom F n p = 1 := (MonoidHom.mem_ker.mp hp)
  simpa [leftExtensionProjHom_apply] using h

private theorem ker_preserves_fst
    {p : leftExtensionSubgroup F n}
    (hp : p ∈ (leftExtensionProjHom F n).ker)
    (x : X F n) :
    X.fst (p.val.2 x) = X.fst x := by
  have hp1 := ker_fst_eq_one (F := F) (n := n) hp
  have hCompat := leftExtension_compat (F := F) (n := n) p.prop x
  rw [hp1, one_mul] at hCompat
  exact hCompat

private theorem centralPerm_central_comm
    (c₁ c₂ : Multiplicative (MilnorK F 2)) :
    Commute (centralPerm (F := F) (n := n) c₁) (centralPerm (F := F) (n := n) c₂) := by
  rw [Commute, SemiconjBy]
  calc centralPerm (F := F) (n := n) c₁ * centralPerm (F := F) (n := n) c₂
      = centralPerm (F := F) (n := n) (c₁ * c₂) := by rw [← centralPerm_mul]
    _ = centralPerm (F := F) (n := n) (c₂ * c₁) := by rw [mul_comm c₁ c₂]
    _ = centralPerm (F := F) (n := n) c₂ * centralPerm (F := F) (n := n) c₁ := by
        rw [centralPerm_mul]

private theorem centralPerm_right_comm
    (c : Multiplicative (MilnorK F 2))
    (g : Equiv.Perm (X F n))
    (hg : g ∈ rightActionSubgroup F n) :
    Commute (centralPerm (F := F) (n := n) c) g := by
  have hMemCentral : centralPerm (F := F) (n := n) c ∈ centralActionSubgroup F n :=
    centralPerm_mem_centralActionSubgroup F c
  have hLe : centralActionSubgroup F n ≤
      Subgroup.centralizer (rightActionSubgroup F n : Set (Equiv.Perm (X F n))) :=
    centralActionSubgroup_le_centralizer_rightActionSubgroup F n
  have hCent : centralPerm (F := F) (n := n) c ∈
      Subgroup.centralizer (rightActionSubgroup F n : Set (Equiv.Perm (X F n))) :=
    hLe hMemCentral
  have hComm : Commute g (centralPerm (F := F) (n := n) c) :=
    (Subgroup.mem_centralizer_iff.mp hCent) g hg
  exact hComm.symm

/-- Kernel elements agree with some central permutation as permutations. -/
theorem exists_centralPerm_eq_of_mem_ker
    (hn : 2 ≤ n)
    (p : leftExtensionSubgroup F n)
    (hp : p ∈ (leftExtensionProjHom F n).ker) :
    ∃ c : Multiplicative (MilnorK F 2), p.val.2 = centralPerm (F := F) (n := n) c := by
  have hp1 := ker_fst_eq_one (F := F) (n := n) hp
  have hPres : ∀ x : X F n, X.fst (p.val.2 x) = X.fst x :=
    fun x => ker_preserves_fst (F := F) (n := n) hp x
  have hFstOne : X.fst (X_one F n) = X.fst (p.val.2 (X_one F n)) := (hPres (X_one F n)).symm
  obtain ⟨c, hc⟩ := central_fiber_exists (x := X_one F n) (y := p.val.2 (X_one F n)) hFstOne
  -- `hc : central c X_one = p.val.2 X_one`, so `p.val.2 X_one = centralPerm c X_one`
  have hpBase : p.val.2 (X_one F n) = centralPerm (F := F) (n := n) c (X_one F n) := by
    calc p.val.2 (X_one F n) = central (F := F) c (X_one F n) := hc.symm
      _ = centralPerm (F := F) (n := n) c (X_one F n) := by
          rw [centralPerm_apply]
  refine ⟨c, ?_⟩
  apply Equiv.ext
  intro x
  obtain ⟨g, hg, c', hx⟩ :=
    rightAction_central_transitive F hn x
  -- `hx : (centralPerm c' * g) X_one = x`
  have hPxEq : p.val.2 x = p.val.2 ((centralPerm (F := F) (n := n) c' * g) (X_one F n)) := by
    rw [hx]
  have hCentralEq : centralPerm (F := F) (n := n) c x =
      centralPerm (F := F) (n := n) c ((centralPerm (F := F) (n := n) c' * g) (X_one F n)) := by
    rw [hx]
  rw [hPxEq, hCentralEq]
  -- commutativity helpers as pointwise equalities
  have hPCommCentral : ∀ (c₀ : Multiplicative (MilnorK F 2)) (y : X F n),
      p.val.2 (centralPerm (F := F) (n := n) c₀ y) =
        centralPerm (F := F) (n := n) c₀ (p.val.2 y) := by
    intro c₀ y
    have hComm : Commute p.val.2 (centralPerm (F := F) (n := n) c₀) :=
      leftExtension_snd_commutes_central F n p c₀
    have hEq : p.val.2 * centralPerm (F := F) (n := n) c₀ =
        centralPerm (F := F) (n := n) c₀ * p.val.2 := hComm.eq
    have hApply := congrArg (fun e : Equiv.Perm (X F n) => e y) hEq
    simp only [Equiv.Perm.mul_apply] at hApply
    exact hApply
  have hPCommRight : ∀ (y : X F n),
      p.val.2 (g y) = g (p.val.2 y) := by
    intro y
    have hComm : Commute p.val.2 g :=
      leftExtension_snd_commutes_rightAction F n p g hg
    have hEq : p.val.2 * g = g * p.val.2 := hComm.eq
    have hApply := congrArg (fun e : Equiv.Perm (X F n) => e y) hEq
    simp only [Equiv.Perm.mul_apply] at hApply
    exact hApply
  have hCentralCommRight : ∀ (y : X F n),
      centralPerm (F := F) (n := n) c (g y) = g (centralPerm (F := F) (n := n) c y) := by
    intro y
    have hComm : Commute (centralPerm (F := F) (n := n) c) g :=
      centralPerm_right_comm (F := F) (n := n) c g hg
    have hEq : centralPerm (F := F) (n := n) c * g = g * centralPerm (F := F) (n := n) c := hComm.eq
    have hApply := congrArg (fun e : Equiv.Perm (X F n) => e y) hEq
    simp only [Equiv.Perm.mul_apply] at hApply
    exact hApply
  have hCentralCommCentral : ∀ (y : X F n),
      centralPerm (F := F) (n := n) c (centralPerm (F := F) (n := n) c' y) =
        centralPerm (F := F) (n := n) c' (centralPerm (F := F) (n := n) c y) := by
    intro y
    have hComm : Commute (centralPerm (F := F) (n := n) c)
        (centralPerm (F := F) (n := n) c') :=
      centralPerm_central_comm (F := F) (n := n) c c'
    have hEq : centralPerm (F := F) (n := n) c * centralPerm (F := F) (n := n) c' =
        centralPerm (F := F) (n := n) c' * centralPerm (F := F) (n := n) c :=
      hComm.eq
    have hApply := congrArg (fun e : Equiv.Perm (X F n) => e y) hEq
    simp only [Equiv.Perm.mul_apply] at hApply
    exact hApply
  -- main pointwise calculation
  calc p.val.2 ((centralPerm (F := F) (n := n) c' * g) (X_one F n))
      = p.val.2 (centralPerm (F := F) (n := n) c' (g (X_one F n))) := by
        simp only [Equiv.Perm.mul_apply]
    _ = centralPerm (F := F) (n := n) c' (p.val.2 (g (X_one F n))) := by
        rw [hPCommCentral c' (g (X_one F n))]
    _ = centralPerm (F := F) (n := n) c' (g (p.val.2 (X_one F n))) := by
        rw [hPCommRight (X_one F n)]
    _ = centralPerm (F := F) (n := n) c' (g (centralPerm (F := F) (n := n) c (X_one F n))) := by
        rw [hpBase]
    _ = centralPerm (F := F) (n := n) c' (centralPerm (F := F) (n := n) c (g (X_one F n))) := by
        rw [← hCentralCommRight (X_one F n)]
    _ = centralPerm (F := F) (n := n) c (centralPerm (F := F) (n := n) c' (g (X_one F n))) := by
        rw [hCentralCommCentral (g (X_one F n))]
    _ = centralPerm (F := F) (n := n) c ((centralPerm (F := F) (n := n) c' * g) (X_one F n)) := by
        simp only [Equiv.Perm.mul_apply]

theorem ker_leftExtensionProjHom_le_range_centralPairHom
    (hn : 2 ≤ n) :
    (leftExtensionProjHom F n).ker ≤ (centralPairHom F n).range := by
  intro p hp
  obtain ⟨c, hcSnd⟩ := exists_centralPerm_eq_of_mem_ker (F := F) (n := n) hn p hp
  have hp1 := ker_fst_eq_one (F := F) (n := n) hp
  have hVal : p.val = (centralPairHom F n c).val := by
    apply Prod.ext
    · simpa [centralPairHom_val] using hp1
    · simpa [centralPairHom_val] using hcSnd
  have hEq : p = centralPairHom F n c := Subtype.ext hVal
  exact MonoidHom.mem_range.mpr ⟨c, hEq.symm ▸ rfl⟩

theorem leftExtensionProjHom_ker_eq_centralPairHom_range
    (hn : 2 ≤ n) :
    (leftExtensionProjHom F n).ker = (centralPairHom F n).range := by
  apply le_antisymm
  · exact ker_leftExtensionProjHom_le_range_centralPairHom (F := F) (n := n) hn
  · exact centralPairHom_range_le_ker_leftExtensionProjHom (F := F) (n := n)

theorem leftExtension_eq_of_proj_eq_of_apply_X_one_eq
    (hn : 2 ≤ n) (p q : leftExtensionSubgroup F n)
    (hProj : leftExtensionProjHom F n p = leftExtensionProjHom F n q)
    (hBase : p.val.2 (X_one F n) = q.val.2 (X_one F n)) : p = q := by
  let r : leftExtensionSubgroup F n := p⁻¹ * q
  have hProjR : leftExtensionProjHom F n r = 1 := by
    calc leftExtensionProjHom F n (p⁻¹ * q)
        = leftExtensionProjHom F n p⁻¹ * leftExtensionProjHom F n q := by
            rw [map_mul]
      _ = (leftExtensionProjHom F n p)⁻¹ * leftExtensionProjHom F n q := by
            rw [map_inv]
      _ = (leftExtensionProjHom F n q)⁻¹ * leftExtensionProjHom F n q := by
            rw [← hProj]
      _ = 1 := by rw [inv_mul_cancel]
  have hMemKer : r ∈ (leftExtensionProjHom F n).ker := by
    rw [MonoidHom.mem_ker]
    exact hProjR
  have hMemRange : r ∈ (centralPairHom F n).range := by
    have hEq : (leftExtensionProjHom F n).ker = (centralPairHom F n).range :=
      leftExtensionProjHom_ker_eq_centralPairHom_range (F := F) (n := n) hn
    rw [← hEq]
    exact hMemKer
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hMemRange
  have hr_eq : r = centralPairHom F n c := hc.symm
  have hRValSnd : r.val.2 = centralPerm (F := F) (n := n) c := by
    have hVal := congrArg Subtype.val hr_eq
    have hSnd := congrArg Prod.snd hVal
    simpa [centralPairHom_val] using hSnd
  have hRFix : r.val.2 (X_one F n) = X_one F n := by
    have hMulSnd : r.val.2 = (p.val.2)⁻¹ * q.val.2 := by
      have hVal : r.val = p.val⁻¹ * q.val := by
        calc r.val = (p⁻¹ * q).val := rfl
          _ = (p⁻¹).val * q.val := by rw [Subgroup.coe_mul]
          _ = (p.val)⁻¹ * q.val := by rw [Subgroup.coe_inv]
      have hSnd := congrArg Prod.snd hVal
      simpa using hSnd
    calc r.val.2 (X_one F n) = ((p.val.2)⁻¹ * q.val.2) (X_one F n) := by rw [hMulSnd]
      _ = (p.val.2)⁻¹ (q.val.2 (X_one F n)) := by rw [Equiv.Perm.mul_apply]
      _ = (p.val.2)⁻¹ (p.val.2 (X_one F n)) := by rw [← hBase]
      _ = X_one F n := by simp
  have hCentralFix : centralPerm (F := F) (n := n) c (X_one F n) = X_one F n := by
    rw [← hRValSnd]
    exact hRFix
  have hCentralEq : central (F := F) (n := n) c (X_one F n) = X_one F n := by
    simpa [centralPerm_apply] using hCentralFix
  have hSndEq : X.snd (central (F := F) (n := n) c (X_one F n)) =
      X.snd (X_one F n) := congrArg X.snd hCentralEq
  have hInl : MatsumotoTitsMonomialExtension.inlHom F n c = 1 := by
    simp [central_snd, X_one_snd] at hSndEq
    simpa using hSndEq
  have hc_one : c = 1 := by
    have hInlEq :
        MatsumotoTitsMonomialExtension.inlHom F n c =
          MatsumotoTitsMonomialExtension.inlHom F n
            (1 : Multiplicative (MilnorK F 2)) := by
      rw [hInl, map_one]
    exact inlHom_injective F n hInlEq
  have hr_one : r = 1 := by
    calc r = centralPairHom F n c := hr_eq
      _ = centralPairHom F n 1 := by rw [hc_one]
      _ = 1 := by rw [map_one]
  have hPQ : p⁻¹ * q = 1 := hr_one
  calc p = p * 1 := by rw [mul_one]
    _ = p * (p⁻¹ * q) := by rw [← hPQ]
    _ = (p * p⁻¹) * q := by rw [mul_assoc]
    _ = 1 * q := by rw [mul_inv_cancel]
    _ = q := by rw [one_mul]

theorem leftExtension_eq_of_proj_eq_of_snd_X_one_eq
    (hn : 2 ≤ n) (p q : leftExtensionSubgroup F n)
    (hProj : leftExtensionProjHom F n p = leftExtensionProjHom F n q)
    (hSnd : X.snd (p.val.2 (X_one F n)) = X.snd (q.val.2 (X_one F n))) : p = q := by
  have hFst : X.fst (p.val.2 (X_one F n)) = X.fst (q.val.2 (X_one F n)) := by
    have hP := leftExtensionProjHom_coe (F := F) (n := n) p (X_one F n)
    have hQ := leftExtensionProjHom_coe (F := F) (n := n) q (X_one F n)
    calc X.fst (p.val.2 (X_one F n)) = leftExtensionProjHom F n p * X.fst (X_one F n) := hP
      _ = leftExtensionProjHom F n p * 1 := by rw [X_one_fst]
      _ = leftExtensionProjHom F n p := by rw [mul_one]
      _ = leftExtensionProjHom F n q := hProj
      _ = leftExtensionProjHom F n q * 1 := by rw [mul_one]
      _ = leftExtensionProjHom F n q * X.fst (X_one F n) := by rw [X_one_fst]
      _ = X.fst (q.val.2 (X_one F n)) := hQ.symm
  have hBase : p.val.2 (X_one F n) = q.val.2 (X_one F n) := X.ext hFst hSnd
  exact leftExtension_eq_of_proj_eq_of_apply_X_one_eq (F := F) (n := n) hn p q hProj hBase

end KernelEquality

end MatsumotoTitsBruhatFiber

end
