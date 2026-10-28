/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Every original genuine two-orbit Conway line has binary sum zero. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignFixedData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLineAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBaseCoordinates
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Pi

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The intrinsic base-point two-core fixes only the actual base line in the binary module. -/
theorem monsterCo1GeometryBaseTwoCore_fixed (v : Fin 24 → ZMod 2)
    (h : ∀ g : monsterCo1GeometryPointTwoCore monsterCo1GeometryBasePoint,
      co1BinaryAction g.val v = v) :
    v = v 11 • monsterCo1GeometryBasePoint.val := by
  rw [monsterCo1GeometryBasePoint_binary]
  apply monsterCo1GeometrySignFixed_vector
  intro k
  have hk := h ⟨QuotientGroup.mk (monsterCo1GeometrySignIsometry k),
    monsterCo1GeometrySign_mem_baseTwoCore k⟩
  rw [monsterCo1GeometrySign_binary] at hk
  exact hk

/-- A genuine base-point two-orbit line has its original binary line sum equal to zero. -/
theorem monsterCo1GeometryBaseAnchoredLine_binary (q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryAnchoredLine monsterCo1GeometryBasePoint q r) :
    monsterCo1GeometryBasePoint.val + q.val + r.val = 0 := by
  have hv : q.val + r.val = (q.val + r.val) 11 • monsterCo1GeometryBasePoint.val := by
    apply monsterCo1GeometryBaseTwoCore_fixed
    intro g
    have hq : g.val • q = q ∨ g.val • q = r := by
      have hh : g.val • q ∈ MulAction.orbit
          (monsterCo1GeometryPointTwoCore monsterCo1GeometryBasePoint) q := ⟨g, rfl⟩
      simpa only [h.2.2.2, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
    have hr : g.val • r = q ∨ g.val • r = r := by
      obtain ⟨k, hk⟩ := monsterCo1GeometryAnchoredLine_transport _ q r h
      change k.val • q = r at hk
      have hh : g.val • r ∈ MulAction.orbit
          (monsterCo1GeometryPointTwoCore monsterCo1GeometryBasePoint) q := by
        refine ⟨g * k, ?_⟩
        change (g.val * k.val) • q = g.val • r
        rw [mul_smul]
        exact congrArg (fun x => g.val • x) hk
      simpa only [h.2.2.2, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
    have hinj : Function.Injective (fun p : MonsterCo1GeometryPoint => g.val • p) :=
      MulAction.injective g.val
    rw [map_add]
    rcases hq with hq | hq <;> rcases hr with hr | hr
    · exact False.elim (h.2.2.1 (hinj (hq.trans hr.symm)))
    · exact congrArg₂ (fun x y : MonsterCo1GeometryPoint => x.val + y.val) hq hr
    · exact (congrArg₂ (fun x y : MonsterCo1GeometryPoint => x.val + y.val) hq hr).trans
        (add_comm _ _)
    · exact False.elim (h.2.2.1 (hinj (hq.trans hr.symm)))
  have hn : (q.val + r.val) 11 ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hv
    exact h.2.2.1 (Subtype.ext (CharTwo.add_eq_zero.mp hv))
  have hs : (q.val + r.val) 11 = 1 := by
    have ht : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    exact (ht _).resolve_left hn
  rw [hs, one_smul] at hv
  rw [add_assoc, hv]
  exact CharTwo.add_self_eq_zero _

/-- Every anchored original Conway line has binary sum zero, by actual point transport. -/
theorem monsterCo1GeometryAnchoredLine_binary (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryAnchoredLine p q r) : p.val + q.val + r.val = 0 := by
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached p
  have hb : monsterCo1GeometryAnchoredLine monsterCo1GeometryBasePoint (g⁻¹ • q) (g⁻¹ • r) := by
    have hh := monsterCo1GeometryAnchoredLine_smul g⁻¹ p q r h
    simpa only [← hg, inv_smul_smul] using hh
  have hz := monsterCo1GeometryBaseAnchoredLine_binary (g⁻¹ • q) (g⁻¹ • r) hb
  have he := congrArg (co1BinaryAction g) hz
  rw [map_add, map_add, map_zero] at he
  change (g • monsterCo1GeometryBasePoint).val + (g • (g⁻¹ • q)).val +
    (g • (g⁻¹ • r)).val = 0 at he
  simpa only [hg, smul_inv_smul] using he

/-- Every unordered genuine source line has its binary sum zero in the actual Leech module. -/
theorem monsterCo1GeometryLine_binary (p q r : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine p q r) : p.val + q.val + r.val = 0 := by
  rcases h with hp | hq | hr
  · exact monsterCo1GeometryAnchoredLine_binary p q r hp
  · simpa only [add_comm p.val q.val] using monsterCo1GeometryAnchoredLine_binary q p r hq
  · have hh := monsterCo1GeometryAnchoredLine_binary r p q hr
    simpa only [add_assoc, add_comm, add_left_comm] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
