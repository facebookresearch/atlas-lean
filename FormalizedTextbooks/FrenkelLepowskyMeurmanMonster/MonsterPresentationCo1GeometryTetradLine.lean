/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A genuine source Conway line from the intrinsic two-core orbit of an actual Xi frame. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryTetradPoints
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLines
public import Mathlib.Tactic.Abel

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The genuine base-point two-core orbit has only the two specified actual binary values. -/
theorem monsterCo1GeometryTetradPoint_orbit_values (q : MonsterCo1GeometryPoint)
    (hq : q ∈ MulAction.orbit (monsterCo1GeometryPointTwoCore monsterCo1GeometryBasePoint)
      monsterCo1GeometryTetradPoint) :
    q = monsterCo1GeometryTetradPoint ∨
      q.val = monsterCo1GeometryTetradPoint.val + monsterCo1GeometryBasePoint.val := by
  obtain ⟨g, hg⟩ := hq
  change g.val • monsterCo1GeometryTetradPoint = q at hg
  have hcore : g.val ∈ monsterCo1GeometrySignClassHom.range :=
    monsterCo1GeometryBasePoint_twoCore.le g.property
  obtain ⟨d, hd⟩ := hcore
  have hv := monsterCo1GeometryTetradPoint_sign (Multiplicative.toAdd d)
  simp only [ofAdd_toAdd] at hv
  rw [hd, hg] at hv
  have hscalar : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
  rcases hscalar (monsterCo1GeometryTetradParity (Multiplicative.toAdd d)) with hzero | hone
  · left
    apply Subtype.ext
    simpa only [hzero, zero_smul, add_zero] using hv
  · right
    simpa only [hone, one_smul] using hv

/-- A genuine odd-tetrad code sign constructs the second actual point in the two-element orbit. -/
theorem monsterCo1GeometryTetradLine_exists :
    ∃ r : MonsterCo1GeometryPoint,
      monsterCo1GeometryAnchoredLine monsterCo1GeometryBasePoint monsterCo1GeometryTetradPoint r ∧
      monsterCo1GeometryBasePoint.val + monsterCo1GeometryTetradPoint.val + r.val = 0 := by
  obtain ⟨d, hd⟩ := monsterCo1GeometryTetradParity_exists_one
  let r : MonsterCo1GeometryPoint :=
    monsterCo1GeometrySignClassHom (Multiplicative.ofAdd d) • monsterCo1GeometryTetradPoint
  have hr : r.val = monsterCo1GeometryTetradPoint.val + monsterCo1GeometryBasePoint.val := by
    simpa only [hd, one_smul] using monsterCo1GeometryTetradPoint_sign d
  have hry : r ≠ monsterCo1GeometryTetradPoint := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hr] at hv
    exact monsterCo1GeometryPoint_ne_zero monsterCo1GeometryBasePoint
      (add_left_cancel (hv.trans (add_zero _).symm))
  have hrp : r ≠ monsterCo1GeometryBasePoint := by
    intro h
    have hv := congrArg Subtype.val h
    rw [hr] at hv
    exact monsterCo1GeometryPoint_ne_zero monsterCo1GeometryTetradPoint
      (add_right_cancel (hv.trans (zero_add _).symm))
  have horbit : MulAction.orbit
      (monsterCo1GeometryPointTwoCore monsterCo1GeometryBasePoint) monsterCo1GeometryTetradPoint =
        {monsterCo1GeometryTetradPoint, r} := by
    ext q
    constructor
    · intro hq
      rcases monsterCo1GeometryTetradPoint_orbit_values q hq with hy | hv
      · rw [hy]
        exact Set.mem_insert _ _
      · have he : q = r := Subtype.ext (hv.trans hr.symm)
        rw [he]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton r)
    · intro hq
      rcases Set.mem_insert_iff.mp hq with hy | hrq
      · rw [hy]
        exact MulAction.mem_orbit_self _
      · have he : q = r := Set.mem_singleton_iff.mp hrq
        rw [he]
        let g : monsterCo1GeometryPointTwoCore monsterCo1GeometryBasePoint :=
          ⟨monsterCo1GeometrySignClassHom (Multiplicative.ofAdd d),
            monsterCo1GeometryBasePoint_twoCore.ge ⟨Multiplicative.ofAdd d, rfl⟩⟩
        exact ⟨g, rfl⟩
  refine ⟨r, ⟨monsterCo1GeometryTetradPoint_ne_base.symm, hrp.symm, hry.symm, horbit⟩, ?_⟩
  have hdouble (v : Fin 24 → ZMod 2) : v + v = 0 := by
    ext i
    have h : ∀ a : ZMod 2, a + a = 0 := by decide +kernel
    exact h (v i)
  rw [hr]
  calc
    _ = (monsterCo1GeometryBasePoint.val + monsterCo1GeometryBasePoint.val) +
      (monsterCo1GeometryTetradPoint.val + monsterCo1GeometryTetradPoint.val) := by abel
    _ = 0 := by rw [hdouble, hdouble, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
