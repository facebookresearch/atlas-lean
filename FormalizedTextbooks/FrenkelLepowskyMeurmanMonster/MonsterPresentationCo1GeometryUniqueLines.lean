/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Source II section 5.1: every genuine collinearity edge lies on exactly one original line. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLineBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryConnected

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Two given actual Conway points determine at most one third point on a genuine source line. -/
theorem monsterCo1GeometryLine_third_unique (p q r s : MonsterCo1GeometryPoint)
    (hr : monsterCo1GeometryLine p q r) (hs : monsterCo1GeometryLine p q s) : r = s := by
  apply Subtype.ext
  have h : (p.val + q.val) + r.val = (p.val + q.val) + s.val :=
    (monsterCo1GeometryLine_binary p q r hr).trans (monsterCo1GeometryLine_binary p q s hs).symm
  exact add_left_cancel h

/-- Every actual adjacency edge has exactly one original genuine line through its two points. -/
theorem monsterCo1GeometryAdjacent_unique_line (p q : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryAdjacent p q) : ∃! r, monsterCo1GeometryLine p q r := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr, fun s hs => monsterCo1GeometryLine_third_unique p q s r hs hr⟩

/-- Genuine adjacency has no loops because every original line has distinct points. -/
theorem monsterCo1GeometryAdjacent_irrefl (p : MonsterCo1GeometryPoint) :
    ¬ monsterCo1GeometryAdjacent p p := by
  rintro ⟨r, hr⟩
  rcases hr with hp | hp | hr
  · exact hp.1 rfl
  · exact hp.1 rfl
  · exact hr.2.2.1 rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
