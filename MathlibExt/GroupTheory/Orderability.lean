/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `e4e4de3e175eab51e689706fcab2456068d90482`.

Original formalization by Metamate
(introduced in commit `f204b2a6`, PR #9859); ported with attribution.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

@[expose] public section

namespace MathlibExt.GroupTheory

universe u

/-- A linear order on a group is bi-invariant if multiplication on either side preserves it. -/
def IsBiInvariantOrder {G : Type u} [Group G] (o : LinearOrder G) : Prop :=
  ∀ a b : G, o.le a b → ∀ c : G, o.le (c * a) (c * b) ∧ o.le (a * c) (b * c)

/-- Characterize a bi-invariant order by monotonicity of left and right multiplication. -/
theorem isBiInvariantOrder_iff {G : Type u} [Group G] (o : LinearOrder G) :
    IsBiInvariantOrder o ↔
      (∀ c a b : G, o.le a b → o.le (c * a) (c * b)) ∧
      ∀ c a b : G, o.le a b → o.le (a * c) (b * c) := by
  constructor
  · intro h
    exact ⟨fun c a b hab => (h a b hab c).1, fun c a b hab => (h a b hab c).2⟩
  · rintro ⟨hl, hr⟩ a b hab c
    exact ⟨hl c a b hab, hr c a b hab⟩

/-- A linear order is bi-invariant exactly when multiplication is monotone on both sides in
Mathlib's standard covariant-class formulation. -/
theorem isBiInvariantOrder_iff_mulLeftMono_mulRightMono {G : Type u} [Group G]
    (o : LinearOrder G) :
    IsBiInvariantOrder o ↔ (letI := o; MulLeftMono G ∧ MulRightMono G) := by
  constructor
  · intro h
    let _ := o
    exact ⟨⟨fun c a b hab => (h a b hab c).1⟩, ⟨fun c a b hab => (h a b hab c).2⟩⟩
  · intro h
    let _ := o
    intro a b hab c
    exact ⟨h.1.elim c hab, h.2.elim c hab⟩

/-- Left multiplication preserves a bi-invariant order. -/
theorem IsBiInvariantOrder.mul_le_mul_left {G : Type u} [Group G] {o : LinearOrder G}
    (h : IsBiInvariantOrder o) {a b : G} (hab : o.le a b) (c : G) :
    o.le (c * a) (c * b) :=
  (h a b hab c).1

/-- Right multiplication preserves a bi-invariant order. -/
theorem IsBiInvariantOrder.mul_le_mul_right {G : Type u} [Group G] {o : LinearOrder G}
    (h : IsBiInvariantOrder o) {a b : G} (hab : o.le a b) (c : G) :
    o.le (a * c) (b * c) :=
  (h a b hab c).2

/-- Multiply two inequalities in a bi-invariant order. -/
theorem IsBiInvariantOrder.mul_le_mul {G : Type u} [Group G] {o : LinearOrder G}
    (h : IsBiInvariantOrder o) {a b c d : G} (hab : o.le a b) (hcd : o.le c d) :
    o.le (a * c) (b * d) :=
  o.le_trans (a * c) (b * c) (b * d) (h.mul_le_mul_right hab c) (h.mul_le_mul_left hcd b)

/-- A group is orderable if it admits a bi-invariant linear order. -/
def IsOrderable (G : Type u) [Group G] : Prop :=
  ∃ o : LinearOrder G, IsBiInvariantOrder o

/-- Characterize group orderability by a bi-invariant linear-order witness. -/
theorem isOrderable_iff (G : Type u) [Group G] :
    IsOrderable G ↔ ∃ o : LinearOrder G, IsBiInvariantOrder o :=
  Iff.rfl

/-- Construct an orderability witness. -/
theorem IsOrderable.intro {G : Type u} [Group G] (o : LinearOrder G)
    (h : IsBiInvariantOrder o) : IsOrderable G :=
  ⟨o, h⟩

/-- Eliminate an orderability witness without unfolding `IsOrderable`. -/
theorem IsOrderable.elim {G : Type u} [Group G] {P : Prop} (h : IsOrderable G)
    (k : ∀ o : LinearOrder G, IsBiInvariantOrder o → P) : P :=
  Exists.elim h k

/-- Characterize group orderability using Mathlib's standard multiplication-monotonicity classes. -/
theorem isOrderable_iff_exists_mulLeftMono_mulRightMono (G : Type u) [Group G] :
    IsOrderable G ↔
      ∃ o : LinearOrder G, letI := o; MulLeftMono G ∧ MulRightMono G := by
  constructor
  · exact fun h => h.elim fun o ho => ⟨o, (isBiInvariantOrder_iff_mulLeftMono_mulRightMono o).mp ho⟩
  · rintro ⟨o, ho⟩
    exact IsOrderable.intro o (isBiInvariantOrder_iff_mulLeftMono_mulRightMono o |>.mpr ho)

/-- A subgroup is relatively convex if it is convex above the identity for some bi-invariant
linear order of the ambient group. -/
def IsRelativelyConvex {G : Type u} [Group G] (H : Subgroup G) : Prop :=
  ∃ o : LinearOrder G, IsBiInvariantOrder o ∧
    ∀ h ∈ H, ∀ g : G, o.le 1 g → o.le g h → g ∈ H

/-- Characterize relative convexity by its witnessing bi-invariant order and convexity condition. -/
theorem isRelativelyConvex_iff {G : Type u} [Group G] (H : Subgroup G) :
    IsRelativelyConvex H ↔
      ∃ o : LinearOrder G, IsBiInvariantOrder o ∧
        ∀ h ∈ H, ∀ g : G, o.le 1 g → o.le g h → g ∈ H :=
  Iff.rfl

/-- Construct a relative-convexity witness. -/
theorem IsRelativelyConvex.intro {G : Type u} [Group G] {H : Subgroup G}
    (o : LinearOrder G) (ho : IsBiInvariantOrder o)
    (hconv : ∀ h ∈ H, ∀ g : G, o.le 1 g → o.le g h → g ∈ H) :
    IsRelativelyConvex H :=
  ⟨o, ho, hconv⟩

/-- Eliminate a relative-convexity witness without unfolding `IsRelativelyConvex`. -/
theorem IsRelativelyConvex.elim {G : Type u} [Group G] {H : Subgroup G} {P : Prop}
    (hH : IsRelativelyConvex H)
    (k : ∀ o : LinearOrder G, IsBiInvariantOrder o →
      (∀ h ∈ H, ∀ g : G, o.le 1 g → o.le g h → g ∈ H) → P) : P := by
  rcases hH with ⟨o, ho, hconv⟩
  exact k o ho hconv

/-- A relatively convex subgroup supplies a bi-invariant order on its ambient group. -/
theorem IsRelativelyConvex.isOrderable {G : Type u} [Group G] {H : Subgroup G}
    (hH : IsRelativelyConvex H) : IsOrderable G :=
  hH.elim fun o ho _ => IsOrderable.intro o ho

end MathlibExt.GroupTheory
