/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicWeightedDirichletComparison











open Finset SimpleGraph

namespace StatMech.Universality

noncomputable section



def isingFiniteGhostGraph
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real) :
    SimpleGraph (Option V) where
  Adj x y :=
    match x, y with
    | some a, some b => G.Adj a b
    | some a, none => 0 < ghostRate a
    | none, some b => 0 < ghostRate b
    | none, none => False
  symm := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => exact hxy
        | some y => exact hxy
    | some x =>
        cases y with
        | none => exact hxy
        | some y => exact G.symm hxy
  loopless := by
    constructor
    intro x hxx
    cases x with
    | none => exact hxx
    | some x => exact G.loopless.irrefl x hxx


noncomputable def isingFiniteGhostConductance
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real) :
    Option V → Option V → Real := by
  classical
  exact fun x y ↦ match x, y with
    | some a, some b => if G.Adj a b then 1 else 0
    | some a, none => ghostRate a
    | none, some b => ghostRate b
    | none, none => 0


def isingFiniteGhostExtension
    {V : Type*} (ghostValue : Real) (f : V → Real) : Option V → Real
  | some x => f x
  | none => ghostValue


def isingFiniteGhostBoundary {V : Type*} : Option V → Prop
  | some _ => False
  | none => True


def isingFiniteGhostBoundaryWith
    {V : Type*} (boundary : V → Prop) : Option V → Prop
  | some x => boundary x
  | none => True


def isingFiniteGhostInclusion
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real) :
    G →g isingFiniteGhostGraph G ghostRate where
  toFun := some
  map_rel' := by
    intro x y hxy
    exact hxy

theorem isingFiniteGhostConductance_nonneg
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real)
    (hrate : ∀ x, 0 ≤ ghostRate x) :
    ∀ x y, 0 ≤ isingFiniteGhostConductance G ghostRate x y := by
  classical
  intro x y
  cases x with
  | none =>
      cases y with
      | none => simp [isingFiniteGhostConductance]
      | some y => simpa [isingFiniteGhostConductance] using hrate y
  | some x =>
      cases y with
      | none => simpa [isingFiniteGhostConductance] using hrate x
      | some y =>
          by_cases hxy : G.Adj x y <;>
            simp [isingFiniteGhostConductance, hxy]

theorem isingFiniteGhostConductance_pos_of_adj
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real) :
    ∀ ⦃x y⦄, (isingFiniteGhostGraph G ghostRate).Adj x y →
      0 < isingFiniteGhostConductance G ghostRate x y := by
  classical
  intro x y hxy
  cases x with
  | none =>
      cases y with
      | none => exact False.elim hxy
      | some y => simpa [isingFiniteGhostConductance] using hxy
  | some x =>
      cases y with
      | none => simpa [isingFiniteGhostConductance] using hxy
      | some y =>
          change G.Adj x y at hxy
          simp [isingFiniteGhostConductance, hxy]



theorem isingFiniteGhostGraph_reachable_boundary
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real)
    (hreach : ∀ x, ∃ b, 0 < ghostRate b ∧ G.Reachable x b) :
    ∀ x : Option V, ∃ b, isingFiniteGhostBoundary b ∧
      (isingFiniteGhostGraph G ghostRate).Reachable x b := by
  intro x
  cases x with
  | none =>
      exact ⟨none, trivial, SimpleGraph.Reachable.refl none⟩
  | some x =>
      obtain ⟨b, hb, hxb⟩ := hreach x
      refine ⟨none, trivial, ?_⟩
      have hsome : (isingFiniteGhostGraph G ghostRate).Reachable (some x) (some b) :=
        hxb.map (isingFiniteGhostInclusion G ghostRate)
      have hghost : (isingFiniteGhostGraph G ghostRate).Reachable (some b) none :=
        (show (isingFiniteGhostGraph G ghostRate).Adj (some b) none from hb).reachable
      exact hsome.trans hghost



theorem isingFiniteGhostGraph_reachable_boundaryWith
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real)
    (boundary : V → Prop)
    (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < ghostRate b) ∧
      G.Reachable x b) :
    ∀ x : Option V, ∃ b, isingFiniteGhostBoundaryWith boundary b ∧
      (isingFiniteGhostGraph G ghostRate).Reachable x b := by
  intro x
  cases x with
  | none =>
      exact ⟨none, trivial, SimpleGraph.Reachable.refl none⟩
  | some x =>
      obtain ⟨b, hb | hb, hxb⟩ := hreach x
      · exact ⟨some b, hb,
          hxb.map (isingFiniteGhostInclusion G ghostRate)⟩
      · refine ⟨none, trivial, ?_⟩
        have hsome :
            (isingFiniteGhostGraph G ghostRate).Reachable (some x) (some b) :=
          hxb.map (isingFiniteGhostInclusion G ghostRate)
        have hghost :
            (isingFiniteGhostGraph G ghostRate).Reachable (some b) none :=
          (show (isingFiniteGhostGraph G ghostRate).Adj (some b) none from hb).reachable
        exact hsome.trans hghost



theorem isingFiniteGhostLaplacian_some
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (ghostValue : Real) (f : V → Real) (x : V) :
    isingFiniteWeightedLaplacian
        (isingFiniteGhostConductance G ghostRate)
        (isingFiniteGhostExtension ghostValue f) (some x) =
      isingFiniteGraphLaplacian G f x +
        ghostRate x * (ghostValue - f x) := by
  classical
  unfold isingFiniteWeightedLaplacian isingFiniteGraphLaplacian
  rw [Fintype.sum_option]
  simp only [isingFiniteGhostConductance, isingFiniteGhostExtension]
  rw [add_comm]
  congr 1
  rw [neighborFinset_eq_filter, sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : G.Adj x y <;>
    simp [isingFiniteGhostConductance, hxy]



theorem isingFiniteGhostExtension_subharmonicOn
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (ghostValue : Real) (f : V → Real)
    (hmodified : ∀ x, 0 ≤ isingFiniteGraphLaplacian G f x +
      ghostRate x * (ghostValue - f x)) :
    IsingFiniteWeightedSubharmonicOn
      (isingFiniteGhostConductance G ghostRate)
      isingFiniteGhostBoundary
      (isingFiniteGhostExtension ghostValue f) := by
  intro x hx
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      rw [isingFiniteGhostLaplacian_some]
      exact hmodified x


theorem isingFiniteGhostExtension_superharmonicOn
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (ghostValue : Real) (f : V → Real)
    (hmodified : ∀ x, isingFiniteGraphLaplacian G f x +
      ghostRate x * (ghostValue - f x) ≤ 0) :
    IsingFiniteWeightedSuperharmonicOn
      (isingFiniteGhostConductance G ghostRate)
      isingFiniteGhostBoundary
      (isingFiniteGhostExtension ghostValue f) := by
  intro x hx
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      rw [isingFiniteGhostLaplacian_some]
      exact hmodified x


theorem isingFiniteGhostExtension_subharmonicOn_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (boundary : V → Prop) (ghostValue : Real) (f : V → Real)
    (hmodified : ∀ x, ¬ boundary x →
      0 ≤ isingFiniteGraphLaplacian G f x +
        ghostRate x * (ghostValue - f x)) :
    IsingFiniteWeightedSubharmonicOn
      (isingFiniteGhostConductance G ghostRate)
      (isingFiniteGhostBoundaryWith boundary)
      (isingFiniteGhostExtension ghostValue f) := by
  intro x hx
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      rw [isingFiniteGhostLaplacian_some]
      exact hmodified x hx


theorem isingFiniteGhostExtension_superharmonicOn_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (boundary : V → Prop) (ghostValue : Real) (f : V → Real)
    (hmodified : ∀ x, ¬ boundary x →
      isingFiniteGraphLaplacian G f x +
        ghostRate x * (ghostValue - f x) ≤ 0) :
    IsingFiniteWeightedSuperharmonicOn
      (isingFiniteGhostConductance G ghostRate)
      (isingFiniteGhostBoundaryWith boundary)
      (isingFiniteGhostExtension ghostValue f) := by
  intro x hx
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      rw [isingFiniteGhostLaplacian_some]
      exact hmodified x hx



theorem isingFiniteGhost_subharmonic_le_ghostValue
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (f : V → Real) (c : Real)
    (hrate : ∀ x, 0 ≤ ghostRate x)
    (hreach : ∀ x, ∃ b, 0 < ghostRate b ∧ G.Reachable x b)
    (hmodified : ∀ x, 0 ≤ isingFiniteGraphLaplacian G f x +
      ghostRate x * (c - f x)) :
    ∀ x, f x ≤ c := by
  intro x
  have h := isingFiniteWeighted_subharmonic_le_const
    (isingFiniteGhostGraph G ghostRate)
    (isingFiniteGhostConductance G ghostRate)
    isingFiniteGhostBoundary (isingFiniteGhostExtension c f) c
    (isingFiniteGhostConductance_nonneg G ghostRate hrate)
    (isingFiniteGhostConductance_pos_of_adj G ghostRate)
    (isingFiniteGhostGraph_reachable_boundary G ghostRate hreach)
    (isingFiniteGhostExtension_subharmonicOn
      G ghostRate c f hmodified)
    (by
      intro y hy
      cases y with
      | none => rfl
      | some y => simp [isingFiniteGhostBoundary] at hy)
  exact h (some x)



theorem isingFiniteGhost_ghostValue_le_superharmonic
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real)
    (f : V → Real) (c : Real)
    (hrate : ∀ x, 0 ≤ ghostRate x)
    (hreach : ∀ x, ∃ b, 0 < ghostRate b ∧ G.Reachable x b)
    (hmodified : ∀ x, isingFiniteGraphLaplacian G f x +
      ghostRate x * (c - f x) ≤ 0) :
    ∀ x, c ≤ f x := by
  intro x
  have h := isingFiniteWeighted_const_le_superharmonic
    (isingFiniteGhostGraph G ghostRate)
    (isingFiniteGhostConductance G ghostRate)
    isingFiniteGhostBoundary (isingFiniteGhostExtension c f) c
    (isingFiniteGhostConductance_nonneg G ghostRate hrate)
    (isingFiniteGhostConductance_pos_of_adj G ghostRate)
    (isingFiniteGhostGraph_reachable_boundary G ghostRate hreach)
    (isingFiniteGhostExtension_superharmonicOn
      G ghostRate c f hmodified)
    (by
      intro y hy
      cases y with
      | none => rfl
      | some y => simp [isingFiniteGhostBoundary] at hy)
  exact h (some x)



theorem isingFiniteGhost_subharmonic_le_const_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real) (boundary : V → Prop)
    (f : V → Real) (ghostValue c : Real)
    (hrate : ∀ x, 0 ≤ ghostRate x)
    (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < ghostRate b) ∧
      G.Reachable x b)
    (hmodified : ∀ x, ¬ boundary x →
      0 ≤ isingFiniteGraphLaplacian G f x +
        ghostRate x * (ghostValue - f x))
    (hghost : ghostValue ≤ c)
    (hboundary : ∀ x, boundary x → f x ≤ c) :
    ∀ x, f x ≤ c := by
  intro x
  have h := isingFiniteWeighted_subharmonic_le_const
    (isingFiniteGhostGraph G ghostRate)
    (isingFiniteGhostConductance G ghostRate)
    (isingFiniteGhostBoundaryWith boundary)
    (isingFiniteGhostExtension ghostValue f) c
    (isingFiniteGhostConductance_nonneg G ghostRate hrate)
    (isingFiniteGhostConductance_pos_of_adj G ghostRate)
    (isingFiniteGhostGraph_reachable_boundaryWith
      G ghostRate boundary hreach)
    (isingFiniteGhostExtension_subharmonicOn_boundaryWith
      G ghostRate boundary ghostValue f hmodified)
    (by
      intro y hy
      cases y with
      | none => exact hghost
      | some y => exact hboundary y hy)
  exact h (some x)



theorem isingFiniteGhost_const_le_superharmonic_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ghostRate : V → Real) (boundary : V → Prop)
    (f : V → Real) (ghostValue c : Real)
    (hrate : ∀ x, 0 ≤ ghostRate x)
    (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < ghostRate b) ∧
      G.Reachable x b)
    (hmodified : ∀ x, ¬ boundary x →
      isingFiniteGraphLaplacian G f x +
        ghostRate x * (ghostValue - f x) ≤ 0)
    (hghost : c ≤ ghostValue)
    (hboundary : ∀ x, boundary x → c ≤ f x) :
    ∀ x, c ≤ f x := by
  intro x
  have h := isingFiniteWeighted_const_le_superharmonic
    (isingFiniteGhostGraph G ghostRate)
    (isingFiniteGhostConductance G ghostRate)
    (isingFiniteGhostBoundaryWith boundary)
    (isingFiniteGhostExtension ghostValue f) c
    (isingFiniteGhostConductance_nonneg G ghostRate hrate)
    (isingFiniteGhostConductance_pos_of_adj G ghostRate)
    (isingFiniteGhostGraph_reachable_boundaryWith
      G ghostRate boundary hreach)
    (isingFiniteGhostExtension_superharmonicOn_boundaryWith
      G ghostRate boundary ghostValue f hmodified)
    (by
      intro y hy
      cases y with
      | none => exact hghost
      | some y => exact hboundary y hy)
  exact h (some x)


noncomputable def isingFermionicGhostCoefficient : Real :=
  2 / (1 + Real.sqrt 2)

theorem isingFermionicGhostCoefficient_pos :
    0 < isingFermionicGhostCoefficient := by
  unfold isingFermionicGhostCoefficient
  positivity



noncomputable def isingFermionicGhostRate
    {V : Type*} (boundaryMultiplicity : V → Nat) : V → Real :=
  fun x ↦ isingFermionicGhostCoefficient * boundaryMultiplicity x

theorem isingFermionicGhostRate_nonneg
    {V : Type*} (boundaryMultiplicity : V → Nat) :
    ∀ x, 0 ≤ isingFermionicGhostRate boundaryMultiplicity x := by
  intro x
  exact mul_nonneg isingFermionicGhostCoefficient_pos.le (by positivity)

theorem isingFermionicGhostRate_pos_iff
    {V : Type*} (boundaryMultiplicity : V → Nat) (x : V) :
    0 < isingFermionicGhostRate boundaryMultiplicity x ↔
      0 < boundaryMultiplicity x := by
  unfold isingFermionicGhostRate
  constructor
  · intro h
    by_contra hx
    have hz : boundaryMultiplicity x = 0 := Nat.eq_zero_of_not_pos hx
    simp [hz] at h
  · intro h
    exact mul_pos isingFermionicGhostCoefficient_pos (by exact_mod_cast h)


theorem isingFermionicGhost_subharmonic_le_ghostValue
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundaryMultiplicity : V → Nat)
    (f : V → Real) (c : Real)
    (hreach : ∀ x, ∃ b, 0 < boundaryMultiplicity b ∧ G.Reachable x b)
    (hmodified : ∀ x, 0 ≤ isingFiniteGraphLaplacian G f x +
      isingFermionicGhostRate boundaryMultiplicity x * (c - f x)) :
    ∀ x, f x ≤ c := by
  apply isingFiniteGhost_subharmonic_le_ghostValue
    G (isingFermionicGhostRate boundaryMultiplicity) f c
    (isingFermionicGhostRate_nonneg boundaryMultiplicity)
  · intro x
    obtain ⟨b, hb, hxb⟩ := hreach x
    exact ⟨b, (isingFermionicGhostRate_pos_iff
      boundaryMultiplicity b).2 hb, hxb⟩
  · exact hmodified


theorem isingFermionicGhost_ghostValue_le_superharmonic
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundaryMultiplicity : V → Nat)
    (f : V → Real) (c : Real)
    (hreach : ∀ x, ∃ b, 0 < boundaryMultiplicity b ∧ G.Reachable x b)
    (hmodified : ∀ x, isingFiniteGraphLaplacian G f x +
      isingFermionicGhostRate boundaryMultiplicity x * (c - f x) ≤ 0) :
    ∀ x, c ≤ f x := by
  apply isingFiniteGhost_ghostValue_le_superharmonic
    G (isingFermionicGhostRate boundaryMultiplicity) f c
    (isingFermionicGhostRate_nonneg boundaryMultiplicity)
  · intro x
    obtain ⟨b, hb, hxb⟩ := hreach x
    exact ⟨b, (isingFermionicGhostRate_pos_iff
      boundaryMultiplicity b).2 hb, hxb⟩
  · exact hmodified



theorem isingFermionicGhost_subharmonic_le_const_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundaryMultiplicity : V → Nat)
    (boundary : V → Prop) (f : V → Real) (ghostValue c : Real)
    (hreach : ∀ x, ∃ b,
      (boundary b ∨ 0 < boundaryMultiplicity b) ∧ G.Reachable x b)
    (hmodified : ∀ x, ¬ boundary x →
      0 ≤ isingFiniteGraphLaplacian G f x +
        isingFermionicGhostRate boundaryMultiplicity x *
          (ghostValue - f x))
    (hghost : ghostValue ≤ c)
    (hboundary : ∀ x, boundary x → f x ≤ c) :
    ∀ x, f x ≤ c := by
  apply isingFiniteGhost_subharmonic_le_const_boundaryWith
    G (isingFermionicGhostRate boundaryMultiplicity) boundary
      f ghostValue c
    (isingFermionicGhostRate_nonneg boundaryMultiplicity)
  · intro x
    obtain ⟨b, hb | hb, hxb⟩ := hreach x
    · exact ⟨b, Or.inl hb, hxb⟩
    · exact ⟨b, Or.inr ((isingFermionicGhostRate_pos_iff
        boundaryMultiplicity b).2 hb), hxb⟩
  · exact hmodified
  · exact hghost
  · exact hboundary


theorem isingFermionicGhost_const_le_superharmonic_boundaryWith
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (boundaryMultiplicity : V → Nat)
    (boundary : V → Prop) (f : V → Real) (ghostValue c : Real)
    (hreach : ∀ x, ∃ b,
      (boundary b ∨ 0 < boundaryMultiplicity b) ∧ G.Reachable x b)
    (hmodified : ∀ x, ¬ boundary x →
      isingFiniteGraphLaplacian G f x +
        isingFermionicGhostRate boundaryMultiplicity x *
          (ghostValue - f x) ≤ 0)
    (hghost : c ≤ ghostValue)
    (hboundary : ∀ x, boundary x → c ≤ f x) :
    ∀ x, c ≤ f x := by
  apply isingFiniteGhost_const_le_superharmonic_boundaryWith
    G (isingFermionicGhostRate boundaryMultiplicity) boundary
      f ghostValue c
    (isingFermionicGhostRate_nonneg boundaryMultiplicity)
  · intro x
    obtain ⟨b, hb | hb, hxb⟩ := hreach x
    · exact ⟨b, Or.inl hb, hxb⟩
    · exact ⟨b, Or.inr ((isingFermionicGhostRate_pos_iff
        boundaryMultiplicity b).2 hb), hxb⟩
  · exact hmodified
  · exact hghost
  · exact hboundary

end

end StatMech.Universality
