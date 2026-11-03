/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ContextAdvance
public import CSLibExt.Languages.SessionTypes.Endpoint.UnliftContext

/-!
# Pure restriction projection of faithful subject advancement
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Installing an outer capability commutes with the entire fresh bound pair. -/
theorem Context.bind_insert_outer (c : Capability) (Δ : Context) (e : Key)
    (u : Capability) :
    Context.bind c (Δ.insert e u) =
      (Context.bind c Δ).insert (Key.mapName (liftName 0) e) u := by
  rw [Context.bind, Context.bind, Context.lift_insert]
  rw [Finmap.insert_insert_of_ne (s := Context.lift 0 Δ)
    (a := Key.mapName (liftName 0) e)
    (a' := (⟨.var 0, .positive⟩ : Key)) (Key.lift_ne_bound e .positive)]
  rw [Finmap.insert_insert_of_ne
    (s := (Context.lift 0 Δ).insert (⟨.var 0, .positive⟩ : Key) c)
    (a := Key.mapName (liftName 0) e)
    (a' := (⟨.var 0, .negative⟩ : Key)) (Key.lift_ne_bound e .negative)]

/-- Two updates at the fresh positive/negative roles replace only the
bound capability pair and retain the entire lifted external context. -/
theorem Context.update_bound_positive (c d : Capability) (Δ : Context) :
    ((Context.bind c Δ).insert (⟨.var 0, .positive⟩ : Key) d).insert
      (⟨.var 0, .negative⟩ : Key) d.dual = Context.bind d Δ := by
  rw [Context.bind, Context.bind]
  rw [Finmap.insert_insert_of_ne
    (s := (Context.lift 0 Δ).insert (⟨.var 0, .positive⟩ : Key) c)
    (a := (⟨.var 0, .negative⟩ : Key)) (a' := (⟨.var 0, .positive⟩ : Key))
    (by decide)]
  rw [Finmap.insert_insert, Finmap.insert_insert]

/-- A negative sender installs the dual continuation on the positive role;
reordering the distinct insertions retains the same complete bound pair. -/
theorem Context.update_bound_negative (c d : Capability) (Δ : Context) :
    ((Context.bind c Δ).insert (⟨.var 0, .negative⟩ : Key) d.dual).insert
      (⟨.var 0, .positive⟩ : Key) d = Context.bind d Δ := by
  rw [Finmap.insert_insert_of_ne (s := Context.bind c Δ)
    (a := (⟨.var 0, .negative⟩ : Key)) (a' := (⟨.var 0, .positive⟩ : Key))
    (by decide)]
  exact Context.update_bound_positive c d Δ

/-- An outer lifted role lookup passes through both fresh bound entries
and reflects to the exact old external capability. -/
theorem Context.lookup_bind_outer {c u : Capability} {Δ : Context} {e : Key} :
    (Context.bind c Δ).lookup (Key.mapName (liftName 0) e) = some u ↔
      Δ.lookup e = some u := by
  rw [Context.bind, Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound e .negative),
    Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound e .positive), Context.lookup_lift]

/-- Exact pure restriction projection. An internal matched pair changes
only the bound pair at the same rank; an outer matched pair changes only the
external context and retains the entire old bound pair. -/
theorem DualAdvance.project_bind {c : Capability} {Δ Ξ : Context}
    (h : DualAdvance (Context.bind c Δ) Ξ) :
    (∃ d, d.rank = c.rank ∧ Ξ = Context.bind d Δ) ∨
      (∃ Δ', DualAdvance Δ Δ' ∧ Ξ = Context.bind c Δ') := by
  cases h with
  | @matched e u s hu hp hs =>
    by_cases hn : e.name = .var 0
    · cases e with
      | mk a r =>
        change a = .var 0 at hn
        subst a
        cases r with
        | positive =>
          have hc := Context.unique hu (Context.lookup_bind_positive c Δ)
          subst u
          exact Or.inl ⟨⟨c.rank, s⟩, rfl, Context.update_bound_positive c ⟨c.rank, s⟩ Δ⟩
        | negative =>
          have hc := Context.unique hu (Context.lookup_bind_negative c Δ)
          subst u
          refine Or.inl ⟨⟨c.rank, s.dual⟩, rfl, ?_⟩
          have ht := Context.update_bound_negative c ⟨c.rank, s.dual⟩ Δ
          simpa only [Capability.dual, Protocol.dual_dual, Key.opposite, Role.opposite]
            using ht
    · let d := Key.mapName (substName (.const 0) 0) e
      have he : Key.mapName (liftName 0) d = e := Key.lift_subst_outer_name e hn
      have hud : Δ.lookup d = some u := Context.lookup_bind_outer.mp (he ▸ hu)
      have hpd : Δ.lookup d.opposite = some u.dual := by
        have he' : Key.mapName (liftName 0) d.opposite = e.opposite :=
          congrArg Key.opposite he
        have ht : (Context.bind c Δ).lookup (Key.mapName (liftName 0) d.opposite) =
            some u.dual := by
          rw [he']
          exact hp
        exact (Context.lookup_bind_outer (c := c) (e := d.opposite)).mp ht
      refine Or.inr ⟨(Δ.insert d ⟨u.rank, s⟩).insert d.opposite ⟨u.rank, s.dual⟩,
        DualAdvance.matched hud hpd hs, ?_⟩
      rw [Context.bind_insert_outer, Context.bind_insert_outer, he]
      have he' : Key.mapName (liftName 0) d.opposite = e.opposite :=
        congrArg Key.opposite he
      rw [he']

/-- An actual external matched update lifts through restriction without
altering its private pair, even when the payload protocol refers to private data. -/
theorem DualAdvance.bind_outer {Δ Δ' : Context} (h : DualAdvance Δ Δ') (c : Capability) :
    DualAdvance (Context.bind c Δ) (Context.bind c Δ') := by
  cases h with
  | @matched e u s hu hp hs =>
    rw [Context.bind_insert_outer, Context.bind_insert_outer]
    have ha : DualAdvance (Context.bind c Δ)
        (((Context.bind c Δ).insert (Key.mapName (liftName 0) e) ⟨u.rank, s⟩).insert
          (Key.mapName (liftName 0) e).opposite ⟨u.rank, s.dual⟩) :=
      DualAdvance.matched (Context.lookup_bind_outer.mpr hu)
        (Context.lookup_bind_outer.mpr hp) hs
    exact ha

/-- Projection additionally retains an actual private old-head/continuation
transition when the communication is hidden by ν. It does not reduce private
advancement to an arbitrary capability with the same rank. -/
theorem DualAdvance.project_bind_faithful {c : Capability} {Δ Ξ : Context}
    (h : DualAdvance (Context.bind c Δ) Ξ) :
    (∃ d, d.rank = c.rank ∧ DualAdvance (Context.bind c ∅) (Context.bind d ∅) ∧
      Ξ = Context.bind d Δ) ∨
    (∃ Δ', DualAdvance Δ Δ' ∧ Ξ = Context.bind c Δ') := by
  cases h with
  | @matched e u s hu hp hs =>
    by_cases hn : e.name = .var 0
    · cases e with
      | mk a r =>
        change a = .var 0 at hn
        subst a
        cases r with
        | positive =>
          have hc := Context.unique hu (Context.lookup_bind_positive c Δ)
          subst u
          have ha := DualAdvance.matched (Context.lookup_bind_positive c ∅)
            (Context.lookup_bind_negative c ∅) hs
          change DualAdvance (Context.bind c ∅)
            (((Context.bind c ∅).insert (⟨.var 0, .positive⟩ : Key) ⟨c.rank, s⟩).insert
              (⟨.var 0, .negative⟩ : Key) (⟨c.rank, s⟩ : Capability).dual) at ha
          rw [Context.update_bound_positive] at ha
          exact Or.inl ⟨⟨c.rank, s⟩, rfl, ha, Context.update_bound_positive c ⟨c.rank, s⟩ Δ⟩
        | negative =>
          have hc := Context.unique hu (Context.lookup_bind_negative c Δ)
          subst u
          have hpos : (Context.bind c ∅).lookup
              (⟨.var 0, .negative⟩ : Key).opposite = some c.dual.dual := by
            rw [Capability.dual_dual]
            exact Context.lookup_bind_positive c ∅
          have ha := DualAdvance.matched (Context.lookup_bind_negative c ∅) hpos hs
          have htarget :
              (((Context.bind c ∅).insert (⟨.var 0, .negative⟩ : Key) ⟨c.rank, s⟩).insert
                (⟨.var 0, .positive⟩ : Key) ⟨c.rank, s.dual⟩) =
              Context.bind ⟨c.rank, s.dual⟩ ∅ := by
            simpa only [Capability.dual, Protocol.dual_dual] using
              Context.update_bound_negative c ⟨c.rank, s.dual⟩ ∅
          change DualAdvance (Context.bind c ∅)
            (((Context.bind c ∅).insert (⟨.var 0, .negative⟩ : Key) ⟨c.rank, s⟩).insert
              (⟨.var 0, .positive⟩ : Key) ⟨c.rank, s.dual⟩) at ha
          rw [htarget] at ha
          refine Or.inl ⟨⟨c.rank, s.dual⟩, rfl, ha, ?_⟩
          simpa only [Capability.dual, Protocol.dual_dual, Key.opposite, Role.opposite] using
            Context.update_bound_negative c ⟨c.rank, s.dual⟩ Δ
    · let d := Key.mapName (substName (.const 0) 0) e
      have he : Key.mapName (liftName 0) d = e := Key.lift_subst_outer_name e hn
      have hud : Δ.lookup d = some u := Context.lookup_bind_outer.mp (he ▸ hu)
      have he' : Key.mapName (liftName 0) d.opposite = e.opposite := congrArg Key.opposite he
      have hpd : Δ.lookup d.opposite = some u.dual :=
        (Context.lookup_bind_outer (c := c) (e := d.opposite)).mp (he' ▸ hp)
      refine Or.inr ⟨(Δ.insert d ⟨u.rank, s⟩).insert d.opposite ⟨u.rank, s.dual⟩,
        DualAdvance.matched hud hpd hs, ?_⟩
      rw [Context.bind_insert_outer, Context.bind_insert_outer, he, he']

end Cslib.SessionTypes.Endpoint
