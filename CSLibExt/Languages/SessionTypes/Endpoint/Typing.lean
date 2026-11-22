/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ContextTransport
public import CSLibExt.Languages.SessionTypes.Endpoint.Fragment

/-!
# Linear endpoint typing of the existing π syntax

The ambient depth is the unrestricted passive-name scope. Receiving passive
data adds a name binder but no linear capability. Restrictions expose both
roles of one bound physical name; parallel composition splits finite maps.
This initial finite-process judgement has no choice or replication rule.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Syntax-directed linear typing. Capabilities never contain preservation
or progress assumptions. Protocol heads may be guarded regular protocols. -/
inductive HasType : Nat → Context → Proc → Prop where
  | nil {n : Nat} {Δ : Context} :
      Δ.Completed → (∀ e ∈ Δ, e.name.ClosedAt n) → HasType n Δ .nil
  | outName {n : Nat} {Δ : Context} {e : Key} {c : Capability}
      {b : Name} {s : Protocol} {p : Proc} :
      Δ.lookup e = some c → c.protocol.unfold = .sendName s →
      e.name.ClosedAt n → b.ClosedAt n →
      HasType n (Δ.insert e ⟨c.rank, s⟩) p →
      HasType n Δ (.out e.name b p)
  | inpName {n : Nat} {Δ : Context} {e : Key} {c : Capability}
      {s : Protocol} {p : Proc} :
      Δ.lookup e = some c → c.protocol.unfold = .recvName s →
      e.name.ClosedAt n →
      HasType (n + 1) (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) p →
      HasType n Δ (.inp e.name p)
  | outEndpoint {n : Nat} {Δ : Context} {e d : Key} {c : Capability}
      {k : Nat} {t s : Protocol} {p : Proc} :
      Δ.lookup e = some c →
      c.protocol.unfold = .sendEndpoint d.role k t s →
      Δ.lookup d = some ⟨k, t⟩ → e ≠ d →
      e.name.ClosedAt n → d.name.ClosedAt n →
      HasType n ((Δ.erase d).insert e ⟨c.rank, s⟩) p →
      HasType n Δ (.out e.name d.name p)
  | inpEndpoint {n : Nat} {Δ : Context} {e : Key} {c : Capability}
      {r : Role} {k : Nat} {t s : Protocol} {p : Proc} :
      Δ.lookup e = some c →
      c.protocol.unfold = .recvEndpoint r k t s →
      e.name.ClosedAt n →
      HasType (n + 1)
        ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩) p →
      HasType n Δ (.inp e.name p)
  | par {n : Nat} {Δ Θ : Context} {p q : Proc} :
      Finmap.Disjoint Δ Θ → HasType n Δ p → HasType n Θ q →
      HasType n (Δ ∪ Θ) (.par p q)
  | nu {n : Nat} {Δ : Context} {c : Capability} {p : Proc} :
      HasType (n + 1) (Context.bind c Δ) p → HasType n Δ (.nu p)

/-- Every endpoint-typed process satisfies the canonical π scope predicate. -/
theorem HasType.closedAt {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ p) : p.ClosedAt n := by
  induction h with
  | nil => trivial
  | outName _ _ ha hb _ ih => exact ⟨ha, hb, ih⟩
  | inpName _ _ ha _ ih => exact ⟨ha, ih⟩
  | outEndpoint _ _ _ _ ha hb _ ih => exact ⟨ha, hb, ih⟩
  | inpEndpoint _ _ ha _ ih => exact ⟨ha, ih⟩
  | par _ _ _ ihp ihq => exact ⟨ihp, ihq⟩
  | nu _ ih => exact ih

/-- Typed terms stay in the proved Cong/Step-closed finite fragment. -/
theorem HasType.finiteLinear {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ p) : FiniteLinear p := by
  induction h <;> simp_all [FiniteLinear]

/-- A recorded completed capability is admissible at nil; an active one
would fail the completed-context premise. -/
theorem HasType.nil_singleton {n k : Nat} {e : Key}
    (he : e.name.ClosedAt n) :
    HasType n (Finmap.singleton e ⟨k, .done⟩) .nil := by
  apply HasType.nil
  · intro d c hc
    have hd : d = e :=
      (Finmap.mem_singleton d e _).mp (Finmap.mem_of_lookup_eq_some hc)
    subst d
    simp only [Finmap.lookup_singleton_eq, Option.some.injEq] at hc
    subst c
    rfl
  · intro d hd
    have h := (Finmap.mem_singleton d e _).mp hd
    subst d
    exact he

/-- Every output subject is backed by an owned role, never merely by a
passive name in the ambient data scope. -/
theorem HasType.out_owned {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : HasType n Δ (.out a b p)) :
    ∃ r c, Δ.lookup ⟨a, r⟩ = some c := by
  cases h with
  | outName hc _ _ _ _ => exact ⟨_, _, hc⟩
  | outEndpoint hc _ _ _ _ _ _ => exact ⟨_, _, hc⟩

/-- Completed endpoint slots may be added at nil without creating a
communication obligation; active protocols cannot use this rule. -/
theorem HasType.nil_insert {n : Nat} {Δ : Context} {e : Key} {c : Capability}
    (h : HasType n Δ .nil) (hc : c.protocol.unfold = .done)
    (he : e.name.ClosedAt n) : HasType n (Δ.insert e c) .nil := by
  cases h with
  | nil hΔ hs =>
    apply HasType.nil (hΔ.insert hc)
    intro d hd
    rcases Finmap.mem_insert.mp hd with hd | hd
    · subst d
      exact he
    · exact hs d hd

/-- Input inversion exposes its owned role, literal payload sort, and
continuation context. Passive and delegated names are not conflated. -/
theorem HasType.inp_inv {n : Nat} {Δ : Context} {a : Name} {p : Proc}
    (h : HasType n Δ (.inp a p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧
      ((∃ s, c.protocol.unfold = .recvName s ∧
          HasType (n + 1) (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) p) ∨
        ∃ r k t s, c.protocol.unfold = .recvEndpoint r k t s ∧
          HasType (n + 1)
            ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩) p) := by
  cases h with
  | inpName hc hs _ hp => exact ⟨_, _, rfl, hc, Or.inl ⟨_, hs, hp⟩⟩
  | inpEndpoint hc hs _ hp => exact ⟨_, _, rfl, hc, Or.inr ⟨_, _, _, _, hs, hp⟩⟩

/-- Output inversion exposes the actual owned subject, distinct payload sort,
and literal continuation resources; delegation consumes the payload role. -/
theorem HasType.out_inv {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : HasType n Δ (.out a b p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧
      ((∃ s, c.protocol.unfold = .sendName s ∧
          HasType n (Δ.insert e ⟨c.rank, s⟩) p) ∨
        ∃ d k t s, d.name = b ∧ c.protocol.unfold = .sendEndpoint d.role k t s ∧
          Δ.lookup d = some ⟨k, t⟩ ∧ e ≠ d ∧
          HasType n ((Δ.erase d).insert e ⟨c.rank, s⟩) p) := by
  cases h with
  | outName hc hs _ _ hp => exact ⟨_, _, rfl, hc, Or.inl ⟨_, hs, hp⟩⟩
  | outEndpoint hc hs hd hne _ _ hp =>
    exact ⟨_, _, rfl, hc, Or.inr ⟨_, _, _, _, rfl, hs, hd, hne, hp⟩⟩

/-- Parallel typing exposes an actual disjoint ownership split, not a
stored preservation or progress witness. -/
theorem HasType.par_inv {n : Nat} {Δ : Context} {p q : Proc}
    (h : HasType n Δ (.par p q)) :
    ∃ Θ Ξ, Δ = Θ ∪ Ξ ∧ Finmap.Disjoint Θ Ξ ∧
      HasType n Θ p ∧ HasType n Ξ q := by
  cases h with
  | par hd hp hq => exact ⟨_, _, rfl, hd, hp, hq⟩

/-- Nil inversion exposes completion and scope of every recorded endpoint. -/
theorem HasType.nil_inv {n : Nat} {Δ : Context} (h : HasType n Δ .nil) :
    Δ.Completed ∧ (∀ e ∈ Δ, e.name.ClosedAt n) := by
  cases h with
  | nil hc hs => exact ⟨hc, hs⟩

/-- Any protocol whose guarded head is completed is admissible at a
single nil-owned slot, including completed regular graph cursors. -/
theorem HasType.nil_singleton_completed {n : Nat} {e : Key} {c : Capability}
    (he : e.name.ClosedAt n) (hc : c.protocol.unfold = .done) :
    HasType n (Finmap.singleton e c) .nil := by
  apply HasType.nil
  · intro d t ht
    have hd := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some ht)
    subst d
    have htc : t = c := Context.unique ht Finmap.lookup_singleton_eq
    exact htc ▸ hc
  · intro d hd
    have hde := (Finmap.mem_singleton _ _ _).mp hd
    exact hde ▸ he

end Cslib.SessionTypes.Endpoint
