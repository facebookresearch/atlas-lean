/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Protocol
public import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
# Regular protocol tree equivalence using canonical CSLib bisimilarity

This is a tree observation LTS on type codes, not process execution semantics.
Labels preserve head direction, payload role/rank and payload/continuation
branch identity. No graph identity or typing theorem is an observation.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- **Payload and continuation branches of an endpoint action.**
The two distinct children of an endpoint action. -/
inductive TypeBranch where
  | payload
  | continuation
  deriving DecidableEq

/-- **Labels of observable protocol-tree edges.**
Observable guarded tree edges. Endpoint metadata is never erased. -/
inductive TypeLabel where
  | sendName
  | recvName
  | sendEndpoint (role : Role) (rank : Nat) (branch : TypeBranch)
  | recvEndpoint (role : Role) (rank : Nat) (branch : TypeBranch)
  deriving DecidableEq

/-- **Visible edge of a protocol tree after root unfolding.**
One visible tree edge obtained by the existing guarded root unfolding. -/
inductive TypeEdge : Protocol → TypeLabel → Protocol → Prop where
  | sendName {p s : Protocol} : p.unfold = .sendName s → TypeEdge p .sendName s
  | recvName {p s : Protocol} : p.unfold = .recvName s → TypeEdge p .recvName s
  | sendPayload {p t s : Protocol} {r : Role} {k : Nat} :
      p.unfold = .sendEndpoint r k t s → TypeEdge p (.sendEndpoint r k .payload) t
  | sendNext {p t s : Protocol} {r : Role} {k : Nat} :
      p.unfold = .sendEndpoint r k t s → TypeEdge p (.sendEndpoint r k .continuation) s
  | recvPayload {p t s : Protocol} {r : Role} {k : Nat} :
      p.unfold = .recvEndpoint r k t s → TypeEdge p (.recvEndpoint r k .payload) t
  | recvNext {p t s : Protocol} {r : Role} {k : Nat} :
      p.unfold = .recvEndpoint r k t s → TypeEdge p (.recvEndpoint r k .continuation) s

/-- **Labelled transition system of protocol-tree observations.**
Canonical CSLib LTS instance for guarded type-tree observations only. -/
def protocolTree : Cslib.LTS Protocol TypeLabel := ⟨TypeEdge⟩

/-- **Regular-tree equivalence of protocols as bisimilarity.**
Equirecursive regular-tree equality is canonical strong bisimilarity,
not equality of graph codes, cursors or finite constructor syntax. -/
def Protocol.TreeEquiv : Protocol → Protocol → Prop := Cslib.LTS.HomBisimilarity protocolTree

/-- **Protocol tree equivalence is reflexive.**
Reflexivity comes from the canonical CSLib bisimilarity API. -/
theorem Protocol.TreeEquiv.refl (p : Protocol) : p.TreeEquiv p :=
  Cslib.LTS.HomBisimilarity.refl p

/-- **Protocol tree equivalence is symmetric.**
Symmetry comes from the canonical CSLib bisimilarity API. -/
theorem Protocol.TreeEquiv.symm {p q : Protocol} (h : p.TreeEquiv q) : q.TreeEquiv p :=
  Cslib.LTS.Bisimilarity.symm h

/-- **Protocol tree equivalence is transitive.**
Transitivity comes from composition of canonical CSLib bisimulations. -/
theorem Protocol.TreeEquiv.trans {p q r : Protocol} (h : p.TreeEquiv q)
    (h' : q.TreeEquiv r) : p.TreeEquiv r := Cslib.LTS.Bisimilarity.trans h h'

/-- **Root unfolding preserves protocol-tree edges.**
Root unfolding exposes exactly the same observation edges. -/
theorem typeEdge_unfold {p q : Protocol} {l : TypeLabel} :
    TypeEdge p.unfold l q ↔ TypeEdge p l q := by
  constructor <;> intro h <;> cases h with
  | sendName h => exact TypeEdge.sendName (by simpa only [Protocol.unfold_unfold] using h)
  | recvName h => exact TypeEdge.recvName (by simpa only [Protocol.unfold_unfold] using h)
  | sendPayload h => exact TypeEdge.sendPayload (by simpa only [Protocol.unfold_unfold] using h)
  | sendNext h => exact TypeEdge.sendNext (by simpa only [Protocol.unfold_unfold] using h)
  | recvPayload h => exact TypeEdge.recvPayload (by simpa only [Protocol.unfold_unfold] using h)
  | recvNext h => exact TypeEdge.recvNext (by simpa only [Protocol.unfold_unfold] using h)

/-- **A protocol is tree-equivalent to its unfolding.**
One unfolding is semantically equivalent even though its code changes. -/
theorem Protocol.treeEquiv_unfold (p : Protocol) : p.TreeEquiv p.unfold := by
  apply Cslib.LTS.HomBisimilarity.of_image_eq
  funext l
  apply Set.ext
  intro q
  exact typeEdge_unfold.symm

/-- **Head and branch matching of protocols up to a child relation.**
Exact head and branch correspondence for a relation on child trees.
Payload and continuation are related separately; only metadata is literal. -/
inductive HeadMatch (R : Protocol → Protocol → Prop) : Protocol → Protocol → Prop where
  | done : HeadMatch R .done .done
  | sendName {s t : Protocol} : R s t → HeadMatch R (.sendName s) (.sendName t)
  | recvName {s t : Protocol} : R s t → HeadMatch R (.recvName s) (.recvName t)
  | sendEndpoint {r : Role} {k : Nat} {p q s t : Protocol} :
      R p q → R s t → HeadMatch R (.sendEndpoint r k p s) (.sendEndpoint r k q t)
  | recvEndpoint {r : Role} {k : Nat} {p q s t : Protocol} :
      R p q → R s t → HeadMatch R (.recvEndpoint r k p s) (.recvEndpoint r k q t)

/-- **Head matching is monotone in the child relation.**
Head matching is monotone in the child relation. -/
theorem HeadMatch.mono {R S : Protocol → Protocol → Prop} {p q : Protocol}
    (h : HeadMatch R p q) (hrs : ∀ a b, R a b → S a b) : HeadMatch S p q := by
  cases h with
  | done => exact HeadMatch.done
  | sendName h => exact HeadMatch.sendName (hrs _ _ h)
  | recvName h => exact HeadMatch.recvName (hrs _ _ h)
  | sendEndpoint hp hs => exact HeadMatch.sendEndpoint (hrs _ _ hp) (hrs _ _ hs)
  | recvEndpoint hp hs => exact HeadMatch.recvEndpoint (hrs _ _ hp) (hrs _ _ hs)

/-- **Head-matching relations are bisimulations.**
A relation matching literal unfolded heads and both child branches is a
canonical CSLib bisimulation. This is the coinductive proof rule, not an axiom. -/
theorem headMatch_isBisimulation {R : Protocol → Protocol → Prop}
    (hR : ∀ p q, R p q → HeadMatch R p.unfold q.unfold) :
    Cslib.LTS.IsBisimulation protocolTree protocolTree R := by
  intro p q hpq l
  change (∀ t, TypeEdge p l t → ∃ u, TypeEdge q l u ∧ R t u) ∧
    (∀ u, TypeEdge q l u → ∃ t, TypeEdge p l t ∧ R t u)
  have hh := hR p q hpq
  generalize hpu : p.unfold = pu at hh
  generalize hqu : q.unfold = qu at hh
  cases hh
  all_goals constructor <;> intro t ht
  all_goals cases ht
  all_goals grind [→ TypeEdge.sendName, → TypeEdge.recvName, → TypeEdge.sendPayload,
    → TypeEdge.sendNext, → TypeEdge.recvPayload, → TypeEdge.recvNext]

/-- **Tree-equivalent protocols have matching heads.**
Canonical bisimilarity determines literal head metadata and both
semantically equivalent child branches. No graph-code equality is required. -/
theorem Protocol.TreeEquiv.head {p q : Protocol} (h : p.TreeEquiv q) :
    HeadMatch Protocol.TreeEquiv p.unfold q.unfold := by
  have hf : ∀ l t, TypeEdge p l t → ∃ u, TypeEdge q l u ∧ t.TreeEquiv u := by
    intro l t ht
    exact Cslib.LTS.Bisimilarity.follow_fst h ht
  have hb : ∀ l u, TypeEdge q l u → ∃ t, TypeEdge p l t ∧ t.TreeEquiv u := by
    intro l u hu
    exact Cslib.LTS.Bisimilarity.follow_snd h hu
  generalize hp : p.unfold = pu
  generalize hq : q.unfold = qu
  cases pu <;> cases qu
  all_goals try { exact HeadMatch.done }
  all_goals try { exact False.elim (Protocol.unfold_ne_regular _ _ _ _ hp) }
  all_goals try { exact False.elim (Protocol.unfold_ne_regular _ _ _ _ hq) }
  all_goals grind [→ TypeEdge.sendName, → TypeEdge.recvName, → TypeEdge.sendPayload,
    → TypeEdge.sendNext, → TypeEdge.recvPayload, → TypeEdge.recvNext,
    cases TypeEdge, HeadMatch]

/-- **Coinduction principle for protocol tree equivalence.**
Coinduction on an explicitly supplied tree relation, checked by CSLib. -/
theorem Protocol.TreeEquiv.coind {R : Protocol → Protocol → Prop}
    (hR : ∀ a b, R a b → HeadMatch R a.unfold b.unfold) {p q : Protocol}
    (hpq : R p q) : p.TreeEquiv q := ⟨R, hpq, headMatch_isBisimulation hR⟩

/-- **Characterization of tree equivalence by matching heads.**
Exact semantic root/branch characterization, in BOTH directions. -/
theorem Protocol.treeEquiv_iff_head {p q : Protocol} :
    p.TreeEquiv q ↔ HeadMatch Protocol.TreeEquiv p.unfold q.unfold := by
  refine ⟨Protocol.TreeEquiv.head, ?_⟩
  intro hh
  let R : Protocol → Protocol → Prop := fun a b => a.TreeEquiv b ∨ (a = p ∧ b = q)
  apply Protocol.TreeEquiv.coind (R := R) ?_ (Or.inr ⟨rfl, rfl⟩)
  intro a b hab
  rcases hab with hab | ⟨rfl, rfl⟩
  · exact hab.head.mono (fun _ _ h => Or.inl h)
  · exact hh.mono (fun _ _ h => Or.inl h)

/-- **Unfolding both protocols preserves and reflects tree equivalence.**
Unfolding on either or both sides leaves the regular tree unchanged. -/
theorem Protocol.treeEquiv_unfold_iff {p q : Protocol} :
    p.unfold.TreeEquiv q.unfold ↔ p.TreeEquiv q := by
  constructor
  · intro h
    exact (p.treeEquiv_unfold.trans h).trans q.treeEquiv_unfold.symm
  · intro h
    exact (p.treeEquiv_unfold.symm.trans h).trans q.treeEquiv_unfold

/-- **Tree equivalence is a congruence for name sending.**
Constructor congruence matches same-direction name continuations. -/
theorem Protocol.TreeEquiv.sendName {p q : Protocol} (h : p.TreeEquiv q) :
    (Protocol.sendName p).TreeEquiv (.sendName q) :=
  Protocol.treeEquiv_iff_head.mpr (HeadMatch.sendName h)

/-- **Tree equivalence is a congruence for name receiving.**
Constructor congruence also matches input direction separately. -/
theorem Protocol.TreeEquiv.recvName {p q : Protocol} (h : p.TreeEquiv q) :
    (Protocol.recvName p).TreeEquiv (.recvName q) :=
  Protocol.treeEquiv_iff_head.mpr (HeadMatch.recvName h)

/-- **Tree equivalence is a congruence for endpoint sending.**
Payload and continuation congruence do not conflate the two branches. -/
theorem Protocol.TreeEquiv.sendEndpoint {p q s t : Protocol} (hp : p.TreeEquiv q)
    (hs : s.TreeEquiv t) (r : Role) (k : Nat) :
    (Protocol.sendEndpoint r k p s).TreeEquiv (.sendEndpoint r k q t) :=
  Protocol.treeEquiv_iff_head.mpr (HeadMatch.sendEndpoint hp hs)

/-- **Tree equivalence is a congruence for endpoint receiving.**
Endpoint receive congruence preserves literal role/rank metadata. -/
theorem Protocol.TreeEquiv.recvEndpoint {p q s t : Protocol} (hp : p.TreeEquiv q)
    (hs : s.TreeEquiv t) (r : Role) (k : Nat) :
    (Protocol.recvEndpoint r k p s).TreeEquiv (.recvEndpoint r k q t) :=
  Protocol.treeEquiv_iff_head.mpr (HeadMatch.recvEndpoint hp hs)

/-- **Head matching transfers to dual protocols.**
Dualizing a head changes subject direction and continuation orientation,
but leaves payload orientation and role/rank metadata untouched. -/
theorem HeadMatch.dual {R S : Protocol → Protocol → Prop} {p q : Protocol}
    (h : HeadMatch R p q) (hpayload : ∀ a b, R a b → S a b)
    (hnext : ∀ a b, R a b → S a.dual b.dual) : HeadMatch S p.dual q.dual := by
  cases h with
  | done => exact HeadMatch.done
  | sendName hs => exact HeadMatch.recvName (hnext _ _ hs)
  | recvName hs => exact HeadMatch.sendName (hnext _ _ hs)
  | sendEndpoint hp hs => exact HeadMatch.recvEndpoint (hpayload _ _ hp) (hnext _ _ hs)
  | recvEndpoint hp hs => exact HeadMatch.sendEndpoint (hpayload _ _ hp) (hnext _ _ hs)

/-- **Duality preserves protocol tree equivalence.**
Semantic equivalence is preserved by actual protocol duality, including
recursive payloads with independently chosen orientation. -/
theorem Protocol.TreeEquiv.dual {p q : Protocol} (h : p.TreeEquiv q) :
    p.dual.TreeEquiv q.dual := by
  let R : Protocol → Protocol → Prop := fun a b => a.TreeEquiv b ∨
    ∃ x y : Protocol, x.TreeEquiv y ∧ a = x.dual ∧ b = y.dual
  apply Protocol.TreeEquiv.coind (R := R) ?_ (Or.inr ⟨p, q, h, rfl, rfl⟩)
  intro a b hab
  rcases hab with hab | ⟨x, y, hxy, rfl, rfl⟩
  · exact hab.head.mono (fun _ _ ht => Or.inl ht)
  · rw [Protocol.unfold_dual, Protocol.unfold_dual]
    exact hxy.head.dual (fun _ _ ht => Or.inl ht)
      (fun x y ht => Or.inr ⟨x, y, ht, rfl, rfl⟩)

/-- **Duality preserves and reflects protocol tree equivalence.**
Duality both preserves and reflects equivalence, not only one direction. -/
theorem Protocol.treeEquiv_dual_iff {p q : Protocol} :
    p.dual.TreeEquiv q.dual ↔ p.TreeEquiv q := by
  refine ⟨fun h => ?_, Protocol.TreeEquiv.dual⟩
  simpa only [Protocol.dual_dual] using h.dual

/-- **Protocol tree equivalence is an equivalence relation.**
The semantic type relation is a genuine equivalence relation. -/
theorem Protocol.treeEquiv_equivalence : Equivalence Protocol.TreeEquiv :=
  ⟨Protocol.TreeEquiv.refl, Protocol.TreeEquiv.symm, Protocol.TreeEquiv.trans⟩

/-- **Tree equivalence of endpoint sends, componentwise.**
Exact endpoint-send characterization exposes literal metadata equality
and separate semantic payload/continuation equivalences for conversion. -/
theorem Protocol.treeEquiv_sendEndpoint_iff {r r' : Role} {k k' : Nat}
    {p q s t : Protocol} :
    (Protocol.sendEndpoint r k p s).TreeEquiv (.sendEndpoint r' k' q t) ↔
      r = r' ∧ k = k' ∧ p.TreeEquiv q ∧ s.TreeEquiv t := by
  constructor
  · intro h
    have hh := h.head
    cases hh with
    | sendEndpoint hp hs => exact ⟨rfl, rfl, hp, hs⟩
  · rintro ⟨rfl, rfl, hp, hs⟩
    exact hp.sendEndpoint hs _ _

/-- **Tree equivalence of endpoint receives, componentwise.**
Receive characterization preserves the same independent payload metadata. -/
theorem Protocol.treeEquiv_recvEndpoint_iff {r r' : Role} {k k' : Nat}
    {p q s t : Protocol} :
    (Protocol.recvEndpoint r k p s).TreeEquiv (.recvEndpoint r' k' q t) ↔
      r = r' ∧ k = k' ∧ p.TreeEquiv q ∧ s.TreeEquiv t := by
  constructor
  · intro h
    have hh := h.head
    cases hh with
    | recvEndpoint hp hs => exact ⟨rfl, rfl, hp, hs⟩
  · rintro ⟨rfl, rfl, hp, hs⟩
    exact hp.recvEndpoint hs _ _

/-- **Tree equivalence preserves completion of a protocol.**
Activity/completion is invariant under semantic type equivalence. -/
theorem Protocol.TreeEquiv.done_iff {p q : Protocol} (h : p.TreeEquiv q) :
    p.unfold = .done ↔ q.unfold = .done := by
  constructor
  · intro hp
    have hh := h.head
    rw [hp] at hh
    generalize hq : q.unfold = qu at hh
    cases hh
    rfl
  · intro hq
    have hh := h.symm.head
    rw [hq] at hh
    generalize hp : p.unfold = pu at hh
    cases hh
    rfl

end Cslib.SessionTypes.Endpoint
