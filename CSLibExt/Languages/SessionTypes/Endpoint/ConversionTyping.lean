/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.TypeEquivalence
public import CSLibExt.Languages.SessionTypes.Endpoint.Typing
public import CSLibExt.Languages.SessionTypes.Endpoint.Balance

/-!
# Conversion-enabled typing over existing protocol codes

Only advertised endpoint payload comparison is relaxed to regular-tree
equivalence. Ownership, ranks, actual unfolded heads and canonical π remain
unchanged. This module defines the typing layer. ConversionCong and
ConversionReduction prove general congruence invariance and subject reduction
at initially semantically compatible interfaces; RankedConversionGlobal proves
global progress for the ranked refinement at semantically balanced interfaces.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- **Equivalence of endpoint capabilities.**
Capability equivalence explicitly retains the enclosing capability rank,
which is not an observation of Protocol.TreeEquiv. -/
def Capability.Equivalent (c d : Capability) : Prop :=
  c.rank = d.rank ∧ c.protocol.TreeEquiv d.protocol

/-- **Reflexivity of capability equivalence.**
Reflexivity retains rank and the exact protocol tree. -/
theorem Capability.Equivalent.refl (c : Capability) : c.Equivalent c :=
  ⟨rfl, Protocol.TreeEquiv.refl _⟩

/-- **Symmetry of capability equivalence.**
Symmetry preserves the separately required rank equality. -/
theorem Capability.Equivalent.symm {c d : Capability} (h : c.Equivalent d) :
    d.Equivalent c := ⟨h.1.symm, h.2.symm⟩

/-- **Transitivity of capability equivalence.**
Transitivity composes rank equality and regular-tree equivalence. -/
theorem Capability.Equivalent.trans {c d e : Capability} (h : c.Equivalent d)
    (h' : d.Equivalent e) : c.Equivalent e := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- **Duality preserves capability equivalence.**
Duality retains the separate rank and preserves protocol-tree equivalence. -/
theorem Capability.Equivalent.dual {c d : Capability} (h : c.Equivalent d) :
    c.dual.Equivalent d.dual := ⟨h.1, h.2.dual⟩

namespace Conversion

open PiCalculus

/-- **Semantic peer compatibility of an ownership map.**
Semantic peer compatibility keeps actual capability ranks equal and
compares dual protocol trees, not merely their direction or payload metadata. -/
def Compatible (Δ : Context) : Prop :=
  ∀ e c d, Δ.lookup e = some c → Δ.lookup e.opposite = some d → d.Equivalent c.dual

/-- **Syntactic compatibility implies semantic compatibility.**
Old syntactic peer compatibility implies the semantic condition. -/
theorem compatible_of_raw {Δ : Context} (h : Endpoint.Compatible Δ) : Compatible Δ := by
  intro e c d hc hd
  rw [h e c d hc hd]
  exact Capability.Equivalent.refl _

/-- **Conversion-enabled endpoint typing judgement.**
Seven syntax-directed rules. No readiness, Step, retyping, preservation
or consistent raw representative is a typing premise. Endpoint input installs
its actual advertised code; endpoint output transfers the actual owned slot. -/
inductive HasType : Nat → Context → Proc → Prop where
  | nil {n : Nat} {Δ : Context} :
      Δ.Completed → (∀ e ∈ Δ, e.name.ClosedAt n) → HasType n Δ .nil
  | outName {n : Nat} {Δ : Context} {e : Key} {c : Capability}
      {b : Name} {s : Protocol} {p : Proc} :
      Δ.lookup e = some c → c.protocol.unfold = .sendName s →
      e.name.ClosedAt n → b.ClosedAt n →
      HasType n (Δ.insert e ⟨c.rank, s⟩) p → HasType n Δ (.out e.name b p)
  | inpName {n : Nat} {Δ : Context} {e : Key} {c : Capability}
      {s : Protocol} {p : Proc} :
      Δ.lookup e = some c → c.protocol.unfold = .recvName s → e.name.ClosedAt n →
      HasType (n + 1) (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) p →
      HasType n Δ (.inp e.name p)
  | outEndpoint {n : Nat} {Δ : Context} {e d : Key} {c v : Capability}
      {k : Nat} {t s : Protocol} {p : Proc} :
      Δ.lookup e = some c → c.protocol.unfold = .sendEndpoint d.role k t s →
      Δ.lookup d = some v → v.Equivalent ⟨k, t⟩ → e ≠ d →
      e.name.ClosedAt n → d.name.ClosedAt n →
      HasType n ((Δ.erase d).insert e ⟨c.rank, s⟩) p →
      HasType n Δ (.out e.name d.name p)
  | inpEndpoint {n : Nat} {Δ : Context} {e : Key} {c : Capability}
      {r : Role} {k : Nat} {t s : Protocol} {p : Proc} :
      Δ.lookup e = some c → c.protocol.unfold = .recvEndpoint r k t s →
      e.name.ClosedAt n →
      HasType (n + 1)
        ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩) p →
      HasType n Δ (.inp e.name p)
  | par {n : Nat} {Δ Θ : Context} {p q : Proc} :
      Finmap.Disjoint Δ Θ → HasType n Δ p → HasType n Θ q →
      HasType n (Δ ∪ Θ) (.par p q)
  | nu {n : Nat} {Δ : Context} {c : Capability} {p : Proc} :
      HasType (n + 1) (Context.bind c Δ) p → HasType n Δ (.nu p)

/-- **Base endpoint typing embeds into conversion typing.**
Actual seven-rule induction embeds the raw judgement. This does not
transport the raw judgement's substitution or progress theorem to new terms. -/
theorem HasType.of_raw {n : Nat} {Δ : Context} {p : Proc}
    (h : Endpoint.HasType n Δ p) : HasType n Δ p := by
  induction h with
  | nil hc hs => exact HasType.nil hc hs
  | outName hc hh ha hb hp ih => exact HasType.outName hc hh ha hb ih
  | inpName hc hh ha hp ih => exact HasType.inpName hc hh ha ih
  | outEndpoint hc hh hv he ha hb hp ih =>
    exact HasType.outEndpoint hc hh hv (Capability.Equivalent.refl _) he ha hb ih
  | inpEndpoint hc hh ha hp ih => exact HasType.inpEndpoint hc hh ha ih
  | par hd hp hq ihp ihq => exact HasType.par hd ihp ihq
  | nu hp ih => exact HasType.nu ih

/-- **Output typing at a code equivalent to one send then end.**
Local finite-tail conversion: replacing a one-send-then-end protocol by
an equivalent code yields a usable output subject, retaining its actual next
code and rank. This is not arbitrary context retyping. -/
theorem one_action_tail {n k : Nat} {Γ : Context} {d : Key} {b : Name} {t : Protocol}
    (hc : Γ.Completed) (hscope : ∀ e ∈ Γ, e.name.ClosedAt n)
    (hd : d.name.ClosedAt n) (hb : b.ClosedAt n)
    (ht : (Protocol.sendName .done).TreeEquiv t) :
    HasType n (Γ.insert d ⟨k, t⟩) (.out d.name b .nil) := by
  have hh := ht.head
  change HeadMatch Protocol.TreeEquiv (.sendName .done) t.unfold at hh
  generalize he : t.unfold = u at hh
  cases hh with
  | sendName hs =>
    apply HasType.outName (e := d) (c := ⟨k, t⟩) (s := _)
    · exact Finmap.lookup_insert _
    · exact he
    · exact hd
    · exact hb
    · rw [Finmap.insert_insert]
      apply HasType.nil
      · exact hc.insert ((hs.done_iff).mp rfl)
      · intro e hm
        rcases Finmap.mem_insert.mp hm with rfl | hm
        · exact hd
        · exact hscope e hm

/-- **Output inversion for conversion typing.**
Conversion output inversion exposes actual owned payload metadata and
semantic comparison, never a supplied retyping result. -/
theorem HasType.out_inv {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : HasType n Δ (.out a b p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧
      ((∃ s, c.protocol.unfold = .sendName s) ∨
       ∃ d v k t s, d.name = b ∧ Δ.lookup d = some v ∧
         c.protocol.unfold = .sendEndpoint d.role k t s ∧ v.Equivalent ⟨k, t⟩) := by
  cases h with
  | outName hc hh ha hb hp => exact ⟨_, _, rfl, hc, Or.inl ⟨_, hh⟩⟩
  | outEndpoint hc hh hv he hne ha hb hp =>
    exact ⟨_, _, rfl, hc, Or.inr ⟨_, _, _, _, _, rfl, hv, hh, he⟩⟩

end Conversion
end Cslib.SessionTypes.Endpoint
