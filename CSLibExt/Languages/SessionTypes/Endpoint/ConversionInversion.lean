/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ConversionTyping
public import CSLibExt.Languages.SessionTypes.Endpoint.NameAbsence

/-! # Derived scope, finite syntax and exact ownership inversions -/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- Canonical scope follows from the seven conversion rules. -/
theorem HasType.closedAt {n : Nat} {Δ : Context} {p : Proc} (h : HasType n Δ p) : p.ClosedAt n := by
  induction h with
  | nil => trivial
  | outName _ _ ha hb _ ih => exact ⟨ha, hb, ih⟩
  | inpName _ _ ha _ ih => exact ⟨ha, ih⟩
  | outEndpoint _ _ _ _ _ ha hb _ ih => exact ⟨ha, hb, ih⟩
  | inpEndpoint _ _ ha _ ih => exact ⟨ha, ih⟩
  | par _ _ _ ihp ihq => exact ⟨ihp, ihq⟩
  | nu _ ih => exact ih

/-- Typing excludes sum and repl by syntax, not by a caller fragment premise. -/
theorem HasType.finiteLinear {n : Nat} {Δ : Context} {p : Proc} (h : HasType n Δ p) :
    FiniteLinear p := by
  induction h <;> simp_all [FiniteLinear]

/-- Parallel inversion derives its actual disjoint map split. -/
theorem HasType.par_inv {n : Nat} {Δ : Context} {p q : Proc} (h : HasType n Δ (.par p q)) :
    ∃ Γ Θ, Δ = Γ ∪ Θ ∧ Finmap.Disjoint Γ Θ ∧ HasType n Γ p ∧ HasType n Θ q := by
  cases h with
  | par hd hp hq => exact ⟨_, _, rfl, hd, hp, hq⟩

/-- The private pair comes from the actual restriction derivation. -/
theorem HasType.nu_inv {n : Nat} {Δ : Context} {p : Proc} (h : HasType n Δ (.nu p)) :
    ∃ c, HasType (n + 1) (Context.bind c Δ) p := by
  cases h with
  | nu hp => exact ⟨_, hp⟩

/-- Nil exposes actual completed ownership and key scope. -/
theorem HasType.nil_inv {n : Nat} {Δ : Context} (h : HasType n Δ .nil) :
    Δ.Completed ∧ (∀ e ∈ Δ, e.name.ClosedAt n) := by
  cases h with
  | nil hc hs => exact ⟨hc, hs⟩

/-- Only a scoped actually completed capability can be added at nil. -/
theorem HasType.nil_insert {n : Nat} {Δ : Context} {e : Key} {c : Capability}
    (h : HasType n Δ .nil) (hc : c.protocol.unfold = .done) (he : e.name.ClosedAt n) :
    HasType n (Δ.insert e c) .nil := by
  obtain ⟨hΔ, hs⟩ := h.nil_inv
  apply HasType.nil (hΔ.insert hc)
  intro d hd
  rcases Finmap.mem_insert.mp hd with rfl | hd
  · exact he
  · exact hs d hd

end Cslib.SessionTypes.Endpoint.Conversion
