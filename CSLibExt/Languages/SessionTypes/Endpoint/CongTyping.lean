/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ScopeTyping
public import CSLibExt.Languages.SessionTypes.Endpoint.SwapTyping

/-!
# Typing transport under every canonical structural congruence
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Parallel commutation swaps a derived disjoint split, not its capabilities. -/
theorem HasType.par_comm {n : Nat} {Δ : Context} {p q : Proc}
    (h : HasType n Δ (.par p q)) : HasType n Δ (.par q p) := by
  obtain ⟨Γ, Ξ, rfl, hd, hp, hq⟩ := h.par_inv
  rw [Finmap.union_comm_of_disjoint hd]
  exact HasType.par (hd.symm _ _) hq hp

/-- Parallel reassociation preserves the actual three-way disjoint split. -/
theorem HasType.par_assoc {n : Nat} {Δ : Context} {p q r : Proc}
    (h : HasType n Δ (.par (.par p q) r)) :
    HasType n Δ (.par p (.par q r)) := by
  obtain ⟨Γ, Ξ, rfl, hd, hpq, hr⟩ := h.par_inv
  obtain ⟨A, B, rfl, hab, hp, hq⟩ := hpq.par_inv
  obtain ⟨ha, hb⟩ := (Finmap.disjoint_union_left A B Ξ).mp hd
  rw [Finmap.union_assoc]
  exact HasType.par ((Finmap.disjoint_union_right A B Ξ).mpr ⟨hab, ha⟩)
    hp (HasType.par hb hq hr)

/-- Reverse reassociation recovers both sub-splits from the supplied typing. -/
theorem HasType.par_assoc_reverse {n : Nat} {Δ : Context} {p q r : Proc}
    (h : HasType n Δ (.par p (.par q r))) :
    HasType n Δ (.par (.par p q) r) := by
  obtain ⟨A, Γ, rfl, hd, hp, hqr⟩ := h.par_inv
  obtain ⟨B, C, rfl, hbc, hq, hr⟩ := hqr.par_inv
  obtain ⟨hab, hac⟩ := (Finmap.disjoint_union_right A B C).mp hd
  rw [← Finmap.union_assoc]
  exact HasType.par ((Finmap.disjoint_union_left A B C).mpr ⟨hac, hbc⟩)
    (HasType.par hab hp hq) hr

/-- Adding a parallel nil allocates it no ownership; no active slot is dropped. -/
theorem HasType.par_nil_intro {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ p) : HasType n Δ (.par p .nil) := by
  have hn : HasType n ∅ .nil :=
    HasType.nil (by intro e c he; simp at he)
      (by intro e he; exact False.elim (Finmap.notMem_empty he))
  have ht := HasType.par ((Finmap.disjoint_empty Δ).symm _ _) h hn
  simpa only [Finmap.union_empty] using ht

/-- Restriction of nil has exactly the completed external ownership of nil. -/
theorem HasType.nu_nil_elim {n : Nat} {Δ : Context}
    (h : HasType n Δ (.nu .nil)) : HasType n Δ .nil := by
  obtain ⟨c, hb⟩ := h.nu_inv
  have ha : NameAbsent (.var 0) Proc.nil := trivial
  have he := (hb.erase_nameAbsent (z := ⟨.var 0, .negative⟩) ha).erase_nameAbsent
    (z := ⟨.var 0, .positive⟩) ha
  rw [Context.erase_bind_pair] at he
  have ht := he.subst_passive (b := .const 0) trivial
  exact ht

/-- A completed fresh pair may be introduced around nil while retaining
all original external capabilities and scope. -/
theorem HasType.nu_nil_intro {n : Nat} {Δ : Context}
    (h : HasType n Δ .nil) : HasType n Δ (.nu .nil) := by
  have hl := h.lift 0
  have hp := hl.nil_insert (e := ⟨.var 0, .positive⟩)
    (c := ⟨0, .done⟩) rfl (Nat.zero_lt_succ n)
  have hn := hp.nil_insert (e := ⟨.var 0, .negative⟩)
    (c := (⟨0, .done⟩ : Capability).dual) rfl (Nat.zero_lt_succ n)
  exact HasType.nu (c := ⟨0, .done⟩) hn

/-- Nested restriction commutation swaps their derived complete dual pairs. -/
theorem HasType.nu_swap {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ (.nu (.nu p))) :
    HasType n Δ (.nu (.nu (swapProc 0 p))) := by
  obtain ⟨c, hc⟩ := h.nu_inv
  obtain ⟨d, hd⟩ := hc.nu_inv
  have ht := hd.swap (k := 0) (by omega)
  rw [Context.swap_bind_bind] at ht
  exact HasType.nu (c := d) (HasType.nu (c := c) ht)

/-- Reverse nested restriction commutation uses the canonical involution. -/
theorem HasType.nu_swap_reverse {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ (.nu (.nu (swapProc 0 p)))) : HasType n Δ (.nu (.nu p)) := by
  have ht := h.nu_swap
  rw [swapProc_swapProc] at ht
  exact ht

private theorem out_context_transport {p p' : Proc} {a b : Name}
    (ih : ∀ n Δ, HasType n Δ p ↔ HasType n Δ p') {n : Nat} {Δ : Context}
    (h : HasType n Δ (.out a b p)) : HasType n Δ (.out a b p') := by
  cases h with
  | outName hc hs ha hb hp =>
    exact HasType.outName hc hs ha hb ((ih _ _).mp hp)
  | outEndpoint hc hs hd hne ha hb hp =>
    exact HasType.outEndpoint hc hs hd hne ha hb ((ih _ _).mp hp)

private theorem inp_context_transport {p p' : Proc} {a : Name}
    (ih : ∀ n Δ, HasType n Δ p ↔ HasType n Δ p') {n : Nat} {Δ : Context}
    (h : HasType n Δ (.inp a p)) : HasType n Δ (.inp a p') := by
  cases h with
  | inpName hc hs ha hp => exact HasType.inpName hc hs ha ((ih _ _).mp hp)
  | inpEndpoint hc hs ha hp => exact HasType.inpEndpoint hc hs ha ((ih _ _).mp hp)

/-- Every existing canonical structural congruence preserves endpoint typing
in both directions with exactly the same depth and ownership. Unsupported
choice/replication shapes are rejected by the typing-derived finite invariant. -/
theorem HasType.cong_iff {n : Nat} {Δ : Context} {p q : Proc} (hc : Cong p q) :
    HasType n Δ p ↔ HasType n Δ q := by
  induction hc generalizing n Δ with
  | refl => exact Iff.rfl
  | symm hc ih => exact (ih).symm
  | trans hc hd ihc ihd => exact ihc.trans ihd
  | par_comm => exact ⟨HasType.par_comm, HasType.par_comm⟩
  | par_assoc => exact ⟨HasType.par_assoc, HasType.par_assoc_reverse⟩
  | par_nil => exact ⟨HasType.par_nil_elim, HasType.par_nil_intro⟩
  | par_cong hc hd ihc ihd =>
    constructor <;> intro ht
    · obtain ⟨Γ, Ξ, rfl, hdis, hp, hq⟩ := ht.par_inv
      exact HasType.par hdis (ihc.mp hp) (ihd.mp hq)
    · obtain ⟨Γ, Ξ, rfl, hdis, hp, hq⟩ := ht.par_inv
      exact HasType.par hdis (ihc.mpr hp) (ihd.mpr hq)
  | nu_cong hc ih =>
    constructor <;> intro ht
    · obtain ⟨c, hp⟩ := ht.nu_inv
      exact HasType.nu (ih.mp hp)
    · obtain ⟨c, hp⟩ := ht.nu_inv
      exact HasType.nu (ih.mpr hp)
  | scope => exact HasType.scope_iff
  | sum_cong =>
    constructor <;> intro ht <;> exact False.elim ht.finiteLinear
  | out_cong a b hc ih =>
    exact ⟨out_context_transport (fun n Δ => ih),
      out_context_transport (fun n Δ => ih.symm)⟩
  | inp_cong a hc ih =>
    exact ⟨inp_context_transport (fun n Δ => ih),
      inp_context_transport (fun n Δ => ih.symm)⟩
  | repl_cong =>
    constructor <;> intro ht <;> exact False.elim ht.finiteLinear
  | nu_nil => exact ⟨HasType.nu_nil_elim, HasType.nu_nil_intro⟩
  | nu_swap => exact ⟨HasType.nu_swap, HasType.nu_swap_reverse⟩
  | repl_unfold =>
    constructor
    · intro ht
      exact False.elim ht.finiteLinear
    · intro ht
      exact False.elim ht.finiteLinear.2

end Cslib.SessionTypes.Endpoint
