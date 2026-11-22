/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeScope

/-!
# General runtime typing under canonical structural congruence

All sixteen Cong constructors retain SAME Γ, n and Δ. Replication is admitted
only through structural guarded templates with exact empty BODY ownership.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

private theorem par_comm {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc}
    (h : HasType n Γ Δ (.par p q)) : HasType n Γ Δ (.par q p) := by
  obtain ⟨Λ, Ξ, rfl, hd, hp, hq⟩ := h.par_inv
  rw [Finmap.union_comm_of_disjoint hd]
  exact HasType.par (hd.symm _ _) hq hp

private theorem par_assoc {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q r : Proc}
    (h : HasType n Γ Δ (.par (.par p q) r)) : HasType n Γ Δ (.par p (.par q r)) := by
  obtain ⟨Λ, Ξ, rfl, hd, hpq, hr⟩ := h.par_inv
  obtain ⟨A, B, rfl, hab, hp, hq⟩ := hpq.par_inv
  obtain ⟨ha, hb⟩ := (Finmap.disjoint_union_left A B Ξ).mp hd
  rw [Finmap.union_assoc]
  exact HasType.par ((Finmap.disjoint_union_right A B Ξ).mpr ⟨hab, ha⟩)
    hp (HasType.par hb hq hr)

private theorem par_assoc_reverse {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q r : Proc}
    (h : HasType n Γ Δ (.par p (.par q r))) : HasType n Γ Δ (.par (.par p q) r) := by
  obtain ⟨A, Λ, rfl, hd, hp, hqr⟩ := h.par_inv
  obtain ⟨B, C, rfl, hbc, hq, hr⟩ := hqr.par_inv
  obtain ⟨hab, hac⟩ := (Finmap.disjoint_union_right A B C).mp hd
  rw [← Finmap.union_assoc]
  exact HasType.par ((Finmap.disjoint_union_left A B C).mpr ⟨hac, hbc⟩)
    (HasType.par hab hp hq) hr

private theorem par_nil_elim {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ (.par p .nil)) : HasType n Γ Δ p := by
  obtain ⟨Λ, Ξ, rfl, hd, hp, hn⟩ := h.par_inv
  exact hp.weaken_completed_union hd hn.nil_inv.1 hn.nil_inv.2.1 hn.separated

private theorem par_nil_intro {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) : HasType n Γ Δ (.par p .nil) := by
  have hn : HasType n Γ ∅ .nil := HasType.nil Context.completed_empty
    (fun _ he => False.elim (Finmap.notMem_empty he)) (separated_empty Γ)
  have ht := HasType.par (fun _ _ he => Finmap.notMem_empty he) h hn
  simpa only [Finmap.union_empty] using ht

private theorem nu_swap {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ (.nu (.nu p))) : HasType n Γ Δ (.nu (.nu (swapProc 0 p))) := by
  obtain ⟨c, hc⟩ := h.nu_inv
  obtain ⟨d, hd⟩ := hc.nu_inv
  have ht := hd.swap (k := 0) (by omega)
  rw [Context.swap_bind_bind] at ht
  exact HasType.nu (c := d) h.separated (HasType.nu (c := c) (h.separated.bind d) ht)

private theorem nu_swap_reverse {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ (.nu (.nu (swapProc 0 p)))) : HasType n Γ Δ (.nu (.nu p)) := by
  have ht := nu_swap h
  rw [swapProc_swapProc] at ht
  exact ht

private theorem repl_unfold {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ (.repl p)) : HasType n Γ Δ (.par p (.repl p)) := by
  obtain ⟨hc, hs, hd, ht, hp⟩ := h.repl_inv
  have hleft := hp.template_reannotate ht hc hs hd
  have hright : HasType n Γ ∅ (.repl p) := HasType.serve ht hp Context.completed_empty
    (fun _ he => False.elim (Finmap.notMem_empty he)) (separated_empty Γ)
  have hpar := HasType.par (fun _ _ he => Finmap.notMem_empty he) hleft hright
  simpa only [Finmap.union_empty] using hpar

private theorem repl_unfold_reverse {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ (.par p (.repl p))) : HasType n Γ Δ (.repl p) := by
  obtain ⟨Λ, Ξ, hsplit, hd, hp, hq⟩ := h.par_inv
  have ht := hq.repl_body_empty.1
  exact HasType.serve ht (hp.template_empty ht) (h.template_completed ⟨ht, ht⟩)
    h.context_closedAt h.separated

private theorem out_context {Γ : ServiceEnv} {p p' : Proc} {a b : Name}
    (ih : ∀ n Δ, HasType n Γ Δ p ↔ HasType n Γ Δ p') {n : Nat} {Δ : Context}
    (h : HasType n Γ Δ (.out a b p)) : HasType n Γ Δ (.out a b p') := by
  cases h with
  | outName hg hd hc hh ha hb hp => exact HasType.outName hg hd hc hh ha hb ((ih _ _).mp hp)
  | outEndpoint hg hd hc hh hv he hne ha hb hp =>
    exact HasType.outEndpoint hg hd hc hh hv he hne ha hb ((ih _ _).mp hp)
  | invoke hs hd hv hr he hg hb hp => exact HasType.invoke hs hd hv hr he hg hb ((ih _ _).mp hp)

private theorem inp_context {Γ : ServiceEnv} {p p' : Proc} {a : Name}
    (ih : ∀ n Δ, HasType n Γ Δ p ↔ HasType n Γ Δ p') {n : Nat} {Δ : Context}
    (h : HasType n Γ Δ (.inp a p)) : HasType n Γ Δ (.inp a p') := by
  cases h with
  | inpName hg hd hc hh ha hp => exact HasType.inpName hg hd hc hh ha ((ih _ _).mp hp)
  | inpEndpoint hg hd hc hh ha hp => exact HasType.inpEndpoint hg hd hc hh ha ((ih _ _).mp hp)
  | accept hs hc hscope hd hp => exact HasType.accept hs hc hscope hd ((ih _ _).mp hp)

/-- ALL16 canonical Cong rules preserve the whole runtime derivation at exactly
SAME Γ/n/Δ, including guarded replicated templates, completed ambient annotations,
and actual runtime delegation continuations. No typing-up-to-Cong constructor. -/
theorem HasType.cong_iff {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p q : Proc} (hc : Cong p q) :
    HasType n Γ Δ p ↔ HasType n Γ Δ q := by
  induction hc generalizing n Δ with
  | refl => exact Iff.rfl
  | symm hc ih => exact ih.symm
  | trans hc hd ihc ihd => exact ihc.trans ihd
  | par_comm => exact ⟨par_comm, par_comm⟩
  | par_assoc => exact ⟨par_assoc, par_assoc_reverse⟩
  | par_nil => exact ⟨par_nil_elim, par_nil_intro⟩
  | par_cong hc hd ihc ihd =>
    constructor <;> intro ht
    · obtain ⟨Λ, Ξ, rfl, hd, hp, hq⟩ := ht.par_inv
      exact HasType.par hd (ihc.mp hp) (ihd.mp hq)
    · obtain ⟨Λ, Ξ, rfl, hd, hp, hq⟩ := ht.par_inv
      exact HasType.par hd (ihc.mpr hp) (ihd.mpr hq)
  | nu_cong hc ih =>
    constructor <;> intro ht
    · obtain ⟨c, hp⟩ := ht.nu_inv
      exact HasType.nu ht.separated (ih.mp hp)
    · obtain ⟨c, hp⟩ := ht.nu_inv
      exact HasType.nu ht.separated (ih.mpr hp)
  | scope => exact HasType.scope_iff
  | sum_cong => constructor <;> intro ht <;> cases ht
  | out_cong a b hc ih =>
    exact ⟨out_context (fun n Δ => ih), out_context (fun n Δ => ih.symm)⟩
  | inp_cong a hc ih =>
    exact ⟨inp_context (fun n Δ => ih), inp_context (fun n Δ => ih.symm)⟩
  | repl_cong hc ih =>
    constructor <;> intro h
    · obtain ⟨hcomplete, hs, hd, ht, hp⟩ := h.repl_inv
      exact HasType.serve ((ServiceTemplate.cong_iff hc).mp ht) (ih.mp hp) hcomplete hs hd
    · obtain ⟨hcomplete, hs, hd, ht, hp⟩ := h.repl_inv
      exact HasType.serve ((ServiceTemplate.cong_iff hc).mpr ht) (ih.mpr hp) hcomplete hs hd
  | nu_nil => exact ⟨HasType.nu_nil_elim, HasType.nu_nil_intro⟩
  | nu_swap => exact ⟨nu_swap, nu_swap_reverse⟩
  | repl_unfold => exact ⟨repl_unfold, repl_unfold_reverse⟩

end Cslib.SessionTypes.Endpoint.Runtime
