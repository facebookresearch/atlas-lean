/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionScope
public import CSLibExt.Languages.SessionTypes.Endpoint.SwapTyping
public import CSLibExt.Languages.SessionTypes.Endpoint.ConversionCong

/-!
# Conversion priority refinement under canonical structural congruence
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- Commutation retains the actual disjoint split and both ranked subterms. -/
theorem RankedType.par_comm {n : Nat} {Δ : Context} {p q : Proc}
    (h : RankedType n Δ (.par p q)) : RankedType n Δ (.par q p) := by
  obtain ⟨Γ, Ξ, rfl, hd, hp, hq⟩ := h.par_inv
  rw [Finmap.union_comm_of_disjoint hd]
  exact RankedType.par (hd.symm _ _) hq hp

/-- Reassociation derives all pairwise disjointness from actual typing. -/
theorem RankedType.par_assoc {n : Nat} {Δ : Context} {p q r : Proc}
    (h : RankedType n Δ (.par (.par p q) r)) : RankedType n Δ (.par p (.par q r)) := by
  obtain ⟨Γ, Ξ, rfl, hd, hpq, hr⟩ := h.par_inv
  obtain ⟨A, B, rfl, hab, hp, hq⟩ := hpq.par_inv
  obtain ⟨ha, hb⟩ := (Finmap.disjoint_union_left A B Ξ).mp hd
  rw [Finmap.union_assoc]
  exact RankedType.par ((Finmap.disjoint_union_right A B Ξ).mpr ⟨hab, ha⟩)
    hp (RankedType.par hb hq hr)

/-- Reverse reassociation retains exact contexts and guard checks. -/
theorem RankedType.par_assoc_reverse {n : Nat} {Δ : Context} {p q r : Proc}
    (h : RankedType n Δ (.par p (.par q r))) : RankedType n Δ (.par (.par p q) r) := by
  obtain ⟨A, Γ, rfl, hd, hp, hqr⟩ := h.par_inv
  obtain ⟨B, C, rfl, hbc, hq, hr⟩ := hqr.par_inv
  obtain ⟨hab, hac⟩ := (Finmap.disjoint_union_right A B C).mp hd
  rw [← Finmap.union_assoc]
  exact RankedType.par ((Finmap.disjoint_union_left A B C).mpr ⟨hac, hbc⟩)
    (RankedType.par hab hp hq) hr

/-- Nil's actual completed ownership can be reattached without new dependencies. -/
theorem RankedType.par_nil_elim {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ (.par p .nil)) : RankedType n Δ p := by
  obtain ⟨Γ, Ξ, rfl, hd, hp, hn⟩ := h.par_inv
  exact hp.weaken_completed_union hd hn.hasType.nil_inv.1 hn.hasType.nil_inv.2

/-- Nil introduction allocates an empty ownership context, not an active frame. -/
theorem RankedType.par_nil_intro {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ p) : RankedType n Δ (.par p .nil) := by
  have hn : RankedType n ∅ .nil := RankedType.nil
    (by intro e c he; simp at he) (by intro e he; exact False.elim (Finmap.notMem_empty he))
  have ht := RankedType.par ((Finmap.disjoint_empty Δ).symm _ _) h hn
  simpa only [Finmap.union_empty] using ht

/-- Restricting nil is equivalent to its original completed/scoped interface. -/
theorem RankedType.nu_nil_elim {n : Nat} {Δ : Context}
    (h : RankedType n Δ (.nu .nil)) : RankedType n Δ .nil :=
  RankedType.nil_of_hasType h.hasType.nu_nil_elim

/-- A completed fresh pair can be introduced around nil without changing guards. -/
theorem RankedType.nu_nil_intro {n : Nat} {Δ : Context}
    (h : RankedType n Δ .nil) : RankedType n Δ (.nu .nil) := by
  obtain ⟨c, hb⟩ := h.hasType.nu_nil_intro.nu_inv
  exact RankedType.nu (RankedType.nil_of_hasType hb)

/-- Swapping the two restrictions preserves all guard constraints by the
GENERAL capture-safe rename theorem and the exact four-role context equation. -/
theorem RankedType.nu_swap {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ (.nu (.nu p))) : RankedType n Δ (.nu (.nu (swapProc 0 p))) := by
  obtain ⟨c, hc⟩ := h.nu_inv
  obtain ⟨d, hd⟩ := hc.nu_inv
  have hf : Set.InjOn (Key.mapName (swapNameAt 0)) {e | e ∈ Context.bind d (Context.bind c Δ)} :=
    fun _ _ _ _ he => Key.mapName_injective (swapNameAt_injective 0) he
  have ht := hd.rename (fun a ha => (closedAt_swapName_iff _ 0 (by omega) a).mpr ha) hf
  rw [mapProc_swapNameAt] at ht
  change RankedType (n + 1 + 1) (Context.swap 0 (Context.bind d (Context.bind c Δ)))
    (swapProc 0 p) at ht
  rw [Context.swap_bind_bind] at ht
  exact RankedType.nu (c := d) (RankedType.nu (c := c) ht)

/-- Reverse restriction swap uses the canonical process involution. -/
theorem RankedType.nu_swap_reverse {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ (.nu (.nu (swapProc 0 p)))) : RankedType n Δ (.nu (.nu p)) := by
  have ht := h.nu_swap
  rw [swapProc_swapProc] at ht
  exact ht

private theorem ranked_out_context {p p' : Proc} {a b : Name}
    (ih : ∀ n Δ, RankedType n Δ p ↔ RankedType n Δ p') {n : Nat} {Δ : Context}
    (h : RankedType n Δ (.out a b p)) : RankedType n Δ (.out a b p') := by
  cases h with
  | outName hg hc hs ha hb hp => exact RankedType.outName hg hc hs ha hb ((ih _ _).mp hp)
  | outEndpoint hg hc hs hd hv he ha hb hp =>
    exact RankedType.outEndpoint hg hc hs hd hv he ha hb ((ih _ _).mp hp)

private theorem ranked_inp_context {p p' : Proc} {a : Name}
    (ih : ∀ n Δ, RankedType n Δ p ↔ RankedType n Δ p') {n : Nat} {Δ : Context}
    (h : RankedType n Δ (.inp a p)) : RankedType n Δ (.inp a p') := by
  cases h with
  | inpName hg hc hs ha hp => exact RankedType.inpName hg hc hs ha ((ih _ _).mp hp)
  | inpEndpoint hg hc hs ha hp => exact RankedType.inpEndpoint hg hc hs ha ((ih _ _).mp hp)

/-- Every canonical Cong constructor preserves the whole priority refinement
at exactly the same context and ambient depth. Unsupported sum/replication
constructors are impossible by the invariant DERIVED from refinement typing. -/
theorem RankedType.cong_iff {n : Nat} {Δ : Context} {p q : Proc} (hc : Cong p q) :
    RankedType n Δ p ↔ RankedType n Δ q := by
  induction hc generalizing n Δ with
  | refl => exact Iff.rfl
  | symm hc ih => exact ih.symm
  | trans hc hd ihc ihd => exact ihc.trans ihd
  | par_comm => exact ⟨RankedType.par_comm, RankedType.par_comm⟩
  | par_assoc => exact ⟨RankedType.par_assoc, RankedType.par_assoc_reverse⟩
  | par_nil => exact ⟨RankedType.par_nil_elim, RankedType.par_nil_intro⟩
  | par_cong hc hd ihc ihd =>
    constructor <;> intro ht
    · obtain ⟨Γ, Ξ, rfl, hd, hp, hq⟩ := ht.par_inv
      exact RankedType.par hd (ihc.mp hp) (ihd.mp hq)
    · obtain ⟨Γ, Ξ, rfl, hd, hp, hq⟩ := ht.par_inv
      exact RankedType.par hd (ihc.mpr hp) (ihd.mpr hq)
  | nu_cong hc ih =>
    constructor <;> intro ht
    · obtain ⟨c, hp⟩ := ht.nu_inv
      exact RankedType.nu (ih.mp hp)
    · obtain ⟨c, hp⟩ := ht.nu_inv
      exact RankedType.nu (ih.mpr hp)
  | scope => exact RankedType.scope_iff
  | sum_cong => constructor <;> intro ht <;> exact False.elim ht.hasType.finiteLinear
  | out_cong a b hc ih =>
    exact ⟨ranked_out_context (fun n Δ => ih), ranked_out_context (fun n Δ => ih.symm)⟩
  | inp_cong a hc ih =>
    exact ⟨ranked_inp_context (fun n Δ => ih), ranked_inp_context (fun n Δ => ih.symm)⟩
  | repl_cong => constructor <;> intro ht <;> exact False.elim ht.hasType.finiteLinear
  | nu_nil => exact ⟨RankedType.nu_nil_elim, RankedType.nu_nil_intro⟩
  | nu_swap => exact ⟨RankedType.nu_swap, RankedType.nu_swap_reverse⟩
  | repl_unfold =>
    constructor
    · intro ht
      exact False.elim ht.hasType.finiteLinear
    · intro ht
      exact False.elim ht.hasType.finiteLinear.2

end Cslib.SessionTypes.Endpoint.Conversion
