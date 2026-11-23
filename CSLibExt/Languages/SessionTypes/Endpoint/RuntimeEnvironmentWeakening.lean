/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeInversion

/-!
# Shared-environment extension with actual owned-name freshness

Adding permissions is not blind monotonicity: the enlarged environment must
be separated from ALL actual owned names, completed caps included. Constructor
induction derives this condition for lifted/received/BODY contexts as well.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- Old shared declarations retain their EXACT signature in the larger environment. -/
def EnvExtends (Γ Ξ : ServiceEnv) : Prop :=
  ∀ s sig, Γ.lookup s = some sig → Ξ.lookup s = some sig

/-- A declared guarded template remains such under literal signature extension. -/
theorem ServiceTemplate.env_extend {Γ Ξ : ServiceEnv} {p : Proc}
    (h : ServiceTemplate Γ p) (he : EnvExtends Γ Ξ) : ServiceTemplate Ξ p := by
  induction p with
  | nil => trivial
  | out => exact False.elim h
  | inp a p ih =>
    obtain ⟨s, ha, hs⟩ := h
    obtain ⟨sig, hsig⟩ := Finmap.mem_iff.mp hs
    exact ⟨s, ha, Finmap.mem_of_lookup_eq_some (he s sig hsig)⟩
  | par p q ihp ihq => exact ⟨ihp h.1, ihq h.2⟩
  | nu p ih => exact ih h
  | repl p ih => exact ih h
  | sum => exact False.elim h

/-- General Γ-extension requires static separation of ALL actual owned names.
The proof establishes fresh lifted/private/received BODY names, rather than
assuming environment monotonicity or carrying a future/result field. -/
theorem HasType.env_extend {n : Nat} {Γ Ξ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) (he : EnvExtends Γ Ξ) (hs : Separated Ξ Δ) : HasType n Ξ Δ p := by
  revert hs
  induction h with
  | nil hc hscope hd =>
    intro hs
    exact HasType.nil hc hscope hs
  | @outName n Γ Δ e c b s p hg hd hc hh ha hb hp ih =>
    intro hs
    exact HasType.outName hg hs hc hh ha hb (ih he (hs.insert e _ (hs e c hc)))
  | @inpName n Γ Δ e c s p hg hd hc hh ha hp ih =>
    intro hs
    exact HasType.inpName hg hs hc hh ha (ih he ((hs.insert e _ (hs e c hc)).lift 0))
  | @outEndpoint n Γ Δ e d c v k t s p hg hd hc hh hv heq hne ha hb hp ih =>
    intro hs
    exact HasType.outEndpoint hg hs hc hh hv heq hne ha hb
      (ih he ((hs.erase d).insert e _ (hs e c hc)))
  | @inpEndpoint n Γ Δ e c r k t s p hg hd hc hh ha hp ih =>
    intro hs
    apply HasType.inpEndpoint hg hs hc hh ha
    apply ih he
    apply ((hs.insert e _ (hs e c hc)).lift 0).insert
    intro s sig hs hn
    cases hn
  | @invoke n Γ Δ s sig e v p hsig hd hv hr heq hg hb hp ih =>
    intro hs
    exact HasType.invoke (he s sig hsig) hs hv hr heq hg hb (ih he (hs.erase e))
  | @accept n Γ Δ s sig p hsig hc hscope hd hp ih =>
    intro hs
    apply HasType.accept (he s sig hsig) hc hscope hs
    apply ih he
    apply separated_singleton
    intro s sig hs hn
    cases hn
  | @serve n Γ Δ p ht hp hc hscope hd ih =>
    intro hs
    exact HasType.serve (ht.env_extend he) (ih he (separated_empty Ξ)) hc hscope hs
  | par hd hp hq ihp ihq =>
    intro hs
    exact HasType.par hd (ihp he hs.union_left) (ihq he (hs.union_right hd))
  | @nu n Γ Δ c p hd hp ih =>
    intro hs
    exact HasType.nu hs (ih he (hs.bind c))

end Cslib.SessionTypes.Endpoint.Runtime
