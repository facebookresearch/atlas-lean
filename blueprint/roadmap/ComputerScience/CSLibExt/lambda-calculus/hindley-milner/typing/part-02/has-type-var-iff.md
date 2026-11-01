---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.hasType_var_iff
---

# Substitution lemma

**Substitution lemma**: `Γ ⊢ e : τ` gives `s Γ ⊢ e : s τ` for every type substitution. -/
theorem HasType.subst {Γ : Ctx B} {e : Expr} {τ : Ty B} (hτ : HasType Γ e τ) :
    ∀ s : Subst B, HasType (Γ.subst s) e (τ.subst s) := by
  induction hτ with
  | @var Γ x σ ts hx =>
    intro s
    rw [← inst_substTy]
    exact HasType.var _ (by rw [Ctx.lookup_subst, hx]; rfl)
  | app _ _ ih₁ ih₂ => exact fun s ↦ HasType.app (ih₁ s) (ih₂ s)
  | @lam Γ x e τ₁ τ₂ _ ih =>
    intro s
    have := ih s
    simp only [Ctx.subst, List.map_cons, ← toScheme_subst] at this
    exact HasType.lam this
  | @let_ Γ x e₁ e₂ τ₁ τ₂ _ _ ih₁ ih₂ =>
    intro s
    -- rename the generalized variables of `τ₁` above everything free in `s Γ`
    let s' : Subst B := fun y ↦
      if y ∈ Γ.ftv then s y else Term.var (y + above (Γ.subst s).ftv)
    have hs'Γ : ∀ y, (Γ.subst s).lookup y = (Γ.subst s').lookup y :=
      Ctx.lookup_subst_congr fun y hy ↦ by simp [s', hy]
    have h₁ : HasType (Γ.subst s) e₁ (τ₁.subst s') :=
      (ih₁ s').mono (Ctx.MoreGeneral.of_lookup_eq hs'Γ)
    have h₂ := ih₂ s
    simp only [Ctx.subst, List.map_cons] at h₂
    exact HasType.let_ h₁ (h₂.mono ((Ctx.MoreGeneral.refl _).cons x
      (gen_subst_moreGeneral Γ τ₁ s)))

/-! ### Inversion

## Depends on

- [Ctx](../part-01/ctx.md)
- [Lookup](../part-01/lookup.md)
- [Expr](../part-01/expr.md)
- [Has Type](../part-01/has-type.md)
- [Scheme](../part-01/scheme.md)
- [Inst](../part-01/inst.md)
- [Ty](../part-01/ty.md)

## Proof depends on

- [Gen](../part-01/gen.md)
- [To Scheme](../part-01/to-scheme.md)
- [Term](../../../../unification/basic/part-01/term.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Typing](../../../../../../../sources/v2/CSLibExt.md)
