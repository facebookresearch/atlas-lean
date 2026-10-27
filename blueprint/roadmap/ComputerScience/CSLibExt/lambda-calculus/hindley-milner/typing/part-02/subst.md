---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.HasType.subst
---

# Substitution lemma

**Substitution lemma**: `Γ ⊢ e : τ` gives `s Γ ⊢ e : s τ` for every type substitution.

## Depends on

- [Ctx](../part-01/ctx.md)
- [Subst](../part-01/subst.md)
- [Expr](../part-01/expr.md)
- [Has Type](../part-01/has-type.md)
- [Ty](../part-01/ty.md)
- [Subst](../../../../unification/basic/part-01/subst.md)
- [Subst](../../../../unification/basic/part-01/subst-2.md)

## Proof depends on

- [More General](../part-01/more-general-2.md)
- [Cons](cons.md)
- [Of lookup eq](of-lookup-eq.md)
- [Ftv](../part-01/ftv.md)
- [Lookup](../part-01/lookup.md)
- [Lookup subst congr](../part-01/lookup-subst-congr.md)
- [Generality](mono.md)
- [Scheme](../part-01/scheme.md)
- [Inst](../part-01/inst.md)
- [Subst Ty](../part-01/subst-ty.md)
- [Above](above.md)
- [Gen](../part-01/gen.md)
- [Gen subst more General](gen-subst-more-general.md)
- [Inst subst Ty](../part-01/inst-subst-ty.md)
- [To Scheme](../part-01/to-scheme.md)
- [Term](../../../../unification/basic/part-01/term.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Typing](../../../../../../../sources/v2/CSLibExt.md)
