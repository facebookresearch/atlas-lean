---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.gen_subst_moreGeneral
---

# Gen subst more General

The renaming step of the substitution lemma: after renaming the generalized variables of
`τ` above `N`, generalizing in `s Γ` is more general than substituting into `gen Γ τ`.

## Depends on

- [Ctx](../part-01/ctx.md)
- [Ftv](../part-01/ftv.md)
- [Subst](../part-01/subst.md)
- [More General](../part-01/more-general.md)
- [Subst Ty](../part-01/subst-ty.md)
- [Ty](../part-01/ty.md)
- [Above](above.md)
- [Gen](../part-01/gen.md)
- [Subst](../../../../unification/basic/part-01/subst.md)
- [Term](../../../../unification/basic/part-01/term.md)
- [Subst](../../../../unification/basic/part-01/subst-2.md)

## Proof depends on

- [Lookup](../part-01/lookup.md)
- [Visible Vars](../part-01/visible-vars.md)
- [Scheme](../part-01/scheme.md)
- [Eval](../part-01/eval.md)
- [Inst](../part-01/inst.md)
- [To Scheme](../part-01/to-scheme.md)
- [Exists of mem vars subst](../../../../unification/basic/part-01/exists-of-mem-vars-subst.md)
- [Subst congr](../../../../unification/basic/part-01/subst-congr.md)
- [Vars](../../../../unification/basic/part-01/vars.md)
- [Vars subset vars subst](../../../../unification/basic/part-01/vars-subset-vars-subst.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Typing](../../../../../../../sources/v2/CSLibExt.md)
