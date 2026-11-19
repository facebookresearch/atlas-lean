# First-order unification

- [Terms for unification](term.md)
- [Substitution](subst.md)
- [Applying a substitution to a term](subst-2.md)
- [Size of a term](size.md)
- [Variables of a term](vars.md)
- [Substitution depends only on the variables of the term](subst-congr.md)
- [Variables of a substituted term](exists-of-mem-vars-subst.md)
- [Variables of a substituted variable occur in the substituted term](vars-subset-vars-subst.md)
- [Occurs check: size bound](size-subst-lt-of-mem.md)
- [Substituting for a variable that does not occur in the substituted term](vars-subst-single-subset.md)
- [Composition of substitutions on first-order terms](comp.md)
- [Single-variable substitution on first-order terms](single.md)
- [Absorbing a single-variable substitution](single-comp-eq.md)
- [A term is fixed by substituting it for a variable it avoids](subst-single-of-not-mem.md)

## Unifiers

- [Lists of equations](equations.md)
- [Unifier of a list of equations](unifies.md)
- [Most general unifier](is-mgu.md)
- [Applying a substitution to a list of equations](subst-eqs.md)
- [Variables of a list of equations](eq-vars.md)
- [Total size of a list of equations](eq-size.md)
- [Eliminating a solved variable lowers the number of variables](card-eq-vars-elim-lt.md)

## The algorithm

- [Martelli–Montanari unification](unify.md)

## Correctness

- [Specification of a unification result](unify-spec.md)
- [Lists of equations with the same unifiers satisfy the same specification](congr.md)
- [Failure is correct when the first equation has no unifier](none-of-head.md)
- [The elimination step preserves the unification specification](elim.md)
- [Soundness of unification](unifies-unify.md)
- [Most generality of unification](unify-eq-some-comp.md)
- [Unification returns a most general unifier](is-mgu-unify.md)
- [Unification returns an idempotent substitution](unify-comp-self.md)
- [Completeness of unification](unify-eq-none-iff.md)

## Variables of the result

- [The elimination step of unification introduces no variables](vars-single-comp-subset.md)
- [Unification introduces no new variables](vars-unify-subset.md)
