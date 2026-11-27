# Magic-set rewriting of Datalog queries is correct

Given a Datalog query $(P, q)$ whose goal binds any set of its arguments to constants, possibly none, the magic-set rewriting (generalized
supplementary magic) produces a Datalog query $(P^m, q^m)$ from the adorned version of $(P, q)$: for each adorned rule
it adds supplementary relations that carry bindings from left to right through the body, input (magic) relations that
collect the bindings passed to intensional subgoals, a seed fact for the bindings of the goal (a nullary seed fact when no argument is bound), and a query rule. Then
(a) on every input instance $I$, $(P^m, q^m)$ computes the same answer as $(P, q)$; and (b) the set of facts produced
by the improved semi-naive evaluation of $(P^m, q^m)$ on $I$ equals the set of facts produced by query-subquery (QSQ)
evaluation of $(P, q)$ on $I$.

## Expansion

This node states the result informally in its definitions. A good expansion adds pages for adorned Datalog programs
(binding patterns and sideways information passing), the query-subquery evaluation and the improved semi-naive
algorithm of the source's Sections 13.1–13.2, and then states the rewriting rule by rule.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Semi-naive evaluation is correct](semi-naive-evaluation-is-correct.md)
- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Section 13.3, Figure 13.3 and Theorem 13.3.1 (pp. 325–327).
