# Developability of finite permutoids and rigid pseudogroups is undecidable

No algorithm decides whether a permutoid on a finite set can be completed to a finite permutation group, proving a conjecture of Cameron; nor whether a finite rigid pseudogroup has a finite development.

A permutoid $(\Pi; X)$ is a set $\Pi$ of partial permutations of a set $X$ that contains the identity and is such that partial compositions, when defined, have at most one extension in $\Pi$. A finite permutoid is developable (completable) if it embeds, compatibly with partial compositions, in a finite permutation group acting on a finite set containing $X$. There does not exist an algorithm that, given a finite permutoid $(\Pi; X)$, can determine whether or not it is developable (Theorem 4.1 of the source); this is Cameron's conjecture of 2004.

The same construction shows that no algorithm determines whether a finite rigid pseudogroup has a finite development (Theorem 5.2 of the source), that is, a finite set $Y \supseteq X$ and a finite group acting freely on $Y$ such that each non-empty element of the pseudogroup is a restriction of a group element.

A naive search finds a completion when one exists, so the developable finite permutoids form a recursively enumerable set that is not recursive.

## Depends on

- [Group](../../group-basics/group.md)
- [Action of a monoid or a group on a set](../group-actions/group-action.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Having a proper finite-index subgroup is undecidable for finitely presented groups](../../profinite-and-topological-groups/triviality-problem-for-profinite-completions/proper-finite-index-subgroup-undecidable.md)

## Expansion

To a finite presentation of a group $G$ and a radius $\rho$ the source attaches the permutoid of left multiplications between balls of radius $\rho$ and $2\rho$ in the Cayley graph. When $\rho$ is at least half the longest relator length and the presentations come from a class with uniformly solvable word problem, $G$ has a non-trivial finite quotient exactly when one of the finitely many non-trivial quotient permutoids is developable (Cameron observed one direction). The authors' earlier theorem that no algorithm decides whether a finitely presented group (in such a class) has a non-trivial finite quotient then gives clause 1; translating to rigid pseudogroups gives clause 2.

## Sources

- M. R. Bridson and H. Wilton, "Undecidability and the developability of permutoids and rigid pseudogroups", Forum of Mathematics, Sigma 5 (2017), article e10, https://doi.org/10.1017/fms.2017.6; read in arXiv:1405.4368v2 (with an appendix by B. Steinberg) (Theorems 4.1 and 5.2 of arXiv:1405.4368v2).
