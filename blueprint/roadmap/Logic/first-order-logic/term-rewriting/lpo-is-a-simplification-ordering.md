# The lexicographic path ordering is a simplification ordering

For every finite signature $\Sigma$ and precedence $\succ$, the [lexicographic path ordering](lexicographic-path-ordering.md) $\succ_{\mathrm{lpo}}$ is a [simplification ordering](simplification-ordering.md) on $T_\Sigma(X)$: it is irreflexive and transitive, stable under substitutions, compatible with $\Sigma$-operations and has the subterm property. Consequently it is a [reduction ordering](reduction-ordering.md).

**Proof.** Each property is proved by induction on the sum of the sizes of the terms involved, with a case analysis over the clauses of the definition. Well-foundedness then follows from Dershowitz's theorem, as $\Sigma$ is finite.

## Depends on

- [Lexicographic path ordering](lexicographic-path-ordering.md)
- [Simplification ordering](simplification-ordering.md)
- [Reduction ordering](reduction-ordering.md)

## Proof depends on

- [Variable condition for the lexicographic path ordering](lpo-variable-condition.md)
- [Simplification orderings over a finite signature are well-founded](dershowitz-s-theorem-on-simplification-orderings.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, Theorem 4.29 and its proof sketch, p. 120, which refers to F. Baader and T. Nipkow, *Term Rewriting and All That*, Cambridge University Press, 1998, pp. 119–120, for details.
