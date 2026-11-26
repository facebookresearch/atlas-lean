# Monotone interpretations give reduction orderings

Let $\mathcal A$ be a $\Sigma$-algebra with universe $U_{\mathcal A}$, interpreting each function symbol $f$ of arity $n$ as a function $f_{\mathcal A} : U_{\mathcal A}^n \to U_{\mathcal A}$, and let $\succ$ be a well-founded strict partial ordering on $U_{\mathcal A}$. For terms $s, t \in T_\Sigma(X)$ put $s \succ_{\mathcal A} t$ if $\mathcal A(\beta)(s) \succ \mathcal A(\beta)(t)$ for every assignment $\beta : X \to U_{\mathcal A}$, where $\mathcal A(\beta)$ evaluates terms. Call $f_{\mathcal A}$ *monotone* if $a \succ a'$ implies $f_{\mathcal A}(b_1, \dots, a, \dots, b_n) \succ f_{\mathcal A}(b_1, \dots, a', \dots, b_n)$ for all arguments.

If $f_{\mathcal A}$ is monotone for every function symbol $f$, then $\succ_{\mathcal A}$ is a [reduction ordering](reduction-ordering.md).

**Proof.** $\succ_{\mathcal A}$ is [stable under substitutions](termination/interpretation-orderings-are-stable-under-substitutions.md) and, by monotonicity, [compatible with operations](termination/monotone-interpretation-orderings-are-compatible-with-operations.md). It is irreflexive, transitive and well-founded because $\succ$ is: an infinite descending chain $s_1 \succ_{\mathcal A} s_2 \succ_{\mathcal A} \cdots$ would give one in $U_{\mathcal A}$ under any fixed assignment.

Polynomial orderings, which interpret symbols over $\{n \in \mathbb N \mid n \ge 1\}$ by polynomials with natural coefficients in which every argument occurs, are an instance.

## Depends on

- [Reduction ordering](reduction-ordering.md)

## Proof depends on

- [Interpretation orderings are stable under substitutions](termination/interpretation-orderings-are-stable-under-substitutions.md)
- [Monotone interpretation orderings are compatible with operations](termination/monotone-interpretation-orderings-are-compatible-with-operations.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, the interpretation method, Theorem 4.22 and its proof, p. 116, and polynomial orderings, p. 116.
