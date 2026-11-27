# Monotone interpretations give reduction orderings

Let $\mathcal A$ be a $\Sigma$-algebra with universe $U_{\mathcal A}$, interpreting each function symbol $f$ of arity $n$ as a function $f_{\mathcal A} : U_{\mathcal A}^n \to U_{\mathcal A}$, and let $\succ$ be a well-founded strict partial ordering on $U_{\mathcal A}$. For terms $s, t \in T_\Sigma(X)$ put $s \succ_{\mathcal A} t$ if $\mathcal A(\beta)(s) \succ \mathcal A(\beta)(t)$ for every assignment $\beta : X \to U_{\mathcal A}$, where $\mathcal A(\beta)$ evaluates terms. Call $f_{\mathcal A}$ *monotone* if $a \succ a'$ implies $f_{\mathcal A}(b_1, \dots, a, \dots, b_n) \succ f_{\mathcal A}(b_1, \dots, a', \dots, b_n)$ for all arguments.

1. $\succ_{\mathcal A}$ is stable under substitutions.
2. If $f_{\mathcal A}$ is monotone for every function symbol $f$, then $\succ_{\mathcal A}$ is compatible with $\Sigma$-operations, and $\succ_{\mathcal A}$ is a [reduction ordering](reduction-ordering.md).

Polynomial orderings, which interpret symbols over $\{n \in \mathbb N \mid n \ge 1\}$ by polynomials with natural coefficients in which a nullary symbol is interpreted by a natural number at least $1$ and every argument of an $n$-ary symbol, $n \ge 1$, occurs with a nonzero coefficient in some monomial, are an instance.

## Depends on

- [Reduction ordering](reduction-ordering.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, the interpretation method, Lemmas 4.20 and 4.21 and Theorem 4.22, pp. 115–116, and polynomial orderings, p. 116.
