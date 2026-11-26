# Refutation of random constraint satisfaction problems

Fix a predicate $P : \{\pm 1\}^k \to \{0,1\}$. A **random instance** of $\mathrm{CSP}(P)$ with $n$ variables and $m = \Delta n$ constraints is obtained by choosing $m$ independent uniformly random $k$-tuples of distinct variables and uniformly random literal signs. With high probability its optimum is at most $\rho(P) + o(1)$ when $\Delta$ is a large constant. An algorithm **strongly refutes** random instances if, with high probability over the instance, it outputs a certificate that $\operatorname{opt} \le \rho(P) + \varepsilon$, and never outputs such a certificate on an instance with $\operatorname{opt} > \rho(P) + \varepsilon$. A predicate $P$ is **$t$-wise uniform supporting** if some distribution on $P^{-1}(1)$ has all $t$-wise marginals uniform.

## Depends on

- [The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization](lasserre-hierarchy.md)

## Sources

- S. R. Allen, R. O'Donnell, D. Witmer, "How to refute a random CSP", FOCS (2015), arXiv:1505.04383.
- P. K. Kothari, R. Mori, R. O'Donnell, D. Witmer, "Sum of squares lower bounds for refuting any CSP", STOC (2017), arXiv:1701.04521.
