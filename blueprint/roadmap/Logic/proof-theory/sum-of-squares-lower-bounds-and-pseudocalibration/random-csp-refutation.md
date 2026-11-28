# Refutation of random constraint satisfaction problems

Fix a predicate $P : \{\pm 1\}^k \to \{0,1\}$. A **random instance** of $\mathrm{CSP}(P)$ with $n$ variables and $m = \Delta n$ constraints is obtained by choosing $m$ independent uniformly random $k$-tuples of distinct variables and uniformly random literal signs. Let $\rho(P) = |P^{-1}(1)|/2^k$ be the fraction of assignments satisfying $P$. For every $\varepsilon > 0$ there is $\Delta_0(P, \varepsilon)$ such that for constant $\Delta \ge \Delta_0$, with high probability its optimum is at most $\rho(P) + \varepsilon$. An algorithm **strongly refutes** random instances if, with high probability over the instance, it outputs a certificate that $\operatorname{opt} \le \rho(P) + \varepsilon$, and never outputs such a certificate on an instance with $\operatorname{opt} > \rho(P) + \varepsilon$. A predicate $P$ is **$t$-wise uniform supporting** if some distribution on $P^{-1}(1)$ has all $t$-wise marginals uniform.

## Depends on

- [The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization](lasserre-hierarchy.md)

## Sources

- S. R. Allen, R. O'Donnell, D. Witmer, "How to refute a random CSP", FOCS (2015), arXiv:1505.04383.
- P. K. Kothari, R. Mori, R. O'Donnell, D. Witmer, "Sum of squares lower bounds for refuting any CSP", STOC (2017), arXiv:1701.04521.
