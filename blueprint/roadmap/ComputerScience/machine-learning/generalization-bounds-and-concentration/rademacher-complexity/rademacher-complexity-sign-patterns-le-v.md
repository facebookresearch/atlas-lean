# Rademacher complexity of a VC class, explicit rate

Let $\mathcal{A}$ be a nonempty family of subsets of the sample $\{1, \dots, n\}$ with VC dimension $d \ge 1$, and let $A$ be the set of the $\pm 1$ sign patterns of its members. Then

$$R(A) \le \sqrt{\frac{2 d \log(e n / d)}{n}}.$$

This is the bound in terms of $\sum_{k \le d} \binom{n}{k}$ combined with the counting bound $\sum_{k \le d} \binom{n}{k} \le (e n / d)^d$; the hypothesis $d \ge 1$ excludes the trivial case, and $d \le n$ holds automatically. Through a risk bound such as Bartlett and Mendelson's Theorem 8, it gives the $O(\sqrt{d \log(n/d) / n})$ generalization rate of empirical risk minimization over a class of VC dimension $d$.

## Informally uses

- [Rademacher complexity of a VC class](rademacher-complexity-sign-patterns-le.md): builds on.
- [Partial binomial sums are at most $(eD/r)^r$](../../../../Combinatorics/binomial-coefficients/binomial-sums/bounds-on-partial-sums-of-binomial-coefficients/sum-choose-le-exp-mul-div-pow.md): builds on.
- [The VC dimension is at most the size of the ground set](../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md): builds on, for the hypothesis $d \le n$ of the counting bound.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Section 28.1 (the bound $R(A) \le \sqrt{2 d \log(e m / d) / m}$ in the proof of the agnostic upper bound).
