# The VC dimension is at most the size of the ground set

For a family $\mathcal{A}$ of subsets of a finite set $\alpha$, the VC dimension of $\mathcal{A}$, the largest size of a set it shatters ($0$ if it shatters none), is at most $\lvert \alpha \rvert$, because every shattered set is a subset of $\alpha$. The bound is attained by the family of all subsets.

By the Sauer–Shelah lemma, $\lvert \mathcal{A} \rvert \le \sum_{k \le d} \binom{\lvert \alpha \rvert}{k}$ with $d$ the VC dimension. This inequality is the hypothesis $d \le n$ of the [counting bound](../binomial-coefficients/binomial-sums/bounds-on-partial-sums-of-binomial-coefficients/sum-choose-le-exp-mul-div-pow.md) that turns that sum into $(e n / d)^d$.

## Background

- [Rademacher complexity of a VC class, explicit rate](../../ComputerScience/machine-learning/generalization-bounds-and-concentration/rademacher-complexity/rademacher-complexity-sign-patterns-le-v.md): where the bound is used, for families of subsets of an $n$-point sample.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Definition 6.5 (VC dimension) and Definition 6.3 (shattering).
