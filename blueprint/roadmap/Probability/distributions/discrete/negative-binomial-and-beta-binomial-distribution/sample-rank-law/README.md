# Beta-binomial law of the sample rank

Let $m, N, r \in \mathbb{N}$ with $1 \le r \le m + 1$. Consider $m + 1$ real scores and $N$ synthetic scores whose joint law $\mu$ is a probability measure on $\mathbb{R}^{m + 1 + N}$ that is invariant under every permutation of the $m + 1 + N$ coordinates and under which the scores are almost surely pairwise distinct. Let $J$ be the number of synthetic scores strictly below the $r$-th smallest real score. Then for every $j \in \mathbb{N}$,

$$\mu(J = j) = \mathrm{BB}(N; r, m + 2 - r)(j),$$

where $\mathrm{BB}$ is the beta-binomial mass function. This applies in particular when all scores are independent with a common law on $\mathbb{R}$ without atoms.

## Idea

When the scores are exchangeable and have no ties, every ordering of the pooled scores is equally likely, so the positions of the $m + 1$ real scores among the $m + 1 + N$ sorted scores form a uniformly random subset. The $r$-th real score has exactly $j$ synthetic scores below it when it sits at position $r + j$, and counting the subsets gives, for $0 \le j \le N$,

$$\mu(J = j) = \binom{r - 1 + j}{r - 1} \binom{m + 1 + N - r - j}{m + 1 - r} \Big/ \binom{m + 1 + N}{m + 1},$$

which equals the beta-binomial mass; for $j > N$ both sides are $0$. The law does not depend on the distribution of the scores, which makes it a distribution-free tool for comparing real data with synthetic or simulated data. The rank $K = J + 1$ has mean $1 + N r / (m + 2)$.

## Statements

- [Beta-binomial law of the sample rank for exchangeable scores without ties](measure-real-sample-rank-eq-of-exchangea.md)
- [The sample rank](sample-rank.md): definition used in the main statement
- [Count formula for the sample rank](sample-rank-eq-card.md): lemma used in the proof of the main statement
- [The sample rank is at most $N$](sample-rank-le.md): lemma used in the proof of the main statement
- [Measurability of the sample rank](measurable-sample-rank.md): lemma used in the proof of the main statement
- [Product measures are exchangeable](map-comp-perm-pi.md): lemma: i.i.d. scores are exchangeable, used for the i.i.d. case
- [Atomless i.i.d. scores are almost surely distinct](ae-injective-pi.md): lemma: atomless i.i.d. scores have no ties, used for the i.i.d. case
- [Beta-binomial law of the sample rank (i.i.d. atomless scores)](measure-real-sample-rank-add-one-eq.md): i.i.d. atomless special case
- [Binomial-ratio form of the sample-rank law](measure-real-sample-rank-add-one-eq-choo.md): binomial-ratio form
- [Distribution function of the rank for exchangeable scores without ties](measure-real-sample-rank-add-one-le-of-e.md): distribution-function form
- [Distribution function of the rank (i.i.d. atomless scores)](measure-real-sample-rank-add-one-le.md): distribution-function form, i.i.d. case
- [Mean of the sample rank for exchangeable scores without ties](integral-sample-rank-add-one-of-exchange.md): mean of the rank
- [Mean of the sample rank (i.i.d. atomless scores)](integral-sample-rank-add-one.md): mean of the rank, i.i.d. case

## Background

- [Beta-binomial distribution](../beta-binomial/README.md)
