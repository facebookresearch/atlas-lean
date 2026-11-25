# Second moments of neutral Wright–Fisher drift along a lineage

Let a neutral frequency process start from a possibly random
$p_0\in[0,1]$, and put $H_0=2\mathbb E[p_0(1-p_0)]$.
For $t\ge0$ integer steps of binomial sampling with integer $M\ge1$
gene copies, meaning $Mp_{n+1}\mid\mathcal F_n\sim\operatorname{Binomial}(M,p_n)$,

$$\mathbb E(p_t-p_0)^2=\frac{H_0}{2}\left(1-(1-1/M)^t\right).$$

The formula remains valid when the starting frequency is off the
$M$-copy grid; after one binomial step it lies on that grid.
Along successive neutral edges, possibly with different copy counts,
the squared increments add exactly in expectation. For two edges whose
heterozygosity retention factors are $b_1,b_2\in[0,1]$,

$$\frac{H_0}{2}(1-b_1b_2)
 =\frac{H_0}{2}(1-b_1)+\frac{H_0b_1}{2}(1-b_2).$$

## Depends on

- [Wright–Fisher heterozygosity decay](../../population-genetics/wright-fisher-markov-chain/sum-mat-pow-mul-heterozygosity.md)

## Proof depends on

- [Canonical martingale-increment orthogonality](../../../Probability/martingales/square-integrable-martingales/integral-sub-mul-eq-zero.md)
- [Canonical squared-increment identity](../../../Probability/martingales/square-integrable-martingales/integral-sub-sq-eq.md)

## Expansion

The binomial mean gives $\mathbb E[p_{n+1}\mid\mathcal F_n]=p_n$,
so the bounded process is square integrable. Its second factorial moment
gives $\mathbb E[2p_{n+1}(1-p_{n+1})\mid\mathcal F_n]
=(1-1/M)2p_n(1-p_n)$ for every real $p_n\in[0,1]$.
This first-step identity supplies the arbitrary-start extension of the
canonical finite-grid result. Since $\mathbb E p_t=\mathbb E p_0$,
$\mathbb E(p_t-p_0)^2=\mathbb E p_t^2-\mathbb E p_0^2$
becomes half the heterozygosity lost.
For disjoint intervals, the earlier increment is measurable at the
start of the later interval; the canonical orthogonality theorem makes
the cross moment zero. Expanding the square of their finite sum proves
additivity. The general martingale orthogonality theorem is used, not restated
as a new probability result. Empty edges have retention factor one;
$M=1$ gives complete loss of heterozygosity after any positive step.

## Sources

- S. Soraggi and C. Wiuf, *General theory for stochastic admixture graphs and F-statistics*, Theoretical Population Biology 125 (2019), 56–66, <https://doi.org/10.1016/j.tpb.2018.12.002>, <https://arxiv.org/abs/1807.07593>, Example 2, Lemma 1 and equation (10). The discrete-generation formula and arbitrary-start qualification are derived above.
