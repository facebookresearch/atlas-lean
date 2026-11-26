# The expected absorption time is bounded by the sum of inverse block-count drifts

Let $\Lambda$ be a nonzero finite measure on $[0,1]$ with
$\Lambda(\{1\})=0$. For $b\ge2$, write
$\lambda_b=\sum_{k=2}^b\binom bk\lambda_{b,k}>0$ for the total merger rate
and $\gamma_b=\sum_{k=2}^b(k-1)\binom bk\lambda_{b,k}>0$ for the
[block-count drift](../block-count-drift-of-coalescents/block-drift.md).
Start the [Λ-coalescent](lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)
from singletons, and let $T_n$ be the absorption time of its restriction to
$[n]$. Then, including $n=1$ with an empty sum,

$$\mathbb E T_n\le\sum_{b=2}^n\gamma_b^{-1}.$$

Therefore $\sum_{b=2}^\infty\gamma_b^{-1}<\infty$ implies
$\mathbb E T_\infty<\infty$ for $T_\infty=\sup_nT_n$, and the coalescent
comes down from infinity by the [entrance and absorption dichotomy](entrance-dichotomy-and-finite-expected-absorption.md).
For unit-rate [Kingman's coalescent](../block-count-drift-of-coalescents/block-drift-dirac-zero.md),
$\gamma_b=\binom b2$ and every decrement is one, giving equality
$\mathbb E T_n=2(1-1/n)$ for $n\ge1$.

## Depends on

- [Block-count drift](../block-count-drift-of-coalescents/block-drift.md)
- [The Λ-coalescent on the natural numbers](lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)

## Proof depends on

- [The drift is nondecreasing](../block-count-drift-of-coalescents/block-drift-mono.md)
- [Entrance dichotomy and finite expected absorption](entrance-dichotomy-and-finite-expected-absorption.md)
- [Kingman's block-count drift](../block-count-drift-of-coalescents/block-drift-dirac-zero.md)

## Expansion

Enumerate the at most $n-1$ mergers before absorption. Just before merger
$i$, let the block count be $N_{i-1}>1$, and let $J_i=N_{i-1}-N_i$ be its
positive decrement. Its waiting time has conditional mean
$\lambda_{N_{i-1}}^{-1}$, and
$\mathbb E[J_i\mid N_{i-1}=b]=\gamma_b/\lambda_b$. Thus

$$\mathbb E T_n=\mathbb E\sum_i J_i/\gamma_{N_{i-1}}
 \le\mathbb E\sum_i\sum_{j=N_i+1}^{N_{i-1}}\gamma_j^{-1}
 =\sum_{j=2}^n\gamma_j^{-1}.$$

The inequality uses nondecreasing drift; the integer ranges partition
$\{2,\ldots,n\}$. No reciprocal at the absorbing state $b=1$ is taken.
The finite-sample inequality itself also holds with an atom at one, but
finite expected absorption alone would not imply coming down then.

## Sources

- J. Schweinsberg, "A necessary and sufficient condition for the Λ-coalescent to come down from infinity", Electronic Communications in Probability 5 (2000), 1--11, <https://www.maths.tcd.ie/EMIS/journals/EJP-ECP/article/download/1013/1013-3391-1-PB.pdf>, Lemma 6 and equation (12), p. 5.
- N. Berestycki, *Recent progress in coalescent theory* (2009), <https://arxiv.org/abs/0909.3985>, Section 3.1.5, equations (72)--(73).
