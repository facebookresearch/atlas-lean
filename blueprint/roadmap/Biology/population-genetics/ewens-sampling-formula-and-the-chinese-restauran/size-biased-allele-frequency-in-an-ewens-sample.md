# First-allele frequency in an Ewens sample and its Beta limit

In one nested CRP with fixed $\theta>0$, let $J_n$ be the size of the
block containing customer one after $n\ge1$ customers. With
$x^{(r)}=\prod_{i=0}^{r-1}(x+i)$ and empty product one,

$$\mathbb P(J_n=j)=\binom{n-1}{j-1}
 \frac{(j-1)!\,\theta^{(n-j)}}{(1+\theta)^{(n-1)}},
 \qquad 1\le j\le n.$$

Moreover $J_n/n\to W$ almost surely, where
$W\sim\operatorname{Beta}(1,\theta)$ has density
$\theta(1-x)^{\theta-1}$ on $(0,1)$. The finite expectation is
$\mathbb E[J_n/n]=(n+\theta)/(n(1+\theta))$, so its limit is
$1/(1+\theta)$. At $n=2$, $\mathbb P(J_2=2)=1/(1+\theta)$.

## Depends on

- [CRP seating law](../../../Probability/bayesian-statistics/blackwell-macqueen-urn/crp.md)

## Proof depends on

- [First Borel–Cantelli lemma](../../../Probability/foundations/borel-cantelli-lemmas/first-borel-cantelli-lemma/measure-limsup-at-top-eq-zero.md)

## Expansion

The first block gains a customer with probability $J_n/(n+\theta)$.
Thus its Pólya urn has red weight $J_n$, black weight $n-J_n+\theta$
and total weight $n+\theta$. The exact bounded martingale is
$J_n/(n+\theta)$, not $J_n/n$.
For any specified sequence of the next $n-1$ membership decisions with
$j-1$ red and $n-j$ black outcomes, multiplying the successive urn
probabilities gives $(j-1)!\theta^{(n-j)}/(1+\theta)^{(n-1)}$.
Counting the possible decision strings proves the displayed law.

A complete Beta-mixture argument also gives the almost-sure limit:
draw $W$ with density $\theta(1-w)^{\theta-1}$ and, conditional on $W$,
draw iid Bernoulli$(W)$ memberships after the first customer.
The Beta integral of each finite membership string is exactly the same
urn probability. Hence the two infinite membership laws agree on all
cylinders. For these Bernoulli draws, conditional variance gives
$\mathbb E[(m^{-1}\sum_{i=1}^m I_i-W)^2]\le1/(4m)$.
Chebyshev at $m=k^2$, Borel–Cantelli and monotonicity of the success count
between consecutive squares give almost-sure convergence to $W$.
Equality of membership laws transfers this to the nested CRP.
The same mixture gives $\mathbb E J_n=1+(n-1)/(1+\theta)$.
Nonintegral $\theta$ is a positive urn weight, not an integer number of
physical black balls.

## Sources

- N. Berestycki, *Recent progress in coalescent theory* (2009), <https://arxiv.org/abs/0909.3985>, Section 1.3.1, proof of Theorem 1.5. The finite law, exact urn normalization and Beta-mixture convergence argument are written out above.
