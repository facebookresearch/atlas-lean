# Dynkin martingale of a discrete-time Markov chain

On a probability space, let $X_n$ be adapted to $\mathcal F_n$ and have
Markov kernel $P$ relative to that filtration: for every bounded measurable
real $f$, $\mathbb E[f(X_{n+1})\mid\mathcal F_n]=(Pf)(X_n)$.
Then for every such $f$,

$$M_n=f(X_n)-f(X_0)-\sum_{k=0}^{n-1}(Pf-f)(X_k)$$

is a real martingale. In particular $Pf=f$ makes $f(X_n)$ a martingale,
and $Pf\le f$ makes it a supermartingale.

## Depends on

- [Markov property](markov-property-full.md)

## Expansion

The process is adapted and integrable, since $f$ is bounded and each
compensator sum is finite. Its increment is
$f(X_{n+1})-(Pf)(X_n)$, whose conditional mean is zero.
For a neutral Wright–Fisher count chain with $M\ge1$ gene copies and
conditional law $X_{n+1}\mid X_n=i\sim\operatorname{Binomial}(M,i/M)$,
$f(i)=i/M$ is harmonic by the binomial mean formula. Thus allele frequency
is a bounded martingale, including the absorbing endpoints.
The linked canonical path-space Markov theorem supplies the hypothesis
for its own natural filtration; an arbitrary larger filtration must
satisfy the displayed conditional property itself.

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th edition (2019), <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>, Theorem 5.2.3 and Example 5.3.9. The general compensator calculation is given above.
