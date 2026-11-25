# Expected origin flux of eventual neutral fixers

Consider neutral haploid Wright–Fisher copying with deterministic integer
sizes $1\le M_t\le\bar M$. Conditional on generation $t$, each of the
$M_{t+1}$ copies chooses a parent independently and uniformly among the
$M_t$ copies. Each copy at generation $t$ acquires a new, distinct-site
mutation with probability $u\in[0,1]$, independently of the copying
randomness. There is no recurrent or back mutation at that site, and
mutations are neutral, so they do not change the copying law.

For a mutation born in one copy at $t$, finite-time fixation has probability
$1/M_t$. Thus the number $A_t$ of mutations born at $t$ that eventually
fix satisfies

$$\mathbb E A_t=M_tu\frac1{M_t}=u.$$

This is an **origination** flux, not a count of substitutions completed
in that calendar generation. Constant size recovers the canonical
[Wright–Fisher fixation probability](../population-genetics/wright-fisher-markov-chain/measure-real-exists-eq-last.md).

## Background

- [Constant-size fixation probability](../population-genetics/wright-fisher-markov-chain/measure-real-exists-eq-last.md)

## Expansion

For the site's frequency $X_v$,
$M_{v+1}X_{v+1}\mid\mathcal F_v\sim\operatorname{Binomial}(M_{v+1},X_v)$;
hence $\mathbb E[X_{v+1}\mid\mathcal F_v]=X_v$.
At every segregating state the event that all offspring copy a specified
parent has probability $M_v^{-M_{v+1}}\ge\delta=\bar M^{-\bar M}$
and causes absorption. Therefore the absorption delay $\tau$ obeys
$\mathbb P(\tau>k)\le(1-\delta)^k$, and is finite almost surely.
Since $\mathbb E X_{t+k}=X_t$ for every $k$, bounded convergence gives
$\mathbb P(\text{fixation})=\mathbb E X_{t+\tau}=X_t=1/M_t$.
Linearity over mutation births proves the flux, without requiring
independence between different sites' eventual fates. The varying-size
argument is supplied here, not inferred from the constant-size provider.

Boundedness of the sizes matters. For $M_v=2^v$, starting at
$X_s=1/2$ gives
$\mathbb E[(X_\infty-1/2)^2]\le\sum_{v>s}(4M_v)^{-1}=2^{-s-2}$
by orthogonality of martingale increments. Thus
$\mathbb P(X_\infty\in\{0,1\})\le2^{-s}$.
A new mutation at generation $s=1$ has frequency $1/2$ already, so it
has probability at least $1/2$ of an interior limiting frequency.
Martingale convergence alone does not imply absorption.
A separate extension would replace bounded sizes by
$\sum_v1/M_v=\infty$ and prove fixation **in the limit** using
heterozygosity decay; that extension and a finite-hitting-time conclusion
are not asserted here.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.5, "Rate of substitution of alleles" (the prospective argument: $2Nu$ new neutral mutants, each fixed with probability $1/(2N)$, give rate $u$). The varying-size form is derived above.
