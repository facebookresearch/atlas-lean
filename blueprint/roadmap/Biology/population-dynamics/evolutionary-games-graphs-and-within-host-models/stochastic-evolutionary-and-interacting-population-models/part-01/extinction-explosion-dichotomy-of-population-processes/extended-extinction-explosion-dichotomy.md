# Extended extinction–explosion dichotomy for population processes

Let $X_1,X_2,\dots$ be non-negative random variables (population sizes) that are **absorbing at $0$**: $X_n=0$ implies $X_k=0$ for all $k\ge n$. The classical dichotomy (Jagers) states that if, from any state, extinction has probability bounded below uniformly in the past whenever the population is small, then with probability one the population either dies out or grows to infinity. The following results identify how far the hypotheses can be weakened.

**Lemma (key lemma).** If $E_n$ is an increasing sequence of events with limit $E$ and $\mathbb P(E\mid\overline{E_n})\ge\epsilon>0$ for all $n$, then $\mathbb P(E)=1$. Conversely, $\mathbb P(E)=1$ if and only if $\mathbb P(E_1)=1$, or $\mathbb P(E_i\mid\overline{E_{i-1}})=1$ for some $i$, or $\sum_i\mathbb P(E_{t_i}\mid\overline{E_{t_{i-1}}})=\infty$ for some strictly increasing sequence $(t_i)$.

**Corollary (bounded populations).** If $0\le X_n\le M$ and $\mathbb P(\exists r:X_r=0\mid X_n\ne0)\ge\delta>0$ for all $n$, then almost surely the population eventually becomes extinct.

**Proposition (convergence in probability).** If for every $m\ge1$ there is $\delta_m>0$ with

$$\mathbb P\bigl(\exists r:X_r=0\ \big|\ X_n\in(0,m]\bigr)\ge\delta_m\quad\text{for all }n,$$

then $\mathbb P(X_n=0\ \text{or}\ X_n>m)\to1$ for every $m$; that is, $X_n\to\{0,\infty\}$ in probability. This conclusion cannot be strengthened to almost-sure convergence: an explicit example satisfies the hypothesis but does not converge almost surely to $0$ or $\infty$.

**Theorem (extended dichotomy).** Let $\kappa_m(X_1,\dots,X_{n-1})$ be the number of earlier sizes that are at most $m$. If for every $m\ge1$ there is $\delta_m>0$ such that, for all $n$,

$$\mathbb P\bigl(\exists r:X_r=0\ \big|\ X_n\in(0,m],\ \kappa_m(X_1,\dots,X_{n-1})\bigr)\ge\delta_m,$$

then with probability one either $X_n\to\infty$ or $X_n=0$ for all large $n$.

The theorem needs extinction probabilities bounded below given only the current size and the number of past visits to small sizes, not the full history (Jagers' classical theorem conditions on the entire past).

## Expansion

For the key lemma, write $E=E_n\cup(E\cap\overline{E_n})$, so $1-\mathbb P(E)=\mathbb P(\overline E\cap\overline{E_n})\le(1-\epsilon)\mathbb P(\overline{E_n})$; letting $n\to\infty$ gives $1-\mathbb P(E)\le(1-\epsilon)(1-\mathbb P(E))$, hence $\mathbb P(E)=1$. Applying it with $E_n=\{X_r=0\text{ for some }r\le n\}$ gives the bounded-population corollary. For the extended theorem, fix $m$ and consider the event that the population visits $(0,m]$ infinitely often without dying out. Each visit, whatever the number of previous visits, carries a conditional chance at least $\delta_m$ of eventual extinction; by a conditional Borel–Cantelli argument over successive visits, indexed through $\kappa_m$, infinitely many visits force extinction almost surely. Hence on survival the process eventually leaves $(0,m]$ for every $m$, i.e. $X_n\to\infty$. Conditioning only on $X_n\in(0,m]$ loses this, because the history can correlate the visits; the example accompanying the proposition shows the gap is real.

## Sources

- Mike Steel, "Reflections on the extinction-explosion dichotomy", arXiv (2014). Section 2 (Lemma 1, Corollary 2), Section 3 (Propositions 1 and 2, Example 2), Section 4 (Theorem 3). <https://doi.org/10.48550/arXiv.1409.4713>. Published version: Theoretical Population Biology 101 (2015), 61–66, <https://doi.org/10.1016/j.tpb.2015.03.001>; locators above refer to the arXiv version.
