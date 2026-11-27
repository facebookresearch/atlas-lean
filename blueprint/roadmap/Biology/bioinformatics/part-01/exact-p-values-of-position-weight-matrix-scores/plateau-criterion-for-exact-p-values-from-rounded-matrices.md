# Plateau criterion for exact p-values from rounded matrices

**Rounding.** For a real position weight matrix $M$ of length $m$ and a granularity $\varepsilon>0$, the round matrix is $M_\varepsilon(i,x)=\varepsilon\lfloor M(i,x)/\varepsilon\rfloor$, with maximal error $E=\sum_{i=1}^m\max_{x\in\Sigma}\bigl(M(i,x)-M_\varepsilon(i,x)\bigr)$. For every word $u$ (Lemma 8),

$$0\le \mathrm{Score}(u,M)-\mathrm{Score}(u,M_\varepsilon)\le E.$$

**Lemma 9 (exact mass on a score range).** Let $M,N,N'$ be matrices of length $m$, $E,E'\ge 0$ and $\alpha\le\beta$, such that for every word $u$:
(i) $\mathrm{Score}(u,N)\le\mathrm{Score}(u,M)\le\mathrm{Score}(u,N)+E$;
(ii) $\mathrm{Score}(u,N')\le\mathrm{Score}(u,N)\le\mathrm{Score}(u,M)\le\mathrm{Score}(u,N')+E'$;
and (iii) $\mathrm{P\text{-}value}(N,\alpha-E)=\mathrm{P\text{-}value}(N,\alpha)$, (iv) $\mathrm{P\text{-}value}(N',\beta-E')=\mathrm{P\text{-}value}(N',\beta)$. If the background gives every letter positive probability, then for every word $u$, $\alpha\le\mathrm{Score}(u,N)<\beta$ if and only if $\alpha\le\mathrm{Score}(u,M)<\beta$. Hence the score distributions of $N$ and $M$ assign the same total probability to $[\alpha,\beta)$.

**Stopping rule (Lemma 11).** In particular, if the rounded distribution has a plateau just below $\alpha$, i.e. $\mathrm{P\text{-}value}(M_\varepsilon,\alpha-E)=\mathrm{P\text{-}value}(M_\varepsilon,\alpha)$, then

$$\mathrm{P\text{-}value}(M,\alpha)=\mathrm{P\text{-}value}(M_\varepsilon,\alpha),$$

so the exact p-value of the real matrix is obtained from a finite integer computation, and refinement $\varepsilon\downarrow$ can stop.

## Depends on

- [Exact p-value of a score threshold](../../position-weight-matrices/p-value.md)
- [Good-word decomposition of the PWM p-value](good-word-decomposition-of-the-pwm-p-value.md)

## Expansion

Lemma 8 holds columnwise because $0\le M(i,x)-M_\varepsilon(i,x)$ and each column contributes at most its maximal error. For the stopping rule take $N=N'=M_\varepsilon$ and $\beta$ above the best score: if $\mathrm{Score}(u,M)\ge\alpha$ then $\mathrm{Score}(u,M_\varepsilon)\ge\alpha-E$, and the plateau (no word of positive probability scores in $[\alpha-E,\alpha)$ under $M_\varepsilon$) forces $\mathrm{Score}(u,M_\varepsilon)\ge\alpha$; the converse follows from $M_\varepsilon\le M$. The source's Algorithm 3 iterates over decreasing granularities, adding the exact mass of each newly certified score range (Lemma 10 invariant $P=\mathrm{P\text{-}value}(M,\beta)$), so fine granularity is spent only where the rounded distribution has no plateau.

## Sources

- H. Touzet and J.-S. Varré, "Efficient and accurate P-value computation for Position Weight Matrices", Algorithms for Molecular Biology 2 (2007) 15. <https://doi.org/10.1186/1748-7188-2-15>, PMCID PMC2238751. Definition 3, Lemmas 8–11.
