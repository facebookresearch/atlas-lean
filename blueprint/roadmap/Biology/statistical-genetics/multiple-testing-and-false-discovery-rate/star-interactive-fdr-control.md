# STAR: interactive FDR control under structural constraints

Let $H_1,\dots,H_n$ be hypotheses with covariates $x_i$ and $p$-values $p_i \in [0,1]$, let $\mathcal H_0$ be the set of nulls, and let $\mathcal K \subseteq 2^{[n]}$ be a family of allowed rejection sets with $\emptyset \in \mathcal K$ (e.g. rooted subtrees, connected regions). Fix an [accumulation function $h$ and a masking function $g$](star-masking-functions.md) satisfying $\mathbb{E}_{u\sim U[0,1]}[h(u)\mid g(u)] = 1$ a.s.

**Selectively traversed accumulation rules (STAR).** Start with $R_0 = [n]$. At step $t$ compute

$$\widehat{\mathrm{FDP}}_t = \frac{h(1) + \sum_{i \in R_t} h(p_i)}{1 + |R_t|}. \tag{1}$$

If $\widehat{\mathrm{FDP}}_t \le \alpha$, stop and reject $R_\tau = R_t$. Otherwise the analyst chooses any $R_{t+1} \subsetneq R_t$ with $R_{t+1} \in \mathcal K$, using only the information

$$\mathcal F_t = \sigma\Big(\{x_i, g(p_i)\}_{i=1}^n,\ (p_i)_{i \notin R_t},\ \textstyle\sum_{i \in R_t} h(p_i)\Big),$$

and the $p$-values in $R_t \setminus R_{t+1}$ are then unmasked.

**Theorem (finite-sample FDR control).** Assume (1) the null $p$-values are mutually independent and independent of the non-null $p$-values, conditional on $(x_i)_{i=1}^n$; and (2) each null $p$-value has a non-decreasing density. If $h$ is non-decreasing and $g$ satisfies the masking condition, then, conditional on $\{x_i, g(p_i)\}_{i=1}^n$, STAR controls the FDR at level $\alpha$; unconditionally,

$$\mathbb{E}\left[\frac{|R_\tau \cap \mathcal H_0|}{\max(|R_\tau|,1)}\right] \le \alpha,$$

for every (possibly human-in-the-loop) update rule adapted to $(\mathcal F_t)$.

## Depends on

- [Accumulation and masking functions for STAR](star-masking-functions.md)

## Expansion

Each null in $R_t$ contributes $h(p_i)$ with conditional mean at least $1$ given its masked value (Proposition 1), so $\sum_{i\in R_t} h(p_i)$ acts as a conservative estimate of $|R_t \cap \mathcal H_0|$. Because the analyst only ever sees masked values of hypotheses still in $R_t$, the null terms $h(p_i)$, $i \in R_t \cap \mathcal H_0$, remain "unrevealed" coin flips; conditioning on the masked values, the paper proves FDR control by an optional-stopping (martingale) argument for the filtration $(\mathcal F_t)$ at the stopping time $\tau$. With $h(p) = 2\,\mathbf 1\{p\ge 1/2\}$ the estimator doubles the count of large $p$-values, as in knockoff-type and AdaPT procedures.

## Sources

- Lihua Lei, Aaditya Ramdas and William Fithian, "A general interactive framework for false discovery rate control under structural constraints", Biometrika (2020), <https://doi.org/10.1093/biomet/asaa064>. Section 2.1, Eqs. (1)–(3) and Algorithm 1; Section 2.2, Theorem 1 (proof in Appendix A.2).
