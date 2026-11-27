# Exponential sample complexity of inferring structured population histories from coalescence times

**Setting.** In a structured coalescent with $k$ subpopulations, the pairwise coalescence time $T$ of two sampled lineages (possibly $T = \infty$ if they can never meet) has, within a period of constant demography, a survival function that is a mixture of exponentials, $\mathbb{P}(T > t) = \sum_{i=1}^k p_i e^{-\lambda_i t}$. A *two-period population history* has one structured demography (subpopulation sizes and migration) on $[0, t_0)$ and another after $t_0$. Inferring the history from $N$ independent coalescence times (e.g. from many unlinked loci, as in PSMC-type methods) therefore includes the problem of learning a $k$-component exponential mixture.

**Reduction to exponential mixtures.**
1. For every mixture $P$ of $k$ exponentials with positive rates and every $t_0 > 0$ there is a two-period history with $k$ subpopulations whose coalescence-time law $Q$ satisfies $Q(T > t + t_0 \mid T \ne \infty, T > t_0) = P(T > t)$: any such mixture is realized by some structured population.
2. Given any two mixtures $P$ (with $k$ components) and $Q$ (with $\ell$), for small $t_0$ there are distinct two-period histories with $k+2$ and $\ell+2$ subpopulations that realize $P$ and $Q$ after $t_0$ and agree on the atoms $\{T = t_0\}$ and $\{T = \infty\}$; so the number of subpopulations is not identifiable from cheap statistics.

**Lower bounds.**
- For every $k > 1$ there are pairs of $k$-component mixtures with rates in $[0,1]$ separated by at least $\frac{1}{2k}$ such that any test distinguishing them from $N$ samples has Bayes error at least $\frac{1-\delta}{2}$ with $\delta = \frac{(2k-1)\sqrt{2N}}{2^{2k-3}}$: distinguishing requires $N = 2^{\Omega(k)}$ samples. The source does not state this bound in this form: it follows from the Hellinger bound $\alpha^2(2k+1)^2/2^{4k-2}$ of the source's Theorem D.7, stated there for $\alpha \in (0, 1/2)$ (the resulting $\delta = \alpha(2k-1)\sqrt{2N}/2^{2k-3}$ increases with $\alpha$, so the bound with the $\alpha = 1$ value of $\delta$ given here holds a fortiori), re-indexed from $k+1$ to $k$ components, together with the standard tensorization of the Hellinger distance over $N$ independent samples.
- With rates in $(0,1]$ separated by $\Delta = 1/(m + 2k)$ and sharing one rate, there are pairs requiring $N \gtrsim \Delta^{-\Omega(k)}$ samples; and for integers $m>k>3$ and $\Delta=1/(m+k-1)$ there exist $\Delta$-separated rates $\lambda_1,\dots,\lambda_k$, held fixed and known, for which the minimax $\ell_1$ error for the weights satisfies

$$\inf_{\hat p}\max_p \mathbb{E}\|p - \hat p\|_1 \ge \frac14\min\Big(1, \frac{k-3}{\sqrt{2N}}\Big(\frac{1}{\Delta(k-3)}\Big)^{k-4}\Big).$$

**Matching upper bound.** The matrix pencil method applied to empirical moments $\tilde v_0, \dots, \tilde v_{2k-1}$ recovers all $(\lambda_j, p_j)$ to accuracy $\epsilon$ with probability $1 - \delta$ once

$$N \ge N_0 = O\Big(\frac{k^{10}}{p_{\min}^4}\Big(\frac{2e}{\Delta}\Big)^{6k}\log\frac1\delta\Big),$$

with errors $O\big(k^{3.5}p_{\min}^{-2}(2e/\Delta)^{2k}\sqrt{\log(1/\delta)/N}\big)$ for the rates; a Nazarov–Turán-based test distinguishes $k_0$ from $k_1$ components with sample size $(c_\Delta/\Delta)^{O(k)}$.

So the data needed to reconstruct a population history grows exponentially in the number of subpopulations: a handful of hidden demes already makes inference from coalescence times infeasible.

## Expansion

Mixtures of exponentials are Laplace transforms of discrete measures, and two such mixtures with $2k$ well-separated rates can match on their first $\approx 2k$ moments, with the residual difference shrinking like $2^{-2k}$ (a Chebyshev-polynomial construction) or $\Delta^{k}$ (a Turán-type construction); Le Cam's two-point method then gives the testing lower bounds. The structured-coalescent realization uses the fact that the coalescence time in a two-period history is a phase-type distribution whose sub-generator can be chosen with arbitrary positive spectrum. The upper bound uses Prony/matrix-pencil recovery from moments, whose conditioning is governed by inverse Vandermonde norms (Gautschi bounds), giving the matching $(1/\Delta)^{O(k)}$ dependence.

## Sources

- Younhun Kim, Frederic Koehler, Ankur Moitra, Elchanan Mossel and Govind Ramnarayan, "How Many Subpopulations Is Too Many? Exponential Lower Bounds for Inferring Population Histories", J. Comput. Biol. 27 (2020), 613–625, <https://doi.org/10.1089/cmb.2019.0318>; conference version in Research in Computational Molecular Biology (RECOMB 2019), Lecture Notes in Comput. Sci. 11467, Springer (2019), 136–157, <https://doi.org/10.1007/978-3-030-17083-7_9>. Numbering follows the arXiv version, arXiv:1811.03177 (2018): Theorems 2.1–2.6 and Theorem D.7 (Hellinger bound), <https://doi.org/10.48550/arXiv.1811.03177>.
