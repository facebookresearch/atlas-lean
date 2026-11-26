# Oracle inequality for Goldenshluger–Lepski Poisson intensity estimation

**Setting.** $n$ i.i.d. Poisson processes with intensity $\lambda \in L^1\cap L^\infty$ are observed and superposed into $N^{a,n}$. For a kernel $K$ and bandwidth $h$, $K_h = h^{-1}K(\cdot/h)$ and $\hat\lambda^{K_h}_n(x) = \frac1n\sum_{T\in N^{a,n}}K_h(x - T)$. Its risk splits as bias plus variance, $E\|\hat\lambda^{K_h}_n - \lambda\|_2^2 = \|K_h\star\lambda - \lambda\|_2^2 + \frac{\|K_h\|_2^2\,\|\lambda\|_1}{n}$, so the best bandwidth depends on the unknown $\lambda$.

**Estimator.** For bandwidths $h, h'$ in a finite set $\mathcal H$ let $\hat\lambda^{h,h'}_n = K_h\star\hat\lambda^{K_{h'}}_n$, fix $\eta > 0$, write $\mathrm{pen}(h) = \frac{(1+\eta)(1+\|K\|_1)\|K\|_2\sqrt{N^{a,n}([0,T_{\max}])}}{n\sqrt h}$, and set

$$A(h) = \sup_{h'\in\mathcal H}\big\{\|\hat\lambda^{h,h'}_n - \hat\lambda^{K_{h'}}_n\|_2 - \mathrm{pen}(h')\big\}_+, \qquad \hat h = \arg\min_{h\in\mathcal H}\{A(h) + \mathrm{pen}(h)\}, \qquad \hat\lambda^{GL}_n = \hat\lambda^{K_{\hat h}}_n.$$

**Theorem.** If $\mathcal H \subset \{D^{-1} : D = 1,\dots,D_{\max}\}$ with $D_{\max} = \delta n$ and $\|\lambda\|_\infty < \infty$, then

$$E\|\hat\lambda^{GL}_n - \lambda\|_2^2 \le C_1\inf_{h\in\mathcal H}\Big\{\|K_h\star\lambda - \lambda\|_2^2 + \frac{\|\lambda\|_1}{nh}\|K\|_2^2\Big\} + C_2\,n^{-1},$$

with $C_1$ depending on $\|K\|_1, \eta$ and $C_2$ on $\delta, \eta, \|K\|_1, \|K\|_2, \|\lambda\|_1, \|\lambda\|_\infty$. In particular, if the $r$-th derivative of $\lambda$ is in $L^2$, the estimator attains the rate $n^{-2r/(2r+1)}$ without knowing $r$.

## Depends on

- [Cumulated time-rescaling test with subsampled plug-in](cumulated-time-rescaling-test-with-subsampled-plug-in.md)

## Expansion

$A(h)$ estimates the bias of bandwidth $h$ by comparing doubly smoothed and singly smoothed estimates, after subtracting the stochastic fluctuation level of each comparison; $\mathrm{pen}(h)$ is a data-driven version of the standard deviation, since $\|K\|_2^2N^{a,n}([0,T_{\max}])/(n^2h)$ is unbiased for the variance term. Concentration inequalities for Poisson functionals control the suprema uniformly over the at most $\delta n$ bandwidths, which is why the remainder is $O(n^{-1})$. The estimates feed the cumulated time-rescaling test, whose plug-in condition requires the intensity to be estimated at a rate faster than $p^{-1/2}$ on a disjoint sample; for Hawkes processes the analogous role is played by least-squares and Lasso estimates of the spontaneous rate and interaction functions.

## Sources

- P. Reynaud-Bouret, V. Rivoirard, F. Grammont, C. Tuleau-Malot, "Goodness-of-fit tests and nonparametric adaptive estimation for spike train analysis", Journal of Mathematical Neuroscience 4 (2014) 3, Section 3.2.1, Eqs (11)–(13) and Theorem 2, <https://doi.org/10.1186/2190-8567-4-3>, PMCID PMC4021619.
