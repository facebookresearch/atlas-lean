# Chatterjee's rank correlation and its rate sub-optimality for testing independence

Let $(X^{(1)}_i, X^{(2)}_i)$, $i = 1,\dots,n$, be i.i.d. copies of a real pair with continuous marginals, and test $H_0 : X^{(1)} \perp\!\!\!\perp X^{(2)}$. Sort the sample so that $X^{(1)}_{[1]} \le \dots \le X^{(1)}_{[n]}$ and let $r_{[i]} = \sum_j \mathbf 1\{X^{(2)}_{[j]} \le X^{(2)}_{[i]}\}$ be the rank of the concomitant.

**Chatterjee's coefficient.** Without ties,
$$\xi_n = 1 - \frac{3\sum_{i=1}^{n-1}|r_{[i+1]} - r_{[i]}|}{n^2-1},$$
computable in $O(n\log n)$ time, which consistently estimates the Dette–Siburg–Stoimenov measure
$$\xi = \frac{\int \operatorname{var}[\mathbb E\{\mathbf 1(X^{(2)} \ge x)\mid X^{(1)}\}]\,dF_2(x)}{\int\operatorname{var}\{\mathbf 1(X^{(2)} \ge x)\}\,dF_2(x)},$$
which vanishes iff $X^{(1)} \perp\!\!\!\perp X^{(2)}$ (for continuous $F$) and equals $1$ iff $X^{(2)}$ is a measurable function of $X^{(1)}$. Comparators are Hoeffding's $D = \int\{F - F_1F_2\}^2\,dF$, the Blum–Kiefer–Rosenblatt $R$ and the Bergsma–Dassios–Yanagimoto $\tau^*$, with rank estimators $D_n, R_n, \tau^*_n$.

**Local alternatives.** (A) *Rotation:* $X = A_\Delta Y$ with $A_\Delta = \begin{pmatrix}1 & \Delta\\ \Delta & 1\end{pmatrix}$ and independent mean-zero $Y^{(1)},Y^{(2)}$ with absolutely continuous densities, finite second moments and finite Fisher information in the log-derivatives (e.g. Gaussian or $t_\nu$, $\nu > 2$). (B) *Mixture:* $F_X = (1-\Delta)F_1F_2 + \Delta G$ with a fixed dependent, compactly supported $G \ll F_1F_2$. In both, $H_{1,n}(\Delta_0)$ takes $\Delta = \Delta_0 n^{-1/2}$.

**Theorem (power analysis).** Let $T_\alpha^{\mu_n}$ be the size-$\alpha$ test rejecting for large $\mu_n$. Under the regularity assumptions for (A) or (B):

1. for every fixed $\Delta_0 > 0$, $\lim_{n\to\infty}\mathrm{pr}\{T_\alpha^{\xi_n} = 1 \mid H_{1,n}(\Delta_0)\} = \alpha$;
2. for each $\beta > 0$ there is $C_\beta$ such that for $\Delta_0 > C_\beta$ and $\mu_n \in \{D_n, R_n, \tau_n^*\}$, $\lim_{n\to\infty}\mathrm{pr}\{T_\alpha^{\mu_n} = 1 \mid H_{1,n}(\Delta_0)\} \ge 1-\beta$.

**Proposition (detection boundary).** For each $\beta$ with $\alpha + \beta < 1$ there is $c_\beta > 0$ such that every size-$\alpha$ test has type-II error at least $1 - \alpha - \beta$ under $H_{1,n}(c_\beta)$ for all large $n$.

Hence the tests based on $D_n$, $R_n$, $\tau_n^*$ are rate-optimal (they detect at the $n^{-1/2}$ boundary), while the test based on $\xi_n$ has trivial power at that scale and is rate sub-optimal.

## Expansion

Both families are locally asymptotically normal with score $s(X)$ satisfying $\mathbb E\{s(X)\mid X^{(1)}\} = 0$ a.s. Chatterjee's asymptotic representation of $\sqrt n\,\xi_n$ under $H_0$ is a sum of terms that are asymptotically uncorrelated with this score, so by Le Cam's third lemma (with a conditional multiplier central limit theorem) the limiting null law is unshifted under $H_{1,n}(\Delta_0)$. For the degenerate U-statistics $D_n, R_n, \tau_n^*$, the suitably scaled limiting laws do shift under $H_{1,n}(\Delta_0)$, and the shift grows without bound in $\Delta_0$.

## Sources

- Hongjian Shi, Mathias Drton and F Han, "On the power of Chatterjee’s rank correlation", Biometrika (2021), <https://doi.org/10.1093/biomet/asab028>. arXiv:2008.11619. Section 2 (Definitions 1–5, Propositions 1 and 3); Section 3 (Eqs. (12)–(15), Assumptions 1–2, Theorem 1, Proposition 6).
