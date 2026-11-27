# Chatterjee's rank correlation and its rate sub-optimality for testing independence

Let $(X^{(1)}_i, X^{(2)}_i)$, $i = 1,\dots,n$, be i.i.d. copies of a real pair with continuous marginals, and test $H_0 : X^{(1)} \perp\!\!\!\perp X^{(2)}$. Sort the sample so that $X^{(1)}_{[1]} \le \dots \le X^{(1)}_{[n]}$ and let $r_{[i]} = \sum_j \mathbf 1\{X^{(2)}_{[j]} \le X^{(2)}_{[i]}\}$ be the rank of the concomitant.

**Chatterjee's coefficient.** Without ties,

$$\xi_n = 1 - \frac{3\sum_{i=1}^{n-1}|r_{[i+1]} - r_{[i]}|}{n^2-1},$$

computable in $O(n\log n)$ time, which consistently estimates the Dette–Siburg–Stoimenov measure

$$\xi = \frac{\int \operatorname{var}[\mathbb E\{\mathbf 1(X^{(2)} \ge x)\mid X^{(1)}\}]\,dF_2(x)}{\int\operatorname{var}\{\mathbf 1(X^{(2)} \ge x)\}\,dF_2(x)},$$

which vanishes iff $X^{(1)} \perp\!\!\!\perp X^{(2)}$ (for continuous $F$) and equals $1$ iff $X^{(2)}$ is a measurable function of $X^{(1)}$. Comparators are Hoeffding's $D = \int\{F - F_1F_2\}^2\,dF$, the Blum–Kiefer–Rosenblatt $R$ and the Bergsma–Dassios–Yanagimoto $\tau^*$, with rank estimators $D_n, R_n, \tau^*_n$.

**Local alternatives.** (A) *Rotation:* $X = A_\Delta Y$ for $\Delta \in (-1, 1)$, with $A_\Delta = \begin{pmatrix}1 & \Delta\\ \Delta & 1\end{pmatrix}$ and independent mean-zero real $Y^{(1)}, Y^{(2)}$ with Lebesgue densities $f_1, f_2$; let $f_X(\cdot\,; \Delta)$ be the density of $X$ and $I_X(0)$ the Fisher information of $X$ relative to $\Delta$ at $\Delta = 0$. *Assumption 1:* (i) the support $\{x : f_X(x; \Delta) > 0\}$ is the same for all $\Delta \in (-1, 1)$; (ii) each $f_k$ is absolutely continuous with non-constant logarithmic derivative $\rho_k = f_k'/f_k$; (iii) $I_X(0) > 0$, and $\mathbb E\{(Y^{(k)})^2\} < \infty$ and $\mathbb E[\{\rho_k(Y^{(k)})\}^2] < \infty$ for $k = 1, 2$. It holds, for example, for centred Gaussian or $t_\nu$ ($\nu > 2$) components.

(B) *Mixture:* $F_X = (1-\Delta)F_0 + \Delta G$ for $\Delta \in [0, 1]$, where $F_0(x^{(1)}, x^{(2)}) = F_1(x^{(1)})F_2(x^{(2)})$ for absolutely continuous $F_1, F_2$, and $G \ne F_0$ is a fixed absolutely continuous bivariate law under which the coordinates are dependent; the densities $f_0$ of $F_0$ and $g$ of $G$ are continuous with compact supports. *Assumption 2:* (i) $G \ll F_0$ and $s(x) = g(x)/f_0(x) - 1$ is continuous; (ii) $\mathbb E\{s(Y) \mid Y^{(1)}\} = 0$ almost surely for $Y \sim F_0$; (iii) $s$ is not additively separable, that is $s(x) \ne h_1(x^{(1)}) + h_2(x^{(2)})$ for all univariate $h_1, h_2$; (iv) $I_X(0) > 0$. It holds, for example, for the Farlie alternative $G = F_1F_2\{1 + (1 - F_1)(1 - F_2)\}$.

In both families, $H_{1,n}(\Delta_0)$ takes $\Delta = \Delta_0 n^{-1/2}$ with $\Delta_0 > 0$.

**Theorem (power analysis).** Let $T_\alpha^{\mu_n}$ be the size-$\alpha$ test rejecting for large $\mu_n$. Under Assumption 1 for (A), or Assumption 2 for (B):

1. for every fixed $\Delta_0 > 0$, $\lim_{n\to\infty}\mathrm{pr}\{T_\alpha^{\xi_n} = 1 \mid H_{1,n}(\Delta_0)\} = \alpha$;
2. for each $\beta > 0$ there is $C_\beta$ such that for $\Delta_0 > C_\beta$ and $\mu_n \in \{D_n, R_n, \tau_n^*\}$, $\lim_{n\to\infty}\mathrm{pr}\{T_\alpha^{\mu_n} = 1 \mid H_{1,n}(\Delta_0)\} \ge 1-\beta$.

**Proposition (detection boundary).** Under the same assumptions, for each $\beta > 0$ with $\alpha + \beta < 1$ there is $c_\beta > 0$ such that every size-$\alpha$ test has type-II error at least $1 - \alpha - \beta$ under $H_{1,n}(c_\beta)$ for all large $n$.

Hence the tests based on $D_n$, $R_n$, $\tau_n^*$ are rate-optimal (they detect at the $n^{-1/2}$ boundary), while the test based on $\xi_n$ has trivial power at that scale and is rate sub-optimal.

## Expansion

Both families are locally asymptotically normal with score $s(X)$ satisfying $\mathbb E\{s(X)\mid X^{(1)}\} = 0$ a.s. Chatterjee's asymptotic representation of $\sqrt n\,\xi_n$ under $H_0$ is a sum of terms that are asymptotically uncorrelated with this score, so by Le Cam's third lemma (with a conditional multiplier central limit theorem) the limiting null law is unshifted under $H_{1,n}(\Delta_0)$. For the degenerate U-statistics $D_n, R_n, \tau_n^*$, the suitably scaled limiting laws do shift under $H_{1,n}(\Delta_0)$, and the shift grows without bound in $\Delta_0$.

## Sources

- Hongjian Shi, Mathias Drton and F Han, "On the power of Chatterjee’s rank correlation", Biometrika (2021), <https://doi.org/10.1093/biomet/asab028>. arXiv:2008.11619. Section 2 (Definitions 1–5, Propositions 1 and 3); Section 3 (Eqs. (12)–(15), Assumptions 1–2, Theorem 1, Proposition 6).
