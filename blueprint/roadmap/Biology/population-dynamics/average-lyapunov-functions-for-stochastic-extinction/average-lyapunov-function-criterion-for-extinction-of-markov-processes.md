# Average Lyapunov function criterion for extinction of Markov processes

**Setting.** Let $(X_t^x)_{t\ge 0}$ be a Feller Markov process on a metric space $\mathcal{M}$ with extended generator $\mathcal{L}$ and carré du champ $\Gamma f=\mathcal{L}(f^2)-2f\mathcal{L}f$. Let $\mathcal{M}_0\subset\mathcal{M}$ be a closed invariant set (the extinction set, e.g. "some species is absent") and $\mathcal{M}_+=\mathcal{M}\setminus\mathcal{M}_0$, also invariant. Write $P_{\mathrm{inv}}(\mathcal{M}_0)$ for the invariant probability measures supported on $\mathcal{M}_0$.

**Hypotheses.**
1. *(Dissipativity.)* There are proper functions $W,W':\mathcal{M}\to[1,\infty)$ and $K>0$ with $W$ in the domain of $\mathcal{L}$ and $\mathcal{L}W\le K-W'$.
2. *(Average Lyapunov function.)* There is $V:\mathcal{M}_+\to\mathbb{R}$ in the domain of $\mathcal{L}$ such that $V(x_n)\to\infty$ forces $d(x_n,\mathcal{M}_0)\to 0$; $\mathcal{L}V$ is negligible relative to $W'$ at infinity; and $\mathcal{L}V$ extends to a continuous $H:\mathcal{M}\to\mathbb{R}$ with

$$\mu H=\int H\,d\mu\ \ge\ \alpha>0\qquad\text{for all }\mu\in P_{\mathrm{inv}}(\mathcal{M}_0).$$

3. *(Controlled fluctuations.)* There are continuous $U,U'\ge 0$ with $\mathcal{L}U\le K-U'$, $\Gamma W\le KU'$ and $\Gamma V\le KU'$.

**Statement.**
- *(Local extinction.)* If $x\in\mathcal{M}_0$ and $V(y)\to\infty$ as $y\to x$, then

$$\lim_{y\to x,\ y\in\mathcal{M}_+}\mathbb{P}\Big(\liminf_{t\to\infty}\tfrac{V(X_t^y)}{t}\ge\alpha\Big)=1 .$$

- *(Global extinction.)* If moreover $\mathcal{M}=\mathcal{M}_+\cup\mathcal{M}_0$ and from every $x\in\mathcal{M}_+$ there is $M$ such that $\{V>D\}\cap\{W<M\}$ is accessible for every $D$, then $\liminf_t V(X_t^x)/t\ge\alpha$ almost surely for every $x\in\mathcal{M}_+$. With $V=-\log(\text{distance to }\mathcal{M}_0)$ this is almost-sure exponential extinction at rate at least $\alpha$.
- *(Change of variables.)* The conclusions persist when $\mathcal{L}V$ only extends continuously after lifting through a quadruple map $\pi:\mathcal{N}\to\mathcal{M}$ (e.g. polar coordinates near $\mathcal{M}_0$), with the condition $\mu H\ge\alpha$ imposed on invariant measures of the lifted boundary $\mathcal{N}_0$.

For $V=-\log x_i$ in a Kolmogorov system, $\mu H$ is minus the invasion rate (Lyapunov exponent) of species $i$ under $\mu$, so the hypothesis says every boundary invariant measure repels away from the interior.

## Expansion

By the martingale decomposition, $V(X_t)-V(X_0)=\int_0^t H(X_s)\,ds+M_t^V$, and the bound $\Gamma V\le KU'$ makes $M_t^V=o(t)$. Starting near $\mathcal{M}_0$, the occupation measures of $X$ are tight (from the $W$ bound) and their limit points are invariant measures that charge $\mathcal{M}_0$, so the time-average of $H$ is eventually at least about $\alpha$; this pushes $V$ up linearly, which keeps the process near $\mathcal{M}_0$, closing a bootstrap. The proof discretizes time into blocks and applies a semimartingale large-deviation estimate for sums with drift at least $b>0$ and bounded conditional variance. Accessibility upgrades the local statement to every starting point by the strong Markov property.

## Sources

- Juraj Foldes, Declan Stacy, "Stochastic Extinction, An Average Lyapunov Function Approach", arXiv:2407.19606 (2024), Assumptions 1-5 (Section 2), Theorems 3.1, 3.2, 3.5 and 3.9, <https://doi.org/10.48550/arXiv.2407.19606>.
