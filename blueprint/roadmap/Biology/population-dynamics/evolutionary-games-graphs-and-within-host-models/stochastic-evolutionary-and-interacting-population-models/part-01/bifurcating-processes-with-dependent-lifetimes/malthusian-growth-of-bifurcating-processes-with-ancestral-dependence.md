# Malthusian growth of bifurcating processes with ancestral dependence

Index cells by the binary tree $\mathbb T = \bigcup_n \{0,1\}^n$; cell $v$ has lifetime $T_v > 0$ and daughters $v0, v1$. The birth date is $S_\emptyset = 0$, $S_{vi} = S_v + T_v$, and the number of living cells is

$$

N_t = \tfrac12 + \tfrac12\sum_{v\in\mathbb T}\mathbf 1_{\{S_v \le t\}} .

$$

Let $S_n$ denote the birth date of a generation-$n$ cell along one lineage and $\mathcal L_n(\gamma) = \mathbb{E}[e^{-\gamma S_n}]$. The process is **birth-stationary** if all generation-$n$ cells have birth dates with the law of $S_n$.

**Classical case.** If the $T_v$ are i.i.d. copies of a non-lattice $T$, then $e^{-\nu t}N_t \to W$ almost surely, where $2\,\mathbb{E}[e^{-\nu T}] = 1$, $\mathbb{E}[W] = C = (4\nu\,\mathbb{E}[Te^{-\nu T}])^{-1}$, and $W$ has finite variance.

**Theorem 2.1 (birth-stationary processes).** If

$$

\nu = \inf\Big\{\gamma > 0 : \sum_{n\ge1}2^n\mathcal L_n(\gamma) < \infty\Big\}, \qquad C = \lim_{\gamma\downarrow 0}\frac{\gamma}{\gamma+\nu}\sum_{n\ge1}2^{n-1}\mathcal L_n(\gamma+\nu)

$$

are positive and finite, then $\mathbb{E}[N_t] < \infty$ and $\frac1t\int_0^t e^{-\nu s}\mathbb{E}[N_s]\,ds \to C$.

**Theorem 3.1 (bifurcating Markov chains).** Let $(T_v)$ be a bifurcating Markov chain: $T_\emptyset \sim \mu$ and, given the lifetimes of generation $n$, the pairs $(T_{v0},T_{v1})$ are independent with law $P(T_v,\cdot)$. Assume the kernel is symmetric in the two daughters and leaves the marginal $\mu$ invariant, and that the lineage sums are **multiplicatively ergodic**: with $\mathcal L_n(\gamma,u) = \mathbb{E}[e^{-\gamma S_n} \mid T_\emptyset = u]$,

$$

\mathcal L_n(\gamma,u) = \alpha(\gamma,u)\,L(\gamma)^n + r_n(\gamma,u),

$$

where $2L(\gamma) = 1$ has a unique root $\nu$, $L$ is differentiable at $\nu$ with $L'(\nu) < 0$, $\sum_n 2^n r_n(\gamma,u)$ converges uniformly in $\gamma$ in a neighborhood of $\nu$ and uniformly in $u$, the maps $u \mapsto \alpha(\gamma,u)$ and $u \mapsto r_n(\gamma,u)$ are $\mu$-integrable uniformly in the other variables, and $(y,z) \mapsto \alpha(\nu,y)\alpha(\nu,z)$ is $P(x,\cdot)$-integrable uniformly in $x$ (Definition 3.3, whose item 5 writes $a(\nu,y)a(\nu,z)$ for this product). Let
$B_\nu(t,u) = e^{-\nu t}\sum_{n\ge1}2^{n-1}\mathbb P[S_n \le t \mid T_\emptyset = u]$ with Laplace transform $\tilde B_\nu(\gamma,u)$, and assume:

- (C1) there are $\delta, \epsilon > 0$, with $\delta$ not depending on $u$, such that for every $u$ the function $\tilde B_\nu(\cdot,u)$ is analytic on $\{|\operatorname{Re} z| < \delta + \epsilon\} \setminus \{0\}$, has a simple pole at $0$ with residue $C(u) = -\alpha(\nu,u)/(4\nu L'(\nu))$, satisfies $\int_{-\infty}^\infty|\tilde B_\nu(\delta + iy,u)|\,dy < \infty$ and $\tilde B_\nu(x + iy,u) \to 0$ as $y \to \pm\infty$ uniformly in $x \in [-\delta,\delta]$, and $\psi(u) = \int_{-\infty}^\infty|\tilde B_\nu(-\delta + iy,u)|\,dy < \infty$;
- (C2) $(y,z) \mapsto \alpha(\nu,y)\psi(z)$ is $P(x,\cdot)$-integrable uniformly in $x$.

Then $e^{-\nu t}N_t \to W$ almost surely, with $W$ of finite variance and

$$

2L(\nu) = 1, \qquad \mathbb{E}[W] = C = -\frac{\alpha(\nu)}{4\nu L'(\nu)}, \qquad \alpha(\nu) = \int \alpha(\nu,u)\,\mu(du).

$$

**Comparison.** Under the hypotheses of Theorem 2.1 (a birth-stationary process with $\nu$ and $C$ positive and finite), if the lineage lifetimes $(T_{0^n})_{n\ge1}$ are associated (positively dependent) and $\nu^*, C^*$ are the parameters for independent lifetimes with the same marginals, then $\nu^* \le \nu$ and $C \le C^*$; for negatively associated lifetimes the inequalities reverse.

In the i.i.d. case $L(\gamma) = \mathbb{E}[e^{-\gamma T}]$, $\alpha \equiv 1$, and the theorem reduces to the classical formulas.

## Expansion

Since $\mathbb{E}[N_t] = \tfrac12 + \tfrac12\sum_n 2^n\,\mathbb{P}[S_n \le t]$, its Laplace transform is $\tfrac{1}{2\gamma}\big(1 + \sum_n 2^n\mathcal L_n(\gamma)\big)$, so the abscissa of convergence is $\nu$ and a Tauberian argument gives the Cesàro limit. Under multiplicative ergodicity the series is close to a geometric series in $2L(\gamma)$ with a simple pole at $\nu$ and residue $-\alpha(\nu)/(2L'(\nu))$, which gives $C$; a contour-shifting lemma upgrades this to exponential convergence of $e^{-\nu t}\mathbb{E}[N_t]$, and second-moment bounds over pairs of cells (fork-stationarity) give the almost sure limit. Association increases $\mathbb{E}[e^{-\gamma S_n}]$ relative to the independent case, which enlarges $\nu$.

## Sources

- Sana Louhichi, Bernard Ycart, "Exponential growth of bifurcating processes with ancestral dependence", arXiv (2013); Advances in Applied Probability (2015). Theorem 1.1, Section 2 (Definitions 2.1–2.3, Theorem 2.1), Section 3 (Definitions 3.2–3.3, Theorem 3.1), Section 5 (Proposition 5.1), Section 6. <https://doi.org/10.48550/arXiv.1307.0343>. Published version: Advances in Applied Probability 47(2) (2015), 545–564, <https://doi.org/10.1239/aap/1435236987>; locators above refer to the arXiv version.
