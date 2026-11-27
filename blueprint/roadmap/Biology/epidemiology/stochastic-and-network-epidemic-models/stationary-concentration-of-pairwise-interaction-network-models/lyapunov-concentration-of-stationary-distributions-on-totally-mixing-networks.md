# Lyapunov concentration of stationary distributions of pairwise interaction network models

**Pairwise interaction network (PIN) model.** Agents $\mathcal{V}$ ($n = |\mathcal{V}|$) sit on a directed graph $\mathcal{G} = (\mathcal{V}, \mathcal{E})$ ($m = |\mathcal{E}|$) and carry states in a finite set $\mathcal{A}$. At each discrete step, with probability $1-\rho$ a uniformly chosen agent mutates from state $i$ to $j$ with probability $P_{ij}$; with probability $\rho$ a uniformly chosen link $(u,v)$ is activated and agent $u$, in state $i$, moves to state $j$ with probability $\phi_{ij}(\ell)$, where $\ell$ is the state of $v$. SIS, SIR and SIRS epidemics on networks, voter models and evolutionary dynamics on graphs are PIN models. Let $\theta(\mathbf{x}) \in \mathcal{P}(\mathcal{A})$ be the empirical state distribution of configuration $\mathbf{x}$.

**Limit drift and Lyapunov functions.** The limit drift is

$$\bar{D}(\theta) = \Big((1-\rho)P^\top + \rho\sum_{\ell\in\mathcal{A}} \theta_\ell\,\phi(\ell)^\top - I\Big)\theta,\qquad \theta \in \mathcal{P}(\mathcal{A}),$$

the right-hand side of the mean-field ODE $\dot\theta = \bar{D}(\theta)$. A differentiable $V : \mathcal{P}(\mathcal{A}) \to \mathbb{R}_+$ is a mean-field Lyapunov function if $\nabla V(\theta)\cdot\bar{D}(\theta) \le 0$ on $\mathcal{P}(\mathcal{A})$.

**Asymptotically totally mixing networks.** The total mixing gap of $\mathcal{G}$ is

$$W_{\mathcal{G}} = \max_{\mathcal{S}\cap\mathcal{U} = \emptyset}\left|\frac{|\mathcal{E}_{\mathcal{S}\mathcal{U}}|}{m} - \frac{|\mathcal{S}||\mathcal{U}|}{n(n-1)}\right|,$$

with $\mathcal{E}_{\mathcal{S}\mathcal{U}}$ the links from $\mathcal{S}$ to $\mathcal{U}$. A sequence $\mathcal{G}_n$ is ATM if $W_{\mathcal{G}_n} \to 0$. Erdős–Rényi graphs $\mathcal{G}(n, p_n)$ with $np_n \to \infty$ are ATM with probability one.

**Theorem (concentration).** Let $\mu_n$ be any stationary distribution of a PIN model with fixed parameters on an ATM sequence $\mathcal{G}_n$, and $V$ a $C^2$ mean-field Lyapunov function. Then for every $\delta > 0$,

$$\lim_{n\to\infty}\mu_n\big\{\mathbf{x} : \nabla V(\theta(\mathbf{x}))\cdot\bar{D}(\theta(\mathbf{x})) > -\delta\big\} = 1.$$

On a complete graph the finite-$n$ bound $\mu(\{\nabla V\cdot\bar{D} > -\delta\}) \ge 1 - C/(n\delta)$ holds with $C$ depending only on $V$.

**Theorem (approximate Lyapunov functions).** For a family of PIN models with parameters $(\mathcal{A}, \rho, P_\alpha, \phi_\alpha)$, suppose $C^2$ functions $V_\alpha$ satisfy $\nabla V_\alpha\cdot\bar{D}_\alpha \le -h(\theta) + \zeta(\alpha)$ with $h \ge 0$ continuous and $\zeta(\alpha) \to 0$. Then for stationary distributions $\mu_n^{(\alpha)}$ on an ATM sequence and every $\delta > 0$,

$$\lim_{\alpha\to 0}\liminf_{n\to\infty}\mu_n^{(\alpha)}\{\mathbf{x} : h(\theta(\mathbf{x})) < \delta\} = 1.$$

## Expansion

The proof is a stochastic analogue of LaSalle's invariance principle that avoids Kurtz's theorem. Stationarity gives $\mathbb{E}_\mu[V(\theta(X(1))) - V(\theta(X(0)))] = 0$; a second-order Taylor expansion shows this increment equals $\frac{1}{n}\nabla V\cdot D(\mathbf{x})$ plus $O(n^{-2})$, where $D$ is the exact mean drift. On a general graph $D$ differs from $\bar{D}(\theta(\mathbf{x}))$ by at most a multiple of $W_{\mathcal{G}}$ plus $O(1/n)$, which the ATM property kills. A Markov-type inequality then bounds the stationary mass where the drift of $V$ is very negative. The approximate version handles models like noisy SIRS, whose natural Lyapunov functions are singular at the boundary and only become $C^2$ after adding spontaneous infection.

## Sources

- Giacomo Como, Fabio Fagnani and Sandro Zampieri, "An Invariance Principle-Based Concentration Result for Large-Scale Stochastic Pairwise Interaction Network Systems", IEEE Transactions on Automatic Control 71 (2026), 5064–5079, <https://doi.org/10.1109/tac.2026.3670758>; numbering as in arXiv:2410.22820: Definitions 1–5, Proposition 1, Theorems 1, 2 and 3 and Corollary 1.
