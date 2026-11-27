# Time-rescaling theorem for marked point processes

**Univariate case.** Let $N(t)$ be a point process on $[0,T]$ with spike times $0 \le s_1 < \dots < s_{N(T)} \le T$, history $H_t$, and conditional intensity

$$\lambda(t\mid H_t) = \lim_{\Delta\to 0}\frac{\Pr(N(t+\Delta)-N(t) = 1 \mid H_t)}{\Delta}.$$

Then $u_j = \int_0^{s_j}\lambda(t\mid H_t)\,dt$ are the event times of a homogeneous Poisson process of unit rate (time-rescaling theorem); equivalently the rescaled intervals $u_j - u_{j-1}$ are i.i.d. exponential with mean $1$.

**Marked case.** Let spikes $(s_j, m_j)$ carry marks in a space $\mathcal{M}$ (discrete or continuous, scalar, vector or functional), with joint mark intensity $\lambda(t,m\mid H_t)$ defined by

$$\int_{M}\lambda(t,m\mid H_t)\,dm = \lim_{\Delta\to0}\frac{\Pr(\text{a spike with mark in } M \text{ in } (t,t+\Delta] \mid H_t)}{\Delta}, \qquad M \subseteq \mathcal{M},$$

and ground intensity $\Lambda(t\mid H_t) = \int_{\mathcal M}\lambda(t,m\mid H_t)\,dm$.

**Theorem.** Assume that the joint mark intensity $\lambda(t,m)$ does not depend on the process's own past (it is deterministic, or driven only by covariates independent of the spikes and conditioned on), so that the region below is fixed. Define the mark-dependent rescaled times and boundary

$$\tau_j(m) = \int_0^{s_j}\lambda(t,m\mid H_t)\,dt, \qquad b(m) = \int_0^T \lambda(t,m\mid H_t)\,dt,$$

and the region $R = \{(\tau,m) : 0 \le \tau \le b(m)\}$. Then the points $\{(\tau_j(m_j), m_j)\}_{j=1}^{N(T)}$ together with their number have the law of a homogeneous marked Poisson process with unit intensity on $R$. In particular, the number of points is Poisson with mean $|R| = \int_{\mathcal M} b(m)\,dm$ and the unordered points are i.i.d. uniform on $R$.

**Corollary.** Ignoring marks, the rescaled times form an inhomogeneous Poisson process with intensity $\tilde\lambda(\tau) = \int_{\mathcal M}\mathbf 1\{(\tau,m)\in R\}\,dm$.

## Expansion

The joint density of the observed marked spikes with $N(T) = n$ is $\prod_{j}\lambda(s_j,m_j\mid H_{s_j})\exp\!\big(-\int_{\mathcal M}\int_0^T\lambda(t,m)\,dt\,dm\big)$. The map $(s_j)\mapsto(\tau_j)$ has a lower-triangular Jacobian with diagonal $\lambda(s_j,m_j\mid H_{s_j})$, so the density of the rescaled points is $e^{-|R|}$, the density of a unit-rate Poisson process on $R$; dividing by $\Pr(N = n) = e^{-|R|}|R|^n/n!$ gives the conditional density $n!/|R|^n$ of ordered i.i.d. uniform points. For history-dependent intensities the boundary is determined by the spikes themselves and the conditional law fails: with one mark and $\lambda(t\mid H_t) = K\,\mathbf 1\{N(t^-) = 0\}$, whenever $b < KT$ there is exactly one point, at $\tau_1 = b$ on the edge of $R$. What survives is the random time-change form: for finitely many marks, the rescaled times of each mark are the points of independent unit-rate Poisson processes on $[0,\infty)$, observed up to $b(m)$. The source gives the theorem without this hypothesis and with a heuristic proof. The theorem also gives a simulation scheme for a deterministic intensity: draw a Poisson($|R|$) number of points uniformly in $R$ and invert $\tau = \int_0^s\lambda(t,m)\,dt$ at each mark.

## Sources

- L. Tao, K. E. Weber, K. Arai, U. T. Eden, "A common goodness-of-fit framework for neural population models using marked point process time-rescaling", Journal of Computational Neuroscience (2018), Section 2, Theorem 1 (Eqs. (1)–(2)), Theorem 2 (Eqs. (3)–(10)) and Corollary 1 (Eqs. (11)–(12)), <https://doi.org/10.1007/s10827-018-0698-4>, PMCID PMC6208891.
