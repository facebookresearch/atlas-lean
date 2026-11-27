# Fluid limit and central limit theorems for stochastic hybrid neuron models with ion channels

**Model $(S_N)$.** A membrane potential $V_N \in \mathbb{R}^p$ evolves by $\dot V_N = f(V_N, \mathbf{e}_N)$ between jumps, where $\mathbf{e}_N = (e_N^{(1)}, \dots, e_N^{(q)})$ collects the proportions of $N$ independent ion channels of each of $q$ types in their $r_j$ conformational states: $e_N^{(j)}$ is a jump Markov process on $\{x \in \{0, \frac1N, \dots, 1\}^{r_j} : \sum_k x_k = 1\}$ in which each channel moves from state $i$ to $k$ at voltage-dependent rate $\alpha^{(j)}_{i,k}(X_N)$ (so the proportions jump by $\pm\frac1N$ at total rate of order $N$). The *deterministic model* $(D)$ is

$$\dot v = f(v, \mathbf{g}), \qquad \dot g^{(j)}_k = \sum_{i \ne k}\big(\alpha^{(j)}_{i,k}(X)g^{(j)}_i - \alpha^{(j)}_{k,i}(X)g^{(j)}_k\big),$$

e.g. the Hodgkin–Huxley equations as the limit of Markov channel models.

**Theorem (law of large numbers with exponential speed).** Assume $f$ and the $\alpha$'s are $C^1$, the solution of $(D)$ is bounded on $[0,T]$, and $V_N$ is bounded uniformly in $N$ on $[0,T]$. Then for suitable initial data, $\sup_{t\le T}\|V_N - v\|$ and $\sup_{t\le T}|e^{(j)}_{N,k} - g^{(j)}_k|$ converge to $0$ in probability, and for small $\Delta > 0$

$$\limsup_{N\to\infty}\frac1N\log\mathbf{P}\Big[\sup_{t\le T}\Big(\|V_N - v\|^2 + \sum_j\|\mathbf{e}^{(j)}_N - \mathbf{g}^{(j)}\|^2\Big) > \Delta\Big] \le -\frac{\Delta e^{-B(T)T}}{CT}$$

for constants $B(T), C > 0$.

**Theorem (central limit theorems).** Under the same hypotheses:
1. The compensated channel fluctuations $R_N = \sqrt{N}\big(\mathbf{e}_N(t) - \mathbf{e}_N(0) - \int_0^t b(X_N(s))\,ds\big)$ converge in law to $\int_0^t\sigma(X(s))\,dW_s$, where $b$ is the drift of $(D)$ and $\sigma^{(j)}\sigma^{(j)\mathsf T} = G^{(j)}$ is the channel-transition covariance evaluated along the deterministic solution.
2. $Z_N = \sqrt{N}(X_N - X)$ converges in law to the Gaussian process $Z$ solving the linearised equation $dZ = DF(X(t))Z\,dt + (0, \sigma(X(t))\,dW)$ (equivalently, an explicit equation for its characteristic function).
3. *Spike times.* If the deterministic trajectory reaches a threshold surface $\{\phi = 0\}$ transversally at time $\tau$ ($\nabla\phi\cdot F < 0$ there) and $\tau_N$ is the corresponding hitting time of $X_N$, then

$$\sqrt{N}(\tau_N - \tau) \Rightarrow -\frac{\nabla\phi(X(\tau))\cdot Z(\tau)}{\nabla\phi(X(\tau))\cdot F(X(\tau))}.$$

## Proof sketch

Between channel jumps the voltage is deterministic, so the hybrid process is a piecewise-deterministic Markov process whose channel part is a density-dependent family with jump size $1/N$. Kurtz-type martingale estimates and Gronwall's inequality give the LLN; an exponential martingale bound yields the large-deviation-type rate. The CLT follows from convergence of the compensated jump martingales to Brownian integrals with covariance determined by the transition rates, propagated through the linearised flow. The spike-time CLT is a delta method for the hitting time of a smooth surface, giving the jitter of spike timing due to finite channel numbers.

## Sources

- K. Pakdaman, M. Thieullen and G. Wainrib, "Fluid limit theorems for stochastic hybrid systems with application to neuron models", *Advances in Applied Probability* 42 (2010), 761–794, <https://doi.org/10.1239/aap/1282924062>. Preprint version: arXiv:1001.2474 (2010), Section 2 (models $(S_N)$ and $(D)$, Theorems 2.1–2.5), <https://doi.org/10.48550/arXiv.1001.2474>.
