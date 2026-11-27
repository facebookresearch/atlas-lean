# Convergence-time bounds for NIMFA SIS below the epidemic threshold

**Model.** On a graph $G$ with $N$ nodes and adjacency matrix $A$, the N-intertwined mean-field approximation (NIMFA) of the SIS process gives each node $i$ an infection probability $v_i(t) \in [0,1]$ with

$$\frac{dv_i}{dt} = -\delta v_i + \beta(1 - v_i)\sum_{j} a_{ij} v_j ,$$

or, with time rescaled so that $\delta = 1$ and effective infection rate $\tau = \beta/\delta$, $\dot V = (\tau A - I)V - \tau\,\mathrm{diag}(V)AV$. The prevalence is $y(t) = \frac1N \sum_i v_i(t)$, the NIMFA epidemic threshold is $\tau_c^{(1)} = 1/\lambda_1(A)$, and $R_0(G,\tau) = \tau\lambda_1(A)$.

On a time-varying network, the process is approximately *annealed* (sees the average network) when topology changes much faster than the epidemic, and *quenched* (sees a static snapshot) when the network changes much slower. For tolerance $r$ the upper-transition time $\overline T(r)$ is the boundary of the quenched regime: the time a static NIMFA process needs before its prevalence is within $r$ of the steady state $y_\infty$.

**Lemma (below threshold).** If $\tau < \tau_c^{(1)}(G)$, then for every initial vector $V(0) \in [0,1]^N$

$$y(t; G, \tau, V(0)) \le y(t; G, \tau, u) \le e^{(R_0(G,\tau) - 1)t},$$

where $u$ is the all-one vector, and consequently

$$\overline T(r) \le \frac{1}{1 - R_0(G,\tau)}\log\frac1r .$$

**Lemma (above threshold, no uniform bound).** If $\tau > \tau_c^{(1)}$, then for every horizon $\mathcal T$ and tolerance $r < y_\infty$ there is $\varepsilon(r) > 0$ such that the start $V(0) = \varepsilon(r)u$ keeps $|y(t) - y_\infty| > r$ for all $t \le \mathcal T$: starts close to the disease-free state converge arbitrarily slowly.

So the quenched-regime boundary is governed by $R_0$ and blows up as $R_0 \to 1$: near the epidemic threshold, timescale separation fails.

## Proof sketch

Dropping the non-positive term $-\tau\,\mathrm{diag}(V)AV$ gives $\dot V \le (\tau A - I)V$ componentwise; since $\tau A - I$ is a Metzler matrix, the comparison principle yields $V(t) \le e^{(\tau A - I)t}V(0) \le e^{(\tau A - I)t}u$, and for symmetric $A$ the average of $e^{(\tau A - I)t}u$ is at most $e^{(\tau\lambda_1 - 1)t}$. Monotonicity of NIMFA in the initial condition gives the first inequality. Solving $e^{(R_0 - 1)t} = r$ bounds $\overline T(r)$. Above threshold, the disease-free state is an unstable equilibrium, and solutions starting within $\varepsilon$ of it need time of order $\log(1/\varepsilon)$ to escape, which can exceed any $\mathcal T$.

## Sources

- Robin Persoons, Mattia Sensi, Bastian Prasse and Piet Van Mieghem, "Transition from time-variant to static networks: Timescale separation in N -intertwined mean-field approximation of susceptible-infectious-susceptible epidemics", *Physical Review E* 109 (2024), 034308, <https://doi.org/10.1103/physreve.109.034308>. Preprint version: arXiv:2305.12446 (2023), lemma on arbitrarily slow convergence above threshold and the second upper bound lemma on the upper-transition time, <https://doi.org/10.48550/arXiv.2305.12446>.
