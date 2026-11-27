# Piecewise contraction of a time-discretized integrate-and-fire network

Consider $N$ integrate-and-fire neurons with membrane potentials $V = (V_1, \dots, V_N)$ in a compact invariant set $M \subset \mathbb R^N$, firing threshold $\theta$ and reset potential $0$. Time is discretized in steps of length $1$, short enough that a neuron fires at most once per step. With $Z(x) = \chi[x \ge \theta]$ the firing state is $\omega_k(t) = Z(V_k(t))$, and the raster plot up to time $t$ is $[\tilde\omega]_t = (\omega(0), \dots, \omega(t))$. Conductances $g_k(s, [\tilde\omega]_t) > 0$ and currents $i_k(s, [\tilde\omega]_t)$ depend on past spikes through synaptic profiles. Integrating $\dot V_k + g_k V_k = i_k$ over one step gives

$$V_k(t+1) = \gamma_k(t, [\tilde\omega]_t)\,\bigl[1 - Z(V_k(t))\bigr]\, V_k(t) + J_k(t, [\tilde\omega]_t), \qquad \gamma_k = e^{-\int_t^{t+1} g_k(s, [\tilde\omega]_t)\, ds} \in (0,1), \tag{20}$$

where $J_k$ is the current integrated over the step, and a neuron that fired is reset and receives the current of that step.

For a raster prefix $[\tilde\omega]_t$, let $M_{[\tilde\omega]_t}$ be the set of initial conditions whose firing patterns at times $0, \dots, t$ are $\omega(0), \dots, \omega(t)$, and let $F^{t+1}_{\tilde\omega} : M_{[\tilde\omega]_t} \to M$ be the time-$(t+1)$ map.

1. $F^{t+1}_{\tilde\omega}$ is affine with diagonal Jacobian whose eigenvalues are

$$\sigma_k(t, \tilde\omega) = \prod_{s=0}^{t} \gamma_k(s, [\tilde\omega]_s)\,\bigl(1 - \omega_k(s)\bigr) < 1, \qquad k = 1, \dots, N,$$

so it is a contraction, and the domains $M_{[\tilde\omega]_t}$ are convex. The global flow is piecewise affine with at most $2^{N(t+1)}$ branches.
2. If every neuron fires at least once by time $t$, then $F^{t+1}_{\tilde\omega}\bigl(M_{[\tilde\omega]_t}\bigr)$ is a single point: all orbits with that raster prefix merge in finite time.
3. If neuron $k$ never fires along $\tilde\omega$, the map contracts in direction $k$ with Lyapunov exponent

$$\liminf_{t \to \infty} \frac{1}{t+1}\sum_{s=0}^t \log \gamma_k(s, [\tilde\omega]_s) \le \lambda_k(\tilde\omega) \le \limsup_{t \to \infty} \frac{1}{t+1}\sum_{s=0}^t \log \gamma_k(s, [\tilde\omega]_s) < 0 .$$

## Expansion

Iterating (20) along a fixed raster prefix gives

$$V_k(t+1) = \prod_{s=0}^{t} \gamma_k(s)\bigl[1-\omega_k(s)\bigr] V_k(0) + \sum_{n=0}^{t} J_k(n) \prod_{s=n+1}^{t} \gamma_k(s)\bigl[1-\omega_k(s)\bigr],$$

in which the coefficients depend only on the prefix, not on $V$. The map is affine in $V(0)$ with a diagonal linear part. Positivity of the conductances gives $\gamma_k < 1$. A spike multiplies the coefficient of $V_k(0)$ by $1 - \omega_k(s) = 0$, erasing the memory of the initial potential, which gives item 2. Without spikes the eigenvalue is the product of the $\gamma_k$, whose log-average bounds the Lyapunov exponent in item 3. The firing threshold is the only source of expansion: two nearby states can be split by the singularity set $\{V_i = \theta\}$ onto different branches. With constant conductances and Dirac synapses, (20) reduces to the Beslon–Mazet–Soula model $V_k(t+1) = \gamma V_k(t)[1 - Z(V_k(t))] + \sum_j W_{kj} Z(V_j(t)) + i_k^{\mathrm{ext}}$.

## Sources

- B. Cessac, T. Viéville, "On dynamics of integrate-and-fire neural networks with conductance based synapses", *Frontiers in Computational Neuroscience* (2008), Section 2 (Eqs. (10)–(21)) and Section 3 ("Piecewise affine map", Eqs. (25)–(28), Proposition 1, Corollaries 1–2, Proposition 2), <https://doi.org/10.3389/neuro.10.002.2008> (PMC2525942).
