# Mean-square prevalence bound for network SIS epidemics under Poisson agent replacement

**Closed-network model.** On a connected undirected graph with $n_0$ nodes and symmetric adjacency matrix $A$ with largest eigenvalue $\lambda_1$, the mean-field SIS model for infection probabilities $x(t) \in [0,1]^{n_0}$ is

$$
\dot x = (\beta A - \delta I)x - \beta X A x, \qquad X = \operatorname{diag}(x_1,\dots,x_{n_0}),
$$

with infection rate $\beta > 0$ and recovery rate $\delta > 0$. Its disease-free equilibrium is globally asymptotically stable iff $\lambda_1\beta/\delta < 1$. The aggregate (Lyapunov) function

$$
V(x) = \frac{1}{n_0}\|x\|^2 \in [0,1]
$$

satisfies $\dot V \le 2(\beta\lambda_1 - \delta)V$.

**Open-network approximation.** Model arrivals and departures of individuals at similar rates as *replacements* on a fixed graph: at the jump times of a homogeneous Poisson process of rate $\mu > 0$, a uniformly chosen node is assigned a fresh infection probability drawn from a continuous law $\Theta$ on $[0,1]$ with mean $m$ and variance $\sigma^2$. The graph is fixed at the Erdős–Rényi mean $\bar A = p(\mathbf 1\mathbf 1^\top - I)$, so $\bar\lambda_1 = p(n_0 - 1)$, and rates are scaled as $\delta = \bar\delta$, $\beta = \bar\beta/n_0$.

**Statement.**

1. *Jump identity.* At a replacement, $\mathbb{E}[V(x(t^+))] - \mathbb{E}[V(x(t^-))] = \frac{1}{n_0}\bigl(\sigma^2 + m^2 - \mathbb{E}[V(x(t^-))]\bigr)$, for any inter-event dynamics.
2. *Pure replacement.* If $\dot x = 0$ between jumps, $\mathbb{E}[V(x(t))] = (V_0 - \sigma^2 - m^2)e^{-\mu t/n_0} + \sigma^2 + m^2$, so $\mathbb{E}[V] \to \mathbb{E}[\Theta^2]$ independently of $\mu$.
3. *First moment.* If the closed epidemic is below threshold, $\lambda_1\beta/\delta < 1$ (here $\bar\beta p(n_0-1) < n_0\bar\delta$), then

$$
\limsup_{t\to\infty} \mathbb{E}[V(x(t))] \le \frac{\mu(\sigma^2 + m^2)}{\mu + 2n_0\bar\delta - 2\bar\beta p(n_0 - 1)} .
$$

4. *Second moment.* Under the same hypotheses, with $D = \mu + 2n_0\bar\delta - 2\bar\beta p(n_0 - 1)$,

$$
\limsup_{t\to\infty} \mathbb{E}[V^2(x(t))] \le \frac{\mu\,\mathbb{E}[\Theta^4]\,D + \mu^2\,\mathbb{E}[\Theta^2]\bigl(2\mathbb{E}\Theta^2 + 1\bigr)}{2n_0 D^2} .
$$

So a stable epidemic on an open network does not die out: replacement keeps reinjecting infection, and the stationary mean-square prevalence is bounded by a quantity proportional to the second moment of the newcomers' infection probability, decreasing in the closed system's stability margin.

## Depends on

- [Spectral radius and die-out of SIS epidemics on graphs](../../sis-extinction-times-on-finite-graphs/prob-ne-empty-le.md)

## Proof sketch

Conditioning on $x^-$ and on the new value $\Theta$, replacing a uniform node gives $\mathbb{E}[V^+ \mid x^-,\Theta] = V^- - V^-/n_0 + \Theta^2/n_0$; averaging gives item 1. Between jumps $V$ follows the SIS flow; at jumps it moves by $\Delta V_k$, so $dV = \omega(x)\,dt + \Delta V\,dN_t$ with $\mathbb{E}[dN_t] = \mu\,dt$. Taking expectations and using $x^\top X\bar A x \ge 0$ and $x^\top(\beta\bar A - \delta I)x \le (\beta\bar\lambda_1 - \delta)\|x\|^2$,

$$
\frac{d}{dt}\mathbb{E}[V] \le 2(\beta\bar\lambda_1 - \delta)\mathbb{E}[V] + \frac{\mu}{n_0}\bigl(\sigma^2 + m^2 - \mathbb{E}[V]\bigr),
$$

and the comparison lemma bounds $\mathbb{E}[V]$ by the solution of the linear ODE, whose limit is item 3. The second moment follows the same pattern using Itô's formula for Poisson-driven equations applied to $V^2$, together with the jump bound $\mathbb{E}[V^{2+}] - \mathbb{E}[V^{2-}] \le -\frac{2}{n_0}\mathbb{E}[V^{2-}] + \frac{\mathbb{E}[\Theta^4]}{n_0^2} + \frac{2\mathbb{E}[\Theta^2]\,(n_0-1)+1}{n_0^2}\mathbb{E}[V^-]$.

## Sources

- Renato Vizuete, Paolo Frasca and Elena Panteley, "SIS Epidemics on Open Networks: A Replacement-Based Approximation", in *2024 European Control Conference (ECC)*, IEEE, 2024, 1602–1608, <https://doi.org/10.23919/ecc64448.2024.10591224>. Preprint version: arXiv:2403.16727 (2024), Propositions 1–4, Lemma 2 and Theorem 1, <https://doi.org/10.48550/arXiv.2403.16727>.
