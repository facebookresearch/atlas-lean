# Replicator and Fleming–Viot limits of Moran processes on metric strategy spaces

**Setting.** A population of $N$ agents carries strategies in a metric space $\mathcal V$ (possibly infinite, e.g. a continuum of traits); its state is the empirical measure $\lambda \in \mathcal P(\mathcal V)$. Let $\pi_\lambda(\sigma)$ be the payoff of strategy $\sigma$ against population $\lambda$, $\bar\pi_\lambda = \int\pi_\lambda\,d\lambda$ the mean payoff, and assume the payoffs are bounded and Lipschitz (assumption $(\pi.1)$). In each step of length $\tau$ of a frequency-dependent Moran process with selection intensity $w$, one agent reproduces with probability proportional to its fitness $1 - w + w\pi_\lambda$ and its offspring replaces a uniformly chosen agent. The law of the empirical measure, $\Lambda^N_t \in \mathcal P(\mathcal P(\mathcal V))$, is the Eulerian description. Write $b(\lambda) = (\pi_\lambda - \bar\pi_\lambda)\lambda$ for the replicator vector field.

**Theorem.** Let $N_k \to \infty$, $w_k \to 0$, with time steps $\tau_k$.
1. If $w_k/(\tau_kN_k) \to \gamma \ge 0$ and $1/(\tau_kN_k^2) \to \nu > 0$, then along a subsequence $\Lambda^{N_k}_t \to \Lambda_t$ in $W_1$ for every $t \in [0,T]$, where $\Lambda$ is a very weak solution of the *replicator equation with genetic drift*: for every $\psi \in C^2([0,T]\times\mathcal P(\mathcal V))$,
$$\frac{d}{dt}\int\psi\,d\Lambda_t = \int\Big(\partial_t\psi + \gamma\,D_\lambda\psi[b(\lambda)] + \frac{\nu}{2}\iint D^2_\lambda\psi\big[\delta_\sigma - \delta_{\bar\sigma},\, \delta_\sigma - \delta_{\bar\sigma}\big]\,d\lambda(\sigma)\,d\lambda(\bar\sigma)\Big)d\Lambda_t(\lambda).$$
The second-order term is the Fleming–Viot (resampling) operator; for two strategies it reduces to the Kimura diffusion. With $\gamma = 0$ (including neutrality, $w = 0$) one obtains pure genetic drift.
2. If $w_k/(\tau_kN_k) \to \gamma > 0$ and $1/(\tau_kN_k^2) \to 0$, the limit is a weak solution of the deterministic *replicator equation* $\partial_t\Lambda_t + \operatorname{div}_\lambda\big(\gamma\, b(\lambda)\Lambda_t\big) = 0$, Lipschitz in $W_1$.
3. Under strong selection ($w \in (0,1]$ fixed) and $1/(\tau_kN_k) \to \gamma > 0$, the same holds with the field $b(\lambda) = \dfrac{w(\pi_\lambda - \bar\pi_\lambda)\lambda}{1 + w(\bar\pi_\lambda - 1)}$.

## Expansion

Each Moran step changes $\lambda$ by $\pm 1/N$ of a Dirac mass; the expected change is $w/N$ times the replicator field and the second moment is of order $1/N^2$. Rescaling time by $\tau$ and expanding test functions to second order in $\lambda$ gives an approximate equation whose drift coefficient is $w/(\tau N)$ and whose diffusion coefficient is $1/(\tau N^2)$, which explains the two scaling regimes. Compactness of the interpolated curves in $W_1$ over $\mathcal P(\mathcal P(\mathcal V))$ then yields limit points solving the limiting weak formulation. Working in Eulerian coordinates (laws of empirical measures) rather than with individual trajectories avoids any structure on $\mathcal V$ beyond a metric.

## Sources

- S. Almi, R. Durastanti, M. Morandotti, G. Orlando, "Scaling limits for Moran processes on metric strategy spaces: an Eulerian derivation of pure replicator and Fleming–Viot measure-valued PDEs", arXiv:2609.23235 (2026), Theorems 3.9, 3.11 and 3.12, <https://doi.org/10.48550/arXiv.2609.23235>.
