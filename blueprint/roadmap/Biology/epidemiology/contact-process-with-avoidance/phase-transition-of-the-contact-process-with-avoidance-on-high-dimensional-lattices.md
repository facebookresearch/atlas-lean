# Phase transition of the contact process with avoidance on high-dimensional lattices

**Model.** On a directed graph $G$, each vertex is healthy or infected and each edge is active or inactive. An infected vertex infects each healthy out-neighbour across each active edge at rate $\lambda$ and recovers at rate $1$; each active edge from an infected vertex to a healthy vertex becomes inactive at rate $\alpha > 0$ (the healthy host avoids the infected one); an inactive edge becomes active again when its tail vertex recovers. With $\alpha = 0$ this is the classical contact process (SIS epidemic).

For fixed $\alpha$ and $G = \mathbb{Z}^d$ with nearest-neighbour edges in both directions, let $\lambda(\alpha, d)^-$ and $\lambda(\alpha, d)^+$ be thresholds such that the infection dies out almost surely for $\lambda < \lambda(\alpha,d)^-$ and survives with positive probability for $\lambda > \lambda(\alpha,d)^+$.

**Theorem.**
1. $\lambda(\alpha, d)^- \ge \dfrac{1}{2d}$ for every $d$.
2. $\lambda(\alpha, d)^+ \le a_1 + a_2\alpha$ for all $d \in \mathbb{N}$, with constants $a_1, a_2$ independent of $d$.
3. There is $D(\alpha) \in \mathbb{N}$ such that for all $d \ge D(\alpha)$,
$$
\lambda(\alpha, d)^+ \le \frac{C}{d}, \qquad C = 2\bigl((1 - e^{-1})\, e^{-4\alpha}\, e^{-3}\bigr)^{-1}.
$$
Hence both thresholds are of order $1/d$ as $d \to \infty$.
4. *(Invariant measure.)* For $d \ge D(\alpha)$ and $\lambda > C/d$, the process started with every vertex infected and every edge active has a non-trivial translation- and time-invariant measure.

The methods and most results also apply to the SIRS model and to an isolation model in which infected vertices become isolated at rate $\alpha$ and both isolated and infected vertices become healthy at rate $1$.

## Depends on

- [Spectral radius and die-out of SIS epidemics](../epidemics-on-networks/spectral-radius-and-die-out-of-sis-epidemics.md)

## Expansion

Avoidance only removes infection paths, so the process is dominated by the classical contact process; a comparison with a branching random walk in which each infected vertex creates $2d$ potential infections at rate $\lambda$ and dies at rate $1$ gives extinction when $2d\lambda < 1$. For survival, avoidance can cut an edge only after the healthy endpoint has been exposed for an exponential time of rate $\alpha$, so an infection that is transmitted quickly still spreads; the explicit constant $C$ collects the probabilities of such favourable events (no recovery and no avoidance during a time window of order one), and in high dimension the abundance of fresh neighbours lets survival be proved once $\lambda d$ exceeds a constant, matching the $1/(2d)$ lower bound up to a constant factor.

## Sources

- A. Heeszel, M. Wascher, "Epidemics with avoidance and isolation on $\mathbb{Z}^d$", arXiv:2609.03359 (2026), Theorems 1–2, <https://doi.org/10.48550/arXiv.2609.03359>.
