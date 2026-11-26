# Stationarity of zig-zag processes on hybrid discrete–continuous spaces

Let $\mathcal{F}$ be a countable set of discrete states (e.g. tree topologies) and, for each $m\in\mathcal{F}$, let $\Omega_m^o\subset\mathbb{R}^d$ be open with piecewise Lipschitz boundary $\partial\Omega_m$ (non-corner points). The state space is $\{(m,\mathbf{x},\mathbf{v}):m\in\mathcal{F},\ \mathbf{x}\in\Omega_m^o,\ \mathbf{v}\in\{-1,1\}^d\}$ together with the inward boundary states. Given a density $\pi(m,\mathbf{x})$, the target is $\tilde\pi(m,\mathbf{x},\mathbf{v})=\pi(m,\mathbf{x})/2^d$.

**Zig-zag dynamics.** Between events $\mathbf{x}$ moves with constant velocity $\mathbf{v}$; coordinate $v_i$ flips at the canonical rate $\lambda_i(m,\mathbf{x},\mathbf{v})=\big(-v_i\,\partial_i\log\tilde\pi(m,\mathbf{x},\mathbf{v})\big)^+$, where $F_i$ denotes the map flipping the $i$th sign of $\mathbf{v}$. When the path hits $\partial\Omega$ with outward velocity, it jumps to an inward boundary state $(j,\mathbf{y},\mathbf{w})$ by a Markov kernel $Q$. The extended generator is

$$Lf(m,\mathbf{x},\mathbf{v})=\sum_{i=1}^dv_i\,\partial_if(m,\mathbf{x},\mathbf{v})+\sum_{i=1}^d\lambda_i(m,\mathbf{x},\mathbf{v})\big(f(m,\mathbf{x},F_i\mathbf{v})-f(m,\mathbf{x},\mathbf{v})\big),$$

with the boundary condition $f(m,\mathbf{x},\mathbf{v})=\int f\,dQ(m,\mathbf{x},\mathbf{v};\cdot)$ at exit points.

**Hypotheses on $Q$.** (i) Skew-detailed balance: $\tilde\pi(m,\mathbf{x},\mathbf{v})\,Q(m,\mathbf{x},\mathbf{v};j,d\mathbf{y},\mathbf{w})\,d\mathbf{x}=\tilde\pi(j,\mathbf{y},-\mathbf{w})\,Q(j,\mathbf{y},-\mathbf{w};m,d\mathbf{x},-\mathbf{v})\,d\mathbf{y}$. (ii) Flux preservation: $\int\sum_{\mathbf{w}}(\mathbf{w}\cdot n(j,\mathbf{y}))\,Q(m,\mathbf{x},\mathbf{v};j,d\mathbf{y},\mathbf{w})=-\mathbf{v}\cdot n(m,\mathbf{x})$, with $n$ the outward unit normal. (iii) Jumps a.s. never land on paths that run into corners.

**Statement.** Suppose $\mathcal{F}$ is finite, $\tilde\pi(m,\cdot,\mathbf{v})\in C^1(\Omega_m^o)$ and $\tilde\pi>0$, each $Q(m,\mathbf{x},\mathbf{v};\cdot)$ has compact support, the expected number of flips and boundary jumps on $[0,t]$ is finite for all $t$ and all starting points, and the initial law of $(m,\mathbf{x})$ has a density. If (i)–(iii) hold, the zig-zag process has stationary distribution $\tilde\pi$.

Ergodicity follows if the restricted single-domain zig-zag processes are ergodic and $Q$ moves mass between domains along a cycle of ordered pairs spanning the support of $\tilde\pi$.

## Expansion

Stationarity amounts to $\int Lf\,d\tilde\pi=0$ for $f$ in the domain. Inside each $\Omega_m^o$ the identity $\lambda_i(\mathbf{v})-\lambda_i(F_i\mathbf{v})=-v_i\partial_i\log\tilde\pi$ cancels the transport term after integration by parts, exactly as for the classical zig-zag sampler; the integration by parts leaves boundary terms $\int_{\partial\Omega}(\mathbf{v}\cdot n)f\,\tilde\pi$, and skew-detailed balance together with flux preservation makes the outgoing and incoming boundary fluxes cancel once the boundary condition of the domain is used. The result lets a non-reversible piecewise-deterministic sampler move between strata of different topology, which standard zig-zag processes on a single Euclidean domain cannot do.

## Sources

- J. Koskela, *Zig-zag sampling for discrete structures and non-reversible phylogenetic MCMC*, *Journal of Computational and Graphical Statistics* 31 (2022), 684–694, <https://doi.org/10.1080/10618600.2022.2032722>; preprint arXiv:2004.08807 (2020), <https://doi.org/10.48550/arXiv.2004.08807>. Preprint locators: Theorem 1 and the remark following it (Section 2, zig-zag on hybrid spaces).
