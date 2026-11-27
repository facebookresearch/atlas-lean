# Extremal stationary measures of voter models with stirring and on dynamical percolation

**Voter model and duality.** In the voter model on a locally finite connected graph $G$, each vertex at rate $1$ copies the opinion ($0$ or $1$) of a uniformly chosen neighbour. Started from Bernoulli($\alpha$) product measure $\pi_\alpha$, the law at time $t$ converges to a stationary measure $\mu_\alpha$. Say that $G$ has the *infinite collision property* if two independent continuous-time simple random walks on $G$ meet almost surely, and the *finite collision property* if they meet only finitely often almost surely.

**Theorem (general graphs).** Let $\mathcal I_e$ be the set of extremal stationary measures.
- (A) If $G$ has the infinite collision property, $\mathcal I_e = \{\delta_{\bar 0}, \delta_{\bar 1}\}$ (consensus).
- (B) If $G$ has the finite collision property and the tail $\sigma$-algebra of simple random walk on $G$ is trivial, $\mathcal I_e = \{\mu_\alpha : \alpha \in [0, 1]\}$.

**Theorem (two variants).**
1. *Voter model with stirring* on a $d$-regular graph ($d \ge 2$), where in addition neighbouring voters exchange opinions at rate $\mathsf v > 0$: from $\pi_\alpha$ the law converges to stationary measures $\mu^{\mathrm{stir}}_\alpha$, which are distinct; under infinite collision the only extremal ones are $\mu^{\mathrm{stir}}_0, \mu^{\mathrm{stir}}_1$, and under finite collision with trivial tail $\mathcal I_e = \{\mu^{\mathrm{stir}}_\alpha\}$. On $\mathbb Z^d$ each $\mu^{\mathrm{stir}}_\alpha$ is translation ergodic.
2. *Voter model on dynamical percolation* on $\mathbb Z^d$: edges refresh at rate $\mathsf v$ to open with probability $p$, and a voter copies a uniformly chosen site in its $\ell^1$-ball of radius $R$ only if an open path inside the ball connects them. From $\pi_\alpha \otimes \pi^{\mathrm{edge}}_p$ the law converges to distinct, translation-ergodic stationary measures $\mu^{\mathrm{dyn}}_\alpha$; for $d = 1, 2$ the only extremal ones are $\mu^{\mathrm{dyn}}_0, \mu^{\mathrm{dyn}}_1$, while for $d \ge 3$ the extremal set is $\{\mu^{\mathrm{dyn}}_\alpha : \alpha \in [0, 1]\}$.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../../../coalescent-theory/structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

The voter model is dual to coalescing random walks: the opinions at finitely many sites are those of the ancestors reached by tracing lineages backward, and lineages merge when they meet. If two lineages always meet, all opinions eventually derive from one ancestor and only consensus survives; if they meet finitely often, the genealogy retains infinitely many ancestral families and a one-parameter family of non-trivial equilibria appears, with tail triviality ruling out further extremal measures. In both variants the dual walks move in a dynamic environment (stirring adds swaps, dynamical percolation blocks moves), and the work is to show that the collision dichotomy of independent walks survives: two walks on a shared dynamical-percolation environment meet a.s. in $d \le 2$ and, for $d \ge 3$, meet only finitely often.

## Sources

- Jhon Astoquillca, "On the Stationary Measures of Two Variants of the Voter Model", J. Theoret. Probab. 39 (2026), 34, <https://doi.org/10.1007/s10959-025-01474-1>. Numbering follows the arXiv version, arXiv:2409.16064 (2024): Theorem 1.1, Proposition 1.2, Theorem 1.3, Theorem 2.2 and Section 4, <https://doi.org/10.48550/arXiv.2409.16064>.
