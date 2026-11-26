# Coupling times with ambiguities

**Setting.** A particle system on $\mathbb{Z}$ with finite alphabet evolves by a countable family of local rules $i\in\mathcal{I}$: rule $i$ fires at the events $\Psi(x,i,k)$ of independent Poisson processes attached to sites $x$, and when fired it updates the configuration on the finite window $x+A_i$ as a function of the current configuration there. Running the system from time $u<0$ to $0^-$ from configuration $\xi$ defines a stochastic flow $\Phi(\xi,u,t,\cdot)$.

**Definition.** A *coupling time with ambiguities* is a pair $(H,T)$, where $T<0$ is a random time and $H=\{H(x,i,k)\}$ is an a.s. finitely supported $\{0,1\}$-valued family, such that $H(x,i,k)=0$ whenever $\Psi(x,i,k)<T$, $H(x,i,k)$ depends only on the Poisson data after $\Psi(x,i,k)$, and for every $t<T$ and all configurations $\xi,\xi'$: if the marked events ($H=1$) are performed or not performed identically from $\xi$ and from $\xi'$, then the state of site $0$ at time $0^-$ is the same. Its *growth parameter* is $m(H,T)=\mathbb{E}\sum_{x,i,k}H(x,i,k)$, and it is *subcritical* if $m(H,T)<1$. The width is bounded by $(a_-,a_+)$ if $H$ and the relevant influences depend only on sites in $[-a_-,a_+]$.

The ambiguities are the marked events whose effect depends on the unknown past; each must itself be resolved recursively, producing a Galton–Watson-type tree of ambiguities with mean offspring $m(H,T)$.

**Theorems.**
1. *(Ergodicity.)* If a subcritical coupling time with ambiguities exists, the system has a unique invariant law $\mu$ and $X_t^\xi\to\mu$ in distribution for every $\xi$.
2. *(Explicit bound.)* For finite $B\subset\mathbb{Z}$, $d_{TV}\bigl(X_t^\xi|_B,\ \mu|_B\bigr)\le \#B\cdot\inf_{n\ge0}\Bigl(m^n+\sum_{k=1}^n\inf_{\lambda\ge0}\Lambda_H(\lambda)^k\Lambda_T(\lambda)e^{-\lambda t}\Bigr)$, with $\Lambda_H,\Lambda_T$ exponential moments built from $H$ and $T$.
3. *(Exponential convergence.)* With finite width and exponentially integrable $T$, finite marginals converge exponentially fast in total variation.
4. *(Decay of correlations.)* With $m<1$ and width bounded by $(a_-,a_+)$, $d_{TV}\bigl(\mu|_{\{x,y\}},\mu|_{\{x\}}\otimes\mu|_{\{y\}}\bigr)\le 2m^{\kappa(y-x)-1}$ with $\kappa(z)=|z|/(a_++a_-)$.

## Expansion

The construction runs coupling from the past: to determine site $0$ at time $0^-$ one looks back to the last event that fixes it regardless of the past. A plain coupling time requires this to happen with no residual dependence; allowing ambiguities means only that the dependence is confined to finitely many marked events, each of which is examined further back in time. When the mean number of ambiguities generated per ambiguity is below $1$, the resulting branching process dies out a.s., which yields a finite backward exploration and hence a perfect sample from $\mu$ at site $0$; uniqueness and convergence follow. The bounds come from controlling the depth of the branching process and the time it spans.

## Sources

- J. Bérard, D. Piau, "Coupling times with ambiguities for particle systems and applications to context-dependent DNA substitution models", arXiv:0712.0072 (2007), Section 2 (Definitions 2.2–2.4, 2.6, 2.9, 2.10 and 2.12, Proposition 2.5, subcriticality), Theorems 1–4, <https://doi.org/10.48550/arXiv.0712.0072>.
