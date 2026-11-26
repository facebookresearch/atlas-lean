# Uniqueness of monostable Lotka–Volterra competition travelling waves

**Model.** Two competitors $u, v$ on $\mathbb{R}$ follow the Lotka–Volterra competition–diffusion system

$$ u_t = u_{xx} + u(1 - u - av), \qquad v_t = d\,v_{xx} + rv(1 - v - bu), $$

with $d, r > 0$, $a \in (0,1)$ and $b \in (0,1)\cup(1,\infty)$. Let $(u^\star, v^\star)$ denote the stable state reached behind the invasion: the coexistence state $\big(\tfrac{1-a}{1-ab}, \tfrac{1-b}{1-ab}\big)$ when $0 < b < 1$, and $(1,0)$ when $b > 1$. A travelling wave of speed $c > 0$ is a profile $(U,V)(x - ct)$ solving

$$ U'' + cU' + U(1 - U - aV) = 0, \qquad dV'' + cV' + rV(1 - V - bU) = 0 . $$

**Theorem.** Let $c > 0$. If $(U,V)$ and $(\widetilde U,\widetilde V)$ are bounded nonnegative travelling waves of speed $c$ connecting $(u^\star,v^\star)$ at $-\infty$ to $(0,1)$ at $+\infty$, then $U' < 0 < V'$ on $\mathbb{R}$ and $(U,V) \equiv (\widetilde U(\cdot - \sigma), \widetilde V(\cdot - \sigma))$ for some $\sigma \in \mathbb{R}$.

So travelling waves are unique up to translation in both monostable regimes: weak competition ($0 < a, b < 1$) and $0 < a < 1 < b$, where the invader $u$ excludes the resident $v$. Such waves exist exactly for $c \ge c^0_{\mathrm{LLW}}$, a critical speed in $[2\sqrt{1-a}, 2]$.

## Expansion

The proof applies a Liouville-type rigidity principle for monotone parabolic systems. After the change of variable $w = 1 - v$ the system is cooperative, so one wave can be compared with translates of the other by sliding. Quantitative control of the leading edge of the single component $u$ (which decays like a solution of the linearization at $(0,1)$), plus mild persistence of $u$ behind the front, forces the infimum of admissible shifts to be attained, and the strong maximum principle then gives identity. The same principle gives convergence to these waves in the paper's results on interacting fronts, where the leading front of the faster species acts as a moving environment for the trailing one.

## Sources

- Émeric Bouin, King-Yeung Lam and Chang-Hong Wu, "Logarithmic corrections and interacting fronts in shifting environments and competition systems", arXiv:2610.26702 (2026), Section 1.3, Theorem 1.7 (uniqueness of travelling fronts) and Theorem 1.8; Section 9 and Appendix C (rigidity for monotone systems), <https://doi.org/10.48550/arXiv.2610.26702>.
