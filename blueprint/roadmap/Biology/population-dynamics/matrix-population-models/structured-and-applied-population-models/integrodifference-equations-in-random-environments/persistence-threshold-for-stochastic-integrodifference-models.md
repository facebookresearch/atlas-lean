# Persistence threshold for stochastic integrodifference models

**Model.** Let $\Omega$ be a bounded habitat (for example a river segment) and $\{\alpha_t\}_{t \ge 0}$ i.i.d. random environmental states in an index set $A$. A population density $n_t \in C_+(\Omega)$ evolves by

$$n_{t+1}(x) = F_{\alpha_t}(n_t)(x) := \int_\Omega K_{\alpha_t}(x - y)\, f_{\alpha_t}(n_t(y))\, dy ,$$

where, uniformly in $\alpha \in A$:
- (C1) each dispersal kernel $K_\alpha$ is continuous with $0 < \underline K \le K_\alpha \le \overline K$ on $\Omega \times \Omega$;
- (C2) each growth function $f_\alpha$ is continuous, vanishes for $u \le 0$, is increasing, bounded by $m$, has $f_\alpha(u)/u$ strictly decreasing in $u > 0$, is right differentiable at $0$ with $f_\alpha(u)/u \to f_\alpha'(0)$ uniformly, $0 < \underline f \le f_\alpha'(0) \le \overline f$, and $\inf_\alpha f_\alpha(m \overline K |\Omega|) > 0$;
- (C3) there is a worst-case-dominating environment $\alpha^\ast$ with $F_\alpha(u) \le F_{\alpha^\ast}(u)$ for all $\alpha$ and $u$.

**Theorem 1.** For nonzero $n_0 \in C_+(\Omega)$, $n_t$ converges in distribution to a stationary distribution $\mu^\ast$ independent of $n_0$, concentrated either at $0$ (extinction) or on $C_+(\Omega) \setminus \{0\}$ (persistence). With $L_\alpha = F_\alpha'(0)$ and

$$r = \lim_{t\to\infty} \big\| L_{\alpha_t} \circ \cdots \circ L_{\alpha_1} \big\|^{1/t},$$

the population goes extinct if $r < 1$ and persists if $r > 1$.

**Theorem 2.** Let $n_t$ solve the linearization $n_{t+1}(x) = R_{\alpha_t} \int_\Omega K_{\alpha_t}(x-y)\, n_t(y)\,dy$ with $R_\alpha = f_\alpha'(0)$. The asymptotic growth rate

$$\Lambda = \lim_{t \to \infty} \Big( \int_\Omega n_t(x)\, dx \Big)^{1/t}$$

exists, is independent of $n_0 \in C_+(\Omega) \setminus \{0\}$, and $\Lambda = r$. Hence $\Lambda > 1$ gives persistence and $\Lambda < 1$ extinction.

## Expansion

Theorem 1 applies the theory of Hardin, Takáč and Webb for random compositions of monotone, sublinear (concave-type) positive operators: positivity and boundedness of the kernels make every $F_\alpha$ strongly positive and compact, the decreasing per-capita growth gives sublinearity, and the dominating environment provides a uniform absorbing bound, so the stochastic dynamics has a unique nontrivial or trivial stationary law decided by the top Lyapunov exponent $\log r$ of the linearized random products. Theorem 2 replaces the operator norm by the total population of the linear model, which is easy to simulate: because the kernels are bounded above and below, the total mass and the norm grow at the same exponential rate.

## Sources

- J. Jacobsen, Y. Jin, M. A. Lewis, "Integrodifference models for persistence in temporally varying river environments", Journal of Mathematical Biology 70(3) (2015) 549, Equations (44)-(48), assumptions (C1)-(C3), Theorems 1-2, Appendices A.3-A.4, <https://doi.org/10.1007/s00285-014-0774-y>, PMCID PMC4289536.
