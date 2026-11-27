# Critical connectivity for survival of a secondary infection on a sparse network

**Model.** Individuals occupy the vertices of an Erdős–Rényi random graph with mean degree $c$. A primary SIR infection is transmitted along each edge at rate $\beta_1$ and recovers at rate $\rho_1$. A secondary SIR infection, with transmission rate $\beta_2$ and recovery rate $\rho_2$, can only be carried by, and transmitted to, individuals currently infected with the primary; it is lost when its host recovers from the primary. Set $\alpha = \beta_1/\rho_1 = \beta_2/\rho_2$ (equal virulence) and $\varphi = \beta_1/\beta_2$ (relative timescale).

**Branching-process reduction.** In the limit of large sparse graphs the secondary infection is a multi-type branching process whose type is the time since the host acquired the primary infection, with a positive, integrable, continuous production kernel $\mu$ on $[0,\infty)$. For such a process the production operator $M$ has a simple positive eigenvalue $\lambda$ equal to its spectral radius (the only eigenvalue with a non-negative eigenfunction); the process dies out almost surely if $\lambda < 1$ and survives with positive probability if $\lambda > 1$.

**Theorem.** For all $\alpha, \varphi > 0$ there is a critical connectivity $c^\star$ such that, as the network size tends to infinity, the secondary infection dies out with probability one when $c < c^\star$ and survives with positive probability when $c > c^\star$. The value $c^\star$ is the smallest positive solution of

$$c^\star = \frac{(1+\alpha+\alpha\varphi)(1+\varphi+2\alpha+\alpha\varphi)}{\varphi}\;\frac{{}_0F_1\big(2+\varphi+(1+\varphi)/\alpha;\,-c^\star\varphi/\alpha^2\big)}{{}_0F_1\big(3+\varphi+(1+\varphi)/\alpha;\,-c^\star\varphi/\alpha^2\big)},$$

where ${}_0F_1(a;z) = \sum_{k\ge0} z^k/(k!\,(a)_k)$. Moreover

$$c^\star = \Theta(\varphi) \ \ (\varphi \to \infty), \qquad c^\star = \Theta(1/\varphi) \ \ (\varphi \to 0).$$

Hence, at fixed connectivity, the secondary infection survives only in a window of relative speeds around $\varphi \asymp 1$: if it is much faster than the primary it burns out the small infected cluster around it, and if it is much slower its hosts recover before it can be passed on. Increasing $\varphi$ through the window at fixed $c$ moves the system from extinction to survival and back, a re-entrant transition.

## Depends on

- [Galton–Watson law of generation sizes](../../branching-process-approximation-of-early-epidemi/has-law-bp-size.md)

## Expansion

The top eigenvalue $\lambda$ of the integral operator with the explicit kernel built from exponential infection and recovery clocks solves an implicit equation in ratios of ${}_0F_1$ functions; setting $\lambda = 1$ under $\beta_2/\rho_2 = \alpha$ gives the stated equation for $c^\star$. The asymptotics follow from bounds on $\Phi_a(z) = {}_0F_1(a;-z)/{}_0F_1(a+1;-z)$ in terms of the first positive zero $j_a$ of the Bessel function $J_a$: $a(a+2) < j_a^2 < 4(a+1)(a+2)$ and $1 < \Phi_a(z) < 1 + 4z/(j_a^2 - 4z)$ for $0 < z < j_a$.

## Sources

- Sam Moore, Peter Mörters, Tim Rogers, "A Re-entrant Phase Transition in the Survival of Secondary Infections on Networks", Journal of Statistical Physics 171 (2018), 1122–1135, <https://doi.org/10.1007/s10955-018-2050-9>. Published version of arXiv:1804.03570, cited next; locators there refer to the arXiv version.
- Sam Moore, Peter Mörters, Tim Rogers, "A re-entrant phase transition in the survival of secondary infections on networks", arXiv (2018). Theorem 1, Lemmas 1–3. <https://doi.org/10.48550/arXiv.1804.03570>
