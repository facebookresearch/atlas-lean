# Stationary distribution of immune status under waning and boosting

**Setting.** The waning-boosting process with waning flow $\pi$, Poisson exposure rate $\Lambda$ and boosting map $f$ (minimum at $y_c$, $f(y) > y$) has transition kernel $Q_t$. Its *next-generation operator* $K$ maps the distribution of immune levels just after one boost to the distribution just after the next boost:

$$(K b)(\Gamma) = \int_{(0,\infty)} \int_0^\infty \Lambda e^{-\Lambda \sigma}\, \mathbf 1_\Gamma\bigl(f(\pi(\sigma, z))\bigr)\, d\sigma\; b(dz).$$

**Fixed point.** Suppose there exist $0 < \rho < 1$ and $z \ge f(f(y_c))$ such that $f(\pi(\rho/\Lambda, y)) < y$ for all large $y$ (precisely, for $y \ge f_+^{-1}(z)$, with $f_+^{-1}$ the branch of the inverse above $y_c$) and such that, with $\mathcal T(y) = \int_{y_c}^{y} d\eta/g(\eta)$ the waning-time primitive ($g < 0$ the waning rate) and $\alpha(y) = -\Lambda/\big(g(f_+^{-1}(y))\, f'(f_+^{-1}(y))\big) > 0$,

$$\int_z^y \alpha(\xi)\, e^{-\Lambda \mathcal T(f_-^{-1}(\xi))}\, d\xi \ \text{ is bounded for } y \in [z, \infty),$$

with $f_-^{-1}$ the branch of the inverse below $y_c$. Then $K$ has a unique fixed point, with a density that is strictly positive on $(f(y_c), \infty)$. For $g(y) = -wy$ the first condition holds for any $\delta \ge 0$ and $\rho \in (0,1)$; with $f(y) = y(1 + \sigma_2 y^{-\sigma_1})$, $\sigma_1 > 1$, $\sigma_2 > 0$, and $g(y) = -wy$ the integrability condition holds, and also holds if $g(y) = -wy$ only near zero provided $\Lambda > w(\sigma_1 - 1)$.

**Correspondence.** If $m$ is a stationary distribution of the process, then $b(\Gamma) = m(f^{-1}(\Gamma))$ is a fixed point of $K$; conversely, if $b$ is a fixed point of $K$, then

$$m(\Gamma) = \int_{(0,\infty)} \int_0^\infty \Lambda e^{-\Lambda \sigma}\, \mathbf 1_\Gamma\bigl(\pi(\sigma, z)\bigr)\, d\sigma\; b(dz)$$

is a stationary distribution (it satisfies $m(f^{-1}(\Gamma)) = (Kb)(\Gamma) = b(\Gamma)$). The source prints the converse as $m(\Gamma) = b(f(\Gamma))$, which is not a measure, since $f$ maps both $(0, y_c)$ and $(y_c, \infty)$ onto $(f(y_c), \infty)$. Hence there is a unique normalized stationary distribution of immune status; it has a density, strictly positive on $(0, \infty)$.

**Stability.** If moreover $f'(y)\, g(y) / g(f(y)) < 1$ for all $y > 0$, then for every initial distribution with density $\phi$, the density $T(t)\phi$ of $Q_t \times m$ satisfies

$$\lim_{t \to \infty} \| T(t)\phi - \psi \|_{L^1} = 0,$$

where $\psi$ is the stationary density.

## Depends on

- [Piecewise-deterministic waning-boosting process and its renewal equation](piecewise-deterministic-waning-boosting-process-and-its-renewal-equation.md)

## Expansion

The fixed-point equation for the density of $K$ is solved by splitting $f$ into its two monotone branches, turning it into a delay-type integral equation in the immune level; the condition $f(\pi(\rho/\Lambda, y)) < y$ says that, at high levels, waning over a typical inter-exposure time outweighs the boost, which keeps the solution integrable. The correspondence with stationary distributions expresses flux balance: in steady state jumps leave every level at rate $\Lambda$, and $f^{-1}$ maps arrival points to departure points. For stability, the semigroup $T(t)$ on $L^1(0, \infty)$ is a Markov semigroup that dominates the one-jump part $T_1(t)$ with $\|T_1(t)\| = \Lambda t e^{-\Lambda t} > 0$, so it is partially integral; a partially integral Markov semigroup with a unique, positive invariant density is asymptotically stable (Pichór–Rudnicki). Since the force of infection $\Lambda$ is held fixed, this stationary distribution describes the immune status of a population in which transmission is in steady state.

## Sources

- O. Diekmann, W. F. de Graaf, M. E. E. Kretzschmar, P. F. M. Teunis, "Waning and boosting: on the dynamics of immune status", Journal of Mathematical Biology (2018), Section 3, Lemmas 3.4–3.8 (conditions 3.25, 3.26, 3.30) and Theorem 3.9; Section 4, Theorem 4.1, Corollary 4.2, Lemma 4.4, Corollary 4.10 and Theorem 4.11 (Eq. 4.12). <https://doi.org/10.1007/s00285-018-1239-5> (PMC6280846).
