# Optimal release ratio for the sterile-insect integrodifference model

**State equation.** On a bounded habitat $\Omega$, the wild mosquito density $W_t(x)$ in discrete generations $t = 0, \dots, T$ evolves as

$$W_{t+1}(x) = \int_\Omega k(x,y)\,\frac{1}{1 + r_t(y)\,\bar W(y)/W_t(y)}\, f\big(W_t(y), y\big)\,dy, \qquad f(W, y) = A\,W e^{-K(y) W},$$

where $f$ is Ricker growth (intrinsic growth $A$, density feedback $K$), $k(x,y) \ge 0$ is a bounded dispersal kernel with $\int_\Omega k(x,y)\,dy \le 1$, $\bar W$ is the wild equilibrium, and $r_t(x) \in [0, r_{\max}]$ is the release ratio: $r_t\bar W$ sterile insects are released, so a wild female mates fertilely with probability $W_t/(W_t + r_t\bar W)$.

**Control problem.** Minimize

$$J(r) = \sum_{t=0}^{T-1}\int_\Omega \Big(m_t W_t(x) + n_t r_t(x)\bar W(x) + s_t\, r_t(x)^2\,\bar W(x)^2\Big)\,dx$$

(linear cost of wild insects, quadratic cost of rearing and releasing sterile ones) over bounded measurable controls.

**Theorem (necessary conditions).** The control-to-state map is differentiable, with sensitivity $\psi$ solving the linearized integrodifference equation with $\psi_0 = 0$. If $r^*$ is optimal with state $W$, there is a weak solution $\lambda$ of the adjoint system

$$\lambda_t(x) = \frac{\partial}{\partial W}\Big[\frac{W f(W, x)}{W + r_t(x)\bar W(x)}\Big]_{W = W_t(x)}\int_\Omega k(y,x)\lambda_{t+1}(y)\,dy + m_t, \qquad \lambda_T = 0,$$

where the coefficient equals $\dfrac{W_t\,\partial_W f(W_t, x)}{W_t + r_t\bar W} + \dfrac{f(W_t, x)\, r_t \bar W}{(W_t + r_t\bar W)^2}$, the second term coming from the dependence of the mating fraction on $W_t$,

and the optimal release ratio is

$$r_t^*(x) = \big(X - 1\big)\,\frac{W_t(x)}{\bar W(x)},$$

where $X$ is the real root of the cubic $X^3 + bX^2 + d = 0$ with

$$b = \frac{n_t}{2 s_t W_t(x)} - 1, \qquad d = -\,\frac{f\big(W_t(x), x\big)\int_\Omega \lambda_{t+1}(y)k(y,x)\,dy}{2 s_t\, W_t(x)^2} ;$$

when the root gives a negative ratio the control is set to zero (no release).

## Expansion

The directional derivative of $J$ at $r^*$ along an admissible variation $l$ is $\sum_t\int (m_t\psi_t + n_t\bar W l_t + 2 s_t r^*_t \bar W^2 l_t)$; the adjoint absorbs the $m_t\psi_t$ term after exchanging integration order. Setting the remaining integrand to zero gives, with $A_1 = f\int\lambda_{t+1}k$, $B = \bar W/W_t$, $C = n_t\bar W$, $D = 2 s_t\bar W^2$, the scalar condition $-A_1 B/(1 + Br)^2 + C + Dr = 0$, since $\partial_r[W f/(W + r\bar W)] = -f\,W\bar W/(W + r\bar W)^2 = -fB/(1 + Br)^2$; substituting $X = 1 + Br$ turns it into the cubic, with $b = CB/D - 1$ and $d = -A_1 B^2/D$. (The source keeps the factor $B$ in its Eq. (19) but drops it in Eqs. (23) and (26), and omits the mating-fraction term of the adjoint.) The left-hand side is increasing in $r$ when $A_1 \ge 0$, so the stationary point is unique. Solved by forward–backward sweeps with a Laplace kernel on $\Omega = [0,1]$ ($A = 2$, $K = 0.001$, $m = n = 1$, $s = 5$), the optimum starts at about $1.23$ sterile per wild insect, releases more where wild density is higher, and suppresses the wild population by about $73\%$ by generation $5$ without eliminating it.

## Sources

- K. Kura, D. Khamis, C. El Mouden, M. B. Bonsall, "Optimal control for disease vector management in SIT models: an integrodifference equation approach", Journal of Mathematical Biology 78 (2019) 1821–1839, Sect. 3–5, equations (4)–(13), Theorem 1, Theorem 2 and Appendix equations (24)–(34), <https://doi.org/10.1007/s00285-019-01327-6>, PMCID: PMC6469698.
