# Large-population limit of a trait-structured population with horizontal transfer

**Model.** Individuals carry a trait $x \in \mathbb{R}_+$. With carrying-capacity parameter $K$, the population is the rescaled point measure $Z^K_t = \frac1K \sum_i \delta_{x_i(t)}$. An individual of trait $x$
- gives birth to a clone at rate $b(x)$ and dies at rate $d(x) + C\langle Z^K_t, 1\rangle$ (logistic competition, $C > 0$);
- changes trait (variation) at rate $\gamma(x)$, jumping to $z$ with probability density $m(x,z)$;
- receives the trait of an individual of trait $y$ by horizontal transfer at rate $h(x, y, Z^K_t) = \frac{\tau\,\mathbf{1}\{y > x\}}{\beta + \mu\langle Z^K_t, 1\rangle}$ per partner (frequency-dependent, asymmetric: transfer only moves traits upward).

Assume $b, d, \gamma$ continuous and nonnegative, $b \le \overline{b}$, $\gamma \le \overline{\gamma}$, a Lyapunov-type moment bound on $d^{\eta}$ under $m$, and $\sup_K \mathbb{E}[\langle Z^K_0, 1\rangle^p] + \sup_K \mathbb{E}[\langle Z^K_0, d^\eta\rangle] < \infty$ for some $p > 2$.

**Theorem.** If $Z^K_0 \to \xi_0$ in probability, then $Z^K \to \xi$ in probability in $\mathbb{D}([0,T], M_F(\mathbb{R}_+))$, where $\xi$ is the unique continuous deterministic solution with $\sup_t \langle \xi_t, 1\rangle < \infty$ of

$$\langle \xi_t, \varphi\rangle = \langle \xi_0, \varphi\rangle + \int_0^t\!\!\int \big(b(x) - d(x) - C\langle\xi_s,1\rangle\big)\varphi(x)\,\xi_s(dx)\,ds + \int_0^t\!\!\int \gamma(x)\!\int (\varphi(z) - \varphi(x))\,m(x,z)\,dz\,\xi_s(dx)\,ds$$

$$\qquad + \int_0^t\!\!\iint (\varphi(x) - \varphi(y))\,\frac{\tau\,\mathbf{1}\{x > y\}}{\beta + \mu\langle\xi_s,1\rangle}\,\xi_s(dy)\,\xi_s(dx)\,ds$$

for bounded $\varphi$. The total mass $\lambda_t = \langle \xi_t, 1\rangle$ satisfies $\inf_{[0,T]}\lambda_t > 0$ and $\sup_t \lambda_t \le \max(\overline{b}/C, \lambda_0)$. If $\xi_0$ has a density, so does $\xi_t$, solving

$$\partial_t \xi_t(x) = \Big(r(x) - C\!\int \xi_t\Big)\xi_t(x) + \int \big[\gamma(y)\xi_t(y)m(y,x) - \gamma(x)\xi_t(x)m(x,y)\big]dy + \frac{\tau\,\xi_t(x)}{\beta + \mu\int\xi_t}\int \operatorname{sgn}(x - y)\,\xi_t(y)\,dy,$$

with $r = b - d$; positivity, continuity and boundedness of $\xi_0$ propagate to $\xi_t$.

## Depends on

## Expansion

Write the semimartingale decomposition of $\langle Z^K_t, \varphi\rangle$: the drift is the right-hand side above evaluated at $Z^K$ and the martingale has quadratic variation of order $1/K$. Moment bounds (using $p > 2$ and the Lyapunov control of the unbounded death rate) give tightness by Aldous–Rebolledo; every limit point solves the measure equation, and the nonlinear terms are Lipschitz in total variation on bounded-mass sets, giving uniqueness. The transfer term is quadratic in $\xi$ but its frequency-dependent normalization keeps it bounded by $2\tau\|\varphi\|_\infty\langle \xi,1\rangle/\mu$.

## Sources

- M. Deangeli Bravo, "Ancestral lineages under horizontal trait transfer: spinal decomposition and time reversal beyond stationarity", arXiv:2609.39270 (2026), Section 2, Theorem 2.2 and Propositions 2.3–2.4, <https://doi.org/10.48550/arXiv.2609.39270>.
