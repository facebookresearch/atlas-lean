# Discrete-time SEIR model as a regular quadratic stochastic operator

**Model.** Let $x, y, u, v$ be the population fractions of susceptible, exposed, infectious and recovered individuals in a closed population, $x + y + u + v = 1$. With transmission rate $\beta \ge 0$, relative infectiousness $q \ge 0$ of exposed individuals, progression rate $a > 0$ (inverse latent period) and removal rate $b > 0$ (inverse infectious period), the explicit Euler step of the SEIR system defines the map $V$ on the simplex $S^3$:

$$
\begin{aligned}
x' &= x - \beta x (u + q y), & y' &= y - a y + \beta x (u + q y),\\
u' &= u - b u + a y, & v' &= v + b u .
\end{aligned}
$$

A **quadratic stochastic operator** (QSO) on $S^{m-1}$ is a map $x'_k = \sum_{i,j} P_{ij,k}\, x_i x_j$ with $P_{ij,k} = P_{ji,k} \ge 0$ and $\sum_k P_{ij,k} = 1$; it is **regular** if $\lim_{n\to\infty} F^n(\lambda)$ exists for every starting point $\lambda$. Using $x + y + u + v = 1$, every linear term can be written as a quadratic form, so $V$ is a candidate QSO.

**Proposition (simplex invariance).** $V(S^3) \subset S^3$ if and only if

$$
a,\ b,\ \beta \in [0,1] \qquad\text{and}\qquad \beta q \le 1 ,
$$

and under these conditions $V$ is a quadratic stochastic operator.

**Fixed points.** Every fixed point lies on the boundary edge $\{y = u = 0\}$, $\Lambda(\alpha) = (\alpha, 0, 0, 1 - \alpha)$ with $\alpha \in [0,1]$ (an uncountable family), and each is non-hyperbolic (one Jacobian eigenvalue equals $1$, along the edge). The two transverse eigenvalues are those of $\begin{pmatrix}1-a+\beta\alpha q&\beta\alpha\\ a&1-b\end{pmatrix}$ and are real. The smaller one has modulus at most $1$, and less than $1$ unless $a=b=\beta=\alpha=1$ and $q=0$, where the transverse eigenvalues are $\pm1$; the other has modulus less than $1$, equal to $1$, or greater than $1$ according as

$$
\alpha < \frac{ab}{\beta(a + bq)}, \qquad \alpha = \frac{ab}{\beta(a + bq)}, \qquad \alpha > \frac{ab}{\beta(a + bq)} .
$$

**Theorem (regularity and epidemic burn-out).** Under the invariance conditions, every trajectory of $V$ that does not start at a fixed point converges:

$$
\lim_{n\to\infty} V^n(x^0, y^0, u^0, v^0) = (\bar x, 0, 0, 1 - \bar x), \qquad \bar x < \frac{ab}{\beta(a + bq)},
$$

where $\bar x$ depends on the parameters and the initial point. In particular $V$ is regular, and the epidemic always dies out, leaving a susceptible fraction below the threshold. When $\beta = 0$ the limit is $(x^0, 0, 0, 1 - x^0)$.

## Expansion

Non-negativity of $x'$ needs $\beta(u + qy) \le 1$ on the simplex, which reduces to $\beta \le 1$ and $\beta q \le 1$; non-negativity of $y'$, $u'$ needs $a, b \le 1$. With $\chi(\mu)=\det(\mu I-B)$ for the transverse block $B$, one has $\chi(-1)=(2-a+\beta\alpha q)(2-b)-a\beta\alpha\ge(2-a)(2-b)-a\ge0$ under the invariance conditions, with equality exactly at the corner $a=b=\beta=\alpha=1$, $q=0$; so the smaller eigenvalue is $\ge-1$, and $>-1$ off that corner. The source's Lemma 1 asserts strict inequality for every $\alpha$, which fails at this corner. The threshold $ab/(\beta(a+bq))$ is the susceptible fraction at which the effective reproduction number $\beta x(1/b + q/a)$ equals $1$: below it the linearized infection subsystem at $\Lambda(\alpha)$ is contracting. For convergence, the sets $\{x = 0\}$, $\{y = u = 0\}$ and $M = \{ay - \beta x(u + qy) > 0,\ bu - ay > 0\}$ are invariant. Every orbit enters $M$ after finitely many steps, and on $M$ the coordinates $x$, $y$ and $u$ decrease monotonically, so they converge; the limit must be a fixed point, hence of the form $\Lambda(\bar x)$. Since $x$ decreases while the infection persists and any limit with $\bar x$ above the threshold is repelling, $\bar x$ lies strictly below the threshold.

## Sources

- U. A. Rozikov and S. K. Shoyimardonov, "An application of discrete-time SEIR model to the COVID-19 spread", arXiv (2021), Definition 1, Proposition 1 (invariance), Proposition 2 (regularity), Proposition 3 and Lemma 1 (fixed points), Lemmas 2–3 and Theorem 1 (limits of trajectories), <https://doi.org/10.48550/arXiv.2105.00238>.
