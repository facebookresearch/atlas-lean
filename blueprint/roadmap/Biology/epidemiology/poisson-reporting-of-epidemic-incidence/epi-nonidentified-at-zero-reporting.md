# With zero reporting, incidence in the first interval is not identified

Let $n \ge 1$ be a number of intervals and $c \in [0, \infty)^n$ a background vector. Consider the
family of laws that sends an incidence vector $x \in [0, \infty)^n$ to the
[reporting law](reporting-law.md) $\bigotimes_j \operatorname{Po}(\lambda_j)$ of the
[intensity vector](intensity-at.md) $\lambda_j = c_j + \rho\, x_j$ at reporting fraction $\rho = 0$.
The estimand $x \mapsto x_0$, the incidence of the first interval, is not identified by this
family: it is not true that incidence vectors with the same law always have the same estimand.
Here an estimand $\tau$ is identified by a family of laws $P_x$ when $P_x = P_{x'}$ implies
$\tau(x) = \tau(x')$. Indeed at $\rho = 0$ the intensity is
[the background vector](intensity-at-zero.md) for every incidence vector, so the zero vector and
the vector equal to $1$ at the first interval and $0$ elsewhere have the same law but estimands
$0$ and $1$.
