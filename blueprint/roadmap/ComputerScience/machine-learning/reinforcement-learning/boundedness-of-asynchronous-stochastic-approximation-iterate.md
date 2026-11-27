# Boundedness of asynchronous stochastic-approximation iterates

Consider the asynchronous stochastic-approximation iteration in $\mathbb{R}^n$ under Tsitsiklis's
Assumptions 1–3 (eventually refreshed outdated information; step sizes measurable with respect to the
history, with $\sum_t \alpha_i(t) = \infty$ and $\sum_t \alpha_i(t)^2 \le C$ for a deterministic $C$; noise
with zero conditional mean and conditional second moment at most $A + B \max_j \max_{\tau \le t}
\lvert x_j(\tau) \rvert^2$). Suppose further (Assumption 6) that there are a positive vector $v$,
$0 \le \beta < 1$ and $D \ge 0$ with $\lVert F(x) \rVert_v \le \beta \lVert x \rVert_v + D$ for every $x$, where
$\lVert x \rVert_v = \max_i \lvert x_i \rvert / v_i$. Then the iterates $x(t)$ are bounded with probability
one.

## Sources

- J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, Machine Learning 16 (1994) 185–202, Assumptions 1–3 and 6 (pp. 188–189) and Theorem 1 (p. 189). <https://www.mit.edu/~jnt/Papers/J052-94-jnt-q.pdf>
