# Primal optimal value

Throughout, $E$ is a real vector space, $D \subseteq E$, $\iota$ is a finite index set, and the problem is to minimize $f_0(x)$ subject to $x \in D$ and $f_i(x) \le 0$ for $i \in \iota$, with $f_0, f_i \colon E \to \mathbb{R}$. Its **optimal value** is

$$p^\star = \inf\{f_0(x) : x \in D,\ f_i(x) \le 0 \text{ for all } i\} \in [-\infty, \infty],$$

with $p^\star = +\infty$ for an infeasible problem and $p^\star = -\infty$ for one unbounded below.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §4.1.1.
