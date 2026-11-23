# Lagrange dual function

Throughout, $E$ is a real vector space, $D \subseteq E$, $\iota$ is a finite index set, and the problem is to minimize $f_0(x)$ subject to $x \in D$ and $f_i(x) \le 0$ for $i \in \iota$, with $f_0, f_i \colon E \to \mathbb{R}$. The **Lagrange dual function** is

$$g(\mu) = \inf_{x \in D} L(x, \mu) \in [-\infty, \infty],$$

taken in the extended reals because it may be $-\infty$ (and is $+\infty$ when $D$ is empty).

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §5.1.2.
