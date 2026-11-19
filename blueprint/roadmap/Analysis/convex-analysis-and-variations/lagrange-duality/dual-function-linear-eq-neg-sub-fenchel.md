# The dual function of a linearly constrained problem is minus a conjugate

Let $E$ be a real normed space, $f_0 \colon E \to \mathbb{R}$, and for $i$ in a finite set $\iota$ let $a_i$ be a continuous linear functional on $E$ and $b_i \in \mathbb{R}$. For the problem of minimizing $f_0(x)$ subject to $a_i(x) \le b_i$, the Lagrange dual function (with $D = E$) is

$$g(\mu) = -\sum_i \mu_i b_i - f_0^*\Big(-\sum_i \mu_i a_i\Big), \qquad \mu \in \mathbb{R}^\iota,$$

where $f_0^*(L) = \sup_x \big(L(x) - f_0(x)\big)$ is the Fenchel conjugate, and both sides are extended reals. Computing the dual of a linearly constrained problem thus amounts to computing a conjugate; e.g. $g(\mu) = -\infty$ exactly when $-\sum_i \mu_i a_i$ lies outside the domain of $f_0^*$.

## Background

- [Fenchel conjugate](../fenchel-moreau-theorem/fenchel-conj.md): background, the conjugate $f_0^*$, here of the real-valued objective viewed as an extended-real function.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §5.1.6 ("The Lagrange dual function and conjugate functions"), eq. (5.11), without equality constraints.
