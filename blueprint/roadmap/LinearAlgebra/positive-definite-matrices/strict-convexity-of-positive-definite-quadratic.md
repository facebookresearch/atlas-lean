# Strict convexity of a positive-definite quadratic form

Let $A$ be a real symmetric $n \times n$ matrix and $q(x) = x^{\mathsf T}Ax$. If $A$ is positive definite, $q$ is strictly convex: for $x \ne y$ and $0 < t < 1$, $tq(x) + (1-t)q(y) - q(tx + (1-t)y) = t(1-t)q(x - y) > 0$. If $A$ is positive semidefinite and singular, $q$ is convex but not strictly convex, being constant along $\ker A$. Then for $b \in \mathbb{R}^n$ the objective $q(x) - 2b^{\mathsf T}x$ has minimizers exactly when $b$ lies in the range of $A$, and they form the affine set $\{x : Ax = b\}$, with more than one point; if $b$ is not in the range, there is $v \in \ker A$ with $b^{\mathsf T}v > 0$ and the objective is unbounded below along $tv$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, Section 3.1.4, Examples (quadratic functions), <https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
