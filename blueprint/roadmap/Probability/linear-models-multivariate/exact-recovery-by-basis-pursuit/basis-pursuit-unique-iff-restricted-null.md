# Exact recovery by basis pursuit

For a matrix $X$ and a set $S$ of coordinates the following are equivalent.

1. For every $\theta^*$ supported on $S$, $\theta^*$ is the unique solution of basis pursuit
   $\min\{\|\theta\|_1 : X\theta = X\theta^*\}$: every $\theta$ with $X\theta = X\theta^*$ and $\|\theta\|_1 \le \|\theta^*\|_1$ equals $\theta^*$.
2. $X$ satisfies the restricted nullspace property over $S$.

The equivalence is uniform over the vectors supported on $S$. For a single $\theta^*$ the
restricted nullspace property is sufficient but not necessary, even when $\theta^*$ is the unique
sparsest solution: with $S = \{1, 2\}$, $\theta^* = (1, 1, 0, 0)$ and a $3 \times 4$ matrix whose
nullspace is spanned by $(1, -1, \tfrac12, \tfrac12)$, basis pursuit recovers $\theta^*$ uniquely
although the property fails.

Hastie, Tibshirani and Wainwright (2015), Theorem 10.1, is stated for a fixed $\theta^*$ that is
the unique sparsest solution; read that way, only its "if" direction holds, by the example above.
Their Exercise 10.4, which proves the converse, assumes recovery of all vectors supported on $S$,
which is the uniform statement above.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §7.2.2 (exact recovery and restricted nullspace).
- T. Hastie, R. Tibshirani and M. J. Wainwright, *Statistical Learning with Sparsity: The Lasso and Generalizations*, CRC Press, 2015: <https://hastie.su.domains/StatLearnSparsity/>, Theorem 10.1, §10.4.3.1 and Exercise 10.4.

## Background

- [$\ell_2$-error bound for the constrained Lasso](../lasso-error-bounds-under-restricted-eigenvalues/constrained-lasso-l2-error-le.md): the noisy counterpart, where the same cone argument bounds the error.
