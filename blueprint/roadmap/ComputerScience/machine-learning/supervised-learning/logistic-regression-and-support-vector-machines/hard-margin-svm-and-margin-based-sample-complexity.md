# Hard-margin SVM and margin-based sample complexity

This node collects the hard-margin and soft-margin SVM results.

## Expansion

A sound expansion has separate pages for:

1. **Hard-SVM program.** For linearly separable data, $\min \lVert w \rVert^2$ subject to $y_i \langle w, x_i \rangle \ge 1$
   (homogeneous form) has a unique solution, and by the KKT conditions it is a nonnegative combination of the
   support vectors $y_i x_i$ with active constraints.
2. **Margin generalization.** If $D$ is separable with margin $\gamma > 0$ (some unit $u$ with
   $y \langle u, x \rangle \ge \gamma$ almost surely) and $\lVert x \rVert \le \rho$ almost surely, then for every
   $\delta \in (0,1)$, with probability at least $1 - \delta$ over $m$ samples, the 0-1 error of the hard-SVM output is at
   most $\sqrt{4(\rho/\gamma)^2/m} + \sqrt{2\log(2/\delta)/m}$, independent of the dimension.
3. **Soft-SVM** as regularized loss minimization with the hinge loss, with its own guarantee.

## Proof depends on

- [Generalization bound for norm-bounded linear predictors with Lipschitz loss](../../generalization-bounds-and-concentration/generalization-bound-for-norm-bounded-linear-predictors-with.md)

## Related topics

- [The support vector expansion](exists-eq-kernel-expansion-of-is-minimiz.md)

## Sources

- Understanding Machine Learning: From Theory to Algorithms — Shalev-Shwartz, Ben-David / Cambridge University Press, Ch 15: Theorem 15.4, Corollary 15.7; Theorem 26.13 referenced. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
