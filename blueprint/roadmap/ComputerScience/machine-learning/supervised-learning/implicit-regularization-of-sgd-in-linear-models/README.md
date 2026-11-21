# Implicit regularization of SGD in linear models

When a linear model has more parameters than data points and the equations $\langle w, x_i\rangle = y_i$ are solvable (for instance when the data matrix $X$ has full row rank), they have infinitely many solutions, all global minima of the empirical risk with the same curvature. Zhang, Bengio, Hardt, Recht and Vinyals (2017, Section 5) observe that stochastic gradient descent selects one of them: started from $w_0 = 0$, its updates $w_{t+1} = w_t - \eta_t e_t x_{i_t}$ keep the iterates in the span of the data, and the interpolant in that span is the unique interpolant of minimum norm, the kernel solution $w = X^\top \alpha$ with $X X^\top \alpha = y$. If SGD converges to an interpolant, it is therefore the minimum-norm one; the convergence itself is a hypothesis.

## Related topics

- [Effective ranks and benign overfitting](../effective-ranks-and-benign-overfitting/README.md): when the minimum-norm interpolant selected here predicts nearly as well as the best linear predictor.
- [Finite-sample expressivity of ReLU networks](../finite-sample-expressivity-of-relu-networks/README.md): the companion observation of the same paper, that networks can fit any labelling, so the choice among interpolants matters.
- [Least squares, ridge and lasso regression](../least-squares-ridge-and-lasso-regression/README.md): ridge regression with vanishing regularization also converges to the minimum-norm least-squares solution.
