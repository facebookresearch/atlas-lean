# Alternating direction method of multipliers

ADMM solves $\min f(x) + g(z)$ subject to $Ax + Bz = c$ by alternately minimizing the augmented Lagrangian $L_\rho(x, z, y) = f(x) + g(z) + \langle y, Ax + Bz - c \rangle + \frac{\rho}{2}\|Ax + Bz - c\|^2$ over $x$ and over $z$, then taking the dual ascent step $y \leftarrow y + \rho(Ax + Bz - c)$. It blends the decomposability of dual decomposition with the robustness of the method of multipliers, which makes it suited to distributed model fitting: the lasso, sparse logistic regression and support vector machines all split into simple subproblems. Its basic convergence theorem rests on [Lagrange duality](../lagrange-duality/README.md): a saddle point of the unaugmented Lagrangian is assumed.

- [Convergence of ADMM](admm-residual-and-objective-convergence.md)

## Related topics

- [Lagrange duality](../lagrange-duality/README.md)
- [Moreau decomposition](../moreau-decomposition/README.md)
- [Least squares, ridge and lasso regression](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/README.md)
- [Logistic regression and support vector machines](../../../ComputerScience/machine-learning/supervised-learning/logistic-regression-and-support-vector-machines/README.md)
