# Dahlquist equivalence theorem

Let a [linear multistep method](linear-multistep-method.md) be [consistent](truncation-error-and-consistency.md), and apply it to initial value problems $y' = f(x, y)$, $y(x_0) = y_0$ on $[x_0, X_M]$ whose right-hand side $f$ is continuous on $[x_0, X_M] \times \mathbb{R}$ and satisfies a Lipschitz condition $|f(x, y) - f(x, z)| \le L|y - z|$ for all $x \in [x_0, X_M]$ and all real $y, z$, and with consistent starting values. Then the method is [convergent](convergence-of-a-linear-multistep-method.md) if and only if it is [zero-stable](zero-stability.md).

Moreover, if the method is zero-stable, the solution $y$ has $p + 1$ continuous derivatives, the truncation error is $O(h^p)$ and the starting errors satisfy $\max_{0 \le s \le k-1} |y_s - y(x_s)| = O(h^p)$, then the global error is $\max_{x_n \le X_M} |y(x_n) - y_n| = O(h^p)$.

The cited statement asserts the order-$p$ error bound without the hypothesis on the starting errors; the bound of the sufficiency proof, linear in $\max_s |y_s - y(x_s)|$, shows that starting errors of order $h^p$ are needed. A method that is not zero-stable has, however accurate its starting values, solutions that grow by arbitrarily large factors on a fixed interval.

## Depends on

- [Convergence of a linear multistep method](convergence-of-a-linear-multistep-method.md)
- [Truncation error and consistency of a linear multistep method](truncation-error-and-consistency.md)
- [Zero-stability](zero-stability.md)
- [Order of accuracy and error constants of a linear multistep method](order-of-accuracy-and-error-constants.md)

## Proof depends on

- [Convergence implies zero-stability](convergence-implies-zero-stability.md)
- [Consistency and zero-stability imply convergence](consistency-and-zero-stability-imply-convergence.md)
- [Error bound for perturbed linear difference equations](error-bound-for-perturbed-linear-difference-equations.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.4.2, Theorem 10 (Dahlquist), combining Theorems 7, 8 and 9, and the paragraph after it; the dependence on the starting error is the term $Ak\,\delta(h)$ of estimate (74). The notes state the Lipschitz condition on a rectangle $|y - y_0| \le Y_M$. For an implicit method that does not control the computed values, which may leave the rectangle: implicit Euler for $y' = y^2$, $y(0) = 0$, has besides $y_n = 0$ the solution with $y_n = 0$ for $n < N$ and $y_N = 1/h$. So a global Lipschitz condition is used here, with steps $h|\beta_k| L < |\alpha_k|$ for which each implicit equation has exactly one solution. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
