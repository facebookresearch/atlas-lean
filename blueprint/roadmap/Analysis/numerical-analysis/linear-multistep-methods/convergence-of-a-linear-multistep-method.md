# Convergence of a linear multistep method

A [linear $k$-step method](linear-multistep-method.md) is *convergent* if, for every initial value problem $y' = f(x, y)$, $y(x_0) = y_0$ on $[x_0, X_M]$ whose right-hand side $f$ is continuous on $[x_0, X_M] \times \mathbb{R}$ and satisfies a Lipschitz condition $|f(x, y) - f(x, z)| \le L|y - z|$ for all $x \in [x_0, X_M]$ and all real $y, z$, the following holds. For every family of starting values $y_s = \eta_s(h)$, $s = 0, \dots, k - 1$, that is *consistent*, $\lim_{h \to 0} \eta_s(h) = y_0$ for each $s$, the values $y_n$ computed by the method (for steps $h|\beta_k| L < |\alpha_k|$, so that each implicit equation has exactly one solution) satisfy

$$\lim_{\substack{h \to 0\\ nh = x - x_0}} y_n = y(x) \qquad \text{for every } x \in [x_0, X_M],$$

where $y$ is the solution of the problem, which exists on $[x_0, X_M]$ and is unique by Picard's theorem under these hypotheses.

The definition asks for convergence from all consistent starting values, not only from exact ones, since in practice $y_1, \dots, y_{k-1}$ are computed by another method.

## Depends on

- [Linear multistep method](linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.4, Definition 7 and the paragraph after it, with the hypotheses of Theorem 1 (Picard's theorem). The notes state the Lipschitz condition on a rectangle $|y - y_0| \le Y_M$. For an implicit method that does not control the computed values, which may leave the rectangle: implicit Euler for $y' = y^2$, $y(0) = 0$, has besides $y_n = 0$ the solution with $y_n = 0$ for $n < N$ and $y_N = 1/h$. So a global Lipschitz condition is used here, with steps $h|\beta_k| L < |\alpha_k|$ for which each implicit equation has exactly one solution. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
