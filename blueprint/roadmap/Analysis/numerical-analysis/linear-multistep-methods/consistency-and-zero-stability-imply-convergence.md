# Consistency and zero-stability imply convergence

Let a [linear multistep method](linear-multistep-method.md) be [consistent](truncation-error-and-consistency.md) and [zero-stable](zero-stability.md). Apply it to an initial value problem $y' = f(x, y)$, $y(x_0) = y_0$ on $[x_0, X_M]$ whose right-hand side $f$ is continuous on $[x_0, X_M] \times \mathbb{R}$ and satisfies a Lipschitz condition $|f(x, y) - f(x, z)| \le L|y - z|$ for all $x \in [x_0, X_M]$ and all real $y, z$, with starting values $y_s = \eta_s(h)$ such that $\delta(h) = \max_{0 \le s \le k-1} |\eta_s(h) - y(x_0 + sh)| \to 0$ as $h \to 0$. Then

$$\lim_{\substack{h \to 0\\ nh = x - x_0}} y_n = y(x) \qquad \text{for every } x \in [x_0, X_M].$$

More precisely, the global error $e_n = y(x_n) - y_n$ satisfies

$$|e_n| \le \Gamma^* \bigl[A k\, \delta(h) + (X_M - x_0) K \chi(kh)\bigr] \exp\bigl[(x_n - x_0) L \Gamma^* B\bigr],$$

where $A = \sum_j |\alpha_j|$, $B = \sum_j |\beta_j|$, $K = |\alpha_1| + 2|\alpha_2| + \cdots + k|\alpha_k| + B$, $\chi(\varepsilon) = \max\{|y'(x^*) - y'(x)| : x, x^* \in [x_0, X_M],\ |x^* - x| \le \varepsilon\}$, and $\Gamma^* = \Gamma/(1 - h|\alpha_k|^{-1}|\beta_k| L)$ with $\Gamma$ the bound of the [coefficients of the reciprocal polynomial](bounded-coefficients-of-the-reciprocal-polynomial.md), for $h$ small enough that $h|\beta_k| L < |\alpha_k|$.

## Depends on

- [Truncation error and consistency of a linear multistep method](truncation-error-and-consistency.md)
- [Zero-stability](zero-stability.md)
- [Bounded coefficients of the reciprocal of a root-stable polynomial](bounded-coefficients-of-the-reciprocal-polynomial.md)
- [Linear multistep method](linear-multistep-method.md)

## Proof depends on

- [Zero-stability is equivalent to the root condition](zero-stability-iff-root-condition.md)
- [Consistency conditions for linear multistep methods](consistency-conditions.md)
- [Error bound for perturbed linear difference equations](error-bound-for-perturbed-linear-difference-equations.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.4.2, Theorem 9 and its proof, estimates (73) and (74). The notes state the Lipschitz condition on a rectangle $|y - y_0| \le Y_M$. For an implicit method that does not control the computed values, which may leave the rectangle: implicit Euler for $y' = y^2$, $y(0) = 0$, has besides $y_n = 0$ the solution with $y_n = 0$ for $n < N$ and $y_N = 1/h$. So a global Lipschitz condition is used here, with steps $h|\beta_k| L < |\alpha_k|$ for which each implicit equation has exactly one solution. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
