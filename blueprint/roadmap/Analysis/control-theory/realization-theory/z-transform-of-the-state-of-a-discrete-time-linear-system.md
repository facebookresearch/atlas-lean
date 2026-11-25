# The z-transform of the state of a discrete-time linear system

Let $A \in \mathbb{C}^{N \times N}$, $B \in \mathbb{C}^{N \times m}$, $C \in \mathbb{C}^{p \times N}$ and $D \in \mathbb{C}^{p \times m}$, let $x_0 \in \mathbb{C}^N$, and let $(u(n))_{n \ge 0}$ be an input sequence in $\mathbb{C}^m$. Define the state and output by

$$x(0) = x_0, \qquad x(n+1) = A x(n) + B u(n), \qquad y(n) = C x(n) + D u(n) \qquad (n \ge 0).$$

For a sequence $v$ indexed by $n \ge 0$, write $V(z) = \sum_{n \ge 0} v(n) z^{-n}$, the one-sided z-transform, taken componentwise where the series converges absolutely. Suppose there are constants $M_A, M_u \ge 0$ and $r_A, r_u \ge 0$ with $\|A^n\| \le M_A r_A^n$ and $\|u(n)\| \le M_u r_u^n$ for every $n \ge 0$, and let $z \in \mathbb{C}$ with $z \ne 0$ and $|z| > \max(r_A, r_u)$. Then:

1. the series $U(z)$, $X(z)$ and $Y(z)$ converge absolutely;
2. $zI - A$ is invertible, with $(zI - A)^{-1} = \sum_{n \ge 0} A^n z^{-n-1}$;
3. $X(z) = (zI - A)^{-1}\big(z\, x_0 + B\, U(z)\big)$ and $Y(z) = C\, X(z) + D\, U(z)$.

In particular, for $x_0 = 0$, $Y(z) = \big(C(zI - A)^{-1}B + D\big)U(z)$. The factor $z$ in front of $x_0$ comes from the convention $V(z) = \sum_{n \ge 0} v(n) z^{-n}$, under which the advanced sequence $(v(n+1))_{n \ge 0}$ has transform $z(V(z) - v(0))$.

**Proof.** Let $\rho = \max(r_A, r_u)$ and $q = \rho / |z| < 1$. Then $\sum_n \|u(n)\| |z|^{-n} \le M_u \sum_n q^n < \infty$. By induction, $x(n) = A^n x_0 + \sum_{j < n} A^{n-1-j} B u(j)$, so $\|x(n)\| \le M_A r_A^n \|x_0\| + n M_A \|B\| M_u \rho^{n-1}$ when $\rho > 0$, and $x(n) = 0$ for $n \ge 2$ when $\rho = 0$. In both cases $\sum_n \|x(n)\| |z|^{-n} < \infty$, since $\sum_n n q^n < \infty$, and $y$ inherits absolute convergence from $x$ and $u$; this is part 1. The series $S = \sum_{n \ge 0} A^n z^{-n-1}$ converges absolutely because $\|A^n z^{-n-1}\| \le M_A |z|^{-1} (r_A / |z|)^n$, and $(zI - A) S = \sum_{n \ge 0} A^n z^{-n} - \sum_{n \ge 0} A^{n+1} z^{-n-1} = I$, the partial sums telescoping to $I - A^{K+1} z^{-K-1} \to I$; likewise $S(zI - A) = I$, which is part 2. Taking the one-sided transform of $x(n+1) = A x(n) + B u(n)$ componentwise, the advance rule gives $z(X(z) - x_0) = A X(z) + B U(z)$, that is, $(zI - A) X(z) = z x_0 + B U(z)$; multiplying by $(zI - A)^{-1}$ and transforming the output equation by linearity give part 3.

## Proof depends on

- [The z-transform: region of convergence, shifts and convolution](../../harmonic-analysis/integral-transforms/z-transform-region-of-convergence-shift-and-convolution.md): the one-sided advance rule $X'_+(z) = z(X_+(z) - x_0)$, applied componentwise

## Background

- [Laplace transform of the matrix exponential and of the state of a linear system](laplace-transform-of-the-state-of-a-linear-system.md): the continuous-time counterpart

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 3.5: Definition 3.12 (z-transform and region of convergence, p. 235) and the shift property (3.137) (p. 241). The state-space identity, the growth hypotheses and the region $|z| > \max(r_A, r_u)$ are derived on the page.
