# Lower complexity bound for smooth convex minimisation

Let $L > 0$ and integers $k \ge 1$, $n \ge 2k + 1$. For every $x_0 \in \mathbb{R}^n$ there are a convex $C^\infty$ function $f$ on $\mathbb{R}^n$ with $L$-Lipschitz gradient and a minimiser $x^* \neq x_0$ of $f$ such that every sequence $(x_j)$ with $x_0$ given and

$$
x_j \in x_0 + \operatorname{span}\{\nabla f(x_0), \dots, \nabla f(x_{j-1})\} \quad \text{for all } j
$$

satisfies

$$
f(x_k) - f(x^*) \ge \frac{3L\,\|x_0 - x^*\|^2}{32(k+1)^2}
\qquad\text{and}\qquad
\|x_k - x^*\|^2 \ge \tfrac{1}{32}\|x_0 - x^*\|^2 .
$$

The sequence $(x_j)$ is the sequence of points at which a method queries the gradient, and the span condition is Assumption 2.1.4 of the source. Gradient descent, the conjugate gradient method and the [accelerated methods](../accelerated-gradient-methods/README.md) (with their query points $y_k$) satisfy it. The function is Nesterov's "worst function in the world", shifted by $x_0$:

$$
f_{2k+1}(x) = \frac{L}{4}\Big(\frac{1}{2}\Big[(x^{(1)})^2 + \sum_{i=1}^{2k} (x^{(i)} - x^{(i+1)})^2 + (x^{(2k+1)})^2\Big] - x^{(1)}\Big),
$$

a quadratic with tridiagonal Hessian $0 \preceq \nabla^2 f_{2k+1} \preceq L I$, minimised at $\bar x^{(i)} = 1 - \frac{i}{2k+2}$ for $i \le 2k+1$ and $\bar x^{(i)} = 0$ otherwise. From $x_0 = 0$, the $j$-th iterate of any method in the class has nonzero entries only in its first $j$ coordinates, so $f(x_k) \ge \min f_k$. For $n > 2k + 1$ the minimiser is not unique; the statement asks for one minimiser, and the one provided is the source's $x^*$, the shift of $\bar x$.

The bound is a **lower** bound on the error of every method in the class, valid for $k \le (n-1)/2$; it does not say that the error stays large after more than $(n-1)/2$ iterations. The source remarks that a finer analysis gives $L\|x_0 - x^*\|^2/(8(k+1)^2)$ and a constant arbitrarily close to $1$ in the second inequality; the statement above keeps the constants of the 1998 draft, whose second constant is $1/32$.

The proof follows the source. Shifting by $x_0$ reduces to $x_0 = 0$. The Krylov argument (Lemma 2.1.3 of the source) shows by strong induction that $x_j$ is supported on the first $j$ coordinates, because a gradient of $f_{{2k+1}}$ at a vector supported on the first $j$ coordinates is supported on the first $j + 1$. Then $f(x_k) - f^* \ge f_k^* - f_{{2k+1}}^* = \frac{L}{16(k+1)}$, and $\|\bar x\|^2 \le \frac{2k+2}{3}$ (from $\sum_{l=1}^{m} l^2 \le (m+1)^3/3$) turns this into the first bound. For the second, the coordinates $k+1, \dots, 2k+1$ of $x_k - \bar x$ are those of $-\bar x$, and $\sum_{l=1}^{k+1} l^2 \ge (k+1)^3/3$ gives $\|x_k - \bar x\|^2 \ge \frac{k+1}{12}$, stronger than the needed $\frac{k+1}{48}$.

## Informally uses

- [Nesterov's worst function in the world](worst-function.md): the witness $f = f_{2k+1}(\cdot - x_0)$.
- [The worst function is smooth, convex and $L$-smooth](worst-function-mem-class.md): smoothness, convexity and the $L$-Lipschitz gradient of the witness, transported by the shift $x \mapsto x - x_0$.
- [Minimum of the worst function on the first $k$ coordinates](worst-function-ge-of-support.md): with $k$ for the lower bound on $f(x_k)$ and with $2k + 1$ for the minimality of $x^*$.
- [Minimum value of the worst function](worst-function-worst-minimizer.md): $f^* = f_{2k+1}(\bar x)$.
- [Minimiser of the worst function](worst-minimizer.md): $x^* = x_0 + \bar x$.

## Background

- [Sublinear rate of gradient descent for smooth convex functions](../gradient-descent/gradient-descent-convex-sublinear-rate.md): a method in the class, whose $O(1/k)$ rate is far from this bound.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Section 2.1.2: Assumption 2.1.4, the functions $f_k$, Lemma 2.1.3, Corollary 2.1.1 and Theorem 2.1.6.
