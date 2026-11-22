# Klein's inequality

Let $E$ be a complex inner product space of finite dimension $n$, let $T$ and $S$ be self-adjoint operators on $E$ with eigenvalues $\mu_0 \ge \dots \ge \mu_{n-1}$ and $\lambda_0 \ge \dots \ge \lambda_{n-1}$ respectively (repeated according to multiplicity), and let $(b_i)_{i < n}$ be an orthonormal basis of $E$. Let $f : \mathbb{R} \to \mathbb{R}$ be convex on a convex set $s$ containing all $\mu_j$, all $\lambda_i$ and all diagonal entries $t_i = \operatorname{Re} \langle b_i, T b_i \rangle$, and differentiable at every $\lambda_i$. Then

$$
\sum_{i=0}^{n-1} \big( f(\lambda_i) + f'(\lambda_i)(t_i - \lambda_i) \big) \le \sum_{j=0}^{n-1} f(\mu_j).
$$

When $(b_i)$ is an orthonormal eigenbasis of $S$ with $S b_i = \lambda_i b_i$, the left side is $\operatorname{tr} f(S) + \operatorname{tr}(f'(S)(T - S))$, and the inequality reads $\operatorname{tr}[f(T) - f(S) - (T - S) f'(S)] \ge 0$, Klein's inequality in Carlen's form.

## Sources

- E. A. Carlen, Trace inequalities and quantum entropy: an introductory course, lecture-notes draft of May 3, 2009 (published in Contemp. Math. 529, 2010), Theorem 2.11. Theorem numbers refer to that draft.
