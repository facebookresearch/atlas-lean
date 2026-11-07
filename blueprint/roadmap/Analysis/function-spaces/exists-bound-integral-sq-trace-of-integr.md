# Sobolev trace bound on the plane $z = 0$ in $\mathbb{R}^3$

Let $(f_n)_{n \in \mathbb{N}}$
be a sequence of continuously differentiable functions $\mathbb{R}^3 \to \mathbb{R}$, where
$\mathbb{R}^3$ has coordinates $(x, y, z)$ and the max norm. For $p \in \mathbb{R}^3$ write
$\|Df_n(p)\|$ for the operator norm of the derivative of $f_n$ at $p$, which equals
$|\partial_x f_n(p)| + |\partial_y f_n(p)| + |\partial_z f_n(p)|$, the sum of the absolute values
of the partial derivatives. Suppose that for every $n$ the function
$p \mapsto |f_n(p)|^2 + \|Df_n(p)\|^2$ is Lebesgue integrable on $\mathbb{R}^3$ with integral at
most $1$. Then there is a constant $C \ge 0$ such that for every $n$ the function
$(x, y) \mapsto |f_n(x, y, 0)|^2$ is Lebesgue integrable on $\mathbb{R}^2$ with integral at most
$C$.

Since $\|Df_n(p)\|$ is at least the Euclidean length $|\nabla f_n(p)|$ of the gradient, the
hypothesis implies the bound $\int_{\mathbb{R}^3} (|\nabla f_n|^2 + |f_n|^2) \le 1$ of the source
problem; conversely, if $f_n$ satisfies that bound, then $f_n / \sqrt{3}$ satisfies the hypothesis.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear function spaces and their duals), `benchmark/level2/ma_proofbench_l2_56.lean` at openbmb/ma-proofbench@31bab4c.
