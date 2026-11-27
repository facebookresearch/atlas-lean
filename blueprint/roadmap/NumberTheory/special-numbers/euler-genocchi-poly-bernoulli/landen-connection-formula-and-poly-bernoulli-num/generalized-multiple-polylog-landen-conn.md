# Generalized Landen connection formula

Let $g = (g_0, g_1, \dots, g_s)$ be Landen data,
where $g_0$ has rows $(1, -1)$ and $(c_0, d_0)$ and each $g_i$ ($1 \le i \le s$) has rows
$(a_i, b_i)$ and $(c_i, d_i)$ with $a_i d_i - b_i c_i \ne 0$. Let $\tilde g$ be the transformed
data: $\tilde g_0$ has rows $(1, -1)$ and $(-d_0, -c_0)$, and $\tilde g_i = M g_i$, where $M$ is
the matrix with rows $(1, 0)$ and $(c_0 - d_0, -1)$. For all $\beta, \gamma \in \mathbb{R}^s$ and
every finite (possibly empty) sequence $\mathbf{k}$ of positive integers,
$\mathrm{Li}_{\mathbf{k}}(g; (\beta, \gamma); \frac{z}{(c_0 - d_0) z - 1}) =
\mathrm{Li}_{\mathbf{k}}(\tilde g; (\beta, \gamma); z)$ in $\mathbb{R}[[z]]$, where
$\frac{z}{(c_0 - d_0) z - 1} = -\sum_{n \ge 0} (c_0 - d_0)^n z^{n+1}$ is substituted for $z$.

The paper also assumes $g_0 \in \mathrm{GL}_2(\mathbb{R})$, that is $c_0 + d_0 \ne 0$; this is not
needed. The invertibility of the $g_i$ is needed: with $a_i = c_i = 0$ the identity fails.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Theorem 2, Identity (8).
