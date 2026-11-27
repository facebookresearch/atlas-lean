# Transformed Landen data

For Landen data $g = (g_0, g_1, \dots, g_s)$ with
$g_0 = \begin{pmatrix} 1 & -1 \\ c_0 & d_0 \end{pmatrix}$ and
$g_i = \begin{pmatrix} a_i & b_i \\ c_i & d_i \end{pmatrix}$ for $1 \le i \le s$, the transformed
data $\tilde g = (\tilde g_0, \tilde g_1, \dots, \tilde g_s)$ has the same $s$, with
$\tilde g_0 = \begin{pmatrix} 1 & -1 \\ -d_0 & -c_0 \end{pmatrix}$ and, for $1 \le i \le s$, the
matrix $\tilde g_i$ has first row $(a_i, b_i)$ and second row
$((c_0 - d_0) a_i - c_i, (c_0 - d_0) b_i - d_i)$. Equivalently,
$\tilde g_i = \begin{pmatrix} 1 & 0 \\ c_0 - d_0 & -1 \end{pmatrix} g_i$ for $0 \le i \le s$.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2, display before Theorem 2.
