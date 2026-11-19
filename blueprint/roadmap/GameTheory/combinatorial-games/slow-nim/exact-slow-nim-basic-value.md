# Basic-vector value

For $k \in \mathbb{N}$ and $x \in \mathbb{N}^{k+1}$, the basic-vector
value $B(x)$ is the largest $b \le \sum_i x_i$ for which some $z \le x$ (componentwise) is a
basic vector of type (A0), (A1) or (B) with parameter $b$; such a $b$ exists, since $z = 0$ is
basic of type (A0) with parameter $0$. For $k \ge 1$ the bound is automatic, because every basic
$z \le x$ with parameter $b$ has $b \le k b \le \sum_i z_i \le \sum_i x_i$, so $B(x)$ is the
largest parameter of a basic vector $z \le x$.

For $k = 0$ that maximum does not exist ($z = 0$ is basic of type (A0) for every even $b$), and
the bound $b \le \sum_i x_i$ totalizes this degenerate case.

## Sources

- Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1, Section 2, equation (1).
