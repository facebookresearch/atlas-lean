# Connected components of a basic semialgebraic set

Let $V \subseteq \mathbb{R}^n$ be the set of solutions of a system

$$q_1(x) = \dots = q_m(x) = 0, \quad p_1(x) > 0, \dots, p_s(x) > 0, \quad p_{s+1}(x) \ge 0, \dots, p_h(x) \ge 0$$

of real polynomials in $n$ variables, and let $d = \max\{2, \deg q_i, \deg p_j\}$. The number of equations $m$ is arbitrary. Then $V$ has at most $d(2d - 1)^{n + h - 1}$ connected components. Ben-Or derives this from the bound of Milnor and Thom for real algebraic varieties: he shrinks each strict inequality $p_j > 0$ to $p_j \ge \varepsilon$ for a small $\varepsilon > 0$ that keeps a point of every component, and then replaces each of the $h$ inequalities by an equation $p_j - c_j = y_j^2$ in a new variable $y_j$, which gives a variety in $\mathbb{R}^{n+h}$.

## Expansion

This page becomes ready once:

- Proof prerequisite: the Milnor–Thom bound, as a page of its own: a real algebraic variety in $\mathbb{R}^N$ defined by polynomials of degree at most $d \ge 2$ has at most $d(2d - 1)^{N - 1}$ connected components.

## Sources

- M. Ben-Or, "Lower bounds for algebraic computation trees", *Proceedings of the 15th Annual ACM Symposium on Theory of Computing*, 1983, pp. 80–86, <https://doi.org/10.1145/800061.808735>: Section 3, Theorem 2 ($\beta_d(n, h) \le d(2d - 1)^{n + h - 1}$) and its proof from Milnor's theorem
