# The worst function is smooth, convex and $L$-smooth

For $L \ge 0$, the [worst function](worst-function.md) $f_m$ on $\mathbb{R}^n$ is $C^\infty$, convex, and its gradient is $L$-Lipschitz: $f_m$ belongs to the class $F^{\infty,1}_L(\mathbb{R}^n)$, as the source shows from $0 \preceq \frac{L}{4} A_m \preceq L I$.

A proof without Hessians: convexity follows from $(a u + b v)^2 \le a u^2 + b v^2$ for $a + b = 1$, $a, b \ge 0$. With the vectors $c_j$ of the [worst function](worst-function.md) ($c_j = e_j$ for $1 \le j \le \min(m, n)$ and $c_j = 0$ otherwise), the gradient is $\nabla f_m(x) = \frac{L}{4}\big(\sum_{i=0}^{m} \langle a_i, x\rangle a_i - c_1\big)$ with $a_i = c_i - c_{i+1}$ (so $\nabla f_0 = 0$); the bound $\sum_{i=0}^{m} \langle a_i, u\rangle^2 \le 4\|u\|^2$ (from $(p - q)^2 \le 2p^2 + 2q^2$ and Bessel's inequality for the distinct basis vectors among the $c_j$) and the Cauchy–Schwarz inequality give $\|\sum_i \langle a_i, w\rangle a_i\| \le 4\|w\|$.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Section 2.1.2: the computation $0 \le f_k''(x) \le L I_n$, hence $f_k \in F^{\infty,1}_L(R^n)$.
